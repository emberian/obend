"""Inject Linux fsync EIO in the native Segments fixture, then reopen in a fresh process.
Run under the build cap from lean/, with a fresh directory inside the build tree.
"""
import os
from pathlib import Path
import subprocess
import sys

work = Path(sys.argv[1]).resolve()
work.mkdir()
source = work / "inject.c"
source.write_text(r"""
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <linux/limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int fsync(int fd) {
    static int selector_synced;
    int (*real_sync)(int) = dlsym(RTLD_NEXT, "fsync");
    char link[64], path[PATH_MAX];
    snprintf(link, sizeof link, "/proc/self/fd/%d", fd);
    ssize_t n = readlink(link, path, sizeof path - 1);
    if (n < 0) return -1;
    path[n] = 0;
    const char *leaf = strrchr(path, '/');
    const char *mode = getenv("FAIL_BARRIER");
    int temp = leaf && (strcmp(leaf, "/log.index-new") == 0 || strcmp(leaf, "/checkpoint.tmp") == 0);
    if (mode && ((strcmp(mode, "temp") == 0 && temp) ||
        (strcmp(mode, "block") == 0 && leaf && strcmp(leaf, "/0") == 0) ||
        (strcmp(mode, "parent") == 0 && selector_synced && leaf && strcmp(leaf, "/.obend") == 0))) {
        fprintf(stderr, "injected EIO on %s\n", path);
        errno = EIO;
        return -1;
    }
    int rc = real_sync(fd);
    if (temp && rc == 0) selector_synced = 1;
    return rc;
}
""")
so = work / "inject.so"
env = dict(os.environ, TMPDIR=str(work))
subprocess.run(["cc", "-shared", "-fPIC", "-Wall", "-Werror", str(source), "-ldl", "-o", str(so)],
               check=True, env=env)
exe = Path(".lake/build/bin/vault-segments").resolve()
for mode in ("block", "temp", "parent"):
    vault = work / mode
    vault.mkdir()
    def call(op, *args, fault=False):
        settings = dict(env, LD_PRELOAD=str(so), FAIL_BARRIER=mode) if fault else env
        return subprocess.run([exe, op, vault, *args], text=True, capture_output=True, env=settings)
    seed = call("replace", "old")
    assert seed.returncode == 0 and seed.stdout.strip() == "ack", seed
    gens = vault / ".obend" / "log-segments"
    old, = gens.iterdir()
    if mode == "temp":
        # A cut can leave both names of the old rename holding the selected inode.
        os.link(vault / ".obend/log", vault / ".obend/log.index-new")
    failed = call("append" if mode == "block" else "replace", "new", fault=True)
    assert failed.returncode != 0 and "injected EIO" in failed.stderr and "ack" not in failed.stdout, failed
    assert old.exists(), "retired old generation before selector parent sync"
    read = call("read")
    expected = {"block": "oldnew", "temp": "old", "parent": "new"}[mode]
    assert read.returncode == 0 and read.stdout.strip() == expected, read
    retry = call("append", "retry")
    assert retry.returncode != 0 and "storage recovery required" in retry.stderr, retry
    print(f"{mode}: no receipt, old generation retained, warm read={expected}, fresh writer refused")

ck_vault = work / "checkpoint-barriers"
ck = ck_vault / ".obend" / "checkpoint"
def call_ck(value, fault_mode=None):
    settings = dict(env, LD_PRELOAD=str(so), FAIL_BARRIER=fault_mode) if fault_mode else env
    return subprocess.run([exe, "atomic", ck, value], text=True, capture_output=True, env=settings)

seeded = call_ck("old-ck")
assert seeded.returncode == 0 and seeded.stdout.strip() == "ack" and ck.read_text() == "old-ck", seeded
os.link(ck, str(ck) + ".tmp")
temp_fail = call_ck("new-ck", fault_mode="temp")
assert temp_fail.returncode != 0 and "injected EIO" in temp_fail.stderr and "ack" not in temp_fail.stdout, temp_fail
assert ck.read_text() == "old-ck", "temp sync fault mutated live checkpoint inode"
parent_fail = call_ck("new-ck", fault_mode="parent")
assert parent_fail.returncode != 0 and "injected EIO" in parent_fail.stderr and "ack" not in parent_fail.stdout, parent_fail
assert ck.read_text() == "new-ck", parent_fail
clean_ok = call_ck("final-ck")
assert clean_ok.returncode == 0 and clean_ok.stdout.strip() == "ack" and ck.read_text() == "final-ck", clean_ok
print("checkpoint: stale .tmp detached, temp/parent EIO refused without ack, final barrier clean")

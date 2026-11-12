#!/usr/bin/env python3
"""A log reader must wait for the vault lock, then read the complete selected generation.

Run on Linux with a built obend and a fresh fixture directory. The kernel's wait channel makes
this a lock test rather than a timing assumption about process startup. Every child gets a PID file.
"""
import fcntl
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def launch(binary, work, *args):
    child = subprocess.Popen([binary, *args], cwd=work, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True)
    pidfile = work / (args[0] + ".pid")
    pidfile.write_text(f"{child.pid}\n")
    return child, pidfile


def finish(child, pidfile, binary):
    try:
        out, err = child.communicate(timeout=30)
    except subprocess.TimeoutExpired:
        pid = int(pidfile.read_text())
        cmd = Path(f"/proc/{pid}/cmdline").read_bytes().split(b"\0")
        if pid != child.pid or os.fsdecode(cmd[0]) != binary:
            raise RuntimeError("PID file no longer names the test child; left running")
        os.kill(pid, signal.SIGKILL)
        child.communicate()
        raise
    if child.returncode:
        raise AssertionError(f"child exited {child.returncode}: {out}{err}")
    return out


def main():
    binary = os.path.abspath(sys.argv[1])
    work = Path(sys.argv[2]).absolute()
    work.mkdir()  # never overwrite another run's fixture
    (work / "Page.md").write_text("A page.\n")
    child, pid = launch(binary, work, "open")
    finish(child, pid, binary)
    with (work / ".obend" / "lock").open("a") as lock:
        # Linux exposes BSD flock and POSIX record locks independently. Hold both so this also
        # detects a runtime change in which native lock primitive IO.FS.Handle.lock uses.
        fcntl.flock(lock, fcntl.LOCK_EX)
        fcntl.lockf(lock, fcntl.LOCK_EX)
        child, pid = launch(binary, work, "log")
        channel = ""
        try:
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                if child.poll() is not None:
                    raise AssertionError("obend log finished while the vault lock was held")
                # Lean may run the IO action on a worker while its main thread waits on a futex.
                channels = [p.read_text().strip()
                            for p in Path(f"/proc/{child.pid}/task").glob("*/wchan")]
                channel = next((c for c in channels if "lock" in c), ",".join(channels))
                if "lock" in channel:
                    break
                time.sleep(0.01)
            else:
                raise AssertionError(f"reader did not reach a kernel lock wait: {channel}")
        finally:
            fcntl.lockf(lock, fcntl.LOCK_UN)
            fcntl.flock(lock, fcntl.LOCK_UN)
    out = finish(child, pid, binary)
    assert out.rstrip().endswith("one world"), out
    print(f"log reader waited in {channel}; after release it read one world")


if __name__ == "__main__":
    main()

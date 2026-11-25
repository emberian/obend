#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>
#include <lean/lean.h>

static lean_obj_res io_error(int err) {
    return lean_io_result_mk_error(lean_decode_io_error(err, NULL));
}

static lean_obj_res sync_fd(int fd) {
    int rc;
    do {
        rc = fsync(fd);
    } while (rc < 0 && errno == EINTR);
    return rc < 0 ? io_error(errno) : lean_io_result_mk_ok(lean_box(0));
}

/* Lean 4.35 IO.FS.Handle external data is the FILE* used by
   lean_io_prim_handle_flush. Borrow it for this call only. */
LEAN_EXPORT lean_obj_res obend_vault_fsync_file(b_lean_obj_arg h) {
    FILE *fp = lean_get_external_data(h);
    if (fflush(fp) != 0) return io_error(errno);
    int fd = fileno(fp);
    return fd < 0 ? io_error(errno) : sync_fd(fd);
}

/* Open before the namespace mutation to observe its writeback errors. */
LEAN_EXPORT lean_obj_res obend_vault_open_dir(b_lean_obj_arg path) {
    int fd;
    do {
        fd = open(lean_string_cstr(path), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return io_error(errno);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res obend_vault_fsync_dir(uint32_t fd) {
    return sync_fd((int)fd);
}

LEAN_EXPORT lean_obj_res obend_vault_close_dir(uint32_t fd) {
    if (close((int)fd) != 0) return io_error(errno);
    return lean_io_result_mk_ok(lean_box(0));
}

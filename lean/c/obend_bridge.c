#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <lean/lean.h>

typedef struct ObendSessionHandle {
    lean_object *lean_state;
    uint8_t *scratch_buf;
    size_t scratch_len;
    size_t scratch_cap;
    uint8_t *err_buf;
    size_t err_len;
    size_t err_cap;
} ObendSessionHandle;

extern void lean_initialize_runtime_module(void);
extern void lean_initialize(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object* initialize_obend_Obend_FFI_Bridge(uint8_t builtin);

static pthread_once_t lean_init_once = PTHREAD_ONCE_INIT;
static _Thread_local int g_thread_initialized = 0;

static void ensure_lean_global_init(void) {
    lean_initialize_runtime_module();
    lean_initialize();
    uint8_t builtin = 1;
    lean_object *res = initialize_obend_Obend_FFI_Bridge(builtin);
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
    } else {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        abort();
    }
    lean_io_mark_end_initialization();
}

static inline void ensure_lean_init(void) {
    pthread_once(&lean_init_once, ensure_lean_global_init);
    if (!g_thread_initialized) {
        lean_initialize_thread();
        g_thread_initialized = 1;
    }
}

static inline void ensure_lean_initialized(void) {
    ensure_lean_init();
}

/* Exported for the Rust side (`obend_ffi::pool::ensure_lean_thread_initialized`): initialize the
 * Lean runtime once per process and attach the calling thread once. Calling
 * `lean_initialize_thread` directly before `lean_initialize_runtime_module` is undefined and was
 * the inferred cause of the obend-gui native segfault (2026-11-04). */
void obend_ensure_lean_thread(void) {
    ensure_lean_init();
}

extern lean_object *obend_session_init_core(lean_object *cfg);
extern void obend_session_free_core(lean_object *s);
extern lean_object *obend_eval_cell_core(lean_object *s, lean_object *cell_bytes);
extern lean_object *obend_turn_propose_core(lean_object *s, lean_object *turn_bytes);
extern lean_object *obend_turn_commit_core(lean_object *s, lean_object *tid_bytes);
extern lean_object *obend_project_hardware_core(lean_object *s, lean_object *hw_bytes);
extern lean_object *obend_verify_receipt_core(lean_object *s, lean_object *rcpt_bytes);
extern lean_object *obend_get_last_error_core(lean_object *s);
extern lean_object *obend_view_affordances_core(lean_object *s, lean_object *query_bytes);
extern lean_object *obend_cell_pop_lean_core(lean_object *s, lean_object *cell_bytes);
extern lean_object *obend_cell_weave_cert_core(lean_object *s, lean_object *cert_bytes);

static inline lean_object *lean_mk_byte_array_from_buf(const uint8_t *buf, size_t len) {
    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len > 0 && buf != NULL) {
        memcpy(lean_sarray_cptr(ba), buf, len);
    }
    return ba;
}

static inline int session_sync_scratch(ObendSessionHandle *sess, lean_object *ba) {
    if (!sess || !ba) return -1;
    size_t len = lean_sarray_size(ba);
    if (len > sess->scratch_cap) {
        size_t next_cap = len < 4096 ? 4096 : len * 2;
        uint8_t *new_buf = (uint8_t*)realloc(sess->scratch_buf, next_cap);
        if (!new_buf) return -1;
        sess->scratch_buf = new_buf;
        sess->scratch_cap = next_cap;
    }
    sess->scratch_len = len;
    if (len > 0) {
        memcpy(sess->scratch_buf, lean_sarray_cptr(ba), len);
    }
    return 0;
}

ObendSessionHandle *obend_session_init(const uint8_t *config_ptr, size_t config_len) {
    ensure_lean_initialized();
    ObendSessionHandle *handle = (ObendSessionHandle*)calloc(1, sizeof(ObendSessionHandle));
    if (!handle) return NULL;
    handle->scratch_cap = 4096;
    handle->scratch_buf = (uint8_t*)calloc(1, handle->scratch_cap);
    handle->err_cap = 1024;
    handle->err_buf = (uint8_t*)calloc(1, handle->err_cap);
    if (!handle->scratch_buf || !handle->err_buf) {
        if (handle->scratch_buf) free(handle->scratch_buf);
        if (handle->err_buf) free(handle->err_buf);
        free(handle);
        return NULL;
    }
    lean_object *cfg = lean_mk_byte_array_from_buf(config_ptr, config_len);
    handle->lean_state = obend_session_init_core(cfg);
    return handle;
}

void obend_session_free(ObendSessionHandle *session_ptr) {
    if (!session_ptr) return;
    ensure_lean_initialized();
    if (session_ptr->lean_state) {
        lean_inc(session_ptr->lean_state);
        obend_session_free_core(session_ptr->lean_state);
        lean_dec(session_ptr->lean_state);
        session_ptr->lean_state = NULL;
    }
    if (session_ptr->scratch_buf) free(session_ptr->scratch_buf);
    if (session_ptr->err_buf) free(session_ptr->err_buf);
    free(session_ptr);
}

int32_t obend_eval_cell(
    ObendSessionHandle *session_ptr,
    const uint8_t *cell_ptr,
    size_t cell_len,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    if (cell_len > 0 && !cell_ptr) return -1;
    ensure_lean_initialized();
    lean_object *cell_ba = lean_mk_byte_array_from_buf(cell_ptr, cell_len);
    lean_object *res = obend_eval_cell_core(session_ptr->lean_state, cell_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *inner = lean_ctor_get(res, 1);
    lean_object *out_ba = lean_ctor_get(inner, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(inner, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    if (session_sync_scratch(session_ptr, out_ba) != 0) {
        lean_dec(res);
        return -1;
    }
    *out_ptr = session_ptr->scratch_buf;
    *out_len = session_ptr->scratch_len;

    lean_dec(res);
    return code;
}

int32_t obend_turn_propose(
    ObendSessionHandle *session_ptr,
    const uint8_t *turn_ptr,
    size_t turn_len,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    if (turn_len > 0 && !turn_ptr) return -1;
    ensure_lean_initialized();
    lean_object *turn_ba = lean_mk_byte_array_from_buf(turn_ptr, turn_len);
    lean_object *res = obend_turn_propose_core(session_ptr->lean_state, turn_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *inner = lean_ctor_get(res, 1);
    lean_object *out_ba = lean_ctor_get(inner, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(inner, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    if (session_sync_scratch(session_ptr, out_ba) != 0) {
        lean_dec(res);
        return -1;
    }
    *out_ptr = session_ptr->scratch_buf;
    *out_len = session_ptr->scratch_len;

    lean_dec(res);
    return code;
}

int32_t obend_turn_commit(
    ObendSessionHandle *session_ptr,
    const uint8_t *turn_id_ptr,
    size_t turn_id_len
) {
    if (!session_ptr) return -1;
    if (turn_id_len > 0 && !turn_id_ptr) return -1;
    ensure_lean_initialized();
    lean_object *tid_ba = lean_mk_byte_array_from_buf(turn_id_ptr, turn_id_len);
    lean_object *res = obend_turn_commit_core(session_ptr->lean_state, tid_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(res, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    lean_dec(res);
    return code;
}

int32_t obend_project_hardware(
    ObendSessionHandle *session_ptr,
    const uint8_t *hw_ptr,
    size_t hw_len,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    if (hw_len > 0 && !hw_ptr) return -1;
    ensure_lean_initialized();
    lean_object *hw_ba = lean_mk_byte_array_from_buf(hw_ptr, hw_len);
    lean_object *res = obend_project_hardware_core(session_ptr->lean_state, hw_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *inner = lean_ctor_get(res, 1);
    lean_object *out_ba = lean_ctor_get(inner, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(inner, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    if (session_sync_scratch(session_ptr, out_ba) != 0) {
        lean_dec(res);
        return -1;
    }
    *out_ptr = session_ptr->scratch_buf;
    *out_len = session_ptr->scratch_len;

    lean_dec(res);
    return code;
}

int32_t obend_verify_receipt(
    ObendSessionHandle *session_ptr,
    const uint8_t *receipt_ptr,
    size_t receipt_len
) {
    if (!session_ptr) return -1;
    if (receipt_len > 0 && !receipt_ptr) return -1;
    ensure_lean_initialized();
    lean_object *rcpt_ba = lean_mk_byte_array_from_buf(receipt_ptr, receipt_len);
    lean_object *res = obend_verify_receipt_core(session_ptr->lean_state, rcpt_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(res, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    lean_dec(res);
    return code;
}

int32_t obend_get_last_error(
    ObendSessionHandle *session_ptr,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    ensure_lean_initialized();
    lean_inc(session_ptr->lean_state);
    lean_object *err_ba = obend_get_last_error_core(session_ptr->lean_state);
    size_t len = lean_sarray_size(err_ba);
    if (len + 1 > session_ptr->err_cap) {
        size_t next_cap = (len + 1) < 1024 ? 1024 : (len + 1) * 2;
        uint8_t *new_buf = (uint8_t*)realloc(session_ptr->err_buf, next_cap);
        if (!new_buf) {
            lean_dec(err_ba);
            return -1;
        }
        session_ptr->err_buf = new_buf;
        session_ptr->err_cap = next_cap;
    }
    session_ptr->err_len = len;
    if (len > 0) {
        memcpy(session_ptr->err_buf, lean_sarray_cptr(err_ba), len);
    }
    session_ptr->err_buf[len] = '\0';
    *out_ptr = session_ptr->err_buf;
    *out_len = session_ptr->err_len;

    lean_dec(err_ba);
    return 0;
}

int32_t obend_view_affordances(
    ObendSessionHandle *session_ptr,
    const uint8_t *query_ptr,
    size_t query_len,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    if (query_len > 0 && !query_ptr) return -1;
    ensure_lean_initialized();
    lean_object *query_ba = lean_mk_byte_array_from_buf(query_ptr, query_len);
    lean_object *res = obend_view_affordances_core(session_ptr->lean_state, query_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *inner = lean_ctor_get(res, 1);
    lean_object *out_ba = lean_ctor_get(inner, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(inner, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    if (session_sync_scratch(session_ptr, out_ba) != 0) {
        lean_dec(res);
        return -1;
    }
    *out_ptr = session_ptr->scratch_buf;
    *out_len = session_ptr->scratch_len;

    lean_dec(res);
    return code;
}

int32_t obend_cell_pop_lean(
    ObendSessionHandle *session_ptr,
    const uint8_t *cell_ptr,
    size_t cell_len,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    if (cell_len > 0 && !cell_ptr) return -1;
    ensure_lean_initialized();
    lean_object *cell_ba = lean_mk_byte_array_from_buf(cell_ptr, cell_len);
    lean_object *res = obend_cell_pop_lean_core(session_ptr->lean_state, cell_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *inner = lean_ctor_get(res, 1);
    lean_object *out_ba = lean_ctor_get(inner, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(inner, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    if (session_sync_scratch(session_ptr, out_ba) != 0) {
        lean_dec(res);
        return -1;
    }
    *out_ptr = session_ptr->scratch_buf;
    *out_len = session_ptr->scratch_len;

    lean_dec(res);
    return code;
}

int32_t obend_cell_weave_cert(
    ObendSessionHandle *session_ptr,
    const uint8_t *cert_ptr,
    size_t cert_len,
    uint8_t **out_ptr,
    size_t *out_len
) {
    if (!session_ptr || !out_ptr || !out_len) return -1;
    if (cert_len > 0 && !cert_ptr) return -1;
    ensure_lean_initialized();
    lean_object *cert_ba = lean_mk_byte_array_from_buf(cert_ptr, cert_len);
    lean_object *res = obend_cell_weave_cert_core(session_ptr->lean_state, cert_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *inner = lean_ctor_get(res, 1);
    lean_object *out_ba = lean_ctor_get(inner, 0);
    int32_t code = (int32_t)lean_unbox_uint32(lean_ctor_get(inner, 1));

    lean_inc(new_state);
    session_ptr->lean_state = new_state;

    if (session_sync_scratch(session_ptr, out_ba) != 0) {
        lean_dec(res);
        return -1;
    }
    *out_ptr = session_ptr->scratch_buf;
    *out_len = session_ptr->scratch_len;

    lean_dec(res);
    return code;
}



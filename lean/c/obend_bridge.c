#include <stdint.h>
#include <stdlib.h>
#include <string.h>
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

extern lean_object *obend_session_init_core(lean_object *cfg);
extern void obend_session_free_core(lean_object *s);
extern lean_object *obend_eval_cell_core(lean_object *s, lean_object *cell_bytes);
extern lean_object *obend_turn_propose_core(lean_object *s, lean_object *turn_bytes);
extern lean_object *obend_turn_commit_core(lean_object *s, lean_object *tid_bytes);
extern lean_object *obend_project_hardware_core(lean_object *s, lean_object *hw_bytes);
extern lean_object *obend_verify_receipt_core(lean_object *s, lean_object *rcpt_bytes);
extern lean_object *obend_get_last_error_core(lean_object *s);

static inline lean_object *lean_mk_byte_array_from_buf(const uint8_t *buf, size_t len) {
    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len > 0 && buf != NULL) {
        memcpy(lean_byte_array_data(ba), buf, len);
    }
    return ba;
}

static inline void session_sync_scratch(ObendSessionHandle *sess, lean_object *ba) {
    size_t len = lean_byte_array_size(ba);
    if (len > sess->scratch_cap) {
        size_t next_cap = len < 4096 ? 4096 : len * 2;
        sess->scratch_buf = (uint8_t*)realloc(sess->scratch_buf, next_cap);
        sess->scratch_cap = next_cap;
    }
    sess->scratch_len = len;
    if (len > 0) {
        memcpy(sess->scratch_buf, lean_byte_array_data(ba), len);
    }
}

ObendSessionHandle *obend_session_init(const uint8_t *config_ptr, size_t config_len) {
    ObendSessionHandle *handle = (ObendSessionHandle*)calloc(1, sizeof(ObendSessionHandle));
    if (!handle) return NULL;
    lean_object *cfg = lean_mk_byte_array_from_buf(config_ptr, config_len);
    handle->lean_state = obend_session_init_core(cfg);
    return handle;
}

void obend_session_free(ObendSessionHandle *session_ptr) {
    if (!session_ptr) return;
    if (session_ptr->lean_state) {
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
    lean_object *cell_ba = lean_mk_byte_array_from_buf(cell_ptr, cell_len);
    lean_object *res = obend_eval_cell_core(session_ptr->lean_state, cell_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *out_ba = lean_ctor_get(res, 1);
    int32_t code = (int32_t)lean_unbox(lean_ctor_get(res, 2));

    lean_inc(new_state);
    lean_dec(session_ptr->lean_state);
    session_ptr->lean_state = new_state;

    session_sync_scratch(session_ptr, out_ba);
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
    lean_object *turn_ba = lean_mk_byte_array_from_buf(turn_ptr, turn_len);
    lean_object *res = obend_turn_propose_core(session_ptr->lean_state, turn_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *out_ba = lean_ctor_get(res, 1);
    int32_t code = (int32_t)lean_unbox(lean_ctor_get(res, 2));

    lean_inc(new_state);
    lean_dec(session_ptr->lean_state);
    session_ptr->lean_state = new_state;

    session_sync_scratch(session_ptr, out_ba);
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
    lean_object *tid_ba = lean_mk_byte_array_from_buf(turn_id_ptr, turn_id_len);
    lean_object *res = obend_turn_commit_core(session_ptr->lean_state, tid_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    int32_t code = (int32_t)lean_unbox(lean_ctor_get(res, 1));

    lean_inc(new_state);
    lean_dec(session_ptr->lean_state);
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
    lean_object *hw_ba = lean_mk_byte_array_from_buf(hw_ptr, hw_len);
    lean_object *res = obend_project_hardware_core(session_ptr->lean_state, hw_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    lean_object *out_ba = lean_ctor_get(res, 1);
    int32_t code = (int32_t)lean_unbox(lean_ctor_get(res, 2));

    lean_inc(new_state);
    lean_dec(session_ptr->lean_state);
    session_ptr->lean_state = new_state;

    session_sync_scratch(session_ptr, out_ba);
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
    lean_object *rcpt_ba = lean_mk_byte_array_from_buf(receipt_ptr, receipt_len);
    lean_object *res = obend_verify_receipt_core(session_ptr->lean_state, rcpt_ba);

    lean_object *new_state = lean_ctor_get(res, 0);
    int32_t code = (int32_t)lean_unbox(lean_ctor_get(res, 1));

    lean_inc(new_state);
    lean_dec(session_ptr->lean_state);
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
    lean_object *err_ba = obend_get_last_error_core(session_ptr->lean_state);
    size_t len = lean_byte_array_size(err_ba);
    if (len + 1 > session_ptr->err_cap) {
        session_ptr->err_buf = (uint8_t*)realloc(session_ptr->err_buf, len + 1);
        session_ptr->err_cap = len + 1;
    }
    session_ptr->err_len = len;
    if (len > 0) {
        memcpy(session_ptr->err_buf, lean_byte_array_data(err_ba), len);
    }
    session_ptr->err_buf[len] = '\0';
    *out_ptr = session_ptr->err_buf;
    *out_len = session_ptr->err_len;

    lean_dec(err_ba);
    return 0;
}

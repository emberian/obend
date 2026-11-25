/* Serialized hosted fixture for the four sDDF ownership queues. Link to
 * EmitPnk's dn_echo with CakeML --pancake --main_return=true. */
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum { N = 4, TX_COUNT = 2, BATCH = 2, CAP = 4096 };
struct packet { uint16_t slot, length; };
struct ring { struct packet slots[N]; unsigned head, count; };
struct shard {
    struct ring rx_active, rx_free, tx_free, tx_active;
    unsigned char rx[N][CAP], tx[TX_COUNT][CAP];
    uint64_t observed;
};
enum stop { BUDGET, IDLE, BACKPRESSURE, INVALID };

extern uint32_t dn_echo(uint64_t src, uint64_t dst, uint64_t len, uint64_t cap);
extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
void cml_clear(void) {}
/* The echo image never installs dynamic code. */
void *cml_install(uint8_t *src, size_t len, uint8_t *dest) {
    (void)src; (void)len; (void)dest;
    abort();
}
void cml_err(int code) { (void)code; abort(); }

static struct packet peek(const struct ring *q) {
    assert(q->count > 0);
    return q->slots[q->head];
}
static struct packet take(struct ring *q) {
    struct packet p = peek(q);
    q->head = (q->head + 1) % N;
    --q->count;
    return p;
}
static void put(struct ring *q, struct packet p) {
    assert(q->count < N);
    q->slots[(q->head + q->count) % N] = p;
    ++q->count;
}

static enum stop step_bounded_batch(struct shard *s) {
    for (unsigned k = 0; k < BATCH; ++k) {
        if (!s->rx_active.count) return IDLE;
        if (!s->tx_free.count) return BACKPRESSURE;
        struct packet rx = peek(&s->rx_active);
        struct packet tx = peek(&s->tx_free);
        if (rx.slot >= N || tx.slot >= TX_COUNT || rx.length > CAP) return INVALID;
        uint32_t n = dn_echo((uintptr_t)s->rx[rx.slot], (uintptr_t)s->tx[tx.slot], rx.length, CAP);
        if (n != rx.length) return INVALID;
        take(&s->rx_active);
        take(&s->tx_free);
        put(&s->tx_active, (struct packet){tx.slot, rx.length});
        put(&s->rx_free, (struct packet){rx.slot, 0});
        ++s->observed;
    }
    return BUDGET;
}

static unsigned count_id(const struct ring *q, unsigned id) {
    unsigned count = 0;
    for (unsigned i = 0; i < q->count; ++i)
        count += q->slots[(q->head + i) % N].slot == id;
    return count;
}

static void check_ownership(const struct shard *s) {
    for (unsigned id = 0; id < N; ++id)
        assert(count_id(&s->rx_active,id) + count_id(&s->rx_free,id) == 1);
    for (unsigned id = 0; id < TX_COUNT; ++id)
        assert(count_id(&s->tx_active,id) + count_id(&s->tx_free,id) == 1);
}

/* Linked allocation traps cover the fixture and the generated assembly. */
static bool booted;
extern void *__real_malloc(size_t), *__real_calloc(size_t, size_t), *__real_realloc(void *, size_t);
void *__wrap_malloc(size_t n) { if (booted) abort(); return __real_malloc(n); }
void *__wrap_calloc(size_t n, size_t k) { if (booted) abort(); return __real_calloc(n,k); }
void *__wrap_realloc(void *p, size_t n) { if (booted) abort(); return __real_realloc(p,n); }

int main(void) {
    static uint64_t runtime[2 * 1024 * 1024];
    static struct shard s;
    cml_heap = runtime;
    cml_stack = runtime + 1024 * 1024;
    cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
    for (unsigned i = 0; i < N; ++i) put(&s.rx_free,(struct packet){i,0});
    for (unsigned i = 0; i < TX_COUNT; ++i) put(&s.tx_free,(struct packet){i,0});
    booted = true;
    assert(step_bounded_batch(&s) == IDLE);
    for (unsigned turn = 0; turn < 10; ++turn) {
        const uint16_t lengths[N] = {0, 17, CAP, 9};
        for (unsigned i = 0; i < N; ++i) {
            struct packet rx = take(&s.rx_free);
            rx.length = lengths[i];
            for (unsigned j = 0; j < rx.length; ++j)
                s.rx[rx.slot][j] = (unsigned char)(turn + 41*i + 7*j);
            put(&s.rx_active,rx);
        }
        for (unsigned pair = 0; pair < N; pair += BATCH) {
            assert(step_bounded_batch(&s) == BUDGET);
            assert(s.observed == N*turn + pair + BATCH);
            check_ownership(&s);
            assert(step_bounded_batch(&s) == (s.rx_active.count ? BACKPRESSURE : IDLE));
            assert(s.observed == N*turn + pair + BATCH);
            for (unsigned i = pair; i < pair+BATCH; ++i) {
                struct packet tx = take(&s.tx_active);
                assert(tx.length == lengths[i]);
                for (unsigned j = 0; j < tx.length; ++j)
                    assert(s.tx[tx.slot][j] == (unsigned char)(turn + 41*i + 7*j));
                put(&s.tx_free,tx);
            }
            check_ownership(&s);
        }
    }
    struct packet bad = take(&s.rx_free);
    bad.length = CAP + 1;
    put(&s.rx_active,bad);
    assert(step_bounded_batch(&s) == INVALID && peek(&s.rx_active).slot == bad.slot);
    check_ownership(&s);
    const uint64_t tag = UINT64_C(1) << 63;
    assert(dn_echo(0,0,tag,0) == UINT32_MAX);
    assert(dn_echo(0,0,0,tag) == UINT32_MAX);
    assert(dn_echo(0,0,0,CAP+1) == UINT32_MAX);
    assert(dn_echo(0,0,2,1) == UINT32_MAX);
    return 0;
}

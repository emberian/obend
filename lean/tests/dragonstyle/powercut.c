/* Hosted, process-reset NVMe model exercising >32 turns (40 turns + checkpoint wrap),
 * variable 0B..4096B payloads (0B, 7B, 99B, 1024B, 4096B), real 512-byte LBA sectors
 * with volatile controller write cache + FLUSH + atomic FUA cSHAKE256 superblock,
 * and post-boot wrapped allocation abort traps. */
#define _GNU_SOURCE
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

enum {
    NUM_TURNS = 40,
    MAX_TURNS = 64,
    BUDGET_CAP = 64,
    SECTOR = 512,
    DATA_SECTORS = 8,
    ENTRY_SECTORS = 1 + DATA_SECTORS,
    MAX_BODY = 4096,
    STATE_HDR = 40,
    ENTRY_HDR = 40,
    ENTRY_STRIDE = ENTRY_HDR + MAX_BODY,
    SCRATCH_CTRL = 64,
    CELLS = 16,
    CUT_EXIT = 77
};

typedef uint8_t sector[SECTOR];
struct media { sector ctrl, wal[MAX_TURNS][ENTRY_SECTORS]; };
struct observer {
    unsigned issues[256], replies, authorization_checks;
    uint64_t generation, body_len;
    uint8_t body[MAX_BODY];
};
struct shared { struct media disk; struct observer seen; };
static struct shared *world;

/* ---- Self-contained zero-allocation SP 800-185 cSHAKE256 (Keccak-f[1600]) ---- */
static const uint64_t KECCAK_RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};
static const unsigned KECCAK_ROT[25] = {
     0,  1, 62, 28, 27,
    36, 44,  6, 55, 20,
     3, 10, 43, 25, 39,
    41, 45, 15, 21,  8,
    18,  2, 61, 56, 14
};
static uint64_t rotl64(uint64_t x, unsigned r) {
    return r ? ((x << r) | (x >> (64 - r))) : x;
}
static void keccak_f1600(uint64_t st[25]) {
    for (unsigned round = 0; round < 24; ++round) {
        uint64_t c[5], d[5], b[25];
        for (unsigned x = 0; x < 5; ++x)
            c[x] = st[x] ^ st[x + 5] ^ st[x + 10] ^ st[x + 15] ^ st[x + 20];
        for (unsigned x = 0; x < 5; ++x)
            d[x] = c[(x + 4) % 5] ^ rotl64(c[(x + 1) % 5], 1);
        for (unsigned i = 0; i < 25; ++i) st[i] ^= d[i % 5];
        for (unsigned y = 0; y < 5; ++y)
            for (unsigned x = 0; x < 5; ++x) {
                unsigned src = x + 5 * y;
                unsigned dst = y + 5 * ((2 * x + 3 * y) % 5);
                b[dst] = rotl64(st[src], KECCAK_ROT[src]);
            }
        for (unsigned y = 0; y < 5; ++y)
            for (unsigned x = 0; x < 5; ++x)
                st[x + 5 * y] = b[x + 5 * y] ^ ((~b[((x + 1) % 5) + 5 * y]) & b[((x + 2) % 5) + 5 * y]);
        st[0] ^= KECCAK_RC[round];
    }
}
static void absorb_block(uint64_t st[25], const uint8_t blk[136]) {
    for (unsigned i = 0; i < 17; ++i) {
        uint64_t w = 0;
        for (unsigned j = 0; j < 8; ++j) w |= ((uint64_t)blk[8 * i + j]) << (8 * j);
        st[i] ^= w;
    }
    keccak_f1600(st);
}
static void cshake256_32(const char *custom, const uint8_t *msg, size_t msg_len, uint8_t out[32]) {
    size_t clen = strlen(custom);
    assert(clen > 0 && clen < 32);
    uint64_t st[25] = {0};
    uint8_t blk[136] = {0};
    /* bytepad(encode_string("") || encode_string(custom), 136) */
    blk[0] = 1; blk[1] = 136;       /* left_encode(136) */
    blk[2] = 1; blk[3] = 0;         /* encode_string("") */
    blk[4] = 1; blk[5] = (uint8_t)(8 * clen); /* left_encode(8 * clen) */
    memcpy(blk + 6, custom, clen);
    absorb_block(st, blk);
    size_t off = 0;
    while (off + 136 <= msg_len) {
        absorb_block(st, msg + off);
        off += 136;
    }
    memset(blk, 0, sizeof(blk));
    size_t rem = msg_len - off;
    if (rem) memcpy(blk, msg + off, rem);
    if (rem == 135) {
        blk[135] = 0x04 ^ 0x80;
    } else {
        blk[rem] = 0x04;
        blk[135] = 0x80;
    }
    absorb_block(st, blk);
    for (unsigned i = 0; i < 4; ++i)
        for (unsigned j = 0; j < 8; ++j)
            out[8 * i + j] = (uint8_t)(st[i] >> (8 * j));
}

static void put_be64(uint8_t *p, uint64_t v) {
    for (int i = 0; i < 8; ++i) p[i] = (uint8_t)(v >> (8 * (7 - i)));
}
static uint64_t get_be64(const uint8_t *p) {
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i) v = (v << 8) | p[i];
    return v;
}
static void put_le64(uint8_t *p, uint64_t v) { memcpy(p, &v, 8); }
static uint64_t get_le64(const uint8_t *p) { uint64_t v; memcpy(&v, p, 8); return v; }

static const char *DOM_SUPERBLOCK = "OBEND.NVME.SUPERBLOCK/v1";
static const char *DOM_PAYLOAD    = "OBEND.NVME.PAYLOAD/v1";
static const char *DOM_CHAIN      = "OBEND.NVME.CHAIN/v1";

struct ring { uint64_t head, tail; uint16_t slots[CELLS]; };
static void put(struct ring *q, uint16_t id) {
    assert(q->tail - q->head < CELLS);
    q->slots[q->tail++ % CELLS] = id;
}
static uint16_t get(struct ring *q) {
    assert(q->tail != q->head);
    return q->slots[q->head++ % CELLS];
}
struct lease { uint16_t owner, slot; uint64_t epoch, generation; };
static bool valid(struct lease a, struct lease b) {
    return a.owner == b.owner && a.slot == b.slot && a.epoch == b.epoch &&
        a.generation == b.generation;
}
static bool recycle(struct lease *l) {
    if (l->generation < UINT64_MAX) { ++l->generation; return true; }
    if (l->epoch == UINT64_MAX) return false;
    ++l->epoch; l->generation = 0; return true;
}

enum cut { NORMAL, DMA, FLUSHED, FUA_OLD, FUA_NEW, DISPATCHED, SENT, EIO_WAL, EIO_FLUSH, EIO_FUA, EIO_FUA_NEW };
struct fault { enum cut cut; int reverse; unsigned bytes; };
static struct fault fault;
static struct ring rx, rx_free, storage, storage_free, tx, tx_free;
static sector cache[ENTRY_SECTORS];
static uint8_t tickets[NUM_TURNS][72];
static uint8_t expected_sb_tags[NUM_TURNS + 1][32];
static _Alignas(8) uint8_t state[STATE_HDR + ENTRY_STRIDE * MAX_TURNS];
static _Alignas(8) uint8_t scratch[SCRATCH_CTRL + MAX_BODY];
static unsigned phase;
static bool cached[ENTRY_SECTORS];
static bool booted;
static uint64_t active_max_turns = MAX_TURNS;
static uint64_t active_budget_cap = BUDGET_CAP;
static uint8_t current_chain_dig[32];
static uint64_t current_base_gen;
static uint64_t current_cp_nullifier;
static bool skip_ticket_check;

extern uint64_t turnIntake(uintptr_t, uint64_t, uintptr_t, uintptr_t);
extern uint64_t parseFrame(uintptr_t, uint64_t);
extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
void cml_clear(void) {}
void *cml_install(uint8_t *src, size_t n, uint8_t *dst) {
    (void)src; (void)n; (void)dst; abort();
}
void cml_err(int code) { (void)code; abort(); }
extern void *__real_malloc(size_t), *__real_calloc(size_t, size_t), *__real_realloc(void *, size_t);
void *__wrap_malloc(size_t n) { if (booted) abort(); return __real_malloc(n); }
void *__wrap_calloc(size_t a, size_t b) { if (booted) abort(); return __real_calloc(a, b); }
void *__wrap_realloc(void *p, size_t n) { if (booted) abort(); return __real_realloc(p, n); }

static void encode_superblock(sector dst, uint64_t gen, uint64_t base, uint64_t cnt,
                              uint64_t hw, const uint8_t chain_dig[32]) {
    memset(dst, 0, SECTOR);
    memcpy(dst, "OBNVME01", 8);
    put_be64(dst + 8, gen);
    put_be64(dst + 16, base);
    put_be64(dst + 24, cnt);
    put_be64(dst + 32, hw);
    memcpy(dst + 40, chain_dig, 32);
    cshake256_32(DOM_SUPERBLOCK, dst, 72, dst + 72);
}

static bool decode_superblock(const sector src, uint64_t *gen, uint64_t *base,
                              uint64_t *cnt, uint64_t *hw, uint8_t chain_dig[32]) {
    if (memcmp(src, "OBNVME01", 8) != 0) return false;
    for (size_t i = 104; i < SECTOR; ++i) if (src[i] != 0) return false;
    uint8_t tag[32];
    cshake256_32(DOM_SUPERBLOCK, src, 72, tag);
    if (memcmp(src + 72, tag, 32) != 0) return false;
    *gen = get_be64(src + 8);
    *base = get_be64(src + 16);
    *cnt = get_be64(src + 24);
    *hw = get_be64(src + 32);
    memcpy(chain_dig, src + 40, 32);
    return true;
}

static void record_preimage(uint8_t out[72], uint64_t principal, uint64_t nonce,
                            uint64_t nullifier, uint64_t cost,
                            const uint8_t *payload, size_t plen) {
    put_be64(out + 0, principal);
    put_be64(out + 8, nonce);
    put_be64(out + 16, nullifier);
    put_be64(out + 24, cost);
    put_be64(out + 32, (uint64_t)plen);
    cshake256_32(DOM_PAYLOAD, payload, plen, out + 40);
}

static void step_chain_digest(uint8_t out[32], const uint8_t prev[32], const uint8_t pre[72]) {
    uint8_t buf[104];
    memcpy(buf, prev, 32);
    memcpy(buf + 32, pre, 72);
    cshake256_32(DOM_CHAIN, buf, sizeof(buf), out);
}

static bool cold(uint8_t *view, uint64_t principal) {
    const struct media *d = &world->disk;
    uint64_t gen, base, cnt, hw;
    uint8_t cdig[32];
    if (!decode_superblock(d->ctrl, &gen, &base, &cnt, &hw, cdig)) return false;
    if (cnt > active_max_turns || cnt > MAX_TURNS || gen != base + cnt) return false;
    put_le64(view + 0, cnt);
    put_le64(view + 8, principal);
    put_le64(view + 16, active_max_turns);
    put_le64(view + 24, active_budget_cap);
    put_le64(view + 32, hw);
    current_base_gen = base;
    current_cp_nullifier = hw;
    memcpy(current_chain_dig, cdig, 32);
    for (uint64_t i = 0; i < cnt; ++i) {
        const uint8_t *meta = d->wal[i][0];
        if (memcmp(meta, "OBWAL001", 8) != 0) return false;
        uint64_t pr = get_be64(meta + 8);
        uint64_t no = get_be64(meta + 16);
        uint64_t nu = get_be64(meta + 24);
        uint64_t co = get_be64(meta + 32);
        uint64_t pl = get_be64(meta + 40);
        if (pl > MAX_BODY) return false;
        uint8_t *entry = view + STATE_HDR + ENTRY_STRIDE * i;
        put_le64(entry + 0, pl);
        put_le64(entry + 8, pr);
        put_le64(entry + 16, no);
        put_le64(entry + 24, nu);
        put_le64(entry + 32, co);
        size_t rem = (size_t)pl, off = 0;
        for (unsigned k = 0; k < DATA_SECTORS && rem > 0; ++k) {
            size_t take = rem < SECTOR ? rem : SECTOR;
            memcpy(entry + ENTRY_HDR + off, d->wal[i][1 + k], take);
            off += take; rem -= take;
        }
        uint8_t pdig[32];
        cshake256_32(DOM_PAYLOAD, entry + ENTRY_HDR, (size_t)pl, pdig);
        if (memcmp(meta + 48, pdig, 32) != 0) return false;
    }
    return true;
}

static void cut_at(enum cut point) { if (fault.cut == point) _exit(CUT_EXIT); }
static void control(const uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    assert(body == scratch + SCRATCH_CTRL && n <= MAX_BODY);
    assert(ctrl == scratch && size == SCRATCH_CTRL && get_le64(ctrl) == 255);
}

void ffiauthorize(uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    control(body, n, ctrl, size);
    uint64_t cnt = get_le64(state + 0);
    uint64_t gen = get_le64(ctrl + 8);
    assert(cnt < active_max_turns && phase == 0 && gen == current_base_gen + cnt + 1);
    ++world->seen.authorization_checks;
    if (skip_ticket_check) {
        put_le64(ctrl + 0, 0);
        return;
    }
    assert(gen >= 1 && gen <= NUM_TURNS);
    uint8_t pre[72];
    record_preimage(pre, get_le64(ctrl + 16), get_le64(ctrl + 24),
                    get_le64(ctrl + 32), get_le64(ctrl + 40), body, n);
    if (memcmp(pre, tickets[gen - 1], 72) == 0) put_le64(ctrl + 0, 0);
}

enum action { REFUSED, WAL_SECTOR, BARRIER, COMMIT };
enum opcode { FLUSH, WRITE };
struct command { enum opcode op; uint32_t nsid; uint64_t slba; uint16_t nlb; bool fua; };
static enum action classify(struct command q, unsigned *sector_idx) {
    uint64_t cnt = get_le64(state + 0);
    if (q.nsid != 1 || q.nlb || cnt >= active_max_turns) return REFUSED;
    uint64_t base = 1 + (uint64_t)ENTRY_SECTORS * cnt;
    if (phase == 2 && q.op == WRITE && q.fua && q.slba == 0) return COMMIT;
    if (phase != 1 || q.fua) return REFUSED;
    if (q.op == WRITE && q.slba >= base && q.slba < base + ENTRY_SECTORS) {
        unsigned k = (unsigned)(q.slba - base);
        if (!cached[k]) {
            if (sector_idx) *sector_idx = k;
            return WAL_SECTOR;
        }
        return REFUSED;
    }
    if (q.op == FLUSH && q.slba == 0) {
        for (unsigned k = 0; k < ENTRY_SECTORS; ++k) if (!cached[k]) return REFUSED;
        return BARRIER;
    }
    return REFUSED;
}

void ffiwal(uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    control(body, n, ctrl, size);
    uint64_t slot = get_le64(state + 0);
    assert(phase == 0 && slot < active_max_turns);
    if (fault.cut == EIO_WAL) return;
    phase = 1;
    uint16_t pending[ENTRY_SECTORS];
    for (unsigned k = 0; k < ENTRY_SECTORS; ++k) put(&storage, get(&storage_free));
    for (unsigned k = 0; k < ENTRY_SECTORS; ++k) pending[k] = get(&storage);
    uint8_t pdig[32];
    cshake256_32(DOM_PAYLOAD, body, n, pdig);
    for (unsigned step = 0; step < ENTRY_SECTORS; ++step) {
        unsigned k = fault.reverse ? (ENTRY_SECTORS - 1 - step) : step;
        unsigned got = 99;
        struct command q = {WRITE, 1, 1 + (uint64_t)ENTRY_SECTORS * slot + k, 0, false};
        assert(classify(q, &got) == WAL_SECTOR && got == k);
        memset(cache[k], 0, SECTOR);
        if (k == 0) {
            memcpy(cache[0], "OBWAL001", 8);
            put_be64(cache[0] + 8, get_le64(ctrl + 16));
            put_be64(cache[0] + 16, get_le64(ctrl + 24));
            put_be64(cache[0] + 24, get_le64(ctrl + 32));
            put_be64(cache[0] + 32, get_le64(ctrl + 40));
            put_be64(cache[0] + 40, (uint64_t)n);
            memcpy(cache[0] + 48, pdig, 32);
        } else {
            size_t off = (size_t)(k - 1) * SECTOR;
            if (off < n) {
                size_t take = n - off < SECTOR ? n - off : SECTOR;
                memcpy(cache[k], body + off, take);
            }
        }
        cached[k] = true;
        unsigned bytes = fault.bytes > step * SECTOR ? fault.bytes - step * SECTOR : 0;
        if (bytes > SECTOR) bytes = SECTOR;
        if (fault.cut == DMA) memcpy(world->disk.wal[slot][k], cache[k], bytes);
        put(&storage_free, pending[k]);
    }
    cut_at(DMA);
    put_le64(ctrl + 0, 0);
}

void ffiflush(uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    control(body, n, ctrl, size);
    assert(classify((struct command){FLUSH, 1, 0, 0, false}, NULL) == BARRIER);
    if (fault.cut == EIO_FLUSH) return;
    uint64_t slot = get_le64(state + 0);
    for (unsigned step = 0; step < ENTRY_SECTORS; ++step) {
        unsigned k = fault.reverse ? (ENTRY_SECTORS - 1 - step) : step;
        memcpy(world->disk.wal[slot][k], cache[k], SECTOR);
    }
    phase = 2; cut_at(FLUSHED); put_le64(ctrl + 0, 0);
}

void ffifua(uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    control(body, n, ctrl, size);
    assert(classify((struct command){WRITE, 1, 0, 0, true}, NULL) == COMMIT);
    cut_at(FUA_OLD);
    if (fault.cut == EIO_FUA) return;
    uint64_t cnt = get_le64(state + 0);
    uint64_t gen = get_le64(ctrl + 8);
    assert(gen == current_base_gen + cnt + 1);
    uint8_t pre[72], next_cdig[32];
    record_preimage(pre, get_le64(ctrl + 16), get_le64(ctrl + 24),
                    get_le64(ctrl + 32), get_le64(ctrl + 40), body, n);
    step_chain_digest(next_cdig, current_chain_dig, pre);
    sector next;
    encode_superblock(next, gen, current_base_gen, cnt + 1, current_cp_nullifier, next_cdig);
    if (!skip_ticket_check && current_base_gen == 0 && gen <= NUM_TURNS) {
        assert(memcmp(next + 72, expected_sb_tags[gen], 32) == 0);
    }
    memcpy(world->disk.ctrl, next, SECTOR);
    memcpy(current_chain_dig, next_cdig, 32);
    phase = 3; cut_at(FUA_NEW);
    if (fault.cut != EIO_FUA_NEW) put_le64(ctrl + 0, 0);
}

void ffidispatch(uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    control(body, n, ctrl, size);
    assert(phase == 3);
    uint64_t nullifier = get_le64(ctrl + 32);
    assert(nullifier < 256 && ++world->seen.issues[nullifier] == 1);
    phase = 4; cut_at(DISPATCHED); put_le64(ctrl + 0, 0);
}

void ffireply(uint8_t *body, size_t n, uint8_t *ctrl, size_t size) {
    control(body, n, ctrl, size);
    assert(phase == 0 || phase == 4);
    static _Alignas(8) uint8_t reader[sizeof(state)];
    memset(reader, 0, sizeof(reader));
    uint64_t principal = get_le64(ctrl + 16);
    uint64_t gen = get_le64(ctrl + 8);
    assert(cold(reader, principal));
    uint64_t cnt = get_le64(reader + 0);
    assert(gen > current_base_gen && gen <= current_base_gen + cnt);
    uint64_t idx = gen - current_base_gen - 1;
    const uint8_t *entry = reader + STATE_HDR + ENTRY_STRIDE * idx;
    assert(get_le64(entry + 0) == n);
    assert(get_le64(entry + 8) == principal);
    assert(get_le64(entry + 16) == get_le64(ctrl + 24));
    assert(get_le64(entry + 24) == get_le64(ctrl + 32));
    assert(get_le64(entry + 32) == get_le64(ctrl + 40));
    if (n) assert(memcmp(entry + ENTRY_HDR, body, n) == 0);
    put(&tx, get(&tx_free));
    world->seen.body_len = n;
    if (n) memcpy(world->seen.body, body, n);
    world->seen.generation = gen;
    ++world->seen.replies;
    put(&tx_free, get(&tx));
    cut_at(SENT);
    put_le64(ctrl + 0, 0);
}

static const char prefix[] = "POST /turn HTTP/1.1\r\nHost: appliance\r\nContent-Length: ";
struct input {
    uint8_t bytes[64 + MAX_BODY];
    size_t n;
    uint64_t channel_principal;
    uint64_t principal, nonce, nullifier, cost;
};

static struct input frame(uint64_t principal, uint64_t nonce, uint64_t id,
                          uint64_t charge, size_t plen) {
    struct input r;
    memset(&r, 0, sizeof(r));
    assert(plen <= MAX_BODY);
    r.channel_principal = principal;
    r.principal = principal; r.nonce = nonce; r.nullifier = id; r.cost = charge;
    size_t h = sizeof(prefix) - 1;
    memcpy(r.bytes, prefix, h);
    char num[16];
    int d = snprintf(num, sizeof(num), "%zu", plen);
    assert(d >= 1 && d <= 4);
    memcpy(r.bytes + h, num, (size_t)d); h += (size_t)d;
    memcpy(r.bytes + h, "\r\n\r\n", 4); h += 4;
    for (size_t j = 0; j < plen; ++j) r.bytes[h + j] = (uint8_t)(id * 13 + j * 41 + 7);
    r.n = h + plen;
    return r;
}

static struct input turn_input(unsigned i) {
    if (i == 1) return frame(1, 17, 1, 20, 0);
    if (i == 2) return frame(1, 31, 2, 44, 1024);
    if (i == 3) return frame(2, 3, 3, 1, 7);
    if (i == 4) return frame(2, 4, 4, 1, 99);
    if (i == 5) return frame(2, 5, 5, 1, 4096);
    static const size_t sizes[5] = {0, 7, 99, 1024, 4096};
    return frame(2, i, i, 1, sizes[i % 5]);
}

struct arena_slot { struct lease owner; size_t used; bool retired; uint8_t data[64 + MAX_BODY]; };
struct borrowed { struct lease lease; size_t offset, length; };
static struct arena_slot slots[CELLS];
static bool parked;

static const uint8_t *resolve(struct borrowed v) {
    if (v.lease.slot >= CELLS) return NULL;
    const struct arena_slot *slot = &slots[v.lease.slot];
    if (slot->retired || !valid(v.lease, slot->owner) || v.offset > slot->used || v.length > slot->used - v.offset)
        return NULL;
    return slot->data + v.offset;
}

static void boot(void) {
    static uint64_t runtime[2 * 1024 * 1024];
    cml_heap = runtime; cml_stack = runtime + 1024 * 1024; cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
    booted = true;
    rx_free.head = rx_free.tail = UINT64_MAX - 1;
    for (int i = 0; i < CELLS; ++i) {
        slots[i].owner = (struct lease){1, (uint16_t)i, 7, UINT64_MAX};
        put(&rx_free, (uint16_t)i); put(&storage_free, (uint16_t)i); put(&tx_free, (uint16_t)i);
    }
}

static uint64_t serve(const struct input *req, struct fault f) {
    if (parked || rx_free.head == rx_free.tail || tx_free.head == tx_free.tail) return 0;
    fault = f;
    phase = 0;
    for (unsigned k = 0; k < ENTRY_SECTORS; ++k) cached[k] = false;
    if (!cold(state, req->channel_principal)) { parked = true; return 0; }
    unsigned count = (unsigned)(rx_free.tail - rx_free.head);
    while (count && slots[rx_free.slots[rx_free.head % CELLS]].retired) {
        put(&rx_free, get(&rx_free));
        --count;
    }
    if (!count) return 0;
    uint16_t slotId = get(&rx_free);
    struct arena_slot *slot = &slots[slotId];
    if (req->n > sizeof(slot->data)) { put(&rx_free, slotId); return 0; }
    memcpy(slot->data, req->bytes, req->n);
    slot->used = req->n;
    put(&rx, slotId);
    struct borrowed v = {slots[get(&rx)].owner, 0, req->n};
    const uint8_t *src = resolve(v);
    assert(src);
    memset(scratch, 0, SCRATCH_CTRL);
    put_le64(scratch + 16, req->principal);
    put_le64(scratch + 24, req->nonce);
    put_le64(scratch + 32, req->nullifier);
    put_le64(scratch + 40, req->cost);
    put_le64(scratch + 56, current_base_gen);
    uint64_t result = turnIntake((uintptr_t)src, v.length, (uintptr_t)state, (uintptr_t)scratch);
    if (!result && (phase || f.cut >= EIO_WAL)) parked = true;
    slot->retired = !recycle(&slot->owner);
    put(&rx_free, slotId);
    assert(!resolve(v));
    assert(storage_free.tail - storage_free.head == CELLS && tx_free.tail - tx_free.head == CELLS);
    return result;
}

static uint64_t invoke(const struct input *req, struct fault f) {
    pid_t pid = fork();
    assert(pid >= 0);
    if (pid == 0) { boot(); _exit((int)serve(req, f)); }
    int status;
    assert(waitpid(pid, &status, 0) == pid && WIFEXITED(status));
    return (uint64_t)WEXITSTATUS(status);
}

static void format(void) {
    memset(world, 0, sizeof(*world));
    uint8_t gdig[32];
    cshake256_32(DOM_CHAIN, NULL, 0, gdig);
    encode_superblock(world->disk.ctrl, 0, 0, 0, 0, gdig);
    if (!skip_ticket_check) assert(memcmp(world->disk.ctrl + 72, expected_sb_tags[0], 32) == 0);
}

static void checkpoint_compact(void) {
    uint64_t gen, base, cnt, hw;
    uint8_t cdig[32];
    assert(decode_superblock(world->disk.ctrl, &gen, &base, &cnt, &hw, cdig));
    uint64_t max_nu = hw;
    for (uint64_t i = 0; i < cnt; ++i) {
        uint64_t nu = get_be64(world->disk.wal[i][0] + 24);
        if (nu > max_nu) max_nu = nu;
    }
    sector next;
    encode_superblock(next, gen, gen, 0, max_nu, cdig);
    memcpy(world->disk.ctrl, next, SECTOR);
}

static unsigned scenarios;
static void scenario(struct fault f, const struct shared *base,
                     const struct input *one, const struct input *two) {
    *world = *base;
    const bool installed = f.cut == FUA_NEW || f.cut == EIO_FUA_NEW || f.cut == DISPATCHED || f.cut == SENT;
    uint64_t status = invoke(two, f);
    assert(status == (f.cut >= EIO_WAL ? 0 : CUT_EXIT));
    uint64_t gen, bgen, cnt, hw; uint8_t cdig[32];
    assert(decode_superblock(world->disk.ctrl, &gen, &bgen, &cnt, &hw, cdig));
    assert(gen == (installed ? 2 : 1));
    assert(memcmp(base->disk.wal[0], world->disk.wal[0], ENTRY_SECTORS * SECTOR) == 0);
    assert(world->seen.replies == 1 + (unsigned)(f.cut == SENT));
    assert(world->seen.issues[2] == (unsigned)(f.cut == DISPATCHED || f.cut == SENT));
    assert(invoke(one, (struct fault){0}) == 1);
    assert(invoke(two, (struct fault){0}) == 2);
    assert(invoke(two, (struct fault){0}) == 2);
    assert(world->seen.issues[1] == 1 && world->seen.issues[2] == (unsigned)(f.cut != FUA_NEW && f.cut != EIO_FUA_NEW));
    assert(world->seen.generation == 2 && world->seen.body_len == 1024);
    ++scenarios;
}

static void allocation_canary(int which) {
    pid_t pid = fork();
    assert(pid >= 0);
    if (!pid) {
        struct rlimit no_core = {0, 0};
        assert(setrlimit(RLIMIT_CORE, &no_core) == 0);
        boot();
        void *(*volatile m)(size_t) = malloc;
        void *(*volatile c)(size_t, size_t) = calloc;
        void *(*volatile r)(void *, size_t) = realloc;
        void *ptr = which == 0 ? m(8) : which == 1 ? c(1, 8) : r(NULL, 8);
        _exit(ptr ? 1 : 2);
    }
    int status;
    assert(waitpid(pid, &status, 0) == pid && WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT);
}

static void test_parse_frame_direct(void) {
    pid_t pid = fork();
    assert(pid >= 0);
    if (pid == 0) {
        boot();
        struct input f0 = frame(1, 1, 1, 1, 0);
        struct input f7 = frame(1, 1, 1, 1, 7);
        struct input f99 = frame(1, 1, 1, 1, 99);
        struct input f1024 = frame(1, 1, 1, 1, 1024);
        struct input f4096 = frame(1, 1, 1, 1, 4096);
        assert(parseFrame((uintptr_t)f0.bytes, f0.n) == 59 && f0.n - 59 == 0);
        assert(parseFrame((uintptr_t)f7.bytes, f7.n) == 59 && f7.n - 59 == 7);
        assert(parseFrame((uintptr_t)f99.bytes, f99.n) == 60 && f99.n - 60 == 99);
        assert(parseFrame((uintptr_t)f1024.bytes, f1024.n) == 62 && f1024.n - 62 == 1024);
        assert(parseFrame((uintptr_t)f4096.bytes, f4096.n) == 62 && f4096.n - 62 == 4096);
        /* Leading zeros, overflow, 5-digit length, truncation, trailing bytes all refused */
        const char *lz0 = "POST /turn HTTP/1.1\r\nHost: appliance\r\nContent-Length: 00\r\n\r\n";
        const char *lz7 = "POST /turn HTTP/1.1\r\nHost: appliance\r\nContent-Length: 07\r\n\r\n1234567";
        const char *ovf = "POST /turn HTTP/1.1\r\nHost: appliance\r\nContent-Length: 4097\r\n\r\n";
        assert(parseFrame((uintptr_t)lz0, strlen(lz0)) == 0);
        assert(parseFrame((uintptr_t)lz7, strlen(lz7)) == 0);
        assert(parseFrame((uintptr_t)ovf, strlen(ovf)) == 0);
        assert(parseFrame((uintptr_t)f1024.bytes, f1024.n - 1) == 0);
        assert(parseFrame((uintptr_t)f1024.bytes, f1024.n + 1) == 0);
        _exit(0);
    }
    int status;
    assert(waitpid(pid, &status, 0) == pid && WIFEXITED(status) && WEXITSTATUS(status) == 0);
}

int main(int argc, char **argv) {
    for (int i = 0; i < 3; ++i) allocation_canary(i);
    test_parse_frame_direct();
    /* Command classifier negative checks */
    put_le64(state + 0, 2); phase = 1;
    assert(classify((struct command){WRITE, 1, 0, 0, true}, NULL) == REFUSED);
    assert(classify((struct command){WRITE, 1, 3, 0, false}, NULL) == REFUSED);
    assert(classify((struct command){WRITE, 2, 19, 0, false}, NULL) == REFUSED);
    assert(classify((struct command){WRITE, 1, 19, 1, false}, NULL) == REFUSED);
    assert(classify((struct command){FLUSH, 1, 0, 0, false}, NULL) == REFUSED);
    phase = 0;

    assert(argc == 2);
    FILE *file = fopen(argv[1], "rb");
    assert(file && fread(tickets, 1, sizeof(tickets), file) == sizeof(tickets));
    assert(fread(expected_sb_tags, 1, sizeof(expected_sb_tags), file) == sizeof(expected_sb_tags));
    assert(fgetc(file) == EOF && fclose(file) == 0);

    world = mmap(NULL, sizeof(*world), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    assert(world != MAP_FAILED);
    format();

    struct input one = turn_input(1);   /* 0B payload */
    struct input two = turn_input(2);   /* 1024B payload */
    assert(invoke(&one, (struct fault){0}) == 1);
    assert(world->seen.generation == 1 && world->seen.body_len == 0);
    struct shared *base = malloc(sizeof(*base));
    assert(base);
    *base = *world;

    /* Forged payload body check */
    struct input forged = two;
    forged.bytes[forged.n - 1] ^= 1;
    assert(invoke(&forged, (struct fault){0}) == 0);
    assert(world->seen.authorization_checks == base->seen.authorization_checks + 1);
    assert(memcmp(&base->disk, &world->disk, sizeof(base->disk)) == 0);

    /* Byte-boundary power-cut matrix across meta + both populated 512B data sectors of the 1024B payload
     * plus all remaining sector boundaries, in BOTH forward and reverse DMA completion orders */
    for (int rev = 0; rev < 2; ++rev) {
        for (unsigned bytes = 0; bytes <= 3 * SECTOR; ++bytes)
            scenario((struct fault){DMA, rev, bytes}, base, &one, &two);
        for (unsigned s = 4; s <= ENTRY_SECTORS; ++s)
            scenario((struct fault){DMA, rev, s * SECTOR}, base, &one, &two);
        for (enum cut c = FLUSHED; c <= EIO_FUA_NEW; ++c)
            scenario((struct fault){c, rev, 0}, base, &one, &two);
    }

    struct shared *full = malloc(sizeof(*full));
    assert(full);
    *full = *world;

    /* Adversarial rejection suite */
    struct input conflict = two; conflict.bytes[conflict.n - 1] ^= 1;
    struct input over = frame(1, 88, 3, 1, 7);       /* principal 1 already spent 20 + 44 = 64 = BUDGET_CAP */
    struct input duplicate = frame(2, 44, 2, 1, 15); /* nullifier 2 already spent */
    assert(!invoke(&conflict, (struct fault){0}) && !invoke(&over, (struct fault){0}));
    assert(!invoke(&duplicate, (struct fault){0}));
    two.channel_principal = 2; assert(!invoke(&two, (struct fault){0})); two.channel_principal = 1;
    for (size_t i = 0; i < 62; ++i) {
        struct input bad = two; bad.bytes[i] ^= 128;
        assert(!invoke(&bad, (struct fault){0}));
    }
    --two.n; assert(!invoke(&two, (struct fault){0})); ++two.n;
    assert(memcmp(full, world, sizeof(*full)) == 0);

    /* Execute turns 3..40 (>32 turns!) across 0B, 7B, 99B, 1024B, and 4096B payloads,
     * cross-checking EVERY single cSHAKE256 superblock tag against Lean's tickets.bin! */
    for (unsigned i = 3; i <= NUM_TURNS; ++i) {
        struct input r = turn_input(i);
        assert(invoke(&r, (struct fault){0}) == i);
    }
    /* Verify cold replays across all 5 payload sizes (0B, 1024B, 7B, 99B, 4096B) */
    for (unsigned i = 1; i <= 5; ++i) {
        struct input r = turn_input(i);
        assert(invoke(&r, (struct fault){0}) == i);
    }
    assert(world->seen.issues[1] == 1 && world->seen.issues[2] == 0);
    for (unsigned i = 3; i <= NUM_TURNS; ++i) assert(world->seen.issues[i] == 1);

    /* Warm replay & ambiguous-completion parking test */
    pid_t warm = fork();
    assert(warm >= 0);
    if (warm == 0) {
        format(); boot();
        assert(serve(&one, (struct fault){0}) == 1);
        for (int i = 0; i < 20; ++i) assert(serve(&one, (struct fault){0}) == 1);
        assert(!serve(&two, (struct fault){EIO_FUA_NEW, 0, 0}));
        uint64_t g, b, c, hw; uint8_t d[32];
        assert(decode_superblock(world->disk.ctrl, &g, &b, &c, &hw, d));
        assert(!serve(&two, (struct fault){0}) && parked && g == 2);
        _exit(0);
    }
    int warmStatus;
    assert(waitpid(warm, &warmStatus, 0) == warm && WIFEXITED(warmStatus) && !WEXITSTATUS(warmStatus));
    assert(invoke(&two, (struct fault){0}) == 2 && world->seen.issues[2] == 0);

    /* Corrupt cSHAKE256 superblock refusal check */
    world->disk.ctrl[8] ^= 1;
    assert(!cold(state, 1));
    world->disk.ctrl[8] ^= 1;
    world->disk.ctrl[72] ^= 1;
    assert(!cold(state, 1));
    world->disk.ctrl[72] ^= 1;
    assert(cold(state, 1));

    /* Checkpoint ring-rollover test: bounded 8-slot WAL running 36 turns across 4 checkpoints! */
    skip_ticket_check = true;
    active_max_turns = 8;
    active_budget_cap = 200;
    format();
    static const size_t cp_sizes[4] = {0, 7, 99, 1024};
    for (unsigned i = 1; i <= 36; ++i) {
        struct input r = frame(2, i, i, 1, cp_sizes[i % 4]);
        uint64_t g = invoke(&r, (struct fault){0});
        assert(g == i);
        if (i % 8 == 0) {
            /* Ring full: next fresh turn refused before checkpoint */
            struct input blocked = frame(2, i + 1, i + 1, 1, 7);
            assert(invoke(&blocked, (struct fault){0}) == 0);
            checkpoint_compact();
            /* Spent nullifier from prior epoch MUST still be refused after checkpoint! */
            struct input stale = frame(2, 999, i, 1, 7);
            assert(invoke(&stale, (struct fault){0}) == 0);
        }
    }

    struct lease last = {1, 0, UINT64_MAX, UINT64_MAX};
    assert(!recycle(&last));
    free(base);
    free(full);
    printf("%u fault schedules passed; 40-turn variable-payload (0B/7B/99B/1024B/4096B) + 36-turn checkpoint rollover verified with cSHAKE256 superblock and zero post-boot wrapped allocations\n", scenarios);
    return 0;
}

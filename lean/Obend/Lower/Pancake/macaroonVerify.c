/* x86-64 Linux differential test driver for synthetic records, little-endian words.
 * cake --pancake --main_return=true < macaroonVerify.pnk > macaroonVerify.S
 * cc -O2 -static -Wl,-z,noexecstack macaroonVerify.c macaroonVerify.S -o macaroonVerify
 * macaroonVerify RECORD reads the caveat count, 25 initial workspace words and 48 token
 * words (root key, nonce, caveats, claimed tag, request, padding). Output is the status
 * word, then the token words (including the fixture root key) and the final workspace.
 * macaroonVerify --bench RECORD times warm calls on the record's token.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { TOKEN = 48, STATE = 25 };

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
extern uint64_t macaroonVerify(const uint64_t *token, uint64_t count, uint64_t *state);
void cml_clear(void) {}
void cml_err(int code) { fprintf(stderr, "CakeML runtime error %d\n", code); exit(1); }

static const uint64_t canary = UINT64_C(0x319765ca6df92c84);
static struct { uint64_t before, token[TOKEN], between, state[STATE], after; } frame;

static int intact(void) {
    return frame.before == canary && frame.between == canary && frame.after == canary;
}

static uint64_t nanos(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &ts)) { perror("clock_gettime"); exit(1); }
    return (uint64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}

static int read_record(const char *path, uint64_t *count) {
    FILE *input = fopen(path, "rb");
    if (!input) { perror(path); return 0; }
    int ok = fread(count, 8, 1, input) == 1 && fread(frame.state, 8, STATE, input) == STATE &&
             fread(frame.token, 8, TOKEN, input) == TOKEN && fgetc(input) == EOF && !ferror(input);
    fclose(input);
    if (!ok) fprintf(stderr, "expected exactly %d bytes\n", 8 * (1 + STATE + TOKEN));
    return ok;
}

static int benchmark(uint64_t count) {
    const unsigned calls = 20000;
    uint64_t expect = macaroonVerify(frame.token, count, frame.state);
    for (unsigned batch = 0; batch <= 5; ++batch) {
        uint64_t differ = 0, start = nanos();
        for (unsigned i = 0; i < calls; ++i)
            differ += macaroonVerify(frame.token, count, frame.state) != expect;
        uint64_t elapsed = nanos() - start;
        if (differ || !intact()) return 1;
        if (batch)
            printf("%llu caveats, status %llu: %.3f us/call\n", (unsigned long long)count,
                   (unsigned long long)expect, (double)elapsed / 1e3 / calls);
    }
    return 0;
}

int main(int argc, char **argv) {
    int bench = argc == 3 && !strcmp(argv[1], "--bench");
    if (argc != 2 && !bench) { fprintf(stderr, "usage: %s RECORD | --bench RECORD\n", argv[0]); return 2; }
    static uint64_t runtime[2 * 1024 * 1024];
    cml_heap = runtime;
    cml_stack = runtime + 1024 * 1024;
    cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
    frame.before = frame.between = frame.after = canary;
    uint64_t count;
    if (!read_record(argv[bench ? 2 : 1], &count)) return 1;
    if (bench) return benchmark(count);
    uint64_t status = macaroonVerify(frame.token, count, frame.state);
    if (!intact()) { fprintf(stderr, "frame overwritten\n"); return 1; }
    return fwrite(&status, 8, 1, stdout) != 1 || fwrite(frame.token, 8, TOKEN, stdout) != TOKEN ||
           fwrite(frame.state, 8, STATE, stdout) != STATE || fflush(stdout) != 0;
}

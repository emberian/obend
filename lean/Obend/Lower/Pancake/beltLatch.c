/* Standalone x86-64 Linux driver, little-endian words.
 * cake --pancake --main_return=true < beltLatch.pnk > beltLatch.S
 * cc -O2 -static -Wl,-z,noexecstack beltLatch.c beltLatch.S -o beltLatch
 * beltLatch RECORD reads 14 state words then 19 candidate words. Output is
 * one status word followed by both buffers in the same order.
 * beltLatch --bench times warm serialized calls on a single latch.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
extern uint64_t stepBeltLatch(uint64_t *current, const uint64_t *candidate);
void cml_clear(void) {}
void cml_err(int code) { fprintf(stderr, "CakeML runtime error %d\n", code); exit(1); }

static uint64_t nanos(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &ts)) { perror("clock_gettime"); exit(1); }
    return (uint64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}

static int benchmark(void) {
    const unsigned calls = 1000000;
    uint64_t state[14] = {1}, candidate[19] = {0};
    for (unsigned ack = 1; ; --ack) {
        candidate[18] = ack;
        for (unsigned batch = 0; batch <= 5; ++batch) {
            uint64_t codes = 0, epoch = state[5], start = nanos();
            for (unsigned i = 0; i < calls; ++i) {
                candidate[4] = epoch;
                candidate[5] = epoch + 1;
                codes += stepBeltLatch(state, candidate);
                epoch += ack;
            }
            uint64_t elapsed = nanos() - start;
            if (state[5] != epoch || codes != (ack ? 0 : (uint64_t)calls * 6)) return 1;
            if (batch)
                printf("%s %.2f ns/call\n", ack ? "accepted" : "missingAck", (double)elapsed / calls);
        }
        if (!ack) break;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: %s RECORD | --bench\n", argv[0]); return 2; }
    static uint64_t runtime[2 * 1024 * 1024];
    cml_heap = runtime;
    cml_stack = runtime + 1024 * 1024;
    cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
    if (!strcmp(argv[1], "--bench")) return benchmark();

    struct { uint64_t before, state[14], between, candidate[19], after; } frame;
    frame.before = frame.between = frame.after = UINT64_C(0x319765ca6df92c84);
    FILE *input = fopen(argv[1], "rb");
    if (!input) { perror(argv[1]); return 1; }
    int ok = fread(frame.state, 8, 14, input) == 14 && fread(frame.candidate, 8, 19, input) == 19
          && fgetc(input) == EOF && !ferror(input);
    fclose(input);
    if (!ok) { fprintf(stderr, "expected exactly 264 bytes\n"); return 1; }
    uint64_t status = stepBeltLatch(frame.state, frame.candidate);
    if (frame.before != UINT64_C(0x319765ca6df92c84) || frame.between != frame.before ||
        frame.after != frame.before) { fprintf(stderr, "frame overwritten\n"); return 1; }
    return fwrite(&status, 8, 1, stdout) != 1 || fwrite(frame.state, 8, 14, stdout) != 14 ||
           fwrite(frame.candidate, 8, 19, stdout) != 19 || fflush(stdout) != 0;
}

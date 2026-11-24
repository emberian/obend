/* Linux x86-64 driver for the two exported Pancake functions.
 * cake --pancake --main_return=true < kmac256.pnk > kmac256.S
 * cc -O2 -static -Wl,-z,noexecstack kmac256.c kmac256.S -o kmac256
 * kmac256 KEY_FILE CUSTOMIZATION_FILE MESSAGE_FILE > tag.bin
 * kmac256 --resume STATE_FILE TRAILER MESSAGE_FILE > digest.bin
 * STATE_FILE holds 25 little-endian words. TRAILER is 1 for KMAC and 0 for cSHAKE256.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
extern uintptr_t kmac256(uint64_t state[25], void *frame, uintptr_t slices[6]);
extern uintptr_t kmacResume(uint64_t state[25], void *frame, uintptr_t slices[6],
                            uintptr_t trailer);

void cml_clear(void) {}
void cml_err(int code) { fprintf(stderr, "CakeML runtime error %d\n", code); exit(1); }

static int read_slice(const char *path, uintptr_t *slice, size_t *capacity) {
    FILE *f = fopen(path, "rb");
    struct stat st;
    if (!f) { perror(path); return 0; }
    if (fstat(fileno(f), &st) || st.st_size < 0 || !S_ISREG(st.st_mode) ||
        (uintmax_t)st.st_size > SIZE_MAX - *capacity) {
        fprintf(stderr, "Invalid input size or file type for %s\n", path);
        fclose(f);
        return 0;
    }
    size_t n = (size_t)st.st_size;
    void *p = malloc(n ? n : 1);
    int ok = p && fread(p, 1, n, f) == n && fgetc(f) == EOF && !ferror(f);
    fclose(f);
    if (!ok) {
        if (p) explicit_bzero(p, n);
        free(p);
        fprintf(stderr, "Cannot read %s\n", path);
        return 0;
    }
    slice[0] = (uintptr_t)p;
    slice[1] = n;
    *capacity += n;
    return 1;
}

static void start_runtime(void) {
    static uint64_t runtime[2 * 1024 * 1024];
    cml_heap = runtime;
    cml_stack = runtime + 1024 * 1024;
    cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
}

/* Each kernel leaves its frame and all 25 lanes in caller-owned memory. */
static int run(char **paths, int resumed) {
    uintptr_t slices[6] = {0};
    uint64_t state[25] = {0};
    size_t capacity = resumed ? 294 : 440;
    void *frame = NULL;
    int rc = 1;
    if (resumed) {
        if (strcmp(paths[1], "0") && strcmp(paths[1], "1")) {
            fprintf(stderr, "TRAILER must be 0 or 1\n");
            return 2;
        }
        FILE *f = fopen(paths[0], "rb");
        if (!f) { perror(paths[0]); return 1; }
        struct stat st;
        int ok = !fstat(fileno(f), &st) && S_ISREG(st.st_mode) && st.st_size == sizeof state &&
                 fread(state, 1, sizeof state, f) == sizeof state && fgetc(f) == EOF && !ferror(f);
        fclose(f);
        if (!ok) {
            fprintf(stderr, "%s must hold exactly 200 bytes\n", paths[0]);
            goto cleanup;
        }
    }
    for (int i = resumed ? 2 : 0; i < 3; ++i)
        if (!read_slice(paths[i], &slices[2*i], &capacity)) goto cleanup;
    frame = malloc(capacity);
    if (!frame) goto cleanup;
    start_runtime();
    uintptr_t status = resumed ? kmacResume(state, frame, slices, paths[1][0] == '1')
                               : kmac256(state, frame, slices);
    if (!status && fwrite(state, 1, 32, stdout) == 32 && fflush(stdout) == 0) rc = 0;

cleanup:
    explicit_bzero(state, sizeof state);
    if (frame) {
        explicit_bzero(frame, capacity);
        free(frame);
    }
    for (int i = 0; i < 6; i += 2) {
        void *p = (void *)slices[i];
        if (p) {
            explicit_bzero(p, slices[i+1]);
            free(p);
        }
    }
    return rc;
}

int main(int argc, char **argv) {
    if (argc == 5 && !strcmp(argv[1], "--resume")) return run(argv + 2, 1);
    if (argc == 4) return run(argv + 1, 0);
    fprintf(stderr, "Usage: %s KEY_FILE CUSTOMIZATION_FILE MESSAGE_FILE\n"
                    "       %s --resume STATE_FILE TRAILER MESSAGE_FILE\n", argv[0], argv[0]);
    return 2;
}

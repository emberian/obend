/* Linux x86-64 driver for the exported Pancake function.
 * cake --pancake --main_return=true < cshake256.pnk > cshake256.S
 * cc -O2 -static -Wl,-z,noexecstack cshake256.c cshake256.S -o cshake256
 * cshake256 NAME_FILE CUSTOMIZATION_FILE MESSAGE_FILE > digest.bin
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
extern uintptr_t cshake256(uint64_t state[25], void *frame, uintptr_t slices[6]);

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
    if (!ok) { free(p); fprintf(stderr, "Cannot read %s\n", path); return 0; }
    slice[0] = (uintptr_t)p;
    slice[1] = n;
    *capacity += n;
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "Usage: %s NAME_FILE CUSTOMIZATION_FILE MESSAGE_FILE\n", argv[0]);
        return 2;
    }
    uintptr_t slices[6];
    size_t capacity = 294;
    for (int i = 0; i < 3; ++i)
        if (!read_slice(argv[i + 1], &slices[2*i], &capacity)) return 1;
    uint64_t state[25];
    void *frame = malloc(capacity);
    static uint64_t runtime[2 * 1024 * 1024];
    if (!frame) return 1;
    cml_heap = runtime;
    cml_stack = runtime + 1024 * 1024;
    cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
    if (cshake256(state, frame, slices)) return 1;
    return fwrite(state, 1, 32, stdout) != 32 || fflush(stdout) != 0;
}

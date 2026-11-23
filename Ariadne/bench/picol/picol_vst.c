/* Ariadne (owner, 2026-11-22): the translation unit verified with VST.
 * picol.c, musl's definitions of the libc globals it reads, and musl's
 * sources of the libc functions verified from source
 * (../../libc/proofs/), so one semax_prog covers them.  The FILE structs
 * stay with libc (their initializers reach musl's stdio internals).
 * Needs ../../libc/fetch_musl.py and musl_clight.py (headers, shim);
 * preprocess with CompCert's defines and
 *   -I<musl>/obj/shim -I<musl>/arch/x86_64 -I<musl>/arch/generic
 *   -I<musl>/obj/include -I<musl>/include
 * (public headers only: musl's internal stdio.h redefines stdout).
 *
 * CompCert's semantics start only `int main(void)` (Clight.v,
 * initial_state), so picol's main(argc, argv) is renamed picol_main and
 * proved for every argv (C11 5.1.2.2.1); the main below calls it in
 * both modes so that VST's semax_prog also holds (owner, 2026-11-22). */
#define main picol_main
#include "picol.c"
#undef main
/* musl 1.2.6, src/stdio/std{in,out,err}.c: the streams' pointers. */
extern FILE __stdin_FILE, __stdout_FILE, __stderr_FILE;
FILE *const stdin = &__stdin_FILE;
FILE *const stdout = &__stdout_FILE;
FILE *const stderr = &__stderr_FILE;
/* musl 1.2.6 sources (strchrnul.c before strchr.c, which calls it). */
#include "../../libc/musl-1.2.6/src/string/strlen.c"
#include "../../libc/musl-1.2.6/src/string/strchrnul.c"
#include "../../libc/musl-1.2.6/src/string/strchr.c"
#include "../../libc/musl-1.2.6/src/string/strcmp.c"
#include "../../libc/musl-1.2.6/src/string/memcpy.c"
#include "../../libc/musl-1.2.6/src/ctype/isupper.c"

/* REPL mode, then script mode (argv strings writable, as C11 says). */
int main(void) {
    char a0[] = "picol", b0[] = "picol", b1[] = "script.tcl";
    char *repl[2], *file[3];
    repl[0] = a0; repl[1] = 0;
    file[0] = b0; file[1] = b1; file[2] = 0;
    picol_main(1, repl);
    return picol_main(2, file);
}

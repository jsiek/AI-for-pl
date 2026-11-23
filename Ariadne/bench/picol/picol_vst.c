/* Ariadne (owner, 2026-11-22): the translation unit verified with VST.
 * picol.c, musl's definitions of the libc globals it reads, and musl's
 * sources of the libc functions verified from source
 * (../../libc/proofs/), so one semax_prog covers them.  The FILE structs
 * stay with libc (their initializers reach musl's stdio internals).
 * Needs ../../libc/fetch_musl.py and musl_clight.py (headers, shim);
 * preprocess with CompCert's defines and
 *   -I<musl>/obj/shim -I<musl>/arch/x86_64 -I<musl>/arch/generic
 *   -I<musl>/obj/include -I<musl>/include
 * (public headers only: musl's internal stdio.h redefines stdout). */
#include "picol.c"
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

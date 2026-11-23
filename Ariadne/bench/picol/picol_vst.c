/* Ariadne (owner, 2026-11-22): the translation unit verified with VST.
 * picol.c plus musl's definitions of the libc globals it reads, so that
 * VST sees their values as the linked program does.  The FILE structs
 * stay with libc (their initializers reach musl's stdio internals). */
#include "picol.c"
/* musl 1.2.6, src/stdio/std{in,out,err}.c: the streams' pointers. */
extern FILE __stdin_FILE, __stdout_FILE, __stderr_FILE;
FILE *const stdin = &__stdin_FILE;
FILE *const stdout = &__stdout_FILE;
FILE *const stderr = &__stderr_FILE;

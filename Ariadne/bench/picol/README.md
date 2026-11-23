# picol (plan §13, step 1; M8)

antirez's Tcl interpreter, `upstream/` = github.com/antirez/picol at
commit `5f902e9b211fff21fb6e6abfd116df665e4091d5` (2026-02-18), BSD-2
(licence in the header of `picol.c`).  Chosen from `../CANDIDATES.md`.

`picol.c` is upstream with the Ariadne fixes below; `picol_test.c` is
upstream's unit tests (it `#include`s `picol.c`, so it tests the fixed
file).  `./run_asan.sh` builds both under gcc ASan/UBSan/LSan and runs
the 67 unit tests, upstream's `fib.tcl` and `mandelbrot.tcl`, the
regression script in `tests/` (fix 1) and a REPL session on stdin
(fix 2).

## Fixes to the C (owner's decisions; `HUMAN_STEPS.md`)

1.  **Use after free when a proc redefines itself** (2026-11-21).
    `tests/proc_redefine_self.tcl`:
    ```tcl
    proc f {} { proc f {} {}; puts after }
    f
    ```
    Upstream: ASan reports a heap-use-after-free read in
    `picolGetToken` (`picol.c:278`): `picolCommandCallProc` evaluates
    `cmd->body` directly, and the inner `proc f` frees it in
    `picolRegisterCommand` (`picol.c:369`) while it is being parsed.
    Fix: `picolCommandCallProc` evaluates a private copy of the body
    (one `xstrdup` and `free` per call).  Fixed: prints `after`,
    sanitizers clean.
2.  **The REPL leaks the interpreter at end of input** (2026-11-21).
    With no file argument, `main` did `return 0` when `fgets` returned
    NULL, skipping `picolFreeInterp`.  Upstream fed
    `set a 1` / `proc f {x} {return $x}` on stdin: LSan reports 541
    bytes leaked in 28 allocations.  Fix: leave the loop (`break`), so
    `main` reaches `picolFreeInterp`.  Fixed: LSan clean
    (`run_asan.sh`, "REPL frees the interpreter").
3.  **Fixed-argument replacements for the variadic calls** (2026-11-22).
    VST cannot verify picol's 6 `snprintf`, 4 `printf` and 1 `fprintf`
    calls.  For example
    ```c
    snprintf(errbuf,sizeof(errbuf),"No such variable '%s'",t);    /* before */
    fmt_str3(errbuf,sizeof(errbuf),"No such variable '",t,"'");   /* after  */
    ```
    `fmt_append`, `fmt_str3` and `fmt_int` are plain C in `picol.c` and
    are verified with it; `printf` of strings becomes `fputs`.  Only
    `fmt_double` (`snprintf(buf,n,"%.12g",v)`, in `trusted.c`) is
    trusted.  The output is unchanged (`run_asan.sh`, "same output as
    upstream", on the examples and on `tests/messages.tcl`, which
    reaches every replaced message), except the out-of-memory message
    in `xrealloc`, now `Out of memory` without the pointer and size.

## The verified unit: `picol_vst.c`

VST verifies `picol_vst.c`: `picol.c` plus musl's definitions of the
globals it reads (`FILE *const stdout = &__stdout_FILE;`, and the same
for `stdin`, `stderr`).  In `picol.c` alone these are externs without
initializers, so VST gives `main` no permission to read them; with
musl's definitions, VST's own `main_pre` gives read permission on each
(`data_at Ers (tptr FILE) (gv ___stdout_FILE) (gv _stdout)`).  The
`FILE` structs stay with libc.  gcc builds (`run_asan.sh`) use
`picol.c` and the host libc.

## Trusted functions

`trusted.c` holds the functions picol calls that are not verified; their
specs, and those of the libc functions with trusted specs
(`../../libc/README.md`), are approved by the owner one at a time and
recorded in `TRUSTED_SPECS.md`.

## libc

`../../libc/README.md`: which of picol's libc functions are verified
from musl source and which get trusted specs.

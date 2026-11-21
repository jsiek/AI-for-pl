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

## libc

`../../libc/README.md`: which of picol's libc functions are verified
from musl source and which get trusted specs.

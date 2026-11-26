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
4.  **No reachable `goto`** (2026-11-23).  VST's only rule for `goto`
    (`semax_goto`) has precondition `FF`, so a function with a reachable
    `goto` has no proof.  `picolEval`'s four `goto err` jumped to the
    code right after its `while(1)` loop; they are now `break`.
    `picolCommandCallProc`'s error exits are now calls to a new
    function:
    ```c
    if (++arity > argc-1) goto arityerr;                     /* before */
    if (++arity > argc-1) {                                  /* after  */
        fmt_str3(errbuf,sizeof(errbuf),"Proc '",argv[0],"' called with wrong arg num");
        return picolCallProcFail(i,errbuf,tofree);
    }
    ```
    The output is unchanged (`run_asan.sh`; `tests/messages.tcl` reaches
    each of these exits).
5.  **`default: break;` in `picolParseString`'s `switch`** (2026-11-24).
    VST's `switch` rule gives falling off the end of a `switch` the
    postcondition `FF`; with no `default`, an ordinary character such
    as `a` does that.  Same behaviour.
6.  **Bound on a command's argument size** (2026-11-24).  Upstream
    overflows `int` lengths (undefined behaviour) on long arguments:
    ```tcl
    set a xxxxxxxx
    set a $a$a      ;# 28 times: 2^31 bytes; oldlen+tlen+1 overflows
    ```
    `picolEval` now counts the current command's argument size (each
    length + 1) and fails with `Command too long` before it would
    exceed `PICOL_MAX_ARGS_SIZE` (`INT_MAX - 10`).  `run_asan.sh` checks
    it with the bound lowered to 40 bytes (`tests/args_limit.tcl`).
7.  **`default: break;` in `picolExpr`'s operator `switch`**
    (2026-11-25).  Unreached (`op` is always one of the cases), but
    without it the proof must carry that fact to the `switch`.  Same
    behaviour.

## Proof runs (`run_picol.py`)

| Run | Budget | Spent | Time | Result |
|---|---|---|---|---|
| 2026-11-22 | $50 | $36.95 | 5.6 h | 26 of 45 functions proved and `prog_correct` (`Qed`), 19 bodies `Admitted`; two of those had reachable `goto`s (fix 4). |
| 2026-11-23, from the first | $50 | $35.81 | 3.3 h | 40 of 46 functions proved and `prog_correct` (`Qed`); open: `picolEval` (no bound on argument sizes), `picolParseString` (`switch` without `default`), `picolExpr`, `picolCommandExpr`, `picolCommandCallProc`, `picol_main`.  Leak lint passes; `Print Assumptions` within the allow-list except the 6 open bodies. |
| 2026-11-24, from the second (after fixes 5, 6) | $50 | $38.37 | 2.5 h | 44 of 46 proved and `prog_correct` (`Qed`); open: `picolEval` (draft started), `picolExpr` (budget).  Leak lint passes. |
| 2026-11-25, from the third (after fix 7), with the spend meter | $50 | $35.55 | 4.9 h, one session | **All 46 functions and `prog_correct` proved (`Qed`), verdict PROVED.**  `Print Assumptions` within the allow-list; leak lint passes.  Spec change by the agent, approved by the owner (2026-11-26): `picolEval`'s script length bound `Zlength s <= Int.max_signed` became `<` (with `INT_MAX` bytes, `tlen+1` overflows), and likewise the procedure-body bound in `cmd_ok` and `proc_extra`.  The meter showed $28.90 at the end, 19% below the exact cost. |

The fourth run's proof is kept in `proofs/` (`proof_files.txt` gives
the build order); re-check it with

    python3 run_picol.py --check proofs

Total cost of picol: $146.68 for the four runs, plus $4.88 for the musl
`libc` runs (`../../libc/README.md`).  Drafts of issues for upstream
(the bugs behind fixes 1, 2 and 6): `UPSTREAM_ISSUES.md`.

## The verified unit: `picol_vst.c`

VST verifies `picol_vst.c`: `picol.c` plus musl's definitions of the
globals it reads (`FILE *const stdout = &__stdout_FILE;`, and the same
for `stdin`, `stderr`).  In `picol.c` alone these are externs without
initializers, so VST gives `main` no permission to read them; with
musl's definitions, VST's own `main_pre` gives read permission on each
(`data_at Ers (tptr FILE) (gv ___stdout_FILE) (gv _stdout)`).  The
`FILE` structs stay with libc.  gcc builds (`run_asan.sh`) use
`picol.c` and the host libc.

It also includes musl's sources of `strlen`, `__strchrnul`, `strchr`,
`strcmp`, `memcpy` and `isupper`, so one `semax_prog` covers them; the
only externals left are the trusted functions (`TRUSTED_SPECS.md`).
The proofs in `../../libc/proofs/` replay unchanged against this
program (2026-11-22: all five, `Print Assumptions` within the
allow-list), so picol's proof reuses them.

## Trusted functions

`trusted.c` holds the functions picol calls that are not verified; their
specs, and those of the libc functions with trusted specs
(`../../libc/README.md`), are approved by the owner one at a time and
recorded in `TRUSTED_SPECS.md`.

## libc

`../../libc/README.md`: which of picol's libc functions are verified
from musl source and which get trusted specs.

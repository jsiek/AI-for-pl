# picol: human steps (G9)

Each question put to the owner, and why a machine could not decide it.

| Date | Question | Why a human | Decision |
|---|---|---|---|
| 2026-11-21 | Picol is the next target (from `../CANDIDATES.md`). | Choice of research target. | Yes. |
| 2026-11-21 | libc: verify from source or trust a spec? | Policy: what enters the trust base. | Verify from musl if clightgen accepts and one $10 run proves it; otherwise a trusted spec the owner approves (plan §4).  Applies to every later program. |
| 2026-11-21 | Fix for the use after free when a proc redefines itself (`README.md`, fix 1): evaluate a copy of the body per call, or reference-count bodies? | A change to the program's C (G3). | One copy per call. |
| 2026-11-21 | Fix for the REPL leaking the interpreter at end of input (`README.md`, fix 2): free it before returning? | A change to the program's C (G3). | Yes (`break` out of the loop to the existing `picolFreeInterp`). |
| 2026-11-22 | Variadic calls (`README.md`, fix 3): replace with fixed-argument functions, or port VST's experimental `printf` support? | A change to the program's C (G3) and to the trust base. | Fixed-argument functions; only `fmt_double` is trusted.  Applies to every later program (`../../libc/README.md`). |
| 2026-11-22 | Trusted spec of `realloc` (`TRUSTED_SPECS.md`). | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | Trusted spec of `fmt_double` (`TRUSTED_SPECS.md`). | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | Trusted spec of `strtod` (`TRUSTED_SPECS.md`), including the unmentioned `errno` write. | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | Trusted predicate `FILE_handle` with facts (a), (b), and specs of `fopen`, `fclose` (`TRUSTED_SPECS.md`). | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | VST gives `main` no read permission on the extern globals `stdin`/`stdout`/`stderr` (no initializer in `picol.c` alone): trusted wrappers, a trusted extra precondition for `main`, or verify picol with musl's one-line definitions of the three globals (`picol_vst.c`)? | Changes the verified unit and the trust base. | `picol_vst.c` (no trust for the loads; `picol.c` and `main`'s spec unchanged).  Applies to every later program's libc globals. |
| 2026-11-22 | Trusted definition `std_stream` and spec of `fputs` (`TRUSTED_SPECS.md`). | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | Trusted spec of `fflush` (`TRUSTED_SPECS.md`). | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | Trusted spec of `fgets` (`TRUSTED_SPECS.md`). | Enters the trust base. | Owner asked for the zero-byte case to be checked against references (C11, POSIX, musl source, a test run); then approved as drafted. |
| 2026-11-22 | Trusted spec of `fread` (`TRUSTED_SPECS.md`). | Enters the trust base. | Approved as drafted. |
| 2026-11-22 | Trusted specs of `perror` and `exit` (`TRUSTED_SPECS.md`); does leak freedom cover memory held at `exit`? | Enters the trust base; defines the property (plan §2.1). | Specs approved as drafted; leak freedom covers `main`'s return only, `exit` may hold memory (picol's C unchanged). |
| 2026-11-22 | Linking the verified musl functions: include their sources in `picol_vst.c`, or keep them as externals with their proved specs? | Changes the verified unit. | Include the sources (one `semax_prog` covers them). |
| 2026-11-22 | CompCert starts only `main(void)`: prove picol's `main(argc,argv)` for every `argv` as `picol_main`, plus a `main(void)` that calls it, or fix one `argv`? | Changes the verified unit and the theorem. | `picol_main` for every `argv` plus the `main(void)` wrapper (`picol_vst.c`). |
| 2026-11-22 | First prover run: budget. | Paid run. | $50 (spent $36.95; 26 of 45 functions and `prog_correct` proved, `README.md`). |
| 2026-11-23 | Fix for the reachable `goto`s VST cannot verify (`README.md`, fix 4): `break` / a helper function? | A change to the program's C (G3). | Yes. |
| 2026-11-23 | The first run's own spec choices: `picolEval`'s input length fits in an `int` (and a bound on the command arguments' total size); each command's function pointer is one of the known command functions. | Assumptions the proof rests on. | Approved. |
| 2026-11-23 | Follow-up run from the first run's proofs: budget. | Paid run. | $50. |
| 2026-11-24 | Fixes 5 (`default: break;` in `picolParseString`) and 6 (a bound on a command's argument size in `picolEval`) (`README.md`). | A change to the program's C (G3). | Yes. |
| 2026-11-24 | Third run from the second run's proofs, only the 6 open functions: budget. | Paid run. | $50 cap. |
| 2026-11-25 | Fix 7 (`default: break;` in `picolExpr`'s operator `switch`, unreached) (`README.md`). | A change to the program's C (G3). | Yes. |
| 2026-11-25 | The runs' agents stopped at 72–77% of the cap, unable to see their spend: show it to them? | Changes how paid runs spend. | Yes: a spend meter printed after each tool call (`run_picol.py`); if the agent stops early with the proof unfinished, start it again ("prod it to keep going"). |
| 2026-11-25 | Fourth run (`picolEval`, `picolExpr`): budget. | Paid run. | $50 (spent $35.55; all 46 bodies and `prog_correct` proved, `README.md`). |
| 2026-11-26 | The fourth run's spec change: `picolEval`'s script length `Zlength s <= Int.max_signed` becomes `<` (with `INT_MAX` bytes, `tlen+1` overflows), and likewise the procedure-body bound in `cmd_ok` and `proc_extra`. | Assumptions the proof rests on. | Approved. |
| 2026-11-23 | VST's allocator axiom `malloc_token_valid_pointer` (`floyd/library.v:72`: a `malloc_token` for a zero-size object gives `valid_pointer p`), used by the first run's proofs: allow it in `Print Assumptions`? | Enters the trust base. | Yes (`run_picol.py`, `TRUSTED_AXIOMS`). |

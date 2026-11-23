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

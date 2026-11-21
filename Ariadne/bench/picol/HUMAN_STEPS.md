# picol: human steps (G9)

Each question put to the owner, and why a machine could not decide it.

| Date | Question | Why a human | Decision |
|---|---|---|---|
| 2026-11-21 | Picol is the next target (from `../CANDIDATES.md`). | Choice of research target. | Yes. |
| 2026-11-21 | libc: verify from source or trust a spec? | Policy: what enters the trust base. | Verify from musl if clightgen accepts and one $10 run proves it; otherwise a trusted spec the owner approves (plan §4).  Applies to every later program. |
| 2026-11-21 | Fix for the use after free when a proc redefines itself (`README.md`, fix 1): evaluate a copy of the body per call, or reference-count bodies? | A change to the program's C (G3). | One copy per call. |
| 2026-11-21 | Fix for the REPL leaking the interpreter at end of input (`README.md`, fix 2): free it before returning? | A change to the program's C (G3). | Yes (`break` out of the loop to the existing `picolFreeInterp`). |

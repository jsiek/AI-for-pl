# Ariadne: evaluation after sglib and picol (2026-11-26)

An evaluation of Ariadne as a tool and a process, after the sglib
doubly linked list (M6, closed at stage 1) and picol (M8, proved
2026-11-25), with proposals for making it reusable and for what comes
next.  The costs are for the prover agents' API usage (`summary.json`
of each run under `runs/`).  They exclude the orchestrating Claude
Code sessions, which were not metered.

## 1. Results so far

| Target | C lines | What was proved | Agent runs | Cost | Human steps |
|---|---|---|---|---|---|
| sglib DL list, library | `sglib.h` macros, 6 functions | 6 `semax_body` against the owner's frozen public spec | 2 (pilot 1 out of memory, no proof; pilot 2 proved all) | $6.04 | spec freeze (SPEC, REVIEW R1–R10, FIT_CHECK), survey Q1–Q8, 2 spec fixes |
| sglib, 13 clients | 13 small programs | `semax_prog` + leak freedom for each | 14 (client 9 failed once: signed `counter++` overflows) | $67.64 | Callbacks rule, the client 9 fix |
| musl libc pieces | 5 functions | `strlen`, `strcmp`, `strchr`, `memcpy` (runs), `isupper` (by hand) | 4 | $4.88 | the libc policy (verify from source, else trusted spec) |
| picol | 809 upstream, 888 after fixes | `semax_prog`: all 46 function bodies, memory safe and leak free through `main`'s return | 4 (5.6 h, 3.3 h, 2.5 h, 4.9 h) | $146.68 | 28 rows in `bench/picol/HUMAN_STEPS.md` |

**The whole picol effort cost $151.56:** $146.68 for the four prover
runs and $4.88 for the libc runs.
- That is about $0.18 per upstream line.
- The proof is 7,051 lines of Coq in 28 files, about 8 lines of proof
  per line of C.
- The agents worked about 16 hours in total.

Each picol run started from the previous run's proofs:

| Run | Proved (of 46) | Cost | What stopped it |
|---|---|---|---|
| 1 | 26 | $36.95 | stopped by itself at 74% of the cap; 2 functions unprovable (reachable `goto`) |
| 2 | 40 | $35.81 | stopped by itself; `picolEval` blocked by an unbounded size (fix 6), `picolParseString` by a `switch` without `default` (fix 5) |
| 3 | 44 | $38.37 | stopped by itself at 77% of the cap, `picolEval` half drafted |
| 4 | 46 | $35.55 | finished, with a spend meter shown to the agent |

**Bugs found in picol:** a use after free, a REPL leak and `int`
overflows (`bench/picol/UPSTREAM_ISSUES.md`).
- The sanitizer harness (`run_asan.sh`) found the first two before any
  proof run, at no model cost.
- The proofs found the overflows.

## 2. What worked

- **Two approaches work together: the agent picks the internal specs,
  and checks hold the line.**
  - The agent chose every internal funspec of picol: 46 functions,
    including the interpreter state's invariant and the commands'
    shared funspec.
  - What makes a run's claim trustworthy is the check: pristine
    recompile, keyword lint, `Print Assumptions` against an allow-list,
    the leak lint, and the frozen statement of `prog_correct`.
  - The agent's reports were accurate in all four runs. For example,
    run 3's "44 of 46, `picolEval` and `picolExpr` open" matched
    `check.json` exactly.
- **Continuing from the last run's proofs.** `--from RUN_DIR` turned
  four bounded runs into one proof, with human fixes in between.
  - No run redid finished work: the count of proved functions went
    26, 40, 44, 46.
  - Owner decisions (fixes 4–7) went in between runs, where they cost
    nothing.
- **Proofs find real defects in the C, and say exactly where.** For
  example, run 4 tightened `Zlength s <= Int.max_signed` to `<`,
  because a single token of `INT_MAX` bytes makes `tlen+1` overflow.
  - No test would find this one: it needs a 2 GB script.
  - sglib had the same pattern: client 9's signed counter, and
    `DLLIST_COMPARATOR`'s `e1->i - e2->i`.
- **The sanitizer harness before the proof.** `run_asan.sh`
  (ASan/UBSan/LSan on upstream's tests, plus a regression test per fix)
  found fix 1 (use after free) and fix 2 (leak) cheaply. It then
  confirmed that fixes 3–7 kept picol's output unchanged.
- **Decisions made once and reused.** The libc policy, the `_vst.c`
  unit for libc globals, the `main(void)` wrapper and the Callbacks
  rule are each written "applies to every later program". clox should
  not re-ask them.
- **The leak-freedom argument.** VST is not affine, so a proof can drop
  memory only through `TT` in a postcondition. A lint on postconditions
  then suffices for leak freedom.
  - The lint was rewritten in Ltac2 after Codex found two ways to
    spell `TT` past the regex.
  - It checked all 58 picol specs.

## 3. What did not work, or cost more than it should

- **Agents stopped early because they could not see their spend.**
  Runs 1–3 ended voluntarily at 72–77% of the $50 cap, with work left.
  That is about $40 of unused budget, and most of it was redone as
  re-reading at the next run's start.
  - Run 4 showed the agent a meter after each tool call, and it
    finished.
  - The meter read $28.90 when the true cost was $35.55, 19% low. The
    prices are right, so some responses' usage never reached the
    stream. The raw stream was not saved, so the gap is not yet
    explained.
- **C constructs that VST cannot verify were found by the paid agent.**
  - Reachable `goto` (run 1: two functions marked unprovable).
  - A `switch` that can fall off its end (run 2).
  - Variadic calls, and extern globals without an initializer (found
    before the runs, by reading).
  - Each is a syntactic property of the C, and a script over
    clightgen's output would find all of them for free.
- **Some human steps were not needed.** The owner approved the first
  run's internal spec choices: the `int` bounds and the command
  function pointers.
  - Under G1, though, only `main`'s spec is claimed. An internal
    funspec is a lemma checked by Rocq, and if it is too strong then
    `prog_correct` does not close.
  - So those approvals add no assurance. 2 of picol's 28 human steps
    are of this kind (the 2026-11-23 spec choices and the 2026-11-26
    precondition).
  - That is a G9 improvement available now: report internal spec
    choices, but don't ask about them.
- **One runner per target.** `q10/run_vst.py` with `m6.py` and
  `check_vst.py`, `libc/run_libc.py`, and `bench/picol/run_picol.py`
  are 2,200 lines in five files.
  - They share `tool_script`, `command` and the ledger.
  - They copy `sh()`, the forbidden-keyword regex, allow-list parsing,
    the TASK boilerplate and the main loop.
  - They differ in places where they should agree. For example, m6's
    keyword lint allows `Admitted` (it detects open lemmas through
    `Print Assumptions`), while picol's forbids it.
  - Codex found that m6's allow-list compared short names, so an
    `Admitted` lemma named `mem_mgr` would pass. This is fixed in
    `m6.py`; picol's check is not affected, because it forbids
    `Admitted`.
- **The certificate is not yet one command.**
  - G4 asks for clightgen, coqc, coqchk, `Print Assumptions` and the
    leak lint.
  - `run_picol.py --check bench/picol/proofs` does all but coqchk.
  - There is no bundle that records tool versions and the image digest.
- **Memory limits the work.** `prog_correct` needs about 6.5 GB and 3–4
  minutes, and two builds at once got a run killed. Run 1 replaced
  VST's `semax_func_cons` tactic, because its unification hung.
- **Only the final answer survives a run.** The agent's reasoning
  across 287 turns is gone; only proofs, `summary.json` and the final
  answer are kept. With the stream saved, a run could be audited, and
  the meter gap explained.

## 4. Against the plan's goals (Minimum level: picol)

| Goal | Status |
|---|---|
| G1 `semax_prog`, memory safety and leak freedom | **Met** for picol (all 46 bodies, `prog_correct` with `Qed`, leak lint). |
| G2 agent outside the trust base | **Met**: verdicts come from the check alone. The m6 hole is fixed; picol's check was not affected. |
| G3 proof-only edits | **Met**: all 7 C changes were owner decisions, recorded with examples. |
| G4 one-command certificate | **Partly**: one command re-checks, but without coqchk or a bundle. |
| G8 reusable workflow | **Partly**: the libc specs and policies carry over; the runner and checker do not yet. |
| G9 minimal human interaction | **Partly**: 28 steps. 10 are trusted specs or axioms (each reusable), 6 are C fixes, 4 are budgets, 2 are internal spec choices (not needed), and 6 are one-time policies or process decisions. |

## 5. Making Ariadne reusable

Proposal: one runner and one checker, with a small file describing
each target.  picol's description would be:

```toml
# bench/picol/target.toml
name     = "picol"
unit     = "picol_vst.c"            # verified unit (picol.c + musl globals + libc sources)
spec     = "spec_picol.v"           # frozen: main's spec, external specs
frozen   = ["picol.c", "picol_vst.c", "spec_picol.v"]
theorem  = "prog_correct"           # semax_prog statement, pinned by the check
trusted  = ["FILE_handle", "FILE_handle_valid", "FILE_handle_ptr",
            "malloc_token_valid_pointer"]
libc     = ["strlen", "strcmp", "strchr", "memcpy", "isupper"]
tests    = "run_asan.sh"
cap_usd  = 50
```

The pieces, each moved out of the existing scripts:

1. **`ariadne/session.py`:**
   - one `claude -p` session with the fence, the tool script, the
     spend meter and the prod loop (from `run_picol.py`);
   - also saves the raw stream to the run directory;
   - one ledger reservation and charge per run.
2. **`ariadne/check.py`:** one checker for every target.
   - pristine recompile;
   - keyword lint;
   - the statement pinned by `Check` (each frozen body for a library,
     `semax_prog` for a program);
   - `Print Assumptions` with fully qualified names, plus a rejection
     of any assumption declared in a proof file (the m6 fix);
   - the leak lint;
   - **coqchk**.
   - It writes a bundle manifest: file hashes, the image digest and
     tool versions. That closes G4.
3. **`ariadne/vst_ready.py`:** a free pre-pass over clightgen's output.
   It lists each reachable `goto`, each `switch` that can fall off its
   end, each variadic call, each extern global without an initializer,
   and each signed length that can overflow.
   - Its report is the list of C changes for the owner to decide,
     before any paid run.
   - On picol it would have produced fixes 3–5 and 7 on day one.
4. **`libc/`** stays the shared library of external specs. It gains
   picol's approved trusted specs, moved out of
   `bench/picol/TRUSTED_SPECS.md`, so a later program asks only about
   functions not yet there.
5. **A policy file**: the owner's standing decisions in one place
   (libc policy, `_vst.c` globals, the `main(void)` wrapper, the
   Callbacks rule, leak freedom at `main`'s return only, internal specs
   not reviewed). Each program's `HUMAN_STEPS.md` then logs only new
   questions.

Once picol's checker runs through `ariadne/check.py` with the same
verdict, delete the old scripts: `run_libc.py`, `run_picol.py`, and the
M6 parts of `q10/`.  The test is free: `--check bench/picol/proofs`
and the sglib proofs, with no model calls.

**Status (2026-11-26).**
- Done in `ariadne/` (`ariadne/README.md`): one runner (`session.py`)
  and one checker (`check.py`) with coqchk and a bundle manifest; the
  pre-pass (`vst_ready.py`); the shared libc specs (`libc/specs/`,
  `libc/TRUSTED_SPECS.md`).
- All 20 kept proofs re-check through it: picol, 5 libc units, sglib's
  library and its 13 clients.
- `run_picol.py`, `run_libc.py`, `m6.py` and `run_clients.py` are
  deleted.
- The policy file is not yet written.
- The meter's gap is explained: the output tokens arrive only in each
  response's `message_delta`. The new meter reads them there.

## 6. Next steps

### Tool and process, in order

1. **Consolidate the runner and checker** (§5). Add coqchk and the
   bundle manifest. Re-check picol, the libc proofs and sglib through
   it. This costs no model spend.
2. **`vst_ready.py`.** Its test: on upstream picol it must report the
   `goto`s, the two `switch`es, the 11 variadic calls and the
   `stdin`/`stdout`/`stderr` globals.
3. **Fix the meter's gap.** Save the stream, compare it with the
   result's `modelUsage`, and correct the estimate. The cap stays
   enforced by `--max-budget-usd` regardless.
4. **Stop asking about internal spec choices** (record the policy). Ask
   only about trusted specs and C changes.
5. **Plan the split before the run.**
   - picol ran as one agent proving functions in the order it chose.
   - For clox, the runner could freeze a shared definitions file (the
     role `picol_defs.v` grew into) after a first run.
   - Then it would hand groups of functions to parallel runs, each
     with its own build.
   - About 6 such runs fit in this machine's 62 GB at 6.5 GB each.
   - This is the M10 skill, tried first at clox's size.

### Benchmarks, in order

1. **huffman** (ranked 3rd in `bench/CANDIDATES.md`): a small first
   program for the consolidated tool. It would show the new runner
   works end to end, with `vst_ready.py`, the shared libc specs and
   the policy file, and record how many human steps remain when
   nothing is new.
2. **clox** (M9, the plan's Target): 2.6k lines, three times picol.
   - The candidates file already lists its known blockers:
     - `Token` passed by value (VST cannot verify struct arguments
       passed by value);
     - a variadic `runtimeError`;
     - a decision about the garbage collector.
   - The first two are exactly what `vst_ready.py` should report.
   - The Target asks for a lower cost per line than picol's $0.18 and
     fewer human steps than 28.
3. **md4c** (M10 candidate, 8.8k lines): only after clox shows the
   split works.

## 7. Owner's decisions (2026-11-26)

1. Internal funspec choices are reported in the run's answer, not
   asked (§3).  Questions go to the owner only for trusted specs and
   changes to the C.
2. Consolidate the runner and checker (§5) before clox.
3. huffman (github.com/drichardson/huffman, `bench/CANDIDATES.md` §3)
   is the first program on the consolidated tool, then clox.

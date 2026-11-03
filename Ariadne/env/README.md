# Ariadne toolchain (M0)

A Docker image with the pinned verification toolchain, and a smoke test
that checks the whole round trip: C + ACSL → Frama-C/WP → Why3 → Coq →
`.vo` → `coqchk`, plus CoqHammer and Pétanque.

## Build and check

```bash
cd Ariadne/env
docker build -t ariadne-m0:dev .     # ~4 min on 24 cores
cd smoke && ./check.sh               # five PASS lines expected
```

`run.sh <command> …` runs a command in the image with the current
directory mounted at `/work`, as the calling user (so files written in
the session are owned by you).  `ARIADNE_IMAGE` overrides the image tag.

## Pinned versions

| Component | Version | Why this one |
|-----------|---------|--------------|
| Frama-C | 33.0 (Arsenic) | latest release |
| Why3 | 1.8.2 | Frama-C 33.0 needs `>= 1.8.2 & < 1.9` |
| Rocq (Coq) | 9.0.1 | newest that `why3-coq.1.8.2` accepts (`coq-stdlib < 9.1`) |
| OCaml | 4.14.2, no flambda | `frama-c` conflicts with flambda variants |
| CoqHammer | 1.3.2+9.0 | release for Rocq 9.0 |
| coq-lsp / Pétanque | 0.2.5+9.0 | latest for Rocq 9.0; provides `pet` |
| Alt-Ergo | 2.6.4 | Why3 1.8.2 accepts 2.6.x |
| Z3 | 4.13.4 | Why3 1.8.2 accepts 4.11–4.13 |
| CVC5 | 1.2.1 | Why3 1.8.2 accepts 1.0–1.2 |
| Vampire | 4.9 (CASC 2024) | Vampire 5 dropped `--output_axiom_names`, which CoqHammer uses |
| Eprover | 2.6 (Debian) | CoqHammer ATP |

Base image: `rocq/rocq-prover:9.0.1-native-ocaml-4.14.2`, pinned by
digest.  Its `ocamlfind 1.9.6` pin is lifted because coq-lsp 0.2.5 needs
`>= 1.9.8`; opam then recompiles Rocq 9.0.1 against it.  Prover binaries
are pinned by SHA-256.

## Local patches to Why3 (in `patch-why3-rocq9.sh`)

1. **Coq detection.**  Why3 1.8.2 only recognises Coq's old version
   banner ("The Coq Proof Assistant, version …") and versions up to
   8.20.  The patch accepts Rocq's banner and 9.0.x.  `why3-coq.1.8.2` is
   built against Rocq 9.0, so only the detection rule was out of date.
2. **`coq-ariadne` driver** (`coq-ariadne.drv`).  Why3 regenerates each
   goal file on every check and keeps only the text between `Proof.` and
   `Qed.`, so imports added by hand are lost.  The driver extends
   `coq.drv` with a prelude importing `Lia` and CoqHammer
   (`Tactics`, `Hammer`).  It adds imports only, no axioms.

## What the smoke test checks (`smoke/check.sh`)

1. `swap.c`: 10/10 goals.  WP's simplifier closes 4, Alt-Ergo 3, and Coq
   closes the induction lemma `sum_nonneg` with the script stored in
   `smoke/session/interactive/lemma_sum_nonneg.v` (`-wp-interactive
   batch`).  The other 2 are WP's terminating/unreachable checks.
2. The same script compiled with `coqc` and re-checked by `coqchk -o`.
   The axioms it relies on are written to `smoke/cert/coqchk.txt`:
   Why3 theory axioms (`c_euclidian`, `eqb'def`, …), classical axioms
   from Rocq's stdlib (excluded middle, functional extensionality,
   `eq_rect_eq`, indefinite description, classical Dedekind reals), and
   **the ACSL definition `sum` itself as `Parameter L_sum` + `Axiom
   L_sum_def`.**  This is the starting point for the axiom allow-list of
   plan §7.4.
3. `hammer_check.v`: `sauto`, and `hammer` via Vampire and Eprover;
   hammer reconstructs `srun eauto use: …`, which then needs no ATP.
4. `pet_check.py`: Pétanque opens the WP-generated goal file, runs the
   proof tactic by tactic, and reports goal counts and `proof_finished`.
5. **Known hole** (`bad_def.c`): WP accepts the non-terminating
   definition `logic integer bad(integer n) = bad(n) + 1;`, exports it as
   an axiom, and Coq proves `bad(0) == 0` from it with
   `pose proof (L_bad_def 0%Z). lia.`.  This step passes while the hole
   exists; see plan §7.3 for the guardrail.

## Notes for the harness (M2)

- WP stores Coq scripts in `<session>/interactive/<goal>.v`.  To create
  stubs for open goals, run with `-wp-prover coq -wp-interactive update`;
  to check them, `-wp-interactive batch`.  Only the `Proof. … Qed.`
  section survives regeneration.
- `-wp-msg-key prover` shows Coq's actual error message; without it a
  failed script is reported only as `Unknown`/`Unsuccess`.
- `pet` speaks JSON-RPC with `Content-Length` headers on stdin/stdout;
  `run.sh` passes `-i` so it works through Docker.  Methods used:
  `petanque/setWorkspace`, `petanque/start`, `petanque/run`,
  `petanque/goals`.  The workspace needs a `_CoqProject` with
  `-R /home/rocq/.opam/4.14.2/lib/why3/coq Why3`.
- `Typed` model: RTE warns that `\aligned` and `\valid_function` guards
  are skipped (not supported).

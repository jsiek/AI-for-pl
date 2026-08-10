# Phase 1 Reachability Catalog Report

## Summary

`GTSFImp/proof/DGG/ReachabilityCatalog.agda` adds 28 closed source
entries.  Each entry stores both gradual typings and one source imprecision
derivation.  The module records both the ordinary compiler projection as
`compiled-standard` and the executable mirror projection as `compiled`.

Hardened rerun result: no entries flipped.  All registered Phase 1 source
entries still screen clean, and every entry now has a skeleton refl gate
checking the mirror output against the ordinary compiler output.

## Catalog

| Id | Entry | Axis | Exp | Act | Notes |
|---:|---|:---:|:---:|:---:|---|
| 1 | baseline-direct | a | clean | clean | star app |
| 2 | baseline-nat-direct | a | clean | clean | Nat app |
| 3 | baseline-bool-direct | a | clean | clean | Bool app |
| 4 | baseline-poly-to-dyn | a | clean | clean | nonrefl |
| 5 | baseline-bool-to-dyn | a | clean | clean | nonrefl |
| 6 | baseline-fun-to-dyn | a | clean | clean | fun value |
| 7 | baseline-higher-order | a | clean | clean | inst value |
| 8 | seal-chain-depth1 | b | clean | clean | one bind |
| 9 | seal-chain-depth2 | b | clean | clean | return poly |
| 10 | seal-chain-depth3 | b | clean | clean | two nests |
| 11 | seal-chain-depth4 | b | clean | clean | three nests |
| 12 | skew-tag-depth2 | c | clean | clean | skew analog |
| 13 | skew-tag-depth3 | c | clean | clean | deeper skew |
| 14 | skew-star-inst | c | clean | clean | star side |
| 15 | tag-boundary-depth4 | d | clean | clean | source analog |
| 16 | tag-boundary-star-inst | d | clean | clean | star analog |
| 17 | gen-inst-return-poly | e | clean | clean | return forall |
| 18 | gen-inst-self-nat | e | clean | clean | self Nat |
| 19 | reveal-conceal-self-star | f | clean | clean | self star |
| 20 | reveal-conceal-return-poly | f | clean | clean | app return |
| 21 | shared-prefix-nat | g | clean | clean | Nat suffix |
| 22 | shared-prefix-bool | g | clean | clean | Bool suffix |
| 23 | shared-prefix-star | g | clean | clean | star suffix |
| 24 | higher-order-poly-arg | h | clean | clean | callee inst |
| 25 | higher-order-shared-arg | h | clean | clean | shared arg |
| 26 | adversarial-source-chain | i | clean | clean | center analog |
| 27 | adversarial-source-star | i | clean | clean | star analog |
| 28 | blame-dyn-bool | j | clean | clean | blame path |

## Fidelity

The catalog now defines `skeleton : C.Term Δ -> TermSkeleton Δ`.  The
skeleton preserves all term constructors, including every cast,
reveal, conceal, seal, and type-application node.  It erases the proof
content of consistency evidence and records each cast node by its intrinsic
source and target types.  Reveal and conceal evidence is not transported by
`compile`, and `Eval` branches on its constructors and seal payloads, so the
conversion skeleton keeps those constructors and payloads.

`Eval.step?` itself recurses by term syntax.  The helpers `value?`,
`inert?`, and `cast-redex?` do branch on consistency evidence constructors,
and the `!`/`？` cases inspect ground endpoints and ground equality.  The
skeleton gate is therefore a compiler-fidelity check, not a theorem that
arbitrary evidence with the same endpoints is operationally identical.  For
these catalog comparisons the mirror and standard compiler insert casts at
the same source typing sites; the gate rules out structural changes such as
dropping an identity `∀` cast.

The old mirror special-cased application consistency
`∀ᶜ (id (＇0) ↦ id (＇0))` by dropping the argument cast.  That has been
removed.  The retained cast initially exposed the normalization blocker:
after a polymorphic β-step, `sym∼` had placed the inner function evidence
under a `transport-env∼ flip-extᵐ` proof, so `cast-redex?` could not expose
the `_↦_` constructor.  The mirror now keeps the cast and gives this exact
identity-`∀` symmetry case a constructor-headed `sym-screen` proof:
`∀ᶜ (id (＇0) ↦ id (＇0))`.  The evaluator then reaches the same
all-clean screen results without changing the reduction relation.

Per-entry gate result: all 28 `*-skeleton-gate` definitions typecheck by
`refl`.

## Surprises

Direct source-level `X ∼ ★` tag-boundary programs are not admissible in the
current source typing relation, because source consistency uses the closed
identity environment.  Variable-ground tag boundaries can be written in the
cast calculus, as in `ReachabilityScreen`, but not directly as source terms.

The ordinary compiler output is recorded and structurally checked, but it is
not the refl-runner.  The screen runner erases proof-only transport around
application symmetry while preserving every cast node.  Without the
constructor-headed identity-`∀` symmetry case described above, Agda gets
stuck deciding evaluator steps for otherwise exact casts.

## Timings

Warm and cold checks for the hardened catalog:

- `ReachabilityCatalog.agda`, warm cache: 2.530s.
- `ReachabilityCatalog.agda`, `--ignore-interfaces`: 50.757s.
- `All.agda`, warm cache before final clean rebuild: 29.677s.
- `All.agda`, fresh rebuild after deleting `.agdai`: 68.272s.

The catalog is fast enough to stay registered in `All.agda`; no split runner
module was needed.

## Shortlist

There are no source-catalog suspects from Phase 1.

Recommended Phase 3 deep dives remain:

- `ReachabilityScreen.adversarial-entry`, the Phase 0 hand-built suspect.
- `adversarial-source-chain`, the closest source chain analogue.
- `tag-boundary-star-inst` and `skew-star-inst`, the ★-right stress cases.
- `higher-order-shared-arg`, because it stresses allocation under a callee.

## Verification

Commands run:

- `agda -i GTSFImp -v0 GTSFImp/proof/DGG/ReachabilityCatalog.agda`
  with the requested `AGDA_DIR`: exit 0, 2.530s warm-cache.
- `agda --ignore-interfaces -i GTSFImp -v0`
  `GTSFImp/proof/DGG/ReachabilityCatalog.agda`
  with the requested `AGDA_DIR`: exit 0, 50.757s.
- `agda -i GTSFImp -v0 GTSFImp/All.agda`
  with the requested `AGDA_DIR`: exit 0, 29.677s warm-cache.
- Source-hole keyword grep on touched files: no matches.
- `awk 'length($0)>80 ...'` on touched files: no output.
- Final clean rebuild:
  `find GTSFImp -name '*.agdai' -delete &&`
  `agda -i GTSFImp -v0 GTSFImp/All.agda`
  with the requested `AGDA_DIR`: exit 0, 68.272s.

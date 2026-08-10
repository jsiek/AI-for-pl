# Split Preflight

Scope: root scratch only.  `GTSFImp/` was read for the dossier and blocked
notes, but not edited.

Agda check:

```sh
AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/abaf167a-fb69-4f9e-bdf7-5f069c5047b5/scratchpad/agda-home agda -i GTSFImp -v0 SplitPf.agda
```

Result: pass.

## Verdict Table

| Item | Verdict | Scratch evidence |
| --- | --- | --- |
| 1. Four-mode model | PASS | `Var∼₅` has `X∼Xᶜ`, `X∼Xˢ`, `X∼★`, `★∼X`; `idᶜ₅` is crossable, `extᵐ₅` opens strict, `instᵐ₅`/`genᵐ₅` are unchanged, and star gates include dynamic plus crossable only. |
| Calibration 1: `Λ`-bound `X ⊢ X ∼ ★` | PASS | `calibration-1₅` derives `idᶜ₅ ⊢ ＇ zero ∼₅ ★` by the crossable gate. |
| Calibration 2: `(∀X. X→X) ∼ (∀X. X→★)` | PASS, rejected | `calibration-2₅` proves formation emptiness.  The direct `∀ᶜ` route hits `strict-var-not-to-star₅`; the `inst`/`gen` routes hit cross-variable failures `no-zero∼suc-zero₅` and `no-suc-zero∼zero₅`. |
| Calibration 3: `(∀X. X→X) ∼ (★→★)` | PASS | `calibration-3₅` derives the judgment via `inst₅` and the ordinary dynamic gates. |
| Calibration 4: `(∀Y. ★→Y→★) ∼ (∀X. X→★→X)` | PASS | `calibration-4₅` derives the judgment via `inst₅` then `gen₅`; no crossable gate is used. |
| Calibration 5: `∀Z.(X→Z) ∼ ∀Z.(★→Z)`, ambient `X` | PASS | `calibration-5₅` derives the judgment under `∀ᶜ₅`; the fresh `Z` slot is strict, while ambient `X` remains crossable. |
| 3. `ground-cast-target⊑` restoration | PASS | `blocked-ground-cast-body-unformable₅` and `blocked-ground-cast-forall-direct-unformable₅` refute the old rigid counterexample shape.  The failing square needs `★ ∼ ＇ zero` under `flipᵐ₅ (extᵐ₅ idᶜ₅)`, and `strict-mode-var-not-from-star₅` rules it out. |
| 4. CrossFree common lower | PASS | `CommonLowerStatement₅` is the intended theorem surface with a `CrossFree₅` premise.  `crossable-counterexample-excluded₅` excludes the new crossable-gate counterexample; `consistent-common-lower-∀ᶜ-clause₅` is the plain recursive `∀ᶜ` shape with no extra strict-slot predicate; dynamic variable clauses are `common-lower-dynamic-to-star-var₅` and `common-lower-dynamic-from-star-var₅`. |
| 5. Totality | PASS | `To★OK₅`/`From★OK₅` encode “no strict variables on that side”.  `to-★₅`/`from-★₅` check the construction; crossable and dynamic variable cases are `to★-crossable-var-ok₅`, `from★-crossable-var-ok₅`, `to★-dynamic-var-ok₅`, and `from★-dynamic-var-ok₅`; strict variables are rejected by `to★-strict-var-impossible₅` and `from★-strict-var-impossible₅`. |
| 6. `SubstEnv∼` | PASS | `SubstEnv∼₅` re-keys the landed rigid fields to `cross-to-★`/`cross-from-★` for `X∼Xᶜ` only.  Strict fresh slots are exact-mode impossible again: `open-to-★-strict-slot-impossible₅`, `open-from-★-strict-slot-impossible₅`, and `open-cross-to-★-strict-slot-impossible₅`. |

## Summary

No failure found in the scratch model.  The split separates the two old uses of
`X∼X`: program-binder variables can still mint name tags through crossable
gates, while `∀ᶜ` body comparison opens a strict slot with no star gate.  That
is enough to keep the five calibration judgments aligned with the dossier and
to remove the rigid `ground-cast-target⊑` blocker without changing the live
term-imprecision relation.

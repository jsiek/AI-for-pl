# DGG Subagent Wave 2

This wave starts after the paired-world refactor:

- `TermRel` now has both worlds:
  `TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B`.
- Left simulation results now carry `Ψˡ ≤ Ψˡ′`.
- Application helpers use `wk-left-world-⊑` with concrete `store-growth`.
- All files currently pass `agda -v0 All.agda`.

Each worker should keep its write set narrow. Do not edit another worker's file
unless a missing interface makes progress impossible; in that case, report the
needed statement instead of changing it.

## Worker 1: Term Imprecision Infrastructure

Write set:

- `proof/DGGTermImprecision.agda`

Primary targets:

1. Replace `wk-left-world-⊑` with a real theorem, or split it into smaller
   concrete weakening lemmas if needed.
2. Try to prove `renameᵗ-suc-⊑`; this is the current blocker inside
   substitution under type binders.
3. If time remains, reduce `tysubst-body-⊑` or state the exact missing
   type-substitution lemma at the smallest useful granularity.

Important current obligations:

```agda
wk-left-world-⊑ :
  ∀ {Ψˡ Ψˡ′ Ψʳ Ψʳ′ Σˡ Σˡ′ Σʳ Σʳ′ M M′ A B} →
  StoreWf 0 Ψˡ′ Σˡ′ →
  StoreWf 0 Ψʳ′ Σʳ′ →
  Ψˡ ≤ Ψˡ′ →
  Σˡ ⊆ˢ Σˡ′ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
  TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ M M′ A B
```

Likely imports:

- `proof.PreservationWkImp` for `wk-⊑` and `wk-⊒`
- `proof.PreservationWkConv` for `wk-conv↑` and `wk-conv↓`
- `proof.TypeProperties` for `WfTy-weakenˢ`
- `proof.PreservationWkTerm` only for right-typed blame cases if needed

Check:

```text
agda -v0 proof/DGGTermImprecision.agda
```

## Worker 2: Value Catchup

Write set:

- `proof/DGGCatchup.agda`

Primary targets:

1. Prove one of the wrapper catchup postulates:
   `right-extra-up-catchup-left`, `right-extra-down-catchup`,
   `right-extra-down-catchup-left`, `right-extra-reveal-catchup`,
   `right-extra-reveal-catchup-left`, `right-extra-conceal-catchup`, or
   `right-extra-conceal-catchup-left`.
2. Prefer the non-store-allocating wrapper cases first; leave ν/fresh-seal
   cases isolated if they need a stronger bridge.
3. If proving a whole helper is too large, add concrete clauses for simple
   evidence cases and isolate the remaining hard cases as smaller postulates.

Current pattern to imitate:

- `right-extra-up-catchup` already handles simple evidence cases concretely.
- `left-value-right-catchup` is recursive and uses these helper lemmas.

Check:

```text
agda -v0 proof/DGGCatchup.agda
```

## Worker 3: Function Application Beta Family

Write set:

- `proof/DGGSimLeftApp.agda`

Primary targets:

1. Prove `sim-left-beta-app` for the direct lambda/lambda catchup case.
2. Then try one wrapper beta helper, preferably `sim-left-beta-up-app` or
   `sim-left-beta-down-app`.
3. Use `left-value-right-catchup`, `subst-⊑`, `appL-↠`, `appR-↠`, and
   `multi-trans`. Import only the specific lemmas you use.

Important shape:

```agda
sim-left-beta-app :
  ...
  ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
    (StoreWf 0 Ψʳ′ Σʳ′ ×
     ∃[ N′ ]
       ((Σʳ ∣ (L′ · W′) —↠ Σʳ′ ∣ N′) ×
        TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ (N [ W ]) N′ B B′))
```

Do not change `SimLeftStepᵃ`; it is now aligned with the main result shape.

Check:

```text
agda -v0 proof/DGGSimLeftApp.agda
```

## Worker 4: Type Application Beta Family

Write set:

- `proof/DGGSimLeftTypeApp.agda`

Primary targets:

1. Try to prove `sim-left-beta-Λ` for the matched right `Λ` case using
   `fresh-seal-sync-Λ`.
2. If that is blocked, improve the statement of `fresh-seal-sync-Λ` into
   smaller helper obligations, but keep the paired-world result.
3. For an easier win, strengthen `sim-left-beta-reveal-∀-matched` so its result
   matches the paired right-world shape used by `sim-left-beta-reveal-∀`.

Important paired allocation shape:

```agda
TermRel (suc Ψˡ) ((length Σˡ , T) ∷ Σˡ)
        (suc Ψʳ) ((length Σʳ , T) ∷ Σʳ)
        ...
```

Do not edit `DGGTermImprecision.agda`; if a type-substitution lemma is needed,
report the exact statement.

Check:

```text
agda -v0 proof/DGGSimLeftTypeApp.agda
```

## Worker 5: Left Simulation Cases

Write set:

- `proof/DGGSimLeft.agda`

Primary targets:

1. Reduce `sim-left-rest` by adding concrete cases to `sim-left`.
2. Good candidates are congruence cases already structurally mirrored by
   `ξ-⇑`, `ξ-⇓`, `ξ-↑`, and `ξ-↓`.
3. Try to replace one of `sim-left-reveal-cong`,
   `sim-left-revealL-cong`, `sim-left-conceal-cong`, or
   `sim-left-concealL-cong` with a concrete proof.

Important interface:

- Every `SimLeftResult` now carries `Ψˡ ≤ Ψˡ′`.
- For unchanged-world cases, use `≤-refl`.
- For recursive multi-step results, compose witnesses with `≤-trans`.

Do not edit the application/type-application helper modules in this wave.

Check:

```text
agda -v0 proof/DGGSimLeft.agda
```

## Worker 6: Right Simulation Cases

Write set:

- `proof/DGGSimRight.agda`

Primary targets:

1. Reduce `sim-right-rest` by proving one congruence family directly.
2. Best first targets: right application/type-application congruence success
   cases currently delegating to `sim-right-rest`.
3. Keep blame propagation cases concrete and preserve the current
   `SimRightResult` shape.

Useful existing helpers:

- `prefix-blames`
- `appL-blames`
- `appR-blames`
- `tyapp-blames`
- `up-blames`, `down-blames`, `reveal-blames`, `conceal-blames`
- `sim-right*`

Check:

```text
agda -v0 proof/DGGSimRight.agda
```

## Integration Checklist

After a worker returns:

1. Run that worker's local Agda check.
2. Run dependent checks:
   - `agda -v0 proof/DGGSimLeft.agda` after workers 3, 4, or 5.
   - `agda -v0 proof/DynamicGradualGuarantee.agda` after workers 2, 5, or 6.
3. Finish with:

```text
agda -v0 All.agda
```

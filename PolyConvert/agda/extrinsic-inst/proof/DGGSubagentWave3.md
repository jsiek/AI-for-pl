# DGG subagent wave 3

## Current checked state

The integrated checkout type-checks with:

```sh
agda -v0 All.agda
```

Two previously reported transport obligations were redundant and are now routed
through `proof.DGGTermImprecision`:

- `DGGSimLeftApp.beta-subst-⊑` is a concrete wrapper around `subst-⊑`.
- `DGGSimRight` uses `wk-left-world-⊑` instead of a local
  `wk-right-app-arg-⊑` postulate.

## GTLC lesson for the tag/untag case

For the `right-extra-down-catchup-tag` case, do not treat right blame as a
normal catchup endpoint. The corresponding GTLC argument rules out the bad tag
case before it arises. The relevant GTLC lemmas/patterns are:

- `ground-upper-unique` in `GTLC/agda/Types.agda`
- `cast!-⊑-not-★`, `inj-⊑-inj`, and `proj-?-less-ground` in
  `GTLC/agda/proof/DynamicGradualGuaranteeCore.agda`
- the `β-proj-inj-bad` simulation case, which allows right blame only in
  right-to-left simulation, not in value catchup

For PolyConvert, the likely core lemma is the raw-imprecision analogue:

```agda
ground-upper-unique-⊑ :
  ∀ {Ψ Γ A G H p q} →
  Ground G →
  Ground H →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
  Ψ ∣ Γ ⊢ q ⦂ A ⊑ H →
  G ≡ H
```

The tag catchup case may also need the chained form:

```agda
ground-upper-unique-chain-⊑ :
  ∀ {Ψ Γ A B C G H p q r s} →
  Ground G →
  Ground H →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ q ⦂ B ⊑ G →
  Ψ ∣ Γ ⊢ r ⦂ A ⊑ C →
  Ψ ∣ Γ ⊢ s ⦂ C ⊑ H →
  G ≡ H
```

Use these to show that the tag carried by the right value and the requested
downcast tag agree, so `tag-untag-bad` is impossible and the catchup proceeds
through `tag-untag-ok`.

## Structural transport shapes for `TermRel`

These shapes type-check in the current development, either as concrete lemmas
or as the remaining named proof holes.

### World/store weakening

Concrete:

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

The right-world-only variants should be aliases/uses of this lemma while
`TermRel` delegates to the left-world evidence.

### Term substitution

Concrete:

```agda
subst-⊑ :
  ∀ {Ψ Σ M M′ N N′ A A′ B B′ p p⊢} →
  TermRel Ψ Σ Ψ Σ N N′ A A′ →
  ⟪ 0 , Ψ , Σ , (A , A′ , p , p⊢) ∷ [] ⟫
    ⊢ M ⊑ M′ ⦂ B ⊑ B′ →
  TermRel Ψ Σ Ψ Σ (M [ N ]) (M′ [ N′ ]) B B′
```

This is already enough for the direct application beta case.

### Type-variable renaming

Remaining proof hole:

```agda
renameᵗ-suc-⊑ :
  ∀ {E M M′ A B} →
  E ⊢ M ⊑ M′ ⦂ A ⊑ B →
  ⇑ᵗᴱ E ⊢ renameᵗᵐ suc M ⊑ renameᵗᵐ suc M′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
```

This is the type-variable analogue of `wk-rel-⊑`: lift the `PCtx` through
`⇑ᵗᴾ`, use `wkImp-plains` for raw imprecision evidence, and rename conversion
evidence under `↑`/`↓`.

### Type substitution / instantiation

Remaining proof hole:

```agda
tysubst-body-⊑ :
  ∀ {Ψ Σ M M′ A B T} →
  WfTy 0 Ψ T →
  ⟪ 1 , Ψ , ⟰ᵗ Σ , [] ⟫ ⊢ M ⊑ M′ ⦂ A ⊑ B →
  TermRel Ψ Σ Ψ Σ (M [ T ]ᵀ) (M′ [ T ]ᵀ) (A [ T ]ᵗ) (B [ T ]ᵗ)
```

This is the key transport lemma for `Λ`/type application after the fresh seal
allocation has exposed the body.

### Fresh-seal synchronization

Remaining proof hole:

```agda
fresh-seal-sync-Λ :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A B T pT} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  length Σˡ ≡ length Σʳ →
  Value V →
  Value V′ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ (Λ V) (Λ V′) (`∀ A) (`∀ B) →
  WfTy 1 Ψˡ A →
  WfTy 1 Ψˡ B →
  WfTy 0 Ψˡ T →
  Ψˡ ∣ plains 0 [] ⊢ pT ⦂ A [ T ]ᵗ ⊑ B [ T ]ᵗ →
  TermRel (suc Ψˡ) ((length Σˡ , T) ∷ Σˡ)
    (suc Ψʳ) ((length Σʳ , T) ∷ Σʳ)
    ((V [ ｀ (length Σˡ) ]ᵀ) ↑ convert↑ A (length Σˡ))
    ((V′ [ ｀ (length Σʳ) ]ᵀ) ↑ convert↑ B (length Σʳ))
    (A [ T ]ᵗ) (B [ T ]ᵗ)
```

This probably combines `tysubst-body-⊑`, fresh seal index synchronization, and
conversion/reveal transport.

## Worker assignments

### Worker 1: ground uniqueness helpers

Owner file: `proof/TypeProperties.agda`.

Add and prove `ground-upper-unique-⊑`. If useful, also prove
`ground-upper-unique-chain-⊑`; otherwise record the exact missing transitivity
lemma for raw imprecision.

### Worker 2: tag/untag catchup

Owner file: `proof/DGGCatchup.agda`.

Use the Worker 1 lemma shape to replace `right-extra-down-catchup-tag`. If the
ground uniqueness helper is not yet available, isolate the one local assumption
needed and keep the proof body otherwise concrete. The target is to rule out
`tag-untag-bad`, not to return right blame from catchup.

### Worker 3: type-renaming transport

Owner file: `proof/DGGTermImprecision.agda`.

Replace `renameᵗ-suc-⊑` with a structural proof. Follow the existing
`wk-rel-⊑` recursion and use the type-renaming lemmas in
`proof.PreservationTermSubst`, `proof.PreservationWkImp`, and
`proof.PreservationWkConv`.

### Worker 4: type-substitution transport

Owner file: `proof/DGGTermImprecision.agda`.

Work on `tysubst-body-⊑`. If editing conflicts with Worker 3, create a short
handoff note instead of touching overlapping code. The expected proof is by
induction on term imprecision under a type-substitution environment.

### Worker 5: fresh-seal sync for `Λ`

Owner file: `proof/DGGSimLeftTypeApp.agda`.

Replace `fresh-seal-sync-Λ` or split it into smaller local lemmas. Lean on
`tysubst-⊑` if Worker 4 lands it; otherwise state the exact conversion/seal
transport bridge needed after type substitution.

### Worker 6: application wrapper beta cases

Owner file: `proof/DGGSimLeftApp.agda`.

Continue from the direct lambda case. Target `sim-left-beta-app-rest` or one
wrapper case (`⊑⇑R`, `⊑⇓R`) or a matching seal wrapper (`⊑↑` or `⊑↓`).
Use catchup, `subst-⊑`, and the world weakening lemma already imported from
`DGGTermImprecision`.

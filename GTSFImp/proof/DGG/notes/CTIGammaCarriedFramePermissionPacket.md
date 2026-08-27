# CTI permission audit: `γ`-carried reveal/conceal frames

Status: design and permission audit only. This packet does not change
`proof/DGG/CastTermImprecision.agda`. The audit concludes that the live CTI
rules remain textually unchanged, so this design does not require permission
to edit that file.

This supersedes the separate `OpenFrames` judgment index proposed in
`CTIBalanceDesignPacket.md`. The smaller design keeps the CTI judgment exactly
`γ ⊢² M ⊑ M′ ∶ p`. The single current world `γ` carries the balance
information: every source-rebase world change carries either an `open-frame`
role or a checked `alignment-only` payload, and `openFramesᶜ γ` is computed by
scanning that history.

## Supporting world change

The role must not be an unchecked bit. An arbitrary source pivot update can
change the meaning of every later type comparison, so accepting every world
tagged `alignment-only` as a zero-open-frame root would be unsound for the
existing transport invariants. The proposed role is indexed by its world and
pivots, and the alignment case carries evidence that the update is demanded
by an actual paired conversion boundary:

```agda
data AlignmentBoundaryᶜ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
    (Xᴸ : TyVar (Δᵉ Γᴸ)) (Xᴿ : TyVar (Δᵉ Γᴿ)) : Set where
  paired-reveal-alignmentᶜ :
      -- source and target reveal typings at Xᴸ and Xᴿ,
      -- equal generator positions, and the paired representation comparison
      ...
    → AlignmentBoundaryᶜ γ Xᴸ Xᴿ

  paired-conceal-alignmentᶜ :
      -- source and target conceal typings at Xᴸ and Xᴿ,
      -- equal generator positions, and the paired representation comparison
      ...
    → AlignmentBoundaryᶜ γ Xᴸ Xᴿ

data SourceRebaseRole {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
    (Xᴸ : TyVar (Δᵉ Γᴸ)) (Xᴿ : TyVar (Δᵉ Γᴿ)) : Set where
  open-frame : SourceRebaseRole γ Xᴸ Xᴿ
  alignment-only : AlignmentBoundaryᶜ γ Xᴸ Xᴿ
    → SourceRebaseRole γ Xᴸ Xᴿ

rebase-source-changeᶜ : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → (Xᴸ : TyVar (Δᵉ Γᴸ))
  → (Xᴿ : TyVar (Δᵉ Γᴿ))
  → SourceRebaseRole γ Xᴸ Xᴿ
  → PivotUpdateᵗ (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ)
  → (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Xᴿ
  → WorldChange γ Γᴸ Γᴿ
```

The ellipses above are a design boundary, not permission to install a weak
postulate. The final `AlignmentBoundaryᶜ` must expose the exact conversion
typing, generator-position equality, and representation comparison already
consumed by `reveal⊑reveal²` or `conceal⊑conceal²`. In the TIR gate below,
`checkpoint₃-source-reveal⊢`, `checkpoint₁-alpha-reveal⊢`, their equal
generator positions, and `ℕ ⊑ ★` supply this payload.

`SourceRebaseᶜ` remains unindexed. Its direct constructor recognizes only the
`open-frame` world change:

```agda
source-rebase-now : ∀ {Γᴸ Γᴿ}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ Xᴿ}
    (ok : PivotUpdateᵗ
      (ηᴸᶜ γ) Xᴸ (toRenameⁱ (ηᴿᶜ γ) Xᴿ))
    (represented :
      (＇ Xᴸ) ⊑ᵀ⟨ γ ⟩ lookupStore (Σᵉ Γᴿ) Xᴿ)
  → SourceRebaseᶜ γ
      (γ ▻ᶜ rebase-source-changeᶜ
        Xᴸ Xᴿ open-frame ok represented)
      Xᴸ Xᴿ
```

Every bind/lift constructor transports such an open-frame proof. There is no
`SourceRebaseᶜ` constructor for an `alignment-only` change. It can change the
current source injection, but cannot be mistaken for a CTI reveal push or
conceal pop.

For endpoint pairs `Xᴸ ↔ Xᴿ`, the scan is definitionally:

```agda
openFramesᶜ emptyᶜ = []
openFramesᶜ (γ ▻ᶜ center-changeᶜ) = openFramesᶜ γ
openFramesᶜ (γ ▻ᶜ bind-term-changeᶜ p) = openFramesᶜ γ

openFramesᶜ (γ ▻ᶜ lift-both-changeᶜ ...) =
  map (λ (Xᴸ ↔ Xᴿ) → Fin.suc Xᴸ ↔ Fin.suc Xᴿ) (openFramesᶜ γ)
openFramesᶜ (γ ▻ᶜ bind-both-changeᶜ ...) =
  map (λ (Xᴸ ↔ Xᴿ) → Fin.suc Xᴸ ↔ Fin.suc Xᴿ) (openFramesᶜ γ)
openFramesᶜ (γ ▻ᶜ bind-both-star-changeᶜ ...) =
  map (λ (Xᴸ ↔ Xᴿ) → Fin.suc Xᴸ ↔ Fin.suc Xᴿ) (openFramesᶜ γ)

openFramesᶜ (γ ▻ᶜ lift-left-changeᶜ ...) =
  map (λ (Xᴸ ↔ Xᴿ) → Fin.suc Xᴸ ↔ Xᴿ) (openFramesᶜ γ)
openFramesᶜ (γ ▻ᶜ bind-left-changeᶜ ...) =
  map (λ (Xᴸ ↔ Xᴿ) → Fin.suc Xᴸ ↔ Xᴿ) (openFramesᶜ γ)

openFramesᶜ (γ ▻ᶜ bind-right-changeᶜ ...) =
  map (λ (Xᴸ ↔ Xᴿ) → Xᴸ ↔ Fin.suc Xᴿ) (openFramesᶜ γ)

openFramesᶜ
  (γ ▻ᶜ rebase-source-changeᶜ
    Xᴸ Xᴿ (alignment-only boundary) ok represented) =
  openFramesᶜ γ
openFramesᶜ
  (γ ▻ᶜ rebase-source-changeᶜ
    Xᴸ Xᴿ open-frame ok represented) =
  (Xᴸ ↔ Xᴿ) ∷ openFramesᶜ γ
```

The intended theorem is therefore a direct reading of the current world:

```agda
open-source-rebase-frames :
  SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → openFramesᶜ γᵖ ≡ (Xᴸ ↔ Xᴿ) ∷ openFramesᶜ γ
```

There is no second CTI index, chronological predecessor stack, balance proof,
or synchronization wrapper.

## Complete live CTI rules before the change

Repository-wide inspection shows that exactly two CTI constructors mention
`SourceRebaseᶜ`. These are their complete live definitions.

```agda
  ⊑reveal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↓ c′ ∶ q
```

## Complete CTI rules after the supporting change

The proposed after-rules are byte-for-byte the same. The strengthened meaning
comes from `SourceRebaseᶜ`: its direct case can now witness only an
`open-frame` world change.

```agda
  ⊑reveal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {c′ : Conv↑ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
    → {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↑ c′ ∶ q

  ⊑conceal-rebase² : ∀
      {γᵖ : Γᴸ ⊑ᶜ Γᴿ}
      {M M′ A B B′ Xᴸ Xᴿ Rᴿ}
      {p : A ⊑ᵀ⟨ γᵖ ⟩ B}
      {c′ : Conv↓ (Δᵉ Γᴿ) B B′}
    → (c′⊢ : Σᵉ Γᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → SourceRebaseᶜ γᵖ γ Xᴸ Xᴿ
    → γᵖ ⊢² M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ γ ⟩ B′)
      ---------------------
    → γ ⊢² M ⊑ M′ ↓ c′ ∶ q
```

There is therefore no proposed CTI edit. In particular:

- `⊑reveal-identity`, `⊑conceal-identity`, `reveal⊑-identity`, and
  `conceal⊑-identity` stay in one world and do not affect the scan;
- `reveal⊑-only²` and `conceal⊑-only²` are source syntax, not source rebasing,
  and do not affect the scan;
- `reveal⊑reveal²` and `conceal⊑conceal²` are paired boundaries and leave the
  current scan unchanged;
- all non-conversion CTI constructors remain textually unchanged because the
  judgment still has only its existing world index.

## Trusted allocation-discharge square

The concrete gate is the Example 12-derived `TargetIdentityReveal` checkpoint
2 to checkpoint 3 transition. The following terms are normalized by
`CTIGammaCarriedFramePacket.agda` using the repository's name-aware
`showTerm`. They contain no checkpoint aliases or de Bruijn indices.

Let

```text
M₂ = (λx. x ·
        (Λλx. (λy. y · x ⟨ X↦★ ⟩) [ ℕ ]
          ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩ · 42 ⟨ ℕ↦ℕ ⟩) ⟨ ★↦ℕ ⟩)

N₂ = (λx. x ·
        (λx. (λy. y · x ⟨ X′↦★ ⟩) ↑ ⇒-rev ↑ ⇒-rev
          ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩ · 42 ⟨ ℕ↦★ ⟩) ⟨ ★↦ℕ ⟩)

M₃ = (λx. x ·
        (λx. (λy. y · x ⟨ X↦★ ⟩) ↑ ⇒-rev
          ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩ · 42 ⟨ ℕ↦ℕ ⟩) ⟨ ★↦ℕ ⟩)

N₃ = (λx. x ·
        (λx. (λy. y · x ⟨ X′↦★ ⟩) ↑ ⇒-rev ↑ ⇒-rev
          ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩ · 42 ⟨ ℕ↦★ ⟩) ⟨ ★↦ℕ ⟩)
```

Here `N₃ = N₂`. The fully normalized reduction-imprecision square is:

```text
M₂  ⊑[ checkpoint₁-world ]  N₂
 │                              │
 │ one source step, bind ℕ      │ 0 target steps
 ▼                              ▼
M₃  ⊑[ checkpoint₃-world ]  N₃
```

The source step is the checked whole-term reduction
`more-checkpoint₂↠₃`; it performs the source runtime allocation with store
change `bind ℕ`. The right edge is the checked reflexive
`less-checkpoint₂↠₃`. The two horizontal edges are the checked
`checkpoint₂-imprecision` and `checkpoint₃-imprecision` derivations.

Before allocation, the relevant path through the checkpoint-2 CTI derivation
is:

```text
[]
  target alpha reveal:  Z ↔ Y′
[Z ↔ Y′]
  target beta reveal:   Z ↔ X′
[Z ↔ X′, Z ↔ Y′]
```

After `bind ℕ`, the source reduction exposes the source alpha reveal. The
post-allocation world first aligns the new source pivot `X` with target alpha
`Y′` using an `alignment-only` rebase. The alpha CTI node is then the existing
paired `reveal⊑reveal²`, which opens no frame. The remaining target-only beta
reveal uses an `open-frame` rebase:

```text
[]
  alpha alignment-only: X aligns with Y′       (scan unchanged)
[]
  paired alpha reveal: X and Y′                 (scan unchanged)
[]
  target beta reveal: X ↔ X′
[X ↔ X′]
```

Thus allocation discharges the old alpha frame by changing its semantic role
at the newly exposed paired boundary; it does not pop a raw pivot pair after
the fact and it does not erase the beta frame.

## Generated post-allocation Imp Ladder

The following is the exact value of
`CTIGammaCarriedFramePacket.checkpoint₃-ladder`, generated by
`impLadderDefault` from the live trusted `checkpoint₃-imprecision` derivation.

```text
⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩
source term                A        ηᴸA      ⊑ costs                            ηᴿB      B         target term
─────────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ────────  ─────────────────────────
□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         □₁ · □₂
├ λx. □                    (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □
│ x                        ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         │ x
└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩
  □₁ · □₂                  ★        ★        ★⊑★                                ★        ★           □₁ · □₂
  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩
  │ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev
  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase         (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev
  │ λx. □                  (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                         (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □
  │ □₁ · □₂                ★        ★        ★⊑★                                ★        ★           │ □₁ · □₂
  │ ├ λy. □                (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □
  │ │ y                    ★        ★        ★⊑★                                ★        ★           │ │ y
  │ └ □ ⟨ X↦★ ⟩            ★        ★        ★⊑★                                ★        ★           │ └ □ ⟨ X′↦★ ⟩
  │   x                    X        Y        Y ≈ Y                              Y        X′          │   x
  └ □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ι⊑★                                ★        ★           └ □ ⟨ ℕ↦★ ⟩
    42                     ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ             42
```

The `matched reveal partner` row is the discharged alpha boundary. The next
row is the sole surviving target-only beta boundary and therefore the sole
`open-frame` rebase. The ladder's world snapshot shows the alignment-only
effect: source `X` and target `Y′` both occupy center `Z`, while the beta
rebase moves the recursive comparison to the center occupied by `X′`.

## Required non-CTI allocation API

No new CTI constructor is needed for discharge. The existing paired reveal
rule performs the post-allocation alpha comparison. The migration does need a
role-aware source-allocation world-evolution operation whose result may append
the required checked `alignment-only` rebase in the same `bind ℕ` evolution
edge.
The present `evolution-bind-left` stops at the raw bind world, while the
trusted bottom horizontal edge lives in that bind world followed by the alpha
alignment change. Adding a separate zero-store evolution edge would put an
extra `keep` into the reduction's store-change list, so it would be the wrong
shape.

The minimal semantic requirement is:

```agda
evolution-bind-left-alignment :
  -- the ordinary source bind premises
  ...
  -- one alignment-only pivot update in the bound world
  → WorldEvolution
       {W = γ}
       {W′ = (γ ▻ᶜ bind-left-changeᶜ ...)
          ▻ᶜ rebase-source-changeᶜ
            Xᴸ Xᴿ (alignment-only boundary) ok represented}
       (bind-ctx eqᴸ) keep-ctx
```

If a trusted example requires several simultaneous discharged alignments, the
last premise should generalize to a genuine list of checked alignment changes;
it should not become an untyped arbitrary-world suffix. For the concrete TIR
gate above, one alignment is exact.

Likewise, replacing the current `sourceRebaseCountᶜ γ ≡ 0` gates by only
`openFramesᶜ γ ≡ []` is not mechanical. Those proofs currently exploit the
absence of every source-embedding change. Each such gate must either be proved
stable under `AlignmentBoundaryᶜ` or retain a stronger no-rebase premise. The
role tag alone is not evidence for that stability.

## Permission conclusion

No authorization to edit `CastTermImprecision.agda` is requested: the complete
before and after rules above are identical. The supporting checked role,
`openFramesᶜ` scan, open-only `SourceRebaseᶜ` constructor, and source-allocation
alignment evolution belong in `World`, `SourceRebase`, and `WorldEvolution`.
If implementation later reveals that a CTI constructor itself must change, a
new permission packet must show that exact additional before/after rule and a
trusted obstruction; this audit does not pre-authorize it.

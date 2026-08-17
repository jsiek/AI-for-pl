# T11 meet point: boundary-kind adapters

Purpose: draft the adapters from a structural bottom-up
`StructuralCatchupRightResult` to the boundary-kind-indexed
`ValueCatchupResult` surface.

## Before context

The fixed top-down surface indexes the result by:

```agda
data CatchupBoundaryKind : Set where
  same-boundary : CatchupBoundaryKind
  source-reveal-boundary : CatchupBoundaryKind
  source-conceal-boundary : CatchupBoundaryKind
  target-reveal-boundary : CatchupBoundaryKind
  target-conceal-boundary : CatchupBoundaryKind
```

The boundary constructors carry either no rebase, a forward tag rebase,
or a reverse tag rebase:

```agda
boundary-refl :
  CatchupBoundary same-boundary nothing nothing W W

boundary-source-reveal :
  ImpEnvMono W Wᵖ →
  TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ? →
  CatchupBoundary source-reveal-boundary Xᴸ? Xᴿ? W Wᵖ

boundary-source-conceal :
  ImpEnvMono W Wᵖ →
  TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ? →
  CatchupBoundary source-conceal-boundary Xᴸ? Xᴿ? W Wᵖ

boundary-target-reveal :
  ImpEnvMono W Wᵖ →
  TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ? →
  CatchupBoundary target-reveal-boundary Xᴸ? Xᴿ? W Wᵖ

boundary-target-conceal :
  ImpEnvMono W Wᵖ →
  TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ? →
  CatchupBoundary target-conceal-boundary Xᴸ? Xᴿ? W Wᵖ
```

The adapters below intentionally take the structural bottom-up result,
because the adapter must reuse both `structural-ext` and the final
empty-context relation from that result.

## Shared helper statements

Boundary packing needs a structural evolution embedding and two
boundary transport helpers.

```agda
StructuralRightParkedEvolveᵀ : Set₁
StructuralRightParkedEvolveᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ParkedWorld W
  → StructuralWorldExtendᴿ χsᴿ W W′
  → ParkedEvolve [] χsᴿ W W′
```

The existing `structural-tag-rebase-atᴸ-pullback` has the reverse
orientation needed for conceal boundaries:

```agda
structural-tag-rebase-atᴸ-pullback :
  (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′) →
  (rb : TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?) →
  StructuralTagRebaseAtᴸPullbackResult planᵖ rb
```

Reveal boundaries need the forward orientation.  Candidate statement:

```agda
record StructuralForwardTagRebaseAtᴸPullbackResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    (rb : TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?) : Set₁ where
  field
    W′ : World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : TagRebaseAtᴸ W′ Wᵖ′ Xᴸ?
      (mapPivotChanges χs Xᴿ?)
    post-mono : ImpEnvMono W Wᵖ → ImpEnvMono W′ Wᵖ′

structural-forward-tag-rebase-atᴸ-pullback :
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    {W : World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → StructuralForwardTagRebaseAtᴸPullbackResult planᵖ rb
```

This helper should be assembled by cases on `TagRebaseAtᴸ`, using
`structural-rebase-atᴸ-pullback` for the `nothing` source-only cases
and `structural-rebase-at-pullback` for the paired-pivot case.  The
paired case also needs the small definitional bridge:

```agda
mapPivotChanges-just : ∀ {Δᴿ Δᴿ′}
    (χs : StoreChanges Δᴿ Δᴿ′) (Xᴿ : TyVar Δᴿ)
  → mapPivotChanges χs (just Xᴿ) ≡ just (mapVarChanges χs Xᴿ)
```

## Kind-specific adapter statements

Same boundary needs no rebase transport.  The outer and premise worlds
are the same, so both structural extensions are the child
`structural-ext`.

```agda
same-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → StructuralCatchupRightResult W [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = W} {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {V = V} {M′ = M′} {A = A} {B = B}
```

Source reveal uses the new forward tag pullback on the child plan:
`planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′` and
`rb : TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?` produce `outer-plan` and
`TagRebaseAtᴸ W′ Wᵖ′ Xᴸ? (mapPivotChanges χs Xᴿ?)`.

```agda
source-reveal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : ImpEnvMono W Wᵖ)
  → (rb : TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-reveal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
```

Target reveal has the same boundary-level transport as source reveal.
If the caller starts from a target-specific `RebaseAtᴿ`, first convert
it with `toTagRebaseAtᴿ`; the adapter itself only sees the generic
boundary tag rebase.

```agda
target-reveal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : ImpEnvMono W Wᵖ)
  → (rb : TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = target-reveal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
```

Source conceal uses the existing reverse-oriented tag pullback:
`planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′` and
`rb : TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?` produce `outer-plan` and
`TagRebaseAtᴸ Wᵖ′ W′ Xᴸ? (mapPivotChanges χs Xᴿ?)`.

```agda
source-conceal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : ImpEnvMono W Wᵖ)
  → (rb : TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-conceal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
```

Target conceal is identical at the boundary layer.  If the caller
starts from a target-specific reverse `RebaseAtᴿ`, first convert it
with `toTagRebaseAtᴿ`; this adapter consumes the generic boundary
shape.

```agda
target-conceal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : ImpEnvMono W Wᵖ)
  → (rb : TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = target-conceal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
```

## Transport summary

Same boundary: no rebase transport; use `boundary-refl`, `refl` for
`nothing ≡ mapPivotChanges χs nothing`, and the child plan twice.

Source reveal and target reveal: use the proposed
`structural-forward-tag-rebase-atᴸ-pullback`; package the result with
`boundary-source-reveal (post-mono mono) post-rebase` or
`boundary-target-reveal (post-mono mono) post-rebase`.

Source conceal and target conceal: use existing
`structural-tag-rebase-atᴸ-pullback`; package the result with
`boundary-source-conceal (post-mono mono) post-rebase` or
`boundary-target-conceal (post-mono mono) post-rebase`.

All five adapters pack:

```agda
Xᴿ′? = mapPivotChanges χs Xᴿ?
pivot equality = refl
post reduction = StructuralCatchupRightResult.post-reduction child
final value = StructuralCatchupRightResult.final-value child
parked evolution = structural-right-parked-evolve parked outer-plan
premise structural plan = StructuralCatchupRightResult.structural-ext child
final relation = StructuralCatchupRightResult.final-relation child
```

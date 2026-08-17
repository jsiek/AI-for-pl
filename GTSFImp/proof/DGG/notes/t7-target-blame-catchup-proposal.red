T7 TargetBlameCatchup proposal

Current checked partial state:

  AGDA_DIR=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda-home \
    agda proof/DGG/TargetBlameCatchupProof.agda

checks.  The partial module exports:

  target-blame-catchup-source-blame
  source-cast-blame-catchup
  source-reveal-blame-catchup
  source-conceal-blame-catchup
  source-type-app-blame-catchup

These pieces cover the no-op `blame⊑²` base case and the non-inductive
replay from a child trace `M —↠ blame` to wrapper traces such as
`M ⟨ c ⟩ —↠ blame`, `M ↑ c —↠ blame`, and
`M ⦂∀ C [ A ] —↠ blame`.

Current blocker:

The full `TargetBlameCatchupᵀ` proof is a structural inversion over
`W ∣ [] ⊢² M ⊑ blame ∶ p`.  Two genuinely major surfaces are needed before the
remaining branches should be implemented.

1. Value-to-target-blame exclusion

Before context:

`TargetBlameCatchupProof.agda` reaches the source-only value-introduction
branches:

  CTI2.Λ⊑² nv z∈A lift vV target⊢ prem q
  CTI2.Λ⊑²-smart-comma nv z∈A lift smart vV target⊢ prem q

with `prem : Wᵖ ∣ [] ⊢² V ⊑ blame ∶ p` and `vV : Value V`.
The fixed catch-up surface cannot recurse here because these premise worlds
are not necessarily `ParkedWorld`, and operationally these branches must be
refuted rather than replayed: `Λ V` is a value.

Proposed new Def-level surface:

  module proof.DGG.TargetBlameValueExclusionDef where

  open import Data.Empty using (⊥)
  open import Types using (Ty)
  open import CastTerms using (Term; Value; blame)
  import proof.DGG.CastTermImprecision2 as CTI2
  open CTI2 using
    (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

  TargetValueBlameExclusionᵀ : Set
  TargetValueBlameExclusionᵀ =
    ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {V : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
    → Value V
    → W ∣ γ ⊢² V ⊑ blame ∶ p
    → ⊥

After context:

`TargetBlameCatchupProof.agda` imports the completed theorem and closes:

  target-blame-catchup-under-boundary parked boundary
      (CTI2.Λ⊑² nv z∈A lift vV target⊢ prem q) =
    ⊥-elim (target-value-blame-exclusion vV prem)

and similarly for `Λ⊑²-smart-comma`.

This proof is an induction over `⊢²`, so it is intentionally only proposed
here.

2. Source-rebase boundary stack for target blame

Before context:

The fixed `TargetBlameCatchupᵀ` surface has:

  ParkedWorld W
  W ∣ [] ⊢² M ⊑ blame ∶ p

The `reveal⊑²` and `conceal⊑²` branches expose premises at rebased worlds:

  reveal⊑² :
    W₁ ∣ γ₁ ⊢² M ⊑ blame ∶ p₁
    where ImpEnvMono W₀ W₁ and RebaseAtᴸ W₀ W₁ Xᴸ?

  conceal⊑² :
    W₁ ∣ γ₁ ⊢² M ⊑ blame ∶ p₁
    where ImpEnvMono W₀ W₁ and TagRebaseAtᴸ W₁ W₀ Xᴸ? Xᴿ?

With outer `γ = []`, `SameCtx [] γ₁` inverts to `same-[]`, so the premise
context is still empty.  The premise world, however, is not known parked.

Proposed new Def-level surface:

  module proof.DGG.TargetBlameBoundaryDef where

  open import Data.List using ([])
  open import Data.Product using (_×_; Σ-syntax)
  open import Data.Maybe using (Maybe)
  open import Types using (Ty; TyCtx; TyVar)
  open import CastTerms using (Term; blame)
  open import Reduction using (StoreChanges; _—↠[_]_)
  import proof.DGG.CastTermImprecision2 as CTI2
  open import proof.DGG.Parked.ParkedWorldDef
    using (ParkedWorld; ParkedEvolve)
  open CTI2 using
    ( World
    ; ImpEnvMono
    ; TagRebaseAtᴸ
    ; _⊑ᵂ⟨_⟩_
    ; _∣_⊢²_⊑_∶_
    )

  data TargetBlameBoundary {Δᴸ Δᴿ Δ}
      (W : World Δᴸ Δᴿ Δ) :
      World Δᴸ Δᴿ Δ → Set where

    target-blame-boundary-refl :
      TargetBlameBoundary W W

    target-blame-boundary-source-reveal : ∀ {W₀ W₁ Xᴸ? Xᴿ?}
      → TargetBlameBoundary W W₀
      → ImpEnvMono W₀ W₁
      → TagRebaseAtᴸ W₀ W₁ Xᴸ? Xᴿ?
      → TargetBlameBoundary W W₁

    target-blame-boundary-source-conceal : ∀ {W₀ W₁ Xᴸ? Xᴿ?}
      → TargetBlameBoundary W W₀
      → ImpEnvMono W₀ W₁
      → TagRebaseAtᴸ W₁ W₀ Xᴸ? Xᴿ?
      → TargetBlameBoundary W W₁

  TargetBlameCatchupUnderBoundaryᵀ : Set
  TargetBlameCatchupUnderBoundaryᵀ =
    ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
    → ParkedWorld W
    → TargetBlameBoundary W Wᵖ
    → Wᵖ ∣ [] ⊢² M ⊑ blame ∶ p
    → Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
        (M —↠[ χsᴸ ] blame) ×
        ParkedEvolve χsᴸ Reduction.[] W W′

After context:

The fixed theorem remains unchanged and is just the same-boundary adapter:

  target-blame-catchup : TargetBlameCatchupᵀ
  target-blame-catchup parked rel =
    target-blame-catchup-under-boundary
      parked target-blame-boundary-refl rel

`reveal⊑²` recurses under
`target-blame-boundary-source-reveal boundary mono (toTagRebaseAtᴸ rb)`,
then uses the checked `source-reveal-blame-catchup` replay helper.

`conceal⊑²` recurses under
`target-blame-boundary-source-conceal boundary mono rb`,
then uses the checked `source-conceal-blame-catchup` replay helper.

This is a new Def-level surface and the proof is an induction over `⊢²`, so
it is intentionally only proposed here.

Target-blame CTI2 branch table:

  blame⊑²
    Status: checked base case.
    Reason: source is already `blame`; return `[]`, `↠-refl`, `evolve-refl`.

  cast⊑²
    Status: replay helper checked, full branch waits for boundary worker.
    Plan: recurse on the child at the same boundary, then use
    `source-cast-blame-catchup`.

  •⊑²
    Status: replay helper checked, full branch waits for boundary worker.
    Plan: recurse on the child at the same boundary, then use
    `source-type-app-blame-catchup`.

  reveal⊑²
    Status: blocked by proposed `TargetBlameBoundary`.
    Plan: extend the boundary with the source-reveal rebase, recurse on the
    premise, then use `source-reveal-blame-catchup`.

  conceal⊑²
    Status: blocked by proposed `TargetBlameBoundary`.
    Plan: extend the boundary with the source-conceal rebase, recurse on the
    premise, then use `source-conceal-blame-catchup`.

  Λ⊑²
    Status: blocked by proposed `TargetValueBlameExclusionᵀ`.
    Plan: refute `Value V` with `prem : Wᵖ ∣ [] ⊢² V ⊑ blame ∶ p`.

  Λ⊑²-smart-comma
    Status: blocked by proposed `TargetValueBlameExclusionᵀ`.
    Plan: same as `Λ⊑²`.

  x⊑x², ƛ⊑ƛ², ·⊑·², Λ⊑Λ², •⊑•², κ⊑κ², cast⊑cast²,
  ⊑cast², ⊑reveal², ⊑conceal², reveal⊑reveal²,
  conceal⊑conceal², packaged-seal-star², ⊕⊑⊕²
    Status: target syntax cannot unify with top-level `blame` or, for
    `x⊑x²`, the empty context has no variable witness.

module proof.DGG.SimSourceCastValuesProof where

-- File Charter:
--   * Implements the direct source-only ordinary-cast value rows.
--   * Names the remaining source-side cast rebuild obligations as residual
--     inputs instead of adding new CTI2 or type-imprecision lemmas.
--   * Keeps the β-inst row as a named residual.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types using (Ty; TyCtx)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using
  ( StoreChange
  ; applyTy
  ; _—→[_]_
  ; pure-step
  ; β-id
  ; ground
  ; expand
  ; tag-untag
  ; tag-untag-bad
  ; blame-bot-intro
  ; blame-⟨⟩
  ; β-inst
  ; ξ-⟨⟩
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open CTI2 using
  ( World
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve; evolve-refl; evolve-keepᴸ)
open import proof.DGG.SimSourceCastValuesDef
  using (SimSourceCastValuesᵀ)
open import proof.Reduction.ValueIrreducibleProof
  using (value-no-step)


SourceCastRel : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ [] ⊢² M ⊑ M′ ∶ p → Set
SourceCastRel (CTI2.cast⊑² _ _ _) = ⊤
SourceCastRel _ = Data.Empty.⊥

GroundStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
GroundStep (pure-step (ground _ _)) = ⊤
GroundStep _ = Data.Empty.⊥

ExpandStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
ExpandStep (pure-step (expand _ _)) = ⊤
ExpandStep _ = Data.Empty.⊥

TagUntagStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
TagUntagStep (pure-step (tag-untag _)) = ⊤
TagUntagStep _ = Data.Empty.⊥

βInstStep : ∀ {Δ Δ′ : TyCtx}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N → Set
βInstStep (β-inst _ _) = ⊤
βInstStep _ = Data.Empty.⊥


record SimSourceCastValuesResiduals : Set where
  field
    source-ground-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {C : Ty Δᴿ} {μ : Env∼ Δᴸ}
        {c : μ ⊢ A ∼ B} {q : B ⊑ᵂ⟨ W ⟩ C}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ∶ q)
      → SourceCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → GroundStep step
      → Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ C ]
          ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ V′ ∶ r)

    source-expand-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {C : Ty Δᴿ} {μ : Env∼ Δᴸ}
        {c : μ ⊢ A ∼ B} {q : B ⊑ᵂ⟨ W ⟩ C}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ∶ q)
      → SourceCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → ExpandStep step
      → Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ C ]
          ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ V′ ∶ r)

    source-tag-untag-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {C : Ty Δᴿ} {μ : Env∼ Δᴸ}
        {c : μ ⊢ A ∼ B} {q : B ⊑ᵂ⟨ W ⟩ C}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ∶ q)
      → SourceCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → TagUntagStep step
      → Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ C ]
          ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ V′ ∶ r)

    source-β-inst-row : ∀ {Δᴸ Δᴿ Δ Δᴸ′}
        {W : World Δᴸ Δᴿ Δ} {χᴸ : StoreChange Δᴸ Δᴸ′}
        {V : Term Δᴸ} {V′ : Term Δᴿ} {N : Term Δᴸ′}
        {A B : Ty Δᴸ} {C : Ty Δᴿ} {μ : Env∼ Δᴸ}
        {c : μ ⊢ A ∼ B} {q : B ⊑ᵂ⟨ W ⟩ C}
      → ParkedWorld W
      → (rel : W ∣ [] ⊢² V ⟨ c ⟩ ⊑ V′ ∶ q)
      → SourceCastRel rel
      → Value V
      → Value V′
      → (step : V ⟨ c ⟩ —→[ χᴸ ] N)
      → βInstStep step
      → Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
        Σ[ r ∈ applyTy χᴸ B ⊑ᵂ⟨ W′ ⟩ C ]
          ParkedEvolve (χᴸ ∷ˢ []ˢ) []ˢ W W′ ×
          (W′ ∣ [] ⊢² N ⊑ V′ ∶ r)


sim-source-cast-values-with :
  SimSourceCastValuesResiduals → SimSourceCastValuesᵀ
sim-source-cast-values-with residuals {world = W} {V = V} {V′ = V′}
    {p = p} parked rel q vV vV′ (pure-step (β-id _)) =
  _ , W , q , evolve-keepᴸ evolve-refl ,
  subst (λ r → W ∣ [] ⊢² V ⊑ V′ ∶ r)
    (PI.⊑-unique p q) rel
sim-source-cast-values-with residuals {c = c} parked rel q vV vV′
    step@(pure-step (ground _ _)) =
  SimSourceCastValuesResiduals.source-ground-row residuals
    parked (CTI2.cast⊑² c rel q) tt vV vV′ step tt
sim-source-cast-values-with residuals {c = c} parked rel q vV vV′
    step@(pure-step (expand _ _)) =
  SimSourceCastValuesResiduals.source-expand-row residuals
    parked (CTI2.cast⊑² c rel q) tt vV vV′ step tt
sim-source-cast-values-with residuals {c = c} parked rel q vV vV′
    step@(pure-step (tag-untag _)) =
  SimSourceCastValuesResiduals.source-tag-untag-row residuals
    parked (CTI2.cast⊑² c rel q) tt vV vV′ step tt
sim-source-cast-values-with residuals {world = W} {V = V} {V′ = V′}
    {c = c} parked rel q vV vV′
    (pure-step (tag-untag-bad _ _)) =
  _ , W , q , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑² (CTI2T.target-typing² (CTI2.cast⊑² c rel q)) q
sim-source-cast-values-with residuals {world = W} {V = V} {V′ = V′}
    {c = c} parked rel q vV vV′
    (pure-step (blame-bot-intro _)) =
  _ , W , q , evolve-keepᴸ evolve-refl ,
  CTI2.blame⊑² (CTI2T.target-typing² (CTI2.cast⊑² c rel q)) q
sim-source-cast-values-with residuals parked rel q () vV′
    (pure-step blame-⟨⟩)
sim-source-cast-values-with residuals {c = c} parked rel q vV vV′
    step@(β-inst _ _) =
  SimSourceCastValuesResiduals.source-β-inst-row residuals
    parked (CTI2.cast⊑² c rel q) tt vV vV′ step tt
sim-source-cast-values-with residuals parked rel q vV vV′
    (ξ-⟨⟩ step _) =
  ⊥-elim (value-no-step vV step)

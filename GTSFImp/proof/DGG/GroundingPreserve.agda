module proof.DGG.GroundingPreserve where

-- File Charter:
--   * States the LG-2 preservation surface for the S-OCC discipline.
--   * Proves allocation atomicity for the live β-inst and β-gen reduction
--     constructors: the right-only target bind and the fresh-name partner
--     conversion are produced in the same step.
--   * Re-exports the occupancy-evolution lemmas used by the catch-up stack
--     and states the higher-order knot that LG-3/M7 must instantiate for the
--     full related-reduction simulation.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (TyCtx; Ty; TyVar; NonVar; _∈ᵗ_; ＇_; ★; ⇑ᵗ)
open import Consistency using
  (Env∼; _⊢_∼_; instᵐ; genᵐ; inst_; gen_; ↑ᶜ_; close-instᶜ;
   toRenameᵗ)
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using
  (bind; applyBody; _—→[_]_; β-inst; β-gen)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Occupancy public using
  ( initial-every-center-occupiedᴼ
  ; initial-no-see-through-emptyᴼ
  ; liftWorldLeft-fresh-no-targetᴼ
  ; liftWorldLeft-old-occupiedᴼ
  ; liftWorldLeft-old-no-targetᴼ
  ; liftWorldLeft-old-no-target-at-sourceᴼ
  ; liftWorldBoth-fresh-occupiedᴼ
  ; liftWorldBoth-old-occupiedᴼ
  ; liftWorldBoth-old-no-targetᴼ
  ; leftOnly-fresh-no-targetᴼ
  ; leftOnly-old-occupiedᴼ
  ; leftOnly-old-no-targetᴼ
  ; rightOnly-new-target-occupiedᴼ
  ; rightOnly-old-occupiedᴼ
  ; rightOnly-old-no-targetᴼ
  ; rightOnly-old-no-target-at-sourceᴼ
  ; bothBind-new-target-occupiedᴼ
  ; bothBind-old-occupiedᴼ
  ; bothBind-old-no-targetᴼ
  ; rebase-occupied-forwardᴼ
  ; rebase-occupied-backwardᴼ
  ; rebase-no-target-forwardᴼ
  ; rebase-no-target-backwardᴼ
  ; rebaseᴸ-no-target-forwardᴼ
  ; rebaseᴿ-no-target-forwardᴼ
  ; tag-rebase-no-target-forwardᴼ
  ; decay-no-target-forwardᴼ
  ; decay-occupied-forwardᴼ
  ; decay-occupied-backwardᴼ
  ; decay-no-target-at-source-forwardᴼ
  ; target-insert-occupied-forwardᴼ
  ; target-insert-no-target-forwardᴼ
  ; target-insert-no-target-at-sourceᴼ
  ; smartFreshBehind-fresh-no-targetᴼ
  ; smartAliasMerge-fresh-occupiedᴼ
  ; smartFreshBehind-old-no-target-at-sourceᴼ
  ; smartAliasMerge-old-no-target-at-sourceᴼ
  ; smartCommaLift-old-no-target-at-sourceᴼ
  ; β-inst-allocation-occupies-targetᴼ
  ; β-gen-allocation-occupies-targetᴼ
  ; source-only-runtime-cell-remains-unoccupiedᴼ
  )

------------------------------------------------------------------------
-- Fresh target partner created by allocation steps
------------------------------------------------------------------------

data FreshPartnerAt0 {Δ : TyCtx}
    (R B : Ty (suc Δ)) : Term (suc Δ) → Set where
  partner-reveal : ∀ {M}
      -----------------------------------------
    → FreshPartnerAt0 R B (M ↑ 〖 zero , R ↑ B 〗)

  partner-reveal-cast : ∀ {M ν C D}
      {c : ν ⊢ C ∼ D}
      -------------------------------------------------
    → FreshPartnerAt0 R B ((M ↑ 〖 zero , R ↑ B 〗) ⟨ c ⟩)

β-inst-allocation-atomic : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {μ : Env∼ Δᴿ}
    {A : Ty (suc Δᴿ)} {B : Ty Δᴿ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
  → (vV : Value V)
  → (B≢★ : B ≢ ★)
  → CTI2.Occupied (CTI2.rightOnlyWorld W ★) zero ×
    Σ[ N ∈ Term (suc Δᴿ) ]
      ((V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ] N)
       × FreshPartnerAt0 ★ A N)
β-inst-allocation-atomic {W = W} {V = V} {A = A} {c = c}
    vV B≢★ =
  β-inst-allocation-occupies-targetᴼ {W = W} ,
  (((⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ zero ])
      ↑ 〖 zero , ★ ↑ A 〗)
      ⟨ ↑ᶜ (close-instᶜ c) ⟩) ,
  β-inst vV B≢★ ,
  partner-reveal-cast

β-gen-allocation-atomic : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {μ : Env∼ Δᴿ}
    {A C : Ty Δᴿ} {B : Ty (suc Δᴿ)}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
  → (vV : Value V)
  → (A≢★ : A ≢ ★)
  → (safe : GenSafe c)
  → CTI2.Occupied (CTI2.rightOnlyWorld W C) zero ×
    Σ[ N ∈ Term (suc Δᴿ) ]
      (((V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ] N)
       × FreshPartnerAt0 (⇑ᵗ C) B N)
β-gen-allocation-atomic {W = W} {V = V} {A = A} {C = C}
    {B = B} {c = c} vV A≢★ safe =
  β-gen-allocation-occupies-targetᴼ {W = W} C ,
  (⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 zero , ⇑ᵗ C ↑ B 〗) ,
  β-gen vV A≢★ safe ,
  partner-reveal

------------------------------------------------------------------------
-- No see-through at occupied cells
------------------------------------------------------------------------

occupied-see-through-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (X : TyVar Δᴸ)
  → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X)
  → CTI2.NoTargetOccupantAtSource W X
  → ⊥
occupied-see-through-empty X occupied no-target =
  no-target occupied

record RelatedReductionGroundingKnot : Set₁ where
  field
    preserves-old-occupied-see-through-empty :
      ∀ {Δᴸ Δᴿ Δ}
        {W W′ : CTI2.World Δᴸ Δᴿ Δ}
      → (∀ X
          → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X)
          → CTI2.Occupied W′ (toRenameᵗ (CTI2.ηᴸʷ W′) X))
      → (X : TyVar Δᴸ)
      → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X)
      → CTI2.NoTargetOccupantAtSource W′ X
      → ⊥

    β-inst-new-cell-grounded :
      ∀ {Δᴸ Δᴿ Δ}
        {W : CTI2.World Δᴸ Δᴿ Δ}
        {V : Term Δᴿ} {μ : Env∼ Δᴿ}
        {A : Ty (suc Δᴿ)} {B : Ty Δᴿ}
        {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
        ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
      → (vV : Value V)
      → (B≢★ : B ≢ ★)
      → CTI2.Occupied (CTI2.rightOnlyWorld W ★) zero ×
        Σ[ N ∈ Term (suc Δᴿ) ]
          ((V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ] N)
           × FreshPartnerAt0 ★ A N)

    β-gen-new-cell-grounded :
      ∀ {Δᴸ Δᴿ Δ}
        {W : CTI2.World Δᴸ Δᴿ Δ}
        {V : Term Δᴿ} {μ : Env∼ Δᴿ}
        {A C : Ty Δᴿ} {B : Ty (suc Δᴿ)}
        {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
        ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
      → (vV : Value V)
      → (A≢★ : A ≢ ★)
      → (safe : GenSafe c)
      → CTI2.Occupied (CTI2.rightOnlyWorld W C) zero ×
        Σ[ N ∈ Term (suc Δᴿ) ]
          (((V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ] N)
           × FreshPartnerAt0 (⇑ᵗ C) B N)

grounding-preservation-knot : RelatedReductionGroundingKnot
grounding-preservation-knot = record
  { preserves-old-occupied-see-through-empty =
      λ occ-at-source-forward X occupied no-target′ →
        no-target′ (occ-at-source-forward X occupied)
  ; β-inst-new-cell-grounded =
      λ {Δᴸ} {Δᴿ} {Δ} {W} {V} {μ} {A} {B} {c}
          ⦃ Anv ⦄ ⦃ z∈A ⦄ vV B≢★ →
        β-inst-allocation-atomic {W = W} {V = V} {μ = μ}
          {A = A} {B = B} {c = c} ⦃ Anv = Anv ⦄
          ⦃ z∈A = z∈A ⦄ vV B≢★
  ; β-gen-new-cell-grounded =
      λ {Δᴸ} {Δᴿ} {Δ} {W} {V} {μ} {A} {C} {B} {c}
          ⦃ Bnv ⦄ ⦃ z∈B ⦄ vV A≢★ safe →
        β-gen-allocation-atomic {W = W} {V = V} {μ = μ}
          {A = A} {C = C} {B = B} {c = c} ⦃ Bnv = Bnv ⦄
          ⦃ z∈B = z∈B ⦄ vV A≢★ safe
  }

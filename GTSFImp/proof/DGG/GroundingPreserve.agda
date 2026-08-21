module proof.DGG.GroundingPreserve where

-- File Charter:
--   * States the LG-2 preservation surface for the S-OCC discipline.
--   * Proves allocation atomicity for the live β-inst and β-gen reduction
--     constructors: the right-only target bind and the fresh-name partner
--     conversion are produced in the same step.
--   * Imports the allocation occupancy lemmas used by the atomicity surface
--     and states the higher-order knot that LG-3/M7 must instantiate for the
--     full related-reduction simulation.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (TyCtx; Ty; TyVar; NonVar; _∈ᵗ_; ＇_; ★; ⇑ᵗ)
open import TyStore using (lookupStore)
open import Imprecision using (X⊑★)
open import Consistency using
  (Env∼; _⊢_∼_; instᵐ; genᵐ; inst_; gen_; ↑ᶜ_; close-instᶜ;
   toRenameᵗ)
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using
  (bind; applyBody; _—→[_]_; β-inst; β-gen)
import proof.DGG.CtxImp as CTI2
import proof.DGG.WorldInvariants as WI
open import proof.DGG.Occupancy using
  ( β-inst-allocation-occupies-targetᴼ
  ; β-gen-allocation-occupies-targetᴼ
  )

------------------------------------------------------------------------
-- Fresh target partner created by allocation steps
------------------------------------------------------------------------

-- Allocation exposes either a reveal at the fresh target cell or that reveal
-- followed by a top-level cast.

β-inst-allocation-atomic : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {μ : Env∼ Δᴿ}
    {A : Ty (suc Δᴿ)} {B : Ty Δᴿ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
  → (vV : Value V)
  → (B≢★ : B ≢ ★)
  → CTI2.Occupied (CTI2.rightOnlyWorld W ★ (inj₁ refl)) zero ×
    Σ[ N ∈ Term (suc Δᴿ) ]
      ((V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ] N)
       × ((Σ[ M ∈ Term (suc Δᴿ) ]
              N ≡ M ↑ 〖 zero , ★ ↑ A 〗)
          ⊎
          (Σ[ M ∈ Term (suc Δᴿ) ]
           Σ[ μ′ ∈ Env∼ (suc Δᴿ) ]
           Σ[ S ∈ Ty (suc Δᴿ) ]
           Σ[ T ∈ Ty (suc Δᴿ) ]
           Σ[ c′ ∈ (μ′ ⊢ S ∼ T) ]
              N ≡ (M ↑ 〖 zero , ★ ↑ A 〗) ⟨ c′ ⟩)))
β-inst-allocation-atomic {W = W} {V = V} {A = A} {c = c}
    vV B≢★ =
  β-inst-allocation-occupies-targetᴼ {W = W} ,
  (((⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ zero ])
      ↑ 〖 zero , ★ ↑ A 〗)
      ⟨ ↑ᶜ (close-instᶜ c) ⟩) ,
  β-inst vV B≢★ ,
  inj₂ (_ , _ , _ , _ , _ , refl)

β-gen-allocation-atomic : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {μ : Env∼ Δᴿ}
    {A C : Ty Δᴿ} {B : Ty (suc Δᴿ)}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
  → (vV : Value V)
  → (A≢★ : A ≢ ★)
  → (safe : GenSafe c)
  → (fresh : CTI2.RightBindFresh W C)
  → CTI2.Occupied (CTI2.rightOnlyWorld W C fresh) zero ×
    Σ[ N ∈ Term (suc Δᴿ) ]
      (((V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ] N)
       × ((Σ[ M ∈ Term (suc Δᴿ) ]
              N ≡ M ↑ 〖 zero , ⇑ᵗ C ↑ B 〗)
          ⊎
          (Σ[ M ∈ Term (suc Δᴿ) ]
           Σ[ μ′ ∈ Env∼ (suc Δᴿ) ]
           Σ[ S ∈ Ty (suc Δᴿ) ]
           Σ[ T ∈ Ty (suc Δᴿ) ]
           Σ[ c′ ∈ (μ′ ⊢ S ∼ T) ]
              N ≡ (M ↑ 〖 zero , ⇑ᵗ C ↑ B 〗) ⟨ c′ ⟩)))
β-gen-allocation-atomic {W = W} {V = V} {A = A} {C = C}
    {B = B} {c = c} vV A≢★ safe fresh =
  β-gen-allocation-occupies-targetᴼ {W = W} C fresh ,
  (⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 zero , ⇑ᵗ C ↑ B 〗) ,
  β-gen vV A≢★ safe ,
  inj₁ (_ , refl)

------------------------------------------------------------------------
-- No see-through at occupied cells
------------------------------------------------------------------------

occupied-see-through-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (X : TyVar Δᴸ)
  → WI.WorldInvariants W
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★
  → lookupStore (CTI2.sourceStoreʷ W) X ≡ ★
  → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X)
  → ⊥
occupied-see-through-empty {W = W} X inv mark entry occupied =
  WI.world-invariants-d17c-occupancy {W = W} {X = X}
    inv mark entry occupied

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
      → WI.WorldInvariants W′
      → CTI2.impEnvʷ W′ (toRenameᵗ (CTI2.ηᴸʷ W′) X) ≡ X⊑★
      → lookupStore (CTI2.sourceStoreʷ W′) X ≡ ★
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
      → CTI2.Occupied
          (CTI2.rightOnlyWorld W ★ (inj₁ refl)) zero ×
        Σ[ N ∈ Term (suc Δᴿ) ]
          ((V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ] N)
           × ((Σ[ M ∈ Term (suc Δᴿ) ]
                  N ≡ M ↑ 〖 zero , ★ ↑ A 〗)
              ⊎
              (Σ[ M ∈ Term (suc Δᴿ) ]
               Σ[ μ′ ∈ Env∼ (suc Δᴿ) ]
               Σ[ S ∈ Ty (suc Δᴿ) ]
               Σ[ T ∈ Ty (suc Δᴿ) ]
               Σ[ c′ ∈ (μ′ ⊢ S ∼ T) ]
                  N ≡ (M ↑ 〖 zero , ★ ↑ A 〗) ⟨ c′ ⟩)))

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
      → (fresh : CTI2.RightBindFresh W C)
      → CTI2.Occupied (CTI2.rightOnlyWorld W C fresh) zero ×
        Σ[ N ∈ Term (suc Δᴿ) ]
          (((V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ] N)
           × ((Σ[ M ∈ Term (suc Δᴿ) ]
                  N ≡ M ↑ 〖 zero , ⇑ᵗ C ↑ B 〗)
              ⊎
              (Σ[ M ∈ Term (suc Δᴿ) ]
               Σ[ μ′ ∈ Env∼ (suc Δᴿ) ]
               Σ[ S ∈ Ty (suc Δᴿ) ]
               Σ[ T ∈ Ty (suc Δᴿ) ]
               Σ[ c′ ∈ (μ′ ⊢ S ∼ T) ]
                  N ≡ (M ↑ 〖 zero , ⇑ᵗ C ↑ B 〗) ⟨ c′ ⟩)))

grounding-preservation-knot : RelatedReductionGroundingKnot
grounding-preservation-knot = record
  { preserves-old-occupied-see-through-empty =
      λ {Δᴸ} {Δᴿ} {Δ} {W} {W′}
          occ-at-source-forward X occupied inv′ mark′ entry′ →
        WI.world-invariants-d17c-occupancy {W = W′} {X = X}
          inv′ mark′ entry′
          (occ-at-source-forward X occupied)
  ; β-inst-new-cell-grounded =
      λ {Δᴸ} {Δᴿ} {Δ} {W} {V} {μ} {A} {B} {c}
          ⦃ Anv ⦄ ⦃ z∈A ⦄ vV B≢★ →
        β-inst-allocation-atomic {W = W} {V = V} {μ = μ}
          {A = A} {B = B} {c = c} ⦃ Anv = Anv ⦄
          ⦃ z∈A = z∈A ⦄ vV B≢★
  ; β-gen-new-cell-grounded =
      λ {Δᴸ} {Δᴿ} {Δ} {W} {V} {μ} {A} {C} {B} {c}
          ⦃ Bnv ⦄ ⦃ z∈B ⦄ vV A≢★ safe fresh →
        β-gen-allocation-atomic {W = W} {V = V} {μ = μ}
          {A = A} {C = C} {B = B} {c = c} ⦃ Bnv = Bnv ⦄
          ⦃ z∈B = z∈B ⦄ vV A≢★ safe fresh
  }

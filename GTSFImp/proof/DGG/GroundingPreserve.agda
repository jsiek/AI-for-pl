{-# OPTIONS --safe #-}

module proof.DGG.GroundingPreserve where

-- File Charter:
--   * Proves allocation atomicity for the live β-inst and β-gen reduction
--     constructors over the canonical complete-context world.
--   * Connects occupied dynamic source cells to the direct world invariant.
--   * Contains no theorem-bundle record or legacy world compatibility layer.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; ★; ⇑ᵗ)
open import TyStore using (lookupStore)
open import Imprecision using (X⊑★)
open import Consistency using
  (Env∼; _⊢_∼_; instᵐ; genᵐ; inst_; gen_; ↑ᶜ_; close-instᶜ;
   toRenameᵗ)
open import CastTerms using
  (Ctx; Term; Value; GenSafe; Δᵉ; Σᵉ; _,ˢ_; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using (bind; applyBody; _—→[_]_; β-inst; β-gen)
open import proof.DGG.World
open import proof.DGG.WorldInvariants
open import proof.DGG.Occupancy using (bindRight-fresh-occupied)


------------------------------------------------------------------------
-- Fresh target partner created by allocation steps
------------------------------------------------------------------------

-- Allocation exposes either a reveal at the fresh target cell or that reveal
-- followed by a top-level cast.  The first component says that the new target
-- variable directly occupies the new center position in the same world step.

β-inst-allocation-atomic : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴿ)} {μ : Env∼ (Δᵉ Γᴿ)}
    {A : Ty (suc (Δᵉ Γᴿ))} {B : Ty (Δᵉ Γᴿ)}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
  → (vV : Value V)
  → (B≢★ : B ≢ ★)
  → (Σ[ Y ∈ TyVar (suc (Δᵉ Γᴿ)) ]
      toRenameᵗ (ηᴿᶜ (bindRightᶜ γ ★ (inj₁ refl))) Y ≡ zero)
    × Σ[ N ∈ Term (suc (Δᵉ Γᴿ)) ]
      ((V ⟨ (inst c) B≢★ ⟩ —→[ bind ★ ] N)
       × ((Σ[ M ∈ Term (suc (Δᵉ Γᴿ)) ]
              N ≡ M ↑ 〖 zero , ★ ↑ A 〗)
          ⊎
          (Σ[ M ∈ Term (suc (Δᵉ Γᴿ)) ]
           Σ[ μ′ ∈ Env∼ (suc (Δᵉ Γᴿ)) ]
           Σ[ S ∈ Ty (suc (Δᵉ Γᴿ)) ]
           Σ[ T ∈ Ty (suc (Δᵉ Γᴿ)) ]
           Σ[ c′ ∈ (μ′ ⊢ S ∼ T) ]
              N ≡ (M ↑ 〖 zero , ★ ↑ A 〗) ⟨ c′ ⟩)))
β-inst-allocation-atomic {γ = γ} {V = V} {A = A} {c = c}
    vV B≢★ =
  bindRight-fresh-occupied {γ = γ} ★ (inj₁ refl) ,
  (((⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ zero ])
      ↑ 〖 zero , ★ ↑ A 〗)
      ⟨ ↑ᶜ (close-instᶜ c) ⟩) ,
  β-inst vV B≢★ ,
  inj₂ (_ , _ , _ , _ , _ , refl)


β-gen-allocation-atomic : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴿ)} {μ : Env∼ (Δᵉ Γᴿ)}
    {A C : Ty (Δᵉ Γᴿ)} {B : Ty (suc (Δᵉ Γᴿ))}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
  → (vV : Value V)
  → (A≢★ : A ≢ ★)
  → (safe : GenSafe c)
  → (fresh : RightBindFreshᶜ γ C)
  → (Σ[ Y ∈ TyVar (suc (Δᵉ Γᴿ)) ]
      toRenameᵗ (ηᴿᶜ (bindRightᶜ γ C fresh)) Y ≡ zero)
    × Σ[ N ∈ Term (suc (Δᵉ Γᴿ)) ]
      (((V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→[ bind C ] N)
       × ((Σ[ M ∈ Term (suc (Δᵉ Γᴿ)) ]
              N ≡ M ↑ 〖 zero , ⇑ᵗ C ↑ B 〗)
          ⊎
          (Σ[ M ∈ Term (suc (Δᵉ Γᴿ)) ]
           Σ[ μ′ ∈ Env∼ (suc (Δᵉ Γᴿ)) ]
           Σ[ S ∈ Ty (suc (Δᵉ Γᴿ)) ]
           Σ[ T ∈ Ty (suc (Δᵉ Γᴿ)) ]
           Σ[ c′ ∈ (μ′ ⊢ S ∼ T) ]
              N ≡ (M ↑ 〖 zero , ⇑ᵗ C ↑ B 〗) ⟨ c′ ⟩)))
β-gen-allocation-atomic {γ = γ} {V = V} {A = A} {C = C}
    {B = B} {c = c} vV A≢★ safe fresh =
  bindRight-fresh-occupied {γ = γ} C fresh ,
  (⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 zero , ⇑ᵗ C ↑ B 〗) ,
  β-gen vV A≢★ safe ,
  inj₁ (_ , refl)


------------------------------------------------------------------------
-- No see-through at occupied cells
------------------------------------------------------------------------

occupied-see-through-empty : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → sourceRebaseCountᶜ γ ≡ 0
  → (X : TyVar (Δᵉ Γᴸ))
  → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) X) ≡ X⊑★
  → lookupStore (Σᵉ Γᴸ) X ≡ ★
  → (Σ[ Y ∈ TyVar (Δᵉ Γᴿ) ]
      toRenameᵗ (ηᴿᶜ γ) Y ≡ toRenameᵗ (ηᴸᶜ γ) X)
  → ⊥
occupied-see-through-empty {γ = γ}
    no-rebase X mark entry (Y , aligned) =
  dynamicStarSourcesUnoccupiedᶜ
    (directInvariantsᶜ γ no-rebase) X mark entry Y aligned

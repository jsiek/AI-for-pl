module proof.DGG.SimBetaAllCastDef where

-- File Charter:
--   * States simulation of source universal-cast beta reduction.
--   * Packages target catch-up, target reduction, parked-world evolution,
--     and the final instantiated cast relation behind one interface.
--   * Contains no beta-all-cast simulation proof.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; `∀; _[_]ᵗ)
open import Consistency using
  (Env∼; extᵐ; _⊢_∼_; ∀ᶜ_; _[_]ᶜ)
open import CastTerms using (Term; Value; _⟨_⟩; _⦂∀_[_])
open import Reduction using
  ( StoreChanges
  ; applyTys
  ; keep
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimBetaAllCastᵀ : Set
SimBetaAllCastᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {μ : Env∼ Δᴸ}
    {A B : Ty (Nat.suc Δᴸ)} {C : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {c : extᵐ μ ⊢ A ∼ B}
    {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    {p∀ : `∀ B ⊑ᵂ⟨ world ⟩ `∀ C′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⟨ ∀ᶜ c ⟩ ⊑ M′ ∶ p∀
  → (q : C ⊑ᵂ⟨ world ⟩ A′)
  → (r : B [ C ]ᵗ ⊑ᵂ⟨ world ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → d ≡ c [ C ]ᶜ
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ s ∈ B [ C ]ᵗ ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (M′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (keep ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢² (V ⦂∀ A [ C ]) ⟨ d ⟩ ⊑ N′ ∶ s)

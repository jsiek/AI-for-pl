module proof.DGG.SimBetaGenDef where

-- File Charter:
--   * States simulation of source generalization beta reduction.
--   * Packages target catch-up, reduction, parked-world evolution, and the
--     final instantiated generalized-value relation behind one interface.
--   * Contains no generalization-beta simulation proof.

import Data.Fin as Fin
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types using
  (Ty; TyCtx; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ; _[_]ᵗ)
open import Consistency using
  (Env∼; genᵐ; _⊢_∼_; gen_)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using
  (Term; Value; GenSafe; ⇑ᵗᵐ; _⟨_⟩; _⦂∀_[_]; _↑_)
open import Reduction using
  ( StoreChanges
  ; applyTy
  ; applyTys
  ; bind
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimBetaGenᵀ : Set
SimBetaGenᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {M′ : Term Δᴿ} {μ : Env∼ Δᴸ}
    {A₀ : Ty Δᴸ} {B : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {B′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {c : genᵐ μ ⊢ ⇑ᵗ A₀ ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {A₀≠★ : A₀ ≢ ★}
    {p∀ : `∀ B ⊑ᵂ⟨ world ⟩ `∀ B′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ⟨ (gen c) A₀≠★ ⟩ ⊑ M′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ A′)
  → (r : B [ A ]ᵗ ⊑ᵂ⟨ world ⟩ B′ [ A′ ]ᵗ)
  → Value V
  → GenSafe c
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World (Nat.suc Δᴸ) Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy (bind A) (B [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (B′ [ A′ ]ᵗ) ]
      (M′ ⦂∀ B′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (bind A ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢²
        ⇑ᵗᵐ V ⟨ c ⟩ ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗
        ⊑ N′ ∶ s)

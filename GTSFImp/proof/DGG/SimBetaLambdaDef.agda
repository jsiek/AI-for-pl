module proof.DGG.SimBetaLambdaDef where

-- File Charter:
--   * States simulation of source universal beta reduction.
--   * Packages target catch-up, reduction, parked-world evolution, and the
--     final instantiated-body relation behind one interface.
--   * Contains no universal-beta simulation proof.

import Data.Fin as Fin
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; `∀; ⇑ᵗ; _[_]ᵗ)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Term; Value; Λ_; _⦂∀_[_]; _↑_)
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


SimBetaLambdaᵀ : Set
SimBetaLambdaᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {V : Term (Nat.suc Δᴸ)} {M′ : Term Δᴿ}
    {C : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {C′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {p∀ : `∀ C ⊑ᵂ⟨ world ⟩ `∀ C′}
  → ParkedWorld world
  → world ∣ [] ⊢² Λ V ⊑ M′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ A′)
  → (r : C [ A ]ᵗ ⊑ᵂ⟨ world ⟩ C′ [ A′ ]ᵗ)
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World (Nat.suc Δᴸ) Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy (bind A) (C [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
      applyTys χsᴿ (C′ [ A′ ]ᵗ) ]
      (M′ ⦂∀ C′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (bind A ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢²
        V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ C 〗 ⊑ N′ ∶ s)

module proof.DGG.SimBetaRevealAllDef where

-- File Charter:
--   * States simulation of source universal-reveal beta reduction.
--   * Packages target catch-up, reduction, parked-world evolution, and the
--     final instantiated revealed-value relation behind one interface.
--   * Contains no universal-reveal-beta simulation proof.

import Data.Fin as Fin
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx; ＇_; `∀; ⇑ᵗ; _[_]ᵗ)
open import Conversion using (Conv↑; `∀↑_; 〖_,_↑_〗)
open import CastTerms using
  (Term; Value; ⇑ᵗᵐ; _⦂∀_[_]; _↑_)
open import Reduction using
  ( StoreChanges
  ; applyTy
  ; applyTys
  ; applyBody
  ; bind
  ; _—↠[_]_
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


SimBetaRevealAllᵀ : Set
SimBetaRevealAllᵀ =
  ∀ {Δᴸ Δᴿ Δ} {world : World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {D B : Ty (Nat.suc Δᴸ)} {A : Ty Δᴸ}
    {B′ : Ty (Nat.suc Δᴿ)} {A′ : Ty Δᴿ}
    {c : Conv↑ (Nat.suc Δᴸ) D B}
    {p∀ : `∀ B ⊑ᵂ⟨ world ⟩ `∀ B′}
  → ParkedWorld world
  → world ∣ [] ⊢² V ↑ `∀↑ c ⊑ M′ ∶ p∀
  → (q : A ⊑ᵂ⟨ world ⟩ A′)
  → (r : B [ A ]ᵗ ⊑ᵂ⟨ world ⟩ B′ [ A′ ]ᵗ)
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ N′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ world′ ∈ World (Nat.suc Δᴸ) Δᴿ′ Δ′ ]
    Σ[ s ∈ applyTy (bind A) (B [ A ]ᵗ) ⊑ᵂ⟨ world′ ⟩
        applyTys χsᴿ (B′ [ A′ ]ᵗ) ]
      (M′ ⦂∀ B′ [ A′ ] —↠[ χsᴿ ] N′) ×
      ParkedEvolve (bind A ∷ˢ []ˢ) χsᴿ world world′ ×
      (world′ ∣ [] ⊢²
        ((⇑ᵗᵐ V ⦂∀ applyBody (bind A) D [ ＇ Fin.zero ]) ↑ c)
          ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗 ⊑ N′ ∶ s)

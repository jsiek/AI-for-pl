module
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTermTransportCore
  where

-- File Charter:
--   * Provides stable term equalities and runtime-bullet facts used by
--     runtime-source/no-bullet-target right-value catch-up transport.
--   * Keeps syntax-directed support independent of QTI constructor analysis.
--   * Contains no term-imprecision case analysis, postulate, hole, or
--     termination bypass.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)

open import ImprecisionWf using
  ( ImpCtx
  ; idι
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( applyCoercion
  ; applyTerms
  ; applyTy
  ; applyTys
  ; bind
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; One•
  ; RuntimeOK
  ; Term
  ; no•-·
  ; no•-ƛ
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; one•
  ; one•-here
  ; one•-ƛ
  ; one•-·₁
  ; one•-·₂
  ; one•-Λ
  ; one•-ν
  ; one•-⊕₁
  ; one•-⊕₂
  ; one•-⟨⟩
  ; _⟨_⟩
  ; zero•
  )
import NuReduction
import NuTerms
open import QuotientedTermImprecision using (StoreImpPrefix)
open import
  proof.NuCore.Misc.NuImprecisionRuntimeBulletStoreStability
  using
  ( one-bullet-prefix-left-store-stable
  ; runtime-at-most-one•
  )
open import
  proof.Core.Properties.ReductionProperties
  using
  ( applyCoercions
  ; applyTerms-cast
  ; applyTys-ℕ
  ; applyTy-ℕ
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; `ℕ
  ; ‵_
  )


target-ℕ-result :
  ∀ χ χs →
  applyTys χs (applyTy χ (‵ `ℕ)) ≡ ‵ `ℕ
target-ℕ-result χ χs =
  trans (cong (applyTys χs) (applyTy-ℕ χ)) (applyTys-ℕ χs)


transport-idι-to-ℕ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (A≡ℕ : A ≡ ‵ `ℕ)
    (B≡ℕ : B ≡ ‵ `ℕ)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ ‵ `ℕ ⊑ T ⊣ Δᴿ)
    B≡ℕ
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ)
      A≡ℕ p)
    ≡ idι
transport-idι-to-ℕ refl refl idι = refl


transport-idι-from-ℕ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (A≡ℕ : A ≡ ‵ `ℕ)
    (B≡ℕ : B ≡ ‵ `ℕ)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  subst
    (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ)
    (sym B≡ℕ)
    (subst
      (λ S → Φ ∣ Δᴸ ⊢ S ⊑ ‵ `ℕ ⊣ Δᴿ)
      (sym A≡ℕ) idι)
    ≡ p
transport-idι-from-ℕ refl refl idι = refl


applyTerms-· :
  ∀ χs L M →
  applyTerms χs (L NuTerms.· M) ≡
    applyTerms χs L NuTerms.· applyTerms χs M
applyTerms-· [] L M = refl
applyTerms-· (keep ∷ χs) L M = applyTerms-· χs L M
applyTerms-· (NuReduction.bind A ∷ χs) L M =
  applyTerms-· χs (NuTerms.⇑ᵗᵐ L) (NuTerms.⇑ᵗᵐ M)


applyTerms-⊕ :
  ∀ χs L op M →
  applyTerms χs (L NuTerms.⊕[ op ] M) ≡
    applyTerms χs L NuTerms.⊕[ op ] applyTerms χs M
applyTerms-⊕ [] L op M = refl
applyTerms-⊕ (keep ∷ χs) L op M = applyTerms-⊕ χs L op M
applyTerms-⊕ (NuReduction.bind A ∷ χs) L op M =
  applyTerms-⊕ χs (NuTerms.⇑ᵗᵐ L) op (NuTerms.⇑ᵗᵐ M)


applyTerms-down-application :
  ∀ χs L M d →
  applyTerms χs (L NuTerms.· (M NuTerms.⟨ d ⟩)) ≡
    applyTerms χs L NuTerms.·
      (applyTerms χs M NuTerms.⟨ applyCoercions χs d ⟩)
applyTerms-down-application χs L M d =
  trans
    (applyTerms-· χs L (M NuTerms.⟨ d ⟩))
    (cong (λ N → applyTerms χs L NuTerms.· N)
      (applyTerms-cast χs M d))


one-no•-absurd : ∀ {M} → One• M → No• M → ⊥
one-no•-absurd (one•-here noM) ()
one-no•-absurd (one•-ƛ oneM) (no•-ƛ noM) =
  one-no•-absurd oneM noM
one-no•-absurd (one•-·₁ oneL noM) (no•-· noL₀ noM₀) =
  one-no•-absurd oneL noL₀
one-no•-absurd (one•-·₂ noL oneM) (no•-· noL₀ noM) =
  one-no•-absurd oneM noM
one-no•-absurd (one•-Λ oneM) (no•-Λ noM) =
  one-no•-absurd oneM noM
one-no•-absurd (one•-ν oneM) (no•-ν noM) =
  one-no•-absurd oneM noM
one-no•-absurd (one•-⊕₁ oneL noM) (no•-⊕ noL₀ noM₀) =
  one-no•-absurd oneL noL₀
one-no•-absurd (one•-⊕₂ noL oneM) (no•-⊕ noL₀ noM) =
  one-no•-absurd oneM noM
one-no•-absurd (one•-⟨⟩ oneM) (no•-⟨⟩ noM) =
  one-no•-absurd oneM noM


active-prefix-left-store-stable :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {M : Term} {A B : Ty}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK M →
  (No• M → ⊥) →
  Δᴸ ∣ leftStoreⁱ ρ₀ ∣ [] ⊢ M ⦂ A →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⦂ B →
  leftStoreⁱ ρ₀ ≡ leftStoreⁱ ρ⁺
active-prefix-left-store-stable prefix okM activeM M⊢₀ M⊢⁺
    with runtime-at-most-one• okM
active-prefix-left-store-stable prefix okM activeM M⊢₀ M⊢⁺
    | zero• noM =
  ⊥-elim (activeM noM)
active-prefix-left-store-stable prefix okM activeM M⊢₀ M⊢⁺
    | one• oneM =
  one-bullet-prefix-left-store-stable prefix oneM M⊢₀ M⊢⁺

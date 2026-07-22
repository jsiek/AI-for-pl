module proof.NuImprecisionRuntimeBulletStoreStability where

-- File Charter:
--   * Proves that typing a term with one runtime bullet exposes the canonical
--     zero-headed runtime store shape.
--   * Proves that a relational-store prefix cannot extend the source store
--     while such a term remains typable.
--   * Classifies RuntimeOK terms by the existing AtMostOne• judgment.
--   * Contains no result carrier, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; store-link
  ; store-left
  ; store-matched
  ; store-right
  )
open import NuTerms using
  ( AtMostOne•
  ; No•
  ; One•
  ; RuntimeOK
  ; no•-·
  ; no•-⟨⟩
  ; no•-ν
  ; no•-⊕
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; ok-⟨⟩
  ; ok-ν
  ; ok-•
  ; ok-⊕₁
  ; ok-⊕₂
  ; one•
  ; one•-·₁
  ; one•-·₂
  ; one•-⟨⟩
  ; one•-Λ
  ; one•-ν
  ; one•-here
  ; one•-⊕₁
  ; one•-⊕₂
  ; one•-ƛ
  ; zero•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢·
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊑
  ; ⊢⟨⟩⊒
  ; ⊢Λ
  ; ⊢ν↑
  ; ⊢ν⊑
  ; ⊢•
  ; ⊢⊕
  ; ⊢ƛ
  )
open import Types using
  ( Ctx
  ; Store
  ; Ty
  ; TyCtx
  ; ⟰ᵗ
  )
open import proof.CoercionProperties using (zero∉-⟰ᵗ)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.NuTermProperties using
  (renameᵗᵐ-preserves-No•)


one-bullet-typing-store-shape :
  ∀ {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : NuTerms.Term} {A : Ty} →
  One• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  ∃[ X ] ∃[ Σ₀ ] Σ ≡ (zero , X) ∷ ⟰ᵗ Σ₀
one-bullet-typing-store-shape
    (one•-here noM)
    (⊢• Δ≡ Σ≡ hC vV noV V⊢) =
  _ , _ , Σ≡
one-bullet-typing-store-shape (one•-ƛ oneM) (⊢ƛ hA M⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape (one•-·₁ oneL noM) (⊢· L⊢ M⊢) =
  one-bullet-typing-store-shape oneL L⊢
one-bullet-typing-store-shape (one•-·₂ noL oneM) (⊢· L⊢ M⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape (one•-Λ oneM) (⊢Λ vM M⊢)
    with one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape (one•-Λ oneM) (⊢Λ vM M⊢)
    | X , Σ₀ , Σ≡ =
  ⊥-elim
    (zero∉-⟰ᵗ
      (subst (λ Σ → (zero , X) ∈ Σ) (sym Σ≡) (here refl)))
one-bullet-typing-store-shape (one•-ν oneM) (⊢ν↑ hA M⊢ c⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape
    (one•-ν oneM) (⊢ν⊑ mode seal★ M⊢ c⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape (one•-⊕₁ oneL noM) (⊢⊕ L⊢ op M⊢) =
  one-bullet-typing-store-shape oneL L⊢
one-bullet-typing-store-shape (one•-⊕₂ noL oneM) (⊢⊕ L⊢ op M⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape (one•-⟨⟩ oneM) (⊢⟨⟩↑ c⊢ M⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape (one•-⟨⟩ oneM) (⊢⟨⟩↓ c⊢ M⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape
    (one•-⟨⟩ oneM) (⊢⟨⟩⊒ mode seal★ c⊢ M⊢) =
  one-bullet-typing-store-shape oneM M⊢
one-bullet-typing-store-shape
    (one•-⟨⟩ oneM) (⊢⟨⟩⊑ mode seal★ c⊢ M⊢) =
  one-bullet-typing-store-shape oneM M⊢


private
  prefix-left-store-shape-stable :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    (∃[ X ] ∃[ Σ₀ ]
      leftStoreⁱ ρ₀ ≡ (zero , X) ∷ ⟰ᵗ Σ₀) →
    (∃[ Y ] ∃[ Σ⁺ ]
      leftStoreⁱ ρ⁺ ≡ (zero , Y) ∷ ⟰ᵗ Σ⁺) →
    leftStoreⁱ ρ₀ ≡ leftStoreⁱ ρ⁺
  prefix-left-store-shape-stable prefix-reflⁱ old-shape new-shape = refl
  prefix-left-store-shape-stable
      (prefix-∷ⁱ {entry = store-matched α A β B p} prefix)
      (X , Σ₀ , old≡) (Y , Σ⁺ , new≡) =
    ⊥-elim
      (zero∉-⟰ᵗ
        (subst (λ Σ → (zero , X) ∈ Σ) (cong (drop 1) new≡)
          (leftStoreⁱ-prefix-inclusion prefix
            (subst (λ Σ → (zero , X) ∈ Σ)
              (sym old≡) (here refl)))))
  prefix-left-store-shape-stable
      (prefix-∷ⁱ {entry = store-left α A hA} prefix)
      (X , Σ₀ , old≡) (Y , Σ⁺ , new≡) =
    ⊥-elim
      (zero∉-⟰ᵗ
        (subst (λ Σ → (zero , X) ∈ Σ) (cong (drop 1) new≡)
          (leftStoreⁱ-prefix-inclusion prefix
            (subst (λ Σ → (zero , X) ∈ Σ)
              (sym old≡) (here refl)))))
  prefix-left-store-shape-stable
      (prefix-∷ⁱ {entry = store-right β B hB} prefix)
      old-shape new-shape =
    prefix-left-store-shape-stable prefix old-shape new-shape
  prefix-left-store-shape-stable
      (prefix-∷ⁱ {entry = store-link α A β B p} prefix)
      old-shape new-shape =
    prefix-left-store-shape-stable prefix old-shape new-shape


one-bullet-prefix-left-store-stable :
  ∀ {Φ} {Δᴸ Δᴿ : TyCtx} {Γ : Ctx}
    {M : NuTerms.Term} {A B : Ty}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  One• M →
  Δᴸ ∣ leftStoreⁱ ρ₀ ∣ Γ ⊢ M ⦂ A →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ ⊢ M ⦂ B →
  leftStoreⁱ ρ₀ ≡ leftStoreⁱ ρ⁺
one-bullet-prefix-left-store-stable prefix oneM old⊢ new⊢ =
  prefix-left-store-shape-stable prefix
    (one-bullet-typing-store-shape oneM old⊢)
    (one-bullet-typing-store-shape oneM new⊢)


runtime-at-most-one• :
  ∀ {M} → RuntimeOK M → AtMostOne• M
runtime-at-most-one• (ok-no noM) = zero• noM
runtime-at-most-one• (ok-• vV noV) =
  one• (one•-here (renameᵗᵐ-preserves-No• suc noV))
runtime-at-most-one• (ok-·₁ okL noM)
    with runtime-at-most-one• okL
runtime-at-most-one• (ok-·₁ okL noM) | zero• noL =
  zero• (no•-· noL noM)
runtime-at-most-one• (ok-·₁ okL noM) | one• oneL =
  one• (one•-·₁ oneL noM)
runtime-at-most-one• (ok-·₂ vL noL okM)
    with runtime-at-most-one• okM
runtime-at-most-one• (ok-·₂ vL noL okM) | zero• noM =
  zero• (no•-· noL noM)
runtime-at-most-one• (ok-·₂ vL noL okM) | one• oneM =
  one• (one•-·₂ noL oneM)
runtime-at-most-one• (ok-ν okM) with runtime-at-most-one• okM
runtime-at-most-one• (ok-ν okM) | zero• noM =
  zero• (no•-ν noM)
runtime-at-most-one• (ok-ν okM) | one• oneM =
  one• (one•-ν oneM)
runtime-at-most-one• (ok-⊕₁ okL noM)
    with runtime-at-most-one• okL
runtime-at-most-one• (ok-⊕₁ okL noM) | zero• noL =
  zero• (no•-⊕ noL noM)
runtime-at-most-one• (ok-⊕₁ okL noM) | one• oneL =
  one• (one•-⊕₁ oneL noM)
runtime-at-most-one• (ok-⊕₂ vL noL okM)
    with runtime-at-most-one• okM
runtime-at-most-one• (ok-⊕₂ vL noL okM) | zero• noM =
  zero• (no•-⊕ noL noM)
runtime-at-most-one• (ok-⊕₂ vL noL okM) | one• oneM =
  one• (one•-⊕₂ noL oneM)
runtime-at-most-one• (ok-⟨⟩ okM) with runtime-at-most-one• okM
runtime-at-most-one• (ok-⟨⟩ okM) | zero• noM =
  zero• (no•-⟨⟩ noM)
runtime-at-most-one• (ok-⟨⟩ okM) | one• oneM =
  one• (one•-⟨⟩ oneM)

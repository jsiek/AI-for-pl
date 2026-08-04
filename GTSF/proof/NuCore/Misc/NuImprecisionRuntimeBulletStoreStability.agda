module proof.NuCore.Misc.NuImprecisionRuntimeBulletStoreStability where

-- File Charter:
--   * Classifies terms as bullet-free or containing a runtime bullet and
--     proves that typing the latter exposes the canonical runtime-store shape.
--   * Proves that a relational-store prefix cannot extend either projected
--     store while a bullet-containing term remains typable.
--   * Aligns an old typing derivation with an enlarged projected store even
--     when a second typing derivation chooses different hidden types.
--   * Classifies RuntimeOK terms by the existing AtMostOne• judgment.
--   * Contains no result carrier, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
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
  ; Term
  ; blame
  ; no•-·
  ; no•-$
  ; no•-`
  ; no•-⟨⟩
  ; no•-Λ
  ; no•-ν
  ; no•-⊕
  ; no•-blame
  ; no•-ƛ
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
  ; `_
  ; ƛ_
  ; _·_
  ; Λ_
  ; _•
  ; ν
  ; $
  ; _⊕[_]_
  ; _⟨_⟩
  ; zero•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢`
  ; ⊢·
  ; ⊢$
  ; ⊢blame
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
open import proof.Core.Properties.CoercionProperties using (zero∉-⟰ᵗ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)
open import proof.Core.Properties.TypePreservation using (term-weaken)


data Contains• : Term → Set where
  contains•-here : ∀ {M} → Contains• (M •)
  contains•-ƛ : ∀ {M} → Contains• M → Contains• (ƛ M)
  contains•-·₁ : ∀ {L M} → Contains• L → Contains• (L · M)
  contains•-·₂ : ∀ {L M} → Contains• M → Contains• (L · M)
  contains•-Λ : ∀ {M} → Contains• M → Contains• (Λ M)
  contains•-ν : ∀ {A L c} → Contains• L → Contains• (ν A L c)
  contains•-⊕₁ :
    ∀ {L op M} → Contains• L → Contains• (L ⊕[ op ] M)
  contains•-⊕₂ :
    ∀ {L op M} → Contains• M → Contains• (L ⊕[ op ] M)
  contains•-⟨⟩ : ∀ {M c} → Contains• M → Contains• (M ⟨ c ⟩)


bullet-classification :
  ∀ M → No• M ⊎ Contains• M
bullet-classification (` x) = inj₁ no•-`
bullet-classification (ƛ M) with bullet-classification M
bullet-classification (ƛ M) | inj₁ noM = inj₁ (no•-ƛ noM)
bullet-classification (ƛ M) | inj₂ hasM = inj₂ (contains•-ƛ hasM)
bullet-classification (L · M)
    with bullet-classification L | bullet-classification M
bullet-classification (L · M) | inj₁ noL | inj₁ noM =
  inj₁ (no•-· noL noM)
bullet-classification (L · M) | inj₁ noL | inj₂ hasM =
  inj₂ (contains•-·₂ hasM)
bullet-classification (L · M) | inj₂ hasL | inj₁ noM =
  inj₂ (contains•-·₁ hasL)
bullet-classification (L · M) | inj₂ hasL | inj₂ hasM =
  inj₂ (contains•-·₁ hasL)
bullet-classification (Λ M) with bullet-classification M
bullet-classification (Λ M) | inj₁ noM = inj₁ (no•-Λ noM)
bullet-classification (Λ M) | inj₂ hasM = inj₂ (contains•-Λ hasM)
bullet-classification (M •) = inj₂ contains•-here
bullet-classification (ν A L c) with bullet-classification L
bullet-classification (ν A L c) | inj₁ noL = inj₁ (no•-ν noL)
bullet-classification (ν A L c) | inj₂ hasL =
  inj₂ (contains•-ν hasL)
bullet-classification ($ κ) = inj₁ no•-$
bullet-classification (L ⊕[ op ] M)
    with bullet-classification L | bullet-classification M
bullet-classification (L ⊕[ op ] M) | inj₁ noL | inj₁ noM =
  inj₁ (no•-⊕ noL noM)
bullet-classification (L ⊕[ op ] M) | inj₁ noL | inj₂ hasM =
  inj₂ (contains•-⊕₂ hasM)
bullet-classification (L ⊕[ op ] M) | inj₂ hasL | inj₁ noM =
  inj₂ (contains•-⊕₁ hasL)
bullet-classification (L ⊕[ op ] M) | inj₂ hasL | inj₂ hasM =
  inj₂ (contains•-⊕₁ hasL)
bullet-classification (M ⟨ c ⟩) with bullet-classification M
bullet-classification (M ⟨ c ⟩) | inj₁ noM = inj₁ (no•-⟨⟩ noM)
bullet-classification (M ⟨ c ⟩) | inj₂ hasM =
  inj₂ (contains•-⟨⟩ hasM)
bullet-classification blame = inj₁ no•-blame


bullet-typing-store-shape :
  ∀ {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
  Contains• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  ∃[ X ] ∃[ Σ₀ ] Σ ≡ (zero , X) ∷ ⟰ᵗ Σ₀
bullet-typing-store-shape contains•-here
    (⊢• Δ≡ Σ≡ hC vV noV V⊢) =
  _ , _ , Σ≡
bullet-typing-store-shape (contains•-ƛ hasM) (⊢ƛ hA M⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape (contains•-·₁ hasL) (⊢· L⊢ M⊢) =
  bullet-typing-store-shape hasL L⊢
bullet-typing-store-shape (contains•-·₂ hasM) (⊢· L⊢ M⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape (contains•-Λ hasM) (⊢Λ vM M⊢)
    with bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape (contains•-Λ hasM) (⊢Λ vM M⊢)
    | X , Σ₀ , Σ≡ =
  ⊥-elim
    (zero∉-⟰ᵗ
      (subst (λ Σ → (zero , X) ∈ Σ) (sym Σ≡) (here refl)))
bullet-typing-store-shape (contains•-ν hasM) (⊢ν↑ hA M⊢ c⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape
    (contains•-ν hasM) (⊢ν⊑ mode seal★ M⊢ c⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape (contains•-⊕₁ hasL) (⊢⊕ L⊢ op M⊢) =
  bullet-typing-store-shape hasL L⊢
bullet-typing-store-shape (contains•-⊕₂ hasM) (⊢⊕ L⊢ op M⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape (contains•-⟨⟩ hasM) (⊢⟨⟩↑ c⊢ M⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape (contains•-⟨⟩ hasM) (⊢⟨⟩↓ c⊢ M⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape
    (contains•-⟨⟩ hasM) (⊢⟨⟩⊒ mode seal★ c⊢ M⊢) =
  bullet-typing-store-shape hasM M⊢
bullet-typing-store-shape
    (contains•-⟨⟩ hasM) (⊢⟨⟩⊑ mode seal★ c⊢ M⊢) =
  bullet-typing-store-shape hasM M⊢


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


prefix-right-store-shape-stable :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (∃[ X ] ∃[ Σ₀ ]
    rightStoreⁱ ρ₀ ≡ (zero , X) ∷ ⟰ᵗ Σ₀) →
  (∃[ Y ] ∃[ Σ⁺ ]
    rightStoreⁱ ρ⁺ ≡ (zero , Y) ∷ ⟰ᵗ Σ⁺) →
  rightStoreⁱ ρ₀ ≡ rightStoreⁱ ρ⁺
prefix-right-store-shape-stable prefix-reflⁱ old-shape new-shape = refl
prefix-right-store-shape-stable
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix)
    (X , Σ₀ , old≡) (Y , Σ⁺ , new≡) =
  ⊥-elim
    (zero∉-⟰ᵗ
      (subst (λ Σ → (zero , X) ∈ Σ) (cong (drop 1) new≡)
        (rightStoreⁱ-prefix-inclusion prefix
          (subst (λ Σ → (zero , X) ∈ Σ)
            (sym old≡) (here refl)))))
prefix-right-store-shape-stable
    (prefix-∷ⁱ {entry = store-left α A hA} prefix)
    old-shape new-shape =
  prefix-right-store-shape-stable prefix old-shape new-shape
prefix-right-store-shape-stable
    (prefix-∷ⁱ {entry = store-right β B hB} prefix)
    (X , Σ₀ , old≡) (Y , Σ⁺ , new≡) =
  ⊥-elim
    (zero∉-⟰ᵗ
      (subst (λ Σ → (zero , X) ∈ Σ) (cong (drop 1) new≡)
        (rightStoreⁱ-prefix-inclusion prefix
          (subst (λ Σ → (zero , X) ∈ Σ)
            (sym old≡) (here refl)))))
prefix-right-store-shape-stable
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix)
    old-shape new-shape =
  prefix-right-store-shape-stable prefix old-shape new-shape


term-typing-prefix-left-align :
  ∀ {Φ} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {Γ Γ⁺ : Ctx} {M : Term} {A A⁺ : Ty} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Δᴸ ∣ leftStoreⁱ ρ₀ ∣ Γ ⊢ M ⦂ A →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ A⁺ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ Γ ⊢ M ⦂ A
term-typing-prefix-left-align {M = M} prefix old⊢ new⊢
    with bullet-classification M
term-typing-prefix-left-align prefix old⊢ new⊢ | inj₁ noM =
  term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix) noM old⊢
term-typing-prefix-left-align prefix old⊢ new⊢ | inj₂ hasM =
  subst
    (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
    (prefix-left-store-shape-stable prefix
      (bullet-typing-store-shape hasM old⊢)
      (bullet-typing-store-shape hasM new⊢))
    old⊢


term-typing-prefix-right-align :
  ∀ {Φ} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {Γ Γ⁺ : Ctx} {M : Term} {A A⁺ : Ty} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Δᴿ ∣ rightStoreⁱ ρ₀ ∣ Γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ⁺ ⊢ M ⦂ A⁺ →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ Γ ⊢ M ⦂ A
term-typing-prefix-right-align {M = M} prefix old⊢ new⊢
    with bullet-classification M
term-typing-prefix-right-align prefix old⊢ new⊢ | inj₁ noM =
  term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix) noM old⊢
term-typing-prefix-right-align prefix old⊢ new⊢ | inj₂ hasM =
  subst
    (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
    (prefix-right-store-shape-stable prefix
      (bullet-typing-store-shape hasM old⊢)
      (bullet-typing-store-shape hasM new⊢))
    old⊢


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

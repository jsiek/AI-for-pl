module PrecisionPolyCoercion where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Nat using (zero; suc; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import PolyCoercions

--------------------------------------------------------------------------------
-- Polymorphic Coercion Precision
--------------------------------------------------------------------------------

infix 4 _∣_⊢_⊑ᶜ_

data _∣_⊢_⊑ᶜ_ : Store → TyCtx → Coercion → Coercion → Set where
  -- congruence rules
  ⊑idᶜ : ∀ {Σ Δ A A′}
    → A ⊑ A′
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ idᶜ A′
  ⊑! : ∀ {Σ Δ A A′}
    → A ⊑ A′
    → Σ ∣ Δ ⊢ A ! ⊑ᶜ A′ !
  ⊑? : ∀ {Σ Δ A A′ p p′}
    → A ⊑ A′
    → Σ ∣ Δ ⊢ A `? p ⊑ᶜ A′ `? p′
  ⊑⁻ : ∀ {Σ Δ U}
    → Σ ∣ Δ ⊢ U ⁻ ⊑ᶜ U ⁻
  ⊑⁺ : ∀ {Σ Δ U}
    → Σ ∣ Δ ⊢ U ⁺ ⊑ᶜ U ⁺
  ⊑↦ : ∀ {Σ Δ c c′ d d′}
    → Σ ∣ Δ ⊢ c ⊑ᶜ c′
    → Σ ∣ Δ ⊢ d ⊑ᶜ d′
    → Σ ∣ Δ ⊢ c ↦ d ⊑ᶜ c′ ↦ d′
  ⊑∀ᶜ : ∀ {Σ Δ c c′}
    → renameΣ suc Σ ∣ suc Δ ⊢ c ⊑ᶜ c′
    → Σ ∣ Δ ⊢ ∀ᶜ c ⊑ᶜ ∀ᶜ c′
  ⊑⨟ : ∀ {Σ Δ c c′ d d′}
    → Σ ∣ Δ ⊢ c ⊑ᶜ c′
    → Σ ∣ Δ ⊢ d ⊑ᶜ d′
    → Σ ∣ Δ ⊢ c ⨟ d ⊑ᶜ c′ ⨟ d′
  ⊑⊥ : ∀ {Σ Δ p p′ A A′ B B′}
    → A ⊑ A′
    → B ⊑ B′
    → Σ ∣ Δ ⊢ (⊥ᶜ p ⦂ A ⇨ B) ⊑ᶜ (⊥ᶜ p′ ⦂ A′ ⇨ B′)

  -- rules relating identity to other coercions
  ⊑idL! : ∀ {Σ Δ A B}
    → A ⊑ B
    → A ⊑ `★
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ B !
  ⊑idL? : ∀ {Σ Δ A B p}
    → A ⊑ `★
    → A ⊑ B
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ B `? p
  ⊑idL↦★ : ∀ {Σ Δ c d}
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ d
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ (c ↦ d)
  ⊑idL↦ : ∀ {Σ Δ A B c d}
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ B ⊑ᶜ d
    → Σ ∣ Δ ⊢ idᶜ (A ⇒ B) ⊑ᶜ (c ↦ d)
  ⊑idL∀★ : ∀ {Σ Δ c}
    → renameΣ suc Σ ∣ suc Δ ⊢ idᶜ `★ ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ ∀ᶜ c
  ⊑idL∀ : ∀ {Σ Δ A c}
    → renameΣ suc Σ ∣ suc Δ ⊢ idᶜ A ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ (`∀ A) ⊑ᶜ ∀ᶜ c
  ⊑idL⨟ : ∀ {Σ Δ A c d}
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ d
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ (c ⨟ d)

  ⊑idR! : ∀ {Σ Δ A B}
    → B ⊑ A
    → `★ ⊑ A
    → Σ ∣ Δ ⊢ B ! ⊑ᶜ idᶜ A
  ⊑idR? : ∀ {Σ Δ A B p}
    → `★ ⊑ A
    → B ⊑ A
    → Σ ∣ Δ ⊢ B `? p ⊑ᶜ idᶜ A
  ⊑idR↦ : ∀ {Σ Δ A B c d}
    → Σ ∣ Δ ⊢ c ⊑ᶜ idᶜ A
    → Σ ∣ Δ ⊢ d ⊑ᶜ idᶜ B
    → Σ ∣ Δ ⊢ (c ↦ d) ⊑ᶜ idᶜ (A ⇒ B)
  ⊑idR∀ : ∀ {Σ Δ A c}
    → renameΣ suc Σ ∣ suc Δ ⊢ c ⊑ᶜ idᶜ A
    → Σ ∣ Δ ⊢ ∀ᶜ c ⊑ᶜ idᶜ (`∀ A)
  ⊑idR⨟ : ∀ {Σ Δ A c d}
    → Σ ∣ Δ ⊢ c ⊑ᶜ idᶜ A
    → Σ ∣ Δ ⊢ d ⊑ᶜ idᶜ A
    → Σ ∣ Δ ⊢ (c ⨟ d) ⊑ᶜ idᶜ A

  -- drop dynamic checks/tags around higher-order coercions
  ⊑drop?↦ : ∀ {Σ Δ p c c′}
    → Σ ∣ Δ ⊢ c′ ⊑ᶜ c
    → Σ ∣ Δ ⊢ (((`★ ⇒ `★) `? p) ⨟ c′) ⊑ᶜ c
  ⊑drop!↦ : ∀ {Σ Δ c c′}
    → Σ ∣ Δ ⊢ c′ ⊑ᶜ c
    → Σ ∣ Δ ⊢ (c′ ⨟ ((`★ ⇒ `★) !)) ⊑ᶜ c
  ⊑drop?∀ : ∀ {Σ Δ p c c′}
    → Σ ∣ Δ ⊢ c′ ⊑ᶜ c
    → Σ ∣ Δ ⊢ (((`∀ `★) `? p) ⨟ c′) ⊑ᶜ c
  ⊑drop!∀ : ∀ {Σ Δ c c′}
    → Σ ∣ Δ ⊢ c′ ⊑ᶜ c
    → Σ ∣ Δ ⊢ (c′ ⨟ ((`∀ `★) !)) ⊑ᶜ c

⊑ᶜ-reflexive : ∀ Σ Δ c → Σ ∣ Δ ⊢ c ⊑ᶜ c
⊑ᶜ-reflexive Σ Δ (idᶜ A) = ⊑idᶜ ⊑-refl
⊑ᶜ-reflexive Σ Δ (A !) = ⊑! ⊑-refl
⊑ᶜ-reflexive Σ Δ (A `? p) = ⊑? ⊑-refl
⊑ᶜ-reflexive Σ Δ (U ⁻) = ⊑⁻
⊑ᶜ-reflexive Σ Δ (U ⁺) = ⊑⁺
⊑ᶜ-reflexive Σ Δ (c ↦ d) = ⊑↦ (⊑ᶜ-reflexive Σ Δ c) (⊑ᶜ-reflexive Σ Δ d)
⊑ᶜ-reflexive Σ Δ (∀ᶜ c) = ⊑∀ᶜ (⊑ᶜ-reflexive (renameΣ suc Σ) (suc Δ) c)
⊑ᶜ-reflexive Σ Δ (c ⨟ d) = ⊑⨟ (⊑ᶜ-reflexive Σ Δ c) (⊑ᶜ-reflexive Σ Δ d)
⊑ᶜ-reflexive Σ Δ (⊥ᶜ p ⦂ A ⇨ B) = ⊑⊥ ⊑-refl ⊑-refl

--------------------------------------------------------------------------------
-- Coerce monotonicity
--------------------------------------------------------------------------------

⊑-renameᵗ : ∀ {ρ A B} → A ⊑ B → renameᵗ ρ A ⊑ renameᵗ ρ B
⊑-renameᵗ ⊑-X = ⊑-X
⊑-renameᵗ ⊑-ℕ = ⊑-ℕ
⊑-renameᵗ ⊑-Bool = ⊑-Bool
⊑-renameᵗ ⊑-Str = ⊑-Str
⊑-renameᵗ ⊑-U = ⊑-U
⊑-renameᵗ (⊑-★ nxB) = ⊑-★ (NoX-renameᵗ nxB)
⊑-renameᵗ (⊑-⇒ A⊑C B⊑D) = ⊑-⇒ (⊑-renameᵗ A⊑C) (⊑-renameᵗ B⊑D)
⊑-renameᵗ {ρ = ρ} (⊑-∀ A⊑B) = ⊑-∀ (⊑-renameᵗ {ρ = extᵗ ρ} A⊑B)

★⊑→NoX : ∀ {A} → `★ ⊑ A → NoX A
★⊑→NoX p = ⊑-NoX-right NoX-★ p

★⊑⇒-dom : ∀ {A B} → `★ ⊑ (A ⇒ B) → `★ ⊑ A
★⊑⇒-dom ★⊑A⇒B with ★⊑→NoX ★⊑A⇒B
... | NoX-⇒ nxA nxB = ⊑-★ nxA

★⊑⇒-cod : ∀ {A B} → `★ ⊑ (A ⇒ B) → `★ ⊑ B
★⊑⇒-cod ★⊑A⇒B with ★⊑→NoX ★⊑A⇒B
... | NoX-⇒ nxA nxB = ⊑-★ nxB

postulate
  ★⊑∀-body : ∀ {A} → `★ ⊑ (`∀ A) → `★ ⊑ A

id★⊑coerce : ∀ {Σ Δ A B}{l : Label}
  → (p : A ~ B)
  → `★ ⊑ A
  → `★ ⊑ B
  → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ coerce l p
id★⊑coerce ~-X (⊑-★ (NoX-X ()))
id★⊑coerce ~-ℕ ★⊑A ★⊑B = ⊑idᶜ ★⊑A
id★⊑coerce ~-Bool ★⊑A ★⊑B = ⊑idᶜ ★⊑A
id★⊑coerce ~-Str ★⊑A ★⊑B = ⊑idᶜ ★⊑A
id★⊑coerce ~-★ ★⊑A ★⊑B = ⊑idᶜ ★⊑A
id★⊑coerce ~-U ★⊑A ★⊑B = ⊑idᶜ ★⊑A
id★⊑coerce ★~ℕ ★⊑A ★⊑B = ⊑idL? ★⊑A ★⊑B
id★⊑coerce ℕ~★ ★⊑A ★⊑B = ⊑idL! ★⊑A ★⊑B
id★⊑coerce ★~Bool ★⊑A ★⊑B = ⊑idL? ★⊑A ★⊑B
id★⊑coerce Bool~★ ★⊑A ★⊑B = ⊑idL! ★⊑A ★⊑B
id★⊑coerce ★~Str ★⊑A ★⊑B = ⊑idL? ★⊑A ★⊑B
id★⊑coerce Str~★ ★⊑A ★⊑B = ⊑idL! ★⊑A ★⊑B
id★⊑coerce ★~U ★⊑A ★⊑B = ⊑idL? ★⊑A ★⊑B
id★⊑coerce U~★ ★⊑A ★⊑B = ⊑idL! ★⊑A ★⊑B
id★⊑coerce {l = l} (★~⇒ c d) ★⊑A ★⊑B =
  ⊑idL⨟
    (⊑idL? ⊑-refl (⊑-★ (NoX-⇒ NoX-★ NoX-★)))
    (⊑idL↦★
      (id★⊑coerce {l = l} c (★⊑⇒-dom ★⊑B) ⊑-refl)
      (id★⊑coerce {l = l} d ⊑-refl (★⊑⇒-cod ★⊑B)))
id★⊑coerce {l = l} (⇒~★ c d) ★⊑A ★⊑B =
  ⊑idL⨟
    (⊑idL↦★
      (id★⊑coerce {l = l} c ⊑-refl (★⊑⇒-dom ★⊑A))
      (id★⊑coerce {l = l} d (★⊑⇒-cod ★⊑A) ⊑-refl))
    (⊑idL! (⊑-★ (NoX-⇒ NoX-★ NoX-★)) ⊑-refl)
id★⊑coerce {l = l} (★~∀ c) ★⊑A ★⊑B =
  ⊑idL⨟
    (⊑idL? ⊑-refl (⊑-★ (NoX-∀ NoX-★)))
    (⊑idL∀★
      (id★⊑coerce {Σ = renameΣ suc _} {Δ = suc _} {l = l}
        c
        ⊑-refl
        ?))
id★⊑coerce {l = l} (∀~★ c) ★⊑A ★⊑B =
  ⊑idL⨟
    (⊑idL∀★
      (id★⊑coerce {Σ = renameΣ suc _} {Δ = suc _} {l = l}
        c
        ?
        ⊑-refl))
    (⊑idL! (⊑-★ (NoX-∀ NoX-★)) ⊑-refl)
id★⊑coerce {l = l} (~-⇒ c d) ★⊑A ★⊑B =
  ⊑idL↦★
    (id★⊑coerce {l = l} c (★⊑⇒-dom ★⊑B) (★⊑⇒-dom ★⊑A))
    (id★⊑coerce {l = l} d (★⊑⇒-cod ★⊑A) (★⊑⇒-cod ★⊑B))
id★⊑coerce {l = l} (~-∀ c) ★⊑A ★⊑B =
  ⊑idL∀★
    (id★⊑coerce {Σ = renameΣ suc _} {Δ = suc _} {l = l}
      c
      (★⊑∀-body ★⊑A)
      (★⊑∀-body ★⊑B))

coerce-monotonic
  : ∀ {Σ Δ}{A A′ B B′}{l : Label}
  → (p : A ~ B)
  → (p′ : A′ ~ B′)
  → A ⊑ A′
  → B ⊑ B′
  → Σ ∣ Δ ⊢ coerce l p ⊑ᶜ coerce l p′
coerce-monotonic ~-X ~-X ⊑-X ⊑-X = ⊑idᶜ ⊑-X
coerce-monotonic ~-ℕ ~-ℕ ⊑-ℕ ⊑-ℕ = ⊑idᶜ ⊑-ℕ
coerce-monotonic ~-Bool ~-Bool ⊑-Bool ⊑-Bool = ⊑idᶜ ⊑-Bool
coerce-monotonic ~-Str ~-Str ⊑-Str ⊑-Str = ⊑idᶜ ⊑-Str
coerce-monotonic ~-U ~-U ⊑-U ⊑-U = ⊑idᶜ ⊑-U
coerce-monotonic ~-★ p′ A≤A′ B≤B′ = id★⊑coerce p′ A≤A′ B≤B′

coerce-monotonic ★~ℕ ~-ℕ A≤A′ B≤B′ = ⊑idR? A≤A′ B≤B′
coerce-monotonic ★~ℕ ★~ℕ A≤A′ B≤B′ = ⊑? B≤B′
coerce-monotonic ℕ~★ ~-ℕ A≤A′ B≤B′ = ⊑idR! A≤A′ B≤B′
coerce-monotonic ℕ~★ ℕ~★ A≤A′ B≤B′ = ⊑! A≤A′

coerce-monotonic ★~Bool ~-Bool A≤A′ B≤B′ = ⊑idR? A≤A′ B≤B′
coerce-monotonic ★~Bool ★~Bool A≤A′ B≤B′ = ⊑? B≤B′
coerce-monotonic Bool~★ ~-Bool A≤A′ B≤B′ = ⊑idR! A≤A′ B≤B′
coerce-monotonic Bool~★ Bool~★ A≤A′ B≤B′ = ⊑! A≤A′

coerce-monotonic ★~Str ~-Str A≤A′ B≤B′ = ⊑idR? A≤A′ B≤B′
coerce-monotonic ★~Str ★~Str A≤A′ B≤B′ = ⊑? B≤B′
coerce-monotonic Str~★ ~-Str A≤A′ B≤B′ = ⊑idR! A≤A′ B≤B′
coerce-monotonic Str~★ Str~★ A≤A′ B≤B′ = ⊑! A≤A′

coerce-monotonic ★~U ~-U A≤A′ B≤B′ = ⊑idR? A≤A′ B≤B′
coerce-monotonic ★~U ★~U A≤A′ B≤B′ = ⊑? B≤B′
coerce-monotonic U~★ ~-U A≤A′ B≤B′ = ⊑idR! A≤A′ B≤B′
coerce-monotonic U~★ U~★ A≤A′ B≤B′ = ⊑! A≤A′

coerce-monotonic {l = l} (★~⇒ c₁ c₂) (★~⇒ d₁ d₂) A≤A′ (⊑-⇒ B≤B′ C≤C′) =
  ⊑⨟
    (⊑? ⊑-refl)
    (⊑↦
      (coerce-monotonic {l = l} c₁ d₁ B≤B′ ⊑-refl)
      (coerce-monotonic {l = l} c₂ d₂ ⊑-refl C≤C′))
coerce-monotonic {l = l} (★~⇒ c₁ c₂) (~-⇒ d₁ d₂) A≤A′ (⊑-⇒ B≤B′ C≤C′) =
  ⊑drop?↦
    (⊑↦
      (coerce-monotonic {l = l} c₁ d₁ B≤B′ (★⊑⇒-dom A≤A′))
      (coerce-monotonic {l = l} c₂ d₂ (★⊑⇒-cod A≤A′) C≤C′))

coerce-monotonic {l = l} (⇒~★ c₁ c₂) (⇒~★ d₁ d₂) (⊑-⇒ A≤A′ B≤B′) C≤C′ =
  ⊑⨟
    (⊑↦
      (coerce-monotonic {l = l} c₁ d₁ ⊑-refl A≤A′)
      (coerce-monotonic {l = l} c₂ d₂ B≤B′ ⊑-refl))
    (⊑! ⊑-refl)
coerce-monotonic {l = l} (⇒~★ c₁ c₂) (~-⇒ d₁ d₂) (⊑-⇒ A≤A′ B≤B′) C≤C′ =
  ⊑drop!↦
    (⊑↦
      (coerce-monotonic {l = l} c₁ d₁ (★⊑⇒-dom C≤C′) A≤A′)
      (coerce-monotonic {l = l} c₂ d₂ B≤B′ (★⊑⇒-cod C≤C′)))

coerce-monotonic {l = l} (~-⇒ c₁ c₂) (~-⇒ d₁ d₂) (⊑-⇒ A≤A′ B≤B′) (⊑-⇒ C≤C′ D≤D′) =
  ⊑↦
    (coerce-monotonic {l = l} c₁ d₁ C≤C′ A≤A′)
    (coerce-monotonic {l = l} c₂ d₂ B≤B′ D≤D′)

coerce-monotonic {l = l} (★~∀ c) (★~∀ d) A≤A′ (⊑-∀ B≤B′) =
  ⊑⨟
    (⊑? ⊑-refl)
    (⊑∀ᶜ (coerce-monotonic {Σ = renameΣ suc _} {Δ = suc _} {l = l}
      c d ⊑-refl ?))
coerce-monotonic {l = l} (★~∀ c) (~-∀ d) A≤A′ (⊑-∀ B≤B′) =
  ⊑drop?∀
    (⊑∀ᶜ (coerce-monotonic {Σ = renameΣ suc _} {Δ = suc _} {l = l}
      c d (★⊑∀-body A≤A′) {!!}))

coerce-monotonic {l = l} (∀~★ c) (∀~★ d) (⊑-∀ A≤A′) B≤B′ =
  ⊑⨟
    (⊑∀ᶜ (coerce-monotonic {Σ = renameΣ suc _} {Δ = suc _} {l = l}
      c d ? ⊑-refl))
    (⊑! ⊑-refl)
coerce-monotonic {l = l} (∀~★ c) (~-∀ d) (⊑-∀ A≤A′) B≤B′ =
  ⊑drop!∀
    (⊑∀ᶜ (coerce-monotonic {Σ = renameΣ suc _} {Δ = suc _} {l = l}
      c d {!!} (★⊑∀-body B≤B′)))

coerce-monotonic {l = l} (~-∀ c) (~-∀ d) (⊑-∀ A≤A′) (⊑-∀ B≤B′) =
  ⊑∀ᶜ (coerce-monotonic {Σ = renameΣ suc _} {Δ = suc _} {l = l}
    c d A≤A′ B≤B′)

--------------------------------------------------------------------------------
-- Precision on coercions implies precision on endpoints
--------------------------------------------------------------------------------

⊑ᶜ→⊑ : ∀ {Σ Δ}{c c′ A B A′ B′ }
    → Σ ∣ Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ c′ ⦂ A′ ⇨ B′
    → Σ ∣ Δ ⊢ c ⊑ᶜ c′
      ----------------
    → A ⊑ A′ × B ⊑ B′
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢idᶜ hA′) (⊑idᶜ A⊑A′) = A⊑A′ , A⊑A′
⊑ᶜ→⊑ (⊢! hG gG) (⊢! hG′ gG′) (⊑! A⊑A′) = A⊑A′ , ⊑-refl
⊑ᶜ→⊑ (⊢? hG gG) (⊢? hG′ gG′) (⊑? A⊑A′) = ⊑-refl , A⊑A′
⊑ᶜ→⊑ (⊢conceal hU) (⊢conceal hU′) ⊑⁻
  with ∋ᵁ-unique hU hU′
... | refl = ⊑-refl , ⊑-refl
⊑ᶜ→⊑ (⊢reveal hU) (⊢reveal hU′) ⊑⁺
  with ∋ᵁ-unique hU hU′
... | refl = ⊑-refl , ⊑-refl
⊑ᶜ→⊑ (⊢↦ cwt dwt) (⊢↦ cwt′ dwt′) (⊑↦ c⊑c′ d⊑d′)
  with ⊑ᶜ→⊑ cwt cwt′ c⊑c′ | ⊑ᶜ→⊑ dwt dwt′ d⊑d′
... | A′⊑A , A″⊑A‴ | B⊑B′ , B″⊑B‴ =
  ⊑-⇒ A″⊑A‴ B⊑B′ , ⊑-⇒ A′⊑A B″⊑B‴
⊑ᶜ→⊑ (⊢∀ᶜ cwt) (⊢∀ᶜ cwt′) (⊑∀ᶜ c⊑c′)
  with ⊑ᶜ→⊑ cwt cwt′ c⊑c′
... | A⊑A′ , B⊑B′ = ⊑-∀ A⊑A′ , ⊑-∀ B⊑B′
⊑ᶜ→⊑ (⊢⨟ cwt dwt) (⊢⨟ cwt′ dwt′) (⊑⨟ c⊑c′ d⊑d′)
  with ⊑ᶜ→⊑ cwt cwt′ c⊑c′ | ⊑ᶜ→⊑ dwt dwt′ d⊑d′
... | A⊑A′ , _ | _ , C⊑C′ = A⊑A′ , C⊑C′
⊑ᶜ→⊑ (⊢⊥ hA hB) (⊢⊥ hA′ hB′) (⊑⊥ A⊑A′ B⊑B′) = A⊑A′ , B⊑B′

⊑ᶜ→⊑ (⊢idᶜ hA) (⊢! hG gG) (⊑idL! A⊑B A⊑★) = A⊑B , A⊑★
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢? hG gG) (⊑idL? A⊑★ A⊑B) = A⊑★ , A⊑B
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢↦ cwt dwt) (⊑idL↦★ p q)
  with ⊑ᶜ→⊑ (⊢idᶜ wf★) cwt p | ⊑ᶜ→⊑ (⊢idᶜ wf★) dwt q
... | ★⊑A′ , ★⊑A | ★⊑B , ★⊑B′ =
  ⊑-★ (NoX-⇒ (★⊑→NoX ★⊑A) (★⊑→NoX ★⊑B))
  , ⊑-★ (NoX-⇒ (★⊑→NoX ★⊑A′) (★⊑→NoX ★⊑B′))
⊑ᶜ→⊑ (⊢idᶜ (wf⇒ hA hB)) (⊢↦ cwt dwt) (⊑idL↦ p q)
  with ⊑ᶜ→⊑ (⊢idᶜ hA) cwt p | ⊑ᶜ→⊑ (⊢idᶜ hB) dwt q
... | A⊑A′ , A⊑A″ | A⊑B , A⊑B′ =
  ⊑-⇒ A⊑A″ A⊑B , ⊑-⇒ A⊑A′ A⊑B′
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢∀ᶜ cwt) (⊑idL∀★ p)
  with ⊑ᶜ→⊑ (⊢idᶜ wf★) cwt p
... | ★⊑A , ★⊑B =
  ⊑-★ (NoX-∀ (NoXᵈ-suc (★⊑→NoX ★⊑A)))
  , ⊑-★ (NoX-∀ (NoXᵈ-suc (★⊑→NoX ★⊑B)))
⊑ᶜ→⊑ (⊢idᶜ (wf∀ hA)) (⊢∀ᶜ cwt) (⊑idL∀ p)
  with ⊑ᶜ→⊑ (⊢idᶜ hA) cwt p
... | A⊑B , A⊑C = ⊑-∀ A⊑B , ⊑-∀ A⊑C
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢⨟ cwt dwt) (⊑idL⨟ p q)
  with ⊑ᶜ→⊑ (⊢idᶜ hA) cwt p | ⊑ᶜ→⊑ (⊢idᶜ hA) dwt q
... | A⊑B , _ | _ , A⊑C = A⊑B , A⊑C

⊑ᶜ→⊑ (⊢! hG gG) (⊢idᶜ hA) (⊑idR! B⊑A ★⊑A) = B⊑A , ★⊑A
⊑ᶜ→⊑ (⊢? hG gG) (⊢idᶜ hA) (⊑idR? ★⊑A B⊑A) = ★⊑A , B⊑A
⊑ᶜ→⊑ (⊢↦ cwt dwt) (⊢idᶜ (wf⇒ hA hB)) (⊑idR↦ p q)
  with ⊑ᶜ→⊑ cwt (⊢idᶜ hA) p | ⊑ᶜ→⊑ dwt (⊢idᶜ hB) q
... | A′⊑A , A⊑A″ | B⊑A‴ , B′⊑A =
  ⊑-⇒ A⊑A″ B⊑A‴ , ⊑-⇒ A′⊑A B′⊑A
⊑ᶜ→⊑ (⊢∀ᶜ cwt) (⊢idᶜ (wf∀ hA)) (⊑idR∀ p)
  with ⊑ᶜ→⊑ cwt (⊢idᶜ hA) p
... | A⊑B , C⊑A = ⊑-∀ A⊑B , ⊑-∀ C⊑A
⊑ᶜ→⊑ (⊢⨟ cwt dwt) (⊢idᶜ hA) (⊑idR⨟ p q)
  with ⊑ᶜ→⊑ cwt (⊢idᶜ hA) p | ⊑ᶜ→⊑ dwt (⊢idᶜ hA) q
... | A⊑B , _ | _ , C⊑A = A⊑B , C⊑A

⊑ᶜ→⊑ (⊢⨟ (⊢? wfG G-⇒★) c′wt) c⦂ (⊑drop?↦ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | starFun⊑A , B⊑B′ =
  ⊑-★ (⊑-NoX-right (NoX-⇒ NoX-★ NoX-★) starFun⊑A) , B⊑B′
⊑ᶜ→⊑ (⊢⨟ c′wt (⊢! wfG G-⇒★)) c⦂ (⊑drop!↦ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | A⊑A′ , starFun⊑B =
  A⊑A′ , ⊑-★ (⊑-NoX-right (NoX-⇒ NoX-★ NoX-★) starFun⊑B)
⊑ᶜ→⊑ (⊢⨟ (⊢? wfG G-∀★) c′wt) c⦂ (⊑drop?∀ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | starAll⊑A , B⊑B′ =
  ⊑-★ (⊑-NoX-right (NoX-∀ NoX-★) starAll⊑A) , B⊑B′
⊑ᶜ→⊑ (⊢⨟ c′wt (⊢! wfG G-∀★)) c⦂ (⊑drop!∀ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | A⊑A′ , starAll⊑B =
  A⊑A′ , ⊑-★ (⊑-NoX-right (NoX-∀ NoX-★) starAll⊑B)

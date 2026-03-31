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
    → A ⊑′ A′
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ idᶜ A′
  ⊑! : ∀ {Σ Δ A A′}
    → A ⊑′ A′
    → Σ ∣ Δ ⊢ A ! ⊑ᶜ A′ !
  ⊑? : ∀ {Σ Δ A A′ p p′}
    → A ⊑′ A′
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
    → A ⊑′ A′
    → B ⊑′ B′
    → Σ ∣ Δ ⊢ (⊥ᶜ p ⦂ A ⇨ B) ⊑ᶜ (⊥ᶜ p′ ⦂ A′ ⇨ B′)

  -- rules relating identity to other coercions
  ⊑idL! : ∀ {Σ Δ A B}
    → A ⊑′ B
    → A ⊑′ `★
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ B !
  ⊑idL? : ∀ {Σ Δ A B p}
    → A ⊑′ `★
    → A ⊑′ B
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ B `? p
  ⊑idL↦★ : ∀ {Σ Δ c d}
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ d
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ (c ↦ d)
  ⊑idL↦ : ∀ {Σ Δ A B c d}
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ B ⊑ᶜ d
    → Σ ∣ Δ ⊢ idᶜ (A ⇒ B) ⊑ᶜ (c ↦ d)
  ⊑idL∀★ : ∀ {Σ Δ A B c}
    → `★ ⊑′ `∀ A
    → `★ ⊑′ `∀ B
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ substᶜᵘ 0 c
    → Σ ∣ Δ ⊢ ∀ᶜ c ⦂ `∀ A ⇨ `∀ B
    → Σ ∣ Δ ⊢ idᶜ `★ ⊑ᶜ ∀ᶜ c
  ⊑idL∀ : ∀ {Σ Δ A c}
    → renameΣ suc Σ ∣ suc Δ ⊢ idᶜ A ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ (`∀ A) ⊑ᶜ ∀ᶜ c
  ⊑idL⨟ : ∀ {Σ Δ A c d}
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ c
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ d
    → Σ ∣ Δ ⊢ idᶜ A ⊑ᶜ (c ⨟ d)

  ⊑idR! : ∀ {Σ Δ A B}
    → B ⊑′ A
    → `★ ⊑′ A
    → Σ ∣ Δ ⊢ B ! ⊑ᶜ idᶜ A
  ⊑idR? : ∀ {Σ Δ A B p}
    → `★ ⊑′ A
    → B ⊑′ A
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
⊑ᶜ-reflexive Σ Δ (idᶜ A) = ⊑idᶜ ⊑′-refl
⊑ᶜ-reflexive Σ Δ (A !) = ⊑! ⊑′-refl
⊑ᶜ-reflexive Σ Δ (A `? p) = ⊑? ⊑′-refl
⊑ᶜ-reflexive Σ Δ (U ⁻) = ⊑⁻
⊑ᶜ-reflexive Σ Δ (U ⁺) = ⊑⁺
⊑ᶜ-reflexive Σ Δ (c ↦ d) = ⊑↦ (⊑ᶜ-reflexive Σ Δ c) (⊑ᶜ-reflexive Σ Δ d)
⊑ᶜ-reflexive Σ Δ (∀ᶜ c) = ⊑∀ᶜ (⊑ᶜ-reflexive (renameΣ suc Σ) (suc Δ) c)
⊑ᶜ-reflexive Σ Δ (c ⨟ d) = ⊑⨟ (⊑ᶜ-reflexive Σ Δ c) (⊑ᶜ-reflexive Σ Δ d)
⊑ᶜ-reflexive Σ Δ (⊥ᶜ p ⦂ A ⇨ B) = ⊑⊥ ⊑′-refl ⊑′-refl

★⇒★⊑′A→★⊑′A : ∀ {A} → (`★ ⇒ `★) ⊑′ A → `★ ⊑′ A
★⇒★⊑′A→★⊑′A (⊑′-⇒ ★⊑′A ★⊑′B) = ★⊑′⇒ ★⊑′A ★⊑′B

∀★⊑′A→★⊑′A : ∀ {A} → `∀ `★ ⊑′ A → `★ ⊑′ A
∀★⊑′A→★⊑′A (⊑′-∀ ★⊑′A) = ★⊑′∀ (⊑′-[]ᵘ {U = zero} ★⊑′A)

--------------------------------------------------------------------------------
-- Precision on coercions implies precision on endpoints
--------------------------------------------------------------------------------

⊑ᶜ→⊑ : ∀ {Σ Δ}{c c′ A0 B0 A1 B1}
    → Σ ∣ Δ ⊢ c ⦂ A0 ⇨ B0
    → Σ ∣ Δ ⊢ c′ ⦂ A1 ⇨ B1
    → Σ ∣ Δ ⊢ c ⊑ᶜ c′
      ----------------
    → A0 ⊑′ A1 × B0 ⊑′ B1
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢idᶜ hA′) (⊑idᶜ A⊑A′) = A⊑A′ , A⊑A′
⊑ᶜ→⊑ (⊢! hG gG) (⊢! hG′ gG′) (⊑! A⊑A′) = A⊑A′ , ⊑′-refl
⊑ᶜ→⊑ (⊢? hG gG) (⊢? hG′ gG′) (⊑? A⊑A′) = ⊑′-refl , A⊑A′
⊑ᶜ→⊑ (⊢conceal hU) (⊢conceal hU′) ⊑⁻
  with ∋ᵁ-unique hU hU′
... | refl = ⊑′-refl , ⊑′-refl
⊑ᶜ→⊑ (⊢reveal hU) (⊢reveal hU′) ⊑⁺
  with ∋ᵁ-unique hU hU′
... | refl = ⊑′-refl , ⊑′-refl
⊑ᶜ→⊑ (⊢↦ cwt dwt) (⊢↦ cwt′ dwt′) (⊑↦ c⊑c′ d⊑d′)
  with ⊑ᶜ→⊑ cwt cwt′ c⊑c′ | ⊑ᶜ→⊑ dwt dwt′ d⊑d′
... | A′⊑A , A″⊑A‴ | B⊑B′ , B″⊑B‴ =
  ⊑′-⇒ A″⊑A‴ B⊑B′ , ⊑′-⇒ A′⊑A B″⊑B‴
⊑ᶜ→⊑ (⊢∀ᶜ cwt) (⊢∀ᶜ cwt′) (⊑∀ᶜ c⊑c′)
  with ⊑ᶜ→⊑ cwt cwt′ c⊑c′
... | A⊑A′ , B⊑B′ = ⊑′-∀ A⊑A′ , ⊑′-∀ B⊑B′
⊑ᶜ→⊑ (⊢⨟ cwt dwt) (⊢⨟ cwt′ dwt′) (⊑⨟ c⊑c′ d⊑d′)
  with ⊑ᶜ→⊑ cwt cwt′ c⊑c′ | ⊑ᶜ→⊑ dwt dwt′ d⊑d′
... | A⊑A′ , _ | _ , C⊑C′ = A⊑A′ , C⊑C′
⊑ᶜ→⊑ (⊢⊥ hA hB) (⊢⊥ hA′ hB′) (⊑⊥ A⊑A′ B⊑B′) = A⊑A′ , B⊑B′

⊑ᶜ→⊑ (⊢idᶜ hA) (⊢! hG gG) (⊑idL! A⊑B A⊑★) = A⊑B , A⊑★
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢? hG gG) (⊑idL? A⊑★ A⊑B) = A⊑★ , A⊑B
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢↦ cwt dwt) (⊑idL↦★ p q)
  with ⊑ᶜ→⊑ (⊢idᶜ wf★) cwt p | ⊑ᶜ→⊑ (⊢idᶜ wf★) dwt q
... | ★⊑A′ , ★⊑A | ★⊑B , ★⊑B′ =
  ★⊑′⇒ ★⊑A ★⊑B , ★⊑′⇒ ★⊑A′ ★⊑B′
⊑ᶜ→⊑ (⊢idᶜ (wf⇒ hA hB)) (⊢↦ cwt dwt) (⊑idL↦ p q)
  with ⊑ᶜ→⊑ (⊢idᶜ hA) cwt p | ⊑ᶜ→⊑ (⊢idᶜ hB) dwt q
... | A⊑A′ , A⊑A″ | A⊑B , A⊑B′ =
  ⊑′-⇒ A⊑A″ A⊑B , ⊑′-⇒ A⊑A′ A⊑B′
⊑ᶜ→⊑ (⊢idᶜ hA) cwt (⊑idL∀★ ★⊑∀A ★⊑∀B p cwt′)
  with coercion-type-unique cwt cwt′
... | refl , refl = ★⊑∀A , ★⊑∀B
⊑ᶜ→⊑ (⊢idᶜ (wf∀ hA)) (⊢∀ᶜ cwt) (⊑idL∀ p)
  with ⊑ᶜ→⊑ (⊢idᶜ hA) cwt p
... | A⊑B , A⊑C = ⊑′-∀ A⊑B , ⊑′-∀ A⊑C
⊑ᶜ→⊑ (⊢idᶜ hA) (⊢⨟ cwt dwt) (⊑idL⨟ p q)
  with ⊑ᶜ→⊑ (⊢idᶜ hA) cwt p | ⊑ᶜ→⊑ (⊢idᶜ hA) dwt q
... | A⊑B , _ | _ , A⊑C = A⊑B , A⊑C

⊑ᶜ→⊑ (⊢! hG gG) (⊢idᶜ hA) (⊑idR! B⊑A ★⊑A) = B⊑A , ★⊑A
⊑ᶜ→⊑ (⊢? hG gG) (⊢idᶜ hA) (⊑idR? ★⊑A B⊑A) = ★⊑A , B⊑A
⊑ᶜ→⊑ (⊢↦ cwt dwt) (⊢idᶜ (wf⇒ hA hB)) (⊑idR↦ p q)
  with ⊑ᶜ→⊑ cwt (⊢idᶜ hA) p | ⊑ᶜ→⊑ dwt (⊢idᶜ hB) q
... | A′⊑A , A⊑A″ | B⊑A‴ , B′⊑A =
  ⊑′-⇒ A⊑A″ B⊑A‴ , ⊑′-⇒ A′⊑A B′⊑A
⊑ᶜ→⊑ (⊢∀ᶜ cwt) (⊢idᶜ (wf∀ hA)) (⊑idR∀ p)
  with ⊑ᶜ→⊑ cwt (⊢idᶜ hA) p
... | A⊑B , C⊑A = ⊑′-∀ A⊑B , ⊑′-∀ C⊑A
⊑ᶜ→⊑ (⊢⨟ cwt dwt) (⊢idᶜ hA) (⊑idR⨟ p q)
  with ⊑ᶜ→⊑ cwt (⊢idᶜ hA) p | ⊑ᶜ→⊑ dwt (⊢idᶜ hA) q
... | A⊑B , _ | _ , C⊑A = A⊑B , C⊑A

⊑ᶜ→⊑ (⊢⨟ (⊢? wfG G-⇒★) c′wt) c⦂ (⊑drop?↦ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | starFun⊑A , B⊑B′ =
  ★⇒★⊑′A→★⊑′A starFun⊑A , B⊑B′
⊑ᶜ→⊑ (⊢⨟ c′wt (⊢! wfG G-⇒★)) c⦂ (⊑drop!↦ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | A⊑A′ , starFun⊑B =
  A⊑A′ , ★⇒★⊑′A→★⊑′A starFun⊑B
⊑ᶜ→⊑ (⊢⨟ (⊢? wfG G-∀★) c′wt) c⦂ (⊑drop?∀ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | starAll⊑A , B⊑B′ =
  ∀★⊑′A→★⊑′A starAll⊑A , B⊑B′
⊑ᶜ→⊑ (⊢⨟ c′wt (⊢! wfG G-∀★)) c⦂ (⊑drop!∀ c′⊑c)
  with ⊑ᶜ→⊑ c′wt c⦂ c′⊑c
... | A⊑A′ , starAll⊑B =
  A⊑A′ , ∀★⊑′A→★⊑′A starAll⊑B

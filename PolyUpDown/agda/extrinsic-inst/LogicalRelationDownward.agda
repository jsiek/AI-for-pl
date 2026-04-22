module LogicalRelationDownward where

-- File Charter:
--   * Experimental downward-closed step-indexed logical relation.
--   * Keeps the existing `LogicalRelation.agda` unchanged.
--   * Uses staged approximants `LR≤ n` so recursion is structurally on `n`.
--   * Exposes the same elimination surface as `LogicalRelation`.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import Types
open import Imprecision
open import UpDown
open import Terms
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)

import LogicalRelation as LR
open LR public hiding
  ( 𝒱
  ; 𝒱′
  ; ℰ
  ; 𝒱-left-value
  ; 𝒱-right-value
  ; 𝒱-core
  ; ℰObs≼
  ; ℰObs≽
  ; observeℰ≼
  ; observeℰ≽
  ; obs≼-stepˡ
  ; obs≼-blameʳ
  ; obs≼-value
  ; obs≽-stepʳ
  ; obs≽-blameʳ
  ; obs≽-value
  )

record LR≤ (n : ℕ) : Set₂ where
  field
    V≤ : ∀ {k A B} → k ≤ n → A ⊑ B → Dir → World → Term → Term → Set₁
    E≤ : ∀ {k A B} → k ≤ n → A ⊑ B → Dir → World → Term → Term → Set₁

mutual
  V-top :
    ∀ {n k A B} →
    LR≤ n →
    k ≤ suc n →
    A ⊑ B →
    Dir →
    World →
    Term →
    Term →
    Set₁
  V-top {k = zero} hist z≤n p dir w V W = Value V × Value W × Lift (lsuc 0ℓ) ⊤
  V-top {k = suc k} hist (s≤s k≤n) p dir w V W =
    Value V × Value W × V-body hist k≤n p dir w V W

  V-body :
    ∀ {n k A B} →
    LR≤ n →
    k ≤ n →
    A ⊑ B →
    Dir →
    World →
    Term →
    Term →
    Set₁
  V-body hist k≤n ⊑-‵ dir w ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)

  V-body {n = n} {k = k} hist k≤n (⊑-⇒ pA pB) dir w V W =
    ∀ {j V′ W′} →
    (j≤k : j ≤ k) →
    LR≤.V≤ hist (≤-trans j≤k k≤n) pA dir w V′ W′ →
    LR≤.E≤ hist (≤-trans j≤k k≤n) pB dir w (V · V′) (W · W′)

  V-body {n = n} {k = k} {A = `∀ A} {B = `∀ B} hist k≤n (⊑-∀ p) dir w V W =
    ∀ {j w′} →
    (j≤k : j ≤ k) →
    w′ ⪰ w →
    (R : Rel) →
    (T U : Ty) →
    LR≤.E≤ hist (≤-trans j≤k k≤n) p dir (extendWorld w′ R)
      (V ⦂∀ A [ T ])
      (W ⦂∀ B [ U ])

  V-body {n = n} {k = k} {A = `∀ A} {B = B} hist k≤n (⊑-ν p) dir w V W =
    ∀ {j w′} →
    (j≤k : j ≤ k) →
    w′ ⪰ w →
    (R : Rel) →
    LR≤.E≤ hist (≤-trans j≤k k≤n) p dir (extendWorld w′ R)
      (V ⦂∀ A [ ｀ length (Σˡ w′) ])
      W

  V-body hist k≤n ⊑-★★ dir w (V up tag G) (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × LR≤.V≤ hist k≤n (⊑-refl {A = G}) dir w V W

  V-body {k = k} hist k≤n ⊑-★★ dir w (V down seal αˡ) (W down seal αʳ) =
    Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × (∀ {j} → j ≤ k → R j dir V W)

  V-body hist k≤n (⊑-★ {G = G} g p) ≼ w V (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × LR≤.V≤ hist k≤n p ≼ w V W

  V-body hist k≤n (⊑-★ {G = G} g p) ≽ w V (W up tag H) =
    Lift (lsuc 0ℓ) (G ≡ H) × LR≤.V≤ hist k≤n p ≽ w V W

  V-body {k = k} hist k≤n (⊑-｀ {α = α}) dir w (V down seal βˡ) (W down seal βʳ) =
    Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
      (η w ∋η α ↔ α ∶ R) ×
      (∀ {j} → j ≤ k → R j dir V W)

  V-body hist k≤n p dir w V W = Lift (lsuc 0ℓ) ⊥

  E-top :
    ∀ {n k A B} →
    LR≤ n →
    k ≤ suc n →
    A ⊑ B →
    Dir →
    World →
    Term →
    Term →
    Set₁
  E-top {k = zero} hist z≤n p dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤

  E-top {k = suc k} hist (s≤s k≤n) p ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      LR≤.E≤ hist k≤n p ≼ (mkWorld Σˡ′ (Σʳ w) (η w)) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      LR≤.V≤ hist k≤n p ≼ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Wʳ)

  E-top {k = suc k} hist (s≤s k≤n) p ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      LR≤.E≤ hist k≤n p ≽ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      LR≤.V≤ hist k≤n p ≽ (mkWorld Σˡ′ (Σʳ w) (η w)) Wˡ Mʳ)

build : (n : ℕ) → LR≤ n
build zero .LR≤.V≤ {zero} z≤n p dir w V W = Value V × Value W × Lift (lsuc 0ℓ) ⊤
build zero .LR≤.V≤ {suc k} ()
build zero .LR≤.E≤ {zero} z≤n p dir w M M′ = Lift (lsuc 0ℓ) ⊤
build zero .LR≤.E≤ {suc k} ()
build (suc n) .LR≤.V≤ {k} k≤ p dir w V W = V-top (build n) k≤ p dir w V W
build (suc n) .LR≤.E≤ {k} k≤ p dir w M M′ = E-top (build n) k≤ p dir w M M′

𝒱 : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱 p n dir w V W = LR≤.V≤ (build n) ≤-refl p dir w V W

𝒱′ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱′ p zero dir w V W = Lift (lsuc 0ℓ) ⊤
𝒱′ p (suc n) dir w V W = V-body (build n) ≤-refl p dir w V W

ℰ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
ℰ p n dir w M M′ = LR≤.E≤ (build n) ≤-refl p dir w M M′

𝒱↓ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
𝒱↓ = 𝒱

ℰ↓ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
ℰ↓ = ℰ

------------------------------------------------------------------------
-- Elimination interface (same surface as `LogicalRelation`)
------------------------------------------------------------------------

𝒱-left-value :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {dir : Dir} {w : World}
    {V W : Term} →
  𝒱 p n dir w V W →
  Value V
𝒱-left-value {n = zero} rel = proj₁ rel
𝒱-left-value {n = suc n} rel = proj₁ rel

𝒱-right-value :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {dir : Dir} {w : World}
    {V W : Term} →
  𝒱 p n dir w V W →
  Value W
𝒱-right-value {n = zero} rel = proj₁ (proj₂ rel)
𝒱-right-value {n = suc n} rel = proj₁ (proj₂ rel)

𝒱-core :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {dir : Dir} {w : World}
    {V W : Term} →
  𝒱 p n dir w V W →
  𝒱′ p n dir w V W
𝒱-core {n = zero} rel = proj₂ (proj₂ rel)
𝒱-core {n = suc n} rel = proj₂ (proj₂ rel)

data ℰObs≼ {A B : Ty} (p : A ⊑ B) (n : ℕ) (w : World)
  (Mˡ Mʳ : Term) : Set₁ where
  obs≼-stepˡ :
    (Σˡ′ : Store) (Mˡ′ : Term) →
    (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) →
    ℰ p n ≼ (mkWorld Σˡ′ (Σʳ w) (η w)) Mˡ′ Mʳ →
    ℰObs≼ p n w Mˡ Mʳ

  obs≼-blameʳ :
    (Σʳ′ : Store) (ℓ : Label) →
    (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ) →
    ℰObs≼ p n w Mˡ Mʳ

  obs≼-value :
    Value Mˡ →
    (Σʳ′ : Store) (Wʳ : Term) →
    (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) →
    𝒱 p n ≼ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Wʳ →
    ℰObs≼ p n w Mˡ Mʳ

data ℰObs≽ {A B : Ty} (p : A ⊑ B) (n : ℕ) (w : World)
  (Mˡ Mʳ : Term) : Set₁ where
  obs≽-stepʳ :
    (Σʳ′ : Store) (Mʳ′ : Term) →
    (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) →
    ℰ p n ≽ (mkWorld (Σˡ w) Σʳ′ (η w)) Mˡ Mʳ′ →
    ℰObs≽ p n w Mˡ Mʳ

  obs≽-blameʳ :
    (Σʳ′ : Store) (ℓ : Label) →
    (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ) →
    ℰObs≽ p n w Mˡ Mʳ

  obs≽-value :
    Value Mʳ →
    (Σˡ′ : Store) (Wˡ : Term) →
    (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) →
    𝒱 p n ≽ (mkWorld Σˡ′ (Σʳ w) (η w)) Wˡ Mʳ →
    ℰObs≽ p n w Mˡ Mʳ

observeℰ≼ :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {w : World} {Mˡ Mʳ : Term} →
  ℰ p (suc n) ≼ w Mˡ Mʳ →
  ℰObs≼ p n w Mˡ Mʳ
observeℰ≼ rel with rel
observeℰ≼ rel | inj₁ red =
  obs≼-stepˡ (proj₁ red) (proj₁ (proj₂ red))
    (proj₁ (proj₂ (proj₂ red))) (proj₂ (proj₂ (proj₂ red)))
observeℰ≼ rel | inj₂ (inj₁ blm) =
  obs≼-blameʳ (proj₁ blm) (proj₁ (proj₂ blm)) (proj₂ (proj₂ blm))
observeℰ≼ rel | inj₂ (inj₂ val) =
  obs≼-value (proj₁ val) (proj₁ (proj₂ val)) (proj₁ (proj₂ (proj₂ val)))
    (proj₁ (proj₂ (proj₂ (proj₂ val)))) (proj₂ (proj₂ (proj₂ (proj₂ val))))

observeℰ≽ :
  ∀ {A B : Ty} {p : A ⊑ B} {n : ℕ} {w : World} {Mˡ Mʳ : Term} →
  ℰ p (suc n) ≽ w Mˡ Mʳ →
  ℰObs≽ p n w Mˡ Mʳ
observeℰ≽ rel with rel
observeℰ≽ rel | inj₁ red =
  obs≽-stepʳ (proj₁ red) (proj₁ (proj₂ red))
    (proj₁ (proj₂ (proj₂ red))) (proj₂ (proj₂ (proj₂ red)))
observeℰ≽ rel | inj₂ (inj₁ blm) =
  obs≽-blameʳ (proj₁ blm) (proj₁ (proj₂ blm)) (proj₂ (proj₂ blm))
observeℰ≽ rel | inj₂ (inj₂ val) =
  obs≽-value (proj₁ val) (proj₁ (proj₂ val)) (proj₁ (proj₂ (proj₂ val)))
    (proj₁ (proj₂ (proj₂ (proj₂ val)))) (proj₂ (proj₂ (proj₂ (proj₂ val))))

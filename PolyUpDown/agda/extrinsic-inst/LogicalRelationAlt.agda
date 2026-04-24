module LogicalRelationAlt where

-- File Charter:
--   * Alternative step-indexed logical relation for `PolyUpDown`.
--   * Avoids well-founded recursion by using direct recursion on the index.
--   * Uses a `V′`-style helper for function types.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
  using (ℕ; zero; suc; _<′_; <′-base; ≤′-step; ≤′-reflexive)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ; lift) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import Types
open import Store using (StoreWf)
open import Imprecision
open import UpDown
open import Terms
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)
open import LogicalRelation
  using
    ( Dir; ≼; ≽; Rel; DownClosed; World; _⪰_; Δ; Ψ; Σˡ; Σʳ; η
    ; _∋η_↔_∶_; extendWorld; mkWorldˡ; mkWorldʳ; ℕ-payload
    )

lift⊤ : Lift (lsuc 0ℓ) ⊤
lift⊤ = lift tt

mutual
  infix 4 𝒱′_⟦_⊢_⇒_⟧

  𝒱′_⟦_⊢_⇒_⟧ :
    ∀ {Aˡ Aʳ Bˡ Bʳ} →
    ℕ → Dir → Aˡ ⊑ Aʳ → Bˡ ⊑ Bʳ → World → Term → Term → Set₁
  𝒱′ zero ⟦ dir ⊢ pA ⇒ pB ⟧ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱′ (suc k) ⟦ dir ⊢ pA ⇒ pB ⟧ w V W =
    (∀ {w′} → w′ ⪰ w → ∀ {V′ W′} →
      𝒱 pA k dir w′ V′ W′ →
      ℰ pB k dir w′ (V · V′) (W · W′))
    ×
    𝒱′ k ⟦ dir ⊢ pA ⇒ pB ⟧ w V W

  𝒱body : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱body (⊑-‵ `ℕ) n dir w V W = ℕ-payload V W
  𝒱body (⊑-‵ `𝔹) n dir w V W = Lift (lsuc 0ℓ) ⊥
  𝒱body {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ}
      (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) n dir w V W =
    𝒱′ n ⟦ dir ⊢ pA ⇒ pB ⟧ w V W
  𝒱body (⊑-∀ Aˡ Aʳ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) → (T U : Ty) →
      ℰ p n dir (extendWorld w′ R downR) (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])
  𝒱body (⊑-ν A′ B′ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      ℰ p n dir (extendWorld w′ R downR) (V ⦂∀ A′ [ ｀ length (Σˡ w′) ]) W

  𝒱body ⊑-★★ zero dir w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ⊑-★★ (suc k) dir w V W = star-rel V W
    where
    star-rel : Term → Term → Set₁
    star-rel (V up tag G) (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 (⊑-refl {A = G}) k dir w V W
    star-rel (V down seal αˡ) (W down seal αʳ) =
      Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × R k dir V W
    star-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱body (⊑-★ _ G g p) zero ≼ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body (⊑-★ _ G g p) zero ≽ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body (⊑-★ _ G g p) (suc k) ≼ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 p k ≼ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥
  𝒱body {A = A} {B = ★} (⊑-★ _ G g p) (suc k) ≽ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 p k ≽ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥

  𝒱body (⊑-｀ α) zero dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R zero dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥
  𝒱body (⊑-｀ α) (suc k) dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R (suc k) dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱body (⊑-＇ X) n dir w V W = Lift (lsuc 0ℓ) ⊥

  ℰbody : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  ℰbody p zero dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤

  ℰbody {A = A} {B = B} p (suc k) ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) (Ψ w) Σˡ′ ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      ℰ p k ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ]
      Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      𝒱 p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ)

  ℰbody {A = A} {B = B} p (suc k) ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      ℰ p k ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) (Ψ w) Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) (Ψ w) Σˡ′ ]
      Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      𝒱 p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ)

  𝒱 : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱 {A = A} {B = B} p n dir w V W =
    Value V × Value W ×
    ((0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ V ⦂ A) ×
     (0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ W ⦂ B)) ×
    𝒱body p n dir w V W

  ℰ : ∀ {A B} → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  ℰ {A = A} {B = B} p n dir w Mˡ Mʳ =
    ((0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A) ×
     (0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B)) ×
    ℰbody p n dir w Mˡ Mʳ

FunAll :
  ∀ {Aˡ Aʳ Bˡ Bʳ} →
  ℕ → Aˡ ⊑ Aʳ → Bˡ ⊑ Bʳ → Dir → World → Term → Term → Set₁
FunAll n pA pB dir w V W =
  ∀ {w′} → w′ ⪰ w → (j : ℕ) → j <′ n →
    ∀ {V′ W′} →
    𝒱 pA j dir w′ V′ W′ →
    ℰ pB j dir w′ (V · V′) (W · W′)

𝒱′→FunAll :
  ∀ {Aˡ Aʳ Bˡ Bʳ n dir w V W} {pA : Aˡ ⊑ Aʳ} {pB : Bˡ ⊑ Bʳ} →
  𝒱′ n ⟦ dir ⊢ pA ⇒ pB ⟧ w V W →
  FunAll n pA pB dir w V W
𝒱′→FunAll {n = zero} V′n w′⪰ j (≤′-reflexive ())
𝒱′→FunAll {n = suc k} (step , rest) w′⪰ j <′-base rel = step w′⪰ rel
𝒱′→FunAll {n = suc k} (step , rest) w′⪰ j (≤′-step j<k) rel =
  𝒱′→FunAll {n = k} rest w′⪰ j j<k rel

FunAll→𝒱′ :
  ∀ {Aˡ Aʳ Bˡ Bʳ n dir w V W} {pA : Aˡ ⊑ Aʳ} {pB : Bˡ ⊑ Bʳ} →
  FunAll n pA pB dir w V W →
  𝒱′ n ⟦ dir ⊢ pA ⇒ pB ⟧ w V W
FunAll→𝒱′ {n = zero} all = lift⊤
FunAll→𝒱′
    {n = suc k} {dir = dir} {w = w} {V = V} {W = W}
    {pA = pA} {pB = pB} all =
  step , rest
  where
  step :
    ∀ {w′} →
    w′ ⪰ w →
    ∀ {V′ W′} →
    𝒱 pA k dir w′ V′ W′ →
    ℰ pB k dir w′ (V · V′) (W · W′)
  step w′⪰ rel = all w′⪰ k <′-base rel

  rest : 𝒱′ k ⟦ dir ⊢ pA ⇒ pB ⟧ w V W
  rest = FunAll→𝒱′ {n = k} all-rest
    where
    all-rest : FunAll k pA pB dir w V W
    all-rest w′⪰ j j<k rel = all w′⪰ j (≤′-step j<k) rel

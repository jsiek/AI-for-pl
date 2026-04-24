module LogicalRelationAlt where

-- File Charter:
--   * Alternative step-indexed logical relation for `PolyUpDown`.
--   * Avoids well-founded recursion by using direct recursion on the index.
--   * Uses a `V′`-style helper for function types.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
  using (ℕ; zero; suc; z<s; _<′_; _≤_; <′-base; ≤′-step; ≤′-reflexive)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ; lift) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types
open import Store using (_⊆ˢ_; ⊆ˢ-trans; StoreWf; substStoreᵗ)
open import Imprecision
open import TypeProperties
  using (liftSubstˢ; substᵗ-ν-src; substᵗ-⇑ˢ; substᵗ-id; renameᵗ-substᵗ;
         substᵗ-ground; renameᵗ-preserves-WfTy; renameˢ-preserves-WfTy;
         TyRenameWf-suc; SealRenameWf-suc; TySubstWf)
open import UpDown
open import Terms
open import TermPrecision using (PCtx; TPEnv; extendᴾ)
open import TermProperties using (Substˣ; substˣ-term)
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_; _—→⟨_⟩_)
open import ProgressFresh using (canonical-★; canonical-｀; sv-up-tag; sv-down-seal)
open import LogicalRelation public
  using
    ( Dir; ≼; ≽; Rel; DownClosed; World; mkWorld; _⪰_; Δ; Ψ; Σˡ; Σʳ; wfΣˡ; wfΣʳ; η
    ; _∋η_↔_∶_; extendWorld; mkWorldˡ; mkWorldʳ; mkWorldˡ-⪰; mkWorldʳ-⪰; ℕ-payload
    ; η∋-downClosed; η∋-weaken; ⪰-trans
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

𝒱-left-value :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 p k dir w V W →
  Value V
𝒱-left-value {k = zero} Vrel = proj₁ Vrel
𝒱-left-value {k = suc n} Vrel = proj₁ Vrel

𝒱-right-value :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 p k dir w V W →
  Value W
𝒱-right-value {k = zero} Vrel = proj₁ (proj₂ Vrel)
𝒱-right-value {k = suc n} Vrel = proj₁ (proj₂ Vrel)

wk⪰ˡ :
  ∀ {w w′ A V} →
  w′ ⪰ w →
  0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ V ⦂ A →
  0 ∣ Ψ w′ ∣ Σˡ w′ ∣ [] ⊢ V ⦂ A
wk⪰ˡ w′⪰ V⊢ rewrite _⪰_.growΨ w′⪰ =
  wkΣ-term (_⪰_.growˡ w′⪰) V⊢

wk⪰ʳ :
  ∀ {w w′ A V} →
  w′ ⪰ w →
  0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ V ⦂ A →
  0 ∣ Ψ w′ ∣ Σʳ w′ ∣ [] ⊢ V ⦂ A
wk⪰ʳ w′⪰ V⊢ rewrite _⪰_.growΨ w′⪰ =
  wkΣ-term (_⪰_.growʳ w′⪰) V⊢

𝒱′-⪰ :
  ∀ {Aˡ Aʳ Bˡ Bʳ k dir w w′ V W} {pA : Aˡ ⊑ Aʳ} {pB : Bˡ ⊑ Bʳ} →
  w′ ⪰ w →
  𝒱′ k ⟦ dir ⊢ pA ⇒ pB ⟧ w V W →
  𝒱′ k ⟦ dir ⊢ pA ⇒ pB ⟧ w′ V W
𝒱′-⪰ {k = zero} w′⪰ rel = lift tt
𝒱′-⪰
    {k = suc k} {dir = dir} {w′ = w′} {V = V} {W = W}
    {pA = pA} {pB = pB} w′⪰ (step , rest) =
  step′ , 𝒱′-⪰ {k = k} w′⪰ rest
  where
  step′ :
    ∀ {w″} →
    w″ ⪰ w′ →
    ∀ {V′ W′} →
    𝒱 pA k dir w″ V′ W′ →
    ℰ pB k dir w″ (V · V′) (W · W′)
  step′ w″⪰ rel = step (⪰-trans w″⪰ w′⪰) rel

𝒱-⪰ :
  ∀ {A B n dir w w′ V W} (p : A ⊑ B) →
  w′ ⪰ w →
  𝒱 p n dir w V W →
  𝒱 p n dir w′ V W
𝒱-⪰ {n = zero} (⊑-‵ `ℕ) w′⪰
  (vV , vW , (V⊢ , W⊢) , nat-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , nat-rel
𝒱-⪰ {n = suc k} (⊑-‵ `ℕ) w′⪰
  (vV , vW , (V⊢ , W⊢) , nat-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , nat-rel
𝒱-⪰ {n = zero} (⊑-‵ `𝔹) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift ())
𝒱-⪰ {n = suc k} (⊑-‵ `𝔹) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift ())
𝒱-⪰ {n = zero} (⊑-＇ X) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift ())
𝒱-⪰ {n = suc k} (⊑-＇ X) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift ())
𝒱-⪰ {n = zero} ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift⊤
𝒱-⪰ {n = suc k} {dir = dir} ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-★ vV V⊢ | canonical-★ vW W⊢
𝒱-⪰ {n = suc k} {dir = dir} ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = U} {G = G} vU eqV
  | sv-up-tag {W = U′} {G = H} vU′ eqW
  rewrite eqV | eqW with rel
𝒱-⪰ {n = suc k} {dir = dir} ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = U} {G = G} vU eqV
  | sv-up-tag {W = U′} {G = H} vU′ eqW
  | eqG , inner =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqG , 𝒱-⪰ {n = k} {dir = dir} (⊑-refl {A = G}) w′⪰ inner
𝒱-⪰ {n = zero} {dir = ≼} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift⊤
𝒱-⪰ {n = zero} {dir = ≽} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift⊤
𝒱-⪰ {n = suc k} {dir = ≼} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-★ vW W⊢
𝒱-⪰ {n = suc k} {dir = ≼} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  rewrite eqW with rel
𝒱-⪰ {n = suc k} {dir = ≼} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  | eqG , inner =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqG , 𝒱-⪰ {n = k} {dir = ≼} p w′⪰ inner
𝒱-⪰ {n = suc k} {dir = ≽} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-★ vW W⊢
𝒱-⪰ {n = suc k} {dir = ≽} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  rewrite eqW with rel
𝒱-⪰ {n = suc k} {dir = ≽} (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  | eqG , inner =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqG , 𝒱-⪰ {n = k} {dir = ≽} p w′⪰ inner
𝒱-⪰ {n = zero} (⊑-｀ α) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
𝒱-⪰ {n = zero} (⊑-｀ α) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  rewrite eqV | eqW with rel
𝒱-⪰ {n = zero} (⊑-｀ α) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  | eqˡ , eqʳ , R , η∋ , Rrel =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqˡ , eqʳ , R , η∋-weaken (_⪰_.growη w′⪰) η∋ , Rrel
𝒱-⪰ {n = suc k} (⊑-｀ α) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
𝒱-⪰ {n = suc k} (⊑-｀ α) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  rewrite eqV | eqW with rel
𝒱-⪰ {n = suc k} (⊑-｀ α) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  | eqˡ , eqʳ , R , η∋ , Rrel =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqˡ , eqʳ , R , η∋-weaken (_⪰_.growη w′⪰) η∋ , Rrel
𝒱-⪰ {n = n} (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) w′⪰
  (vV , vW , (V⊢ , W⊢) , fun-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , 𝒱′-⪰ {k = n} w′⪰ fun-rel
𝒱-⪰ {n = n} (⊑-∀ Aˡ Aʳ p) w′⪰
  (vV , vW , (V⊢ , W⊢) , all-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    λ {w″} w″⪰ R downR T U →
      all-rel (⪰-trans w″⪰ w′⪰) R downR T U
𝒱-⪰ {n = n} (⊑-ν Aˡ Bʳ p) w′⪰
  (vV , vW , (V⊢ , W⊢) , nu-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    λ {w″} w″⪰ R downR →
      nu-rel (⪰-trans w″⪰ w′⪰) R downR

ℰ-expand-≼-left :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {w : World} {Mˡ Mˡ′ Mʳ} →
  0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A →
  0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B →
  Σˡ w ∣ Mˡ —→ Σˡ w ∣ Mˡ′ →
  ℰ p k ≼ w Mˡ′ Mʳ →
  ℰ p (suc k) ≼ w Mˡ Mʳ
ℰ-expand-≼-left
  {w = mkWorld Δ Ψ Σˡ Σʳ wfΣˡ wfΣʳ η}
  Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′ rel =
  (Mˡ⊢ , Mʳ⊢) , inj₁ (Σˡ , wfΣˡ , _ , Mˡ→Mˡ′ , rel)

ℰ-expand-≽-right :
  ∀ {A B} {p : A ⊑ B} {k : ℕ} {w : World} {Mˡ Mʳ Mʳ′} →
  0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A →
  0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B →
  Σʳ w ∣ Mʳ —→ Σʳ w ∣ Mʳ′ →
  ℰ p k ≽ w Mˡ Mʳ′ →
  ℰ p (suc k) ≽ w Mˡ Mʳ
ℰ-expand-≽-right
  {w = mkWorld Δ Ψ Σˡ Σʳ wfΣˡ wfΣʳ η}
  Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′ rel =
  (Mˡ⊢ , Mʳ⊢) , inj₁ (Σʳ , wfΣʳ , _ , Mʳ→Mʳ′ , rel)

mutual
  ℰ-expand-≼-right :
    ∀ {A B} {p : A ⊑ B} {k : ℕ} {w : World} {Mˡ Mʳ Mʳ′} →
    0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A →
    0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B →
    Σʳ w ∣ Mʳ —→ Σʳ w ∣ Mʳ′ →
    ℰ p k ≼ w Mˡ Mʳ′ →
    ℰ p k ≼ w Mˡ Mʳ
  ℰ-expand-≼-right {k = zero} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′ rel =
    (Mˡ⊢ , Mʳ⊢) , lift tt
  ℰ-expand-≼-right {p = p} {k = suc k} {w = w} {Mʳ = Mʳ}
    {Mʳ′ = Mʳ′} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₁ (Σˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ , rel)) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₁
      (Σˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ ,
        ℰ-expand-≼-right {p = p} {k = k}
          {w = mkWorldˡ w Σˡ′ wfΣˡ′} {Mˡ = Mˡ′}
          {Mʳ = Mʳ} {Mʳ′ = Mʳ′}
          (proj₁ (proj₁ rel)) Mʳ⊢ Mʳ→Mʳ′ rel)
  ℰ-expand-≼-right {k = suc k} {Mʳ = Mʳ} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , Mʳ′↠blame))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂
      (inj₁
        (Σʳ′ , wfΣʳ′ , ℓ ,
         _—→⟨_⟩_ Mʳ Mʳ→Mʳ′ Mʳ′↠blame))
  ℰ-expand-≼-right {k = suc k} {Mʳ = Mʳ} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₂ (inj₂
      (vMˡ , Σʳ′ , wfΣʳ′ , Wʳ , Mʳ′↠Wʳ , rel))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₂
      (vMˡ , Σʳ′ , wfΣʳ′ , Wʳ ,
       _—→⟨_⟩_ Mʳ Mʳ→Mʳ′ Mʳ′↠Wʳ ,
       rel))

  ℰ-expand-≽-left :
    ∀ {A B} {p : A ⊑ B} {k : ℕ} {w : World} {Mˡ Mˡ′ Mʳ} →
    0 ∣ Ψ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ A →
    0 ∣ Ψ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ B →
    Σˡ w ∣ Mˡ —→ Σˡ w ∣ Mˡ′ →
    ℰ p k ≽ w Mˡ′ Mʳ →
    ℰ p k ≽ w Mˡ Mʳ
  ℰ-expand-≽-left {k = zero} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′ rel =
    (Mˡ⊢ , Mʳ⊢) , lift tt
  ℰ-expand-≽-left {p = p} {k = suc k} {w = w} {Mˡ = Mˡ}
    {Mˡ′ = Mˡ′} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₁ (Σʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ , rel)) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₁
      (Σʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ ,
        ℰ-expand-≽-left {p = p} {k = k}
          {w = mkWorldʳ w Σʳ′ wfΣʳ′} {Mˡ = Mˡ}
          {Mˡ′ = Mˡ′} {Mʳ = Mʳ′}
          Mˡ⊢ (proj₂ (proj₁ rel)) Mˡ→Mˡ′ rel)
  ℰ-expand-≽-left {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , Mʳ↠blame))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , Mʳ↠blame))
  ℰ-expand-≽-left {k = suc k} {Mˡ = Mˡ} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMʳ , Σˡ′ , wfΣˡ′ , Wˡ , Mˡ′↠Wˡ , rel))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₂
      (vMʳ , Σˡ′ , wfΣˡ′ , Wˡ ,
       _—→⟨_⟩_ Mˡ Mˡ→Mˡ′ Mˡ′↠Wˡ ,
       rel))

------------------------------------------------------------------------
-- Environment interpretation for open terms
------------------------------------------------------------------------

WfTyClosedᵗ : TyCtx → Ty → Set
WfTyClosedᵗ Δ A = Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

record RelSub (Δ : TyCtx) : Set₁ where
  field
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ Δ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ Δ (rightᵗ X)
    precᵗ : (X : TyVar) → leftᵗ X ⊑ rightᵗ X
open RelSub public

∅ρ : RelSub 0
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑-‵ `ℕ

shift-substᵗ : (A : Ty) → substᵗ (λ X → ＇ suc X) A ≡ renameᵗ suc A
shift-substᵗ A = trans (sym (renameᵗ-substᵗ suc (λ X → ＇ X) A))
                        (cong (renameᵗ suc) (substᵗ-id A))

⇑ᵗρ : ∀ {Δ} → RelSub Δ → RelSub (suc Δ)
(⇑ᵗρ ρ .leftᵗ) = extsᵗ (leftᵗ ρ)
(⇑ᵗρ ρ .rightᵗ) = extsᵗ (rightᵗ ρ)
(⇑ᵗρ ρ .left-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .left-closed) (suc X) =
  let Ψ , wfA = left-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .right-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .right-closed) (suc X) =
  let Ψ , wfA = right-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .precᵗ) zero = ⊑-＇ zero
(⇑ᵗρ ρ .precᵗ) (suc X) =
  cast-⊑ (shift-substᵗ (leftᵗ ρ X))
          (shift-substᵗ (rightᵗ ρ X))
          (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) (precᵗ ρ X))

⇑ˢρ : ∀ {Δ} → RelSub Δ → RelSub Δ
(⇑ˢρ ρ .leftᵗ) = liftSubstˢ (leftᵗ ρ)
(⇑ˢρ ρ .rightᵗ) = liftSubstˢ (rightᵗ ρ)
(⇑ˢρ ρ .left-closed) X =
  let Ψ , wfA = left-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .right-closed) X =
  let Ψ , wfA = right-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .precᵗ) X = renameˢ-⊑ suc (precᵗ ρ X)

substᴿ-⊑ :
  ∀ {Δ} →
  (ρ : RelSub Δ) →
  ∀ {A B} →
  A ⊑ B →
  substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) B
substᴿ-⊑ ρ ⊑-★★ = ⊑-★★
substᴿ-⊑ ρ (⊑-★ A G g p) =
  ⊑-★
    (substᵗ (leftᵗ ρ) A)
    (substᵗ (rightᵗ ρ) G)
    (substᵗ-ground (rightᵗ ρ) g)
    (substᴿ-⊑ ρ p)
substᴿ-⊑ ρ (⊑-＇ X) = precᵗ ρ X
substᴿ-⊑ ρ (⊑-｀ α) = ⊑-｀ α
substᴿ-⊑ ρ (⊑-‵ ι) = ⊑-‵ ι
substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ p q) =
  ⊑-⇒
    (substᵗ (leftᵗ ρ) A)
    (substᵗ (rightᵗ ρ) A′)
    (substᵗ (leftᵗ ρ) B)
    (substᵗ (rightᵗ ρ) B′)
    (substᴿ-⊑ ρ p)
    (substᴿ-⊑ ρ q)
substᴿ-⊑ ρ (⊑-∀ A B p) =
  ⊑-∀
    (substᵗ (extsᵗ (leftᵗ ρ)) A)
    (substᵗ (extsᵗ (rightᵗ ρ)) B)
    (substᴿ-⊑ (⇑ᵗρ ρ) p)
substᴿ-⊑ ρ (⊑-ν A B p) =
  ⊑-ν
    (substᵗ (extsᵗ (leftᵗ ρ)) A)
    (substᵗ (rightᵗ ρ) B)
    (cast-⊑ (substᵗ-ν-src (leftᵗ ρ) A)
             (substᵗ-⇑ˢ (rightᵗ ρ) B)
             (substᴿ-⊑ (⇑ˢρ ρ) p))

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

∅γ : RelEnv
(∅γ .leftˣ) x = ` x
(∅γ .rightˣ) x = ` x

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

𝒢 : PCtx → ℕ → Dir → World → RelSub 0 → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) n dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  (substᵗᵐ (leftᵗ ρ) (leftˣ γ zero) ≡ leftˣ γ zero) ×
  (substᵗᵐ (rightᵗ ρ) (rightˣ γ zero) ≡ rightˣ γ zero) ×
  𝒢 Γ n dir w ρ (⇓γ γ)

record RelWf (E : TPEnv) (w : World) (ρ : RelSub 0) : Set where
  field
    Ψ≡ : TPEnv.Ψ E ≡ Ψ w
    leftᵗ-wf : TySubstWf (TPEnv.Δ E) 0 (Ψ w) (leftᵗ ρ)
    rightᵗ-wf : TySubstWf (TPEnv.Δ E) 0 (Ψ w) (rightᵗ ρ)
    storeˡ : substStoreᵗ (leftᵗ ρ) (TPEnv.store E) ⊆ˢ Σˡ w
    storeʳ : substStoreᵗ (rightᵗ ρ) (TPEnv.store E) ⊆ˢ Σʳ w
open RelWf public

Ψ≤ : ∀ {E w ρ} → RelWf E w ρ → TPEnv.Ψ E ≤ Ψ w
Ψ≤ wf rewrite Ψ≡ wf = ≤-refl

RelWf-extend :
  ∀ {E P w ρ} →
  RelWf E w ρ →
  RelWf (extendᴾ E P) w ρ
RelWf-extend wf .RelWf.Ψ≡ = Ψ≡ wf
RelWf-extend wf .RelWf.leftᵗ-wf = leftᵗ-wf wf
RelWf-extend wf .RelWf.rightᵗ-wf = rightᵗ-wf wf
RelWf-extend wf .RelWf.storeˡ = storeˡ wf
RelWf-extend wf .RelWf.storeʳ = storeʳ wf

RelWf-⪰ :
  ∀ {E w w′ ρ} →
  w′ ⪰ w →
  RelWf E w ρ →
  RelWf E w′ ρ
RelWf-⪰ w′⪰ wf .RelWf.Ψ≡ =
  trans (Ψ≡ wf) (sym (_⪰_.growΨ w′⪰))
RelWf-⪰ w′⪰ wf .RelWf.leftᵗ-wf rewrite _⪰_.growΨ w′⪰ =
  leftᵗ-wf wf
RelWf-⪰ w′⪰ wf .RelWf.rightᵗ-wf rewrite _⪰_.growΨ w′⪰ =
  rightᵗ-wf wf
RelWf-⪰ w′⪰ wf .RelWf.storeˡ =
  ⊆ˢ-trans (storeˡ wf) (_⪰_.growˡ w′⪰)
RelWf-⪰ w′⪰ wf .RelWf.storeʳ =
  ⊆ˢ-trans (storeʳ wf) (_⪰_.growʳ w′⪰)

_∣_⊨_⊑_⦂_ : TPEnv → Dir → Term → Term → ∀ {A B} → A ⊑ B → Set₁
E ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub 0) (γ : RelEnv) →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  ℰ (substᴿ-⊑ ρ p) n dir w
    (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
    (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))

_⊨_⊑_⦂_ : TPEnv → Term → Term → ∀ {A B} → A ⊑ B → Set₁
E ⊨ M ⊑ M′ ⦂ p = (E ∣ ≼ ⊨ M ⊑ M′ ⦂ p) × (E ∣ ≽ ⊨ M ⊑ M′ ⦂ p)

proj⊨ :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  E ⊨ M ⊑ M′ ⦂ p →
  E ∣ dir ⊨ M ⊑ M′ ⦂ p
proj⊨ ≼ rel = proj₁ rel
proj⊨ ≽ rel = proj₂ rel

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

mutual
  𝒱-monotone :
    ∀ A B (p : A ⊑ B) k dir w V W →
    𝒱 p (suc k) dir w V W →
    𝒱 p k dir w V W
  𝒱-monotone .(‵ `ℕ) .(‵ `ℕ) (⊑-‵ `ℕ) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , nat-rel) =
    vV , vW , (V⊢ , W⊢) , nat-rel
  𝒱-monotone .(‵ `ℕ) .(‵ `ℕ) (⊑-‵ `ℕ) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , nat-rel) =
    vV , vW , (V⊢ , W⊢) , nat-rel
  𝒱-monotone .(‵ `𝔹) .(‵ `𝔹) (⊑-‵ `𝔹) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , lift ())
  𝒱-monotone .(‵ `𝔹) .(‵ `𝔹) (⊑-‵ `𝔹) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , lift ())
  𝒱-monotone .(＇ _) .(＇ _) (⊑-＇ X) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , lift ())
  𝒱-monotone .(＇ _) .(＇ _) (⊑-＇ X) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , lift ())
  𝒱-monotone .(★) .(★) ⊑-★★ zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    with canonical-★ vV V⊢ | canonical-★ vW W⊢
  𝒱-monotone .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-up-tag {W = U} {G = G} vU eqV
    | sv-up-tag {W = U′} {G = H} vU′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-up-tag {W = U} {G = G} vU eqV
    | sv-up-tag {W = U′} {G = H} vU′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-monotone G G (⊑-refl {A = G}) k dir w U U′ inner
  𝒱-monotone A .(★) (⊑-★ _ G g p) zero ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone A .(★) (⊑-★ _ G g p) zero ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    with canonical-★ vW W⊢
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    rewrite eqW with star-rel
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-monotone A G p k ≼ w V W′ inner
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    with canonical-★ vW W⊢
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    rewrite eqW with star-rel
  𝒱-monotone A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-monotone A G p k ≽ w V W′ inner
  𝒱-monotone A B (⊑-｀ α) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱-monotone A B (⊑-｀ α) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone A B (⊑-｀ α) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    | eqˡ , eqʳ , R , η∋ , Rrel =
    vV , vW , (V⊢ , W⊢) ,
      eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱-monotone A B (⊑-｀ α) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱-monotone A B (⊑-｀ α) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone A B (⊑-｀ α) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    | eqˡ , eqʳ , R , η∋ , Rrel =
    vV , vW , (V⊢ , W⊢) ,
      eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱-monotone A B (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) k dir w V W
    (vV , vW , (V⊢ , W⊢) , fun-rel) =
    vV , vW , (V⊢ , W⊢) , proj₂ fun-rel
  𝒱-monotone A B (⊑-∀ Aˡ Aʳ p) k dir w V W
    (vV , vW , (V⊢ , W⊢) , all-rel) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) T U →
        ℰ-monotone _ _ p k dir (extendWorld w′ R downR)
          (V ⦂∀ Aˡ [ T ]) (W ⦂∀ Aʳ [ U ])
          (all-rel w⪰ R downR T U)
  𝒱-monotone .(`∀ _) B (⊑-ν Aˡ Bʳ p) k dir w V W
    (vV , vW , (V⊢ , W⊢) , nu-rel) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) →
        ℰ-monotone _ _ p k dir (extendWorld w′ R downR)
          (V ⦂∀ Aˡ [ ｀ length (Σˡ w′) ]) W
          (nu-rel w⪰ R downR)

  ℰ-monotone :
    ∀ A B (p : A ⊑ B) k dir w Mˡ Mʳ →
    ℰ p (suc k) dir w Mˡ Mʳ →
    ℰ p k dir w Mˡ Mʳ
  ℰ-monotone A B p zero ≼ w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , rel) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone A B p zero ≽ w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , rel) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₁ (Σˡ′ , wfΣˡ′ , Mˡ′ , step , rel′)) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₁ (Σˡ′ , wfΣˡ′ , Mˡ′ , step ,
        ℰ-monotone A B p k ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ rel′)
  ℰ-monotone A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰ-monotone A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ′ , wfΣʳ′ , Wʳ , steps , Vrel))) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ′ , wfΣʳ′ , Wʳ , steps ,
        𝒱-monotone A B p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ Vrel))
  ℰ-monotone A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₁ (Σʳ′ , wfΣʳ′ , Mʳ′ , step , rel′)) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₁ (Σʳ′ , wfΣʳ′ , Mʳ′ , step ,
        ℰ-monotone A B p k ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′ rel′)
  ℰ-monotone A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰ-monotone A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMʳ , Σˡ′ , wfΣˡ′ , Wˡ , steps , Vrel))) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMʳ , Σˡ′ , wfΣˡ′ , Wˡ , steps ,
        𝒱-monotone A B p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ Vrel))

𝒱-lower :
  ∀ {n j A B} (j<n : j <′ n) {p : A ⊑ B} {dir w V W} →
  𝒱 p n dir w V W →
  𝒱 p j dir w V W
𝒱-lower {n = zero} (≤′-reflexive ()) rel
𝒱-lower
    {n = suc n} {A = A} {B = B} <′-base
    {p = p} {dir = dir} {w = w} {V = V} {W = W} rel =
  𝒱-monotone A B p n dir w V W rel
𝒱-lower
    {n = suc n} {A = A} {B = B} (≤′-step j<n)
    {p = p} {dir = dir} {w = w} {V = V} {W = W} rel =
  𝒱-lower j<n {p = p} {dir = dir} {w = w} {V = V} {W = W}
    (𝒱-monotone A B p n dir w V W rel)

ℰ-lower :
  ∀ {n j A B} (j<n : j <′ n) {p : A ⊑ B} {dir w Mˡ Mʳ} →
  ℰ p n dir w Mˡ Mʳ →
  ℰ p j dir w Mˡ Mʳ
ℰ-lower {n = zero} (≤′-reflexive ()) rel
ℰ-lower
    {n = suc n} {A = A} {B = B} <′-base
    {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ} rel =
  ℰ-monotone A B p n dir w Mˡ Mʳ rel
ℰ-lower
    {n = suc n} {A = A} {B = B} (≤′-step j<n)
    {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ} rel =
  ℰ-lower j<n {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ}
    (ℰ-monotone A B p n dir w Mˡ Mʳ rel)

module intrinsic-subst.proof.FreeTheorems where

-- File Charter:
--   * Private proofs of two free theorems, from the fundamental theorem
--     (intrinsic-subst/proof/Parametricity.agda) and so under its
--     hypothesis `CompatInst`:
--       - `free-theorem-id`: a term of type `∀α. α → α`, instantiated and
--         applied to a value, returns that value;
--       - `free-theorem-rep`: a term of type `∀α. α → (α → α) → α`,
--         instantiated at `Bool` with `true` and `neg` and at `Nat` with 1
--         and `flip`, returns related results (representation
--         independence).

open import Level using (Lift; lift; zero)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym;
  subst)
open import Relation.Binary.HeterogeneousEquality using (≅-to-≡)

open import intrinsic-subst.Types
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction
open import intrinsic-subst.Parametricity
open import intrinsic-subst.FreeTheorems
open import intrinsic-subst.proof.Parametricity

-- neg and flip are related at α → α when α is interpreted by R
neg-flip-related :
  𝒱 (` Z ⇒ ` Z) (extendRelSub (ρ∅ {zero}) `Bool `Nat R) neg flip V-ƛ V-ƛ
neg-flip-related V-true V-zero (lift (Level.lift ()))
neg-flip-related V-true (V-suc V-zero) _ =
  ⟨ `false , ⟨ `zero , ⟨ V-false , ⟨ V-zero
  , ⟨ (`if `true then `false else `true
      —→⟨ β-true ⟩
        `false
      ∎)
  , ⟨ (`case-nat (`suc `zero) (`suc `zero) `zero
      —→⟨ β-suc V-zero ⟩
        `zero
      ∎)
  , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related V-true (V-suc (V-suc w)) (lift (Level.lift ()))
neg-flip-related V-false V-zero _ =
  ⟨ `true , ⟨ `suc `zero , ⟨ V-true , ⟨ V-suc V-zero
  , ⟨ (`if `false then `false else `true
      —→⟨ β-false ⟩
        `true
      ∎)
  , ⟨ (`case-nat `zero (`suc `zero) `zero
      —→⟨ β-zero ⟩
        `suc `zero
      ∎)
  , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
neg-flip-related V-false (V-suc w) (lift (Level.lift ()))

module FreeTheoremProofs (compat-∙ : CompatInst) where

  open Fundamental (λ {ℓ} {Δ} {Γ} {A} {M} → compat-∙ {ℓ} {Δ} {Γ} {A} {M})

  -- a closed term of a closed type is related to itself
  closed-rel : ∀ {A} (M : ∅ ∣ ∅ ⊢ A)
    → ℰ A (ρ∅ {zero}) (close₁ (e∅ {zero}) M) (close₁ (e∅ {zero}) M)
  closed-rel M = fundamental zero M (ρ∅ {zero}) (e∅ {zero}) (g∅ {zero})

  free-theorem-id : ∀ (M : ∅ ∣ ∅ ⊢ `∀ (` Z ⇒ ` Z)) (A : Type ∅)
    (V : ∅ ∣ ∅ ⊢ A)
    → Value V
    → M ∙ A · V —↠ V
  free-theorem-id M A V v
    with subst (λ X → ℰ (`∀ (` Z ⇒ ` Z)) (ρ∅ {zero}) X X)
           (≅-to-≡ (close∅-≅ {ℓ = zero} M)) (closed-rel M)
  ... | ⟨ _ , ⟨ _ , ⟨ V-Λ {N = N} , ⟨ V-Λ , ⟨ M↠ΛN , ⟨ _ , f ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with f A A (λ V₁ W₁ _ _ → V₁ ≡ V × W₁ ≡ V)
  ... | ⟨ _ , ⟨ _ , ⟨ V-ƛ {N = P} , ⟨ V-ƛ , ⟨ N↠ƛP , ⟨ _ , g ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with g v v (lift ⟨ refl , refl ⟩)
  ... | ⟨ U , ⟨ _ , ⟨ _ , ⟨ _ , ⟨ P↠U , ⟨ _ , lift ⟨ U≡V , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    subst (λ X → M ∙ A · V —↠ X) U≡V
      (↠-trans (·₁-↠ (∙-↠ M↠ΛN))
        (Λ N ∙ A · V
        —→⟨ ξ-·₁ β-Λ ⟩
          ↠-trans (·₁-↠ (subst (λ X → X —↠ ƛ A ˙ P)
                           (conv-refl _ (N [ A ]ᵀ)) N↠ƛP))
            ((ƛ A ˙ P) · V
            —→⟨ β-ƛ v ⟩
              P↠U)))

  free-theorem-rep :
    ∀ (M : ∅ ∣ ∅ ⊢ `∀ (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z))
    → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
        (M ∙ `Bool · `true · neg —↠ V)
      × (M ∙ `Nat · (`suc `zero) · flip —↠ W)
      × R V W v w
  free-theorem-rep M
    with subst (λ X → ℰ (`∀ (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z)) (ρ∅ {zero}) X X)
           (≅-to-≡ (close∅-≅ {ℓ = zero} M)) (closed-rel M)
  ... | ⟨ _ , ⟨ _ , ⟨ V-Λ {N = N₁} , ⟨ V-Λ {N = N₂}
      , ⟨ M↠₁ , ⟨ M↠₂ , f ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with f `Bool `Nat R
  ... | ⟨ _ , ⟨ _ , ⟨ V-ƛ {N = P₁} , ⟨ V-ƛ {N = P₂}
      , ⟨ N↠₁ , ⟨ N↠₂ , g ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with g V-true (V-suc V-zero) _
  ... | ⟨ _ , ⟨ _ , ⟨ V-ƛ {N = Q₁} , ⟨ V-ƛ {N = Q₂}
      , ⟨ P↠₁ , ⟨ P↠₂ , h ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with h V-ƛ V-ƛ neg-flip-related
  ... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ Q↠₁ , ⟨ Q↠₂ , lift r ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w
    , ⟨ ↠-trans (·₁-↠ (·₁-↠ (∙-↠ M↠₁)))
          (Λ N₁ ∙ `Bool · `true · neg
          —→⟨ ξ-·₁ (ξ-·₁ β-Λ) ⟩
            ↠-trans (·₁-↠ (·₁-↠ (subst (λ X → X —↠ ƛ `Bool ˙ P₁)
                                   (conv-refl _ (N₁ [ `Bool ]ᵀ)) N↠₁)))
              ((ƛ `Bool ˙ P₁) · `true · neg
              —→⟨ ξ-·₁ (β-ƛ V-true) ⟩
                ↠-trans (·₁-↠ P↠₁)
                  ((ƛ (`Bool ⇒ `Bool) ˙ Q₁) · neg
                  —→⟨ β-ƛ V-ƛ ⟩
                    Q↠₁)))
    , ⟨ ↠-trans (·₁-↠ (·₁-↠ (∙-↠ M↠₂)))
          (Λ N₂ ∙ `Nat · (`suc `zero) · flip
          —→⟨ ξ-·₁ (ξ-·₁ β-Λ) ⟩
            ↠-trans (·₁-↠ (·₁-↠ (subst (λ X → X —↠ ƛ `Nat ˙ P₂)
                                   (conv-refl _ (N₂ [ `Nat ]ᵀ)) N↠₂)))
              ((ƛ `Nat ˙ P₂) · (`suc `zero) · flip
              —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
                ↠-trans (·₁-↠ P↠₂)
                  ((ƛ (`Nat ⇒ `Nat) ˙ Q₂) · flip
                  —→⟨ β-ƛ V-ƛ ⟩
                    Q↠₂)))
    , r ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

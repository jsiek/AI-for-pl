module proof.TermSubst where

-- File Charter:
--   * Private term-renaming and substitution lemmas used by type safety.
--   * Boundaries remain term-closed; casts recurse only through their term.
--   * Values are preserved by ordinary renaming and substitution.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; subst)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst

------------------------------------------------------------------------
-- 3. Term-variable renaming
------------------------------------------------------------------------

extⁿ : (Var → Var) → Var → Var
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (Var → Var) → Term → Term
renⁿ ρ (` x)          = ` (ρ x)
renⁿ ρ ($ n)          = $ n
renⁿ ρ `true           = `true
renⁿ ρ `false          = `false
renⁿ ρ (ƛ A ∙ N)      = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)        = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)          = Λ (renⁿ ρ N)
renⁿ ρ (ν A · L ⟨ c ⟩) = ν A · renⁿ ρ L ⟨ c ⟩
renⁿ ρ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫
renⁿ ρ (M ⟨ μ ∣ p ⟩)  = renⁿ ρ M ⟨ μ ∣ p ⟩
renⁿ ρ (blame ℓ)      = blame ℓ

shiftᵐ : Term → Term
shiftᵐ = renⁿ suc

-- Ordinary-variable renaming never enters a boundary and a variable is
-- never a value, so values are preserved on the nose.
mutual
  simple-renⁿ : ∀ {M} {ρ : Var → Var} → Simple M → Simple (renⁿ ρ M)
  simple-renⁿ S-$     = S-$
  simple-renⁿ S-true  = S-true
  simple-renⁿ S-false = S-false
  simple-renⁿ S-ƛ     = S-ƛ
  simple-renⁿ (S-Λ v) = S-Λ (value-renⁿ v)
  simple-renⁿ (S-cast v inert) = S-cast (value-renⁿ v) inert

  value-renⁿ : ∀ {M} {ρ : Var → Var} → Value M → Value (renⁿ ρ M)
  value-renⁿ (V-simple u) = V-simple (simple-renⁿ u)
  value-renⁿ (V-⟪⟫ u it)  = V-⟪⟫ u it
  value-renⁿ (V-fresh v fresh) = V-fresh v fresh

∋-extⁿ : ∀ {Γ Γ′ A x B} {ρ : Var → Var}
  → (∀ {y C} → Γ ∋ y ⦂ C → Γ′ ∋ ρ y ⦂ C)
  → (A ∷ Γ) ∋ x ⦂ B
  → (A ∷ Γ′) ∋ extⁿ ρ x ⦂ B
∋-extⁿ h here      = here
∋-extⁿ h (there d) = there (h d)

------------------------------------------------------------------------
-- 4. Type-binder transport of term contexts
------------------------------------------------------------------------

∋-map⁻ : ∀ {f : Ty → Ty} {Γ x A′}
  → map f Γ ∋ x ⦂ A′
  → ∃[ A ] ((A′ ≡ f A) × (Γ ∋ x ⦂ A))
∋-map⁻ {Γ = []} ()
∋-map⁻ {Γ = A ∷ Γ} here = A , refl , here
∋-map⁻ {Γ = A ∷ Γ} (there d) with ∋-map⁻ d
∋-map⁻ {Γ = A ∷ Γ} (there d) | B , eq , q = B , eq , there q

∋-⤊ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⤊ Γ ∋ x ⦂ ⇑ᵗ A
∋-⤊ here      = here
∋-⤊ (there d) = there (∋-⤊ d)

⤊-∋ⁿ : ∀ {ρ : Var → Var} {Γ Γ′}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → (∀ {x A} → ⤊ Γ ∋ x ⦂ A → ⤊ Γ′ ∋ ρ x ⦂ A)
⤊-∋ⁿ h d with ∋-map⁻ d
⤊-∋ⁿ h d | A , refl , q = ∋-⤊ (h q)

⊢renⁿ : ∀ {Δ Γ Γ′ M A} {ρ : Var → Var}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ∣ Γ′ ⊢ renⁿ ρ M ⦂ A
⊢renⁿ h (⊢` d) = ⊢` (h d)
⊢renⁿ h ⊢$ = ⊢$
⊢renⁿ h ⊢true = ⊢true
⊢renⁿ h ⊢false = ⊢false
⊢renⁿ h (⊢ƛ w ⊢N) = ⊢ƛ w (⊢renⁿ (∋-extⁿ h) ⊢N)
⊢renⁿ h (⊢· ⊢L ⊢M) = ⊢· (⊢renⁿ h ⊢L) (⊢renⁿ h ⊢M)
⊢renⁿ h (⊢Λ vN ⊢N) = ⊢Λ (value-renⁿ vN) (⊢renⁿ (⤊-∋ⁿ h) ⊢N)
⊢renⁿ h (⊢ν wA rA ⊢L mw ⊢c same wB) =
  ⊢ν wA rA (⊢renⁿ h ⊢L) mw ⊢c same wB
⊢renⁿ h (boundary mwᵥ ⊢M ⊢c sameᵢ sameₑ wE) =
  boundary mwᵥ ⊢M ⊢c sameᵢ sameₑ wE
⊢renⁿ h (⊢cast ⊢M ⊢p len) = ⊢cast (⊢renⁿ h ⊢M) ⊢p len
⊢renⁿ h (⊢blame wA) = ⊢blame wA

renⁿ-id : (ρ : Var → Var) → (∀ x → ρ x ≡ x)
  → (M : Term) → renⁿ ρ M ≡ M
renⁿ-id ρ h (` x) = cong `_ (h x)
renⁿ-id ρ h ($ n) = refl
renⁿ-id ρ h `true = refl
renⁿ-id ρ h `false = refl
renⁿ-id ρ h (ƛ A ∙ N) = cong (ƛ A ∙_) (renⁿ-id (extⁿ ρ) ext-id N)
  where
  ext-id : ∀ x → extⁿ ρ x ≡ x
  ext-id zero    = refl
  ext-id (suc x) = cong suc (h x)
renⁿ-id ρ h (L · M) = cong₂ _·_ (renⁿ-id ρ h L) (renⁿ-id ρ h M)
renⁿ-id ρ h (Λ N) = cong Λ_ (renⁿ-id ρ h N)
renⁿ-id ρ h (ν A · L ⟨ c ⟩) =
  cong (λ L′ → ν A · L′ ⟨ c ⟩) (renⁿ-id ρ h L)
renⁿ-id ρ h (M ⟪ Θ , c ⟫) = refl
renⁿ-id ρ h (M ⟨ μ ∣ p ⟩) =
  cong (λ M′ → M′ ⟨ μ ∣ p ⟩) (renⁿ-id ρ h M)
renⁿ-id ρ h (blame ℓ) = refl

⊢weakenⁿ : ∀ {Δ Γ M A}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ∣ Γ ⊢ M ⦂ A
⊢weakenⁿ {Γ = Γ} {M = M} {A = A} ⊢M =
  subst (λ N → _ ∣ Γ ⊢ N ⦂ A)
        (renⁿ-id TermSubst.idᵗ (λ x → refl) M)
        (⊢renⁿ (λ ()) ⊢M)

------------------------------------------------------------------------
-- 5. Term substitution
------------------------------------------------------------------------

-- Likewise for substitution: a value contains no free ordinary variable
-- at a value position, and boundaries are left alone.
mutual
  simple-substᵐ : ∀ {M} {σ : Var → Img} → Simple M
    → Simple (substᵐ σ M)
  simple-substᵐ S-$     = S-$
  simple-substᵐ S-true  = S-true
  simple-substᵐ S-false = S-false
  simple-substᵐ S-ƛ     = S-ƛ
  simple-substᵐ (S-Λ v) = S-Λ (value-substᵐ v)
  simple-substᵐ (S-cast v inert) = S-cast (value-substᵐ v) inert

  value-substᵐ : ∀ {M} {σ : Var → Img} → Value M → Value (substᵐ σ M)
  value-substᵐ (V-simple u) = V-simple (simple-substᵐ u)
  value-substᵐ (V-⟪⟫ u it)  = V-⟪⟫ u it
  value-substᵐ (V-fresh v fresh) = V-fresh v fresh

------------------------------------------------------------------------
-- 6. Typed images away from type-context transport
------------------------------------------------------------------------

infix 3 _∣_⊢ⁱ_⦂_
data _∣_⊢ⁱ_⦂_ : Ctxᵗ → Ctx → Img → Ty → Set where
  ⊢ivar : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ⁱ ivar x ⦂ A
  ⊢ival : ∀ {Δ Γ W A} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A
    → Δ ∣ Γ ⊢ⁱ ival W A ⦂ A

⊢imgTm : ∀ {Δ Γ i A}
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
  → Δ ∣ Γ ⊢ imgTm i ⦂ A
⊢imgTm (⊢ivar d) = ⊢` d
⊢imgTm (⊢ival w ⊢W) = ⊢weakenⁿ ⊢W

shiftᴵ-⊢ : ∀ {Δ Γ i A B}
  → Δ ∣ Γ ⊢ⁱ i ⦂ B
  → Δ ∣ A ∷ Γ ⊢ⁱ shiftᴵ i ⦂ B
shiftᴵ-⊢ (⊢ivar d) = ⊢ivar (there d)
shiftᴵ-⊢ (⊢ival w ⊢W) = ⊢ival w ⊢W

extᴵ-⊢ : ∀ {σ : Var → Img} {Δ Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B
        → Δ ∣ (A ∷ Γ′) ⊢ⁱ extᴵ σ x ⦂ B)
extᴵ-⊢ h here      = ⊢ivar here
extᴵ-⊢ h (there d) = shiftᴵ-⊢ (h d)

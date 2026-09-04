module strong.Canonical where

-- Canonical forms for values at the runtime term context [] (PLAN.md §5).
--
-- Progress works at an arbitrary TYPE context Δ (ξ-⟪⟫ reduces under a
-- whose body lives at the interior intOf Δ Θ) but always at the EMPTY term
-- context, so a value is a numeral, a ƛ, a Λ, or a wrapped value V ⟪ Θ , B₀ ⟫.
-- The type of the value rules out the constructors that do not fit; only a
-- wrapper can have any type, including a type variable.

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; renameᵀ)

-- V is a wrapped term
Wrapped : Term → Set
Wrapped V = Σ Term λ V′ → Σ BCtx λ Θ → Σ Ty λ B₀ → V ≡ V′ ⟪ Θ , B₀ ⟫

canon-ℕ : ∀ {Δ V} → Value V → Δ ∣ [] ⊢ V ⦂ `ℕ
  → (Σ ℕ λ n → V ≡ $ n) ⊎ Wrapped V
canon-ℕ (V-$ {n}) _ = inj₁ (n , refl)
canon-ℕ (V-⟪⟫ {V'} {Θ} {B₀} v) _ = inj₂ (V' , Θ , B₀ , refl)
canon-ℕ (V-G (G-ƛ)) ()
canon-ℕ (V-G (G-Λ _)) ()

canon-⇒ : ∀ {Δ V A B} → Value V → Δ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → (Σ Ty λ A′ → Σ Term λ N → V ≡ ƛ A′ ∙ N) ⊎ Wrapped V
canon-⇒ (V-$ {n}) ()
canon-⇒ (V-G (G-Λ _)) ()
canon-⇒ (V-G (G-ƛ {A = A} {N = N})) (⊢ƛ dA dN) = inj₁ (A , N , refl)
canon-⇒ (V-⟪⟫ {V'} {Θ} {B₀} v) _ = inj₂ (V' , Θ , B₀ , refl)

canon-∀ : ∀ {Δ V B} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ B
  → (Σ Term λ V′ → V ≡ Λ V′) ⊎ Wrapped V
canon-∀ (V-$ {n}) ()
canon-∀ (V-G (G-ƛ)) ()
canon-∀ (V-G (G-Λ {V = V'} v)) (⊢Λ dN) = inj₁ (V' , refl)
canon-∀ (V-⟪⟫ {V'} {Θ} {B₀} v) _ = inj₂ (V' , Θ , B₀ , refl)


-- the external face of a wrapper is a variable only if its boundary type is
substᵗ-var : ∀ (σ : Substᵗ) B₀ X → substᵗ σ B₀ ≡ ` X → Σ ℕ λ Y → B₀ ≡ ` Y
substᵗ-var σ (` Y) X eq = Y , refl
substᵗ-var σ `ℕ X ()
substᵗ-var σ `𝔹 X ()
substᵗ-var σ (A ⇒ B) X ()
substᵗ-var σ (`∀ A) X ()

-- a value of VARIABLE type is a wrapper whose boundary type is a variable
canon-var : ∀ {Δ V X} → Value V → Δ ∣ [] ⊢ V ⦂ ` X
  → Σ Term λ V′ → Σ BCtx λ Θ → Σ ℕ λ Y → V ≡ V′ ⟪ Θ , ` Y ⟫
canon-var v ⊢V = {!!}

-- type-variable renaming preserves value-hood (needed by TyWrap, whose
-- contractum applies ⇑ᵀ V)
Value-renameᵀ : ∀ {ρ V} → Value V → Value (renameᵀ ρ V)
Value-renameᵀ {ρ} V-$ = V-$
Value-renameᵀ {ρ} (V-G G-ƛ) = V-G G-ƛ
Value-renameᵀ {ρ} (V-G (G-Λ v)) = V-G (G-Λ (Value-renameᵀ {extᵗ ρ} v))
Value-renameᵀ {ρ} (V-⟪⟫ {Θ = Θ} v) =
  V-⟪⟫ (Value-renameᵀ {strong.BReduction.intRen ρ Θ} v)


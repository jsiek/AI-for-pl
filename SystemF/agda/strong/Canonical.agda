module strong.Canonical where

-- Canonical forms for values at the runtime term context [] (PLAN.md §5).
--
-- Progress works at an arbitrary TYPE context Δ (ξ-⟪⟫ reduces under a
-- boundary, whose body lives at the interior intOf Δ Θ) but always at the
-- EMPTY term context, so a value is a numeral, a ƛ, a Λ, or a wrapped value
-- V ⟪ Θ , B₀ ⟫.  The type of the value rules out the constructors that do not
-- fit.
--
-- AFTER THE DECISION-6 INSTALL these SHARPEN, because a wrapper is a value
-- only when its face is INERT and `inert-ext` says an inert face keeps its
-- head constructor when read outward:
--
--   canon-ℕ  a value of type ℕ is a NUMERAL — no wrapper case survives
--            (`baseNotInert`, the paper's field of the same name);
--   canon-𝔹  there is NO value of type 𝔹 at all (the calculus has no
--            boolean introduction form, and no wrapper can export 𝔹);
--   canon-var-conceal  a value of VARIABLE type is a wrapper whose face
--            is a variable the boundary does NOT reveal — the SEALED
--            value.  This is the long-sought sharpening of canon-var: the
--            interior of a reveal-variable-faced boundary is a
--            CONCEAL/ambient-faced wrapper, which is exactly the redex
--            shape Merge is stated on.

open import Data.Nat using (ℕ; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import strong.Types
open import strong.Context using (TCtx)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; renameᵀ;
         Inert; I-⇒; I-∀; I-var; inert-ext;
         baseNotInert-ℕ; baseNotInert-𝔹; env-ty)

-- V is a wrapped term
Wrapped : Term → Set
Wrapped V = Σ Term λ V′ → Σ BCtx λ Θ → Σ Ty λ B₀ → V ≡ V′ ⟪ Θ , B₀ ⟫

-- a value of type ℕ is a numeral.  A wrapper would need an ℕ-exporting
-- INERT face, and baseNotInert-ℕ says there is none.
canon-ℕ : ∀ {Δ V} → Value V → Δ ∣ [] ⊢ V ⦂ `ℕ → Σ ℕ λ n → V ≡ $ n
canon-ℕ v ⊢V = go v ⊢V refl
  where
  -- generalise the type so the derivation can be matched first
  go : ∀ {Δ V T} → Value V → Δ ∣ [] ⊢ V ⦂ T → T ≡ `ℕ
     → Σ ℕ λ n → V ≡ $ n
  go (V-$ {n})       ⊢$       eq = n , refl
  go (V-G G-ƛ)       (⊢ƛ _ _) ()
  go (V-G (G-Λ _))   (⊢Λ _)   ()
  go (V-⟪⟫ {Θ = Θ} {B₀ = B₀} _ i) ⊢W eq =
    ⊥-elim (baseNotInert-ℕ Θ B₀ i (trans-ty (env-ty ⊢W) eq))
    where
    trans-ty : ∀ {T} → T ≡ substᵗ (ρᵇ Θ) B₀ → T ≡ `ℕ
             → substᵗ (ρᵇ Θ) B₀ ≡ `ℕ
    trans-ty refl e = e

-- there is no value of type 𝔹: the calculus has no boolean literal, and
-- no INERT face exports a base type
canon-𝔹 : ∀ {Δ V} → Value V → Δ ∣ [] ⊢ V ⦂ `𝔹 → ⊥
canon-𝔹 v ⊢V = go v ⊢V refl
  where
  go : ∀ {Δ V T} → Value V → Δ ∣ [] ⊢ V ⦂ T → T ≡ `𝔹 → ⊥
  go V-$             ⊢$       ()
  go (V-G G-ƛ)       (⊢ƛ _ _) ()
  go (V-G (G-Λ _))   (⊢Λ _)   ()
  go (V-⟪⟫ {Θ = Θ} {B₀ = B₀} _ i) ⊢W eq =
    baseNotInert-𝔹 Θ B₀ i (trans-ty (env-ty ⊢W) eq)
    where
    trans-ty : ∀ {T} → T ≡ substᵗ (ρᵇ Θ) B₀ → T ≡ `𝔹
             → substᵗ (ρᵇ Θ) B₀ ≡ `𝔹
    trans-ty refl e = e

canon-⇒ : ∀ {Δ V A B} → Value V → Δ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → (Σ Ty λ A′ → Σ Term λ N → V ≡ ƛ A′ ∙ N) ⊎ Wrapped V
canon-⇒ (V-$ {n}) ()
canon-⇒ (V-G (G-Λ _)) ()
canon-⇒ (V-G (G-ƛ {A = A} {N = N})) (⊢ƛ dA dN) = inj₁ (A , N , refl)
canon-⇒ (V-⟪⟫ {V'} {Θ} {B₀} v i) _ = inj₂ (V' , Θ , B₀ , refl)

canon-∀ : ∀ {Δ V B} → Value V → Δ ∣ [] ⊢ V ⦂ `∀ B
  → (Σ Term λ V′ → V ≡ Λ V′) ⊎ Wrapped V
canon-∀ (V-$ {n}) ()
canon-∀ (V-G (G-ƛ)) ()
canon-∀ (V-G (G-Λ {V = V'} v)) (⊢Λ dN) = inj₁ (V' , refl)
canon-∀ (V-⟪⟫ {V'} {Θ} {B₀} v i) _ = inj₂ (V' , Θ , B₀ , refl)


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
canon-var v ⊢V = canon-var′ v ⊢V refl
  where
  -- generalise the type so the derivation can be matched first
  canon-var′ : ∀ {Δ V T X} → Value V → Δ ∣ [] ⊢ V ⦂ T → T ≡ ` X
    → Σ Term λ V′ → Σ BCtx λ Θ → Σ ℕ λ Y → V ≡ V′ ⟪ Θ , ` Y ⟫
  canon-var′ V-$            ⊢$        ()
  canon-var′ (V-G G-ƛ)      (⊢ƛ _ _)  ()
  canon-var′ (V-G (G-Λ _))  (⊢Λ _)    ()
  canon-var′ (V-⟪⟫ {V′} {Θ} {B₀} _ _) (env _ _ _) eq
    with substᵗ-var (ρᵇ Θ) B₀ _ eq
  canon-var′ (V-⟪⟫ {V′} {Θ} {B₀} _ _) (env _ _ _) eq | (Y , refl) =
    V′ , Θ , Y , refl

-- THE SEALED-VALUE CANONICAL FORM.  A value of variable type is a
-- wrapper whose face is a variable the boundary does NOT reveal — a
-- conceal slot or an ambient one.  (If the face were a REVEAL variable
-- the boundary would be ACTIVE and the term would not be a value at all.)
-- This is what progress needs at a reveal-variable face: the body there
-- is typed at ` X, so it is one of these, and Merge's redex shape —
-- inert-faced wrapper inside an active-faced one — is forced.
canon-var-conceal : ∀ {Δ V X} → Value V → Δ ∣ [] ⊢ V ⦂ ` X
  → Σ Term λ V′ → Σ BCtx λ Θ → Σ ℕ λ Y
      → (V ≡ V′ ⟪ Θ , ` Y ⟫) × (revs Θ ≤ Y) × Value V′
canon-var-conceal v ⊢V = go v ⊢V refl
  where
  go : ∀ {Δ V T X} → Value V → Δ ∣ [] ⊢ V ⦂ T → T ≡ ` X
     → Σ Term λ V′ → Σ BCtx λ Θ → Σ ℕ λ Y
         → (V ≡ V′ ⟪ Θ , ` Y ⟫) × (revs Θ ≤ Y) × Value V′
  go V-$           ⊢$       ()
  go (V-G G-ƛ)     (⊢ƛ _ _) ()
  go (V-G (G-Λ _)) (⊢Λ _)   ()
  go (V-⟪⟫ {V′} {Θ} {` Y} v (I-var ge)) (env _ _ _) eq =
    V′ , Θ , Y , refl , ge , v
  go (V-⟪⟫ {V′} {Θ} {A ⇒ B} v I-⇒) (env _ _ _) ()
  go (V-⟪⟫ {V′} {Θ} {`∀ B} v I-∀) (env _ _ _) ()

-- type-variable renaming preserves value-hood.  No reduction rule needs it
-- any more (the direct-combine TyWrap shifts no term — notes/DECISIONS.md,
-- Decision 2 as revised); kept because renameᵀ is still applied to terms by
-- substᵀᵐ's Λ case, so a value-stability fact about it stays wanted.
Value-renameᵀ : ∀ {ρ V} → Value V → Value (renameᵀ ρ V)
Value-renameᵀ {ρ} V-$ = V-$
Value-renameᵀ {ρ} (V-G G-ƛ) = V-G G-ƛ
Value-renameᵀ {ρ} (V-G (G-Λ v)) = V-G (G-Λ (Value-renameᵀ {extᵗ ρ} v))
Value-renameᵀ {ρ} (V-⟪⟫ {Θ = Θ} {B₀ = B₀} v i) =
  V-⟪⟫ (Value-renameᵀ {strong.BReduction.intRen ρ Θ} v)
       (strong.BReduction.Inert-ren ρ (strong.BReduction.intRen ρ Θ)
                                    Θ B₀ i)


module strong.TermSubst where

-- Strong System F — TERM-variable renaming and substitution preserve typing.
--
-- This is step 3c of strong/PLAN.md: the last piece needed for the Beta case of
-- preservation.  Everything here is about the TERM variables (Γₜ : Ctx); the
-- TYPE-variable side (renameᵀ / ⊢renameᵀ) lives in strong.BReduction and is
-- used here only as a black box, at the Λ case, to push a substitution under a
-- type binder.
--
-- Two things make these proofs shorter than the usual System F versions:
--
--   * A boundary wrapper is TERM-CLOSED — the (env) rule types its body at the
--     empty term context [] — so both renameᵀᵐ and substᵀᵐ are the IDENTITY on
--     wrappers, and the (env) case is literally `env bwf sc ⊢M` (the rule's
--     conclusion carries an arbitrary term context).
--
--   * Under a Λ the term context is shifted, ⤊ Γₜ = map ⇑ᵗ Γₜ, so a lookup in
--     the body must be pulled back through `map`.  That is `∋-map⁻`, the
--     inverse of `∋-map` from strong.BReduction.
--
-- Contents: ⊢renameᵀᵐ, ⊢substᵀᵐ, the single-substitution corollary ⊢[]ᵐ, and
-- preserve-Beta, which is the Beta preservation case ready to be wired into
-- strong.BReduction's `preservation`.

open import Data.Nat using (ℕ; zero; suc; s≤s)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
  using (TCtx; abst; rvld; _⊢_; wf-var; wf-ℕ; _∋tv_; here-rvld; skip-abst;
         _∋_:=_; Ctx; _∋_⦂_; here; there; ⤊)
open import strong.Unfold using (≡→≈)
open import strong.Boundary
open import strong.BReduction
  using (extⁿ; renameᵀᵐ; ⇑ᵀ; extsᵀᵐ; substᵀᵐ; _[_]ᵐ; Mono; ⊢renameᵀ; ∋-map;
         hk-suc; hx-suc)

------------------------------------------------------------------------
-- Pulling a lookup back through `map`
------------------------------------------------------------------------

-- The inverse of ∋-map (strong.BReduction): every entry of a mapped context is
-- the image of an entry of the original.  Needed at the ⊢Λ cases below, where
-- the body's context is ⤊ Γₜ = map ⇑ᵗ Γₜ.
∋-map⁻ : ∀ {f : Ty → Ty} {Γₜ : Ctx} {x A′}
  → map f Γₜ ∋ x ⦂ A′
  → ∃ λ A → (A′ ≡ f A) × (Γₜ ∋ x ⦂ A)
∋-map⁻ {Γₜ = []}      ()
∋-map⁻ {Γₜ = A₀ ∷ Γ₀} here      = A₀ , refl , here
∋-map⁻ {Γₜ = A₀ ∷ Γ₀} (there p) with ∋-map⁻ p
∋-map⁻ {Γₜ = A₀ ∷ Γ₀} (there p) | A , eq , q = A , eq , there q

------------------------------------------------------------------------
-- Term-variable renaming preserves typing
------------------------------------------------------------------------

-- extⁿ extends a term renaming under a ƛ.
extⁿ-∋ : ∀ {ρ Γₜ Γₜ′ A}
  → (∀ {x B} → Γₜ ∋ x ⦂ B → Γₜ′ ∋ ρ x ⦂ B)
  → (∀ {x B} → (A ∷ Γₜ) ∋ x ⦂ B → (A ∷ Γₜ′) ∋ extⁿ ρ x ⦂ B)
extⁿ-∋ h here      = here
extⁿ-∋ h (there p) = there (h p)

-- A term renaming survives the type-context shift ⤊ imposed by a Λ: the term
-- variables are untouched, only their types are shifted, so we pull back with
-- ∋-map⁻ and push forward with ∋-map.
⤊-∋ : ∀ {ρ : ℕ → ℕ} {Γₜ Γₜ′ : Ctx}
  → (∀ {x B} → Γₜ ∋ x ⦂ B → Γₜ′ ∋ ρ x ⦂ B)
  → (∀ {x B} → ⤊ Γₜ ∋ x ⦂ B → ⤊ Γₜ′ ∋ ρ x ⦂ B)
⤊-∋ h {x} {B} p with ∋-map⁻ p
⤊-∋ h {x} {B} p | A , refl , q = ∋-map {ρ = suc} (h q)

-- renameᵀᵐ is the identity on wrappers (a wrapped body is term-closed),
-- and the (env) rule's conclusion holds at an arbitrary term context, so
-- that case just rebuilds the derivation.
⊢renameᵀᵐ : ∀ {ρ Δ Γₜ Γₜ′ M A}
  → (∀ {x B} → Γₜ ∋ x ⦂ B → Γₜ′ ∋ ρ x ⦂ B)
  → Δ ∣ Γₜ ⊢ M ⦂ A
  → Δ ∣ Γₜ′ ⊢ renameᵀᵐ ρ M ⦂ A
⊢renameᵀᵐ h (⊢` p)          = ⊢` (h p)
⊢renameᵀᵐ h ⊢$              = ⊢$
⊢renameᵀᵐ h (⊢ƛ wfA ⊢N)     = ⊢ƛ wfA (⊢renameᵀᵐ (extⁿ-∋ h) ⊢N)
⊢renameᵀᵐ h (⊢· ⊢L ⊢M)      = ⊢· (⊢renameᵀᵐ h ⊢L) (⊢renameᵀᵐ h ⊢M)
⊢renameᵀᵐ h (⊢Λ ⊢N)         = ⊢Λ (⊢renameᵀᵐ (⤊-∋ h) ⊢N)
⊢renameᵀᵐ h (⊢·[] ⊢L wfA)   = ⊢·[] (⊢renameᵀᵐ h ⊢L) wfA
⊢renameᵀᵐ h (env bwf sc ⊢M) = env bwf sc ⊢M

------------------------------------------------------------------------
-- Term-variable substitution preserves typing
------------------------------------------------------------------------

-- The weakening renaming `suc` is strictly monotone, which is what ⊢renameᵀ
-- demands of a TYPE renaming (boundary renaming depends on index order).
Mono-suc : Mono suc
Mono-suc a<b = s≤s a<b

-- Disambiguates the _∋tv_ constructor from the like-named _∋_:=_ one when
-- it is handed to ⊢renameᵀ as its lookup premise.
∋tv-suc : ∀ {Δ : TCtx} {X} → Δ ∋tv X → (abst ∷ Δ) ∋tv suc X
∋tv-suc p = skip-abst p

-- extsᵀᵐ extends a term substitution under a ƛ: the new variable maps to
-- itself and the old images are weakened by ⊢renameᵀᵐ.
extsᵀᵐ-⊢ : ∀ {σ Δ Γₜ Γₜ′ A}
  → (∀ {x B} → Γₜ ∋ x ⦂ B → Δ ∣ Γₜ′ ⊢ σ x ⦂ B)
  → (∀ {x B} → (A ∷ Γₜ) ∋ x ⦂ B → Δ ∣ (A ∷ Γₜ′) ⊢ extsᵀᵐ σ x ⦂ B)
extsᵀᵐ-⊢ h here      = ⊢` here
extsᵀᵐ-⊢ h (there p) = ⊢renameᵀᵐ there (h p)

-- Pushing a term substitution under a Λ:  substᵀᵐ σ (Λ N) is
-- Λ (substᵀᵐ (λ x → ⇑ᵀ (σ x)) N), so every image must be shifted by the
-- TYPE-variable weakening ⇑ᵀ = renameᵀ suc.
-- That is ⊢renameᵀ at ρ = suc (used as a black box), whose Mono premise is
-- Mono-suc, whose lookup premise is skip-abst, and whose KNOWLEDGE-transport
-- premise (new: the reversal-form conceal rule reads the exterior's ∋:=) is
-- hk-suc — restrictRen X suc is pointwise the identity, so the rep is
-- carried across unchanged — and whose EXTERIOR-READ transport (in its
-- SkelX form, since the repaired (bwf-↓x) compares the two reps by
-- skeleton) is hx-suc: weakening does not touch a stored entry, so the
-- x-rep is carried across verbatim (only the lookup index shifts) and its
-- skeleton witness is skel-refl.
⇑ᵀ-⊢ : ∀ {σ : ℕ → Term} {Δ Γₜ Γₜ′}
  → (∀ {x B} → Γₜ ∋ x ⦂ B → Δ ∣ Γₜ′ ⊢ σ x ⦂ B)
  → (∀ {x B} → ⤊ Γₜ ∋ x ⦂ B → (abst ∷ Δ) ∣ ⤊ Γₜ′ ⊢ ⇑ᵀ (σ x) ⦂ B)
⇑ᵀ-⊢ h {x} {B} p with ∋-map⁻ p
⇑ᵀ-⊢ h {x} {B} p | A , refl , q =
  ⊢renameᵀ ∋tv-suc Mono-suc hk-suc hx-suc (h q)

-- As for renaming, substᵀᵐ is the identity on wrappers, so (env) is rebuilt.
⊢substᵀᵐ : ∀ {σ Δ Γₜ Γₜ′ N B}
  → (∀ {x A} → Γₜ ∋ x ⦂ A → Δ ∣ Γₜ′ ⊢ σ x ⦂ A)
  → Δ ∣ Γₜ ⊢ N ⦂ B
  → Δ ∣ Γₜ′ ⊢ substᵀᵐ σ N ⦂ B
⊢substᵀᵐ h (⊢` p)          = h p
⊢substᵀᵐ h ⊢$              = ⊢$
⊢substᵀᵐ h (⊢ƛ wfA ⊢N)     = ⊢ƛ wfA (⊢substᵀᵐ (extsᵀᵐ-⊢ h) ⊢N)
⊢substᵀᵐ h (⊢· ⊢L ⊢M)      = ⊢· (⊢substᵀᵐ h ⊢L) (⊢substᵀᵐ h ⊢M)
⊢substᵀᵐ h (⊢Λ ⊢N)         = ⊢Λ (⊢substᵀᵐ (⇑ᵀ-⊢ h) ⊢N)
⊢substᵀᵐ h (⊢·[] ⊢L wfA)   = ⊢·[] (⊢substᵀᵐ h ⊢L) wfA
⊢substᵀᵐ h (env bwf sc ⊢M) = env bwf sc ⊢M

------------------------------------------------------------------------
-- Single substitution and the Beta preservation step
------------------------------------------------------------------------

-- N [ W ]ᵐ substitutes W for the outermost term variable.  Its environment
-- sends zero to W and suc x to ` x, so the lookup hypothesis is exactly the
-- two-case function below.
⊢[]ᵐ : ∀ {Δ Γₜ N W A B}
  → Δ ∣ (A ∷ Γₜ) ⊢ N ⦂ B
  → Δ ∣ Γₜ ⊢ W ⦂ A
  → Δ ∣ Γₜ ⊢ N [ W ]ᵐ ⦂ B
⊢[]ᵐ ⊢N ⊢W = ⊢substᵀᵐ (λ { here → ⊢W ; (there p) → ⊢` p }) ⊢N

-- Beta preservation.  (⊢·) is the only rule that can conclude an application —
-- (env) concludes a wrapper — so the inversion is a single clause.
preserve-Beta : ∀ {Δ Γₜ N W A B}
  → Δ ∣ Γₜ ⊢ (ƛ A ∙ N) · W ⦂ B
  → Δ ∣ Γₜ ⊢ N [ W ]ᵐ ⦂ B
preserve-Beta (⊢· (⊢ƛ _ ⊢N) ⊢W) = ⊢[]ᵐ ⊢N ⊢W

------------------------------------------------------------------------
-- Sanity checks
------------------------------------------------------------------------

private
  -- (λx:ℕ. x) · 5  ↦  5 : the substitution really produces $ 5.
  _ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
  _ = ⊢[]ᵐ {A = `ℕ} (⊢` here) ⊢$

  _ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
  _ = preserve-Beta (⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$)

  -- The wrapper-identity case.  Δ₁ reveals X:=ℕ; W₁ is Boundary's Example 1,
  -- the value 7 wrapped in the conceal ↓X:=ℕ, so W₁ : X externally.
  Δ₁ : TCtx
  Δ₁ = rvld `ℕ ∷ []

  W₁ : Term
  W₁ = ($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫

  ⊢W₁ : Δ₁ ∣ [] ⊢ W₁ ⦂ ` 0
  ⊢W₁ = env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$

  -- Substituting W₁ under a ƛ: the body's occurrence sits at index 1, so
  -- extsᵀᵐ weakens W₁ by renameᵀᵐ suc — which is the IDENTITY on wrappers.
  -- Hence the contractum is ƛ ℕ ∙ W₁, with W₁ unchanged.
  _ : Δ₁ ∣ [] ⊢ ƛ `ℕ ∙ W₁ ⦂ (`ℕ ⇒ ` 0)
  _ = ⊢[]ᵐ (⊢ƛ wf-ℕ (⊢` (there here))) ⊢W₁

  -- and the same contractum as a Beta step from (λy:X. λx:ℕ. y) · W₁
  _ : Δ₁ ∣ [] ⊢ ƛ `ℕ ∙ W₁ ⦂ (`ℕ ⇒ ` 0)
  _ = preserve-Beta
        (⊢· (⊢ƛ (wf-var here-rvld) (⊢ƛ wf-ℕ (⊢` (there here)))) ⊢W₁)

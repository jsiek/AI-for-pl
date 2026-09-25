module strong-rep-nu.notes.DualTightness where

-- File Charter:
--   * THE UNBIND IS LOAD-BEARING: strong-rep-nu's port of
--     strong/proof/DualTightness.agda (Jeremy's test, 2026-09-06).
--   * `↥U` is a BINDER for type variables and `↓U` its inverse.  When
--     `Wrap` sends an argument into a boundary that binds `U`, the
--     argument crosses under `dual [↥U] = [↓U]`, so it is read in the
--     scope it came from.  Drop that `↓U` and an argument that names `U`
--     — ill scoped where it was written — becomes well typed inside:
--     SCOPE GAINED THROUGH A BOUNDARY, the color violation Decision 3 of
--     paper/draft.md is about.
--   * §1 the exterior (a cell with NO live name) and the boundary `↥U`;
--     §2 the argument `W`, which names `U`; §3 the redex is ill typed;
--     §4 the real `Wrap` step (computed by `Eval.step`) and the
--     contractum REFUSED; §5 the same contractum WITHOUT the unbind is
--     WELL TYPED; §6 the control: an argument that does not name `U`
--     types before and after the real step.
--   * The old file's defect was a `dual` that dropped the inverse of an
--     unmasking entry; here the inverse of `↥U` is `↓U`, and §5 is what
--     the calculus would do with the old `dual`.

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.TypeCheck using (tc; int!)
open import strong-rep-nu.Eval using (Steps)

------------------------------------------------------------------------
-- §1  The exterior and the boundary
------------------------------------------------------------------------

-- One representation cell α := ℕ in the store, and NO ordinary name for
-- it: we sit where the type variable `U` is out of scope.
Δᵤ : Ctxᵗ
Δᵤ = (bindR `ℕ ∷ []) ∣ []

-- `↥U`: the boundary binds ordinary name 0 (`U`) to α for its interior.
Θᵤ : Boundary
Θᵤ = bind 0 0 ∷ []

-- Its interior has `U` in scope …
int-Θᵤ : Δᵤ ⊢ⁱ Θᵤ ⇒ ((bindR `ℕ ∷ []) ∣ (0 ∷ []))
int-Θᵤ = proj₂ (int! Δᵤ Θᵤ)

-- … and its dual is `↓U`, which ends that scope again.
dual-Θᵤ : dual Θᵤ ≡ unbind 0 0 ∷ []
dual-Θᵤ = refl

------------------------------------------------------------------------
-- §2  The function inside, the conversion, and the argument
------------------------------------------------------------------------

-- the identity on ℕ ⇒ ℕ, and the identity conversion at that type
V : Term
V = ƛ (`ℕ ⇒ `ℕ) ∙ ` 0

idℕ⇒ℕ : Conv
idℕ⇒ℕ = ⌞ ⌞ id `ℕ ⌟ ↦ ⌞ id `ℕ ⌟ ⌟

-- W = λz:ℕ. (λy:(U⇒U). z) · (λu:U. u)    — it NAMES `U`.
W : Term
W = ƛ `ℕ ∙ ((ƛ (` 0 ⇒ ` 0) ∙ ` 1) · (ƛ (` 0) ∙ ` 0))

-- W is ill scoped wherever no ordinary name is live.
¬W : ∀ {Δ A} → names Δ ≡ [] → ¬ (Δ ∣ [] ⊢ W ⦂ A)
¬W eq (⊢ƛ _ (⊢· (⊢ƛ (wf-⇒ (wf-var (_ , d)) _) _) _)) = no-name eq d
  where
  no-name : ∀ {η X α} → η ≡ [] → η ∋ˡ X := α → ⊥
  no-name refl ()

------------------------------------------------------------------------
-- §3  The redex is ILL TYPED
------------------------------------------------------------------------

Redex : Term
Redex = (V ⟪ Θᵤ , ⌞ idℕ⇒ℕ ↦ idℕ⇒ℕ ⌟ ⟫) · W

¬Redex : ∀ {A} → ¬ (Δᵤ ∣ [] ⊢ Redex ⦂ A)
¬Redex (⊢· _ ⊢W) = ¬W refl ⊢W

------------------------------------------------------------------------
-- §4  The real `Wrap` step, and its contractum REFUSED
------------------------------------------------------------------------

-- The argument crosses under `↓U`, the inverse of the boundary's `↥U`.
Contractum : Term
Contractum = (V · (W ⟪ unbind 0 0 ∷ [] , idℕ⇒ℕ ⟫)) ⟪ Θᵤ , idℕ⇒ℕ ⟫

-- This is what the reduction relation does (computed, not asserted).
wrap-steps : Steps Δᵤ Redex Contractum
wrap-steps = refl

-- Inside the `↥U` boundary and then the `↓U` boundary, the name map is
-- empty again, so `W` is refused exactly as it was outside.
¬Contractum : ∀ {A} → ¬ (Δᵤ ∣ [] ⊢ Contractum ⦂ A)
¬Contractum (boundary mw (⊢· _ (boundary mw′ ⊢W _ _ _ _)) _ _ _ _)
  with interior-functional (bw-interior mw) int-Θᵤ
... | refl with bw-interior mw′
... | interior cs = ¬W (dual-names cs) ⊢W
  where
  dual-names : ∀ {Δ′} → (bindR `ℕ ∷ []) ∣ (0 ∷ []) ⊢χ unbind 0 0 ∷ [] ⇒ Δ′
    → Δ′ ≡ []
  dual-names cs′
    with interior-functional (interior cs′)
           (proj₂ (int! ((bindR `ℕ ∷ []) ∣ (0 ∷ [])) (unbind 0 0 ∷ [])))
  ... | eq = cong names eq

------------------------------------------------------------------------
-- §5  WITHOUT the unbind, the same contractum is WELL TYPED
------------------------------------------------------------------------

-- The argument crosses under the EMPTY scope — the old `dual` that dropped
-- the inverse of an entry.  It is read in the boundary's interior, where
-- `U` is live: an argument ill scoped at its birth now types.
Leaky : Term
Leaky = (V · (W ⟪ [] , idℕ⇒ℕ ⟫)) ⟪ Θᵤ , idℕ⇒ℕ ⟫

⊢Leaky : Δᵤ ∣ [] ⊢ Leaky ⦂ (`ℕ ⇒ `ℕ)
⊢Leaky = tc

------------------------------------------------------------------------
-- §6  The control: an argument that does not name `U`
------------------------------------------------------------------------

-- The real rule is not vacuous: with an argument written in scope, the
-- redex and its `Wrap` contractum both type.
W₀ : Term
W₀ = ƛ `ℕ ∙ ` 0

Redex₀ Contractum₀ : Term
Redex₀ = (V ⟪ Θᵤ , ⌞ idℕ⇒ℕ ↦ idℕ⇒ℕ ⌟ ⟫) · W₀
Contractum₀ = (V · (W₀ ⟪ unbind 0 0 ∷ [] , idℕ⇒ℕ ⟫)) ⟪ Θᵤ , idℕ⇒ℕ ⟫

⊢Redex₀ : Δᵤ ∣ [] ⊢ Redex₀ ⦂ (`ℕ ⇒ `ℕ)
⊢Redex₀ = tc

wrap-steps₀ : Steps Δᵤ Redex₀ Contractum₀
wrap-steps₀ = refl

⊢Contractum₀ : Δᵤ ∣ [] ⊢ Contractum₀ ⦂ (`ℕ ⇒ `ℕ)
⊢Contractum₀ = tc

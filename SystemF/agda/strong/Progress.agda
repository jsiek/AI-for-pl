module strong.Progress where

-- PROGRESS for the conversion-boundary calculus.
--
--     a closed, well-typed term is a VALUE or it STEPS.
--
-- The three ordinary cases (application, type application, Λ) are the
-- usual ones, decided by strong.proof.Canonical.  The boundary case is
-- the whole content of the theorem, and it is a two-step argument:
--
--   1. run the induction hypothesis on the INTERIOR, at `intC Θ Δ`
--      (`env`'s second premise types it there).  An interior step lifts by
--      ξ-⟪⟫; an interior VALUE moves to step 2.
--
--   2. classify the FACE by inverting `env`'s conversion premise —
--      i.e. `act-or-inert` (strong.Terms) with its two branches read off
--      the derivation, so that the ACTIVE branches keep their premises:
--
--        INERT  (id (` X) / seal / ↦ / `∀)   the boundary is a VALUE, V-⟪⟫.
--        ACTIVE:
--          conv-id b   — base exterior, so the interior value is a
--                        NUMERAL (canon-base): Drop$ fires, with `b` the
--                        rule's own Base premise.
--          conv-unseal d — the interior value has the VARIABLE type ` Y,
--                        so it is a seal-faced or id-variable-faced
--                        wrapper (canon-var) and CancelR / IdPush fires.
--                        Both rules ask for `fceC Θ Δ ∋ Y := A`, which IS
--                        `conv-unseal`'s own premise `d` — the lookup is
--                        FREE, never re-derived.
--
-- The historically hard case — a value at an abstract type — costs one
-- two-way split here (canon-var), because the only faces with a variable
-- exterior are precisely the two the id-layer rules consume.
--
-- ZERO module parameters: nothing is assumed, nothing is postulated.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Canonical

------------------------------------------------------------------------
-- THE BOUNDARY CASE
------------------------------------------------------------------------

-- Split off so that the face classification is a flat, named case
-- analysis.  The interior has already been run: `v` is the interior
-- value, `⊢M` its typing at `intC Θ Δ`, `⊢c` the face.
--
-- The split is `act-or-inert` — the classification is total over TYPED
-- conversions — and the ACTIVE branches recover their premises from `⊢c`
-- by the face inversions of strong.Conversion, so no lookup and no Base
-- witness is ever re-derived:
--
--   A-idb b   : `b` IS Drop$'s Base premise;
--               conv-id-base-src pins the interior face to the base type.
--   A-unseal  : conv-unseal-src pins the interior face to ` Y, and
--               unseal-face-is-the-owners-rep IS CancelR's / IdPush's
--               `fceC Θ Δ ∋ Y := A` premise.
progress-env : ∀ {Δ Θ c M Bᵢ Bₑ p}
  → Value M
  → intC Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
  → fceC Θ Δ ⊢ c ∶ Bᵢ ⇝ liftN (nbind Θ) Bₑ ∙ p
    ------------------------------------------------------------
  → Value (M ⟪ Θ , c ⟫)
  ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M ⟪ Θ , c ⟫ -→ M′))
progress-env v ⊢M ⊢c with act-or-inert ⊢c

-- INERT face over an interior value: the boundary IS a value.
progress-env v ⊢M ⊢c | inj₂ ic = inj₁ (V-⟪⟫ v ic)

-- ACTIVE `id A` at a base type: the interior value is a numeral.
progress-env v ⊢M ⊢c | inj₁ (A-idb b)
  with canon-base v b (⊢ty≡ (conv-id-base-src b ⊢c) ⊢M)
progress-env v ⊢M ⊢c | inj₁ (A-idb b) | n , refl = inj₂ ($ n , Drop$ b)

-- ACTIVE `unseal Y`: the interior value sits at the VARIABLE type ` Y,
-- so it is a seal-faced or an id-variable-faced wrapper — and those two
-- are exactly CancelR's and IdPush's left-hand sides.
progress-env v ⊢M ⊢c | inj₁ A-unseal
  with canon-var v (⊢ty≡ (conv-unseal-src ⊢c) ⊢M)
progress-env v ⊢M ⊢c | inj₁ A-unseal | W , Θ₁ , Z , vW , inj₁ refl =
  inj₂ (_ , CancelR vW (unseal-face-is-the-owners-rep ⊢c))
progress-env v ⊢M ⊢c | inj₁ A-unseal | W , Θ₁ , Z , vW , inj₂ refl =
  inj₂ (_ , IdPush vW (unseal-face-is-the-owners-rep ⊢c))

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

progress : ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))

-- ` x — impossible at the empty term context.
progress (⊢` ())

-- the two introduction forms that are values outright
progress ⊢$         = inj₁ V-$
progress (⊢ƛ _ _)   = inj₁ V-ƛ

-- Λ N — reduction goes UNDER Λ, so `Λ N` is a value only when N is one.
progress (⊢Λ ⊢N) with progress ⊢N
progress (⊢Λ ⊢N) | inj₁ vN        = inj₁ (V-Λ vN)
progress (⊢Λ ⊢N) | inj₂ (N′ , st) = inj₂ (Λ N′ , ξ-Λ st)

-- L · M — Beta at a λ, Peel at a ↦-faced wrapper (canon-⇒ exhausts).
progress (⊢· ⊢L ⊢M) with progress ⊢L
progress (⊢· ⊢L ⊢M) | inj₂ (L′ , st) = inj₂ (L′ · _ , ξ-·-l st)
progress (⊢· ⊢L ⊢M) | inj₁ vL with progress ⊢M
progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₂ (M′ , st) =
  inj₂ (_ · M′ , ξ-·-r vL st)
progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM with canon-⇒ vL ⊢L
progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM | inj₁ (N , refl) =
  inj₂ (_ , Beta vM)
progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM
  | inj₂ (W , Θ , s , t , vW , refl) = inj₂ (_ , Peel vW vM)

-- L ·[ B , A ] — TyBeta at a Λ (whose body is a value: V-Λ's premise IS
-- TyBeta's premise), TyPeelR at a ∀-faced wrapper.
progress (⊢·[] ⊢L wA) with progress ⊢L
progress (⊢·[] ⊢L wA) | inj₂ (L′ , st) = inj₂ (L′ ·[ _ , _ ] , ξ-·[] st)
progress (⊢·[] ⊢L wA) | inj₁ vL with canon-∀ vL ⊢L
progress (⊢·[] ⊢L wA) | inj₁ vL | inj₁ (N , vN , refl) =
  inj₂ (_ , TyBeta vN)
progress (⊢·[] ⊢L wA) | inj₁ vL | inj₂ (W , Θ , s , vW , refl) =
  inj₂ (_ , TyPeelR vW)

-- M ⟪ Θ , c ⟫ — the boundary.  The interior is typed at `intC Θ Δ`; an
-- interior step lifts by ξ-⟪⟫, an interior value goes to `progress-env`.
progress (env bw ⊢M ⊢c wE) with progress ⊢M
progress (env bw ⊢M ⊢c wE) | inj₂ (M′ , st) =
  inj₂ (M′ ⟪ _ , _ ⟫ , ξ-⟪⟫ st)
progress (env bw ⊢M ⊢c wE) | inj₁ vM = progress-env vM ⊢M ⊢c

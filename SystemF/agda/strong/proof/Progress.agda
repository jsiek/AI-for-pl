module strong.proof.Progress where

-- PROGRESS for the conversion-boundary calculus — THE PROOF SCRIPT.
-- The public statement is `strong.Progress.progress`, a one-line wrapper
-- around the `progress` below.
--
--     a closed, well-typed term is a VALUE or it STEPS.
--
-- The three ordinary cases (application, type application, Λ) are the
-- usual ones, decided by strong.proof.Canonical — type application at a
-- ∀-conversion wrapper takes ONE MORE `canon-∀`, on the boundary's
-- interior, because TyPeelR is split on it (`progress-·[]-∀conv`).  The
-- boundary case is
-- the whole content of the theorem, and it is a two-step argument:
--
--   1. run the induction hypothesis on the INTERIOR, at `interior Θ Δ`
--      (`env`'s second premise types it there).  An interior step lifts by
--      ξ-⟪⟫; an interior VALUE moves to step 2.
--
--   2. classify the CONVERSION by inverting `env`'s conversion premise —
--      i.e. `act-or-inert` (strong.Terms) with its two branches read off
--      the derivation, so that the ACTIVE branches keep their premises:
--
--        INERT  (id (` X) / seal / ↦ / `∀)   the boundary is a VALUE, V-⟪⟫.
--        ACTIVE:
--          conv-id b   — base exterior, so the interior value is a
--                        NUMERAL (canon-base): Drop$ fires, with `b` the
--                        rule's own Base premise.
--          conv-unseal d — the interior value has the VARIABLE type ` Y,
--                        so it is a concealing wrapper or one whose
--                        conversion is `id (` Z)` (canon-var), and
--                        CancelR / IdPush fires.
--                        Both rules ask for `convCtx Θ Δ ∋ Y := A`, which IS
--                        `conv-unseal`'s own premise `d` — the lookup is
--                        FREE, never re-derived.
--
-- The historically hard case — a value at an abstract type — costs one
-- two-way split here (canon-var), because the only conversions with a
-- variable target type are precisely the two the id-layer rules consume.
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
open import strong.CtxMorph
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Canonical

------------------------------------------------------------------------
-- THE BOUNDARY CASE
------------------------------------------------------------------------

-- Split off so that the conversion classification is a flat, named case
-- analysis.  The interior has already been run: `v` is the interior
-- value, `⊢M` its typing at `interior Θ Δ`, `⊢c` the conversion.
--
-- The split is `act-or-inert` — the classification is total over TYPED
-- conversions — and the ACTIVE branches recover their premises from `⊢c`
-- by the conversion inversions of strong.Conversion, so no lookup and no
-- Base witness is ever re-derived:
--
--   A-idb b   : `b` IS Drop$'s Base premise;
--               conv-id-base-src pins the source type to the base type.
--   A-unseal  : conv-unseal-src pins the source type to ` Y, and
--               unseal-target-is-rep IS CancelR's / IdPush's
--               `convCtx Θ Δ ∋ Y := A` premise.
progress-env : ∀ {Δ Θ c M Bᵢ Bₑ}
  → Value M
  → interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
  → convCtx Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ
    ------------------------------------------------------------
  → Value (M ⟪ Θ , c ⟫)
  ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M ⟪ Θ , c ⟫ -→ M′))
progress-env v ⊢M ⊢c with act-or-inert ⊢c

-- INERT conversion over an interior value: the boundary IS a value.
progress-env v ⊢M ⊢c | inj₂ ic = inj₁ (V-⟪⟫ v ic)

-- ACTIVE `id A` at a base type: the interior value is a numeral.
progress-env v ⊢M ⊢c | inj₁ (A-idb b)
  with canon-base v b (⊢ty≡ (conv-id-base-src b ⊢c) ⊢M)
progress-env v ⊢M ⊢c | inj₁ (A-idb b) | n , refl = inj₂ ($ n , Drop$ b)

-- ACTIVE `unseal Y`: the interior value sits at the VARIABLE type ` Y,
-- so it is a concealing wrapper or one whose conversion is `id (` Z)` —
-- and those two are exactly CancelR's and IdPush's left-hand sides.
progress-env v ⊢M ⊢c | inj₁ A-unseal
  with canon-var v (⊢ty≡ (conv-unseal-src ⊢c) ⊢M)
progress-env v ⊢M ⊢c | inj₁ A-unseal | W , Θ₁ , Z , vW , inj₁ refl =
  inj₂ (_ , CancelR vW (unseal-target-is-rep ⊢c))
progress-env v ⊢M ⊢c | inj₁ A-unseal | W , Θ₁ , Z , vW , inj₂ refl =
  inj₂ (_ , IdPush vW (unseal-target-is-rep ⊢c))

------------------------------------------------------------------------
-- THE TYPEELR SPLIT, DECIDED BY `canon-∀`
------------------------------------------------------------------------

-- TyPeelR is TWO CLAUSES (strong.Reduction, 2026-09-08), split on the
-- crossed boundary's INTERIOR, and `canon-∀` hands the split EXACTLY its
-- two patterns — a `Λ` over a value, or a wrapper with a `∀` conversion.
-- So the pair is TOTAL over canonical `∀`-values: it REPLACES the single
-- rule rather than supplementing it.
--
-- Both clauses' premises come off the redex's own derivation, and ONE
-- inversion supplies both: `conv-all-inv` gives the conversion typing
-- `⊢s` (TyPeelR's pushed-in annotation is the INTERIOR ∀-body, which the
-- rule carries as a premise — strong.Reduction, repair 2a) and pins the
-- interior's type to `` `∀ A₀ ``, which is what lets `canon-∀` run on the
-- interior at all.
progress-·[]-∀conv : ∀ {Δ V Θ s B A C} → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    -----------------------------------------------------------
  → Σ[ M ∈ Term ] (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] -→ M)
progress-·[]-∀conv v (⊢·[] (env mwᵥ ⊢V ⊢c wE) wA) with conv-all-inv ⊢c
progress-·[]-∀conv v (⊢·[] (env mwᵥ ⊢V ⊢c wE) wA)
  | A₀ , B₀ , refl , eqₑ , ⊢s with canon-∀ v ⊢V
progress-·[]-∀conv v (⊢·[] (env mwᵥ ⊢V ⊢c wE) wA)
  | A₀ , B₀ , refl , eqₑ , ⊢s | inj₁ (N , vN , refl) =
  _ , TyPeelR-Λ vN ⊢s
progress-·[]-∀conv v (⊢·[] (env mwᵥ ⊢V ⊢c wE) wA)
  | A₀ , B₀ , refl , eqₑ , ⊢s | inj₂ (W , Θ′ , s′ , vW , refl) =
  _ , TyPeelR-⟪⟫ vW ⊢s

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

-- L · M — Beta at a λ, Peel at a function-conversion wrapper (canon-⇒
-- exhausts).
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
-- TyBeta's premise), and at a ∀-conversion wrapper the TyPeelR SPLIT,
-- which `progress-·[]-∀conv` decides by a second `canon-∀`, on the
-- boundary's interior.
progress (⊢·[] ⊢L wA) with progress ⊢L
progress (⊢·[] ⊢L wA) | inj₂ (L′ , st) = inj₂ (L′ ·[ _ , _ ] , ξ-·[] st)
progress (⊢·[] ⊢L wA) | inj₁ vL with canon-∀ vL ⊢L
progress (⊢·[] ⊢L wA) | inj₁ vL | inj₁ (N , vN , refl) =
  inj₂ (_ , TyBeta vN)
progress (⊢·[] ⊢L wA) | inj₁ vL | inj₂ (W , Θ , s , vW , refl) =
  inj₂ (progress-·[]-∀conv vW (⊢·[] ⊢L wA))

-- M ⟪ Θ , c ⟫ — the boundary.  The interior is typed at `interior Θ Δ`; an
-- interior step lifts by ξ-⟪⟫, an interior value goes to `progress-env`.
progress (env mwᵥ ⊢M ⊢c wE) with progress ⊢M
progress (env mwᵥ ⊢M ⊢c wE) | inj₂ (M′ , st) =
  inj₂ (M′ ⟪ _ , _ ⟫ , ξ-⟪⟫ st)
progress (env mwᵥ ⊢M ⊢c wE) | inj₁ vM = progress-env vM ⊢M ⊢c

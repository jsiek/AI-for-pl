module strong.Eval where

-- Strong System F — THE EVALUATOR.
--
-- *** THE STEP FUNCTION IS PROGRESS. ***  v1's evaluator was a second,
-- TYPE-BLIND transcription of the rule table (`step : TCtx → Term →
-- Maybe Term`, with a `step-sound` theorem tying it back to the
-- relation) because progress was FALSE for v1 as it stood, so there was
-- nothing to iterate.  In v2 progress is a theorem, so
--
--     step ⊢M  =  progress ⊢M
--       : Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))
--
-- IS the step function: it decides "value or redex" and, in the redex
-- case, hands back the contractum TOGETHER WITH its derivation.  There
-- is no second rule table to get wrong, no `Maybe`, no decision
-- procedure for values or for inertness, and no soundness theorem to
-- prove — soundness is the type.
--
-- `eval k ⊢M` iterates it with fuel `k`, retyping each contractum by
-- PRESERVATION so that the next step has a derivation to run on, and
-- returns a TRACE: a cons list of the steps taken, ending in the final
-- STATUS (a value, or out of fuel).  Because a `Trace` stores the
-- `_⊢_-→_` derivations themselves:
--
--   trace-sound   — the states really are a run, `Δ ⊢ M -→* traceEnd tr`
--                   (it is `done`/`_then_` over the stored steps);
--   traceFinal    — the status is a status OF THE LAST STATE;
--   trace-unique  — two traces of the same length from the same term
--                   have the same states (`det`).
--
-- So `evalTerms k ⊢M` is a machine-generated version of the
-- hand-composed `-→*` chains in strong.Examples, and each pinned run
-- there is checked against it by `refl` (Examples §§6, 11, 12, 12b, 13,
-- 13b, 14).
--
-- `showTrace n tr` renders the run with strong.Show's `showTmIn`, one
-- state per line, each arrow labelled by `ruleName` — the name of the
-- REDEX rule that fired, found by descending through the congruences of
-- the stored derivation.  Driven non-interactively by
-- scripts/render_term.sh:
--
--   scripts/render_term.sh 'showTrace 0 (eval 6 ⊢P₀)' \
--     'open import strong.Examples' 'open import strong.Eval'
--
-- (the script reads the string out of an Agda type error, so the
-- newlines arrive escaped; pipe through  sed 's/\\n/\n/g' ).

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction
  using (_⊢_-→_; _⊢_-→*_; done; _then_; det;
         TyBeta; Beta; Peel; TyPeelR-Λ; TyPeelR-⟪⟫; CancelR; Drop$; IdPush;
         ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫)
open import strong.Progress using (progress)
open import strong.Preservation using (preservation; preservation*)
open import strong.Show using (showTmIn)

------------------------------------------------------------------------
-- 1.  THE STEP FUNCTION — it is progress
------------------------------------------------------------------------

step : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
    ---------------------------------------------
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))
step = progress

------------------------------------------------------------------------
-- 2.  TRACES
------------------------------------------------------------------------

-- why the run stopped, said of the state it stopped at
data Final (M : Term) : Set where
  value       : Value M → Final M
  out-of-fuel : Final M

-- a run from M: the steps taken, each with its derivation, then the
-- status of the state they arrive at.  A trace always has a first state
-- (the index M), so the state list below is never empty.
infixr 5 _◅_
data Trace (Δ : Ctxᵗ) : Term → Set where
  stop : ∀ {M} → Final M → Trace Δ M
  _◅_  : ∀ {M M′} → Δ ⊢ M -→ M′ → Trace Δ M′ → Trace Δ M

------------------------------------------------------------------------
-- 3.  THE EVALUATOR
------------------------------------------------------------------------

-- Each contractum is retyped by PRESERVATION, which is what lets the
-- next `step` run at all: the iteration is (progress ⨟ preservation)ᵏ.
eval : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → ℕ → Δ ∣ [] ⊢ M ⦂ A → Trace Δ M
eval zero ⊢M with step ⊢M
eval zero ⊢M | inj₁ v = stop (value v)
eval zero ⊢M | inj₂ _ = stop out-of-fuel
eval (suc k) ⊢M with step ⊢M
eval (suc k) ⊢M | inj₁ v        = stop (value v)
eval (suc k) ⊢M | inj₂ (M′ , r) = r ◅ eval k (preservation ⊢M r)

------------------------------------------------------------------------
-- 4.  READING A TRACE
------------------------------------------------------------------------

-- the states, first one included — v1's `trace`
traceTerms : ∀ {Δ M} → Trace Δ M → List Term
traceTerms {M = M} (stop f) = M ∷ []
traceTerms {M = M} (r ◅ tr) = M ∷ traceTerms tr

traceEnd : ∀ {Δ M} → Trace Δ M → Term
traceEnd {M = M} (stop f) = M
traceEnd         (r ◅ tr) = traceEnd tr

traceLen : ∀ {Δ M} → Trace Δ M → ℕ
traceLen (stop f) = zero
traceLen (r ◅ tr) = suc (traceLen tr)

-- the status is a status OF THE LAST STATE
traceFinal : ∀ {Δ M} (tr : Trace Δ M) → Final (traceEnd tr)
traceFinal (stop f) = f
traceFinal (r ◅ tr) = traceFinal tr

evalTerms : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → ℕ → Δ ∣ [] ⊢ M ⦂ A → List Term
evalTerms k ⊢M = traceTerms (eval k ⊢M)

------------------------------------------------------------------------
-- 5.  SOUNDNESS — by construction
------------------------------------------------------------------------

-- Every recorded step IS a `_⊢_-→_` derivation: it is literally stored
-- in the trace, so the run is assembled by `_then_` and nothing is
-- re-checked.
trace-sound : ∀ {Δ M} (tr : Trace Δ M) → Δ ⊢ M -→* traceEnd tr
trace-sound (stop f) = done
trace-sound (r ◅ tr) = r then trace-sound tr

eval-sound : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
    ---------------------------------
  → Δ ⊢ M -→* traceEnd (eval k ⊢M)
eval-sound k ⊢M = trace-sound (eval k ⊢M)

-- and the endpoint still has the type it started with
eval-⦂ : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
    ---------------------------------------
  → Δ ∣ [] ⊢ traceEnd (eval k ⊢M) ⦂ A
eval-⦂ k ⊢M = preservation* ⊢M (eval-sound k ⊢M)

------------------------------------------------------------------------
-- 6.  UNIQUENESS — by determinism
------------------------------------------------------------------------

-- Reduction is deterministic, so a run of a given length from a given
-- term is THE run: any two traces of equal length agree state by state.
-- (Nothing is said about unequal lengths: one trace may stop for fuel
-- where the other keeps going.)
trace-unique : ∀ {Δ M} (tr₁ tr₂ : Trace Δ M)
  → traceLen tr₁ ≡ traceLen tr₂
    -----------------------------------
  → traceTerms tr₁ ≡ traceTerms tr₂
trace-unique (stop f)   (stop g)   eq = refl
trace-unique (stop f)   (r₂ ◅ tr₂) ()
trace-unique (r₁ ◅ tr₁) (stop g)   ()
trace-unique (r₁ ◅ tr₁) (r₂ ◅ tr₂) eq with det r₁ r₂
trace-unique (r₁ ◅ tr₁) (r₂ ◅ tr₂) eq | refl =
  cong (_ ∷_) (trace-unique tr₁ tr₂ (suc-injective eq))

------------------------------------------------------------------------
-- 7.  RENDERING
------------------------------------------------------------------------

-- WHICH RULE FIRED, read off the stored derivation: the congruences are
-- transparent, so what is named is the REDEX rule at the bottom.
ruleName : ∀ {Δ M M′} → Δ ⊢ M -→ M′ → String
ruleName (TyBeta v)     = "TyBeta"
ruleName (Beta w)       = "Beta"
ruleName (Peel v w)     = "Peel"
ruleName (TyPeelR-Λ v ⊢s)  = "TyPeelR-Λ"
ruleName (TyPeelR-⟪⟫ v ⊢s) = "TyPeelR-⟪⟫"
ruleName (CancelR v d)  = "CancelR"
ruleName (Drop$ b)      = "Drop$"
ruleName (IdPush v d)   = "IdPush"
ruleName (ξ-·-l r)      = ruleName r
ruleName (ξ-·-r v r)    = ruleName r
ruleName (ξ-·[] r)      = ruleName r
ruleName (ξ-Λ r)        = ruleName r
ruleName (ξ-⟪⟫ r)       = ruleName r

showFinal : ∀ {M} → Final M → String
showFinal (value v)   = "\n  -- VALUE"
showFinal out-of-fuel = "\n  -- OUT OF FUEL"

-- `n` is the ambient type context's length, as everywhere in
-- strong.Show: it is the naming supply for the free slots, so slot 0 is
-- named X.  One state per line, each arrow labelled by its rule.
showTrace : ∀ {Δ M} → ℕ → Trace Δ M → String
showTrace {M = M} n (stop f) = showTmIn n M ++ showFinal f
showTrace {M = M} n (r ◅ tr) =
  showTmIn n M ++ "\n  --[" ++ ruleName r ++ "]-->\n" ++ showTrace n tr

module Eval where

-- File Charter:
--   * A decidable, untyped one-step function for PolyCν reduction
--     (Reduction.agda): `step Σ M` reports that M is a value, is ℧,
--     takes a step (with the derivation), or is stuck.
--   * A fuel-bounded evaluator `eval` that returns the final
--     configuration together with the multi-step derivation that
--     reaches it.
--   * Values, frames and redexes are decided syntactically, so both
--     functions compute on closed terms: an example's run is checked by
--     `refl`, or by using `trace (eval n Σ M)` at the type
--     `Σ ▷ M —↠ Σ′ ▷ N` with the expected endpoint.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import Terms
open import Reduction

------------------------------------------------------------------------
-- The result of one step
------------------------------------------------------------------------

data Step (Σ : Store) (M : Term) : Set where
  done  : Value M → Step Σ M
  blame : M ≡ ℧ → Step Σ M
  next  : ∀ {Σ′ N} → Σ ▷ M —→ Σ′ ▷ N → Step Σ M
  stuck : Step Σ M

-- the step of a term in a frame, given the step of the hole and what
-- to do when the hole holds a value
step-plug : ∀ {Σ M} F
  → (Value M → Step Σ (plug F M))
  → Step Σ M
  → Step Σ (plug F M)
step-plug F k (done v) = k v
step-plug F k (blame refl) = next (ξ-℧ F)
step-plug F k (next s) = next (ξ F s)
step-plug F k stuck = stuck

------------------------------------------------------------------------
-- Redexes: an elimination form whose principal argument is a value
------------------------------------------------------------------------

step-if : ∀ {Σ L M N} → Value L → Step Σ (if L M N)
step-if V-true = next β-if-true
step-if V-false = next β-if-false
step-if V-ƛ = stuck
step-if V-Λν = stuck
step-if (V-seal v) = stuck
step-if (V-inj v) = stuck
step-if (V-cast⇒ v) = stuck

step-app : ∀ {Σ L M} → Value L → Value M → Step Σ (L · M)
step-app V-true w = stuck
step-app V-false w = stuck
step-app V-ƛ w = next (β-ƛ w)
step-app V-Λν w = stuck
step-app (V-seal v) w = stuck
step-app (V-inj v) w = stuck
step-app (V-cast⇒ v) w = next (β-cast⇒ v w)

step-unseal : ∀ {Σ M} α → Value M → Step Σ (unseal α M)
step-unseal α V-true = stuck
step-unseal α V-false = stuck
step-unseal α V-ƛ = stuck
step-unseal α V-Λν = stuck
step-unseal α (V-seal {α = β} v) with α ≟ₙ β
step-unseal α (V-seal {α = β} v) | yes refl = next (β-unseal v)
step-unseal α (V-seal {α = β} v) | no α≢β = stuck
step-unseal α (V-inj v) = stuck
step-unseal α (V-cast⇒ v) = stuck

step-is : ∀ {Σ M} G → Value M → Step Σ (is G M)
step-is G V-true = stuck
step-is G V-false = stuck
step-is G V-ƛ = stuck
step-is G V-Λν = stuck
step-is G (V-seal v) = stuck
step-is G (V-inj {G = H} v) with G ≟G H
step-is G (V-inj {G = H} v) | yes refl = next (β-is-yes v)
step-is G (V-inj {G = H} v) | no G≢H = next (β-is-no v G≢H)
step-is G (V-cast⇒ v) = stuck

step-inst : ∀ {Σ M B N} → Value M → Step Σ (inst M B N)
step-inst V-true = stuck
step-inst V-false = stuck
step-inst V-ƛ = stuck
step-inst V-Λν = next β-inst
step-inst (V-seal v) = stuck
step-inst (V-inj v) = stuck
step-inst (V-cast⇒ v) = stuck

-- a ∀ν cast on a value
step-cast∀ : ∀ {Σ V} d p → Value V → Step Σ (cast d (∀⊑ p) V)
step-cast∀ d p V-true = stuck
step-cast∀ d p V-false = stuck
step-cast∀ d p V-ƛ = stuck
step-cast∀ d p V-Λν = next β-cast∀
step-cast∀ d p (V-seal v) = stuck
step-cast∀ d p (V-inj v) = stuck
step-cast∀ d p (V-cast⇒ v) = stuck

-- a tag downcast on a value
step-tag-down : ∀ {Σ V} G p → Value V → Step Σ (cast down (tag G p) V)
step-tag-down G p V-true = stuck
step-tag-down G p V-false = stuck
step-tag-down G p V-ƛ = stuck
step-tag-down G p V-Λν = stuck
step-tag-down G p (V-seal v) = stuck
step-tag-down G p (V-inj {G = H} v) with G ≟G H
step-tag-down G p (V-inj {G = H} v) | yes refl = next (β-tag-down v)
step-tag-down G p (V-inj {G = H} v) | no G≢H =
  next (β-tag-down-℧ v G≢H)
step-tag-down G p (V-cast⇒ v) = stuck

step-cast : ∀ {Σ V} d p → Value V → Step Σ (cast d p V)
step-cast d ★⊑ v = next (β-id at★ v)
step-cast up (tag G p) v = next (β-tag-up v)
step-cast down (tag G p) v = step-tag-down G p v
step-cast d (‵⊑ α) v = next (β-id at‵ v)
step-cast d 𝔹⊑ v = next (β-id at𝔹 v)
step-cast d (p ⇒⊑ q) v = done (V-cast⇒ v)
step-cast d (∀⊑ p) v = step-cast∀ d p v

------------------------------------------------------------------------
-- One step
------------------------------------------------------------------------

step : (Σ : Store) (M : Term) → Step Σ M
step Σ (` x) = stuck
step Σ ℧ = blame refl
step Σ true = done V-true
step Σ false = done V-false
step Σ (if L M N) = step-plug (if□ M N) step-if (step Σ L)
step Σ (ƛ A M) = done V-ƛ
step Σ (L · M) = step-plug (□· M) k (step Σ L)
  where
  k : Value L → Step Σ (L · M)
  k v = step-plug (app□ L v) (step-app v) (step Σ M)
step Σ (letv M N) = step-plug (letv□ N) (λ v → next (β-letv v)) (step Σ M)
step Σ (seal α M) = step-plug (seal□ α) (λ v → done (V-seal v)) (step Σ M)
step Σ (unseal α M) = step-plug (unseal□ α) (step-unseal α) (step Σ M)
step Σ (is G M) = step-plug (is□ G) (step-is G) (step Σ M)
step Σ (inj G M) = step-plug (inj□ G) (λ v → done (V-inj v)) (step Σ M)
step Σ (cast d p M) = step-plug (cast□ d p) (step-cast d p) (step Σ M)
step Σ (Λν cs M) = done V-Λν
step Σ (inst M B N) = step-plug (inst□ B N) step-inst (step Σ M)

------------------------------------------------------------------------
-- Fuel-bounded evaluation
------------------------------------------------------------------------

-- a run from Σ ▷ M: the configuration reached and how
record Run (Σ : Store) (M : Term) : Set where
  constructor run
  field
    store : Store
    final : Term
    trace : Σ ▷ M —↠ store ▷ final

open Run public

-- prefix a run with one step
step-run : ∀ {Σ Σ′ M N} → Σ ▷ M —→ Σ′ ▷ N → Run Σ′ N → Run Σ M
step-run {M = M} s (run Σ″ N′ N↠) = run Σ″ N′ (M —→⟨ s ⟩ N↠)

-- run until a value, ℧, a stuck term, or the fuel runs out
eval : (gas : ℕ) (Σ : Store) (M : Term) → Run Σ M
eval zero Σ M = run Σ M (M ∎)
eval (suc gas) Σ M with step Σ M
eval (suc gas) Σ M | done v = run Σ M (M ∎)
eval (suc gas) Σ M | blame eq = run Σ M (M ∎)
eval (suc gas) Σ M | next {Σ′} {N} s = step-run s (eval gas Σ′ N)
eval (suc gas) Σ M | stuck = run Σ M (M ∎)

module ExamplesCoverage where

-- File Charter:
--   * A checked coverage catalog for the runs of Examples.agda: every
--     rule of the reduction relation (Reduction.agda) is used by at
--     least one example run.
--   * `rules` lists the rules a multi-step derivation uses, with a
--     congruence step ξξ listed together with the rule it wraps, and
--     β-id split by its Atomic case.  Each entry of the catalog is a
--     proof, by computation, that a named run uses the rule.

open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Unit using (tt)

open import Types
open import Terms using (Term)
open import Reduction
open import Examples

------------------------------------------------------------------------
-- Rule names
------------------------------------------------------------------------

data Rule : Set where
  r-ξξ r-ξξ-℧ r-β-letv r-β-unseal r-β-is-yes r-β-is-no : Rule
  r-β-if-true r-β-if-false r-β-ƛ r-β-cast⇒ r-β-inst : Rule
  r-β-id★ r-β-id𝔹 r-β-id‵ : Rule
  r-β-tag-up r-β-tag-down r-β-tag-down-℧ r-β-cast∀ : Rule

rule-index : Rule → ℕ
rule-index r-ξξ = 0
rule-index r-ξξ-℧ = 1
rule-index r-β-letv = 2
rule-index r-β-unseal = 3
rule-index r-β-is-yes = 4
rule-index r-β-is-no = 5
rule-index r-β-if-true = 6
rule-index r-β-if-false = 7
rule-index r-β-ƛ = 8
rule-index r-β-cast⇒ = 9
rule-index r-β-inst = 10
rule-index r-β-id★ = 11
rule-index r-β-id𝔹 = 12
rule-index r-β-id‵ = 13
rule-index r-β-tag-up = 14
rule-index r-β-tag-down = 15
rule-index r-β-tag-down-℧ = 16
rule-index r-β-cast∀ = 17

atomic-rule : ∀ {p} → Atomic p → Rule
atomic-rule at★ = r-β-id★
atomic-rule at𝔹 = r-β-id𝔹
atomic-rule at‵ = r-β-id‵

------------------------------------------------------------------------
-- The rules a derivation uses
------------------------------------------------------------------------

step-rules : ∀ {Σ Σ′ M N} → Σ ▷ M —→ Σ′ ▷ N → List Rule
step-rules (ξξ F eq₁ eq₂ s) = r-ξξ ∷ step-rules s
step-rules (ξξ-℧ F eq) = r-ξξ-℧ ∷ []
step-rules (β-letv v) = r-β-letv ∷ []
step-rules (β-unseal v) = r-β-unseal ∷ []
step-rules (β-is-yes v) = r-β-is-yes ∷ []
step-rules (β-is-no v G≢H) = r-β-is-no ∷ []
step-rules β-if-true = r-β-if-true ∷ []
step-rules β-if-false = r-β-if-false ∷ []
step-rules (β-ƛ v) = r-β-ƛ ∷ []
step-rules (β-cast⇒ v w) = r-β-cast⇒ ∷ []
step-rules β-inst = r-β-inst ∷ []
step-rules (β-id a v) = atomic-rule a ∷ []
step-rules (β-tag-up v) = r-β-tag-up ∷ []
step-rules (β-tag-down v) = r-β-tag-down ∷ []
step-rules (β-tag-down-℧ v G≢H) = r-β-tag-down-℧ ∷ []
step-rules β-cast∀ = r-β-cast∀ ∷ []

rules : ∀ {Σ Σ′ M N} → Σ ▷ M —↠ Σ′ ▷ N → List Rule
rules (M ∎) = []
rules (L —→⟨ s ⟩ M↠N) = step-rules s ++ rules M↠N

_∈ʳ_ : Rule → List Rule → Bool
r ∈ʳ [] = false
r ∈ʳ (r′ ∷ rs) = (rule-index r ≡ᵇ rule-index r′) ∨ (r ∈ʳ rs)

-- the run M↠N uses the rule r
Uses : ∀ {Σ Σ′ M N} → Rule → Σ ▷ M —↠ Σ′ ▷ N → Set
Uses r M↠N = T (r ∈ʳ rules M↠N)

------------------------------------------------------------------------
-- The catalog
------------------------------------------------------------------------
--
--   rule            example run (Examples.agda)
--   ξξ              id-seal-↠ (and almost every run)
--   ξξ-℧            id-dyn-noseal-↠, c-℧-arg-↠
--   β-letv          id-seal-↠, c-let-if-↠
--   β-unseal        id-seal-↠, c-unseal-↠
--   β-is-yes        is-bool-↠, is-seal-yes-↠, c-proxy-↠
--   β-is-no         is-fun-↠, is-seal-no-↠, c-is-seal-no-↠
--   β-if-true       let-if-↠, c-let-if-↠
--   β-if-false      let-if-dyn-↠
--   β-ƛ             id-seal-↠
--   β-cast⇒         fun-cast-↠, const-seal-↠, c-proxy-↠
--   β-inst          id-seal-↠, nested-↠ (two seals; see its store)
--   β-id (★)        id-dyn-seal-↠
--   β-id (𝔹)        id-seal-↠
--   β-id (‵ α)      c-proxy-↠
--   β-tag-up        id-seal-↠
--   β-tag-down      id-seal-↠
--   β-tag-down-℧    id-dyn-noseal-↠, const-noseal-↠, tag-mismatch-↠
--   β-cast∀         id-via-dyn-↠, const-seal-↠, c-proxy-↠

cover-ξξ : Uses r-ξξ id-seal-↠
cover-ξξ = tt

cover-ξξ-℧ : Uses r-ξξ-℧ id-dyn-noseal-↠
cover-ξξ-℧ = tt

cover-ξξ-℧′ : Uses r-ξξ-℧ c-℧-arg-↠
cover-ξξ-℧′ = tt

cover-β-letv : Uses r-β-letv id-seal-↠
cover-β-letv = tt

cover-β-unseal : Uses r-β-unseal id-seal-↠
cover-β-unseal = tt

cover-β-unseal′ : Uses r-β-unseal c-unseal-↠
cover-β-unseal′ = tt

cover-β-is-yes : Uses r-β-is-yes is-seal-yes-↠
cover-β-is-yes = tt

cover-β-is-yes′ : Uses r-β-is-yes is-bool-↠
cover-β-is-yes′ = tt

cover-β-is-no : Uses r-β-is-no is-seal-no-↠
cover-β-is-no = tt

cover-β-is-no′ : Uses r-β-is-no c-is-seal-no-↠
cover-β-is-no′ = tt

cover-β-if-true : Uses r-β-if-true let-if-↠
cover-β-if-true = tt

cover-β-if-false : Uses r-β-if-false let-if-dyn-↠
cover-β-if-false = tt

cover-β-ƛ : Uses r-β-ƛ id-seal-↠
cover-β-ƛ = tt

cover-β-cast⇒ : Uses r-β-cast⇒ fun-cast-↠
cover-β-cast⇒ = tt

cover-β-cast⇒′ : Uses r-β-cast⇒ const-seal-↠
cover-β-cast⇒′ = tt

cover-β-inst : Uses r-β-inst nested-↠
cover-β-inst = tt

cover-β-id★ : Uses r-β-id★ id-dyn-seal-↠
cover-β-id★ = tt

cover-β-id𝔹 : Uses r-β-id𝔹 id-seal-↠
cover-β-id𝔹 = tt

cover-β-id‵ : Uses r-β-id‵ c-proxy-↠
cover-β-id‵ = tt

cover-β-tag-up : Uses r-β-tag-up id-seal-↠
cover-β-tag-up = tt

cover-β-tag-down : Uses r-β-tag-down id-seal-↠
cover-β-tag-down = tt

cover-β-tag-down-℧ : Uses r-β-tag-down-℧ id-dyn-noseal-↠
cover-β-tag-down-℧ = tt

cover-β-tag-down-℧′ : Uses r-β-tag-down-℧ const-noseal-↠
cover-β-tag-down-℧′ = tt

cover-β-tag-down-℧″ : Uses r-β-tag-down-℧ tag-mismatch-↠
cover-β-tag-down-℧″ = tt

cover-β-cast∀ : Uses r-β-cast∀ id-via-dyn-↠
cover-β-cast∀ = tt

cover-β-cast∀′ : Uses r-β-cast∀ const-seal-↠
cover-β-cast∀′ = tt

cover-β-cast∀″ : Uses r-β-cast∀ c-proxy-↠
cover-β-cast∀″ = tt

cover-β-letv′ : Uses r-β-letv c-let-if-↠
cover-β-letv′ = tt

cover-β-is-yes″ : Uses r-β-is-yes c-proxy-↠
cover-β-is-yes″ = tt

cover-β-if-true′ : Uses r-β-if-true c-let-if-↠
cover-β-if-true′ = tt

cover-β-cast⇒″ : Uses r-β-cast⇒ c-proxy-↠
cover-β-cast⇒″ = tt

cover-β-inst′ : Uses r-β-inst id-seal-↠
cover-β-inst′ = tt

cover-β-is-no″ : Uses r-β-is-no is-fun-↠
cover-β-is-no″ = tt

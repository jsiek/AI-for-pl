module Eval where

-- File Charter:
--   * Untyped, partial execution for extrinsic-inst PolyConvert.
--   * Provides a computable one-step function `step?`, a progress-style
--     classifier `progress?`, and a fuel-bounded evaluator `eval?`.
--   * Intended for running examples and testing store-threaded reduction rules
--     without depending on preservation/progress typing proofs. Multi-step
--     reduction witnesses come from `Reduction`.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _≟_; _+_)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import Imprecision
  using
    ( Imp
    ; ★⊑★
    ; X⊑★
    ; A⊑★
    ; X⊑X
    ; α⊑α
    ; ι⊑ι
    ; A⇒B⊑A′⇒B′
    ; `∀A⊑∀B
    ; `∀A⊑B
    ; src⊑
    ; tgt⊑
    )
open import Conversion
open import Terms
open import Reduction

Step : Store → Term → Set
Step Σ M = Σ[ Σ′ ∈ Store ] Σ[ N ∈ Term ] (Σ ∣ M —→ Σ′ ∣ N)

------------------------------------------------------------------------
-- Step classification for coverage reports
------------------------------------------------------------------------

data RuleTag : Set where
  rule-β : RuleTag
  rule-β-up-∀ : RuleTag
  rule-β-up-↦ : RuleTag
  rule-β-down-↦ : RuleTag
  rule-β-reveal-↦ : RuleTag
  rule-β-conceal-↦ : RuleTag
  rule-id-up : RuleTag
  rule-id-down : RuleTag
  rule-id-reveal : RuleTag
  rule-id-conceal : RuleTag
  rule-seal-unseal : RuleTag
  rule-tag-untag-ok : RuleTag
  rule-tag-untag-bad : RuleTag
  rule-δ-⊕ : RuleTag
  rule-blame-·₁ : RuleTag
  rule-blame-·₂ : RuleTag
  rule-blame-·α : RuleTag
  rule-blame-up : RuleTag
  rule-blame-down : RuleTag
  rule-blame-reveal : RuleTag
  rule-blame-conceal : RuleTag
  rule-blame-⊕₁ : RuleTag
  rule-blame-⊕₂ : RuleTag
  rule-β-Λ : RuleTag
  rule-β-down-∀ : RuleTag
  rule-β-down-ν : RuleTag
  rule-β-up-ν : RuleTag
  rule-β-reveal-∀ : RuleTag
  rule-β-conceal-∀ : RuleTag
  rule-ξ-·₁ : RuleTag
  rule-ξ-·₂ : RuleTag
  rule-ξ-·α : RuleTag
  rule-ξ-⇑ : RuleTag
  rule-ξ-⇓ : RuleTag
  rule-ξ-↑ : RuleTag
  rule-ξ-↓ : RuleTag
  rule-ξ-⊕₁ : RuleTag
  rule-ξ-⊕₂ : RuleTag

data SealAllocTag : Set where
  alloc-β-Λ : SealAllocTag
  alloc-β-down-∀ : SealAllocTag
  alloc-β-down-ν : SealAllocTag
  alloc-β-up-ν : SealAllocTag

classify-raw :
  ∀ {M N : Term} →
  M —→ N →
  RuleTag
classify-raw (β v) = rule-β
classify-raw (β-up-∀ v) = rule-β-up-∀
classify-raw (β-up-↦ vV vW) = rule-β-up-↦
classify-raw (β-down-↦ vV vW) = rule-β-down-↦
classify-raw (β-reveal-↦ vV vW) = rule-β-reveal-↦
classify-raw (β-conceal-↦ vV vW) = rule-β-conceal-↦
classify-raw (id-up-★ v) = rule-id-up
classify-raw (id-up-＇ v) = rule-id-up
classify-raw (id-up-｀ v) = rule-id-up
classify-raw (id-up-‵ v) = rule-id-up
classify-raw (id-down-★ v) = rule-id-down
classify-raw (id-down-＇ v) = rule-id-down
classify-raw (id-down-｀ v) = rule-id-down
classify-raw (id-down-‵ v) = rule-id-down
classify-raw (id-reveal v) = rule-id-reveal
classify-raw (id-conceal v) = rule-id-conceal
classify-raw (seal-unseal v) = rule-seal-unseal
classify-raw (tag-untag-ok v eq) = rule-tag-untag-ok
classify-raw (tag-untag-bad v neq) = rule-tag-untag-bad
classify-raw δ-⊕ = rule-δ-⊕
classify-raw blame-·₁ = rule-blame-·₁
classify-raw (blame-·₂ v) = rule-blame-·₂
classify-raw blame-·α = rule-blame-·α
classify-raw blame-up = rule-blame-up
classify-raw blame-down = rule-blame-down
classify-raw blame-reveal = rule-blame-reveal
classify-raw blame-conceal = rule-blame-conceal
classify-raw blame-⊕₁ = rule-blame-⊕₁
classify-raw (blame-⊕₂ v) = rule-blame-⊕₂

classify-step :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —→ Σ′ ∣ N →
  RuleTag
classify-step (pure-step red) = classify-raw red
classify-step β-Λ = rule-β-Λ
classify-step (β-down-∀ v) = rule-β-down-∀
classify-step (β-down-ν v) = rule-β-down-ν
classify-step (β-up-ν v) = rule-β-up-ν
classify-step (β-reveal-∀ v) = rule-β-reveal-∀
classify-step (β-conceal-∀ v) = rule-β-conceal-∀
classify-step (ξ-·₁ red) = rule-ξ-·₁
classify-step (ξ-·₂ v red) = rule-ξ-·₂
classify-step (ξ-·α red) = rule-ξ-·α
classify-step (ξ-⇑ red) = rule-ξ-⇑
classify-step (ξ-⇓ red) = rule-ξ-⇓
classify-step (ξ-↑ red) = rule-ξ-↑
classify-step (ξ-↓ red) = rule-ξ-↓
classify-step (ξ-⊕₁ red) = rule-ξ-⊕₁
classify-step (ξ-⊕₂ v red) = rule-ξ-⊕₂

StepPath : Set
StepPath = List RuleTag

path-of-step :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —→ Σ′ ∣ N →
  StepPath
path-of-step (pure-step red) = classify-raw red ∷ []
path-of-step β-Λ = rule-β-Λ ∷ []
path-of-step (β-down-∀ v) = rule-β-down-∀ ∷ []
path-of-step (β-down-ν v) = rule-β-down-ν ∷ []
path-of-step (β-up-ν v) = rule-β-up-ν ∷ []
path-of-step (β-reveal-∀ v) = rule-β-reveal-∀ ∷ []
path-of-step (β-conceal-∀ v) = rule-β-conceal-∀ ∷ []
path-of-step (ξ-·₁ red) = rule-ξ-·₁ ∷ path-of-step red
path-of-step (ξ-·₂ v red) = rule-ξ-·₂ ∷ path-of-step red
path-of-step (ξ-·α red) = rule-ξ-·α ∷ path-of-step red
path-of-step (ξ-⇑ red) = rule-ξ-⇑ ∷ path-of-step red
path-of-step (ξ-⇓ red) = rule-ξ-⇓ ∷ path-of-step red
path-of-step (ξ-↑ red) = rule-ξ-↑ ∷ path-of-step red
path-of-step (ξ-↓ red) = rule-ξ-↓ ∷ path-of-step red
path-of-step (ξ-⊕₁ red) = rule-ξ-⊕₁ ∷ path-of-step red
path-of-step (ξ-⊕₂ v red) = rule-ξ-⊕₂ ∷ path-of-step red

concat-step-paths : List StepPath → List RuleTag
concat-step-paths [] = []
concat-step-paths (p ∷ ps) = p ++ concat-step-paths ps

paths-of-multi :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  List StepPath
paths-of-multi (_ ∎) = []
paths-of-multi (_ —→⟨ M→N ⟩ M↠N) =
  path-of-step M→N ∷ paths-of-multi M↠N

rules-of-multi :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  List RuleTag
rules-of-multi M↠N = concat-step-paths (paths-of-multi M↠N)

------------------------------------------------------------------------
-- Decidable values
------------------------------------------------------------------------

tyEq? : (A B : Ty) → Dec (A ≡ B)
tyEq? (＇ X) (＇ Y) with X ≟ Y
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
tyEq? (｀ α) (｀ β₁) with seal-≟ α β₁
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
tyEq? (‵ ι) (‵ ι′) with ι ≟Base ι′
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
tyEq? ★ ★ = yes refl
tyEq? (A ⇒ B) (A′ ⇒ B′) with tyEq? A A′ | tyEq? B B′
... | yes refl | yes refl = yes refl
... | no neq | _ = no (λ { refl → neq refl })
... | _ | no neq = no (λ { refl → neq refl })
tyEq? (`∀ A) (`∀ B) with tyEq? A B
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
tyEq? (＇ X) (｀ α) = no (λ ())
tyEq? (＇ X) (‵ ι) = no (λ ())
tyEq? (＇ X) ★ = no (λ ())
tyEq? (＇ X) (A ⇒ B) = no (λ ())
tyEq? (＇ X) (`∀ A) = no (λ ())
tyEq? (｀ α) (＇ X) = no (λ ())
tyEq? (｀ α) (‵ ι) = no (λ ())
tyEq? (｀ α) ★ = no (λ ())
tyEq? (｀ α) (A ⇒ B) = no (λ ())
tyEq? (｀ α) (`∀ A) = no (λ ())
tyEq? (‵ ι) (＇ X) = no (λ ())
tyEq? (‵ ι) (｀ α) = no (λ ())
tyEq? (‵ ι) ★ = no (λ ())
tyEq? (‵ ι) (A ⇒ B) = no (λ ())
tyEq? (‵ ι) (`∀ A) = no (λ ())
tyEq? ★ (＇ X) = no (λ ())
tyEq? ★ (｀ α) = no (λ ())
tyEq? ★ (‵ ι) = no (λ ())
tyEq? ★ (A ⇒ B) = no (λ ())
tyEq? ★ (`∀ A) = no (λ ())
tyEq? (A ⇒ B) (＇ X) = no (λ ())
tyEq? (A ⇒ B) (｀ α) = no (λ ())
tyEq? (A ⇒ B) (‵ ι) = no (λ ())
tyEq? (A ⇒ B) ★ = no (λ ())
tyEq? (A ⇒ B) (`∀ A′) = no (λ ())
tyEq? (`∀ A) (＇ X) = no (λ ())
tyEq? (`∀ A) (｀ α) = no (λ ())
tyEq? (`∀ A) (‵ ι) = no (λ ())
tyEq? (`∀ A) ★ = no (λ ())
tyEq? (`∀ A) (B ⇒ C) = no (λ ())

upValue? : (p : Imp) → Maybe (UpValue p)
upValue? ★⊑★ = nothing
upValue? (X⊑★ X) = just tagν
upValue? (A⊑★ p) = just tag
upValue? (X⊑X X) = nothing
upValue? (α⊑α α) = nothing
upValue? (ι⊑ι ι) = nothing
upValue? (A⇒B⊑A′⇒B′ p q) = just (_↦_ {p = p} {q = q})
upValue? (`∀A⊑∀B p) = just (`∀ {p = p})
upValue? (`∀A⊑B B p) = nothing

downValue? : (p : Imp) → Maybe (DownValue p)
downValue? ★⊑★ = nothing
downValue? (X⊑★ X) = nothing
downValue? (A⊑★ p) = nothing
downValue? (X⊑X X) = nothing
downValue? (α⊑α α) = nothing
downValue? (ι⊑ι ι) = nothing
downValue? (A⇒B⊑A′⇒B′ p q) = just (_↦_ {p = p} {q = q})
downValue? (`∀A⊑∀B p) = just (`∀ {p = p})
downValue? (`∀A⊑B B p) = just (ν_ {B = B} {p = p})

revealValue? : (c : Conv↑) → Maybe (RevealValue c)
revealValue? (↑-unseal α) = nothing
revealValue? (↑-⇒ p q) = just (_↦_ {p = p} {q = q})
revealValue? (↑-∀ c) = just (`∀ {c = c})
revealValue? (↑-id A) = nothing

concealValue? : (c : Conv↓) → Maybe (ConcealValue c)
concealValue? (↓-seal α) = just (seal {α = α})
concealValue? (↓-⇒ p q) = just (_↦_ {p = p} {q = q})
concealValue? (↓-∀ c) = just (`∀ {c = c})
concealValue? (↓-id A) = nothing

value? : (M : Term) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ N) = just (ƛ A ⇒ N)
value? (L · M) = nothing
value? (Λ M) = just (Λ M)
value? (M ⦂∀ B [ T ]) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op ] M) = nothing
value? (M ⇑ p) with value? M | upValue? p
... | just vM | just vp = just (vM ⇑ vp)
... | _ | _ = nothing
value? (M ⇓ p) with value? M | downValue? p
... | just vM | just vp = just (vM ⇓ vp)
... | _ | _ = nothing
value? (M ↑ c) with value? M | revealValue? c
... | just vM | just vc = just (vM ↑ vc)
... | _ | _ = nothing
value? (M ↓ c) with value? M | concealValue? c
... | just vM | just vc = just (vM ↓ vc)
... | _ | _ = nothing
value? (blame ℓ) = nothing

blame? : (M : Term) → Dec (∃[ ℓ ] M ≡ blame ℓ)
blame? (` x) = no (λ ())
blame? (ƛ A ⇒ M) = no (λ ())
blame? (M · N) = no (λ ())
blame? (Λ M) = no (λ ())
blame? (M ⦂∀ B [ T ]) = no (λ ())
blame? ($ κ) = no (λ ())
blame? (M ⊕[ op ] N) = no (λ ())
blame? (M ⇑ p) = no (λ ())
blame? (M ⇓ p) = no (λ ())
blame? (M ↑ c) = no (λ ())
blame? (M ↓ c) = no (λ ())
blame? (blame ℓ) = yes (ℓ , refl)

natConstView : (M : Term) → Maybe (Σ[ n ∈ ℕ ] (M ≡ $ (κℕ n)))
natConstView ($ (κℕ n)) = just (n , refl)
natConstView _ = nothing

------------------------------------------------------------------------
-- Head redex selection
------------------------------------------------------------------------

app-redex? :
  ∀ {L M : Term} →
  Value L →
  Value M →
  Maybe (Σ[ N ∈ Term ] (L · M —→ N))
app-redex? (ƛ A ⇒ N) vM = just (_ , β vM)
app-redex? ($ κ) vM = nothing
app-redex? (Λ N) vM = nothing
app-redex? (_⇑_ {V = W} vW tagν) vM = nothing
app-redex? (_⇑_ {V = W} vW tag) vM = nothing
app-redex? (_⇑_ {V = W} vW (_↦_ {p = p} {q = q})) vM =
  just (_ , β-up-↦ vW vM)
app-redex? (_⇑_ {V = W} vW (`∀ {p = p})) vM = nothing
app-redex? (_⇓_ {V = W} vW (_↦_ {p = p} {q = q})) vM =
  just (_ , β-down-↦ vW vM)
app-redex? (_⇓_ {V = W} vW (`∀ {p = p})) vM = nothing
app-redex? (_⇓_ {V = W} vW (ν_ {B = B} {p = p})) vM = nothing
app-redex? (_↑_ {V = W} vW (_↦_ {p = p} {q = q})) vM =
  just (_ , β-reveal-↦ vW vM)
app-redex? (_↑_ {V = W} vW (`∀ {c = c})) vM = nothing
app-redex? (_↓_ {V = W} vW seal) vM = nothing
app-redex? (_↓_ {V = W} vW (_↦_ {p = p} {q = q})) vM =
  just (_ , β-conceal-↦ vW vM)
app-redex? (_↓_ {V = W} vW (`∀ {c = c})) vM = nothing

tapp-redex? :
  ∀ {Σ : Store}{M : Term}{B T : Ty} →
  Value M →
  Maybe (Step Σ (M ⦂∀ B [ T ]))
tapp-redex? (ƛ A ⇒ N) = nothing
tapp-redex? ($ κ) = nothing
tapp-redex? (Λ V) = just (_ , _ , β-Λ)
tapp-redex? (_⇑_ {V = W} vW tagν) = nothing
tapp-redex? (_⇑_ {V = W} vW tag) = nothing
tapp-redex? (_⇑_ {V = W} vW (_↦_ {p = p} {q = q})) = nothing
tapp-redex? (_⇑_ {V = W} vW (`∀ {p = p})) =
  just (_ , _ , pure-step (β-up-∀ vW))
tapp-redex? (_⇓_ {V = W} vW (_↦_ {p = p} {q = q})) = nothing
tapp-redex? (_⇓_ {V = W} vW (`∀ {p = p})) = just (_ , _ , β-down-∀ vW)
tapp-redex? (_⇓_ {V = W} vW (ν_ {B = B} {p = p})) =
  just (_ , _ , β-down-ν vW)
tapp-redex? (_↑_ {V = W} vW (_↦_ {p = p} {q = q})) = nothing
tapp-redex? (_↑_ {V = W} vW (`∀ {c = c})) =
  just (_ , _ , β-reveal-∀ vW)
tapp-redex? (_↓_ {V = W} vW seal) = nothing
tapp-redex? (_↓_ {V = W} vW (_↦_ {p = p} {q = q})) = nothing
tapp-redex? (_↓_ {V = W} vW (`∀ {c = c})) =
  just (_ , _ , β-conceal-∀ vW)

untag-step? :
  (Σ : Store) →
  (q : Imp) →
  (M : Term) →
  Maybe (Step Σ (M ⇓ (A⊑★ q)))
untag-step? Σ q (V ⇑ (A⊑★ p))
  with tyEq? (tgt⊑ p) (tgt⊑ q) | value? V
... | yes eq | just vV =
  just (Σ , _ , pure-step (tag-untag-ok {p = p} {q = q} vV eq))
... | no neq | just vV =
  just (Σ , _ , pure-step (tag-untag-bad {p = p} {q = q} {ℓ = zero} vV neq))
... | _ | _ = nothing
untag-step? Σ q M = nothing

unseal-step? :
  (Σ : Store) →
  (α : Seal) →
  (M : Term) →
  Maybe (Step Σ (M ↑ (↑-unseal α)))
unseal-step? Σ α (V ↓ (↓-seal beta)) with seal-≟ α beta | value? V
... | yes refl | just vV = just (Σ , _ , pure-step (seal-unseal vV))
... | _ | _ = nothing
unseal-step? Σ α M = nothing

up-id-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Imp) →
  Maybe (Step Σ (M ⇑ p))
up-id-step? Σ M ★⊑★ with value? M
... | just vM = just (Σ , _ , pure-step (id-up-★ vM))
... | nothing = nothing
up-id-step? Σ M (X⊑X X) with value? M
... | just vM = just (Σ , _ , pure-step (id-up-＇ vM))
... | nothing = nothing
up-id-step? Σ M (α⊑α α) with value? M
... | just vM = just (Σ , _ , pure-step (id-up-｀ vM))
... | nothing = nothing
up-id-step? Σ M (ι⊑ι ι) with value? M
... | just vM = just (Σ , _ , pure-step (id-up-‵ vM))
... | nothing = nothing
up-id-step? Σ M p = nothing

down-id-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Imp) →
  Maybe (Step Σ (M ⇓ p))
down-id-step? Σ M ★⊑★ with value? M
... | just vM = just (Σ , _ , pure-step (id-down-★ vM))
... | nothing = nothing
down-id-step? Σ M (X⊑X X) with value? M
... | just vM = just (Σ , _ , pure-step (id-down-＇ vM))
... | nothing = nothing
down-id-step? Σ M (α⊑α α) with value? M
... | just vM = just (Σ , _ , pure-step (id-down-｀ vM))
... | nothing = nothing
down-id-step? Σ M (ι⊑ι ι) with value? M
... | just vM = just (Σ , _ , pure-step (id-down-‵ vM))
... | nothing = nothing
down-id-step? Σ M p = nothing

up-head-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Imp) →
  Maybe (Step Σ (M ⇑ p))
up-head-step? Σ M (`∀A⊑B B p) with value? M
... | just vM = just (_ , _ , β-up-ν vM)
... | nothing = nothing
up-head-step? Σ M p = up-id-step? Σ M p

down-head-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Imp) →
  Maybe (Step Σ (M ⇓ p))
down-head-step? Σ M (A⊑★ p) = untag-step? Σ p M
down-head-step? Σ M p = down-id-step? Σ M p

reveal-head-step? :
  (Σ : Store) →
  (M : Term) →
  (c : Conv↑) →
  Maybe (Step Σ (M ↑ c))
reveal-head-step? Σ M (↑-unseal α) = unseal-step? Σ α M
reveal-head-step? Σ M (↑-id A) with value? M
... | just vM = just (Σ , _ , pure-step (id-reveal vM))
... | nothing = nothing
reveal-head-step? Σ M c = nothing

conceal-head-step? :
  (Σ : Store) →
  (M : Term) →
  (c : Conv↓) →
  Maybe (Step Σ (M ↓ c))
conceal-head-step? Σ M (↓-id A) with value? M
... | just vM = just (Σ , _ , pure-step (id-conceal vM))
... | nothing = nothing
conceal-head-step? Σ M c = nothing

------------------------------------------------------------------------
-- Partial progress and one-step execution
------------------------------------------------------------------------

data Progress? {Σ : Store} (M : Term) : Set where
  done : Value M → Progress? M
  step : Step Σ M → Progress? M
  stuck : Progress? M

step? : (Σ : Store) (M : Term) → Maybe (Step Σ M)
step? Σ (` x) = nothing
step? Σ (ƛ A ⇒ N) = nothing
step? Σ (Λ M) = nothing
step? Σ ($ κ) = nothing
step? Σ (blame ℓ) = nothing

step? Σ (L · M) with blame? L
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-·₁)
... | no neq with step? Σ L
...   | just (Σ′ , L′ , L→L′) = just (Σ′ , (L′ · M) , ξ-·₁ L→L′)
...   | nothing with value? L
...     | nothing = nothing
...     | just vL with step? Σ M
...       | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-·₂ vL M→M′)
...       | nothing with blame? M
...         | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step (blame-·₂ vL))
...         | no neq with value? M
...           | nothing = nothing
...           | just vM with app-redex? vL vM
...             | just (N , red) = just (Σ , N , pure-step red)
...             | nothing = nothing

step? Σ (M ⦂∀ B [ T ]) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-·α)
... | no neq with step? Σ M
... | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-·α M→M′)
... | nothing with value? M
...   | nothing = nothing
...   | just vM with tapp-redex? {Σ = Σ} {B = B} {T = T} vM
...     | just s = just s
...     | nothing = nothing

step? Σ (L ⊕[ op ] M) with blame? L
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-⊕₁)
... | no neq with step? Σ L
...   | just (Σ′ , L′ , L→L′) = just (Σ′ , (L′ ⊕[ op ] M) , ξ-⊕₁ L→L′)
...   | nothing with value? L
...     | nothing = nothing
...     | just vL with step? Σ M
...       | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-⊕₂ vL M→M′)
...       | nothing with blame? M
...         | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step (blame-⊕₂ vL))
...         | no neq with natConstView L | natConstView M | op
...           | just (m , refl) | just (n , refl) | addℕ =
                just (Σ , _ , pure-step δ-⊕)
...           | _ | _ | _ = nothing

step? Σ (M ⇑ p) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-up)
... | no neq with step? Σ M
...   | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ ⇑ p) , ξ-⇑ M→M′)
...   | nothing = up-head-step? Σ M p

step? Σ (M ⇓ p) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-down)
... | no neq with step? Σ M
...   | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ ⇓ p) , ξ-⇓ M→M′)
...   | nothing = down-head-step? Σ M p

step? Σ (M ↑ c) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-reveal)
... | no neq with step? Σ M
...   | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ ↑ c) , ξ-↑ M→M′)
...   | nothing = reveal-head-step? Σ M c

step? Σ (M ↓ c) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , pure-step blame-conceal)
... | no neq with step? Σ M
...   | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ ↓ c) , ξ-↓ M→M′)
...   | nothing = conceal-head-step? Σ M c

progress? : ∀ {Σ : Store} (M : Term) → Progress? {Σ = Σ} M
progress? {Σ = Σ} M with value? M
... | just v = done v
... | nothing with step? Σ M
...   | just s = step s
...   | nothing = stuck

------------------------------------------------------------------------
-- Fuel-bounded partial evaluation
------------------------------------------------------------------------

EvalResult : Store → Term → Set
EvalResult Σ M = Σ[ Σ′ ∈ Store ] Σ[ N ∈ Term ] (Σ ∣ M —↠ Σ′ ∣ N)

eval? : (gas : ℕ) (σ : Store) (M : Term) → Maybe (EvalResult σ M)
eval? zero σ M = just (σ , (M , (M ∎)))
eval? (suc gas) σ (blame ℓ) = just (σ , (blame ℓ , (blame ℓ ∎)))
eval? (suc gas) σ M with value? M
... | just v = just (σ , (M , (M ∎)))
... | nothing with step? σ M
...   | nothing = nothing
...   | just (Σ₁ , N , M→N) with eval? gas Σ₁ N
...     | nothing = nothing
...     | just (Σ₂ , K , N—↠K) =
          just (Σ₂ , (K , (M —→⟨ M→N ⟩ N—↠K)))

trace? :
  (gas : ℕ) →
  (σ : Store) →
  (M : Term) →
  Maybe (List RuleTag)
trace? gas σ M with eval? gas σ M
... | nothing = nothing
... | just (_ , (_ , M↠N)) = just (rules-of-multi M↠N)

trace-paths? :
  (gas : ℕ) →
  (σ : Store) →
  (M : Term) →
  Maybe (List StepPath)
trace-paths? gas σ M with eval? gas σ M
... | nothing = nothing
... | just (_ , (_ , M↠N)) = just (paths-of-multi M↠N)

trace-step-paths :
  (gas : ℕ) →
  (σ : Store) →
  (M : Term) →
  List StepPath
trace-step-paths zero σ M = []
trace-step-paths (suc gas) σ M with step? σ M
... | nothing = []
... | just (Σ₁ , N , M→N) =
    path-of-step M→N ∷ trace-step-paths gas Σ₁ N

trace-steps :
  (gas : ℕ) →
  (σ : Store) →
  (M : Term) →
  List RuleTag
trace-steps gas σ M = concat-step-paths (trace-step-paths gas σ M)

alloc-of-step :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —→ Σ′ ∣ N →
  List SealAllocTag
alloc-of-step (pure-step red) = []
alloc-of-step β-Λ = alloc-β-Λ ∷ []
alloc-of-step (β-down-∀ v) = alloc-β-down-∀ ∷ []
alloc-of-step (β-down-ν v) = alloc-β-down-ν ∷ []
alloc-of-step (β-up-ν v) = alloc-β-up-ν ∷ []
alloc-of-step (β-reveal-∀ v) = []
alloc-of-step (β-conceal-∀ v) = []
alloc-of-step (ξ-·₁ red) = alloc-of-step red
alloc-of-step (ξ-·₂ v red) = alloc-of-step red
alloc-of-step (ξ-·α red) = alloc-of-step red
alloc-of-step (ξ-⇑ red) = alloc-of-step red
alloc-of-step (ξ-⇓ red) = alloc-of-step red
alloc-of-step (ξ-↑ red) = alloc-of-step red
alloc-of-step (ξ-↓ red) = alloc-of-step red
alloc-of-step (ξ-⊕₁ red) = alloc-of-step red
alloc-of-step (ξ-⊕₂ v red) = alloc-of-step red

alloc-trace-steps :
  (gas : ℕ) →
  (σ : Store) →
  (M : Term) →
  List SealAllocTag
alloc-trace-steps zero σ M = []
alloc-trace-steps (suc gas) σ M with step? σ M
... | nothing = []
... | just (Σ₁ , N , M→N) =
    alloc-of-step M→N ++ alloc-trace-steps gas Σ₁ N

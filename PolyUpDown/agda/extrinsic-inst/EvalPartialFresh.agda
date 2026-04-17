module EvalPartialFresh where

-- File Charter:
--   * Untyped, partial execution for extrinsic-inst PolyUpDown under
--   * `ReductionFresh`.
--   * Provides a computable one-step function `step?`, a progress-style
--   * classifier `progress?`, and a fuel-bounded evaluator `eval?`.
--   * Intended for running examples and testing reduction rules without
--   * preservation/progress typing proofs.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _≟_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import ReductionFresh
  using
    ( UpValue
    ; DownValue
    ; Value
    ; tag
    ; seal
    ; _↦_
    ; ∀ᵖ
    ; ν_
    ; ƛ_⇒_
    ; $
    ; Λ_
    ; _up_
    ; _down_
    ; _—→_
    ; β
    ; β-up-∀
    ; β-up-↦
    ; β-down-↦
    ; id-up
    ; id-down
    ; seal-unseal
    ; tag-untag-ok
    ; tag-untag-bad
    ; β-up-；
    ; β-down-；
    ; δ-⊕
    ; blame-·₁
    ; blame-·₂
    ; blame-·α
    ; blame-up
    ; blame-down
    ; blame-⊕₁
    ; blame-⊕₂
    ; _∣_—→_∣_
    ; _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; id-step
    ; β-Λ
    ; β-down-∀
    ; β-down-ν
    ; β-up-ν
    ; ξ-·₁
    ; ξ-·₂
    ; ξ-·α
    ; ξ-up
    ; ξ-down
    ; ξ-⊕₁
    ; ξ-⊕₂
    )

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
  rule-id-up : RuleTag
  rule-id-down : RuleTag
  rule-seal-unseal : RuleTag
  rule-tag-untag-ok : RuleTag
  rule-tag-untag-bad : RuleTag
  rule-β-up-； : RuleTag
  rule-β-down-； : RuleTag
  rule-δ-⊕ : RuleTag
  rule-blame-·₁ : RuleTag
  rule-blame-·₂ : RuleTag
  rule-blame-·α : RuleTag
  rule-blame-up : RuleTag
  rule-blame-down : RuleTag
  rule-blame-⊕₁ : RuleTag
  rule-blame-⊕₂ : RuleTag
  rule-β-Λ : RuleTag
  rule-β-down-∀ : RuleTag
  rule-β-down-ν : RuleTag
  rule-β-up-ν : RuleTag
  rule-ξ-·₁ : RuleTag
  rule-ξ-·₂ : RuleTag
  rule-ξ-·α : RuleTag
  rule-ξ-up : RuleTag
  rule-ξ-down : RuleTag
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
classify-raw (id-up v) = rule-id-up
classify-raw (id-down v) = rule-id-down
classify-raw (seal-unseal v) = rule-seal-unseal
classify-raw (tag-untag-ok v) = rule-tag-untag-ok
classify-raw (tag-untag-bad v neq) = rule-tag-untag-bad
classify-raw (β-up-； v) = rule-β-up-；
classify-raw (β-down-； v) = rule-β-down-；
classify-raw δ-⊕ = rule-δ-⊕
classify-raw blame-·₁ = rule-blame-·₁
classify-raw (blame-·₂ v) = rule-blame-·₂
classify-raw blame-·α = rule-blame-·α
classify-raw blame-up = rule-blame-up
classify-raw blame-down = rule-blame-down
classify-raw blame-⊕₁ = rule-blame-⊕₁
classify-raw (blame-⊕₂ v) = rule-blame-⊕₂

classify-step :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —→ Σ′ ∣ N →
  RuleTag
classify-step (id-step red) = classify-raw red
classify-step β-Λ = rule-β-Λ
classify-step (β-down-∀ v) = rule-β-down-∀
classify-step (β-down-ν v) = rule-β-down-ν
classify-step (β-up-ν v) = rule-β-up-ν
classify-step (ξ-·₁ red) = rule-ξ-·₁
classify-step (ξ-·₂ v red) = rule-ξ-·₂
classify-step (ξ-·α red) = rule-ξ-·α
classify-step (ξ-up red) = rule-ξ-up
classify-step (ξ-down red) = rule-ξ-down
classify-step (ξ-⊕₁ red) = rule-ξ-⊕₁
classify-step (ξ-⊕₂ v red) = rule-ξ-⊕₂

StepPath : Set
StepPath = List RuleTag

path-of-step :
  ∀ {Σ Σ′ : Store}{M N : Term} →
  Σ ∣ M —→ Σ′ ∣ N →
  StepPath
path-of-step (id-step red) = classify-raw red ∷ []
path-of-step β-Λ = rule-β-Λ ∷ []
path-of-step (β-down-∀ v) = rule-β-down-∀ ∷ []
path-of-step (β-down-ν v) = rule-β-down-ν ∷ []
path-of-step (β-up-ν v) = rule-β-up-ν ∷ []
path-of-step (ξ-·₁ red) = rule-ξ-·₁ ∷ path-of-step red
path-of-step (ξ-·₂ v red) = rule-ξ-·₂ ∷ path-of-step red
path-of-step (ξ-·α red) = rule-ξ-·α ∷ path-of-step red
path-of-step (ξ-up red) = rule-ξ-up ∷ path-of-step red
path-of-step (ξ-down red) = rule-ξ-down ∷ path-of-step red
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

upValue? : (p : Up) → Maybe (UpValue p)
upValue? (tag G) = just tag
upValue? (unseal α) = nothing
upValue? (p ↦ q) = just (_↦_ {p = p} {q = q})
upValue? (∀ᵖ p) = just (∀ᵖ {p = p})
upValue? (ν p) = nothing
upValue? (id A) = nothing
upValue? (p ； q) = nothing

downValue? : (p : Down) → Maybe (DownValue p)
downValue? (untag G ℓ) = nothing
downValue? (seal α) = just seal
downValue? (p ↦ q) = just (_↦_ {p = p} {q = q})
downValue? (∀ᵖ p) = just (∀ᵖ {p = p})
downValue? (ν p) = just (ν_ {p = p})
downValue? (id A) = nothing
downValue? (p ； q) = nothing

value? : (M : Term) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ N) = just (ƛ A ⇒ N)
value? (L · M) = nothing
value? (Λ M) = just (Λ M)
value? (M ⦂∀ B [ T ]) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op ] M) = nothing
value? (M up p) with value? M | upValue? p
... | just vM | just vp = just (vM up vp)
... | _ | _ = nothing
value? (M down p) with value? M | downValue? p
... | just vM | just vp = just (vM down vp)
... | _ | _ = nothing
value? (blame ℓ) = nothing

blameLabel? : Term → Maybe Label
blameLabel? (blame ℓ) = just ℓ
blameLabel? _ = nothing

blameView : (M : Term) → Maybe (Σ[ ℓ ∈ Label ] (M ≡ blame ℓ))
blameView (blame ℓ) = just (ℓ , refl)
blameView _ = nothing

natConstView : (M : Term) → Maybe (Σ[ n ∈ ℕ ] (M ≡ $ (κℕ n)))
natConstView ($ (κℕ n)) = just (n , refl)
natConstView _ = nothing

app-redex? :
  ∀ {L M : Term} →
  Value L →
  Value M →
  Maybe (Σ[ N ∈ Term ] (L · M —→ N))
app-redex? (ƛ A ⇒ N) vM = just (_ , β vM)
app-redex? ($ κ) vM = nothing
app-redex? (Λ N) vM = nothing
app-redex? (_up_ {V = W} vW tag) vM = nothing
app-redex? (_up_ {V = W} vW (_↦_ {p = p} {q = q})) vM =
  just (_ , β-up-↦ vW vM)
app-redex? (_up_ {V = W} vW (∀ᵖ {p = p})) vM = nothing
app-redex? (_down_ {V = W} vW seal) vM = nothing
app-redex? (_down_ {V = W} vW (_↦_ {p = p} {q = q})) vM =
  just (_ , β-down-↦ vW vM)
app-redex? (_down_ {V = W} vW (∀ᵖ {p = p})) vM = nothing
app-redex? (_down_ {V = W} vW (ν_ {p = p})) vM = nothing

tapp-redex? :
  ∀ {Σ : Store}{M : Term}{B T : Ty} →
  Value M →
  Maybe (Step Σ (M ⦂∀ B [ T ]))
tapp-redex? (ƛ A ⇒ N) = nothing
tapp-redex? ($ κ) = nothing
tapp-redex? (Λ V) = just (_ , _ , β-Λ)
tapp-redex? (_up_ {V = W} vW tag) = nothing
tapp-redex? (_up_ {V = W} vW (_↦_ {p = p} {q = q})) = nothing
tapp-redex? (_up_ {V = W} vW (∀ᵖ {p = p})) =
  just (_ , _ , id-step (β-up-∀ vW))
tapp-redex? (_down_ {V = W} vW seal) = nothing
tapp-redex? (_down_ {V = W} vW (_↦_ {p = p} {q = q})) = nothing
tapp-redex? (_down_ {V = W} vW (∀ᵖ {p = p})) = just (_ , _ , β-down-∀ vW)
tapp-redex? (_down_ {V = W} vW (ν_ {p = p})) = just (_ , _ , β-down-ν vW)

unseal-step? :
  (Σ : Store) →
  (α : Seal) →
  (M : Term) →
  Maybe (Step Σ (M up (unseal α)))
unseal-step? Σ α M with value? M
unseal-step? Σ α M | just (_down_ {V = V} vV (seal {α = β₁})) with α ≟ β₁
unseal-step? Σ α M | just (_down_ {V = V} vV (seal {α = β₁})) | yes refl =
  just (Σ , _ , id-step (seal-unseal vV))
unseal-step? Σ α M | just (_down_ {V = V} vV (seal {α = β₁})) | no neq = nothing
unseal-step? Σ α M | _ = nothing

untag-step? :
  (Σ : Store) →
  (G : Ty) →
  (ℓ : Label) →
  (M : Term) →
  Maybe (Step Σ (M down (untag G ℓ)))
untag-step? Σ G ℓ (V up (tag H)) with tyEq? H G | value? V
untag-step? Σ G ℓ (V up (tag H)) | yes refl | just vV =
  just (Σ , _ , id-step (tag-untag-ok vV))
untag-step? Σ G ℓ (V up (tag H)) | no neq | just vV =
  just (Σ , _ , id-step (tag-untag-bad vV neq))
untag-step? Σ G ℓ (V up (tag H)) | _ | _ = nothing
untag-step? Σ G ℓ M = nothing

up-head-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Up) →
  Maybe (Step Σ (M up p))
up-head-step? Σ M (tag G) = nothing
up-head-step? Σ M (unseal α) = unseal-step? Σ α M
up-head-step? Σ M (p ↦ q) = nothing
up-head-step? Σ M (∀ᵖ p) = nothing
up-head-step? Σ M (ν p) with value? M
up-head-step? Σ M (ν p) | just vM = just (_ , _ , β-up-ν vM)
up-head-step? Σ M (ν p) | nothing = nothing
up-head-step? Σ M (id A) with value? M
up-head-step? Σ M (id A) | just vM = just (Σ , _ , id-step (id-up vM))
up-head-step? Σ M (id A) | nothing = nothing
up-head-step? Σ M (p ； q) with value? M
up-head-step? Σ M (p ； q) | just vM = just (Σ , _ , id-step (β-up-； vM))
up-head-step? Σ M (p ； q) | nothing = nothing

down-head-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Down) →
  Maybe (Step Σ (M down p))
down-head-step? Σ M (untag G ℓ) = untag-step? Σ G ℓ M
down-head-step? Σ M (seal α) = nothing
down-head-step? Σ M (p ↦ q) = nothing
down-head-step? Σ M (∀ᵖ p) = nothing
down-head-step? Σ M (ν p) = nothing
down-head-step? Σ M (id A) with value? M
down-head-step? Σ M (id A) | just vM = just (Σ , _ , id-step (id-down vM))
down-head-step? Σ M (id A) | nothing = nothing
down-head-step? Σ M (p ； q) with value? M
down-head-step? Σ M (p ； q) | just vM = just (Σ , _ , id-step (β-down-； vM))
down-head-step? Σ M (p ； q) | nothing = nothing

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

step? Σ ((blame ℓ) · M) = just (Σ , blame ℓ , id-step blame-·₁)
step? Σ (L · M) with step? Σ L
... | just (Σ′ , L′ , L→L′) = just (Σ′ , (L′ · M) , ξ-·₁ L→L′)
... | nothing with value? L
...   | nothing = nothing
...   | just vL with step? Σ M
...     | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-·₂ vL M→M′)
...     | nothing with blameView M
...       | just (ℓ , refl) = just (Σ , blame ℓ , id-step (blame-·₂ vL))
...       | nothing with value? M
...         | nothing = nothing
...         | just vM with app-redex? vL vM
...           | just (N , red) = just (Σ , N , id-step red)
...           | nothing = nothing

step? Σ (_⦂∀_[_] (blame ℓ) B T) = just (Σ , blame ℓ , id-step blame-·α)
step? Σ (_⦂∀_[_] M B T) with step? Σ M
... | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-·α M→M′)
... | nothing with value? M
...   | nothing = nothing
...   | just vM with tapp-redex? {Σ = Σ} {B = B} {T = T} vM
...     | just s = just s
...     | nothing = nothing

step? Σ ((blame ℓ) ⊕[ op ] M) = just (Σ , blame ℓ , id-step blame-⊕₁)
step? Σ (L ⊕[ op ] M) with step? Σ L
... | just (Σ′ , L′ , L→L′) = just (Σ′ , (L′ ⊕[ op ] M) , ξ-⊕₁ L→L′)
... | nothing with value? L
...   | nothing = nothing
...   | just vL with step? Σ M
...     | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-⊕₂ vL M→M′)
...     | nothing with blameView M
...       | just (ℓ , refl) = just (Σ , blame ℓ , id-step (blame-⊕₂ vL))
...       | nothing with natConstView L | natConstView M | op
...         | just (m , refl) | just (n , refl) | addℕ =
              just (Σ , _ , id-step δ-⊕)
...         | _ | _ | _ = nothing

step? Σ ((blame ℓ) up p) = just (Σ , blame ℓ , id-step blame-up)
step? Σ (M up p) with step? Σ M
... | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ up p) , ξ-up M→M′)
... | nothing = up-head-step? Σ M p

step? Σ ((blame ℓ) down p) = just (Σ , blame ℓ , id-step blame-down)
step? Σ (M down p) with step? Σ M
... | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ down p) , ξ-down M→M′)
... | nothing = down-head-step? Σ M p

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
...     | just (Σ₂ , K , N—↠K) = just (Σ₂ , (K , (M —→⟨ M→N ⟩ N—↠K)))

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
... | just (Σ₁ , N , M→N) = path-of-step M→N ∷ trace-step-paths gas Σ₁ N

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
alloc-of-step (id-step red) = []
alloc-of-step β-Λ = alloc-β-Λ ∷ []
alloc-of-step (β-down-∀ v) = alloc-β-down-∀ ∷ []
alloc-of-step (β-down-ν v) = alloc-β-down-ν ∷ []
alloc-of-step (β-up-ν v) = alloc-β-up-ν ∷ []
alloc-of-step (ξ-·₁ red) = alloc-of-step red
alloc-of-step (ξ-·₂ v red) = alloc-of-step red
alloc-of-step (ξ-·α red) = alloc-of-step red
alloc-of-step (ξ-up red) = alloc-of-step red
alloc-of-step (ξ-down red) = alloc-of-step red
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

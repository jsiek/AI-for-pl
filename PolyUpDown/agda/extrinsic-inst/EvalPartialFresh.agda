module EvalPartialFresh where

-- File Charter:
--   * Untyped, partial execution for extrinsic-inst PolyUpDown under
--   * `ReductionFresh`.
--   * Provides a computable one-step function `step?`, a progress-style
--   * classifier `progress?`, and a fuel-bounded evaluator `eval?`.
--   * Intended for running examples and testing reduction rules without
--   * preservation/progress typing proofs.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _≟_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import ReductionFresh

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
upValue? (tag p G) = just tag
upValue? (unseal α p) = nothing
upValue? (p ↦ q) = just (_↦_ {p = p} {q = q})
upValue? (∀ᵖ p) = just (∀ᵖ {p = p})
upValue? (ν p) = nothing
upValue? (id A) = nothing

downValue? : (p : Down) → Maybe (DownValue p)
downValue? (untag G ℓ p) = nothing
downValue? (seal p α) = just seal
downValue? (p ↦ q) = just (_↦_ {p = p} {q = q})
downValue? (∀ᵖ p) = just (∀ᵖ {p = p})
downValue? (ν p) = just (ν_ {p = p})
downValue? (id A) = nothing

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
  (q : Up) →
  (M : Term) →
  Maybe (Step Σ (M up (unseal α q)))
unseal-step? Σ α q M with value? M
unseal-step? Σ α q M | just (_down_ {V = V} vV (seal {p = p} {α = β₁})) with α ≟ β₁
unseal-step? Σ α q M | just (_down_ {V = V} vV (seal {p = p} {α = β₁})) | yes refl =
  just (Σ , _ , id-step (seal-unseal {p = p} {q = q} vV))
unseal-step? Σ α q M | just (_down_ {V = V} vV (seal {p = p} {α = β₁})) | no neq = nothing
unseal-step? Σ α q M | _ = nothing

untag-step? :
  (Σ : Store) →
  (G : Ty) →
  (ℓ : Label) →
  (q : Down) →
  (M : Term) →
  Maybe (Step Σ (M down (untag G ℓ q)))
untag-step? Σ G ℓ q (V up (tag p H)) with tyEq? H G | value? V
untag-step? Σ G ℓ q (V up (tag p H)) | yes refl | just vV =
  just (Σ , _ , id-step (tag-untag-ok {p = p} {q = q} vV))
untag-step? Σ G ℓ q (V up (tag p H)) | no neq | just vV =
  just (Σ , _ , id-step (tag-untag-bad {p = p} {q = q} vV neq))
untag-step? Σ G ℓ q (V up (tag p H)) | _ | _ = nothing
untag-step? Σ G ℓ q M = nothing

up-head-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Up) →
  Maybe (Step Σ (M up p))
up-head-step? Σ M (tag p G) = nothing
up-head-step? Σ M (unseal α p) = unseal-step? Σ α p M
up-head-step? Σ M (p ↦ q) = nothing
up-head-step? Σ M (∀ᵖ p) = nothing
up-head-step? Σ M (ν p) with value? M
up-head-step? Σ M (ν p) | just vM = just (_ , _ , β-up-ν vM)
up-head-step? Σ M (ν p) | nothing = nothing
up-head-step? Σ M (id A) with value? M
up-head-step? Σ M (id A) | just vM = just (Σ , _ , id-step (id-up vM))
up-head-step? Σ M (id A) | nothing = nothing

down-head-step? :
  (Σ : Store) →
  (M : Term) →
  (p : Down) →
  Maybe (Step Σ (M down p))
down-head-step? Σ M (untag G ℓ p) = untag-step? Σ G ℓ p M
down-head-step? Σ M (seal p α) = nothing
down-head-step? Σ M (p ↦ q) = nothing
down-head-step? Σ M (∀ᵖ p) = nothing
down-head-step? Σ M (ν p) = nothing
down-head-step? Σ M (id A) with value? M
down-head-step? Σ M (id A) | just vM = just (Σ , _ , id-step (id-down vM))
down-head-step? Σ M (id A) | nothing = nothing

------------------------------------------------------------------------
-- Partial progress and one-step execution
------------------------------------------------------------------------

data Progress? {Σ : Store} (M : Term) : Set where
  done : Value M → Progress? M
  step : Step Σ M → Progress? M
  stuck : Progress? M

blame? : (M : Term) → Dec (∃[ ℓ ] M ≡ blame ℓ)
blame? (` x) = no (λ ())
blame? (ƛ x ⇒ M) = no (λ ())
blame? (M · M₁) = no (λ ())
blame? (Λ M) = no (λ ())
blame? (M ⦂∀ x [ x₁ ]) = no (λ ())
blame? ($ x) = no (λ ())
blame? (M ⊕[ x ] M₁) = no λ ()
blame? (M up x) = no λ ()
blame? (M down x) = no (λ ())
blame? (blame ℓ) = yes (ℓ , refl)

step? : (Σ : Store) (M : Term) → Maybe (Step Σ M)
step? Σ (` x) = nothing
step? Σ (ƛ A ⇒ N) = nothing
step? Σ (Λ M) = nothing
step? Σ ($ κ) = nothing
step? Σ (blame ℓ) = nothing

step? Σ (L · M) with blame? L
... | yes (ℓ , refl) = just (Σ , blame ℓ , id-step blame-·₁)
... | no neq with step? Σ L
...   | just (Σ′ , L′ , L→L′) = just (Σ′ , (L′ · M) , ξ-·₁ L→L′)
...   | nothing with value? L
...     | nothing = nothing
...     | just vL with step? Σ M
...       | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-·₂ vL M→M′)
...       | nothing with blame? M
...         | yes (ℓ , refl) = just (Σ , blame ℓ , id-step (blame-·₂ vL))
...         | no neq with value? M
...           | nothing = nothing
...           | just vM with app-redex? vL vM
...             | just (N , red) = just (Σ , N , id-step red)
...             | nothing = nothing

step? Σ (_⦂∀_[_] M B T) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , id-step blame-·α)
... | no neq with step? Σ M
... | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-·α M→M′)
... | nothing with value? M
...   | nothing = nothing
...   | just vM with tapp-redex? {Σ = Σ} {B = B} {T = T} vM
...     | just s = just s
...     | nothing = nothing

step? Σ (L ⊕[ op ] M) with blame? L
... | yes (ℓ , refl) = just (Σ , blame ℓ , id-step blame-⊕₁)
... | no neq with step? Σ L
...   | just (Σ′ , L′ , L→L′) = just (Σ′ , (L′ ⊕[ op ] M) , ξ-⊕₁ L→L′)
...   | nothing with value? L
...     | nothing = nothing
...     | just vL with step? Σ M
...       | just (Σ′ , M′ , M→M′) = just (Σ′ , _ , ξ-⊕₂ vL M→M′)
...       | nothing with blame? M
...         | yes (ℓ , refl) = just (Σ , blame ℓ , id-step (blame-⊕₂ vL))
...         | no neq with natConstView L | natConstView M | op
...           | just (m , refl) | just (n , refl) | addℕ =
                just (Σ , _ , id-step δ-⊕)
...           | _ | _ | _ = nothing

step? Σ (M up p) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , id-step blame-up)
... | no neq with step? Σ M
...   | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ up p) , ξ-up M→M′)
...   | nothing = up-head-step? Σ M p

step? Σ (M down p) with blame? M
... | yes (ℓ , refl) = just (Σ , blame ℓ , id-step blame-down)
... | no neq with step? Σ M
...   | just (Σ′ , M′ , M→M′) = just (Σ′ , (M′ down p) , ξ-down M→M′)
...   | nothing = down-head-step? Σ M p

progress? : ∀ {Σ : Store} (M : Term) → Progress? {Σ = Σ} M
progress? {Σ = Σ} M with value? M
... | just v = done v
... | nothing with step? Σ M
...   | just s = step s
...   | nothing = stuck

------------------------------------------------------------------------
-- Completeness of `step?` for one-step reduction
------------------------------------------------------------------------

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

step?-value-none :
  ∀ {Σ : Store} {V : Term} →
  Value V →
  step? Σ V ≡ nothing
step?-value-none {Σ = Σ} {V = V} vV with step? Σ V
step?-value-none {Σ = Σ} {V = V} vV | nothing = refl
step?-value-none {Σ = Σ} {V = V} vV | just (Σ′ , N , red) =
  ⊥-elim (value-no-step vV red)

step?-blame-none :
  ∀ {Σ : Store} {ℓ : Label} →
  step? Σ (blame ℓ) ≡ nothing
step?-blame-none = refl

target : ∀ {Σ : Store} {M : Term} → Step Σ M → Store × Term
target (Σ′ , N , red) = Σ′ , N

value?-complete :
  ∀ {V : Term} →
  (vV : Value V) →
  Σ[ v ∈ Value V ] (value? V ≡ just v)
value?-complete (ƛ A ⇒ N) = (ƛ A ⇒ N) , refl
value?-complete ($ κ) = ($ κ) , refl
value?-complete (Λ N) = (Λ N) , refl
value?-complete (_up_ {V = V} vV tag) with value?-complete vV
value?-complete (_up_ {V = V} vV tag) | vV′ , eqV rewrite eqV =
  (vV′ up tag) , refl
value?-complete (_up_ {V = V} vV (_↦_ {p = p} {q = q})) with value?-complete vV
value?-complete (_up_ {V = V} vV (_↦_ {p = p} {q = q})) | vV′ , eqV rewrite eqV =
  (vV′ up (_↦_ {p = p} {q = q})) , refl
value?-complete (_up_ {V = V} vV (∀ᵖ {p = p})) with value?-complete vV
value?-complete (_up_ {V = V} vV (∀ᵖ {p = p})) | vV′ , eqV rewrite eqV =
  (vV′ up (∀ᵖ {p = p})) , refl
value?-complete (_down_ {V = V} vV seal) with value?-complete vV
value?-complete (_down_ {V = V} vV seal) | vV′ , eqV rewrite eqV =
  (vV′ down seal) , refl
value?-complete (_down_ {V = V} vV (_↦_ {p = p} {q = q})) with value?-complete vV
value?-complete (_down_ {V = V} vV (_↦_ {p = p} {q = q})) | vV′ , eqV rewrite eqV =
  (vV′ down (_↦_ {p = p} {q = q})) , refl
value?-complete (_down_ {V = V} vV (∀ᵖ {p = p})) with value?-complete vV
value?-complete (_down_ {V = V} vV (∀ᵖ {p = p})) | vV′ , eqV rewrite eqV =
  (vV′ down (∀ᵖ {p = p})) , refl
value?-complete (_down_ {V = V} vV (ν_ {p = p})) with value?-complete vV
value?-complete (_down_ {V = V} vV (ν_ {p = p})) | vV′ , eqV rewrite eqV =
  (vV′ down (ν_ {p = p})) , refl

value-not-blame :
  ∀ {V : Term} {ℓ : Label} →
  Value V →
  V ≡ blame ℓ →
  ⊥
value-not-blame (ƛ A ⇒ N) ()
value-not-blame ($ κ) ()
value-not-blame (Λ N) ()
value-not-blame (_up_ vV tag) ()
value-not-blame (_up_ vV (_↦_ {p = p} {q = q})) ()
value-not-blame (_up_ vV (∀ᵖ {p = p})) ()
value-not-blame (_down_ vV seal) ()
value-not-blame (_down_ vV (_↦_ {p = p} {q = q})) ()
value-not-blame (_down_ vV (∀ᵖ {p = p})) ()
value-not-blame (_down_ vV (ν_ {p = p})) ()

value?-not-none :
  ∀ {V : Term} →
  Value V →
  value? V ≡ nothing →
  ⊥
value?-not-none vV eq with value?-complete vV
value?-not-none vV eq | vV′ , eqV = nothing≢just (trans (sym eq) eqV)

step?-β-up-↦ :
  ∀ {Σ : Store} {V W : Term} {p : Down} {q : Up} →
  (vV : Value V) →
  (vW : Value W) →
  Σ[ s ∈ Step Σ ((V up (p UpDown.↦ q)) · W) ]
    (step? Σ ((V up (p UpDown.↦ q)) · W) ≡ just s) ×
    (target s ≡ (Σ , ((V · (W down p)) up q)))
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  with step? Σ (V up (p UpDown.↦ q))
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | just (ΣL , L′ , redL) =
  ⊥-elim (value-no-step (_up_ {V = V} vV (_↦_ {p = p} {q = q})) redL)
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing with value? (V up (p UpDown.↦ q)) in eqL
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | nothing = ⊥-elim (value?-not-none (_up_ vV (_↦_ {p = p} {q = q})) eqL)
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) with step? Σ W
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | just (ΣW , W′ , redW) =
  ⊥-elim (value-no-step vW redW)
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing
  with blame? W
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | yes (ℓ , W≡blame) =
  ⊥-elim (value-not-blame vW W≡blame)
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | no neq
  with value? W in eqW
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | no neq | nothing =
  ⊥-elim (value?-not-none vW eqW)
step?-β-up-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_up_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | no neq | just vW′ =
  (_ , _ , id-step (β-up-↦ vV′ vW′)) , refl , refl

step?-β-down-↦ :
  ∀ {Σ : Store} {V W : Term} {p : Up} {q : Down} →
  (vV : Value V) →
  (vW : Value W) →
  Σ[ s ∈ Step Σ ((V down (p UpDown.↦ q)) · W) ]
    (step? Σ ((V down (p UpDown.↦ q)) · W) ≡ just s) ×
    (target s ≡ (Σ , ((V · (W up p)) down q)))
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  with step? Σ (V down (p UpDown.↦ q))
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | just (ΣL , L′ , redL) =
  ⊥-elim (value-no-step (_down_ {V = V} vV (_↦_ {p = p} {q = q})) redL)
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing with value? (V down (p UpDown.↦ q)) in eqL
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | nothing = ⊥-elim (value?-not-none (_down_ vV (_↦_ {p = p} {q = q})) eqL)
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) with step? Σ W
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | just (ΣW , W′ , redW) =
  ⊥-elim (value-no-step vW redW)
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing
  with blame? W
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | yes (ℓ , W≡blame) =
  ⊥-elim (value-not-blame vW W≡blame)
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | no neq
  with value? W in eqW
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | no neq | nothing =
  ⊥-elim (value?-not-none vW eqW)
step?-β-down-↦ {Σ = Σ} {V = V} {W = W} {p = p} {q = q} vV vW
  | nothing | just (_down_ {V = .V} vV′ (_↦_ {p = .p} {q = .q})) | nothing | no neq | just vW′ =
  (_ , _ , id-step (β-down-↦ vV′ vW′)) , refl , refl

step?-id-up :
  ∀ {Σ : Store} {V : Term} {A : Ty} →
  (vV : Value V) →
  Σ[ s ∈ Step Σ (V up (UpDown.id A)) ]
    (step? Σ (V up (UpDown.id A)) ≡ just s) ×
    (target s ≡ (Σ , V))
step?-id-up {Σ = Σ} {V = V} {A = A} vV with step? Σ V
step?-id-up {Σ = Σ} {V = V} {A = A} vV | just (ΣV , V′ , redV) =
  ⊥-elim (value-no-step vV redV)
step?-id-up {Σ = Σ} {V = V} {A = A} vV | nothing
  with blame? V
... | yes (ℓ , refl) = (Σ , blame ℓ , id-step blame-up) , refl , refl
... | no neq
  rewrite step?-value-none {Σ = Σ} {V = V} vV
        | proj₂ (value?-complete vV)
  =
  let vV′ = proj₁ (value?-complete vV) in
  (_ , _ , id-step (id-up vV′)) , refl , refl

step?-id-down :
  ∀ {Σ : Store} {V : Term} {A : Ty} →
  (vV : Value V) →
  Σ[ s ∈ Step Σ (V down (Down.id A)) ]
    (step? Σ (V down (Down.id A)) ≡ just s) ×
    (target s ≡ (Σ , V))
step?-id-down {Σ = Σ} {V = V} {A = A} vV with step? Σ V
step?-id-down {Σ = Σ} {V = V} {A = A} vV | just (ΣV , V′ , redV) =
  ⊥-elim (value-no-step vV redV)
step?-id-down {Σ = Σ} {V = V} {A = A} vV | nothing
  with blame? V
... | yes (ℓ , refl) = (Σ , blame ℓ , id-step blame-down) , refl , refl
... | no neq
  rewrite step?-value-none {Σ = Σ} {V = V} vV
        | proj₂ (value?-complete vV)
  =
  let vV′ = proj₁ (value?-complete vV) in
  (_ , _ , id-step (id-down vV′)) , refl , refl

step?-seal-unseal :
  ∀ {Σ : Store} {V : Term} {α : Seal} {p : Down} {q : Up} →
  (vV : Value V) →
  Σ[ s ∈ Step Σ ((V down (Down.seal p α)) up (Up.unseal α q)) ]
    (step? Σ ((V down (Down.seal p α)) up (Up.unseal α q)) ≡ just s) ×
    (target s ≡ (Σ , ((V down p) up q)))
step?-seal-unseal {Σ = Σ} {V = V} {α = α} {p = p} {q = q} vV
  with step? Σ (V down (Down.seal p α))
step?-seal-unseal {Σ = Σ} {V = V} {α = α} {p = p} {q = q} vV
  | just (Σ′ , N′ , red) = ⊥-elim (value-no-step (_down_ vV seal) red)
step?-seal-unseal {Σ = Σ} {V = V} {α = α} {p = p} {q = q} vV
  | nothing with blame? (V down (Down.seal p α))
... | yes (ℓ , eq) = ⊥-elim (value-not-blame (_down_ vV seal) eq)
... | no neq with value? (V down (Down.seal p α)) in eqM
... | nothing = ⊥-elim (value?-not-none (_down_ vV seal) eqM)
... | just (_down_ {V = .V} vV′ (seal {p = .p} {α = .α})) with α ≟ α
... | yes refl = (_ , _ , id-step (seal-unseal {p = p} {q = q} vV′)) , refl , refl
... | no α≢α = ⊥-elim (α≢α refl)

step?-complete :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  (red : Σ ∣ M —→ Σ′ ∣ N) →
  Σ[ s ∈ Step Σ M ]
    (step? Σ M ≡ just s) ×
    (target s ≡ (Σ′ , N))
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  with blame? (Term.ƛ B ⇒ N)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | yes (ℓ , ())
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq with step? Σ (Term.ƛ B ⇒ N)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | just (ΣL , L′ , redL) = ⊥-elim (value-no-step (ƛ B ⇒ N) redL)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing with value? (Term.ƛ B ⇒ N) in eqL
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | nothing = ⊥-elim (value?-not-none (ƛ B ⇒ N) eqL)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) with step? Σ V
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) | just (ΣV , V′ , redV) =
  ⊥-elim (value-no-step vV redV)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) | nothing with blame? V
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) | nothing | yes (ℓ , eq) =
  ⊥-elim (value-not-blame vV eq)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) | nothing | no neqV with value? V in eqV
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) | nothing | no neqV | nothing =
  ⊥-elim (value?-not-none vV eqV)
step?-complete {Σ = Σ} (id-step (β {B = B} {N = N} {V = V} vV))
  | no neq | nothing | just (ƛ .B ⇒ .N) | nothing | no neqV | just x =
  (_ , _ , id-step (β x)) , refl , refl
step?-complete {Σ = Σ} (id-step (β-up-∀ {V = V} {p = p} vV))
  with step? Σ (V up (UpDown.∀ᵖ p))
step?-complete {Σ = Σ} (id-step (β-up-∀ {V = V} {p = p} vV))
  | just (ΣM , M′ , redM) =
  ⊥-elim (value-no-step (_up_ {V = V} vV (∀ᵖ {p = p})) redM)
step?-complete {Σ = Σ} (id-step (β-up-∀ {V = V} {p = p} vV))
  | nothing with value?-complete (_up_ {V = V} vV (∀ᵖ {p = p}))
step?-complete {Σ = Σ} (id-step (β-up-∀ {V = V} {p = p} vV))
  | nothing | (_up_ {V = .V} vV′ (∀ᵖ {p = .p})) , eqM
  rewrite eqM =
  (_ , _ , id-step (β-up-∀ vV′)) , refl , refl
step?-complete (id-step (β-up-↦ vV vW)) =
  step?-β-up-↦ vV vW
step?-complete (id-step (β-down-↦ vV vW)) =
  step?-β-down-↦ vV vW
step?-complete (id-step (id-up {V = V} {A = A} vV)) = step?-id-up {V = V} {A = A} vV
step?-complete (id-step (id-down {V = V} {A = A} vV)) = step?-id-down {V = V} {A = A} vV
step?-complete (id-step (seal-unseal {V = V} {p = p} {q = q} {α = α} vV)) =
  step?-seal-unseal vV
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  with blame? (V up (UpDown.tag p G))
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | yes (ℓb , eq) = ⊥-elim (value-not-blame (_up_ vV tag) eq)
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq with step? Σ (V up (UpDown.tag p G))
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq | just (Σ′ , M′ , red) = ⊥-elim (value-no-step (_up_ vV tag) red)
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq | nothing with tyEq? G G
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq | nothing | no G≢G = ⊥-elim (G≢G refl)
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq | nothing | yes refl with value? V in eqV
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq | nothing | yes refl | nothing = ⊥-elim (value?-not-none vV eqV)
step?-complete {Σ = Σ}
  (id-step (tag-untag-ok {G = G} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV))
  | no neq | nothing | yes refl | just vV′ =
  (_ , _ , id-step (tag-untag-ok {p = p} {q = q} vV′)) , refl , refl
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  with blame? (V up (UpDown.tag p G))
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | yes (ℓb , eq) = ⊥-elim (value-not-blame (_up_ vV tag) eq)
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq with step? Σ (V up (UpDown.tag p G))
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq | just (Σ′ , M′ , red) = ⊥-elim (value-no-step (_up_ vV tag) red)
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq | nothing with tyEq? G H
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq | nothing | yes G≡H = ⊥-elim (G≢H G≡H)
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq | nothing | no G≢H′ with value? V in eqV
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq | nothing | no G≢H′ | nothing = ⊥-elim (value?-not-none vV eqV)
step?-complete {Σ = Σ}
  (id-step (tag-untag-bad {G = G} {H = H} {V = V} {p = p} {q = q} {ℓ′ = ℓ} vV G≢H))
  | no neq | nothing | no G≢H′ | just vV′ =
  (_ , _ , id-step (tag-untag-bad {p = p} {q = q} vV′ G≢H′)) , refl , refl
step?-complete (id-step δ-⊕) = (_ , _ , id-step δ-⊕) , refl , refl
step?-complete (id-step blame-·₁) = (_ , _ , id-step blame-·₁) , refl , refl
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  with blame? V
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | yes (ℓV , eq) = ⊥-elim (value-not-blame vV eq)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV with step? Σ V
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | just (ΣV , V′ , redV) = ⊥-elim (value-no-step vV redV)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing with value? V in eqV
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing | nothing = ⊥-elim (value?-not-none vV eqV)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing | just vV′ with step? Σ (blame ℓ) in eqM
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing | just vV′ | just s =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eqM))
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing | just vV′ | nothing with blame? (blame ℓ)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing | just vV′ | nothing | yes (ℓ′ , refl) =
  (_ , _ , id-step (blame-·₂ vV′)) , refl , refl
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-·₂ {V = V} vV))
  | no neqV | nothing | just vV′ | nothing | no neqℓ =
  ⊥-elim (neqℓ (ℓ , refl))
step?-complete (id-step blame-·α) = (_ , _ , id-step blame-·α) , refl , refl
step?-complete (id-step blame-up) = (_ , _ , id-step blame-up) , refl , refl
step?-complete (id-step blame-down) = (_ , _ , id-step blame-down) , refl , refl
step?-complete (id-step blame-⊕₁) = (_ , _ , id-step blame-⊕₁) , refl , refl
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  with blame? L
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | yes (ℓL , eq) = ⊥-elim (value-not-blame vL eq)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL with step? Σ L
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | just (ΣL , L′ , redL) = ⊥-elim (value-no-step vL redL)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing with value? L in eqL
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing | nothing = ⊥-elim (value?-not-none vL eqL)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing | just vL′ with step? Σ (blame ℓ) in eqM
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing | just vL′ | just s =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eqM))
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing | just vL′ | nothing with blame? (blame ℓ)
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing | just vL′ | nothing | yes (ℓ′ , refl) =
  (_ , _ , id-step (blame-⊕₂ vL′)) , refl , refl
step?-complete {Σ = Σ} {N = blame ℓ} (id-step (blame-⊕₂ {L = L} {op = op} vL))
  | no neqL | nothing | just vL′ | nothing | no neqℓ =
  ⊥-elim (neqℓ (ℓ , refl))
step?-complete β-Λ = (_ , _ , β-Λ) , refl , refl
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  with blame? (V down (Down.∀ᵖ p))
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  | yes (ℓ , eq) = ⊥-elim (value-not-blame (_down_ vV (∀ᵖ {p = p})) eq)
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  | no neq with step? Σ (V down (Down.∀ᵖ p))
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | just (Σ′ , M′ , red) =
  ⊥-elim (value-no-step (_down_ vV (∀ᵖ {p = p})) red)
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | nothing with value? (V down (Down.∀ᵖ p)) in eqM
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | nothing | nothing =
  ⊥-elim (value?-not-none (_down_ vV (∀ᵖ {p = p})) eqM)
step?-complete {Σ = Σ} (β-down-∀ {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | nothing | just (_down_ {V = .V} vV′ (∀ᵖ {p = .p})) =
  (_ , _ , β-down-∀ vV′) , refl , refl
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  with blame? (V down (Down.ν p))
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  | yes (ℓ , eq) = ⊥-elim (value-not-blame (_down_ vV (ν_ {p = p})) eq)
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  | no neq with step? Σ (V down (Down.ν p))
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | just (Σ′ , M′ , red) =
  ⊥-elim (value-no-step (_down_ vV (ν_ {p = p})) red)
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | nothing with value? (V down (Down.ν p)) in eqM
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | nothing | nothing =
  ⊥-elim (value?-not-none (_down_ vV (ν_ {p = p})) eqM)
step?-complete {Σ = Σ} (β-down-ν {A = A} {B = B} {V = V} {p = p} vV)
  | no neq | nothing | just (_down_ {V = .V} vV′ (ν_ {p = .p})) =
  (_ , _ , β-down-ν vV′) , refl , refl
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) with blame? V
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) | yes (ℓ , eq) =
  ⊥-elim (value-not-blame vV eq)
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) | no neq with step? Σ V
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) | no neq | just (Σ′ , M′ , red) =
  ⊥-elim (value-no-step vV red)
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) | no neq | nothing with value? V in eqV
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) | no neq | nothing | nothing =
  ⊥-elim (value?-not-none vV eqV)
step?-complete {Σ = Σ} (β-up-ν {V = V} {p = p} vV) | no neq | nothing | just vV′ =
  (_ , _ , β-up-ν vV′) , refl , refl
step?-complete {Σ = Σ} (ξ-·₁ {L = L} {M = M} red) with step?-complete red
step?-complete {Σ = Σ} (ξ-·₁ {L = L} {M = M} red)
  | (Σ′ , L′ , red′) , eq , tgt with blame? L
step?-complete {Σ = Σ} (ξ-·₁ {L = L} {M = M} red)
  | (Σ′ , L′ , red′) , eq , tgt | yes (ℓ , refl) =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eq))
step?-complete {Σ = Σ} (ξ-·₁ {L = L} {M = M} red)
  | (Σ′ , L′ , red′) , eq , tgt | no neq
  rewrite eq =
  (Σ′ , L′ · M , ξ-·₁ red′) , refl ,
  cong (λ p → proj₁ p , (proj₂ p · M)) tgt
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red) with step?-complete red
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt with blame? V
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | yes (ℓ , eqV) =
  ⊥-elim (value-not-blame vV eqV)
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV with step? Σ V
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | just (ΣV , V′ , redV) =
  ⊥-elim (value-no-step vV redV)
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | nothing with value? V in eqVal
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | nothing | nothing =
  ⊥-elim (value?-not-none vV eqVal)
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | nothing | just vV′
  with step? Σ M in eqM
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | nothing | just vV′ | nothing =
  ⊥-elim (nothing≢just eq)
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | nothing | just vV′ | just s
  with just-injective eq
step?-complete {Σ = Σ} (ξ-·₂ {V = V} {M = M} vV red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqV | nothing | just vV′ | just s
  | refl =
  (Σ′ , V · M′ , ξ-·₂ vV′ red′) , refl ,
  cong (λ p → proj₁ p , (V · proj₂ p)) tgt
step?-complete {Σ = Σ} (ξ-·α {M = M} {B = B} {T = T} red) with step?-complete red
step?-complete {Σ = Σ} (ξ-·α {M = M} {B = B} {T = T} red)
  | (Σ′ , M′ , red′) , eq , tgt with blame? M
step?-complete {Σ = Σ} (ξ-·α {M = M} {B = B} {T = T} red)
  | (Σ′ , M′ , red′) , eq , tgt | yes (ℓ , refl) =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eq))
step?-complete {Σ = Σ} (ξ-·α {M = M} {B = B} {T = T} red)
  | (Σ′ , M′ , red′) , eq , tgt | no neq
  rewrite eq =
  (Σ′ , (M′ ⦂∀ B [ T ]) , ξ-·α red′) , refl ,
  cong (λ p → proj₁ p , (proj₂ p ⦂∀ B [ T ])) tgt
step?-complete {Σ = Σ} {M = (M₀ up p)} (ξ-up {p = p} red) with step?-complete red
step?-complete {Σ = Σ} {M = (M₀ up p)} (ξ-up {p = p} red)
  | (Σ′ , M′ , red′) , eq , tgt with blame? M₀
step?-complete {Σ = Σ} {M = (M₀ up p)} (ξ-up {p = p} red)
  | (Σ′ , M′ , red′) , eq , tgt | yes (ℓ , refl) =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eq))
step?-complete {Σ = Σ} {M = (M₀ up p)} (ξ-up {p = p} red)
  | (Σ′ , M′ , red′) , eq , tgt | no neq
  rewrite eq =
  (Σ′ , (M′ up p) , ξ-up red′) , refl ,
  cong (λ q → proj₁ q , (proj₂ q up p)) tgt
step?-complete {Σ = Σ} {M = (M₀ down p)} (ξ-down {p = p} red) with step?-complete red
step?-complete {Σ = Σ} {M = (M₀ down p)} (ξ-down {p = p} red)
  | (Σ′ , M′ , red′) , eq , tgt with blame? M₀
step?-complete {Σ = Σ} {M = (M₀ down p)} (ξ-down {p = p} red)
  | (Σ′ , M′ , red′) , eq , tgt | yes (ℓ , refl) =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eq))
step?-complete {Σ = Σ} {M = (M₀ down p)} (ξ-down {p = p} red)
  | (Σ′ , M′ , red′) , eq , tgt | no neq
  rewrite eq =
  (Σ′ , (M′ down p) , ξ-down red′) , refl ,
  cong (λ q → proj₁ q , (proj₂ q down p)) tgt
step?-complete {Σ = Σ} {M = (L₀ ⊕[ op ] M₀)} (ξ-⊕₁ {op = op} red) with step?-complete red
step?-complete {Σ = Σ} {M = (L₀ ⊕[ op ] M₀)} (ξ-⊕₁ {op = op} red)
  | (Σ′ , L′ , red′) , eq , tgt with blame? L₀
step?-complete {Σ = Σ} {M = (L₀ ⊕[ op ] M₀)} (ξ-⊕₁ {op = op} red)
  | (Σ′ , L′ , red′) , eq , tgt | yes (ℓ , refl) =
  ⊥-elim (nothing≢just (trans (sym step?-blame-none) eq))
step?-complete {Σ = Σ} {M = (L₀ ⊕[ op ] M₀)} (ξ-⊕₁ {op = op} red)
  | (Σ′ , L′ , red′) , eq , tgt | no neq
  rewrite eq =
  (Σ′ , (L′ ⊕[ op ] M₀) , ξ-⊕₁ red′) , refl ,
  cong (λ p → proj₁ p , (proj₂ p ⊕[ op ] M₀)) tgt
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red) with step?-complete red
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt with blame? L
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | yes (ℓ , eqL) =
  ⊥-elim (value-not-blame vL eqL)
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL with step? Σ L
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | just (ΣL , L′ , redL) =
  ⊥-elim (value-no-step vL redL)
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | nothing with value? L in eqVal
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | nothing | nothing =
  ⊥-elim (value?-not-none vL eqVal)
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | nothing | just vL′
  with step? Σ M in eqM
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | nothing | just vL′ | nothing =
  ⊥-elim (nothing≢just eq)
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | nothing | just vL′ | just s
  with just-injective eq
step?-complete {Σ = Σ} (ξ-⊕₂ {L = L} {M = M} {op = op} vL red)
  | (Σ′ , M′ , red′) , eq , tgt | no neqL | nothing | just vL′ | just s
  | refl =
  (Σ′ , (L ⊕[ op ] M′) , ξ-⊕₂ vL′ red′) , refl ,
  cong (λ p → proj₁ p , (L ⊕[ op ] proj₂ p)) tgt

step-deterministic :
  ∀ {Σ Σ₁ Σ₂ : Store} {M N₁ N₂ : Term} →
  (red₁ : Σ ∣ M —→ Σ₁ ∣ N₁) →
  (red₂ : Σ ∣ M —→ Σ₂ ∣ N₂) →
  (Σ₁ ≡ Σ₂) × (N₁ ≡ N₂)
step-deterministic red₁ red₂ with step?-complete red₁ | step?-complete red₂
... | s₁ , eq₁ , tgt₁ | s₂ , eq₂ , tgt₂ with just-injective (trans (sym eq₁) eq₂)
... | s₁≡s₂ =
  let tgtEq = trans (sym tgt₁) (trans (cong target s₁≡s₂) tgt₂) in
  cong proj₁ tgtEq , cong proj₂ tgtEq

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

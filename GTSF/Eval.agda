module Eval where

-- File Charter:
--   * Raw fuel-bounded evaluator for Nu GTSF terms.
--   * Decides values and one-step reduction directly from syntax, without
--     invoking progress, preservation, or store-typing proofs.
--   * Returns the complete store-change reduction trace for either a value
--     or blame; returns `nothing` for exhausted fuel or a stuck raw term.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import Primitives

------------------------------------------------------------------------
-- Raw syntactic decisions
------------------------------------------------------------------------

inert? : (c : Coercion) → Maybe (Inert c)
inert? (id A) = nothing
inert? (c ︔ d) = nothing
inert? (c ↦ d) = just (c ↦ d)
inert? (`∀ c) = just (`∀ c)
inert? (G !) = just (G !)
inert? (G ？) = nothing
inert? (seal A α) = just (seal A α)
inert? (unseal α A) = nothing
inert? (gen A c) = just (gen A c)
inert? (inst B c) = nothing

value? : (M : Term) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ M) = just (ƛ M)
value? (L · M) = nothing
value? (Λ M) with value? M
value? (Λ M) | just vM = just (Λ vM)
value? (Λ M) | nothing = nothing
value? (M •) = nothing
value? (ν A L c) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op ] M) = nothing
value? (M ⟨ c ⟩) with value? M | inert? c
value? (M ⟨ c ⟩) | just vM | just ic = just (vM ⟨ ic ⟩)
value? (M ⟨ c ⟩) | just vM | nothing = nothing
value? (M ⟨ c ⟩) | nothing | just ic = nothing
value? (M ⟨ c ⟩) | nothing | nothing = nothing
value? blame = nothing

no•? : (M : Term) → Maybe (No• M)
no•? (` x) = just no•-`
no•? (ƛ M) with no•? M
no•? (ƛ M) | just noM = just (no•-ƛ noM)
no•? (ƛ M) | nothing = nothing
no•? (L · M) with no•? L | no•? M
no•? (L · M) | just noL | just noM = just (no•-· noL noM)
no•? (L · M) | just noL | nothing = nothing
no•? (L · M) | nothing | just noM = nothing
no•? (L · M) | nothing | nothing = nothing
no•? (Λ M) with no•? M
no•? (Λ M) | just noM = just (no•-Λ noM)
no•? (Λ M) | nothing = nothing
no•? (M •) = nothing
no•? (ν A L c) with no•? L
no•? (ν A L c) | just noL = just (no•-ν noL)
no•? (ν A L c) | nothing = nothing
no•? ($ κ) = just no•-$
no•? (L ⊕[ op ] M) with no•? L | no•? M
no•? (L ⊕[ op ] M) | just noL | just noM = just (no•-⊕ noL noM)
no•? (L ⊕[ op ] M) | just noL | nothing = nothing
no•? (L ⊕[ op ] M) | nothing | just noM = nothing
no•? (L ⊕[ op ] M) | nothing | nothing = nothing
no•? (M ⟨ c ⟩) with no•? M
no•? (M ⟨ c ⟩) | just noM = just (no•-⟨⟩ noM)
no•? (M ⟨ c ⟩) | nothing = nothing
no•? blame = just no•-blame

shiftable? : (χ : StoreChange) → (M : Term) → Maybe (Shiftable χ M)
shiftable? keep M = just shift-keep
shiftable? (bind A) M with no•? M
shiftable? (bind A) M | just noM = just (shift-bind noM)
shiftable? (bind A) M | nothing = nothing

------------------------------------------------------------------------
-- Raw one-step evaluator
------------------------------------------------------------------------

Step : Term → Set
Step M = Σ[ χ ∈ StoreChange ] Σ[ N ∈ Term ] (M —→[ χ ] N)

app-redex? :
  ∀ {L M} →
  Value L →
  Value M →
  Maybe (Step (L · M))
app-redex? (ƛ N) vM = just (keep , _ , pure-step (β vM))
app-redex? (Λ vL) vM = nothing
app-redex? ($ κ) vM = nothing
app-redex? (_⟨_⟩ vL (G !)) vM = nothing
app-redex? (_⟨_⟩ vL (seal A α)) vM = nothing
app-redex? (_⟨_⟩ vL (p ↦ q)) vM =
  just (keep , _ , pure-step (β-↦ vL vM))
app-redex? (_⟨_⟩ vL (`∀ c)) vM = nothing
app-redex? (_⟨_⟩ vL (gen A c)) vM = nothing

app-final? :
  ∀ {L} →
  Value L →
  (M : Term) →
  Maybe (Step (L · M))
app-final? vL blame =
  just (keep , blame , pure-step (blame-·₂ vL))
app-final? vL M with value? M
app-final? vL M | just vM = app-redex? vL vM
app-final? vL M | nothing = nothing

prim-left-final? :
  (L M : Term) →
  Maybe (Step (L ⊕[ addℕ ] M))
prim-left-final? blame M =
  just (keep , blame , pure-step blame-⊕₁)
prim-left-final? (` x) M = nothing
prim-left-final? (ƛ N) M = nothing
prim-left-final? (L₁ · L₂) M = nothing
prim-left-final? (Λ N) M = nothing
prim-left-final? (N •) M = nothing
prim-left-final? (ν A N c) M = nothing
prim-left-final? ($ κ) M = nothing
prim-left-final? (L₁ ⊕[ op ] L₂) M = nothing
prim-left-final? (N ⟨ c ⟩) M = nothing

prim-final? :
  ∀ {L} →
  Value L →
  (M : Term) →
  Maybe (Step (L ⊕[ addℕ ] M))
prim-final? vL blame =
  just (keep , blame , pure-step (blame-⊕₂ vL))
prim-final? ($ (κℕ m)) ($ (κℕ n)) =
  just (keep , _ , pure-step δ-⊕)
prim-final? (ƛ N) M = nothing
prim-final? (Λ vL) M = nothing
prim-final? ($ (κℕ m)) (` x) = nothing
prim-final? ($ (κℕ m)) (ƛ N) = nothing
prim-final? ($ (κℕ m)) (L₁ · L₂) = nothing
prim-final? ($ (κℕ m)) (Λ N) = nothing
prim-final? ($ (κℕ m)) (N •) = nothing
prim-final? ($ (κℕ m)) (ν A N c) = nothing
prim-final? ($ (κℕ m)) (L₁ ⊕[ op ] L₂) = nothing
prim-final? ($ (κℕ m)) (N ⟨ c ⟩) = nothing
prim-final? (_⟨_⟩ vL (G !)) M = nothing
prim-final? (_⟨_⟩ vL (seal A α)) M = nothing
prim-final? (_⟨_⟩ vL (p ↦ q)) M = nothing
prim-final? (_⟨_⟩ vL (`∀ c)) M = nothing
prim-final? (_⟨_⟩ vL (gen A c)) M = nothing

type-app-redex? : (M : Term) → Maybe (Step (M •))
type-app-redex? (Λ V) with value? V
type-app-redex? (Λ V) | just vV =
  just (keep , _ , pure-step (β-Λ• vV))
type-app-redex? (Λ V) | nothing = nothing
type-app-redex? (V ⟨ `∀ c ⟩) with value? V
type-app-redex? (V ⟨ `∀ c ⟩) | just vV =
  just (keep , _ , pure-step (β-∀• vV))
type-app-redex? (V ⟨ `∀ c ⟩) | nothing = nothing
type-app-redex? (V ⟨ gen A c ⟩) with value? V
type-app-redex? (V ⟨ gen A c ⟩) | just vV =
  just (keep , _ , pure-step (β-gen• vV))
type-app-redex? (V ⟨ gen A c ⟩) | nothing = nothing
type-app-redex? blame = just (keep , blame , pure-step blame-•)
type-app-redex? (` x) = nothing
type-app-redex? (ƛ N) = nothing
type-app-redex? (L · N) = nothing
type-app-redex? (M •) = nothing
type-app-redex? (ν A L c) = nothing
type-app-redex? ($ κ) = nothing
type-app-redex? (L ⊕[ op ] N) = nothing
type-app-redex? (V ⟨ id A ⟩) = nothing
type-app-redex? (V ⟨ p ︔ q ⟩) = nothing
type-app-redex? (V ⟨ p ↦ q ⟩) = nothing
type-app-redex? (V ⟨ G ! ⟩) = nothing
type-app-redex? (V ⟨ G ？ ⟩) = nothing
type-app-redex? (V ⟨ seal A α ⟩) = nothing
type-app-redex? (V ⟨ unseal α A ⟩) = nothing
type-app-redex? (V ⟨ inst B c ⟩) = nothing

cast-redex? : (M : Term) → (c : Coercion) → Maybe (Step (M ⟨ c ⟩))
cast-redex? blame c = just (keep , blame , pure-step blame-⟨⟩)
cast-redex? (V ⟨ G ! ⟩) (H ？) with value? V | G ≟Ty H
cast-redex? (V ⟨ G ! ⟩) (.G ？) | just vV | yes refl =
  just (keep , V , pure-step (tag-untag-ok vV))
cast-redex? (V ⟨ G ! ⟩) (H ？) | just vV | no G≢H =
  just (keep , blame , pure-step (tag-untag-bad vV G≢H))
cast-redex? (V ⟨ G ! ⟩) (H ？) | nothing | yes G≡H = nothing
cast-redex? (V ⟨ G ! ⟩) (H ？) | nothing | no G≢H = nothing
cast-redex? (V ⟨ seal A α ⟩) (unseal α′ B) with value? V | α ≟ α′
cast-redex? (V ⟨ seal A α ⟩) (unseal .α B) | just vV | yes refl =
  just (keep , V , pure-step (seal-unseal vV))
cast-redex? (V ⟨ seal A α ⟩) (unseal α′ B) | just vV | no α≢α′ =
  nothing
cast-redex? (V ⟨ seal A α ⟩) (unseal α′ B) | nothing | yes α≡α′ =
  nothing
cast-redex? (V ⟨ seal A α ⟩) (unseal α′ B) | nothing | no α≢α′ =
  nothing
cast-redex? M (id A) with value? M
cast-redex? M (id A) | just vM =
  just (keep , M , pure-step (β-id vM))
cast-redex? M (id A) | nothing = nothing
cast-redex? M (p ︔ q) with value? M
cast-redex? M (p ︔ q) | just vM =
  just (keep , _ , pure-step (β-seq vM))
cast-redex? M (p ︔ q) | nothing = nothing
cast-redex? M (inst B c) with value? M
cast-redex? M (inst B c) | just vM =
  just (keep , _ , pure-step (β-inst vM))
cast-redex? M (inst B c) | nothing = nothing
cast-redex? (` x) (p ↦ q) = nothing
cast-redex? (ƛ N) (p ↦ q) = nothing
cast-redex? (L · N) (p ↦ q) = nothing
cast-redex? (Λ N) (p ↦ q) = nothing
cast-redex? (M •) (p ↦ q) = nothing
cast-redex? (ν A L d) (p ↦ q) = nothing
cast-redex? ($ κ) (p ↦ q) = nothing
cast-redex? (L ⊕[ op ] N) (p ↦ q) = nothing
cast-redex? (M ⟨ d ⟩) (p ↦ q) = nothing
cast-redex? M (`∀ c) = nothing
cast-redex? M (G !) = nothing
cast-redex? M (G ？) = nothing
cast-redex? M (seal A α) = nothing
cast-redex? M (unseal α A) = nothing
cast-redex? M (gen A c) = nothing

step? : (M : Term) → Maybe (Step M)
step? (` x) = nothing
step? (ƛ N) = nothing
step? (Λ N) = nothing
step? ($ κ) = nothing
step? blame = nothing
step? (M •) = type-app-redex? M
step? (ν A L c) with step? L
step? (ν A L c) | just (χ , L′ , L→L′) =
  just (χ , _ , ξ-ν L→L′)
step? (ν A L c) | nothing with value? L | no•? L
step? (ν A L c) | nothing | just vL | just noL =
  just (bind A , _ , ν-step vL noL)
step? (ν A L c) | nothing | just vL | nothing = nothing
step? (ν A L c) | nothing | nothing | just noL with L
step? (ν A L c) | nothing | nothing | just noL | blame =
  just (keep , blame , blame-ν)
step? (ν A L c) | nothing | nothing | just noL | ` x = nothing
step? (ν A L c) | nothing | nothing | just noL | ƛ N = nothing
step? (ν A L c) | nothing | nothing | just noL | L₁ · L₂ = nothing
step? (ν A L c) | nothing | nothing | just noL | Λ N = nothing
step? (ν A L c) | nothing | nothing | just noL | N • = nothing
step? (ν A L c) | nothing | nothing | just noL | ν B N d = nothing
step? (ν A L c) | nothing | nothing | just noL | $ κ = nothing
step? (ν A L c) | nothing | nothing | just noL
    | L₁ ⊕[ op ] L₂ = nothing
step? (ν A L c) | nothing | nothing | just noL | N ⟨ d ⟩ = nothing
step? (ν A L c) | nothing | nothing | nothing = nothing
step? (L · M) with step? L
step? (L · M) | just (χ , L′ , L→L′) with shiftable? χ M
step? (L · M) | just (χ , L′ , L→L′) | just shiftM =
  just (χ , _ , ξ-·₁ L→L′ shiftM)
step? (L · M) | just (χ , L′ , L→L′) | nothing = nothing
step? (L · M) | nothing with value? L
step? (L · M) | nothing | nothing with L
step? (L · M) | nothing | nothing | blame =
  just (keep , blame , pure-step blame-·₁)
step? (L · M) | nothing | nothing | ` x = nothing
step? (L · M) | nothing | nothing | ƛ N = nothing
step? (L · M) | nothing | nothing | L₁ · L₂ = nothing
step? (L · M) | nothing | nothing | Λ N = nothing
step? (L · M) | nothing | nothing | N • = nothing
step? (L · M) | nothing | nothing | ν A N c = nothing
step? (L · M) | nothing | nothing | $ κ = nothing
step? (L · M) | nothing | nothing | L₁ ⊕[ op ] L₂ = nothing
step? (L · M) | nothing | nothing | N ⟨ c ⟩ = nothing
step? (L · M) | nothing | just vL with step? M
step? (L · M) | nothing | just vL | just (χ , M′ , M→M′)
    with shiftable? χ L
step? (L · M) | nothing | just vL | just (χ , M′ , M→M′)
    | just shiftL =
  just (χ , _ , ξ-·₂ vL shiftL M→M′)
step? (L · M) | nothing | just vL | just (χ , M′ , M→M′)
    | nothing = nothing
step? (L · M) | nothing | just vL | nothing = app-final? vL M
step? (L ⊕[ addℕ ] M) with step? L
step? (L ⊕[ addℕ ] M) | just (χ , L′ , L→L′) with shiftable? χ M
step? (L ⊕[ addℕ ] M) | just (χ , L′ , L→L′) | just shiftM =
  just (χ , _ , ξ-⊕₁ L→L′ shiftM)
step? (L ⊕[ addℕ ] M) | just (χ , L′ , L→L′) | nothing = nothing
step? (L ⊕[ addℕ ] M) | nothing with value? L
step? (L ⊕[ addℕ ] M) | nothing | nothing = prim-left-final? L M
step? (L ⊕[ addℕ ] M) | nothing | just vL with step? M
step? (L ⊕[ addℕ ] M) | nothing | just vL
    | just (χ , M′ , M→M′) with shiftable? χ L
step? (L ⊕[ addℕ ] M) | nothing | just vL
    | just (χ , M′ , M→M′) | just shiftL =
  just (χ , _ , ξ-⊕₂ vL shiftL M→M′)
step? (L ⊕[ addℕ ] M) | nothing | just vL
    | just (χ , M′ , M→M′) | nothing = nothing
step? (L ⊕[ addℕ ] M) | nothing | just vL | nothing = prim-final? vL M
step? (M ⟨ c ⟩) with step? M
step? (M ⟨ c ⟩) | just (χ , M′ , M→M′) =
  just (χ , _ , ξ-⟨⟩ M→M′)
step? (M ⟨ c ⟩) | nothing = cast-redex? M c

------------------------------------------------------------------------
-- Traced outcomes and fuel-bounded iteration
------------------------------------------------------------------------

record EvalResult (M : Term) : Set where
  constructor result
  field
    changes : StoreChanges
    term    : Term
    trace   : M —↠[ changes ] term
    value   : Value term

open EvalResult public

data EvalOutcome (M : Term) : Set where
  returned : EvalResult M → EvalOutcome M
  blamed :
    (changes : StoreChanges) →
    M —↠[ changes ] blame →
    EvalOutcome M

outcomeChanges : ∀ {M} → EvalOutcome M → StoreChanges
outcomeChanges (returned r) = changes r
outcomeChanges (blamed changes trace) = changes

finalTerm : ∀ {M} → EvalOutcome M → Term
finalTerm (returned r) = term r
finalTerm (blamed changes trace) = blame

outcomeTrace :
  ∀ {M} →
  (r : EvalOutcome M) →
  M —↠[ outcomeChanges r ] finalTerm r
outcomeTrace (returned r) = trace r
outcomeTrace (blamed changes trace) = trace

eval : (gas : ℕ) → (M : Term) → Maybe (EvalOutcome M)
eval zero blame = just (blamed [] ↠-refl)
eval zero M with value? M
eval zero M | just vM =
  just (returned (result [] M ↠-refl vM))
eval zero M | nothing = nothing
eval (suc gas) blame = just (blamed [] ↠-refl)
eval (suc gas) M with value? M
eval (suc gas) M | just vM =
  just (returned (result [] M ↠-refl vM))
eval (suc gas) M | nothing with step? M
eval (suc gas) M | nothing | nothing = nothing
eval (suc gas) M | nothing | just (χ , N , M→N) with eval gas N
eval (suc gas) M | nothing | just (χ , N , M→N) | nothing = nothing
eval (suc gas) M | nothing | just (χ , N , M→N)
    | just (returned (result χs V N↠V vV)) =
  just (returned (result (χ ∷ χs) V (↠-step M→N N↠V) vV))
eval (suc gas) M | nothing | just (χ , N , M→N)
    | just (blamed χs N↠blame) =
  just (blamed (χ ∷ χs) (↠-step M→N N↠blame))

module alt.U26RepEvaluatorSpecProbe where

-- U26 found a genuine disagreement between the bracket-directed U24 lookup
-- specification and its syntax-directed evaluator.  The raw telescope below
-- admitted a big-step bracketing in which the middle begin paired with its
-- later end, while the walk consumed it as the earlier end's re-entry.
--
-- U27 resolves the disagreement by deleting representation lookup evidence.
-- The σ telescope records only the current type-variable-to-anchor map, and `rep?`
-- transports crossing variables by anchor identity.  Consequently the old
-- ambiguous telescope computes `＇zero` without consulting either bracketing.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import Primitives
open import Consistency
open import alt.ThetaTyping

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

nothing-fresh : ∀ {Θ} {α : TyVar Θ}
  → α ∉ᵛ (nothing Vec.∷ Vec.[])
nothing-fresh zero ()

outer : TyEnv 1 1 (just zero Vec.∷ Vec.[])
outer = (∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩

birth-σ : Vec.Vec (Maybe (TyVar 2)) 1
birth-σ = just (suc zero) Vec.∷ Vec.[]

birth : TyEnv 2 1 birth-σ
birth = outer ,:= ＇ zero

outer-tyVar : Vec.lookup birth-σ zero ≡ just (suc zero)
outer-tyVar = refl

after-end : TyEnv 2 0 Vec.[]
after-end = birth ,end[ zero ]

after-inner : TyEnv 2 1 (nothing Vec.∷ Vec.[])
after-inner =
  after-end ,begin[ zero ≔ suc zero ]⟨ empty-fresh ⟩
    ,typ ,end[ suc zero ]

target : TyEnv 2 2
  (just (suc zero) Vec.∷ nothing Vec.∷ Vec.[])
target = after-inner ,begin[ zero ≔ suc zero ]⟨ nothing-fresh ⟩

-- The historical big-step bracketing remains a valid balance certificate;
-- it no longer participates in lookup.
inner-extension : after-end ≼[ 0 , skip empty ] after-inner
inner-extension = ≼-begin-end ≼-refl (≼-typ ≼-refl)

whole-extension : birth ≼[ 0 , keep (skip empty) ] target
whole-extension =
  ≼-end-begin outer-tyVar ≼-refl inner-extension shifted-zero

source-computes : rep? birth zero ≡ just (＇ zero)
source-computes = refl

both-bracketings-compute : rep? target zero ≡ just (＇ zero)
both-bracketings-compute = refl

module proof.Eval where

-- File Charter:
--   * Private, fuel-bounded evaluator for STLCRef configurations.
--   * Implements untyped stepping via `value?` and `step-term` over term+store states.
--   * Exported publicly through the wrapper in `Eval.agda`.

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _,_)

open import STLCRef

Step : Config -> Set
Step c = Σ[ c′ ∈ Config ] (c —→ c′)

StepAt : (M : Term) (μ : Store) -> Set
StepAt M μ = Σ[ c′ ∈ Config ] ((M , μ) —→ c′)

value? : (M : Term) -> Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ N) = just (ƛ A ⇒ N)
value? (L · M) = nothing
value? `zero = just `zero
value? (`suc M) with value? M
value? (`suc M) | just vM = just (`suc vM)
value? (`suc M) | nothing = nothing
value? (case_[zero⇒_|suc⇒_] L M N) = nothing
value? `unit = just `unit
value? (ref M) = nothing
value? (! M) = nothing
value? (L := M) = nothing
value? (`loc l) = just (`loc l)

app-redex? :
  ∀ {L M : Term} {μ : Store} ->
  Value L ->
  Value M ->
  Maybe (StepAt (L · M) μ)
app-redex? (ƛ A ⇒ N) vM = just (_ , β-ƛ vM)
app-redex? `zero vM = nothing
app-redex? (`suc vL) vM = nothing
app-redex? `unit vM = nothing
app-redex? (`loc l) vM = nothing

case-redex? :
  ∀ {L M N : Term} {μ : Store} ->
  Value L ->
  Maybe (StepAt (case_[zero⇒_|suc⇒_] L M N) μ)
case-redex? {M = M} {N = N} `zero = just (_ , β-zero {M = M} {N = N})
case-redex? (`suc vL) = just (_ , β-suc vL)
case-redex? (ƛ A ⇒ N) = nothing
case-redex? `unit = nothing
case-redex? (`loc l) = nothing

deref-redex? :
  ∀ {M : Term} {μ : Store} ->
  Value M ->
  Maybe (StepAt (! M) μ)
deref-redex? {μ = μ} (`loc l) with lookupStore μ l in eq
... | just V = just ((V , μ) , β-! {V = V} eq)
... | nothing = nothing
deref-redex? (ƛ A ⇒ N) = nothing
deref-redex? `zero = nothing
deref-redex? (`suc vM) = nothing
deref-redex? `unit = nothing

assign-redex? :
  ∀ {L M : Term} {μ : Store} ->
  Value L ->
  Value M ->
  Maybe (StepAt (L := M) μ)
assign-redex? {M = M} {μ = μ} (`loc l) vM with updateStore μ l M in eq
... | just μ′ = just ((`unit , μ′) , β-:= {V = M} vM eq)
... | nothing = nothing
assign-redex? (ƛ A ⇒ N) vM = nothing
assign-redex? `zero vM = nothing
assign-redex? (`suc vL) vM = nothing
assign-redex? `unit vM = nothing

step-term : (M : Term) -> (μ : Store) -> Maybe (StepAt M μ)
step-term (` x) μ = nothing
step-term (ƛ A ⇒ N) μ = nothing
step-term `zero μ = nothing

step-term (`suc M) μ with step-term M μ
... | just ((M′ , μ′) , M→M′) = just ((`suc M′ , μ′) , ξ-suc M→M′)
... | nothing = nothing

step-term (L · M) μ with step-term L μ
... | just ((L′ , μ′) , L→L′) = just ((L′ · M , μ′) , ξ-·₁ L→L′)
... | nothing with value? L
...   | nothing = nothing
...   | just vL with step-term M μ
...     | just ((M′ , μ′) , M→M′) = just ((L · M′ , μ′) , ξ-·₂ vL M→M′)
...     | nothing with value? M
...       | nothing = nothing
...       | just vM with app-redex? {μ = μ} vL vM
...         | just s = just s
...         | nothing = nothing

step-term (case_[zero⇒_|suc⇒_] L M N) μ with step-term L μ
... | just ((L′ , μ′) , L→L′) =
  just ((case_[zero⇒_|suc⇒_] L′ M N , μ′) , ξ-case L→L′)
... | nothing with value? L
...   | nothing = nothing
...   | just vL with case-redex? {μ = μ} vL
...     | just s = just s
...     | nothing = nothing

step-term `unit μ = nothing

step-term (ref M) μ with step-term M μ
... | just ((M′ , μ′) , M→M′) = just ((ref M′ , μ′) , ξ-ref M→M′)
... | nothing with value? M
...   | just vM = just ((`loc (length μ) , μ ++ (M ∷ [])) , β-ref vM)
...   | nothing = nothing

step-term (! M) μ with step-term M μ
... | just ((M′ , μ′) , M→M′) = just ((! M′ , μ′) , ξ-! M→M′)
... | nothing with value? M
...   | nothing = nothing
...   | just vM with deref-redex? {μ = μ} vM
...     | just s = just s
...     | nothing = nothing

step-term (L := M) μ with step-term L μ
... | just ((L′ , μ′) , L→L′) = just ((L′ := M , μ′) , ξ-:=₁ L→L′)
... | nothing with value? L
...   | nothing = nothing
...   | just vL with step-term M μ
...     | just ((M′ , μ′) , M→M′) = just ((L := M′ , μ′) , ξ-:=₂ vL M→M′)
...     | nothing with value? M
...       | nothing = nothing
...       | just vM with assign-redex? {μ = μ} vL vM
...         | just s = just s
...         | nothing = nothing

step-term (`loc l) μ = nothing

step? : (c : Config) -> Maybe (Step c)
step? (M , μ) = step-term M μ

eval :
  (gas : ℕ) ->
  (c : Config) ->
  Maybe (∃[ c′ ] (c —↠ c′))
eval zeroℕ c = just (c , (c ∎))
eval (sucℕ gas) (M , μ) with value? M
eval (sucℕ gas) (M , μ) | just v = just ((M , μ) , ((M , μ) ∎))
eval (sucℕ gas) (M , μ) | nothing with step? (M , μ)
eval (sucℕ gas) (M , μ) | nothing | nothing = nothing
eval (sucℕ gas) (M , μ) | nothing | just (c′ , c→c′) with eval gas c′
eval (sucℕ gas) (M , μ) | nothing | just (c′ , c→c′) | nothing = nothing
eval (sucℕ gas) (M , μ) | nothing | just (c′ , c→c′) | just (c″ , c′—↠c″) =
  just (c″ , ((M , μ) —→⟨ c→c′ ⟩ c′—↠c″))

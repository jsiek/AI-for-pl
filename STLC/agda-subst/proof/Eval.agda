module proof.Eval where

-- File Charter:
--   * Private, fuel-bounded evaluator for STLC terms.
--   * Implements untyped stepping via `value?` and `step?`.
--   * Exported publicly through the wrapper in `Eval.agda`.

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _,_)

open import STLC

Step : Term → Set
Step M = Σ[ N ∈ Term ] (M —→ N)

value? : (M : Term) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ N) = just (ƛ A ⇒ N)
value? (L · M) = nothing
value? `zero = just `zero
value? (`suc M) with value? M
value? (`suc M) | just vM = just (`suc vM)
value? (`suc M) | nothing = nothing
value? (case_[zero⇒_|suc⇒_] L M N) = nothing

app-redex? :
  ∀ {L M : Term} →
  Value L →
  Value M →
  Maybe (Step (L · M))
app-redex? (ƛ A ⇒ N) vM = just (_ , β-ƛ vM)
app-redex? `zero vM = nothing
app-redex? (`suc vL) vM = nothing

case-redex? :
  ∀ {L M N : Term} →
  Value L →
  Maybe (Step (case_[zero⇒_|suc⇒_] L M N))
case-redex? {M = M} {N = N} `zero = just (_ , β-zero {M = M} {N = N})
case-redex? (`suc vL) = just (_ , β-suc vL)
case-redex? (ƛ A ⇒ N) = nothing

step? : (M : Term) → Maybe (Step M)
step? (` x) = nothing
step? (ƛ A ⇒ N) = nothing
step? `zero = nothing
step? (`suc M) with step? M
step? (`suc M) | just (M′ , M→M′) = just (`suc M′ , ξ-suc M→M′)
step? (`suc M) | nothing = nothing

step? (L · M) with step? L
step? (L · M) | just (L′ , L→L′) = just (L′ · M , ξ-·₁ L→L′)
step? (L · M) | nothing with value? L
step? (L · M) | nothing | nothing = nothing
step? (L · M) | nothing | just vL with step? M
step? (L · M) | nothing | just vL | just (M′ , M→M′) =
  just (L · M′ , ξ-·₂ (vL , M→M′))
step? (L · M) | nothing | just vL | nothing with value? M
step? (L · M) | nothing | just vL | nothing | nothing = nothing
step? (L · M) | nothing | just vL | nothing | just vM with app-redex? vL vM
step? (L · M) | nothing | just vL | nothing | just vM | just s = just s
step? (L · M) | nothing | just vL | nothing | just vM | nothing = nothing

step? (case_[zero⇒_|suc⇒_] L M N) with step? L
step? (case_[zero⇒_|suc⇒_] L M N) | just (L′ , L→L′) =
  just (case_[zero⇒_|suc⇒_] L′ M N , ξ-case L→L′)
step? (case_[zero⇒_|suc⇒_] L M N) | nothing with value? L
step? (case_[zero⇒_|suc⇒_] L M N) | nothing | nothing = nothing
step? (case_[zero⇒_|suc⇒_] L M N) | nothing | just vL with case-redex? vL
step? (case_[zero⇒_|suc⇒_] L M N) | nothing | just vL | just s = just s
step? (case_[zero⇒_|suc⇒_] L M N) | nothing | just vL | nothing = nothing

eval :
  (gas : ℕ) →
  (M : Term) →
  Maybe (∃[ N ] (M —↠ N))
eval zeroℕ M = just (M , (M ∎))
eval (sucℕ gas) M with value? M
eval (sucℕ gas) M | just v = just (M , (M ∎))
eval (sucℕ gas) M | nothing with step? M
eval (sucℕ gas) M | nothing | nothing = nothing
eval (sucℕ gas) M | nothing | just (N , M→N) with eval gas N
eval (sucℕ gas) M | nothing | just (N , M→N) | nothing = nothing
eval (sucℕ gas) M | nothing | just (N , M→N) | just (K , N—↠K) =
  just (K , (M —→⟨ M→N ⟩ N—↠K))

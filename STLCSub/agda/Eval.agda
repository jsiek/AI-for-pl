module Eval where

-- File Charter:
--   * Executable fuel-bounded evaluator for STLCSub.
--   * Computes by iterating a deterministic one-step function that mirrors the
--     small-step rules in `STLCSub`.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Relation.Nullary using (Dec; yes; no)

open import STLCSub

isValue : Term -> Bool
isValue (` i) = false
isValue (ƛ A ⇒ N) = true
isValue (L · M) = false
isValue `zero = true
isValue (`suc M) = isValue M
isValue (case_[zero⇒_|suc⇒_] L M N) = false
isValue (`record fs) = true
isValue (M ‼ ℓ) = false

lookupField : List FieldTerm -> Label -> Maybe Term
lookupField [] ℓ = nothing
lookupField ((ℓ′ ≔ M) ∷ fs) ℓ with ℓ′ ≟ ℓ
lookupField ((ℓ′ ≔ M) ∷ fs) ℓ | yes _ = just M
lookupField ((ℓ′ ≔ M) ∷ fs) ℓ | no _ = lookupField fs ℓ

step : Term -> Maybe Term
step (` i) = nothing
step (ƛ A ⇒ N) = nothing
step ((ƛ A ⇒ N) · W) with isValue W
step ((ƛ A ⇒ N) · W) | true = just (N [ W ])
step ((ƛ A ⇒ N) · W) | false with step W
step ((ƛ A ⇒ N) · W) | false | just W′ = just ((ƛ A ⇒ N) · W′)
step ((ƛ A ⇒ N) · W) | false | nothing = nothing
step (L · M) with step L
step (L · M) | just L′ = just (L′ · M)
step (L · M) | nothing with isValue L
step (L · M) | nothing | true with step M
step (L · M) | nothing | true | just M′ = just (L · M′)
step (L · M) | nothing | true | nothing = nothing
step (L · M) | nothing | false = nothing
step `zero = nothing
step (`suc M) with step M
step (`suc M) | just M′ = just (`suc M′)
step (`suc M) | nothing = nothing
step (case_[zero⇒_|suc⇒_] L M N) with step L
step (case_[zero⇒_|suc⇒_] L M N) | just L′ =
  just (case_[zero⇒_|suc⇒_] L′ M N)
step (case_[zero⇒_|suc⇒_] L M N) | nothing with L
step (case_[zero⇒_|suc⇒_] L M N) | nothing | `zero = just M
step (case_[zero⇒_|suc⇒_] L M N) | nothing | `suc V with isValue V
step (case_[zero⇒_|suc⇒_] L M N) | nothing | `suc V | true = just (N [ V ])
step (case_[zero⇒_|suc⇒_] L M N) | nothing | `suc V | false = nothing
step (case_[zero⇒_|suc⇒_] L M N) | nothing | ` i = nothing
step (case_[zero⇒_|suc⇒_] L M N) | nothing | ƛ A ⇒ P = nothing
step (case_[zero⇒_|suc⇒_] L M N) | nothing | P · Q = nothing
step (case_[zero⇒_|suc⇒_] L M N) | nothing |
  case_[zero⇒_|suc⇒_] P Q R = nothing
step (case_[zero⇒_|suc⇒_] L M N) | nothing | `record fs = nothing
step (case_[zero⇒_|suc⇒_] L M N) | nothing | P ‼ ℓ = nothing
step (`record fs) = nothing
step ((`record fs) ‼ ℓ) = lookupField fs ℓ
step (M ‼ ℓ) with step M
step (M ‼ ℓ) | just M′ = just (M′ ‼ ℓ)
step (M ‼ ℓ) | nothing = nothing

eval : ℕ -> Term -> Term
eval zero M = M
eval (suc gas) M with step M
eval (suc gas) M | just N = eval gas N
eval (suc gas) M | nothing = M

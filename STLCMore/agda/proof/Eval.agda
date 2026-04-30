module proof.Eval where

-- File Charter:
--   * Private, fuel-bounded evaluator for STLCMore terms.
--   * Implements untyped stepping via `value?` and `step?`.
--   * Exported publicly through the wrapper in `Eval.agda`.

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _,_)

open import STLCMore

Step : Term → Set
Step M = Σ[ N ∈ Term ] (M —→ N)

value? : (M : Term) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ N) = just (ƛ A ⇒ N)
value? (L · M) = nothing
value? (M as A) = nothing
value? (let' M `in N) = nothing
value? `zero = just `zero
value? (`suc M) with value? M
value? (`suc M) | just vM = just (`suc vM)
value? (`suc M) | nothing = nothing
value? (case_[zero⇒_|suc⇒_] L M N) = nothing
value? `unit = just `unit
value? (pair M , N) with value? M | value? N
value? (pair M , N) | just vM | just vN = just (pair vM , vN)
value? (pair M , N) | just vM | nothing = nothing
value? (pair M , N) | nothing | _ = nothing
value? (fst M) = nothing
value? (snd M) = nothing
value? (inl M `to A) with value? M
value? (inl M `to A) | just vM = just (inl_`to_ vM A)
value? (inl M `to A) | nothing = nothing
value? (inr M `to A) with value? M
value? (inr M `to A) | just vM = just (inr_`to_ vM A)
value? (inr M `to A) | nothing = nothing
value? (case⊎_[inl⇒_|inr⇒_] L M N) = nothing

app-redex? :
  ∀ {L M : Term} →
  Value L →
  Value M →
  Maybe (Step (L · M))
app-redex? (ƛ A ⇒ N) vM = just (_ , β-ƛ vM)
app-redex? `zero vM = nothing
app-redex? (`suc vL) vM = nothing
app-redex? `unit vM = nothing
app-redex? (pair vL , vW) vM = nothing
app-redex? (inl_`to_ vL _) vM = nothing
app-redex? (inr_`to_ vL _) vM = nothing

case-redex? :
  ∀ {L M N : Term} →
  Value L →
  Maybe (Step (case_[zero⇒_|suc⇒_] L M N))
case-redex? {M = M} {N = N} `zero = just (_ , β-zero {M = M} {N = N})
case-redex? (`suc vL) = just (_ , β-suc vL)
case-redex? (ƛ A ⇒ N) = nothing
case-redex? `unit = nothing
case-redex? (pair vL , vW) = nothing
case-redex? (inl_`to_ vL _) = nothing
case-redex? (inr_`to_ vL _) = nothing

fst-redex? :
  ∀ {M : Term} →
  Value M →
  Maybe (Step (fst M))
fst-redex? (pair vV , vW) = just (_ , β-fst vV vW)
fst-redex? (ƛ A ⇒ N) = nothing
fst-redex? `zero = nothing
fst-redex? (`suc vM) = nothing
fst-redex? `unit = nothing
fst-redex? (inl_`to_ vM _) = nothing
fst-redex? (inr_`to_ vM _) = nothing

snd-redex? :
  ∀ {M : Term} →
  Value M →
  Maybe (Step (snd M))
snd-redex? (pair vV , vW) = just (_ , β-snd vV vW)
snd-redex? (ƛ A ⇒ N) = nothing
snd-redex? `zero = nothing
snd-redex? (`suc vM) = nothing
snd-redex? `unit = nothing
snd-redex? (inl_`to_ vM _) = nothing
snd-redex? (inr_`to_ vM _) = nothing

case⊎-redex? :
  ∀ {L M N : Term} →
  Value L →
  Maybe (Step (case⊎_[inl⇒_|inr⇒_] L M N))
case⊎-redex? (inl_`to_ vL _) = just (_ , β-inl vL)
case⊎-redex? (inr_`to_ vL _) = just (_ , β-inr vL)
case⊎-redex? (ƛ A ⇒ N) = nothing
case⊎-redex? `zero = nothing
case⊎-redex? (`suc vL) = nothing
case⊎-redex? `unit = nothing
case⊎-redex? (pair vL , vW) = nothing

step? : (M : Term) → Maybe (Step M)
step? (` x) = nothing
step? (ƛ A ⇒ N) = nothing
step? (M as A) with step? M
step? (M as A) | just (M′ , M→M′) = just (M′ as A , ξ-as M→M′)
step? (M as A) | nothing with value? M
step? (M as A) | nothing | nothing = nothing
step? (M as A) | nothing | just vM = just (M , β-as vM)
step? (let' M `in N) with step? M
step? (let' M `in N) | just (M′ , M→M′) = just (let' M′ `in N , ξ-let M→M′)
step? (let' M `in N) | nothing with value? M
step? (let' M `in N) | nothing | nothing = nothing
step? (let' M `in N) | nothing | just vM = just (N [ M ] , β-let vM)
step? `zero = nothing
step? `unit = nothing
step? (`suc M) with step? M
step? (`suc M) | just (M′ , M→M′) = just (`suc M′ , ξ-suc M→M′)
step? (`suc M) | nothing = nothing
step? (pair M , N) with step? M
step? (pair M , N) | just (M′ , M→M′) = just ((pair M′ , N) , ξ-pair₁ M→M′)
step? (pair M , N) | nothing with value? M
step? (pair M , N) | nothing | nothing = nothing
step? (pair M , N) | nothing | just vM with step? N
step? (pair M , N) | nothing | just vM | just (N′ , N→N′) =
  just ((pair M , N′) , ξ-pair₂ (vM , N→N′))
step? (pair M , N) | nothing | just vM | nothing = nothing
step? (fst M) with step? M
step? (fst M) | just (M′ , M→M′) = just (fst M′ , ξ-fst M→M′)
step? (fst M) | nothing with value? M
step? (fst M) | nothing | nothing = nothing
step? (fst M) | nothing | just vM with fst-redex? vM
step? (fst M) | nothing | just vM | just s = just s
step? (fst M) | nothing | just vM | nothing = nothing
step? (snd M) with step? M
step? (snd M) | just (M′ , M→M′) = just (snd M′ , ξ-snd M→M′)
step? (snd M) | nothing with value? M
step? (snd M) | nothing | nothing = nothing
step? (snd M) | nothing | just vM with snd-redex? vM
step? (snd M) | nothing | just vM | just s = just s
step? (snd M) | nothing | just vM | nothing = nothing
step? (inl M `to A) with step? M
step? (inl M `to A) | just (M′ , M→M′) = just (inl M′ `to A , ξ-inl M→M′)
step? (inl M `to A) | nothing = nothing
step? (inr M `to A) with step? M
step? (inr M `to A) | just (M′ , M→M′) = just (inr M′ `to A , ξ-inr M→M′)
step? (inr M `to A) | nothing = nothing

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
step? (case⊎_[inl⇒_|inr⇒_] L M N) with step? L
step? (case⊎_[inl⇒_|inr⇒_] L M N) | just (L′ , L→L′) =
  just (case⊎_[inl⇒_|inr⇒_] L′ M N , ξ-case⊎ L→L′)
step? (case⊎_[inl⇒_|inr⇒_] L M N) | nothing with value? L
step? (case⊎_[inl⇒_|inr⇒_] L M N) | nothing | nothing = nothing
step? (case⊎_[inl⇒_|inr⇒_] L M N) | nothing | just vL with case⊎-redex? vL
step? (case⊎_[inl⇒_|inr⇒_] L M N) | nothing | just vL | just s = just s
step? (case⊎_[inl⇒_|inr⇒_] L M N) | nothing | just vL | nothing = nothing

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

module proof.TypeCheckDec where

-- File Charter:
--   * Private implementation proof of decidable type checking.
--   * Exported through public wrappers in `TypeCheckDec.agda`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym; refl; cong; cong₂; trans; _≡_)
open import Data.Empty using (⊥; ⊥-elim)

open import STLC
open import proof.CoreLemmas
open import proof.TypingLemmas

type-check : (Γ : Ctx) (M : Term) → Dec (∃[ A ] Γ ⊢ M ⦂ A)

type-check Γ (` x)
    with lookup Γ x
... | yes (A , x:A) = yes (A , ⊢` x:A)
... | no nxx = no λ { (B , ⊢` xB) → nxx (B , xB) }

type-check Γ (ƛ A ⇒ N)
    with type-check (A ∷ Γ) N
... | yes (B , NB) = yes ((A ⇒ B) , (⊢ƛ NB))
... | no xx = no λ { (_ , ⊢ƛ NB) → xx (_ , NB)}

type-check Γ (L · M)
    with type-check Γ L | type-check Γ M
... | yes (A , L:A) | yes (B , M:B)
    with A
... | nat = no λ { (C , ⊢· {A = A₁} snd snd₁) →
                 let eq-nat-fun : nat ≡ A₁ ⇒ C
                     eq-nat-fun = typing-unique Γ L nat (A₁ ⇒ C) L:A snd in
                 nat-fun eq-nat-fun}
... | A₁ ⇒ B₁
    with A₁ ≟Ty B
... | yes refl = yes (B₁ , (⊢· L:A M:B))
... | no neq = no λ { (C , ⊢· {A = A′} L:AC M:A) →
                    let eq-fun : A₁ ⇒ B₁ ≡ A′ ⇒ C
                        eq-fun = typing-unique Γ L (A₁ ⇒ B₁) (A′ ⇒ C) L:A L:AC in
                    let eqA : A₁ ≡ A′
                        eqA = fun-inv1 eq-fun in
                    let eqB : A′ ≡ B
                        eqB = typing-unique Γ M A′ B M:A M:B in
                    neq (trans eqA eqB) 
                    }
    
type-check Γ (L · M) | no nL | _ = no λ { (C , ⊢· L:AC MA) → nL (_ , L:AC)}
type-check Γ (L · M) | yes (A , L:A) | no nM = no λ { (C , ⊢· L: M:) → nM (_ , M:)}

type-check Γ `zero = yes (nat , ⊢zero)

type-check Γ (`suc M)
    with type-check Γ M
... | yes (nat , M:A) = yes (nat , (⊢suc M:A))
... | yes (A ⇒ B , M:A) =
      no λ { (nat , ⊢suc M:) →
           let eq-nat-fun = typing-unique _ M _ _ M: M:A in
           nat-fun eq-nat-fun}
... | no nxx = no λ { (nat , ⊢suc M:) → nxx (nat , M:)}

type-check Γ case L [zero⇒ M |suc⇒ N ]
    with type-check Γ L
... | yes (nat , L:nat)
    with type-check Γ M | type-check (nat ∷ Γ) N
... | yes (A , M:A) | yes (B , N:B)
    with A ≟Ty B
... | yes refl = yes (A , ⊢case L:nat M:A N:B)
... | no neq = no λ { (C , ⊢case L:nat′ M:C N:C) →
                let eqA : A ≡ C
                    eqA = typing-unique Γ M A C M:A M:C in
                let eqB : C ≡ B
                    eqB = typing-unique (nat ∷ Γ) N C B N:C N:B in
                neq (trans eqA eqB)
                }
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (nat , L:nat) | yes (A , M:A) | no nN =
  no λ { (C , ⊢case L:nat′ M:C N:C) → nN (C , N:C)}
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (nat , L:nat) | no nM | _ =
  no λ { (C , ⊢case L:nat′ M:C N:C) → nM (C , M:C)}
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (A ⇒ B , L:fun) =
  no λ { (C , ⊢case L:nat _ _) →
       let eq-nat-fun = typing-unique Γ L nat (A ⇒ B) L:nat L:fun in
       nat-fun eq-nat-fun}
type-check Γ case L [zero⇒ M |suc⇒ N ] | no nL =
  no λ { (C , ⊢case L:nat _ _) → nL (nat , L:nat)}

type-check-expect : (Γ : Ctx) (M : Term) (A : Ty) → Dec (Γ ⊢ M ⦂ A)
type-check-expect Γ M A with type-check Γ M
... | yes (B , M:B) with B ≟Ty A
...   | yes refl = yes M:B
...   | no B≢A = no λ M:A → B≢A (typing-unique Γ M B A M:B M:A)
type-check-expect Γ M A | no nM =
  no λ M:A → nM (A , M:A)

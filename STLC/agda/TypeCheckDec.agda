module TypeCheckDec where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym; refl; cong; cong₂; trans; _≡_)
open import Data.Empty using (⊥; ⊥-elim)

open import STLC

type-check : (Γ : Context) (M : Term) → Dec(∃[ A ] HasType Γ M A)

type-check Γ (` x)
    with lookup Γ x
... | yes (A , x:A) = yes (A , tVar x:A)
... | no nxx = no λ { (B , tVar xB) → nxx (B , xB) }

type-check Γ (ƛ A ⇒ N)
    with type-check (A ∷ Γ) N
... | yes (B , NB) = yes ((A ⇒ B) , (tLam NB))
... | no xx = no λ { (_ , tLam NB) → xx (_ , NB)}

type-check Γ (L · M)
    with type-check Γ L | type-check Γ M
... | yes (A , L:A) | yes (B , M:B)
    with A
... | nat = no λ { (C , tApp {A = A₁} snd snd₁) →
                 let eq-nat-fun : nat ≡ A₁ ⇒ C
                     eq-nat-fun = typing-unique Γ L nat (A₁ ⇒ C) L:A snd in
                 nat-fun eq-nat-fun}
... | A₁ ⇒ B₁
    with A₁ ≟Ty B
... | yes refl = yes (B₁ , (tApp L:A M:B))
... | no neq = no λ { (C , tApp {A = A′} L:AC M:A) →
                    let eq-fun : A₁ ⇒ B₁ ≡ A′ ⇒ C
                        eq-fun = typing-unique Γ L (A₁ ⇒ B₁) (A′ ⇒ C) L:A L:AC in
                    let eqA : A₁ ≡ A′
                        eqA = fun-inv1 eq-fun in
                    let eqB : A′ ≡ B
                        eqB = typing-unique Γ M A′ B M:A M:B in
                    neq (trans eqA eqB) 
                    }
    
type-check Γ (L · M) | no nL | _ = no λ { (C , tApp L:AC MA) → nL (_ , L:AC)}
type-check Γ (L · M) | yes (A , L:A) | no nM = no λ { (C , tApp L: M:) → nM (_ , M:)}

type-check Γ `zero = yes (nat , tZero)

type-check Γ (`suc M)
    with type-check Γ M
... | yes (nat , M:A) = yes (nat , (tSuc M:A))
... | yes (A ⇒ B , M:A) =
      no λ { (nat , tSuc M:) →
           let eq-nat-fun = typing-unique _ M _ _ M: M:A in
           nat-fun eq-nat-fun}
... | no nxx = no λ { (nat , tSuc M:) → nxx (nat , M:)}

type-check Γ case L [zero⇒ M |suc⇒ N ]
    with type-check Γ L
... | yes (nat , L:nat)
    with type-check Γ M | type-check (nat ∷ Γ) N
... | yes (A , M:A) | yes (B , N:B)
    with A ≟Ty B
... | yes refl = yes (A , tCase L:nat M:A N:B)
... | no neq = no λ { (C , tCase L:nat′ M:C N:C) →
                let eqA : A ≡ C
                    eqA = typing-unique Γ M A C M:A M:C in
                let eqB : C ≡ B
                    eqB = typing-unique (nat ∷ Γ) N C B N:C N:B in
                neq (trans eqA eqB)
                }
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (nat , L:nat) | yes (A , M:A) | no nN =
  no λ { (C , tCase L:nat′ M:C N:C) → nN (C , N:C)}
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (nat , L:nat) | no nM | _ =
  no λ { (C , tCase L:nat′ M:C N:C) → nM (C , M:C)}
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (A ⇒ B , L:fun) =
  no λ { (C , tCase L:nat _ _) →
       let eq-nat-fun = typing-unique Γ L nat (A ⇒ B) L:nat L:fun in
       nat-fun eq-nat-fun}
type-check Γ case L [zero⇒ M |suc⇒ N ] | no nL =
  no λ { (C , tCase L:nat _ _) → nL (nat , L:nat)}

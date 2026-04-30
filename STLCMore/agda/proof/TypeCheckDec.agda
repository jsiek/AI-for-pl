module proof.TypeCheckDec where

-- File Charter:
--   * Private implementation proof of decidable type checking.
--   * Exported through public wrappers in `TypeCheckDec.agda`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (sym; refl; cong; cong₂; trans; _≡_)
  renaming (subst to substEq)
open import Data.Empty using (⊥; ⊥-elim)

open import STLCMore
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
type-check Γ (L · M) | yes (nat , L:nat) | yes (Barg , M:Barg) =
  no λ { (C , ⊢· {A = A₁} L:fun M:arg) →
       let eq-nat-fun : nat ≡ A₁ ⇒ C
           eq-nat-fun = typing-unique Γ L nat (A₁ ⇒ C) L:nat L:fun in
       nat-fun eq-nat-fun}
type-check Γ (L · M) | yes (unit , L:unit) | yes (Barg , M:Barg) =
  no λ { (C , ⊢· {A = A₁} L:fun M:arg) →
       let eq-unit-fun : unit ≡ A₁ ⇒ C
           eq-unit-fun = typing-unique Γ L unit (A₁ ⇒ C) L:unit L:fun in
       unit-fun eq-unit-fun}
type-check Γ (L · M) | yes (A₁ ⇒ B₁ , L:fun) | yes (Barg , M:Barg)
    with A₁ ≟Ty Barg
type-check Γ (L · M) | yes (A₁ ⇒ B₁ , L:fun) | yes (Barg , M:Barg) | yes refl =
  yes (B₁ , ⊢· L:fun M:Barg)
type-check Γ (L · M) | yes (A₁ ⇒ B₁ , L:fun) | yes (Barg , M:Barg) | no neq =
  no λ { (C , ⊢· {A = A′} L:AC M:A) →
       let eq-fun : A₁ ⇒ B₁ ≡ A′ ⇒ C
           eq-fun = typing-unique Γ L (A₁ ⇒ B₁) (A′ ⇒ C) L:fun L:AC in
       let eqA : A₁ ≡ A′
           eqA = fun-inv1 eq-fun in
       let eqB : A′ ≡ Barg
           eqB = typing-unique Γ M A′ Barg M:A M:Barg in
       neq (trans eqA eqB)}
type-check Γ (L · M) | yes (A₁ `× B₁ , L:prod) | yes (Barg , M:Barg) =
  no λ { (C , ⊢· {A = A′} L:AC M:A′) →
       let eq-prod-fun : A₁ `× B₁ ≡ A′ ⇒ C
           eq-prod-fun = typing-unique Γ L (A₁ `× B₁) (A′ ⇒ C) L:prod L:AC in
       prod-fun eq-prod-fun}
type-check Γ (L · M) | yes (A₁ `+ B₁ , L:sum) | yes (Barg , M:Barg) =
  no λ { (C , ⊢· {A = A′} L:AC M:A′) →
       let eq-sum-fun : A₁ `+ B₁ ≡ A′ ⇒ C
           eq-sum-fun = typing-unique Γ L (A₁ `+ B₁) (A′ ⇒ C) L:sum L:AC in
       sum-fun eq-sum-fun}
type-check Γ (L · M) | no nL | _ = no λ { (C , ⊢· L:AC MA) → nL (_ , L:AC)}
type-check Γ (L · M) | yes (A , L:A) | no nM = no λ { (C , ⊢· L: M:) → nM (_ , M:)}

type-check Γ (M as A)
    with type-check Γ M
... | yes (B , M:B)
    with B ≟Ty A
... | yes refl = yes (A , ⊢as M:B)
... | no B≢A = no λ { (_ , ⊢as M:A) -> B≢A (typing-unique Γ M B A M:B M:A) }
type-check Γ (M as A) | no nM =
  no λ { (_ , ⊢as M:A) -> nM (_ , M:A) }

type-check Γ (let' M `in N)
    with type-check Γ M
... | yes (A , M:A)
    with type-check (A ∷ Γ) N
... | yes (B , N:B) = yes (B , ⊢let M:A N:B)
... | no nN = no λ { (C , ⊢let {A = A′} M:A′ N:C) ->
                nN (C , substEq (λ X -> (X ∷ Γ) ⊢ N ⦂ C)
                              (typing-unique Γ M A′ A M:A′ M:A)
                              N:C) }
type-check Γ (let' M `in N) | no nM =
  no λ { (C , ⊢let M:A N:C) -> nM (_ , M:A) }

type-check Γ `zero = yes (nat , ⊢zero)
type-check Γ `unit = yes (unit , ⊢unit)

type-check Γ (`suc M)
    with type-check Γ M
... | yes (nat , M:A) = yes (nat , (⊢suc M:A))
... | yes (unit , M:A) =
      no λ { (nat , ⊢suc M:) →
           let eq-nat-unit = typing-unique _ M _ _ M: M:A in
           nat-unit eq-nat-unit}
... | yes (A ⇒ B , M:A) =
      no λ { (nat , ⊢suc M:) →
           let eq-nat-fun = typing-unique _ M _ _ M: M:A in
           nat-fun eq-nat-fun}
... | yes (A `× B , M:A) =
      no λ { (nat , ⊢suc M:) →
           let eq-nat-prod = typing-unique _ M _ _ M: M:A in
           nat-prod eq-nat-prod}
... | yes (A `+ B , M:A) =
      no λ { (nat , ⊢suc M:) →
           let eq-nat-sum = typing-unique _ M _ _ M: M:A in
           nat-sum eq-nat-sum}
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
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (unit , L:unit) =
  no λ { (C , ⊢case L:nat _ _) →
       let eq-nat-unit = typing-unique Γ L nat unit L:nat L:unit in
       nat-unit eq-nat-unit}
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (A `× B , L:prod) =
  no λ { (C , ⊢case L:nat _ _) →
       let eq-nat-prod = typing-unique Γ L nat (A `× B) L:nat L:prod in
       nat-prod eq-nat-prod}
type-check Γ case L [zero⇒ M |suc⇒ N ] | yes (A `+ B , L:sum) =
  no λ { (C , ⊢case L:nat _ _) →
       let eq-nat-sum = typing-unique Γ L nat (A `+ B) L:nat L:sum in
       nat-sum eq-nat-sum}
type-check Γ case L [zero⇒ M |suc⇒ N ] | no nL =
  no λ { (C , ⊢case L:nat _ _) → nL (nat , L:nat)}

type-check Γ (pair M , N)
    with type-check Γ M | type-check Γ N
... | yes (A , M:A) | yes (B , N:B) = yes (A `× B , ⊢pair M:A N:B)
type-check Γ (pair M , N) | no nM | _ =
  no λ { (C , ⊢pair M:C N:D) → nM (_ , M:C) }
type-check Γ (pair M , N) | yes (A , M:A) | no nN =
  no λ { (C , ⊢pair M:C N:D) → nN (_ , N:D) }

type-check Γ (fst M)
    with type-check Γ M
... | yes (A `× B , M:AB) = yes (A , ⊢fst M:AB)
... | yes (nat , M:nat) =
      no λ { (C , ⊢fst {A = A′} {B = B′} M:AB) →
           let eq-nat-prod = typing-unique Γ M nat (A′ `× B′) M:nat M:AB in
           nat-prod eq-nat-prod }
... | yes (unit , M:unit) =
      no λ { (C , ⊢fst {A = A′} {B = B′} M:AB) →
           let eq-unit-prod = typing-unique Γ M unit (A′ `× B′) M:unit M:AB in
           unit-prod eq-unit-prod }
... | yes (A ⇒ B , M:fun) =
      no λ { (C , ⊢fst {A = A′} {B = B′} M:AB) →
           let eq-fun-prod = typing-unique Γ M (A ⇒ B) (A′ `× B′) M:fun M:AB in
           fun-prod eq-fun-prod }
... | yes (A `+ B , M:sum) =
      no λ { (C , ⊢fst {A = A′} {B = B′} M:AB) →
           let eq-sum-prod = typing-unique Γ M (A `+ B) (A′ `× B′) M:sum M:AB in
           sum-prod eq-sum-prod }
... | no nM = no λ { (C , ⊢fst M:AB) → nM (_ , M:AB) }

type-check Γ (snd M)
    with type-check Γ M
... | yes (A `× B , M:AB) = yes (B , ⊢snd M:AB)
... | yes (nat , M:nat) =
      no λ { (C , ⊢snd {A = A′} {B = B′} M:AB) →
           let eq-nat-prod = typing-unique Γ M nat (A′ `× B′) M:nat M:AB in
           nat-prod eq-nat-prod }
... | yes (unit , M:unit) =
      no λ { (C , ⊢snd {A = A′} {B = B′} M:AB) →
           let eq-unit-prod = typing-unique Γ M unit (A′ `× B′) M:unit M:AB in
           unit-prod eq-unit-prod }
... | yes (A ⇒ B , M:fun) =
      no λ { (C , ⊢snd {A = A′} {B = B′} M:AB) →
           let eq-fun-prod = typing-unique Γ M (A ⇒ B) (A′ `× B′) M:fun M:AB in
           fun-prod eq-fun-prod }
... | yes (A `+ B , M:sum) =
      no λ { (C , ⊢snd {A = A′} {B = B′} M:AB) →
           let eq-sum-prod = typing-unique Γ M (A `+ B) (A′ `× B′) M:sum M:AB in
           sum-prod eq-sum-prod }
... | no nM = no λ { (C , ⊢snd M:AB) → nM (_ , M:AB) }

type-check Γ (inl M `to nat) = no λ { (_ , ()) }
type-check Γ (inl M `to unit) = no λ { (_ , ()) }
type-check Γ (inl M `to (A ⇒ B)) = no λ { (_ , ()) }
type-check Γ (inl M `to (A `× B)) = no λ { (_ , ()) }
type-check Γ (inl M `to (A `+ B))
    with type-check Γ M
... | yes (C , M:C)
    with C ≟Ty A
... | yes refl = yes (A `+ B , ⊢inl M:C)
... | no C≢A = no λ { (_ , ⊢inl M:A) -> C≢A (typing-unique Γ M C A M:C M:A) }
type-check Γ (inl M `to (A `+ B)) | no nM =
  no λ { (_ , ⊢inl M:A) -> nM (_ , M:A) }

type-check Γ (inr M `to nat) = no λ { (_ , ()) }
type-check Γ (inr M `to unit) = no λ { (_ , ()) }
type-check Γ (inr M `to (A ⇒ B)) = no λ { (_ , ()) }
type-check Γ (inr M `to (A `× B)) = no λ { (_ , ()) }
type-check Γ (inr M `to (A `+ B))
    with type-check Γ M
... | yes (C , M:C)
    with C ≟Ty B
... | yes refl = yes (A `+ B , ⊢inr M:C)
... | no C≢B = no λ { (_ , ⊢inr M:B) -> C≢B (typing-unique Γ M C B M:C M:B) }
type-check Γ (inr M `to (A `+ B)) | no nM =
  no λ { (_ , ⊢inr M:B) -> nM (_ , M:B) }

type-check Γ case⊎ L [inl⇒ M |inr⇒ N ]
    with type-check Γ L
... | yes (A `+ B , L:AB)
    with type-check (A ∷ Γ) M | type-check (B ∷ Γ) N
... | yes (C , M:C) | yes (D , N:D)
    with C ≟Ty D
... | yes refl = yes (C , ⊢case⊎ L:AB M:C N:D)
... | no neq = no λ { (E , ⊢case⊎ {A = A₁} {B = B₁} L:AB′ M:E N:E) →
                let eqAB : A `+ B ≡ A₁ `+ B₁
                    eqAB = typing-unique Γ L (A `+ B) (A₁ `+ B₁) L:AB L:AB′ in
                let eqA : A ≡ A₁
                    eqA = sum-inv1 eqAB in
                let eqB : B ≡ B₁
                    eqB = sum-inv2 eqAB in
                let M:E′ : (A ∷ Γ) ⊢ M ⦂ E
                    M:E′ = substEq (λ X -> (X ∷ Γ) ⊢ M ⦂ E) (sym eqA) M:E in
                let N:E′ : (B ∷ Γ) ⊢ N ⦂ E
                    N:E′ = substEq (λ X -> (X ∷ Γ) ⊢ N ⦂ E) (sym eqB) N:E in
                let eqC : C ≡ E
                    eqC = typing-unique (A ∷ Γ) M C E M:C M:E′ in
                let eqD : E ≡ D
                    eqD = typing-unique (B ∷ Γ) N E D N:E′ N:D in
                neq (trans eqC eqD)
                }
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | yes (A `+ B , L:AB) | yes (C , M:C) | no nN =
  no λ { (E , ⊢case⊎ {A = A₁} {B = B₁} L:AB′ M:E N:E) →
       let eqAB : A `+ B ≡ A₁ `+ B₁
           eqAB = typing-unique Γ L (A `+ B) (A₁ `+ B₁) L:AB L:AB′ in
       let eqB : B ≡ B₁
           eqB = sum-inv2 eqAB in
       nN (E , substEq (λ X -> (X ∷ Γ) ⊢ N ⦂ E) (sym eqB) N:E)}
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | yes (A `+ B , L:AB) | no nM | _ =
  no λ { (E , ⊢case⊎ {A = A₁} {B = B₁} L:AB′ M:E N:E) →
       let eqAB : A `+ B ≡ A₁ `+ B₁
           eqAB = typing-unique Γ L (A `+ B) (A₁ `+ B₁) L:AB L:AB′ in
       let eqA : A ≡ A₁
           eqA = sum-inv1 eqAB in
       nM (E , substEq (λ X -> (X ∷ Γ) ⊢ M ⦂ E) (sym eqA) M:E)}
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | yes (nat , L:nat) =
  no λ { (C , ⊢case⊎ L:AB _ _) →
       let eq-nat-sum = typing-unique Γ L nat _ L:nat L:AB in
       nat-sum eq-nat-sum}
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | yes (unit , L:unit) =
  no λ { (C , ⊢case⊎ L:AB _ _) →
       let eq-unit-sum = typing-unique Γ L unit _ L:unit L:AB in
       unit-sum eq-unit-sum}
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | yes (A ⇒ B , L:fun) =
  no λ { (C , ⊢case⊎ L:AB _ _) →
       let eq-fun-sum = typing-unique Γ L (A ⇒ B) _ L:fun L:AB in
       fun-sum eq-fun-sum}
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | yes (A `× B , L:prod) =
  no λ { (C , ⊢case⊎ L:AB _ _) →
       let eq-prod-sum = typing-unique Γ L (A `× B) _ L:prod L:AB in
       prod-sum eq-prod-sum}
type-check Γ case⊎ L [inl⇒ M |inr⇒ N ] | no nL =
  no λ { (C , ⊢case⊎ L:AB _ _) → nL (_ , L:AB)}

type-check-expect : (Γ : Ctx) (M : Term) (A : Ty) → Dec (Γ ⊢ M ⦂ A)
type-check-expect Γ M A with type-check Γ M
... | yes (B , M:B) with B ≟Ty A
...   | yes refl = yes M:B
...   | no B≢A = no λ M:A → B≢A (typing-unique Γ M B A M:B M:A)
type-check-expect Γ M A | no nM =
  no λ M:A → nM (A , M:A)

module strong-rep-nu.Source where

-- File Charter:
--   * THE SOURCE LANGUAGE: plain System F with the standard type
--     application `L [ A ]`, which strong-rep-nu.Compile elaborates
--     into the run-time language's `ν`.  §1 syntax, §2 type formation
--     over a COUNT of type variables, §3 values, §4 the typing
--     judgement, §5 a checker that builds typing derivations.
--   * NO BOUNDARIES, NO REPRESENTATIONS, NO REDUCTION.  The source
--     shares `Ty` and `Ctx` with the run-time language and nothing else.
--   * THE VALUE RESTRICTION, as in the run-time `⊢Λ`: a type
--     abstraction's body is a (source) value.

open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; s≤s; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
open import strong-rep-nu.Terms using (Var; Ctx; _∋_⦂_; here; there; ⤊)

------------------------------------------------------------------------
-- 1.  Syntax
------------------------------------------------------------------------

infix  9 `_
infix  9 $_
infixl 7 _·_
infixl 7 _[_]
infix  6 ƛ_∙_

data STerm : Set where
  `_     : Var → STerm
  $_     : ℕ → STerm
  `true  : STerm
  `false : STerm
  ƛ_∙_   : Ty → STerm → STerm
  _·_    : STerm → STerm → STerm
  Λ_     : STerm → STerm
  _[_]   : STerm → Ty → STerm

------------------------------------------------------------------------
-- 2.  Type formation: `n ⊢ˢ A` — A's free variables are below n
------------------------------------------------------------------------

infix 4 _⊢ˢ_
data _⊢ˢ_ (n : ℕ) : Ty → Set where
  swf-var : ∀ {X} → X < n → n ⊢ˢ ` X
  swf-ℕ   : n ⊢ˢ `ℕ
  swf-𝔹   : n ⊢ˢ `𝔹
  swf-⇒   : ∀ {A B} → n ⊢ˢ A → n ⊢ˢ B → n ⊢ˢ A ⇒ B
  swf-∀   : ∀ {A} → suc n ⊢ˢ A → n ⊢ˢ `∀ A

------------------------------------------------------------------------
-- 3.  Values
------------------------------------------------------------------------

data SValue : STerm → Set where
  SV-$     : ∀ {n} → SValue ($ n)
  SV-true  : SValue `true
  SV-false : SValue `false
  SV-ƛ     : ∀ {A N} → SValue (ƛ A ∙ N)
  SV-Λ     : ∀ {N} → SValue N → SValue (Λ N)

------------------------------------------------------------------------
-- 4.  Typing
------------------------------------------------------------------------

infix 3 _∣_⊢ˢ_⦂_
data _∣_⊢ˢ_⦂_ : ℕ → Ctx → STerm → Ty → Set where

  ⊢ˢ` : ∀ {n Γ x A} → Γ ∋ x ⦂ A → n ∣ Γ ⊢ˢ ` x ⦂ A

  ⊢ˢ$ : ∀ {n Γ k} → n ∣ Γ ⊢ˢ $ k ⦂ `ℕ

  ⊢ˢtrue : ∀ {n Γ} → n ∣ Γ ⊢ˢ `true ⦂ `𝔹

  ⊢ˢfalse : ∀ {n Γ} → n ∣ Γ ⊢ˢ `false ⦂ `𝔹

  ⊢ˢƛ : ∀ {n Γ A B N} → n ⊢ˢ A → n ∣ A ∷ Γ ⊢ˢ N ⦂ B
      → n ∣ Γ ⊢ˢ ƛ A ∙ N ⦂ (A ⇒ B)

  ⊢ˢ· : ∀ {n Γ A B L M}
      → n ∣ Γ ⊢ˢ L ⦂ (A ⇒ B)
      → n ∣ Γ ⊢ˢ M ⦂ A
      → n ∣ Γ ⊢ˢ L · M ⦂ B

  ⊢ˢΛ : ∀ {n Γ C N} → SValue N → suc n ∣ ⤊ Γ ⊢ˢ N ⦂ C
      → n ∣ Γ ⊢ˢ Λ N ⦂ `∀ C

  -- THE STANDARD TYPE APPLICATION: no annotation beyond the argument.
  ⊢ˢ[] : ∀ {n Γ A C L} → n ∣ Γ ⊢ˢ L ⦂ `∀ C → n ⊢ˢ A
       → n ∣ Γ ⊢ˢ L [ A ] ⦂ C [ A ]ᵗ

------------------------------------------------------------------------
-- 5.  A checker that builds derivations (for the examples)
------------------------------------------------------------------------

svalue? : (M : STerm) → Maybe (SValue M)
svalue? (` x)     = nothing
svalue? ($ k)     = just SV-$
svalue? `true     = just SV-true
svalue? `false    = just SV-false
svalue? (ƛ A ∙ N) = just SV-ƛ
svalue? (L · M)   = nothing
svalue? (Λ N) with svalue? N
svalue? (Λ N) | just v  = just (SV-Λ v)
svalue? (Λ N) | nothing = nothing
svalue? (L [ A ]) = nothing

lt? : (X n : ℕ) → Maybe (X < n)
lt? X       zero    = nothing
lt? zero    (suc n) = just (s≤s z≤n)
lt? (suc X) (suc n) with lt? X n
lt? (suc X) (suc n) | just p  = just (s≤s p)
lt? (suc X) (suc n) | nothing = nothing

swf? : (n : ℕ) (A : Ty) → Maybe (n ⊢ˢ A)
swf? n (` X) with lt? X n
swf? n (` X) | just p  = just (swf-var p)
swf? n (` X) | nothing = nothing
swf? n `ℕ = just swf-ℕ
swf? n `𝔹 = just swf-𝔹
swf? n (A ⇒ B) with swf? n A
swf? n (A ⇒ B) | nothing = nothing
swf? n (A ⇒ B) | just wA with swf? n B
swf? n (A ⇒ B) | just wA | nothing = nothing
swf? n (A ⇒ B) | just wA | just wB = just (swf-⇒ wA wB)
swf? n (`∀ A) with swf? (suc n) A
swf? n (`∀ A) | just w  = just (swf-∀ w)
swf? n (`∀ A) | nothing = nothing

lookupˢ? : (Γ : Ctx) (x : Var) → Maybe (∃[ A ] Γ ∋ x ⦂ A)
lookupˢ? []      x       = nothing
lookupˢ? (A ∷ Γ) zero    = just (A , here)
lookupˢ? (A ∷ Γ) (suc x) with lookupˢ? Γ x
lookupˢ? (A ∷ Γ) (suc x) | just (B , d) = just (B , there d)
lookupˢ? (A ∷ Γ) (suc x) | nothing      = nothing

tyEq? : (A B : Ty) → Maybe (A ≡ B)
tyEq? (` X) (` Y) with X ≟ Y
tyEq? (` X) (` Y) | yes refl = just refl
tyEq? (` X) (` Y) | no _     = nothing
tyEq? `ℕ `ℕ = just refl
tyEq? `𝔹 `𝔹 = just refl
tyEq? (A ⇒ B) (A′ ⇒ B′) with tyEq? A A′
tyEq? (A ⇒ B) (A′ ⇒ B′) | nothing = nothing
tyEq? (A ⇒ B) (A′ ⇒ B′) | just refl with tyEq? B B′
tyEq? (A ⇒ B) (A′ ⇒ B′) | just refl | just refl = just refl
tyEq? (A ⇒ B) (A′ ⇒ B′) | just refl | nothing   = nothing
tyEq? (`∀ A) (`∀ A′) with tyEq? A A′
tyEq? (`∀ A) (`∀ A′) | just refl = just refl
tyEq? (`∀ A) (`∀ A′) | nothing   = nothing
tyEq? _ _ = nothing

inferˢ : (n : ℕ) (Γ : Ctx) (M : STerm)
  → Maybe (∃[ A ] (n ∣ Γ ⊢ˢ M ⦂ A))
inferˢ n Γ (` x) with lookupˢ? Γ x
inferˢ n Γ (` x) | just (A , d) = just (A , ⊢ˢ` d)
inferˢ n Γ (` x) | nothing      = nothing
inferˢ n Γ ($ k)  = just (`ℕ , ⊢ˢ$)
inferˢ n Γ `true  = just (`𝔹 , ⊢ˢtrue)
inferˢ n Γ `false = just (`𝔹 , ⊢ˢfalse)
inferˢ n Γ (ƛ A ∙ N) with swf? n A
inferˢ n Γ (ƛ A ∙ N) | nothing = nothing
inferˢ n Γ (ƛ A ∙ N) | just wA with inferˢ n (A ∷ Γ) N
inferˢ n Γ (ƛ A ∙ N) | just wA | just (B , dN) =
  just (A ⇒ B , ⊢ˢƛ wA dN)
inferˢ n Γ (ƛ A ∙ N) | just wA | nothing = nothing
inferˢ n Γ (L · M) with inferˢ n Γ L
inferˢ n Γ (L · M) | just (A ⇒ B , dL) with inferˢ n Γ M
inferˢ n Γ (L · M) | just (A ⇒ B , dL) | just (A′ , dM)
  with tyEq? A′ A
inferˢ n Γ (L · M) | just (A ⇒ B , dL) | just (A′ , dM)
  | just refl = just (B , ⊢ˢ· dL dM)
inferˢ n Γ (L · M) | just (A ⇒ B , dL) | just (A′ , dM)
  | nothing = nothing
inferˢ n Γ (L · M) | just (A ⇒ B , dL) | nothing = nothing
inferˢ n Γ (L · M) | just (_ , dL) = nothing
inferˢ n Γ (L · M) | nothing = nothing
inferˢ n Γ (Λ N) with svalue? N
inferˢ n Γ (Λ N) | nothing = nothing
inferˢ n Γ (Λ N) | just v with inferˢ (suc n) (⤊ Γ) N
inferˢ n Γ (Λ N) | just v | just (C , dN) = just (`∀ C , ⊢ˢΛ v dN)
inferˢ n Γ (Λ N) | just v | nothing = nothing
inferˢ n Γ (L [ A ]) with swf? n A
inferˢ n Γ (L [ A ]) | nothing = nothing
inferˢ n Γ (L [ A ]) | just wA with inferˢ n Γ L
inferˢ n Γ (L [ A ]) | just wA | just (`∀ C , dL) =
  just (C [ A ]ᵗ , ⊢ˢ[] dL wA)
inferˢ n Γ (L [ A ]) | just wA | just (_ , dL) = nothing
inferˢ n Γ (L [ A ]) | just wA | nothing = nothing

module Eval where

-- File Charter:
--   * Executable evaluator for the full PolyNuBar barrier calculus.
--   * Follows the evaluation-context order of `interp-nu/reduce.ss`.
--   * Provides fuelled `eval` for regression examples; it distinguishes
--     successful termination, stuck terms, and gas exhaustion where another
--     step is still available.  The declarative reduction rules remain in
--     `Reduction`.

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Relation.Nullary using (yes; no)
open import Reduction public
open import TypeCheck using (inferClosed; checkInAs)

------------------------------------------------------------------------
-- Boolean helpers
------------------------------------------------------------------------

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

natEq : ℕ → ℕ → Bool
natEq m n with m ≟ n
natEq m n | yes _ = true
natEq m n | no _ = false

baseEq : Base → Base → Bool
baseEq 𝕀 𝕀 = true
baseEq 𝔹 𝔹 = true
baseEq _ _ = false

labelEq : Label → Label → Bool
labelEq - - = true
labelEq (ℓ m) (ℓ n) = natEq m n
labelEq (bar p) (bar q) = labelEq p q
labelEq _ _ = false

binderEq : Binder → Binder → Bool
binderEq (bind X) (bind Y) = natEq X Y
binderEq (unbind X) (unbind Y) = natEq X Y
binderEq _ _ = false

popBind : Binder → Maybe Binder
popBind (bind zero) = nothing
popBind (bind (suc X)) = nothing
popBind (unbind zero) = nothing
popBind (unbind (suc X)) = just (unbind X)

tyEq : Ty → Ty → Bool
tyEq (` X) (` Y) = natEq X Y
tyEq (`ι ι) (`ι κ) = baseEq ι κ
tyEq ★ ★ = true
tyEq (A ⇒ B) (C ⇒ D) = tyEq A C && tyEq B D
tyEq (A `× B) (C `× D) = tyEq A C && tyEq B D
tyEq (`∀ A) (`∀ B) = tyEq A B
tyEq _ _ = false

mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe g (just x) = just (g x)
mapMaybe g nothing = nothing

maybe2 : {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
maybe2 g (just x) (just y) = just (g x y)
maybe2 g _ _ = nothing

maybe3 :
  {A B C D : Set} →
  (A → B → C → D) → Maybe A → Maybe B → Maybe C → Maybe D
maybe3 g (just x) (just y) (just z) = just (g x y z)
maybe3 g _ _ _ = nothing

downVarAt : ℕ → Var → Maybe Var
downVarAt zero zero = nothing
downVarAt zero (suc X) = just X
downVarAt (suc k) zero = just zero
downVarAt (suc k) (suc X) = mapMaybe suc (downVarAt k X)

downTyAt : ℕ → Ty → Maybe Ty
downTyAt k (` X) = mapMaybe (λ X′ → ` X′) (downVarAt k X)
downTyAt k (`ι ι) = just (`ι ι)
downTyAt k ★ = just ★
downTyAt k (A ⇒ B) = maybe2 _⇒_ (downTyAt k A) (downTyAt k B)
downTyAt k (A `× B) = maybe2 _`×_ (downTyAt k A) (downTyAt k B)
downTyAt k (`∀ A) = mapMaybe `∀_ (downTyAt (suc k) A)

downTermAt : ℕ → Term → Maybe Term
downTermAt k (` x) = just (` x)
downTermAt k ($ c) = just ($ c)
downTermAt k (ƛ[ A ] M) =
  maybe2 (λ A′ M′ → ƛ[ A′ ] M′) (downTyAt k A) (downTermAt k M)
downTermAt k (L · M) = maybe2 _·_ (downTermAt k L) (downTermAt k M)
downTermAt k (letin L M) =
  maybe2 (λ L′ M′ → letin L′ M′) (downTermAt k L) (downTermAt k M)
downTermAt k (Λ[ p ] M :: A) =
  maybe2 (λ M′ A′ → Λ[ p ] M′ :: A′)
    (downTermAt (suc k) M) (downTyAt (suc k) A)
downTermAt k (M • A) =
  maybe2 _•_ (downTermAt k M) (downTyAt k A)
downTermAt k (ν[ A ] p ∙ M) =
  maybe2 (λ A′ M′ → ν[ A′ ] p ∙ M′)
    (downTyAt k A) (downTermAt k M)
downTermAt k (M ⦂ A ⇒[ p ] B) =
  maybe3 (λ M′ A′ B′ → M′ ⦂ A′ ⇒[ p ] B′)
    (downTermAt k M) (downTyAt k A) (downTyAt k B)
downTermAt k (M ⦂ A ⇒⟨ bind X ⟩ B) =
  maybe3 (λ M′ A′ B′ → M′ ⦂ A′ ⇒⟨ bind X ⟩ B′)
    (downTermAt (suc k) M) (downTyAt (suc k) A) (downTyAt k B)
downTermAt k (M ⦂ A ⇒⟨ unbind X ⟩ B) =
  maybe3 (λ M′ A′ B′ → M′ ⦂ A′ ⇒⟨ unbind X ⟩ B′)
    (downTermAt k M) (downTyAt k A) (downTyAt k B)
downTermAt k (is p M G) =
  maybe2 (λ M′ G′ → is p M′ G′) (downTermAt k M) (downTyAt k G)
downTermAt k (pair L M) =
  maybe2 pair (downTermAt k L) (downTermAt k M)
downTermAt k (fst M) = mapMaybe fst (downTermAt k M)
downTermAt k (snd M) = mapMaybe snd (downTermAt k M)
downTermAt k (ifte L M N) =
  maybe3 ifte (downTermAt k L) (downTermAt k M) (downTermAt k N)
downTermAt k (prim op M) = mapMaybe (prim op) (downTermAt k M)
downTermAt k (blame p) = just (blame p)

------------------------------------------------------------------------
-- Dynamic type predicates
------------------------------------------------------------------------

ground : Ty → Maybe Ty
ground (` X) = just (` X)
ground (`ι ι) = just (`ι ι)
ground ★ = nothing
ground (A ⇒ B) = just (★ ⇒ ★)
ground (A `× B) = just (★ `× ★)
ground (`∀ A) = nothing

ground? : Ty → Bool
ground? A with ground A
ground? A | just G = true
ground? A | nothing = false

groundTag? : Ty → Bool
groundTag? (`ι ι) = true
groundTag? (★ ⇒ ★) = true
groundTag? _ = false

consistentFuel : ℕ → Ty → Ty → Bool
consistentFuel zero A B = false
consistentFuel (suc n) (`ι ι) (`ι κ) = baseEq ι κ
consistentFuel (suc n) ★ B = true
consistentFuel (suc n) A ★ = true
consistentFuel (suc n) (` X) (` Y) = natEq X Y
consistentFuel (suc n) (A ⇒ B) (C ⇒ D) =
  consistentFuel n A C && consistentFuel n B D
consistentFuel (suc n) (A `× B) (C `× D) =
  consistentFuel n A C && consistentFuel n B D
consistentFuel (suc n) (`∀ A) B = consistentFuel n (A [ ★ ]ᵗ) B
consistentFuel (suc n) A (`∀ B) = consistentFuel n A (B [ ★ ]ᵗ)
consistentFuel (suc n) _ _ = false

consistent? : Ty → Ty → Bool
consistent? = consistentFuel 64

------------------------------------------------------------------------
-- Values and context plugging
------------------------------------------------------------------------

value? : Term → Bool
value? (` x) = false
value? ($ c) = true
value? (ƛ[ A ] M) = true
value? (L · M) = false
value? (letin L M) = false
value? (Λ[ p ] M :: A) = value? M
value? (M • A) = false
value? (ν[ A ] p ∙ M) = false
value? (V ⦂ G ⇒[ - ] ★) = value? V && ground? G
value? (V ⦂ A ⇒[ p ] B) = false
value? (V ⦂ A ⇒⟨ unbind X ⟩ (` zero)) = value? V
value? (V ⦂ A ⇒⟨ P ⟩ B) = false
value? (is p M G) = false
value? (pair L M) = value? L && value? M
value? (fst M) = false
value? (snd M) = false
value? (ifte L M N) = false
value? (prim op M) = false
value? (blame p) = false

final? : Term → Bool
final? (blame p) = true
final? M = value? M

plug : (Term → Term) → Term → Term
plug C (blame p) = blame p
plug C M = C M

mapStep : (Term → Term) → Maybe Term → Maybe Term
mapStep C nothing = nothing
mapStep C (just M) = just (plug C M)

------------------------------------------------------------------------
-- Evaluation results
------------------------------------------------------------------------

data EvalResult : Set where
  done       : Term → EvalResult
  stuck      : EvalResult
  out-of-gas : Term → EvalResult
  type-error : Term → EvalResult

------------------------------------------------------------------------
-- Redex contraction
------------------------------------------------------------------------

castStep : Term → Ty → Label → Ty → Maybe Term
castStep V A p (`∀ B) =
  just (Λ[ p ] ((renameᵀ suc V) ⦂ ⇑ᵗ A ⇒[ p ] B) :: B)
castStep V (`∀ A) p B = just (V • ★ ⦂ A [ ★ ]ᵗ ⇒[ p ] B)
castStep (ƛ[ C ] M) (A₁ ⇒ B₁) p (A₂ ⇒ B₂) =
  just
    (ƛ[ A₂ ]
      ((rename suc (ƛ[ C ] M) · ((` zero) ⦂ A₂ ⇒[ neg p ] A₁))
        ⦂ B₁ ⇒[ p ] B₂))
castStep V (`ι ι) p (`ι κ) with baseEq ι κ
castStep V (`ι ι) p (`ι κ) | true = just V
castStep V (`ι ι) p (`ι κ) | false = nothing
castStep V (` X) p (` Y) with natEq X Y
castStep V (` X) p (` Y) | true = just V
castStep V (` X) p (` Y) | false = nothing
castStep (V ⦂ G ⇒[ - ] ★) ★ p A with consistent? G A
castStep (V ⦂ G ⇒[ - ] ★) ★ p A | true = just (V ⦂ G ⇒[ p ] A)
castStep (V ⦂ G ⇒[ - ] ★) ★ p A | false = just (blame p)
castStep V A p ★ with labelEq p - | ground A
castStep V A p ★ | true | just G = nothing
castStep V A p ★ | true | nothing = nothing
castStep V A p ★ | false | just G with tyEq A ★
castStep V A p ★ | false | just G | true = nothing
castStep V A p ★ | false | just G | false =
  just ((V ⦂ A ⇒[ p ] G) ⦂ G ⇒[ - ] ★)
castStep V A p ★ | false | nothing = nothing
castStep V A p B = nothing

isStep : Label → Term → Ty → Maybe Term
isStep p (V ⦂ (` X) ⇒[ q ] ★) G = just (blame p)
isStep p (V ⦂ H ⇒[ - ] ★) G with tyEq H G | groundTag? H
isStep p (V ⦂ H ⇒[ - ] ★) G | true | true = just ($ bool true)
isStep p (V ⦂ H ⇒[ - ] ★) G | true | false = nothing
isStep p (V ⦂ H ⇒[ - ] ★) G | false | tag = nothing
isStep p M G = nothing

νStep : Ty → Label → Term → Maybe Term
νStep A p ($ c) = just ($ c)
νStep A p (pair V W) = just (pair (ν[ A ] p ∙ V) (ν[ A ] p ∙ W))
νStep A p (ƛ[ B ] M) = just (ƛ[ B ] (ν[ A ] p ∙ M))
νStep A p (Λ[ q ] M :: B) = just (Λ[ q ] (ν[ ⇑ᵗ A ] p ∙ M) :: B)
νStep A p (V ⦂ G ⇒[ - ] ★) with ground? G
νStep A p (V ⦂ G ⇒[ - ] ★) | true = just ((ν[ A ] p ∙ V) ⦂ G ⇒[ - ] ★)
νStep A p (V ⦂ G ⇒[ - ] ★) | false = nothing
νStep A p (V ⦂ (` X) ⇒[ q ] ★) = just (blame p)
νStep A p (V ⦂ B ⇒⟨ P ⟩ Y) with value? (V ⦂ B ⇒⟨ P ⟩ Y)
νStep A p (V ⦂ B ⇒⟨ P ⟩ Y) | true with popBind P
νStep A p (V ⦂ B ⇒⟨ P ⟩ Y) | true | just P′ =
  just ((ν[ A ] p ∙ V) ⦂ B ⇒⟨ P′ ⟩ Y)
νStep A p (V ⦂ B ⇒⟨ P ⟩ Y) | true | nothing = nothing
νStep A p (V ⦂ B ⇒⟨ P ⟩ Y) | false = nothing
νStep A p M = nothing

barrierStep : Term → Ty → Binder → Ty → Maybe Term
barrierStep V (`ι ι) P (`ι κ) with baseEq ι κ
barrierStep V (`ι ι) P (`ι κ) | true = just V
barrierStep V (`ι ι) P (`ι κ) | false = nothing
barrierStep (pair V W) (A `× B) P (A′ `× B′) =
  just (pair (V ⦂ A ⇒⟨ P ⟩ A′) (W ⦂ B ⇒⟨ P ⟩ B′))
barrierStep (ƛ[ C ] M) (A ⇒ B) P (A′ ⇒ B′) =
  just
    (ƛ[ A′ ]
      ((letin
        ((` zero) ⦂ A′ ⇒⟨ negBind P ⟩ A)
        (rename (ext suc) M))
        ⦂ B ⇒⟨ P ⟩ B′))
barrierStep (Λ[ p ] V :: B) (`∀ B₁) (bind X) (`∀ B₂) =
  just
    (Λ[ p ]
      ((renameᵀ swap₀₁ V) ⦂ renameᵗ swap₀₁ B ⇒⟨ bind X ⟩ B₂)
      :: B₂)
barrierStep (Λ[ p ] V :: B) (`∀ B₁) (unbind X) (`∀ B₂) =
  just (Λ[ p ] (V ⦂ B ⇒⟨ unbind X ⟩ B₂) :: B₂)
barrierStep (V ⦂ G ⇒[ - ] ★) ★ Q ★ with ground? G
barrierStep (V ⦂ G ⇒[ - ] ★) ★ Q ★ | true = just (V ⦂ G ⇒[ - ] ★)
barrierStep (V ⦂ G ⇒[ - ] ★) ★ Q ★ | false = nothing
barrierStep (V ⦂ A′ ⇒⟨ unbind X ⟩ (` zero)) (` zero) (bind Y) A
  with natEq X Y
barrierStep (V ⦂ A′ ⇒⟨ unbind X ⟩ (` zero)) (` zero) (bind Y) A
    | true = just V
barrierStep (V ⦂ A′ ⇒⟨ unbind X ⟩ (` zero)) (` zero) (bind Y) A
    | false = nothing
barrierStep V (` suc X) (bind α) (` Y) with natEq X Y | downTermAt zero V
barrierStep V (` suc X) (bind α) (` Y) | true | just V′ = just V′
barrierStep V (` suc X) (bind α) (` Y) | _ | _ = nothing
barrierStep V (` X) (unbind α) (` suc Y) with natEq X Y
barrierStep V (` X) (unbind α) (` suc Y) | true = just (renameᵀ suc V)
barrierStep V (` X) (unbind α) (` suc Y) | false = nothing
barrierStep V A P B = nothing

------------------------------------------------------------------------
-- One executable full-barrier step
------------------------------------------------------------------------

step : Term → Maybe Term
step (` x) = nothing
step ($ c) = nothing
step (ƛ[ A ] M) = nothing
step (L · M) with value? L
step (L · M) | false = mapStep (λ L′ → L′ · M) (step L)
step (L · M) | true with value? M
step (L · M) | true | false = mapStep (λ M′ → L · M′) (step M)
step ((ƛ[ A ] N) · M) | true | true = just (N [ M ])
step (L · M) | true | true = nothing
step (letin L M) with value? L
step (letin L M) | false = mapStep (λ L′ → letin L′ M) (step L)
step (letin L M) | true = just (M [ L ])
step (Λ[ p ] M :: A) with value? M
step (Λ[ p ] M :: A) | true = nothing
step (Λ[ p ] M :: A) | false = mapStep (λ M′ → Λ[ p ] M′ :: A) (step M)
step (M • A) with value? M
step (M • A) | false = mapStep (λ M′ → M′ • A) (step M)
step ((Λ[ p ] V :: B) • A) | true =
  just (ν[ A ] p ∙ (V ⦂ B ⇒⟨ bind zero ⟩ (B [ A ]ᵗ)))
step (M • A) | true = nothing
step (ν[ A ] p ∙ M) with value? M
step (ν[ A ] p ∙ M) | false = mapStep (λ M′ → ν[ A ] p ∙ M′) (step M)
step (ν[ A ] p ∙ M) | true = νStep A p M
step (M ⦂ A ⇒[ p ] B) with value? M
step (M ⦂ A ⇒[ p ] B) | false = mapStep (λ M′ → M′ ⦂ A ⇒[ p ] B) (step M)
step (M ⦂ A ⇒[ p ] B) | true = castStep M A p B
step (M ⦂ A ⇒⟨ P ⟩ B) with value? M
step (M ⦂ A ⇒⟨ P ⟩ B) | false =
  mapStep (λ M′ → M′ ⦂ A ⇒⟨ P ⟩ B) (step M)
step (M ⦂ A ⇒⟨ P ⟩ B) | true = barrierStep M A P B
step (is p M G) with value? M
step (is p M G) | false = mapStep (λ M′ → is p M′ G) (step M)
step (is p M G) | true = isStep p M G
step (pair L M) with value? L
step (pair L M) | false = mapStep (λ L′ → pair L′ M) (step L)
step (pair L M) | true with value? M
step (pair L M) | true | false = mapStep (λ M′ → pair L M′) (step M)
step (pair L M) | true | true = nothing
step (fst M) with value? M
step (fst M) | false = mapStep fst (step M)
step (fst (pair V W)) | true = just V
step (fst M) | true = nothing
step (snd M) with value? M
step (snd M) | false = mapStep snd (step M)
step (snd (pair V W)) | true = just W
step (snd M) | true = nothing
step (ifte L M N) with value? L
step (ifte L M N) | false = mapStep (λ L′ → ifte L′ M N) (step L)
step (ifte ($ bool true) M N) | true = just M
step (ifte ($ bool false) M N) | true = just N
step (ifte L M N) | true = nothing
step (prim op M) with value? M
step (prim op M) | false = mapStep (prim op) (step M)
step (prim op ($ c)) | true = just ($ delta op c)
step (prim op M) | true = nothing
step (blame p) = just (blame p)

evalWithTypeIn : ℕ → Ctx → Ty → Term → EvalResult
evalWithTypeIn zero Γ A M with checkInAs Γ M A
evalWithTypeIn zero Γ A M | false = type-error M
evalWithTypeIn zero Γ A M | true with final? M
evalWithTypeIn zero Γ A M | true | true = done M
evalWithTypeIn zero Γ A M | true | false with step M
evalWithTypeIn zero Γ A M | true | false | just M′ = out-of-gas M
evalWithTypeIn zero Γ A M | true | false | nothing = stuck
evalWithTypeIn (suc n) Γ A M with checkInAs Γ M A
evalWithTypeIn (suc n) Γ A M | false = type-error M
evalWithTypeIn (suc n) Γ A M | true with final? M
evalWithTypeIn (suc n) Γ A M | true | true = done M
evalWithTypeIn (suc n) Γ A M | true | false with step M
evalWithTypeIn (suc n) Γ A M | true | false | just M′ =
  evalWithTypeIn n Γ A M′
evalWithTypeIn (suc n) Γ A M | true | false | nothing = stuck

evalIn : ℕ → Ctx → Ty → Term → EvalResult
evalIn = evalWithTypeIn

eval : ℕ → Term → EvalResult
eval n M with inferClosed M
eval n M | just A = evalWithTypeIn n ∅ A M
eval n M | nothing = type-error M

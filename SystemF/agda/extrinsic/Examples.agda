module extrinsic.Examples where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base using (z<s; s<s)
open import Data.List using ([]; _∷_)

open import extrinsic.Reduction

------------------------------------------------------------------------
-- Small reusable typing helpers
------------------------------------------------------------------------

wfBool : WfTy 0 `Bool
wfBool = wf`Bool

wfNat : WfTy 0 `ℕ
wfNat = wf`ℕ

wfTy0 : WfTy 1 (` 0)
wfTy0 = wfVar z<s

wfTy0⇒Ty0 : WfTy 1 (` 0 ⇒ ` 0)
wfTy0⇒Ty0 = wfFn wfTy0 wfTy0

------------------------------------------------------------------------
-- Source-inspired seed examples
------------------------------------------------------------------------

-- Wadler-style identity seed.
polyId : Term
polyId = Λ (ƛ (` 0))

polyId-⊢ : 0 ⊢ [] ⊢ polyId ⦂ `∀ (` 0 ⇒ ` 0)
polyId-⊢ = ⊢Λ (⊢ƛ wfTy0 (⊢` Z))

polyIdBool : Term
polyIdBool = (polyId ·[]) · `true

polyIdBool-⊢ : 0 ⊢ [] ⊢ polyIdBool ⦂ `Bool
polyIdBool-⊢ =
  ⊢·
    (⊢·[] {A = (` 0 ⇒ ` 0)} {B = `Bool} polyId-⊢ wfBool)
    ⊢true

polyIdBool-↠ : polyIdBool —↠ `true
polyIdBool-↠ =
  polyIdBool —→⟨ ξ-·₁ (β-Λ {A = `Bool}) ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

polyId-↠ : polyIdBool —↠ `true
polyId-↠ = polyIdBool-↠

------------------------------------------------------------------------
-- TAPL-inspired examples
------------------------------------------------------------------------

-- TAPL section 23.4 uses a cluster of classic System F examples:
-- identity, constant, higher-order iteration, self-application, and
-- Church encodings. We keep the raw closed terms here and add typing
-- derivations/reduction traces for representative uses.

wfTy0₂ : WfTy 2 (` 0)
wfTy0₂ = wfVar z<s

wfTy1₂ : WfTy 2 (` 1)
wfTy1₂ = wfVar (s<s z<s)

wfTy0₃ : WfTy 3 (` 0)
wfTy0₃ = wfVar z<s

wfTy1₃ : WfTy 3 (` 1)
wfTy1₃ = wfVar (s<s z<s)

wfTy2₃ : WfTy 3 (` 2)
wfTy2₃ = wfVar (s<s (s<s z<s))

one : Term
one = `suc `zero

one-⊢ : 0 ⊢ [] ⊢ one ⦂ `ℕ
one-⊢ = ⊢suc ⊢zero

one-↠ : one —↠ one
one-↠ = one ∎

two : Term
two = `suc one

two-⊢ : 0 ⊢ [] ⊢ two ⦂ `ℕ
two-⊢ = ⊢suc one-⊢

two-↠ : two —↠ two
two-↠ = two ∎

four : Term
four = `suc (`suc two)

four-⊢ : 0 ⊢ [] ⊢ four ⦂ `ℕ
four-⊢ = ⊢suc (⊢suc two-⊢)

four-↠ : four —↠ four
four-↠ = four ∎

succFn : Term
succFn = ƛ (`suc (` 0))

succFn-⊢ : 0 ⊢ [] ⊢ succFn ⦂ (`ℕ ⇒ `ℕ)
succFn-⊢ = ⊢ƛ wfNat (⊢suc (⊢` Z))

succFnOnZero : Term
succFnOnZero = succFn · `zero

succFnOnZero-⊢ : 0 ⊢ [] ⊢ succFnOnZero ⦂ `ℕ
succFnOnZero-⊢ = ⊢· succFn-⊢ ⊢zero

succFnOnZero-↠ : succFnOnZero —↠ one
succFnOnZero-↠ =
  succFnOnZero —→⟨ β-ƛ vZero ⟩
  one ∎

succFn-↠ : succFnOnZero —↠ one
succFn-↠ = succFnOnZero-↠

------------------------------------------------------------------------
-- TAPL combinators
------------------------------------------------------------------------

identity : Term
identity = polyId

id-⊢ : 0 ⊢ [] ⊢ identity ⦂ `∀ (` 0 ⇒ ` 0)
id-⊢ = polyId-⊢

idBool : Term
idBool = (identity ·[]) · `true

idBool-⊢ : 0 ⊢ [] ⊢ idBool ⦂ `Bool
idBool-⊢ = ⊢· (⊢·[] {A = (` 0 ⇒ ` 0)} {B = `Bool} id-⊢ wfBool) ⊢true

idBool-↠ : idBool —↠ `true
idBool-↠ =
  idBool —→⟨ ξ-·₁ (β-Λ {A = `Bool}) ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

id-↠ : idBool —↠ `true
id-↠ = idBool-↠

taplConst : Term
taplConst = Λ (Λ (ƛ (ƛ (` 1))))

taplConstTy : Ty
taplConstTy = `∀ (`∀ (` 1 ⇒ ` 0 ⇒ ` 1))

taplConst-⊢ : 0 ⊢ [] ⊢ taplConst ⦂ taplConstTy
taplConst-⊢ =
  ⊢Λ (⊢Λ (⊢ƛ wfTy1₂ (⊢ƛ wfTy0₂ (⊢` (S Z)))))


taplConstApp : Term
taplConstApp = (((taplConst ·[]) ·[]) · `true) · `zero

taplConstApp-⊢ : 0 ⊢ [] ⊢ taplConstApp ⦂ `Bool
taplConstApp-⊢ =
  ⊢·
    (⊢·
      (⊢·[]
        {A = (`Bool ⇒ ` 0 ⇒ `Bool)}
        {B = `ℕ}
        (⊢·[] {A = `∀ (` 1 ⇒ ` 0 ⇒ ` 1)} {B = `Bool} taplConst-⊢ wfBool)
        wfNat)
      ⊢true)
    ⊢zero

taplConstApp-↠ : taplConstApp —↠ `true
taplConstApp-↠ =
  taplConstApp —→⟨ ξ-·₁ (ξ-·₁ (ξ-·[] (β-Λ {A = `Bool}))) ⟩
  ((((Λ (ƛ (ƛ (` 1)))) ·[]) · `true) · `zero) —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `ℕ})) ⟩
  (((ƛ (ƛ (` 1))) · `true) · `zero) —→⟨ ξ-·₁ (β-ƛ vTrue) ⟩
  ((ƛ `true) · `zero) —→⟨ β-ƛ vZero ⟩
  `true ∎

taplConst-↠ : taplConstApp —↠ `true
taplConst-↠ = taplConstApp-↠

double : Term
double = Λ (ƛ (ƛ (` 1 · (` 1 · ` 0))))

doubleTy : Ty
doubleTy = `∀ ((` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)

double-⊢ : 0 ⊢ [] ⊢ double ⦂ doubleTy
double-⊢ =
  ⊢Λ
    (⊢ƛ wfTy0⇒Ty0
      (⊢ƛ wfTy0
        (⊢· (⊢` (S Z))
          (⊢· (⊢` (S Z)) (⊢` Z)))))

doubleOnSuccZero : Term
doubleOnSuccZero = ((double ·[]) · succFn) · `zero

doubleOnSuccZero-⊢ : 0 ⊢ [] ⊢ doubleOnSuccZero ⦂ `ℕ
doubleOnSuccZero-⊢ =
  ⊢·
    (⊢·
      (⊢·[] {A = ((` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)} {B = `ℕ} double-⊢ wfNat)
      succFn-⊢)
    ⊢zero

doubleOnSuccZero-↠ : doubleOnSuccZero —↠ two
doubleOnSuccZero-↠ =
  doubleOnSuccZero —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `ℕ})) ⟩
  (((ƛ (ƛ (` 1 · (` 1 · ` 0)))) · succFn) · `zero) —→⟨ ξ-·₁ (β-ƛ vLam) ⟩
  ((ƛ (succFn · (succFn · ` 0))) · `zero) —→⟨ β-ƛ vZero ⟩
  (succFn · (succFn · `zero)) —→⟨ ξ-·₂ vLam (β-ƛ vZero) ⟩
  (succFn · one) —→⟨ β-ƛ (vSuc vZero) ⟩
  two ∎

double-↠ : doubleOnSuccZero —↠ two
double-↠ = doubleOnSuccZero-↠

selfApp : Term
selfApp = ((((identity ·[]) · identity) ·[]) · `true)

wfPolyIdTy : WfTy 0 (`∀ (` 0 ⇒ ` 0))
wfPolyIdTy = wf`∀ (wfFn wfTy0 wfTy0)

selfApp-⊢ : 0 ⊢ [] ⊢ selfApp ⦂ `Bool
selfApp-⊢ =
  ⊢·
    (⊢·[] {A = (` 0 ⇒ ` 0)} {B = `Bool}
      (⊢·
        (⊢·[] {A = (` 0 ⇒ ` 0)} {B = `∀ (` 0 ⇒ ` 0)} id-⊢ wfPolyIdTy)
        id-⊢)
      wfBool)
    ⊢true

selfApp-↠ : selfApp —↠ `true
selfApp-↠ =
  selfApp —→⟨ ξ-·₁ (ξ-·[] (ξ-·₁ (β-Λ {A = `∀ (` 0 ⇒ ` 0)}))) ⟩
  ((((ƛ (` 0)) · identity) ·[]) · `true) —→⟨ ξ-·₁ (ξ-·[] (β-ƛ vTlam)) ⟩
  ((identity ·[]) · `true) —→⟨ ξ-·₁ (β-Λ {A = `Bool}) ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

quadruple : Term
quadruple = ((double ·[]) · succFn) · two

three : Term
three = `suc two

three-⊢ : 0 ⊢ [] ⊢ three ⦂ `ℕ
three-⊢ = ⊢suc two-⊢

three-↠ : three —↠ three
three-↠ = three ∎

quadruple-⊢ : 0 ⊢ [] ⊢ quadruple ⦂ `ℕ
quadruple-⊢ =
  ⊢·
    (⊢·
      (⊢·[] {A = ((` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)} {B = `ℕ} double-⊢ wfNat)
      succFn-⊢)
    two-⊢

quadruple-↠ : quadruple —↠ four
quadruple-↠ =
  quadruple —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `ℕ})) ⟩
  (((ƛ (ƛ (` 1 · (` 1 · ` 0)))) · succFn) · two) —→⟨ ξ-·₁ (β-ƛ vLam) ⟩
  ((ƛ (succFn · (succFn · ` 0))) · two) —→⟨ β-ƛ (vSuc (vSuc vZero)) ⟩
  (succFn · (succFn · two)) —→⟨ ξ-·₂ vLam (β-ƛ (vSuc (vSuc vZero))) ⟩
  (succFn · three) —→⟨ β-ƛ (vSuc (vSuc (vSuc vZero))) ⟩
  four ∎

------------------------------------------------------------------------
-- Church booleans and naturals
------------------------------------------------------------------------

CBool : Ty
CBool = `∀ (` 0 ⇒ ` 0 ⇒ ` 0)

tru : Term
tru = Λ (ƛ (ƛ (` 1)))

fls : Term
fls = Λ (ƛ (ƛ (` 0)))

tru-⊢ : 0 ⊢ [] ⊢ tru ⦂ CBool
tru-⊢ = ⊢Λ (⊢ƛ wfTy0 (⊢ƛ wfTy0 (⊢` (S Z))))

fls-⊢ : 0 ⊢ [] ⊢ fls ⦂ CBool
fls-⊢ = ⊢Λ (⊢ƛ wfTy0 (⊢ƛ wfTy0 (⊢` Z)))

flsBool : Term
flsBool = ((fls ·[]) · `true) · `false

flsBool-⊢ : 0 ⊢ [] ⊢ flsBool ⦂ `Bool
flsBool-⊢ =
  ⊢·
    (⊢· (⊢·[] {A = (` 0 ⇒ ` 0 ⇒ ` 0)} {B = `Bool} fls-⊢ wfBool) ⊢true)
    ⊢false

flsBool-↠ : flsBool —↠ `false
flsBool-↠ =
  flsBool —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `Bool})) ⟩
  (((ƛ (ƛ (` 0))) · `true) · `false) —→⟨ ξ-·₁ (β-ƛ vTrue) ⟩
  ((ƛ (` 0)) · `false) —→⟨ β-ƛ vFalse ⟩
  `false ∎

fls-↠ : flsBool —↠ `false
fls-↠ = flsBool-↠

truBool : Term
truBool = ((tru ·[]) · `true) · `false

truBool-⊢ : 0 ⊢ [] ⊢ truBool ⦂ `Bool
truBool-⊢ =
  ⊢·
    (⊢· (⊢·[] {A = (` 0 ⇒ ` 0 ⇒ ` 0)} {B = `Bool} tru-⊢ wfBool) ⊢true)
    ⊢false

truBool-↠ : truBool —↠ `true
truBool-↠ =
  truBool —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `Bool})) ⟩
  (((ƛ (ƛ (` 1))) · `true) · `false) —→⟨ ξ-·₁ (β-ƛ vTrue) ⟩
  ((ƛ `true) · `false) —→⟨ β-ƛ vFalse ⟩
  `true ∎

tru-↠ : truBool —↠ `true
tru-↠ = truBool-↠

CNat : Ty
CNat = `∀ ((` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)

CNatBody : Ty
CNatBody = ((` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)

wfCNat : WfTy 0 CNat
wfCNat = wf`∀ (wfFn (wfFn wfTy0 wfTy0) (wfFn wfTy0 wfTy0))

c0 : Term
c0 = Λ (ƛ (ƛ (` 0)))

c0-⊢ : 0 ⊢ [] ⊢ c0 ⦂ CNat
c0-⊢ = ⊢Λ (⊢ƛ wfTy0⇒Ty0 (⊢ƛ wfTy0 (⊢` Z)))

c1 : Term
c1 = Λ (ƛ (ƛ (` 1 · ` 0)))

c1-⊢ : 0 ⊢ [] ⊢ c1 ⦂ CNat
c1-⊢ =
  ⊢Λ
    (⊢ƛ wfTy0⇒Ty0
      (⊢ƛ wfTy0
        (⊢· (⊢` (S Z)) (⊢` Z))))

c2 : Term
c2 = Λ (ƛ (ƛ (` 1 · (` 1 · ` 0))))

c2-⊢ : 0 ⊢ [] ⊢ c2 ⦂ CNat
c2-⊢ =
  ⊢Λ
    (⊢ƛ wfTy0⇒Ty0
      (⊢ƛ wfTy0
        (⊢· (⊢` (S Z))
          (⊢· (⊢` (S Z)) (⊢` Z)))))

csucc : Term
csucc = ƛ (Λ (ƛ (ƛ (` 1 · (((` 2 ·[]) · ` 1) · ` 0)))))

csucc-⊢ : 0 ⊢ [] ⊢ csucc ⦂ (CNat ⇒ CNat)
csucc-⊢ =
  ⊢ƛ wfCNat
    (⊢Λ
      (⊢ƛ wfTy0⇒Ty0
        (⊢ƛ wfTy0
          (⊢·
            (⊢` (S Z))
            (⊢·
              (⊢·
                (⊢·[] {A = CNatBody} {B = ` 0}
                  (⊢` (S (S Z)))
                  wfTy0)
                (⊢` (S Z)))
              (⊢` Z))))))

cplus : Term
cplus = ƛ (ƛ (Λ (ƛ (ƛ (((` 3 ·[]) · ` 1) · (((` 2 ·[]) · ` 1) · ` 0))))))

cplus-⊢ : 0 ⊢ [] ⊢ cplus ⦂ (CNat ⇒ CNat ⇒ CNat)
cplus-⊢ =
  ⊢ƛ wfCNat
    (⊢ƛ wfCNat
      (⊢Λ
        (⊢ƛ wfTy0⇒Ty0
          (⊢ƛ wfTy0
            (⊢·
              (⊢·
                (⊢·[] {A = CNatBody} {B = ` 0}
                  (⊢` (S (S (S Z))))
                  wfTy0)
                (⊢` (S Z)))
              (⊢·
                (⊢·
                  (⊢·[] {A = CNatBody} {B = ` 0}
                    (⊢` (S (S Z)))
                    wfTy0)
                  (⊢` (S Z)))
                (⊢` Z)))))))

cnat2nat : Term
cnat2nat = ƛ (((` 0 ·[]) · succFn) · `zero)

cnat2nat-⊢ : 0 ⊢ [] ⊢ cnat2nat ⦂ (CNat ⇒ `ℕ)
cnat2nat-⊢ =
  ⊢ƛ wfCNat
    (⊢·
      (⊢·
        (⊢·[] {A = ((` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)} {B = `ℕ}
          (⊢` Z)
          wfNat)
        (⊢ƛ wfNat (⊢suc (⊢` Z))))
      ⊢zero)

csuccBool : Term
csuccBool = (ƛ `true) · csucc

csuccBool-⊢ : 0 ⊢ [] ⊢ csuccBool ⦂ `Bool
csuccBool-⊢ =
  ⊢·
    (⊢ƛ (wfFn wfCNat wfCNat) ⊢true)
    csucc-⊢

csuccBool-↠ : csuccBool —↠ `true
csuccBool-↠ =
  csuccBool —→⟨ β-ƛ vLam ⟩
  `true ∎

csucc-↠ : csuccBool —↠ `true
csucc-↠ = csuccBool-↠

cplusBool : Term
cplusBool = (ƛ `true) · cplus

cplusBool-⊢ : 0 ⊢ [] ⊢ cplusBool ⦂ `Bool
cplusBool-⊢ =
  ⊢·
    (⊢ƛ (wfFn wfCNat (wfFn wfCNat wfCNat)) ⊢true)
    cplus-⊢

cplusBool-↠ : cplusBool —↠ `true
cplusBool-↠ =
  cplusBool —→⟨ β-ƛ vLam ⟩
  `true ∎

cplus-↠ : cplusBool —↠ `true
cplus-↠ = cplusBool-↠

c0AsNat : Term
c0AsNat = cnat2nat · c0

c0AsNat-⊢ : 0 ⊢ [] ⊢ c0AsNat ⦂ `ℕ
c0AsNat-⊢ = ⊢· cnat2nat-⊢ c0-⊢

c0AsNat-↠ : c0AsNat —↠ `zero
c0AsNat-↠ =
  c0AsNat —→⟨ β-ƛ vTlam ⟩
  (((c0 ·[]) · succFn) · `zero) —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `ℕ})) ⟩
  (((ƛ (ƛ (` 0))) · succFn) · `zero) —→⟨ ξ-·₁ (β-ƛ vLam) ⟩
  ((ƛ (` 0)) · `zero) —→⟨ β-ƛ vZero ⟩
  `zero ∎

c0-↠ : c0AsNat —↠ `zero
c0-↠ = c0AsNat-↠

c1AsNat : Term
c1AsNat = cnat2nat · c1

c1AsNat-⊢ : 0 ⊢ [] ⊢ c1AsNat ⦂ `ℕ
c1AsNat-⊢ = ⊢· cnat2nat-⊢ c1-⊢

c1AsNat-↠ : c1AsNat —↠ one
c1AsNat-↠ =
  c1AsNat —→⟨ β-ƛ vTlam ⟩
  (((c1 ·[]) · succFn) · `zero) —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `ℕ})) ⟩
  (((ƛ (ƛ (` 1 · ` 0))) · succFn) · `zero) —→⟨ ξ-·₁ (β-ƛ vLam) ⟩
  ((ƛ (succFn · ` 0)) · `zero) —→⟨ β-ƛ vZero ⟩
  (succFn · `zero) —→⟨ β-ƛ vZero ⟩
  one ∎

c1-↠ : c1AsNat —↠ one
c1-↠ = c1AsNat-↠

c2AsNat : Term
c2AsNat = cnat2nat · c2

c2AsNat-⊢ : 0 ⊢ [] ⊢ c2AsNat ⦂ `ℕ
c2AsNat-⊢ = ⊢· cnat2nat-⊢ c2-⊢

c2AsNat-↠ : c2AsNat —↠ two
c2AsNat-↠ =
  c2AsNat —→⟨ β-ƛ vTlam ⟩
  (((c2 ·[]) · succFn) · `zero) —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `ℕ})) ⟩
  (((ƛ (ƛ (` 1 · (` 1 · ` 0)))) · succFn) · `zero) —→⟨ ξ-·₁ (β-ƛ vLam) ⟩
  ((ƛ (succFn · (succFn · ` 0))) · `zero) —→⟨ β-ƛ vZero ⟩
  (succFn · (succFn · `zero)) —→⟨ ξ-·₂ vLam (β-ƛ vZero) ⟩
  (succFn · one) —→⟨ β-ƛ (vSuc vZero) ⟩
  two ∎

c2-↠ : c2AsNat —↠ two
c2-↠ = c2AsNat-↠

cnat2nat-↠ : c2AsNat —↠ two
cnat2nat-↠ = c2AsNat-↠

------------------------------------------------------------------------
-- Encoded lists and pairs
------------------------------------------------------------------------

List : Ty → Ty
List A = `∀ (((renameᵗ suc A) ⇒ ` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)

nil : Term
nil = Λ (Λ (ƛ (ƛ (` 0))))

wfListTy0 : WfTy 1 (List (` 0))
wfListTy0 = wf`∀ (wfFn (wfFn wfTy1₂ (wfFn wfTy0₂ wfTy0₂)) (wfFn wfTy0₂ wfTy0₂))

nil-⊢ : 0 ⊢ [] ⊢ nil ⦂ `∀ (List (` 0))
nil-⊢ =
  ⊢Λ
    (⊢Λ
      (⊢ƛ
        (wfFn wfTy1₂ (wfFn wfTy0₂ wfTy0₂))
        (⊢ƛ wfTy0₂ (⊢` Z))))

cons : Term
cons = Λ (ƛ (ƛ (Λ (ƛ (ƛ ((` 1 · ` 3) · (((` 2 ·[]) · ` 1) · ` 0)))))))

cons-⊢ : 0 ⊢ [] ⊢ cons ⦂ `∀ (` 0 ⇒ List (` 0) ⇒ List (` 0))
cons-⊢ =
  ⊢Λ
    (⊢ƛ wfTy0
      (⊢ƛ wfListTy0
        (⊢Λ
          (⊢ƛ
            (wfFn wfTy1₂ (wfFn wfTy0₂ wfTy0₂))
            (⊢ƛ wfTy0₂
              (⊢·
                (⊢· (⊢` (S Z)) (⊢` (S (S (S Z)))))
                (⊢·
                  (⊢·
                    (⊢·[] {A = ((` 2 ⇒ ` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)} {B = ` 0}
                      (⊢` (S (S Z)))
                      wfTy0₂)
                    (⊢` (S Z)))
                  (⊢` Z))))))))

isnil : Term
isnil = Λ (ƛ (((` 0 ·[]) · (ƛ (ƛ `false))) · `true))

isnil-⊢ : 0 ⊢ [] ⊢ isnil ⦂ `∀ (List (` 0) ⇒ `Bool)
isnil-⊢ =
  ⊢Λ
    (⊢ƛ wfListTy0
      (⊢·
        (⊢·
          (⊢·[] {A = ((` 1 ⇒ ` 0 ⇒ ` 0) ⇒ ` 0 ⇒ ` 0)} {B = `Bool}
            (⊢` Z)
            wf`Bool)
          (⊢ƛ wfTy0 (⊢ƛ wf`Bool ⊢false)))
        ⊢true))

nilIsNil : Term
nilIsNil = ((isnil ·[]) · (nil ·[]))

nilIsNil-⊢ : 0 ⊢ [] ⊢ nilIsNil ⦂ `Bool
nilIsNil-⊢ =
  ⊢·
    (⊢·[] {A = (List (` 0) ⇒ `Bool)} {B = `Bool} isnil-⊢ wfBool)
    (⊢·[] {A = List (` 0)} {B = `Bool} nil-⊢ wfBool)

nilIsNil-↠ : nilIsNil —↠ `true
nilIsNil-↠ =
  nilIsNil —→⟨ ξ-·₁ (β-Λ {A = `Bool}) ⟩
  ((ƛ (((` 0 ·[]) · (ƛ (ƛ `false))) · `true)) · (nil ·[]))
    —→⟨ ξ-·₂ vLam (β-Λ {A = `Bool}) ⟩
  ((ƛ (((` 0 ·[]) · (ƛ (ƛ `false))) · `true)) · (Λ (ƛ (ƛ (` 0)))))
    —→⟨ β-ƛ vTlam ⟩
  ((((Λ (ƛ (ƛ (` 0)))) ·[]) · (ƛ (ƛ `false))) · `true)
    —→⟨ ξ-·₁ (ξ-·₁ (β-Λ {A = `Bool})) ⟩
  (((ƛ (ƛ (` 0))) · (ƛ (ƛ `false))) · `true)
    —→⟨ ξ-·₁ (β-ƛ vLam) ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

nil-↠ : nilIsNil —↠ `true
nil-↠ = nilIsNil-↠

wfConsTy : WfTy 0 (`∀ (` 0 ⇒ List (` 0) ⇒ List (` 0)))
wfConsTy = wf`∀ (wfFn wfTy0 (wfFn wfListTy0 wfListTy0))

consIsNil : Term
consIsNil = (ƛ `false) · cons

consIsNil-⊢ : 0 ⊢ [] ⊢ consIsNil ⦂ `Bool
consIsNil-⊢ =
  ⊢·
    (⊢ƛ wfConsTy ⊢false)
    cons-⊢

consIsNil-↠ : consIsNil —↠ `false
consIsNil-↠ =
  consIsNil —→⟨ β-ƛ vTlam ⟩
  `false ∎

cons-↠ : consIsNil —↠ `false
cons-↠ = consIsNil-↠

isnil-↠ : nilIsNil —↠ `true
isnil-↠ = nilIsNil-↠

Pair : Ty → Ty → Ty
Pair A B = `∀ (((renameᵗ suc A) ⇒ (renameᵗ suc B) ⇒ ` 0) ⇒ ` 0)

pair : Term
pair = Λ (Λ (ƛ (ƛ (Λ (ƛ ((` 0 · ` 2) · ` 1))))))

pair-⊢ : 0 ⊢ [] ⊢ pair ⦂ `∀ (`∀ (` 1 ⇒ ` 0 ⇒ Pair (` 1) (` 0)))
pair-⊢ =
  ⊢Λ
    (⊢Λ
      (⊢ƛ wfTy1₂
        (⊢ƛ wfTy0₂
          (⊢Λ
            (⊢ƛ (wfFn wfTy2₃ (wfFn wfTy1₃ wfTy0₃))
              (⊢· (⊢· (⊢` Z) (⊢` (S (S Z)))) (⊢` (S Z))))))))

fst : Term
fst = Λ (Λ (ƛ ((` 0 ·[]) · (ƛ (ƛ (` 1))))))

fst-⊢ : 0 ⊢ [] ⊢ fst ⦂ `∀ (`∀ (Pair (` 1) (` 0) ⇒ ` 1))
fst-⊢ =
  ⊢Λ
    (⊢Λ
      (⊢ƛ
        (wf`∀ (wfFn (wfFn wfTy2₃ (wfFn wfTy1₃ wfTy0₃)) wfTy0₃))
        (⊢·
          (⊢·[] {A = ((` 2 ⇒ ` 1 ⇒ ` 0) ⇒ ` 0)} {B = ` 1}
            (⊢` Z)
            wfTy1₂)
          (⊢ƛ wfTy1₂ (⊢ƛ wfTy0₂ (⊢` (S Z)))))))

snd : Term
snd = Λ (Λ (ƛ ((` 0 ·[]) · (ƛ (ƛ (` 0))))))

snd-⊢ : 0 ⊢ [] ⊢ snd ⦂ `∀ (`∀ (Pair (` 1) (` 0) ⇒ ` 0))
snd-⊢ =
  ⊢Λ
    (⊢Λ
      (⊢ƛ
        (wf`∀ (wfFn (wfFn wfTy2₃ (wfFn wfTy1₃ wfTy0₃)) wfTy0₃))
        (⊢·
          (⊢·[] {A = ((` 2 ⇒ ` 1 ⇒ ` 0) ⇒ ` 0)} {B = ` 0}
            (⊢` Z)
            wfTy0₂)
          (⊢ƛ wfTy1₂ (⊢ƛ wfTy0₂ (⊢` Z))))))

wfPair10₂ : WfTy 2 (Pair (` 1) (` 0))
wfPair10₂ = wf`∀ (wfFn (wfFn wfTy2₃ (wfFn wfTy1₃ wfTy0₃)) wfTy0₃)

wfPairTy : WfTy 0 (`∀ (`∀ (` 1 ⇒ ` 0 ⇒ Pair (` 1) (` 0))))
wfPairTy = wf`∀ (wf`∀ (wfFn wfTy1₂ (wfFn wfTy0₂ wfPair10₂)))

wfFstTy : WfTy 0 (`∀ (`∀ (Pair (` 1) (` 0) ⇒ ` 1)))
wfFstTy = wf`∀ (wf`∀ (wfFn wfPair10₂ wfTy1₂))

wfSndTy : WfTy 0 (`∀ (`∀ (Pair (` 1) (` 0) ⇒ ` 0)))
wfSndTy = wf`∀ (wf`∀ (wfFn wfPair10₂ wfTy0₂))

pairBool : Term
pairBool = (ƛ `true) · pair

pairBool-⊢ : 0 ⊢ [] ⊢ pairBool ⦂ `Bool
pairBool-⊢ =
  ⊢·
    (⊢ƛ wfPairTy ⊢true)
    pair-⊢

pairBool-↠ : pairBool —↠ `true
pairBool-↠ =
  pairBool —→⟨ β-ƛ vTlam ⟩
  `true ∎

pair-↠ : pairBool —↠ `true
pair-↠ = pairBool-↠

fstBool : Term
fstBool = (ƛ `true) · fst

fstBool-⊢ : 0 ⊢ [] ⊢ fstBool ⦂ `Bool
fstBool-⊢ =
  ⊢·
    (⊢ƛ wfFstTy ⊢true)
    fst-⊢

fstBool-↠ : fstBool —↠ `true
fstBool-↠ =
  fstBool —→⟨ β-ƛ vTlam ⟩
  `true ∎

fst-↠ : fstBool —↠ `true
fst-↠ = fstBool-↠

sndBool : Term
sndBool = (ƛ `zero) · snd

sndBool-⊢ : 0 ⊢ [] ⊢ sndBool ⦂ `ℕ
sndBool-⊢ =
  ⊢·
    (⊢ƛ wfSndTy ⊢zero)
    snd-⊢

sndBool-↠ : sndBool —↠ `zero
sndBool-↠ =
  sndBool —→⟨ β-ƛ vTlam ⟩
  `zero ∎

snd-↠ : sndBool —↠ `zero
snd-↠ = sndBool-↠

------------------------------------------------------------------------
-- Coverage targets
------------------------------------------------------------------------

data Rule : Set where
  r-xi-app1 : Rule
  r-xi-app2 : Rule
  r-beta-lam : Rule
  r-xi-suc : Rule
  r-xi-if : Rule
  r-xi-case : Rule
  r-beta-true : Rule
  r-beta-false : Rule
  r-beta-zero : Rule
  r-beta-suc : Rule
  r-xi-tapp : Rule
  r-beta-tlam : Rule

data ExampleId : Set where
  ex-xi-app1-id : ExampleId
  ex-xi-app2-id : ExampleId
  ex-beta-lam-id : ExampleId
  ex-xi-suc-id : ExampleId
  ex-xi-if-id : ExampleId
  ex-xi-case-id : ExampleId
  ex-beta-true-id : ExampleId
  ex-beta-false-id : ExampleId
  ex-beta-zero-id : ExampleId
  ex-beta-suc-id : ExampleId
  ex-xi-tapp-id : ExampleId
  ex-beta-tlam-id : ExampleId

coverage : Rule → ExampleId
coverage r-xi-app1 = ex-xi-app1-id
coverage r-xi-app2 = ex-xi-app2-id
coverage r-beta-lam = ex-beta-lam-id
coverage r-xi-suc = ex-xi-suc-id
coverage r-xi-if = ex-xi-if-id
coverage r-xi-case = ex-xi-case-id
coverage r-beta-true = ex-beta-true-id
coverage r-beta-false = ex-beta-false-id
coverage r-beta-zero = ex-beta-zero-id
coverage r-beta-suc = ex-beta-suc-id
coverage r-xi-tapp = ex-xi-tapp-id
coverage r-beta-tlam = ex-beta-tlam-id

------------------------------------------------------------------------
-- `ξ-·₁`: reduce the function position of an application.
------------------------------------------------------------------------

ex-xi-app1 : Term
ex-xi-app1 = (`if_then_else `true (ƛ (` 0)) (ƛ (` 0))) · `true

ex-xi-app1-⊢ : 0 ⊢ [] ⊢ ex-xi-app1 ⦂ `Bool
ex-xi-app1-⊢ =
  ⊢·
    (⊢if ⊢true
      (⊢ƛ wfBool (⊢` Z))
      (⊢ƛ wfBool (⊢` Z)))
    ⊢true

ex-xi-app1-↠ : ex-xi-app1 —↠ `true
ex-xi-app1-↠ =
  ex-xi-app1 —→⟨ ξ-·₁ β-true ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

------------------------------------------------------------------------
-- `ξ-·₂`: reduce the argument position of an application.
------------------------------------------------------------------------

ex-xi-app2 : Term
ex-xi-app2 = (ƛ (` 0)) · (`if_then_else `false `true `false)

ex-xi-app2-⊢ : 0 ⊢ [] ⊢ ex-xi-app2 ⦂ `Bool
ex-xi-app2-⊢ =
  ⊢· (⊢ƛ wfBool (⊢` Z))
     (⊢if ⊢false ⊢true ⊢false)

ex-xi-app2-↠ : ex-xi-app2 —↠ `false
ex-xi-app2-↠ =
  ex-xi-app2 —→⟨ ξ-·₂ vLam β-false ⟩
  ((ƛ (` 0)) · `false) —→⟨ β-ƛ vFalse ⟩
  `false ∎

------------------------------------------------------------------------
-- `β-ƛ`: ordinary lambda beta reduction.
------------------------------------------------------------------------

ex-beta-lam : Term
ex-beta-lam = (ƛ (` 0)) · `true

ex-beta-lam-⊢ : 0 ⊢ [] ⊢ ex-beta-lam ⦂ `Bool
ex-beta-lam-⊢ =
  ⊢· (⊢ƛ wfBool (⊢` Z))
     ⊢true

ex-beta-lam-↠ : ex-beta-lam —↠ `true
ex-beta-lam-↠ =
  ex-beta-lam —→⟨ β-ƛ vTrue ⟩
  `true ∎

------------------------------------------------------------------------
-- `ξ-suc`: reduce under `suc`.
------------------------------------------------------------------------

ex-xi-suc : Term
ex-xi-suc = `suc (`if_then_else `false `zero `zero)

ex-xi-suc-⊢ : 0 ⊢ [] ⊢ ex-xi-suc ⦂ `ℕ
ex-xi-suc-⊢ =
  ⊢suc (⊢if ⊢false ⊢zero ⊢zero)

ex-xi-suc-↠ : ex-xi-suc —↠ `suc `zero
ex-xi-suc-↠ =
  ex-xi-suc —→⟨ ξ-suc β-false ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- `ξ-if`: reduce the condition of an if-expression.
------------------------------------------------------------------------

ex-xi-if : Term
ex-xi-if = `if_then_else (`if_then_else `true `false `true) `zero (`suc `zero)

ex-xi-if-⊢ : 0 ⊢ [] ⊢ ex-xi-if ⦂ `ℕ
ex-xi-if-⊢ =
  ⊢if
    (⊢if ⊢true ⊢false ⊢true)
    ⊢zero
    (⊢suc ⊢zero)

ex-xi-if-↠ : ex-xi-if —↠ `suc `zero
ex-xi-if-↠ =
  ex-xi-if —→⟨ ξ-if β-true ⟩
  (`if_then_else `false `zero (`suc `zero)) —→⟨ β-false ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- `ξ-case`: reduce the scrutinee of a case expression.
------------------------------------------------------------------------

ex-xi-case : Term
ex-xi-case =
  case_[zero⇒_|suc⇒_] (`if_then_else `true `zero `zero) `zero (`suc (` 0))

ex-xi-case-⊢ : 0 ⊢ [] ⊢ ex-xi-case ⦂ `ℕ
ex-xi-case-⊢ =
  ⊢case
    (⊢if ⊢true ⊢zero ⊢zero)
    ⊢zero
    (⊢suc (⊢` Z))

ex-xi-case-↠ : ex-xi-case —↠ `zero
ex-xi-case-↠ =
  ex-xi-case —→⟨ ξ-case β-true ⟩
  (case_[zero⇒_|suc⇒_] `zero `zero (`suc (` 0))) —→⟨ β-zero ⟩
  (`zero ∎)

------------------------------------------------------------------------
-- `β-true`: if-true.
------------------------------------------------------------------------

ex-beta-true : Term
ex-beta-true = `if_then_else `true `zero (`suc `zero)

ex-beta-true-⊢ : 0 ⊢ [] ⊢ ex-beta-true ⦂ `ℕ
ex-beta-true-⊢ =
  ⊢if ⊢true ⊢zero (⊢suc ⊢zero)

ex-beta-true-↠ : ex-beta-true —↠ `zero
ex-beta-true-↠ =
  ex-beta-true —→⟨ β-true ⟩
  `zero ∎

------------------------------------------------------------------------
-- `β-false`: if-false.
------------------------------------------------------------------------

ex-beta-false : Term
ex-beta-false = `if_then_else `false `zero (`suc `zero)

ex-beta-false-⊢ : 0 ⊢ [] ⊢ ex-beta-false ⦂ `ℕ
ex-beta-false-⊢ =
  ⊢if ⊢false ⊢zero (⊢suc ⊢zero)

ex-beta-false-↠ : ex-beta-false —↠ `suc `zero
ex-beta-false-↠ =
  ex-beta-false —→⟨ β-false ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- `β-zero`: case on zero.
------------------------------------------------------------------------

ex-beta-zero : Term
ex-beta-zero = case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero)

ex-beta-zero-⊢ : 0 ⊢ [] ⊢ ex-beta-zero ⦂ `ℕ
ex-beta-zero-⊢ =
  ⊢case ⊢zero ⊢zero (⊢suc ⊢zero)

ex-beta-zero-↠ : ex-beta-zero —↠ `zero
ex-beta-zero-↠ =
  ex-beta-zero —→⟨ β-zero ⟩
  `zero ∎

------------------------------------------------------------------------
-- `β-suc`: case on a successor value.
------------------------------------------------------------------------

ex-beta-suc : Term
ex-beta-suc = case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc (` 0))

ex-beta-suc-⊢ : 0 ⊢ [] ⊢ ex-beta-suc ⦂ `ℕ
ex-beta-suc-⊢ =
  ⊢case
    (⊢suc ⊢zero)
    ⊢zero
    (⊢suc (⊢` Z))

ex-beta-suc-↠ : ex-beta-suc —↠ `suc `zero
ex-beta-suc-↠ =
  ex-beta-suc —→⟨ β-suc vZero ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- `ξ-·[]`: reduce under a type application.
------------------------------------------------------------------------

ex-xi-tapp : Term
ex-xi-tapp = ((`if_then_else `true polyId polyId) ·[]) · `true

ex-xi-tapp-⊢ : 0 ⊢ [] ⊢ ex-xi-tapp ⦂ `Bool
ex-xi-tapp-⊢ =
  ⊢·
    (⊢·[] {A = (` 0 ⇒ ` 0)} {B = `Bool}
      (⊢if ⊢true polyId-⊢ polyId-⊢)
      wfBool)
    ⊢true

ex-xi-tapp-↠ : ex-xi-tapp —↠ `true
ex-xi-tapp-↠ =
  ex-xi-tapp —→⟨ ξ-·₁ (ξ-·[] β-true) ⟩
  ((polyId ·[]) · `true) —→⟨ ξ-·₁ (β-Λ {A = (` 0 ⇒ ` 0)}) ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

------------------------------------------------------------------------
-- `β-Λ`: polymorphic beta reduction.
------------------------------------------------------------------------

ex-beta-tlam : Term
ex-beta-tlam = (polyId ·[]) · `true

ex-beta-tlam-⊢ : 0 ⊢ [] ⊢ ex-beta-tlam ⦂ `Bool
ex-beta-tlam-⊢ =
  ⊢·
    (⊢·[] {A = (` 0 ⇒ ` 0)} {B = `Bool} polyId-⊢ wfBool)
    ⊢true

ex-beta-tlam-↠ : ex-beta-tlam —↠ `true
ex-beta-tlam-↠ =
  ex-beta-tlam —→⟨ ξ-·₁ (β-Λ {A = (` 0 ⇒ ` 0)}) ⟩
  ((ƛ (` 0)) · `true) —→⟨ β-ƛ vTrue ⟩
  `true ∎

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- The 12 coverage examples above collectively exercise every reduction
-- rule in `extrinsic.SystemF`:
-- `ξ-·₁`, `ξ-·₂`, `β-ƛ`, `ξ-suc`, `ξ-if`, `ξ-case`, `β-true`,
-- `β-false`, `β-zero`, `β-suc`, `ξ-·[]`, and `β-Λ`.

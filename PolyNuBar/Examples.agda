module Examples where

-- File Charter:
--   * Checked PolyNuBar examples corresponding to core regression-test.ss
--     cases and rule families.
--   * Each executable term includes a typing derivation and a reduction
--     witness to the expected result or next semantic wrapper.

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reduction
open import Eval
open import TypeCheck using (checkClosedAs; checkInAs; closeFor?)
open import Untyped

------------------------------------------------------------------------
-- Common abbreviations
------------------------------------------------------------------------

Int BoolT Dyn : Ty
Int = `ι 𝕀
BoolT = `ι 𝔹
Dyn = ★

p q p1 p2 q1 q2 q3 : Label
p = ℓ 1
q = ℓ 2
p1 = ℓ 11
p2 = ℓ 12
q1 = ℓ 21
q2 = ℓ 22
q3 = ℓ 23

wfInt : ∀ {Δ} → WfTy Δ Int
wfInt = wf-base

wfBool : ∀ {Δ} → WfTy Δ BoolT
wfBool = wf-base

wfDyn : ∀ {Δ} → WfTy Δ Dyn
wfDyn = wf-★

------------------------------------------------------------------------
-- regression-test.ss: beta0
------------------------------------------------------------------------

beta0 : Term
beta0 = (ƛ[ Int ] ` zero) · ($ int 42)

beta0-⊢ : ∅ ⊢ beta0 ⦂ Int
beta0-⊢ = ⊢· (⊢ƛ wfInt (⊢` Z)) ⊢const

beta0-↠ : beta0 —↠ ($ int 42)
beta0-↠ =
  beta0 —→⟨ β-ƛ v-const ⟩
  ($ int 42) ∎

beta0-out-of-gas : eval 0 beta0 ≡ out-of-gas beta0
beta0-out-of-gas = refl

------------------------------------------------------------------------
-- Primitive delta behavior
------------------------------------------------------------------------

positive-three : Term
positive-three = prim positive? ($ int 3)

positive-three-⊢ : ∅ ⊢ positive-three ⦂ BoolT
positive-three-⊢ = ⊢prim refl ⊢const

positive-three-↠ : positive-three —↠ ($ bool true)
positive-three-↠ =
  positive-three —→⟨ δ ⟩
  ($ bool true) ∎

one-minus-one : Term
one-minus-one = prim one-minus ($ int 1)

one-minus-one-⊢ : ∅ ⊢ one-minus-one ⦂ Int
one-minus-one-⊢ = ⊢prim refl ⊢const

one-minus-one-↠ : one-minus-one —↠ ($ int 0)
one-minus-one-↠ =
  one-minus-one —→⟨ δ ⟩
  ($ int 0) ∎

------------------------------------------------------------------------
-- regression-test.ss: untyped-primitive
------------------------------------------------------------------------

u-positive-three : UTerm
u-positive-three = primᵘ positive? (lit (int 3))

untyped-primitive : Term
untyped-primitive = elaborate u-positive-three

untyped-primitive-expected : Term
untyped-primitive-expected = elaborate (lit (bool true))

untyped-primitive-⊢ : ∅ ⊢ untyped-primitive ⦂ Dyn
untyped-primitive-⊢ =
  ⊢cast wfBool wfDyn
    (⊢prim refl
      (⊢cast wfDyn wfInt
        (⊢cast wfInt wfDyn ⊢const refl ∼-★ʳ)
        refl
        ∼-★ˡ))
    refl
    ∼-★ʳ

untyped-primitive-↠ : untyped-primitive —↠ untyped-primitive-expected
untyped-primitive-↠ =
  untyped-primitive
    —→⟨ ξ-cast (ξ-prim (cast-collapse v-const g-base ∼-base)) ⟩
  ((prim positive? (($ int 3) ⦂ Int ⇒[ autoLabel 0 ] Int))
    ⦂ BoolT ⇒[ autoLabel 1 ] Dyn)
    —→⟨ ξ-cast (ξ-prim (cast-id-base v-const)) ⟩
  ((prim positive? ($ int 3)) ⦂ BoolT ⇒[ autoLabel 1 ] Dyn)
    —→⟨ ξ-cast δ ⟩
  (($ bool true) ⦂ BoolT ⇒[ autoLabel 1 ] Dyn)
    —→⟨ cast-ground v-const go-base ⟩
  ((($ bool true) ⦂ BoolT ⇒[ autoLabel 1 ] BoolT) ⦂ BoolT ⇒[ - ] Dyn)
    —→⟨ ξ-cast (cast-id-base v-const) ⟩
  untyped-primitive-expected ∎

untyped-primitive-eval : eval 20 untyped-primitive ≡ done untyped-primitive-expected
untyped-primitive-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: popl10-2
------------------------------------------------------------------------

typed-app-inner-ty : Ty
typed-app-inner-ty = (` 1 ⇒ ` 0) ⇒ (` 1 ⇒ ` 0)

typed-app-ty : Ty
typed-app-ty = `∀ (`∀ typed-app-inner-ty)

typed-app : Term
typed-app =
  Λ[ p1 ]
    (Λ[ p2 ]
      (ƛ[ ` 1 ⇒ ` 0 ] (ƛ[ ` 1 ] (` 1 · ` 0)))
      :: typed-app-inner-ty)
    :: (`∀ typed-app-inner-ty)

popl10-2 : Term
popl10-2 =
  letin
    (ƛ[ Int ] ($ bool true))
    (letin
      typed-app
      ((((` zero) • Int) • BoolT) · (` suc zero)) · ($ int 1))

-- The Scheme regression expects `#t`.  With checked full-barrier evaluation,
-- the barrier version currently gets stuck after the preservation failures
-- exposed earlier in this example have been fixed.
popl10-2-after-first-inst : Term
popl10-2-after-first-inst =
  ν[ Int ] p1 ∙
    (Λ[ p2 ]
      ((ƛ[ ` 1 ⇒ ` 0 ] (ƛ[ ` 1 ] (` 1 · ` 0)))
        ⦂ typed-app-inner-ty ⇒⟨ bind 0 ⟩ ((Int ⇒ ` 0) ⇒ Int ⇒ ` 0))
      :: ((Int ⇒ ` 0) ⇒ Int ⇒ ` 0))

popl10-2-expected : EvalResult
popl10-2-expected = stuck

popl10-2-eval : eval 50 popl10-2 ≡ popl10-2-expected
popl10-2-eval = refl

------------------------------------------------------------------------
-- Conditionals and products
------------------------------------------------------------------------

if-true-test : Term
if-true-test = ifte ($ bool true) ($ int 42) ($ int 0)

if-true-test-⊢ : ∅ ⊢ if-true-test ⦂ Int
if-true-test-⊢ = ⊢if ⊢const ⊢const ⊢const

if-true-test-↠ : if-true-test —↠ ($ int 42)
if-true-test-↠ =
  if-true-test —→⟨ if-true ⟩
  ($ int 42) ∎

pair-fst-test : Term
pair-fst-test = fst (pair ($ int 1) ($ int 2))

pair-fst-test-⊢ : ∅ ⊢ pair-fst-test ⦂ Int
pair-fst-test-⊢ = ⊢fst (⊢pair ⊢const ⊢const)

pair-fst-test-↠ : pair-fst-test —↠ ($ int 1)
pair-fst-test-↠ =
  pair-fst-test —→⟨ fst-pair v-const v-const ⟩
  ($ int 1) ∎

pair-snd-test : Term
pair-snd-test = snd (pair ($ int 1) ($ int 2))

pair-snd-test-⊢ : ∅ ⊢ pair-snd-test ⦂ Int
pair-snd-test-⊢ = ⊢snd (⊢pair ⊢const ⊢const)

pair-snd-test-↠ : pair-snd-test —↠ ($ int 2)
pair-snd-test-↠ =
  pair-snd-test —→⟨ snd-pair v-const v-const ⟩
  ($ int 2) ∎

------------------------------------------------------------------------
-- Cast identity and dynamic tags
------------------------------------------------------------------------

id-base-cast : Term
id-base-cast = ($ int 42) ⦂ Int ⇒[ p ] Int

id-base-cast-⊢ : ∅ ⊢ id-base-cast ⦂ Int
id-base-cast-⊢ = ⊢cast wfInt wfInt ⊢const refl ∼-base

id-base-cast-↠ : id-base-cast —↠ ($ int 42)
id-base-cast-↠ =
  id-base-cast —→⟨ cast-id-base v-const ⟩
  ($ int 42) ∎

ground-int-cast : Term
ground-int-cast = ($ int 42) ⦂ Int ⇒[ p ] Dyn

ground-int-cast-⊢ : ∅ ⊢ ground-int-cast ⦂ Dyn
ground-int-cast-⊢ = ⊢cast wfInt wfDyn ⊢const refl ∼-★ʳ

ground-int-cast-↠ :
  ground-int-cast —↠ ((($ int 42) ⦂ Int ⇒[ p ] Int) ⦂ Int ⇒[ - ] Dyn)
ground-int-cast-↠ =
  ground-int-cast —→⟨ cast-ground v-const go-base ⟩
  ((($ int 42) ⦂ Int ⇒[ p ] Int) ⦂ Int ⇒[ - ] Dyn) ∎

is-int-true : Term
is-int-true = is p (($ int 42) ⦂ Int ⇒[ - ] Dyn) Int

is-int-true-⊢ : ∅ ⊢ is-int-true ⦂ BoolT
is-int-true-⊢ =
  ⊢is g-base (⊢cast wfInt wfDyn ⊢const refl ∼-★ʳ)

is-int-true-↠ : is-int-true —↠ ($ bool true)
is-int-true-↠ =
  is-int-true —→⟨ is-true v-const ⟩
  ($ bool true) ∎

------------------------------------------------------------------------
-- regression-test.ss: dcast-fun0
------------------------------------------------------------------------

dcast-fun0 : Term
dcast-fun0 =
  (((ƛ[ Dyn ] ` zero) ⦂ (Dyn ⇒ Dyn) ⇒[ p ] (Int ⇒ Int))
    · ($ int 42))

dcast-fun0-⊢ : ∅ ⊢ dcast-fun0 ⦂ Int
dcast-fun0-⊢ =
  ⊢·
    (⊢cast
      (wf-fun wfDyn wfDyn)
      (wf-fun wfInt wfInt)
      (⊢ƛ wfDyn (⊢` Z))
      refl
      (∼-fun ∼-★ˡ ∼-★ˡ))
    ⊢const

dcast-fun0-eval : eval 80 dcast-fun0 ≡ done ($ int 42)
dcast-fun0-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: dcast-fun1
------------------------------------------------------------------------

dcast-fun1 : Term
dcast-fun1 =
  (((ƛ[ Dyn ] ($ int 42)) ⦂ (Dyn ⇒ Int) ⇒[ p ] (BoolT ⇒ Int))
    · ($ bool true))

dcast-fun1-⊢ : ∅ ⊢ dcast-fun1 ⦂ Int
dcast-fun1-⊢ =
  ⊢·
    (⊢cast
      (wf-fun wfDyn wfInt)
      (wf-fun wfBool wfInt)
      (⊢ƛ wfDyn ⊢const)
      refl
      (∼-fun ∼-★ˡ ∼-base))
    ⊢const

dcast-fun1-eval : eval 50 dcast-fun1 ≡ done ($ int 42)
dcast-fun1-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: dcast-fun2
------------------------------------------------------------------------

II : Ty
II = Int ⇒ Int

II∼II : II ∼ II
II∼II = ∼-fun ∼-base ∼-base

dcast-fun2-arg : Term
dcast-fun2-arg = ƛ[ Int ] prim add1 (` zero)

dcast-fun2-arg-⊢ : ∅ ⊢ dcast-fun2-arg ⦂ II
dcast-fun2-arg-⊢ = ⊢ƛ wfInt (⊢prim refl (⊢` Z))

dcast-fun2 : Term
dcast-fun2 =
  ((((ƛ[ II ] ` zero) ⦂ (II ⇒ II) ⇒[ p ] (II ⇒ II)) · dcast-fun2-arg)
    · ($ int 41))

dcast-fun2-⊢ : ∅ ⊢ dcast-fun2 ⦂ Int
dcast-fun2-⊢ =
  ⊢·
    (⊢·
      (⊢cast
        (wf-fun (wf-fun wfInt wfInt) (wf-fun wfInt wfInt))
        (wf-fun (wf-fun wfInt wfInt) (wf-fun wfInt wfInt))
        (⊢ƛ (wf-fun wfInt wfInt) (⊢` Z))
        refl
        (∼-fun II∼II II∼II))
      dcast-fun2-arg-⊢)
    ⊢const

dcast-fun2-eval : eval 200 dcast-fun2 ≡ done ($ int 42)
dcast-fun2-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: dcast-fun3
------------------------------------------------------------------------

dcast-fun3 : Term
dcast-fun3 =
  ((((ƛ[ Dyn ] ` zero) ⦂ (Dyn ⇒ Dyn) ⇒[ p ] (II ⇒ II)) · dcast-fun2-arg)
    · ($ int 41))

dcast-fun3-⊢ : ∅ ⊢ dcast-fun3 ⦂ Int
dcast-fun3-⊢ =
  ⊢·
    (⊢·
      (⊢cast
        (wf-fun wfDyn wfDyn)
        (wf-fun (wf-fun wfInt wfInt) (wf-fun wfInt wfInt))
        (⊢ƛ wfDyn (⊢` Z))
        refl
        (∼-fun ∼-★ˡ ∼-★ˡ))
      dcast-fun2-arg-⊢)
    ⊢const

dcast-fun3-eval : eval 300 dcast-fun3 ≡ done ($ int 42)
dcast-fun3-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: cast-fun-dyn
------------------------------------------------------------------------

cast-fun-dyn : Term
cast-fun-dyn =
  ((((((ƛ[ Int ] ` zero) ⦂ II ⇒[ p ] Dyn)
    ⦂ Dyn ⇒[ q1 ] Dyn)
    ⦂ Dyn ⇒[ q2 ] Dyn)
    ⦂ Dyn ⇒[ q3 ] (BoolT ⇒ Int))
    · ($ bool true))

cast-fun-dyn-⊢ : ∅ ⊢ cast-fun-dyn ⦂ Int
cast-fun-dyn-⊢ =
  ⊢·
    (⊢cast
      wfDyn
      (wf-fun wfBool wfInt)
      (⊢cast
        wfDyn
        wfDyn
        (⊢cast
          wfDyn
          wfDyn
          (⊢cast
            (wf-fun wfInt wfInt)
            wfDyn
            (⊢ƛ wfInt (⊢` Z))
            refl
            ∼-★ʳ)
          refl
          ∼-★ˡ)
        refl
        ∼-★ˡ)
      refl
      ∼-★ˡ)
    ⊢const

cast-fun-dyn-eval : eval 500 cast-fun-dyn ≡ done (blame (bar p))
cast-fun-dyn-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: forall-to-dyn-to-int
------------------------------------------------------------------------

forall-int-const : Term
forall-int-const = Λ[ q ] ($ int 42) :: Int

forall-int-const-⊢ : ∅ ⊢ forall-int-const ⦂ `∀ Int
forall-int-const-⊢ = ⊢Λ wfInt ⊢const

forall-to-dyn-to-int : Term
forall-to-dyn-to-int =
  ((forall-int-const ⦂ (`∀ Int) ⇒[ p ] Dyn) ⦂ Dyn ⇒[ q ] Int)

forall-to-dyn-to-int-⊢ : ∅ ⊢ forall-to-dyn-to-int ⦂ Int
forall-to-dyn-to-int-⊢ =
  ⊢cast
    wfDyn
    wfInt
    (⊢cast (wf-∀ wfInt) wfDyn forall-int-const-⊢ refl ∼-★ʳ)
    refl
    ∼-★ˡ

forall-to-dyn-to-int-eval : eval 200 forall-to-dyn-to-int ≡ done ($ int 42)
forall-to-dyn-to-int-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: dcast-forall1
------------------------------------------------------------------------

dcast-forall1 : Term
dcast-forall1 = forall-int-const ⦂ (`∀ Int) ⇒[ p ] Int

dcast-forall1-⊢ : ∅ ⊢ dcast-forall1 ⦂ Int
dcast-forall1-⊢ =
  ⊢cast (wf-∀ wfInt) wfInt forall-int-const-⊢ refl (∼-∀ˡ ∼-base)

dcast-forall1-eval : eval 100 dcast-forall1 ≡ done ($ int 42)
dcast-forall1-eval = refl

-- System-F instantiation wrapper, matching the Scheme TyBeta rule
------------------------------------------------------------------------

id-X-body-ty : Ty
id-X-body-ty = ` zero ⇒ ` zero

id-X : Term
id-X = Λ[ p ] (ƛ[ ` zero ] ` zero) :: id-X-body-ty

id-X-⊢ : ∅ ⊢ id-X ⦂ `∀ id-X-body-ty
id-X-⊢ =
  ⊢Λ
    (wf-fun (wf-var TZ) (wf-var TZ))
    (⊢ƛ (wf-var TZ) (⊢` Z))

tybeta-id-int : Term
tybeta-id-int = id-X • Int

tybeta-id-int-⊢ : ∅ ⊢ tybeta-id-int ⦂ Int ⇒ Int
tybeta-id-int-⊢ = ⊢inst id-X-⊢ wfInt

tybeta-id-int-target : Term
tybeta-id-int-target =
  ν[ Int ] p ∙
    ((ƛ[ ` zero ] ` zero)
      ⦂ id-X-body-ty ⇒⟨ bind zero ⟩ (id-X-body-ty [ Int ]ᵗ))

tybeta-id-int-target-⊢ : ∅ ⊢ tybeta-id-int-target ⦂ Int ⇒ Int
tybeta-id-int-target-⊢ =
  ⊢ν wfInt (wf-fun wfInt wfInt)
    (⊢bar
      (wf-fun (wf-var TZᵇ) (wf-var TZᵇ))
      (wf-fun wfInt wfInt)
      here
      (⊢ƛ (wf-var TZᵇ) (⊢` Z))
      refl)

tybeta-id-int-↠ : tybeta-id-int —↠ tybeta-id-int-target
tybeta-id-int-↠ =
  tybeta-id-int —→⟨ β-ty v-ƛ ⟩
  tybeta-id-int-target ∎

anti-barrier-int-open : Term
anti-barrier-int-open = ($ int 2) ⦂ Int ⇒⟨ unbind zero ⟩ (` zero)

anti-barrier-int-open-⊢ :
  ((∅ ▷ˢ Int) ▷ᵇ zero) ⊢ anti-barrier-int-open ⦂ ` zero
anti-barrier-int-open-⊢ = ⊢bar̄ wfInt (wf-var TZᵇ) here ⊢const refl

anti-barrier-int : Term
anti-barrier-int =
  ν[ Int ] p ∙ (anti-barrier-int-open ⦂ (` zero) ⇒⟨ bind zero ⟩ Int)

anti-barrier-int-⊢ : ∅ ⊢ anti-barrier-int ⦂ Int
anti-barrier-int-⊢ =
  ⊢ν wfInt wfInt
    (⊢bar (wf-var TZᵇ) wfInt here anti-barrier-int-open-⊢ refl)

anti-barrier-int-eval : eval 2 anti-barrier-int ≡ done ($ int 2)
anti-barrier-int-eval = refl

------------------------------------------------------------------------
-- PopCtx probes
------------------------------------------------------------------------

-- This suffix type mentions the popped barrier variable under a `∀`.
-- Closing the context should replace the outer variable, now index 1 under
-- the `∀`, while preserving the locally bound index 0.
popctx-forall-suffix-open-ty : Ty
popctx-forall-suffix-open-ty = `∀ (` suc zero `× ` zero)

popctx-forall-suffix-closed-ty : Ty
popctx-forall-suffix-closed-ty = `∀ (Int `× ` zero)

popctx-forall-suffix-open : Ctx
popctx-forall-suffix-open =
  ((∅ ▷ˢ Int) ▷ᵇ zero) ▷ᵛ popctx-forall-suffix-open-ty

popctx-forall-suffix-closed : Ctx
popctx-forall-suffix-closed =
  (∅ ▷ˢ Int) ▷ᵛ popctx-forall-suffix-closed-ty

popctx-forall-suffix-closeFor :
  closeFor? popctx-forall-suffix-open zero ≡
    just
      (Int ,
       zero ,
       popctx-forall-suffix-closed ,
       popᵛ (pop-here here) refl)
popctx-forall-suffix-closeFor = refl

-- This is the suspicious case.  The context has a seal α, then the barrier
-- variable X, then an unrelated type variable Y.  Deep pop targets X even
-- though Y is on top, so the closing depth is 1 and the closed context keeps Y.
popctx-wrong-top-open : Ctx
popctx-wrong-top-open = (∅ ▷ˢ Int) ▷ᵇ zero ▷ᵗ

popctx-wrong-top-closeFor :
  closeFor? popctx-wrong-top-open zero ≡
    just (Int , suc zero , ((∅ ▷ˢ Int) ▷ᵗ) , popᵗ (pop-here here))
popctx-wrong-top-closeFor = refl

-- This term still fails: the target type is Y, not X, and closing Y at depth
-- 1 leaves it as Y rather than replacing it with Int.
popctx-wrong-top-term : Term
popctx-wrong-top-term = ($ int 7) ⦂ Int ⇒⟨ unbind zero ⟩ (` zero)

popctx-wrong-top-tc :
  checkInAs popctx-wrong-top-open popctx-wrong-top-term (` zero) ≡ false
popctx-wrong-top-tc = refl

-- But targeting X succeeds even with Y above it.
popctx-deep-pop-term : Term
popctx-deep-pop-term = ($ int 7) ⦂ Int ⇒⟨ unbind zero ⟩ (` suc zero)

popctx-deep-pop-tc :
  checkInAs popctx-wrong-top-open popctx-deep-pop-term (` suc zero) ≡ true
popctx-deep-pop-tc = refl

-- This is the order that appears in the popl10-2 function-wrapper step:
-- α is introduced, then an ordinary type variable Y, then the barrier-pushed
-- variable X^α.  The marker makes `unbind α` pop X rather than Y.
popctx-marked-after-ordinary-open : Ctx
popctx-marked-after-ordinary-open = (∅ ▷ˢ Int) ▷ᵗ ▷ᵇ zero

popctx-marked-after-ordinary-closeFor :
  closeFor? popctx-marked-after-ordinary-open zero ≡
    just (Int , zero , ((∅ ▷ˢ Int) ▷ᵗ) , pop-here (thereᵗ here))
popctx-marked-after-ordinary-closeFor = refl

popctx-marked-after-ordinary-term : Term
popctx-marked-after-ordinary-term =
  ($ int 7) ⦂ Int ⇒⟨ unbind zero ⟩ (` zero)

popctx-marked-after-ordinary-tc :
  checkInAs
    popctx-marked-after-ordinary-open
    popctx-marked-after-ordinary-term
    (` zero)
    ≡ true
popctx-marked-after-ordinary-tc = refl

-- Term substitution under `ν` must not capture free seal variables in the
-- substituted value.  The free `unbind 0` below refers to an outer seal β; once
-- it is substituted under a fresh `ν α`, it must become `unbind 1`.
seal-subst-capture-value : Term
seal-subst-capture-value = ($ int 7) ⦂ Int ⇒⟨ unbind zero ⟩ (` zero)

seal-subst-under-ν :
  (ν[ BoolT ] p ∙ (` zero)) [ seal-subst-capture-value ] ≡
  ν[ BoolT ] p ∙ (($ int 7) ⦂ Int ⇒⟨ unbind (suc zero) ⟩ (` zero))
seal-subst-under-ν = refl

------------------------------------------------------------------------
-- regression-test.ss: subtyping-killer, full barrier residual
------------------------------------------------------------------------

id-X-reg : Term
id-X-reg = Λ[ p1 ] (ƛ[ ` zero ] ` zero) :: id-X-body-ty

id-X-reg-⊢ : ∅ ⊢ id-X-reg ⦂ `∀ id-X-body-ty
id-X-reg-⊢ =
  ⊢Λ
    (wf-fun (wf-var TZ) (wf-var TZ))
    (⊢ƛ (wf-var TZ) (⊢` Z))

id-X-dyn-body-ty : Ty
id-X-dyn-body-ty = ` zero ⇒ Dyn

id-X∼id-X-dyn : (`∀ id-X-body-ty) ∼ (`∀ id-X-dyn-body-ty)
id-X∼id-X-dyn = ∼-∀ˡ (∼-∀ʳ (∼-fun ∼-★ˡ ∼-★ˡ))

subtyping-killer : Term
subtyping-killer =
  ((id-X-reg ⦂ (`∀ id-X-body-ty) ⇒[ p ] (`∀ id-X-dyn-body-ty)) • Int)
    · ($ int 2)

subtyping-killer-⊢ : ∅ ⊢ subtyping-killer ⦂ Dyn
subtyping-killer-⊢ =
  ⊢·
    (⊢inst
      (⊢cast
        (wf-∀ (wf-fun (wf-var TZ) (wf-var TZ)))
        (wf-∀ (wf-fun (wf-var TZ) wf-★))
        id-X-reg-⊢
        refl
        id-X∼id-X-dyn)
      wfInt)
    ⊢const

-- The Scheme no-barrier regression expects `blame p`.  The full barrier
-- evaluator reaches the protected dynamic value below; checked evaluation
-- reports it as a type error because the abstract result type has escaped.

subtyping-killer-type-error-term : Term
subtyping-killer-type-error-term =
  ν[ Int ] p ∙
    ((($ int 2) ⦂ Int ⇒⟨ unbind zero ⟩ (` zero)) ⦂ (` zero) ⇒[ - ] Dyn)

subtyping-killer-expected : EvalResult
subtyping-killer-expected = type-error subtyping-killer-type-error-term

subtyping-killer-eval : eval 200 subtyping-killer ≡ subtyping-killer-expected
subtyping-killer-eval = refl

------------------------------------------------------------------------
-- regression-test.ss: dcast-forall2
------------------------------------------------------------------------

dcast-forall2 : Term
dcast-forall2 =
  ((id-X ⦂ (`∀ id-X-body-ty) ⇒[ p ] II) · ($ int 42))

dcast-forall2-⊢ : ∅ ⊢ dcast-forall2 ⦂ Int
dcast-forall2-⊢ =
  ⊢·
    (⊢cast
      (wf-∀ (wf-fun (wf-var TZ) (wf-var TZ)))
      (wf-fun wfInt wfInt)
      id-X-⊢
      refl
      (∼-∀ˡ (∼-fun ∼-★ˡ ∼-★ˡ)))
    ⊢const

dcast-forall2-eval : eval 300 dcast-forall2 ≡ done ($ int 42)
dcast-forall2-eval = refl

------------------------------------------------------------------------
-- Executable type checker coverage
------------------------------------------------------------------------

beta0-tc : checkClosedAs beta0 Int ≡ true
beta0-tc = refl

positive-three-tc : checkClosedAs positive-three BoolT ≡ true
positive-three-tc = refl

one-minus-one-tc : checkClosedAs one-minus-one Int ≡ true
one-minus-one-tc = refl

untyped-primitive-tc : checkClosedAs untyped-primitive Dyn ≡ true
untyped-primitive-tc = refl

typed-app-tc : checkClosedAs typed-app typed-app-ty ≡ true
typed-app-tc = refl

popl10-2-tc : checkClosedAs popl10-2 BoolT ≡ true
popl10-2-tc = refl

if-true-test-tc : checkClosedAs if-true-test Int ≡ true
if-true-test-tc = refl

pair-fst-test-tc : checkClosedAs pair-fst-test Int ≡ true
pair-fst-test-tc = refl

pair-snd-test-tc : checkClosedAs pair-snd-test Int ≡ true
pair-snd-test-tc = refl

id-base-cast-tc : checkClosedAs id-base-cast Int ≡ true
id-base-cast-tc = refl

ground-int-cast-tc : checkClosedAs ground-int-cast Dyn ≡ true
ground-int-cast-tc = refl

is-int-true-tc : checkClosedAs is-int-true BoolT ≡ true
is-int-true-tc = refl

dcast-fun0-tc : checkClosedAs dcast-fun0 Int ≡ true
dcast-fun0-tc = refl

dcast-fun1-tc : checkClosedAs dcast-fun1 Int ≡ true
dcast-fun1-tc = refl

dcast-fun2-arg-tc : checkClosedAs dcast-fun2-arg II ≡ true
dcast-fun2-arg-tc = refl

dcast-fun2-tc : checkClosedAs dcast-fun2 Int ≡ true
dcast-fun2-tc = refl

dcast-fun3-tc : checkClosedAs dcast-fun3 Int ≡ true
dcast-fun3-tc = refl

cast-fun-dyn-tc : checkClosedAs cast-fun-dyn Int ≡ true
cast-fun-dyn-tc = refl

forall-int-const-tc : checkClosedAs forall-int-const (`∀ Int) ≡ true
forall-int-const-tc = refl

forall-to-dyn-to-int-tc : checkClosedAs forall-to-dyn-to-int Int ≡ true
forall-to-dyn-to-int-tc = refl

dcast-forall1-tc : checkClosedAs dcast-forall1 Int ≡ true
dcast-forall1-tc = refl

id-X-tc : checkClosedAs id-X (`∀ id-X-body-ty) ≡ true
id-X-tc = refl

tybeta-id-int-tc : checkClosedAs tybeta-id-int (Int ⇒ Int) ≡ true
tybeta-id-int-tc = refl

tybeta-id-int-target-tc :
  checkClosedAs tybeta-id-int-target (Int ⇒ Int) ≡ true
tybeta-id-int-target-tc = refl

anti-barrier-int-open-tc :
  checkInAs ((∅ ▷ˢ Int) ▷ᵇ zero) anti-barrier-int-open (` zero) ≡ true
anti-barrier-int-open-tc = refl

anti-barrier-int-tc : checkClosedAs anti-barrier-int Int ≡ true
anti-barrier-int-tc = refl

id-X-reg-tc : checkClosedAs id-X-reg (`∀ id-X-body-ty) ≡ true
id-X-reg-tc = refl

subtyping-killer-tc : checkClosedAs subtyping-killer Dyn ≡ true
subtyping-killer-tc = refl

dcast-forall2-tc : checkClosedAs dcast-forall2 Int ≡ true
dcast-forall2-tc = refl

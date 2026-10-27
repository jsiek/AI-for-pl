module Examples where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; [])
open import Data.Nat using (zero)
open import Data.Nat.Base using (z<s)
open import Data.Product using (_,_)

open import PolyC
open import PolyG
open import PolyGEval

------------------------------------------------------------------------
-- Environment used by the paper examples: X ↦ Bool
------------------------------------------------------------------------

ΔB : TyEnv
ΔB = known TBool ∷ []

hKnownB : KnownMember ΔB zero TBool
hKnownB = kz

------------------------------------------------------------------------
-- Example terms from §3.1 / §3.2 of the paper
------------------------------------------------------------------------

-- Λ X . λ x : ? . (x :: X)
polyIdDyn : GTerm
polyIdDyn = gtlam (glam TDyn (gasc (gvar zero) (nameTy (tvar zero))))

-- Λ X . λ x : X . (x :: X)
polyIdPrec : GTerm
polyIdPrec = gtlam (glam (nameTy (tvar zero)) (gasc (gvar zero) (nameTy (tvar zero))))

-- unsealX ((ΛX. λx:X. x::X){X↦B}(sealX true))
ex-precise : GTerm
ex-precise =
  gunseal zero
    (gapp
      (gtapp polyIdPrec zero TBool)
      (gseal zero gtrue))

-- unsealX ((ΛX. λx:?. x::X){X↦B}(sealX true))
ex-sealed : GTerm
ex-sealed =
  gunseal zero
    (gapp
      (gtapp polyIdDyn zero TBool)
      (gseal zero gtrue))

-- unsealX ((ΛX. λx:?. x::X){X↦B} true)
ex-unsealed : GTerm
ex-unsealed =
  gunseal zero
    (gapp
      (gtapp polyIdDyn zero TBool)
      gtrue)

------------------------------------------------------------------------
-- Typing derivations
------------------------------------------------------------------------

hVarDyn :
  (absTy ∷ ΔB) ⊢g (TDyn ∷ []) ⊢ gvar zero ⦂ TDyn
hVarDyn = ⊢gvar Z

hAscX :
  (absTy ∷ ΔB) ⊢g (TDyn ∷ []) ⊢ gasc (gvar zero) (nameTy (tvar zero)) ⦂ nameTy (tvar zero)
hAscX = ⊢gasc hVarDyn ∼-dynL (wf-name z<s)

hLamDyn :
  (absTy ∷ ΔB) ⊢g [] ⊢ glam TDyn (gasc (gvar zero) (nameTy (tvar zero))) ⦂ TDyn ⇒ nameTy (tvar zero)
hLamDyn = ⊢glam wf-dyn hAscX

hPolyIdDyn : 
  ΔB ⊢g [] ⊢ polyIdDyn ⦂ Forall (TDyn ⇒ nameTy (tvar zero))
hPolyIdDyn = ⊢gtlam hLamDyn

hVarPrec :
  (absTy ∷ ΔB) ⊢g (nameTy (tvar zero) ∷ []) ⊢ gvar zero ⦂ nameTy (tvar zero)
hVarPrec = ⊢gvar Z

hAscX-prec :
  (absTy ∷ ΔB) ⊢g (nameTy (tvar zero) ∷ []) ⊢ gasc (gvar zero) (nameTy (tvar zero)) ⦂ nameTy (tvar zero)
hAscX-prec = ⊢gasc hVarPrec ∼-name (wf-name z<s)

hLamPrec :
  (absTy ∷ ΔB) ⊢g [] ⊢ glam (nameTy (tvar zero)) (gasc (gvar zero) (nameTy (tvar zero))) ⦂ nameTy (tvar zero) ⇒ nameTy (tvar zero)
hLamPrec = ⊢glam (wf-name z<s) hAscX-prec

hPolyIdPrec :
  ΔB ⊢g [] ⊢ polyIdPrec ⦂ Forall (nameTy (tvar zero) ⇒ nameTy (tvar zero))
hPolyIdPrec = ⊢gtlam hLamPrec

hInstPrec :
  ΔB ⊢g [] ⊢ gtapp polyIdPrec zero TBool ⦂ nameTy (tvar zero) ⇒ nameTy (tvar zero)
hInstPrec = ⊢gtapp hPolyIdPrec as-forall hKnownB

hInst :
  ΔB ⊢g [] ⊢ gtapp polyIdDyn zero TBool ⦂ TDyn ⇒ nameTy (tvar zero)
hInst = ⊢gtapp hPolyIdDyn as-forall hKnownB

hSealTrue :
  ΔB ⊢g [] ⊢ gseal zero gtrue ⦂ nameTy (tvar zero)
hSealTrue = ⊢gseal hKnownB ⊢gtrue ∼-bool

hApp-precise :
  ΔB ⊢g [] ⊢ gapp (gtapp polyIdPrec zero TBool) (gseal zero gtrue) ⦂ nameTy (tvar zero)
hApp-precise = ⊢gapp hInstPrec as-fun hSealTrue ∼-name (wf-name z<s)

hEx-precise :
  ΔB ⊢g [] ⊢ ex-precise ⦂ TBool
hEx-precise = ⊢gunseal hKnownB hApp-precise ∼-name

hApp-sealed :
  ΔB ⊢g [] ⊢ gapp (gtapp polyIdDyn zero TBool) (gseal zero gtrue) ⦂ nameTy (tvar zero)
hApp-sealed = ⊢gapp hInst as-fun hSealTrue ∼-dynR wf-dyn

hEx-sealed :
  ΔB ⊢g [] ⊢ ex-sealed ⦂ TBool
hEx-sealed = ⊢gunseal hKnownB hApp-sealed ∼-name

hApp-unsealed :
  ΔB ⊢g [] ⊢ gapp (gtapp polyIdDyn zero TBool) gtrue ⦂ nameTy (tvar zero)
hApp-unsealed = ⊢gapp hInst as-fun ⊢gtrue ∼-dynR wf-dyn

hEx-unsealed :
  ΔB ⊢g [] ⊢ ex-unsealed ⦂ TBool
hEx-unsealed = ⊢gunseal hKnownB hApp-unsealed ∼-name

------------------------------------------------------------------------
-- Evaluation checks
------------------------------------------------------------------------

ex-precise-evals-true :
  evalPolyG 80 hEx-precise ≡ ([] , true)
ex-precise-evals-true = refl

ex-sealed-evals-true :
  evalPolyG 80 hEx-sealed ≡ ([] , true)
ex-sealed-evals-true = refl

ex-unsealed-evals-err :
  evalPolyG 80 hEx-unsealed ≡ ([] , err)
ex-unsealed-evals-err = refl

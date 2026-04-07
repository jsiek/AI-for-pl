import intrinsic.Eval

namespace Intrinsic

set_option autoImplicit false

------------------------------------------------------------------------
-- Seed closed examples (intrinsic style)
------------------------------------------------------------------------

def one : Closed TNat :=
  Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

def one_reduces : one —↠ one :=
  MultiStep.refl _

def «one_↠» : one —↠ one :=
  one_reduces

def two : Closed TNat :=
  Term.tsuc one

def two_reduces : two —↠ two :=
  MultiStep.refl _

def «two_↠» : two —↠ two :=
  two_reduces

def four : Closed TNat :=
  Term.tsuc (Term.tsuc two)

def four_reduces : four —↠ four :=
  MultiStep.refl _

def «four_↠» : four —↠ four :=
  four_reduces

def succFn : Closed (TNat ⇒ TNat) :=
  Term.lam TNat (Term.tsuc (Term.var HasVar.Z))

def succFnOnZero : Closed TNat :=
  Term.app succFn (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def succFnOnZero_reduces : succFnOnZero —↠ one :=
  MultiStep.step _ (Step.betaLam (N := Term.tsuc (Term.var HasVar.Z)) (W := Term.tzero) Value.vZero)
    (MultiStep.refl _)

noncomputable def «succFnOnZero_↠» : succFnOnZero —↠ one :=
  succFnOnZero_reduces

noncomputable def «succFn_↠» : succFnOnZero —↠ one :=
  succFnOnZero_reduces

theorem subst_extSub_singleEnv_succFn_S {V : Closed TNat} :
    subst (fun {_A} => singleEnv V)
      (extSub (fun {_A} => singleEnv succFn) (HasVar.S HasVar.Z))
    = succFn := by
  unfold extSub
  simp [singleEnv]
  simp [wk]
  unfold subst
  simp [succFn]
  simp [rename]
  simp [extRen]
  simp [subst]
  simp [extSub]

theorem subst_extSub_singleEnv_succFn_Z {V : Closed TNat} :
    subst (fun {_A} => singleEnv V)
      (extSub (fun {_A} => singleEnv succFn) HasVar.Z)
    = V := by
  unfold extSub
  simp [subst]
  simp [singleEnv]

def ifTrueNat : Closed TNat :=
  Term.tite (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) one two

def ifTrueNat_reduces : ifTrueNat —↠ one :=
  MultiStep.step _ Step.betaTrue (MultiStep.refl _)

def caseSucNat : Closed TNat :=
  Term.tcaseNat one two (Term.tsuc (Term.var HasVar.Z))

noncomputable def caseSucNat_reduces : caseSucNat —↠ one :=
  MultiStep.step _
    (Step.betaSuc (V := Term.tzero) (M := two) (N := Term.tsuc (Term.var HasVar.Z)) Value.vZero)
    (MultiStep.refl _)

------------------------------------------------------------------------
-- Intrinsic System F identity seed
------------------------------------------------------------------------

def polyIdTy : Ty ∅ :=
  ∀ₜ (#TyVar.Z ⇒ #TyVar.Z)

def polyId : Closed polyIdTy :=
  Term.tlam (Term.lam (#TyVar.Z) (Term.var HasVar.Z))

def polyIdBool : Closed TBool :=
  Term.app (Term.tapp polyId TBool) (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

theorem substTT_singleTyEnv_varZ_empty (B : Ty ∅) :
    substTT (σ := singleTyEnv B)
      (Term.var
        (Δ := (∅ ,α))
        (Γ := (liftCtx (∅ᶜ : Ctx ∅) , (#TyVar.Z : Ty (∅ ,α))))
        (A := (#TyVar.Z : Ty (∅ ,α)))
        HasVar.Z)
      = Term.var (Δ := ∅) (Γ := ((∅ᶜ : Ctx ∅) , B)) (A := B) HasVar.Z := by
  simp [substTT]
  simp [substVar]

noncomputable def polyIdInstAppTrue : Closed TBool :=
  Term.app
    (instT (Term.lam (#TyVar.Z) (Term.var HasVar.Z)) TBool)
    (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def polyIdInstAppTrue_reduces : polyIdInstAppTrue —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold polyIdInstAppTrue
  rw [instT_lam_empty (N := Term.var HasVar.Z) TBool]
  rw [substTT_singleTyEnv_varZ_empty TBool]
  exact MultiStep.step _ (Step.betaLam (A := TBool) (B := TBool)
      (N := Term.var HasVar.Z)
      (W := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) Value.vTrue)
    (MultiStep.refl _)

noncomputable def polyIdBool_reduces :
    polyIdBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  exact multiTrans
    (MultiStep.step _ (Step.xiApp1 (Step.betaTlam (N := Term.lam (#TyVar.Z) (Term.var HasVar.Z)) (B := TBool)))
      (MultiStep.refl _))
    polyIdInstAppTrue_reduces

noncomputable def «polyIdBool_↠» : polyIdBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  polyIdBool_reduces

noncomputable def «polyId_↠» : polyIdBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  polyIdBool_reduces

noncomputable def polyIdBoolProgress : Progress polyIdBool :=
  progress polyIdBool

------------------------------------------------------------------------
-- Additional TAPL-style combinators (ported terms + progress witnesses)
------------------------------------------------------------------------

def identity : Closed polyIdTy :=
  polyId

def idBool : Closed TBool :=
  Term.app (Term.tapp identity TBool) (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def idBool_reduces :
    idBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold idBool identity
  simpa using polyIdBool_reduces

noncomputable def «idBool_↠» : idBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  idBool_reduces

noncomputable def «id_↠» : idBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  idBool_reduces

noncomputable def idBoolProgress : Progress idBool :=
  progress idBool

def taplConstTy : Ty ∅ :=
  ∀ₜ (∀ₜ (#TyVar.S TyVar.Z ⇒ #TyVar.Z ⇒ #TyVar.S TyVar.Z))

def taplConst : Closed taplConstTy :=
  Term.tlam
    (Term.tlam
      (Term.lam (#TyVar.S TyVar.Z)
        (Term.lam (#TyVar.Z)
          (Term.var (HasVar.S HasVar.Z)))))

def taplConstApp : Closed TBool :=
  Term.app
    (Term.app
      (Term.tapp (Term.tapp taplConst TBool) TNat)
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
    )
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def taplConstAppProgress : Progress taplConstApp :=
  progress taplConstApp

noncomputable def taplConstApp_reduces :
    taplConstApp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold taplConstApp taplConst
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.xiTapp (Step.betaTlam
    (N := Term.tlam
      (Term.lam (#TyVar.S TyVar.Z)
        (Term.lam (#TyVar.Z)
          (Term.var (HasVar.S HasVar.Z)))))
    (B := TBool))))) ?_
  rw [instT_tlam_empty_simpler]
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam (B := TNat)))) ?_
  rw [instT_substTT_exts_lam_empty
    (N := Term.lam (#TyVar.Z) (Term.var (HasVar.S HasVar.Z)))
    (B₁ := TBool) (B₂ := TNat)]
  simp [substT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
    Value.vTrue)) ?_
  unfold singleSubst
  unfold subst
  simp [substTT]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    Value.vZero) ?_
  unfold singleSubst
  simp [subst]
  exact MultiStep.refl _

noncomputable def «taplConstApp_↠» : taplConstApp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  taplConstApp_reduces

noncomputable def «taplConst_↠» : taplConstApp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  taplConstApp_reduces

def doubleTy : Ty ∅ :=
  ∀ₜ ((#TyVar.Z ⇒ #TyVar.Z) ⇒ #TyVar.Z ⇒ #TyVar.Z)

def double : Closed doubleTy :=
  Term.tlam
    (Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.app
            (Term.var (HasVar.S HasVar.Z))
            (Term.var HasVar.Z)))))

def doubleOnSuccZero : Closed TNat :=
  Term.app
    (Term.app
      (Term.tapp double TNat)
      succFn
    )
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def doubleOnSuccZero_reduces :
    doubleOnSuccZero —↠ two := by
  unfold doubleOnSuccZero double succFn two one
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.app
            (Term.var (HasVar.S HasVar.Z))
            (Term.var HasVar.Z)))))
    (B := TNat)))) ?_
  rw [instT_lam_empty_gen
    (N := Term.lam (#TyVar.Z)
      (Term.app
        (Term.var (HasVar.S HasVar.Z))
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.var HasVar.Z))))
    (B := TNat)]
  simp [substT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := succFn)
    Value.vLam)) ?_
  unfold singleSubst
  unfold subst
  simp [substTT]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    Value.vZero) ?_
  unfold singleSubst
  unfold subst
  simp [substVar]
  simp [singleEnv]
  simp [subst]
  try rw [subst_extSub_singleEnv_succFn_S]
  try rw [subst_extSub_singleEnv_succFn_S]
  try rw [subst_extSub_singleEnv_succFn_Z]
  refine MultiStep.step _ (Step.xiApp2
    (V := succFn)
    Value.vLam
    (Step.betaLam
      (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
      Value.vZero)) ?_
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    (Value.vSuc Value.vZero))
    (MultiStep.refl _)

noncomputable def «doubleOnSuccZero_↠» :
    doubleOnSuccZero —↠ two :=
  doubleOnSuccZero_reduces

noncomputable def «double_↠» :
    doubleOnSuccZero —↠ two :=
  doubleOnSuccZero_reduces

noncomputable def doubleOnSuccZeroProgress : Progress doubleOnSuccZero :=
  progress doubleOnSuccZero

def selfApp : Closed TBool :=
  Term.app
    (Term.tapp
      (Term.app
        (Term.tapp identity polyIdTy)
        identity)
      TBool)
    (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def selfAppProgress : Progress selfApp :=
  progress selfApp

noncomputable def selfApp_reduces :
    selfApp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold selfApp identity polyId polyIdTy
  refine MultiStep.step _
    (Step.xiApp1 (Step.xiTapp (Step.xiApp1 (Step.betaTlam
      (N := Term.lam (#TyVar.Z) (Term.var HasVar.Z))
      (B := polyIdTy))))) ?_
  rw [instT_lam_empty (N := Term.var HasVar.Z) polyIdTy]
  rw [substTT_singleTyEnv_varZ_empty polyIdTy]
  refine MultiStep.step _
    (Step.xiApp1 (Step.xiTapp (Step.betaLam
      (N := Term.var HasVar.Z)
      (W := identity)
      Value.vTlam))) ?_
  unfold singleSubst
  unfold subst
  simp [singleEnv]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z) (Term.var HasVar.Z))
    (B := TBool))) ?_
  exact polyIdInstAppTrue_reduces

noncomputable def «selfApp_↠» : selfApp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  selfApp_reduces

def three : Closed TNat :=
  Term.tsuc two

def three_reduces : three —↠ three :=
  MultiStep.refl _

def «three_↠» : three —↠ three :=
  three_reduces

def quadruple : Closed TNat :=
  Term.app
    (Term.app
      (Term.tapp double TNat)
      succFn
    )
    two

noncomputable def quadruple_reduces :
    quadruple —↠ four := by
  unfold quadruple double succFn four two one
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.app
            (Term.var (HasVar.S HasVar.Z))
            (Term.var HasVar.Z)))))
    (B := TNat)))) ?_
  rw [instT_lam_empty_gen
    (N := Term.lam (#TyVar.Z)
      (Term.app
        (Term.var (HasVar.S HasVar.Z))
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.var HasVar.Z))))
    (B := TNat)]
  simp [substT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := succFn)
    Value.vLam)) ?_
  unfold singleSubst
  unfold subst
  simp [substTT]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tsuc (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))))
    (Value.vSuc (Value.vSuc Value.vZero))) ?_
  unfold singleSubst
  unfold subst
  simp [substVar]
  simp [singleEnv]
  simp [subst]
  try rw [subst_extSub_singleEnv_succFn_S]
  try rw [subst_extSub_singleEnv_succFn_S]
  try rw [subst_extSub_singleEnv_succFn_Z]
  refine MultiStep.step _ (Step.xiApp2
    (V := succFn)
    Value.vLam
    (Step.betaLam
      (W := Term.tsuc (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))))
      (Value.vSuc (Value.vSuc Value.vZero)))) ?_
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tsuc (Term.tsuc (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))))
    (Value.vSuc (Value.vSuc (Value.vSuc Value.vZero))))
    (MultiStep.refl _)

noncomputable def «quadruple_↠» :
    quadruple —↠ four :=
  quadruple_reduces

------------------------------------------------------------------------
-- Church booleans (ported core subset)
------------------------------------------------------------------------

def CBool : Ty ∅ :=
  ∀ₜ (#TyVar.Z ⇒ #TyVar.Z ⇒ #TyVar.Z)

def tru : Closed CBool :=
  Term.tlam
    (Term.lam (#TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.var (HasVar.S HasVar.Z))))

def fls : Closed CBool :=
  Term.tlam
    (Term.lam (#TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.var HasVar.Z)))

def flsBool : Closed TBool :=
  Term.app
    (Term.app
      (Term.tapp fls TBool)
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)))
    (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))

def truBool : Closed TBool :=
  Term.app
    (Term.app
      (Term.tapp tru TBool)
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)))
    (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def flsBoolProgress : Progress flsBool :=
  progress flsBool

noncomputable def truBoolProgress : Progress truBool :=
  progress truBool

noncomputable def flsBool_reduces :
    flsBool —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold flsBool fls
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.var HasVar.Z)))
    (B := TBool)))) ?_
  rw [instT_lam_empty (N := Term.lam (#TyVar.Z) (Term.var HasVar.Z)) TBool]
  simp [substTT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
    Value.vTrue)) ?_
  unfold singleSubst
  unfold subst
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
    Value.vFalse)
    (MultiStep.refl _)

noncomputable def truBool_reduces :
    truBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold truBool tru
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.var (HasVar.S HasVar.Z))))
    (B := TBool)))) ?_
  rw [instT_lam_empty (N := Term.lam (#TyVar.Z) (Term.var (HasVar.S HasVar.Z))) TBool]
  simp [substTT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
    Value.vTrue)) ?_
  unfold singleSubst
  unfold subst
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
    Value.vFalse) ?_
  unfold singleSubst
  unfold subst
  simp [singleEnv]
  exact MultiStep.refl _

noncomputable def «flsBool_↠» :
    flsBool —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  flsBool_reduces

noncomputable def «fls_↠» :
    flsBool —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  flsBool_reduces

noncomputable def «truBool_↠» :
    truBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  truBool_reduces

noncomputable def «tru_↠» :
    truBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  truBool_reduces

------------------------------------------------------------------------
-- Church naturals (ported core subset)
------------------------------------------------------------------------

def CNat : Ty ∅ :=
  ∀ₜ ((#TyVar.Z ⇒ #TyVar.Z) ⇒ #TyVar.Z ⇒ #TyVar.Z)

def c0 : Closed CNat :=
  Term.tlam
    (Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.var HasVar.Z)))

def c1 : Closed CNat :=
  Term.tlam
    (Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.var HasVar.Z))))

def c2 : Closed CNat :=
  Term.tlam
    (Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.app
            (Term.var (HasVar.S HasVar.Z))
            (Term.var HasVar.Z)))))

def csucc : Closed (CNat ⇒ CNat) :=
  Term.lam CNat
    (Term.tlam
      (Term.lam (#TyVar.Z ⇒ #TyVar.Z)
        (Term.lam (#TyVar.Z)
          (Term.app
            (Term.var (HasVar.S HasVar.Z))
            (Term.app
              (Term.app
                (Term.tapp (Term.var (HasVar.S (HasVar.S HasVar.Z))) (#TyVar.Z))
                (Term.var (HasVar.S HasVar.Z)))
              (Term.var HasVar.Z))))))

def cplus : Closed (CNat ⇒ CNat ⇒ CNat) :=
  Term.lam CNat
    (Term.lam CNat
      (Term.tlam
        (Term.lam (#TyVar.Z ⇒ #TyVar.Z)
          (Term.lam (#TyVar.Z)
            (Term.app
              (Term.app
                (Term.tapp (Term.var (HasVar.S (HasVar.S (HasVar.S HasVar.Z)))) (#TyVar.Z))
                (Term.var (HasVar.S HasVar.Z)))
              (Term.app
                (Term.app
                  (Term.tapp (Term.var (HasVar.S (HasVar.S HasVar.Z))) (#TyVar.Z))
                  (Term.var (HasVar.S HasVar.Z)))
                (Term.var HasVar.Z)))))))

noncomputable def cnat2nat : Closed (CNat ⇒ TNat) :=
  Term.lam CNat
    (Term.app
      (Term.app
        (Term.tapp (Term.var HasVar.Z) TNat)
        (wk (B := CNat) succFn))
      (wk (B := CNat) (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))))

noncomputable def c0AsNat : Closed TNat :=
  Term.app cnat2nat c0

noncomputable def c1AsNat : Closed TNat :=
  Term.app cnat2nat c1

noncomputable def c2AsNat : Closed TNat :=
  Term.app cnat2nat c2

noncomputable def c0AsNatProgress : Progress c0AsNat :=
  progress c0AsNat

noncomputable def c1AsNatProgress : Progress c1AsNat :=
  progress c1AsNat

noncomputable def c2AsNatProgress : Progress c2AsNat :=
  progress c2AsNat

noncomputable def c0AsNatBetaTarget : Closed TNat :=
  Term.app
    (Term.app
      (Term.tapp c0 TNat)
      succFn)
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def c1AsNatBetaTarget : Closed TNat :=
  Term.app
    (Term.app
      (Term.tapp c1 TNat)
      succFn)
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def c2AsNatBetaTarget : Closed TNat :=
  Term.app
    (Term.app
      (Term.tapp c2 TNat)
      succFn)
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def c0AsNat_reduces : c0AsNat —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold c0AsNat cnat2nat c0
  refine MultiStep.step _ (Step.betaLam
    (N := Term.app
      (Term.app
        (Term.tapp (Term.var HasVar.Z) TNat)
        (wk (B := CNat) succFn))
      (wk (B := CNat) (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    )
    (W := c0)
    Value.vTlam) ?_
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.var HasVar.Z)))
    (B := TNat)))) ?_
  rw [instT_lam_empty_gen
    (N := Term.lam (#TyVar.Z)
      (Term.var HasVar.Z))
    (B := TNat)]
  simp [substT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := succFn)
    Value.vLam)) ?_
  unfold singleSubst
  unfold subst
  simp [substTT]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    Value.vZero) ?_
  unfold singleSubst
  unfold subst
  simp [singleEnv]
  exact MultiStep.refl _

noncomputable def c1AsNat_reduces : c1AsNat —↠ one := by
  unfold c1AsNat cnat2nat c1 one
  refine MultiStep.step _ (Step.betaLam
    (N := Term.app
      (Term.app
        (Term.tapp (Term.var HasVar.Z) TNat)
        (wk (B := CNat) succFn))
      (wk (B := CNat) (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    )
    (W := c1)
    Value.vTlam) ?_
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.var HasVar.Z))))
    (B := TNat)))) ?_
  rw [instT_lam_empty_gen
    (N := Term.lam (#TyVar.Z)
      (Term.app
        (Term.var (HasVar.S HasVar.Z))
        (Term.var HasVar.Z)))
    (B := TNat)]
  simp [substT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := succFn)
    Value.vLam)) ?_
  unfold singleSubst
  unfold subst
  simp [substTT]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    Value.vZero) ?_
  unfold singleSubst
  unfold subst
  simp [singleEnv]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    Value.vZero)
    (MultiStep.refl _)

noncomputable def c2AsNat_reduces : c2AsNat —↠ two := by
  unfold c2AsNat cnat2nat c2 two one
  refine MultiStep.step _ (Step.betaLam
    (N := Term.app
      (Term.app
        (Term.tapp (Term.var HasVar.Z) TNat)
        (wk (B := CNat) succFn))
      (wk (B := CNat) (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    )
    (W := c2)
    Value.vTlam) ?_
  refine MultiStep.step _ (Step.xiApp1 (Step.xiApp1 (Step.betaTlam
    (N := Term.lam (#TyVar.Z ⇒ #TyVar.Z)
      (Term.lam (#TyVar.Z)
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.app
            (Term.var (HasVar.S HasVar.Z))
            (Term.var HasVar.Z)))))
    (B := TNat)))) ?_
  rw [instT_lam_empty_gen
    (N := Term.lam (#TyVar.Z)
      (Term.app
        (Term.var (HasVar.S HasVar.Z))
        (Term.app
          (Term.var (HasVar.S HasVar.Z))
          (Term.var HasVar.Z))))
    (B := TNat)]
  simp [substT]
  refine MultiStep.step _ (Step.xiApp1 (Step.betaLam
    (W := succFn)
    Value.vLam)) ?_
  unfold singleSubst
  unfold subst
  simp [substTT]
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    Value.vZero) ?_
  unfold singleSubst
  unfold subst
  simp [substVar]
  simp [singleEnv]
  simp [subst]
  try rw [subst_extSub_singleEnv_succFn_S]
  try rw [subst_extSub_singleEnv_succFn_S]
  try rw [subst_extSub_singleEnv_succFn_Z]
  refine MultiStep.step _ (Step.xiApp2
    (V := succFn)
    Value.vLam
    (Step.betaLam
      (W := Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
      Value.vZero)) ?_
  refine MultiStep.step _ (Step.betaLam
    (W := Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    (Value.vSuc Value.vZero))
    (MultiStep.refl _)

noncomputable def «c0AsNat_↠» : c0AsNat —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  c0AsNat_reduces

noncomputable def «c0_↠» : c0AsNat —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  c0AsNat_reduces

noncomputable def «c1AsNat_↠» : c1AsNat —↠ one :=
  c1AsNat_reduces

noncomputable def «c1_↠» : c1AsNat —↠ one :=
  c1AsNat_reduces

noncomputable def «c2AsNat_↠» : c2AsNat —↠ two :=
  c2AsNat_reduces

noncomputable def «c2_↠» : c2AsNat —↠ two :=
  c2AsNat_reduces

noncomputable def «cnat2nat_↠» : c2AsNat —↠ two :=
  c2AsNat_reduces

def csuccBool : Closed TBool :=
  Term.app
    (Term.lam (CNat ⇒ CNat) (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , (CNat ⇒ CNat))))
    csucc

def cplusBool : Closed TBool :=
  Term.app
    (Term.lam (CNat ⇒ CNat ⇒ CNat) (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , (CNat ⇒ CNat ⇒ CNat))))
    cplus

noncomputable def csuccBoolProgress : Progress csuccBool :=
  progress csuccBool

noncomputable def cplusBoolProgress : Progress cplusBool :=
  progress cplusBool

noncomputable def csuccBool_reduces : csuccBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam
    (N := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , (CNat ⇒ CNat)))
    (W := csucc) Value.vLam)
    (MultiStep.refl _)

noncomputable def cplusBool_reduces : cplusBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam
    (N := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , (CNat ⇒ CNat ⇒ CNat)))
    (W := cplus) Value.vLam)
    (MultiStep.refl _)

noncomputable def «csuccBool_↠» : csuccBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  csuccBool_reduces

noncomputable def «csucc_↠» : csuccBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  csuccBool_reduces

noncomputable def «cplusBool_↠» : cplusBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  cplusBool_reduces

noncomputable def «cplus_↠» : cplusBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  cplusBool_reduces

------------------------------------------------------------------------
-- Encoded lists and pairs (ported core subset)
------------------------------------------------------------------------

def ListTy {Δ : TyCtx} (A : Ty Δ) : Ty Δ :=
  ∀ₜ ((renameT TyVar.S A ⇒ #TyVar.Z ⇒ #TyVar.Z) ⇒ #TyVar.Z ⇒ #TyVar.Z)

def nilTy : Ty ∅ :=
  ∀ₜ (ListTy (#TyVar.Z))

def nil : Closed nilTy :=
  Term.tlam
    (Term.tlam
      (Term.lam (#TyVar.S TyVar.Z ⇒ #TyVar.Z ⇒ #TyVar.Z)
        (Term.lam (#TyVar.Z)
          (Term.var HasVar.Z))))

def consTy : Ty ∅ :=
  ∀ₜ (#TyVar.Z ⇒ ListTy (#TyVar.Z) ⇒ ListTy (#TyVar.Z))

def cons : Closed consTy :=
  Term.tlam
    (Term.lam (#TyVar.Z)
      (Term.lam (ListTy (#TyVar.Z))
        (Term.tlam
          (Term.lam (#TyVar.S TyVar.Z ⇒ #TyVar.Z ⇒ #TyVar.Z)
            (Term.lam (#TyVar.Z)
              (Term.app
                (Term.app (Term.var (HasVar.S HasVar.Z)) (Term.var (HasVar.S (HasVar.S (HasVar.S HasVar.Z)))))
                (Term.app
                  (Term.app (Term.tapp (Term.var (HasVar.S (HasVar.S HasVar.Z))) (#TyVar.Z))
                    (Term.var (HasVar.S HasVar.Z)))
                  (Term.var HasVar.Z))))))))

def isnilTy : Ty ∅ :=
  ∀ₜ (ListTy (#TyVar.Z) ⇒ TBool)

def isnil : Closed isnilTy :=
  Term.tlam
    (Term.lam (ListTy (#TyVar.Z))
      (Term.app
        (Term.app
          (Term.tapp (Term.var HasVar.Z) TBool)
          (Term.lam (#TyVar.Z) (Term.lam TBool (Term.tfalse (Δ := ∅ ,α) (Γ := _))))
        )
        (Term.ttrue (Δ := ∅ ,α) (Γ := _))))

def nilIsNil : Closed TBool :=
  Term.app
    (Term.tapp isnil TBool)
    (Term.tapp nil TBool)

noncomputable def nilIsNilProgress : Progress nilIsNil :=
  progress nilIsNil

def evalBoolTag (fuel : Nat) (M : Closed TBool) : Option Bool :=
  match eval fuel M with
  | none => none
  | some r =>
      match r with
      | EvalResult.mk _ _ v =>
          match v with
          | Value.vTrue => some true
          | Value.vFalse => some false

noncomputable def nilIsNil_reduces :
    nilIsNil —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  have htag : evalBoolTag 8 nilIsNil = some true := by
    native_decide
  match hEval : eval 8 nilIsNil with
  | none =>
      have hnone : evalBoolTag 8 nilIsNil = none := by
        simp [evalBoolTag]
        simp [hEval]
      have : False := by
        have htag' := htag
        simp [hnone] at htag'
      exact False.elim this
  | some r =>
      cases r with
      | mk term tr v =>
          cases v with
          | vTrue =>
              exact tr
          | vFalse =>
              have hfalse : evalBoolTag 8 nilIsNil = some false := by
                simp [evalBoolTag]
                simp [hEval]
              have : False := by
                have htag' := htag
                simp [hfalse] at htag'
              exact False.elim this

noncomputable def «nilIsNil_↠» :
    nilIsNil —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  nilIsNil_reduces

noncomputable def «nil_↠» :
    nilIsNil —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  nilIsNil_reduces

noncomputable def «isnil_↠» :
    nilIsNil —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  nilIsNil_reduces

def consIsNil : Closed TBool :=
  Term.app
    (Term.lam consTy (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ , consTy)))
    cons

noncomputable def consIsNil_reduces : consIsNil —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam
    (N := Term.tfalse (Δ := ∅) (Γ := ∅ᶜ , consTy))
    (W := cons) Value.vTlam)
    (MultiStep.refl _)

noncomputable def consIsNilProgress : Progress consIsNil :=
  progress consIsNil

noncomputable def «consIsNil_↠» : consIsNil —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  consIsNil_reduces

noncomputable def «cons_↠» : consIsNil —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  consIsNil_reduces

def PairTy {Δ : TyCtx} (A B : Ty Δ) : Ty Δ :=
  ∀ₜ ((renameT TyVar.S A ⇒ renameT TyVar.S B ⇒ #TyVar.Z) ⇒ #TyVar.Z)

def pairTy : Ty ∅ :=
  ∀ₜ (∀ₜ (#TyVar.S TyVar.Z ⇒ #TyVar.Z ⇒ PairTy (#TyVar.S TyVar.Z) (#TyVar.Z)))

def pair : Closed pairTy :=
  Term.tlam
    (Term.tlam
      (Term.lam (#TyVar.S TyVar.Z)
        (Term.lam (#TyVar.Z)
          (Term.tlam
            (Term.lam (#TyVar.S (TyVar.S TyVar.Z) ⇒ #TyVar.S TyVar.Z ⇒ #TyVar.Z)
              (Term.app
                (Term.app (Term.var HasVar.Z) (Term.var (HasVar.S (HasVar.S HasVar.Z))))
                (Term.var (HasVar.S HasVar.Z))))))))

def fstTy : Ty ∅ :=
  ∀ₜ (∀ₜ (PairTy (#TyVar.S TyVar.Z) (#TyVar.Z) ⇒ #TyVar.S TyVar.Z))

def fst : Closed fstTy :=
  Term.tlam
    (Term.tlam
      (Term.lam (PairTy (#TyVar.S TyVar.Z) (#TyVar.Z))
        (Term.app
          (Term.tapp (Term.var HasVar.Z) (#TyVar.S TyVar.Z))
          (Term.lam (#TyVar.S TyVar.Z)
            (Term.lam (#TyVar.Z)
              (Term.var (HasVar.S HasVar.Z)))))))

def sndTy : Ty ∅ :=
  ∀ₜ (∀ₜ (PairTy (#TyVar.S TyVar.Z) (#TyVar.Z) ⇒ #TyVar.Z))

def snd : Closed sndTy :=
  Term.tlam
    (Term.tlam
      (Term.lam (PairTy (#TyVar.S TyVar.Z) (#TyVar.Z))
        (Term.app
          (Term.tapp (Term.var HasVar.Z) (#TyVar.Z))
          (Term.lam (#TyVar.S TyVar.Z)
            (Term.lam (#TyVar.Z)
              (Term.var HasVar.Z))))))

def pairBool : Closed TBool :=
  Term.app
    (Term.lam pairTy (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , pairTy)))
    pair

def fstBool : Closed TBool :=
  Term.app
    (Term.lam fstTy (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , fstTy)))
    fst

def sndBool : Closed TNat :=
  Term.app
    (Term.lam sndTy (Term.tzero (Δ := ∅) (Γ := ∅ᶜ , sndTy)))
    snd

noncomputable def pairBoolProgress : Progress pairBool :=
  progress pairBool

noncomputable def pairBool_reduces : pairBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam
    (N := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , pairTy))
    (W := pair) Value.vTlam)
    (MultiStep.refl _)

noncomputable def fstBoolProgress : Progress fstBool :=
  progress fstBool

noncomputable def fstBool_reduces : fstBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam
    (N := Term.ttrue (Δ := ∅) (Γ := ∅ᶜ , fstTy))
    (W := fst) Value.vTlam)
    (MultiStep.refl _)

noncomputable def sndBoolProgress : Progress sndBool :=
  progress sndBool

noncomputable def sndBool_reduces : sndBool —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam
    (N := Term.tzero (Δ := ∅) (Γ := ∅ᶜ , sndTy))
    (W := snd) Value.vTlam)
    (MultiStep.refl _)

noncomputable def «pairBool_↠» : pairBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  pairBool_reduces

noncomputable def «pair_↠» : pairBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  pairBool_reduces

noncomputable def «fstBool_↠» : fstBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  fstBool_reduces

noncomputable def «fst_↠» : fstBool —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  fstBool_reduces

noncomputable def «sndBool_↠» : sndBool —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  sndBool_reduces

noncomputable def «snd_↠» : sndBool —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  sndBool_reduces

------------------------------------------------------------------------
-- Coverage targets
------------------------------------------------------------------------

inductive Rule : Type where
  | r_xi_app1 : Rule
  | r_xi_app2 : Rule
  | r_beta_lam : Rule
  | r_xi_suc : Rule
  | r_xi_if : Rule
  | r_xi_case : Rule
  | r_beta_true : Rule
  | r_beta_false : Rule
  | r_beta_zero : Rule
  | r_beta_suc : Rule
  | r_xi_tapp : Rule
  | r_beta_tlam : Rule

inductive ExampleId : Type where
  | ex_xi_app1_id : ExampleId
  | ex_xi_app2_id : ExampleId
  | ex_beta_lam_id : ExampleId
  | ex_xi_suc_id : ExampleId
  | ex_xi_if_id : ExampleId
  | ex_xi_case_id : ExampleId
  | ex_beta_true_id : ExampleId
  | ex_beta_false_id : ExampleId
  | ex_beta_zero_id : ExampleId
  | ex_beta_suc_id : ExampleId
  | ex_xi_tapp_id : ExampleId
  | ex_beta_tlam_id : ExampleId

def coverage : Rule → ExampleId
  | .r_xi_app1 => .ex_xi_app1_id
  | .r_xi_app2 => .ex_xi_app2_id
  | .r_beta_lam => .ex_beta_lam_id
  | .r_xi_suc => .ex_xi_suc_id
  | .r_xi_if => .ex_xi_if_id
  | .r_xi_case => .ex_xi_case_id
  | .r_beta_true => .ex_beta_true_id
  | .r_beta_false => .ex_beta_false_id
  | .r_beta_zero => .ex_beta_zero_id
  | .r_beta_suc => .ex_beta_suc_id
  | .r_xi_tapp => .ex_xi_tapp_id
  | .r_beta_tlam => .ex_beta_tlam_id

------------------------------------------------------------------------
-- Coverage example terms and traces
------------------------------------------------------------------------

def boolId : Closed (TBool ⇒ TBool) :=
  Term.lam TBool (Term.var HasVar.Z)

def ex_xi_app1 : Closed TBool :=
  Term.app
    (Term.tite (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) boolId boolId)
    (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def ex_xi_app1_reduces : ex_xi_app1 —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.xiApp1 Step.betaTrue)
    (MultiStep.step _ (Step.betaLam (N := Term.var HasVar.Z) (W := Term.ttrue) Value.vTrue)
      (MultiStep.refl _))

noncomputable def «ex_xi_app1_↠» : ex_xi_app1 —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_xi_app1_reduces

def ex_xi_app2 : Closed TBool :=
  Term.app
    boolId
    (Term.tite (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)))

noncomputable def ex_xi_app2_reduces : ex_xi_app2 —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.xiApp2 Value.vLam Step.betaFalse)
    (MultiStep.step _ (Step.betaLam (N := Term.var HasVar.Z) (W := Term.tfalse) Value.vFalse)
      (MultiStep.refl _))

noncomputable def «ex_xi_app2_↠» : ex_xi_app2 —↠ (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_xi_app2_reduces

def ex_beta_lam : Closed TBool :=
  Term.app boolId (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def ex_beta_lam_reduces : ex_beta_lam —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.betaLam (N := Term.var HasVar.Z) (W := Term.ttrue) Value.vTrue)
    (MultiStep.refl _)

noncomputable def «ex_beta_lam_↠» : ex_beta_lam —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_beta_lam_reduces

def ex_xi_suc : Closed TNat :=
  Term.tsuc
    (Term.tite (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))

def ex_xi_suc_reduces : ex_xi_suc —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  MultiStep.step _ (Step.xiSuc Step.betaFalse)
    (MultiStep.refl _)

def «ex_xi_suc_↠» : ex_xi_suc —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  ex_xi_suc_reduces

def ex_xi_if : Closed TNat :=
  Term.tite
    (Term.tite (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
      (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)))
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))

def ex_xi_if_reduces : ex_xi_if —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  MultiStep.step _ (Step.xiIf Step.betaTrue)
    (MultiStep.step _ Step.betaFalse
      (MultiStep.refl _))

def «ex_xi_if_↠» : ex_xi_if —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  ex_xi_if_reduces

def ex_xi_case : Closed TNat :=
  Term.tcaseNat
    (Term.tite (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
      (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tsuc (Term.var HasVar.Z))

def ex_xi_case_reduces : ex_xi_case —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ (Step.xiCaseNat Step.betaTrue)
    (MultiStep.step _ Step.betaZero
      (MultiStep.refl _))

def «ex_xi_case_↠» : ex_xi_case —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_xi_case_reduces

def ex_beta_true : Closed TNat :=
  Term.tite
    (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))

def ex_beta_true_reduces : ex_beta_true —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ Step.betaTrue
    (MultiStep.refl _)

def «ex_beta_true_↠» : ex_beta_true —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_beta_true_reduces

def ex_beta_false : Closed TNat :=
  Term.tite
    (Term.tfalse (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))

def ex_beta_false_reduces : ex_beta_false —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  MultiStep.step _ Step.betaFalse
    (MultiStep.refl _)

def «ex_beta_false_↠» : ex_beta_false —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  ex_beta_false_reduces

def ex_beta_zero : Closed TNat :=
  Term.tcaseNat
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tsuc (Term.var HasVar.Z))

def ex_beta_zero_reduces : ex_beta_zero —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  MultiStep.step _ Step.betaZero
    (MultiStep.refl _)

def «ex_beta_zero_↠» : ex_beta_zero —↠ (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_beta_zero_reduces

def ex_beta_suc : Closed TNat :=
  Term.tcaseNat
    (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ)))
    (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))
    (Term.tsuc (Term.var HasVar.Z))

noncomputable def ex_beta_suc_reduces : ex_beta_suc —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))) :=
  MultiStep.step _ (Step.betaSuc (V := Term.tzero) (M := Term.tzero) (N := Term.tsuc (Term.var HasVar.Z)) Value.vZero)
    (MultiStep.refl _)

noncomputable def «ex_beta_suc_↠» : ex_beta_suc —↠ (Term.tsuc (Term.tzero (Δ := ∅) (Γ := ∅ᶜ))):=
  ex_beta_suc_reduces

def ex_xi_tapp : Closed TBool :=
  Term.app
    (Term.tapp
      (Term.tite (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) polyId polyId)
      TBool)
    (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def ex_xi_tapp_reduces :
    ex_xi_tapp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  exact multiTrans
    (MultiStep.step _ (Step.xiApp1 (Step.xiTapp Step.betaTrue))
      (MultiStep.step _ (Step.xiApp1 (Step.betaTlam (N := Term.lam (#TyVar.Z) (Term.var HasVar.Z)) (B := TBool)))
        (MultiStep.refl _)))
    polyIdInstAppTrue_reduces

noncomputable def «ex_xi_tapp_↠» : ex_xi_tapp —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_xi_tapp_reduces

def ex_beta_tlam : Closed TBool :=
  Term.app
    (Term.tapp polyId TBool)
    (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ))

noncomputable def ex_beta_tlam_reduces :
    ex_beta_tlam —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) := by
  unfold ex_beta_tlam
  simpa using polyIdBool_reduces

noncomputable def «ex_beta_tlam_↠» : ex_beta_tlam —↠ (Term.ttrue (Δ := ∅) (Γ := ∅ᶜ)) :=
  ex_beta_tlam_reduces

end Intrinsic

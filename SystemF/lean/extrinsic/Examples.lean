import extrinsic.Eval

namespace Extrinsic

-- A focused subset of the Agda `extrinsic/Examples.agda` corpus.

def wfBool : WfTy 0 𝔹 := .bool

def wfNat : WfTy 0 ℕ := .nat

def wfTy0 : WfTy 1 (#0) := .var (Nat.zero_lt_succ 0)

def wfTy0_to_ty0 : WfTy 1 (#0 ⇒ #0) := .fn wfTy0 wfTy0

def polyId : Term :=
  Term.tlam (Term.lam (#0) (Term.var 0))

def polyId_typed : 0 ⊢ [] ⊢ polyId ⦂ (∀ₜ (#0 ⇒ #0)) := by
  refine .t_tlam ?_
  exact .t_lam wfTy0 (.t_var .Z)

def polyIdBool : Term :=
  Term.app (Term.tapp polyId 𝔹) Term.ttrue

def polyIdBool_typed : 0 ⊢ [] ⊢ polyIdBool ⦂ 𝔹 := by
  refine .t_app ?_ .t_true
  exact .t_tapp polyId_typed wfBool

def polyIdBool_reduces : polyIdBool —↠ Term.ttrue := by
  exact
    MultiStep.step _ (Step.xi_app₁ (Step.beta_tlam (A := 𝔹)))
      (MultiStep.step _ (Step.beta_lam Value.vTrue) (MultiStep.refl _))

def succFn : Term :=
  Term.lam ℕ (Term.suc (Term.var 0))

def succFn_typed : 0 ⊢ [] ⊢ succFn ⦂ (ℕ ⇒ ℕ) := by
  refine .t_lam wfNat ?_
  exact .t_suc (.t_var .Z)

def succFnOnZero : Term :=
  Term.app succFn Term.zero

def succFnOnZero_typed : 0 ⊢ [] ⊢ succFnOnZero ⦂ ℕ := by
  exact .t_app succFn_typed .t_zero

def one : Term := Term.suc Term.zero

def one_typed : 0 ⊢ [] ⊢ one ⦂ ℕ := .t_suc .t_zero

def two : Term := Term.suc one

def two_typed : 0 ⊢ [] ⊢ two ⦂ ℕ := .t_suc one_typed

def three : Term := Term.suc two

def three_typed : 0 ⊢ [] ⊢ three ⦂ ℕ := .t_suc two_typed

def four : Term := Term.suc (Term.suc two)

def four_typed : 0 ⊢ [] ⊢ four ⦂ ℕ := .t_suc (.t_suc two_typed)

def succFnOnZero_reduces : succFnOnZero —↠ one := by
  exact MultiStep.step _ (Step.beta_lam Value.vZero) (MultiStep.refl _)

def idBool : Term := Term.app (Term.tapp polyId 𝔹) Term.ttrue

def idBool_typed : 0 ⊢ [] ⊢ idBool ⦂ 𝔹 := polyIdBool_typed

def idBool_reduces : idBool —↠ Term.ttrue := polyIdBool_reduces

-- TAPL-style polymorphic constant: Λ.Λ.λx:1.λy:0.x
def taplConst : Term :=
  Term.tlam (Term.tlam (Term.lam (#1) (Term.lam (#0) (Term.var 1))))

def wfTy0_2 : WfTy 2 (#0) := .var (Nat.zero_lt_succ 1)

def wfTy1_2 : WfTy 2 (#1) := .var (Nat.succ_lt_succ (Nat.zero_lt_succ 0))

def taplConst_typed : 0 ⊢ [] ⊢ taplConst ⦂ (∀ₜ (∀ₜ (#1 ⇒ #0 ⇒ #1))) := by
  refine .t_tlam ?_
  refine .t_tlam ?_
  refine .t_lam wfTy1_2 ?_
  refine .t_lam wfTy0_2 ?_
  exact .t_var (.S .Z)

def taplConstApp : Term :=
  Term.app (Term.app (Term.tapp (Term.tapp taplConst 𝔹) ℕ) Term.ttrue) Term.zero

def taplConstApp_typed : 0 ⊢ [] ⊢ taplConstApp ⦂ 𝔹 := by
  have hTapBool : 0 ⊢ [] ⊢ (Term.tapp taplConst 𝔹) ⦂ (∀ₜ (𝔹 ⇒ #0 ⇒ 𝔹)) := by
    exact .t_tapp (A := (∀ₜ (#1 ⇒ #0 ⇒ #1))) taplConst_typed wfBool
  have hTapNat : 0 ⊢ [] ⊢ (Term.tapp (Term.tapp taplConst 𝔹) ℕ) ⦂ (𝔹 ⇒ ℕ ⇒ 𝔹) := by
    exact .t_tapp (A := (𝔹 ⇒ #0 ⇒ 𝔹)) hTapBool wfNat
  refine .t_app ?_ .t_zero
  refine .t_app ?_ .t_true
  exact hTapNat

def taplConstApp_reduces : taplConstApp —↠ Term.ttrue := by
  exact
    MultiStep.step _ (Step.xi_app₁ (Step.xi_app₁ (Step.xi_tapp (Step.beta_tlam (A := 𝔹)))))
      (MultiStep.step _ (Step.xi_app₁ (Step.xi_app₁ (Step.beta_tlam (A := ℕ))))
        (MultiStep.step _ (Step.xi_app₁ (Step.beta_lam Value.vTrue))
          (MultiStep.step _ (Step.beta_lam Value.vZero) (MultiStep.refl _))))

def CBool : Ty := ∀ₜ (#0 ⇒ #0 ⇒ #0)

def tru : Term := Term.tlam (Term.lam (#0) (Term.lam (#0) (Term.var 1)))

def fls : Term := Term.tlam (Term.lam (#0) (Term.lam (#0) (Term.var 0)))

def tru_typed : 0 ⊢ [] ⊢ tru ⦂ CBool := by
  refine .t_tlam ?_
  refine .t_lam wfTy0 ?_
  refine .t_lam wfTy0 ?_
  exact .t_var (.S .Z)

def fls_typed : 0 ⊢ [] ⊢ fls ⦂ CBool := by
  refine .t_tlam ?_
  refine .t_lam wfTy0 ?_
  refine .t_lam wfTy0 ?_
  exact .t_var .Z

def flsBool : Term :=
  Term.app (Term.app (Term.tapp fls 𝔹) Term.ttrue) Term.tfalse

def flsBool_typed : 0 ⊢ [] ⊢ flsBool ⦂ 𝔹 := by
  refine .t_app ?_ .t_false
  refine .t_app ?_ .t_true
  exact .t_tapp fls_typed wfBool

def flsBool_reduces : flsBool —↠ Term.tfalse := by
  exact
    MultiStep.step _ (Step.xi_app₁ (Step.xi_app₁ (Step.beta_tlam (A := 𝔹))))
      (MultiStep.step _ (Step.xi_app₁ (Step.beta_lam Value.vTrue))
        (MultiStep.step _ (Step.beta_lam Value.vFalse) (MultiStep.refl _)))

def truBool : Term :=
  Term.app (Term.app (Term.tapp tru 𝔹) Term.ttrue) Term.tfalse

def truBool_typed : 0 ⊢ [] ⊢ truBool ⦂ 𝔹 := by
  refine .t_app ?_ .t_false
  refine .t_app ?_ .t_true
  exact .t_tapp tru_typed wfBool

def truBool_reduces : truBool —↠ Term.ttrue := by
  exact
    MultiStep.step _ (Step.xi_app₁ (Step.xi_app₁ (Step.beta_tlam (A := 𝔹))))
      (MultiStep.step _ (Step.xi_app₁ (Step.beta_lam Value.vTrue))
        (MultiStep.step _ (Step.beta_lam Value.vFalse) (MultiStep.refl _)))

end Extrinsic

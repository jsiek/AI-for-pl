import extrinsic.Preservation

namespace Extrinsic

def wfBool : WfTy 0 .bool := .bool
def wfNat : WfTy 0 .nat := .nat
def wfTy0 : WfTy 1 (.var 0) := .var (Nat.zero_lt_succ 0)
def wfTy0_fn_ty0 : WfTy 1 ((.var 0) ⇒ (.var 0)) := .fn wfTy0 wfTy0

def polyId : Term := .tlam (.lam (.var 0))

def polyId_hasType : HasType 0 [] polyId (.all ((.var 0) ⇒ (.var 0))) :=
  .t_tlam (.t_lam wfTy0 (.t_var .Z))

def polyIdBool : Term := (.app (.tapp polyId) .ttrue)

def polyIdBool_hasType : HasType 0 [] polyIdBool .bool :=
  .t_app
    (.t_tapp (M := polyId) (A := (.var 0 ⇒ .var 0)) (B := .bool) polyId_hasType wfBool)
    .t_true

def polyIdBool_reduces : polyIdBool —↠ .ttrue :=
  .step _ (.xi_app₁ .beta_tlam)
    (.step _ (.beta_lam .vTrue) (.refl _))

def one : Term := .suc .zero
def one_hasType : HasType 0 [] one .nat := .t_suc .t_zero
def one_reduces : one —↠ one := .refl _

def two : Term := .suc one
def two_hasType : HasType 0 [] two .nat := .t_suc one_hasType
def two_reduces : two —↠ two := .refl _

def four : Term := .suc (.suc two)
def four_hasType : HasType 0 [] four .nat := .t_suc (.t_suc two_hasType)
def four_reduces : four —↠ four := .refl _

def succFn : Term := .lam (.suc (.var 0))
def succFn_hasType : HasType 0 [] succFn (.nat ⇒ .nat) :=
  .t_lam wfNat (.t_suc (.t_var .Z))

def succFnOnZero : Term := .app succFn .zero
def succFnOnZero_hasType : HasType 0 [] succFnOnZero .nat :=
  .t_app succFn_hasType .t_zero

def succFnOnZero_reduces : succFnOnZero —↠ one :=
  .step _ (.beta_lam .vZero) (.refl _)

def taplConst : Term := .tlam (.tlam (.lam (.lam (.var 1))))
def taplConstTy : Ty := .all (.all ((.var 1) ⇒ (.var 0) ⇒ (.var 1)))

def taplConst_hasType : HasType 0 [] taplConst taplConstTy :=
  .t_tlam
    (.t_tlam
      (.t_lam (.var (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))
        (.t_lam (.var (Nat.zero_lt_succ 1))
          (.t_var (.S .Z)))))

def taplConstApp : Term :=
  .app (.app (.tapp (.tapp taplConst)) .ttrue) .zero

def taplConstApp_hasType : HasType 0 [] taplConstApp .bool :=
  .t_app
    (.t_app
      (.t_tapp
        (.t_tapp taplConst_hasType wfBool)
        wfNat)
      .t_true)
    .t_zero

def taplConstApp_reduces : taplConstApp —↠ .ttrue :=
  .step _ (.xi_app₁ (.xi_app₁ (.xi_tapp .beta_tlam)))
    (.step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
      (.step _ (.xi_app₁ (.beta_lam .vTrue))
        (.step _ (.beta_lam .vZero) (.refl _))))

def double : Term := .tlam (.lam (.lam (.app (.var 1) (.app (.var 1) (.var 0)))))
def doubleTy : Ty := .all (((.var 0) ⇒ (.var 0)) ⇒ (.var 0) ⇒ (.var 0))

def double_hasType : HasType 0 [] double doubleTy :=
  .t_tlam
    (.t_lam wfTy0_fn_ty0
      (.t_lam wfTy0
        (.t_app
          (.t_var (.S .Z))
          (.t_app (.t_var (.S .Z)) (.t_var .Z)))))

def doubleOnSuccZero : Term := .app (.app (.tapp double) succFn) .zero
def doubleOnSuccZero_hasType : HasType 0 [] doubleOnSuccZero .nat :=
  .t_app
    (.t_app
      (.t_tapp double_hasType wfNat)
      succFn_hasType)
    .t_zero

def doubleOnSuccZero_reduces : doubleOnSuccZero —↠ two :=
  .step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
    (.step _ (.xi_app₁ (.beta_lam .vLam))
      (.step _ (.beta_lam .vZero)
        (.step _ (.xi_app₂ .vLam (.beta_lam .vZero))
          (.step _ (.beta_lam (.vSuc .vZero)) (.refl _)))))

end Extrinsic

import curry.Preservation

namespace Curry

------------------------------------------------------------------------
-- Small reusable typing helpers
------------------------------------------------------------------------

def wfBool : WfTy 0 𝔹 := .bool

def wfNat : WfTy 0 ℕ := .nat

def wfTy0 : WfTy 1 (#0) := .var (Nat.zero_lt_succ 0)

def wfTy0_fn_ty0 : WfTy 1 ((#0) ⇒ (#0)) := .fn wfTy0 wfTy0

def «wfTy0⇒Ty0» : WfTy 1 ((#0) ⇒ (#0)) := wfTy0_fn_ty0

------------------------------------------------------------------------
-- Source-inspired seed examples
------------------------------------------------------------------------

def polyId : Term := Λ (ƛ (ˋ0))

def polyId_hasType : 0 ⊢ [] ⊢ polyId ⦂ (∀ₜ ((#0) ⇒ (#0))) :=
  .t_tlam (.t_lam wfTy0 (.t_var .Z))

def «polyId_⊢» : 0 ⊢ [] ⊢ polyId ⦂ (∀ₜ ((#0) ⇒ (#0))) :=
  polyId_hasType

def polyIdBool : Term := ((polyId ∙[]) ∙ ˋtrue)

def polyIdBool_hasType : 0 ⊢ [] ⊢ polyIdBool ⦂ 𝔹 :=
  .t_app
    (.t_tapp (M := polyId) (A := (.var 0 ⇒ .var 0)) (B := .bool) polyId_hasType wfBool)
    .t_true

def «polyIdBool_⊢» : 0 ⊢ [] ⊢ polyIdBool ⦂ 𝔹 :=
  polyIdBool_hasType

def polyIdBool_reduces : polyIdBool —↠ ˋtrue :=
  .step _ (.xi_app₁ .beta_tlam)
    (.step _ (.beta_lam .vTrue) (.refl _))

def «polyIdBool_↠» : polyIdBool —↠ ˋtrue :=
  polyIdBool_reduces

def «polyId_↠» : polyIdBool —↠ ˋtrue :=
  polyIdBool_reduces

------------------------------------------------------------------------
-- TAPL-inspired examples
------------------------------------------------------------------------

def wfTy0₂ : WfTy 2 (#0) :=
  .var (Nat.zero_lt_succ 1)

def wfTy1₂ : WfTy 2 (#1) :=
  .var (Nat.succ_lt_succ (Nat.zero_lt_succ 0))

def wfTy0₃ : WfTy 3 (#0) :=
  .var (Nat.zero_lt_succ 2)

def wfTy1₃ : WfTy 3 (#1) :=
  .var (Nat.succ_lt_succ (Nat.zero_lt_succ 1))

def wfTy2₃ : WfTy 3 (#2) :=
  .var (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))

def one : Term := ˋsuc ˋzero

def one_hasType : 0 ⊢ [] ⊢ one ⦂ ℕ :=
  .t_suc .t_zero

def «one_⊢» : 0 ⊢ [] ⊢ one ⦂ ℕ :=
  one_hasType

def one_reduces : one —↠ one :=
  .refl _

def «one_↠» : one —↠ one :=
  one_reduces

def two : Term := ˋsuc one

def two_hasType : 0 ⊢ [] ⊢ two ⦂ ℕ :=
  .t_suc one_hasType

def «two_⊢» : 0 ⊢ [] ⊢ two ⦂ ℕ :=
  two_hasType

def two_reduces : two —↠ two :=
  .refl _

def «two_↠» : two —↠ two :=
  two_reduces

def four : Term := ˋsuc (ˋsuc two)

def four_hasType : 0 ⊢ [] ⊢ four ⦂ ℕ :=
  .t_suc (.t_suc two_hasType)

def «four_⊢» : 0 ⊢ [] ⊢ four ⦂ ℕ :=
  four_hasType

def four_reduces : four —↠ four :=
  .refl _

def «four_↠» : four —↠ four :=
  four_reduces

def succFn : Term := ƛ (ˋsuc (ˋ0))

def succFn_hasType : 0 ⊢ [] ⊢ succFn ⦂ (ℕ ⇒ ℕ) :=
  .t_lam wfNat (.t_suc (.t_var .Z))

def «succFn_⊢» : 0 ⊢ [] ⊢ succFn ⦂ (ℕ ⇒ ℕ) :=
  succFn_hasType

def succFnOnZero : Term := (succFn ∙ ˋzero)

def succFnOnZero_hasType : 0 ⊢ [] ⊢ succFnOnZero ⦂ ℕ :=
  .t_app succFn_hasType .t_zero

def «succFnOnZero_⊢» : 0 ⊢ [] ⊢ succFnOnZero ⦂ ℕ :=
  succFnOnZero_hasType

def succFnOnZero_reduces : succFnOnZero —↠ one :=
  .step _ (.beta_lam .vZero) (.refl _)

def «succFnOnZero_↠» : succFnOnZero —↠ one :=
  succFnOnZero_reduces

def «succFn_↠» : succFnOnZero —↠ one :=
  succFnOnZero_reduces

------------------------------------------------------------------------
-- TAPL combinators
------------------------------------------------------------------------

def identity : Term :=
  polyId

def id_hasType : 0 ⊢ [] ⊢ identity ⦂ (∀ₜ ((#0) ⇒ (#0))) :=
  polyId_hasType

def «id_⊢» : 0 ⊢ [] ⊢ identity ⦂ (∀ₜ ((#0) ⇒ (#0))) :=
  id_hasType

def idBool : Term :=
  ((identity ∙[]) ∙ ˋtrue)

def idBool_hasType : 0 ⊢ [] ⊢ idBool ⦂ 𝔹 :=
  .t_app
    (.t_tapp (M := identity) (A := (.var 0 ⇒ .var 0)) (B := .bool) id_hasType wfBool)
    .t_true

def «idBool_⊢» : 0 ⊢ [] ⊢ idBool ⦂ 𝔹 :=
  idBool_hasType

def idBool_reduces : idBool —↠ ˋtrue :=
  .step _ (.xi_app₁ .beta_tlam)
    (.step _ (.beta_lam .vTrue) (.refl _))

def «idBool_↠» : idBool —↠ ˋtrue :=
  idBool_reduces

def «id_↠» : idBool —↠ ˋtrue :=
  idBool_reduces

def taplConst : Term :=
  Λ (Λ (ƛ (ƛ (ˋ1))))

def taplConstTy : Ty :=
  ∀ₜ (∀ₜ (#1 ⇒ #0 ⇒ #1))

def taplConst_hasType : 0 ⊢ [] ⊢ taplConst ⦂ taplConstTy :=
  .t_tlam
    (.t_tlam
      (.t_lam wfTy1₂
        (.t_lam wfTy0₂
          (.t_var (.S .Z)))))

def «taplConst_⊢» : 0 ⊢ [] ⊢ taplConst ⦂ taplConstTy :=
  taplConst_hasType

def taplConstApp : Term :=
  ((((taplConst ∙[]) ∙[]) ∙ ˋtrue) ∙ ˋzero)

def taplConstApp_hasType : 0 ⊢ [] ⊢ taplConstApp ⦂ 𝔹 :=
  .t_app
    (.t_app
      (.t_tapp
        (.t_tapp taplConst_hasType wfBool)
        wfNat)
      .t_true)
    .t_zero

def «taplConstApp_⊢» : 0 ⊢ [] ⊢ taplConstApp ⦂ 𝔹 :=
  taplConstApp_hasType

def taplConstApp_reduces : taplConstApp —↠ ˋtrue :=
  .step _ (.xi_app₁ (.xi_app₁ (.xi_tapp .beta_tlam)))
    (.step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
      (.step _ (.xi_app₁ (.beta_lam .vTrue))
        (.step _ (.beta_lam .vZero) (.refl _))))

def «taplConstApp_↠» : taplConstApp —↠ ˋtrue :=
  taplConstApp_reduces

def «taplConst_↠» : taplConstApp —↠ ˋtrue :=
  taplConstApp_reduces

def double : Term :=
  Λ (ƛ (ƛ (ˋ1 ∙ (ˋ1 ∙ ˋ0))))

def doubleTy : Ty :=
  ∀ₜ ((#0 ⇒ #0) ⇒ #0 ⇒ #0)

def double_hasType : 0 ⊢ [] ⊢ double ⦂ doubleTy :=
  .t_tlam
    (.t_lam wfTy0_fn_ty0
      (.t_lam wfTy0
        (.t_app
          (.t_var (.S .Z))
          (.t_app (.t_var (.S .Z)) (.t_var .Z)))))

def «double_⊢» : 0 ⊢ [] ⊢ double ⦂ doubleTy :=
  double_hasType

def doubleOnSuccZero : Term :=
  (((double ∙[]) ∙ succFn) ∙ ˋzero)

def doubleOnSuccZero_hasType : 0 ⊢ [] ⊢ doubleOnSuccZero ⦂ ℕ :=
  .t_app
    (.t_app
      (.t_tapp double_hasType wfNat)
      succFn_hasType)
    .t_zero

def «doubleOnSuccZero_⊢» : 0 ⊢ [] ⊢ doubleOnSuccZero ⦂ ℕ :=
  doubleOnSuccZero_hasType

def doubleOnSuccZero_reduces : doubleOnSuccZero —↠ two :=
  .step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
    (.step _ (.xi_app₁ (.beta_lam .vLam))
      (.step _ (.beta_lam .vZero)
        (.step _ (.xi_app₂ .vLam (.beta_lam .vZero))
          (.step _ (.beta_lam (.vSuc .vZero)) (.refl _)))))

def «doubleOnSuccZero_↠» : doubleOnSuccZero —↠ two :=
  doubleOnSuccZero_reduces

def «double_↠» : doubleOnSuccZero —↠ two :=
  doubleOnSuccZero_reduces

def selfApp : Term :=
  ((((identity ∙[]) ∙ identity) ∙[]) ∙ ˋtrue)

def wfPolyIdTy : WfTy 0 (∀ₜ ((#0) ⇒ (#0))) :=
  .all (.fn wfTy0 wfTy0)

def selfApp_hasType : 0 ⊢ [] ⊢ selfApp ⦂ 𝔹 :=
  .t_app
    (.t_tapp (B := .bool)
      (.t_app
        (.t_tapp (B := (.all ((.var 0) ⇒ (.var 0)))) id_hasType wfPolyIdTy)
        id_hasType)
      wfBool)
    .t_true

def «selfApp_⊢» : 0 ⊢ [] ⊢ selfApp ⦂ 𝔹 :=
  selfApp_hasType

def selfApp_reduces : selfApp —↠ ˋtrue :=
  .step _ (.xi_app₁ (.xi_tapp (.xi_app₁ .beta_tlam)))
    (.step _ (.xi_app₁ (.xi_tapp (.beta_lam .vTlam)))
      (.step _ (.xi_app₁ .beta_tlam)
        (.step _ (.beta_lam .vTrue) (.refl _))))

def «selfApp_↠» : selfApp —↠ ˋtrue :=
  selfApp_reduces

def quadruple : Term :=
  (((double ∙[]) ∙ succFn) ∙ two)

def three : Term :=
  ˋsuc two

def three_hasType : 0 ⊢ [] ⊢ three ⦂ ℕ :=
  .t_suc two_hasType

def «three_⊢» : 0 ⊢ [] ⊢ three ⦂ ℕ :=
  three_hasType

def three_reduces : three —↠ three :=
  .refl _

def «three_↠» : three —↠ three :=
  three_reduces

def quadruple_hasType : 0 ⊢ [] ⊢ quadruple ⦂ ℕ :=
  .t_app
    (.t_app
      (.t_tapp double_hasType wfNat)
      succFn_hasType)
    two_hasType

def «quadruple_⊢» : 0 ⊢ [] ⊢ quadruple ⦂ ℕ :=
  quadruple_hasType

def quadruple_reduces : quadruple —↠ four :=
  .step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
    (.step _ (.xi_app₁ (.beta_lam .vLam))
      (.step _ (.beta_lam (.vSuc (.vSuc .vZero)))
        (.step _ (.xi_app₂ .vLam (.beta_lam (.vSuc (.vSuc .vZero))))
          (.step _ (.beta_lam (.vSuc (.vSuc (.vSuc .vZero)))) (.refl _)))))

def «quadruple_↠» : quadruple —↠ four :=
  quadruple_reduces

------------------------------------------------------------------------
-- Church booleans and naturals
------------------------------------------------------------------------

def CBool : Ty :=
  ∀ₜ (#0 ⇒ #0 ⇒ #0)

def tru : Term :=
  Λ (ƛ (ƛ (ˋ1)))

def fls : Term :=
  Λ (ƛ (ƛ (ˋ0)))

def tru_hasType : 0 ⊢ [] ⊢ tru ⦂ CBool :=
  .t_tlam (.t_lam wfTy0 (.t_lam wfTy0 (.t_var (.S .Z))))

def «tru_⊢» : 0 ⊢ [] ⊢ tru ⦂ CBool :=
  tru_hasType

def fls_hasType : 0 ⊢ [] ⊢ fls ⦂ CBool :=
  .t_tlam (.t_lam wfTy0 (.t_lam wfTy0 (.t_var .Z)))

def «fls_⊢» : 0 ⊢ [] ⊢ fls ⦂ CBool :=
  fls_hasType

def flsBool : Term :=
  (((fls ∙[]) ∙ ˋtrue) ∙ ˋfalse)

def flsBool_hasType : 0 ⊢ [] ⊢ flsBool ⦂ 𝔹 :=
  .t_app
    (.t_app
      (.t_tapp (A := ((.var 0) ⇒ (.var 0) ⇒ (.var 0))) (B := .bool) fls_hasType wfBool)
      .t_true)
    .t_false

def «flsBool_⊢» : 0 ⊢ [] ⊢ flsBool ⦂ 𝔹 :=
  flsBool_hasType

def flsBool_reduces : flsBool —↠ ˋfalse :=
  .step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
    (.step _ (.xi_app₁ (.beta_lam .vTrue))
      (.step _ (.beta_lam .vFalse) (.refl _)))

def «flsBool_↠» : flsBool —↠ ˋfalse :=
  flsBool_reduces

def «fls_↠» : flsBool —↠ ˋfalse :=
  flsBool_reduces

def truBool : Term :=
  (((tru ∙[]) ∙ ˋtrue) ∙ ˋfalse)

def truBool_hasType : 0 ⊢ [] ⊢ truBool ⦂ 𝔹 :=
  .t_app
    (.t_app
      (.t_tapp (A := ((.var 0) ⇒ (.var 0) ⇒ (.var 0))) (B := .bool) tru_hasType wfBool)
      .t_true)
    .t_false

def «truBool_⊢» : 0 ⊢ [] ⊢ truBool ⦂ 𝔹 :=
  truBool_hasType

def truBool_reduces : truBool —↠ ˋtrue :=
  .step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
    (.step _ (.xi_app₁ (.beta_lam .vTrue))
      (.step _ (.beta_lam .vFalse) (.refl _)))

def «truBool_↠» : truBool —↠ ˋtrue :=
  truBool_reduces

def «tru_↠» : truBool —↠ ˋtrue :=
  truBool_reduces

def CNat : Ty :=
  ∀ₜ ((#0 ⇒ #0) ⇒ #0 ⇒ #0)

def CNatBody : Ty :=
  (#0 ⇒ #0) ⇒ #0 ⇒ #0

def wfCNat : WfTy 0 CNat :=
  .all (.fn (.fn wfTy0 wfTy0) (.fn wfTy0 wfTy0))

def c0 : Term :=
  Λ (ƛ (ƛ (ˋ0)))

def c0_hasType : 0 ⊢ [] ⊢ c0 ⦂ CNat :=
  .t_tlam (.t_lam wfTy0_fn_ty0 (.t_lam wfTy0 (.t_var .Z)))

def «c0_⊢» : 0 ⊢ [] ⊢ c0 ⦂ CNat :=
  c0_hasType

def c1 : Term :=
  Λ (ƛ (ƛ (((ˋ1) ∙ (ˋ0)))))

def c1_hasType : 0 ⊢ [] ⊢ c1 ⦂ CNat :=
  .t_tlam
    (.t_lam wfTy0_fn_ty0
      (.t_lam wfTy0
        (.t_app (.t_var (.S .Z)) (.t_var .Z))))

def «c1_⊢» : 0 ⊢ [] ⊢ c1 ⦂ CNat :=
  c1_hasType

def c2 : Term :=
  Λ (ƛ (ƛ (ˋ1 ∙ (ˋ1 ∙ ˋ0))))

def c2_hasType : 0 ⊢ [] ⊢ c2 ⦂ CNat :=
  .t_tlam
    (.t_lam wfTy0_fn_ty0
      (.t_lam wfTy0
        (.t_app
          (.t_var (.S .Z))
          (.t_app (.t_var (.S .Z)) (.t_var .Z)))))

def «c2_⊢» : 0 ⊢ [] ⊢ c2 ⦂ CNat :=
  c2_hasType

def csucc : Term :=
  ƛ (Λ (ƛ (ƛ (ˋ1 ∙ (((ˋ2 ∙[]) ∙ ˋ1) ∙ ˋ0)))))

def csucc_hasType : 0 ⊢ [] ⊢ csucc ⦂ (CNat ⇒ CNat) :=
  .t_lam wfCNat
    (.t_tlam
      (.t_lam wfTy0_fn_ty0
        (.t_lam wfTy0
          (.t_app
            (.t_var (.S .Z))
            (.t_app
              (.t_app
                (.t_tapp (A := CNatBody) (B := .var 0) (.t_var (.S (.S .Z))) wfTy0)
                (.t_var (.S .Z)))
              (.t_var .Z))))))

def «csucc_⊢» : 0 ⊢ [] ⊢ csucc ⦂ (CNat ⇒ CNat) :=
  csucc_hasType

def cplus : Term :=
  ƛ (ƛ
    (Λ (ƛ (ƛ
      (((ˋ3 ∙[]) ∙ ˋ1) ∙ (((ˋ2 ∙[]) ∙ ˋ1) ∙ ˋ0))))))

def cplus_hasType : 0 ⊢ [] ⊢ cplus ⦂ (CNat ⇒ CNat ⇒ CNat) :=
  .t_lam wfCNat
    (.t_lam wfCNat
      (.t_tlam
        (.t_lam wfTy0_fn_ty0
          (.t_lam wfTy0
            (.t_app
              (.t_app
                (.t_tapp (A := CNatBody) (B := .var 0)
                  (.t_var (.S (.S (.S .Z))))
                  wfTy0)
                (.t_var (.S .Z)))
              (.t_app
                (.t_app
                  (.t_tapp (A := CNatBody) (B := .var 0)
                    (.t_var (.S (.S .Z)))
                    wfTy0)
                  (.t_var (.S .Z)))
                (.t_var .Z)))))))

def «cplus_⊢» : 0 ⊢ [] ⊢ cplus ⦂ (CNat ⇒ CNat ⇒ CNat) :=
  cplus_hasType

def cnat2nat : Term :=
  ƛ ((((ˋ0 ∙[]) ∙ succFn) ∙ ˋzero))

def cnat2nat_hasType : 0 ⊢ [] ⊢ cnat2nat ⦂ (CNat ⇒ ℕ) :=
  .t_lam wfCNat
    (.t_app
      (.t_app
        (.t_tapp (A := (((.var 0) ⇒ (.var 0)) ⇒ (.var 0) ⇒ (.var 0)))
          (B := .nat)
          (.t_var .Z)
          wfNat)
        (.t_lam wfNat (.t_suc (.t_var .Z))))
      .t_zero)

def «cnat2nat_⊢» : 0 ⊢ [] ⊢ cnat2nat ⦂ (CNat ⇒ ℕ) :=
  cnat2nat_hasType

def csuccBool : Term :=
  ((ƛ ˋtrue) ∙ csucc)

def csuccBool_hasType : 0 ⊢ [] ⊢ csuccBool ⦂ 𝔹 :=
  .t_app
    (.t_lam (.fn wfCNat wfCNat) .t_true)
    csucc_hasType

def «csuccBool_⊢» : 0 ⊢ [] ⊢ csuccBool ⦂ 𝔹 :=
  csuccBool_hasType

def csuccBool_reduces : csuccBool —↠ ˋtrue :=
  .step _ (.beta_lam .vLam) (.refl _)

def «csuccBool_↠» : csuccBool —↠ ˋtrue :=
  csuccBool_reduces

def «csucc_↠» : csuccBool —↠ ˋtrue :=
  csuccBool_reduces

def cplusBool : Term :=
  ((ƛ ˋtrue) ∙ cplus)

def cplusBool_hasType : 0 ⊢ [] ⊢ cplusBool ⦂ 𝔹 :=
  .t_app
    (.t_lam (.fn wfCNat (.fn wfCNat wfCNat)) .t_true)
    cplus_hasType

def «cplusBool_⊢» : 0 ⊢ [] ⊢ cplusBool ⦂ 𝔹 :=
  cplusBool_hasType

def cplusBool_reduces : cplusBool —↠ ˋtrue :=
  .step _ (.beta_lam .vLam) (.refl _)

def «cplusBool_↠» : cplusBool —↠ ˋtrue :=
  cplusBool_reduces

def «cplus_↠» : cplusBool —↠ ˋtrue :=
  cplusBool_reduces

def c0AsNat : Term :=
  (cnat2nat ∙ c0)

def c0AsNat_hasType : 0 ⊢ [] ⊢ c0AsNat ⦂ ℕ :=
  .t_app cnat2nat_hasType c0_hasType

def «c0AsNat_⊢» : 0 ⊢ [] ⊢ c0AsNat ⦂ ℕ :=
  c0AsNat_hasType

def c0AsNat_reduces : c0AsNat —↠ ˋzero :=
  .step _ (.beta_lam .vTlam)
    (.step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
      (.step _ (.xi_app₁ (.beta_lam .vLam))
        (.step _ (.beta_lam .vZero) (.refl _))))

def «c0AsNat_↠» : c0AsNat —↠ ˋzero :=
  c0AsNat_reduces

def «c0_↠» : c0AsNat —↠ ˋzero :=
  c0AsNat_reduces

def c1AsNat : Term :=
  (cnat2nat ∙ c1)

def c1AsNat_hasType : 0 ⊢ [] ⊢ c1AsNat ⦂ ℕ :=
  .t_app cnat2nat_hasType c1_hasType

def «c1AsNat_⊢» : 0 ⊢ [] ⊢ c1AsNat ⦂ ℕ :=
  c1AsNat_hasType

def c1AsNat_reduces : c1AsNat —↠ one :=
  .step _ (.beta_lam .vTlam)
    (.step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
      (.step _ (.xi_app₁ (.beta_lam .vLam))
        (.step _ (.beta_lam .vZero)
          (.step _ (.beta_lam .vZero) (.refl _)))))

def «c1AsNat_↠» : c1AsNat —↠ one :=
  c1AsNat_reduces

def «c1_↠» : c1AsNat —↠ one :=
  c1AsNat_reduces

def c2AsNat : Term :=
  (cnat2nat ∙ c2)

def c2AsNat_hasType : 0 ⊢ [] ⊢ c2AsNat ⦂ ℕ :=
  .t_app cnat2nat_hasType c2_hasType

def «c2AsNat_⊢» : 0 ⊢ [] ⊢ c2AsNat ⦂ ℕ :=
  c2AsNat_hasType

def c2AsNat_reduces : c2AsNat —↠ two :=
  .step _ (.beta_lam .vTlam)
    (.step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
      (.step _ (.xi_app₁ (.beta_lam .vLam))
        (.step _ (.beta_lam .vZero)
          (.step _ (.xi_app₂ .vLam (.beta_lam .vZero))
            (.step _ (.beta_lam (.vSuc .vZero)) (.refl _))))))

def «c2AsNat_↠» : c2AsNat —↠ two :=
  c2AsNat_reduces

def «c2_↠» : c2AsNat —↠ two :=
  c2AsNat_reduces

def «cnat2nat_↠» : c2AsNat —↠ two :=
  c2AsNat_reduces

------------------------------------------------------------------------
-- Encoded lists and pairs
------------------------------------------------------------------------

def List (A : Ty) : Ty :=
  ∀ₜ (((renameT Nat.succ A) ⇒ #0 ⇒ #0) ⇒ #0 ⇒ #0)

def nil : Term :=
  Λ (Λ (ƛ (ƛ (ˋ0))))

def wfListTy0 : WfTy 1 (List (#0)) :=
  .all (.fn (.fn wfTy1₂ (.fn wfTy0₂ wfTy0₂)) (.fn wfTy0₂ wfTy0₂))

def nil_hasType : 0 ⊢ [] ⊢ nil ⦂ (∀ₜ (List (#0))) :=
  .t_tlam
    (.t_tlam
      (.t_lam
        (.fn wfTy1₂ (.fn wfTy0₂ wfTy0₂))
        (.t_lam wfTy0₂ (.t_var .Z))))

def «nil_⊢» : 0 ⊢ [] ⊢ nil ⦂ (∀ₜ (List (#0))) :=
  nil_hasType

def cons : Term :=
  Λ
    (ƛ
      (ƛ
        (Λ
          (ƛ
            (ƛ
              ((ˋ1 ∙ ˋ3) ∙ (((ˋ2 ∙[]) ∙ ˋ1) ∙ ˋ0)))))))

def cons_hasType : 0 ⊢ [] ⊢ cons ⦂ (∀ₜ ((#0) ⇒ List (#0) ⇒ List (#0))) :=
  .t_tlam
    (.t_lam wfTy0
      (.t_lam wfListTy0
        (.t_tlam
          (.t_lam
            (.fn wfTy1₂ (.fn wfTy0₂ wfTy0₂))
            (.t_lam wfTy0₂
              (.t_app
                (.t_app (.t_var (.S .Z)) (.t_var (.S (.S (.S .Z)))))
                (.t_app
                  (.t_app
                    (.t_tapp
                      (A := (((.var 2) ⇒ (.var 0) ⇒ (.var 0)) ⇒ (.var 0) ⇒ (.var 0)))
                      (B := .var 0)
                      (.t_var (.S (.S .Z)))
                      wfTy0₂)
                    (.t_var (.S .Z)))
                  (.t_var .Z))))))))

def «cons_⊢» : 0 ⊢ [] ⊢ cons ⦂ (∀ₜ ((#0) ⇒ List (#0) ⇒ List (#0))) :=
  cons_hasType

def isnil : Term :=
  Λ (ƛ ((((ˋ0 ∙[]) ∙ (ƛ (ƛ ˋfalse))) ∙ ˋtrue)))

def isnil_hasType : 0 ⊢ [] ⊢ isnil ⦂ (∀ₜ (List (#0) ⇒ 𝔹)) :=
  .t_tlam
    (.t_lam wfListTy0
      (.t_app
        (.t_app
          (.t_tapp
            (A := (((.var 1) ⇒ (.var 0) ⇒ (.var 0)) ⇒ (.var 0) ⇒ (.var 0)))
            (B := .bool)
            (.t_var .Z)
            .bool)
          (.t_lam wfTy0 (.t_lam .bool .t_false)))
        .t_true))

def «isnil_⊢» : 0 ⊢ [] ⊢ isnil ⦂ (∀ₜ (List (#0) ⇒ 𝔹)) :=
  isnil_hasType

def nilIsNil : Term :=
  ((isnil ∙[]) ∙ (nil ∙[]))

def nilIsNil_hasType : 0 ⊢ [] ⊢ nilIsNil ⦂ 𝔹 :=
  .t_app
    (.t_tapp (A := (List (.var 0) ⇒ .bool)) (B := .bool) isnil_hasType wfBool)
    (.t_tapp (A := List (.var 0)) (B := .bool) nil_hasType wfBool)

def «nilIsNil_⊢» : 0 ⊢ [] ⊢ nilIsNil ⦂ 𝔹 :=
  nilIsNil_hasType

def nilIsNil_reduces : nilIsNil —↠ ˋtrue :=
  .step _ (.xi_app₁ .beta_tlam)
    (.step _ (.xi_app₂ .vLam .beta_tlam)
      (.step _ (.beta_lam .vTlam)
        (.step _ (.xi_app₁ (.xi_app₁ .beta_tlam))
          (.step _ (.xi_app₁ (.beta_lam .vLam))
            (.step _ (.beta_lam .vTrue) (.refl _))))))

def «nilIsNil_↠» : nilIsNil —↠ ˋtrue :=
  nilIsNil_reduces

def «nil_↠» : nilIsNil —↠ ˋtrue :=
  nilIsNil_reduces

def wfConsTy : WfTy 0 (∀ₜ ((#0) ⇒ List (#0) ⇒ List (#0))) :=
  .all (.fn wfTy0 (.fn wfListTy0 wfListTy0))

def consIsNil : Term :=
  ((ƛ ˋfalse) ∙ cons)

def consIsNil_hasType : 0 ⊢ [] ⊢ consIsNil ⦂ 𝔹 :=
  .t_app
    (.t_lam wfConsTy .t_false)
    cons_hasType

def «consIsNil_⊢» : 0 ⊢ [] ⊢ consIsNil ⦂ 𝔹 :=
  consIsNil_hasType

def consIsNil_reduces : consIsNil —↠ ˋfalse :=
  .step _ (.beta_lam .vTlam) (.refl _)

def «consIsNil_↠» : consIsNil —↠ ˋfalse :=
  consIsNil_reduces

def «cons_↠» : consIsNil —↠ ˋfalse :=
  consIsNil_reduces

def «isnil_↠» : nilIsNil —↠ ˋtrue :=
  nilIsNil_reduces

def Pair (A B : Ty) : Ty :=
  ∀ₜ (((renameT Nat.succ A) ⇒ (renameT Nat.succ B) ⇒ #0) ⇒ #0)

def pair : Term :=
  Λ (Λ (ƛ (ƛ (Λ (ƛ ((ˋ0 ∙ ˋ2) ∙ ˋ1))))))

def pair_hasType : 0 ⊢ [] ⊢ pair ⦂ (∀ₜ (∀ₜ ((#1) ⇒ (#0) ⇒ Pair (#1) (#0)))) :=
  .t_tlam
    (.t_tlam
      (.t_lam wfTy1₂
        (.t_lam wfTy0₂
          (.t_tlam
            (.t_lam (.fn wfTy2₃ (.fn wfTy1₃ wfTy0₃))
              (.t_app
                (.t_app (.t_var .Z) (.t_var (.S (.S .Z))))
                (.t_var (.S .Z))))))))

def «pair_⊢» : 0 ⊢ [] ⊢ pair ⦂ (∀ₜ (∀ₜ ((#1) ⇒ (#0) ⇒ Pair (#1) (#0)))) :=
  pair_hasType

def fst : Term :=
  Λ (Λ (ƛ ((ˋ0 ∙[]) ∙ (ƛ (ƛ ˋ1)))))

def fst_hasType : 0 ⊢ [] ⊢ fst ⦂ (∀ₜ (∀ₜ (Pair (#1) (#0) ⇒ (#1)))) :=
  .t_tlam
    (.t_tlam
      (.t_lam
        (.all (.fn (.fn wfTy2₃ (.fn wfTy1₃ wfTy0₃)) wfTy0₃))
        (.t_app
          (.t_tapp
            (A := (((.var 2) ⇒ (.var 1) ⇒ (.var 0)) ⇒ (.var 0)))
            (B := .var 1)
            (.t_var .Z)
            wfTy1₂)
          (.t_lam wfTy1₂ (.t_lam wfTy0₂ (.t_var (.S .Z)))))))

def «fst_⊢» : 0 ⊢ [] ⊢ fst ⦂ (∀ₜ (∀ₜ (Pair (#1) (#0) ⇒ (#1)))) :=
  fst_hasType

def snd : Term :=
  Λ (Λ (ƛ ((ˋ0 ∙[]) ∙ (ƛ (ƛ ˋ0)))))

def snd_hasType : 0 ⊢ [] ⊢ snd ⦂ (∀ₜ (∀ₜ (Pair (#1) (#0) ⇒ (#0)))) :=
  .t_tlam
    (.t_tlam
      (.t_lam
        (.all (.fn (.fn wfTy2₃ (.fn wfTy1₃ wfTy0₃)) wfTy0₃))
        (.t_app
          (.t_tapp
            (A := (((.var 2) ⇒ (.var 1) ⇒ (.var 0)) ⇒ (.var 0)))
            (B := .var 0)
            (.t_var .Z)
            wfTy0₂)
          (.t_lam wfTy1₂ (.t_lam wfTy0₂ (.t_var .Z))))) )

def «snd_⊢» : 0 ⊢ [] ⊢ snd ⦂ (∀ₜ (∀ₜ (Pair (#1) (#0) ⇒ (#0)))) :=
  snd_hasType

def wfPair10₂ : WfTy 2 (Pair (#1) (#0)) :=
  .all (.fn (.fn wfTy2₃ (.fn wfTy1₃ wfTy0₃)) wfTy0₃)

def wfPairTy : WfTy 0 (∀ₜ (∀ₜ ((#1) ⇒ (#0) ⇒ Pair (#1) (#0)))) :=
  .all (.all (.fn wfTy1₂ (.fn wfTy0₂ wfPair10₂)))

def wfFstTy : WfTy 0 (∀ₜ (∀ₜ (Pair (#1) (#0) ⇒ (#1)))) :=
  .all (.all (.fn wfPair10₂ wfTy1₂))

def wfSndTy : WfTy 0 (∀ₜ (∀ₜ (Pair (#1) (#0) ⇒ (#0)))) :=
  .all (.all (.fn wfPair10₂ wfTy0₂))

def pairBool : Term :=
  ((ƛ ˋtrue) ∙ pair)

def pairBool_hasType : 0 ⊢ [] ⊢ pairBool ⦂ 𝔹 :=
  .t_app
    (.t_lam wfPairTy .t_true)
    pair_hasType

def «pairBool_⊢» : 0 ⊢ [] ⊢ pairBool ⦂ 𝔹 :=
  pairBool_hasType

def pairBool_reduces : pairBool —↠ ˋtrue :=
  .step _ (.beta_lam .vTlam) (.refl _)

def «pairBool_↠» : pairBool —↠ ˋtrue :=
  pairBool_reduces

def «pair_↠» : pairBool —↠ ˋtrue :=
  pairBool_reduces

def fstBool : Term :=
  ((ƛ ˋtrue) ∙ fst)

def fstBool_hasType : 0 ⊢ [] ⊢ fstBool ⦂ 𝔹 :=
  .t_app
    (.t_lam wfFstTy .t_true)
    fst_hasType

def «fstBool_⊢» : 0 ⊢ [] ⊢ fstBool ⦂ 𝔹 :=
  fstBool_hasType

def fstBool_reduces : fstBool —↠ ˋtrue :=
  .step _ (.beta_lam .vTlam) (.refl _)

def «fstBool_↠» : fstBool —↠ ˋtrue :=
  fstBool_reduces

def «fst_↠» : fstBool —↠ ˋtrue :=
  fstBool_reduces

def sndBool : Term :=
  ((ƛ ˋzero) ∙ snd)

def sndBool_hasType : 0 ⊢ [] ⊢ sndBool ⦂ ℕ :=
  .t_app
    (.t_lam wfSndTy .t_zero)
    snd_hasType

def «sndBool_⊢» : 0 ⊢ [] ⊢ sndBool ⦂ ℕ :=
  sndBool_hasType

def sndBool_reduces : sndBool —↠ ˋzero :=
  .step _ (.beta_lam .vTlam) (.refl _)

def «sndBool_↠» : sndBool —↠ ˋzero :=
  sndBool_reduces

def «snd_↠» : sndBool —↠ ˋzero :=
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
-- `ξ-·₁`: reduce the function position of an application.
------------------------------------------------------------------------

def ex_xi_app1 : Term :=
  ((ˋif ˋtrue then (ƛ ˋ0) else (ƛ ˋ0)) ∙ ˋtrue)

def ex_xi_app1_hasType : 0 ⊢ [] ⊢ ex_xi_app1 ⦂ 𝔹 :=
  .t_app
    (.t_if .t_true
      (.t_lam wfBool (.t_var .Z))
      (.t_lam wfBool (.t_var .Z)))
    .t_true

def «ex_xi_app1_⊢» : 0 ⊢ [] ⊢ ex_xi_app1 ⦂ 𝔹 :=
  ex_xi_app1_hasType

def ex_xi_app1_reduces : ex_xi_app1 —↠ ˋtrue :=
  .step _ (.xi_app₁ .beta_true)
    (.step _ (.beta_lam .vTrue) (.refl _))

def «ex_xi_app1_↠» : ex_xi_app1 —↠ ˋtrue :=
  ex_xi_app1_reduces

------------------------------------------------------------------------
-- `ξ-·₂`: reduce the argument position of an application.
------------------------------------------------------------------------

def ex_xi_app2 : Term :=
  ((ƛ ˋ0) ∙ (ˋif ˋfalse then ˋtrue else ˋfalse))

def ex_xi_app2_hasType : 0 ⊢ [] ⊢ ex_xi_app2 ⦂ 𝔹 :=
  .t_app
    (.t_lam wfBool (.t_var .Z))
    (.t_if .t_false .t_true .t_false)

def «ex_xi_app2_⊢» : 0 ⊢ [] ⊢ ex_xi_app2 ⦂ 𝔹 :=
  ex_xi_app2_hasType

def ex_xi_app2_reduces : ex_xi_app2 —↠ ˋfalse :=
  .step _ (.xi_app₂ .vLam .beta_false)
    (.step _ (.beta_lam .vFalse) (.refl _))

def «ex_xi_app2_↠» : ex_xi_app2 —↠ ˋfalse :=
  ex_xi_app2_reduces

------------------------------------------------------------------------
-- `β-ƛ`: ordinary lambda beta reduction.
------------------------------------------------------------------------

def ex_beta_lam : Term :=
  ((ƛ ˋ0) ∙ ˋtrue)

def ex_beta_lam_hasType : 0 ⊢ [] ⊢ ex_beta_lam ⦂ 𝔹 :=
  .t_app
    (.t_lam wfBool (.t_var .Z))
    .t_true

def «ex_beta_lam_⊢» : 0 ⊢ [] ⊢ ex_beta_lam ⦂ 𝔹 :=
  ex_beta_lam_hasType

def ex_beta_lam_reduces : ex_beta_lam —↠ ˋtrue :=
  .step _ (.beta_lam .vTrue) (.refl _)

def «ex_beta_lam_↠» : ex_beta_lam —↠ ˋtrue :=
  ex_beta_lam_reduces

------------------------------------------------------------------------
-- `ξ-suc`: reduce under `suc`.
------------------------------------------------------------------------

def ex_xi_suc : Term :=
  ˋsuc (ˋif ˋfalse then ˋzero else ˋzero)

def ex_xi_suc_hasType : 0 ⊢ [] ⊢ ex_xi_suc ⦂ ℕ :=
  .t_suc (.t_if .t_false .t_zero .t_zero)

def «ex_xi_suc_⊢» : 0 ⊢ [] ⊢ ex_xi_suc ⦂ ℕ :=
  ex_xi_suc_hasType

def ex_xi_suc_reduces : ex_xi_suc —↠ (ˋsuc ˋzero) :=
  .step _ (.xi_suc .beta_false) (.refl _)

def «ex_xi_suc_↠» : ex_xi_suc —↠ (ˋsuc ˋzero) :=
  ex_xi_suc_reduces

------------------------------------------------------------------------
-- `ξ-if`: reduce the condition of an if-expression.
------------------------------------------------------------------------

def ex_xi_if : Term :=
  ˋif (ˋif ˋtrue then ˋfalse else ˋtrue) then ˋzero else (ˋsuc ˋzero)

def ex_xi_if_hasType : 0 ⊢ [] ⊢ ex_xi_if ⦂ ℕ :=
  .t_if
    (.t_if .t_true .t_false .t_true)
    .t_zero
    (.t_suc .t_zero)

def «ex_xi_if_⊢» : 0 ⊢ [] ⊢ ex_xi_if ⦂ ℕ :=
  ex_xi_if_hasType

def ex_xi_if_reduces : ex_xi_if —↠ (ˋsuc ˋzero) :=
  .step _ (.xi_if .beta_true)
    (.step _ .beta_false (.refl _))

def «ex_xi_if_↠» : ex_xi_if —↠ (ˋsuc ˋzero) :=
  ex_xi_if_reduces

------------------------------------------------------------------------
-- `ξ-case`: reduce the scrutinee of a case expression.
------------------------------------------------------------------------

def ex_xi_case : Term :=
  caseₜ (ˋif ˋtrue then ˋzero else ˋzero) [zero⇒ ˋzero |suc⇒ ˋsuc ˋ0]

def ex_xi_case_hasType : 0 ⊢ [] ⊢ ex_xi_case ⦂ ℕ :=
  .t_case
    (.t_if .t_true .t_zero .t_zero)
    .t_zero
    (.t_suc (.t_var .Z))

def «ex_xi_case_⊢» : 0 ⊢ [] ⊢ ex_xi_case ⦂ ℕ :=
  ex_xi_case_hasType

def ex_xi_case_reduces : ex_xi_case —↠ ˋzero :=
  .step _ (.xi_case .beta_true)
    (.step _ .beta_zero (.refl _))

def «ex_xi_case_↠» : ex_xi_case —↠ ˋzero :=
  ex_xi_case_reduces

------------------------------------------------------------------------
-- `β-true`: if-true.
------------------------------------------------------------------------

def ex_beta_true : Term :=
  ˋif ˋtrue then ˋzero else (ˋsuc ˋzero)

def ex_beta_true_hasType : 0 ⊢ [] ⊢ ex_beta_true ⦂ ℕ :=
  .t_if .t_true .t_zero (.t_suc .t_zero)

def «ex_beta_true_⊢» : 0 ⊢ [] ⊢ ex_beta_true ⦂ ℕ :=
  ex_beta_true_hasType

def ex_beta_true_reduces : ex_beta_true —↠ ˋzero :=
  .step _ .beta_true (.refl _)

def «ex_beta_true_↠» : ex_beta_true —↠ ˋzero :=
  ex_beta_true_reduces

------------------------------------------------------------------------
-- `β-false`: if-false.
------------------------------------------------------------------------

def ex_beta_false : Term :=
  ˋif ˋfalse then ˋzero else (ˋsuc ˋzero)

def ex_beta_false_hasType : 0 ⊢ [] ⊢ ex_beta_false ⦂ ℕ :=
  .t_if .t_false .t_zero (.t_suc .t_zero)

def «ex_beta_false_⊢» : 0 ⊢ [] ⊢ ex_beta_false ⦂ ℕ :=
  ex_beta_false_hasType

def ex_beta_false_reduces : ex_beta_false —↠ (ˋsuc ˋzero) :=
  .step _ .beta_false (.refl _)

def «ex_beta_false_↠» : ex_beta_false —↠ (ˋsuc ˋzero) :=
  ex_beta_false_reduces

------------------------------------------------------------------------
-- `β-zero`: case on zero.
------------------------------------------------------------------------

def ex_beta_zero : Term :=
  caseₜ ˋzero [zero⇒ ˋzero |suc⇒ ˋsuc ˋzero]

def ex_beta_zero_hasType : 0 ⊢ [] ⊢ ex_beta_zero ⦂ ℕ :=
  .t_case .t_zero .t_zero (.t_suc .t_zero)

def «ex_beta_zero_⊢» : 0 ⊢ [] ⊢ ex_beta_zero ⦂ ℕ :=
  ex_beta_zero_hasType

def ex_beta_zero_reduces : ex_beta_zero —↠ ˋzero :=
  .step _ .beta_zero (.refl _)

def «ex_beta_zero_↠» : ex_beta_zero —↠ ˋzero :=
  ex_beta_zero_reduces

------------------------------------------------------------------------
-- `β-suc`: case on a successor value.
------------------------------------------------------------------------

def ex_beta_suc : Term :=
  caseₜ (ˋsuc ˋzero) [zero⇒ ˋzero |suc⇒ ˋsuc ˋ0]

def ex_beta_suc_hasType : 0 ⊢ [] ⊢ ex_beta_suc ⦂ ℕ :=
  .t_case
    (.t_suc .t_zero)
    .t_zero
    (.t_suc (.t_var .Z))

def «ex_beta_suc_⊢» : 0 ⊢ [] ⊢ ex_beta_suc ⦂ ℕ :=
  ex_beta_suc_hasType

def ex_beta_suc_reduces : ex_beta_suc —↠ (ˋsuc ˋzero) :=
  .step _ (.beta_suc .vZero) (.refl _)

def «ex_beta_suc_↠» : ex_beta_suc —↠ (ˋsuc ˋzero) :=
  ex_beta_suc_reduces

------------------------------------------------------------------------
-- `ξ-·[]`: reduce under a type application.
------------------------------------------------------------------------

def ex_xi_tapp : Term :=
  (((ˋif ˋtrue then polyId else polyId) ∙[]) ∙ ˋtrue)

def ex_xi_tapp_hasType : 0 ⊢ [] ⊢ ex_xi_tapp ⦂ 𝔹 :=
  .t_app
    (.t_tapp
      (A := (.var 0 ⇒ .var 0))
      (B := .bool)
      (.t_if .t_true polyId_hasType polyId_hasType)
      wfBool)
    .t_true

def «ex_xi_tapp_⊢» : 0 ⊢ [] ⊢ ex_xi_tapp ⦂ 𝔹 :=
  ex_xi_tapp_hasType

def ex_xi_tapp_reduces : ex_xi_tapp —↠ ˋtrue :=
  .step _ (.xi_app₁ (.xi_tapp .beta_true))
    (.step _ (.xi_app₁ .beta_tlam)
      (.step _ (.beta_lam .vTrue) (.refl _)))

def «ex_xi_tapp_↠» : ex_xi_tapp —↠ ˋtrue :=
  ex_xi_tapp_reduces

------------------------------------------------------------------------
-- `β-Λ`: polymorphic beta reduction.
------------------------------------------------------------------------

def ex_beta_tlam : Term :=
  ((polyId ∙[]) ∙ ˋtrue)

def ex_beta_tlam_hasType : 0 ⊢ [] ⊢ ex_beta_tlam ⦂ 𝔹 :=
  .t_app
    (.t_tapp (A := (.var 0 ⇒ .var 0)) (B := .bool) polyId_hasType wfBool)
    .t_true

def «ex_beta_tlam_⊢» : 0 ⊢ [] ⊢ ex_beta_tlam ⦂ 𝔹 :=
  ex_beta_tlam_hasType

def ex_beta_tlam_reduces : ex_beta_tlam —↠ ˋtrue :=
  .step _ (.xi_app₁ .beta_tlam)
    (.step _ (.beta_lam .vTrue) (.refl _))

def «ex_beta_tlam_↠» : ex_beta_tlam —↠ ˋtrue :=
  ex_beta_tlam_reduces

end Curry

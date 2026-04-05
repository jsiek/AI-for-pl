import extrinsic.TypeSubst

namespace Extrinsic

inductive Term where
  | var   : Var → Term
  | lam   : Term → Term
  | app   : Term → Term → Term
  | ttrue : Term
  | tfalse : Term
  | zero  : Term
  | suc   : Term → Term
  | natCase : Term → Term → Term → Term
  | ite   : Term → Term → Term → Term
  | tlam  : Term → Term
  | tapp  : Term → Term
  deriving DecidableEq, Repr

infixl:70 " · " => Term.app

def renameTT (ρ : RenameT) (M : Term) : Term := M
def substTT (σ : SubstT) (M : Term) : Term := M
def substOneTT (N : Term) (A : Ty) : Term := N

abbrev Rename : Type := Var → Var
abbrev Subst : Type := Var → Term

def ext (ρ : Rename) : Rename
  | 0 => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Rename) : Term → Term
  | .var i => .var (ρ i)
  | .lam N => .lam (rename (ext ρ) N)
  | .app L M => .app (rename ρ L) (rename ρ M)
  | .ttrue => .ttrue
  | .tfalse => .tfalse
  | .zero => .zero
  | .suc M => .suc (rename ρ M)
  | .natCase L M N => .natCase (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  | .ite L M N => .ite (rename ρ L) (rename ρ M) (rename ρ N)
  | .tlam N => .tlam (rename ρ N)
  | .tapp M => .tapp (rename ρ M)

def exts (σ : Subst) : Subst
  | 0 => .var 0
  | i + 1 => rename Nat.succ (σ i)

def up (σ : Subst) : Subst :=
  fun i => renameTT Nat.succ (σ i)

def upT (σ : Subst) : Subst :=
  fun i => rename Nat.succ (σ i)

def id : Subst := Term.var

def consSub (M : Term) (σ : Subst) : Subst
  | 0 => M
  | i + 1 => σ i

infixr:61 " • " => consSub

def subst (σ : Subst) : Term → Term
  | .var i => σ i
  | .lam N => .lam (subst (exts σ) N)
  | .app L M => .app (subst σ L) (subst σ M)
  | .ttrue => .ttrue
  | .tfalse => .tfalse
  | .zero => .zero
  | .suc M => .suc (subst σ M)
  | .natCase L M N => .natCase (subst σ L) (subst σ M) (subst (exts σ) N)
  | .ite L M N => .ite (subst σ L) (subst σ M) (subst σ N)
  | .tlam N => .tlam (subst (up σ) N)
  | .tapp M => .tapp (subst σ M)

def singleEnv (M : Term) : Subst
  | 0 => M
  | i + 1 => .var i

def singleSubst (N M : Term) : Term :=
  subst (singleEnv M) N

infixr:67 " ⨟ " => fun (σ τ : Subst) i => subst τ (σ i)

-- Ported theorem surface (extrinsic/Terms.agda), used by later modules.
theorem ext_cong {ρ ρ' : Rename} :
  (∀ i, ρ i = ρ' i) → ∀ i, ext ρ i = ext ρ' i
  | h, 0 => rfl
  | h, i + 1 => by simpa [ext] using congrArg Nat.succ (h i)

theorem exts_cong {σ τ : Subst} :
  (∀ i, σ i = τ i) → ∀ i, exts σ i = exts τ i
  | h, 0 => rfl
  | h, i + 1 => by simpa [exts] using congrArg (rename Nat.succ) (h i)

theorem rename_cong_tm {ρ ρ' : Rename} :
  (∀ i, ρ i = ρ' i) → ∀ M, rename ρ M = rename ρ' M
  | h, .var i => by simpa [rename, h i]
  | h, .lam N => by simpa [rename] using congrArg Term.lam (rename_cong_tm (ext_cong h) N)
  | h, .app L M => by simp [rename, rename_cong_tm h L, rename_cong_tm h M]
  | h, .ttrue => rfl
  | h, .tfalse => rfl
  | h, .zero => rfl
  | h, .suc M => by simpa [rename] using congrArg Term.suc (rename_cong_tm h M)
  | h, .natCase L M N => by
      simp [rename, rename_cong_tm h L, rename_cong_tm h M, rename_cong_tm (ext_cong h) N]
  | h, .ite L M N => by
      simp [rename, rename_cong_tm h L, rename_cong_tm h M, rename_cong_tm h N]
  | h, .tlam N => by simpa [rename] using congrArg Term.tlam (rename_cong_tm h N)
  | h, .tapp M => by simpa [rename] using congrArg Term.tapp (rename_cong_tm h M)

theorem subst_cong_tm {σ τ : Subst} :
  (∀ i, σ i = τ i) → ∀ M, subst σ M = subst τ M
  | h, .var i => h i
  | h, .lam N => by simpa [subst] using congrArg Term.lam (subst_cong_tm (exts_cong h) N)
  | h, .app L M => by simp [subst, subst_cong_tm h L, subst_cong_tm h M]
  | h, .ttrue => rfl
  | h, .tfalse => rfl
  | h, .zero => rfl
  | h, .suc M => by simpa [subst] using congrArg Term.suc (subst_cong_tm h M)
  | h, .natCase L M N => by
      simp [subst, subst_cong_tm h L, subst_cong_tm h M, subst_cong_tm (exts_cong h) N]
  | h, .ite L M N => by
      simp [subst, subst_cong_tm h L, subst_cong_tm h M, subst_cong_tm h N]
  | h, .tlam N => by simpa [subst] using congrArg Term.tlam (subst_cong_tm h N)
  | h, .tapp M => by simpa [subst] using congrArg Term.tapp (subst_cong_tm h M)

theorem ext_comp_tm (ρ₁ ρ₂ : Rename) :
  (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i <;> rfl

theorem rename_comp (ρ₁ ρ₂ : Rename) :
  ∀ M, rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M
  | .var i => rfl
  | .lam N => by
      calc
        rename ρ₂ (rename ρ₁ (.lam N))
            = .lam (rename (ext ρ₂) (rename (ext ρ₁) N)) := rfl
        _ = .lam (rename (fun i => ext ρ₂ (ext ρ₁ i)) N) := by
              simpa using congrArg Term.lam (rename_comp (ext ρ₁) (ext ρ₂) N)
        _ = .lam (rename (ext (fun i => ρ₂ (ρ₁ i))) N) := by
              apply congrArg Term.lam
              exact rename_cong_tm (fun i => congrFun (ext_comp_tm ρ₁ ρ₂) i) N
        _ = rename (fun i => ρ₂ (ρ₁ i)) (.lam N) := rfl
  | .app L M => by simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M]
  | .ttrue => rfl
  | .tfalse => rfl
  | .zero => rfl
  | .suc M => by simpa [rename] using congrArg Term.suc (rename_comp ρ₁ ρ₂ M)
  | .natCase L M N => by
      simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M,
        rename_comp (ext ρ₁) (ext ρ₂) N,
        rename_cong_tm (fun i => congrFun (ext_comp_tm ρ₁ ρ₂) i) N]
  | .ite L M N => by simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M, rename_comp ρ₁ ρ₂ N]
  | .tlam N => by simpa [rename] using congrArg Term.tlam (rename_comp ρ₁ ρ₂ N)
  | .tapp M => by simpa [rename] using congrArg Term.tapp (rename_comp ρ₁ ρ₂ M)

theorem exts_ext (ρ : Rename) (σ : Subst) :
  (fun i => exts σ (ext ρ i)) = exts (fun y => σ (ρ y)) := by
  funext i
  cases i <;> rfl

theorem ren_sub (ρ : Rename) (σ : Subst) :
  ∀ M, subst σ (rename ρ M) = subst (fun x => σ (ρ x)) M
  | .var i => rfl
  | .lam N => by
      simp [rename, subst, ren_sub (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (exts_ext ρ σ) i) N]
  | .app L M => by simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M]
  | .ttrue => rfl
  | .tfalse => rfl
  | .zero => rfl
  | .suc M => by simpa [rename, subst] using congrArg Term.suc (ren_sub ρ σ M)
  | .natCase L M N => by
      simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M,
        ren_sub (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (exts_ext ρ σ) i) N]
  | .ite L M N => by simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M, ren_sub ρ σ N]
  | .tlam N => by
      simpa [rename, subst, up, renameTT] using
        congrArg Term.tlam (ren_sub ρ (up σ) N)
  | .tapp M => by simpa [rename, subst] using congrArg Term.tapp (ren_sub ρ σ M)

theorem rename_shift (ρ : Rename) :
  ∀ M, rename (ext ρ) (rename Nat.succ M) = rename Nat.succ (rename ρ M)
  | M => by
      calc
        rename (ext ρ) (rename Nat.succ M)
            = rename (fun i => ext ρ (Nat.succ i)) M := by
                exact rename_comp Nat.succ (ext ρ) M
        _ = rename (fun i => Nat.succ (ρ i)) M := by
                apply rename_cong_tm
                intro i
                rfl
        _ = rename Nat.succ (rename ρ M) := by
                symm
                exact rename_comp ρ Nat.succ M

theorem ext_exts (ρ : Rename) (σ : Subst) :
  (fun i => rename (ext ρ) (exts σ i)) = exts (fun y => rename ρ (σ y)) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      simpa [exts] using rename_shift ρ (σ j)

theorem sub_ren (ρ : Rename) (σ : Subst) :
  ∀ M, rename ρ (subst σ M) = subst (fun x => rename ρ (σ x)) M
  | .var i => rfl
  | .lam N => by
      simp [rename, subst, sub_ren (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (ext_exts ρ σ) i) N]
  | .app L M => by simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M]
  | .ttrue => rfl
  | .tfalse => rfl
  | .zero => rfl
  | .suc M => by simpa [rename, subst] using congrArg Term.suc (sub_ren ρ σ M)
  | .natCase L M N => by
      simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M,
        sub_ren (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (ext_exts ρ σ) i) N]
  | .ite L M N => by simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M, sub_ren ρ σ N]
  | .tlam N => by
      simpa [rename, subst, up, renameTT] using congrArg Term.tlam (sub_ren ρ (up σ) N)
  | .tapp M => by simpa [rename, subst] using congrArg Term.tapp (sub_ren ρ σ M)

theorem exts_subst (σ τ : Subst) :
  (fun i => subst (exts τ) (exts σ i)) = exts (σ ⨟ τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      calc
        subst (exts τ) (exts σ (j + 1))
            = subst (exts τ) (rename Nat.succ (σ j)) := rfl
        _ = subst (fun x => exts τ (Nat.succ x)) (σ j) := by
              exact ren_sub Nat.succ (exts τ) (σ j)
        _ = subst (fun x => rename Nat.succ (τ x)) (σ j) := by
              apply subst_cong_tm
              intro x
              rfl
        _ = rename Nat.succ (subst τ (σ j)) := by
              symm
              exact sub_ren Nat.succ τ (σ j)
        _ = exts (σ ⨟ τ) (j + 1) := rfl

theorem sub_sub_tm (σ τ : Subst) :
  ∀ M, subst τ (subst σ M) = subst (σ ⨟ τ) M
  | .var i => rfl
  | .lam N => by
      simp [subst, sub_sub_tm (exts σ) (exts τ) N,
        subst_cong_tm (fun i => congrFun (exts_subst σ τ) i) N]
  | .app L M => by simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M]
  | .ttrue => rfl
  | .tfalse => rfl
  | .zero => rfl
  | .suc M => by simpa [subst] using congrArg Term.suc (sub_sub_tm σ τ M)
  | .natCase L M N => by
      simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M,
        sub_sub_tm (exts σ) (exts τ) N,
        subst_cong_tm (fun i => congrFun (exts_subst σ τ) i) N]
  | .ite L M N => by simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M, sub_sub_tm σ τ N]
  | .tlam N => by
      have hmain := sub_sub_tm (up σ) (up τ) N
      have hupσ : up σ = σ := by
        funext i
        simp [up, renameTT]
      have hupτ : up τ = τ := by
        funext i
        simp [up, renameTT]
      have henv : (up σ ⨟ up τ) = up (σ ⨟ τ) := by
        have h1 : (up σ ⨟ up τ) = (σ ⨟ τ) := by
          funext i
          simp [hupσ, hupτ]
        have h2 : up (σ ⨟ τ) = (σ ⨟ τ) := by
          funext i
          simp [up, renameTT]
        simpa [h2] using h1
      simpa [henv, subst] using hmain
  | .tapp M => by simpa [subst] using congrArg Term.tapp (sub_sub_tm σ τ M)

theorem exts_id : ∀ i, exts id i = id i
  | 0 => rfl
  | i + 1 => rfl

theorem sub_id : ∀ M, subst id M = M
  | .var i => rfl
  | .lam N => by
      simpa [subst] using congrArg Term.lam (Eq.trans (subst_cong_tm exts_id N) (sub_id N))
  | .app L M => by simp [subst, sub_id L, sub_id M]
  | .ttrue => rfl
  | .tfalse => rfl
  | .zero => rfl
  | .suc M => by simpa [subst] using congrArg Term.suc (sub_id M)
  | .natCase L M N => by
      simp [subst, sub_id L, sub_id M, Eq.trans (subst_cong_tm exts_id N) (sub_id N)]
  | .ite L M N => by simp [subst, sub_id L, sub_id M, sub_id N]
  | .tlam N => by
      have hN : subst (up id) N = N := by simpa [up, renameTT] using sub_id N
      simpa [subst] using congrArg Term.tlam hN
  | .tapp M => by simpa [subst] using congrArg Term.tapp (sub_id M)

theorem exts_sub_cons_tm (σ : Subst) (N V : Term) :
  singleSubst (subst (exts σ) N) V = subst (V • σ) N := by
  unfold singleSubst
  calc
    subst (singleEnv V) (subst (exts σ) N)
        = subst ((exts σ) ⨟ singleEnv V) N := by
            exact sub_sub_tm (exts σ) (singleEnv V) N
    _ = subst (V • σ) N := by
          apply subst_cong_tm
          intro i
          cases i with
          | zero => rfl
          | succ x =>
              calc
                subst (singleEnv V) (exts σ (x + 1))
                    = subst (singleEnv V) (rename Nat.succ (σ x)) := rfl
                _ = subst (fun y => singleEnv V (Nat.succ y)) (σ x) := by
                      exact ren_sub Nat.succ (singleEnv V) (σ x)
                _ = subst (fun y => Term.var y) (σ x) := by
                      apply subst_cong_tm
                      intro y
                      rfl
                _ = σ x := sub_id (σ x)
                _ = (V • σ) (x + 1) := rfl

inductive HasType : TyCtx → Ctx → Term → Ty → Type where
  | t_var {Δ Γ i A} :
      HasTypeVar Γ i A →
      HasType Δ Γ (.var i) A
  | t_lam {Δ Γ A B N} :
      WfTy Δ A →
      HasType Δ (A :: Γ) N B →
      HasType Δ Γ (.lam N) (.fn A B)
  | t_app {Δ Γ A B L M} :
      HasType Δ Γ L (.fn A B) →
      HasType Δ Γ M A →
      HasType Δ Γ (.app L M) B
  | t_true {Δ Γ} : HasType Δ Γ .ttrue .bool
  | t_false {Δ Γ} : HasType Δ Γ .tfalse .bool
  | t_zero {Δ Γ} : HasType Δ Γ .zero .nat
  | t_suc {Δ Γ M} :
      HasType Δ Γ M .nat →
      HasType Δ Γ (.suc M) .nat
  | t_case {Δ Γ A L M N} :
      HasType Δ Γ L .nat →
      HasType Δ Γ M A →
      HasType Δ (.nat :: Γ) N A →
      HasType Δ Γ (.natCase L M N) A
  | t_if {Δ Γ A L M N} :
      HasType Δ Γ L .bool →
      HasType Δ Γ M A →
      HasType Δ Γ N A →
      HasType Δ Γ (.ite L M N) A
  | t_tlam {Δ Γ N A} :
      HasType (Δ + 1) (liftCtx Γ) N A →
      HasType Δ Γ (.tlam N) (.all A)
  | t_tapp {Δ Γ M A B} :
      HasType Δ Γ M (.all A) →
      WfTy Δ B →
      HasType Δ Γ (.tapp M) (substOneT A B)

end Extrinsic

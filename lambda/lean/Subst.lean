import Lambda

namespace Subst

open Lambda

-------------------------------------------------------------------------------
-- 1. SIGMA-CALCULUS DEFINITIONS
-------------------------------------------------------------------------------

abbrev Ren := Nat → Nat
abbrev Sub := Nat → Term

def seq (σ₁ : Sub) (σ₂ : Sub) : Sub :=
  fun i => subst σ₂ (σ₁ i)

infixr:50 " ⨟ " => seq

def subst_one_at_one (N : Term) (M : Term) : Term :=
  subst (exts (fun i => match i with | 0 => M | j + 1 => .var j)) N

-------------------------------------------------------------------------------
-- 2. CORE SUBSTITUTION THEOREMS
-------------------------------------------------------------------------------

theorem ext_comp (ρ₁ ρ₂ : Ren) :
  (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ n => rfl

theorem rename_rename_commute (ρ₁ ρ₂ : Ren) (M : Term) :
  rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M := by
  induction M generalizing ρ₁ ρ₂ with
  | var i =>
    rfl
  | lam N ih =>
    simp only [rename]
    rw [ih (ext ρ₁) (ext ρ₂), ext_comp]
  | app L R ihL ihR =>
    simp only [rename]
    rw [ihL, ihR]

theorem exts_ext_comp (ρ : Ren) (τ : Sub) :
  (fun i => exts τ (ext ρ i)) = exts (fun i => τ (ρ i)) := by
  funext i
  cases i with
  | zero =>
    rfl
  | succ n =>
    rfl

theorem rename_subst_commute (ρ : Ren) (τ : Sub) (M : Term) :
  subst τ (rename ρ M) = subst (fun i => τ (ρ i)) M := by
  induction M generalizing ρ τ with
  | var i =>
    rfl
  | lam N ih =>
    simp only [rename, subst]
    rw [ih (ext ρ) (exts τ), exts_ext_comp]
  | app L R ihL ihR =>
    simp only [rename, subst]
    rw [ihL, ihR]

theorem ext_exts_comp (ρ : Ren) (τ : Sub) :
  (fun i => rename (ext ρ) (exts τ i)) = exts (fun i => rename ρ (τ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    change rename (ext ρ) (rename Nat.succ (τ j)) = rename Nat.succ (rename ρ (τ j))
    rw [rename_rename_commute, rename_rename_commute]
    rfl

theorem rename_subst (ρ : Ren) (τ : Sub) (M : Term) :
  rename ρ (subst τ M) = subst (fun i => rename ρ (τ i)) M := by
  induction M generalizing ρ τ with
  | var i => rfl
  | lam N ih =>
    simp only [rename, subst]
    rw [ih, ext_exts_comp]
  | app L R ihL ihR =>
    simp only [rename, subst]
    rw [ihL, ihR]

theorem exts_seq (σ τ : Sub) :
  (exts σ ⨟ exts τ) = exts (σ ⨟ τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    dsimp [seq, exts]
    rw [rename_subst_commute, rename_subst]
    rfl

theorem sub_sub (σ τ : Sub) (M : Term) :
  subst τ (subst σ M) = subst (σ ⨟ τ) M := by
  induction M generalizing σ τ with
  | var i =>
    rfl
  | lam N ih =>
    simp only [subst]
    rw [ih, exts_seq]
  | app L R ihL ihR =>
    simp only [subst]
    rw [ihL, ihR]

theorem subst_id (M : Term) : subst Term.var M = M := by
  induction M with
  | var i => rfl
  | lam N ih =>
    simp only [subst]
    have h_exts : exts Term.var = Term.var := by
      funext i
      cases i <;> rfl
    rw [h_exts, ih]
  | app L R ihL ihR =>
    simp only [subst]
    rw [ihL, ihR]

theorem substitution {M N L : Term} :
  single_subst (single_subst M N) L =
    single_subst (subst_one_at_one M L) (single_subst N L) := by
  dsimp only [single_subst, subst_one_at_one]
  rw [sub_sub, sub_sub]
  apply congrArg (fun (σ : Sub) => subst σ M)
  funext i
  cases i with
  | zero =>
    rfl
  | succ j =>
    cases j with
    | zero =>
      change L = subst (fun x => match x with | 0 => single_subst N L | y + 1 => Term.var y)
        (rename Nat.succ L)
      symm
      rw [rename_subst_commute]
      change subst Term.var L = L
      exact subst_id L
    | succ k =>
      rfl

theorem exts_sub_cons {σ : Sub} {N : Term} {V : Term} :
  single_subst (subst (exts σ) N) V =
    subst (fun i => match i with | 0 => V | j + 1 => σ j) N := by
  dsimp only [single_subst]
  rw [sub_sub]
  apply congrArg (fun (env : Sub) => subst env N)
  funext i
  cases i with
  | zero =>
    rfl
  | succ j =>
    dsimp only [seq, exts]
    rw [rename_subst_commute]
    change subst Term.var (σ j) = σ j
    exact subst_id (σ j)

end Subst

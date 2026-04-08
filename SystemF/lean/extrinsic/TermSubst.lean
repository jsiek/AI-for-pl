import extrinsic.TypeTermSubst
import extrinsic.Ctx

namespace Extrinsic

-- File Charter:
--   * Term-level renaming/substitution metatheory for `extrinsic.Terms`.
--   * Keeps congruence, composition, identity, and cons-extension lemmas.
--   * Provides the substitution/renaming interaction needed by preservation.

theorem ext_cong {ρ ρ' : Rename} :
    (∀ i, ρ i = ρ' i) → ∀ i, ext ρ i = ext ρ' i
  | h, 0 => rfl
  | h, i + 1 => by simpa [ext] using congrArg Nat.succ (h i)

theorem exts_cong {σ τ : Subst} :
    (∀ i, σ i = τ i) → ∀ i, exts σ i = exts τ i
  | h, 0 => rfl
  | h, i + 1 => by simpa [exts] using congrArg (rename Nat.succ) (h i)

theorem up_cong {σ τ : Subst} :
    (∀ i, σ i = τ i) → ∀ i, up σ i = up τ i
  | h, i => by simpa [up] using congrArg (renameTT Nat.succ) (h i)

theorem rename_cong_tm {ρ ρ' : Rename} :
    (∀ i, ρ i = ρ' i) → ∀ M, rename ρ M = rename ρ' M
  | h, Term.var i => by simpa [rename, h i]
  | h, Term.lam A N => by
      simpa [rename] using congrArg (Term.lam A) (rename_cong_tm (ext_cong h) N)
  | h, Term.app L M => by simp [rename, rename_cong_tm h L, rename_cong_tm h M]
  | h, Term.ttrue => rfl
  | h, Term.tfalse => rfl
  | h, Term.zero => rfl
  | h, Term.suc M => by simpa [rename] using congrArg Term.suc (rename_cong_tm h M)
  | h, Term.natCase L M N => by
      simp [rename, rename_cong_tm h L, rename_cong_tm h M, rename_cong_tm (ext_cong h) N]
  | h, Term.ite L M N => by
      simp [rename, rename_cong_tm h L, rename_cong_tm h M, rename_cong_tm h N]
  | h, Term.tlam N => by simpa [rename] using congrArg Term.tlam (rename_cong_tm h N)
  | h, Term.tapp M A => by simpa [rename] using congrArg (fun T => Term.tapp T A) (rename_cong_tm h M)

theorem subst_cong_tm {σ τ : Subst} :
    (∀ i, σ i = τ i) → ∀ M, subst σ M = subst τ M
  | h, Term.var i => h i
  | h, Term.lam A N => by
      simpa [subst] using congrArg (Term.lam A) (subst_cong_tm (exts_cong h) N)
  | h, Term.app L M => by simp [subst, subst_cong_tm h L, subst_cong_tm h M]
  | h, Term.ttrue => rfl
  | h, Term.tfalse => rfl
  | h, Term.zero => rfl
  | h, Term.suc M => by simpa [subst] using congrArg Term.suc (subst_cong_tm h M)
  | h, Term.natCase L M N => by
      simp [subst, subst_cong_tm h L, subst_cong_tm h M, subst_cong_tm (exts_cong h) N]
  | h, Term.ite L M N => by
      simp [subst, subst_cong_tm h L, subst_cong_tm h M, subst_cong_tm h N]
  | h, Term.tlam N => by
      simpa [subst] using congrArg Term.tlam (subst_cong_tm (up_cong h) N)
  | h, Term.tapp M A => by simpa [subst] using congrArg (fun T => Term.tapp T A) (subst_cong_tm h M)

theorem subst_cong_typed {Δ Γ M A σ τ}
    (hM : Δ ⊢ Γ ⊢ M ⦂ A)
    (hστ : ∀ {x C}, HasTypeVar Γ x C → σ x = τ x) :
    subst σ M = subst τ M := by
  induction hM generalizing σ τ with
  | t_var h =>
      simpa [subst] using hστ h
  | t_lam hA hN ih =>
      simp [subst, ih (σ := exts σ) (τ := exts τ) (by
        intro x C hx
        cases hx with
        | Z =>
            rfl
        | S hx' =>
            simpa [exts] using congrArg (rename Nat.succ) (hστ hx'))]
  | t_app hL hM ihL ihM =>
      simp [subst, ihL hστ, ihM hστ]
  | t_true =>
      rfl
  | t_false =>
      rfl
  | t_zero =>
      rfl
  | t_suc hM ih =>
      simpa [subst] using congrArg Term.suc (ih hστ)
  | t_case hL hM hN ihL ihM ihN =>
      simp [subst, ihL hστ, ihM hστ,
        ihN (σ := exts σ) (τ := exts τ) (by
          intro x C hx
          cases hx with
          | Z =>
              rfl
          | S hx' =>
              simpa [exts] using congrArg (rename Nat.succ) (hστ hx'))]
  | t_if hL hM hN ihL ihM ihN =>
      simp [subst, ihL hστ, ihM hστ, ihN hστ]
  | t_tlam hN ih =>
      simp [subst, ih (σ := up σ) (τ := up τ) (by
        intro x C hx
        rcases lookup_map_inv (x := x) (B := C) (f := renameT Nat.succ) hx with
          ⟨C', ⟨hC', hEq⟩⟩
        simpa [up] using congrArg (renameTT Nat.succ) (hστ hC'))]
  | t_tapp hM hB ih =>
      simp [subst, ih hστ]

theorem ext_comp_tm (ρ₁ ρ₂ : Rename) :
    (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i <;> rfl

theorem rename_comp (ρ₁ ρ₂ : Rename) :
    ∀ M, rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M
  | Term.var i => rfl
  | Term.lam A N => by
      simpa [rename] using congrArg (Term.lam A)
        (Eq.trans (rename_comp (ext ρ₁) (ext ρ₂) N)
          (rename_cong_tm (fun i => congrFun (ext_comp_tm ρ₁ ρ₂) i) N))
  | Term.app L M => by simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by simpa [rename] using congrArg Term.suc (rename_comp ρ₁ ρ₂ M)
  | Term.natCase L M N => by
      simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M,
        rename_comp (ext ρ₁) (ext ρ₂) N,
        rename_cong_tm (fun i => congrFun (ext_comp_tm ρ₁ ρ₂) i) N]
  | Term.ite L M N => by simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M, rename_comp ρ₁ ρ₂ N]
  | Term.tlam N => by simpa [rename] using congrArg Term.tlam (rename_comp ρ₁ ρ₂ N)
  | Term.tapp M A => by simpa [rename] using congrArg (fun T => Term.tapp T A) (rename_comp ρ₁ ρ₂ M)

theorem exts_ext (ρ : Rename) (σ : Subst) :
    (fun i => exts σ (ext ρ i)) = exts (fun y => σ (ρ y)) := by
  funext i
  cases i <;> rfl

theorem ren_sub (ρ : Rename) (σ : Subst) :
    ∀ M, subst σ (rename ρ M) = subst (fun x => σ (ρ x)) M
  | Term.var i => rfl
  | Term.lam A N => by
      simp [rename, subst, ren_sub (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (exts_ext ρ σ) i) N]
  | Term.app L M => by simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by simpa [rename, subst] using congrArg Term.suc (ren_sub ρ σ M)
  | Term.natCase L M N => by
      simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M,
        ren_sub (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (exts_ext ρ σ) i) N]
  | Term.ite L M N => by simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M, ren_sub ρ σ N]
  | Term.tlam N => by
      have hmain := ren_sub ρ (up σ) N
      have henv : (fun x => up σ (ρ x)) = up (fun y => σ (ρ y)) := by
        funext i
        rfl
      simpa [rename, subst, henv] using congrArg Term.tlam hmain
  | Term.tapp M A => by simpa [rename, subst] using congrArg (fun T => Term.tapp T A) (ren_sub ρ σ M)

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
  | Term.var i => rfl
  | Term.lam A N => by
      simp [rename, subst, sub_ren (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (ext_exts ρ σ) i) N]
  | Term.app L M => by simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by simpa [rename, subst] using congrArg Term.suc (sub_ren ρ σ M)
  | Term.natCase L M N => by
      simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M,
        sub_ren (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (ext_exts ρ σ) i) N]
  | Term.ite L M N => by simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M, sub_ren ρ σ N]
  | Term.tlam N => by
      have hmain := sub_ren ρ (up σ) N
      have henv : (fun i => rename ρ (up σ i)) = up (fun y => rename ρ (σ y)) := by
        funext i
        simpa [up] using rename_renameTT_commute ρ Nat.succ (σ i)
      simpa [rename, subst, henv] using congrArg Term.tlam hmain
  | Term.tapp M A => by simpa [rename, subst] using congrArg (fun T => Term.tapp T A) (sub_ren ρ σ M)

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
  | Term.var i => rfl
  | Term.lam A N => by
      simp [subst, sub_sub_tm (exts σ) (exts τ) N,
        subst_cong_tm (fun i => congrFun (exts_subst σ τ) i) N]
  | Term.app L M => by simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by simpa [subst] using congrArg Term.suc (sub_sub_tm σ τ M)
  | Term.natCase L M N => by
      simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M,
        sub_sub_tm (exts σ) (exts τ) N,
        subst_cong_tm (fun i => congrFun (exts_subst σ τ) i) N]
  | Term.ite L M N => by simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M, sub_sub_tm σ τ N]
  | Term.tlam N => by
      have hmain := sub_sub_tm (up σ) (up τ) N
      have henv : (up σ ⨟ up τ) = up (σ ⨟ τ) := by
        funext i
        change subst (up τ) (up σ i) = up (σ ⨟ τ) i
        change subst (up τ) (renameTT Nat.succ (σ i)) = renameTT Nat.succ (subst τ (σ i))
        simpa [up] using subst_renameTT_commute τ Nat.succ (σ i)
      simpa [subst, henv] using congrArg Term.tlam hmain
  | Term.tapp M A => by simpa [subst] using congrArg (fun T => Term.tapp T A) (sub_sub_tm σ τ M)

theorem exts_id : ∀ i, exts id i = id i
  | 0 => rfl
  | i + 1 => rfl

theorem up_id : ∀ i, up id i = id i
  | i => rfl

theorem sub_id : ∀ M, subst id M = M
  | Term.var i => rfl
  | Term.lam A N => by
      simpa [subst] using congrArg (Term.lam A) (Eq.trans (subst_cong_tm exts_id N) (sub_id N))
  | Term.app L M => by simp [subst, sub_id L, sub_id M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by simpa [subst] using congrArg Term.suc (sub_id M)
  | Term.natCase L M N => by
      simp [subst, sub_id L, sub_id M, Eq.trans (subst_cong_tm exts_id N) (sub_id N)]
  | Term.ite L M N => by simp [subst, sub_id L, sub_id M, sub_id N]
  | Term.tlam N => by
      simpa [subst] using congrArg Term.tlam (Eq.trans (subst_cong_tm up_id N) (sub_id N))
  | Term.tapp M A => by simpa [subst] using congrArg (fun T => Term.tapp T A) (sub_id M)

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

theorem exts_ren (ρ : Rename) :
    (fun i => exts (ren ρ) i) = ren (ext ρ) := by
  funext i
  cases i <;> rfl

theorem up_ren (ρ : Rename) :
    (fun i => up (ren ρ) i) = ren ρ := by
  funext i
  rfl

theorem subst_ren (ρ : Rename) :
    ∀ M, subst (ren ρ) M = rename ρ M
  | Term.var i => rfl
  | Term.lam A N => by
      simpa [subst, rename] using congrArg (Term.lam A)
        (Eq.trans (subst_cong_tm (fun i => congrFun (exts_ren ρ) i) N) (subst_ren (ext ρ) N))
  | Term.app L M => by simp [subst, rename, subst_ren ρ L, subst_ren ρ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by simpa [subst, rename] using congrArg Term.suc (subst_ren ρ M)
  | Term.natCase L M N => by
      simp [subst, rename, subst_ren ρ L, subst_ren ρ M,
        subst_ren (ext ρ) N,
        subst_cong_tm (fun i => congrFun (exts_ren ρ) i) N]
  | Term.ite L M N => by simp [subst, rename, subst_ren ρ L, subst_ren ρ M, subst_ren ρ N]
  | Term.tlam N => by
      simpa [subst, rename] using congrArg Term.tlam
        (Eq.trans (subst_cong_tm (fun i => congrFun (up_ren ρ) i) N) (subst_ren ρ N))
  | Term.tapp M A => by simpa [subst, rename] using congrArg (fun T => Term.tapp T A) (subst_ren ρ M)

end Extrinsic

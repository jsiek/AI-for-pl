import curry.Terms

-- File Charter:
--   * Term-level renaming/substitution metatheory for `curry.Terms`.
--   * Keeps congruence, composition, identity, and cons-extension lemmas.
--   * Provides substitution/renaming interaction used by downstream proofs.

namespace Curry

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
  | h, ˋi => by simpa [rename, h i]
  | h, ƛ N => by simpa [rename] using congrArg (fun T => ƛ T) (rename_cong_tm (ext_cong h) N)
  | h, (L ∙ M) => by simp [rename, rename_cong_tm h L, rename_cong_tm h M]
  | h, ˋtrue => rfl
  | h, ˋfalse => rfl
  | h, ˋzero => rfl
  | h, ˋsuc M => by simpa [rename] using congrArg (fun T => ˋsuc T) (rename_cong_tm h M)
  | h, caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [rename, rename_cong_tm h L, rename_cong_tm h M, rename_cong_tm (ext_cong h) N]
  | h, ˋif L then M else N => by
      simp [rename, rename_cong_tm h L, rename_cong_tm h M, rename_cong_tm h N]
  | h, Λ N => by simpa [rename] using congrArg (fun T => Λ T) (rename_cong_tm h N)
  | h, M ∙[] => by simpa [rename] using congrArg (fun T => T ∙[]) (rename_cong_tm h M)

theorem subst_cong_tm {σ τ : Subst} :
  (∀ i, σ i = τ i) → ∀ M, subst σ M = subst τ M
  | h, ˋi => h i
  | h, ƛ N => by simpa [subst] using congrArg (fun T => ƛ T) (subst_cong_tm (exts_cong h) N)
  | h, (L ∙ M) => by simp [subst, subst_cong_tm h L, subst_cong_tm h M]
  | h, ˋtrue => rfl
  | h, ˋfalse => rfl
  | h, ˋzero => rfl
  | h, ˋsuc M => by simpa [subst] using congrArg (fun T => ˋsuc T) (subst_cong_tm h M)
  | h, caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [subst, subst_cong_tm h L, subst_cong_tm h M, subst_cong_tm (exts_cong h) N]
  | h, ˋif L then M else N => by
      simp [subst, subst_cong_tm h L, subst_cong_tm h M, subst_cong_tm h N]
  | h, Λ N => by simpa [subst] using congrArg (fun T => Λ T) (subst_cong_tm h N)
  | h, M ∙[] => by simpa [subst] using congrArg (fun T => T ∙[]) (subst_cong_tm h M)

theorem ext_comp_tm (ρ₁ ρ₂ : Rename) :
  (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i <;> rfl

theorem rename_comp (ρ₁ ρ₂ : Rename) :
  ∀ M, rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M
  | ˋi => rfl
  | ƛ N => by
      calc
        rename ρ₂ (rename ρ₁ (ƛ N))
            = ƛ (rename (ext ρ₂) (rename (ext ρ₁) N)) := rfl
        _ = ƛ (rename (fun i => ext ρ₂ (ext ρ₁ i)) N) := by
              simpa using congrArg (fun T => ƛ T) (rename_comp (ext ρ₁) (ext ρ₂) N)
        _ = ƛ (rename (ext (fun i => ρ₂ (ρ₁ i))) N) := by
              apply congrArg (fun T => ƛ T)
              exact rename_cong_tm (fun i => congrFun (ext_comp_tm ρ₁ ρ₂) i) N
        _ = rename (fun i => ρ₂ (ρ₁ i)) (ƛ N) := rfl
  | (L ∙ M) => by simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M]
  | ˋtrue => rfl
  | ˋfalse => rfl
  | ˋzero => rfl
  | ˋsuc M => by simpa [rename] using congrArg (fun T => ˋsuc T) (rename_comp ρ₁ ρ₂ M)
  | caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M,
        rename_comp (ext ρ₁) (ext ρ₂) N,
        rename_cong_tm (fun i => congrFun (ext_comp_tm ρ₁ ρ₂) i) N]
  | ˋif L then M else N => by simp [rename, rename_comp ρ₁ ρ₂ L, rename_comp ρ₁ ρ₂ M, rename_comp ρ₁ ρ₂ N]
  | Λ N => by simpa [rename] using congrArg (fun T => Λ T) (rename_comp ρ₁ ρ₂ N)
  | M ∙[] => by simpa [rename] using congrArg (fun T => T ∙[]) (rename_comp ρ₁ ρ₂ M)

theorem exts_ext (ρ : Rename) (σ : Subst) :
  (fun i => exts σ (ext ρ i)) = exts (fun y => σ (ρ y)) := by
  funext i
  cases i <;> rfl

theorem ren_sub (ρ : Rename) (σ : Subst) :
  ∀ M, subst σ (rename ρ M) = subst (fun x => σ (ρ x)) M
  | ˋi => rfl
  | ƛ N => by
      simp [rename, subst, ren_sub (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (exts_ext ρ σ) i) N]
  | (L ∙ M) => by simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M]
  | ˋtrue => rfl
  | ˋfalse => rfl
  | ˋzero => rfl
  | ˋsuc M => by simpa [rename, subst] using congrArg (fun T => ˋsuc T) (ren_sub ρ σ M)
  | caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M,
        ren_sub (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (exts_ext ρ σ) i) N]
  | ˋif L then M else N => by simp [rename, subst, ren_sub ρ σ L, ren_sub ρ σ M, ren_sub ρ σ N]
  | Λ N => by
      simpa [rename, subst, up, renameTT] using
        congrArg (fun T => Λ T) (ren_sub ρ (up σ) N)
  | M ∙[] => by simpa [rename, subst] using congrArg (fun T => T ∙[]) (ren_sub ρ σ M)

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
  | ˋi => rfl
  | ƛ N => by
      simp [rename, subst, sub_ren (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (ext_exts ρ σ) i) N]
  | (L ∙ M) => by simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M]
  | ˋtrue => rfl
  | ˋfalse => rfl
  | ˋzero => rfl
  | ˋsuc M => by simpa [rename, subst] using congrArg (fun T => ˋsuc T) (sub_ren ρ σ M)
  | caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M,
        sub_ren (ext ρ) (exts σ) N,
        subst_cong_tm (fun i => congrFun (ext_exts ρ σ) i) N]
  | ˋif L then M else N => by simp [rename, subst, sub_ren ρ σ L, sub_ren ρ σ M, sub_ren ρ σ N]
  | Λ N => by
      simpa [rename, subst, up, renameTT] using congrArg (fun T => Λ T) (sub_ren ρ (up σ) N)
  | M ∙[] => by simpa [rename, subst] using congrArg (fun T => T ∙[]) (sub_ren ρ σ M)

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
  | ˋi => rfl
  | ƛ N => by
      simp [subst, sub_sub_tm (exts σ) (exts τ) N,
        subst_cong_tm (fun i => congrFun (exts_subst σ τ) i) N]
  | (L ∙ M) => by simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M]
  | ˋtrue => rfl
  | ˋfalse => rfl
  | ˋzero => rfl
  | ˋsuc M => by simpa [subst] using congrArg (fun T => ˋsuc T) (sub_sub_tm σ τ M)
  | caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M,
        sub_sub_tm (exts σ) (exts τ) N,
        subst_cong_tm (fun i => congrFun (exts_subst σ τ) i) N]
  | ˋif L then M else N => by simp [subst, sub_sub_tm σ τ L, sub_sub_tm σ τ M, sub_sub_tm σ τ N]
  | Λ N => by
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
  | M ∙[] => by simpa [subst] using congrArg (fun T => T ∙[]) (sub_sub_tm σ τ M)

theorem exts_id : ∀ i, exts id i = id i
  | 0 => rfl
  | i + 1 => rfl

theorem sub_id : ∀ M, subst id M = M
  | ˋi => rfl
  | ƛ N => by
      simpa [subst] using congrArg (fun T => ƛ T) (Eq.trans (subst_cong_tm exts_id N) (sub_id N))
  | (L ∙ M) => by simp [subst, sub_id L, sub_id M]
  | ˋtrue => rfl
  | ˋfalse => rfl
  | ˋzero => rfl
  | ˋsuc M => by simpa [subst] using congrArg (fun T => ˋsuc T) (sub_id M)
  | caseₜ L [zero⇒ M |suc⇒ N] => by
      simp [subst, sub_id L, sub_id M, Eq.trans (subst_cong_tm exts_id N) (sub_id N)]
  | ˋif L then M else N => by simp [subst, sub_id L, sub_id M, sub_id N]
  | Λ N => by
      have hN : subst (up id) N = N := by simpa [up, renameTT] using sub_id N
      simpa [subst] using congrArg (fun T => Λ T) hN
  | M ∙[] => by simpa [subst] using congrArg (fun T => T ∙[]) (sub_id M)

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
                _ = subst (fun y => ˋy) (σ x) := by
                      apply subst_cong_tm
                      intro y
                      rfl
                _ = σ x := sub_id (σ x)
                _ = (V • σ) (x + 1) := rfl

end Curry

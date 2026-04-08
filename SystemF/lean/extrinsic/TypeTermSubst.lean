import extrinsic.Terms

namespace Extrinsic

-- Three-argument congruence helper used throughout substitution proofs.
theorem cong₃ {A B C D : Sort _}
    (f : A → B → C → D)
    {x x' : A} {y y' : B} {z z' : C}
    (hx : x = x') (hy : y = y') (hz : z = z') :
    f x y z = f x' y' z' := by
  cases hx
  cases hy
  cases hz
  rfl

theorem extT_cong {ρ ρ' : RenameT} :
    (∀ i, ρ i = ρ' i) → ∀ i, extT ρ i = extT ρ' i
  | h, 0 => rfl
  | h, i + 1 => by simpa [extT] using congrArg Nat.succ (h i)

theorem renameTT_cong {ρ ρ' : RenameT} :
    (∀ i, ρ i = ρ' i) → ∀ M, renameTT ρ M = renameTT ρ' M
  | h, Term.var i => rfl
  | h, Term.lam A N => by
      simp [renameTT, rename_cong h A, renameTT_cong h N]
  | h, Term.app L M => by simp [renameTT, renameTT_cong h L, renameTT_cong h M]
  | h, Term.ttrue => rfl
  | h, Term.tfalse => rfl
  | h, Term.zero => rfl
  | h, Term.suc M => by simpa [renameTT] using congrArg Term.suc (renameTT_cong h M)
  | h, Term.natCase L M N => by
      simp [renameTT, renameTT_cong h L, renameTT_cong h M, renameTT_cong h N]
  | h, Term.ite L M N => by
      simp [renameTT, renameTT_cong h L, renameTT_cong h M, renameTT_cong h N]
  | h, Term.tlam N => by
      simpa [renameTT] using congrArg Term.tlam (renameTT_cong (extT_cong h) N)
  | h, Term.tapp M A => by
      simp [renameTT, renameTT_cong h M, rename_cong h A]

theorem substTT_cong {σ τ : SubstT} :
    (∀ i, σ i = τ i) → ∀ M, substTT σ M = substTT τ M
  | h, Term.var i => rfl
  | h, Term.lam A N => by
      simp [substTT, subst_cong h A, substTT_cong h N]
  | h, Term.app L M => by
      simp [substTT, substTT_cong h L, substTT_cong h M]
  | h, Term.ttrue => rfl
  | h, Term.tfalse => rfl
  | h, Term.zero => rfl
  | h, Term.suc M => by simpa [substTT] using congrArg Term.suc (substTT_cong h M)
  | h, Term.natCase L M N => by
      simp [substTT, substTT_cong h L, substTT_cong h M, substTT_cong h N]
  | h, Term.ite L M N => by
      simp [substTT, substTT_cong h L, substTT_cong h M, substTT_cong h N]
  | h, Term.tlam N => by
      simpa [substTT] using congrArg Term.tlam (substTT_cong (fun i => by
        cases i with
        | zero => rfl
        | succ j => simpa [extsT] using congrArg (renameT Nat.succ) (h j)) N)
  | h, Term.tapp M A => by
      simp [substTT, substTT_cong h M, subst_cong h A]

theorem substTT_substTT (τ σ : SubstT) :
    ∀ M, substTT τ (substTT σ M) = substTT (σ ⨟ᵗ τ) M
  | Term.var i => rfl
  | Term.lam A N => by
      simp [substTT, sub_sub, substTT_substTT τ σ N]
  | Term.app L M => by
      simp [substTT, substTT_substTT τ σ L, substTT_substTT τ σ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [substTT] using congrArg Term.suc (substTT_substTT τ σ M)
  | Term.natCase L M N => by
      simp [substTT, substTT_substTT τ σ L, substTT_substTT τ σ M, substTT_substTT τ σ N]
  | Term.ite L M N => by
      simp [substTT, substTT_substTT τ σ L, substTT_substTT τ σ M, substTT_substTT τ σ N]
  | Term.tlam N => by
      simpa [substTT] using congrArg Term.tlam
        (Eq.trans (substTT_substTT (extsT τ) (extsT σ) N)
          (substTT_cong (fun i => congrFun (exts_seq σ τ) i) N))
  | Term.tapp M A => by
      simp [substTT, sub_sub, substTT_substTT τ σ M]

theorem renameTT_renameTT (ρ₁ ρ₂ : RenameT) :
    ∀ M, renameTT ρ₂ (renameTT ρ₁ M) = renameTT (fun i => ρ₂ (ρ₁ i)) M
  | Term.var i => rfl
  | Term.lam A N => by
      simp [renameTT, rename_rename_commute, renameTT_renameTT ρ₁ ρ₂ N]
  | Term.app L M => by
      simp [renameTT, renameTT_renameTT ρ₁ ρ₂ L, renameTT_renameTT ρ₁ ρ₂ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [renameTT] using congrArg Term.suc (renameTT_renameTT ρ₁ ρ₂ M)
  | Term.natCase L M N => by
      simp [renameTT, renameTT_renameTT ρ₁ ρ₂ L, renameTT_renameTT ρ₁ ρ₂ M, renameTT_renameTT ρ₁ ρ₂ N]
  | Term.ite L M N => by
      simp [renameTT, renameTT_renameTT ρ₁ ρ₂ L, renameTT_renameTT ρ₁ ρ₂ M, renameTT_renameTT ρ₁ ρ₂ N]
  | Term.tlam N => by
      simpa [renameTT] using congrArg Term.tlam
        (Eq.trans (renameTT_renameTT (extT ρ₁) (extT ρ₂) N)
          (renameTT_cong (fun i => congrFun (ext_comp ρ₁ ρ₂) i) N))
  | Term.tapp M A => by
      simp [renameTT, renameTT_renameTT ρ₁ ρ₂ M, rename_rename_commute]

theorem renameTT_suc_extT (ρt : RenameT) :
    ∀ M, renameTT Nat.succ (renameTT ρt M) = renameTT (extT ρt) (renameTT Nat.succ M)
  | M => by
      calc
        renameTT Nat.succ (renameTT ρt M)
            = renameTT (fun i => Nat.succ (ρt i)) M := by
                exact renameTT_renameTT ρt Nat.succ M
        _ = renameTT (fun i => extT ρt (Nat.succ i)) M := by
              apply renameTT_cong
              intro i
              rfl
        _ = renameTT (extT ρt) (renameTT Nat.succ M) := by
              symm
              exact renameTT_renameTT Nat.succ (extT ρt) M

theorem rename_renameTT_commute (ρ : Rename) (ρt : RenameT) :
    ∀ M, rename ρ (renameTT ρt M) = renameTT ρt (rename ρ M)
  | Term.var i => rfl
  | Term.lam A N => by
      simp [rename, renameTT, rename_renameTT_commute (ext ρ) ρt N]
  | Term.app L M => by
      simp [rename, renameTT, rename_renameTT_commute ρ ρt L, rename_renameTT_commute ρ ρt M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [rename, renameTT] using congrArg Term.suc (rename_renameTT_commute ρ ρt M)
  | Term.natCase L M N => by
      simp [rename, renameTT,
        rename_renameTT_commute ρ ρt L,
        rename_renameTT_commute ρ ρt M,
        rename_renameTT_commute (ext ρ) ρt N]
  | Term.ite L M N => by
      simp [rename, renameTT,
        rename_renameTT_commute ρ ρt L,
        rename_renameTT_commute ρ ρt M,
        rename_renameTT_commute ρ ρt N]
  | Term.tlam N => by
      simpa [rename, renameTT] using congrArg Term.tlam (rename_renameTT_commute ρ (extT ρt) N)
  | Term.tapp M A => by
      simp [rename, renameTT, rename_renameTT_commute ρ ρt M]

theorem rename_substTT_commute (ρ : Rename) (σt : SubstT) :
    ∀ M, rename ρ (substTT σt M) = substTT σt (rename ρ M)
  | Term.var i => rfl
  | Term.lam A N => by
      simp [rename, substTT, rename_substTT_commute (ext ρ) σt N]
  | Term.app L M => by
      simp [rename, substTT, rename_substTT_commute ρ σt L, rename_substTT_commute ρ σt M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [rename, substTT] using congrArg Term.suc (rename_substTT_commute ρ σt M)
  | Term.natCase L M N => by
      simp [rename, substTT,
        rename_substTT_commute ρ σt L,
        rename_substTT_commute ρ σt M,
        rename_substTT_commute (ext ρ) σt N]
  | Term.ite L M N => by
      simp [rename, substTT,
        rename_substTT_commute ρ σt L,
        rename_substTT_commute ρ σt M,
        rename_substTT_commute ρ σt N]
  | Term.tlam N => by
      simp [rename, substTT, rename_substTT_commute ρ (extsT σt) N]
  | Term.tapp M A => by
      simp [rename, substTT, rename_substTT_commute ρ σt M]

theorem substTT_renameTT_commute (ρt : RenameT) (τ : SubstT) :
    ∀ M, substTT τ (renameTT ρt M) = substTT (fun i => τ (ρt i)) M
  | Term.var i => rfl
  | Term.lam A N => by
      simp [renameTT, substTT, rename_subst_commute, substTT_renameTT_commute ρt τ N]
  | Term.app L M => by
      simp [renameTT, substTT, substTT_renameTT_commute ρt τ L, substTT_renameTT_commute ρt τ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [renameTT, substTT] using congrArg Term.suc (substTT_renameTT_commute ρt τ M)
  | Term.natCase L M N => by
      simp [renameTT, substTT,
        substTT_renameTT_commute ρt τ L,
        substTT_renameTT_commute ρt τ M,
        substTT_renameTT_commute ρt τ N]
  | Term.ite L M N => by
      simp [renameTT, substTT,
        substTT_renameTT_commute ρt τ L,
        substTT_renameTT_commute ρt τ M,
        substTT_renameTT_commute ρt τ N]
  | Term.tlam N => by
      simp [renameTT, substTT]
      calc
        substTT (extsT τ) (renameTT (extT ρt) N)
            = substTT (fun i => extsT τ (extT ρt i)) N := by
                exact substTT_renameTT_commute (extT ρt) (extsT τ) N
        _ = substTT (extsT (fun j => τ (ρt j))) N := by
              apply substTT_cong
              intro i
              exact congrFun (exts_ext_comp ρt τ) i
        _ = substTT (extsT (fun i => τ (ρt i))) N := rfl
  | Term.tapp M A => by
      simp [renameTT, substTT, rename_subst_commute, substTT_renameTT_commute ρt τ M]

theorem renameTT_substTT (ρt : RenameT) (τ : SubstT) :
    ∀ M, renameTT ρt (substTT τ M) = substTT (fun i => renameT ρt (τ i)) M
  | Term.var i => rfl
  | Term.lam A N => by
      simp [renameTT, substTT, rename_subst, renameTT_substTT ρt τ N]
  | Term.app L M => by
      simp [renameTT, substTT, renameTT_substTT ρt τ L, renameTT_substTT ρt τ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [renameTT, substTT] using congrArg Term.suc (renameTT_substTT ρt τ M)
  | Term.natCase L M N => by
      simp [renameTT, substTT,
        renameTT_substTT ρt τ L,
        renameTT_substTT ρt τ M,
        renameTT_substTT ρt τ N]
  | Term.ite L M N => by
      simp [renameTT, substTT,
        renameTT_substTT ρt τ L,
        renameTT_substTT ρt τ M,
        renameTT_substTT ρt τ N]
  | Term.tlam N => by
      simp [renameTT, substTT]
      calc
        renameTT (extT ρt) (substTT (extsT τ) N)
            = substTT (fun i => renameT (extT ρt) (extsT τ i)) N := by
                exact renameTT_substTT (extT ρt) (extsT τ) N
        _ = substTT (extsT (fun j => renameT ρt (τ j))) N := by
              apply substTT_cong
              intro i
              exact congrFun (ext_exts_comp ρt τ) i
        _ = substTT (extsT (fun i => renameT ρt (τ i))) N := rfl
  | Term.tapp M A => by
      simp [renameTT, substTT, rename_subst, renameTT_substTT ρt τ M]

theorem renameTT_suc_extsT (τ : SubstT) :
    ∀ M, renameTT Nat.succ (substTT τ M) = substTT (extsT τ) (renameTT Nat.succ M)
  | M => by
      calc
        renameTT Nat.succ (substTT τ M)
            = substTT (fun i => renameT Nat.succ (τ i)) M := by
                exact renameTT_substTT Nat.succ τ M
        _ = substTT (fun i => extsT τ (Nat.succ i)) M := by
              apply substTT_cong
              intro i
              rfl
        _ = substTT (extsT τ) (renameTT Nat.succ M) := by
              symm
              exact substTT_renameTT_commute Nat.succ (extsT τ) M

theorem subst_substTT_commute_gen (σ τ : Subst) (σt : SubstT) :
    (∀ i, τ i = substTT σt (σ i)) →
    ∀ M, subst τ (substTT σt M) = substTT σt (subst σ M)
  | h, Term.var i => h i
  | h, Term.lam A N => by
      simp [subst, substTT]
      apply subst_substTT_commute_gen (exts σ) (exts τ) σt
      intro i
      cases i with
      | zero => rfl
      | succ j =>
          calc
            exts τ (j + 1)
                = rename Nat.succ (τ j) := rfl
            _ = rename Nat.succ (substTT σt (σ j)) := by simpa [h j]
            _ = substTT σt (rename Nat.succ (σ j)) := by
                  exact rename_substTT_commute Nat.succ σt (σ j)
            _ = substTT σt (exts σ (j + 1)) := rfl
  | h, Term.app L M => by
      simp [subst, substTT,
        subst_substTT_commute_gen σ τ σt h L,
        subst_substTT_commute_gen σ τ σt h M]
  | h, Term.ttrue => rfl
  | h, Term.tfalse => rfl
  | h, Term.zero => rfl
  | h, Term.suc M => by
      simpa [subst, substTT] using congrArg Term.suc (subst_substTT_commute_gen σ τ σt h M)
  | h, Term.natCase L M N => by
      simp [subst, substTT,
        subst_substTT_commute_gen σ τ σt h L,
        subst_substTT_commute_gen σ τ σt h M]
      apply subst_substTT_commute_gen (exts σ) (exts τ) σt
      intro i
      cases i with
      | zero => rfl
      | succ j =>
          calc
            exts τ (j + 1)
                = rename Nat.succ (τ j) := rfl
            _ = rename Nat.succ (substTT σt (σ j)) := by simpa [h j]
            _ = substTT σt (rename Nat.succ (σ j)) := by
                  exact rename_substTT_commute Nat.succ σt (σ j)
            _ = substTT σt (exts σ (j + 1)) := rfl
  | h, Term.ite L M N => by
      simp [subst, substTT,
        subst_substTT_commute_gen σ τ σt h L,
        subst_substTT_commute_gen σ τ σt h M,
        subst_substTT_commute_gen σ τ σt h N]
  | h, Term.tlam N => by
      simp [subst, substTT]
      apply subst_substTT_commute_gen (up σ) (up τ) (extsT σt)
      intro i
      calc
        up τ i = renameTT Nat.succ (τ i) := rfl
        _ = renameTT Nat.succ (substTT σt (σ i)) := by simpa [h i]
        _ = substTT (extsT σt) (renameTT Nat.succ (σ i)) := by
              exact renameTT_suc_extsT σt (σ i)
        _ = substTT (extsT σt) (up σ i) := rfl
  | h, Term.tapp M A => by
      simpa [subst, substTT] using congrArg (fun T => Term.tapp T (substT σt A))
        (subst_substTT_commute_gen σ τ σt h M)

theorem subst_substTT_commute (σ : Subst) (σt : SubstT) :
    ∀ M, subst (fun i => substTT σt (σ i)) (substTT σt M) = substTT σt (subst σ M) := by
  intro M
  exact subst_substTT_commute_gen σ (fun i => substTT σt (σ i)) σt (fun i => rfl) M

theorem subst_renameTT_commute_gen (σ τ : Subst) (ρt : RenameT) :
    (∀ i, τ i = renameTT ρt (σ i)) →
    ∀ M, subst τ (renameTT ρt M) = renameTT ρt (subst σ M)
  | h, Term.var i => h i
  | h, Term.lam A N => by
      simp [subst, renameTT]
      apply subst_renameTT_commute_gen (exts σ) (exts τ) ρt
      intro i
      cases i with
      | zero => rfl
      | succ j =>
          calc
            exts τ (j + 1)
                = rename Nat.succ (τ j) := rfl
            _ = rename Nat.succ (renameTT ρt (σ j)) := by simpa [h j]
            _ = renameTT ρt (rename Nat.succ (σ j)) := by
                  exact rename_renameTT_commute Nat.succ ρt (σ j)
            _ = renameTT ρt (exts σ (j + 1)) := rfl
  | h, Term.app L M => by
      simp [subst, renameTT,
        subst_renameTT_commute_gen σ τ ρt h L,
        subst_renameTT_commute_gen σ τ ρt h M]
  | h, Term.ttrue => rfl
  | h, Term.tfalse => rfl
  | h, Term.zero => rfl
  | h, Term.suc M => by
      simpa [subst, renameTT] using congrArg Term.suc (subst_renameTT_commute_gen σ τ ρt h M)
  | h, Term.natCase L M N => by
      simp [subst, renameTT,
        subst_renameTT_commute_gen σ τ ρt h L,
        subst_renameTT_commute_gen σ τ ρt h M]
      apply subst_renameTT_commute_gen (exts σ) (exts τ) ρt
      intro i
      cases i with
      | zero => rfl
      | succ j =>
          calc
            exts τ (j + 1)
                = rename Nat.succ (τ j) := rfl
            _ = rename Nat.succ (renameTT ρt (σ j)) := by simpa [h j]
            _ = renameTT ρt (rename Nat.succ (σ j)) := by
                  exact rename_renameTT_commute Nat.succ ρt (σ j)
            _ = renameTT ρt (exts σ (j + 1)) := rfl
  | h, Term.ite L M N => by
      simp [subst, renameTT,
        subst_renameTT_commute_gen σ τ ρt h L,
        subst_renameTT_commute_gen σ τ ρt h M,
        subst_renameTT_commute_gen σ τ ρt h N]
  | h, Term.tlam N => by
      simp [subst, renameTT]
      apply subst_renameTT_commute_gen (up σ) (up τ) (extT ρt)
      intro i
      calc
        up τ i = renameTT Nat.succ (τ i) := rfl
        _ = renameTT Nat.succ (renameTT ρt (σ i)) := by simpa [h i]
        _ = renameTT (extT ρt) (renameTT Nat.succ (σ i)) := by
              exact renameTT_suc_extT ρt (σ i)
        _ = renameTT (extT ρt) (up σ i) := rfl
  | h, Term.tapp M A => by
      simpa [subst, renameTT] using congrArg (fun T => Term.tapp T A)
        (subst_renameTT_commute_gen σ τ ρt h M)

theorem subst_renameTT_commute (σ : Subst) (ρt : RenameT) :
    ∀ M, subst (fun i => renameTT ρt (σ i)) (renameTT ρt M) = renameTT ρt (subst σ M) := by
  intro M
  exact subst_renameTT_commute_gen σ (fun i => renameTT ρt (σ i)) ρt (fun i => rfl) M

end Extrinsic

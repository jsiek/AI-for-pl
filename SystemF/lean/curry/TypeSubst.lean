import curry.Types

-- File Charter:
--   * Type-level substitution composition utilities for curry System F.
--   * Proves congruence/commutation lemmas for renaming and substitution.
--   * Provides single-substitution helpers used by metatheory modules.

namespace Curry

infixr:67 " ⨟ᵗ " => fun (σ₁ : SubstT) (σ₂ : SubstT) i => substT σ₂ (σ₁ i)

def substOneAtOne (A B : Ty) : Ty :=
  substT (extsT (singleTyEnv B)) A

theorem single_subst_def (A B : Ty) :
    A [ B ]ₜ = substT (singleTyEnv B) A := rfl

theorem substOneAtOne_def (A B : Ty) :
    substOneAtOne A B = substT (extsT (singleTyEnv B)) A := rfl

theorem rename_cong {ρ ρ' : RenameT} (h : ∀ i, ρ i = ρ' i) :
    ∀ A, renameT ρ A = renameT ρ' A
  | #i => by simpa [renameT, h i]
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by
      simp [renameT, rename_cong h A, rename_cong h B]
  | ∀ₜ A => by
      refine congrArg (fun T => ∀ₜ T) ?_
      apply rename_cong
      intro i
      cases i with
      | zero => rfl
      | succ j => simpa [extT] using congrArg Nat.succ (h j)

theorem subst_cong {σ τ : SubstT} (h : ∀ i, σ i = τ i) :
    ∀ A, substT σ A = substT τ A
  | #i => by simpa [substT, h i]
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by
      simp [substT, subst_cong h A, subst_cong h B]
  | ∀ₜ A => by
      refine congrArg (fun T => ∀ₜ T) ?_
      apply subst_cong
      intro i
      cases i with
      | zero => rfl
      | succ j => simpa [extsT] using congrArg (renameT Nat.succ) (h j)

theorem ext_comp (ρ₁ ρ₂ : RenameT) :
    (fun i => extT ρ₂ (extT ρ₁ i)) = extT (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i <;> rfl

theorem rename_rename_commute (ρ₁ ρ₂ : RenameT) :
    ∀ A, renameT ρ₂ (renameT ρ₁ A) = renameT (fun i => ρ₂ (ρ₁ i)) A
  | #i => rfl
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by
      simp [renameT, rename_rename_commute ρ₁ ρ₂ A, rename_rename_commute ρ₁ ρ₂ B]
  | ∀ₜ A => by
      simp [renameT]
      rw [rename_rename_commute (extT ρ₁) (extT ρ₂) A, ext_comp]

theorem exts_ext_comp (ρ : RenameT) (τ : SubstT) :
    (fun i => extsT τ (extT ρ i)) = extsT (fun j => τ (ρ j)) := by
  funext i
  cases i <;> rfl

theorem rename_subst_commute (ρ : RenameT) (τ : SubstT) :
    ∀ A, substT τ (renameT ρ A) = substT (fun i => τ (ρ i)) A
  | #i => rfl
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by
      simp [renameT, substT, rename_subst_commute ρ τ A, rename_subst_commute ρ τ B]
  | ∀ₜ A => by
      simp [renameT, substT]
      rw [rename_subst_commute (extT ρ) (extsT τ) A, exts_ext_comp ρ τ]

theorem ext_exts_comp (ρ : RenameT) (τ : SubstT) :
    (fun i => renameT (extT ρ) (extsT τ i)) = extsT (fun j => renameT ρ (τ j)) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      change renameT (extT ρ) (renameT Nat.succ (τ j)) = renameT Nat.succ (renameT ρ (τ j))
      rw [rename_rename_commute Nat.succ (extT ρ), rename_rename_commute ρ Nat.succ]
      rfl

theorem rename_subst (ρ : RenameT) (τ : SubstT) :
    ∀ A, renameT ρ (substT τ A) = substT (fun i => renameT ρ (τ i)) A
  | #i => rfl
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by
      simp [renameT, substT, rename_subst ρ τ A, rename_subst ρ τ B]
  | ∀ₜ A => by
      simp [renameT, substT]
      rw [rename_subst (extT ρ) (extsT τ) A, ext_exts_comp ρ τ]

theorem exts_seq (σ τ : SubstT) :
    (fun i => substT (extsT τ) (extsT σ i)) = extsT (σ ⨟ᵗ τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      dsimp [extsT]
      rw [rename_subst_commute Nat.succ (extsT τ), rename_subst Nat.succ τ]
      rfl

theorem sub_sub (σ τ : SubstT) :
    ∀ A, substT τ (substT σ A) = substT (σ ⨟ᵗ τ) A
  | #i => rfl
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by
      simp [substT, sub_sub σ τ A, sub_sub σ τ B]
  | ∀ₜ A => by
      simp [substT]
      rw [sub_sub (extsT σ) (extsT τ) A]
      simpa using congrArg (fun env : SubstT => substT env A) (exts_seq σ τ)

theorem subst_id : ∀ A, substT idₜ A = A
  | #i => rfl
  | ℕ => rfl
  | 𝔹 => rfl
  | A ⇒ B => by simp [substT, subst_id A, subst_id B]
  | ∀ₜ A => by
      simp [substT]
      have h : extsT idₜ = idₜ := by
        funext i
        cases i <;> rfl
      rw [h, subst_id A]

theorem exts_sub_cons {σ : SubstT} {a v : Ty} :
    (substT (extsT σ) a) [ v ]ₜ = substT (v •ₜ σ) a := by
  dsimp [substOneT]
  rw [sub_sub]
  apply congrArg (fun env => substT env a)
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      change substT (singleTyEnv v) (renameT Nat.succ (σ j)) = σ j
      rw [rename_subst_commute Nat.succ (singleTyEnv v)]
      change substT idₜ (σ j) = σ j
      exact subst_id (σ j)

theorem rename_substOne_commute (ρ : RenameT) (A B : Ty) :
    renameT ρ (A [ B ]ₜ) = (renameT (extT ρ) A) [ renameT ρ B ]ₜ := by
  dsimp [substOneT]
  rw [rename_subst ρ (singleTyEnv B), rename_subst_commute (extT ρ) (singleTyEnv (renameT ρ B))]
  apply congrArg (fun env => substT env A)
  funext i
  cases i <;> rfl

theorem subst_substOne_commute (σ : SubstT) (A B : Ty) :
    substT σ (A [ B ]ₜ) = (substT (extsT σ) A) [ substT σ B ]ₜ := by
  dsimp [substOneT]
  rw [sub_sub, sub_sub]
  apply congrArg (fun env => substT env A)
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      change σ j = substT (singleTyEnv (substT σ B)) (renameT Nat.succ (σ j))
      symm
      rw [rename_subst_commute Nat.succ (singleTyEnv (substT σ B))]
      change substT idₜ (σ j) = σ j
      exact subst_id (σ j)

theorem substitution {a b c : Ty} :
    (a [ b ]ₜ) [ c ]ₜ = (substOneAtOne a c) [ (b [ c ]ₜ) ]ₜ := by
  dsimp [substOneT, substOneAtOne]
  exact subst_substOne_commute (singleTyEnv c) a b

def map_renameT_lift (ρ : RenameT) :
  ∀ Γ, List.map (renameT (extT ρ)) (liftCtx Γ) = liftCtx (List.map (renameT ρ) Γ)
  | [] => rfl
  | A :: Γ => by
      change
        renameT (extT ρ) (renameT Nat.succ A) :: List.map (renameT (extT ρ)) (liftCtx Γ) =
        renameT Nat.succ (renameT ρ A) :: liftCtx (List.map (renameT ρ) Γ)
      have hHead :
          renameT (extT ρ) (renameT Nat.succ A) = renameT Nat.succ (renameT ρ A) := by
        calc
          renameT (extT ρ) (renameT Nat.succ A)
              = renameT (fun i => extT ρ (Nat.succ i)) A := by
                  exact rename_rename_commute Nat.succ (extT ρ) A
          _ = renameT (fun i => Nat.succ (ρ i)) A := by rfl
          _ = renameT Nat.succ (renameT ρ A) := by
                symm
                exact rename_rename_commute ρ Nat.succ A
      calc
        renameT (extT ρ) (renameT Nat.succ A) :: List.map (renameT (extT ρ)) (liftCtx Γ)
            = renameT Nat.succ (renameT ρ A) :: List.map (renameT (extT ρ)) (liftCtx Γ) := by
                simpa [hHead]
        _ = renameT Nat.succ (renameT ρ A) :: liftCtx (List.map (renameT ρ) Γ) := by
              simpa [map_renameT_lift ρ Γ]

def map_substT_lift (σ : SubstT) :
  ∀ Γ, List.map (substT (extsT σ)) (liftCtx Γ) = liftCtx (List.map (substT σ) Γ)
  | [] => rfl
  | A :: Γ => by
      change
        substT (extsT σ) (renameT Nat.succ A) :: List.map (substT (extsT σ)) (liftCtx Γ) =
        renameT Nat.succ (substT σ A) :: liftCtx (List.map (substT σ) Γ)
      have hHead :
          substT (extsT σ) (renameT Nat.succ A) = renameT Nat.succ (substT σ A) := by
        calc
          substT (extsT σ) (renameT Nat.succ A)
              = substT (fun i => extsT σ (Nat.succ i)) A := by
                  exact rename_subst_commute Nat.succ (extsT σ) A
          _ = substT (fun i => renameT Nat.succ (σ i)) A := by rfl
          _ = renameT Nat.succ (substT σ A) := by
                symm
                exact rename_subst Nat.succ σ A
      calc
        substT (extsT σ) (renameT Nat.succ A) :: List.map (substT (extsT σ)) (liftCtx Γ)
            = renameT Nat.succ (substT σ A) :: List.map (substT (extsT σ)) (liftCtx Γ) := by
                simpa [hHead]
        _ = renameT Nat.succ (substT σ A) :: liftCtx (List.map (substT σ) Γ) := by
              simpa [map_substT_lift σ Γ]

def substT_renameT_cancel (C B : Ty) :
    substT (singleTyEnv B) (renameT Nat.succ C) = C := by
  calc
    substT (singleTyEnv B) (renameT Nat.succ C)
        = substT (fun i => singleTyEnv B (Nat.succ i)) C := by
            exact rename_subst_commute Nat.succ (singleTyEnv B) C
    _ = substT idₜ C := by
          apply subst_cong
          intro i
          rfl
    _ = C := subst_id C

def singleTySubst_lift_cancel :
    ∀ (Γ : Ctx) (B : Ty),
      List.map (substT (singleTyEnv B)) (liftCtx Γ) = Γ
  | [], _ => rfl
  | C :: Γ, B => by
      change
        substT (singleTyEnv B) (renameT Nat.succ C) ::
          List.map (substT (singleTyEnv B)) (liftCtx Γ) = C :: Γ
      simpa [substT_renameT_cancel C B] using congrArg (List.cons C) (singleTySubst_lift_cancel Γ B)

end Curry

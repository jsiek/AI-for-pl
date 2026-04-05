import extrinsic.Progress

namespace Extrinsic

noncomputable section

def TyRenameWf (Δ Δ' : TyCtx) (ρ : RenameT) : Prop :=
  ∀ {X}, X < Δ → ρ X < Δ'

def TySubstWf (Δ Δ' : TyCtx) (σ : SubstT) : Type :=
  ∀ {X}, X < Δ → WfTy Δ' (σ X)

def RenameWf (Γ Γ' : Ctx) (ρ : Rename) : Type :=
  ∀ {x A}, HasTypeVar Γ x A → HasTypeVar Γ' (ρ x) A

def SubstWf (Δ : TyCtx) (Γ Γ' : Ctx) (σ : Subst) : Type :=
  ∀ {x A}, HasTypeVar Γ x A → HasType Δ Γ' (σ x) A

-- Step 1 (from log strategy): context-map commutation lemmas.
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

def lookup_map_renameT :
  ∀ {Γ x A ρ},
    HasTypeVar Γ x A →
    HasTypeVar (List.map (renameT ρ) Γ) x (renameT ρ A)
  | _, _, _, _, .Z => .Z
  | _, _, _, _, .S h => .S (lookup_map_renameT h)

def lookup_map_substT :
  ∀ {Γ x A σ},
    HasTypeVar Γ x A →
    HasTypeVar (List.map (substT σ) Γ) x (substT σ A)
  | _, _, _, _, .Z => .Z
  | _, _, _, _, .S h => .S (lookup_map_substT h)

def tyRenameWf_ext {Δ Δ' ρ}
    (hρ : TyRenameWf Δ Δ' ρ) :
    TyRenameWf (Δ + 1) (Δ' + 1) (extT ρ) := by
  intro X
  intro hX
  cases X with
  | zero =>
      simpa [extT] using (Nat.zero_lt_succ Δ')
  | succ X =>
      have hX' : X < Δ := Nat.lt_of_succ_lt_succ hX
      simpa [extT] using Nat.succ_lt_succ (hρ hX')

def renameT_preserves_WfTy :
  ∀ {Δ Δ' A ρ},
    WfTy Δ A →
    TyRenameWf Δ Δ' ρ →
    WfTy Δ' (renameT ρ A)
  | _, _, _, _, .var hX, hρ => .var (hρ hX)
  | _, _, _, _, .nat, _ => .nat
  | _, _, _, _, .bool, _ => .bool
  | _, _, _, _, .fn hA hB, hρ =>
      .fn (renameT_preserves_WfTy hA hρ) (renameT_preserves_WfTy hB hρ)
  | _, _, _, _, .all hA, hρ =>
      .all (renameT_preserves_WfTy hA (tyRenameWf_ext hρ))

def tySubstWf_exts {Δ Δ' σ}
    (hσ : TySubstWf Δ Δ' σ) :
    TySubstWf (Δ + 1) (Δ' + 1) (extsT σ) := by
  intro X
  intro hX
  cases X with
  | zero =>
      simpa [extsT] using (WfTy.var (Δ := Δ' + 1) (X := 0) (Nat.zero_lt_succ Δ'))
  | succ X =>
      have hX' : X < Δ := Nat.lt_of_succ_lt_succ hX
      have hSucc : TyRenameWf Δ' (Δ' + 1) Nat.succ := by
        intro i hi
        exact Nat.succ_lt_succ hi
      simpa [extsT] using renameT_preserves_WfTy (hσ hX') hSucc

def substT_preserves_WfTy :
  ∀ {Δ Δ' A σ},
    WfTy Δ A →
    TySubstWf Δ Δ' σ →
    WfTy Δ' (substT σ A)
  | _, _, _, _, .var hX, hσ => hσ hX
  | _, _, _, _, .nat, _ => .nat
  | _, _, _, _, .bool, _ => .bool
  | _, _, _, _, .fn hA hB, hσ =>
      .fn (substT_preserves_WfTy hA hσ) (substT_preserves_WfTy hB hσ)
  | _, _, _, _, .all hA, hσ =>
      .all (substT_preserves_WfTy hA (tySubstWf_exts hσ))

def typing_renameTT :
  ∀ {Δ Δ' Γ M A ρ},
    TyRenameWf Δ Δ' ρ →
    HasType Δ Γ M A →
    HasType Δ' (List.map (renameT ρ) Γ) (renameTT ρ M) (renameT ρ A)
  | _, _, _, _, _, ρ, _, .t_var h => by
      simpa [renameTT] using HasType.t_var (lookup_map_renameT (ρ := ρ) h)
  | _, _, _, _, _, ρ, hρ, .t_lam hA hN => by
      refine HasType.t_lam (renameT_preserves_WfTy hA hρ) ?_
      simpa [renameTT, renameT] using typing_renameTT (ρ := ρ) hρ hN
  | _, _, _, _, _, ρ, hρ, .t_app hL hM => by
      simpa [renameTT, renameT] using HasType.t_app (typing_renameTT (ρ := ρ) hρ hL) (typing_renameTT (ρ := ρ) hρ hM)
  | _, Δ', Γ, _, _, ρ, _, .t_true => by
      simpa [renameTT, renameT] using (HasType.t_true : HasType Δ' (List.map (renameT ρ) Γ) .ttrue .bool)
  | _, Δ', Γ, _, _, ρ, _, .t_false => by
      simpa [renameTT, renameT] using (HasType.t_false : HasType Δ' (List.map (renameT ρ) Γ) .tfalse .bool)
  | _, Δ', Γ, _, _, ρ, _, .t_zero => by
      simpa [renameTT, renameT] using (HasType.t_zero : HasType Δ' (List.map (renameT ρ) Γ) .zero .nat)
  | _, _, _, _, _, ρ, hρ, .t_suc hM => by
      simpa [renameTT, renameT] using HasType.t_suc (typing_renameTT (ρ := ρ) hρ hM)
  | _, _, _, _, _, ρ, hρ, .t_case hL hM hN => by
      simpa [renameTT, renameT] using
        HasType.t_case (typing_renameTT (ρ := ρ) hρ hL) (typing_renameTT (ρ := ρ) hρ hM) (typing_renameTT (ρ := ρ) hρ hN)
  | _, _, _, _, _, ρ, hρ, .t_if hL hM hN => by
      simpa [renameTT, renameT] using
        HasType.t_if (typing_renameTT (ρ := ρ) hρ hL) (typing_renameTT (ρ := ρ) hρ hM) (typing_renameTT (ρ := ρ) hρ hN)
  | _, Δ', _, _, _, ρ, hρ, .t_tlam (Γ := Γ) (N := N) (A := A) hN => by
      have hNren :
          HasType (Δ' + 1) (List.map (renameT (extT ρ)) (liftCtx Γ))
            (renameTT (extT ρ) N) (renameT (extT ρ) A) :=
        typing_renameTT (Δ' := Δ' + 1) (ρ := extT ρ) (tyRenameWf_ext hρ) hN
      have hNren' :
          HasType (Δ' + 1) (liftCtx (List.map (renameT ρ) Γ))
            (renameTT (extT ρ) N) (renameT (extT ρ) A) := by
        refine Eq.ndrec
          (motive := fun Ψ =>
            HasType (Δ' + 1) Ψ (renameTT (extT ρ) N) (renameT (extT ρ) A))
          hNren (map_renameT_lift ρ Γ)
      have hNren'' :
          HasType (Δ' + 1) (liftCtx (List.map (renameT ρ) Γ))
            N (renameT (extT ρ) A) := by
        simpa [renameTT] using hNren'
      simpa [renameTT, renameT] using (HasType.t_tlam hNren'')
  | _, Δ', _, _, _, ρ, hρ, .t_tapp (Γ := Γ) (M := M) (A := A) (B := B) hM hB => by
      have hM' :
          HasType Δ' (List.map (renameT ρ) Γ) (renameTT ρ M) (renameT ρ (.all A)) :=
        typing_renameTT (ρ := ρ) hρ hM
      have hB' : WfTy Δ' (renameT ρ B) :=
        renameT_preserves_WfTy hB hρ
      have hTap :
          HasType Δ' (List.map (renameT ρ) Γ) (.tapp (renameTT ρ M))
            (substOneT (renameT (extT ρ) A) (renameT ρ B)) :=
        HasType.t_tapp hM' hB'
      have hTap' :
          HasType Δ' (List.map (renameT ρ) Γ) (.tapp (renameTT ρ M))
            (renameT ρ (substOneT A B)) := by
        exact Eq.ndrec (motive := fun T =>
            HasType Δ' (List.map (renameT ρ) Γ) (.tapp (renameTT ρ M)) T)
          hTap (rename_substOne_commute ρ A B).symm
      simpa [renameTT] using hTap'

def typing_substTT :
  ∀ {Δ Δ' Γ M A σ},
    TySubstWf Δ Δ' σ →
    HasType Δ Γ M A →
    HasType Δ' (List.map (substT σ) Γ) (substTT σ M) (substT σ A)
  | _, _, _, _, _, σ, _, .t_var h => by
      simpa [substTT] using HasType.t_var (lookup_map_substT (σ := σ) h)
  | _, _, _, _, _, σ, hσ, .t_lam hA hN => by
      refine HasType.t_lam (substT_preserves_WfTy hA hσ) ?_
      simpa [substTT, substT] using typing_substTT (σ := σ) hσ hN
  | _, _, _, _, _, σ, hσ, .t_app hL hM => by
      simpa [substTT, substT] using HasType.t_app (typing_substTT (σ := σ) hσ hL) (typing_substTT (σ := σ) hσ hM)
  | _, Δ', Γ, _, _, σ, _, .t_true => by
      simpa [substTT, substT] using (HasType.t_true : HasType Δ' (List.map (substT σ) Γ) .ttrue .bool)
  | _, Δ', Γ, _, _, σ, _, .t_false => by
      simpa [substTT, substT] using (HasType.t_false : HasType Δ' (List.map (substT σ) Γ) .tfalse .bool)
  | _, Δ', Γ, _, _, σ, _, .t_zero => by
      simpa [substTT, substT] using (HasType.t_zero : HasType Δ' (List.map (substT σ) Γ) .zero .nat)
  | _, _, _, _, _, σ, hσ, .t_suc hM => by
      simpa [substTT, substT] using HasType.t_suc (typing_substTT (σ := σ) hσ hM)
  | _, _, _, _, _, σ, hσ, .t_case hL hM hN => by
      simpa [substTT, substT] using
        HasType.t_case (typing_substTT (σ := σ) hσ hL) (typing_substTT (σ := σ) hσ hM) (typing_substTT (σ := σ) hσ hN)
  | _, _, _, _, _, σ, hσ, .t_if hL hM hN => by
      simpa [substTT, substT] using
        HasType.t_if (typing_substTT (σ := σ) hσ hL) (typing_substTT (σ := σ) hσ hM) (typing_substTT (σ := σ) hσ hN)
  | _, Δ', _, _, _, σ, hσ, .t_tlam (Γ := Γ) (N := N) (A := A) hN => by
      have hNsub :
          HasType (Δ' + 1) (List.map (substT (extsT σ)) (liftCtx Γ))
            (substTT (extsT σ) N) (substT (extsT σ) A) :=
        typing_substTT (Δ' := Δ' + 1) (σ := extsT σ) (tySubstWf_exts hσ) hN
      have hNsub' :
          HasType (Δ' + 1) (liftCtx (List.map (substT σ) Γ))
            (substTT (extsT σ) N) (substT (extsT σ) A) := by
        refine Eq.ndrec
          (motive := fun Ψ =>
            HasType (Δ' + 1) Ψ (substTT (extsT σ) N) (substT (extsT σ) A))
          hNsub (map_substT_lift σ Γ)
      have hNsub'' :
          HasType (Δ' + 1) (liftCtx (List.map (substT σ) Γ))
            N (substT (extsT σ) A) := by
        simpa [substTT] using hNsub'
      simpa [substTT, substT] using (HasType.t_tlam hNsub'')
  | _, Δ', _, _, _, σ, hσ, .t_tapp (Γ := Γ) (M := M) (A := A) (B := B) hM hB => by
      have hM' :
          HasType Δ' (List.map (substT σ) Γ) (substTT σ M) (substT σ (.all A)) :=
        typing_substTT (σ := σ) hσ hM
      have hB' : WfTy Δ' (substT σ B) :=
        substT_preserves_WfTy hB hσ
      have hTap :
          HasType Δ' (List.map (substT σ) Γ) (.tapp (substTT σ M))
            (substOneT (substT (extsT σ) A) (substT σ B)) :=
        HasType.t_tapp hM' hB'
      have hTap' :
          HasType Δ' (List.map (substT σ) Γ) (.tapp (substTT σ M))
            (substT σ (substOneT A B)) := by
        exact Eq.ndrec (motive := fun T =>
            HasType Δ' (List.map (substT σ) Γ) (.tapp (substTT σ M)) T)
          hTap (subst_substOne_commute σ A B).symm
      simpa [substTT] using hTap'

def singleTySubstWf {Δ B} :
    WfTy Δ B →
    TySubstWf (Δ + 1) Δ (singleTyEnv B) := by
  intro hB X hX
  cases X with
  | zero =>
      simpa [singleTyEnv] using hB
  | succ X =>
      exact .var (Nat.lt_of_succ_lt_succ hX)

def substT_renameT_cancel (C B : Ty) :
    substT (singleTyEnv B) (renameT Nat.succ C) = C := by
  calc
    substT (singleTyEnv B) (renameT Nat.succ C)
        = substT (fun i => singleTyEnv B (Nat.succ i)) C := by
            exact rename_subst_commute Nat.succ (singleTyEnv B) C
    _ = substT Ty.var C := by
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

def typing_single_substTT :
  ∀ {Δ Γ M A B},
    HasType (Δ + 1) (liftCtx Γ) M A →
    WfTy Δ B →
    HasType Δ Γ (substOneTT M B) (substOneT A B)
  | Δ, Γ, M, A, B, hM, hB => by
      have hsub :
          HasType Δ (List.map (substT (singleTyEnv B)) (liftCtx Γ))
            (substTT (singleTyEnv B) M) (substOneT A B) :=
        typing_substTT (σ := singleTyEnv B) (singleTySubstWf hB) hM
      have hcast :
          HasType Δ Γ (substTT (singleTyEnv B) M) (substOneT A B) := by
        refine Eq.ndrec
          (motive := fun Ψ => HasType Δ Ψ (substTT (singleTyEnv B) M) (substOneT A B))
          hsub (singleTySubst_lift_cancel Γ B)
      simpa [substOneTT, substTT] using hcast

def lookup_map_inv :
  ∀ {Γ x B f},
    HasTypeVar (List.map f Γ) x B →
    Σ A, { hA : HasTypeVar Γ x A // B = f A }
  | [], _, _, _, h => by
      cases h
  | A :: Γ, 0, _, _, .Z =>
      ⟨A, ⟨.Z, rfl⟩⟩
  | A :: Γ, x + 1, B, f, .S h => by
      rcases lookup_map_inv (Γ := Γ) (x := x) (B := B) (f := f) h with ⟨A', ⟨hA', hEq⟩⟩
      exact ⟨A', ⟨.S hA', hEq⟩⟩

def renameWf_ext {Γ Γ' B ρ} :
    RenameWf Γ Γ' ρ →
    RenameWf (B :: Γ) (B :: Γ') (ext ρ) := by
  intro hρ x A h
  cases h with
  | Z =>
      exact .Z
  | S h' =>
      exact .S (hρ h')

def renameWf_lift {Γ Γ' ρ} :
    RenameWf Γ Γ' ρ →
    RenameWf (liftCtx Γ) (liftCtx Γ') ρ := by
  intro hρ x A h
  rcases lookup_map_inv (Γ := Γ) (x := x) (B := A) (f := renameT Nat.succ) h with ⟨B, ⟨hB, hEq⟩⟩
  have hB' : HasTypeVar Γ' (ρ x) B :=
    hρ hB
  have hLift : HasTypeVar (liftCtx Γ') (ρ x) (renameT Nat.succ B) :=
    lookup_map_renameT (ρ := Nat.succ) hB'
  exact Eq.ndrec
    (motive := fun T => HasTypeVar (liftCtx Γ') (ρ x) T)
    hLift hEq.symm

def typing_rename :
  ∀ {Δ Γ Γ' M A ρ},
    RenameWf Γ Γ' ρ →
    HasType Δ Γ M A →
    HasType Δ Γ' (rename ρ M) A
  | _, _, _, _, _, _, hρ, .t_var h =>
      .t_var (hρ h)
  | _, _, _, _, _, _, hρ, .t_lam hA hN => by
      simpa [rename] using HasType.t_lam hA (typing_rename (renameWf_ext hρ) hN)
  | _, _, _, _, _, _, hρ, .t_app hL hM => by
      simpa [rename] using HasType.t_app (typing_rename hρ hL) (typing_rename hρ hM)
  | _, _, _, _, _, _, _, .t_true => by
      simpa [rename] using (HasType.t_true : HasType _ _ .ttrue .bool)
  | _, _, _, _, _, _, _, .t_false => by
      simpa [rename] using (HasType.t_false : HasType _ _ .tfalse .bool)
  | _, _, _, _, _, _, _, .t_zero => by
      simpa [rename] using (HasType.t_zero : HasType _ _ .zero .nat)
  | _, _, _, _, _, _, hρ, .t_suc hM => by
      simpa [rename] using HasType.t_suc (typing_rename hρ hM)
  | _, _, _, _, _, _, hρ, .t_case hL hM hN => by
      simpa [rename] using
        HasType.t_case (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename (renameWf_ext hρ) hN)
  | _, _, _, _, _, _, hρ, .t_if hL hM hN => by
      simpa [rename] using HasType.t_if (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hρ hN)
  | _, _, _, _, _, _, hρ, .t_tlam hN => by
      simpa [rename] using HasType.t_tlam (typing_rename (renameWf_lift hρ) hN)
  | _, _, _, _, _, _, hρ, .t_tapp hM hB => by
      simpa [rename] using HasType.t_tapp (typing_rename hρ hM) hB

def typing_rename_shift :
  ∀ {Δ Γ M A B},
    HasType Δ Γ M A →
    HasType Δ (B :: Γ) (rename Nat.succ M) A
  | Δ, Γ, M, A, B, hM =>
      typing_rename (Δ := Δ) (Γ := Γ) (Γ' := B :: Γ) (M := M) (A := A) (ρ := Nat.succ)
        (fun {_ _} h => HasTypeVar.S h) hM

def substWf_exts {Δ Γ Γ' B σ} :
    SubstWf Δ Γ Γ' σ →
    SubstWf Δ (B :: Γ) (B :: Γ') (exts σ) := by
  intro hσ x A h
  cases h with
  | Z =>
      simpa [exts] using (HasType.t_var (HasTypeVar.Z : HasTypeVar (B :: Γ') 0 B))
  | S h' =>
      simpa [exts] using typing_rename_shift (B := B) (hσ h')

def substWf_up {Δ Γ Γ' σ} :
    SubstWf Δ Γ Γ' σ →
    SubstWf (Δ + 1) (liftCtx Γ) (liftCtx Γ') (up σ) := by
  intro hσ x A h
  rcases lookup_map_inv (Γ := Γ) (x := x) (B := A) (f := renameT Nat.succ) h with ⟨B, ⟨hB, hEq⟩⟩
  have hRenWf : TyRenameWf Δ (Δ + 1) Nat.succ := by
    intro i hi
    exact Nat.succ_lt_succ hi
  have htyped :
      HasType (Δ + 1) (liftCtx Γ') (renameTT Nat.succ (σ x)) (renameT Nat.succ B) := by
    simpa [liftCtx] using typing_renameTT (ρ := Nat.succ) hRenWf (hσ hB)
  have htyped' : HasType (Δ + 1) (liftCtx Γ') (up σ x) (renameT Nat.succ B) := by
    simpa [up] using htyped
  exact Eq.ndrec
    (motive := fun T => HasType (Δ + 1) (liftCtx Γ') (up σ x) T)
    htyped' hEq.symm

def typing_subst :
  ∀ {Δ Γ Γ' M A σ},
    SubstWf Δ Γ Γ' σ →
    HasType Δ Γ M A →
    HasType Δ Γ' (subst σ M) A
  | _, _, _, _, _, _, hσ, .t_var h => by
      simpa [subst] using hσ h
  | _, _, _, _, _, _, hσ, .t_lam hA hN => by
      simpa [subst] using HasType.t_lam hA (typing_subst (substWf_exts hσ) hN)
  | _, _, _, _, _, _, hσ, .t_app hL hM => by
      simpa [subst] using HasType.t_app (typing_subst hσ hL) (typing_subst hσ hM)
  | _, _, _, _, _, _, _, .t_true => by
      simpa [subst] using (HasType.t_true : HasType _ _ .ttrue .bool)
  | _, _, _, _, _, _, _, .t_false => by
      simpa [subst] using (HasType.t_false : HasType _ _ .tfalse .bool)
  | _, _, _, _, _, _, _, .t_zero => by
      simpa [subst] using (HasType.t_zero : HasType _ _ .zero .nat)
  | _, _, _, _, _, _, hσ, .t_suc hM => by
      simpa [subst] using HasType.t_suc (typing_subst hσ hM)
  | _, _, _, _, _, _, hσ, .t_case hL hM hN => by
      simpa [subst] using
        HasType.t_case (typing_subst hσ hL) (typing_subst hσ hM) (typing_subst (substWf_exts hσ) hN)
  | _, _, _, _, _, _, hσ, .t_if hL hM hN => by
      simpa [subst] using HasType.t_if (typing_subst hσ hL) (typing_subst hσ hM) (typing_subst hσ hN)
  | _, _, _, _, _, _, hσ, .t_tlam hN => by
      simpa [subst] using HasType.t_tlam (typing_subst (substWf_up hσ) hN)
  | _, _, _, _, _, _, hσ, .t_tapp hM hB => by
      simpa [subst] using HasType.t_tapp (typing_subst hσ hM) hB

def singleSubstWf {Δ Γ A V} :
    HasType Δ Γ V A →
    SubstWf Δ (A :: Γ) Γ (singleEnv V) := by
  intro hV x B h
  cases h with
  | Z =>
      simpa [singleEnv] using hV
  | S h' =>
      simpa [singleEnv] using (HasType.t_var h')

def typing_single_subst :
  ∀ {Δ Γ N V A B},
    HasType Δ (A :: Γ) N B →
    HasType Δ Γ V A →
    HasType Δ Γ (singleSubst N V) B
  | _, _, _, _, _, _, hN, hV => by
      simpa [singleSubst] using typing_subst (singleSubstWf hV) hN

def preservation :
  ∀ {Δ Γ M N A},
    HasType Δ Γ M A →
    M —→ N →
    HasType Δ Γ N A
  | _, _, _, _, _, .t_app (.t_lam hA hN) hW, .beta_lam _ =>
      typing_single_subst hN hW
  | _, _, _, _, _, .t_app hL hM, .xi_app₁ s =>
      .t_app (preservation hL s) hM
  | _, _, _, _, _, .t_app hL hM, .xi_app₂ _ s =>
      .t_app hL (preservation hM s)
  | _, _, _, _, _, .t_if hL hM hN, .xi_if s =>
      .t_if (preservation hL s) hM hN
  | _, _, _, _, _, .t_if hL hM hN, .beta_true =>
      hM
  | _, _, _, _, _, .t_if hL hM hN, .beta_false =>
      hN
  | _, _, _, _, _, .t_suc hM, .xi_suc s =>
      .t_suc (preservation hM s)
  | _, _, _, _, _, .t_case hL hM hN, .xi_case s =>
      .t_case (preservation hL s) hM hN
  | _, _, _, _, _, .t_case hL hM hN, .beta_zero =>
      hM
  | _, _, _, _, _, .t_case (.t_suc hV) hM hN, .beta_suc _ =>
      typing_single_subst hN hV
  | _, _, _, _, _, .t_tapp (.t_tlam hN) hB, .beta_tlam =>
      typing_single_substTT hN hB
  | _, _, _, _, _, .t_tapp hM hB, .xi_tapp s =>
      .t_tapp (preservation hM s) hB

def multi_preservation :
  ∀ {Δ Γ M N A},
    HasType Δ Γ M A →
    M —↠ N →
    HasType Δ Γ N A
  | _, _, _, _, _, hM, .refl _ =>
      hM
  | _, _, _, _, _, hM, .step _ s ms =>
      multi_preservation (preservation hM s) ms

end

end Extrinsic

import extrinsic.Reduction

namespace Extrinsic

abbrev Rel (A B : Ty) : Type :=
  (V W : Term) → Value V → Value W → Prop

structure RelSub where
  rho1 : SubstT
  rho2 : SubstT
  rhoR : ∀ α, Rel (rho1 α) (rho2 α)

def emptyRelSub : RelSub where
  rho1 := idT
  rho2 := idT
  rhoR := fun _ _ _ _ _ => False

def extendRelSub (ρ : RelSub) (A₁ A₂ : Ty) (R : Rel A₁ A₂) : RelSub where
  rho1 := A₁ •ᵗ ρ.rho1
  rho2 := A₂ •ᵗ ρ.rho2
  rhoR := fun
    | 0 => R
    | i + 1 => ρ.rhoR i

def VNatRel : {V W : Term} → Value V → Value W → Prop
  | _, _, .vZero, .vZero => True
  | _, _, .vZero, _ => False
  | _, _, .vSuc v, .vSuc w => VNatRel v w
  | _, _, .vSuc _, _ => False
  | _, _, _, _ => False

def VBoolRel : {V W : Term} → Value V → Value W → Prop
  | _, _, .vTrue, .vTrue => True
  | _, _, .vFalse, .vFalse => True
  | _, _, _, _ => False

def VRel :
  (A : Ty) → (ρ : RelSub) → (V W : Term) → Value V → Value W → Prop
  | .var α, ρ, V, W, v, w => ρ.rhoR α V W v w
  | .nat, _, _, _, v, w => VNatRel v w
  | .bool, _, _, _, v, w => VBoolRel v w
  | .fn A B, ρ, _, _, v, w =>
      match v, w with
      | .vLam (N := N), .vLam (N := M) =>
          ∀ {V' W'} (v' : Value V') (w' : Value W'),
            VRel A ρ V' W' v' w' →
            ∃ (VB WB : Term), ∃ (vb : Value VB), ∃ (wb : Value WB),
              Nonempty (singleSubst N V' —↠ VB) ∧
              Nonempty (singleSubst M W' —↠ WB) ∧
              VRel B ρ VB WB vb wb
      | _, _ => False
  | .all A, ρ, _, _, v, w =>
      match v, w with
      | .vTlam (N := N), .vTlam (N := M) =>
          ∀ (A₁ A₂ : Ty) (R : Rel A₁ A₂),
            ∃ (VA WA : Term), ∃ (va : Value VA), ∃ (wa : Value WA),
              Nonempty (N —↠ VA) ∧
              Nonempty (M —↠ WA) ∧
              VRel A (extendRelSub ρ A₁ A₂ R) VA WA va wa
      | _, _ => False

def ERel :
  (A : Ty) → (ρ : RelSub) → Term → Term → Prop
  | A, ρ, M, N =>
      ∃ (V W : Term), ∃ (v : Value V), ∃ (w : Value W),
        Nonempty (M —↠ V) ∧ Nonempty (N —↠ W) ∧ VRel A ρ V W v w

structure RelEnv where
  gamma1 : Subst
  gamma2 : Subst

def emptyRelEnv : RelEnv where
  gamma1 := id
  gamma2 := id

def extendRelEnv (γ : RelEnv) (V W : Term) : RelEnv where
  gamma1 := V • γ.gamma1
  gamma2 := W • γ.gamma2

def tailRelEnv (γ : RelEnv) : RelEnv where
  gamma1 := fun i => γ.gamma1 (i + 1)
  gamma2 := fun i => γ.gamma2 (i + 1)

def GRel : Ctx → RelSub → RelEnv → Prop
  | [], _, _ => True
  | A :: Γ, ρ, γ =>
      ERel A ρ (γ.gamma1 0) (γ.gamma2 0) ∧ GRel Γ ρ (tailRelEnv γ)

def LogicalRel (Γ : Ctx) (A : Ty) (M N : Term) : Prop :=
  ∀ (ρ : RelSub) (γ : RelEnv), GRel Γ ρ γ → ERel A ρ (subst γ.gamma1 M) (subst γ.gamma2 N)

theorem VRel_to_ERel :
  ∀ {A ρ V W} (v : Value V) (w : Value W),
    VRel A ρ V W v w → ERel A ρ V W
  | _, _, V, W, v, w, h =>
      ⟨V, W, v, w, ⟨.refl V⟩, ⟨.refl W⟩, h⟩

def GRel_empty : GRel [] emptyRelSub emptyRelEnv := trivial

theorem tailRelEnv_extendRelEnv (γ : RelEnv) (V W : Term) :
    tailRelEnv (extendRelEnv γ V W) = γ := by
  cases γ
  rfl

theorem extendRelEnv_related :
  ∀ {Γ A ρ γ V W},
    GRel Γ ρ γ →
    (v : Value V) →
    (w : Value W) →
    VRel A ρ V W v w →
    GRel (A :: Γ) ρ (extendRelEnv γ V W)
  | Γ, A, ρ, γ, V, W, env, v, w, VWrel => by
      exact And.intro
        (VRel_to_ERel (A := A) (ρ := ρ) (V := V) (W := W) v w VWrel)
        (Eq.ndrec env (tailRelEnv_extendRelEnv γ V W))

inductive WkRel : RenameT → RelSub → RelSub → Prop where
  | wk_suc {ρ A₁ A₂} (R : Rel A₁ A₂) :
      WkRel Nat.succ ρ (extendRelSub ρ A₁ A₂ R)
  | wk_ext {ξ ρ ρ' B₁ B₂} (S : Rel B₁ B₂) :
      WkRel ξ ρ ρ' →
      WkRel (extT ξ) (extendRelSub ρ B₁ B₂ S) (extendRelSub ρ' B₁ B₂ S)

theorem wk_rhoR_cast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W},
      ρ.rhoR α V W v w → ρ'.rhoR (ξ α) V W v w
  | _, _, _, .wk_suc _, _, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, 0, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, α + 1, _, _, _, _, rel => by
      simpa [extendRelSub, extT] using wk_rhoR_cast (ξ := _) (ρ := _) (ρ' := _) wk α rel

theorem wk_rhoR_uncast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W},
      ρ'.rhoR (ξ α) V W v w → ρ.rhoR α V W v w
  | _, _, _, .wk_suc _, _, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, 0, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, α + 1, _, _, _, _, rel => by
      simpa [extendRelSub, extT] using wk_rhoR_uncast (ξ := _) (ρ := _) (ρ' := _) wk α rel

mutual

theorem VRel_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    VRel A ρ V W v w →
    VRel (renameT ξ A) ρ' V W v w
  | .var α, ξ, ρ, ρ', V, W, v, w, wk, h =>
      wk_rhoR_cast (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk α (show ρ.rhoR α V W v w from h)
  | .nat, _, _, _, _, _, _, _, _, h => h
  | .bool, _, _, _, _, _, _, _, _, h => h
  | .fn A B, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [VRel, renameT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg0 :
            VRel A ρ V' W' v' w' :=
          VRel_unrename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hArg
        rcases h v' w' hArg0 with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          VRel_rename_wk (A := B) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hVB⟩
  | .all A, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [VRel, renameT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have wk' :
            WkRel (extT ξ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          WkRel.wk_ext (S := R) wk
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          VRel_rename_wk (A := A) (ξ := extT ξ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) wk' hVA⟩

theorem VRel_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    VRel (renameT ξ A) ρ' V W v w →
    VRel A ρ V W v w
  | .var α, ξ, ρ, ρ', V, W, v, w, wk, h =>
      wk_rhoR_uncast (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk α (show ρ'.rhoR (ξ α) V W v w from h)
  | .nat, _, _, _, _, _, _, _, _, h => h
  | .bool, _, _, _, _, _, _, _, _, h => h
  | .fn A B, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [VRel, renameT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg' :
            VRel (renameT ξ A) ρ' V' W' v' w' :=
          VRel_rename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hArg
        rcases h v' w' hArg' with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          VRel_unrename_wk (A := B) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hVB⟩
  | .all A, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [VRel, renameT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have wk' :
            WkRel (extT ξ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          WkRel.wk_ext (S := R) wk
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          VRel_unrename_wk (A := A) (ξ := extT ξ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) wk' hVA⟩

end

theorem ERel_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    ERel A ρ M N →
    ERel (renameT ξ A) ρ' M N
  | _, _, _, _, _, _, wk, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, VRel_rename_wk (ξ := _) (ρ := _) (ρ' := _) wk rel⟩

theorem ERel_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    ERel (renameT ξ A) ρ' M N →
    ERel A ρ M N
  | _, _, _, _, _, _, wk, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, VRel_unrename_wk (ξ := _) (ρ := _) (ρ' := _) wk rel⟩

theorem liftERel :
  ∀ {A A₁ A₂ : Ty} {ρ : RelSub} {γ : RelEnv},
    (R : Rel A₁ A₂) →
    ERel A ρ (γ.gamma1 0) (γ.gamma2 0) →
    ERel (renameT Nat.succ A) (extendRelSub ρ A₁ A₂ R) (γ.gamma1 0) (γ.gamma2 0)
  | A, A₁, A₂, ρ, γ, R, rel =>
      ERel_rename_wk (A := A) (ξ := Nat.succ) (ρ := ρ) (ρ' := extendRelSub ρ A₁ A₂ R)
        (M := γ.gamma1 0) (N := γ.gamma2 0) (WkRel.wk_suc R) rel

theorem liftRelEnv_related :
  ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv},
    (R : Rel A₁ A₂) →
    GRel Γ ρ γ →
    GRel (liftCtx Γ) (extendRelSub ρ A₁ A₂ R) γ
  | [], _, _, _, _, _, _ => trivial
  | A :: Γ, A₁, A₂, ρ, γ, R, h => by
      exact And.intro
        (liftERel (A := A) (A₁ := A₁) (A₂ := A₂) (ρ := ρ) (γ := γ) R h.1)
        (liftRelEnv_related (Γ := Γ) (A₁ := A₁) (A₂ := A₂)
          (ρ := ρ) (γ := tailRelEnv γ) R h.2)

structure SubstRel (σ : SubstT) (ρ ρ' : RelSub) : Prop where
  varTo :
    ∀ α {V W} {v : Value V} {w : Value W},
      VRel (.var α) ρ' V W v w → VRel (σ α) ρ V W v w
  varFrom :
    ∀ α {V W} {v : Value V} {w : Value W},
      VRel (σ α) ρ V W v w → VRel (.var α) ρ' V W v w

theorem exts_SubstRel :
  ∀ {σ : SubstT} {ρ ρ' : RelSub} {A₁ A₂ : Ty},
    (R : Rel A₁ A₂) →
    SubstRel σ ρ ρ' →
    SubstRel (extsT σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)
  := fun {σ} {ρ} {ρ'} {A₁} {A₂} R sr =>
    { varTo := by
        intro α V W v w rel
        cases α with
        | zero =>
            simpa [VRel, extendRelSub, extsT] using rel
        | succ α =>
            have rel' : VRel (.var α) ρ' V W v w := by
              simpa [VRel, extendRelSub] using rel
            have hσ : VRel (σ α) ρ V W v w :=
              sr.varTo α rel'
            have hShift :
                VRel (renameT Nat.succ (σ α)) (extendRelSub ρ A₁ A₂ R) V W v w :=
              VRel_rename_wk (ξ := Nat.succ) (ρ := ρ) (ρ' := extendRelSub ρ A₁ A₂ R)
                (WkRel.wk_suc R) hσ
            simpa [extsT] using hShift
      varFrom := by
        intro α V W v w rel
        cases α with
        | zero =>
            simpa [VRel, extendRelSub, extsT] using rel
        | succ α =>
            have hShift :
                VRel (renameT Nat.succ (σ α)) (extendRelSub ρ A₁ A₂ R) V W v w := by
              simpa [extsT] using rel
            have hσ : VRel (σ α) ρ V W v w :=
              VRel_unrename_wk (ξ := Nat.succ) (ρ := ρ) (ρ' := extendRelSub ρ A₁ A₂ R)
                (WkRel.wk_suc R) hShift
            have rel' : VRel (.var α) ρ' V W v w :=
              sr.varFrom α hσ
            simpa [VRel, extendRelSub] using rel' }

mutual

theorem VRel_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    VRel A ρ' V W v w →
    VRel (substT σ A) ρ V W v w
  | .var α, σ, ρ, ρ', V, W, v, w, sr, h =>
      sr.varTo α h
  | .nat, _, _, _, _, _, _, _, _, h => h
  | .bool, _, _, _, _, _, _, _, _, h => h
  | .fn A B, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [VRel, substT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg0 :
            VRel A ρ' V' W' v' w' :=
          VRel_unsubst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hArg
        rcases h v' w' hArg0 with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          VRel_subst (A := B) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hVB⟩
  | .all A, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [VRel, substT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have sr' :
            SubstRel (extsT σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          exts_SubstRel (σ := σ) (ρ := ρ) (ρ' := ρ') (A₁ := A₁) (A₂ := A₂) R sr
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          VRel_subst (A := A) (σ := extsT σ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) sr' hVA⟩

theorem VRel_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    VRel (substT σ A) ρ V W v w →
    VRel A ρ' V W v w
  | .var α, σ, ρ, ρ', V, W, v, w, sr, h =>
      sr.varFrom α h
  | .nat, _, _, _, _, _, _, _, _, h => h
  | .bool, _, _, _, _, _, _, _, _, h => h
  | .fn A B, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [VRel, substT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg0 :
            VRel (substT σ A) ρ V' W' v' w' :=
          VRel_subst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hArg
        rcases h v' w' hArg0 with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          VRel_unsubst (A := B) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hVB⟩
  | .all A, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [VRel, substT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have sr' :
            SubstRel (extsT σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          exts_SubstRel (σ := σ) (ρ := ρ) (ρ' := ρ') (A₁ := A₁) (A₂ := A₂) R sr
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          VRel_unsubst (A := A) (σ := extsT σ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) sr' hVA⟩

end

theorem ERel_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    ERel A ρ' M N →
    ERel (substT σ A) ρ M N
  | _, _, _, _, _, _, sr, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, VRel_subst (A := _) (σ := _) (ρ := _) (ρ' := _) sr rel⟩

theorem ERel_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    ERel (substT σ A) ρ M N →
    ERel A ρ' M N
  | _, _, _, _, _, _, sr, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, VRel_unsubst (A := _) (σ := _) (ρ := _) (ρ' := _) sr rel⟩

end Extrinsic

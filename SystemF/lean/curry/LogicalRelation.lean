import curry.Reduction

-- File Charter:
--   * Defines the logical relation for curry System F.
--   * Includes relation environments and logical-relatedness judgments.
--   * Proves helper lemmas for renaming/substitution and environment lifting.

namespace Curry

abbrev Rel (A B : Ty) : Type :=
  (V W : Term) → Value V → Value W → Prop

structure RelSub where
  left : SubstT
  right : SubstT
  R : ∀ α, Rel (left α) (right α)

def emptyRelSub : RelSub where
  left := idT
  right := idT
  R := fun _ _ _ _ _ => False

def extendRelSub (ρ : RelSub) (A₁ A₂ : Ty) (R : Rel A₁ A₂) : RelSub where
  left := A₁ •ᵗ ρ.left
  right := A₂ •ᵗ ρ.right
  R := fun
    | 0 => R
    | i + 1 => ρ.R i

def 𝒱nat : {V W : Term} → Value V → Value W → Prop
  | _, _, .vZero, .vZero => True
  | _, _, .vZero, _ => False
  | _, _, .vSuc v, .vSuc w => 𝒱nat v w
  | _, _, .vSuc _, _ => False
  | _, _, _, _ => False

def 𝒱bool : {V W : Term} → Value V → Value W → Prop
  | _, _, .vTrue, .vTrue => True
  | _, _, .vFalse, .vFalse => True
  | _, _, _, _ => False

def 𝒱 :
  (A : Ty) → (ρ : RelSub) → (V W : Term) → Value V → Value W → Prop
  | #α, ρ, V, W, v, w => ρ.R α V W v w
  | ℕ, _, _, _, v, w => 𝒱nat v w
  | 𝔹, _, _, _, v, w => 𝒱bool v w
  | A ⇒ B, ρ, _, _, v, w =>
      match v, w with
      | .vLam (N := N), .vLam (N := M) =>
          ∀ {V' W'} (v' : Value V') (w' : Value W'),
            𝒱 A ρ V' W' v' w' →
            ∃ (VB WB : Term), ∃ (vb : Value VB), ∃ (wb : Value WB),
              Nonempty (singleSubst N V' —↠ VB) ∧
              Nonempty (singleSubst M W' —↠ WB) ∧
              𝒱 B ρ VB WB vb wb
      | _, _ => False
  | ∀ₜ A, ρ, _, _, v, w =>
      match v, w with
      | .vTlam (N := N), .vTlam (N := M) =>
          ∀ (A₁ A₂ : Ty) (R : Rel A₁ A₂),
            ∃ (VA WA : Term), ∃ (va : Value VA), ∃ (wa : Value WA),
              Nonempty (N —↠ VA) ∧
              Nonempty (M —↠ WA) ∧
              𝒱 A (extendRelSub ρ A₁ A₂ R) VA WA va wa
      | _, _ => False

def 𝓔 :
  (A : Ty) → (ρ : RelSub) → Term → Term → Prop
  | A, ρ, M, N =>
      ∃ (V W : Term), ∃ (v : Value V), ∃ (w : Value W),
        Nonempty (M —↠ V) ∧ Nonempty (N —↠ W) ∧ 𝒱 A ρ V W v w

structure RelEnv where
  left : Subst
  right : Subst

def emptyRelEnv : RelEnv where
  left := id
  right := id

def extendRelEnv (γ : RelEnv) (V W : Term) : RelEnv where
  left := V • γ.left
  right := W • γ.right

def tailRelEnv (γ : RelEnv) : RelEnv where
  left := fun i => γ.left (i + 1)
  right := fun i => γ.right (i + 1)


def 𝒢 : Ctx → RelSub → RelEnv → Prop
  | [], _, _ => True
  | A :: Γ, ρ, γ =>
      𝓔 A ρ (γ.left 0) (γ.right 0) ∧ 𝒢 Γ ρ (tailRelEnv γ)

def LogicalRel (Γ : Ctx) (A : Ty) (M N : Term) : Prop :=
  ∀ (ρ : RelSub) (γ : RelEnv), 𝒢 Γ ρ γ → 𝓔 A ρ (subst γ.left M) (subst γ.right N)

syntax:55 term:56 " ⊨ " term:56 " ≈ " term:56 " ⦂ " term:56 : term
macro_rules
  | `($Γ ⊨ $M ≈ $N ⦂ $A) => `(LogicalRel $Γ $A $M $N)

theorem 𝒱_to_𝓔 :
  ∀ {A ρ V W} (v : Value V) (w : Value W),
    𝒱 A ρ V W v w → 𝓔 A ρ V W
  | _, _, V, W, v, w, h =>
      ⟨V, W, v, w, ⟨.refl V⟩, ⟨.refl W⟩, h⟩

def 𝒢_empty : 𝒢 [] emptyRelSub emptyRelEnv := trivial

theorem tailRelEnv_extendRelEnv (γ : RelEnv) (V W : Term) :
    tailRelEnv (extendRelEnv γ V W) = γ := by
  cases γ
  rfl

theorem extendRelEnv_related :
  ∀ {Γ A ρ γ V W},
    𝒢 Γ ρ γ →
    (v : Value V) →
    (w : Value W) →
    𝒱 A ρ V W v w →
    𝒢 (A :: Γ) ρ (extendRelEnv γ V W)
  | Γ, A, ρ, γ, V, W, env, v, w, VWrel => by
      exact And.intro
        (𝒱_to_𝓔 (A := A) (ρ := ρ) (V := V) (W := W) v w VWrel)
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
      ρ.R α V W v w → ρ'.R (ξ α) V W v w
  | _, _, _, .wk_suc _, _, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, 0, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, α + 1, _, _, _, _, rel => by
      simpa [extendRelSub, extT] using wk_rhoR_cast (ξ := _) (ρ := _) (ρ' := _) wk α rel

theorem wk_rhoR_uncast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W},
      ρ'.R (ξ α) V W v w → ρ.R α V W v w
  | _, _, _, .wk_suc _, _, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, 0, _, _, _, _, rel => rel
  | _, _, _, .wk_ext _ wk, α + 1, _, _, _, _, rel => by
      simpa [extendRelSub, extT] using wk_rhoR_uncast (ξ := _) (ρ := _) (ρ' := _) wk α rel

mutual

theorem 𝒱_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    𝒱 A ρ V W v w →
    𝒱 (renameT ξ A) ρ' V W v w
  | #α, ξ, ρ, ρ', V, W, v, w, wk, h =>
      wk_rhoR_cast (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk α (show ρ.R α V W v w from h)
  | ℕ, _, _, _, _, _, _, _, _, h => h
  | 𝔹, _, _, _, _, _, _, _, _, h => h
  | A ⇒ B, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg0 :
            𝒱 A ρ V' W' v' w' :=
          𝒱_unrename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hArg
        rcases h v' w' hArg0 with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          𝒱_rename_wk (A := B) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hVB⟩
  | ∀ₜ A, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have wk' :
            WkRel (extT ξ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          WkRel.wk_ext (S := R) wk
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          𝒱_rename_wk (A := A) (ξ := extT ξ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) wk' hVA⟩

theorem 𝒱_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    𝒱 (renameT ξ A) ρ' V W v w →
    𝒱 A ρ V W v w
  | #α, ξ, ρ, ρ', V, W, v, w, wk, h =>
      wk_rhoR_uncast (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk α (show ρ'.R (ξ α) V W v w from h)
  | ℕ, _, _, _, _, _, _, _, _, h => h
  | 𝔹, _, _, _, _, _, _, _, _, h => h
  | A ⇒ B, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg' :
            𝒱 (renameT ξ A) ρ' V' W' v' w' :=
          𝒱_rename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hArg
        rcases h v' w' hArg' with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          𝒱_unrename_wk (A := B) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hVB⟩
  | ∀ₜ A, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have wk' :
            WkRel (extT ξ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          WkRel.wk_ext (S := R) wk
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          𝒱_unrename_wk (A := A) (ξ := extT ξ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) wk' hVA⟩

end

theorem 𝓔_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    𝓔 A ρ M N →
    𝓔 (renameT ξ A) ρ' M N
  | _, _, _, _, _, _, wk, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, 𝒱_rename_wk (ξ := _) (ρ := _) (ρ' := _) wk rel⟩

theorem 𝓔_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    𝓔 (renameT ξ A) ρ' M N →
    𝓔 A ρ M N
  | _, _, _, _, _, _, wk, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, 𝒱_unrename_wk (ξ := _) (ρ := _) (ρ' := _) wk rel⟩

theorem lift𝓔 :
  ∀ {A A₁ A₂ : Ty} {ρ : RelSub} {γ : RelEnv},
    (R : Rel A₁ A₂) →
    𝓔 A ρ (γ.left 0) (γ.right 0) →
    𝓔 (renameT Nat.succ A) (extendRelSub ρ A₁ A₂ R) (γ.left 0) (γ.right 0)
  | A, A₁, A₂, ρ, γ, R, rel =>
      𝓔_rename_wk (A := A) (ξ := Nat.succ) (ρ := ρ) (ρ' := extendRelSub ρ A₁ A₂ R)
        (M := γ.left 0) (N := γ.right 0) (WkRel.wk_suc R) rel

theorem liftRelEnv_related :
  ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv},
    (R : Rel A₁ A₂) →
    𝒢 Γ ρ γ →
    𝒢 (liftCtx Γ) (extendRelSub ρ A₁ A₂ R) γ
  | [], _, _, _, _, _, _ => trivial
  | A :: Γ, A₁, A₂, ρ, γ, R, h => by
      exact And.intro
        (lift𝓔 (A := A) (A₁ := A₁) (A₂ := A₂) (ρ := ρ) (γ := γ) R h.1)
        (liftRelEnv_related (Γ := Γ) (A₁ := A₁) (A₂ := A₂)
          (ρ := ρ) (γ := tailRelEnv γ) R h.2)

structure SubstRel (σ : SubstT) (ρ ρ' : RelSub) : Prop where
  varTo :
    ∀ α {V W} {v : Value V} {w : Value W},
      𝒱 (#α) ρ' V W v w → 𝒱 (σ α) ρ V W v w
  varFrom :
    ∀ α {V W} {v : Value V} {w : Value W},
      𝒱 (σ α) ρ V W v w → 𝒱 (#α) ρ' V W v w

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
            simpa [𝒱, extendRelSub, extsT] using rel
        | succ α =>
            have rel' : 𝒱 (#α) ρ' V W v w := by
              simpa [𝒱, extendRelSub] using rel
            have hσ : 𝒱 (σ α) ρ V W v w :=
              sr.varTo α rel'
            have hShift :
                𝒱 (renameT Nat.succ (σ α)) (extendRelSub ρ A₁ A₂ R) V W v w :=
              𝒱_rename_wk (ξ := Nat.succ) (ρ := ρ) (ρ' := extendRelSub ρ A₁ A₂ R)
                (WkRel.wk_suc R) hσ
            simpa [extsT] using hShift
      varFrom := by
        intro α V W v w rel
        cases α with
        | zero =>
            simpa [𝒱, extendRelSub, extsT] using rel
        | succ α =>
            have hShift :
                𝒱 (renameT Nat.succ (σ α)) (extendRelSub ρ A₁ A₂ R) V W v w := by
              simpa [extsT] using rel
            have hσ : 𝒱 (σ α) ρ V W v w :=
              𝒱_unrename_wk (ξ := Nat.succ) (ρ := ρ) (ρ' := extendRelSub ρ A₁ A₂ R)
                (WkRel.wk_suc R) hShift
            have rel' : 𝒱 (#α) ρ' V W v w :=
              sr.varFrom α hσ
            simpa [𝒱, extendRelSub] using rel' }

mutual

theorem 𝒱_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    𝒱 A ρ' V W v w →
    𝒱 (substT σ A) ρ V W v w
  | #α, σ, ρ, ρ', V, W, v, w, sr, h =>
      sr.varTo α h
  | ℕ, _, _, _, _, _, _, _, _, h => h
  | 𝔹, _, _, _, _, _, _, _, _, h => h
  | A ⇒ B, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg0 :
            𝒱 A ρ' V' W' v' w' :=
          𝒱_unsubst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hArg
        rcases h v' w' hArg0 with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          𝒱_subst (A := B) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hVB⟩
  | ∀ₜ A, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have sr' :
            SubstRel (extsT σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          exts_SubstRel (σ := σ) (ρ := ρ) (ρ' := ρ') (A₁ := A₁) (A₂ := A₂) R sr
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          𝒱_subst (A := A) (σ := extsT σ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) sr' hVA⟩

theorem 𝒱_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    𝒱 (substT σ A) ρ V W v w →
    𝒱 A ρ' V W v w
  | #α, σ, ρ, ρ', V, W, v, w, sr, h =>
      sr.varFrom α h
  | ℕ, _, _, _, _, _, _, _, _, h => h
  | 𝔹, _, _, _, _, _, _, _, _, h => h
  | A ⇒ B, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vLam.vLam =>
        intro V' W' v' w' hArg
        have hArg0 :
            𝒱 (substT σ A) ρ V' W' v' w' :=
          𝒱_subst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hArg
        rcases h v' w' hArg0 with ⟨VB, WB, vb, wb, mSteps, nSteps, hVB⟩
        exact ⟨VB, WB, vb, wb, mSteps, nSteps,
          𝒱_unsubst (A := B) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hVB⟩
  | ∀ₜ A, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vTlam.vTlam =>
        intro A₁ A₂ R
        have sr' :
            SubstRel (extsT σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R) :=
          exts_SubstRel (σ := σ) (ρ := ρ) (ρ' := ρ') (A₁ := A₁) (A₂ := A₂) R sr
        rcases h A₁ A₂ R with ⟨VA, WA, va, wa, mSteps, nSteps, hVA⟩
        exact ⟨VA, WA, va, wa, mSteps, nSteps,
          𝒱_unsubst (A := A) (σ := extsT σ)
            (ρ := extendRelSub ρ A₁ A₂ R) (ρ' := extendRelSub ρ' A₁ A₂ R) sr' hVA⟩

end

theorem 𝓔_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    𝓔 A ρ' M N →
    𝓔 (substT σ A) ρ M N
  | _, _, _, _, _, _, sr, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, 𝒱_subst (A := _) (σ := _) (ρ := _) (ρ' := _) sr rel⟩

theorem 𝓔_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    𝓔 (substT σ A) ρ M N →
    𝓔 A ρ' M N
  | _, _, _, _, _, _, sr, h => by
      rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨V, W, v, w, mSteps, nSteps, 𝒱_unsubst (A := _) (σ := _) (ρ := _) (ρ' := _) sr rel⟩

end Curry

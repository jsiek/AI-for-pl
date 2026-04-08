import extrinsic.Preservation

namespace Extrinsic

abbrev Rel (A B : Ty) : Type :=
  (V W : Term) → Value V → Value W →
  (0 ⊢ [] ⊢ V ⦂ A) → (0 ⊢ [] ⊢ W ⦂ B) → Prop

structure RelSub where
  left : SubstT
  right : SubstT
  leftClosed : ∀ α, WfTy 0 (left α)
  rightClosed : ∀ α, WfTy 0 (right α)
  R : ∀ α, Rel (left α) (right α)

def emptyRelSub : RelSub where
  left := fun _ => ℕ
  right := fun _ => ℕ
  leftClosed := fun _ => .nat
  rightClosed := fun _ => .nat
  R := fun _ _ _ _ _ _ _ => False

def extendRelSub (ρ : RelSub) (A₁ A₂ : Ty)
    (hA₁ : WfTy 0 A₁) (hA₂ : WfTy 0 A₂) (R : Rel A₁ A₂) : RelSub where
  left := A₁ •ᵗ ρ.left
  right := A₂ •ᵗ ρ.right
  leftClosed := fun
    | 0 => hA₁
    | i + 1 => ρ.leftClosed i
  rightClosed := fun
    | 0 => hA₂
    | i + 1 => ρ.rightClosed i
  R := fun
    | 0 => R
    | i + 1 => ρ.R i

def substT_codom_closed :
    ∀ {Δ : TyCtx} (σ : SubstT),
      (∀ α, WfTy Δ (σ α)) →
      (A : Ty) →
      WfTy Δ (substT σ A)
  | _, σ, hσ, #α => hσ α
  | _, _, _, ℕ => .nat
  | _, _, _, 𝔹 => .bool
  | _, σ, hσ, A ⇒ B =>
      .fn (substT_codom_closed σ hσ A) (substT_codom_closed σ hσ B)
  | _, σ, hσ, ∀ₜ A =>
      .all (substT_codom_closed (extsT σ)
        (fun
          | 0 => .var (Nat.zero_lt_succ _)
          | α + 1 =>
              renameT_preserves_WfTy (hσ α)
                (by
                  intro i hi
                  exact Nat.succ_lt_succ hi))
        A)

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

mutual

def 𝒱 :
  (A : Ty) → (ρ : RelSub) → (V W : Term) → Value V → Value W → Prop
  | #α, ρ, V, W, v, w =>
      ∃ (hV : 0 ⊢ [] ⊢ V ⦂ ρ.left α),
        ∃ (hW : 0 ⊢ [] ⊢ W ⦂ ρ.right α),
          (ρ.R α) V W v w hV hW
  | ℕ, _, _, _, v, w => 𝒱nat v w
  | 𝔹, _, _, _, v, w => 𝒱bool v w
  | A ⇒ B, ρ, _, _, v, w =>
      match v, w with
      | .vLam (A := C) (N := N), .vLam (A := D) (N := M) =>
          ∃ (hV : 0 ⊢ [] ⊢ (ƛ[ C ] N) ⦂ substT ρ.left (A ⇒ B)),
            ∃ (hW : 0 ⊢ [] ⊢ (ƛ[ D ] M) ⦂ substT ρ.right (A ⇒ B)),
              ∀ {V' W'} (v' : Value V') (w' : Value W'),
                𝒱 A ρ V' W' v' w' →
                𝓔 B ρ (singleSubst N V') (singleSubst M W')
      | _, _ => False
  | ∀ₜ A, ρ, _, _, v, w =>
      match v, w with
      | .vTlam (N := N), .vTlam (N := M) =>
          ∃ (hV : 0 ⊢ [] ⊢ (Λ N) ⦂ substT ρ.left (∀ₜ A)),
            ∃ (hW : 0 ⊢ [] ⊢ (Λ M) ⦂ substT ρ.right (∀ₜ A)),
              ∀ (A₁ A₂ : Ty) (hA₁ : WfTy 0 A₁) (hA₂ : WfTy 0 A₂) (R : Rel A₁ A₂),
                𝓔 A (extendRelSub ρ A₁ A₂ hA₁ hA₂ R) (substOneTT N A₁) (substOneTT M A₂)
      | _, _ => False

def 𝓔 :
  (A : Ty) → (ρ : RelSub) → Term → Term → Prop
  | A, ρ, M, N =>
      ∃ (hM : 0 ⊢ [] ⊢ M ⦂ substT ρ.left A),
        ∃ (hN : 0 ⊢ [] ⊢ N ⦂ substT ρ.right A),
          ∃ (V W : Term), ∃ (v : Value V), ∃ (w : Value W),
            Nonempty (M —↠ V) ∧ Nonempty (N —↠ W) ∧ 𝒱 A ρ V W v w

end

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
      (𝓔 A ρ (γ.left 0) (γ.right 0)) ∧ (𝒢 Γ ρ (tailRelEnv γ))

def LogicalRel (Γ : Ctx) (A : Ty) (M N : Term) : Prop :=
  ∀ (ρ : RelSub) (γ : RelEnv), 𝒢 Γ ρ γ →
    𝓔 A ρ
      (substTT ρ.left (subst γ.left M))
      (substTT ρ.right (subst γ.right N))

syntax:55 term:56 " ⊨ " term:56 " ≈ " term:56 " ⦂ " term:56 : term
macro_rules
  | `($Γ ⊨ $M ≈ $N ⦂ $A) => `(LogicalRel $Γ $A $M $N)

theorem 𝓔_typing :
  ∀ {A ρ M N},
    𝓔 A ρ M N →
    Nonempty (0 ⊢ [] ⊢ M ⦂ substT ρ.left A) ∧
    Nonempty (0 ⊢ [] ⊢ N ⦂ substT ρ.right A)
  | _, _, _, _, h => by
      have h' := h
      simp [𝓔] at h'
      rcases h' with ⟨hM, hN, _V, _W, _v, _w, _mSteps, _nSteps, _rel⟩
      exact ⟨⟨hM⟩, ⟨hN⟩⟩

theorem 𝒱_typing :
  ∀ {A ρ V W} {v : Value V} {w : Value W},
    𝒱 A ρ V W v w →
    Nonempty (0 ⊢ [] ⊢ V ⦂ substT ρ.left A) ∧
    Nonempty (0 ⊢ [] ⊢ W ⦂ substT ρ.right A)
  | #α, ρ, _V, _W, _v, _w, h => by
      have h' := h
      simp [𝒱] at h'
      rcases h' with ⟨hV, hW, _rel⟩
      exact ⟨⟨hV⟩, ⟨hW⟩⟩
  | ℕ, ρ, _V, _W, v, w, h => by
      cases v with
      | vZero =>
          cases w with
          | vZero =>
              simp [𝒱, 𝒱nat] at h
              exact ⟨⟨.t_zero⟩, ⟨.t_zero⟩⟩
          | vLam => simp [𝒱, 𝒱nat] at h
          | vTrue => simp [𝒱, 𝒱nat] at h
          | vFalse => simp [𝒱, 𝒱nat] at h
          | vSuc _ => simp [𝒱, 𝒱nat] at h
          | vTlam => simp [𝒱, 𝒱nat] at h
      | vSuc v' =>
          cases w with
          | vSuc w' =>
              simp [𝒱, 𝒱nat] at h
              have hNat : 𝒱 ℕ ρ _ _ v' w' := by
                simpa [𝒱] using h
              rcases 𝒱_typing (A := ℕ) (ρ := ρ) (v := v') (w := w') hNat with
                ⟨⟨hV⟩, ⟨hW⟩⟩
              exact ⟨⟨.t_suc hV⟩, ⟨.t_suc hW⟩⟩
          | vLam => simp [𝒱, 𝒱nat] at h
          | vTrue => simp [𝒱, 𝒱nat] at h
          | vFalse => simp [𝒱, 𝒱nat] at h
          | vZero => simp [𝒱, 𝒱nat] at h
          | vTlam => simp [𝒱, 𝒱nat] at h
      | vLam =>
          simp [𝒱, 𝒱nat] at h
      | vTrue =>
          simp [𝒱, 𝒱nat] at h
      | vFalse =>
          simp [𝒱, 𝒱nat] at h
      | vTlam =>
          simp [𝒱, 𝒱nat] at h
  | 𝔹, _ρ, _V, _W, v, w, h => by
      cases v <;> cases w <;> simp [𝒱, 𝒱bool] at h ⊢
      case vTrue.vTrue =>
        exact ⟨⟨.t_true⟩, ⟨.t_true⟩⟩
      case vFalse.vFalse =>
        exact ⟨⟨.t_false⟩, ⟨.t_false⟩⟩
  | A ⇒ B, _ρ, _V, _W, v, w, h => by
      cases v <;> cases w <;> simp [𝒱] at h ⊢
      case vLam.vLam =>
        rcases h with ⟨hV, hW, _fRel⟩
        exact ⟨⟨hV⟩, ⟨hW⟩⟩
  | ∀ₜ A, _ρ, _V, _W, v, w, h => by
      cases v <;> cases w <;> simp [𝒱] at h ⊢
      case vTlam.vTlam =>
        rcases h with ⟨hV, hW, _allRel⟩
        exact ⟨⟨hV⟩, ⟨hW⟩⟩

theorem 𝒱_to_𝓔 :
  ∀ {A ρ V W} (v : Value V) (w : Value W),
    𝒱 A ρ V W v w → 𝓔 A ρ V W
  | A, ρ, V, W, v, w, VWrel => by
      rcases 𝒱_typing (A := A) (ρ := ρ) (V := V) (W := W) (v := v) (w := w) VWrel with
        ⟨⟨hV⟩, ⟨hW⟩⟩
      unfold 𝓔
      exact ⟨hV, hW, V, W, v, w, ⟨.refl V⟩, ⟨.refl W⟩, VWrel⟩

def 𝒢_empty : 𝒢 [] emptyRelSub emptyRelEnv := trivial

def tailRelEnv_extendRelEnv (γ : RelEnv) (V W : Term) :
    tailRelEnv (extendRelEnv γ V W) = γ := by
  cases γ
  rfl

def extendRelEnv_related :
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
  | wk_suc {ρ A₁ A₂} (hA₁ : WfTy 0 A₁) (hA₂ : WfTy 0 A₂) (R : Rel A₁ A₂) :
      WkRel Nat.succ ρ (extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
  | wk_ext {ξ ρ ρ' B₁ B₂}
      (hB₁ : WfTy 0 B₁) (hB₂ : WfTy 0 B₂) (S : Rel B₁ B₂) :
      WkRel ξ ρ ρ' →
      WkRel (extT ξ)
        (extendRelSub ρ B₁ B₂ hB₁ hB₂ S)
        (extendRelSub ρ' B₁ B₂ hB₁ hB₂ S)

def wk_left_var :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ρ.left α = ρ'.left (ξ α)
  | _, _, _, .wk_suc _ _ _, α => rfl
  | _, _, _, .wk_ext _ _ _ wk, 0 => rfl
  | _, _, _, .wk_ext _ _ _ wk, α + 1 =>
      wk_left_var wk α

def wk_right_var :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ρ.right α = ρ'.right (ξ α)
  | _, _, _, .wk_suc _ _ _, α => rfl
  | _, _, _, .wk_ext _ _ _ wk, 0 => rfl
  | _, _, _, .wk_ext _ _ _ wk, α + 1 =>
      wk_right_var wk α

def wk_left_subst :
  ∀ {ξ ρ ρ'}, WkRel ξ ρ ρ' →
    (A : Ty) → substT ρ'.left (renameT ξ A) = substT ρ.left A
  | ξ, ρ, ρ', wk, A =>
      (rename_subst_commute ξ ρ'.left A).trans
        (subst_cong (fun α => (wk_left_var wk α).symm) A)

def wk_right_subst :
  ∀ {ξ ρ ρ'}, WkRel ξ ρ ρ' →
    (A : Ty) → substT ρ'.right (renameT ξ A) = substT ρ.right A
  | ξ, ρ, ρ', wk, A =>
      (rename_subst_commute ξ ρ'.right A).trans
        (subst_cong (fun α => (wk_right_var wk α).symm) A)

theorem wk_rhoR_cast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    (wk : WkRel ξ ρ ρ') →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W}
      {hV : 0 ⊢ [] ⊢ V ⦂ ρ.left α} {hW : 0 ⊢ [] ⊢ W ⦂ ρ.right α},
      (ρ.R α) V W v w hV hW →
      (ρ'.R (ξ α)) V W v w
        (Eq.ndrec hV (wk_left_var wk α))
        (Eq.ndrec hW (wk_right_var wk α))
  := by
    intro ξ ρ ρ' wk α V W v w hV hW rel
    induction wk generalizing α V W v w with
    | wk_suc hA₁ hA₂ R =>
        simpa [wk_left_var, wk_right_var] using rel
    | wk_ext hB₁ hB₂ S wk ih =>
        cases α with
        | zero =>
            simpa [wk_left_var, wk_right_var] using rel
        | succ α =>
            simpa [extendRelSub, extT, wk_left_var, wk_right_var] using
              ih α rel

theorem wk_rhoR_uncast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    (wk : WkRel ξ ρ ρ') →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W}
      {hV : 0 ⊢ [] ⊢ V ⦂ ρ'.left (ξ α)} {hW : 0 ⊢ [] ⊢ W ⦂ ρ'.right (ξ α)},
      (ρ'.R (ξ α)) V W v w hV hW →
      (ρ.R α) V W v w
        (Eq.ndrec hV (wk_left_var wk α).symm)
        (Eq.ndrec hW (wk_right_var wk α).symm)
  := by
    intro ξ ρ ρ' wk α V W v w hV hW rel
    induction wk generalizing α V W v w with
    | wk_suc hA₁ hA₂ R =>
        simpa [wk_left_var, wk_right_var] using rel
    | wk_ext hB₁ hB₂ S wk ih =>
        cases α with
        | zero =>
            simpa [wk_left_var, wk_right_var] using rel
        | succ α =>
            simpa [extendRelSub, extT, wk_left_var, wk_right_var] using
              ih α rel

mutual

theorem 𝒱_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    𝒱 A ρ V W v w →
    𝒱 (renameT ξ A) ρ' V W v w
  | #α, ξ, ρ, ρ', V, W, v, w, wk, h => by
      simp [𝒱, renameT] at h ⊢
      rcases h with ⟨hV, hW, rel⟩
      refine ⟨Eq.ndrec hV (wk_left_var wk α), ⟨Eq.ndrec hW (wk_right_var wk α), ?_⟩⟩
      exact wk_rhoR_cast (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk α rel
  | ℕ, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, renameT] using h
  | 𝔹, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, renameT] using h
  | A ⇒ B, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vLam.vLam =>
        rcases h with ⟨hV, hW, fRel⟩
        refine ⟨Eq.ndrec hV (wk_left_subst wk (A ⇒ B)).symm,
          ⟨Eq.ndrec hW (wk_right_subst wk (A ⇒ B)).symm, ?_⟩⟩
        intro V' W' v' w' hArg
        have hArg0 :
            𝒱 A ρ V' W' v' w' :=
          𝒱_unrename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hArg
        exact 𝓔_rename_wk (A := B) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk (fRel v' w' hArg0)
  | ∀ₜ A, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vTlam.vTlam =>
        rcases h with ⟨hV, hW, allRel⟩
        refine ⟨Eq.ndrec hV (wk_left_subst wk (∀ₜ A)).symm,
          ⟨Eq.ndrec hW (wk_right_subst wk (∀ₜ A)).symm, ?_⟩⟩
        intro A₁ A₂ hA₁ hA₂ R
        have wk' :
            WkRel (extT ξ)
              (extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
              (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R) :=
          WkRel.wk_ext (hB₁ := hA₁) (hB₂ := hA₂) (S := R) wk
        exact 𝓔_rename_wk
          (A := A)
          (ξ := extT ξ)
          (ρ := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
          (ρ' := extendRelSub ρ' A₁ A₂ hA₁ hA₂ R)
          wk' (allRel A₁ A₂ hA₁ hA₂ R)

theorem 𝒱_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    𝒱 (renameT ξ A) ρ' V W v w →
    𝒱 A ρ V W v w
  | #α, ξ, ρ, ρ', V, W, v, w, wk, h => by
      simp [𝒱, renameT] at h ⊢
      rcases h with ⟨hV, hW, rel⟩
      refine ⟨Eq.ndrec hV (wk_left_var wk α).symm, ⟨Eq.ndrec hW (wk_right_var wk α).symm, ?_⟩⟩
      exact wk_rhoR_uncast (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk α rel
  | ℕ, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, renameT] using h
  | 𝔹, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, renameT] using h
  | A ⇒ B, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vLam.vLam =>
        rcases h with ⟨hV, hW, fRel⟩
        refine ⟨Eq.ndrec hV (wk_left_subst wk (A ⇒ B)),
          ⟨Eq.ndrec hW (wk_right_subst wk (A ⇒ B)), ?_⟩⟩
        intro V' W' v' w' hArg
        have hArg' :
            𝒱 (renameT ξ A) ρ' V' W' v' w' :=
          𝒱_rename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk hArg
        exact 𝓔_unrename_wk (A := B) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk (fRel v' w' hArg')
  | ∀ₜ A, ξ, ρ, ρ', V, W, v, w, wk, h => by
      cases v <;> cases w <;> simp [𝒱, renameT] at h ⊢
      case vTlam.vTlam =>
        rcases h with ⟨hV, hW, allRel⟩
        refine ⟨Eq.ndrec hV (wk_left_subst wk (∀ₜ A)),
          ⟨Eq.ndrec hW (wk_right_subst wk (∀ₜ A)), ?_⟩⟩
        intro A₁ A₂ hA₁ hA₂ R
        have wk' :
            WkRel (extT ξ)
              (extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
              (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R) :=
          WkRel.wk_ext (hB₁ := hA₁) (hB₂ := hA₂) (S := R) wk
        exact 𝓔_unrename_wk
          (A := A)
          (ξ := extT ξ)
          (ρ := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
          (ρ' := extendRelSub ρ' A₁ A₂ hA₁ hA₂ R)
          wk' (allRel A₁ A₂ hA₁ hA₂ R)

theorem 𝓔_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    𝓔 A ρ M N →
    𝓔 (renameT ξ A) ρ' M N
  | A, ξ, ρ, ρ', M, N, wk, h => by
      simp [𝓔] at h ⊢
      rcases h with ⟨hM, hN, V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨Eq.ndrec hM (wk_left_subst wk A).symm,
        Eq.ndrec hN (wk_right_subst wk A).symm,
        V, W, v, w, mSteps, nSteps,
        𝒱_rename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk rel⟩

theorem 𝓔_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    𝓔 (renameT ξ A) ρ' M N →
    𝓔 A ρ M N
  | A, ξ, ρ, ρ', M, N, wk, h => by
      simp [𝓔] at h ⊢
      rcases h with ⟨hM, hN, V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨Eq.ndrec hM (wk_left_subst wk A),
        Eq.ndrec hN (wk_right_subst wk A),
        V, W, v, w, mSteps, nSteps,
        𝒱_unrename_wk (A := A) (ξ := ξ) (ρ := ρ) (ρ' := ρ') wk rel⟩

end

theorem lift𝓔 :
  ∀ {A A₁ A₂ : Ty} {ρ : RelSub} {γ : RelEnv},
    (hA₁ : WfTy 0 A₁) →
    (hA₂ : WfTy 0 A₂) →
    (R : Rel A₁ A₂) →
    𝓔 A ρ (γ.left 0) (γ.right 0) →
    𝓔 (renameT Nat.succ A) (extendRelSub ρ A₁ A₂ hA₁ hA₂ R) (γ.left 0) (γ.right 0)
  | A, A₁, A₂, ρ, γ, hA₁, hA₂, R, rel =>
      𝓔_rename_wk (A := A) (ξ := Nat.succ) (ρ := ρ)
        (ρ' := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
        (M := γ.left 0) (N := γ.right 0)
        (WkRel.wk_suc (hA₁ := hA₁) (hA₂ := hA₂) (R := R))
        rel

theorem liftRelEnv_related :
  ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv},
    (hA₁ : WfTy 0 A₁) →
    (hA₂ : WfTy 0 A₂) →
    (R : Rel A₁ A₂) →
    𝒢 Γ ρ γ →
    𝒢 (liftCtx Γ) (extendRelSub ρ A₁ A₂ hA₁ hA₂ R) γ
  | [], _, _, _, _, _, _, _, _ => trivial
  | A :: Γ, A₁, A₂, ρ, γ, hA₁, hA₂, R, h => by
      exact And.intro
        (lift𝓔 (A := A) (A₁ := A₁) (A₂ := A₂) (ρ := ρ) (γ := γ) hA₁ hA₂ R h.1)
        (liftRelEnv_related (Γ := Γ) (A₁ := A₁) (A₂ := A₂)
          (ρ := ρ) (γ := tailRelEnv γ) hA₁ hA₂ R h.2)

structure SubstRel (σ : SubstT) (ρ ρ' : RelSub) : Prop where
  leftSubstVar :
    ∀ α, ρ'.left α = substT ρ.left (σ α)
  rightSubstVar :
    ∀ α, ρ'.right α = substT ρ.right (σ α)
  varTo :
    ∀ α {V W} {v : Value V} {w : Value W},
      𝒱 (#α) ρ' V W v w → 𝒱 (σ α) ρ V W v w
  varFrom :
    ∀ α {V W} {v : Value V} {w : Value W},
      𝒱 (σ α) ρ V W v w → 𝒱 (#α) ρ' V W v w

theorem exts_SubstRel :
  ∀ {σ : SubstT} {ρ ρ' : RelSub} {A₁ A₂ : Ty},
    (hA₁ : WfTy 0 A₁) →
    (hA₂ : WfTy 0 A₂) →
    (R : Rel A₁ A₂) →
    SubstRel σ ρ ρ' →
    SubstRel (extsT σ)
      (extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
      (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R)
  := fun {σ} {ρ} {ρ'} {A₁} {A₂} hA₁ hA₂ R sr =>
    { leftSubstVar := by
        intro α
        cases α with
        | zero => rfl
        | succ α =>
            have hwk :
                substT (extendRelSub ρ A₁ A₂ hA₁ hA₂ R).left (renameT Nat.succ (σ α)) =
                  substT ρ.left (σ α) :=
              wk_left_subst (ξ := Nat.succ) (ρ := ρ)
                (ρ' := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
                (WkRel.wk_suc (hA₁ := hA₁) (hA₂ := hA₂) (R := R)) (σ α)
            calc
              (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R).left (α + 1)
                  = ρ'.left α := rfl
              _ = substT ρ.left (σ α) := sr.leftSubstVar α
              _ = substT (extendRelSub ρ A₁ A₂ hA₁ hA₂ R).left (renameT Nat.succ (σ α)) :=
                    hwk.symm
              _ = substT (extendRelSub ρ A₁ A₂ hA₁ hA₂ R).left (extsT σ (α + 1)) := rfl
      rightSubstVar := by
        intro α
        cases α with
        | zero => rfl
        | succ α =>
            have hwk :
                substT (extendRelSub ρ A₁ A₂ hA₁ hA₂ R).right (renameT Nat.succ (σ α)) =
                  substT ρ.right (σ α) :=
              wk_right_subst (ξ := Nat.succ) (ρ := ρ)
                (ρ' := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
                (WkRel.wk_suc (hA₁ := hA₁) (hA₂ := hA₂) (R := R)) (σ α)
            calc
              (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R).right (α + 1)
                  = ρ'.right α := rfl
              _ = substT ρ.right (σ α) := sr.rightSubstVar α
              _ = substT (extendRelSub ρ A₁ A₂ hA₁ hA₂ R).right (renameT Nat.succ (σ α)) :=
                    hwk.symm
              _ = substT (extendRelSub ρ A₁ A₂ hA₁ hA₂ R).right (extsT σ (α + 1)) := rfl
      varTo := by
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
                𝒱 (renameT Nat.succ (σ α))
                  (extendRelSub ρ A₁ A₂ hA₁ hA₂ R) V W v w :=
              𝒱_rename_wk (A := σ α) (ξ := Nat.succ) (ρ := ρ)
                (ρ' := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
                (WkRel.wk_suc (hA₁ := hA₁) (hA₂ := hA₂) (R := R)) hσ
            simpa [extsT] using hShift
      varFrom := by
        intro α V W v w rel
        cases α with
        | zero =>
            simpa [𝒱, extendRelSub, extsT] using rel
        | succ α =>
            have hShift :
                𝒱 (renameT Nat.succ (σ α))
                  (extendRelSub ρ A₁ A₂ hA₁ hA₂ R) V W v w := by
              simpa [extsT] using rel
            have hσ : 𝒱 (σ α) ρ V W v w :=
              𝒱_unrename_wk (A := σ α) (ξ := Nat.succ) (ρ := ρ)
                (ρ' := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
                (WkRel.wk_suc (hA₁ := hA₁) (hA₂ := hA₂) (R := R)) hShift
            have rel' : 𝒱 (#α) ρ' V W v w :=
              sr.varFrom α hσ
            simpa [𝒱, extendRelSub] using rel' }

def substRel_left_subst :
  ∀ {σ ρ ρ'} (sr : SubstRel σ ρ ρ') (A : Ty),
    substT ρ'.left A = substT ρ.left (substT σ A)
  | σ, ρ, ρ', sr, A =>
      (subst_cong sr.leftSubstVar A).trans (sub_sub σ ρ.left A).symm

def substRel_right_subst :
  ∀ {σ ρ ρ'} (sr : SubstRel σ ρ ρ') (A : Ty),
    substT ρ'.right A = substT ρ.right (substT σ A)
  | σ, ρ, ρ', sr, A =>
      (subst_cong sr.rightSubstVar A).trans (sub_sub σ ρ.right A).symm

mutual

theorem 𝒱_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    𝒱 A ρ' V W v w →
    𝒱 (substT σ A) ρ V W v w
  | #α, σ, ρ, ρ', V, W, v, w, sr, h =>
      sr.varTo α h
  | ℕ, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, substT] using h
  | 𝔹, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, substT] using h
  | A ⇒ B, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vLam.vLam =>
        rcases h with ⟨hV, hW, fRel⟩
        refine ⟨Eq.ndrec hV (substRel_left_subst sr (A ⇒ B)),
          ⟨Eq.ndrec hW (substRel_right_subst sr (A ⇒ B)), ?_⟩⟩
        intro V' W' v' w' hArg
        have hArg0 :
            𝒱 A ρ' V' W' v' w' :=
          𝒱_unsubst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hArg
        exact 𝓔_subst (A := B) (σ := σ) (ρ := ρ) (ρ' := ρ') sr (fRel v' w' hArg0)
  | ∀ₜ A, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vTlam.vTlam =>
        rcases h with ⟨hV, hW, allRel⟩
        refine ⟨Eq.ndrec hV (substRel_left_subst sr (∀ₜ A)),
          ⟨Eq.ndrec hW (substRel_right_subst sr (∀ₜ A)), ?_⟩⟩
        intro A₁ A₂ hA₁ hA₂ R
        have sr' :
            SubstRel (extsT σ)
              (extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
              (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R) :=
          exts_SubstRel (σ := σ) (ρ := ρ) (ρ' := ρ')
            (A₁ := A₁) (A₂ := A₂) hA₁ hA₂ R sr
        exact 𝓔_subst
          (A := A)
          (σ := extsT σ)
          (ρ := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
          (ρ' := extendRelSub ρ' A₁ A₂ hA₁ hA₂ R)
          sr' (allRel A₁ A₂ hA₁ hA₂ R)

theorem 𝒱_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    𝒱 (substT σ A) ρ V W v w →
    𝒱 A ρ' V W v w
  | #α, σ, ρ, ρ', V, W, v, w, sr, h =>
      sr.varFrom α h
  | ℕ, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, substT] using h
  | 𝔹, _, _, _, _, _, _, _, _, h => by
      simpa [𝒱, substT] using h
  | A ⇒ B, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vLam.vLam =>
        rcases h with ⟨hV, hW, fRel⟩
        refine ⟨Eq.ndrec hV (substRel_left_subst sr (A ⇒ B)).symm,
          ⟨Eq.ndrec hW (substRel_right_subst sr (A ⇒ B)).symm, ?_⟩⟩
        intro V' W' v' w' hArg
        have hArg0 :
            𝒱 (substT σ A) ρ V' W' v' w' :=
          𝒱_subst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr hArg
        exact 𝓔_unsubst (A := B) (σ := σ) (ρ := ρ) (ρ' := ρ') sr (fRel v' w' hArg0)
  | ∀ₜ A, σ, ρ, ρ', V, W, v, w, sr, h => by
      cases v <;> cases w <;> simp [𝒱, substT] at h ⊢
      case vTlam.vTlam =>
        rcases h with ⟨hV, hW, allRel⟩
        refine ⟨Eq.ndrec hV (substRel_left_subst sr (∀ₜ A)).symm,
          ⟨Eq.ndrec hW (substRel_right_subst sr (∀ₜ A)).symm, ?_⟩⟩
        intro A₁ A₂ hA₁ hA₂ R
        have sr' :
            SubstRel (extsT σ)
              (extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
              (extendRelSub ρ' A₁ A₂ hA₁ hA₂ R) :=
          exts_SubstRel (σ := σ) (ρ := ρ) (ρ' := ρ')
            (A₁ := A₁) (A₂ := A₂) hA₁ hA₂ R sr
        exact 𝓔_unsubst
          (A := A)
          (σ := extsT σ)
          (ρ := extendRelSub ρ A₁ A₂ hA₁ hA₂ R)
          (ρ' := extendRelSub ρ' A₁ A₂ hA₁ hA₂ R)
          sr' (allRel A₁ A₂ hA₁ hA₂ R)

theorem 𝓔_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    𝓔 A ρ' M N →
    𝓔 (substT σ A) ρ M N
  | A, σ, ρ, ρ', M, N, sr, h => by
      simp [𝓔] at h ⊢
      rcases h with ⟨hM, hN, V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨Eq.ndrec hM (substRel_left_subst sr A),
        Eq.ndrec hN (substRel_right_subst sr A),
        V, W, v, w, mSteps, nSteps,
        𝒱_subst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr rel⟩

theorem 𝓔_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    𝓔 (substT σ A) ρ M N →
    𝓔 A ρ' M N
  | A, σ, ρ, ρ', M, N, sr, h => by
      simp [𝓔] at h ⊢
      rcases h with ⟨hM, hN, V, W, v, w, mSteps, nSteps, rel⟩
      exact ⟨Eq.ndrec hM (substRel_left_subst sr A).symm,
        Eq.ndrec hN (substRel_right_subst sr A).symm,
        V, W, v, w, mSteps, nSteps,
        𝒱_unsubst (A := A) (σ := σ) (ρ := ρ) (ρ' := ρ') sr rel⟩

end

theorem singleTy_SubstRel :
  ∀ {ρ B},
    SubstRel (singleTyEnv B) ρ
      (extendRelSub ρ
        (substT ρ.left B)
        (substT ρ.right B)
        (substT_codom_closed ρ.left ρ.leftClosed B)
        (substT_codom_closed ρ.right ρ.rightClosed B)
        (fun V W v w hV hW => 𝒱 B ρ V W v w))
  | ρ, B => by
      refine
      { leftSubstVar := by
          intro α
          cases α <;> rfl
        rightSubstVar := by
          intro α
          cases α <;> rfl
        varTo := by
          intro α V W v w rel
          cases α with
          | zero =>
              simp [𝒱, extendRelSub] at rel
              rcases rel with ⟨_hV, _hW, relB⟩
              simpa [singleTyEnv] using relB
          | succ α =>
              simpa [𝒱, extendRelSub, singleTyEnv] using rel
        varFrom := by
          intro α V W v w rel
          cases α with
          | zero =>
              rcases 𝒱_typing (A := B) (ρ := ρ) (V := V) (W := W) (v := v) (w := w) rel with
                ⟨⟨hV⟩, ⟨hW⟩⟩
              simpa [𝒱, extendRelSub, singleTyEnv] using
                (show ∃ (hV0 : 0 ⊢ [] ⊢ V ⦂ substT ρ.left B),
                    ∃ (hW0 : 0 ⊢ [] ⊢ W ⦂ substT ρ.right B),
                      𝒱 B ρ V W v w from ⟨hV, hW, rel⟩)
          | succ α =>
              simpa [𝒱, extendRelSub, singleTyEnv] using rel }

theorem 𝒱_compositionality_to :
  ∀ {A B ρ V W} {v : Value V} {w : Value W},
    𝒱 A
      (extendRelSub ρ
        (substT ρ.left B)
        (substT ρ.right B)
        (substT_codom_closed ρ.left ρ.leftClosed B)
        (substT_codom_closed ρ.right ρ.rightClosed B)
        (fun V W v w hV hW => 𝒱 B ρ V W v w))
      V W v w →
    𝒱 (A [ B ]ₜ) ρ V W v w
  | A, B, ρ, V, W, v, w, h =>
      𝒱_subst (A := A) (σ := singleTyEnv B) (ρ := ρ)
        (ρ' := extendRelSub ρ
          (substT ρ.left B)
          (substT ρ.right B)
          (substT_codom_closed ρ.left ρ.leftClosed B)
          (substT_codom_closed ρ.right ρ.rightClosed B)
          (fun V W v w hV hW => 𝒱 B ρ V W v w))
        singleTy_SubstRel h

theorem 𝒱_compositionality_from :
  ∀ {A B ρ V W} {v : Value V} {w : Value W},
    𝒱 (A [ B ]ₜ) ρ V W v w →
    𝒱 A
      (extendRelSub ρ
        (substT ρ.left B)
        (substT ρ.right B)
        (substT_codom_closed ρ.left ρ.leftClosed B)
        (substT_codom_closed ρ.right ρ.rightClosed B)
        (fun V W v w hV hW => 𝒱 B ρ V W v w))
      V W v w
  | A, B, ρ, V, W, v, w, h =>
      𝒱_unsubst (A := A) (σ := singleTyEnv B) (ρ := ρ)
        (ρ' := extendRelSub ρ
          (substT ρ.left B)
          (substT ρ.right B)
          (substT_codom_closed ρ.left ρ.leftClosed B)
          (substT_codom_closed ρ.right ρ.rightClosed B)
          (fun V W v w hV hW => 𝒱 B ρ V W v w))
        singleTy_SubstRel h

theorem 𝓔_compositionality_to :
  ∀ {A B ρ M N},
    𝓔 A
      (extendRelSub ρ
        (substT ρ.left B)
        (substT ρ.right B)
        (substT_codom_closed ρ.left ρ.leftClosed B)
        (substT_codom_closed ρ.right ρ.rightClosed B)
        (fun V W v w hV hW => 𝒱 B ρ V W v w))
      M N →
    𝓔 (A [ B ]ₜ) ρ M N
  | A, B, ρ, M, N, h =>
      𝓔_subst (A := A) (σ := singleTyEnv B) (ρ := ρ)
        (ρ' := extendRelSub ρ
          (substT ρ.left B)
          (substT ρ.right B)
          (substT_codom_closed ρ.left ρ.leftClosed B)
          (substT_codom_closed ρ.right ρ.rightClosed B)
          (fun V W v w hV hW => 𝒱 B ρ V W v w))
        singleTy_SubstRel h

theorem 𝓔_compositionality_from :
  ∀ {A B ρ M N},
    𝓔 (A [ B ]ₜ) ρ M N →
    𝓔 A
      (extendRelSub ρ
        (substT ρ.left B)
        (substT ρ.right B)
        (substT_codom_closed ρ.left ρ.leftClosed B)
        (substT_codom_closed ρ.right ρ.rightClosed B)
        (fun V W v w hV hW => 𝒱 B ρ V W v w))
      M N
  | A, B, ρ, M, N, h =>
      𝓔_unsubst (A := A) (σ := singleTyEnv B) (ρ := ρ)
        (ρ' := extendRelSub ρ
          (substT ρ.left B)
          (substT ρ.right B)
          (substT_codom_closed ρ.left ρ.leftClosed B)
          (substT_codom_closed ρ.right ρ.rightClosed B)
          (fun V W v w hV hW => 𝒱 B ρ V W v w))
        singleTy_SubstRel h

end Extrinsic

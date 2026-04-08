import extrinsic.LogicalRelation
import extrinsic.TermSubst

namespace Extrinsic

--------------------------------------------------------------------------------
-- Compatibility Lemmas
--------------------------------------------------------------------------------

noncomputable section

def 𝒢_left_SubstWf {Γ ρ γ} (env : 𝒢 Γ ρ γ) :
    SubstWf 0 (List.map (substT ρ.left) Γ) [] γ.left := by
  intro x A h
  induction Γ generalizing γ x A with
  | nil =>
      cases h
  | cons A₀ Γ ih =>
      cases env with
      | intro hHead hTail =>
          cases h with
          | Z =>
              exact Classical.choice ((𝓔_typing (A := A₀) (ρ := ρ) (M := γ.left 0) (N := γ.right 0) hHead).1)
          | S h' =>
              simpa [tailRelEnv] using ih hTail h'

def 𝒢_right_SubstWf {Γ ρ γ} (env : 𝒢 Γ ρ γ) :
    SubstWf 0 (List.map (substT ρ.right) Γ) [] γ.right := by
  intro x A h
  induction Γ generalizing γ x A with
  | nil =>
      cases h
  | cons A₀ Γ ih =>
      cases env with
      | intro hHead hTail =>
          cases h with
          | Z =>
              exact Classical.choice ((𝓔_typing (A := A₀) (ρ := ρ) (M := γ.left 0) (N := γ.right 0) hHead).2)
          | S h' =>
              simpa [tailRelEnv] using ih hTail h'

theorem substT_id_typed {Δ A σ}
    (hA : WfTy Δ A)
    (hσ : ∀ α, α < Δ → σ α = #α) :
    substT σ A = A := by
  induction hA generalizing σ with
  | var hX =>
      simpa using hσ _ hX
  | nat =>
      rfl
  | bool =>
      rfl
  | fn hA hB ihA ihB =>
      simpa [substT, ihA hσ, ihB hσ]
  | all hA ih =>
      have hBody := ih (σ := extsT σ) (by
        intro α hα
        cases α with
        | zero =>
            rfl
        | succ α =>
            have hα' := Nat.lt_of_succ_lt_succ hα
            simpa [extsT, renameT, hσ α hα'])
      simpa [substT, hBody]

theorem substTT_id_typed {Δ Γ M A σ}
    (hM : Δ ⊢ Γ ⊢ M ⦂ A)
    (hσ : ∀ α, α < Δ → σ α = #α) :
    substTT σ M = M := by
  induction hM generalizing σ with
  | t_var h =>
      rfl
  | t_lam hA hN ih =>
      simpa [substTT, substT_id_typed hA hσ, ih hσ]
  | t_app hL hM ihL ihM =>
      simpa [substTT, ihL hσ, ihM hσ]
  | t_true =>
      rfl
  | t_false =>
      rfl
  | t_zero =>
      rfl
  | t_suc hM ih =>
      simpa [substTT, ih hσ]
  | t_case hL hM hN ihL ihM ihN =>
      simpa [substTT, ihL hσ, ihM hσ, ihN hσ]
  | t_if hL hM hN ihL ihM ihN =>
      simpa [substTT, ihL hσ, ihM hσ, ihN hσ]
  | t_tlam hN ih =>
      have hNid := ih (σ := extsT σ) (by
        intro α hα
        cases α with
        | zero =>
            rfl
        | succ α =>
            have hα' := Nat.lt_of_succ_lt_succ hα
            simpa [extsT, renameT, hσ α hα'])
      simpa [substTT, hNid]
  | t_tapp hM hB ih =>
      simpa [substTT, ih hσ, substT_id_typed hB hσ]

theorem substTT_rename_commute (σ : SubstT) (ρ : Rename) :
    ∀ M, substTT σ (rename ρ M) = rename ρ (substTT σ M)
  | Term.var i => rfl
  | Term.lam A N => by
      simp [substTT, rename, substTT_rename_commute σ (ext ρ) N]
  | Term.app L M => by
      simp [substTT, rename, substTT_rename_commute σ ρ L, substTT_rename_commute σ ρ M]
  | Term.ttrue => rfl
  | Term.tfalse => rfl
  | Term.zero => rfl
  | Term.suc M => by
      simpa [substTT, rename] using congrArg Term.suc (substTT_rename_commute σ ρ M)
  | Term.natCase L M N => by
      simp [substTT, rename,
        substTT_rename_commute σ ρ L,
        substTT_rename_commute σ ρ M,
        substTT_rename_commute σ (ext ρ) N]
  | Term.ite L M N => by
      simp [substTT, rename,
        substTT_rename_commute σ ρ L,
        substTT_rename_commute σ ρ M,
        substTT_rename_commute σ ρ N]
  | Term.tlam N => by
      simpa [substTT, rename] using congrArg Term.tlam (substTT_rename_commute (extsT σ) ρ N)
  | Term.tapp M A => by
      simp [substTT, rename, substTT_rename_commute σ ρ M]

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

theorem compat_app :
  ∀ {Γ A B} (L M : Term),
    LogicalRel Γ (A ⇒ B) L L →
    LogicalRel Γ A M M →
    LogicalRel Γ B (Term.app L M) (Term.app L M)
  | Γ, A, B, L, M, Lrel, Mrel => by
      intro ρ γ env
      have hLrel := Lrel ρ γ env
      have hMrel := Mrel ρ γ env
      simp only [𝓔] at hLrel hMrel
      rcases hLrel with ⟨hL, hL', VL, WL, vL, wL, lSteps, rSteps, hFun⟩
      rcases hMrel with ⟨hM, hM', VM, WM, vM, wM, mSteps, mStepsR, hArg⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      cases vL <;> cases wL <;> simp [𝒱] at hFun
      case vLam.vLam C N D P =>
        rcases hFun with ⟨_, _, hFun⟩
        have hRes := hFun vM wM hArg
        simp only [𝓔] at hRes
        rcases hRes with ⟨_, _, VB, WB, vb, wb, redL, redR, hVB⟩
        rcases redL with ⟨redL⟩
        rcases redR with ⟨redR⟩
        have hAppL :
            0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (Term.app L M)) ⦂ substT ρ.left B := by
          simpa [subst, substTT] using HasType.t_app hL hM
        have hAppR :
            0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (Term.app L M)) ⦂ substT ρ.right B := by
          simpa [subst, substTT] using HasType.t_app hL' hM'
        have leftRed :
            substTT ρ.left (subst γ.left (Term.app L M)) —↠ singleSubst N VM := by
          exact multi_trans
            (by
              simpa [subst, substTT] using app_multi lSteps Value.vLam mSteps)
            (by simpa using beta_lam_multi (N := N) (W := VM) vM)
        have rightRed :
            substTT ρ.right (subst γ.right (Term.app L M)) —↠ singleSubst P WM := by
          exact multi_trans
            (by
              simpa [subst, substTT] using app_multi rSteps Value.vLam mStepsR)
            (by simpa using beta_lam_multi (N := P) (W := WM) wM)
        unfold 𝓔
        exact ⟨hAppL, hAppR, VB, WB, vb, wb,
          ⟨multi_trans leftRed redL⟩,
          ⟨multi_trans rightRed redR⟩,
          hVB⟩

theorem compat_true :
  ∀ {Γ}, Γ ⊨ ˋtrue ≈ ˋtrue ⦂ 𝔹
  | Γ => by
      intro ρ γ env
      exact 𝒱_to_𝓔 (A := 𝔹) (ρ := ρ) (V := ˋtrue) (W := ˋtrue)
        .vTrue .vTrue (by simpa [𝒱, 𝒱bool])

theorem compat_suc :
  ∀ {Γ} (M : Term),
    Γ ⊨ M ≈ M ⦂ ℕ →
    Γ ⊨ (ˋsuc M) ≈ (ˋsuc M) ⦂ ℕ
  | Γ, M, Mrel => by
      intro ρ γ env
      have hMrel := Mrel ρ γ env
      simp only [𝓔] at hMrel
      rcases hMrel with ⟨hM, hM', V, W, v, w, mSteps, mStepsR, hVW⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      have hSucL :
          0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (ˋsuc M)) ⦂ substT ρ.left ℕ := by
        simpa [subst, substTT] using HasType.t_suc hM
      have hSucR :
          0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (ˋsuc M)) ⦂ substT ρ.right ℕ := by
        simpa [subst, substTT] using HasType.t_suc hM'
      unfold 𝓔
      exact ⟨hSucL, hSucR, ˋsuc V, ˋsuc W, .vSuc v, .vSuc w,
        ⟨by simpa [subst, substTT] using suc_multi mSteps⟩,
        ⟨by simpa [subst, substTT] using suc_multi mStepsR⟩,
        by simpa [𝒱, 𝒱nat] using hVW⟩

theorem compat_case :
  ∀ {Δ Γ A} (L M N : Term),
    Δ ⊢ (ℕ :: Γ) ⊢ N ⦂ A →
    Γ ⊨ L ≈ L ⦂ ℕ →
    Γ ⊨ M ≈ M ⦂ A →
    (ℕ :: Γ) ⊨ N ≈ N ⦂ A →
    Γ ⊨ (caseₜ L [zero⇒ M |suc⇒ N]) ≈ (caseₜ L [zero⇒ M |suc⇒ N]) ⦂ A
  | Δ, Γ, A, L, M, N, hN, Lrel, Mrel, Nrel => by
      intro ρ γ env
      have hTySubL : TySubstWf Δ 0 ρ.left := by
        intro X hX
        exact ρ.leftClosed X
      have hTySubR : TySubstWf Δ 0 ρ.right := by
        intro X hX
        exact ρ.rightClosed X
      have hSubExtL :
          SubstWf 0 (List.map (substT ρ.left) (ℕ :: Γ)) [substT ρ.left ℕ] (exts γ.left) := by
        intro x C hx
        cases hx with
        | Z =>
            simpa [exts] using
              (HasType.t_var (Δ := 0) (Γ := [substT ρ.left ℕ]) (i := 0)
                (A := substT ρ.left ℕ) HasTypeVar.Z)
        | S hx' =>
            simpa [exts] using
              typing_rename_shift (B := substT ρ.left ℕ)
                (𝒢_left_SubstWf (Γ := Γ) (ρ := ρ) (γ := γ) env hx')
      have hSubExtR :
          SubstWf 0 (List.map (substT ρ.right) (ℕ :: Γ)) [substT ρ.right ℕ] (exts γ.right) := by
        intro x C hx
        cases hx with
        | Z =>
            simpa [exts] using
              (HasType.t_var (Δ := 0) (Γ := [substT ρ.right ℕ]) (i := 0)
                (A := substT ρ.right ℕ) HasTypeVar.Z)
        | S hx' =>
            simpa [exts] using
              typing_rename_shift (B := substT ρ.right ℕ)
                (𝒢_right_SubstWf (Γ := Γ) (ρ := ρ) (γ := γ) env hx')
      have hNopenL :
          0 ⊢ [substT ρ.left ℕ] ⊢ substTT ρ.left (subst (exts γ.left) N) ⦂ substT ρ.left A := by
        have hSubExtLTT :
            SubstWf 0 (List.map (substT ρ.left) (ℕ :: Γ)) [substT ρ.left ℕ]
              (fun i => substTT ρ.left (exts γ.left i)) := by
          intro x C hx
          have hTyped : 0 ⊢ [substT ρ.left ℕ] ⊢ exts γ.left x ⦂ C := hSubExtL hx
          have hId : substTT ρ.left (exts γ.left x) = exts γ.left x := by
            exact substTT_id_typed (hM := hTyped) (hσ := by
              intro α hα
              exact False.elim (Nat.not_lt_zero α hα))
          exact Eq.ndrec
            (motive := fun T => 0 ⊢ [substT ρ.left ℕ] ⊢ T ⦂ C)
            hTyped
            hId.symm
        have hRaw :
            0 ⊢ [substT ρ.left ℕ] ⊢
              subst (fun i => substTT ρ.left (exts γ.left i)) (substTT ρ.left N) ⦂ substT ρ.left A := by
          exact typing_subst hSubExtLTT (typing_substTT (σ := ρ.left) hTySubL hN)
        exact Eq.ndrec
          (motive := fun T => 0 ⊢ [substT ρ.left ℕ] ⊢ T ⦂ substT ρ.left A)
          hRaw
          (subst_substTT_commute (exts γ.left) ρ.left N)
      have hNopenR :
          0 ⊢ [substT ρ.right ℕ] ⊢ substTT ρ.right (subst (exts γ.right) N) ⦂ substT ρ.right A := by
        have hSubExtRTT :
            SubstWf 0 (List.map (substT ρ.right) (ℕ :: Γ)) [substT ρ.right ℕ]
              (fun i => substTT ρ.right (exts γ.right i)) := by
          intro x C hx
          have hTyped : 0 ⊢ [substT ρ.right ℕ] ⊢ exts γ.right x ⦂ C := hSubExtR hx
          have hId : substTT ρ.right (exts γ.right x) = exts γ.right x := by
            exact substTT_id_typed (hM := hTyped) (hσ := by
              intro α hα
              exact False.elim (Nat.not_lt_zero α hα))
          exact Eq.ndrec
            (motive := fun T => 0 ⊢ [substT ρ.right ℕ] ⊢ T ⦂ C)
            hTyped
            hId.symm
        have hRaw :
            0 ⊢ [substT ρ.right ℕ] ⊢
              subst (fun i => substTT ρ.right (exts γ.right i)) (substTT ρ.right N) ⦂ substT ρ.right A := by
          exact typing_subst hSubExtRTT (typing_substTT (σ := ρ.right) hTySubR hN)
        exact Eq.ndrec
          (motive := fun T => 0 ⊢ [substT ρ.right ℕ] ⊢ T ⦂ substT ρ.right A)
          hRaw
          (subst_substTT_commute (exts γ.right) ρ.right N)
      have hMrel := Mrel ρ γ env
      have hMtypedL :
          0 ⊢ [] ⊢ substTT ρ.left (subst γ.left M) ⦂ substT ρ.left A :=
        Classical.choice (𝓔_typing (A := A) (ρ := ρ)
          (M := substTT ρ.left (subst γ.left M))
          (N := substTT ρ.right (subst γ.right M)) hMrel).1
      have hMtypedR :
          0 ⊢ [] ⊢ substTT ρ.right (subst γ.right M) ⦂ substT ρ.right A :=
        Classical.choice (𝓔_typing (A := A) (ρ := ρ)
          (M := substTT ρ.left (subst γ.left M))
          (N := substTT ρ.right (subst γ.right M)) hMrel).2
      have hLrel := Lrel ρ γ env
      simp only [𝓔] at hLrel
      rcases hLrel with ⟨hL, hL', VL, WL, vL, wL, lSteps, rSteps, hNat⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      cases vL with
      | vZero =>
          cases wL with
          | vZero =>
              simp [𝒱, 𝒱nat] at hNat
              have hMrel' := hMrel
              simp only [𝓔] at hMrel'
              rcases hMrel' with ⟨hM, hM', VM, WM, vM, wM, mSteps, mStepsR, hMval⟩
              rcases mSteps with ⟨mSteps⟩
              rcases mStepsR with ⟨mStepsR⟩
              have hCaseL :
                  0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (caseₜ L [zero⇒ M |suc⇒ N])) ⦂ substT ρ.left A := by
                simpa [subst, substTT] using HasType.t_case hL hM hNopenL
              have hCaseR :
                  0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (caseₜ L [zero⇒ M |suc⇒ N])) ⦂ substT ρ.right A := by
                simpa [subst, substTT] using HasType.t_case hL' hM' hNopenR
              have leftZeroRed :
                  substTT ρ.left (subst γ.left (caseₜ L [zero⇒ M |suc⇒ N])) —↠ VM := by
                exact multi_trans
                  (by
                    simpa [subst, substTT] using
                      (case_multi
                        (M := substTT ρ.left (subst γ.left M))
                        (N := substTT ρ.left (subst (exts γ.left) N))
                        lSteps))
                  (multi_trans
                    (by
                      simpa using
                        (case_zero_multi
                          (M := substTT ρ.left (subst γ.left M))
                          (N := substTT ρ.left (subst (exts γ.left) N))))
                    mSteps)
              have rightZeroRed :
                  substTT ρ.right (subst γ.right (caseₜ L [zero⇒ M |suc⇒ N])) —↠ WM := by
                exact multi_trans
                  (by
                    simpa [subst, substTT] using
                      (case_multi
                        (M := substTT ρ.right (subst γ.right M))
                        (N := substTT ρ.right (subst (exts γ.right) N))
                        rSteps))
                  (multi_trans
                    (by
                      simpa using
                        (case_zero_multi
                          (M := substTT ρ.right (subst γ.right M))
                          (N := substTT ρ.right (subst (exts γ.right) N))))
                    mStepsR)
              unfold 𝓔
              exact ⟨hCaseL, hCaseR, VM, WM, vM, wM, ⟨leftZeroRed⟩, ⟨rightZeroRed⟩, hMval⟩
          | _ =>
              simp [𝒱, 𝒱nat] at hNat
      | @vSuc V v =>
          cases wL with
          | @vSuc W w =>
              simp [𝒱, 𝒱nat] at hNat
              have hVW : 𝒱 ℕ ρ V W v w := by
                simpa [𝒱, 𝒱nat] using hNat
              have hNrel :
                  𝓔 A ρ
                    (substTT ρ.left (subst (V • γ.left) N))
                    (substTT ρ.right (subst (W • γ.right) N)) :=
                Nrel ρ (extendRelEnv γ V W)
                  (extendRelEnv_related (Γ := Γ) (A := ℕ) (ρ := ρ) (γ := γ)
                    (V := V) (W := W) env v w hVW)
              simp only [𝓔] at hNrel
              rcases hNrel with ⟨hNL, hNR, VN, WN, vN, wN, nSteps, nStepsR, hNval⟩
              rcases nSteps with ⟨nSteps⟩
              rcases nStepsR with ⟨nStepsR⟩
              have hCaseL :
                  0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (caseₜ L [zero⇒ M |suc⇒ N])) ⦂ substT ρ.left A := by
                simpa [subst, substTT] using HasType.t_case hL hMtypedL hNopenL
              have hCaseR :
                  0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (caseₜ L [zero⇒ M |suc⇒ N])) ⦂ substT ρ.right A := by
                simpa [subst, substTT] using HasType.t_case hL' hMtypedR hNopenR
              have hVtyped : 0 ⊢ [] ⊢ V ⦂ substT ρ.left ℕ :=
                Classical.choice (𝒱_typing (A := ℕ) (ρ := ρ) (V := V) (W := W) (v := v) (w := w) hVW).1
              have hWtyped : 0 ⊢ [] ⊢ W ⦂ substT ρ.right ℕ :=
                Classical.choice (𝒱_typing (A := ℕ) (ρ := ρ) (V := V) (W := W) (v := v) (w := w) hVW).2
              have leftVId : substTT ρ.left V = V :=
                substTT_id_typed (hM := hVtyped) (hσ := by
                  intro α hα
                  exact False.elim (Nat.not_lt_zero α hα))
              have rightWId : substTT ρ.right W = W :=
                substTT_id_typed (hM := hWtyped) (hσ := by
                  intro α hα
                  exact False.elim (Nat.not_lt_zero α hα))
              have leftSucBridge :
                  singleSubst (substTT ρ.left (subst (exts γ.left) N)) V =
                    substTT ρ.left (subst (V • γ.left) N) := by
                calc
                  singleSubst (substTT ρ.left (subst (exts γ.left) N)) V
                      = subst (singleEnv V) (substTT ρ.left (subst (exts γ.left) N)) := by
                            rfl
                  _ = subst (fun i => substTT ρ.left (singleEnv V i))
                        (substTT ρ.left (subst (exts γ.left) N)) := by
                        apply subst_cong_tm
                        intro i
                        cases i with
                        | zero =>
                            simpa using leftVId.symm
                        | succ j =>
                            rfl
                  _ = substTT ρ.left (subst (singleEnv V) (subst (exts γ.left) N)) := by
                        exact subst_substTT_commute (singleEnv V) ρ.left (subst (exts γ.left) N)
                  _ = substTT ρ.left (subst (V • γ.left) N) := by
                        simpa [singleSubst] using congrArg (substTT ρ.left) (exts_sub_cons_tm γ.left N V)
              have rightSucBridge :
                  singleSubst (substTT ρ.right (subst (exts γ.right) N)) W =
                    substTT ρ.right (subst (W • γ.right) N) := by
                calc
                  singleSubst (substTT ρ.right (subst (exts γ.right) N)) W
                      = subst (singleEnv W) (substTT ρ.right (subst (exts γ.right) N)) := by
                            rfl
                  _ = subst (fun i => substTT ρ.right (singleEnv W i))
                        (substTT ρ.right (subst (exts γ.right) N)) := by
                        apply subst_cong_tm
                        intro i
                        cases i with
                        | zero =>
                            simpa using rightWId.symm
                        | succ j =>
                            rfl
                  _ = substTT ρ.right (subst (singleEnv W) (subst (exts γ.right) N)) := by
                        exact subst_substTT_commute (singleEnv W) ρ.right (subst (exts γ.right) N)
                  _ = substTT ρ.right (subst (W • γ.right) N) := by
                        simpa [singleSubst] using congrArg (substTT ρ.right) (exts_sub_cons_tm γ.right N W)
              have leftCaseSucBase :
                  substTT ρ.left (subst γ.left (caseₜ L [zero⇒ M |suc⇒ N])) —↠
                    singleSubst (substTT ρ.left (subst (exts γ.left) N)) V := by
                exact multi_trans
                  (by
                    simpa [subst, substTT] using
                      (case_multi
                        (M := substTT ρ.left (subst γ.left M))
                        (N := substTT ρ.left (subst (exts γ.left) N))
                        lSteps))
                  (by
                    exact .step _ (.beta_suc v)
                      (.refl _))
              have rightCaseSucBase :
                  substTT ρ.right (subst γ.right (caseₜ L [zero⇒ M |suc⇒ N])) —↠
                    singleSubst (substTT ρ.right (subst (exts γ.right) N)) W := by
                exact multi_trans
                  (by
                    simpa [subst, substTT] using
                      (case_multi
                        (M := substTT ρ.right (subst γ.right M))
                        (N := substTT ρ.right (subst (exts γ.right) N))
                        rSteps))
                  (by
                    exact .step _ (.beta_suc w)
                      (.refl _))
              have leftSucRed :
                  substTT ρ.left (subst γ.left (caseₜ L [zero⇒ M |suc⇒ N])) —↠ VN := by
                exact multi_trans leftCaseSucBase
                  (Eq.ndrec
                    (motive := fun T => T —↠ VN)
                    nSteps
                    leftSucBridge.symm)
              have rightSucRed :
                  substTT ρ.right (subst γ.right (caseₜ L [zero⇒ M |suc⇒ N])) —↠ WN := by
                exact multi_trans rightCaseSucBase
                  (Eq.ndrec
                    (motive := fun T => T —↠ WN)
                    nStepsR
                    rightSucBridge.symm)
              unfold 𝓔
              exact ⟨hCaseL, hCaseR, VN, WN, vN, wN, ⟨leftSucRed⟩, ⟨rightSucRed⟩, hNval⟩
          | _ =>
              simp [𝒱, 𝒱nat] at hNat
      | vLam =>
          cases wL <;> simp [𝒱, 𝒱nat] at hNat
      | vTrue =>
          cases wL <;> simp [𝒱, 𝒱nat] at hNat
      | vFalse =>
          cases wL <;> simp [𝒱, 𝒱nat] at hNat
      | vTlam =>
          cases wL <;> simp [𝒱, 𝒱nat] at hNat

theorem compat_zero :
  ∀ {Γ}, Γ ⊨ ˋzero ≈ ˋzero ⦂ ℕ
  | Γ => by
      intro ρ γ env
      exact 𝒱_to_𝓔 (A := ℕ) (ρ := ρ) (V := ˋzero) (W := ˋzero)
        .vZero .vZero (by simpa [𝒱, 𝒱nat])

theorem compat_lam :
  ∀ {Δ Γ A B} (N : Term),
    Δ ⊢ (A :: Γ) ⊢ N ⦂ B →
    (A :: Γ) ⊨ N ≈ N ⦂ B →
    Γ ⊨ (ƛ[ A ] N) ≈ (ƛ[ A ] N) ⦂ (A ⇒ B)
  | Δ, Γ, A, B, N, hN, Nrel => by
      intro ρ γ env
      have hTySubL : TySubstWf Δ 0 ρ.left := by
        intro X hX
        exact ρ.leftClosed X
      have hTySubR : TySubstWf Δ 0 ρ.right := by
        intro X hX
        exact ρ.rightClosed X
      have hSubExtL :
          SubstWf 0 (List.map (substT ρ.left) (A :: Γ)) [substT ρ.left A] (exts γ.left) := by
        intro x C hx
        cases hx with
        | Z =>
            simpa [exts] using
              (HasType.t_var (Δ := 0) (Γ := [substT ρ.left A]) (i := 0)
                (A := substT ρ.left A) HasTypeVar.Z)
        | S hx' =>
            simpa [exts] using
              typing_rename_shift (B := substT ρ.left A)
                (𝒢_left_SubstWf (Γ := Γ) (ρ := ρ) (γ := γ) env hx')
      have hSubExtR :
          SubstWf 0 (List.map (substT ρ.right) (A :: Γ)) [substT ρ.right A] (exts γ.right) := by
        intro x C hx
        cases hx with
        | Z =>
            simpa [exts] using
              (HasType.t_var (Δ := 0) (Γ := [substT ρ.right A]) (i := 0)
                (A := substT ρ.right A) HasTypeVar.Z)
        | S hx' =>
            simpa [exts] using
              typing_rename_shift (B := substT ρ.right A)
                (𝒢_right_SubstWf (Γ := Γ) (ρ := ρ) (γ := γ) env hx')
      have hNsubL :
          0 ⊢ [substT ρ.left A] ⊢ substTT ρ.left (subst (exts γ.left) N) ⦂ substT ρ.left B := by
        have hSubExtLTT :
            SubstWf 0 (List.map (substT ρ.left) (A :: Γ)) [substT ρ.left A]
              (fun i => substTT ρ.left (exts γ.left i)) := by
          intro x C hx
          have hTyped : 0 ⊢ [substT ρ.left A] ⊢ exts γ.left x ⦂ C := hSubExtL hx
          have hId : substTT ρ.left (exts γ.left x) = exts γ.left x := by
            exact substTT_id_typed (hM := hTyped) (hσ := by
              intro α hα
              exact False.elim (Nat.not_lt_zero α hα))
          exact Eq.ndrec
            (motive := fun T => 0 ⊢ [substT ρ.left A] ⊢ T ⦂ C)
            hTyped
            hId.symm
        have hRaw :
            0 ⊢ [substT ρ.left A] ⊢
              subst (fun i => substTT ρ.left (exts γ.left i)) (substTT ρ.left N) ⦂ substT ρ.left B := by
          exact typing_subst hSubExtLTT (typing_substTT (σ := ρ.left) hTySubL hN)
        exact Eq.ndrec
          (motive := fun T => 0 ⊢ [substT ρ.left A] ⊢ T ⦂ substT ρ.left B)
          hRaw
          (subst_substTT_commute (exts γ.left) ρ.left N)
      have hNsubR :
          0 ⊢ [substT ρ.right A] ⊢ substTT ρ.right (subst (exts γ.right) N) ⦂ substT ρ.right B := by
        have hSubExtRTT :
            SubstWf 0 (List.map (substT ρ.right) (A :: Γ)) [substT ρ.right A]
              (fun i => substTT ρ.right (exts γ.right i)) := by
          intro x C hx
          have hTyped : 0 ⊢ [substT ρ.right A] ⊢ exts γ.right x ⦂ C := hSubExtR hx
          have hId : substTT ρ.right (exts γ.right x) = exts γ.right x := by
            exact substTT_id_typed (hM := hTyped) (hσ := by
              intro α hα
              exact False.elim (Nat.not_lt_zero α hα))
          exact Eq.ndrec
            (motive := fun T => 0 ⊢ [substT ρ.right A] ⊢ T ⦂ C)
            hTyped
            hId.symm
        have hRaw :
            0 ⊢ [substT ρ.right A] ⊢
              subst (fun i => substTT ρ.right (exts γ.right i)) (substTT ρ.right N) ⦂ substT ρ.right B := by
          exact typing_subst hSubExtRTT (typing_substTT (σ := ρ.right) hTySubR hN)
        exact Eq.ndrec
          (motive := fun T => 0 ⊢ [substT ρ.right A] ⊢ T ⦂ substT ρ.right B)
          hRaw
          (subst_substTT_commute (exts γ.right) ρ.right N)
      have hLamL :
          0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (ƛ[ A ] N)) ⦂ substT ρ.left (A ⇒ B) := by
        simpa [subst, substTT] using
          (HasType.t_lam (substT_codom_closed ρ.left ρ.leftClosed A) hNsubL)
      have hLamR :
          0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (ƛ[ A ] N)) ⦂ substT ρ.right (A ⇒ B) := by
        simpa [subst, substTT] using
          (HasType.t_lam (substT_codom_closed ρ.right ρ.rightClosed A) hNsubR)
      have hFun :
          𝒱 (A ⇒ B) ρ
            (substTT ρ.left (subst γ.left (ƛ[ A ] N)))
            (substTT ρ.right (subst γ.right (ƛ[ A ] N)))
            .vLam .vLam := by
        have hFunCore :
            ∃ (hVL : 0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (ƛ[ A ] N)) ⦂ substT ρ.left (A ⇒ B)),
              ∃ (hVR : 0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (ƛ[ A ] N)) ⦂ substT ρ.right (A ⇒ B)),
                ∀ {V W} (v : Value V) (w : Value W),
                  𝒱 A ρ V W v w →
                  𝓔 B ρ
                    (singleSubst (substTT ρ.left (subst (exts γ.left) N)) V)
                    (singleSubst (substTT ρ.right (subst (exts γ.right) N)) W) := by
          refine ⟨hLamL, hLamR, ?_⟩
          intro V W v w hVW
          have hNrel := Nrel ρ (extendRelEnv γ V W)
            (extendRelEnv_related (Γ := Γ) (A := A) (ρ := ρ) (γ := γ)
              (V := V) (W := W) env v w hVW)
          have leftBetaBridge :
              singleSubst (substTT ρ.left (subst (exts γ.left) N)) V =
                substTT ρ.left (subst (V • γ.left) N) := by
            calc
              singleSubst (substTT ρ.left (subst (exts γ.left) N)) V
                  = subst (singleEnv V) (substTT ρ.left (subst (exts γ.left) N)) := by
                        rfl
              _ = subst (fun i => substTT ρ.left (singleEnv V i))
                    (substTT ρ.left (subst (exts γ.left) N)) := by
                    apply subst_cong_tm
                    intro i
                    cases i with
                    | zero =>
                        have hVtyped : 0 ⊢ [] ⊢ V ⦂ substT ρ.left A :=
                          Classical.choice (𝒱_typing (A := A) (ρ := ρ) (V := V) (W := W) (v := v) (w := w) hVW).1
                        simpa using (substTT_id_typed (hM := hVtyped) (hσ := by
                          intro α hα
                          exact False.elim (Nat.not_lt_zero α hα))).symm
                    | succ j =>
                        rfl
              _ = substTT ρ.left (subst (singleEnv V) (subst (exts γ.left) N)) := by
                    exact subst_substTT_commute (singleEnv V) ρ.left (subst (exts γ.left) N)
              _ = substTT ρ.left (subst (V • γ.left) N) := by
                    simpa [singleSubst] using congrArg (substTT ρ.left) (exts_sub_cons_tm γ.left N V)
          have rightBetaBridge :
              singleSubst (substTT ρ.right (subst (exts γ.right) N)) W =
                substTT ρ.right (subst (W • γ.right) N) := by
            calc
              singleSubst (substTT ρ.right (subst (exts γ.right) N)) W
                  = subst (singleEnv W) (substTT ρ.right (subst (exts γ.right) N)) := by
                        rfl
              _ = subst (fun i => substTT ρ.right (singleEnv W i))
                    (substTT ρ.right (subst (exts γ.right) N)) := by
                    apply subst_cong_tm
                    intro i
                    cases i with
                    | zero =>
                        have hWtyped : 0 ⊢ [] ⊢ W ⦂ substT ρ.right A :=
                          Classical.choice (𝒱_typing (A := A) (ρ := ρ) (V := V) (W := W) (v := v) (w := w) hVW).2
                        simpa using (substTT_id_typed (hM := hWtyped) (hσ := by
                          intro α hα
                          exact False.elim (Nat.not_lt_zero α hα))).symm
                    | succ j =>
                        rfl
              _ = substTT ρ.right (subst (singleEnv W) (subst (exts γ.right) N)) := by
                    exact subst_substTT_commute (singleEnv W) ρ.right (subst (exts γ.right) N)
              _ = substTT ρ.right (subst (W • γ.right) N) := by
                    simpa [singleSubst] using congrArg (substTT ρ.right) (exts_sub_cons_tm γ.right N W)
          simpa [extendRelEnv, leftBetaBridge, rightBetaBridge] using hNrel
        simpa [𝒱, subst, substTT] using hFunCore
      unfold 𝓔
      exact ⟨hLamL, hLamR,
        substTT ρ.left (subst γ.left (ƛ[ A ] N)),
        substTT ρ.right (subst γ.right (ƛ[ A ] N)),
        .vLam, .vLam,
        ⟨.refl _⟩, ⟨.refl _⟩, hFun⟩

theorem compat_false :
  ∀ {Γ}, Γ ⊨ ˋfalse ≈ ˋfalse ⦂ 𝔹
  | Γ => by
      intro ρ γ env
      exact 𝒱_to_𝓔 (A := 𝔹) (ρ := ρ) (V := ˋfalse) (W := ˋfalse)
        .vFalse .vFalse (by simpa [𝒱, 𝒱bool])

theorem compat_if :
  ∀ {Γ A} (L M N : Term),
    Γ ⊨ L ≈ L ⦂ 𝔹 →
    Γ ⊨ M ≈ M ⦂ A →
    Γ ⊨ N ≈ N ⦂ A →
    Γ ⊨ (ˋif L then M else N) ≈ (ˋif L then M else N) ⦂ A
  | Γ, A, L, M, N, Lrel, Mrel, Nrel => by
      intro ρ γ env
      have hLrel := Lrel ρ γ env
      have hMrel := Mrel ρ γ env
      have hNrel := Nrel ρ γ env
      simp only [𝓔] at hLrel hMrel hNrel
      rcases hLrel with ⟨hL, hL', VL, WL, v, w, lSteps, rSteps, hBool⟩
      rcases hMrel with ⟨hM, hM', VM, WM, vM, wM, mSteps, mStepsR, hMrel⟩
      rcases hNrel with ⟨hN, hN', VN, WN, vN, wN, nSteps, nStepsR, hNrel⟩
      rcases lSteps with ⟨lSteps⟩
      rcases rSteps with ⟨rSteps⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      rcases nSteps with ⟨nSteps⟩
      rcases nStepsR with ⟨nStepsR⟩
      have hIfL :
          0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (ˋif L then M else N)) ⦂ substT ρ.left A := by
        simpa [subst, substTT] using HasType.t_if hL hM hN
      have hIfR :
          0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (ˋif L then M else N)) ⦂ substT ρ.right A := by
        simpa [subst, substTT] using HasType.t_if hL' hM' hN'
      cases v <;> cases w <;> simp [𝒱, 𝒱bool] at hBool
      case vTrue.vTrue =>
        have hIfTrueL :
            substTT ρ.left (subst γ.left (ˋif L then M else N)) —↠
              substTT ρ.left (subst γ.left M) := by
          simpa [subst, substTT] using
            (if_true_multi
              (M := substTT ρ.left (subst γ.left M))
              (N := substTT ρ.left (subst γ.left N))
              lSteps)
        have hIfTrueR :
            substTT ρ.right (subst γ.right (ˋif L then M else N)) —↠
              substTT ρ.right (subst γ.right M) := by
          simpa [subst, substTT] using
            (if_true_multi
              (M := substTT ρ.right (subst γ.right M))
              (N := substTT ρ.right (subst γ.right N))
              rSteps)
        unfold 𝓔
        exact ⟨hIfL, hIfR, VM, WM, vM, wM,
          ⟨multi_trans hIfTrueL mSteps⟩,
          ⟨multi_trans hIfTrueR mStepsR⟩,
          hMrel⟩
      case vFalse.vFalse =>
        have hIfFalseL :
            substTT ρ.left (subst γ.left (ˋif L then M else N)) —↠
              substTT ρ.left (subst γ.left N) := by
          simpa [subst, substTT] using
            (if_false_multi
              (M := substTT ρ.left (subst γ.left M))
              (N := substTT ρ.left (subst γ.left N))
              lSteps)
        have hIfFalseR :
            substTT ρ.right (subst γ.right (ˋif L then M else N)) —↠
              substTT ρ.right (subst γ.right N) := by
          simpa [subst, substTT] using
            (if_false_multi
              (M := substTT ρ.right (subst γ.right M))
              (N := substTT ρ.right (subst γ.right N))
              rSteps)
        unfold 𝓔
        exact ⟨hIfL, hIfR, VN, WN, vN, wN,
          ⟨multi_trans hIfFalseL nSteps⟩,
          ⟨multi_trans hIfFalseR nStepsR⟩,
          hNrel⟩

theorem compat_var :
  ∀ {Γ A x},
    HasTypeVar Γ x A →
    Γ ⊨ (ˋx) ≈ (ˋx) ⦂ A
  | _, _, _, .Z => by
      intro ρ γ env
      have hHead := env.1
      have hIdL :
          substTT ρ.left (γ.left 0) = γ.left 0 := by
        exact substTT_id_typed
          (Classical.choice ((𝓔_typing (A := _) (ρ := ρ) (M := γ.left 0) (N := γ.right 0) hHead).1))
          (fun α h => (Nat.not_lt_zero _ h).elim)
      have hIdR :
          substTT ρ.right (γ.right 0) = γ.right 0 := by
        exact substTT_id_typed
          (Classical.choice ((𝓔_typing (A := _) (ρ := ρ) (M := γ.left 0) (N := γ.right 0) hHead).2))
          (fun α h => (Nat.not_lt_zero _ h).elim)
      simpa [subst, hIdL, hIdR] using hHead
  | _, _, _, .S hx => by
      intro ρ γ env
      simpa [subst, tailRelEnv] using
        (compat_var hx ρ (tailRelEnv γ) env.2)

theorem compat_tapp :
  ∀ {Γ A B} (M : Term),
    LogicalRel Γ (∀ₜ A) M M →
    LogicalRel Γ (A [ B ]ₜ) (Term.tapp M B) (Term.tapp M B)
  | Γ, A, B, M, Mrel => by
      intro ρ γ env
      have hMrel := Mrel ρ γ env
      simp only [𝓔] at hMrel
      rcases hMrel with ⟨hM, hM', V, W, v, w, mSteps, mStepsR, hAll⟩
      rcases mSteps with ⟨mSteps⟩
      rcases mStepsR with ⟨mStepsR⟩
      cases v <;> cases w <;> simp [𝒱] at hAll
      case vTlam.vTlam =>
        rename_i N N_1
        rcases hAll with ⟨_, _, hAll⟩
        have hA1 : WfTy 0 (substT ρ.left B) :=
          substT_codom_closed ρ.left ρ.leftClosed B
        have hA2 : WfTy 0 (substT ρ.right B) :=
          substT_codom_closed ρ.right ρ.rightClosed B
        have relInst :
            𝓔 A
              (extendRelSub ρ
                (substT ρ.left B)
                (substT ρ.right B)
                (substT_codom_closed ρ.left ρ.leftClosed B)
                (substT_codom_closed ρ.right ρ.rightClosed B)
                (fun V W v w hV hW => 𝒱 B ρ V W v w))
              (substOneTT N (substT ρ.left B))
              (substOneTT N_1 (substT ρ.right B)) :=
          hAll
            (substT ρ.left B)
            (substT ρ.right B)
            (substT_codom_closed ρ.left ρ.leftClosed B)
            (substT_codom_closed ρ.right ρ.rightClosed B)
            (fun V W v w hV hW => 𝒱 B ρ V W v w)
        have hComp :
            𝓔 (A [ B ]ₜ) ρ
              (substOneTT N (substT ρ.left B))
              (substOneTT N_1 (substT ρ.right B)) :=
          𝓔_compositionality_to (A := A) (B := B) (ρ := ρ) relInst
        simp only [𝓔] at hComp
        rcases hComp with ⟨hNL, hNR, VB, WB, vb, wb, nStepsL, nStepsR, hVB⟩
        rcases nStepsL with ⟨nStepsL⟩
        rcases nStepsR with ⟨nStepsR⟩
        have hTapL :
            0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (Term.tapp M B)) ⦂ substT ρ.left (A [ B ]ₜ) := by
          have hTap0 :
              0 ⊢ [] ⊢ Term.tapp (substTT ρ.left (subst γ.left M)) (substT ρ.left B)
                ⦂ substOneT (substT (extsT ρ.left) A) (substT ρ.left B) :=
            HasType.t_tapp hM hA1
          have hTap1 :
              0 ⊢ [] ⊢ Term.tapp (substTT ρ.left (subst γ.left M)) (substT ρ.left B)
                ⦂ substT ρ.left (A [ B ]ₜ) := by
            exact Eq.ndrec
              (motive := fun T =>
                0 ⊢ [] ⊢ Term.tapp (substTT ρ.left (subst γ.left M)) (substT ρ.left B) ⦂ T)
              hTap0
              (subst_substOne_commute ρ.left A B).symm
          simpa [subst, substTT] using hTap1
        have hTapR :
            0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (Term.tapp M B)) ⦂ substT ρ.right (A [ B ]ₜ) := by
          have hTap0 :
              0 ⊢ [] ⊢ Term.tapp (substTT ρ.right (subst γ.right M)) (substT ρ.right B)
                ⦂ substOneT (substT (extsT ρ.right) A) (substT ρ.right B) :=
            HasType.t_tapp hM' hA2
          have hTap1 :
              0 ⊢ [] ⊢ Term.tapp (substTT ρ.right (subst γ.right M)) (substT ρ.right B)
                ⦂ substT ρ.right (A [ B ]ₜ) := by
            exact Eq.ndrec
              (motive := fun T =>
                0 ⊢ [] ⊢ Term.tapp (substTT ρ.right (subst γ.right M)) (substT ρ.right B) ⦂ T)
              hTap0
              (subst_substOne_commute ρ.right A B).symm
          simpa [subst, substTT] using hTap1
        unfold 𝓔
        exact ⟨hTapL, hTapR, VB, WB, vb, wb,
          ⟨multi_trans
            (by simpa [subst, substTT] using tapp_multi (A := substT ρ.left B) mSteps)
            (multi_trans
              (by simpa using (beta_tlam_multi (N := N) (A := substT ρ.left B)))
              nStepsL)⟩,
          ⟨multi_trans
            (by simpa [subst, substTT] using tapp_multi (A := substT ρ.right B) mStepsR)
            (multi_trans
              (by simpa using (beta_tlam_multi (N := N_1) (A := substT ρ.right B)))
              nStepsR)⟩,
          hVB⟩

theorem tlam_left_inst :
  ∀ {Δ Γ A} {ρ : RelSub} {γ : RelEnv} {N : Term}
    (hN : (Δ + 1) ⊢ (liftCtx Γ) ⊢ N ⦂ A)
    (env : 𝒢 Γ ρ γ)
    {A1 A2 : Ty} {hA1 : WfTy 0 A1} {hA2 : WfTy 0 A2} {R : Rel A1 A2},
    substOneTT (substTT (extsT ρ.left) (subst (up γ.left) N)) A1 =
      substTT (extendRelSub ρ A1 A2 hA1 hA2 R).left (subst γ.left N)
  | Δ, Γ, A, ρ, γ, N, hN, env, A1, A2, hA1, hA2, R => by
      let ρl : SubstT := (extendRelSub ρ A1 A2 hA1 hA2 R).left
      have hTySubL : TySubstWf (Δ + 1) 0 ρl := by
        intro X hX
        cases X with
        | zero =>
            simpa [ρl, extendRelSub] using hA1
        | succ X =>
            simpa [ρl, extendRelSub] using ρ.leftClosed X
      have hNtyped :
          0 ⊢ (List.map (substT ρl) (liftCtx Γ)) ⊢ substTT ρl N ⦂ substT ρl A :=
        typing_substTT (Δ := Δ + 1) (Δ' := 0) (Γ := liftCtx Γ) (σ := ρl) hTySubL hN
      have left_var_close :
          ∀ {x C}, HasTypeVar Γ x C →
            substTT ρl (up γ.left x) = substTT ρl (γ.left x) := by
        intro x C hx
        have hγx : 0 ⊢ [] ⊢ γ.left x ⦂ substT ρ.left C :=
          𝒢_left_SubstWf (Γ := Γ) (ρ := ρ) (γ := γ) env
            (lookup_map_substT (σ := ρ.left) hx)
        have hIdρ : substTT ρ.left (γ.left x) = γ.left x :=
          substTT_id_typed (hM := hγx) (hσ := by
            intro α hα
            exact False.elim (Nat.not_lt_zero α hα))
        have hIdρl : substTT ρl (γ.left x) = γ.left x :=
          substTT_id_typed (hM := hγx) (hσ := by
            intro α hα
            exact False.elim (Nat.not_lt_zero α hα))
        calc
          substTT ρl (up γ.left x)
              = substTT ρl (renameTT Nat.succ (γ.left x)) := rfl
          _ = substTT (fun i => ρl (Nat.succ i)) (γ.left x) := by
                exact substTT_renameTT_commute Nat.succ ρl (γ.left x)
          _ = substTT ρ.left (γ.left x) := by
                apply substTT_cong
                intro i
                rfl
          _ = γ.left x := hIdρ
          _ = substTT ρl (γ.left x) := by
                symm
                exact hIdρl
      have left_pointwise :
          ∀ {x B}, HasTypeVar (List.map (substT ρl) (liftCtx Γ)) x B →
            substTT ρl (up γ.left x) = substTT ρl (γ.left x) := by
        intro x B hx
        rcases lookup_map_inv (Γ := liftCtx Γ) (x := x) (B := B) (f := substT ρl) hx with
          ⟨B', ⟨hB', hEqB'⟩⟩
        rcases lookup_map_inv (Γ := Γ) (x := x) (B := B') (f := renameT Nat.succ) hB' with
          ⟨C, ⟨hC, hEqC⟩⟩
        exact left_var_close hC
      have left_map :
          ∀ i, substT (singleTyEnv A1) (extsT ρ.left i) = ρl i := by
        intro i
        cases i with
        | zero =>
            rfl
        | succ j =>
            simpa [ρl, extendRelSub] using substT_renameT_cancel (C := ρ.left j) (B := A1)
      calc
        substOneTT (substTT (extsT ρ.left) (subst (up γ.left) N)) A1
            = substTT (singleTyEnv A1) (substTT (extsT ρ.left) (subst (up γ.left) N)) := rfl
        _ = substTT ((extsT ρ.left) ⨟ᵗ (singleTyEnv A1)) (subst (up γ.left) N) := by
              exact substTT_substTT (singleTyEnv A1) (extsT ρ.left) (subst (up γ.left) N)
        _ = substTT ρl (subst (up γ.left) N) := by
              apply substTT_cong
              exact left_map
        _ = subst (fun i => substTT ρl (up γ.left i)) (substTT ρl N) := by
              symm
              exact subst_substTT_commute (up γ.left) ρl N
        _ = subst (fun i => substTT ρl (γ.left i)) (substTT ρl N) := by
              exact subst_cong_typed hNtyped (by
                intro x C hx
                exact left_pointwise hx)
        _ = substTT ρl (subst γ.left N) := by
              exact subst_substTT_commute γ.left ρl N
        _ = substTT (extendRelSub ρ A1 A2 hA1 hA2 R).left (subst γ.left N) := rfl

theorem tlam_right_inst :
  ∀ {Δ Γ A} {ρ : RelSub} {γ : RelEnv} {N : Term}
    (hN : (Δ + 1) ⊢ (liftCtx Γ) ⊢ N ⦂ A)
    (env : 𝒢 Γ ρ γ)
    {A1 A2 : Ty} {hA1 : WfTy 0 A1} {hA2 : WfTy 0 A2} {R : Rel A1 A2},
    substOneTT (substTT (extsT ρ.right) (subst (up γ.right) N)) A2 =
      substTT (extendRelSub ρ A1 A2 hA1 hA2 R).right (subst γ.right N)
  | Δ, Γ, A, ρ, γ, N, hN, env, A1, A2, hA1, hA2, R => by
      let ρr : SubstT := (extendRelSub ρ A1 A2 hA1 hA2 R).right
      have hTySubR : TySubstWf (Δ + 1) 0 ρr := by
        intro X hX
        cases X with
        | zero =>
            simpa [ρr, extendRelSub] using hA2
        | succ X =>
            simpa [ρr, extendRelSub] using ρ.rightClosed X
      have hNtyped :
          0 ⊢ (List.map (substT ρr) (liftCtx Γ)) ⊢ substTT ρr N ⦂ substT ρr A :=
        typing_substTT (Δ := Δ + 1) (Δ' := 0) (Γ := liftCtx Γ) (σ := ρr) hTySubR hN
      have right_var_close :
          ∀ {x C}, HasTypeVar Γ x C →
            substTT ρr (up γ.right x) = substTT ρr (γ.right x) := by
        intro x C hx
        have hγx : 0 ⊢ [] ⊢ γ.right x ⦂ substT ρ.right C :=
          𝒢_right_SubstWf (Γ := Γ) (ρ := ρ) (γ := γ) env
            (lookup_map_substT (σ := ρ.right) hx)
        have hIdρ : substTT ρ.right (γ.right x) = γ.right x :=
          substTT_id_typed (hM := hγx) (hσ := by
            intro α hα
            exact False.elim (Nat.not_lt_zero α hα))
        have hIdρr : substTT ρr (γ.right x) = γ.right x :=
          substTT_id_typed (hM := hγx) (hσ := by
            intro α hα
            exact False.elim (Nat.not_lt_zero α hα))
        calc
          substTT ρr (up γ.right x)
              = substTT ρr (renameTT Nat.succ (γ.right x)) := rfl
          _ = substTT (fun i => ρr (Nat.succ i)) (γ.right x) := by
                exact substTT_renameTT_commute Nat.succ ρr (γ.right x)
          _ = substTT ρ.right (γ.right x) := by
                apply substTT_cong
                intro i
                rfl
          _ = γ.right x := hIdρ
          _ = substTT ρr (γ.right x) := by
                symm
                exact hIdρr
      have right_pointwise :
          ∀ {x B}, HasTypeVar (List.map (substT ρr) (liftCtx Γ)) x B →
            substTT ρr (up γ.right x) = substTT ρr (γ.right x) := by
        intro x B hx
        rcases lookup_map_inv (Γ := liftCtx Γ) (x := x) (B := B) (f := substT ρr) hx with
          ⟨B', ⟨hB', hEqB'⟩⟩
        rcases lookup_map_inv (Γ := Γ) (x := x) (B := B') (f := renameT Nat.succ) hB' with
          ⟨C, ⟨hC, hEqC⟩⟩
        exact right_var_close hC
      have right_map :
          ∀ i, substT (singleTyEnv A2) (extsT ρ.right i) = ρr i := by
        intro i
        cases i with
        | zero =>
            rfl
        | succ j =>
            simpa [ρr, extendRelSub] using substT_renameT_cancel (C := ρ.right j) (B := A2)
      calc
        substOneTT (substTT (extsT ρ.right) (subst (up γ.right) N)) A2
            = substTT (singleTyEnv A2) (substTT (extsT ρ.right) (subst (up γ.right) N)) := rfl
        _ = substTT ((extsT ρ.right) ⨟ᵗ (singleTyEnv A2)) (subst (up γ.right) N) := by
              exact substTT_substTT (singleTyEnv A2) (extsT ρ.right) (subst (up γ.right) N)
        _ = substTT ρr (subst (up γ.right) N) := by
              apply substTT_cong
              exact right_map
        _ = subst (fun i => substTT ρr (up γ.right i)) (substTT ρr N) := by
              symm
              exact subst_substTT_commute (up γ.right) ρr N
        _ = subst (fun i => substTT ρr (γ.right i)) (substTT ρr N) := by
              exact subst_cong_typed hNtyped (by
                intro x C hx
                exact right_pointwise hx)
        _ = substTT ρr (subst γ.right N) := by
              exact subst_substTT_commute γ.right ρr N
        _ = substTT (extendRelSub ρ A1 A2 hA1 hA2 R).right (subst γ.right N) := rfl

theorem compat_tlam :
  ∀ {Δ Γ A} (N : Term),
    (Δ + 1) ⊢ (liftCtx Γ) ⊢ N ⦂ A →
    (liftCtx Γ) ⊨ N ≈ N ⦂ A →
    Γ ⊨ (Λ N) ≈ (Λ N) ⦂ (∀ₜ A)
  | Δ, Γ, A, N, hN, Nrel => by
      intro ρ γ env
      let leftBody : Term := substTT (extsT ρ.left) (subst (up γ.left) N)
      let rightBody : Term := substTT (extsT ρ.right) (subst (up γ.right) N)
      have hTySubL : TySubstWf Δ 0 ρ.left := by
        intro X Xlt
        exact ρ.leftClosed X
      have hTySubR : TySubstWf Δ 0 ρ.right := by
        intro X Xlt
        exact ρ.rightClosed X
      have hNttL :
          1 ⊢ (List.map (substT (extsT ρ.left)) (liftCtx Γ))
            ⊢ (substTT (extsT ρ.left) N) ⦂ (substT (extsT ρ.left) A) :=
        typing_substTT (Δ := Δ + 1) (Δ' := 1) (Γ := liftCtx Γ)
          (σ := extsT ρ.left) (tySubstWf_exts hTySubL) hN
      have hNttR :
          1 ⊢ (List.map (substT (extsT ρ.right)) (liftCtx Γ))
            ⊢ (substTT (extsT ρ.right) N) ⦂ (substT (extsT ρ.right) A) :=
        typing_substTT (Δ := Δ + 1) (Δ' := 1) (Γ := liftCtx Γ)
          (σ := extsT ρ.right) (tySubstWf_exts hTySubR) hN
      have hBaseSubL : SubstWf 0 (List.map (substT ρ.left) Γ) [] γ.left :=
        𝒢_left_SubstWf env
      have hBaseSubR : SubstWf 0 (List.map (substT ρ.right) Γ) [] γ.right :=
        𝒢_right_SubstWf env
      have hUpSubL0 : SubstWf 1 (liftCtx (List.map (substT ρ.left) Γ)) (liftCtx []) (up γ.left) :=
        substWf_up (Δ := 0) (Γ := List.map (substT ρ.left) Γ) (Γ' := []) (σ := γ.left) hBaseSubL
      have hUpSubR0 : SubstWf 1 (liftCtx (List.map (substT ρ.right) Γ)) (liftCtx []) (up γ.right) :=
        substWf_up (Δ := 0) (Γ := List.map (substT ρ.right) Γ) (Γ' := []) (σ := γ.right) hBaseSubR
      have hUpSubL :
          SubstWf 1 (List.map (substT (extsT ρ.left)) (liftCtx Γ)) [] (up γ.left) := by
        intro x C hx
        have hx' :
            HasTypeVar (liftCtx (List.map (substT ρ.left) Γ)) x C :=
          Eq.ndrec
            (motive := fun Ψ => HasTypeVar Ψ x C)
            hx
            (map_substT_lift ρ.left Γ)
        simpa [liftCtx] using hUpSubL0 hx'
      have hUpSubR :
          SubstWf 1 (List.map (substT (extsT ρ.right)) (liftCtx Γ)) [] (up γ.right) := by
        intro x C hx
        have hx' :
            HasTypeVar (liftCtx (List.map (substT ρ.right) Γ)) x C :=
          Eq.ndrec
            (motive := fun Ψ => HasTypeVar Ψ x C)
            hx
            (map_substT_lift ρ.right Γ)
        simpa [liftCtx] using hUpSubR0 hx'
      have hBodyL0 :
          1 ⊢ [] ⊢
            subst (fun i => substTT (extsT ρ.left) (up γ.left i)) (substTT (extsT ρ.left) N) ⦂
              substT (extsT ρ.left) A := by
        have hUpSubLTT :
            SubstWf 1 (List.map (substT (extsT ρ.left)) (liftCtx Γ)) []
              (fun i => substTT (extsT ρ.left) (up γ.left i)) := by
          intro x C hx
          have hTyped : 1 ⊢ [] ⊢ up γ.left x ⦂ C := hUpSubL hx
          have hId : substTT (extsT ρ.left) (up γ.left x) = up γ.left x := by
            exact substTT_id_typed (hM := hTyped) (hσ := by
              intro α hα
              cases α with
              | zero =>
                  rfl
              | succ β =>
                  exact False.elim (Nat.not_lt_zero β (Nat.lt_of_succ_lt_succ hα)))
          exact Eq.ndrec
            (motive := fun T => 1 ⊢ [] ⊢ T ⦂ C)
            hTyped
            hId.symm
        exact typing_subst hUpSubLTT hNttL
      have hBodyR0 :
          1 ⊢ [] ⊢
            subst (fun i => substTT (extsT ρ.right) (up γ.right i)) (substTT (extsT ρ.right) N) ⦂
              substT (extsT ρ.right) A := by
        have hUpSubRTT :
            SubstWf 1 (List.map (substT (extsT ρ.right)) (liftCtx Γ)) []
              (fun i => substTT (extsT ρ.right) (up γ.right i)) := by
          intro x C hx
          have hTyped : 1 ⊢ [] ⊢ up γ.right x ⦂ C := hUpSubR hx
          have hId : substTT (extsT ρ.right) (up γ.right x) = up γ.right x := by
            exact substTT_id_typed (hM := hTyped) (hσ := by
              intro α hα
              cases α with
              | zero =>
                  rfl
              | succ β =>
                  exact False.elim (Nat.not_lt_zero β (Nat.lt_of_succ_lt_succ hα)))
          exact Eq.ndrec
            (motive := fun T => 1 ⊢ [] ⊢ T ⦂ C)
            hTyped
            hId.symm
        exact typing_subst hUpSubRTT hNttR
      have hBodyL :
          1 ⊢ [] ⊢ leftBody ⦂ substT (extsT ρ.left) A := by
        exact Eq.ndrec
          (motive := fun T => 1 ⊢ [] ⊢ T ⦂ substT (extsT ρ.left) A)
          hBodyL0
          (subst_substTT_commute (up γ.left) (extsT ρ.left) N)
      have hBodyR :
          1 ⊢ [] ⊢ rightBody ⦂ substT (extsT ρ.right) A := by
        exact Eq.ndrec
          (motive := fun T => 1 ⊢ [] ⊢ T ⦂ substT (extsT ρ.right) A)
          hBodyR0
          (subst_substTT_commute (up γ.right) (extsT ρ.right) N)
      have hLamBodyL : 0 ⊢ [] ⊢ (Λ leftBody) ⦂ substT ρ.left (∀ₜ A) := by
        have h0 : 0 ⊢ [] ⊢ (Λ leftBody) ⦂ (∀ₜ (substT (extsT ρ.left) A)) :=
          HasType.t_tlam hBodyL
        simpa [substT] using h0
      have hLamBodyR : 0 ⊢ [] ⊢ (Λ rightBody) ⦂ substT ρ.right (∀ₜ A) := by
        have h0 : 0 ⊢ [] ⊢ (Λ rightBody) ⦂ (∀ₜ (substT (extsT ρ.right) A)) :=
          HasType.t_tlam hBodyR
        simpa [substT] using h0
      have hLamL :
          0 ⊢ [] ⊢ substTT ρ.left (subst γ.left (Λ N)) ⦂ substT ρ.left (∀ₜ A) := by
        simpa [leftBody, subst, substTT] using hLamBodyL
      have hLamR :
          0 ⊢ [] ⊢ substTT ρ.right (subst γ.right (Λ N)) ⦂ substT ρ.right (∀ₜ A) := by
        simpa [rightBody, subst, substTT] using hLamBodyR
      have hAllCore :
          ∃ (hVL : 0 ⊢ [] ⊢ (Λ leftBody) ⦂ substT ρ.left (∀ₜ A)),
            ∃ (hVR : 0 ⊢ [] ⊢ (Λ rightBody) ⦂ substT ρ.right (∀ₜ A)),
              ∀ (A1 A2 : Ty) (hA1 : WfTy 0 A1) (hA2 : WfTy 0 A2) (R : Rel A1 A2),
                𝓔 A (extendRelSub ρ A1 A2 hA1 hA2 R)
                  (substOneTT leftBody A1)
                  (substOneTT rightBody A2) := by
        refine ⟨hLamBodyL, hLamBodyR, ?_⟩
        intro A1 A2 hA1 hA2 R
        have hLift :
            𝒢 (liftCtx Γ) (extendRelSub ρ A1 A2 hA1 hA2 R) γ :=
          liftRelEnv_related (Γ := Γ) (A₁ := A1) (A₂ := A2) (ρ := ρ) (γ := γ)
            hA1 hA2 R env
        have hNinst :
            𝓔 A (extendRelSub ρ A1 A2 hA1 hA2 R)
              (substTT (extendRelSub ρ A1 A2 hA1 hA2 R).left (subst γ.left N))
              (substTT (extendRelSub ρ A1 A2 hA1 hA2 R).right (subst γ.right N)) :=
          Nrel (extendRelSub ρ A1 A2 hA1 hA2 R) γ hLift
        have leftInst :
            substOneTT leftBody A1 =
              substTT (extendRelSub ρ A1 A2 hA1 hA2 R).left (subst γ.left N) := by
          simpa [leftBody] using
            (tlam_left_inst (Δ := Δ) (Γ := Γ) (A := A) (ρ := ρ) (γ := γ) (N := N)
              hN env (A1 := A1) (A2 := A2)
              (hA1 := hA1) (hA2 := hA2) (R := R))
        have rightInst :
            substOneTT rightBody A2 =
              substTT (extendRelSub ρ A1 A2 hA1 hA2 R).right (subst γ.right N) := by
          simpa [rightBody] using
            (tlam_right_inst (Δ := Δ) (Γ := Γ) (A := A) (ρ := ρ) (γ := γ) (N := N)
              hN env (A1 := A1) (A2 := A2)
              (hA1 := hA1) (hA2 := hA2) (R := R))
        simpa [leftInst.symm, rightInst.symm] using hNinst
      have hAll :
          𝒱 (∀ₜ A) ρ
            (substTT ρ.left (subst γ.left (Λ N)))
            (substTT ρ.right (subst γ.right (Λ N)))
            .vTlam .vTlam := by
        simpa [𝒱, leftBody, rightBody, subst, substTT] using hAllCore
      unfold 𝓔
      exact ⟨hLamL, hLamR,
        substTT ρ.left (subst γ.left (Λ N)),
        substTT ρ.right (subst γ.right (Λ N)),
        .vTlam, .vTlam,
        ⟨.refl _⟩, ⟨.refl _⟩, hAll⟩

theorem fundamental :
  ∀ {Δ Γ A} (M : Term),
    Δ ⊢ Γ ⊢ M ⦂ A →
    Γ ⊨ M ≈ M ⦂ A
  | _, _, _, _, .t_var hx =>
      compat_var hx
  | _, _, _, _, .t_lam _ hN =>
      compat_lam (Δ := _) _ hN (fundamental _ hN)
  | _, _, _, _, .t_app hL hM =>
      compat_app _ _ (fundamental _ hL) (fundamental _ hM)
  | _, _, _, _, .t_true =>
      compat_true
  | _, _, _, _, .t_false =>
      compat_false
  | _, _, _, _, .t_zero =>
      compat_zero
  | _, _, _, _, .t_suc hM =>
      compat_suc _ (fundamental _ hM)
  | _, _, _, _, .t_case hL hM hN =>
      compat_case (Δ := _) _ _ _ hN (fundamental _ hL) (fundamental _ hM) (fundamental _ hN)
  | _, _, _, _, .t_if hL hM hN =>
      compat_if _ _ _ (fundamental _ hL) (fundamental _ hM) (fundamental _ hN)
  | _, _, _, _, .t_tlam hN =>
      compat_tlam (Δ := _) _ hN (fundamental _ hN)
  | _, _, _, _, .t_tapp hM _ =>
      compat_tapp _ (fundamental _ hM)

end

end Extrinsic

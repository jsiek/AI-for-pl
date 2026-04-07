import intrinsic.Reduction

namespace Intrinsic

set_option autoImplicit false

abbrev Rel {Ξ : TyCtx} (A B : Ty Ξ) : Type :=
  (V : Term Ξ ∅ᶜ A) → (W : Term Ξ ∅ᶜ B) → Value V → Value W → Prop

structure RelSub (Δ Ξ : TyCtx) where
  rho1 : SubstT Δ Ξ
  rho2 : SubstT Δ Ξ
  rhoR : ∀ α, Rel (rho1 α) (rho2 α)

def emptyRelSub : RelSub ∅ ∅ where
  rho1 := idSubstT
  rho2 := idSubstT
  rhoR := by
    intro α
    nomatch α

def extendRelSub {Δ Ξ : TyCtx} (ρ : RelSub Δ Ξ) (A₁ A₂ : Ty Ξ) (R : Rel A₁ A₂) :
    RelSub (Δ ,α) Ξ where
  rho1 := A₁ •ₜ ρ.rho1
  rho2 := A₂ •ₜ ρ.rho2
  rhoR := by
    intro α
    cases α with
    | Z => exact R
    | S β => exact ρ.rhoR β

def castTy {Ξ : TyCtx} {A B : Ty Ξ} (h : A = B) (M : Term Ξ ∅ᶜ A) :
    Term Ξ ∅ᶜ B := by
  cases h
  exact M

def castValue {Ξ : TyCtx} {A B : Ty Ξ} (h : A = B) {V : Term Ξ ∅ᶜ A}
    (v : Value V) : Value (castTy h V) := by
  cases h
  simpa using v

def castStepTy {Ξ : TyCtx} {A B : Ty Ξ} (h : A = B) {M N : Term Ξ ∅ᶜ A} :
    Step M N → Step (castTy h M) (castTy h N) := by
  intro s
  cases h
  simpa using s

noncomputable def castMultiTy {Ξ : TyCtx} {A B : Ty Ξ} (h : A = B) {M N : Term Ξ ∅ᶜ A} :
    M —↠ N → (castTy h M) —↠ (castTy h N) := by
  intro ms
  induction ms with
  | refl M =>
      exact MultiStep.refl _
  | step L s ms ih =>
      exact MultiStep.step _ (castStepTy h s) ih

theorem uipEq {A : Sort _} {x y : A} (p q : x = y) : p = q := by
  cases p
  cases q
  rfl

theorem castTy_trans
    {Ξ : TyCtx} {A B C : Ty Ξ} (h₁ : A = B) (h₂ : B = C)
    (M : Term Ξ ∅ᶜ A) :
    castTy h₂ (castTy h₁ M) = castTy (Eq.trans h₁ h₂) M := by
  cases h₁
  cases h₂
  rfl

@[simp] theorem castTy_rfl {Ξ : TyCtx} {A : Ty Ξ} (M : Term Ξ ∅ᶜ A) :
    castTy rfl M = M := rfl

@[simp] theorem castValue_rfl {Ξ : TyCtx} {A : Ty Ξ}
    {V : Term Ξ ∅ᶜ A} (v : Value V) :
    castValue rfl v = v := by
  rfl

theorem castTy_symm {Ξ : TyCtx} {A B : Ty Ξ} (h : A = B) (M : Term Ξ ∅ᶜ A) :
    castTy (Eq.symm h) (castTy h M) = M := by
  cases h
  rfl

theorem castTy_lam_exists
    {Ξ : TyCtx}
    {A₁ B₁ A₂ B₂ : Ty Ξ}
    {N : Term Ξ (∅ᶜ , A₁) B₁}
  (h : (Ty.fn A₁ B₁) = (Ty.fn A₂ B₂)) :
    ∃ (N' : Term Ξ (∅ᶜ , A₂) B₂),
      castTy h (Term.lam A₁ N) = Term.lam A₂ N' := by
  cases h
  exact Exists.intro N rfl

theorem castTy_tlam_exists
    {Ξ : TyCtx}
    {A₁ A₂ : Ty (Ξ ,α)}
    {N : Term (Ξ ,α) (liftCtx (∅ᶜ : Ctx Ξ)) A₁}
  (h : Ty.all A₁ = Ty.all A₂) :
    ∃ (N' : Term (Ξ ,α) (liftCtx (∅ᶜ : Ctx Ξ)) A₂),
      castTy h (Term.tlam N) = Term.tlam N' := by
  cases h
  exact Exists.intro N rfl

theorem castValue_lam_heq
    {Ξ : TyCtx}
    {A₁ B₁ A₂ B₂ : Ty Ξ}
    {N : Term Ξ (∅ᶜ , A₁) B₁}
    (h : Ty.fn A₁ B₁ = Ty.fn A₂ B₂) :
    ∃ (N' : Term Ξ (∅ᶜ , A₂) B₂),
      HEq (castValue h (v := (Value.vLam (N := N))))
        (Value.vLam (N := N')) := by
  cases h
  exact Exists.intro N HEq.rfl

theorem castValue_tlam_heq
    {Ξ : TyCtx}
    {A₁ A₂ : Ty (Ξ ,α)}
    {N : Term (Ξ ,α) (liftCtx (∅ᶜ : Ctx Ξ)) A₁}
    (h : Ty.all A₁ = Ty.all A₂) :
    ∃ (N' : Term (Ξ ,α) (liftCtx (∅ᶜ : Ctx Ξ)) A₂),
      HEq (castValue h (v := (Value.vTlam (N := N))))
        (Value.vTlam (N := N')) := by
  cases h
  exact Exists.intro N HEq.rfl

theorem castValue_lam_transport
    {Ξ : TyCtx}
    {A₁ B₁ A₂ B₂ : Ty Ξ}
    {N : Term Ξ (∅ᶜ , A₁) B₁}
    {N' : Term Ξ (∅ᶜ , A₂) B₂}
    (h : Ty.fn A₁ B₁ = Ty.fn A₂ B₂)
    (hN : castTy h (Term.lam A₁ N) = Term.lam A₂ N') :
    castValue h (v := (Value.vLam (N := N)))
      = Eq.ndrec (Value.vLam (N := N')) (Eq.symm hN) := by
  cases h
  cases hN
  rfl

theorem castValue_tlam_transport
    {Ξ : TyCtx}
    {A₁ A₂ : Ty (Ξ ,α)}
    {N : Term (Ξ ,α) (liftCtx (∅ᶜ : Ctx Ξ)) A₁}
    {N' : Term (Ξ ,α) (liftCtx (∅ᶜ : Ctx Ξ)) A₂}
    (h : Ty.all A₁ = Ty.all A₂)
    (hN : castTy h (Term.tlam N) = Term.tlam N') :
    castValue h (v := (Value.vTlam (N := N)))
      = Eq.ndrec (Value.vTlam (N := N')) (Eq.symm hN) := by
  cases h
  cases hN
  rfl

def VNatRel {Ξ : TyCtx} {V W : Term Ξ ∅ᶜ TNat} (v : Value V) (w : Value W) : Prop :=
  match v with
  | Value.vZero =>
      match w with
      | Value.vZero => True
      | _ => False
  | Value.vSuc v' =>
      match w with
      | Value.vSuc w' => VNatRel v' w'
      | _ => False
  | _ => False

def VBoolRel {Ξ : TyCtx} {V W : Term Ξ ∅ᶜ TBool} (v : Value V) (w : Value W) : Prop :=
  match v with
  | Value.vTrue =>
      match w with
      | Value.vTrue => True
      | _ => False
  | Value.vFalse =>
      match w with
      | Value.vFalse => True
      | _ => False
  | _ => False

theorem exts_single_comp {Δ Ξ : TyCtx} (σ : SubstT Δ Ξ) (B : Ty Ξ) :
    (fun x => substT (singleTyEnv B) (extsT σ x)) = (B •ₜ σ) := by
  funext x
  cases x with
  | Z =>
      rfl
  | S y =>
      calc
        substT (singleTyEnv B) (extsT σ (TyVar.S y))
            = substT (singleTyEnv B) (renameT TyVar.S (σ y)) := rfl
        _ = substT (fun a => singleTyEnv B (TyVar.S a)) (σ y) := by
              exact ren_subT TyVar.S (singleTyEnv B) (σ y)
        _ = substT idSubstT (σ y) := by rfl
        _ = σ y := by simpa using sub_idT (σ y)

theorem subst_exts_single {Δ Ξ : TyCtx} (σ : SubstT Δ Ξ) (A : Ty (Δ ,α)) (B : Ty Ξ) :
    substT (singleTyEnv B) (substT (extsT σ) A) = substT (B •ₜ σ) A := by
  rw [sub_subT (extsT σ) (singleTyEnv B)]
  simpa [compSubT] using congrArg (fun env => substT env A) (exts_single_comp σ B)

theorem exts_compSubT
    {Δ₁ Δ₂ Δ₃ : TyCtx} (σ : SubstT Δ₁ Δ₂) (τ : SubstT Δ₂ Δ₃) :
    (extsT σ ⨟ᵗ extsT τ) = extsT (σ ⨟ᵗ τ) := by
  funext α
  exact congrArg (fun env => env α) (extsT_substT σ τ)

noncomputable def instAt {Δ Ξ : TyCtx} (σ : SubstT Δ Ξ) {A : Ty (Δ ,α)}
    (N : Term (Ξ ,α) (liftCtx ∅ᶜ) (substT (extsT σ) A)) (B : Ty Ξ) :
    Term Ξ ∅ᶜ (substT (B •ₜ σ) A) :=
  castTy (subst_exts_single σ A B) (instT N B)

noncomputable def VRel {Δ Ξ : TyCtx} (A : Ty Δ) (ρ : RelSub Δ Ξ)
    (V : Term Ξ ∅ᶜ (substT ρ.rho1 A))
    (W : Term Ξ ∅ᶜ (substT ρ.rho2 A))
    (v : Value V) (w : Value W) : Prop :=
  match A with
  | Ty.var α =>
      ρ.rhoR α V W v w
  | Ty.nat =>
      VNatRel v w
  | Ty.bool =>
      VBoolRel v w
  | Ty.fn A₁ B₁ =>
      match v with
      | Value.vLam (N := Nfun) =>
          match w with
          | Value.vLam (N := Mfun) =>
              ∀ {V' : Term Ξ ∅ᶜ (substT ρ.rho1 A₁)} {W' : Term Ξ ∅ᶜ (substT ρ.rho2 A₁)},
                (v' : Value V') → (w' : Value W') →
                VRel A₁ ρ V' W' v' w' →
                ∃ (VB : Term Ξ ∅ᶜ (substT ρ.rho1 B₁))
                  (WB : Term Ξ ∅ᶜ (substT ρ.rho2 B₁)),
                  ∃ (vb : Value VB), ∃ (wb : Value WB),
                    Nonempty (singleSubst Nfun V' —↠ VB) ∧
                    Nonempty (singleSubst Mfun W' —↠ WB) ∧
                    VRel B₁ ρ VB WB vb wb
          | _ => False
      | _ => False
  | Ty.all A₁ =>
      match v with
      | Value.vTlam (N := Npoly) =>
          match w with
          | Value.vTlam (N := Mpoly) =>
              ∀ (B₁ B₂ : Ty Ξ), ∀ (Rrel : Rel B₁ B₂),
                ∃ (VA : Term Ξ ∅ᶜ (substT (extendRelSub ρ B₁ B₂ Rrel).rho1 A₁))
                  (WA : Term Ξ ∅ᶜ (substT (extendRelSub ρ B₁ B₂ Rrel).rho2 A₁)),
                  ∃ (va : Value VA), ∃ (wa : Value WA),
                    Nonempty (instAt ρ.rho1 Npoly B₁ —↠ VA) ∧
                    Nonempty (instAt ρ.rho2 Mpoly B₂ —↠ WA) ∧
                    VRel A₁ (extendRelSub ρ B₁ B₂ Rrel) VA WA va wa
          | _ => False
      | _ => False

def ERel {Δ Ξ : TyCtx} (A : Ty Δ) (ρ : RelSub Δ Ξ)
    (M : Term Ξ ∅ᶜ (substT ρ.rho1 A))
    (N : Term Ξ ∅ᶜ (substT ρ.rho2 A)) : Prop :=
  ∃ (V : Term Ξ ∅ᶜ (substT ρ.rho1 A))
    (W : Term Ξ ∅ᶜ (substT ρ.rho2 A)),
  ∃ (v : Value V), ∃ (w : Value W),
      Nonempty (M —↠ V) ∧ Nonempty (N —↠ W) ∧ VRel A ρ V W v w

theorem VRel_fn_inv
    {Δ Ξ : TyCtx} {A B : Ty Δ} {ρ : RelSub Δ Ξ}
    {Nfun : Term Ξ (∅ᶜ , substT ρ.rho1 A) (substT ρ.rho1 B)}
    {Mfun : Term Ξ (∅ᶜ , substT ρ.rho2 A) (substT ρ.rho2 B)} :
    VRel (Ty.fn A B) ρ
      (Term.lam (substT ρ.rho1 A) Nfun)
      (Term.lam (substT ρ.rho2 A) Mfun)
      (Value.vLam (N := Nfun))
      (Value.vLam (N := Mfun)) →
    ∀ {V' : Term Ξ ∅ᶜ (substT ρ.rho1 A)} {W' : Term Ξ ∅ᶜ (substT ρ.rho2 A)},
      (v' : Value V') → (w' : Value W') →
      VRel A ρ V' W' v' w' →
      ∃ (VB : Term Ξ ∅ᶜ (substT ρ.rho1 B))
        (WB : Term Ξ ∅ᶜ (substT ρ.rho2 B)),
        ∃ (vb : Value VB), ∃ (wb : Value WB),
          Nonempty (singleSubst Nfun V' —↠ VB) ∧
          Nonempty (singleSubst Mfun W' —↠ WB) ∧
          VRel B ρ VB WB vb wb := by
  intro h
  dsimp [VRel] at h
  intro V' W' v' w' hv
  exact h v' w' hv

theorem VRel_fn_intro
    {Δ Ξ : TyCtx} {A B : Ty Δ} {ρ : RelSub Δ Ξ}
    {Nfun : Term Ξ (∅ᶜ , substT ρ.rho1 A) (substT ρ.rho1 B)}
    {Mfun : Term Ξ (∅ᶜ , substT ρ.rho2 A) (substT ρ.rho2 B)}
    (h :
      ∀ {V' : Term Ξ ∅ᶜ (substT ρ.rho1 A)} {W' : Term Ξ ∅ᶜ (substT ρ.rho2 A)},
        (v' : Value V') → (w' : Value W') →
        VRel A ρ V' W' v' w' →
        ∃ (VB : Term Ξ ∅ᶜ (substT ρ.rho1 B))
          (WB : Term Ξ ∅ᶜ (substT ρ.rho2 B)),
          ∃ (vb : Value VB), ∃ (wb : Value WB),
            Nonempty (singleSubst Nfun V' —↠ VB) ∧
            Nonempty (singleSubst Mfun W' —↠ WB) ∧
            VRel B ρ VB WB vb wb) :
    VRel (Ty.fn A B) ρ
      (Term.lam (substT ρ.rho1 A) Nfun)
      (Term.lam (substT ρ.rho2 A) Mfun)
      (Value.vLam (N := Nfun))
      (Value.vLam (N := Mfun)) := by
  dsimp [VRel]
  exact h

theorem VRel_all_inv
    {Δ Ξ : TyCtx} {A : Ty (Δ ,α)} {ρ : RelSub Δ Ξ}
    {Npoly : Term (Ξ ,α) (liftCtx ∅ᶜ) (substT (extsT ρ.rho1) A)}
    {Mpoly : Term (Ξ ,α) (liftCtx ∅ᶜ) (substT (extsT ρ.rho2) A)} :
    VRel (Ty.all A) ρ
      (Term.tlam Npoly)
      (Term.tlam Mpoly)
      (Value.vTlam (N := Npoly))
      (Value.vTlam (N := Mpoly)) →
    ∀ (B₁ B₂ : Ty Ξ), ∀ (Rrel : Rel B₁ B₂),
      ∃ (VA : Term Ξ ∅ᶜ (substT (extendRelSub ρ B₁ B₂ Rrel).rho1 A))
        (WA : Term Ξ ∅ᶜ (substT (extendRelSub ρ B₁ B₂ Rrel).rho2 A)),
        ∃ (va : Value VA), ∃ (wa : Value WA),
          Nonempty (instAt ρ.rho1 Npoly B₁ —↠ VA) ∧
          Nonempty (instAt ρ.rho2 Mpoly B₂ —↠ WA) ∧
          VRel A (extendRelSub ρ B₁ B₂ Rrel) VA WA va wa := by
  intro h
  dsimp [VRel] at h
  intro B₁ B₂ Rrel
  exact h B₁ B₂ Rrel

theorem VRel_all_intro
    {Δ Ξ : TyCtx} {A : Ty (Δ ,α)} {ρ : RelSub Δ Ξ}
    {Npoly : Term (Ξ ,α) (liftCtx ∅ᶜ) (substT (extsT ρ.rho1) A)}
    {Mpoly : Term (Ξ ,α) (liftCtx ∅ᶜ) (substT (extsT ρ.rho2) A)}
    (h :
      ∀ (B₁ B₂ : Ty Ξ), ∀ (Rrel : Rel B₁ B₂),
        ∃ (VA : Term Ξ ∅ᶜ (substT (extendRelSub ρ B₁ B₂ Rrel).rho1 A))
          (WA : Term Ξ ∅ᶜ (substT (extendRelSub ρ B₁ B₂ Rrel).rho2 A)),
          ∃ (va : Value VA), ∃ (wa : Value WA),
            Nonempty (instAt ρ.rho1 Npoly B₁ —↠ VA) ∧
            Nonempty (instAt ρ.rho2 Mpoly B₂ —↠ WA) ∧
            VRel A (extendRelSub ρ B₁ B₂ Rrel) VA WA va wa) :
    VRel (Ty.all A) ρ
      (Term.tlam Npoly)
      (Term.tlam Mpoly)
      (Value.vTlam (N := Npoly))
      (Value.vTlam (N := Mpoly)) := by
  dsimp [VRel]
  exact h

theorem VRel_to_ERel
    {Δ Ξ : TyCtx} {A : Ty Δ} {ρ : RelSub Δ Ξ}
    {V : Term Ξ ∅ᶜ (substT ρ.rho1 A)}
    {W : Term Ξ ∅ᶜ (substT ρ.rho2 A)}
    (v : Value V) (w : Value W) :
    VRel A ρ V W v w → ERel A ρ V W := by
  intro h
  exact Exists.intro V (Exists.intro W (Exists.intro v (Exists.intro w
    (And.intro ⟨MultiStep.refl _⟩ (And.intro ⟨MultiStep.refl _⟩ h)))))

theorem VRel_castTyIndex
    {Δ Ξ : TyCtx} (ρ : RelSub Δ Ξ)
    {A B : Ty Δ} (p : A = B)
    {V : Term Ξ ∅ᶜ (substT ρ.rho1 A)}
    {W : Term Ξ ∅ᶜ (substT ρ.rho2 A)}
    {v : Value V} {w : Value W} :
    VRel A ρ V W v w →
    VRel B ρ
      (castTy (congrArg (substT ρ.rho1) p) V)
      (castTy (congrArg (substT ρ.rho2) p) W)
      (castValue (congrArg (substT ρ.rho1) p) v)
      (castValue (congrArg (substT ρ.rho2) p) w) := by
  cases p
  intro h
  simpa using h

theorem ERel_castTyIndex
    {Δ Ξ : TyCtx} (ρ : RelSub Δ Ξ)
    {A B : Ty Δ} (p : A = B)
    {M : Term Ξ ∅ᶜ (substT ρ.rho1 A)}
    {N : Term Ξ ∅ᶜ (substT ρ.rho2 A)} :
    ERel A ρ M N →
    ERel B ρ
      (castTy (congrArg (substT ρ.rho1) p) M)
      (castTy (congrArg (substT ρ.rho2) p) N) := by
  intro h
  rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
  rcases mSteps with ⟨mSteps'⟩
  rcases nSteps with ⟨nSteps'⟩
  apply Exists.intro (castTy (congrArg (substT ρ.rho1) p) V)
  apply Exists.intro (castTy (congrArg (substT ρ.rho2) p) W)
  apply Exists.intro (castValue (congrArg (substT ρ.rho1) p) v)
  apply Exists.intro (castValue (congrArg (substT ρ.rho2) p) w)
  apply And.intro
  · exact ⟨castMultiTy (congrArg (substT ρ.rho1) p) mSteps'⟩
  · apply And.intro
    · exact ⟨castMultiTy (congrArg (substT ρ.rho2) p) nSteps'⟩
    · exact VRel_castTyIndex (ρ := ρ) p rel

inductive WkRel : {Δ Δ' Ξ : TyCtx} → RenameT Δ Δ' → RelSub Δ Ξ → RelSub Δ' Ξ → Prop where
  | wk_suc {Δ Ξ : TyCtx} {ρ : RelSub Δ Ξ} {A₁ A₂ : Ty Ξ} (R : Rel A₁ A₂) :
      WkRel TyVar.S ρ (extendRelSub ρ A₁ A₂ R)
  | wk_ext {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
      {B₁ B₂ : Ty Ξ} (S : Rel B₁ B₂) :
      WkRel ξ ρ ρ' →
      WkRel (extT ξ) (extendRelSub ρ B₁ B₂ S) (extendRelSub ρ' B₁ B₂ S)

theorem wk_rho1_var
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') :
    ∀ α, ρ'.rho1 (ξ α) = ρ.rho1 α := by
  intro α
  induction wk with
  | wk_suc =>
      rfl
  | wk_ext _ wk ih =>
      cases α with
      | Z =>
          rfl
      | S β =>
          simp [extendRelSub]
          simp [extT]
          exact ih β

theorem wk_rho2_var
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') :
    ∀ α, ρ'.rho2 (ξ α) = ρ.rho2 α := by
  intro α
  induction wk with
  | wk_suc =>
      rfl
  | wk_ext _ wk ih =>
      cases α with
      | Z =>
          rfl
      | S β =>
          simp [extendRelSub]
          simp [extT]
          exact ih β

theorem wk_substT_rho1
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (A : Ty Δ) :
    substT ρ'.rho1 (renameT ξ A) = substT ρ.rho1 A := by
  calc
    substT ρ'.rho1 (renameT ξ A)
        = substT (fun α => ρ'.rho1 (ξ α)) A := by
            simpa using ren_subT ξ ρ'.rho1 A
    _ = substT ρ.rho1 A := by
          apply substT_cong
          intro α
          exact wk_rho1_var (wk := wk) α

theorem wk_substT_rho2
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (A : Ty Δ) :
    substT ρ'.rho2 (renameT ξ A) = substT ρ.rho2 A := by
  calc
    substT ρ'.rho2 (renameT ξ A)
        = substT (fun α => ρ'.rho2 (ξ α)) A := by
            simpa using ren_subT ξ ρ'.rho2 A
    _ = substT ρ.rho2 A := by
          apply substT_cong
          intro α
          exact wk_rho2_var (wk := wk) α

theorem wk_substT_ext_rho1
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (A : Ty (Δ ,α)) :
    substT (extsT ρ'.rho1) (renameT (extT ξ) A) = substT (extsT ρ.rho1) A := by
  calc
    substT (extsT ρ'.rho1) (renameT (extT ξ) A)
        = substT (fun α => extsT ρ'.rho1 (extT ξ α)) A := by
            simpa using ren_subT (extT ξ) (extsT ρ'.rho1) A
    _ = substT (extsT ρ.rho1) A := by
          apply substT_cong
          intro α
          cases α with
          | Z =>
              rfl
          | S β =>
              have hβ : renameT TyVar.S (ρ'.rho1 (ξ β)) = renameT TyVar.S (ρ.rho1 β) := by
                simpa using congrArg (renameT TyVar.S) (wk_rho1_var (wk := wk) β)
              simpa [extsT] using (by simpa [extT] using hβ)

theorem wk_substT_ext_rho2
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (A : Ty (Δ ,α)) :
    substT (extsT ρ'.rho2) (renameT (extT ξ) A) = substT (extsT ρ.rho2) A := by
  calc
    substT (extsT ρ'.rho2) (renameT (extT ξ) A)
        = substT (fun α => extsT ρ'.rho2 (extT ξ α)) A := by
            simpa using ren_subT (extT ξ) (extsT ρ'.rho2) A
    _ = substT (extsT ρ.rho2) A := by
          apply substT_cong
          intro α
          cases α with
          | Z =>
              rfl
          | S β =>
              have hβ : renameT TyVar.S (ρ'.rho2 (ξ β)) = renameT TyVar.S (ρ.rho2 β) := by
                simpa using congrArg (renameT TyVar.S) (wk_rho2_var (wk := wk) β)
              simpa [extsT] using (by simpa [extT] using hβ)

theorem wk_rhoR_cast
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ')
    (α : TyVar Δ)
    {V : Term Ξ ∅ᶜ (ρ.rho1 α)}
    {W : Term Ξ ∅ᶜ (ρ.rho2 α)}
    {v : Value V} {w : Value W} :
    ρ.rhoR α V W v w →
    ρ'.rhoR (ξ α)
      (castTy (Eq.symm (wk_rho1_var (wk := wk) α)) V)
      (castTy (Eq.symm (wk_rho2_var (wk := wk) α)) W)
      (castValue (Eq.symm (wk_rho1_var (wk := wk) α)) v)
      (castValue (Eq.symm (wk_rho2_var (wk := wk) α)) w) := by
  intro h
  induction wk with
  | wk_suc R =>
      simpa [extendRelSub] using h
  | wk_ext S wk ih =>
      cases α with
      | Z =>
          simpa [extendRelSub] using h
      | S β =>
          simpa [extendRelSub] using
            ih (α := β) (V := V) (W := W) (v := v) (w := w)
              (by simpa [extendRelSub] using h)

theorem wk_rhoR_uncast
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ')
    (α : TyVar Δ)
    {V : Term Ξ ∅ᶜ (ρ.rho1 α)}
    {W : Term Ξ ∅ᶜ (ρ.rho2 α)}
    {v : Value V} {w : Value W} :
    ρ'.rhoR (ξ α)
      (castTy (Eq.symm (wk_rho1_var (wk := wk) α)) V)
      (castTy (Eq.symm (wk_rho2_var (wk := wk) α)) W)
      (castValue (Eq.symm (wk_rho1_var (wk := wk) α)) v)
      (castValue (Eq.symm (wk_rho2_var (wk := wk) α)) w) →
    ρ.rhoR α V W v w := by
  intro h
  induction wk with
  | wk_suc R =>
      simpa [extendRelSub] using h
  | wk_ext S wk ih =>
      cases α with
      | Z =>
          simpa [extendRelSub] using h
      | S β =>
          simpa [extendRelSub] using
            ih (α := β) (V := V) (W := W) (v := v) (w := w)
              (by simpa [extendRelSub] using h)

theorem wk_rhoR_uncast_plain
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ')
    (α : TyVar Δ)
    {V : Term Ξ ∅ᶜ (ρ'.rho1 (ξ α))}
    {W : Term Ξ ∅ᶜ (ρ'.rho2 (ξ α))}
    {v : Value V} {w : Value W} :
    ρ'.rhoR (ξ α) V W v w →
    ρ.rhoR α
      (castTy (wk_rho1_var (wk := wk) α) V)
      (castTy (wk_rho2_var (wk := wk) α) W)
      (castValue (wk_rho1_var (wk := wk) α) v)
      (castValue (wk_rho2_var (wk := wk) α) w) := by
  intro h
  induction wk with
  | wk_suc R =>
      simp [extendRelSub] at h ⊢
      exact h
  | wk_ext S wk ih =>
      cases α with
      | Z =>
          simp [extendRelSub] at h ⊢
          exact h
      | S β =>
          have h' := by
            simpa [extendRelSub] using h
          have ih' := ih (α := β) (V := V) (W := W) (v := v) (w := w) h'
          simp [extendRelSub] at ih' ⊢
          exact ih'

structure SubstRel
    {Δ Δ' Ξ : TyCtx} (σ : SubstT Δ Δ') (ρ : RelSub Δ' Ξ) (ρ' : RelSub Δ Ξ) : Prop where
  sigmaRho1 : ∀ α, substT ρ.rho1 (σ α) = ρ'.rho1 α
  sigmaRho2 : ∀ α, substT ρ.rho2 (σ α) = ρ'.rho2 α
  varTo : ∀ α
      {V : Term Ξ ∅ᶜ (ρ'.rho1 α)}
      {W : Term Ξ ∅ᶜ (ρ'.rho2 α)}
      {v : Value V} {w : Value W},
      ρ'.rhoR α V W v w →
      VRel (σ α) ρ
        (castTy (Eq.symm (sigmaRho1 α)) V)
        (castTy (Eq.symm (sigmaRho2 α)) W)
        (castValue (Eq.symm (sigmaRho1 α)) v)
        (castValue (Eq.symm (sigmaRho2 α)) w)
  varFrom : ∀ α
      {V : Term Ξ ∅ᶜ (substT ρ.rho1 (σ α))}
      {W : Term Ξ ∅ᶜ (substT ρ.rho2 (σ α))}
      {v : Value V} {w : Value W},
      VRel (σ α) ρ V W v w →
      ρ'.rhoR α
        (castTy (sigmaRho1 α) V)
        (castTy (sigmaRho2 α) W)
        (castValue (sigmaRho1 α) v)
        (castValue (sigmaRho2 α) w)

theorem SubstRel_substT_rho1
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (A : Ty Δ) :
    substT ρ.rho1 (substT σ A) = substT ρ'.rho1 A := by
  induction A with
  | var α =>
      exact sr.sigmaRho1 α
  | nat =>
      rfl
  | bool =>
      rfl
  | fn A B ihA ihB =>
      calc
        substT ρ.rho1 (substT σ (Ty.fn A B))
            = Ty.fn (substT ρ.rho1 (substT σ A)) (substT ρ.rho1 (substT σ B)) := rfl
        _ = Ty.fn (substT ρ'.rho1 A) (substT ρ'.rho1 B) := by
              have hA := ihA sr
              have hB := ihB sr
              rw [hA]
              rw [hB]
        _ = substT ρ'.rho1 (Ty.fn A B) := rfl
  | all A ih =>
      refine congrArg Ty.all ?_
      calc
        substT (extsT ρ.rho1) (substT (extsT σ) A)
            = substT (extsT (σ ⨟ᵗ ρ.rho1)) A := by
                rw [sub_subT (extsT σ) (extsT ρ.rho1) A]
                rw [exts_compSubT σ ρ.rho1]
        _ = substT (extsT (fun α => substT ρ.rho1 (σ α))) A := by
              rfl
        _ = substT (extsT ρ'.rho1) A := by
              apply substT_cong
              intro α
              cases α with
              | Z =>
                  rfl
              | S β =>
                  simpa [extsT] using congrArg (renameT TyVar.S) (sr.sigmaRho1 β)

theorem SubstRel_substT_rho2
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (A : Ty Δ) :
    substT ρ.rho2 (substT σ A) = substT ρ'.rho2 A := by
  induction A with
  | var α =>
      exact sr.sigmaRho2 α
  | nat =>
      rfl
  | bool =>
      rfl
  | fn A B ihA ihB =>
      calc
        substT ρ.rho2 (substT σ (Ty.fn A B))
            = Ty.fn (substT ρ.rho2 (substT σ A)) (substT ρ.rho2 (substT σ B)) := rfl
        _ = Ty.fn (substT ρ'.rho2 A) (substT ρ'.rho2 B) := by
              have hA := ihA sr
              have hB := ihB sr
              rw [hA]
              rw [hB]
        _ = substT ρ'.rho2 (Ty.fn A B) := rfl
  | all A ih =>
      refine congrArg Ty.all ?_
      calc
        substT (extsT ρ.rho2) (substT (extsT σ) A)
            = substT (extsT (σ ⨟ᵗ ρ.rho2)) A := by
                rw [sub_subT (extsT σ) (extsT ρ.rho2) A]
                rw [exts_compSubT σ ρ.rho2]
        _ = substT (extsT (fun α => substT ρ.rho2 (σ α))) A := by
              rfl
        _ = substT (extsT ρ'.rho2) A := by
              apply substT_cong
              intro α
              cases α with
              | Z =>
                  rfl
              | S β =>
                  simpa [extsT] using congrArg (renameT TyVar.S) (sr.sigmaRho2 β)

theorem SubstRel_substT_ext_rho1
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (A : Ty (Δ ,α)) :
    substT (extsT ρ.rho1) (substT (extsT σ) A) = substT (extsT ρ'.rho1) A := by
  calc
    substT (extsT ρ.rho1) (substT (extsT σ) A)
        = substT (extsT (σ ⨟ᵗ ρ.rho1)) A := by
            rw [sub_subT (extsT σ) (extsT ρ.rho1) A]
            rw [exts_compSubT σ ρ.rho1]
    _ = substT (extsT (fun α => substT ρ.rho1 (σ α))) A := by
          rfl
    _ = substT (extsT ρ'.rho1) A := by
          apply substT_cong
          intro α
          cases α with
          | Z =>
              rfl
          | S β =>
              simpa [extsT] using congrArg (renameT TyVar.S) (sr.sigmaRho1 β)

theorem SubstRel_substT_ext_rho2
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (A : Ty (Δ ,α)) :
    substT (extsT ρ.rho2) (substT (extsT σ) A) = substT (extsT ρ'.rho2) A := by
  calc
    substT (extsT ρ.rho2) (substT (extsT σ) A)
        = substT (extsT (σ ⨟ᵗ ρ.rho2)) A := by
            rw [sub_subT (extsT σ) (extsT ρ.rho2) A]
            rw [exts_compSubT σ ρ.rho2]
    _ = substT (extsT (fun α => substT ρ.rho2 (σ α))) A := by
          rfl
    _ = substT (extsT ρ'.rho2) A := by
          apply substT_cong
          intro α
          cases α with
          | Z =>
              rfl
          | S β =>
              simpa [extsT] using congrArg (renameT TyVar.S) (sr.sigmaRho2 β)

theorem VRel_rename_wk_var
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (α : TyVar Δ)
    {V : Term Ξ ∅ᶜ (substT ρ.rho1 (#α))}
    {W : Term Ξ ∅ᶜ (substT ρ.rho2 (#α))}
    {v : Value V} {w : Value W} :
    VRel (#α) ρ V W v w →
    VRel (renameT ξ (#α)) ρ'
      (castTy (Eq.symm (wk_substT_rho1 (wk := wk) (#α))) V)
      (castTy (Eq.symm (wk_substT_rho2 (wk := wk) (#α))) W)
      (castValue (Eq.symm (wk_substT_rho1 (wk := wk) (#α))) v)
      (castValue (Eq.symm (wk_substT_rho2 (wk := wk) (#α))) w) := by
  intro h
  simpa [VRel] using
    wk_rhoR_cast (wk := wk) α (V := V) (W := W) (v := v) (w := w) h

theorem VRel_subst_var
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (α : TyVar Δ)
    {V : Term Ξ ∅ᶜ (substT ρ'.rho1 (#α))}
    {W : Term Ξ ∅ᶜ (substT ρ'.rho2 (#α))}
    {v : Value V} {w : Value W} :
    VRel (#α) ρ' V W v w →
    VRel (substT σ (#α)) ρ
      (castTy (Eq.symm (SubstRel_substT_rho1 sr (#α))) V)
      (castTy (Eq.symm (SubstRel_substT_rho2 sr (#α))) W)
      (castValue (Eq.symm (SubstRel_substT_rho1 sr (#α))) v)
      (castValue (Eq.symm (SubstRel_substT_rho2 sr (#α))) w) := by
  intro h
  simpa [VRel] using sr.varTo α h

theorem VRel_unrename_wk_var
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (α : TyVar Δ)
    {V : Term Ξ ∅ᶜ (substT ρ'.rho1 (renameT ξ (#α)))}
    {W : Term Ξ ∅ᶜ (substT ρ'.rho2 (renameT ξ (#α)))}
    {v : Value V} {w : Value W} :
    VRel (renameT ξ (#α)) ρ' V W v w →
    VRel (#α) ρ
      (castTy (wk_substT_rho1 (wk := wk) (#α)) V)
      (castTy (wk_substT_rho2 (wk := wk) (#α)) W)
      (castValue (wk_substT_rho1 (wk := wk) (#α)) v)
      (castValue (wk_substT_rho2 (wk := wk) (#α)) w) := by
  intro h
  simpa [VRel] using wk_rhoR_uncast_plain (wk := wk) α h

theorem ERel_subst_var
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (α : TyVar Δ)
    {M : Term Ξ ∅ᶜ (substT ρ'.rho1 (#α))}
    {N : Term Ξ ∅ᶜ (substT ρ'.rho2 (#α))} :
    ERel (#α) ρ' M N →
    ERel (substT σ (#α)) ρ
      (castTy (Eq.symm (SubstRel_substT_rho1 sr (#α))) M)
      (castTy (Eq.symm (SubstRel_substT_rho2 sr (#α))) N) := by
  intro h
  rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
  rcases mSteps with ⟨mSteps'⟩
  rcases nSteps with ⟨nSteps'⟩
  apply Exists.intro (castTy (Eq.symm (SubstRel_substT_rho1 sr (#α))) V)
  apply Exists.intro (castTy (Eq.symm (SubstRel_substT_rho2 sr (#α))) W)
  apply Exists.intro (castValue (Eq.symm (SubstRel_substT_rho1 sr (#α))) v)
  apply Exists.intro (castValue (Eq.symm (SubstRel_substT_rho2 sr (#α))) w)
  apply And.intro
  · exact ⟨castMultiTy (Eq.symm (SubstRel_substT_rho1 sr (#α))) mSteps'⟩
  · apply And.intro
    · exact ⟨castMultiTy (Eq.symm (SubstRel_substT_rho2 sr (#α))) nSteps'⟩
    · exact VRel_subst_var (sr := sr) α rel

theorem ERel_unsubst_var
    {Δ Δ' Ξ : TyCtx} {σ : SubstT Δ Δ'} {ρ : RelSub Δ' Ξ} {ρ' : RelSub Δ Ξ}
    (sr : SubstRel σ ρ ρ') (α : TyVar Δ)
    {M : Term Ξ ∅ᶜ (substT ρ.rho1 (substT σ (#α)))}
    {N : Term Ξ ∅ᶜ (substT ρ.rho2 (substT σ (#α)))} :
    ERel (substT σ (#α)) ρ M N →
    ERel (#α) ρ'
      (castTy (SubstRel_substT_rho1 sr (#α)) M)
      (castTy (SubstRel_substT_rho2 sr (#α)) N) := by
  intro h
  rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
  rcases mSteps with ⟨mSteps'⟩
  rcases nSteps with ⟨nSteps'⟩
  apply Exists.intro (castTy (SubstRel_substT_rho1 sr (#α)) V)
  apply Exists.intro (castTy (SubstRel_substT_rho2 sr (#α)) W)
  apply Exists.intro (castValue (SubstRel_substT_rho1 sr (#α)) v)
  apply Exists.intro (castValue (SubstRel_substT_rho2 sr (#α)) w)
  apply And.intro
  · exact ⟨castMultiTy (SubstRel_substT_rho1 sr (#α)) mSteps'⟩
  · apply And.intro
    · exact ⟨castMultiTy (SubstRel_substT_rho2 sr (#α)) nSteps'⟩
    · simpa [VRel] using sr.varFrom α rel

theorem ERel_rename_wk_var
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (α : TyVar Δ)
    {M : Term Ξ ∅ᶜ (substT ρ.rho1 (#α))}
    {N : Term Ξ ∅ᶜ (substT ρ.rho2 (#α))} :
    ERel (#α) ρ M N →
    ERel (renameT ξ (#α)) ρ'
      (castTy (Eq.symm (wk_substT_rho1 (wk := wk) (#α))) M)
      (castTy (Eq.symm (wk_substT_rho2 (wk := wk) (#α))) N) := by
  intro h
  rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
  rcases mSteps with ⟨mSteps'⟩
  rcases nSteps with ⟨nSteps'⟩
  apply Exists.intro (castTy (Eq.symm (wk_substT_rho1 (wk := wk) (#α))) V)
  apply Exists.intro (castTy (Eq.symm (wk_substT_rho2 (wk := wk) (#α))) W)
  apply Exists.intro (castValue (Eq.symm (wk_substT_rho1 (wk := wk) (#α))) v)
  apply Exists.intro (castValue (Eq.symm (wk_substT_rho2 (wk := wk) (#α))) w)
  apply And.intro
  · exact ⟨castMultiTy (Eq.symm (wk_substT_rho1 (wk := wk) (#α))) mSteps'⟩
  · apply And.intro
    · exact ⟨castMultiTy (Eq.symm (wk_substT_rho2 (wk := wk) (#α))) nSteps'⟩
    · exact VRel_rename_wk_var (wk := wk) α rel

theorem ERel_unrename_wk_var
    {Δ Δ' Ξ : TyCtx} {ξ : RenameT Δ Δ'} {ρ : RelSub Δ Ξ} {ρ' : RelSub Δ' Ξ}
    (wk : WkRel ξ ρ ρ') (α : TyVar Δ)
    {M : Term Ξ ∅ᶜ (substT ρ'.rho1 (renameT ξ (#α)))}
    {N : Term Ξ ∅ᶜ (substT ρ'.rho2 (renameT ξ (#α)))} :
    ERel (renameT ξ (#α)) ρ' M N →
    ERel (#α) ρ
      (castTy (wk_substT_rho1 (wk := wk) (#α)) M)
      (castTy (wk_substT_rho2 (wk := wk) (#α)) N) := by
  intro h
  rcases h with ⟨V, W, v, w, mSteps, nSteps, rel⟩
  rcases mSteps with ⟨mSteps'⟩
  rcases nSteps with ⟨nSteps'⟩
  apply Exists.intro (castTy (wk_substT_rho1 (wk := wk) (#α)) V)
  apply Exists.intro (castTy (wk_substT_rho2 (wk := wk) (#α)) W)
  apply Exists.intro (castValue (wk_substT_rho1 (wk := wk) (#α)) v)
  apply Exists.intro (castValue (wk_substT_rho2 (wk := wk) (#α)) w)
  apply And.intro
  · exact ⟨castMultiTy (wk_substT_rho1 (wk := wk) (#α)) mSteps'⟩
  · apply And.intro
    · exact ⟨castMultiTy (wk_substT_rho2 (wk := wk) (#α)) nSteps'⟩
    · simpa [VRel] using
        wk_rhoR_uncast_plain (wk := wk) α rel

structure RelEnv {Δ Ξ : TyCtx} (Γ : Ctx Δ) (ρ : RelSub Δ Ξ) where
  gamma1 : Sub (substCtx ρ.rho1 Γ) (∅ᶜ : Ctx Ξ)
  gamma2 : Sub (substCtx ρ.rho2 Γ) (∅ᶜ : Ctx Ξ)

def emptyRelEnv {Δ Ξ : TyCtx} (ρ : RelSub Δ Ξ) :
    RelEnv (Γ := (∅ᶜ : Ctx Δ)) ρ where
  gamma1 := by
    intro A x
    cases x
  gamma2 := by
    intro A x
    cases x

def extendRelEnv {Δ Ξ : TyCtx} {Γ : Ctx Δ} {ρ : RelSub Δ Ξ} {A : Ty Δ}
    (γ : RelEnv Γ ρ)
    (V : Term Ξ ∅ᶜ (substT ρ.rho1 A))
    (W : Term Ξ ∅ᶜ (substT ρ.rho2 A)) :
    RelEnv (Γ := (Γ , A)) ρ where
  gamma1 := by
    intro B x
    cases x with
    | Z =>
        exact V
    | S y =>
        exact γ.gamma1 y
  gamma2 := by
    intro B x
    cases x with
    | Z =>
        exact W
    | S y =>
        exact γ.gamma2 y

def tailRelEnv {Δ Ξ : TyCtx} {Γ : Ctx Δ} {ρ : RelSub Δ Ξ} {A : Ty Δ}
    (γ : RelEnv (Γ := (Γ , A)) ρ) :
    RelEnv (Γ := Γ) ρ where
  gamma1 := by
    intro B x
    exact γ.gamma1 (HasVar.S x)
  gamma2 := by
    intro B x
    exact γ.gamma2 (HasVar.S x)

theorem tailRelEnv_extendRelEnv
    {Δ Ξ : TyCtx} {Γ : Ctx Δ} {ρ : RelSub Δ Ξ} {A : Ty Δ}
    (γ : RelEnv Γ ρ)
    (V : Term Ξ ∅ᶜ (substT ρ.rho1 A))
    (W : Term Ξ ∅ᶜ (substT ρ.rho2 A)) :
    tailRelEnv (extendRelEnv γ V W) = γ := by
  cases γ
  rfl

def GRel {Δ Ξ : TyCtx} (Γ : Ctx Δ) (ρ : RelSub Δ Ξ) (γ : RelEnv Γ ρ) : Prop :=
  match Γ with
  | .empty =>
      True
  | .snoc Γ' A =>
      ERel A ρ (γ.gamma1 HasVar.Z) (γ.gamma2 HasVar.Z) ∧
      GRel Γ' ρ (tailRelEnv (A := A) γ)
termination_by Γ

def LogicalRel {Δ : TyCtx} (Γ : Ctx Δ) (A : Ty Δ)
    (M N : Term Δ Γ A) : Prop :=
  ∀ {Ξ : TyCtx} (ρ : RelSub Δ Ξ) (γ : RelEnv Γ ρ),
    GRel Γ ρ γ →
    ERel A ρ
      (subst γ.gamma1 (substTT ρ.rho1 M))
      (subst γ.gamma2 (substTT ρ.rho2 N))

def GRel_empty : GRel (Γ := (∅ᶜ : Ctx ∅)) emptyRelSub (emptyRelEnv emptyRelSub) := by
  simp [GRel]

theorem extendRelEnv_related
    {Δ Ξ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ} {ρ : RelSub Δ Ξ}
    {γ : RelEnv Γ ρ}
    {V : Term Ξ ∅ᶜ (substT ρ.rho1 A)}
    {W : Term Ξ ∅ᶜ (substT ρ.rho2 A)}
    (env : GRel Γ ρ γ)
    (v : Value V)
    (w : Value W)
    (hVW : VRel A ρ V W v w) :
    GRel (Γ := (Γ , A)) ρ (extendRelEnv γ V W) := by
  simpa [GRel] using And.intro
    (VRel_to_ERel (A := A) (ρ := ρ) (V := V) (W := W) v w hVW)
    (Eq.ndrec env (tailRelEnv_extendRelEnv γ V W))

end Intrinsic

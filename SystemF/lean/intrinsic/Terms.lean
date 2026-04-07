import intrinsic.Ctx

namespace Intrinsic

set_option autoImplicit false

inductive Term : (Δ : TyCtx) → Ctx Δ → Ty Δ → Type where
  | ttrue : {Δ : TyCtx} → {Γ : Ctx Δ} → Term Δ Γ TBool
  | tfalse : {Δ : TyCtx} → {Γ : Ctx Δ} → Term Δ Γ TBool
  | tzero : {Δ : TyCtx} → {Γ : Ctx Δ} → Term Δ Γ TNat
  | tsuc : {Δ : TyCtx} → {Γ : Ctx Δ} → Term Δ Γ TNat → Term Δ Γ TNat
  | tcaseNat : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      Term Δ Γ TNat → Term Δ Γ A → Term Δ (Γ , TNat) A → Term Δ Γ A
  | tite : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} →
      Term Δ Γ TBool → Term Δ Γ A → Term Δ Γ A → Term Δ Γ A
  | var : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} → HasVar Γ A → Term Δ Γ A
  | lam : {Δ : TyCtx} → {Γ : Ctx Δ} → {B : Ty Δ} →
      (A : Ty Δ) → Term Δ (Γ , A) B → Term Δ Γ (A ⇒ B)
  | app : {Δ : TyCtx} → {Γ : Ctx Δ} → {A B : Ty Δ} →
      Term Δ Γ (A ⇒ B) → Term Δ Γ A → Term Δ Γ B
  | tlam : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty (Δ ,α)} →
      Term (Δ ,α) (liftCtx Γ) A → Term Δ Γ (∀ₜ A)
  | tapp : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty (Δ ,α)} →
      Term Δ Γ (∀ₜ A) → (B : Ty Δ) → Term Δ Γ (A [ B ]ₜ)

abbrev Closed (A : Ty ∅) : Type := Term ∅ ∅ᶜ A

def castTermCtx {Δ : TyCtx} {Γ Γ' : Ctx Δ} {A : Ty Δ}
    (h : Γ = Γ') (M : Term Δ Γ A) : Term Δ Γ' A := by
  cases h
  exact M

def castTermTy {Δ : TyCtx} {Γ : Ctx Δ} {A B : Ty Δ}
    (h : A = B) (M : Term Δ Γ A) : Term Δ Γ B := by
  cases h
  exact M

def renameTT {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') {Γ : Ctx Δ} {A : Ty Δ}
    (M : Term Δ Γ A) : Term Δ' (renameCtx ρ Γ) (renameT ρ A) :=
  match M with
  | Term.ttrue => Term.ttrue
  | Term.tfalse => Term.tfalse
  | Term.tzero => Term.tzero
  | Term.tsuc N => Term.tsuc (renameTT ρ N)
  | Term.tcaseNat L M N => Term.tcaseNat (renameTT ρ L) (renameTT ρ M) (renameTT ρ N)
  | Term.tite L M N => Term.tite (renameTT ρ L) (renameTT ρ M) (renameTT ρ N)
  | Term.var x => Term.var (renameVar ρ x)
  | Term.lam B N => Term.lam (renameT ρ B) (renameTT ρ N)
  | Term.app L M => Term.app (renameTT ρ L) (renameTT ρ M)
  | @Term.tlam _ Γ A N =>
      Term.tlam (castTermCtx (renameCtx_ext_lift ρ Γ) (renameTT (extT ρ) N))
  | @Term.tapp _ _ A N B =>
      castTermTy (Eq.symm (renameT_substOne ρ A B))
        (Term.tapp (renameTT ρ N) (renameT ρ B))
termination_by sizeOf M
decreasing_by
  all_goals simp_wf
  all_goals omega

def substTT {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') {Γ : Ctx Δ} {A : Ty Δ}
    (M : Term Δ Γ A) : Term Δ' (substCtx σ Γ) (substT σ A) :=
  match M with
  | Term.ttrue => Term.ttrue
  | Term.tfalse => Term.tfalse
  | Term.tzero => Term.tzero
  | Term.tsuc N => Term.tsuc (substTT σ N)
  | Term.tcaseNat L M N => Term.tcaseNat (substTT σ L) (substTT σ M) (substTT σ N)
  | Term.tite L M N => Term.tite (substTT σ L) (substTT σ M) (substTT σ N)
  | Term.var x => Term.var (substVar σ x)
  | Term.lam B N => Term.lam (substT σ B) (substTT σ N)
  | Term.app L M => Term.app (substTT σ L) (substTT σ M)
  | @Term.tlam _ Γ A N =>
      Term.tlam (castTermCtx (substCtx_exts_lift σ Γ) (substTT (extsT σ) N))
  | @Term.tapp _ _ A N B =>
      castTermTy (Eq.symm (substT_substOne σ A B))
        (Term.tapp (substTT σ N) (substT σ B))
termination_by sizeOf M
decreasing_by
  all_goals simp_wf
  all_goals omega

def instT {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty (Δ ,α)}
    (N : Term (Δ ,α) (liftCtx Γ) A) (B : Ty Δ) : Term Δ Γ (A [ B ]ₜ) :=
  castTermCtx (substCtx_single_cancel Γ B) (substTT (singleTyEnv B) N)

theorem instT_empty_eq_substTT {Δ : TyCtx} {A : Ty (Δ ,α)}
    (N : Term (Δ ,α) (liftCtx (∅ᶜ : Ctx Δ)) A) (B : Ty Δ) :
    instT (Γ := (∅ᶜ : Ctx Δ)) N B = substTT (singleTyEnv B) N := by
  unfold instT
  have h : substCtx_single_cancel (Γ := (∅ᶜ : Ctx Δ)) B =
      (rfl : substCtx (singleTyEnv B) (liftCtx (∅ᶜ : Ctx Δ)) = (∅ᶜ : Ctx Δ)) := by
    exact Subsingleton.elim _ _
  rw [h]
  rfl

@[simp] theorem instT_lam_empty {Δ : TyCtx} {C : Ty (Δ ,α)}
    (N : Term (Δ ,α) (liftCtx (∅ᶜ : Ctx Δ) , #TyVar.Z) C) (B : Ty Δ) :
    instT (Γ := (∅ᶜ : Ctx Δ)) (N := Term.lam (#TyVar.Z) N) B
      = Term.lam B (substTT (singleTyEnv B) N) := by
  rw [instT_empty_eq_substTT]
  simp [substTT]
  have hty : substT (singleTyEnv B) ((#TyVar.Z : Ty (Δ ,α))) = B := rfl
  cases hty
  rfl

@[simp] theorem instT_lam_empty_gen {Δ : TyCtx} {A C : Ty (Δ ,α)}
    (N : Term (Δ ,α) (liftCtx (∅ᶜ : Ctx Δ) , A) C) (B : Ty Δ) :
    instT (Γ := (∅ᶜ : Ctx Δ)) (N := Term.lam A N) B
      = Term.lam (substT (singleTyEnv B) A) (substTT (singleTyEnv B) N) := by
  rw [instT_empty_eq_substTT]
  simp [substTT]

@[simp] theorem instT_tlam_empty_simpler {Δ : TyCtx} {A : Ty ((Δ ,α) ,α)}
    (N : Term ((Δ ,α) ,α) (liftCtx (liftCtx (∅ᶜ : Ctx Δ))) A) (B : Ty Δ) :
    instT (Γ := (∅ᶜ : Ctx Δ)) (N := Term.tlam N) B
      = Term.tlam (substTT (extsT (singleTyEnv B)) N) := by
  rw [instT_empty_eq_substTT]
  simp [substTT]
  rw [show substCtx_exts_lift (singleTyEnv B) (liftCtx (∅ᶜ : Ctx Δ)) =
      (rfl :
          substCtx (extsT (singleTyEnv B)) (liftCtx (liftCtx (∅ᶜ : Ctx Δ)))
            = liftCtx (substCtx (singleTyEnv B) (liftCtx (∅ᶜ : Ctx Δ)))) by rfl]
  rfl

@[simp] theorem instT_substTT_exts_lam_empty {Δ : TyCtx} {A C : Ty ((Δ ,α) ,α)}
    (N : Term ((Δ ,α) ,α) (liftCtx (liftCtx (∅ᶜ : Ctx Δ)) , A) C)
    (B₁ B₂ : Ty Δ) :
    instT (Γ := (∅ᶜ : Ctx Δ))
      (N := substTT (extsT (singleTyEnv B₁)) (Term.lam A N))
      B₂
      = Term.lam
          (substT (singleTyEnv B₂) (substT (extsT (singleTyEnv B₁)) A))
          (substTT (singleTyEnv B₂)
            (substTT (extsT (singleTyEnv B₁)) N)) := by
  rw [instT_empty_eq_substTT]
  simp [substTT]


-- Term-level renaming and substitution.
abbrev Ren {Δ : TyCtx} (Γ Γ' : Ctx Δ) : Type :=
  ∀ {A : Ty Δ}, HasVar Γ A → HasVar Γ' A

abbrev Sub {Δ : TyCtx} (Γ Γ' : Ctx Δ) : Type :=
  ∀ {A : Ty Δ}, HasVar Γ A → Term Δ Γ' A

def idRen {Δ : TyCtx} {Γ : Ctx Δ} : Ren Γ Γ := fun x => x

def extRen {Δ : TyCtx} {Γ Γ' : Ctx Δ} {A : Ty Δ}
    (ρ : Ren Γ Γ') : Ren (Γ , A) (Γ' , A) :=
  fun x =>
    match x with
    | HasVar.Z => HasVar.Z
    | HasVar.S y => HasVar.S (ρ y)

def liftRen {Δ : TyCtx} {Γ Γ' : Ctx Δ} (ρ : Ren Γ Γ') : Ren (liftCtx Γ) (liftCtx Γ') := by
  intro A x
  let rec go {Γ₁ : Ctx Δ} (ρ₁ : Ren Γ₁ Γ') {A : Ty (Δ ,α)} :
      HasVar (liftCtx Γ₁) A → HasVar (liftCtx Γ') A := by
    match Γ₁ with
    | .empty =>
        intro x
        cases x
    | .snoc Γ₂ B =>
        intro x
        cases x with
        | Z =>
            exact renameVar TyVar.S (ρ₁ HasVar.Z)
        | S y =>
            exact go (ρ₁ := fun z => ρ₁ (HasVar.S z)) y
  exact go (ρ₁ := ρ) x

def rename {Δ : TyCtx} {Γ Γ' : Ctx Δ} {A : Ty Δ}
    (ρ : Ren Γ Γ') : Term Δ Γ A → Term Δ Γ' A
  | Term.ttrue => Term.ttrue
  | Term.tfalse => Term.tfalse
  | Term.tzero => Term.tzero
  | Term.tsuc M => Term.tsuc (rename ρ M)
  | Term.tcaseNat L M N => Term.tcaseNat (rename ρ L) (rename ρ M) (rename (extRen ρ) N)
  | Term.tite L M N => Term.tite (rename ρ L) (rename ρ M) (rename ρ N)
  | Term.var x => Term.var (ρ x)
  | Term.lam A N => Term.lam A (rename (extRen ρ) N)
  | Term.app L M => Term.app (rename ρ L) (rename ρ M)
  | Term.tlam N => Term.tlam (rename (liftRen ρ) N)
  | Term.tapp M B => Term.tapp (rename ρ M) B

def renToSub {Δ : TyCtx} {Γ Γ' : Ctx Δ} (ρ : Ren Γ Γ') : Sub Γ Γ' :=
  fun x => Term.var (ρ x)

def wk {Δ : TyCtx} {Γ : Ctx Δ} {A B : Ty Δ} (M : Term Δ Γ A) :
    Term Δ (Γ , B) A :=
  rename (fun x => HasVar.S x) M

def extSub {Δ : TyCtx} {Γ Γ' : Ctx Δ} {A : Ty Δ}
    (σ : Sub Γ Γ') : Sub (Γ , A) (Γ' , A) :=
  fun x =>
    match x with
    | HasVar.Z => Term.var HasVar.Z
    | HasVar.S y => wk (σ y)

def idSub {Δ : TyCtx} {Γ : Ctx Δ} : Sub Γ Γ :=
  renToSub idRen

def liftSub {Δ : TyCtx} {Γ Γ' : Ctx Δ} (σ : Sub Γ Γ') : Sub (liftCtx Γ) (liftCtx Γ') := by
  intro A x
  let rec go {Γ₁ : Ctx Δ} (σ₁ : Sub Γ₁ Γ') {A : Ty (Δ ,α)} :
      HasVar (liftCtx Γ₁) A → Term (Δ ,α) (liftCtx Γ') A := by
    match Γ₁ with
    | .empty =>
        intro x
        cases x
    | .snoc Γ₂ B =>
        intro x
        cases x with
        | Z =>
            exact renameTT TyVar.S (σ₁ HasVar.Z)
        | S y =>
            exact go (σ₁ := fun z => σ₁ (HasVar.S z)) y
  exact go (σ₁ := σ) x

def subst {Δ : TyCtx} {Γ Γ' : Ctx Δ} {A : Ty Δ}
    (σ : Sub Γ Γ') : Term Δ Γ A → Term Δ Γ' A
  | Term.ttrue => Term.ttrue
  | Term.tfalse => Term.tfalse
  | Term.tzero => Term.tzero
  | Term.tsuc M => Term.tsuc (subst σ M)
  | Term.tcaseNat L M N => Term.tcaseNat (subst σ L) (subst σ M) (subst (extSub σ) N)
  | Term.tite L M N => Term.tite (subst σ L) (subst σ M) (subst σ N)
  | Term.var x => σ x
  | Term.lam A N => Term.lam A (subst (extSub σ) N)
  | Term.app L M => Term.app (subst σ L) (subst σ M)
  | Term.tlam N => Term.tlam (subst (liftSub σ) N)
  | Term.tapp M B => Term.tapp (subst σ M) B

def singleEnv {Δ : TyCtx} {Γ : Ctx Δ} {A : Ty Δ}
    (M : Term Δ Γ A) : Sub (Γ , A) Γ :=
  fun x =>
    match x with
    | HasVar.Z => M
    | HasVar.S y => Term.var y

def singleSubst {Δ : TyCtx} {Γ : Ctx Δ} {A B : Ty Δ} :
    Term Δ (Γ , A) B → Term Δ Γ A → Term Δ Γ B :=
  fun N M => subst (singleEnv M) N

notation:67 N " [ " M " ]" => singleSubst N M

end Intrinsic

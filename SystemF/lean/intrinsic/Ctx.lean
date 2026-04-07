import intrinsic.Types

namespace Intrinsic

set_option autoImplicit false

inductive Ctx : TyCtx → Type where
  | empty : {Δ : TyCtx} → Ctx Δ
  | snoc : {Δ : TyCtx} → Ctx Δ → Ty Δ → Ctx Δ
  deriving DecidableEq, Repr

notation "∅ᶜ" => Ctx.empty
infixl:65 " , " => Ctx.snoc

inductive HasVar : {Δ : TyCtx} → Ctx Δ → Ty Δ → Type where
  | Z : {Δ : TyCtx} → {Γ : Ctx Δ} → {A : Ty Δ} → HasVar (Γ , A) A
  | S : {Δ : TyCtx} → {Γ : Ctx Δ} → {A B : Ty Δ} → HasVar Γ A → HasVar (Γ , B) A


def renameCtx {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') : Ctx Δ → Ctx Δ'
  | .empty => .empty
  | .snoc Γ A => .snoc (renameCtx ρ Γ) (renameT ρ A)

def substCtx {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') : Ctx Δ → Ctx Δ'
  | .empty => .empty
  | .snoc Γ A => .snoc (substCtx σ Γ) (substT σ A)

def liftCtx {Δ : TyCtx} : Ctx Δ → Ctx (Δ ,α) :=
  renameCtx TyVar.S

def renameVar {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') :
    ∀ {Γ : Ctx Δ} {A : Ty Δ},
      HasVar Γ A → HasVar (renameCtx ρ Γ) (renameT ρ A)
  := fun {Γ} {A} h =>
      match h with
      | HasVar.Z => HasVar.Z
      | HasVar.S h' => HasVar.S (renameVar ρ h')

def substVar {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') :
    ∀ {Γ : Ctx Δ} {A : Ty Δ},
      HasVar Γ A → HasVar (substCtx σ Γ) (substT σ A)
  := fun {Γ} {A} h =>
      match h with
      | HasVar.Z => HasVar.Z
      | HasVar.S h' => HasVar.S (substVar σ h')

theorem renameCtx_ext_lift {Δ Δ' : TyCtx} (ρ : RenameT Δ Δ') :
    ∀ (Γ : Ctx Δ),
      renameCtx (extT ρ) (liftCtx Γ) = liftCtx (renameCtx ρ Γ)
  | .empty => rfl
  | .snoc Γ A => by
      change
        Ctx.snoc (renameCtx (extT ρ) (liftCtx Γ))
          (renameT (extT ρ) (renameT TyVar.S A))
          =
        Ctx.snoc (liftCtx (renameCtx ρ Γ))
          (renameT TyVar.S (renameT ρ A))
      calc
        Ctx.snoc (renameCtx (extT ρ) (liftCtx Γ))
            (renameT (extT ρ) (renameT TyVar.S A))
            =
          Ctx.snoc (liftCtx (renameCtx ρ Γ))
            (renameT (extT ρ) (renameT TyVar.S A)) := by
              simp [renameCtx_ext_lift ρ Γ]
        _ =
          Ctx.snoc (liftCtx (renameCtx ρ Γ))
            (renameT TyVar.S (renameT ρ A)) := by
              simp [renameT_shift]

theorem substCtx_exts_lift {Δ Δ' : TyCtx} (σ : SubstT Δ Δ') :
    ∀ (Γ : Ctx Δ),
      substCtx (extsT σ) (liftCtx Γ) = liftCtx (substCtx σ Γ)
  | .empty => rfl
  | .snoc Γ A => by
      change
        Ctx.snoc (substCtx (extsT σ) (liftCtx Γ))
          (substT (extsT σ) (renameT TyVar.S A))
          =
        Ctx.snoc (liftCtx (substCtx σ Γ))
          (renameT TyVar.S (substT σ A))
      have hHead : substT (extsT σ) (renameT TyVar.S A) = renameT TyVar.S (substT σ A) := by
        calc
          substT (extsT σ) (renameT TyVar.S A)
              = substT (fun x => extsT σ (TyVar.S x)) A := by
                  exact ren_subT TyVar.S (extsT σ) A
          _ = substT (fun x => renameT TyVar.S (σ x)) A := by rfl
          _ = renameT TyVar.S (substT σ A) := by
                symm
                exact sub_renT TyVar.S σ A
      calc
        Ctx.snoc (substCtx (extsT σ) (liftCtx Γ))
            (substT (extsT σ) (renameT TyVar.S A))
            =
          Ctx.snoc (liftCtx (substCtx σ Γ))
            (substT (extsT σ) (renameT TyVar.S A)) := by
              simp [substCtx_exts_lift σ Γ]
        _ =
          Ctx.snoc (liftCtx (substCtx σ Γ))
            (renameT TyVar.S (substT σ A)) := by
              simp [hHead]

theorem substCtx_single_cancel {Δ : TyCtx} (Γ : Ctx Δ) (B : Ty Δ) :
    substCtx (singleTyEnv B) (liftCtx Γ) = Γ := by
  induction Γ with
  | empty =>
      rfl
  | snoc Γ A ih =>
      change
        Ctx.snoc (substCtx (singleTyEnv B) (liftCtx Γ))
          (substT (singleTyEnv B) (renameT TyVar.S A))
          =
        Ctx.snoc Γ A
      have hHead : substT (singleTyEnv B) (renameT TyVar.S A) = A := by
        calc
          substT (singleTyEnv B) (renameT TyVar.S A)
              = substT (fun x => singleTyEnv B (TyVar.S x)) A := by
                  exact ren_subT TyVar.S (singleTyEnv B) A
          _ = substT idSubstT A := by rfl
          _ = A := sub_idT A
      calc
        Ctx.snoc (substCtx (singleTyEnv B) (liftCtx Γ))
            (substT (singleTyEnv B) (renameT TyVar.S A))
            =
          Ctx.snoc Γ (substT (singleTyEnv B) (renameT TyVar.S A)) := by
              simp [ih]
        _ = Ctx.snoc Γ A := by
              simp [hHead]

end Intrinsic

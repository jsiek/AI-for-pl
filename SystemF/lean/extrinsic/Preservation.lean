import extrinsic.Progress

namespace Extrinsic

def TyRenameWf (Δ Δ' : TyCtx) (ρ : RenameT) : Prop :=
  ∀ {X}, X < Δ → ρ X < Δ'

def TySubstWf (Δ Δ' : TyCtx) (σ : SubstT) : Type :=
  ∀ {X}, X < Δ → WfTy Δ' (σ X)

def RenameWf (Γ Γ' : Ctx) (ρ : Rename) : Type :=
  ∀ {x A}, HasTypeVar Γ x A → HasTypeVar Γ' (ρ x) A

def SubstWf (Δ : TyCtx) (Γ Γ' : Ctx) (σ : Subst) : Type :=
  ∀ {x A}, HasTypeVar Γ x A → HasType Δ Γ' (σ x) A

axiom lookup_map_renameT :
  ∀ {Γ x A ρ},
    HasTypeVar Γ x A →
    HasTypeVar (List.map (renameT ρ) Γ) x (renameT ρ A)

axiom lookup_map_substT :
  ∀ {Γ x A σ},
    HasTypeVar Γ x A →
    HasTypeVar (List.map (substT σ) Γ) x (substT σ A)

axiom tyRenameWf_ext :
  ∀ {Δ Δ' ρ},
    TyRenameWf Δ Δ' ρ →
    TyRenameWf (Δ + 1) (Δ' + 1) (extT ρ)

axiom renameT_preserves_WfTy :
  ∀ {Δ Δ' A ρ},
    WfTy Δ A →
    TyRenameWf Δ Δ' ρ →
    WfTy Δ' (renameT ρ A)

axiom tySubstWf_exts :
  ∀ {Δ Δ' σ},
    TySubstWf Δ Δ' σ →
    TySubstWf (Δ + 1) (Δ' + 1) (extsT σ)

axiom substT_preserves_WfTy :
  ∀ {Δ Δ' A σ},
    WfTy Δ A →
    TySubstWf Δ Δ' σ →
    WfTy Δ' (substT σ A)

axiom typing_renameTT :
  ∀ {Δ Δ' Γ M A ρ},
    TyRenameWf Δ Δ' ρ →
    HasType Δ Γ M A →
    HasType Δ' (List.map (renameT ρ) Γ) (renameTT ρ M) (renameT ρ A)

axiom typing_substTT :
  ∀ {Δ Δ' Γ M A σ},
    TySubstWf Δ Δ' σ →
    HasType Δ Γ M A →
    HasType Δ' (List.map (substT σ) Γ) (substTT σ M) (substT σ A)

axiom typing_single_substTT :
  ∀ {Δ Γ M A B},
    HasType (Δ + 1) (liftCtx Γ) M A →
    WfTy Δ B →
    HasType Δ Γ (substOneTT M B) (substOneT A B)

axiom typing_rename :
  ∀ {Δ Γ Γ' M A ρ},
    RenameWf Γ Γ' ρ →
    HasType Δ Γ M A →
    HasType Δ Γ' (rename ρ M) A

axiom typing_rename_shift :
  ∀ {Δ Γ M A B},
    HasType Δ Γ M A →
    HasType Δ (B :: Γ) (rename Nat.succ M) A

axiom typing_subst :
  ∀ {Δ Γ Γ' M A σ},
    SubstWf Δ Γ Γ' σ →
    HasType Δ Γ M A →
    HasType Δ Γ' (subst σ M) A

axiom typing_single_subst :
  ∀ {Δ Γ N V A B},
    HasType Δ (A :: Γ) N B →
    HasType Δ Γ V A →
    HasType Δ Γ (singleSubst N V) B

axiom preservation :
  ∀ {Δ Γ M N A},
    HasType Δ Γ M A →
    M —→ N →
    HasType Δ Γ N A

axiom multi_preservation :
  ∀ {Δ Γ M N A},
    HasType Δ Γ M A →
    M —↠ N →
    HasType Δ Γ N A

end Extrinsic

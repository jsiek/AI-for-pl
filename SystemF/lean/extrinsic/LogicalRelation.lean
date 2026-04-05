import extrinsic.ProductOmega
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

axiom VRel :
  (A : Ty) → (ρ : RelSub) → (V W : Term) → Value V → Value W → Prop

axiom ERel :
  (A : Ty) → (ρ : RelSub) → Term → Term → Prop

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

axiom VRel_to_ERel :
  ∀ {A ρ V W} (v : Value V) (w : Value W),
    VRel A ρ V W v w → ERel A ρ V W

def GRel_empty : GRel [] emptyRelSub emptyRelEnv := trivial

axiom extendRelEnv_related :
  ∀ {Γ A ρ γ V W},
    GRel Γ ρ γ →
    (v : Value V) →
    (w : Value W) →
    VRel A ρ V W v w →
    GRel (A :: Γ) ρ (extendRelEnv γ V W)

inductive WkRel : RenameT → RelSub → RelSub → Prop where
  | wk_suc {ρ A₁ A₂} (R : Rel A₁ A₂) :
      WkRel Nat.succ ρ (extendRelSub ρ A₁ A₂ R)
  | wk_ext {ξ ρ ρ' B₁ B₂} (S : Rel B₁ B₂) :
      WkRel ξ ρ ρ' →
      WkRel (extT ξ) (extendRelSub ρ B₁ B₂ S) (extendRelSub ρ' B₁ B₂ S)

axiom wk_rhoR_cast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W},
      ρ.rhoR α V W v w → ρ'.rhoR (ξ α) V W v w

axiom wk_rhoR_uncast :
  ∀ {ξ : RenameT} {ρ ρ' : RelSub},
    WkRel ξ ρ ρ' →
    (α : Var) →
    ∀ {V W} {v : Value V} {w : Value W},
      ρ'.rhoR (ξ α) V W v w → ρ.rhoR α V W v w

axiom VRel_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    VRel A ρ V W v w →
    VRel (renameT ξ A) ρ' V W v w

axiom VRel_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    WkRel ξ ρ ρ' →
    VRel (renameT ξ A) ρ' V W v w →
    VRel A ρ V W v w

axiom ERel_rename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    ERel A ρ M N →
    ERel (renameT ξ A) ρ' M N

axiom ERel_unrename_wk :
  ∀ {A : Ty} {ξ : RenameT} {ρ ρ' : RelSub} {M N : Term},
    WkRel ξ ρ ρ' →
    ERel (renameT ξ A) ρ' M N →
    ERel A ρ M N

axiom liftERel :
  ∀ {A A₁ A₂ : Ty} {ρ : RelSub} {γ : RelEnv},
    (R : Rel A₁ A₂) →
    ERel A ρ (γ.gamma1 0) (γ.gamma2 0) →
    ERel (renameT Nat.succ A) (extendRelSub ρ A₁ A₂ R) (γ.gamma1 0) (γ.gamma2 0)

axiom liftRelEnv_related :
  ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv},
    (R : Rel A₁ A₂) →
    GRel Γ ρ γ →
    GRel (liftCtx Γ) (extendRelSub ρ A₁ A₂ R) γ

structure SubstRel (σ : SubstT) (ρ ρ' : RelSub) : Prop where
  varTo :
    ∀ α {V W} {v : Value V} {w : Value W},
      VRel (.var α) ρ' V W v w → VRel (σ α) ρ V W v w
  varFrom :
    ∀ α {V W} {v : Value V} {w : Value W},
      VRel (σ α) ρ V W v w → VRel (.var α) ρ' V W v w

axiom exts_SubstRel :
  ∀ {σ : SubstT} {ρ ρ' : RelSub} {A₁ A₂ : Ty},
    (R : Rel A₁ A₂) →
    SubstRel σ ρ ρ' →
    SubstRel (extsT σ) (extendRelSub ρ A₁ A₂ R) (extendRelSub ρ' A₁ A₂ R)

axiom VRel_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    VRel A ρ' V W v w →
    VRel (substT σ A) ρ V W v w

axiom VRel_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {V W : Term} {v : Value V} {w : Value W},
    SubstRel σ ρ ρ' →
    VRel (substT σ A) ρ V W v w →
    VRel A ρ' V W v w

axiom ERel_subst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    ERel A ρ' M N →
    ERel (substT σ A) ρ M N

axiom ERel_unsubst :
  ∀ {A : Ty} {σ : SubstT} {ρ ρ' : RelSub} {M N : Term},
    SubstRel σ ρ ρ' →
    ERel (substT σ A) ρ M N →
    ERel A ρ' M N

end Extrinsic

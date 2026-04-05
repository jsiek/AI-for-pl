namespace Extrinsic

abbrev Var : Type := Nat
abbrev TyCtx : Type := Nat

inductive Ty where
  | var  : Var → Ty
  | nat  : Ty
  | bool : Ty
  | fn   : Ty → Ty → Ty
  | all  : Ty → Ty
  deriving DecidableEq, Repr

infixr:60 " ⇒ " => Ty.fn

abbrev Ctx : Type := List Ty

abbrev RenameT : Type := Var → Var
abbrev SubstT : Type := Var → Ty

def extT (ρ : RenameT) : RenameT
  | 0 => 0
  | i + 1 => (ρ i) + 1

def renameT (ρ : RenameT) : Ty → Ty
  | .var i => .var (ρ i)
  | .nat => .nat
  | .bool => .bool
  | .fn A B => .fn (renameT ρ A) (renameT ρ B)
  | .all A => .all (renameT (extT ρ) A)

def extsT (σ : SubstT) : SubstT
  | 0 => .var 0
  | i + 1 => renameT Nat.succ (σ i)

def substT (σ : SubstT) : Ty → Ty
  | .var i => σ i
  | .nat => .nat
  | .bool => .bool
  | .fn A B => .fn (substT σ A) (substT σ B)
  | .all A => .all (substT (extsT σ) A)

def singleTyEnv (B : Ty) : SubstT
  | 0 => B
  | i + 1 => .var i

def substOneT (A B : Ty) : Ty :=
  substT (singleTyEnv B) A

def idT : SubstT := Ty.var

def consSubT (A : Ty) (σ : SubstT) : SubstT
  | 0 => A
  | i + 1 => σ i

infixr:61 " •ᵗ " => consSubT

def substCtx (σ : SubstT) : Ctx → Ctx
  | [] => []
  | A :: Γ => substT σ A :: substCtx σ Γ

def liftCtx (Γ : Ctx) : Ctx :=
  Γ.map (renameT Nat.succ)

inductive WfTy : TyCtx → Ty → Type where
  | var  {Δ X} : X < Δ → WfTy Δ (.var X)
  | nat  {Δ}   : WfTy Δ .nat
  | bool {Δ}   : WfTy Δ .bool
  | fn   {Δ A B} : WfTy Δ A → WfTy Δ B → WfTy Δ (.fn A B)
  | all  {Δ A} : WfTy (Δ + 1) A → WfTy Δ (.all A)

inductive HasTypeVar : Ctx → Var → Ty → Type where
  | Z {Γ A} : HasTypeVar (A :: Γ) 0 A
  | S {Γ A B x} : HasTypeVar Γ x A → HasTypeVar (B :: Γ) (x + 1) A

end Extrinsic

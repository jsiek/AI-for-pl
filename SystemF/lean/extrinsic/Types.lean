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

syntax "#" num : term
syntax "#" ident : term
syntax "#(" term ")" : term
macro_rules
  | `(#$n:num) => `(Ty.var $n)
  | `(#$x:ident) => `(Ty.var $x)
  | `(#($t:term)) => `(Ty.var $t)

@[match_pattern] abbrev ℕ : Ty := Ty.nat
@[match_pattern] abbrev 𝔹 : Ty := Ty.bool
infixr:60 " ⇒ " => Ty.fn
prefix:80 "∀ₜ " => Ty.all

abbrev Ctx : Type := List Ty

abbrev RenameT : Type := Var → Var
abbrev SubstT : Type := Var → Ty
abbrev Renameₜ : Type := RenameT
abbrev Substₜ : Type := SubstT

def extT (ρ : RenameT) : RenameT
  | 0 => 0
  | i + 1 => (ρ i) + 1

abbrev extₜ := extT

def renameT (ρ : RenameT) : Ty → Ty
  | #i => #(ρ i)
  | ℕ => ℕ
  | 𝔹 => 𝔹
  | A ⇒ B => (renameT ρ A) ⇒ (renameT ρ B)
  | ∀ₜ A => ∀ₜ (renameT (extT ρ) A)

abbrev renameₜ := renameT

def extsT (σ : SubstT) : SubstT
  | 0 => #0
  | i + 1 => renameT Nat.succ (σ i)

abbrev extsₜ := extsT

def substT (σ : SubstT) : Ty → Ty
  | #i => σ i
  | ℕ => ℕ
  | 𝔹 => 𝔹
  | A ⇒ B => (substT σ A) ⇒ (substT σ B)
  | ∀ₜ A => ∀ₜ (substT (extsT σ) A)

abbrev substₜ := substT

def singleTyEnv (B : Ty) : SubstT
  | 0 => B
  | i + 1 => #i

def substOneT (A B : Ty) : Ty :=
  substT (singleTyEnv B) A

notation:67 A " [ " B " ]ₜ" => substOneT A B

def idT : SubstT := fun i => #i
abbrev idₜ : Substₜ := idT

def consSubT (A : Ty) (σ : SubstT) : SubstT
  | 0 => A
  | i + 1 => σ i

infixr:61 " •ᵗ " => consSubT
infixr:61 " •ₜ " => consSubT

def substCtx (σ : SubstT) : Ctx → Ctx
  | [] => []
  | A :: Γ => substT σ A :: substCtx σ Γ

def liftCtx (Γ : Ctx) : Ctx :=
  Γ.map (renameT Nat.succ)

prefix:100 "⤊" => liftCtx

inductive WfTy : TyCtx → Ty → Type where
  | var  {Δ X} : X < Δ → WfTy Δ (#X)
  | nat  {Δ}   : WfTy Δ ℕ
  | bool {Δ}   : WfTy Δ 𝔹
  | fn   {Δ A B} : WfTy Δ A → WfTy Δ B → WfTy Δ (.fn A B)
  | all  {Δ A} : WfTy (Δ + 1) A → WfTy Δ (∀ₜ A)

inductive HasTypeVar : Ctx → Var → Ty → Type where
  | Z {Γ A} : HasTypeVar (A :: Γ) 0 A
  | S {Γ A B x} : HasTypeVar Γ x A → HasTypeVar (B :: Γ) (x + 1) A

end Extrinsic

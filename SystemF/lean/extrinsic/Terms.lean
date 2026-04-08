import extrinsic.TypeSubst

namespace Extrinsic

-- File Charter:
--   * Core extrinsic System F syntax and static semantics.
--   * Defines terms, renaming/substitution, and typing.
--   * Includes all three renaming/substitution actions:
--       (1) types in types, (2) types in terms, (3) terms in terms.

inductive Term where
  | var   : Var → Term
  | lam   : Extrinsic.Ty → Term → Term
  | app   : Term → Term → Term
  | ttrue : Term
  | tfalse : Term
  | zero  : Term
  | suc   : Term → Term
  | natCase : Term → Term → Term → Term
  | ite   : Term → Term → Term → Term
  | tlam  : Term → Term
  | tapp  : Term → Extrinsic.Ty → Term
  deriving DecidableEq, Repr

syntax "ˋ" num : term
syntax "ˋ" ident : term
syntax "ˋ(" term ")" : term
macro_rules
  | `(ˋ$n:num) => `(Term.var $n)
  | `(ˋ$x:ident) => `(Term.var $x)
  | `(ˋ($t:term)) => `(Term.var $t)

syntax "ƛ[" term "] " term : term
macro_rules
  | `(ƛ[$A] $N) => `(Term.lam $A $N)

prefix:75 "Λ " => Term.tlam
infixl:70 " · " => Term.app
syntax:70 term:71 " ·[ " term:71 " ]" : term
macro_rules
  | `($M ·[ $A ]) => `(Term.tapp $M $A)

notation:max "ˋtrue" => Term.ttrue
notation:max "ˋfalse" => Term.tfalse
notation:max "ˋzero" => Term.zero
prefix:80 "ˋsuc " => Term.suc
notation:max "caseₜ " L " [zero⇒ " M " |suc⇒ " N "]" => Term.natCase L M N
notation:max "ˋif " L " then " M " else " N => Term.ite L M N

def renameTT (ρ : RenameT) : Term → Term
  | ˋi => ˋi
  | Term.lam A N => Term.lam (renameT ρ A) (renameTT ρ N)
  | Term.app L M => Term.app (renameTT ρ L) (renameTT ρ M)
  | ˋtrue => ˋtrue
  | ˋfalse => ˋfalse
  | ˋzero => ˋzero
  | ˋsuc M => ˋsuc (renameTT ρ M)
  | Term.natCase L M N =>
      Term.natCase (renameTT ρ L) (renameTT ρ M) (renameTT ρ N)
  | Term.ite L M N => Term.ite (renameTT ρ L) (renameTT ρ M) (renameTT ρ N)
  | Term.tlam N => Term.tlam (renameTT (extT ρ) N)
  | Term.tapp M A => Term.tapp (renameTT ρ M) (renameT ρ A)

def substTT (σ : SubstT) : Term → Term
  | ˋi => ˋi
  | Term.lam A N => Term.lam (substT σ A) (substTT σ N)
  | Term.app L M => Term.app (substTT σ L) (substTT σ M)
  | ˋtrue => ˋtrue
  | ˋfalse => ˋfalse
  | ˋzero => ˋzero
  | ˋsuc M => ˋsuc (substTT σ M)
  | Term.natCase L M N =>
      Term.natCase (substTT σ L) (substTT σ M) (substTT σ N)
  | Term.ite L M N => Term.ite (substTT σ L) (substTT σ M) (substTT σ N)
  | Term.tlam N => Term.tlam (substTT (extsT σ) N)
  | Term.tapp M A => Term.tapp (substTT σ M) (substT σ A)

def substOneTT (N : Term) (A : Ty) : Term :=
  substTT (singleTyEnv A) N

notation:67 N " [ " A " ]ᵀ" => substOneTT N A

abbrev Rename : Type := Var → Var
abbrev Subst : Type := Var → Term

def ren (ρ : Rename) : Subst :=
  fun i => ˋ(ρ i)

def ext (ρ : Rename) : Rename
  | 0 => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Rename) : Term → Term
  | ˋi => ˋ(ρ i)
  | Term.lam A N => Term.lam A (rename (ext ρ) N)
  | Term.app L M => Term.app (rename ρ L) (rename ρ M)
  | ˋtrue => ˋtrue
  | ˋfalse => ˋfalse
  | ˋzero => ˋzero
  | ˋsuc M => ˋsuc (rename ρ M)
  | Term.natCase L M N =>
      Term.natCase (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  | Term.ite L M N => Term.ite (rename ρ L) (rename ρ M) (rename ρ N)
  | Term.tlam N => Term.tlam (rename ρ N)
  | Term.tapp M A => Term.tapp (rename ρ M) A

def exts (σ : Subst) : Subst
  | 0 => ˋ0
  | i + 1 => rename Nat.succ (σ i)

def up (σ : Subst) : Subst :=
  fun i => renameTT Nat.succ (σ i)

def upT (σ : Subst) : Subst :=
  fun i => rename Nat.succ (σ i)

def id : Subst := fun i => ˋi

def consSub (M : Term) (σ : Subst) : Subst
  | 0 => M
  | i + 1 => σ i

infixr:61 " • " => consSub

def subst (σ : Subst) : Term → Term
  | ˋi => σ i
  | Term.lam A N => Term.lam A (subst (exts σ) N)
  | Term.app L M => Term.app (subst σ L) (subst σ M)
  | ˋtrue => ˋtrue
  | ˋfalse => ˋfalse
  | ˋzero => ˋzero
  | ˋsuc M => ˋsuc (subst σ M)
  | Term.natCase L M N =>
      Term.natCase (subst σ L) (subst σ M) (subst (exts σ) N)
  | Term.ite L M N => Term.ite (subst σ L) (subst σ M) (subst σ N)
  | Term.tlam N => Term.tlam (subst (up σ) N)
  | Term.tapp M A => Term.tapp (subst σ M) A

def singleEnv (M : Term) : Subst
  | 0 => M
  | i + 1 => ˋi

def singleSubst (N M : Term) : Term :=
  subst (singleEnv M) N

infixr:67 " ⨟ " => fun (σ τ : Subst) i => subst τ (σ i)

inductive HasType : TyCtx → Ctx → Term → Ty → Type where
  | t_var {Δ Γ i A} :
      HasTypeVar Γ i A →
      HasType Δ Γ (ˋi) A
  | t_lam {Δ Γ A B N} :
      WfTy Δ A →
      HasType Δ (A :: Γ) N B →
      HasType Δ Γ (Term.lam A N) (A ⇒ B)
  | t_app {Δ Γ A B L M} :
      HasType Δ Γ L (A ⇒ B) →
      HasType Δ Γ M A →
      HasType Δ Γ (Term.app L M) B
  | t_true {Δ Γ} : HasType Δ Γ ˋtrue 𝔹
  | t_false {Δ Γ} : HasType Δ Γ ˋfalse 𝔹
  | t_zero {Δ Γ} : HasType Δ Γ ˋzero ℕ
  | t_suc {Δ Γ M} :
      HasType Δ Γ M ℕ →
      HasType Δ Γ (ˋsuc M) ℕ
  | t_case {Δ Γ A L M N} :
      HasType Δ Γ L ℕ →
      HasType Δ Γ M A →
      HasType Δ (ℕ :: Γ) N A →
      HasType Δ Γ (Term.natCase L M N) A
  | t_if {Δ Γ A L M N} :
      HasType Δ Γ L 𝔹 →
      HasType Δ Γ M A →
      HasType Δ Γ N A →
      HasType Δ Γ (Term.ite L M N) A
  | t_tlam {Δ Γ N A} :
      HasType (Δ + 1) (liftCtx Γ) N A →
      HasType Δ Γ (Term.tlam N) (∀ₜ A)
  | t_tapp {Δ Γ M A B} :
      HasType Δ Γ M (∀ₜ A) →
      WfTy Δ B →
      HasType Δ Γ (Term.tapp M B) (A [ B ]ₜ)

syntax:55 term:56 " ⊢ " term:56 " ⊢ " term:56 " ⦂ " term:56 : term
macro_rules
  | `($Δ ⊢ $Γ ⊢ $M ⦂ $A) => `(HasType $Δ $Γ $M $A)

end Extrinsic

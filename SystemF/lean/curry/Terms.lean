import curry.TypeSubst

-- File Charter:
--   * Core curry System F syntax and static semantics.
--   * Defines terms, renaming/substitution, and typing.
--   * Keeps `renameTT`/`substTT` as identity-on-terms by design.

namespace Curry

inductive Term where
  | var   : Var → Term
  | lam   : Term → Term
  | app   : Term → Term → Term
  | ttrue : Term
  | tfalse : Term
  | zero  : Term
  | suc   : Term → Term
  | natCase : Term → Term → Term → Term
  | ite   : Term → Term → Term → Term
  | tlam  : Term → Term
  | tapp  : Term → Term
  deriving DecidableEq, Repr

syntax "ˋ" num : term
syntax "ˋ" ident : term
syntax "ˋ(" term ")" : term
macro_rules
  | `(ˋ$n:num) => `(Term.var $n)
  | `(ˋ$x:ident) => `(Term.var $x)
  | `(ˋ($t:term)) => `(Term.var $t)

prefix:75 "ƛ " => Term.lam
prefix:75 "Λ " => Term.tlam
infixl:70 " ∙ " => Term.app
notation:70 M " ∙[]" => Term.tapp M
notation:max "ˋtrue" => Term.ttrue
notation:max "ˋfalse" => Term.tfalse
notation:max "ˋzero" => Term.zero
prefix:80 "ˋsuc " => Term.suc
notation:max "caseₜ " L " [zero⇒ " M " |suc⇒ " N "]" => Term.natCase L M N
notation:max "ˋif " L " then " M " else " N => Term.ite L M N

def renameTT (_ρ : RenameT) (M : Term) : Term := M
def substTT (_σ : SubstT) (M : Term) : Term := M
def substOneTT (N : Term) (_A : Ty) : Term := N

abbrev Rename : Type := Var → Var
abbrev Subst : Type := Var → Term

def ext (ρ : Rename) : Rename
  | 0 => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Rename) : Term → Term
  | ˋi => ˋ(ρ i)
  | ƛ N => ƛ (rename (ext ρ) N)
  | (L ∙ M) => (rename ρ L) ∙ (rename ρ M)
  | ˋtrue => ˋtrue
  | ˋfalse => ˋfalse
  | ˋzero => ˋzero
  | ˋsuc M => ˋsuc (rename ρ M)
  | caseₜ L [zero⇒ M |suc⇒ N] => caseₜ (rename ρ L) [zero⇒ (rename ρ M) |suc⇒ (rename (ext ρ) N)]
  | ˋif L then M else N => ˋif (rename ρ L) then (rename ρ M) else (rename ρ N)
  | Λ N => Λ (rename ρ N)
  | M ∙[] => (rename ρ M) ∙[]

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
  | ƛ N => ƛ (subst (exts σ) N)
  | (L ∙ M) => (subst σ L) ∙ (subst σ M)
  | ˋtrue => ˋtrue
  | ˋfalse => ˋfalse
  | ˋzero => ˋzero
  | ˋsuc M => ˋsuc (subst σ M)
  | caseₜ L [zero⇒ M |suc⇒ N] => caseₜ (subst σ L) [zero⇒ (subst σ M) |suc⇒ (subst (exts σ) N)]
  | ˋif L then M else N => ˋif (subst σ L) then (subst σ M) else (subst σ N)
  | Λ N => Λ (subst (up σ) N)
  | M ∙[] => (subst σ M) ∙[]

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
      HasType Δ Γ (ƛ N) (A ⇒ B)
  | t_app {Δ Γ A B L M} :
      HasType Δ Γ L (A ⇒ B) →
      HasType Δ Γ M A →
      HasType Δ Γ (L ∙ M) B
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
      HasType Δ Γ (caseₜ L [zero⇒ M |suc⇒ N]) A
  | t_if {Δ Γ A L M N} :
      HasType Δ Γ L 𝔹 →
      HasType Δ Γ M A →
      HasType Δ Γ N A →
      HasType Δ Γ (ˋif L then M else N) A
  | t_tlam {Δ Γ N A} :
      HasType (Δ + 1) (liftCtx Γ) N A →
      HasType Δ Γ (Λ N) (∀ₜ A)
  | t_tapp {Δ Γ M A B} :
      HasType Δ Γ M (∀ₜ A) →
      WfTy Δ B →
      HasType Δ Γ (M ∙[]) (A [ B ]ₜ)

syntax:55 term:56 " ⊢ " term:56 " ⊢ " term:56 " ⦂ " term:56 : term
macro_rules
  | `($Δ ⊢ $Γ ⊢ $M ⦂ $A) => `(HasType $Δ $Γ $M $A)

end Curry

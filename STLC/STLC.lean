-- Extrinsically typed STLC with de Bruijn indices
namespace STLC

-------------------------------------------------------------------------------
-- 1. SYNTAX & TYPES
-------------------------------------------------------------------------------

inductive Ty where
  | nat : Ty
  | fn  : Ty → Ty → Ty
  deriving BEq

infixr:70 " ⇒ " => Ty.fn

inductive Term where
  | var  : Nat → Term
  | lam  : Ty → Term → Term
  | app  : Term → Term → Term
  | zero : Term
  | suc  : Term → Term
  | case : Term → Term → Term → Term
  -- leave out mu because we want to prove termination

-------------------------------------------------------------------------------
-- 2. RENAMING & PARALLEL SUBSTITUTION
-------------------------------------------------------------------------------

abbrev Rename := Nat → Nat
abbrev Subst := Nat → Term

def ext (ρ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Nat → Nat) : Term → Term
  | .var i      => .var (ρ i)
  | .lam A N    => .lam A (rename (ext ρ) N)
  | .app L M    => .app (rename ρ L) (rename ρ M)
  | .zero       => .zero
  | .suc M      => .suc (rename ρ M)
  | .case L M N => .case (rename ρ L) (rename ρ M) (rename (ext ρ) N)

def exts (σ : Nat → Term) : Nat → Term
  | 0     => .var 0
  | i + 1 => rename (Nat.succ) (σ i)

def subst (σ : Nat → Term) : Term → Term
  | .var i      => σ i
  | .lam A N    => .lam A (subst (exts σ) N)
  | .app L M    => .app (subst σ L) (subst σ M)
  | .zero       => .zero
  | .suc M      => .suc (subst σ M)
  | .case L M N => .case (subst σ L) (subst σ M) (subst (exts σ) N)

def single_subst (N : Term) (M : Term) : Term :=
  let σ : Nat → Term
    | 0     => M
    | i + 1 => .var i
  subst σ N

-------------------------------------------------------------------------------
-- 3. TYPING RELATION (Defined in Type for constructivity)
-------------------------------------------------------------------------------

abbrev Context := List Ty

inductive HasTypeVar : Context → Nat → Ty → Type where
  | Z : ∀ {Γ A}, HasTypeVar (A :: Γ) 0 A
  | S : ∀ {Γ A B i}, HasTypeVar Γ i A → HasTypeVar (B :: Γ) (i + 1) A

inductive HasType : Context → Term → Ty → Type where
  | t_var : ∀ {Γ i A},
      HasTypeVar Γ i A → HasType Γ (.var i) A
  | t_lam : ∀ {Γ A B N},
      HasType (A :: Γ) N B → HasType Γ (.lam A N) (A ⇒ B)
  | t_app : ∀ {Γ A B L M},
      HasType Γ L (A ⇒ B) → HasType Γ M A → HasType Γ (.app L M) B
  | t_zero : ∀ {Γ},
      HasType Γ .zero .nat
  | t_suc : ∀ {Γ M},
      HasType Γ M .nat → HasType Γ (.suc M) .nat
  | t_case : ∀ {Γ A L M N},
      HasType Γ L .nat →
      HasType Γ M A →
      HasType (.nat :: Γ) N A →
      HasType Γ (.case L M N) A

-------------------------------------------------------------------------------
-- 4. VALUES & REDUCTION
-------------------------------------------------------------------------------

inductive Value : Term → Type where
  | v_lam  : ∀ {A N}, Value (.lam A N)
  | v_zero : Value .zero
  | v_suc  : ∀ {V}, Value V → Value (.suc V)

inductive Step : Term → Term → Type where
  | xi_app1 : ∀ {L L' M}, Step L L' → Step (.app L M) (.app L' M)
  | xi_app2 : ∀ {V M M'}, Value V → Step M M' → Step (.app V M) (.app V M')
  | β_lam   : ∀ {A N W}, Value W → Step (.app (.lam A N) W) (single_subst N W)
  | xi_suc  : ∀ {M M'}, Step M M' → Step (.suc M) (.suc M')
  | xi_case : ∀ {L L' M N}, Step L L' → Step (.case L M N) (.case L' M N)
  | β_zero  : ∀ {M N}, Step (.case .zero M N) M
  | β_suc   : ∀ {V M N}, Value V → Step (.case (.suc V) M N) (single_subst N V)

infix:20 " —→ " => Step


-------------------------------------------------------------------------------
-- 7. MULTI-STEP REDUCTION
-------------------------------------------------------------------------------

/-- Multi-step reduction (reflexive-transitive closure of Step) -/
inductive MultiStep : Term → Term → Type where
  | refl (M : Term) : MultiStep M M
  | step (L : Term) {M N : Term} : Step L M → MultiStep M N → MultiStep L N

infix:20 " —↠ " => MultiStep

-- Notation for the end of a reduction sequence
postfix:max " ∎" => MultiStep.refl

-- Notation for a single step in a reduction sequence
notation:2 L " —→⟨ " s " ⟩ " ms => MultiStep.step L s ms

-- Notation to begin a reduction sequence
notation:1 "begin " ms => ms

/-- Transitivity of multi-step reduction -/
def multi_trans {M N L : Term} : (M —↠ N) → (N —↠ L) → (M —↠ L)
  | .refl _, ms2 => ms2
  | .step _ s ms1', ms2 => .step _ s (multi_trans ms1' ms2)

end STLC

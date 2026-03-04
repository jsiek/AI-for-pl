namespace Lambda

-------------------------------------------------------------------------------
-- 1. SYNTAX
-------------------------------------------------------------------------------

inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term

-------------------------------------------------------------------------------
-- 2. RENAMING & PARALLEL SUBSTITUTION
-------------------------------------------------------------------------------

abbrev Rename := Nat → Nat
abbrev Subst := Nat → Term

def ext (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Nat → Nat) : Term → Term
  | .var i => .var (ρ i)
  | .lam N => .lam (rename (ext ρ) N)
  | .app L M => .app (rename ρ L) (rename ρ M)

def exts (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | i + 1 => rename Nat.succ (σ i)

def subst (σ : Nat → Term) : Term → Term
  | .var i => σ i
  | .lam N => .lam (subst (exts σ) N)
  | .app L M => .app (subst σ L) (subst σ M)

def single_subst (N : Term) (M : Term) : Term :=
  let σ : Nat → Term
    | 0 => M
    | i + 1 => .var i
  subst σ N

-------------------------------------------------------------------------------
-- 3. VALUES
-------------------------------------------------------------------------------

inductive Value : Term → Type where
  | var : ∀ {i}, Value (.var i)
  | lam : ∀ {N}, Value (.lam N)

end Lambda

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
-- 3. NEUTRAL & NORMAL TERMS
-------------------------------------------------------------------------------

mutual

inductive Neutral : Term → Type where
  | var : ∀ {i}, Neutral (.var i)
  | app : ∀ {L M}, Neutral L → Normal M → Neutral (.app L M)

inductive Normal : Term → Type where
  | neu : ∀ {M}, Neutral M → Normal M
  | lam : ∀ {N}, Normal N → Normal (.lam N)

end

-------------------------------------------------------------------------------
-- 4. REDUCTION
-------------------------------------------------------------------------------

inductive Step : Term → Term → Type where
  | xi_lam : ∀ {N N'}, Step N N' → Step (.lam N) (.lam N')
  | xi_app1 : ∀ {L L' M}, Step L L' → Step (.app L M) (.app L' M)
  | xi_app2 : ∀ {L M M'}, Step M M' → Step (.app L M) (.app L M')
  | β_lam : ∀ {N W}, Step (.app (.lam N) W) (single_subst N W)

infix:20 " —→ " => Step

-------------------------------------------------------------------------------
-- 5. MULTI-STEP REDUCTION
-------------------------------------------------------------------------------

inductive MultiStep : Term → Term → Type where
  | refl (M : Term) : MultiStep M M
  | step (L : Term) {M N : Term} : Step L M → MultiStep M N → MultiStep L N

infix:20 " —↠ " => MultiStep

postfix:max " ∎" => MultiStep.refl
notation:2 L " —→⟨ " s " ⟩ " ms => MultiStep.step L s ms
notation:1 "begin " ms => ms

def multi_trans {M N L : Term} : (M —↠ N) → (N —↠ L) → (M —↠ L)
  | .refl _, ms2 => ms2
  | .step _ s ms1', ms2 => .step _ s (multi_trans ms1' ms2)

end Lambda

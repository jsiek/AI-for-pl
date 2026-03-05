import STLC

namespace Subst

open STLC

-------------------------------------------------------------------------------
-- 1. SIGMA-CALCULUS DEFINITIONS
-------------------------------------------------------------------------------

abbrev Ren := Nat → Nat
abbrev Sub := Nat → Term

/-- Substitution sequencing (σ ⨟ τ): Applying τ to the result of σ -/
def seq (σ₁ : Sub) (σ₂ : Sub) : Sub :=
  fun i => subst σ₂ (σ₁ i)

infixr:50 " ⨟ " => seq

/-- Substitution for single term at index 1: N 〔 M 〕 -/
def subst_one_at_one (N : Term) (M : Term) : Term :=
  subst (exts (fun i => match i with | 0 => M | j+1 => .var j)) N

-------------------------------------------------------------------------------
-- 2. CORE SUBSTITUTION THEOREMS
-------------------------------------------------------------------------------

/-- Lemma: Composition of extensions is the extension of the composition.
    Corresponds to `ext-equiv` and `Z-shiftʳ` in the Agda source[cite: 1]. -/
theorem ext_comp (ρ₁ ρ₂ : Ren) :
  (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ n => rfl

/-- rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M -/
theorem rename_rename_commute (ρ₁ ρ₂ : Ren) (M : Term) :
  rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M := by
  induction M generalizing ρ₁ ρ₂ with
  | var i => 
    -- Variables are trivially renamed[cite: 8].
    rfl
  | lam A N ih =>
    -- For lambdas, we apply the inductive hypothesis to the body N.
    -- We use ext_comp to rewrite the composition of extended environments.
    simp only [rename]
    rw [ih (ext ρ₁) (ext ρ₂), ext_comp]
  | app L R ihL ihR =>
    -- Applications distribute the renaming to both sides[cite: 10].
    simp only [rename]
    rw [ihL, ihR]
  | zero => 
    -- Zero is a constant, so it remains unchanged[cite: 11].
    rfl
  | suc M ih =>
    -- Successor simply applies to its inner term[cite: 12].
    simp only [rename]
    rw [ih]
  | case L M N ihL ihM ihN =>
    -- Case statements distribute to all three branches[cite: 13].
    -- The N branch binds a variable, so we use ext_comp again.
    simp only [rename]
    rw [ihL, ihM, ihN (ext ρ₁) (ext ρ₂), ext_comp]

/-- Helper lemma: composing `ext` and `exts` is equivalent to extending the composition. -/
theorem exts_ext_comp (ρ : Ren) (τ : Sub) :
  (fun i => exts τ (ext ρ i)) = exts (fun i => τ (ρ i)) := by
  funext i
  cases i with
  | zero => 
    -- exts τ (ext ρ 0) = exts τ 0 = .var 0
    -- exts (fun i => τ (ρ i)) 0 = .var 0
    rfl
  | succ n => 
    -- exts τ (ext ρ (n+1)) = exts τ (ρ n + 1) = rename Nat.succ (τ (ρ n))
    -- exts (fun i => τ (ρ i)) (n+1) = rename Nat.succ (τ (ρ n))
    rfl

/-- Renaming followed by substitution is equivalent to a composed substitution. -/
theorem rename_subst_commute (ρ : Ren) (τ : Sub) (M : Term) :
  subst τ (rename ρ M) = subst (fun i => τ (ρ i)) M := by
  induction M generalizing ρ τ with
  | var i => 
    -- Variables evaluate directly to τ (ρ i) on both sides
    rfl
  | lam A N ih =>
    -- Under a lambda, we use the inductive hypothesis and our helper lemma
    simp only [rename, subst]
    rw [ih (ext ρ) (exts τ), exts_ext_comp]
  | app L R ihL ihR =>
    -- Application distributes to both subterms
    simp only [rename, subst]
    rw [ihL, ihR]
  | zero => 
    -- Constants remain unchanged
    rfl
  | suc M ih =>
    simp only [rename, subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    -- Case statements distribute; the N branch binds a variable
    simp only [rename, subst]
    rw [ihL, ihM, ihN (ext ρ) (exts τ), exts_ext_comp]

/-- Helper 1: Commuting `ext` (renaming extension) and `exts` (substitution extension). -/
theorem ext_exts_comp (ρ : Ren) (τ : Sub) :
  (fun i => rename (ext ρ) (exts τ i)) = exts (fun i => rename ρ (τ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    -- Focus on the `succ` case and use `rename_rename_commute` twice
    change rename (ext ρ) (rename Nat.succ (τ j)) = rename Nat.succ (rename ρ (τ j))
    rw [rename_rename_commute, rename_rename_commute]
    rfl

/-- Helper 2: Renaming a substitution is equivalent to substituting with renamed terms. -/
theorem rename_subst (ρ : Ren) (τ : Sub) (M : Term) :
  rename ρ (subst τ M) = subst (fun i => rename ρ (τ i)) M := by
  induction M generalizing ρ τ with
  | var i => rfl
  | lam A N ih =>
    simp only [rename, subst]
    rw [ih, ext_exts_comp]
  | app L R ihL ihR =>
    simp only [rename, subst]
    rw [ihL, ihR]
  | zero => rfl
  | suc M ih =>
    simp only [rename, subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    simp only [rename, subst]
    rw [ihL, ihM, ihN, ext_exts_comp]

/-- Helper 3: Extending a composed substitution is the composition of extended substitutions. -/
theorem exts_seq (σ τ : Sub) :
  (exts σ ⨟ exts τ) = exts (σ ⨟ τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    -- Simplify to expose the inner `rename` and `subst` applications
    dsimp [seq, exts]
    -- Use the previously proven commutation lemmas on both sides
    rw [rename_subst_commute, rename_subst]
    rfl

/-- Main Theorem: Double substitution is equivalent to substituting a composed mapping. -/
theorem sub_sub (σ τ : Sub) (M : Term) :
  subst τ (subst σ M) = subst (σ ⨟ τ) M := by
  induction M generalizing σ τ with
  | var i => 
    rfl
  | lam A N ih =>
    simp only [subst]
    rw [ih, exts_seq]
  | app L R ihL ihR =>
    simp only [subst]
    rw [ihL, ihR]
  | zero => 
    rfl
  | suc M ih =>
    simp only [subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    simp only [subst]
    rw [ihL, ihM, ihN, exts_seq]

/-- Helper: Substitution with the variable constructor is the identity. -/
theorem subst_id (M : Term) : subst Term.var M = M := by
  induction M with
  | var i => rfl
  | lam A N ih =>
    simp only [subst]
    have h_exts : exts Term.var = Term.var := by
      funext i; cases i <;> rfl
    rw [h_exts, ih]
  | app L R ihL ihR =>
    simp only [subst]
    rw [ihL, ihR]
  | zero => rfl
  | suc M ih =>
    simp only [subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    simp only [subst]
    have h_exts : exts Term.var = Term.var := by
      funext i; cases i <;> rfl
    rw [h_exts, ihL, ihM, ihN]

/-- The main substitution lemma: M[N][L] = M[L][N[L]] -/
theorem substitution {M N L : Term} :
  single_subst (single_subst M N) L =
    single_subst (subst_one_at_one M L) (single_subst N L) := by
  -- Unfold the custom substitution definitions into raw `subst` applications
  dsimp only [single_subst, subst_one_at_one]
  
  -- Apply our `sub_sub` lemma to both sides to fuse the double substitutions
  rw [sub_sub, sub_sub]
  
  -- We prove the composed substitution environments are pointwise identical.
  -- Using congrArg forces Lean to ONLY strip the outer `subst ... M`,
  -- avoiding `congr`'s aggressive and destructive unifications.
  apply congrArg (fun (σ : Sub) => subst σ M)
  funext i
  cases i with
  | zero =>
    -- Case i = 0: Both evaluate definitionally to `single_subst N L`
    rfl
  | succ j =>
    cases j with
    | zero =>
      -- Case i = 1: 
      -- The LHS evaluates cleanly to `L`.
      -- The RHS evaluates to `subst τ (rename Nat.succ L)`.
      -- We use `change` to bypass brittle unfolding tactics and let the kernel verify it.
      change L = subst (fun x => match x with | 0 => single_subst N L | y+1 => Term.var y) (rename Nat.succ L)
      
      -- Flip the equation to match the commutation lemma
      symm
      
      -- Commute the renaming and substitution on the RHS
      rw [rename_subst_commute]
      
      -- After commutation, the mapped function evaluates exactly to `Term.var`.
      change subst Term.var L = L
      
      -- Apply our identity helper lemma backwards
      exact subst_id L
    | succ k =>
      -- Case i = k + 2: Both mappings shift and evaluate nicely to `.var k`
      rfl

/-- Substituting into an extended substitution is equivalent to a single mapping. -/
theorem exts_sub_cons {σ : Sub} {N : Term} {V : Term} :
  single_subst (subst (exts σ) N) V =
    subst (fun i => match i with | 0 => V | j+1 => σ j) N := by
  -- Unfold the definition of single_subst
  dsimp only [single_subst]
  
  -- Fuse the double substitution into a single composed substitution
  rw [sub_sub]
  
  -- Apply congrArg to isolate the substitution environments
  apply congrArg (fun (env : Sub) => subst env N)
  funext i
  cases i with
  | zero => 
    -- Case i = 0: Both evaluate to `V`
    rfl
  | succ j =>
    -- Case i = j + 1:
    -- The LHS evaluates to `subst τ (rename Nat.succ (σ j))`
    dsimp only [seq, exts]
    
    -- Commute the rename and subst operations
    rw [rename_subst_commute]
    
    -- The composed mapping function strictly evaluates to `Term.var`
    change subst Term.var (σ j) = σ j
    
    -- Close the goal with our identity lemma
    exact subst_id (σ j)

end Subst

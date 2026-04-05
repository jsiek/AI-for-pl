namespace SystemF

-------------------------------------------------------------------------------
-- SYNTAX & TYPES
-------------------------------------------------------------------------------

inductive Ty where
  | tvar : Nat → Ty
  | nat  : Ty
  | fn   : Ty → Ty → Ty
  | univ : Ty → Ty             -- ∀X. A
  deriving BEq

infixr:70 " ⇒ " => Ty.fn

inductive Raw where
  | var  : Nat → Raw
  | lam  : Ty → Raw → Raw
  | app  : Raw → Raw → Raw
  | zero : Raw
  | suc  : Raw → Raw
  | case : Raw → Raw → Raw → Raw
  | tlam : Raw → Raw           -- ΛX. N (Binds a TYPE variable)
  | tapp : Raw → Ty → Raw      -- M [A] (Applies a TYPE)

-------------------------------------------------------------------------------
-- ABBREVIATIONS
-------------------------------------------------------------------------------

abbrev Rename := Nat → Nat
abbrev Subst  := Nat → Raw
abbrev TySubst := Nat → Ty

-------------------------------------------------------------------------------
-- TYPE SUBSTITUTION (Types into Types)
-------------------------------------------------------------------------------

def extTy (ρ : Rename) : Rename
  | 0     => 0
  | i + 1 => (ρ i) + 1

def renameTy (ρ : Rename) : Ty → Ty
  | .tvar X   => .tvar (ρ X)
  | .nat      => .nat
  | .fn A B   => .fn (renameTy ρ A) (renameTy ρ B)
  | .univ A   => .univ (renameTy (extTy ρ) A)

def extsTy (σ : TySubst) : TySubst
  | 0     => .tvar 0
  | X + 1 => renameTy (fun i => i + 1) (σ X)

def substTy (σ : TySubst) : Ty → Ty
  | .tvar X   => σ X
  | .nat      => .nat
  | .fn A B   => .fn (substTy σ A) (substTy σ B)
  | .univ A   => .univ (substTy (extsTy σ) A)

-------------------------------------------------------------------------------
-- TYPE-INTO-TERM SUBSTITUTION (Types into Terms)
-------------------------------------------------------------------------------

def renameTyInRaw (ρ : Rename) : Raw → Raw
  | .var i      => .var i                 -- Term vars are untouched
  | .lam A N    => .lam (renameTy ρ A) (renameTyInRaw ρ N)
  | .app L M    => .app (renameTyInRaw ρ L) (renameTyInRaw ρ M)
  | .zero       => .zero
  | .suc M      => .suc (renameTyInRaw ρ M)
  | .case L M N => .case (renameTyInRaw ρ L) (renameTyInRaw ρ M) (renameTyInRaw ρ N)
  | .tlam N     => .tlam (renameTyInRaw (extTy ρ) N) -- Binds a type var, so extend ρ!
  | .tapp M A   => .tapp (renameTyInRaw ρ M) (renameTy ρ A)

def substTyInRaw (σ : TySubst) : Raw → Raw
  | .var i      => .var i                 -- Term vars are untouched
  | .lam A N    => .lam (substTy σ A) (substTyInRaw σ N)
  | .app L M    => .app (substTyInRaw σ L) (substTyInRaw σ M)
  | .zero       => .zero
  | .suc M      => .suc (substTyInRaw σ M)
  | .case L M N => .case (substTyInRaw σ L) (substTyInRaw σ M) (substTyInRaw σ N)
  | .tlam N     => .tlam (substTyInRaw (extsTy σ) N) -- Binds a type var, so extend σ!
  | .tapp M A   => .tapp (substTyInRaw σ M) (substTy σ A)

-------------------------------------------------------------------------------
-- TERM SUBSTITUTION (Terms into Terms)
-------------------------------------------------------------------------------

def ext (ρ : Rename) : Rename
  | 0     => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Rename) : Raw → Raw
  | .var i      => .var (ρ i)
  | .lam A N    => .lam A (rename (ext ρ) N)
  | .app L M    => .app (rename ρ L) (rename ρ M)
  | .zero       => .zero
  | .suc M      => .suc (rename ρ M)
  | .case L M N => .case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  | .tlam N     => .tlam (rename ρ N)     -- Does NOT bind a term var, no `ext`!
  | .tapp M A   => .tapp (rename ρ M) A

def exts (σ : Subst) : Subst
  | 0     => .var 0
  | i + 1 => rename (fun x => x + 1) (σ i)

/-- Shifts the type variables inside all terms of a term substitution by 1. -/
def shiftSubstTy (σ : Subst) : Subst :=
  fun i => renameTyInRaw (fun x => x + 1) (σ i)

/-- CORRECTED TERM SUBSTITUTION -/
def subst (σ : Subst) : Raw → Raw
  | .var i      => σ i
  | .lam A N    => .lam A (subst (exts σ) N)
  | .app L M    => .app (subst σ L) (subst σ M)
  | .zero       => .zero
  | .suc M      => .suc (subst σ M)
  | .case L M N => .case (subst σ L) (subst σ M) (subst (exts σ) N)
  | .tlam N     => .tlam (subst (shiftSubstTy σ) N)
  | .tapp M A   => .tapp (subst σ M) A

-------------------------------------------------------------------------------
-- SINGLE SUBSTITUTION (For Beta Reductions)
-------------------------------------------------------------------------------

/-- Substitutes a type `B` for the type variable `0` inside a type `A`, 
    decrementing all other free type variables. 
    (Used for type-level beta reduction if you ever add type operators, 
    or when evaluating type applications in typing rules). -/
def singleSubstTy (A : Ty) (B : Ty) : Ty :=
  substTy (fun i => match i with
    | 0     => B
    | j + 1 => .tvar j) A

/-- Substitutes a term `N` for the term variable `0` inside a term `M`, 
    decrementing all other free term variables. 
    (Used for standard term-level beta reduction: `(λA. M) N ⟶ M[N/0]`). -/
def singleSubst (M : Raw) (N : Raw) : Raw :=
  subst (fun i => match i with
    | 0     => N
    | j + 1 => .var j) M

/-- Substitutes a type `B` for the type variable `0` inside a term `M`, 
    decrementing all other free type variables in `M`. 
    (Used for polymorphic beta reduction: `(Λ. M) [B] ⟶ M[B/0]`). -/
def singleSubstTyInRaw (M : Raw) (B : Ty) : Raw :=
  substTyInRaw (fun i => match i with
    | 0     => B
    | j + 1 => .tvar j) M

-------------------------------------------------------------------------------
-- WELL-FORMED TYPES
-------------------------------------------------------------------------------

/-- WfTy Δ A means that all free type variables in A are < Δ -/
inductive WfTy : Nat → Ty → Prop where
  | wf_tvar {Δ X : Nat} : X < Δ → WfTy Δ (.tvar X)
  | wf_nat  {Δ : Nat}   : WfTy Δ .nat
  | wf_fn   {Δ : Nat} {A B : Ty} : WfTy Δ A → WfTy Δ B → WfTy Δ (.fn A B)
  | wf_univ {Δ : Nat} {A : Ty}   : WfTy (Δ + 1) A → WfTy Δ (.univ A)

-------------------------------------------------------------------------------
-- TYPING CONTEXTS
-------------------------------------------------------------------------------

abbrev Context := List Ty

inductive HasTypeVar : Context → Nat → Ty → Prop where
  | Z {Γ A}   : HasTypeVar (A :: Γ) 0 A
  | S {Γ x A B} : HasTypeVar Γ x A → HasTypeVar (B :: Γ) (x + 1) A

def shiftContextTy (Γ : Context) : Context :=
  Γ.map (renameTy (fun i => i + 1))

-------------------------------------------------------------------------------
-- TYPING RULES
-------------------------------------------------------------------------------

/-- 
  The Typing Judgment for System F.
  `HasType Δ Γ M A` means term `M` has type `A` in type context `Δ` and term context `Γ`.
-/
inductive HasType : Nat → Context → Raw → Ty → Prop where
  
  -- Variables
  | t_var {Δ Γ x A} : 
      HasTypeVar Γ x A → 
      HasType Δ Γ (.var x) A
      
  -- Term Abstraction (STLC λ)
  | t_lam {Δ Γ A B N} : 
      WfTy Δ A →                         
      HasType Δ (A :: Γ) N B →           
      HasType Δ Γ (.lam A N) (.fn A B)
      
  -- Term Application
  | t_app {Δ Γ L M A B} : 
      HasType Δ Γ L (.fn A B) → 
      HasType Δ Γ M A → 
      HasType Δ Γ (.app L M) B
      
  -- Base Type (Nat)
  | t_zero {Δ Γ} : 
      HasType Δ Γ .zero .nat
      
  | t_suc {Δ Γ M} : 
      HasType Δ Γ M .nat → 
      HasType Δ Γ (.suc M) .nat
      
  | t_case {Δ Γ L M N B} : 
      HasType Δ Γ L .nat → 
      HasType Δ Γ M B → 
      HasType Δ (.nat :: Γ) N B →        
      HasType Δ Γ (.case L M N) B
      
  -- Type Abstraction (System F Λ)
  | t_tlam {Δ Γ N A} : 
      HasType (Δ + 1) (shiftContextTy Γ) N A → 
      HasType Δ Γ (.tlam N) (.univ A)
      
-- Type Application
  | t_tapp {Δ Γ M A B} : 
      HasType Δ Γ M (.univ A) → 
      WfTy Δ B →                         
      HasType Δ Γ (.tapp M B) (singleSubstTy A B)

-------------------------------------------------------------------------------
-- WELL-FORMED TYPE RENAMING
-------------------------------------------------------------------------------

/-- A renaming is well-formed if it maps variables < Δ to variables < Δ' -/
def WfRename (Δ Δ' : Nat) (ρ : Rename) : Prop :=
  ∀ {x}, x < Δ → ρ x < Δ'

/-- Extending a well-formed renaming preserves its well-formedness -/
theorem extTy_preserves_WfRename {Δ Δ' : Nat} {ρ : Rename} 
  (hρ : WfRename Δ Δ' ρ) : WfRename (Δ + 1) (Δ' + 1) (extTy ρ) := by
  intro x hx
  cases x with
  | zero => 
    -- 0 < Δ' + 1
    exact Nat.zero_lt_succ _
  | succ x' =>
    -- ρ x' + 1 < Δ' + 1
    have h1 : x' < Δ := Nat.lt_of_succ_lt_succ hx
    have h2 : ρ x' < Δ' := hρ h1
    exact Nat.succ_lt_succ h2

/-- Renaming a well-formed type yields a well-formed type -/
theorem renameTy_preserves_WfTy {Δ Δ' : Nat} {A : Ty} {ρ : Rename} 
  (hA : WfTy Δ A) (hρ : WfRename Δ Δ' ρ) : WfTy Δ' (renameTy ρ A) := by
  induction hA generalizing Δ' ρ with
  | wf_tvar hx => 
    exact .wf_tvar (hρ hx)
  | wf_nat => 
    exact .wf_nat
  | wf_fn _ _ ih1 ih2 => 
    exact .wf_fn (ih1 hρ) (ih2 hρ)
  | wf_univ _ ih => 
    exact .wf_univ (ih (extTy_preserves_WfRename hρ))

-------------------------------------------------------------------------------
-- WELL-FORMED TYPE SUBSTITUTION
-------------------------------------------------------------------------------

/-- A substitution is well-formed if it maps variables < Δ to well-formed types in Δ' -/
def WfTySubst (Δ Δ' : Nat) (σ : TySubst) : Prop :=
  ∀ {x}, x < Δ → WfTy Δ' (σ x)

/-- Extending a well-formed substitution preserves its well-formedness -/
theorem extsTy_preserves_WfTySubst {Δ Δ' : Nat} {σ : TySubst} 
  (hσ : WfTySubst Δ Δ' σ) : WfTySubst (Δ + 1) (Δ' + 1) (extsTy σ) := by
  intro x hx
  cases x with
  | zero => 
    -- .tvar 0 is well-formed in Δ' + 1
    exact .wf_tvar (Nat.zero_lt_succ _)
  | succ x' =>
    -- renameTy (+1) (σ x') is well-formed in Δ' + 1
    have h1 : x' < Δ := Nat.lt_of_succ_lt_succ hx
    have h2 : WfTy Δ' (σ x') := hσ h1
    
    -- We need to show that shifting by 1 is a valid WfRename
    have h_ren : WfRename Δ' (Δ' + 1) (fun i => i + 1) := by
      intro i hi
      exact Nat.succ_lt_succ hi
      
    exact renameTy_preserves_WfTy h2 h_ren

/-- Substituting into a well-formed type yields a well-formed type -/
theorem substTy_preserves_WfTy {Δ Δ' : Nat} {A : Ty} {σ : TySubst} 
  (hA : WfTy Δ A) (hσ : WfTySubst Δ Δ' σ) : WfTy Δ' (substTy σ A) := by
  induction hA generalizing Δ' σ with
  | wf_tvar hx => 
    exact hσ hx
  | wf_nat => 
    exact .wf_nat
  | wf_fn _ _ ih1 ih2 => 
    exact .wf_fn (ih1 hσ) (ih2 hσ)
  | wf_univ _ ih => 
    exact .wf_univ (ih (extsTy_preserves_WfTySubst hσ))

-------------------------------------------------------------------------------
-- WELL-FORMED TERM RENAMING
-------------------------------------------------------------------------------

/-- A renaming is well-formed if it maps variables of type A to variables of type A -/
def WfRenameTrm (Γ Γ' : Context) (ρ : Rename) : Prop :=
  ∀ {x A}, HasTypeVar Γ x A → HasTypeVar Γ' (ρ x) A

/-- Extending a well-formed term renaming preserves its well-formedness -/
theorem ext_preserves_WfRenameTrm {Γ Γ' : Context} {B : Ty} {ρ : Rename} 
  (hρ : WfRenameTrm Γ Γ' ρ) : WfRenameTrm (B :: Γ) (B :: Γ') (ext ρ) := by
  intro x A hx
  cases hx with
  | Z => 
    -- ext ρ 0 = 0, and index 0 has type B in (B :: Γ')
    exact .Z
  | S hx' => 
    -- ext ρ (x' + 1) = ρ x' + 1
    exact .S (hρ hx')

-------------------------------------------------------------------------------
-- CONTEXT SHIFT PRESERVES LOOKUPS
-------------------------------------------------------------------------------

/-- Mapping any type renaming over the context preserves variable lookups. -/
theorem HasTypeVar_map_renameTy {Γ : Context} {x : Nat} {A : Ty} {ρ : Rename}
  (h : HasTypeVar Γ x A) : HasTypeVar (Γ.map (renameTy ρ)) x (renameTy ρ A) := by
  induction h with
  | Z => 
    -- Γ.map (renameTy ρ) on (A :: Γ) evaluates to (renameTy ρ A) :: (Γ.map ...)
    -- which perfectly matches the .Z constructor.
    exact .Z
  | S _ ih => 
    -- By induction, x has type (renameTy ρ A) in the mapped tail.
    -- Applying .S adds the mapped head (renameTy ρ B) to the context.
    exact .S ih

/-- Specifically, shiftContextTy preserves lookups while shifting the type by 1. -/
theorem shiftContextTy_preserves_lookup {Γ : Context} {x : Nat} {A : Ty}
  (h : HasTypeVar Γ x A) : HasTypeVar (shiftContextTy Γ) x (renameTy (fun i => i + 1) A) := by
  -- shiftContextTy Γ is definitionally exactly Γ.map (renameTy (fun i => i + 1))
  exact HasTypeVar_map_renameTy h

-------------------------------------------------------------------------------
-- SHIFT CONTEXT INVERSION
-------------------------------------------------------------------------------

/-- If we found a type in a shifted context, it must be the shifted version 
    of a type from the original context. -/
theorem shiftContextTy_inv {Γ : Context} {x : Nat} {A' : Ty}
  (h : HasTypeVar (shiftContextTy Γ) x A') : 
  ∃ A, HasTypeVar Γ x A ∧ A' = renameTy (fun i => i + 1) A := by
  induction Γ generalizing x A' with
  | nil => 
    -- Empty context cannot contain variables
    cases h
  | cons B Γ ih =>
    cases h with
    | Z => exact ⟨B, .Z, rfl⟩
    | S h_tail =>
      let ⟨A, hA, heq⟩ := ih h_tail
      rw [heq]
      exact ⟨A, .S hA, rfl⟩

/-- Shifting both contexts preserves the well-formedness of a term renaming. -/
theorem shiftContextTy_preserves_WfRenameTrm {Γ Γ' : Context} {ρ : Rename}
  (hρ : WfRenameTrm Γ Γ' ρ) : WfRenameTrm (shiftContextTy Γ) (shiftContextTy Γ') ρ := by
  intro x A' hx
  -- Extract the original unshifted type A from Γ
  let ⟨A, hA, heq⟩ := shiftContextTy_inv hx
  rw [heq]
  -- Apply our previous lookup preservation theorem
  exact shiftContextTy_preserves_lookup (hρ hA)

-------------------------------------------------------------------------------
-- RENAME PRESERVES HASTYPE
-------------------------------------------------------------------------------

theorem rename_preserves_HasType {Δ : Nat} {Γ Γ' : Context} {M : Raw} {A : Ty} {ρ : Rename} 
  (hM : HasType Δ Γ M A) (hρ : WfRenameTrm Γ Γ' ρ) : HasType Δ Γ' (rename ρ M) A := by
  induction hM generalizing Γ' ρ with
  | t_var hx => 
    exact .t_var (hρ hx)
  | t_lam hA _ ih => 
    exact .t_lam hA (ih (ext_preserves_WfRenameTrm hρ))
  | t_app _ _ ih1 ih2 => 
    exact .t_app (ih1 hρ) (ih2 hρ)
  | t_zero => 
    exact .t_zero
  | t_suc _ ih => 
    exact .t_suc (ih hρ)
  | t_case _ _ _ ihL ihM ihN => 
    exact .t_case (ihL hρ) (ihM hρ) (ihN (ext_preserves_WfRenameTrm hρ))
  | t_tapp _ hB ih => 
    exact .t_tapp (ih hρ) hB
  | t_tlam _ ih => 
    exact .t_tlam (ih (shiftContextTy_preserves_WfRenameTrm hρ))

-------------------------------------------------------------------------------
-- 3. WELL-FORMED TERM SUBSTITUTION
-------------------------------------------------------------------------------

/-- A substitution is well-formed if it maps variables of type A to terms of type A -/
def WfSubstTrm (Δ : Nat) (Γ Γ' : Context) (σ : Subst) : Prop :=
  ∀ {x A}, HasTypeVar Γ x A → HasType Δ Γ' (σ x) A

/-- Weakening lemma (Shift): A simple consequence of `rename_preserves_HasType` -/
theorem rename_shift {Δ : Nat} {Γ : Context} {B : Ty} {M : Raw} {A : Ty}
  (hM : HasType Δ Γ M A) : HasType Δ (B :: Γ) (rename (fun i => i + 1) M) A := by
  apply rename_preserves_HasType hM
  intro x A' hx
  exact .S hx

/-- Extending a well-formed term substitution preserves its well-formedness -/
theorem exts_preserves_WfSubstTrm {Δ : Nat} {Γ Γ' : Context} {B : Ty} {σ : Subst} 
  (hσ : WfSubstTrm Δ Γ Γ' σ) : WfSubstTrm Δ (B :: Γ) (B :: Γ') (exts σ) := by
  intro x A hx
  cases hx with
  | Z => 
    -- exts σ 0 = .var 0, which has type B in (B :: Γ')
    exact .t_var .Z
  | S hx' => 
    -- exts σ (x' + 1) = rename (+1) (σ x')
    -- We use our shift lemma to typecheck the renamed term!
    exact rename_shift (hσ hx')

-------------------------------------------------------------------------------
-- SUBSTITUTION COMMUTATION LEMMAS
-------------------------------------------------------------------------------

/-- Lemma: Composition of extensions is the extension of the composition. 
    Corresponds directly to the STLC `ext_comp` lemma. [cite: 3] -/
theorem extTy_comp (ρ₁ ρ₂ : Rename) :
  (fun i => extTy ρ₂ (extTy ρ₁ i)) = extTy (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i <;> rfl -- [cite: 4, 44]

/-- renameTy ρ₂ (renameTy ρ₁ A) ≡ renameTy (ρ₂ ∘ ρ₁) A.  -/
theorem renameTy_renameTy_commute (ρ₁ ρ₂ : Rename) (A : Ty) :
  renameTy ρ₂ (renameTy ρ₁ A) = renameTy (fun i => ρ₂ (ρ₁ i)) A := by
  induction A generalizing ρ₁ ρ₂ with
  | tvar i => rfl -- Variables are trivially renamed. [cite: 5]
  | nat => rfl
  | fn A B ihA ihB => 
    simp only [renameTy]
    rw [ihA, ihB] -- Applications distribute the renaming to both sides. [cite: 8, 9]
  | univ A ih => 
    simp only [renameTy]
    rw [ih (extTy ρ₁) (extTy ρ₂), extTy_comp] -- For lambdas, we apply the inductive hypothesis to the body and use ext_comp. [cite: 6, 7]

/-- Helper lemma: composing `extTy` and `extsTy` is equivalent to extending the composition. [cite: 16] -/
theorem extsTy_extTy_comp (ρ : Rename) (τ : TySubst) :
  (fun i => extsTy τ (extTy ρ i)) = extsTy (fun i => τ (ρ i)) := by
  funext i
  cases i <;> rfl -- [cite: 17, 18, 44]

/-- Renaming followed by substitution is equivalent to a composed substitution. [cite: 19] -/
theorem renameTy_substTy_commute (ρ : Rename) (τ : TySubst) (A : Ty) :
  substTy τ (renameTy ρ A) = substTy (fun i => τ (ρ i)) A := by
  induction A generalizing ρ τ with
  | tvar i => rfl -- Variables evaluate directly to τ (ρ i) on both sides. [cite: 20]
  | nat => rfl
  | fn A B ihA ihB => 
    simp only [renameTy, substTy]
    rw [ihA, ihB] -- Application distributes to both subterms. [cite: 22]
  | univ A ih => 
    simp only [renameTy, substTy]
    rw [ih (extTy ρ) (extsTy τ), extsTy_extTy_comp] -- Under a lambda, we use the inductive hypothesis and our helper lemma. [cite: 21]

/-- Helper 1: Commuting `extTy` (renaming extension) and `extsTy` (substitution extension). [cite: 27] -/
theorem extTy_extsTy_comp (ρ : Rename) (τ : TySubst) :
  (fun i => renameTy (extTy ρ) (extsTy τ i)) = extsTy (fun i => renameTy ρ (τ i)) := by
  funext i
  cases i with
  | zero => rfl -- [cite: 28]
  | succ j =>
    -- Focus on the `succ` case and use `rename_rename_commute` twice. [cite: 28]
    change renameTy (extTy ρ) (renameTy Nat.succ (τ j)) = renameTy Nat.succ (renameTy ρ (τ j))
    rw [renameTy_renameTy_commute, renameTy_renameTy_commute] -- [cite: 28]
    rfl

/-- Helper 2: Renaming a substitution is equivalent to substituting with renamed terms. [cite: 29] -/
theorem renameTy_substTy (ρ : Rename) (τ : TySubst) (A : Ty) :
  renameTy ρ (substTy τ A) = substTy (fun i => renameTy ρ (τ i)) A := by
  induction A generalizing ρ τ with
  | tvar i => rfl -- [cite: 30]
  | nat => rfl
  | fn A B ihA ihB => 
    simp only [renameTy, substTy]
    rw [ihA, ihB] -- [cite: 31]
  | univ A ih => 
    simp only [renameTy, substTy]
    rw [ih, extTy_extsTy_comp] -- [cite: 30]


namespace SystemF

-------------------------------------------------------------------------------
-- 21. DOUBLE SUBSTITUTION COMMUTATION (substTy ∘ substTy)
-------------------------------------------------------------------------------

/-- Helper: Extending a composed type substitution is the composition of extended substitutions.
    (Corresponds directly to `exts_seq` from STLC). -/
theorem extsTy_comp (σ τ : TySubst) :
  (fun i => substTy (extsTy τ) (extsTy σ i)) = extsTy (fun i => substTy τ (σ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    -- Focus on the inner `rename` and `subst` applications for the succ case
    dsimp only [extsTy]
    -- Use the previously proven commutation lemmas on both sides
    rw [renameTy_substTy_commute, renameTy_substTy]
    rfl

/-- Composing two substitutions is equivalent to a single composed substitution.
    (Corresponds directly to `sub_sub` from STLC). -/
theorem substTy_substTy_commute (σ τ : TySubst) (A : Ty) :
  substTy τ (substTy σ A) = substTy (fun i => substTy τ (σ i)) A := by
  induction A generalizing σ τ with
  | tvar i => 
    rfl
  | nat => 
    rfl
  | fn A B ihA ihB =>
    simp only [substTy]
    rw [ihA, ihB]
  | univ A ih =>
    simp only [substTy]
    -- Apply the IH to the body, then collapse the extended environments
    rw [ih, extsTy_comp]

/-- Helper: Substitution with the variable constructor is the identity. 
    (Corresponds directly to `subst_id` from STLC). -/
theorem substTy_id (A : Ty) : substTy Ty.tvar A = A := by
  induction A with
  | tvar i => rfl
  | nat => rfl
  | fn A B ihA ihB =>
    simp only [substTy]
    rw [ihA, ihB]
  | univ A ih =>
    simp only [substTy]
    have h_exts : extsTy Ty.tvar = Ty.tvar := by
      funext i; cases i <;> rfl
    rw [h_exts, ih]

/-- Corollary: The substitution lemma for single substitutions. -/
theorem substTy_singleSubstTy {A B : Ty} {σ : TySubst} :
  substTy σ (singleSubstTy A B) = singleSubstTy (substTy (extsTy σ) A) (substTy σ B) := by
  dsimp only [singleSubstTy]
  rw [substTy_substTy_commute, substTy_substTy_commute]
  
  -- Using congrArg forces Lean to ONLY strip the outer `substTy ... A`
  apply congrArg (fun env => substTy env A)
  funext i
  cases i with
  | zero => 
    -- Case i = 0: Both evaluate to `substTy σ B`
    rfl
  | succ j =>
    -- Case i = j + 1:
    -- The LHS evaluates cleanly to `σ j`.
    -- The RHS evaluates to `substTy τ (renameTy Nat.succ (σ j))`.
    -- We use `change` to bypass brittle unfolding tactics.
    change σ j = substTy (fun x => match x with | 0 => substTy σ B | k+1 => Ty.tvar k) (renameTy Nat.succ (σ j))
    
    -- Flip the equation to match the commutation lemma
    symm
    
    -- Commute the renaming and substitution on the RHS
    rw [renameTy_substTy_commute]
    
    -- After commutation, the composed mapping strictly evaluates to `Ty.tvar`
    change substTy Ty.tvar (σ j) = σ j
    
    -- Close the goal with our identity lemma!
    exact substTy_id (σ j)


/-- Shifting a context and then mapping a renaming over it is the same as 
    mapping the extended renaming over it, then shifting. -/
theorem shiftContextTy_map {Γ : Context} {ρ : Rename} :
  shiftContextTy (Γ.map (renameTy ρ)) = (shiftContextTy Γ).map (renameTy (extTy ρ)) := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.map, shiftContextTy] at ih ⊢
    rw [ih]
    
    -- h1: Commute the LHS
    have h1 : renameTy (fun i => i + 1) (renameTy ρ A) = renameTy (fun i => ρ i + 1) A := by
      rw [renameTy_renameTy_commute]
      
    -- h2: Commute the RHS. Because extTy ρ (i + 1) evaluates to ρ i + 1,
    -- the result is definitionally equal to the right side of our equality, 
    -- so `rfl` closes it immediately!
    have h2 : renameTy (extTy ρ) (renameTy (fun i => i + 1) A) = renameTy (fun i => ρ i + 1) A := by
      rw [renameTy_renameTy_commute]
      rfl
    rw [h1, h2]

/-- Renaming a type after a single substitution is the same as 
    substituting the renamed type into the extended renamed body. -/
theorem renameTy_singleSubstTy {A B : Ty} {ρ : Rename} :
  renameTy ρ (singleSubstTy A B) = singleSubstTy (renameTy (extTy ρ) A) (renameTy ρ B) := by
  -- Unfold the custom substitution definitions into raw `substTy` applications. 
  dsimp only [singleSubstTy]
  
  -- Commute rename inside subst on the LHS, and subst inside rename on the RHS
  rw [renameTy_substTy, renameTy_substTy_commute]
  
  -- Using congrArg forces Lean to ONLY strip the outer `subst ... M`,
  -- avoiding `congr`'s aggressive and destructive unifications. [cite: 49, 50]
  apply congrArg (fun (σ : TySubst) => substTy σ A)
  funext i
  cases i <;> rfl -- Cases 0 and succ evaluate identically [cite: 51, 52]

-------------------------------------------------------------------------------
-- TYPE WEAKENING FOR TERMS
-------------------------------------------------------------------------------

/-- Applying a well-formed type renaming to a term, its type, and its context 
    preserves the typing judgment. -/
theorem renameTyInRaw_preserves_HasType {Δ Δ' : Nat} {Γ : Context} {M : Raw} {A : Ty} {ρ : Rename}
  (hM : HasType Δ Γ M A) (hρ : WfRename Δ Δ' ρ) : 
  HasType Δ' (Γ.map (renameTy ρ)) (renameTyInRaw ρ M) (renameTy ρ A) := by
  induction hM generalizing Δ' ρ with
  | t_var hx => 
    exact .t_var (HasTypeVar_map_renameTy hx)
    
  | t_lam hA _ ih => 
    -- The type A is renamed, so we must prove it remains well-formed.
    exact .t_lam (renameTy_preserves_WfTy hA hρ) (ih hρ)
    
  | t_app _ _ ih1 ih2 => 
    exact .t_app (ih1 hρ) (ih2 hρ)
    
  | t_zero => 
    exact .t_zero
    
  | t_suc _ ih => 
    exact .t_suc (ih hρ)
    
  | t_case _ _ _ ihL ihM ihN => 
    exact .t_case (ihL hρ) (ihM hρ) (ihN hρ)
    
  | t_tlam _ ih => 
    -- 1. Get the induction hypothesis with the extended renaming (Δ + 1)
    have ih_stepped := ih (extTy_preserves_WfRename hρ)
    -- 2. Use our commutation lemma to align the shifted contexts
    rw [← shiftContextTy_map] at ih_stepped
    exact .t_tlam ih_stepped
    
  | t_tapp _ hB ih => 
    -- 1. Apply the type application rule to our renamed M and renamed B
    have ih_stepped := HasType.t_tapp (ih hρ) (renameTy_preserves_WfTy hB hρ)
    -- 2. Use our commutation lemma to align the substituted types
    rw [renameTy_singleSubstTy]
    exact ih_stepped

-------------------------------------------------------------------------------
-- SUBST PRESERVES HASTYPE
-------------------------------------------------------------------------------

/-- Shifting the types inside a substitution preserves its well-formedness 
    in the shifted contexts. -/
theorem shiftSubstTy_preserves_WfSubstTrm {Δ : Nat} {Γ Γ' : Context} {σ : Subst}
  (hσ : WfSubstTrm Δ Γ Γ' σ) : 
  WfSubstTrm (Δ + 1) (shiftContextTy Γ) (shiftContextTy Γ') (shiftSubstTy σ) := by
  intro x A' hx
  -- 1. Invert the shifted context to find the original type A
  let ⟨A, hA, heq⟩ := shiftContextTy_inv hx
  rw [heq]
  
  -- 2. Define our simple +1 renaming and prove it's well-formed
  have h_ren : WfRename Δ (Δ + 1) (fun i => i + 1) := fun h => Nat.succ_lt_succ h
  
  -- 3. Apply the Type Weakening for Terms lemma!
  -- We know `hσ hA` gives `HasType Δ Γ' (σ x) A`.
  -- Weakening it gives exactly what we need for `shiftSubstTy σ x`.
  exact renameTyInRaw_preserves_HasType (hσ hA) h_ren


/-- Term substitution preserves typing in System F. -/
theorem subst_preserves_HasType {Δ : Nat} {Γ Γ' : Context} {M : Raw} {A : Ty} {σ : Subst} 
  (hM : HasType Δ Γ M A) (hσ : WfSubstTrm Δ Γ Γ' σ) : HasType Δ Γ' (subst σ M) A := by
  induction hM generalizing Γ' σ with
  | t_var hx => 
    exact hσ hx
  | t_lam hA _ ih => 
    exact .t_lam hA (ih (exts_preserves_WfSubstTrm hσ))
  | t_app _ _ ih1 ih2 => 
    exact .t_app (ih1 hσ) (ih2 hσ)
  | t_zero => 
    exact .t_zero
  | t_suc _ ih => 
    exact .t_suc (ih hσ)
  | t_case _ _ _ ihL ihM ihN => 
    exact .t_case (ihL hσ) (ihM hσ) (ihN (exts_preserves_WfSubstTrm hσ))
  | t_tapp _ hB ih => 
    exact .t_tapp (ih hσ) hB
  | t_tlam _ ih => 
    exact .t_tlam (ih (shiftSubstTy_preserves_WfSubstTrm hσ))

-------------------------------------------------------------------------------
-- SINGLE SUBSTITUTION PRESERVES TYPING (Terms)
-------------------------------------------------------------------------------

/-- Substituting a term `N` of type `A` into a term `M` of type `B` 
    (where `M` expects `A` at index 0) yields a term of type `B`. -/
theorem singleSubst_preserves_HasType {Δ : Nat} {Γ : Context} {M N : Raw} {A B : Ty}
  (hM : HasType Δ (A :: Γ) M B) (hN : HasType Δ Γ N A) :
  HasType Δ Γ (singleSubst M N) B := by
  -- We just apply our master substitution theorem!
  apply subst_preserves_HasType hM
  
  -- Now we just prove the environment is well-formed
  intro x C hx
  cases hx with
  | Z => 
    -- Index 0 is mapped to N. Does N have type A? Yes, hN!
    exact hN
  | S h_tail => 
    -- Index x+1 is mapped to .var x. Does .var x have the right type? Yes!
    exact .t_var h_tail

namespace SystemF

-------------------------------------------------------------------------------
-- SUBSTITUTION INTO CONTEXTS
-------------------------------------------------------------------------------

/-- Mapping any type substitution over the context preserves variable lookups. -/
theorem HasTypeVar_map_substTy {Γ : Context} {x : Nat} {A : Ty} {σ : TySubst}
  (h : HasTypeVar Γ x A) : HasTypeVar (Γ.map (substTy σ)) x (substTy σ A) := by
  induction h with
  | Z => 
    -- Γ.map (substTy σ) on (A :: Γ) evaluates to (substTy σ A) :: (Γ.map ...)
    exact .Z
  | S _ ih => 
    -- By induction, x has type (substTy σ A) in the mapped tail.
    -- Applying .S adds the mapped head (substTy σ B) to the context.
    exact .S ih

-------------------------------------------------------------------------------
-- 19. SHIFT AND SUBST COMMUTATION FOR CONTEXTS
-------------------------------------------------------------------------------

/-- Shifting a context and then mapping a substitution over it is the same as 
    mapping the extended substitution over the shifted context. -/
theorem shiftContextTy_map_substTy {Γ : Context} {σ : TySubst} :
  shiftContextTy (Γ.map (substTy σ)) = (shiftContextTy Γ).map (substTy (extsTy σ)) := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.map, shiftContextTy] at ih ⊢
    rw [ih]
    
    -- Commute the LHS head: rename (subst A) -> subst (rename_inside σ) A
    have h1 : renameTy (fun i => i + 1) (substTy σ A) = 
              substTy (fun i => renameTy (fun j => j + 1) (σ i)) A := by
      rw [renameTy_substTy]
      
    -- Commute the RHS head: subst (rename A) -> subst (exts σ (i + 1)) A
    have h2 : substTy (extsTy σ) (renameTy (fun i => i + 1) A) = 
              substTy (fun i => extsTy σ (i + 1)) A := by
      rw [renameTy_substTy_commute]
      
    -- Rewrite BOTH the LHS head and the RHS head in the goal
    rw [h1, h2]
    -- Because `extsTy σ (i + 1)` evaluates exactly to `renameTy (+1) (σ i)`,
    -- both lists are now definitionally identical!
    rfl

theorem substTyInRaw_preserves_HasType {Δ Δ' : Nat} {Γ : Context} {M : Raw} {A : Ty} {σ : TySubst}
  (hM : HasType Δ Γ M A) (hσ : WfTySubst Δ Δ' σ) : 
  HasType Δ' (Γ.map (substTy σ)) (substTyInRaw σ M) (substTy σ A) := by
  induction hM generalizing Δ' σ with
  | t_var hx => 
    exact .t_var (HasTypeVar_map_substTy hx)
  | t_lam hA _ ih => 
    exact .t_lam (substTy_preserves_WfTy hA hσ) (ih hσ)
  | t_app _ _ ih1 ih2 => 
    exact .t_app (ih1 hσ) (ih2 hσ)
  | t_zero => 
    exact .t_zero
  | t_suc _ ih => 
    exact .t_suc (ih hσ)
  | t_case _ _ _ ihL ihM ihN => 
    exact .t_case (ihL hσ) (ihM hσ) (ihN hσ)
  | t_tlam _ ih => 
    -- 1. Apply IH with extended substitution for Δ + 1
    have ih_stepped := ih (extsTy_preserves_WfTySubst hσ)
    -- 2. Use our brand new commutation lemma to align the context!
    rw [← shiftContextTy_map_substTy] at ih_stepped
    exact .t_tlam ih_stepped
  | t_tapp hM hB ih => 
    -- 1. Apply the type application rule to our substituted M and substituted B.
    -- We use `substTy_preserves_WfTy` to prove B remains well-formed.
    have ih_stepped := HasType.t_tapp (ih hσ) (substTy_preserves_WfTy hB hσ)
    
    -- 2. The type of ih_stepped is `singleSubstTy (substTy (extsTy σ) A) (substTy σ B)`.
    -- The goal type is `substTy σ (singleSubstTy A B)`.
    -- Rewrite backwards (or forwards depending on your goal state) using our lemma!
    rw [substTy_singleSubstTy]
    
    -- 3. The types now match perfectly.
    exact ih_stepped

/-- Shifting a type up by 1 and then substituting `B` for `0` cancels out to the identity. -/
theorem substTy_renameTy_cancel (C B : Ty) :
  substTy (fun i => match i with | 0 => B | j + 1 => .tvar j) (renameTy (fun i => i + 1) C) = C := by
  -- Commute the rename and subst
  rw [renameTy_substTy_commute]
  -- The composed mapping `fun i => σ (i + 1)` cleanly evaluates to `.tvar i`.
  change substTy Ty.tvar C = C
  -- Apply our identity lemma!
  exact substTy_id C

/-- Shifting a context up by 1 and then substituting `B` for `0` yields the original context. -/
theorem shiftContextTy_substTy_cancel (Γ : Context) (B : Ty) :
  (shiftContextTy Γ).map (substTy (fun i => match i with | 0 => B | j + 1 => .tvar j)) = Γ := by
  induction Γ with
  | nil => rfl
  | cons C Γ' ih =>
    -- Simplify the map and shift operations
    simp only [List.map, shiftContextTy] at ih ⊢
    -- Rewrite the tail using the IH, and the head using our new cancellation lemma
    rw [ih, substTy_renameTy_cancel]

/-- Corollary: Substituting a well-formed type `B` for type variable `0` 
    inside a term `M` preserves typing. -/
theorem singleSubstTyInRaw_preserves_HasType {Δ : Nat} {Γ : Context} {M : Raw} {A B : Ty}
  (hM : HasType (Δ + 1) (shiftContextTy Γ) M A) (hB : WfTy Δ B) :
  HasType Δ Γ (singleSubstTyInRaw M B) (singleSubstTy A B) := by
  
  -- 1. Define the substitution environment for `singleSubstTy`
  let σ : TySubst := fun i => match i with
    | 0 => B
    | j + 1 => .tvar j
    
  -- 2. Prove it is a well-formed type substitution from Δ+1 to Δ
  have hσ : WfTySubst (Δ + 1) Δ σ := by
    intro x hx
    cases x with
    | zero => exact hB
    | succ j => exact .wf_tvar (Nat.lt_of_succ_lt_succ hx)
    
  -- 3. Apply the master theorem
  have h_subst := substTyInRaw_preserves_HasType hM hσ
  
  -- 4. Clean up the context using our separated cancellation lemma!
  have h_cancel : (shiftContextTy Γ).map (substTy σ) = Γ := by
    exact shiftContextTy_substTy_cancel Γ B
      
  rw [h_cancel] at h_subst
  exact h_subst

-------------------------------------------------------------------------------
-- VALUES
-------------------------------------------------------------------------------

/-- Defines what terms are considered fully evaluated values. -/
inductive Value : Raw → Prop where
  | v_lam {A N}  : Value (.lam A N)
  | v_zero       : Value .zero
  | v_suc {V}    : Value V → Value (.suc V)
  | v_tlam {N}   : Value (.tlam N)        -- NEW: Type abstractions are values!

-------------------------------------------------------------------------------
-- SINGLE-STEP REDUCTION (Call-by-Value)
-------------------------------------------------------------------------------

/-- The single-step reduction relation (M —→ M'). -/
inductive Step : Raw → Raw → Prop where
  -- STLC Rules
  | β_lam {A N V} :
      Value V →
      Step (.app (.lam A N) V) (singleSubst N V)
  | app_L {L L' M} :
      Step L L' →
      Step (.app L M) (.app L' M)
  | app_R {V M M'} :
      Value V →
      Step M M' →
      Step (.app V M) (.app V M')
      
  | suc_step {M M'} :
      Step M M' →
      Step (.suc M) (.suc M')
      
  | β_zero {M N} :
      Step (.case .zero M N) M
  | β_suc {V M N} :
      Value V →
      Step (.case (.suc V) M N) (singleSubst N V)
  | case_step {L L' M N} :
      Step L L' →
      Step (.case L M N) (.case L' M N)

  -- System F Rules
  | β_tapp {N A} :
      -- Type application to a type abstraction substitutes the type into the term
      Step (.tapp (.tlam N) A) (singleSubstTyInRaw N A)
  | tapp_step {M M' A} :
      Step M M' →
      Step (.tapp M A) (.tapp M' A)

-------------------------------------------------------------------------------
-- MULTI-STEP REDUCTION
-------------------------------------------------------------------------------

/-- Reflexive transitive closure of Step (M —↠ M') -/
inductive MultiStep : Raw → Raw → Prop where
  | refl (M) : MultiStep M M
  | step (M) {N P} : Step M N → MultiStep N P → MultiStep M P

/-- MultiStep is transitive -/
theorem multi_trans {M N P : Raw} (h1 : MultiStep M N) (h2 : MultiStep N P) : MultiStep M P := by
  induction h1 with
  | refl => exact h2
  | step M' h_step _ ih => exact .step M' h_step (ih h2)

-------------------------------------------------------------------------------
-- COMPATIBILITY LEMMAS FOR SYSTEM F
-------------------------------------------------------------------------------

/-- If M reduces to M', then M [A] reduces to M' [A] -/
theorem tapp_compat {M M' : Raw} {A : Ty} (h : MultiStep M M') : 
  MultiStep (.tapp M A) (.tapp M' A) := by
  induction h with
  | refl => exact .refl _
  | step _ h_step _ ih => exact .step _ (.tapp_step h_step) ih

-------------------------------------------------------------------------------
-- CANONICAL FORMS
-------------------------------------------------------------------------------

/-- If a value has a function type, it must be a term abstraction (λ). -/
theorem canonical_fn {Δ A B v} (hv : Value v) (h : HasType Δ [] v (.fn A B)) :
  ∃ C N, v = .lam C N := by
  cases hv with
  | v_lam => exact ⟨_, _, rfl⟩
  | v_zero => cases h
  | v_suc => cases h
  | v_tlam => cases h

/-- If a value has the Nat type, it must be zero or a successor of a value. -/
theorem canonical_nat {Δ v} (hv : Value v) (h : HasType Δ [] v .nat) :
  v = .zero ∨ ∃ V, v = .suc V ∧ Value V := by
  cases hv with
  | v_lam => cases h
  | v_zero => exact Or.inl rfl
  | v_suc hv' => exact Or.inr ⟨_, rfl, hv'⟩
  | v_tlam => cases h

/-- If a value has a universal type (∀), it must be a type abstraction (Λ). -/
theorem canonical_univ {Δ A v} (hv : Value v) (h : HasType Δ [] v (.univ A)) :
  ∃ N, v = .tlam N := by
  cases hv with
  | v_lam => cases h
  | v_zero => cases h
  | v_suc => cases h
  | v_tlam => exact ⟨_, rfl⟩

-------------------------------------------------------------------------------
-- PROGRESS
-------------------------------------------------------------------------------

/-- Helper for Progress: We evaluate in an explicitly empty term context.
    We pass `Γ = []` as an explicit equality so the induction hypothesis 
    is correctly instantiated for subterms. -/
theorem progress_lemma {Δ Γ M A} (h : HasType Δ Γ M A) (hΓ : Γ = []) :
  Value M ∨ ∃ M', Step M M' := by
  induction h
  
  case t_var hx =>
    -- A variable cannot exist in an empty context!
    rw [hΓ] at hx
    cases hx
    
  case t_lam =>
    -- A lambda abstraction is immediately a value.
    exact Or.inl .v_lam
    
  case t_app hL hM ihL ihM =>
    -- Evaluate the function part (L)
    cases ihL hΓ with
    | inr hStepL =>
      let ⟨L', h_step⟩ := hStepL
      exact Or.inr ⟨_, .app_L h_step⟩
    | inl hValL =>
      -- L is a value, so evaluate the argument part (M)
      cases ihM hΓ with
      | inr hStepM =>
        let ⟨M', h_step⟩ := hStepM
        exact Or.inr ⟨_, .app_R hValL h_step⟩
      | inl hValM =>
        -- Both are values! Use Canonical Forms to extract the lambda body.
        have hL_ty : HasType _ [] _ _ := hΓ ▸ hL
        let ⟨C, N, h_eq⟩ := canonical_fn hValL hL_ty
        rw [h_eq]
        exact Or.inr ⟨_, .β_lam hValM⟩
        
  case t_zero =>
    exact Or.inl .v_zero
    
  case t_suc hM ihM =>
    cases ihM hΓ with
    | inl hVal => exact Or.inl (.v_suc hVal)
    | inr hStep =>
      let ⟨M', h_step⟩ := hStep
      exact Or.inr ⟨_, .suc_step h_step⟩
      
  case t_case hL hM hN ihL ihM ihN =>
    cases ihL hΓ with
    | inr hStepL =>
      let ⟨L', h_step⟩ := hStepL
      exact Or.inr ⟨_, .case_step h_step⟩
    | inl hValL =>
      -- The target is a value. Use Canonical Forms to see if it's zero or suc.
      have hL_ty : HasType _ [] _ _ := hΓ ▸ hL
      cases canonical_nat hValL hL_ty with
      | inl h_zero =>
        rw [h_zero]
        exact Or.inr ⟨_, .β_zero⟩
      | inr h_suc =>
        let ⟨V, h_eq, hValV⟩ := h_suc
        rw [h_eq]
        exact Or.inr ⟨_, .β_suc hValV⟩
        
  case t_tlam =>
    -- A type abstraction is immediately a value.
    exact Or.inl .v_tlam
    
  case t_tapp hM hB ih =>
    cases ih hΓ with
    | inr hStepM =>
      let ⟨M', h_step⟩ := hStepM
      exact Or.inr ⟨_, .tapp_step h_step⟩
    | inl hValM =>
      -- M is a value being applied to a type. Must be a type abstraction!
      have hM_ty : HasType _ [] _ _ := hΓ ▸ hM
      let ⟨N, h_eq⟩ := canonical_univ hValM hM_ty
      rw [h_eq]
      exact Or.inr ⟨_, .β_tapp⟩

/-- Main Theorem: Well-typed closed terms are either values or can take a step. -/
theorem progress {Δ M A} (h : HasType Δ [] M A) : Value M ∨ ∃ M', Step M M' :=
  progress_lemma h rfl

-------------------------------------------------------------------------------
-- PRESERVATION (Subject Reduction)
-------------------------------------------------------------------------------

/-- Main Theorem: If a well-typed term takes a step, its type is preserved. -/
theorem preservation {Δ Γ M M' A} (h_step : Step M M') (h_type : HasType Δ Γ M A) :
  HasType Δ Γ M' A := by
  -- We proceed by induction on the evaluation step. 
  -- Lean's unifier is smart enough that when we invert (`cases`) the typing 
  -- derivation `h_type`, it instantly discards impossible cases based on syntax.
  induction h_step generalizing Δ Γ A with

  -- Base Case 1: Term-level beta reduction
  | β_lam h_Val =>
    cases h_type with
    | t_app h_lam h_V =>
      cases h_lam with
      -- We must bind BOTH the well-formedness of A and the typing of the body N
      | t_lam h_WfA h_body =>
        -- Now we pass the typing of the body (h_body) and the argument (h_V)
        exact singleSubst_preserves_HasType h_body h_V
  
  -- Inductive Step: Application (Left)
  | app_L h_step_L ih =>
    cases h_type with
    | t_app h_L h_M => exact .t_app (ih h_L) h_M
    
  -- Inductive Step: Application (Right)
  | app_R h_Val h_step_M ih =>
    cases h_type with
    | t_app h_L h_M => exact .t_app h_L (ih h_M)
    
  -- Base Case 2: Nat zero beta reduction
  | β_zero =>
    cases h_type with
    | t_case h_zero h_M h_N => exact h_M
    
  -- Base Case 3: Nat successor beta reduction
  | β_suc h_Val =>
    cases h_type with
    | t_case h_suc h_M h_N =>
      cases h_suc with
      | t_suc h_V =>
        -- We have `Γ, x:Nat ⊢ N : A` and `Γ ⊢ V : Nat`.
        -- Apply term substitution lemma for successor.
        exact singleSubst_preserves_HasType h_N h_V
        
  -- Inductive Step: Successor
  | suc_step h_step ih =>
    cases h_type with
    | t_suc h_M => exact .t_suc (ih h_M)
    
  -- Inductive Step: Case split
  | case_step h_step ih =>
    cases h_type with
    | t_case h_L h_M h_N => exact .t_case (ih h_L) h_M h_N
    
  -- Base Case 4: Type-level beta reduction (System F)
  | β_tapp =>
    cases h_type with
    | t_tapp h_tlam h_B =>
      cases h_tlam with
      | t_tlam h_N =>
        -- We have `Δ+1; shift Γ ⊢ N : A` and `Δ ⊢ B : Ty`.
        -- We need `Δ; Γ ⊢ singleSubstTyInRaw N B : singleSubstTy B A`.
        -- Apply the type substitution lemma!
        exact singleSubstTyInRaw_preserves_HasType h_N h_B
        
  -- Inductive Step: Type Application
  | tapp_step h_step ih =>
    cases h_type with
    | t_tapp h_M h_B => exact .t_tapp (ih h_M) h_B

-------------------------------------------------------------------------------
-- TYPE SAFETY
-------------------------------------------------------------------------------

/-- If M has type A and M multi-steps to M', then M' also has type A. -/
theorem multi_preservation {M M' : Raw} {A : Ty} 
  (hM : HasType 0 [] M A) (hsteps : MultiStep M M') : HasType 0 [] M' A := by
  induction hsteps with
  | refl => 
    -- Zero steps: M is M'
    exact hM
  | step _ h_step _ ih => 
    -- M steps to N, and N multi-steps to P. 
    -- 1. Preservation on the first step:
    have hN := preservation h_step hM 
    -- 2. Use IH to show N multi-stepping to P preserves the type:
    exact ih hN

/-- Type Safety: 
    If a well-typed term M reduces (in any number of steps) to M', then:
    1. M' is still well-typed
    2. M' is either a finished value or can take another step (it isn't "stuck"). -/
theorem type_safety {M M' : Raw} {A : Ty} 
  (h : HasType 0 [] M A) (hsteps : MultiStep M M') : 
  (HasType 0 [] M' A) ∧ (Value M' ∨ ∃ M'', Step M' M'') := by
  -- 1. M' has the correct type via our multi-step preservation lemma
  have hM' : HasType 0 [] M' A := multi_preservation h hsteps
  
  -- 2. M' is either a value or can step via our progress theorem
  have h_prog := progress hM'
  
  constructor
  · exact hM'
  · exact h_prog

end SystemF



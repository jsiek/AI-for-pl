import STLC
import Subst

namespace Termination

open STLC
open Subst

-------------------------------------------------------------------------------
-- 8. TERMINATION VIA LOGICAL RELATIONS
-------------------------------------------------------------------------------

inductive VNat : Raw → Type where
  | zero : VNat .zero
  | suc {V : Raw} : VNat V → VNat (.suc V)

def 𝒱 : Ty → Raw → Type
  | .nat, M => VNat M
  | .fn A B, .lam _ N => ∀ (V : Raw), 𝒱 A V →
      Σ (V' : Raw), (MultiStep (single_subst N V) V') × (Value V') × (𝒱 B V')
  | .fn _ _, _ => Empty

def ℰ (A : Ty) (M : Raw) : Type :=
  Σ (V : Raw), (M —↠ V) × (Value V) × (𝒱 A V)

def VNat_to_Value : ∀ {M : Raw}, VNat M → Value M
  | _, .zero  => .v_zero
  | _, .suc v => .v_suc (VNat_to_Value v)

/-- A well-behaved value is indeed a value. -/
noncomputable def 𝒱_to_Value {A : Ty} {M : Raw} (wtv : 𝒱 A M) : Value M := by
  cases A with
  | nat =>
    -- When A is `.nat`, `wtv` definitionally evaluates to `VNat M`.
    -- We bind it to a new hypothesis to lock in this type, then induct on it.
    have h : VNat M := wtv
    exact (VNat_to_Value h)
  | fn A B =>
    -- When A is `.fn`, we examine the structure of `M`. 
    -- If it's a lambda, it's trivially a value. Any other term makes `wtv` Empty.
    cases M with
    | lam T N => exact .v_lam
    | var i => exact nomatch wtv
    | app L R => exact nomatch wtv
    | zero => exact nomatch wtv
    | suc M' => exact nomatch wtv
    | case L M' N => exact nomatch wtv

/-- A well-behaved value is a well-behaved term. -/
noncomputable def 𝒱_to_ℰ {A : Ty} {M : Raw} (wtv : 𝒱 A M) : ℰ A M :=
  -- We construct the Sigma type. 
  -- Make sure you use `wtv` here and not `wt` to avoid the "Unknown identifier" error!
  ⟨M, .refl M, 𝒱_to_Value wtv, wtv⟩

/-- Compatibility lemma about reduction for application.
    If L reduces to L', L' is a value, and M reduces to M',
    then L M reduces to L' M'. -/
def app_compat {L L' M M' : Raw} 
  (hL : MultiStep L L') (vL' : Value L') (hM : MultiStep M M') : 
  MultiStep (.app L M) (.app L' M') :=
  match hL with
  | .refl _ =>
      match hM with
      | .refl _ => 
          -- Base case: 0 steps for both L and M
          .refl _
      | .step _ s ms_next =>
          -- L is fully evaluated (it's a value), M takes a step `s`.
          -- We step M using `xi_app2` and recurse.
          .step _ (.xi_app2 vL' s) (app_compat (.refl _) vL' ms_next)
  | .step _ s ms_next =>
      -- L takes a step `s`. 
      -- We step L using `xi_app1` and recurse.
      .step _ (.xi_app1 s) (app_compat ms_next vL' hM)

/-- Compatibility lemma: if M reduces to M', then (suc M) reduces to (suc M') -/
def suc_compat {M M' : Raw} : MultiStep M M' → MultiStep (.suc M) (.suc M')
  | .refl _ => .refl _
  | .step _ s ms_next => 
      -- Step the outer `suc` using `xi_suc`, then recurse on the rest of the sequence
      .step _ (.xi_suc s) (suc_compat ms_next)

/-- Compatibility lemma: if L reduces to L', then (case L M N) reduces to (case L' M N) -/
def case_compat {L L' M N : Raw} : MultiStep L L' → MultiStep (.case L M N) (.case L' M N)
  | .refl _ => .refl _
  | .step _ s ms_next => 
      -- Step the discriminant of the `case` using `xi_case`, then recurse
      .step _ (.xi_case s) (case_compat ms_next)

/-- A substitution σ is well-behaved for a context Γ if it maps 
    every variable in Γ to a well-behaved value of the correct type. -/
def SubstWellBehaved (Γ : Context) (σ : Nat → Raw) : Type :=
  ∀ {x C}, HasTypeVar Γ x C → 𝒱 C (σ x)

/-- Extending a well-behaved substitution with a well-behaved value 
    produces a new well-behaved substitution for the extended context. -/
def extend_sub {Γ : Context} {σ : Nat → Raw} {A : Ty} {V : Raw}
  (wtv : 𝒱 A V) (hσ : SubstWellBehaved Γ σ) :
  SubstWellBehaved (A :: Γ) (fun i => match i with | 0 => V | j+1 => σ j) := by
  intro x C hVar
  cases hVar with
  | Z => exact wtv
  | S hVar' => exact hσ hVar'


/-- The Fundamental Property of Logical Relations (Termination)
    If a term is well-typed, and we substitute it with well-behaved values,
    the resulting term is well-behaved (and therefore terminates).
-/
noncomputable def fundamental_property {Γ : Context} {M : Raw} {A : Ty} {σ : Nat → Raw}
  (hM : HasType Γ M A) (hσ : SubstWellBehaved Γ σ) : ℰ A (subst σ M) :=
  match hM with
  | .t_var hV => 
    -- Variables are simply looked up in our well-behaved substitution
    𝒱_to_ℰ (hσ hV)
    
  | .t_lam (A := TyA) (B := TyB) (N := N) hN =>
    ⟨.lam TyA (subst (exts σ) N), .refl _, .v_lam, fun V wtv =>
      -- Recursively evaluate the body with the extended substitution
      let ⟨V', ms_N, v_V', wtv_V'⟩ := fundamental_property hN (extend_sub wtv hσ)
      
      -- ms_N starts from `subst (extend_sub ...) N`.
      -- We rewrite its type to start from `single_subst (subst (exts σ) N) V` 
      -- using our previously proven lemma `exts_sub_cons`.
      have heq : subst (fun i => match i with | 0 => V | j+1 => σ j) N = single_subst (subst (exts σ) N) V := exts_sub_cons.symm
      have ms_N_rewritten : MultiStep (single_subst (subst (exts σ) N) V) V' := heq ▸ ms_N
      
      ⟨V', ms_N_rewritten, v_V', wtv_V'⟩⟩
      
  | .t_app hL hM_arg =>
    let ⟨L', ms_L, v_L, wtv_L⟩ := fundamental_property hL hσ
    let ⟨M', ms_M, v_M, wtv_M⟩ := fundamental_property hM_arg hσ
    
    -- L' must be a well-behaved function value (a lambda)
    match L', wtv_L with
    | .lam T N', wtv_L_fn =>
      let ⟨V, ms_V, v_V, wtv_V⟩ := wtv_L_fn M' wtv_M
      -- Stitch the reductions together: evaluate L, evaluate M, then beta reduce and evaluate body
      have ms_app := multi_trans (app_compat ms_L v_L ms_M) (.step _ (.β_lam v_M) ms_V)
      ⟨V, ms_app, v_V, wtv_V⟩
    | .var _, wtv_L_fn => nomatch wtv_L_fn
    | .app _ _, wtv_L_fn => nomatch wtv_L_fn
    | .zero, wtv_L_fn => nomatch wtv_L_fn
    | .suc _, wtv_L_fn => nomatch wtv_L_fn
    | .case _ _ _, wtv_L_fn => nomatch wtv_L_fn
    
  | .t_zero => 
    ⟨.zero, .refl _, .v_zero, .zero⟩
    
  | .t_suc hM_inner =>
    let ⟨V, ms_M, v_V, wtv_V⟩ := fundamental_property hM_inner hσ
    ⟨.suc V, suc_compat ms_M, .v_suc v_V, .suc wtv_V⟩
    

  | .t_case (L := L_branch) (M := M_branch) (N := N_branch) hL hM_branch hN_branch =>
    let ⟨L', ms_L, v_L, wtv_L⟩ := fundamental_property hL hσ
    
    -- L' must be a well-behaved natural number
    match L', wtv_L with
    | _, .zero =>
      -- If L' evaluates to zero, we step into the M branch
      let ⟨M', ms_M, v_M, wtv_M⟩ := fundamental_property hM_branch hσ
      have ms_case := multi_trans (case_compat ms_L) (.step _ .β_zero ms_M)
      ⟨M', ms_case, v_M, wtv_M⟩
      
    | _, @VNat.suc V wtv_V =>
      -- Explicitly cast wtv_V to `𝒱 .nat V` so Lean unifies `A = .nat`
      have wtv_V_typed : 𝒱 .nat V := wtv_V
      let ⟨N', ms_N, v_N, wtv_N⟩ := fundamental_property hN_branch (extend_sub wtv_V_typed hσ)
      
      have heq : subst (fun i => match i with | 0 => V | j+1 => σ j) N_branch 
           = single_subst (subst (exts σ) N_branch) V := exts_sub_cons.symm
      have ms_N_rewritten : MultiStep (single_subst (subst (exts σ) N_branch) V) N' := heq ▸ ms_N
      
      -- vV gives us the proof that V is a Value natively required by `β_suc`
      have ms_case := multi_trans (case_compat ms_L) (.step _ (.β_suc (𝒱_to_Value wtv_V_typed)) ms_N_rewritten)
      ⟨N', ms_case, v_N, wtv_N⟩

end Termination

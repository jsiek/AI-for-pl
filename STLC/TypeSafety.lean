import STLC

namespace TypeSafety

open STLC

-------------------------------------------------------------------------------
-- 5. STRUCTURAL LEMMAS
-------------------------------------------------------------------------------

def typing_rename {Γ Δ : Context} {ρ : Nat → Nat} {M : Raw} {A : Ty}
  (hρ : ∀ {i B}, HasTypeVar Γ i B → HasTypeVar Δ (ρ i) B)
  (hM : HasType Γ M A) : HasType Δ (rename ρ M) A :=
  match hM with
  | .t_var hV => .t_var (hρ hV)
  | .t_lam (A := A) (B := B) hN =>
      let hρ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasTypeVar (A :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_lam (typing_rename hρ' hN)
  | .t_app hL hM => .t_app (typing_rename hρ hL) (typing_rename hρ hM)
  | .t_zero => .t_zero
  | .t_suc hM => .t_suc (typing_rename hρ hM)
  | .t_case (A := A) hL hM hN =>
      let hρ' : ∀ {i C}, HasTypeVar (Ty.nat :: Γ) i C →
                        HasTypeVar (Ty.nat :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_case (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hρ' hN)

def typing_subst {Γ Δ : Context} {σ : Nat → Raw} {M : Raw} {A : Ty}
  (hσ : ∀ {i B}, HasTypeVar Γ i B → HasType Δ (σ i) B)
  (hM : HasType Γ M A) : HasType Δ (subst σ M) A :=
  match hM with
  | .t_var hV => hσ hV
  | .t_lam (A := A) (B := B) hN =>
      let hσ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasType (A :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              -- We use an explicit lambda for the renaming map
              typing_rename (Δ := A :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_lam (typing_subst hσ' hN)
  | .t_app hL hR => .t_app (typing_subst hσ hL) (typing_subst hσ hR)
  | .t_zero => .t_zero
  | .t_suc hK => .t_suc (typing_subst hσ hK)
  | .t_case (A := A) hL hM hN =>
      let hσ' : ∀ {i C}, HasTypeVar (Ty.nat :: Γ) i C →
                        HasType (Ty.nat :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              typing_rename (Δ := Ty.nat :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_case (typing_subst hσ hL) (typing_subst hσ hM) (typing_subst hσ' hN)

def typing_single_subst {Γ : Context} {A B : Ty} {N M : Raw}
  (hN : HasType (B :: Γ) N A) (hM : HasType Γ M B) :
  HasType Γ (single_subst N M) A := by
  -- Define the mapping: 0 goes to M, and j+1 shifts down to j
  let σ := fun (i : Nat) => match i with | 0 => M | j+1 => .var j

  -- Apply the substitution lemma
  refine typing_subst (Δ := Γ) (σ := σ) ?_ hN

  -- Prove the substitution is well-typed for all variables
  intro i C hVar
  cases hVar with
  | Z =>
    -- Case i = 0: σ(0) = M. We know Γ ⊢ M : B from hM.
    exact hM
  | S hVar' =>
    -- Case i = j+1: σ(j+1) = var j.
    -- Since the context was (B :: Γ), index j+1 had type C.
    -- Therefore, in Γ, index j has type C.
    exact .t_var hVar'

-------------------------------------------------------------------------------
-- 6. PROGRESS & PRESERVATION
-------------------------------------------------------------------------------

def preservation {M N : Raw} {A : Ty}
  (hT : HasType [] M A) (hS : M —→ N) : HasType [] N A :=
  match hS with
  | .β_lam hV =>
      match hT with
      | .t_app (.t_lam hN) hM => typing_single_subst hN hM
  | .β_zero =>
      match hT with
      | .t_case _ hM _ => hM
  | .β_suc hV =>
      match hT with
      | .t_case (.t_suc hL) _ hN => typing_single_subst hN hL
  | .xi_app1 s =>
      match hT with
      | .t_app hL hM => .t_app (preservation hL s) hM
  | .xi_app2 v s =>
      match hT with
      | .t_app hL hM => .t_app hL (preservation hM s)
  | .xi_suc s =>
      match hT with
      | .t_suc hM => .t_suc (preservation hM s)
  | .xi_case s =>
      match hT with
      | .t_case hL hM hN => .t_case (preservation hL s) hM hN

inductive ProgressResult (M : Raw) where
  | step : ∀ {N}, (M —→ N) → ProgressResult M
  | done : Value M → ProgressResult M

def progress {Γ : Context} {M : Raw} {A : Ty} (h : HasType Γ M A) :
  Γ = [] → ProgressResult M := fun hEmpty =>
  match Γ, M, A, h with
  | _, .var i, _, .t_var hV => by subst hEmpty; nomatch hV
  | _, .lam A N, _, .t_lam hN => .done .v_lam
  | _, .app L M, B, .t_app hL hM =>
      match progress hL hEmpty, progress hM hEmpty with
      | .step s, _ => .step (.xi_app1 s)
      | .done vL, .step s => .step (.xi_app2 vL s)
      | .done vL, .done vM => match L, vL with | .lam _ _, .v_lam => .step (.β_lam vM)
  | _, .zero, _, .t_zero => .done .v_zero
  | _, .suc M, _, .t_suc hM =>
      match progress hM hEmpty with | .step s => .step (.xi_suc s) | .done v => .done (.v_suc v)
  | _, .case L M N, A, .t_case hL hM hN =>
      match progress hL hEmpty with
      | .step s => .step (.xi_case s)
      | .done vL => match L, vL with
          | .zero, .v_zero => .step .β_zero
          | .suc _, .v_suc v => .step (.β_suc v)

def progress_top {M : Raw} {A : Ty} (h : HasType [] M A) : ProgressResult M :=
  progress h rfl

end TypeSafety

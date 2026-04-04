module TypeSafety where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (_,_; snd)
open import STLC

------------------------------------------------------------------------
-- Empty type and eliminator
------------------------------------------------------------------------

data ⊥ : Set where

⊥-elim : {A : Set} -> ⊥ -> A
⊥-elim ()

------------------------------------------------------------------------
-- Structural lemmas
------------------------------------------------------------------------

typing_rename :
  {Γ Δ : Context} {ρ : Rename} {M : Term} {A : Ty} ->
  (∀ {i B} -> HasTypeVar Γ i B -> HasTypeVar Δ (ρ i) B) ->
  HasType Γ M A ->
  HasType Δ (rename ρ M) A
typing_rename hρ (tVar hV) = tVar (hρ hV)
typing_rename {Γ} {Δ} {ρ} hρ (tLam {A = A} hN) =
  tLam (typing_rename hrExt hN)
  where
    hrExt : ∀ {i C} -> HasTypeVar (A ∷ Γ) i C -> HasTypeVar (A ∷ Δ) (ext ρ i) C
    hrExt STLC.Z = STLC.Z
    hrExt (STLC.S hV') = STLC.S (hρ hV')
typing_rename hρ (tApp hL hM) =
  tApp (typing_rename hρ hL) (typing_rename hρ hM)
typing_rename hρ tZero = tZero
typing_rename hρ (tSuc hM) = tSuc (typing_rename hρ hM)
typing_rename {Γ} {Δ} {ρ} hρ (tCase hL hM hN) =
  tCase (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hrExt hN)
  where
    hrExt : ∀ {i C} -> HasTypeVar (nat ∷ Γ) i C -> HasTypeVar (nat ∷ Δ) (ext ρ i) C
    hrExt STLC.Z = STLC.Z
    hrExt (STLC.S hV') = STLC.S (hρ hV')

typing_subst :
  {Γ Δ : Context} {σ : Subst} {M : Term} {A : Ty} ->
  (∀ {i B} -> HasTypeVar Γ i B -> HasType Δ (σ i) B) ->
  HasType Γ M A ->
  HasType Δ (subst σ M) A
typing_subst hs (tVar hV) = hs hV
typing_subst {Γ} {Δ} {σ} hs (tLam {A = A} hN) =
  tLam (typing_subst hsExt hN)
  where
    shift : ∀ {i B} -> HasTypeVar Δ i B -> HasTypeVar (A ∷ Δ) (sucℕ i) B
    shift hV = STLC.S hV

    hsExt : ∀ {i C} -> HasTypeVar (A ∷ Γ) i C -> HasType (A ∷ Δ) (exts σ i) C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> HasTypeVar (A ∷ Γ) i C -> HasType (A ∷ Δ) (exts σ i) C
        hsExtAux STLC.Z = tVar STLC.Z
        hsExtAux (STLC.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs (tApp hL hR) =
  tApp (typing_subst hs hL) (typing_subst hs hR)
typing_subst hs tZero = tZero
typing_subst hs (tSuc hK) = tSuc (typing_subst hs hK)
typing_subst {Γ} {Δ} {σ} hs (tCase hL hM hN) =
  tCase (typing_subst hs hL) (typing_subst hs hM) (typing_subst hsExt hN)
  where
    shift : ∀ {i B} -> HasTypeVar Δ i B -> HasTypeVar (nat ∷ Δ) (sucℕ i) B
    shift hV = STLC.S hV

    hsExt : ∀ {i C} -> HasTypeVar (nat ∷ Γ) i C -> HasType (nat ∷ Δ) (exts σ i) C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> HasTypeVar (nat ∷ Γ) i C -> HasType (nat ∷ Δ) (exts σ i) C
        hsExtAux STLC.Z = tVar STLC.Z
        hsExtAux (STLC.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')

typing_single_subst :
  {Γ : Context} {A B : Ty} {N M : Term} ->
  HasType (B ∷ Γ) N A ->
  HasType Γ M B ->
  HasType Γ (singleSubst N M) A
typing_single_subst {Γ} {A} {B} {N} {M} hN hM =
  typing_subst hσ hN
  where
    hσ : ∀ {i C} -> HasTypeVar (B ∷ Γ) i C -> HasType Γ (singleEnv M i) C
    hσ STLC.Z = hM
    hσ (STLC.S hVar') = tVar hVar'

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation :
  {M N : Term} {A : Ty} ->
  HasType [] M A ->
  M —→ N ->
  HasType [] N A
preservation (tApp (tLam hN) hM) (betaLam vW) =
  typing_single_subst hN hM
preservation (tCase hL hM hN) betaZero = hM
preservation (tCase (tSuc hL) hM hN) (betaSuc vV) =
  typing_single_subst hN hL
preservation (tApp hL hM) (xiAppLeft s) =
  tApp (preservation hL s) hM
preservation (tApp hL hM) (xiAppRight p) =
  tApp hL (preservation hM (snd p))
preservation (tSuc hM) (xiSuc s) =
  tSuc (preservation hM s)
preservation (tCase hL hM hN) (xiCase s) =
  tCase (preservation hL s) hM hN

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

data ProgressResult (M : Term) : Set where
  pr-step : {N : Term} -> M —→ N -> ProgressResult M
  pr-done : Value M -> ProgressResult M

noZeroFn : {A B : Ty} -> HasType [] `zero (A ⇒ B) -> ⊥
noZeroFn ()

noSucFn : {A B : Ty} {M : Term} -> HasType [] (`suc M) (A ⇒ B) -> ⊥
noSucFn ()

noLamNat : {A : Ty} {N : Term} -> HasType [] (ƛ A ⇒ N) nat -> ⊥
noLamNat ()

progress-empty :
  {M : Term} {A : Ty} ->
  HasType [] M A ->
  ProgressResult M
progress-empty (tVar ())
progress-empty (tLam hN) = pr-done vLam
progress-empty (tApp hL hM) with progress-empty hL
... | pr-step s = pr-step (xiAppLeft s)
... | pr-done vL with progress-empty hM
...   | pr-step s = pr-step (xiAppRight (vL , s))
...   | pr-done vM with vL
...     | vLam = pr-step (betaLam vM)
...     | vZero = ⊥-elim (noZeroFn hL)
...     | vSuc _ = ⊥-elim (noSucFn hL)
progress-empty tZero = pr-done vZero
progress-empty (tSuc hM) with progress-empty hM
... | pr-step s = pr-step (xiSuc s)
... | pr-done v = pr-done (vSuc v)
progress-empty (tCase hL hM hN) with progress-empty hL
... | pr-step s = pr-step (xiCase s)
... | pr-done vL with vL
...   | vZero = pr-step betaZero
...   | vSuc v = pr-step (betaSuc v)
...   | vLam = ⊥-elim (noLamNat hL)

progress :
  {Γ : Context} {M : Term} {A : Ty} ->
  HasType Γ M A ->
  Γ ≡ [] ->
  ProgressResult M
progress h refl = progress-empty h

progress_top : 
  {M : Term} {A : Ty} ->
  HasType [] M A ->
  ProgressResult M
progress_top h = progress-empty h

------------------------------------------------------------------------
-- Compact safety wrapper
------------------------------------------------------------------------

record Safety (M : Term) (A : Ty) : Set where
  constructor safety
  field
    progress-witness : ProgressResult M
    preservation-step : ∀ {N : Term} -> M —→ N -> HasType [] N A

open Safety public

typeSafety :
  {M : Term} {A : Ty} ->
  HasType [] M A ->
  Safety M A
typeSafety hM = safety (progress_top hM) (preservation hM)

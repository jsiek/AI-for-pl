module TypeSafety where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (Σ; _,_; snd)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import STLC

------------------------------------------------------------------------
-- Structural lemmas
------------------------------------------------------------------------

typing_rename :
  {Γ Δ : Ctx} {ρ : Rename} {M : Term} {A : Ty} ->
  (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ∋ (ρ i) ⦂ B) ->
  Γ ⊢ M ⦂ A ->
  Δ ⊢ (rename ρ M) ⦂ A
typing_rename hρ (⊢` hV) = ⊢` (hρ hV)
typing_rename {Γ} {Δ} {ρ} hρ (⊢ƛ {A = A} hN) =
  ⊢ƛ (typing_rename hrExt hN)
  where
    hrExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ∋ (ext ρ i) ⦂ C
    hrExt STLC.Z = STLC.Z
    hrExt (STLC.S hV') = STLC.S (hρ hV')
typing_rename hρ (⊢· hL hM) =
  ⊢· (typing_rename hρ hL) (typing_rename hρ hM)
typing_rename hρ ⊢zero = ⊢zero
typing_rename hρ (⊢suc hM) = ⊢suc (typing_rename hρ hM)
typing_rename {Γ} {Δ} {ρ} hρ (⊢case hL hM hN) =
  ⊢case (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hrExt hN)
  where
    hrExt : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ∋ (ext ρ i) ⦂ C
    hrExt STLC.Z = STLC.Z
    hrExt (STLC.S hV') = STLC.S (hρ hV')

typing_subst :
  {Γ Δ : Ctx} {σ : Subst} {M : Term} {A : Ty} ->
  (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ⊢ (σ i) ⦂ B) ->
  Γ ⊢ M ⦂ A ->
  Δ ⊢ (subst σ M) ⦂ A
typing_subst hs (⊢` hV) = hs hV
typing_subst {Γ} {Δ} {σ} hs (⊢ƛ {A = A} hN) =
  ⊢ƛ (typing_subst hsExt hN)
  where
    shift : ∀ {i B} -> Δ ∋ i ⦂ B -> (A ∷ Δ) ∋ sucℕ i ⦂ B
    shift hV = STLC.S hV

    hsExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
        hsExtAux STLC.Z = ⊢` STLC.Z
        hsExtAux (STLC.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs (⊢· hL hR) =
  ⊢· (typing_subst hs hL) (typing_subst hs hR)
typing_subst hs ⊢zero = ⊢zero
typing_subst hs (⊢suc hK) = ⊢suc (typing_subst hs hK)
typing_subst {Γ} {Δ} {σ} hs (⊢case hL hM hN) =
  ⊢case (typing_subst hs hL) (typing_subst hs hM) (typing_subst hsExt hN)
  where
    shift : ∀ {i B} -> Δ ∋ i ⦂ B -> (nat ∷ Δ) ∋ sucℕ i ⦂ B
    shift hV = STLC.S hV

    hsExt : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ⊢ (exts σ i) ⦂ C
        hsExtAux STLC.Z = ⊢` STLC.Z
        hsExtAux (STLC.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')

typing_single_subst :
  {Γ : Ctx} {A B : Ty} {N M : Term} ->
  (B ∷ Γ) ⊢ N ⦂ A ->
  Γ ⊢ M ⦂ B ->
  Γ ⊢ (N [ M ]) ⦂ A
typing_single_subst {Γ} {A} {B} {N} {M} hN hM =
  typing_subst hσ hN
  where
    hσ : ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> Γ ⊢ (singleEnv M i) ⦂ C
    hσ STLC.Z = hM
    hσ (STLC.S hVar') = ⊢` hVar'

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —→ N ->
  [] ⊢ N ⦂ A
preservation (⊢· (⊢ƛ hN) hM) (β-ƛ vW) =
  typing_single_subst hN hM
preservation (⊢case hL hM hN) β-zero = hM
preservation (⊢case (⊢suc hL) hM hN) (β-suc vV) =
  typing_single_subst hN hL
preservation (⊢· hL hM) (ξ-·₁ s) =
  ⊢· (preservation hL s) hM
preservation (⊢· hL hM) (ξ-·₂ p) =
  ⊢· hL (preservation hM (snd p))
preservation (⊢suc hM) (ξ-suc s) =
  ⊢suc (preservation hM s)
preservation (⊢case hL hM hN) (ξ-case s) =
  ⊢case (preservation hL s) hM hN

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

noZeroFn : {A B : Ty} -> [] ⊢ `zero ⦂ (A ⇒ B) -> ⊥
noZeroFn ()

noSucFn : {A B : Ty} {M : Term} -> [] ⊢ (`suc M) ⦂ (A ⇒ B) -> ⊥
noSucFn ()

noLamNat : {A : Ty} {N : Term} -> [] ⊢ (ƛ A ⇒ N) ⦂ nat -> ⊥
noLamNat ()

progress-empty :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  (Σ Term (λ N -> M —→ N)) ⊎ Value M
progress-empty (⊢` ())
progress-empty (⊢ƛ hN) = inj₂ V-ƛ
progress-empty (⊢· hL hM) with progress-empty hL
progress-empty (⊢· hL hM) | inj₁ (N , s) = inj₁ (_ , ξ-·₁ s)
progress-empty (⊢· hL hM) | inj₂ vL with progress-empty hM
progress-empty (⊢· hL hM) | inj₂ vL | inj₁ (N , s) = inj₁ (_ , ξ-·₂ (vL , s))
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM with vL
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | V-ƛ = inj₁ (_ , β-ƛ vM)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | V-zero = ⊥-elim (noZeroFn hL)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | V-suc _ = ⊥-elim (noSucFn hL)
progress-empty ⊢zero = inj₂ V-zero
progress-empty (⊢suc hM) with progress-empty hM
progress-empty (⊢suc hM) | inj₁ (N , s) = inj₁ (`suc N , ξ-suc s)
progress-empty (⊢suc hM) | inj₂ v = inj₂ (V-suc v)
progress-empty (⊢case hL hM hN) with progress-empty hL
progress-empty (⊢case hL hM hN) | inj₁ (L' , s) = inj₁ (_ , ξ-case s)
progress-empty (⊢case hL hM hN) | inj₂ vL with vL
progress-empty (⊢case hL hM hN) | inj₂ vL | V-zero = inj₁ (_ , β-zero)
progress-empty (⊢case hL hM hN) | inj₂ vL | V-suc v = inj₁ (_ , β-suc v)
progress-empty (⊢case hL hM hN) | inj₂ vL | V-ƛ = ⊥-elim (noLamNat hL)

progress :
  {Γ : Ctx} {M : Term} {A : Ty} ->
  Γ ⊢ M ⦂ A ->
  Γ ≡ [] ->
  (Σ Term (λ N -> M —→ N)) ⊎ Value M
progress h refl = progress-empty h

progress_top :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  (Σ Term (λ N -> M —→ N)) ⊎ Value M
progress_top h = progress-empty h

------------------------------------------------------------------------
-- Type safety
------------------------------------------------------------------------

typeSafety-step :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  ∀ {N : Term} -> M —→ N -> [] ⊢ N ⦂ A
typeSafety-step hM s = preservation hM s

typeSafety-↠ :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  [] ⊢ N ⦂ A
typeSafety-↠ hM (_ ∎) = hM
typeSafety-↠ hM (_ —→⟨ s ⟩ ms) = typeSafety-↠ (preservation hM s) ms

typeSafety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (Σ Term (λ N' -> N —→ N')) ⊎ Value N
typeSafety hM M—↠N = progress-empty (typeSafety-↠ hM M—↠N)

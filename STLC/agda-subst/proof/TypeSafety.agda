module proof.TypeSafety where

-- File Charter:
--   * Private progress/preservation development and type-safety proof.
--   * Exported through public wrappers in `TypeSafety.agda`.

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

-- One lemma for both kits: a traversal preserves typing when its
-- substitution maps each variable to a well-typed thing of the kit.
-- `⊢K` says what it is for a thing of the kit to have a type, with
-- variables (`⊢vr`), under a binder (`⊢wk`), and as a term (`⊢tm`).
module _ (𝒦 : Kit)
  (_⊢K_⦂_ : Ctx -> Kit.K 𝒦 _ _ -> Ty -> Set)
  (⊢vr : ∀ {Γ i A} -> Γ ∋ i ⦂ A -> Γ ⊢K Kit.vr 𝒦 i ⦂ A)
  (⊢wk : ∀ {Γ k A B} -> Γ ⊢K k ⦂ A -> (B ∷ Γ) ⊢K Kit.wk 𝒦 k ⦂ A)
  (⊢tm : ∀ {Γ k A} -> Γ ⊢K k ⦂ A -> Γ ⊢ Kit.tm 𝒦 k ⦂ A)
  where

  typing_exts :
    {Γ Δ : Ctx} {σ : Sub 𝒦 _ _} {B : Ty} ->
    (∀ {i C} -> Γ ∋ i ⦂ C -> Δ ⊢K σ i ⦂ C) ->
    ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> (B ∷ Δ) ⊢K exts 𝒦 σ i ⦂ C
  typing_exts hσ STLC.Z = ⊢vr STLC.Z
  typing_exts hσ (STLC.S hV) = ⊢wk (hσ hV)

  typing_trav :
    {Γ Δ : Ctx} {σ : Sub 𝒦 _ _} {M : Term} {A : Ty} ->
    (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ⊢K σ i ⦂ B) ->
    Γ ⊢ M ⦂ A ->
    Δ ⊢ trav 𝒦 σ M ⦂ A
  typing_trav hσ (⊢` hV) = ⊢tm (hσ hV)
  typing_trav hσ (⊢ƛ hN) = ⊢ƛ (typing_trav (typing_exts hσ) hN)
  typing_trav hσ (⊢· hL hM) = ⊢· (typing_trav hσ hL) (typing_trav hσ hM)
  typing_trav hσ ⊢zero = ⊢zero
  typing_trav hσ (⊢suc hM) = ⊢suc (typing_trav hσ hM)
  typing_trav hσ (⊢case hL hM hN) =
    ⊢case (typing_trav hσ hL) (typing_trav hσ hM)
      (typing_trav (typing_exts hσ) hN)

typing_rename :
  {Γ Δ : Ctx} {ρ : Rename} {M : Term} {A : Ty} ->
  (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ∋ (ρ i) ⦂ B) ->
  Γ ⊢ M ⦂ A ->
  Δ ⊢ (ren ρ M) ⦂ A
typing_rename = typing_trav varK _∋_⦂_ (λ hV -> hV) STLC.S ⊢`

typing_subst :
  {Γ Δ : Ctx} {σ : Subst} {M : Term} {A : Ty} ->
  (∀ {i B} -> Γ ∋ i ⦂ B -> Δ ⊢ (σ i) ⦂ B) ->
  Γ ⊢ M ⦂ A ->
  Δ ⊢ (sub σ M) ⦂ A
typing_subst =
  typing_trav tmK _⊢_⦂_ ⊢` (typing_rename STLC.S) (λ hM -> hM)

typing_single_subst :
  {Γ : Ctx} {A B : Ty} {N M : Term} ->
  (B ∷ Γ) ⊢ N ⦂ A ->
  Γ ⊢ M ⦂ B ->
  Γ ⊢ (N [ M ]) ⦂ A
typing_single_subst {Γ} {A} {B} {N} {M} hN hM =
  typing_subst hσ hN
  where
    hσ : ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> Γ ⊢ ((M • ids) i) ⦂ C
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
progress-empty (⊢ƛ hN) = inj₂ (ƛ _ ⇒ _)
progress-empty (⊢· hL hM) with progress-empty hL
progress-empty (⊢· hL hM) | inj₁ (N , s) = inj₁ (_ , ξ-·₁ s)
progress-empty (⊢· hL hM) | inj₂ vL with progress-empty hM
progress-empty (⊢· hL hM) | inj₂ vL | inj₁ (N , s) = inj₁ (_ , ξ-·₂ (vL , s))
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM with vL
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | ƛ _ ⇒ _ = inj₁ (_ , β-ƛ vM)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | `zero = ⊥-elim (noZeroFn hL)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | `suc _ = ⊥-elim (noSucFn hL)
progress-empty ⊢zero = inj₂ `zero
progress-empty (⊢suc hM) with progress-empty hM
progress-empty (⊢suc hM) | inj₁ (N , s) = inj₁ (`suc N , ξ-suc s)
progress-empty (⊢suc hM) | inj₂ v = inj₂ (`suc v)
progress-empty (⊢case hL hM hN) with progress-empty hL
progress-empty (⊢case hL hM hN) | inj₁ (L' , s) = inj₁ (_ , ξ-case s)
progress-empty (⊢case hL hM hN) | inj₂ vL with vL
progress-empty (⊢case hL hM hN) | inj₂ vL | `zero = inj₁ (_ , β-zero)
progress-empty (⊢case hL hM hN) | inj₂ vL | `suc v = inj₁ (_ , β-suc v)
progress-empty (⊢case hL hM hN) | inj₂ vL | ƛ _ ⇒ _ = ⊥-elim (noLamNat hL)

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

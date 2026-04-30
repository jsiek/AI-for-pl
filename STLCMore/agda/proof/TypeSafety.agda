module proof.TypeSafety where

-- File Charter:
--   * Private progress/preservation development and type-safety proof.
--   * Exported through public wrappers in `TypeSafety.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import STLCMore

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
    hrExt STLCMore.Z = STLCMore.Z
    hrExt (STLCMore.S hV') = STLCMore.S (hρ hV')
typing_rename hρ (⊢· hL hM) =
  ⊢· (typing_rename hρ hL) (typing_rename hρ hM)
typing_rename hρ (⊢as hM) = ⊢as (typing_rename hρ hM)
typing_rename {Γ} {Δ} {ρ} hρ (⊢let {A = A} hM hN) =
  ⊢let (typing_rename hρ hM) (typing_rename hrExt hN)
  where
    hrExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ∋ (ext ρ i) ⦂ C
    hrExt STLCMore.Z = STLCMore.Z
    hrExt (STLCMore.S hV') = STLCMore.S (hρ hV')
typing_rename hρ ⊢zero = ⊢zero
typing_rename hρ ⊢unit = ⊢unit
typing_rename hρ (⊢suc hM) = ⊢suc (typing_rename hρ hM)
typing_rename {Γ} {Δ} {ρ} hρ (⊢case hL hM hN) =
  ⊢case (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hrExt hN)
  where
    hrExt : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ∋ (ext ρ i) ⦂ C
    hrExt STLCMore.Z = STLCMore.Z
    hrExt (STLCMore.S hV') = STLCMore.S (hρ hV')
typing_rename hρ (⊢pair hM hN) =
  ⊢pair (typing_rename hρ hM) (typing_rename hρ hN)
typing_rename hρ (⊢fst hM) = ⊢fst (typing_rename hρ hM)
typing_rename hρ (⊢snd hM) = ⊢snd (typing_rename hρ hM)
typing_rename hρ (⊢inl hM) = ⊢inl (typing_rename hρ hM)
typing_rename hρ (⊢inr hM) = ⊢inr (typing_rename hρ hM)
typing_rename {Γ} {Δ} {ρ} hρ (⊢case⊎ {A = A} {B = B} hL hM hN) =
  ⊢case⊎ (typing_rename hρ hL) (typing_rename hMExt hM) (typing_rename hNExt hN)
  where
    hMExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ∋ (ext ρ i) ⦂ C
    hMExt STLCMore.Z = STLCMore.Z
    hMExt (STLCMore.S hV') = STLCMore.S (hρ hV')

    hNExt : ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> (B ∷ Δ) ∋ (ext ρ i) ⦂ C
    hNExt STLCMore.Z = STLCMore.Z
    hNExt (STLCMore.S hV') = STLCMore.S (hρ hV')

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
    shift hV = STLCMore.S hV

    hsExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
        hsExtAux STLCMore.Z = ⊢` STLCMore.Z
        hsExtAux (STLCMore.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs (⊢· hL hR) =
  ⊢· (typing_subst hs hL) (typing_subst hs hR)
typing_subst hs (⊢as hM) = ⊢as (typing_subst hs hM)
typing_subst {Γ} {Δ} {σ} hs (⊢let {A = A} hM hN) =
  ⊢let (typing_subst hs hM) (typing_subst hsExt hN)
  where
    shift : ∀ {i B} -> Δ ∋ i ⦂ B -> (A ∷ Δ) ∋ sucℕ i ⦂ B
    shift hV = STLCMore.S hV

    hsExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
        hsExtAux STLCMore.Z = ⊢` STLCMore.Z
        hsExtAux (STLCMore.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs ⊢zero = ⊢zero
typing_subst hs ⊢unit = ⊢unit
typing_subst hs (⊢suc hK) = ⊢suc (typing_subst hs hK)
typing_subst {Γ} {Δ} {σ} hs (⊢case hL hM hN) =
  ⊢case (typing_subst hs hL) (typing_subst hs hM) (typing_subst hsExt hN)
  where
    shift : ∀ {i B} -> Δ ∋ i ⦂ B -> (nat ∷ Δ) ∋ sucℕ i ⦂ B
    shift hV = STLCMore.S hV

    hsExt : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsExt x = hsExtAux x
      where
        hsExtAux : ∀ {i C} -> (nat ∷ Γ) ∋ i ⦂ C -> (nat ∷ Δ) ⊢ (exts σ i) ⦂ C
        hsExtAux STLCMore.Z = ⊢` STLCMore.Z
        hsExtAux (STLCMore.S hV') = typing_rename {ρ = sucℕ} shift (hs hV')
typing_subst hs (⊢pair hM hN) =
  ⊢pair (typing_subst hs hM) (typing_subst hs hN)
typing_subst hs (⊢fst hM) = ⊢fst (typing_subst hs hM)
typing_subst hs (⊢snd hM) = ⊢snd (typing_subst hs hM)
typing_subst hs (⊢inl hM) = ⊢inl (typing_subst hs hM)
typing_subst hs (⊢inr hM) = ⊢inr (typing_subst hs hM)
typing_subst {Γ} {Δ} {σ} hs (⊢case⊎ {A = A} {B = B} hL hM hN) =
  ⊢case⊎ (typing_subst hs hL) (typing_subst hsMExt hM) (typing_subst hsNExt hN)
  where
    shiftM : ∀ {i C} -> Δ ∋ i ⦂ C -> (A ∷ Δ) ∋ sucℕ i ⦂ C
    shiftM hV = STLCMore.S hV

    hsMExt : ∀ {i C} -> (A ∷ Γ) ∋ i ⦂ C -> (A ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsMExt STLCMore.Z = ⊢` STLCMore.Z
    hsMExt (STLCMore.S hV') = typing_rename {ρ = sucℕ} shiftM (hs hV')

    shiftN : ∀ {i C} -> Δ ∋ i ⦂ C -> (B ∷ Δ) ∋ sucℕ i ⦂ C
    shiftN hV = STLCMore.S hV

    hsNExt : ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> (B ∷ Δ) ⊢ (exts σ i) ⦂ C
    hsNExt STLCMore.Z = ⊢` STLCMore.Z
    hsNExt (STLCMore.S hV') = typing_rename {ρ = sucℕ} shiftN (hs hV')

typing_single_subst :
  {Γ : Ctx} {A B : Ty} {N M : Term} ->
  (B ∷ Γ) ⊢ N ⦂ A ->
  Γ ⊢ M ⦂ B ->
  Γ ⊢ (N [ M ]) ⦂ A
typing_single_subst {Γ} {A} {B} {N} {M} hN hM =
  typing_subst hσ hN
  where
    hσ : ∀ {i C} -> (B ∷ Γ) ∋ i ⦂ C -> Γ ⊢ (singleEnv M i) ⦂ C
    hσ STLCMore.Z = hM
    hσ (STLCMore.S hVar') = ⊢` hVar'

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
preservation (⊢as hM) (ξ-as s) = ⊢as (preservation hM s)
preservation (⊢as hV) (β-as vV) = hV
preservation (⊢let hM hN) (ξ-let s) = ⊢let (preservation hM s) hN
preservation (⊢let hV hN) (β-let vV) = typing_single_subst hN hV
preservation (⊢case hL hM hN) β-zero = hM
preservation (⊢case (⊢suc hL) hM hN) (β-suc vV) =
  typing_single_subst hN hL
preservation (⊢· hL hM) (ξ-·₁ s) =
  ⊢· (preservation hL s) hM
preservation (⊢· hL hM) (ξ-·₂ (_ , s)) =
  ⊢· hL (preservation hM s)
preservation (⊢suc hM) (ξ-suc s) =
  ⊢suc (preservation hM s)
preservation (⊢case hL hM hN) (ξ-case s) =
  ⊢case (preservation hL s) hM hN
preservation (⊢pair hM hN) (ξ-pair₁ s) =
  ⊢pair (preservation hM s) hN
preservation (⊢pair hM hN) (ξ-pair₂ (_ , s)) =
  ⊢pair hM (preservation hN s)
preservation (⊢fst hM) (ξ-fst s) =
  ⊢fst (preservation hM s)
preservation (⊢fst (⊢pair hV hW)) (β-fst vV vW) = hV
preservation (⊢snd hM) (ξ-snd s) =
  ⊢snd (preservation hM s)
preservation (⊢snd (⊢pair hV hW)) (β-snd vV vW) = hW
preservation (⊢inl hM) (ξ-inl s) =
  ⊢inl (preservation hM s)
preservation (⊢inr hM) (ξ-inr s) =
  ⊢inr (preservation hM s)
preservation (⊢case⊎ hL hM hN) (ξ-case⊎ s) =
  ⊢case⊎ (preservation hL s) hM hN
preservation (⊢case⊎ (⊢inl hV) hM hN) (β-inl vV) =
  typing_single_subst hM hV
preservation (⊢case⊎ (⊢inr hV) hM hN) (β-inr vV) =
  typing_single_subst hN hV

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

noZeroFn : {A B : Ty} -> [] ⊢ `zero ⦂ (A ⇒ B) -> ⊥
noZeroFn ()

noSucFn : {A B : Ty} {M : Term} -> [] ⊢ (`suc M) ⦂ (A ⇒ B) -> ⊥
noSucFn ()

noUnitFn : {A B : Ty} -> [] ⊢ `unit ⦂ (A ⇒ B) -> ⊥
noUnitFn ()

noLamNat : {A : Ty} {N : Term} -> [] ⊢ (ƛ A ⇒ N) ⦂ nat -> ⊥
noLamNat ()

noUnitNat : [] ⊢ `unit ⦂ nat -> ⊥
noUnitNat ()

noPairFn : {A B : Ty} {V W : Term} -> [] ⊢ (pair V , W) ⦂ (A ⇒ B) -> ⊥
noPairFn ()

noInlFn : {A B C : Ty} {V : Term} -> [] ⊢ (inl V `to C) ⦂ (A ⇒ B) -> ⊥
noInlFn ()

noInrFn : {A B C : Ty} {V : Term} -> [] ⊢ (inr V `to C) ⦂ (A ⇒ B) -> ⊥
noInrFn ()

noPairNat : {V W : Term} -> [] ⊢ (pair V , W) ⦂ nat -> ⊥
noPairNat ()

noInlNat : {A : Ty} {V : Term} -> [] ⊢ (inl V `to A) ⦂ nat -> ⊥
noInlNat ()

noInrNat : {A : Ty} {V : Term} -> [] ⊢ (inr V `to A) ⦂ nat -> ⊥
noInrNat ()

noLamProd : {A B C : Ty} {N : Term} -> [] ⊢ (ƛ A ⇒ N) ⦂ (B `× C) -> ⊥
noLamProd ()

noZeroProd : {A B : Ty} -> [] ⊢ `zero ⦂ (A `× B) -> ⊥
noZeroProd ()

noSucProd : {A B : Ty} {M : Term} -> [] ⊢ (`suc M) ⦂ (A `× B) -> ⊥
noSucProd ()

noUnitProd : {A B : Ty} -> [] ⊢ `unit ⦂ (A `× B) -> ⊥
noUnitProd ()

noInlProd : {A B C : Ty} {V : Term} -> [] ⊢ (inl V `to C) ⦂ (A `× B) -> ⊥
noInlProd ()

noInrProd : {A B C : Ty} {V : Term} -> [] ⊢ (inr V `to C) ⦂ (A `× B) -> ⊥
noInrProd ()

noLamSum : {A B C : Ty} {N : Term} -> [] ⊢ (ƛ A ⇒ N) ⦂ (B `+ C) -> ⊥
noLamSum ()

noZeroSum : {A B : Ty} -> [] ⊢ `zero ⦂ (A `+ B) -> ⊥
noZeroSum ()

noSucSum : {A B : Ty} {M : Term} -> [] ⊢ (`suc M) ⦂ (A `+ B) -> ⊥
noSucSum ()

noUnitSum : {A B : Ty} -> [] ⊢ `unit ⦂ (A `+ B) -> ⊥
noUnitSum ()

noPairSum : {A B : Ty} {V W : Term} -> [] ⊢ (pair V , W) ⦂ (A `+ B) -> ⊥
noPairSum ()

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
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | `unit = ⊥-elim (noUnitFn hL)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | pair _ , _ = ⊥-elim (noPairFn hL)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | inl_`to_ _ _ = ⊥-elim (noInlFn hL)
progress-empty (⊢· hL hM) | inj₂ vL | inj₂ vM | inr_`to_ _ _ = ⊥-elim (noInrFn hL)
progress-empty (⊢as hM) with progress-empty hM
progress-empty (⊢as hM) | inj₁ (N , s) = inj₁ (_ , ξ-as s)
progress-empty (⊢as hM) | inj₂ vM = inj₁ (_ , β-as vM)
progress-empty (⊢let hM hN) with progress-empty hM
progress-empty (⊢let hM hN) | inj₁ (M' , s) = inj₁ (_ , ξ-let s)
progress-empty (⊢let hM hN) | inj₂ vM = inj₁ (_ , β-let vM)
progress-empty ⊢zero = inj₂ `zero
progress-empty ⊢unit = inj₂ `unit
progress-empty (⊢suc hM) with progress-empty hM
progress-empty (⊢suc hM) | inj₁ (N , s) = inj₁ (`suc N , ξ-suc s)
progress-empty (⊢suc hM) | inj₂ v = inj₂ (`suc v)
progress-empty (⊢case hL hM hN) with progress-empty hL
progress-empty (⊢case hL hM hN) | inj₁ (L' , s) = inj₁ (_ , ξ-case s)
progress-empty (⊢case hL hM hN) | inj₂ vL with vL
progress-empty (⊢case hL hM hN) | inj₂ vL | `zero = inj₁ (_ , β-zero)
progress-empty (⊢case hL hM hN) | inj₂ vL | `suc v = inj₁ (_ , β-suc v)
progress-empty (⊢case hL hM hN) | inj₂ vL | ƛ _ ⇒ _ = ⊥-elim (noLamNat hL)
progress-empty (⊢case hL hM hN) | inj₂ vL | `unit = ⊥-elim (noUnitNat hL)
progress-empty (⊢case hL hM hN) | inj₂ vL | pair _ , _ = ⊥-elim (noPairNat hL)
progress-empty (⊢case hL hM hN) | inj₂ vL | inl_`to_ _ _ = ⊥-elim (noInlNat hL)
progress-empty (⊢case hL hM hN) | inj₂ vL | inr_`to_ _ _ = ⊥-elim (noInrNat hL)
progress-empty (⊢pair hM hN) with progress-empty hM
progress-empty (⊢pair hM hN) | inj₁ (M' , s) = inj₁ (_ , ξ-pair₁ s)
progress-empty (⊢pair hM hN) | inj₂ vM with progress-empty hN
progress-empty (⊢pair hM hN) | inj₂ vM | inj₁ (N' , s) = inj₁ (_ , ξ-pair₂ (vM , s))
progress-empty (⊢pair hM hN) | inj₂ vM | inj₂ vN = inj₂ (pair vM , vN)
progress-empty (⊢fst hM) with progress-empty hM
progress-empty (⊢fst hM) | inj₁ (M' , s) = inj₁ (_ , ξ-fst s)
progress-empty (⊢fst hM) | inj₂ vM with vM
progress-empty (⊢fst hM) | inj₂ vM | pair vV , vW = inj₁ (_ , β-fst vV vW)
progress-empty (⊢fst hM) | inj₂ vM | ƛ _ ⇒ _ = ⊥-elim (noLamProd hM)
progress-empty (⊢fst hM) | inj₂ vM | `zero = ⊥-elim (noZeroProd hM)
progress-empty (⊢fst hM) | inj₂ vM | `suc _ = ⊥-elim (noSucProd hM)
progress-empty (⊢fst hM) | inj₂ vM | `unit = ⊥-elim (noUnitProd hM)
progress-empty (⊢fst hM) | inj₂ vM | inl_`to_ _ _ = ⊥-elim (noInlProd hM)
progress-empty (⊢fst hM) | inj₂ vM | inr_`to_ _ _ = ⊥-elim (noInrProd hM)
progress-empty (⊢snd hM) with progress-empty hM
progress-empty (⊢snd hM) | inj₁ (M' , s) = inj₁ (_ , ξ-snd s)
progress-empty (⊢snd hM) | inj₂ vM with vM
progress-empty (⊢snd hM) | inj₂ vM | pair vV , vW = inj₁ (_ , β-snd vV vW)
progress-empty (⊢snd hM) | inj₂ vM | ƛ _ ⇒ _ = ⊥-elim (noLamProd hM)
progress-empty (⊢snd hM) | inj₂ vM | `zero = ⊥-elim (noZeroProd hM)
progress-empty (⊢snd hM) | inj₂ vM | `suc _ = ⊥-elim (noSucProd hM)
progress-empty (⊢snd hM) | inj₂ vM | `unit = ⊥-elim (noUnitProd hM)
progress-empty (⊢snd hM) | inj₂ vM | inl_`to_ _ _ = ⊥-elim (noInlProd hM)
progress-empty (⊢snd hM) | inj₂ vM | inr_`to_ _ _ = ⊥-elim (noInrProd hM)
progress-empty (⊢inl hM) with progress-empty hM
progress-empty (⊢inl hM) | inj₁ (M' , s) = inj₁ (_ , ξ-inl s)
progress-empty (⊢inl {A = A} {B = B} hM) | inj₂ vM = inj₂ (inl_`to_ vM (A `+ B))
progress-empty (⊢inr hM) with progress-empty hM
progress-empty (⊢inr hM) | inj₁ (M' , s) = inj₁ (_ , ξ-inr s)
progress-empty (⊢inr {A = A} {B = B} hM) | inj₂ vM = inj₂ (inr_`to_ vM (A `+ B))
progress-empty (⊢case⊎ hL hM hN) with progress-empty hL
progress-empty (⊢case⊎ hL hM hN) | inj₁ (L' , s) = inj₁ (_ , ξ-case⊎ s)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL with vL
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | inl_`to_ v _ = inj₁ (_ , β-inl v)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | inr_`to_ v _ = inj₁ (_ , β-inr v)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | ƛ _ ⇒ _ = ⊥-elim (noLamSum hL)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | `zero = ⊥-elim (noZeroSum hL)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | `suc _ = ⊥-elim (noSucSum hL)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | `unit = ⊥-elim (noUnitSum hL)
progress-empty (⊢case⊎ hL hM hN) | inj₂ vL | pair _ , _ = ⊥-elim (noPairSum hL)

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

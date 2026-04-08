module extrinsic.Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z<s; s<s; s<s⁻¹)

open import extrinsic.Reduction
open import extrinsic.Ctx
open import extrinsic.TypeSubst as TS
open import extrinsic.TypeTermSubst using (cong₃)

------------------------------------------------------------------------
-- Well-formed renamings/substitutions on type variables
------------------------------------------------------------------------

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ' ρ = ∀ {X} → X < Δ → ρ X < Δ'

TySubstWf : TyCtx → TyCtx → Substᵗ → Set
TySubstWf Δ Δ' σ = ∀ {X} → X < Δ → WfTy Δ' (σ X)

TyRenameWf-ext :
  {Δ Δ' : TyCtx} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  TyRenameWf (suc Δ) (suc Δ') (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s x<Δ) = s<s (hρ {X} x<Δ)

renameᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {A : Ty} {ρ : Renameᵗ} →
  WfTy Δ A →
  TyRenameWf Δ Δ' ρ →
  WfTy Δ' (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfVar x<Δ) hρ = wfVar (hρ x<Δ)
renameᵗ-preserves-WfTy wf`ℕ hρ = wf`ℕ
renameᵗ-preserves-WfTy wf`Bool hρ = wf`Bool
renameᵗ-preserves-WfTy (wfFn hA hB) hρ =
  wfFn (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf`∀ hA) hρ =
  wf`∀ (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))

TySubstWf-exts :
  {Δ Δ' : TyCtx} {σ : Substᵗ} →
  TySubstWf Δ Δ' σ →
  TySubstWf (suc Δ) (suc Δ') (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wfVar z<s
TySubstWf-exts hσ {suc X} (s<s x<Δ) =
  renameᵗ-preserves-WfTy
    (hσ {X} x<Δ)
    (λ {i} i<Δ' → s<s i<Δ')

substᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {A : Ty} {σ : Substᵗ} →
  WfTy Δ A →
  TySubstWf Δ Δ' σ →
  WfTy Δ' (substᵗ σ A)
substᵗ-preserves-WfTy (wfVar x<Δ) hσ = hσ x<Δ
substᵗ-preserves-WfTy wf`ℕ hσ = wf`ℕ
substᵗ-preserves-WfTy wf`Bool hσ = wf`Bool
substᵗ-preserves-WfTy (wfFn hA hB) hσ =
  wfFn (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy (wf`∀ hA) hσ =
  wf`∀ (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))

------------------------------------------------------------------------
-- Renaming type variables in typing derivations
------------------------------------------------------------------------

map-renameᵗ-⤊ : (ρ : Renameᵗ) (Γ : Ctx) →
  map (renameᵗ (extᵗ ρ)) (⤊ Γ) ≡ ⤊ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ ρ [] = refl
map-renameᵗ-⤊ ρ (A ∷ Γ) =
  cong₂ _∷_
    (trans
      (rename-rename-commute suc (extᵗ ρ) A)
      (trans
        (TS.rename-cong (λ i → refl) A)
        (sym (rename-rename-commute ρ suc A))))
    (map-renameᵗ-⤊ ρ Γ)

typing-renameᵀ : {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ' ∣ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ hρ (⊢` h) =
  ⊢` (lookup-map-renameᵗ h)
typing-renameᵀ hρ (⊢ƛ hA hN) =
  ⊢ƛ
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ hρ hN)
typing-renameᵀ hρ (⊢· hL hM) =
  ⊢· (typing-renameᵀ hρ hL) (typing-renameᵀ hρ hM)
typing-renameᵀ hρ ⊢true = ⊢true
typing-renameᵀ hρ ⊢false = ⊢false
typing-renameᵀ hρ ⊢zero = ⊢zero
typing-renameᵀ hρ (⊢suc hM) = ⊢suc (typing-renameᵀ hρ hM)
typing-renameᵀ hρ (⊢if hL hM hN) =
  ⊢if
    (typing-renameᵀ hρ hL)
    (typing-renameᵀ hρ hM)
    (typing-renameᵀ hρ hN)
typing-renameᵀ hρ (⊢case hL hM hN) =
  ⊢case
    (typing-renameᵀ hρ hL)
    (typing-renameᵀ hρ hM)
    (typing-renameᵀ hρ hN)
typing-renameᵀ {Δ' = Δ'} {ρ = ρ} hρ (⊢Λ {Γ = Γ} {N = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ Ψ → suc Δ' ∣ Ψ ⊢ renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameᵗ-⤊ ρ Γ)
      (typing-renameᵀ
        {Γ = ⤊ Γ}
        {ρ = extᵗ ρ}
        (TyRenameWf-ext {ρ = ρ} hρ)
        hN))
typing-renameᵀ {Γ = Γ} {ρ = ρ} hρ (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → _ ∣ map (renameᵗ ρ) Γ ⊢ (renameᵀ ρ M ·[ renameᵗ ρ B ]) ⦂ T)
    (sym (rename-[]ᵗ-commute ρ A B))
    (⊢·[]
      (typing-renameᵀ hρ hM)
      (renameᵗ-preserves-WfTy hB hρ))

------------------------------------------------------------------------
-- Substituting type variables in typing derivations
------------------------------------------------------------------------

map-substᵗ-⤊ : (σ : Substᵗ) (Γ : Ctx) →
  map (substᵗ (extsᵗ σ)) (⤊ Γ) ≡ ⤊ (map (substᵗ σ) Γ)
map-substᵗ-⤊ σ [] = refl
map-substᵗ-⤊ σ (A ∷ Γ) =
  cong₂ _∷_
    (trans
      (rename-subst-commute suc (extsᵗ σ) A)
      (sym (rename-subst suc σ A)))
    (map-substᵗ-⤊ σ Γ)

typing-substᵀ : {Δ Δ' : TyCtx} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  TySubstWf Δ Δ' σ →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ' ∣ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ hσ (⊢` h) =
  ⊢` (lookup-map-substᵗ h)
typing-substᵀ hσ (⊢ƛ hA hN) =
  ⊢ƛ
    (substᵗ-preserves-WfTy hA hσ)
    (typing-substᵀ hσ hN)
typing-substᵀ hσ (⊢· hL hM) =
  ⊢· (typing-substᵀ hσ hL) (typing-substᵀ hσ hM)
typing-substᵀ hσ ⊢true = ⊢true
typing-substᵀ hσ ⊢false = ⊢false
typing-substᵀ hσ ⊢zero = ⊢zero
typing-substᵀ hσ (⊢suc hM) = ⊢suc (typing-substᵀ hσ hM)
typing-substᵀ hσ (⊢if hL hM hN) =
  ⊢if
    (typing-substᵀ hσ hL)
    (typing-substᵀ hσ hM)
    (typing-substᵀ hσ hN)
typing-substᵀ hσ (⊢case hL hM hN) =
  ⊢case
    (typing-substᵀ hσ hL)
    (typing-substᵀ hσ hM)
    (typing-substᵀ hσ hN)
typing-substᵀ {Δ' = Δ'} {σ = σ} hσ (⊢Λ {Γ = Γ} {N = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ Ψ → suc Δ' ∣ Ψ ⊢ substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
      (map-substᵗ-⤊ σ Γ)
      (typing-substᵀ
        {Γ = ⤊ Γ}
        {σ = extsᵗ σ}
        (TySubstWf-exts hσ)
        hN))
typing-substᵀ {Γ = Γ} {σ = σ} hσ (⊢·[] {M = M} {A = A} {B = B} hM hB) =
  Eq.subst
    (λ T → _ ∣ map (substᵗ σ) Γ ⊢ (substᵀ σ M ·[ substᵗ σ B ]) ⦂ T)
    (sym (subst-[]ᵗ-commute σ A B))
    (⊢·[]
      (typing-substᵀ hσ hM)
      (substᵗ-preserves-WfTy hB hσ))

singleTySubstWf : {Δ : TyCtx} {B : Ty} →
  WfTy Δ B →
  TySubstWf (suc Δ) Δ (singleTyEnv B)
singleTySubstWf hB {zero} z<s = hB
singleTySubstWf hB {suc X} (s<s x<Δ) = wfVar x<Δ

------------------------------------------------------------------------
-- Well-formedness of typing derivations
------------------------------------------------------------------------

ctxWf-⤊ : ∀ {Δ Γ} → CtxWf Δ Γ → CtxWf (suc Δ) (⤊ Γ)
ctxWf-⤊ {Δ = Δ} hΓ h with lookup-map-inv h
... | A , (hA , eq) rewrite eq =
  renameᵗ-preserves-WfTy (hΓ hA) (λ {i} i<Δ → s<s i<Δ)

typing-wf : ∀ {Δ Γ A} {M : Term}
  → CtxWf Δ Γ
  → Δ ∣ Γ ⊢ M ⦂ A
  → WfTy Δ A
typing-wf hΓ (⊢` h) = hΓ h
typing-wf hΓ (⊢ƛ hA hN) = wfFn hA (typing-wf (ctxWf-∷ hA hΓ) hN)
typing-wf hΓ (⊢· hL hM) with typing-wf hΓ hL
... | wfFn _ hB = hB
typing-wf hΓ ⊢true = wf`Bool
typing-wf hΓ ⊢false = wf`Bool
typing-wf hΓ ⊢zero = wf`ℕ
typing-wf hΓ (⊢suc hM) = wf`ℕ
typing-wf hΓ (⊢case hL hM hN) = typing-wf hΓ hM
typing-wf hΓ (⊢if hL hM hN) = typing-wf hΓ hM
typing-wf hΓ (⊢Λ hN) = wf`∀ (typing-wf (ctxWf-⤊ hΓ) hN)
typing-wf hΓ (⊢·[] hM hB) with typing-wf hΓ hM
... | wf`∀ hA = substᵗ-preserves-WfTy hA (singleTySubstWf hB)

closed-typing-wf : ∀ {A : Ty} {M : Term}
  → 0 ∣ [] ⊢ M ⦂ A
  → WfTy 0 A
closed-typing-wf = typing-wf ctxWf-[]

------------------------------------------------------------------------
-- Type-substitution cancellation under shifted contexts
------------------------------------------------------------------------

substᵗ-renameᵗ-cancel : (C B : Ty) →
  substᵗ (singleTyEnv B) (renameᵗ suc C) ≡ C
substᵗ-renameᵗ-cancel C B =
  trans
    (rename-subst-commute suc (singleTyEnv B) C)
    (subst-id C)

singleTySubst-⤊-cancel : (Γ : Ctx) (B : Ty) →
  map (substᵗ (singleTyEnv B)) (⤊ Γ) ≡ Γ
singleTySubst-⤊-cancel [] B = refl
singleTySubst-⤊-cancel (C ∷ Γ) B =
  cong₂ _∷_
    (substᵗ-renameᵗ-cancel C B)
    (singleTySubst-⤊-cancel Γ B)

typing-single-substᵀ : {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
  (suc Δ) ∣ (⤊ Γ) ⊢ M ⦂ A →
  WfTy Δ B →
  Δ ∣ Γ ⊢ M [ B ]ᵀ ⦂ A [ B ]ᵗ
typing-single-substᵀ {Δ} {Γ} {M} {A} {B} hM hB =
  Eq.subst
    (λ Ψ → Δ ∣ Ψ ⊢ M [ B ]ᵀ ⦂ A [ B ]ᵗ)
    (singleTySubst-⤊-cancel Γ B)
    (typing-substᵀ (singleTySubstWf hB) hM)

------------------------------------------------------------------------
-- Substituting term variables in typing derivations
------------------------------------------------------------------------

RenameWf : Ctx → Ctx → Rename → Set
RenameWf Γ Γ' ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ' ∋ ρ x ⦂ A

SubstWf : TyCtx → Ctx → Ctx → Subst → Set
SubstWf Δ Γ Γ' σ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Γ' ⊢ σ x ⦂ A

RenameWf-ext : {Γ Γ' : Ctx} {B : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ') (ext ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

typing-rename : {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Γ' ⊢ rename ρ M ⦂ A
typing-rename hρ (⊢` h) = ⊢` (hρ h)
typing-rename hρ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-rename (RenameWf-ext hρ) hN)
typing-rename hρ (⊢· hL hM) =
  ⊢· (typing-rename hρ hL) (typing-rename hρ hM)
typing-rename hρ ⊢true = ⊢true
typing-rename hρ ⊢false = ⊢false
typing-rename hρ ⊢zero = ⊢zero
typing-rename hρ (⊢suc hM) = ⊢suc (typing-rename hρ hM)
typing-rename hρ (⊢if hL hM hN) =
  ⊢if
    (typing-rename hρ hL)
    (typing-rename hρ hM)
    (typing-rename hρ hN)
typing-rename hρ (⊢case hL hM hN) =
  ⊢case
    (typing-rename hρ hL)
    (typing-rename hρ hM)
    (typing-rename (RenameWf-ext hρ) hN)
typing-rename {Γ = Γ} {Γ' = Γ'} {ρ = ρ} hρ (⊢Λ hN) =
  ⊢Λ (typing-rename hρ' hN)
  where
    hρ' : RenameWf (⤊ Γ) (⤊ Γ') ρ
    hρ' h with lookup-map-inv h
    ... | A , (hA , eq)
      rewrite eq = lookup-map-renameᵗ (hρ hA)
typing-rename hρ (⊢·[] hM hB) =
  ⊢·[] (typing-rename hρ hM) hB

typing-rename-shift : {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ (B ∷ Γ) ⊢ rename suc M ⦂ A
typing-rename-shift hM =
  typing-rename (λ {x} {A} h → S h) hM

SubstWf-exts : {Δ : TyCtx} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
  SubstWf Δ Γ Γ' σ →
  SubstWf Δ (B ∷ Γ) (B ∷ Γ') (exts σ)
SubstWf-exts hσ Z = ⊢` Z
SubstWf-exts hσ (S h) = typing-rename-shift (hσ h)

SubstWf-⇑ : {Δ : TyCtx} {Γ Γ' : Ctx} {σ : Subst} →
  SubstWf Δ Γ Γ' σ →
  SubstWf (suc Δ) (⤊ Γ) (⤊ Γ') (⇑ σ)
SubstWf-⇑ hσ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = typing-renameᵀ (λ {i} i<Δ → s<s i<Δ) (hσ hA)

typing-subst : {Δ : TyCtx} {Γ Γ' : Ctx} {M : Term} {A : Ty} {σ : Subst} →
  SubstWf Δ Γ Γ' σ →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Γ' ⊢ subst σ M ⦂ A
typing-subst hσ (⊢` h) = hσ h
typing-subst hσ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-subst (SubstWf-exts hσ) hN)
typing-subst hσ (⊢· hL hM) =
  ⊢· (typing-subst hσ hL) (typing-subst hσ hM)
typing-subst hσ ⊢true = ⊢true
typing-subst hσ ⊢false = ⊢false
typing-subst hσ ⊢zero = ⊢zero
typing-subst hσ (⊢suc hM) = ⊢suc (typing-subst hσ hM)
typing-subst hσ (⊢if hL hM hN) =
  ⊢if
    (typing-subst hσ hL)
    (typing-subst hσ hM)
    (typing-subst hσ hN)
typing-subst hσ (⊢case hL hM hN) =
  ⊢case
    (typing-subst hσ hL)
    (typing-subst hσ hM)
    (typing-subst (SubstWf-exts hσ) hN)
typing-subst hσ (⊢Λ hN) =
  ⊢Λ (typing-subst (SubstWf-⇑ hσ) hN)
typing-subst hσ (⊢·[] hM hB) =
  ⊢·[] (typing-subst hσ hM) hB

singleSubstWf : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {V : Term} →
  Δ ∣ Γ ⊢ V ⦂ A →
  SubstWf Δ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢` h

typing-single-subst : {Δ : TyCtx} {Γ : Ctx} {N V : Term} {A B : Ty} →
  Δ ∣ (A ∷ Γ) ⊢ N ⦂ B →
  Δ ∣ Γ ⊢ V ⦂ A →
  Δ ∣ Γ ⊢ N [ V ] ⦂ B
typing-single-subst hN hV =
  typing-subst (singleSubstWf hV) hN

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation : {Δ : TyCtx} {Γ : Ctx} {M N : Term} {A : Ty} →
  Δ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Γ ⊢ N ⦂ A
preservation (⊢· (⊢ƛ hA hN) hW) (β-ƛ vW) =
  typing-single-subst hN hW
preservation (⊢· hL hM) (ξ-·₁ s) =
  ⊢· (preservation hL s) hM
preservation (⊢· hL hM) (ξ-·₂ vV s) =
  ⊢· hL (preservation hM s)
preservation (⊢if hL hM hN) (ξ-if s) =
  ⊢if (preservation hL s) hM hN
preservation (⊢if hL hM hN) β-true = hM
preservation (⊢if hL hM hN) β-false = hN
preservation (⊢suc hM) (ξ-suc s) =
  ⊢suc (preservation hM s)
preservation (⊢case hL hM hN) (ξ-case s) =
  ⊢case (preservation hL s) hM hN
preservation (⊢case hL hM hN) β-zero = hM
preservation (⊢case (⊢suc hV) hM hN) (β-suc vV) =
  typing-single-subst hN hV
preservation (⊢·[] (⊢Λ hN) hB) (β-Λ {A = A}) =
  typing-single-substᵀ hN hB
preservation (⊢·[] hM hB) (ξ-·[] s) =
  ⊢·[] (preservation hM s) hB

multi-preservation : {Δ : TyCtx} {Γ : Ctx} {M N : Term} {A : Ty} →
  Δ ∣ Γ ⊢ M ⦂ A →
  M —↠ N →
  Δ ∣ Γ ⊢ N ⦂ A
multi-preservation hM (_ ∎) = hM
multi-preservation hM (_ —→⟨ s ⟩ ms) =
  multi-preservation (preservation hM s) ms

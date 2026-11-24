module proof.LR.FrameProps where

-- File Charter:
--   * Reduction under an evaluation frame (`LR.Frame`): a step of the
--     plugged term carries the frame along the step's store embedding,
--     and blame under a frame steps to blame.
--   * The reduction rules carry a frame's parts with the store-change
--     functions (`applyTerm`, `applyConsistency`, ...); these agree, as
--     terms, with renaming along the change's embedding.
--   * Counted reductions concatenate, and the embedding of concatenated
--     store changes is the composite embedding.

import Data.Fin as Fin
open import Data.Nat using (zero; suc; _+_)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types
open import Consistency using (Env∼; X∼X; _⊢_∼_; rename∼; renameEnv∼;
  renameEnv∼-preserves; renameᵐᶜ; _↪ᵗ_; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import CastTerms hiding (subst)
open import Reduction
open import proof.Reduction using (_++χ_)
open import proof.DGG.CenterRename using (_∘↪_)
open import proof.TypeInTermSubst using (toRename-id-eq; toRename-wk-eq;
  renameᵗ-wk-eq)
open import proof.TermRename
open import proof.LR.WorldProps using (renameTy-id; renameTy-∘; ∘↪-idʳ;
  ∘↪-assoc)
open import LR.Steps
open import LR.Frame

private
  variable
    Δ Δ′ Δ″ : TyCtx

------------------------------------------------------------------------
-- Store changes are renamings
------------------------------------------------------------------------

applyTerm-rename : (χ : StoreChange Δ Δ′) (M : Term Δ)
  → renameᵗᵐ (embedᶜ χ) M ≡ applyTerm χ M
applyTerm-rename keep M = renameᵗᵐ-id M
applyTerm-rename (bind A) M = refl

applyTy-rename : (χ : StoreChange Δ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (embedᶜ χ)) A ≡ applyTy χ A
applyTy-rename keep A = renameTy-id A
applyTy-rename (bind C) A = renameᵗ-wk-eq A

applyBody-rename : (χ : StoreChange Δ Δ′) (B : Ty (suc Δ))
  → renameᵗ (toRenameᵗ (Consistency.keep (embedᶜ χ))) B ≡ applyBody χ B
applyBody-rename keep B = renameTy-id B
applyBody-rename (bind C) B = renameᵗ-cong B h
  where
  h : ∀ X → toRenameᵗ (Consistency.keep wk↪ᵗ) X ≡ extᵗ Fin.suc X
  h Fin.zero = refl
  h (Fin.suc X) = cong Fin.suc (toRename-wk-eq X)

applyVar-rename : (χ : StoreChange Δ Δ′) (X : TyVar Δ)
  → applyVar χ X ≡ toRenameᵗ (embedᶜ χ) X
applyVar-rename keep X = sym (toRename-id-eq X)
applyVar-rename (bind A) X = sym (toRename-wk-eq X)

applyConsistency-rename : ∀ {μ : Env∼ Δ} {A B : Ty Δ}
    (χ : StoreChange Δ Δ′) (N : Term Δ′) (c : μ ⊢ A ∼ B)
  → N ⟨ applyConsistency χ c ⟩ ≡ N ⟨ renameᵐᶜ (embedᶜ χ) c ⟩
applyConsistency-rename {μ = μ} keep N c =
  sym (cast-id {ν = renameEnv∼ id↪ᵗ μ} (toRenameᵗ id↪ᵗ)
    (renameEnv∼-preserves id↪ᵗ μ) refl (renameEnv∼-id μ)
    toRename-id-eq c)
applyConsistency-rename {μ = μ} (bind A) N c =
  cast-cong Fin.suc (toRenameᵗ wk↪ᵗ) (λ X → refl)
    (renameEnv∼-preserves wk↪ᵗ μ) refl
    (cong (X∼X ∷_) (sym (renameEnv∼-id μ)))
    (λ X → sym (toRename-wk-eq X)) c

------------------------------------------------------------------------
-- Renaming frames
------------------------------------------------------------------------

plug-rename-id : (F : Frame Δ) (N : Term Δ)
  → plug (renameFrame id↪ᵗ F) N ≡ plug F N
plug-rename-id (app₁ M) N = cong (N ·_) (renameᵗᵐ-id M)
plug-rename-id (app₂ V v) N = cong (_· N) (renameᵗᵐ-id V)
plug-rename-id (tyApp B A) N =
  cong₂ (λ B′ A′ → N ⦂∀ B′ [ A′ ]) (renameTy-id B) (renameTy-id A)
plug-rename-id (cast {μ = μ} c) N =
  cast-id {ν = renameEnv∼ id↪ᵗ μ} (toRenameᵗ id↪ᵗ)
    (renameEnv∼-preserves id↪ᵗ μ) refl (renameEnv∼-id μ)
    toRename-id-eq c
plug-rename-id (reveal c) N = ↑-cong refl (rename↑-id toRename-id-eq c)
plug-rename-id (conceal c) N = ↓-cong refl (rename↓-id toRename-id-eq c)
plug-rename-id (prim₁ op M) N = cong (N ⊕[ op ]_) (renameᵗᵐ-id M)
plug-rename-id (prim₂ V v op) N = cong (_⊕[ op ] N) (renameᵗᵐ-id V)

plug-rename-∘ : (π : Δ′ ↪ᵗ Δ″) (η : Δ ↪ᵗ Δ′) (F : Frame Δ) (N : Term Δ″)
  → plug (renameFrame π (renameFrame η F)) N
    ≡ plug (renameFrame (π ∘↪ η) F) N
plug-rename-∘ π η (app₁ M) N = cong (N ·_) (renameᵗᵐ-∘ π η M)
plug-rename-∘ π η (app₂ V v) N = cong (_· N) (renameᵗᵐ-∘ π η V)
plug-rename-∘ π η (tyApp B A) N =
  cong₂ (λ B′ A′ → N ⦂∀ B′ [ A′ ])
    (renameTy-∘ (Consistency.keep π) (Consistency.keep η) B)
    (renameTy-∘ π η A)
plug-rename-∘ π η (cast {μ = μ} c) N =
  cast-∘ {μ₂ = renameEnv∼ η μ} {ν = renameEnv∼ π (renameEnv∼ η μ)}
    {ν′ = renameEnv∼ (π ∘↪ η) μ}
    (toRenameᵗ η) (toRenameᵗ π) (toRenameᵗ (π ∘↪ η))
    (renameEnv∼-preserves η μ)
    (renameEnv∼-preserves π (renameEnv∼ η μ))
    (renameEnv∼-preserves (π ∘↪ η) μ)
    refl (renameEnv∼-∘ π η μ) (toRenameᵗ-∘′ π η) c
plug-rename-∘ π η (reveal c) N =
  ↑-cong refl (rename↑-∘ (toRenameᵗ-∘′ π η) c)
plug-rename-∘ π η (conceal c) N =
  ↓-cong refl (rename↓-∘ (toRenameᵗ-∘′ π η) c)
plug-rename-∘ π η (prim₁ op M) N = cong (N ⊕[ op ]_) (renameᵗᵐ-∘ π η M)
plug-rename-∘ π η (prim₂ V v op) N =
  cong (_⊕[ op ] N) (renameᵗᵐ-∘ π η V)

------------------------------------------------------------------------
-- Reduction under a frame
------------------------------------------------------------------------

frame-step : ∀ {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
    (F : Frame Δ)
  → M —→[ χ ] N
  → plug F M —→[ χ ] plug (renameFrame (embedᶜ χ) F) N
frame-step {χ = χ} (app₁ M) s = ξ-·₁ s (applyTerm-rename χ M)
frame-step {χ = χ} (app₂ V v) s = ξ-·₂ v s (applyTerm-rename χ V)
frame-step {χ = χ} (tyApp B A) s =
  ξ-• s (applyBody-rename χ B) (applyTy-rename χ A)
frame-step {M = M} {N = N} {χ = χ} (cast c) s =
  subst (λ T → M ⟨ c ⟩ —→[ χ ] T) (applyConsistency-rename χ N c)
    (ξ-⟨⟩ s refl)
frame-step {M = M} {N = N} {χ = χ} (reveal c) s =
  subst (λ T → M ↑ c —→[ χ ] T)
    (↑-cong refl (rename↑-cong (applyVar-rename χ) c))
    (ξ-reveal s refl)
frame-step {M = M} {N = N} {χ = χ} (conceal c) s =
  subst (λ T → M ↓ c —→[ χ ] T)
    (↓-cong refl (rename↓-cong (applyVar-rename χ) c))
    (ξ-conceal s refl)
frame-step {χ = χ} (prim₁ op M) s = ξ-⊕₁ s (applyTerm-rename χ M)
frame-step {χ = χ} (prim₂ V v op) s = ξ-⊕₂ v s (applyTerm-rename χ V)

frame-blame : (F : Frame Δ) → plug F blame —→[ keep ] blame
frame-blame (app₁ M) = pure-step blame-·₁
frame-blame (app₂ V v) = pure-step (blame-·₂ v)
frame-blame (tyApp B A) = pure-step blame-•
frame-blame (cast c) = pure-step blame-⟨⟩
frame-blame (reveal c) = pure-step blame-reveal
frame-blame (conceal c) = pure-step blame-conceal
frame-blame (prim₁ op M) = pure-step blame-⊕₁
frame-blame (prim₂ V v op) = pure-step (blame-⊕₂ v)

frame-steps : ∀ {k} {M : Term Δ} {N : Term Δ′} {χs : StoreChanges Δ Δ′}
    (F : Frame Δ)
  → M —→^ k [ χs ] N
  → plug F M —→^ k [ χs ] plug (renameFrame (embedᶜˢ χs) F) N
frame-steps {M = M} F none =
  subst (λ T → plug F M —→^ zero [ [] ] T) (sym (plug-rename-id F M)) none
frame-steps F (more {k = k} {N = N} {P = P} {χ = χ} {χs = χs} s ss) =
  more (frame-step F s)
    (subst (λ T → plug (renameFrame (embedᶜ χ) F) N —→^ k [ χs ] T)
      (plug-rename-∘ (embedᶜˢ χs) (embedᶜ χ) F P)
      (frame-steps (renameFrame (embedᶜ χ) F) ss))

frame-↠ : ∀ {M : Term Δ} {N : Term Δ′} {χs : StoreChanges Δ Δ′}
    (F : Frame Δ)
  → M —↠[ χs ] N
  → plug F M —↠[ χs ] plug (renameFrame (embedᶜˢ χs) F) N
frame-↠ {M = M} F ↠-refl =
  subst (λ T → plug F M —↠[ [] ] T) (sym (plug-rename-id F M)) ↠-refl
frame-↠ F (↠-step {N = N} {P = P} {χ = χ} {χs = χs} s ss) =
  ↠-step (frame-step F s)
    (subst (λ T → plug (renameFrame (embedᶜ χ) F) N —↠[ χs ] T)
      (plug-rename-∘ (embedᶜˢ χs) (embedᶜ χ) F P)
      (frame-↠ (renameFrame (embedᶜ χ) F) ss))

------------------------------------------------------------------------
-- Concatenating counted reductions
------------------------------------------------------------------------

steps-++ : ∀ {Δ₀ Δ₁ Δ₂ j k} {M : Term Δ₀} {N : Term Δ₁} {P : Term Δ₂}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
  → M —→^ j [ χs ] N → N —→^ k [ ψs ] P → M —→^ j + k [ χs ++χ ψs ] P
steps-++ none ss = ss
steps-++ (more s ss₁) ss₂ = more s (steps-++ ss₁ ss₂)

steps-snoc : ∀ {Δ₀ Δ₁ Δ₂ k} {M : Term Δ₀} {N : Term Δ₁} {P : Term Δ₂}
    {χs : StoreChanges Δ₀ Δ₁} {χ : StoreChange Δ₁ Δ₂}
  → M —→^ k [ χs ] N → N —→[ χ ] P → M —→^ suc k [ χs ++χ (χ ∷ []) ] P
steps-snoc none s = more s none
steps-snoc (more s′ ss) s = more s′ (steps-snoc ss s)

embedᶜˢ-++ : ∀ {Δ₀ Δ₁ Δ₂}
    (χs : StoreChanges Δ₀ Δ₁) (ψs : StoreChanges Δ₁ Δ₂)
  → embedᶜˢ (χs ++χ ψs) ≡ embedᶜˢ ψs ∘↪ embedᶜˢ χs
embedᶜˢ-++ [] ψs = sym (∘↪-idʳ (embedᶜˢ ψs))
embedᶜˢ-++ (χ ∷ χs) ψs =
  trans (cong (_∘↪ embedᶜ χ) (embedᶜˢ-++ χs ψs))
    (∘↪-assoc (embedᶜˢ ψs) (embedᶜˢ χs) (embedᶜ χ))

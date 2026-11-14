module LR.Frame where

-- File Charter:
--   * One-layer evaluation frames, plugging, and renaming a frame along
--     an embedding of type contexts.  The bind lemma of the logical
--     relation is stated with them (notes/logrel-dgg.md, Section 6.9,
--     item 3).

open import Data.Nat using (suc)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _↪ᵗ_; keep; toRenameᵗ;
  renameᵐᶜ)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import Primitives using (Prim)
open import CastTerms using (Term; Value; _·_; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_;
  _⊕[_]_; renameᵗᵐ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)

private
  variable
    Δ Δ′ : TyCtx

data Frame (Δ : TyCtx) : Set where
  -- □ · M
  app₁ : Term Δ → Frame Δ
  -- V · □
  app₂ : (V : Term Δ) → Value V → Frame Δ
  -- □ ⦂∀ B [ A ]
  tyApp : Ty (suc Δ) → Ty Δ → Frame Δ
  -- □ ⟨ c ⟩
  cast : ∀ {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Frame Δ
  -- □ ↑ c
  reveal : ∀ {A B : Ty Δ} → Conv↑ Δ A B → Frame Δ
  -- □ ↓ c
  conceal : ∀ {A B : Ty Δ} → Conv↓ Δ A B → Frame Δ
  -- □ ⊕[ op ] M
  prim₁ : Prim → Term Δ → Frame Δ
  -- V ⊕[ op ] □
  prim₂ : (V : Term Δ) → Value V → Prim → Frame Δ

plug : Frame Δ → Term Δ → Term Δ
plug (app₁ M) L = L · M
plug (app₂ V v) M = V · M
plug (tyApp B A) L = L ⦂∀ B [ A ]
plug (cast c) M = M ⟨ c ⟩
plug (reveal c) M = M ↑ c
plug (conceal c) M = M ↓ c
plug (prim₁ op M) L = L ⊕[ op ] M
plug (prim₂ V v op) M = V ⊕[ op ] M

renameFrame : Δ ↪ᵗ Δ′ → Frame Δ → Frame Δ′
renameFrame ρ (app₁ M) = app₁ (renameᵗᵐ ρ M)
renameFrame ρ (app₂ V v) =
  app₂ (renameᵗᵐ ρ V) (renameᵗᵐ-preserves-Value ρ v)
renameFrame ρ (tyApp B A) =
  tyApp (renameᵗ (toRenameᵗ (keep ρ)) B) (renameᵗ (toRenameᵗ ρ) A)
renameFrame ρ (cast c) = cast (renameᵐᶜ ρ c)
renameFrame ρ (reveal c) = reveal (rename↑ (toRenameᵗ ρ) c)
renameFrame ρ (conceal c) = conceal (rename↓ (toRenameᵗ ρ) c)
renameFrame ρ (prim₁ op M) = prim₁ op (renameᵗᵐ ρ M)
renameFrame ρ (prim₂ V v op) =
  prim₂ (renameᵗᵐ ρ V) (renameᵗᵐ-preserves-Value ρ v) op

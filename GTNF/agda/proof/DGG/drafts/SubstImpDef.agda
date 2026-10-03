module proof.DGG.drafts.SubstImpDef where

-- File Charter:
--   * DRAFT STATEMENT (2026-10-03), NOT APPROVED: substituting related
--     images into related terms preserves `⊑` (PLAN.md §3 `Subst⊑`).
--     For review (drafts/STATEMENTS.md).
--   * GENERALIZED FOR ITS INDUCTION: an arbitrary pair of parallel
--     substitutions σ, σ′ (TermSubst's `substᵐ`), pointwise related on
--     γ by `ImgImp`, into an arbitrary target context γ₁; `extᴵ` (under
--     `ƛ⊑ƛ`) and `⇑ᴵ` (under `Λ⊑Λ`, `Λ⊑`) stay in that form.  The two
--     sides' images have the same shape at each variable (both `Beta`s
--     substitute; a one-sided Beta never meets a `·⊑·`).
--   * The consumer form is `SubstImpBeta`: one Beta on each side.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax)

open import Types using (Ty)
open import Ctx using (Ctxᵗ)
open import Terms using (Term; Value; Var)
open import TermSubst using (Img; ivar; ival; substᵐ; _[_∶_]ᵐ)
open import ImprecisionWorld
open import TermImprecision using (_∣_⊢_⊑_∶_)

private
  variable
    Δ Δ′ : Ctxᵗ

-- an image pair for one entry of γ, read in the target context γ₁:
-- two variables with the entry's types in γ₁, or two related closed
-- values (any index: the proof of the types is not fixed)
data ImgImp {W : World Δ Δ′} (γ₁ : CtxImp W)
    : Img → Img → CtxImpEntry W → Set where
  ivar⊑ivar : ∀ {y A A′} {p q : A ⊑ᵂ⟨ W ⟩ A′}
    → γ₁ ∋ʷ y ⦂ ctx-imp A A′ q
    → ImgImp γ₁ (ivar y) (ivar y) (ctx-imp A A′ p)
  ival⊑ival : ∀ {V V′ A A′} {p q : A ⊑ᵂ⟨ W ⟩ A′}
    → Value V → Value V′
    → W ∣ [] ⊢ V ⊑ V′ ∶ q
    → ImgImp γ₁ (ival V A) (ival V′ A′) (ctx-imp A A′ p)

SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)

-- the consumer form (SimBeta-Beta, SimBackBeta-Beta, after CastFun)
SubstImpBeta : Set
SubstImpBeta = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA pV : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
  → W ∣ ctx-imp A A′ pA ∷ [] ⊢ N ⊑ N′ ∶ pB
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ∶ pV
  → Σ[ q ∈ B ⊑ᵂ⟨ W ⟩ B′ ] (W ∣ [] ⊢ N [ V ∶ A ]ᵐ ⊑ N′ [ V′ ∶ A′ ]ᵐ ∶ q)

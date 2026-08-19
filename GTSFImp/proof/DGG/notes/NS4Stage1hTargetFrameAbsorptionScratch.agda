module proof.DGG.notes.NS4Stage1hTargetFrameAbsorptionScratch where

-- File Charter:
--   * Calibrates the NS-4 stage 1h target-frame absorption-chain surface.
--   * Keeps the negative control from stage 1g: final `q` alone is not the
--     cast-frame intermediate witness.
--   * Checks the statement indices for C1-C4 before live proof edits.
--   * This notes-only module is checked directly with the notes directory
--     included and is not imported by `All.agda`.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ＇_; `∀; ⇑ᵗ; _[_]ᵗ)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; _[_]ᶜ)
open import Conversion using (Conv↑; Conv↓; replaceTy; 〖_,_↑_〗)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using (keep; bind; applyTy; applyBody)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef


data TargetFrameAbsorptionChain {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ) (γ : CTX.CtxImp W)
    (A : Ty Δᴸ) :
    ∀ {B E : Ty Δᴿ}
    → InstantiationSpine B E
    → A CTX.⊑ᵂ⟨ W ⟩ E
    → Set₁ where

  tfa-[] : ∀ {B} {q : A CTX.⊑ᵂ⟨ W ⟩ B}
    → TargetFrameAbsorptionChain W γ A []ⁱ q

  tfa-type : ∀ {B C E}
      {eq : B ≡ C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A
        (type-transport-frame eq ▻ⁱ spine) q

  tfa-name : ∀ {B C E X}
      {D : Ty (suc Δᴿ)} {eqB : B ≡ `∀ D}
      {eqC : C ≡ D [ ＇ X ]ᵗ}
      {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A
        (name-type-app-frame D X eqB eqC ▻ⁱ spine) q

  tfa-cast : ∀ {B C E μ}
      {c : μ ⊢ B ∼ C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → A CTX.⊑ᵂ⟨ W ⟩ C
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (cast-frame c ▻ⁱ spine) q

  tfa-reveal : ∀ {B C E Xᴿ?}
      {c : Conv↑ Δᴿ B C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
      {Wᵖ : CTX.World Δᴸ Δᴿ Δ}
      {γᵖ : CTX.CtxImp Wᵖ}
    → CTX.ImpEnvMono W Wᵖ
    → CTX.RebaseAtᴿ W Wᵖ Xᴿ?
    → CTX.SameCtx γ γᵖ
    → CTX.targetStoreʷ W Conv.⊢↑[ Xᴿ? ] c
    → A CTX.⊑ᵂ⟨ W ⟩ C
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (reveal-frame c ▻ⁱ spine) q

  tfa-conceal : ∀ {B C E Xᴿ?}
      {c : Conv↓ Δᴿ B C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
      {Wᵖ : CTX.World Δᴸ Δᴿ Δ}
      {γᵖ : CTX.CtxImp Wᵖ}
    → CTX.ImpEnvMono W Wᵖ
    → CTX.RebaseAtᴿ Wᵖ W Xᴿ?
    → CTX.SameCtx γ γᵖ
    → CTX.targetStoreʷ W Conv.⊢↓[ Xᴿ? ] c
    → A CTX.⊑ᵂ⟨ W ⟩ C
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (conceal-frame c ▻ⁱ spine) q


-- C1: the 1g cast-frame square closes once the chain supplies the
-- post-cast endpoint.  The final `q` is still only the tail endpoint.
cast-frame-absorption-cell : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ} {μ : Env∼ Δᴿ}
    {c : μ ⊢ B ∼ C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (cast-frame c ▻ⁱ spine) q
  → W CTX.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTX.∣ γ ⊢² M ⊑ V ⟨ c ⟩ ∶ qC
cast-frame-absorption-cell (tfa-cast qC tail) rel =
  qC , CTI2.⊑cast² _ rel qC


-- C2: a strict `allv-∀` peel refines the parent chain by inserting the
-- generated cast-frame entry.  The generated post-cast witness is explicit
-- here; the live refinement must derive it from the opened endpoints.
allv-∀-child-chain-cell : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {spine : InstantiationSpine (C [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame C X refl refl ▻ⁱ spine) q
  → Aₛ CTX.⊑ᵂ⟨ W ⟩ C [ ＇ X ]ᵗ
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine) q
allv-∀-child-chain-cell parent qCast tail =
  tfa-name (tfa-cast qCast tail)


-- C3a: a strict `allv-reveal` peel has two generated target-conversion
-- entries.  The live refinement must derive the two entries from the
-- commute geometry returned by the peel.
allv-reveal-child-chain-cell : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↑ (suc Δᴿ) C B}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ applyTy (bind (＇ X)) E}
    {X₁? X₂? : Maybe (TyVar (suc Δᴿ))}
    {Wᵖ₁ Wᵖ₂ : CTX.World Δᴸ (suc Δᴿ) Δ}
    {γᵖ₁ : CTX.CtxImp Wᵖ₁}
    {γᵖ₂ : CTX.CtxImp Wᵖ₂}
  → CTX.ImpEnvMono W Wᵖ₁
  → CTX.RebaseAtᴿ W Wᵖ₁ X₁?
  → CTX.SameCtx γ γᵖ₁
  → CTX.targetStoreʷ W Conv.⊢↑[ X₁? ] c
  → Aₛ CTX.⊑ᵂ⟨ W ⟩ B
  → CTX.ImpEnvMono W Wᵖ₂
  → CTX.RebaseAtᴿ W Wᵖ₂ X₂?
  → CTX.SameCtx γ γᵖ₂
  → CTX.targetStoreʷ W Conv.⊢↑[ X₂? ]
      〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗
  → Aₛ CTX.⊑ᵂ⟨ W ⟩
      replaceTy Fin.zero (⇑ᵗ (＇ X)) B
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine (bind (＇ X)) spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine) q
allv-reveal-child-chain-cell mono₁ rb₁ sc₁ c⊢₁ q₁
    mono₂ rb₂ sc₂ c⊢₂ q₂ tail =
  tfa-name (tfa-type (tfa-reveal mono₁ rb₁ sc₁ c⊢₁ q₁
    (tfa-reveal mono₂ rb₂ sc₂ c⊢₂ q₂ (tfa-type tail))))


-- C3b: `allv-conceal` is the same refinement shape except for the first
-- generated conversion frame.
allv-conceal-child-chain-cell : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↓ (suc Δᴿ) C B}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ applyTy (bind (＇ X)) E}
    {X₁? X₂? : Maybe (TyVar (suc Δᴿ))}
    {Wᵖ₁ Wᵖ₂ : CTX.World Δᴸ (suc Δᴿ) Δ}
    {γᵖ₁ : CTX.CtxImp Wᵖ₁}
    {γᵖ₂ : CTX.CtxImp Wᵖ₂}
  → CTX.ImpEnvMono W Wᵖ₁
  → CTX.RebaseAtᴿ Wᵖ₁ W X₁?
  → CTX.SameCtx γ γᵖ₁
  → CTX.targetStoreʷ W Conv.⊢↓[ X₁? ] c
  → Aₛ CTX.⊑ᵂ⟨ W ⟩ B
  → CTX.ImpEnvMono W Wᵖ₂
  → CTX.RebaseAtᴿ W Wᵖ₂ X₂?
  → CTX.SameCtx γ γᵖ₂
  → CTX.targetStoreʷ W Conv.⊢↑[ X₂? ]
      〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗
  → Aₛ CTX.⊑ᵂ⟨ W ⟩
      replaceTy Fin.zero (⇑ᵗ (＇ X)) B
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine (bind (＇ X)) spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine) q
allv-conceal-child-chain-cell mono₁ rb₁ sc₁ c⊢₁ q₁
    mono₂ rb₂ sc₂ c⊢₂ q₂ tail =
  tfa-name (tfa-type (tfa-conceal mono₁ rb₁ sc₁ c⊢₁ q₁
    (tfa-reveal mono₂ rb₂ sc₂ c⊢₂ q₂ (tfa-type tail))))


-- C4: the public `StructuralValueInstantiationᵀ` entry spine has no target
-- absorption frames, so its chain is constructible from the statement shape.
root-value-instantiation-chain-cell : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {R : Ty Δᴿ}
    {q : A CTX.⊑ᵂ⟨ W ⟩
      applyBody (bind R) B [ ＇ Fin.zero ]ᵗ}
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame (applyBody (bind R) B)
        Fin.zero refl refl ▻ⁱ []ⁱ) q
root-value-instantiation-chain-cell = tfa-name tfa-[]

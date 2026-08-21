{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.SourceValueContextResidualProbe where

-- File Charter:
--   * Checks a constructor-indexed source value context as a diagnostic for
--     overgeneralized standalone source-strip inputs.
--   * Packages the exact immediate residual row without duplicating the
--     live SourceSpineStripBranch result datatype.
--   * Checks that the corresponding live RightInj bare-seal boundary is
--     contradictory before the residual can reach the DGG.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
import Conversion as Conv
import CastTerms as CT
open CT using
  (Term; Inert; RevealValue; ConcealValue; _⟨_⟩; _↑_; _↓_)
open import Imprecision
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI2
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-cast; sv-seal; variable-obligation-aligns)
open CTX using
  (World; CtxImp; RebaseAt; RebaseAtᴸ; TagRebaseAtᴸ; _⊑ᵂ⟨_⟩_;
   sourceStoreʷ; targetStoreʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Constructor-form source value contexts
------------------------------------------------------------------------

data SourceValueContext {Δ : TyCtx}
    (P : Term Δ) (A : Ty Δ) : Term Δ → Ty Δ → Set where
  source-hole : SourceValueContext P A P A

  source-cast : ∀ {V B C μ} {c : μ ⊢ B ∼ C}
    → SourceValueContext P A V B
    → Inert c
    → SourceValueContext P A (V ⟨ c ⟩) C

  source-reveal : ∀ {V B C} {c : Conv.Conv↑ Δ B C}
    → SourceValueContext P A V B
    → RevealValue c
    → SourceValueContext P A (V ↑ c) C

  source-conceal : ∀ {V B C} {c : Conv.Conv↓ Δ B C}
    → SourceValueContext P A V B
    → ConcealValue c
    → SourceValueContext P A (V ↓ c) C

wrap-star-cast-seal-context : ∀ {Δ} {P : Term Δ} {X : TyVar Δ}
    {μ : Env∼ Δ} {c : μ ⊢ (＇ X) ∼ ★}
  → Inert c
  → SourceValueContext (P ↓ Conv.seal X ★) (＇ X)
      (((P ↓ Conv.seal X ★) ⟨ c ⟩) ↓ Conv.seal X ★) (＇ X)
wrap-star-cast-seal-context inert =
  source-conceal (source-cast source-hole inert) CT.seal

sameCtx-refl : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
  → CTX.SameCtx γ γ
sameCtx-refl {γ = []} = CTX.same-[]
sameCtx-refl {γ = CTX.ctx-imp A B p ∷ γ} =
  CTX.same-∷ sameCtx-refl

------------------------------------------------------------------------
-- The live RightInj boundary is contradictory
------------------------------------------------------------------------

right-inj-bare-seal-boundary-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → TagRebaseAtᴸ W′ W (just X) nothing
  → (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)
  → ⊥
right-inj-bare-seal-boundary-⊥ {W = W} {X = X} {Y = Y}
    (CTX.tag-rebase-onlyᴸ to-star disaligned represented) q =
  disaligned Y
    (sym (variable-obligation-aligns {W = W} {X = X} {Y = Y} q))

------------------------------------------------------------------------
-- Diagnostic package for the broader standalone source-strip surface
------------------------------------------------------------------------

wrap-star-residual-package : ∀ {Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ Δ} {γ′ : CtxImp W′}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {μ : Env∼ Δᴸ} {c : μ ⊢ (＇ X) ∼ ★}
    {p₂ : (＇ X) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
  → SpineValue P
  → Inert c
  → sourceStoreʷ W′ ∋ X ⦂ ★
  → targetStoreʷ W′ ∋ Y ⦂ ★
  → RebaseAt W′ W′ X Y
  → W′ ∣ γ′ ⊢² P ↓ Conv.seal X ★
      ⊑ U ↓ Conv.seal Y ★ ∶ p₂
  → SourceValueContext (P ↓ Conv.seal X ★) (＇ X)
      (((P ↓ Conv.seal X ★) ⟨ c ⟩) ↓ Conv.seal X ★) (＇ X)
    × SpineValue (P ↓ Conv.seal X ★)
    × (Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
       Σ[ γʳ ∈ CtxImp Wʳ ]
       Σ[ qʳ ∈ (＇ X) ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
         (CTX.ImpEnvMono W′ Wʳ
          × CTX.SameCtx γ′ γʳ
          × RebaseAtᴸ Wʳ W′ (just X)
          × targetStoreʷ Wʳ ∋ Y ⦂ ★
          × Wʳ ∣ γʳ ⊢² P ↓ Conv.seal X ★
              ⊑ U ↓ Conv.seal Y ★ ∶ qʳ))
wrap-star-residual-package sv inert source∈ target∈ rb residual =
  wrap-star-cast-seal-context inert ,
  sv-seal sv ,
  _ , _ , _ ,
  CTX.impEnvMono-refl , sameCtx-refl , CTX.rebase-varᴸ rb ,
  target∈ , residual

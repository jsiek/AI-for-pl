module proof.NuImprecisionWorldCoherentRightValueCatchupCasesDef where

-- File Charter:
--   * Defines the eight major semantic capabilities used by recursive
--     world-coherent right-value catch-up.
--   * Keeps constructor-specific frame, quotient, binder, and allocation
--     premises explicit at their independently provable boundaries.
--   * Contains no dispatcher, implementation, postulate, hole, or permissive
--     option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import Coercions using
  ( Coercion
  ; Inert
  ; genᵈ
  ; id-onlyᵈ
  ; instᵈ
  ; tag-or-idᵈ
  )
open import Conversion using (RevealConversion)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _∣_⊢_⊑_⊣_
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  )
import ImprecisionWf as IW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( CtxImp
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftRightCtxⁱ
  ; LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; Λ_
  ; _•
  ; _⟨_⟩
  ; ⇑ᵗᵐ
  ; ν
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; `∀
  ; occurs
  ; ⟰ᵗ
  ; ⇑ᵗ
  )
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)
open import proof.NuImprecisionWorldCoherentRightSourceFramesDef using
  (WorldCoherentRightSourceFrames)
open import proof.NuImprecisionWorldCoherentRightTargetCastFramesDef using
  (WorldCoherentRightTargetCastFrames)
open import proof.NuImprecisionWorldCoherentRightValueTerminalDef using
  (WorldCoherentRightValueTerminalᵀ)


WorldCoherentRightPairedCastFrameᵀ : Set₁
WorldCoherentRightPairedCastFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  Value M →
  No• M →
  Inert c →
  PairedCast Φ Δᴸ Δᴿ ρ₀ c c′ p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q


record WorldCoherentRightQuotientDownUpFrame : Set₁ where
  field
    rightQuotientIdDownUpFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {C C′ D D′ A A′ : Ty}
        {d d′ u u′ : Coercion}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
      Value M →
      No• M →
      Inert d →
      Inert u →
      id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ d′ ∶ C′ ⊒ D′ →
      (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} pC →
      WorldCoherentRightValueCatchupIndexedResult
        {V = (M ⟨ d ⟩) ⟨ u ⟩}
        {M′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩} {ρ = ρ⁺} pA

    rightQuotientGenDownUpFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {C C′ D D′ A A′ : Ty}
        {d d′ u u′ : Coercion}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
      Value M →
      No• M →
      Inert d →
      Inert u →
      genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ₀
        ⊢ d ∶ C ⊒ D →
      genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ d′ ∶ C′ ⊒ D′ →
      (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} pC →
      WorldCoherentRightValueCatchupIndexedResult
        {V = (M ⟨ d ⟩) ⟨ u ⟩}
        {M′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩} {ρ = ρ⁺} pA

open WorldCoherentRightQuotientDownUpFrame public


WorldCoherentRightSourceAllClosingᵀ : Set₁
WorldCoherentRightSourceAllClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {occ : occurs zero A ≡ true} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value V →
  No• V →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = Λ V} {M′ = N′} {ρ = ρ⁺} (IW.ν occ p)


WorldCoherentRightTargetBulletClosingᵀ : Set₁
WorldCoherentRightTargetBulletClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {A B C′ : Ty} {N L′ : Term}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ}
    {ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  StoreImpPrefix (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′) ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive (⇑ᴿᵢ Φ) →
  StoreWf (suc Δᴿ) (rightStoreⁱ ρ⁺) →
  RuntimeOK ((⇑ᵗᵐ L′) •) →
  Value N →
  No• N →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
  LiftRightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    (⇑ᴿᵢ Φ) [] [] →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ L′ ⦂ B ⊑ `∀ C′ ∶ q →
  Δᴸ ∣ leftStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ [] ⊢ N ⦂ B →
  suc Δᴿ ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρ′)
    ∣ [] ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  WorldCoherentRightValueCatchupIndexedResult
    {V = N} {M′ = (⇑ᵗᵐ L′) •} {ρ = ρ⁺} r


record WorldCoherentRightTargetAllocationFrames : Set₁ where
  field
    rightTargetNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
        {A B B′ C′ : Ty} {N N′ : Term} {s : Coercion} {μ}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν A N′ s) →
      Value N →
      No• N →
      WfTy Δᴿ A →
      WfTy (suc Δᴿ) (⇑ᵗ A) →
      RevealConversion μ (suc Δᴿ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ′ →
      LiftRightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        (⇑ᴿᵢ Φ) [] [] →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = N′} {ρ = ρ⁺} q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = ν A N′ s} {ρ = ρ⁺} p

    rightTargetNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
        {B B′ C′ : Ty} {N N′ : Term} {s : Coercion} {μ}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν ★ N′ s) →
      Value N →
      No• N →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴿ
        ∣ ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ₀ ρ′ →
      LiftRightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        (⇑ᴿᵢ Φ) [] [] →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = N′} {ρ = ρ⁺} q →
      WorldCoherentRightValueCatchupIndexedResult
        {V = N} {M′ = ν ★ N′ s} {ρ = ρ⁺} p

open WorldCoherentRightTargetAllocationFrames public


record WorldCoherentRightValueCatchupCases : Set₁ where
  field
    rightValueTerminalCase : WorldCoherentRightValueTerminalᵀ
    rightValueSourceFramesCase : WorldCoherentRightSourceFrames
    rightValueTargetCastFramesCase : WorldCoherentRightTargetCastFrames
    rightValuePairedCastFrameCase : WorldCoherentRightPairedCastFrameᵀ
    rightValueQuotientDownUpFrameCase :
      WorldCoherentRightQuotientDownUpFrame
    rightValueSourceAllClosingCase : WorldCoherentRightSourceAllClosingᵀ
    rightValueTargetBulletClosingCase :
      WorldCoherentRightTargetBulletClosingᵀ
    rightValueTargetAllocationFramesCase :
      WorldCoherentRightTargetAllocationFrames

open WorldCoherentRightValueCatchupCases public

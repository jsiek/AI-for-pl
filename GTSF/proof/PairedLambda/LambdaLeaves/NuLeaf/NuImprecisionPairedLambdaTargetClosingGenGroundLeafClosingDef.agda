module
  proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaTargetClosingGenGroundLeafClosingDef
  where

-- File Charter:
--   * Defines terminal paired-lambda closing for the dedicated
--     `gen⊑groundᵀ` leaf.
--   * Retains the ground witness, target typing, tagged inner relation, and
--     final proof-relevant imprecision index from the quotient constructor.
--   * Contains no implementation, postulate, hole, permissive option,
--     generic catch-all leaf, or broad simulation import.

import Coercions as C
open import Coercions using (Coercion; ModeEnv; _!)
open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ground
  ; Ty
  ; TyCtx
  ; ★
  ; `∀
  )
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingGenGroundLeafClosingᵀ : Set₁
PairedLambdaTargetClosingGenGroundLeafClosingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A B H : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {c : Coercion} {μ : ModeEnv} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.gen A c ∶ A ⊒ `∀ B →
  Ground H →
  Value V → No• V →
  Value W → No• W →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ W ⦂ H →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⟨ H ! ⟩ ⦂ A ⊑ ★ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (V ⟨ C.gen A c ⟩) W B H q

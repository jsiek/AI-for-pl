module
  proof.PairedLambda.LambdaLeaves.Core.NuImprecisionPairedLambdaTargetClosingLambdaLeafClosingProof
  where

-- File Charter:
--   * Proves the fused ordinary source-`Λ` leaf contract from the canonical
--     `ν` paired-conversion rotation theorem.
--   * Reconstructs and prefix-transports the leaf relation, introduces the
--     source runtime bullet, rotates the whole paired conversion, and only
--     then applies the final structural universal reveal.
--   * Also checks that the resulting theorem directly inhabits the
--     corresponding target-closing frame handler field.
--   * Contains no postulate, hole, permissive option, or broad simulation
--     import.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Conversion using (reveal-all)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  ; ⊑-src-wf
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ-lift-left
  ; lift-left-ctx-[]
  ; rightStoreⁱ-lift-left
  )
open import NuTerms using (No•; Term; Value; Λ_; no•-Λ)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; conv↑⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; paired-conversion
  ; Λ⊑ᵀ
  ; α⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (_∣_∣_⊢_⦂_; ⊢•)
open import Types using (Ty; TyCtx; occurs)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.PairedLambda.LambdaLeaves.Core.NuImprecisionPairedLambdaTargetClosingLambdaLeafClosingDef
  using (PairedLambdaTargetClosingLambdaLeafClosingᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import proof.Core.Properties.TypePreservation using (term-weaken)


paired-lambda-target-closing-lambda-leaf-closing-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingLambdaLeafClosingᵀ
paired-lambda-target-closing-lambda-leaf-closing-proofᵀ
    rotate {r = r} occ liftΛ liftγ vV noV vN′ noN′ V⊑N′
    prefix h⇑Aν reveal liftν lift∀ conversion
    with rotate h⇑Aν liftν occ conversion
paired-lambda-target-closing-lambda-leaf-closing-proofᵀ
    rotate {r = r} occ liftΛ liftγ vV noV vN′ noN′ V⊑N′
    prefix h⇑Aν reveal liftν lift∀ conversion
    | u , rotated-conversion =
  conv↑⊑ᵀ (reveal-all reveal)
    (conv⊑convᵀ (paired-conversion rotated-conversion)
      bullet-relation)
    (⊑-source-liftνᵢ _)
  where
  lambda-value = Λ vV

  lambda-no-bullet = no•-Λ noV

  lambda-relation₀ = Λ⊑ᵀ occ liftΛ liftγ vV V⊑N′

  lambda-relation =
    allocation-prefixᵀ prefix lambda-relation₀
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        lambda-no-bullet
        (nu-term-imprecision-source-typing lambda-relation₀))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noN′ (nu-term-imprecision-target-typing lambda-relation₀))

  source-bullet-typing =
    subst
      (λ Σ → _ ∣ (_ , _) ∷ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (leftStoreⁱ-lift-left liftν))
      (⊢• refl refl (⊑-src-wf r) lambda-value lambda-no-bullet
        (nu-term-imprecision-source-typing lambda-relation))

  target-typing =
    subst
      (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (rightStoreⁱ-lift-left liftν))
      (nu-term-imprecision-target-typing lambda-relation)

  bullet-relation =
    α⊑ᵀ lambda-value lambda-no-bullet h⇑Aν liftν
      lift-left-ctx-[] lambda-relation source-bullet-typing target-typing


paired-lambda-target-closing-lambda-leaf-handler-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {γ′ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (occ : occurs zero A ≡ true) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] γ′ →
  Value V → No• V →
  Value N′ → No• N′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (Λ V) N′ A B (ν _ occ p)
paired-lambda-target-closing-lambda-leaf-handler-proofᵀ
    rotate occ liftΛ liftγ vV noV vN′ noN′ V⊑N′
    prefix coherent exclusive wfL h⇑Aν reveal liftν lift∀ conversion =
  paired-lambda-target-closing-lambda-leaf-closing-proofᵀ
    rotate occ liftΛ liftγ vV noV vN′ noN′ V⊑N′
    prefix h⇑Aν reveal liftν lift∀ conversion

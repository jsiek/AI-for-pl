module
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  where

-- File Charter:
--   * Defines the smaller quotient-imprecision prototype used to test
--     simulation up to reduction.
--   * Gives the ordinary fragment its own syntax-directed constructors; no
--     constructor embeds or converts from another term-imprecision judgment.
--   * Includes matched and source-only type application and `ν`, with their
--     allocation-aware store lifts and exact index-substitution equations.
--   * Includes ordinary one-sided and paired reveal/conceal conversions.
--     General store-prefix weakening is admissible rather than a constructor.
--   * Retains the terminal `gen`/ground join, whose value endpoints cannot be
--     recovered merely by closing the simulation under reduction.
--   * Keeps quotient indices only across one paired narrowing cast and closes
--     them with compatible paired widenings.
--   * Includes the exact residual created by target-only instantiation.
--   * Represents exact and subsequently embedded target-instantiation
--     residuals with one syntax-directed creation constructor.
--   * Defines an allocation-aware bilateral reduction closure for closed
--     terms, with exact context, store, type, and index transport.
--   * Does not change or re-export the live term-imprecision relation.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using
  (Coercion; Inert; ModeEnv; id-onlyᵈ; inst; gen; _!)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; _ˣ⊑★; ⇑ᵢ; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; NonVar; ∀ⁱ_; ν; _↦_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—↠[_]_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; StoreCorresponds
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  ; store-matched
  ; store-right
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; ctx-imp
  ; leftCtxⁱ
  ; rightCtxⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; renameᵗᵐ
  ; ⇑ᵗᵐ
  ; `_
  ; ƛ_
  ; _·_
  ; Λ_
  ; _•
  ; ν
  ; _⟨_⟩
  ; $
  ; _⊕[_]_
  ; blame
  )
open import Primitives using (Prim; κℕ)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  ( Ground
  ; Renameᵗ
  ; Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; wf★
  ; _⇒_
  ; `∀
  ; renameᵗ
  ; ⇑ᵗ
  ; ⟰ᵗ
  ; occurs
  )
open import QuotientImprecisionCompatibility
  using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( StoreImpPrefixᴿ
  ; EmbeddedTargetInstantiationCreation
  )
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using
  ( rename-assm²ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)


variable
  Φ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  ρ : StoreImp Φ Δᴸ Δᴿ
  γ : CtxImp Φ Δᴸ Δᴿ

data QuotientWideningPairᴿ
    {Φ : ImpCtx} (Δᴸ Δᴿ : TyCtx) (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (u u′ : Coercion) → (D D′ A A′ : Ty) → Set₁ where
  quotient-id-wideningᴿ :
    ∀ {u u′ D D′ A A′} →
    id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′

  quotient-cast-wideningᴿ :
    ∀ {μ μ′ u u′ D D′ A A′} →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′

------------------------------------------------------------------------
-- Smaller ordinary and quotient relations
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
infix 4 _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_

mutual
  data _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_ :
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
      StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
      Term → Term → (A B : Ty) →
      Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

    blame⊑ᴿ :
      ∀ {M A B p} →
      Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ blame ⊑ M ⦂ A ⊑ B ∶ p

    x⊑xᴿ :
      ∀ {x A B p} →
      γ Types.∋ x ⦂ ctx-imp A B p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

    ƛ⊑ƛᴿ :
      ∀ {N N′ A A′ B B′ pA pB} →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ γ
        ⊢ᴿ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ ƛ N ⊑ ƛ N′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB

    _·ᴿ_ :
      ∀ {L L′ M M′ A A′ B B′ pA pB} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L · M ⊑ L′ · M′ ⦂ B ⊑ B′ ∶ pB

    Λ⊑Λᴿ :
      ∀ {ρ′ γ′ V V′ A B p} →
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′ →
      Value V →
      Value V′ →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴿ V ⊑ V′ ⦂ A ⊑ B ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ Λ V ⊑ Λ V′ ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p

    Λ⊑ᴿ :
      ∀ {ρ′ γ′ V N′ A B p} →
      {{safe : NonVar A}} →
      (occ : occurs zero A ≡ true) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′ →
      Value V →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴿ V ⊑ N′ ⦂ A ⊑ B ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ Λ V ⊑ N′ ⦂ `∀ A ⊑ B ∶ ν safe occ p

    α⊑αᴿ :
      ∀ {ρ′ ρ⁺ γ′ L L′ A B C D p} →
      Value L →
      No• L →
      Value L′ →
      No• L′ →
      (A⇑⊑B⇑ :
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ) →
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ L′ ⦂ `∀ C ⊑ `∀ D ∶ ∀ⁱ p →
      StoreImpPrefixᴿ
        (store-matched zero (⇑ᵗ A) zero (⇑ᵗ B)
          A⇑⊑B⇑ ∷ ρ′)
        ρ⁺ →
      suc Δᴸ
        ∣ leftStoreⁱ ρ⁺
        ∣ leftCtxⁱ γ′
        ⊢ (⇑ᵗᵐ L) • ⦂ C →
      suc Δᴿ
        ∣ rightStoreⁱ ρ⁺
        ∣ rightCtxⁱ γ′
        ⊢ (⇑ᵗᵐ L′) • ⦂ D →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ⁺ ∣ γ′
        ⊢ᴿ (⇑ᵗᵐ L) • ⊑ (⇑ᵗᵐ L′) • ⦂ C ⊑ D ∶ p

    α⊑ᴿ :
      ∀ {ρ′ ρ⁺ γ′ L N′ A B′ C p occ} →
      {{safe : NonVar C}} →
      Value L →
      No• L →
      (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ p →
      StoreImpPrefixᴿ
        (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
        ρ⁺ →
      suc Δᴸ
        ∣ leftStoreⁱ ρ⁺
        ∣ leftCtxⁱ γ′
        ⊢ (⇑ᵗᵐ L) • ⦂ C →
      Δᴿ
        ∣ rightStoreⁱ ρ⁺
        ∣ rightCtxⁱ γ′
        ⊢ N′ ⦂ B′ →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ′
        ⊢ᴿ (⇑ᵗᵐ L) • ⊑ N′ ⦂ C ⊑ B′ ∶ p

    ν⊑νᴿ :
      ∀ {ρ′ γ′ A A′ B B′ C C′ N N′ p q s s′ μ μ′} →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
      Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
      (A⇑⊑A′⇑ :
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
      q [ zero ↦ ⇑ᵗ A
          ⊑⟨ A⇑⊑A′⇑ ⟩
          ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ ν A N s ⊑ ν A′ N′ s′ ⦂ B ⊑ B′ ∶ p

    ν⊑ᴿ :
      ∀ {ρ′ γ′ A B B′ C N N′ p q s μ occ} →
      {{safe : NonVar C}} →
      WfTy Δᴸ A →
      (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ q →
      q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ ν A N s ⊑ N′ ⦂ B ⊑ B′ ∶ p

    κ⊑κᴿ :
      ∀ {n} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ $ (κℕ n) ⊑ $ (κℕ n)
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι

    _⊕ᴿ[_]_ :
      ∀ {L L′ M M′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ L′
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι →
      (op : Prim) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι

    gen⊑groundᴿ :
      ∀ {V W A B H p c μ} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ gen A c ∶ A ⊒ `∀ B →
      Ground H →
      Value V →
      Value W →
      Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ W ⦂ H →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ V ⊑ W ⟨ H ! ⟩ ⦂ A ⊑ ★ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ V ⟨ gen A c ⟩ ⊑ W ⦂ `∀ B ⊑ H ∶ q

    cast⊒⊑ᴿ :
      ∀ {M M′ A B B′ p c μ s} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      narrowing ⊢ᶜ c ⦂ s →
      s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    cast⊑⊑ᴿ :
      ∀ {M M′ A B B′ p c μ s} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      widening ⊢ᶜ c ⦂ s →
      s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    ⊑cast⊒ᴿ :
      ∀ {M M′ A A′ B′ p c′ μ′ s} →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      narrowing ⊢ᶜ c′ ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    ⊑cast⊑ᴿ :
      ∀ {M M′ A A′ B′ p c′ μ′ s} →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      widening ⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    conv↑⊑ᴿ :
      ∀ {M M′ A B B′ p c μ α X} →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      p [ α ↦ X ]ᴸ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    conv↓⊑ᴿ :
      ∀ {M M′ A B B′ p c μ α X} →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      q [ α ↦ X ]ᴸ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    ⊑conv↑ᴿ :
      ∀ {M M′ A A′ B′ p c′ μ′ β X′} →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      p [ β ↦ X′ ]ᴿ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    ⊑conv↓ᴿ :
      ∀ {M M′ A A′ B′ p c′ μ′ β X′} →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c′ A′ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      q [ β ↦ X′ ]ᴿ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    paired-revealᴿ :
      ∀ {M M′ A A′ B B′ p q c c′
          α β X X′ pX μ μ′} →
      StoreCorresponds ρ α X β X′ pX →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

    paired-concealᴿ :
      ∀ {M M′ A A′ B B′ p q c c′
          α β X X′ pX μ μ′} →
      StoreCorresponds ρ α X β X′ pX →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

    target-instantiationᴿ :
      ∀ {Φ₀ Θᴸ Θᴿ}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {W W′ : Term} {B C D : Ty} {s : Coercion}
        {μ : ModeEnv}
        {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ⊢ D ⊑ C ⊣ suc Θᴿ}
        {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
        {body-shape : ImprecisionShape}
        {Ψ : ImpCtx} {Δᴸ′ Δᴿ′ : TyCtx}
        {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ′}
        {γ′ : CtxImp Ψ Δᴸ′ Δᴿ′}
        {M M′ : Term} {A A′ : Ty}
        {p : Ψ ∣ Δᴸ′ ⊢ A ⊑ A′ ⊣ Δᴿ′} →
      EmbeddedTargetInstantiationCreation
        {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (StoreImpPrefixᴿ ρ₀ ρ⁺)
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
          ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r)
        {Ψ = Ψ} {Δᴸ = Δᴸ′} {Δᴿ = Δᴿ′}
        ρ′ M M′ A A′ p →
      Ψ ∣ Δᴸ′ ∣ Δᴿ′ ∣ ρ′ ∣ γ′
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p

    closeᴿ :
      ∀ {N N′ D D′ A A′ q p u u′ s s′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q →
      QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ s →
      widening ⊢ᶜ u′ ⦂ s′ →
      s ；⌊ p ⌋≋ᵖ q ； s′ →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′ q p s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ N ⟨ u ⟩ ⊑ N′ ⟨ u′ ⟩ ⦂ A ⊑ A′ ∶ p

    paired-wideningᴿ :
      ∀ {M M′ A A′ B B′ p q c c′ μ μ′ s s′ r} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ s →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s′ →
      s ； ⌊ q ⌋ ≋ r →
      ⌊ p ⌋ ； s′ ≋ r →
      ReductionClosedPairedWideningCompatible
        Φ Δᴸ Δᴿ c c′ p q s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

  data _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_ :
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
      StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
      Term → Term → (D D′ : Ty) →
      Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ → Set₁ where

    paired-downᴿ :
      ∀ {M M′ A A′ D D′ p d d′ s s′ q μ μ′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      SpineCastMode (leftStoreⁱ ρ) μ →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ A ⊒ D →
      narrowing ⊢ᶜ d ⦂ s →
      SpineCastMode (rightStoreⁱ ρ) μ′ →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ A′ ⊒ D′ →
      narrowing ⊢ᶜ d′ ⦂ s′ →
      s ；⌊ p ⌋≋ᵖ q ； s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ M ⟨ d ⟩ ⊑ M′ ⟨ d′ ⟩
        ⦂ D ⊑ᵖ D′ ∶ q

------------------------------------------------------------------------
-- Allocation-aware bilateral reduction closure
------------------------------------------------------------------------

infix 4 _∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_

record _∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (M M′ : Term) (A A′ : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) : Set₁ where
  constructor related-after-bilateral-reduction
  field
    sourceChanges : StoreChanges
    targetChanges : StoreChanges
    sourceResult : Term
    targetResult : Term

    resultCtx : ImpCtx
    resultLeftCtx : TyCtx
    resultRightCtx : TyCtx
    sourceCtxResult :
      resultLeftCtx ≡ applyTyCtxs sourceChanges Δᴸ
    targetCtxResult :
      resultRightCtx ≡ applyTyCtxs targetChanges Δᴿ

    resultStore :
      StoreImp resultCtx resultLeftCtx resultRightCtx
    sourceStoreResult :
      leftStoreⁱ resultStore
        ≡ applyStores sourceChanges (leftStoreⁱ ρ)
    targetStoreResult :
      rightStoreⁱ resultStore
        ≡ applyStores targetChanges (rightStoreⁱ ρ)

    resultSourceType : Ty
    resultTargetType : Ty
    sourceTypeResult :
      resultSourceType ≡ applyTys sourceChanges A
    targetTypeResult :
      resultTargetType ≡ applyTys targetChanges A′

    transportType :
      ∀ {C D} →
      Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
      resultCtx ∣ resultLeftCtx
        ⊢ applyTys sourceChanges C
          ⊑ applyTys targetChanges D
        ⊣ resultRightCtx

    sourceReduction :
      M —↠[ sourceChanges ] sourceResult
    targetReduction :
      M′ —↠[ targetChanges ] targetResult

    resultImprecision :
      resultCtx
        ∣ resultLeftCtx
        ∣ resultRightCtx
        ∣ resultStore ∣ []
        ⊢ᴿ sourceResult ⊑ targetResult
        ⦂ resultSourceType ⊑ resultTargetType
        ∶ subst
            (λ T → resultCtx ∣ resultLeftCtx
              ⊢ resultSourceType ⊑ T ⊣ resultRightCtx)
            (sym targetTypeResult)
            (subst
              (λ S → resultCtx ∣ resultLeftCtx
                ⊢ S ⊑ applyTys targetChanges A′
                ⊣ resultRightCtx)
              (sym sourceTypeResult)
              (transportType p))

open _∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_ public

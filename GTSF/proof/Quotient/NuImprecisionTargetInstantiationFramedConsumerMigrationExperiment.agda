module
  proof.Quotient.NuImprecisionTargetInstantiationFramedConsumerMigrationExperiment
  where

-- File Charter:
--   * Shadow-migrates paired-lambda leaf reconstruction and framed universal
--     fusion to the independent smaller term-imprecision relation.
--   * Defines a closing-frame spine whose fold constructs every frame with a
--     smaller ordinary, prefix, conversion, or single-boundary quotient rule.
--   * Reconstructs exact target-instantiation leaves through canonical
--     transport before folding any surrounding frames.
--   * Contains no legacy term-imprecision judgment, postulate, hole,
--     permissive option, termination bypass, or catch-all clause.

open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using
  (Coercion; ModeEnv)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using (ImpCtx)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using
  (Term; _⟨_⟩)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx)
open import QuotientImprecisionCompatibility
  using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( QuotientWideningPairᴿ
  ; cast⊒⊑ᴿ
  ; cast⊑⊑ᴿ
  ; ⊑cast⊒ᴿ
  ; ⊑cast⊑ᴿ
  ; conv↑⊑ᴿ
  ; conv↓⊑ᴿ
  ; ⊑conv↑ᴿ
  ; ⊑conv↓ᴿ
  ; paired-revealᴿ
  ; paired-concealᴿ
  ; closeᴿ
  ; paired-downᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientStorePrefixExperiment
  using (term-imprecision-store-prefixᴿ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationConsumerMigrationExperiment
  using
  ( CanonicalTargetInstantiationLeafᴿ
  ; canonical-target-instantiation-leaf-reconstructᴿ
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (StoreImpPrefixᴿ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationTransportSpineExperiment
  using
  ( TargetInstantiationTransportSpine
  ; target-instantiation-transport-spine-foldᴿ
  )


data SmallerClosingFramesᴿ
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ₀ : StoreImp Φ Δᴸ Δᴿ)
    (L L′ : Term) (A A′ : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) :
    (ρ : StoreImp Φ Δᴸ Δᴿ) →
    (M M′ : Term) → (B B′ : Ty) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) → Set₁ where

  frame-reflᴿ :
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ₀ L L′ A A′ p

  frame-prefixᴿ :
    ∀ {ρ₁ ρ₂ M M′ B B′ q} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ₁ M M′ B B′ q →
    StoreImpPrefixᴿ ρ₁ ρ₂ →
    Δᴸ ∣ leftStoreⁱ ρ₂ ∣ [] ⊢ M ⦂ B →
    Δᴿ ∣ rightStoreⁱ ρ₂ ∣ [] ⊢ M′ ⦂ B′ →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ₂ M M′ B B′ q

  frame-source-narrowᴿ :
    ∀ {ρ M M′ B C B′ q c μ s} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ B ⊒ C →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) →
    narrowing ⊢ᶜ c ⦂ s →
    s ； ⌊ q ⌋ ≋ ⌊ r ⌋ →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ (M ⟨ c ⟩) M′ C B′ r

  frame-source-widenᴿ :
    ∀ {ρ M M′ B C B′ q c μ s} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ B ⊑ C →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) →
    widening ⊢ᶜ c ⦂ s →
    s ； ⌊ r ⌋ ≋ ⌊ q ⌋ →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ (M ⟨ c ⟩) M′ C B′ r

  frame-target-narrowᴿ :
    ∀ {ρ M M′ B B′ C′ q c′ μ′ s′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊒ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    narrowing ⊢ᶜ c′ ⦂ s′ →
    ⌊ r ⌋ ； s′ ≋ ⌊ q ⌋ →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M (M′ ⟨ c′ ⟩) B C′ r

  frame-target-widenᴿ :
    ∀ {ρ M M′ B B′ C′ q c′ μ′ s′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊑ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    widening ⊢ᶜ c′ ⦂ s′ →
    ⌊ q ⌋ ； s′ ≋ ⌊ r ⌋ →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M (M′ ⟨ c′ ⟩) B C′ r

  frame-source-revealᴿ :
    ∀ {ρ M M′ B C B′ q c μ α X} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c B C →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) →
    q [ α ↦ X ]ᴸ r →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ (M ⟨ c ⟩) M′ C B′ r

  frame-source-concealᴿ :
    ∀ {ρ M M′ B C B′ q c μ α X} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c B C →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) →
    r [ α ↦ X ]ᴸ q →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ (M ⟨ c ⟩) M′ C B′ r

  frame-target-revealᴿ :
    ∀ {ρ M M′ B B′ C′ q c′ μ′ β X′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    q [ β ↦ X′ ]ᴿ r →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M (M′ ⟨ c′ ⟩) B C′ r

  frame-target-concealᴿ :
    ∀ {ρ M M′ B B′ C′ q c′ μ′ β X′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    r [ β ↦ X′ ]ᴿ q →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M (M′ ⟨ c′ ⟩) B C′ r

  frame-paired-revealᴿ :
    ∀ {ρ M M′ B B′ C C′ q c c′
        α β X X′ pX μ μ′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    StoreCorresponds ρ α X β X′ pX →
    RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c B C →
    RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
    q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ r →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) C C′ r

  frame-paired-concealᴿ :
    ∀ {ρ M M′ B B′ C C′ q c c′
        α β X X′ pX μ μ′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    StoreCorresponds ρ α X β X′ pX →
    ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c B C →
    ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
    r [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) C C′ r

  frame-single-boundaryᴿ :
    ∀ {ρ M M′ B B′ D D′ C C′ q
        d d′ u u′ μ μ′ sd sd′ su su′} →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
      ρ M M′ B B′ q →
    SpineCastMode (leftStoreⁱ ρ) μ →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ B ⊒ D →
    narrowing ⊢ᶜ d ⦂ sd →
    SpineCastMode (rightStoreⁱ ρ) μ′ →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ B′ ⊒ D′ →
    narrowing ⊢ᶜ d′ ⦂ sd′ →
    (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
    sd ；⌊ q ⌋≋ᵖ qD ； sd′ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ
      u u′ D D′ C C′ →
    (r : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ) →
    widening ⊢ᶜ u ⦂ su →
    widening ⊢ᶜ u′ ⦂ su′ →
    su ；⌊ r ⌋≋ᵖ qD ； su′ →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ qD r su su′ →
    SmallerClosingFramesᴿ ρ₀ L L′ A A′ p ρ
      ((M ⟨ d ⟩) ⟨ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩)
      C C′ r


smaller-closing-frames-foldᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴿ L ⊑ L′ ⦂ A ⊑ A′ ∶ p →
  SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
    ρ M M′ B B′ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ M ⊑ M′ ⦂ B ⊑ B′ ∶ q
smaller-closing-frames-foldᴿ relation frame-reflᴿ =
  relation
smaller-closing-frames-foldᴿ relation
    (frame-prefixᴿ frames prefix M⊢ M′⊢) =
  term-imprecision-store-prefixᴿ prefix
    (smaller-closing-frames-foldᴿ relation frames)
    M⊢ M′⊢
smaller-closing-frames-foldᴿ relation
    (frame-source-narrowᴿ
      frames mode seal★ c⊒ r shape composition) =
  cast⊒⊑ᴿ mode seal★ c⊒
    (smaller-closing-frames-foldᴿ relation frames)
    r shape composition
smaller-closing-frames-foldᴿ relation
    (frame-source-widenᴿ
      frames mode seal★ c⊑ r shape composition) =
  cast⊑⊑ᴿ mode seal★ c⊑
    (smaller-closing-frames-foldᴿ relation frames)
    r shape composition
smaller-closing-frames-foldᴿ relation
    (frame-target-narrowᴿ
      frames mode seal★ c⊒ r shape composition) =
  ⊑cast⊒ᴿ mode seal★ c⊒
    (smaller-closing-frames-foldᴿ relation frames)
    r shape composition
smaller-closing-frames-foldᴿ relation
    (frame-target-widenᴿ
      frames mode seal★ c⊑ r shape composition) =
  ⊑cast⊑ᴿ mode seal★ c⊑
    (smaller-closing-frames-foldᴿ relation frames)
    r shape composition
smaller-closing-frames-foldᴿ relation
    (frame-source-revealᴿ frames conversion r replacement) =
  conv↑⊑ᴿ conversion
    (smaller-closing-frames-foldᴿ relation frames)
    r replacement
smaller-closing-frames-foldᴿ relation
    (frame-source-concealᴿ frames conversion r replacement) =
  conv↓⊑ᴿ conversion
    (smaller-closing-frames-foldᴿ relation frames)
    r replacement
smaller-closing-frames-foldᴿ relation
    (frame-target-revealᴿ frames conversion r replacement) =
  ⊑conv↑ᴿ conversion
    (smaller-closing-frames-foldᴿ relation frames)
    r replacement
smaller-closing-frames-foldᴿ relation
    (frame-target-concealᴿ frames conversion r replacement) =
  ⊑conv↓ᴿ conversion
    (smaller-closing-frames-foldᴿ relation frames)
    r replacement
smaller-closing-frames-foldᴿ relation
    (frame-paired-revealᴿ
      frames corresponds source target r replacement) =
  paired-revealᴿ corresponds source target replacement
    (smaller-closing-frames-foldᴿ relation frames)
smaller-closing-frames-foldᴿ relation
    (frame-paired-concealᴿ
      frames corresponds source target r replacement) =
  paired-concealᴿ corresponds source target replacement
    (smaller-closing-frames-foldᴿ relation frames)
smaller-closing-frames-foldᴿ relation
    (frame-single-boundaryᴿ
      frames source-mode d⊒ d-shape target-mode d′⊒ d′-shape
      qD down-square widening-pair r u-shape u′-shape
      up-square compatible) =
  closeᴿ
    (paired-downᴿ
      (smaller-closing-frames-foldᴿ relation frames)
      source-mode d⊒ d-shape target-mode d′⊒ d′-shape
      down-square)
    widening-pair u-shape u′-shape up-square compatible


canonical-leaf-with-frames-reconstructᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ M M′ : Term} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  CanonicalTargetInstantiationLeafᴿ ρ₀ L L′ A A′ p →
  SmallerClosingFramesᴿ ρ₀ L L′ A A′ p
    ρ M M′ B B′ q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ M ⊑ M′ ⦂ B ⊑ B′ ∶ q
canonical-leaf-with-frames-reconstructᴿ leaf frames =
  smaller-closing-frames-foldᴿ
    (canonical-target-instantiation-leaf-reconstructᴿ leaf)
    frames


data FramedTargetUniversalFusionSpineᴿ
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (M M′ : Term) → (A A′ : Ty) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) → Set₁ where

  framed-fusion-pureᴿ :
    ∀ {ρ₀ L L′ A₀ A₀′ p₀ M M′ A A′ p} →
    TargetInstantiationTransportSpine ρ₀ L L′ A₀ A₀′ p₀ →
    SmallerClosingFramesᴿ ρ₀ L L′ A₀ A₀′ p₀
      ρ M M′ A A′ p →
    FramedTargetUniversalFusionSpineᴿ ρ M M′ A A′ p

  framed-fusion-creationᴿ :
    ∀ {ρ₀ L L′ A₀ A₀′ p₀ M M′ A A′ p} →
    CanonicalTargetInstantiationLeafᴿ ρ₀ L L′ A₀ A₀′ p₀ →
    SmallerClosingFramesᴿ ρ₀ L L′ A₀ A₀′ p₀
      ρ M M′ A A′ p →
    FramedTargetUniversalFusionSpineᴿ ρ M M′ A A′ p


framed-target-universal-fusion-spine-foldᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  FramedTargetUniversalFusionSpineᴿ ρ M M′ A A′ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
framed-target-universal-fusion-spine-foldᴿ
    (framed-fusion-pureᴿ pure frames) =
  smaller-closing-frames-foldᴿ
    (target-instantiation-transport-spine-foldᴿ pure)
    frames
framed-target-universal-fusion-spine-foldᴿ
    (framed-fusion-creationᴿ leaf frames) =
  canonical-leaf-with-frames-reconstructᴿ leaf frames

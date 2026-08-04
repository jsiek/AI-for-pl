module QuotientImprecisionCompatibility where

-- File Charter:
--   * Defines the canonical cast-mode and mutually recursive narrowing and
--     widening elimination evidence at the reduction-closed quotient boundary.
--   * Requires an inert source widening to be paired with an active target;
--     inert targets instead supply an exact intermediate imprecision bridge.
--   * Requires function widenings to retain contravariant narrowing
--     elimination evidence and recurse through their codomain widening.
--   * Keeps these concepts independent of term imprecision and operational
--     simulation.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using
  (Coercion; Inert; ModeEnv; id-onlyᵈ)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (Σ; _×_; _,_)
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; quotientᵖ; ≈∀-refl; ⊑ᵖ-arrow-components)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _↦ˢ_
  ; ∀ˢ_
  ; _；_≋_
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  )
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using
  (Store; Ty; TyCtx; _⇒_; `∀)


data SpineCastMode (Σ : Store) : ModeEnv → Set where
  id-only↓ :
    SpineCastMode Σ id-onlyᵈ

  gradual↓ :
    ∀ {μ} →
    CastMode μ →
    SealModeStore★ μ Σ →
    SpineCastMode Σ μ


data ReductionClosedPairedWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (c c′ : Coercion) → {A A′ B B′ : Ty} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    (c-shape c′-shape : ImprecisionShape) → Set where

  compatible-tagᴿ :
    ∀ {c′ A A′ B B′ p q c-shape c′-shape} G →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ (G C.!) c′
      {A} {A′} {B} {B′} p q c-shape c′-shape

  compatible-functionᴿ :
    ∀ {c₁ c₂ c₁′ c₂′ A₁ A₁′ A₂ A₂′
      B₁ B₁′ B₂ B₂′
      p₁ p₂ q₁ q₂ c₁-shape c₂-shape c₁′-shape c₂′-shape} →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c₂ c₂′ p₂ q₂ c₂-shape c₂′-shape →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ
      (c₁ C.↦ c₂) (c₁′ C.↦ c₂′)
      {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
      {B₁ ⇒ B₂} {B₁′ ⇒ B₂′}
      (p₁ ↦ p₂) (q₁ ↦ q₂)
      (c₁-shape ↦ˢ c₂-shape) (c₁′-shape ↦ˢ c₂′-shape)

  compatible-allᴿ :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    ReductionClosedPairedWideningCompatible
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (suc Δᴸ) (suc Δᴿ)
      c c′ p q c-shape c′-shape →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ
      (C.`∀ c) (C.`∀ c′)
      {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
      (∀ⁱ p) (∀ⁱ q) (∀ˢ c-shape) (∀ˢ c′-shape)

  compatible-target-activeᴿ :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    Inert c →
    (Inert c′ → ⊥) →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c c′
      {A} {A′} {B} {B′} p q c-shape c′-shape

  compatible-target-inert-bridgeᴿ :
    ∀ {c c′ A A′ B B′ p q c-shape c′-shape} →
    (Inert c′ →
      Σ (Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) (λ bridge →
      (c-shape ； ⌊ bridge ⌋ ≋ ⌊ p ⌋) ×
      (⌊ bridge ⌋ ； c′-shape ≋ ⌊ q ⌋))) →
    ReductionClosedPairedWideningCompatible
      Φ Δᴸ Δᴿ c c′
      {A} {A′} {B} {B′} p q c-shape c′-shape


private
  ↦ˢ-left-injective :
    ∀ {p q p′ q′} →
    p ↦ˢ q ≡ p′ ↦ˢ q′ →
    p ≡ p′
  ↦ˢ-left-injective refl = refl

  ↦ˢ-right-injective :
    ∀ {p q p′ q′} →
    p ↦ˢ q ≡ p′ ↦ˢ q′ →
    q ≡ q′
  ↦ˢ-right-injective refl = refl

  ∀ˢ-injective :
    ∀ {p p′} →
    ∀ˢ p ≡ ∀ˢ p′ →
    p ≡ p′
  ∀ˢ-injective refl = refl


reduction-closed-paired-compatible-shape-transport :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q q′ : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {c-shape c′-shape : ImprecisionShape} →
  ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
  ⌊ q′ ⌋ ≡ ⌊ q ⌋ →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′
    {A} {A′} {B} {B′} p q c-shape c′-shape →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ p′ q′ c-shape c′-shape
reduction-closed-paired-compatible-shape-transport
    p-shape q-shape (compatible-tagᴿ G) =
  compatible-tagᴿ G
reduction-closed-paired-compatible-shape-transport
    {p′ = p₁′ ↦ p₂′} {q′ = q₁′ ↦ q₂′}
    p-shape q-shape (compatible-functionᴿ compatible) =
  compatible-functionᴿ
    (reduction-closed-paired-compatible-shape-transport
      (↦ˢ-right-injective p-shape)
      (↦ˢ-right-injective q-shape)
      compatible)
reduction-closed-paired-compatible-shape-transport
    {p′ = ∀ⁱ p′} {q′ = ∀ⁱ q′}
    p-shape q-shape (compatible-allᴿ compatible) =
  compatible-allᴿ
    (reduction-closed-paired-compatible-shape-transport
      (∀ˢ-injective p-shape)
      (∀ˢ-injective q-shape)
      compatible)
reduction-closed-paired-compatible-shape-transport
    p-shape q-shape (compatible-target-activeᴿ inert active′) =
  compatible-target-activeᴿ inert active′
reduction-closed-paired-compatible-shape-transport
    p-shape q-shape
    (compatible-target-inert-bridgeᴿ bridge-evidence) =
  compatible-target-inert-bridgeᴿ λ inert′ →
    let
      bridge , source-triangle , target-triangle =
        bridge-evidence inert′
    in
      bridge
      , transport-result p-shape source-triangle
      , transport-result q-shape target-triangle
  where
  transport-result :
    ∀ {s t r r′} →
    r′ ≡ r →
    s ； t ≋ r →
    s ； t ≋ r′
  transport-result refl comp = comp


data NonFunctionCoercion : Coercion → Set where
  non-function-id :
    ∀ {A} →
    NonFunctionCoercion (C.id A)

  non-function-sequence :
    ∀ {c d} →
    NonFunctionCoercion (c C.︔ d)

  non-function-universal :
    ∀ {c} →
    NonFunctionCoercion (C.`∀ c)

  non-function-tag :
    ∀ {G} →
    NonFunctionCoercion (G C.!)

  non-function-untag :
    ∀ {G} →
    NonFunctionCoercion (G C.？)

  non-function-seal :
    ∀ {A α} →
    NonFunctionCoercion (C.seal A α)

  non-function-unseal :
    ∀ {α A} →
    NonFunctionCoercion (C.unseal α A)

  non-function-generalize :
    ∀ {A c} →
    NonFunctionCoercion (C.gen A c)

  non-function-instantiate :
    ∀ {A c} →
    NonFunctionCoercion (C.inst A c)


data NonPairedFunctionCoercions : Coercion → Coercion → Set where
  source-non-function :
    ∀ {d d′} →
    NonFunctionCoercion d →
    NonPairedFunctionCoercions d d′

  target-non-function :
    ∀ {d d′} →
    NonFunctionCoercion d′ →
    NonPairedFunctionCoercions d d′


mutual
  data ReductionClosedQuotientWideningCompatible
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
      (u u′ : Coercion) → {D D′ A A′ : Ty} →
      (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
      ImprecisionShape → ImprecisionShape → Set where

    compatible-through-non-function-representativesᴿ :
      ∀ {u u′ D D′ A A′ C C′ r p s s′ t t′}
        {src : D ForallPermutation.≈∀ C}
        {tgt : C′ ForallPermutation.≈∀ D′} →
      NonPairedFunctionCoercions u u′ →
      src ⊢ s ≈∀ˢ t →
      tgt ⊢ t′ ≈∀ˢ s′ →
      ReductionClosedPairedWideningCompatible
        Φ Δᴸ Δᴿ u u′
        {C} {C′} {A} {A′} r p t t′ →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′
        (quotientᵖ src r tgt) p s s′

    compatible-quotient-functionᴿ :
      ∀ {c d c′ d′ D₁ D₁′ D₂ D₂′ A₁ A₁′ A₂ A₂′
        q₁ q₂ p₁ p₂ qF
        c-shape d-shape c′-shape d′-shape} →
      ⊑ᵖ-arrow-components qF ≡ (q₁ , q₂) →
      QuotientNarrowingEliminationCompatible
        Φ Δᴸ Δᴿ c c′ p₁ q₁ c-shape c′-shape →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ d d′ q₂ p₂ d-shape d′-shape →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ
        (c C.↦ d) (c′ C.↦ d′)
        {D₁ ⇒ D₂} {D₁′ ⇒ D₂′}
        {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
        qF (p₁ ↦ p₂)
        (c-shape ↦ˢ d-shape) (c′-shape ↦ˢ d′-shape)

  data QuotientNarrowingEliminationCompatible
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
      (d d′ : Coercion) → {A A′ D D′ : Ty} →
      (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
      (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
      (d-shape d′-shape : ImprecisionShape) → Set where

    non-function-elimination :
      ∀ {d d′ A A′ D D′ p q d-shape d′-shape} →
      NonPairedFunctionCoercions d d′ →
      QuotientNarrowingEliminationCompatible
        Φ Δᴸ Δᴿ d d′
        {A} {A′} {D} {D′} p q d-shape d′-shape

    function-elimination :
      ∀ {a b a′ b′ A₁ A₁′ A₂ A₂′ D₁ D₁′ D₂ D₂′
        p₁ p₂ q₁ q₂ qF
        a-shape b-shape a′-shape b′-shape} →
      ⊑ᵖ-arrow-components qF ≡ (q₁ , q₂) →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ a a′ q₁ p₁ a-shape a′-shape →
      QuotientNarrowingEliminationCompatible
        Φ Δᴸ Δᴿ b b′ p₂ q₂ b-shape b′-shape →
      QuotientNarrowingEliminationCompatible
        Φ Δᴸ Δᴿ
        (a C.↦ b) (a′ C.↦ b′)
        {A₁ ⇒ A₂} {A₁′ ⇒ A₂′}
        {D₁ ⇒ D₂} {D₁′ ⇒ D₂′}
        (p₁ ↦ p₂) qF
        (a-shape ↦ˢ b-shape) (a′-shape ↦ˢ b′-shape)


mutual
  reduction-closed-quotient-compatible-result-shape-transport :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {u u′ : Coercion}
      {D D′ A A′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
      {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {u-shape u′-shape : ImprecisionShape} →
    ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ q p u-shape u′-shape →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ q p′ u-shape u′-shape
  reduction-closed-quotient-compatible-result-shape-transport
      p-shape
      (compatible-through-non-function-representativesᴿ
        non-function source-shape target-shape compatible) =
    compatible-through-non-function-representativesᴿ
      non-function source-shape target-shape
      (reduction-closed-paired-compatible-shape-transport
        refl p-shape compatible)
  reduction-closed-quotient-compatible-result-shape-transport
      {p′ = p₁′ ↦ p₂′} p-shape
      (compatible-quotient-functionᴿ components domain codomain) =
    compatible-quotient-functionᴿ components
      (quotient-narrowing-elimination-source-shape-transport
        (↦ˢ-left-injective p-shape) domain)
      (reduction-closed-quotient-compatible-result-shape-transport
        (↦ˢ-right-injective p-shape) codomain)

  quotient-narrowing-elimination-source-shape-transport :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {d d′ : Coercion}
      {A A′ D D′ : Ty}
      {p p′ : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
      {d-shape d′-shape : ImprecisionShape} →
    ⌊ p′ ⌋ ≡ ⌊ p ⌋ →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ p q d-shape d′-shape →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ p′ q d-shape d′-shape
  quotient-narrowing-elimination-source-shape-transport
      p-shape (non-function-elimination non-function) =
    non-function-elimination non-function
  quotient-narrowing-elimination-source-shape-transport
      {p′ = p₁′ ↦ p₂′} p-shape
      (function-elimination components domain codomain) =
    function-elimination components
      (reduction-closed-quotient-compatible-result-shape-transport
        (↦ˢ-left-injective p-shape) domain)
      (quotient-narrowing-elimination-source-shape-transport
        (↦ˢ-right-injective p-shape) codomain)


reduction-closed-exact-non-function-widening-compatible :
  ∀ {Φ Δᴸ Δᴿ u u′ D D′ A A′ r p s s′} →
  NonPairedFunctionCoercions u u′ →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ u u′
    {D} {D′} {A} {A′} r p s s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′
    (quotientᵖ ≈∀-refl r ≈∀-refl) p s s′
reduction-closed-exact-non-function-widening-compatible
    non-function compatible =
  compatible-through-non-function-representativesᴿ
    {src = ≈∀-refl} {tgt = ≈∀-refl}
    non-function source-perm-refl source-perm-refl compatible

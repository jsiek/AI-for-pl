module proof.EndpointMLB.Core.MLBGlbCounterexample where

-- File Charter:
--   * Formalizes the small counterexample from `GTSF/notes.md` showing that
--     lower bounds of two consistent types need not have a greatest element.
--   * Keeps the bad GLB theorem separate from the selector-specific maximal
--     lower-bound proof in `proof.EndpointMLB.Core.MaximalLowerBoundsWf`.
--   * Uses `ImprecisionWf` for the positive lower-bound witnesses and the
--     old imprecision decision procedure, via `⊑-forgetᵢ`, for the negative
--     incomparability witnesses.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)

open import Types
import Imprecision as Imp
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.Core.Properties.ImprecisionProperties using (idᵢ-var-identity)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using (MLB; rawEndpointMlbsAt)
open import proof.EndpointMLB.Core.MLBGlbExample
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( choice-idᵢ
  ; leftChoice-id-proofᵢ
  ; mlb-typeᵢ
  ; MlbTypeSelectorᵢ
  ; MlbTypeSelectorCoherenceᵢ
  ; rightChoice-id-proofᵢ
  ; ⊑-forgetᵢ
  )

------------------------------------------------------------------------
-- `mlb-typeᵢ` follows the lower-bound derivation order.
------------------------------------------------------------------------

glb-lower-XY-selected :
  mlb-typeᵢ glb-lower-XY⊑A glb-lower-XY⊑B ≡ glb-lower-XY
glb-lower-XY-selected = refl

glb-lower-YX-selected :
  mlb-typeᵢ glb-lower-YX⊑A glb-lower-YX⊑B ≡ glb-lower-YX
glb-lower-YX-selected = refl

------------------------------------------------------------------------
-- The flipped lower bounds are incomparable.
------------------------------------------------------------------------

glb-lower-XY⋢YX-old : ¬ (idᵢ zero Imp.⊢ glb-lower-XY ⊑ glb-lower-YX)
glb-lower-XY⋢YX-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    with idᵢ-var-identity x∈
glb-lower-XY⋢YX-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    | ()
glb-lower-XY⋢YX-old (Imp.∀ⁱ (Imp.ν occ ()))
glb-lower-XY⋢YX-old (Imp.ν occ (Imp.∀ⁱ ()))
glb-lower-XY⋢YX-old (Imp.ν occ (Imp.ν occ′ ()))

glb-lower-YX⋢XY-old : ¬ (idᵢ zero Imp.⊢ glb-lower-YX ⊑ glb-lower-XY)
glb-lower-YX⋢XY-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    with idᵢ-var-identity x∈
glb-lower-YX⋢XY-old (Imp.∀ⁱ (Imp.∀ⁱ (Imp.idˣ x∈ Imp.↦ q)))
    | ()
glb-lower-YX⋢XY-old (Imp.∀ⁱ (Imp.ν occ ()))
glb-lower-YX⋢XY-old (Imp.ν occ (Imp.∀ⁱ ()))
glb-lower-YX⋢XY-old (Imp.ν occ (Imp.ν occ′ ()))

glb-lower-XY⋢YX :
  ¬ (idᵢ zero ∣ zero ⊢ glb-lower-XY ⊑ glb-lower-YX ⊣ zero)
glb-lower-XY⋢YX p = glb-lower-XY⋢YX-old (⊑-forgetᵢ p)

glb-lower-YX⋢XY :
  ¬ (idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ glb-lower-XY ⊣ zero)
glb-lower-YX⋢XY p = glb-lower-YX⋢XY-old (⊑-forgetᵢ p)

------------------------------------------------------------------------
-- The source factors through the compatible raw target route.
------------------------------------------------------------------------

glb-lower-YX-raw :
  glb-lower-YX ∈ rawEndpointMlbsAt zero glb-bad-A glb-bad-B
glb-lower-YX-raw = there (here refl)

glb-lower-YX⊑YX :
  idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ glb-lower-YX ⊣ zero
glb-lower-YX⊑YX =
  ∀ⁱ
    (∀ⁱ
      ( idˣ (here refl) z<s z<s
      ↦ idˣ (there (here refl)) (s<s z<s) (s<s z<s)
      ))

glb-lower-YX-raw-factor :
  ∃[ D ]
    (D ∈ rawEndpointMlbsAt zero glb-bad-A glb-bad-B ×
     idᵢ zero ∣ zero ⊢ glb-lower-YX ⊑ D ⊣ zero)
glb-lower-YX-raw-factor =
  glb-lower-YX , glb-lower-YX-raw , glb-lower-YX⊑YX

------------------------------------------------------------------------
-- No maximal endpoint selector can satisfy the proposed broad coherence.
------------------------------------------------------------------------

bad-simple-selector-coherence-counterexampleᵢ :
  ¬
    (∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      MLB Δᴸ A B ≡ just C →
      MLB Δᴿ A′ B′ ≡ just C′ →
      Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
bad-simple-selector-coherence-counterexampleᵢ coherence =
  glb-lower-YX⋢XY
    (coherence
      {Φ = idᵢ zero}
      {Δᴸ = zero}
      {Δᴿ = zero}
      {A = glb-lower-YX}
      {A′ = glb-bad-A}
      {B = glb-lower-YX}
      {B′ = glb-bad-B}
      {C = glb-lower-YX}
      {C′ = glb-lower-XY}
      {pA = glb-lower-YX⊑A}
      {pB = glb-lower-YX⊑B}
      refl
      refl)

------------------------------------------------------------------------
-- The broad lower-bound-driven coherence theorem is refuted.
------------------------------------------------------------------------

bad-mlb-coherence-counterexampleᵢ :
  ¬
    (∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      (p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ) →
      (q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ) →
      (p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ) →
      (q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ) →
      Φ ∣ Δᴸ ⊢
        mlb-typeᵢ
          {Γ = choice-idᵢ Δᴸ}
          (leftChoice-id-proofᵢ p)
          (rightChoice-id-proofᵢ q)
        ⊑
        mlb-typeᵢ
          {Γ = choice-idᵢ Δᴿ}
          (leftChoice-id-proofᵢ p′)
          (rightChoice-id-proofᵢ q′)
        ⊣ Δᴿ)
bad-mlb-coherence-counterexampleᵢ coherence =
  glb-lower-XY⋢YX
    (coherence
      {Φ = idᵢ zero}
      {Δᴸ = zero}
      {Δᴿ = zero}
      {A = glb-bad-A}
      {A′ = glb-bad-A}
      {B = glb-bad-B}
      {B′ = glb-bad-B}
      {C = glb-lower-XY}
      {C′ = glb-lower-YX}
      {pA = glb-bad-A⊑A}
      {pB = glb-bad-B⊑B}
      glb-lower-XY⊑A
      glb-lower-XY⊑B
      glb-lower-YX⊑A
      glb-lower-YX⊑B)

bad-selector-coherence-counterexampleᵢ :
  (∀ {Δ C A B} →
    (p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
    (q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ) →
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)) →
  ¬
    (∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {p : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ A ⊣ Δᴸ}
      {q : idᵢ Δᴸ ∣ Δᴸ ⊢ C ⊑ B ⊣ Δᴸ}
      {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
      {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
      (route :
        MlbTypeSelectorᵢ
          {Γ = choice-idᵢ Δᴸ}
          (leftChoice-id-proofᵢ p)
          (rightChoice-id-proofᵢ q)) →
      (route′ :
        MlbTypeSelectorᵢ
          {Γ = choice-idᵢ Δᴿ}
          (leftChoice-id-proofᵢ p′)
          (rightChoice-id-proofᵢ q′)) →
      MlbTypeSelectorCoherenceᵢ Φ route route′)
bad-selector-coherence-counterexampleᵢ route coherence =
  glb-lower-XY⋢YX
    (coherence
      {Φ = idᵢ zero}
      {Δᴸ = zero}
      {Δᴿ = zero}
      {A = glb-bad-A}
      {A′ = glb-bad-A}
      {B = glb-bad-B}
      {B′ = glb-bad-B}
      {C = glb-lower-XY}
      {C′ = glb-lower-YX}
      {pA = glb-bad-A⊑A}
      {pB = glb-bad-B⊑B}
      {p = glb-lower-XY⊑A}
      {q = glb-lower-XY⊑B}
      {p′ = glb-lower-YX⊑A}
      {q′ = glb-lower-YX⊑B}
      (route glb-lower-XY⊑A glb-lower-XY⊑B)
      (route glb-lower-YX⊑A glb-lower-YX⊑B))

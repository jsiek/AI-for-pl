module proof.EndpointCanonicalMLBProof where

-- File Charter:
--   * Checked proof-target surface for the endpoint-canonical MLB algorithm.
--   * States the soundness, maximality, failure-completeness, and coherence
--     targets from `EndpointCanonicalMLBDesign.md` directly for `endpointMlb`.
--   * Provides the first checked bridge: a proof-producing common-lower
--     checker that certifies successful endpoint MLB results via the existing
--     decidable imprecision relation and `ImprecisionWf` conversion.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_<_; zero; suc; s<s; z<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.EndpointCanonicalMLB using (_==ᵇ_; endpointMlb)
open import proof.ImprecisionProperties using
  ( idᵢ-no-star
  ; imp?
  ; no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left
  ; ⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᴸᵢ-ˣ∈
  )
open import proof.MaximalLowerBoundsWf using
  ( CommonLowerBoundᵢ
  ; CanonicalLowerᵢ
  ; ComparableMaximalLowerBoundᵢ
  ; MaximalLowerBoundCoherenceᵢ
  ; MlbTypeSelectorᵢ
  ; MlbTypeSelectorCoherenceᵢ
  ; c-lowerᵢ
  ; c-lower-leftᵢ
  ; c-lower-rightᵢ
  ; c-comparableᵢ
  ; comparable⇒maximalᵢ
  ; comparable-arrow-arrowᵢ
  ; comparable-arrow-starᵢ
  ; comparable-forall-forall-from-supportᵢ
  ; comparable-star-arrowᵢ
  ; choice-id-comparable-selectorᵢ
  ; choice-id-commonCtxᵢ
  ; choice-idᵢ
  ; choiceCommonCtxᵢ
  ; comparable-star-starᵢ
  ; comparable-base-baseᵢ
  ; comparable-base-starᵢ
  ; comparable-star-baseᵢ
  ; comparable-var-varᵢ
  ; leftChoice-id-proofᵢ
  ; mlb-typeᵢ
  ; rightChoice-id-proofᵢ
  ; sel-∀νᵢ
  ; sel-∀ν-arrow-starᵢ
  ; sel-∀ν-non∀ᵢ
  ; sel-ν∀ᵢ
  ; sel-ν∀-star-arrowᵢ
  ; sel-ν∀-non∀ᵢ
  ; sel-first-orderᵢ
  ; fo-star-starᵢ
  ; fo-base-starᵢ
  ; fo-star-varᵢ
  ; fo-star-baseᵢ
  ; fo-var-starᵢ
  ; ForallForallComparableSupportᵢ
  ; FirstOrderSelectorAtᵢ
  ; left-endpoint-∀ν-supportᵢ
  ; leftChoice-id-proofAtᵢ
  ; mlb-type-from-lowerᵢ
  ; mlb-type-from-lower-first-order-canonicalᵢ
  ; mlb-type-from-lower-∀∀-first-order-maximal-coherenceᵢ
  ; mlb-type-from-lower-∀∀-first-order-target-maximal-coherenceᵢ
  ; right-endpoint-ν∀-supportᵢ
  ; rightChoice-id-proofAtᵢ
  ; canonical-lower-comparableᵢ
  ; canonical-lower-comparable-lowerᵢ
  ; canonical-maximal-lower-coherenceᵢ
  ; canonical-first-order-coherenceᵢ
  ; canonical-forall-forall-comparableᵢ
  ; canonical-forall-forall-comparable-lowerᵢ
  ; canonical-forall-forall-maximal-coherenceᵢ
  ; canonical-forall-forall-to-first-order-maximal-coherenceᵢ
  ; canonical-forall-forall-coherence-∀∀ᵢ
  ; old⊑→wf-idᵢ
  ; un⇑ᴸᵢ-★∈
  ; νᵢᶜ
  )

------------------------------------------------------------------------
-- Proof targets for the endpoint-canonical algorithm
------------------------------------------------------------------------

EndpointMlbSoundᵢ : TyCtx → Ty → Ty → Set
EndpointMlbSoundᵢ Δ A B =
  WfTy Δ A →
  WfTy Δ B →
  ∀ {C} →
  endpointMlb A B ≡ just C →
  CommonLowerBoundᵢ Δ A B C

EndpointMlbMaximalᵢ : TyCtx → Ty → Ty → Set
EndpointMlbMaximalᵢ Δ A B =
  WfTy Δ A →
  WfTy Δ B →
  ∀ {C D} →
  endpointMlb A B ≡ just C →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ

EndpointMlbFailureCompleteᵢ : TyCtx → Ty → Ty → Set
EndpointMlbFailureCompleteᵢ Δ A B =
  WfTy Δ A →
  WfTy Δ B →
  endpointMlb A B ≡ nothing →
  ∀ {D} →
  ¬ CommonLowerBoundᵢ Δ A B D

EndpointMlbCoherentᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  endpointMlb A B ≡ just C →
  endpointMlb A′ B′ ≡ just C′ →
  Set
EndpointMlbCoherentᵢ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {C = C} {C′ = C′} pA pB eq eq′ =
  Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ

EndpointMlbCoherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  Set
EndpointMlbCoherenceᵢ {A = A} {A′ = A′} {B = B} {B′ = B′} pA pB =
  ∀ {C C′} →
  (eq : endpointMlb A B ≡ just C) →
  (eq′ : endpointMlb A′ B′ ≡ just C′) →
  EndpointMlbCoherentᵢ pA pB eq eq′

------------------------------------------------------------------------
-- Proof-producing common-lower checker
------------------------------------------------------------------------

record EndpointMlbCommonLowerᵢ (Δ : TyCtx) (A B : Ty) : Set where
  constructor endpoint-common
  field
    endpointLowerᵢ : Ty
    endpointLowerEqᵢ : endpointMlb A B ≡ just endpointLowerᵢ
    endpointCommonᵢ : CommonLowerBoundᵢ Δ A B endpointLowerᵢ

open EndpointMlbCommonLowerᵢ public

endpointMlbCommonLower? :
  (Δ : TyCtx) → (A B : Ty) → Maybe (EndpointMlbCommonLowerᵢ Δ A B)
endpointMlbCommonLower? Δ A B with endpointMlb A B in eq
endpointMlbCommonLower? Δ A B | nothing = nothing
endpointMlbCommonLower? Δ A B | just C
    with imp? (idᵢ Δ) C A | imp? (idᵢ Δ) C B
endpointMlbCommonLower? Δ A B | just C | yes C⊑A | yes C⊑B =
  just
    (endpoint-common
      C
      eq
      (old⊑→wf-idᵢ C⊑A , old⊑→wf-idᵢ C⊑B))
endpointMlbCommonLower? Δ A B | just C | no _ | _ = nothing
endpointMlbCommonLower? Δ A B | just C | yes _ | no _ = nothing

endpointMlbCommonLowerTy? : TyCtx → Ty → Ty → Maybe Ty
endpointMlbCommonLowerTy? Δ A B with endpointMlbCommonLower? Δ A B
endpointMlbCommonLowerTy? Δ A B | nothing = nothing
endpointMlbCommonLowerTy? Δ A B | just certified =
  just (endpointLowerᵢ certified)

endpointMlb-certified-soundᵢ :
  ∀ {Δ A B} →
  (certified : EndpointMlbCommonLowerᵢ Δ A B) →
  CommonLowerBoundᵢ Δ A B (endpointLowerᵢ certified)
endpointMlb-certified-soundᵢ certified = endpointCommonᵢ certified

endpoint-common-lower-sound-targetᵢ :
  ∀ {Δ A B} →
  EndpointMlbCommonLowerᵢ Δ A B →
  EndpointMlbSoundᵢ Δ A B
endpoint-common-lower-sound-targetᵢ certified hA hB eq
    rewrite endpointLowerEqᵢ certified
    with eq
endpoint-common-lower-sound-targetᵢ certified hA hB eq | refl =
  endpointCommonᵢ certified

endpoint-common-lower-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (left : EndpointMlbCommonLowerᵢ Δᴸ A B) →
  (right : EndpointMlbCommonLowerᵢ Δᴿ A′ B′) →
  Φ ∣ Δᴸ ⊢ endpointLowerᵢ left ⊑ endpointLowerᵢ right ⊣ Δᴿ →
  EndpointMlbCoherenceᵢ pA pB
endpoint-common-lower-coherence-targetᵢ left right lower-coh eq eq′
    rewrite endpointLowerEqᵢ left
          | endpointLowerEqᵢ right
    with eq | eq′
endpoint-common-lower-coherence-targetᵢ left right lower-coh eq eq′
    | refl | refl =
  lower-coh

endpoint-common-lower-to-star-star-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ ★ ⊣ Δᴿ} →
  (certified : EndpointMlbCommonLowerᵢ Δᴸ A B) →
  Φ ∣ Δᴸ ⊢ endpointLowerᵢ certified ⊑ ★ ⊣ Δᴿ →
  EndpointMlbCoherenceᵢ pA pB
endpoint-common-lower-to-star-star-coherence-targetᵢ
    certified lower⊑★ eq eq′
    rewrite endpointLowerEqᵢ certified
    with eq | eq′
endpoint-common-lower-to-star-star-coherence-targetᵢ
    certified lower⊑★ eq eq′ | refl | refl =
  lower⊑★

==ᵇ-reflᵢ : ∀ X → (X ==ᵇ X) ≡ true
==ᵇ-reflᵢ zero = refl
==ᵇ-reflᵢ (suc X) = ==ᵇ-reflᵢ X

false≠trueᵢ : false ≡ true → ⊥
false≠trueᵢ ()

∨-falseᵢ : ∀ {b c} → b ≡ false → c ≡ false → b ∨ c ≡ false
∨-falseᵢ {b = false} {c = false} refl refl = refl
∨-falseᵢ {b = false} {c = true} refl ()
∨-falseᵢ {b = true} {c = false} ()
∨-falseᵢ {b = true} {c = true} ()

endpointMlb-var-varᵢ :
  ∀ X →
  endpointMlb (＇ X) (＇ X) ≡ just (＇ X)
endpointMlb-var-varᵢ zero = refl
endpointMlb-var-varᵢ (suc X) rewrite ==ᵇ-reflᵢ X = refl

------------------------------------------------------------------------
-- Well-formedness boundary for the endpoint proof targets
------------------------------------------------------------------------

endpointMlb-ill-scoped-var-computes :
  endpointMlb (＇ 0) (＇ 0) ≡ just (＇ 0)
endpointMlb-ill-scoped-var-computes = refl

endpointMlb-ill-scoped-var-no-common-lowerᵢ :
  ¬ CommonLowerBoundᵢ 0 (＇ 0) (＇ 0) (＇ 0)
endpointMlb-ill-scoped-var-no-common-lowerᵢ (idˣ _ () _ , _)

------------------------------------------------------------------------
-- Failure-completeness certificates for endpoint `nothing` results
------------------------------------------------------------------------

record EndpointMlbFailureᵢ (Δ : TyCtx) (A B : Ty) : Set where
  constructor endpoint-failure
  field
    endpointFailureEqᵢ : endpointMlb A B ≡ nothing
    endpointNoCommonᵢ : ∀ {D} → ¬ CommonLowerBoundᵢ Δ A B D

open EndpointMlbFailureᵢ public

endpoint-failure-complete-targetᵢ :
  ∀ {Δ A B} →
  EndpointMlbFailureᵢ Δ A B →
  EndpointMlbFailureCompleteᵢ Δ A B
endpoint-failure-complete-targetᵢ certified hA hB eq
    rewrite endpointFailureEqᵢ certified
    with eq
endpoint-failure-complete-targetᵢ certified hA hB eq | refl =
  endpointNoCommonᵢ certified

no-common-ℕ-𝔹ᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ ‵ `ℕ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ‵ `𝔹 ⊣ Δᴿ)
no-common-ℕ-𝔹ᵢ idι ()
no-common-ℕ-𝔹ᵢ (ν occ p) (ν occ′ q) = no-common-ℕ-𝔹ᵢ p q

no-common-𝔹-ℕᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ ‵ `𝔹 ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ‵ `ℕ ⊣ Δᴿ)
no-common-𝔹-ℕᵢ p q = no-common-ℕ-𝔹ᵢ q p

endpoint-failure-base-mismatch-ℕ𝔹ᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (‵ `ℕ) (‵ `𝔹)
endpoint-failure-base-mismatch-ℕ𝔹ᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (‵ `ℕ) (‵ `𝔹) D
    no-common (p , q) = no-common-ℕ-𝔹ᵢ p q

endpoint-failure-base-mismatch-𝔹ℕᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (‵ `𝔹) (‵ `ℕ)
endpoint-failure-base-mismatch-𝔹ℕᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (‵ `𝔹) (‵ `ℕ) D
    no-common (p , q) = no-common-𝔹-ℕᵢ p q

no-common-var-baseᵢ :
  ∀ {Φ Δᴸ Δᴿ D X ι} →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ X ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ‵ ι ⊣ Δᴿ)
no-common-var-baseᵢ (idˣ _ _ _) ()
no-common-var-baseᵢ (ν occ p) (ν occ′ q) =
  no-common-var-baseᵢ p q

no-common-base-varᵢ :
  ∀ {Φ Δᴸ Δᴿ D X ι} →
  Φ ∣ Δᴸ ⊢ D ⊑ ‵ ι ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ＇ X ⊣ Δᴿ)
no-common-base-varᵢ p q = no-common-var-baseᵢ q p

endpoint-failure-var-baseᵢ :
  ∀ {Δ X ι} →
  EndpointMlbFailureᵢ Δ (＇ X) (‵ ι)
endpoint-failure-var-baseᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ X ι D} →
      ¬ CommonLowerBoundᵢ Δ (＇ X) (‵ ι) D
    no-common (p , q) = no-common-var-baseᵢ p q

endpoint-failure-base-varᵢ :
  ∀ {Δ X ι} →
  EndpointMlbFailureᵢ Δ (‵ ι) (＇ X)
endpoint-failure-base-varᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ X ι D} →
      ¬ CommonLowerBoundᵢ Δ (‵ ι) (＇ X) D
    no-common (p , q) = no-common-base-varᵢ p q

no-common-base-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ D ι A B} →
  Φ ∣ Δᴸ ⊢ D ⊑ ‵ ι ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ A ⇒ B ⊣ Δᴿ)
no-common-base-arrowᵢ idι ()
no-common-base-arrowᵢ (ν occ p) (ν occ′ q) =
  no-common-base-arrowᵢ p q

no-common-arrow-baseᵢ :
  ∀ {Φ Δᴸ Δᴿ D ι A B} →
  Φ ∣ Δᴸ ⊢ D ⊑ A ⇒ B ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ‵ ι ⊣ Δᴿ)
no-common-arrow-baseᵢ p q = no-common-base-arrowᵢ q p

endpoint-failure-base-arrowᵢ :
  ∀ {Δ ι A B} →
  EndpointMlbFailureᵢ Δ (‵ ι) (A ⇒ B)
endpoint-failure-base-arrowᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ ι A B D} →
      ¬ CommonLowerBoundᵢ Δ (‵ ι) (A ⇒ B) D
    no-common (p , q) = no-common-base-arrowᵢ p q

endpoint-failure-arrow-baseᵢ :
  ∀ {Δ ι A B} →
  EndpointMlbFailureᵢ Δ (A ⇒ B) (‵ ι)
endpoint-failure-arrow-baseᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ ι A B D} →
      ¬ CommonLowerBoundᵢ Δ (A ⇒ B) (‵ ι) D
    no-common (p , q) = no-common-arrow-baseᵢ p q

no-common-var-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ D X A B} →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ X ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ A ⇒ B ⊣ Δᴿ)
no-common-var-arrowᵢ (idˣ _ _ _) ()
no-common-var-arrowᵢ (ν occ p) (ν occ′ q) =
  no-common-var-arrowᵢ p q

no-common-arrow-varᵢ :
  ∀ {Φ Δᴸ Δᴿ D X A B} →
  Φ ∣ Δᴸ ⊢ D ⊑ A ⇒ B ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ＇ X ⊣ Δᴿ)
no-common-arrow-varᵢ p q = no-common-var-arrowᵢ q p

endpoint-failure-var-arrowᵢ :
  ∀ {Δ X A B} →
  EndpointMlbFailureᵢ Δ (＇ X) (A ⇒ B)
endpoint-failure-var-arrowᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ X A B D} →
      ¬ CommonLowerBoundᵢ Δ (＇ X) (A ⇒ B) D
    no-common (p , q) = no-common-var-arrowᵢ p q

endpoint-failure-arrow-varᵢ :
  ∀ {Δ X A B} →
  EndpointMlbFailureᵢ Δ (A ⇒ B) (＇ X)
endpoint-failure-arrow-varᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ X A B D} →
      ¬ CommonLowerBoundᵢ Δ (A ⇒ B) (＇ X) D
    no-common (p , q) = no-common-arrow-varᵢ p q

no-common-arrow-arrow-domainᵢ :
  ∀ {A₁ A₂ B₁ B₂ Φ Δᴸ Δᴿ D} →
  (∀ {Φ′ Δᴸ′ Δᴿ′ E} →
    Φ′ ∣ Δᴸ′ ⊢ E ⊑ A₁ ⊣ Δᴿ′ →
    ¬ (Φ′ ∣ Δᴸ′ ⊢ E ⊑ B₁ ⊣ Δᴿ′)) →
  Φ ∣ Δᴸ ⊢ D ⊑ A₁ ⇒ A₂ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₁ ⇒ B₂ ⊣ Δᴿ)
no-common-arrow-arrow-domainᵢ no-domain (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-domain p₁ q₁
no-common-arrow-arrow-domainᵢ no-domain (ν occ p) (ν occ′ q) =
  no-common-arrow-arrow-domainᵢ no-domain p q

no-common-arrow-arrow-codomainᵢ :
  ∀ {A₁ A₂ B₁ B₂ Φ Δᴸ Δᴿ D} →
  (∀ {Φ′ Δᴸ′ Δᴿ′ E} →
    Φ′ ∣ Δᴸ′ ⊢ E ⊑ A₂ ⊣ Δᴿ′ →
    ¬ (Φ′ ∣ Δᴸ′ ⊢ E ⊑ B₂ ⊣ Δᴿ′)) →
  Φ ∣ Δᴸ ⊢ D ⊑ A₁ ⇒ A₂ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₁ ⇒ B₂ ⊣ Δᴿ)
no-common-arrow-arrow-codomainᵢ no-codomain (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-codomain p₂ q₂
no-common-arrow-arrow-codomainᵢ no-codomain (ν occ p) (ν occ′ q) =
  no-common-arrow-arrow-codomainᵢ no-codomain p q

endpoint-failure-arrow-arrow-domainᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  (∀ {Φ Δᴸ Δᴿ D} →
    Φ ∣ Δᴸ ⊢ D ⊑ A₁ ⊣ Δᴿ →
    ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₁ ⊣ Δᴿ)) →
  endpointMlb (A₁ ⇒ A₂) (B₁ ⇒ B₂) ≡ nothing →
  EndpointMlbFailureᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
endpoint-failure-arrow-arrow-domainᵢ
    {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} no-domain eq =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) D
    no-common (p , q) = no-common-arrow-arrow-domainᵢ no-domain p q

endpoint-failure-arrow-arrow-codomainᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  (∀ {Φ Δᴸ Δᴿ D} →
    Φ ∣ Δᴸ ⊢ D ⊑ A₂ ⊣ Δᴿ →
    ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₂ ⊣ Δᴿ)) →
  endpointMlb (A₁ ⇒ A₂) (B₁ ⇒ B₂) ≡ nothing →
  EndpointMlbFailureᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
endpoint-failure-arrow-arrow-codomainᵢ
    {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂}
    no-codomain eq =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) D
    no-common (p , q) = no-common-arrow-arrow-codomainᵢ no-codomain p q

endpoint-failure-arrow-arrow-domain-ℕ𝔹ᵢ :
  ∀ {Δ A B} →
  EndpointMlbFailureᵢ Δ ((‵ `ℕ) ⇒ A) ((‵ `𝔹) ⇒ B)
endpoint-failure-arrow-arrow-domain-ℕ𝔹ᵢ =
  endpoint-failure-arrow-arrow-domainᵢ no-common-ℕ-𝔹ᵢ refl

endpoint-failure-arrow-arrow-domain-𝔹ℕᵢ :
  ∀ {Δ A B} →
  EndpointMlbFailureᵢ Δ ((‵ `𝔹) ⇒ A) ((‵ `ℕ) ⇒ B)
endpoint-failure-arrow-arrow-domain-𝔹ℕᵢ =
  endpoint-failure-arrow-arrow-domainᵢ no-common-𝔹-ℕᵢ refl

endpoint-failure-arrow-arrow-codomain-ℕ𝔹ᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ‵ `ℕ) (★ ⇒ ‵ `𝔹)
endpoint-failure-arrow-arrow-codomain-ℕ𝔹ᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ no-common-ℕ-𝔹ᵢ refl

endpoint-failure-arrow-arrow-codomain-𝔹ℕᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ‵ `𝔹) (★ ⇒ ‵ `ℕ)
endpoint-failure-arrow-arrow-codomain-𝔹ℕᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ no-common-𝔹-ℕᵢ refl

no-common-arrow-star-domainᵢ :
  ∀ {A₁ A₂ Φ Δᴸ Δᴿ D} →
  (∀ {Φ′ Δᴸ′ Δᴿ′ E} →
    Φ′ ∣ Δᴸ′ ⊢ E ⊑ A₁ ⊣ Δᴿ′ →
    ¬ (Φ′ ∣ Δᴸ′ ⊢ E ⊑ ★ ⊣ Δᴿ′)) →
  Φ ∣ Δᴸ ⊢ D ⊑ A₁ ⇒ A₂ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-arrow-star-domainᵢ no-domain (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  no-domain p₁ q₁
no-common-arrow-star-domainᵢ no-domain (ν occ p) (ν occ′ q) =
  no-common-arrow-star-domainᵢ no-domain p q

no-common-arrow-star-codomainᵢ :
  ∀ {A₁ A₂ Φ Δᴸ Δᴿ D} →
  (∀ {Φ′ Δᴸ′ Δᴿ′ E} →
    Φ′ ∣ Δᴸ′ ⊢ E ⊑ A₂ ⊣ Δᴿ′ →
    ¬ (Φ′ ∣ Δᴸ′ ⊢ E ⊑ ★ ⊣ Δᴿ′)) →
  Φ ∣ Δᴸ ⊢ D ⊑ A₁ ⇒ A₂ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-arrow-star-codomainᵢ no-codomain (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  no-codomain p₂ q₂
no-common-arrow-star-codomainᵢ no-codomain (ν occ p) (ν occ′ q) =
  no-common-arrow-star-codomainᵢ no-codomain p q

no-common-star-arrow-domainᵢ :
  ∀ {B₁ B₂ Φ Δᴸ Δᴿ D} →
  (∀ {Φ′ Δᴸ′ Δᴿ′ E} →
    Φ′ ∣ Δᴸ′ ⊢ E ⊑ ★ ⊣ Δᴿ′ →
    ¬ (Φ′ ∣ Δᴸ′ ⊢ E ⊑ B₁ ⊣ Δᴿ′)) →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₁ ⇒ B₂ ⊣ Δᴿ)
no-common-star-arrow-domainᵢ no-domain (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  no-domain p₁ q₁
no-common-star-arrow-domainᵢ no-domain (ν occ p) (ν occ′ q) =
  no-common-star-arrow-domainᵢ no-domain p q

no-common-star-arrow-codomainᵢ :
  ∀ {B₁ B₂ Φ Δᴸ Δᴿ D} →
  (∀ {Φ′ Δᴸ′ Δᴿ′ E} →
    Φ′ ∣ Δᴸ′ ⊢ E ⊑ ★ ⊣ Δᴿ′ →
    ¬ (Φ′ ∣ Δᴸ′ ⊢ E ⊑ B₂ ⊣ Δᴿ′)) →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₁ ⇒ B₂ ⊣ Δᴿ)
no-common-star-arrow-codomainᵢ no-codomain (tag p₁ ⇛ p₂) (q₁ ↦ q₂) =
  no-codomain p₂ q₂
no-common-star-arrow-codomainᵢ no-codomain (ν occ p) (ν occ′ q) =
  no-common-star-arrow-codomainᵢ no-codomain p q

endpoint-failure-arrow-star-domainᵢ :
  ∀ {Δ A₁ A₂} →
  (∀ {Φ Δᴸ Δᴿ D} →
    Φ ∣ Δᴸ ⊢ D ⊑ A₁ ⊣ Δᴿ →
    ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)) →
  endpointMlb (A₁ ⇒ A₂) ★ ≡ nothing →
  EndpointMlbFailureᵢ Δ (A₁ ⇒ A₂) ★
endpoint-failure-arrow-star-domainᵢ
    {A₁ = A₁} {A₂ = A₂} no-domain eq =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (A₁ ⇒ A₂) ★ D
    no-common (p , q) = no-common-arrow-star-domainᵢ no-domain p q

endpoint-failure-arrow-star-codomainᵢ :
  ∀ {Δ A₁ A₂} →
  (∀ {Φ Δᴸ Δᴿ D} →
    Φ ∣ Δᴸ ⊢ D ⊑ A₂ ⊣ Δᴿ →
    ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)) →
  endpointMlb (A₁ ⇒ A₂) ★ ≡ nothing →
  EndpointMlbFailureᵢ Δ (A₁ ⇒ A₂) ★
endpoint-failure-arrow-star-codomainᵢ
    {A₁ = A₁} {A₂ = A₂} no-codomain eq =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (A₁ ⇒ A₂) ★ D
    no-common (p , q) = no-common-arrow-star-codomainᵢ no-codomain p q

endpoint-failure-star-arrow-domainᵢ :
  ∀ {Δ B₁ B₂} →
  (∀ {Φ Δᴸ Δᴿ D} →
    Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
    ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₁ ⊣ Δᴿ)) →
  endpointMlb ★ (B₁ ⇒ B₂) ≡ nothing →
  EndpointMlbFailureᵢ Δ ★ (B₁ ⇒ B₂)
endpoint-failure-star-arrow-domainᵢ
    {B₁ = B₁} {B₂ = B₂} no-domain eq =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ ★ (B₁ ⇒ B₂) D
    no-common (p , q) = no-common-star-arrow-domainᵢ no-domain p q

endpoint-failure-star-arrow-codomainᵢ :
  ∀ {Δ B₁ B₂} →
  (∀ {Φ Δᴸ Δᴿ D} →
    Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
    ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B₂ ⊣ Δᴿ)) →
  endpointMlb ★ (B₁ ⇒ B₂) ≡ nothing →
  EndpointMlbFailureᵢ Δ ★ (B₁ ⇒ B₂)
endpoint-failure-star-arrow-codomainᵢ
    {B₁ = B₁} {B₂ = B₂} no-codomain eq =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ ★ (B₁ ⇒ B₂) D
    no-common (p , q) = no-common-star-arrow-codomainᵢ no-codomain p q

NoVarStarOverlapᵢ : ImpCtx → Set
NoVarStarOverlapᵢ Φ =
  ∀ {W X} →
  (W ˣ⊑ˣ X) ∈ Φ →
  (W ˣ⊑★) ∈ Φ →
  ⊥

id-no-var-star-overlapᵢ : ∀ Δ → NoVarStarOverlapᵢ (idᵢ Δ)
id-no-var-star-overlapᵢ Δ w⊑x w⊑★ = idᵢ-no-star w⊑★

ν-no-var-star-overlapᵢ :
  ∀ {Φ} →
  NoVarStarOverlapᵢ Φ →
  NoVarStarOverlapᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
ν-no-var-star-overlapᵢ no-overlap (here ()) w⊑★
ν-no-var-star-overlapᵢ no-overlap {W = zero}
    (there w⊑x) (here refl) =
  no-⇑ᴸᵢ-zero-left w⊑x
ν-no-var-star-overlapᵢ no-overlap {W = suc W} w⊑x (here ())
ν-no-var-star-overlapᵢ no-overlap {W = zero}
    (there w⊑x) (there w⊑★) =
  no-⇑ᴸᵢ-zero-left w⊑x
ν-no-var-star-overlapᵢ no-overlap {W = suc W}
    (there w⊑x) (there w⊑★) =
  no-overlap (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★)

no-common-var-star-overlapᵢ :
  ∀ {Φ Δᴸ Δᴿ D X} →
  NoVarStarOverlapᵢ Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ X ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-var-star-overlapᵢ no-overlap
    (idˣ w⊑x _ _) (tagˣ w⊑★ _) =
  no-overlap w⊑x w⊑★
no-common-var-star-overlapᵢ no-overlap (ν occ p) (ν occ′ q) =
  no-common-var-star-overlapᵢ
    (ν-no-var-star-overlapᵢ no-overlap)
    p
    q

no-common-star-var-overlapᵢ :
  ∀ {Φ Δᴸ Δᴿ D X} →
  NoVarStarOverlapᵢ Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ＇ X ⊣ Δᴿ)
no-common-star-var-overlapᵢ no-overlap p q =
  no-common-var-star-overlapᵢ no-overlap q p

no-common-arrow-var-star-star-var-overlapᵢ :
  ∀ {Φ Δᴸ Δᴿ D X} →
  NoVarStarOverlapᵢ Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ (＇ X ⇒ ★) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ (★ ⇒ ＇ X) ⊣ Δᴿ)
no-common-arrow-var-star-star-var-overlapᵢ no-overlap
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-common-var-star-overlapᵢ no-overlap p₁ q₁
no-common-arrow-var-star-star-var-overlapᵢ no-overlap
    (ν occ p) (ν occ′ q) =
  no-common-arrow-var-star-star-var-overlapᵢ
    (ν-no-var-star-overlapᵢ no-overlap)
    p
    q

NoTargetZeroStarOverlapᵢ : ImpCtx → Set
NoTargetZeroStarOverlapᵢ Φ =
  ∀ {W} →
  (W ˣ⊑ˣ zero) ∈ Φ →
  (W ˣ⊑★) ∈ Φ →
  ⊥

NoTargetZeroAtZeroᵢ : ImpCtx → Set
NoTargetZeroAtZeroᵢ Φ = (zero ˣ⊑ˣ zero) ∈ Φ → ⊥

OnlyTargetZeroAtZeroᵢ : ImpCtx → Set
OnlyTargetZeroAtZeroᵢ Φ =
  ∀ {W} →
  (W ˣ⊑ˣ zero) ∈ Φ →
  W ≡ zero

NoTargetZeroZeroCrossᵢ : ImpCtx → ImpCtx → Set
NoTargetZeroZeroCrossᵢ Φ Ψ =
  ∀ {W} →
  (W ˣ⊑ˣ zero) ∈ Φ →
  (W ˣ⊑ˣ zero) ∈ Ψ →
  ⊥

NoVarLeftAtᵢ : TyVar → ImpCtx → Set
NoVarLeftAtᵢ X Φ = ∀ {Y} → (X ˣ⊑ˣ Y) ∈ Φ → ⊥

NoVarTargetAtᵢ : TyVar → TyVar → ImpCtx → Set
NoVarTargetAtᵢ X Y Φ = (X ˣ⊑ˣ Y) ∈ Φ → ⊥

OnlyTargetAtᵢ : TyVar → TyVar → ImpCtx → Set
OnlyTargetAtᵢ X Y Φ =
  ∀ {W} →
  (W ˣ⊑ˣ Y) ∈ Φ →
  W ≡ X

νctx-no-target-zero-at-zeroᵢ :
  ∀ {Φ} →
  NoTargetZeroAtZeroᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-target-zero-at-zeroᵢ (there w⊑0) =
  no-⇑ᴸᵢ-zero-left w⊑0

∀ctx-only-target-zero-at-zeroᵢ :
  ∀ {Φ} →
  OnlyTargetZeroAtZeroᵢ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-only-target-zero-at-zeroᵢ (here refl) = refl
∀ctx-only-target-zero-at-zeroᵢ (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)

∀ctx-only-target-zero-zeroᵢ :
  ∀ {Φ} →
  OnlyTargetAtᵢ zero zero ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-only-target-zero-zeroᵢ (here refl) = refl
∀ctx-only-target-zero-zeroᵢ (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)

target-zero-cross-fromᵢ :
  ∀ {Φ Ψ} →
  NoTargetZeroAtZeroᵢ Φ →
  OnlyTargetZeroAtZeroᵢ Ψ →
  NoTargetZeroZeroCrossᵢ Φ Ψ
target-zero-cross-fromᵢ no-zero only-zero w⊑0 w⊑0′
    with only-zero w⊑0′
target-zero-cross-fromᵢ no-zero only-zero w⊑0 w⊑0′ | refl =
  no-zero w⊑0

target-zero-cross-from-rightᵢ :
  ∀ {Φ Ψ} →
  OnlyTargetZeroAtZeroᵢ Φ →
  NoTargetZeroAtZeroᵢ Ψ →
  NoTargetZeroZeroCrossᵢ Φ Ψ
target-zero-cross-from-rightᵢ only-zero no-zero w⊑0 w⊑0′
    with only-zero w⊑0
target-zero-cross-from-rightᵢ only-zero no-zero w⊑0 w⊑0′ | refl =
  no-zero w⊑0′

νctx-no-var-left-zeroᵢ :
  ∀ {Φ} →
  NoVarLeftAtᵢ zero ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-var-left-zeroᵢ (there x∈) = no-⇑ᴸᵢ-zero-left x∈

νctx-no-var-left-sucᵢ :
  ∀ {Φ X} →
  NoVarLeftAtᵢ X Φ →
  NoVarLeftAtᵢ (suc X) ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-var-left-sucᵢ noX (there x∈) =
  noX (un⇑ᴸᵢ-ˣ∈ x∈)

∀ctx-no-var-left-sucᵢ :
  ∀ {Φ X} →
  NoVarLeftAtᵢ X Φ →
  NoVarLeftAtᵢ (suc X) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-no-var-left-sucᵢ noX {Y = zero} (there x∈) =
  no-⇑ᵢ-zero-right x∈
∀ctx-no-var-left-sucᵢ noX {Y = suc Y} (there x∈) =
  noX (un⇑ᵢ-ˣ∈ x∈)

νctx-no-var-target-sucᵢ :
  ∀ {Φ X Y} →
  NoVarTargetAtᵢ X Y Φ →
  NoVarTargetAtᵢ (suc X) Y ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-var-target-sucᵢ noXY (there x∈) =
  noXY (un⇑ᴸᵢ-ˣ∈ x∈)

νctx-no-var-target-zeroᵢ :
  ∀ {Φ Y} →
  NoVarTargetAtᵢ zero Y ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-var-target-zeroᵢ (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈

νctx-only-target-sucᵢ :
  ∀ {Φ X Y} →
  OnlyTargetAtᵢ X Y Φ →
  OnlyTargetAtᵢ (suc X) Y ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-only-target-sucᵢ only (here ())
νctx-only-target-sucᵢ only {W = zero} (there w∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w∈)
νctx-only-target-sucᵢ only {W = suc W} (there w∈)
    with only (un⇑ᴸᵢ-ˣ∈ w∈)
νctx-only-target-sucᵢ only {W = suc W} (there w∈) | refl = refl

∀ctx-no-var-target-zero-sucᵢ :
  ∀ {Φ Y} →
  NoVarTargetAtᵢ zero (suc Y) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-no-var-target-zero-sucᵢ (here ())
∀ctx-no-var-target-zero-sucᵢ (there x∈) =
  no-⇑ᵢ-zero-left x∈

∀ctx-no-var-target-suc-sucᵢ :
  ∀ {Φ X Y} →
  NoVarTargetAtᵢ X Y Φ →
  NoVarTargetAtᵢ (suc X) (suc Y) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-no-var-target-suc-sucᵢ noXY (here ())
∀ctx-no-var-target-suc-sucᵢ noXY (there x∈) =
  noXY (un⇑ᵢ-ˣ∈ x∈)

∀ctx-no-var-target-suc-zeroᵢ :
  ∀ {Φ X} →
  NoVarTargetAtᵢ (suc X) zero ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-no-var-target-suc-zeroᵢ (here ())
∀ctx-no-var-target-suc-zeroᵢ (there x∈) =
  no-⇑ᵢ-zero-right x∈

∀ctx-only-target-suc-sucᵢ :
  ∀ {Φ X Y} →
  OnlyTargetAtᵢ X Y Φ →
  OnlyTargetAtᵢ (suc X) (suc Y) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-only-target-suc-sucᵢ only (here ())
∀ctx-only-target-suc-sucᵢ only {W = zero} (there w∈) =
  ⊥-elim (no-⇑ᵢ-zero-left w∈)
∀ctx-only-target-suc-sucᵢ only {W = suc W} (there w∈)
    with only (un⇑ᵢ-ˣ∈ w∈)
∀ctx-only-target-suc-sucᵢ only {W = suc W} (there w∈) | refl = refl

∀ctx-no-target-zero-star-overlapᵢ :
  ∀ {Φ} →
  NoTargetZeroStarOverlapᵢ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-no-target-zero-star-overlapᵢ (here refl) (here ())
∀ctx-no-target-zero-star-overlapᵢ (here refl) (there w★∈) =
  no-⇑ᵢ-zero-star w★∈
∀ctx-no-target-zero-star-overlapᵢ (there w⊑0) w★∈ =
  no-⇑ᵢ-zero-right w⊑0

νctx-no-target-zero-star-overlapᵢ :
  ∀ {Φ} →
  NoTargetZeroStarOverlapᵢ Φ →
  NoTargetZeroStarOverlapᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-target-zero-star-overlapᵢ no-overlap (here ()) w★∈
νctx-no-target-zero-star-overlapᵢ no-overlap {W = zero}
    (there w⊑0) (here refl) =
  no-⇑ᴸᵢ-zero-left w⊑0
νctx-no-target-zero-star-overlapᵢ no-overlap {W = suc W}
    w⊑0 (here ())
νctx-no-target-zero-star-overlapᵢ no-overlap {W = zero}
    (there w⊑0) (there w★∈) =
  no-⇑ᴸᵢ-zero-left w⊑0
νctx-no-target-zero-star-overlapᵢ no-overlap {W = suc W}
    (there w⊑0) (there w★∈) =
  no-overlap (un⇑ᴸᵢ-ˣ∈ w⊑0) (un⇑ᴸᵢ-★∈ w★∈)

no-common-target-var0-star-overlapᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  NoTargetZeroStarOverlapᵢ Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-target-var0-star-overlapᵢ no-overlap
    (idˣ w⊑0 _ _) (tagˣ w★∈ _) =
  no-overlap w⊑0 w★∈
no-common-target-var0-star-overlapᵢ no-overlap (ν occ p) (ν occ′ q) =
  no-common-target-var0-star-overlapᵢ
    (νctx-no-target-zero-star-overlapᵢ no-overlap)
    p
    q

occurs-var-reflᵢ : ∀ X → occurs X (＇ X) ≡ true
occurs-var-reflᵢ X with X ≟ X
occurs-var-reflᵢ X | yes refl = refl
occurs-var-reflᵢ X | no X≢X = ⊥-elim (X≢X refl)

⊑-to-target-var-occurs-false-atᵢ :
  ∀ {Φ Δᴸ Δᴿ C Y} X →
  NoVarTargetAtᵢ X Y Φ →
  Φ ∣ Δᴸ ⊢ C ⊑ ＇ Y ⊣ Δᴿ →
  occurs X C ≡ false
⊑-to-target-var-occurs-false-atᵢ X noXY (idˣ {X = z} x∈ _ _)
    with X ≟ z
⊑-to-target-var-occurs-false-atᵢ X noXY (idˣ {X = .X} x∈ _ _)
    | yes refl =
  ⊥-elim (noXY x∈)
⊑-to-target-var-occurs-false-atᵢ X noXY (idˣ {X = z} x∈ _ _)
    | no X≢z =
  refl
⊑-to-target-var-occurs-false-atᵢ X noXY (ν occ p) =
  ⊑-to-target-var-occurs-false-atᵢ
    (suc X)
    (νctx-no-var-target-sucᵢ noXY)
    p

⊑-to-only-target-var-occurs-trueᵢ :
  ∀ {Φ Δᴸ Δᴿ C Y} X →
  OnlyTargetAtᵢ X Y Φ →
  Φ ∣ Δᴸ ⊢ C ⊑ ＇ Y ⊣ Δᴿ →
  occurs X C ≡ true
⊑-to-only-target-var-occurs-trueᵢ X only (idˣ {X = z} x∈ _ _)
    with only x∈
⊑-to-only-target-var-occurs-trueᵢ X only (idˣ {X = .X} x∈ _ _)
    | refl =
  occurs-var-reflᵢ X
⊑-to-only-target-var-occurs-trueᵢ X only (ν occ p) =
  ⊑-to-only-target-var-occurs-trueᵢ
    (suc X)
    (νctx-only-target-sucᵢ only)
    p

no-common-target-var-by-occursᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ C Y Z} X →
  NoVarTargetAtᵢ X Y Φ →
  OnlyTargetAtᵢ X Z Ψ →
  Φ ∣ Δᴸ ⊢ C ⊑ ＇ Y ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ C ⊑ ＇ Z ⊣ Δᴿ)
no-common-target-var-by-occursᵢ X noXY only p q =
  false≠trueᵢ
    (trans
      (sym (⊑-to-target-var-occurs-false-atᵢ X noXY p))
      (⊑-to-only-target-var-occurs-trueᵢ X only q))

no-common-target-var-by-occurs′ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴿ′ C Y Z} X →
  NoVarTargetAtᵢ X Y Φ →
  OnlyTargetAtᵢ X Z Ψ →
  Φ ∣ Δᴸ ⊢ C ⊑ ＇ Y ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ C ⊑ ＇ Z ⊣ Δᴿ′)
no-common-target-var-by-occurs′ᵢ X noXY only p q =
  false≠trueᵢ
    (trans
      (sym (⊑-to-target-var-occurs-false-atᵢ X noXY p))
      (⊑-to-only-target-var-occurs-trueᵢ X only q))

νctx-no-forall-target-sucᵢ :
  ∀ {Φ X Y} →
  NoVarTargetAtᵢ (suc X) (suc Y) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  NoVarTargetAtᵢ
    (suc (suc X))
    (suc Y)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
νctx-no-forall-target-sucᵢ noXY (here ())
νctx-no-forall-target-sucᵢ noXY (there x∈)
    with un⇑ᵢ-ˣ∈ x∈
νctx-no-forall-target-sucᵢ noXY (there x∈) | here ()
νctx-no-forall-target-sucᵢ noXY (there x∈) | there y∈ =
  noXY (there (⇑ᵢ-ˣ∈ (un⇑ᴸᵢ-ˣ∈ y∈)))

∀νctx-no-var-target-one-oneᵢ :
  ∀ {Φ} →
  NoVarTargetAtᵢ
    (suc zero)
    (suc zero)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
∀νctx-no-var-target-one-oneᵢ (here ())
∀νctx-no-var-target-one-oneᵢ (there x∈)
    with un⇑ᵢ-ˣ∈ x∈
∀νctx-no-var-target-one-oneᵢ (there x∈) | here ()
∀νctx-no-var-target-one-oneᵢ (there x∈) | there y∈ =
  no-⇑ᴸᵢ-zero-left y∈

∀ctx-id0-no-var-target-one-oneᵢ :
  NoVarTargetAtᵢ
    (suc zero)
    (suc zero)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (idᵢ zero))
∀ctx-id0-no-var-target-one-oneᵢ (here ())
∀ctx-id0-no-var-target-one-oneᵢ (there ())

⊑-to-forall-target-var-occurs-false-atᵢ :
  ∀ {Φ Δᴸ Δᴿ C Y} X →
  NoVarTargetAtᵢ (suc X) (suc Y) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  Φ ∣ Δᴸ ⊢ C ⊑ `∀ (＇ (suc Y)) ⊣ Δᴿ →
  occurs X C ≡ false
⊑-to-forall-target-var-occurs-false-atᵢ X noXY (∀ⁱ p) =
  ⊑-to-target-var-occurs-false-atᵢ (suc X) noXY p
⊑-to-forall-target-var-occurs-false-atᵢ X noXY (ν occ p) =
  ⊑-to-forall-target-var-occurs-false-atᵢ
    (suc X)
    (νctx-no-forall-target-sucᵢ noXY)
    p

⊑-to-forall-inner-target-var-occurs-falseᵢ :
  ∀ {Φ Δᴸ Δᴿ C} X →
  Φ ∣ Δᴸ ⊢ C ⊑ `∀ (＇ zero) ⊣ Δᴿ →
  occurs X C ≡ false
⊑-to-forall-inner-target-var-occurs-falseᵢ X (∀ⁱ p) =
  ⊑-to-target-var-occurs-false-atᵢ
    (suc X)
    ∀ctx-no-var-target-suc-zeroᵢ
    p
⊑-to-forall-inner-target-var-occurs-falseᵢ X (ν occ p) =
  ⊑-to-forall-inner-target-var-occurs-falseᵢ (suc X) p

no-common-target-var-forallᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴿ′ A D Y} →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ Y ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ `∀ A ⊣ Δᴿ′)
no-common-target-var-forallᵢ (ν occ p) (∀ⁱ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-target-var-occurs-false-atᵢ
          zero
          νctx-no-var-target-zeroᵢ
          p))
      occ)
no-common-target-var-forallᵢ (ν occ p) (ν occ′ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-target-var-occurs-false-atᵢ
          zero
          νctx-no-var-target-zeroᵢ
          p))
      occ)

no-common-forall-var1-forall-forall-var0-∀νᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (＇ (suc zero)) ⊣ suc Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ `∀ (`∀ (＇ zero)) ⊣ Δᴿ)
no-common-forall-var1-forall-forall-var0-∀νᵢ (∀ⁱ p) (∀ⁱ q) =
  no-common-target-var-forallᵢ p q
no-common-forall-var1-forall-forall-var0-∀νᵢ (∀ⁱ p) (ν occ q) =
  no-common-target-var-forallᵢ p q
no-common-forall-var1-forall-forall-var0-∀νᵢ (ν occ p) (∀ⁱ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-forall-target-var-occurs-false-atᵢ
          zero
          ∀νctx-no-var-target-one-oneᵢ
          p))
      occ)
no-common-forall-var1-forall-forall-var0-∀νᵢ (ν occ p) (ν occ′ q) =
  no-common-forall-var1-forall-forall-var0-∀νᵢ p q

no-common-forall-var1-var0ᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (＇ (suc zero)) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (＇ zero) ⊣ Δᴿ)
no-common-forall-var1-var0ᵢ (∀ⁱ p) (∀ⁱ q) =
  no-common-target-var-by-occursᵢ
    zero
    ∀ctx-no-var-target-zero-sucᵢ
    ∀ctx-only-target-zero-zeroᵢ
    p
    q
no-common-forall-var1-var0ᵢ (∀ⁱ p) (ν occ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-target-var-occurs-false-atᵢ
          zero
          ∀ctx-no-var-target-zero-sucᵢ
          p))
      occ)
no-common-forall-var1-var0ᵢ (ν occ p) (∀ⁱ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-forall-target-var-occurs-false-atᵢ
          zero
          ∀νctx-no-var-target-one-oneᵢ
          p))
      (⊑-to-only-target-var-occurs-trueᵢ
        zero
        ∀ctx-only-target-zero-zeroᵢ
        q))
no-common-forall-var1-var0ᵢ (ν occ p) (ν occ′ q) =
  no-common-forall-var1-var0ᵢ p q

no-common-forall-forall-var1-var0-withᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  NoVarTargetAtᵢ
    (suc zero)
    (suc zero)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (`∀ (＇ (suc zero))) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (`∀ (＇ zero)) ⊣ Δᴿ)
no-common-forall-forall-var1-var0-withᵢ no11 (∀ⁱ p) (∀ⁱ q) =
  no-common-forall-var1-var0ᵢ p q
no-common-forall-forall-var1-var0-withᵢ no11 (∀ⁱ p) (ν occ q) =
  no-common-forall-var1-forall-forall-var0-∀νᵢ p q
no-common-forall-forall-var1-var0-withᵢ no11 (ν occ p) (∀ⁱ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-forall-inner-target-var-occurs-falseᵢ zero q))
      occ)
no-common-forall-forall-var1-var0-withᵢ no11 (ν occ p) (ν occ′ q) =
  no-common-forall-forall-var1-var0-withᵢ
    ∀νctx-no-var-target-one-oneᵢ
    p
    q

no-common-forall-forall-var1-var0ᵢ :
  ∀ {D} →
  idᵢ zero ∣ zero ⊢ D ⊑ `∀ (`∀ (＇ (suc zero))) ⊣ zero →
  ¬ (idᵢ zero ∣ zero ⊢ D ⊑ `∀ (`∀ (＇ zero)) ⊣ zero)
no-common-forall-forall-var1-var0ᵢ =
  no-common-forall-forall-var1-var0-withᵢ
    ∀ctx-id0-no-var-target-one-oneᵢ

no-common-forall-forall-var0-var1ᵢ :
  ∀ {D} →
  idᵢ zero ∣ zero ⊢ D ⊑ `∀ (`∀ (＇ zero)) ⊣ zero →
  ¬ (idᵢ zero ∣ zero ⊢ D ⊑ `∀ (`∀ (＇ (suc zero))) ⊣ zero)
no-common-forall-forall-var0-var1ᵢ p q =
  no-common-forall-forall-var1-var0ᵢ q p

⊑-to-target-var-occurs-falseᵢ :
  ∀ {Φ Δᴸ Δᴿ C X} Y →
  NoVarLeftAtᵢ Y Φ →
  Φ ∣ Δᴸ ⊢ C ⊑ ＇ X ⊣ Δᴿ →
  occurs Y C ≡ false
⊑-to-target-var-occurs-falseᵢ Y noY (idˣ {X = z} x∈ _ _)
    with Y ≟ z
⊑-to-target-var-occurs-falseᵢ Y noY (idˣ {X = .Y} x∈ _ _)
    | yes refl =
  ⊥-elim (noY x∈)
⊑-to-target-var-occurs-falseᵢ Y noY (idˣ {X = z} x∈ _ _)
    | no Y≢z =
  refl
⊑-to-target-var-occurs-falseᵢ Y noY (ν occ p) =
  ⊑-to-target-var-occurs-falseᵢ
    (suc Y)
    (νctx-no-var-left-sucᵢ noY)
    p

⊑-to-arrow-target-vars-occurs-falseᵢ :
  ∀ {Φ Δᴸ Δᴿ C X Y} Z →
  NoVarLeftAtᵢ Z Φ →
  Φ ∣ Δᴸ ⊢ C ⊑ ＇ X ⇒ ＇ Y ⊣ Δᴿ →
  occurs Z C ≡ false
⊑-to-arrow-target-vars-occurs-falseᵢ z noZ (p ↦ q) =
  ∨-falseᵢ
    (⊑-to-target-var-occurs-falseᵢ z noZ p)
    (⊑-to-target-var-occurs-falseᵢ z noZ q)
⊑-to-arrow-target-vars-occurs-falseᵢ z noZ (ν occ p) =
  ⊑-to-arrow-target-vars-occurs-falseᵢ
    (suc z)
    (νctx-no-var-left-sucᵢ noZ)
    p

no-common-target-var0-var0-crossᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  NoTargetZeroZeroCrossᵢ Φ Ψ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⊣ Δᴿ)
no-common-target-var0-var0-crossᵢ no-cross
    (idˣ w⊑0 _ _) (idˣ w⊑0′ _ _) =
  no-cross w⊑0 w⊑0′
no-common-target-var0-var0-crossᵢ no-cross (ν occ p) (ν occ′ q) =
  no-common-target-var0-var0-crossᵢ
    (ννctx-no-target-zero-zero-crossᵢ no-cross)
    p
    q
  where
    ννctx-no-target-zero-zero-crossᵢ :
      ∀ {Φ Ψ} →
      NoTargetZeroZeroCrossᵢ Φ Ψ →
      NoTargetZeroZeroCrossᵢ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
    ννctx-no-target-zero-zero-crossᵢ no-cross (here ()) w⊑0′
    ννctx-no-target-zero-zero-crossᵢ no-cross w⊑0 (here ())
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = zero}
        (there w⊑0) (there w⊑0′) =
      no-⇑ᴸᵢ-zero-left w⊑0
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = suc W}
        (there w⊑0) (there w⊑0′) =
      no-cross (un⇑ᴸᵢ-ˣ∈ w⊑0) (un⇑ᴸᵢ-ˣ∈ w⊑0′)

no-common-target-var0-var0-cross′ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴿ′ D} →
  NoTargetZeroZeroCrossᵢ Φ Ψ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⊣ Δᴿ′)
no-common-target-var0-var0-cross′ᵢ no-cross
    (idˣ w⊑0 _ _) (idˣ w⊑0′ _ _) =
  no-cross w⊑0 w⊑0′
no-common-target-var0-var0-cross′ᵢ no-cross (ν occ p) (ν occ′ q) =
  no-common-target-var0-var0-cross′ᵢ
    (ννctx-no-target-zero-zero-crossᵢ no-cross)
    p
    q
  where
    ννctx-no-target-zero-zero-crossᵢ :
      ∀ {Φ Ψ} →
      NoTargetZeroZeroCrossᵢ Φ Ψ →
      NoTargetZeroZeroCrossᵢ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
    ννctx-no-target-zero-zero-crossᵢ no-cross (here ()) w⊑0′
    ννctx-no-target-zero-zero-crossᵢ no-cross w⊑0 (here ())
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = zero}
        (there w⊑0) (there w⊑0′) =
      no-⇑ᴸᵢ-zero-left w⊑0
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = suc W}
        (there w⊑0) (there w⊑0′) =
      no-cross (un⇑ᴸᵢ-ˣ∈ w⊑0) (un⇑ᴸᵢ-ˣ∈ w⊑0′)

no-common-arrow-domain-target-var0-var0-crossᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ A B D} →
  NoTargetZeroZeroCrossᵢ Φ Ψ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⇒ A ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⇒ B ⊣ Δᴿ)
no-common-arrow-domain-target-var0-var0-crossᵢ no-cross
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-common-target-var0-var0-crossᵢ no-cross p₁ q₁
no-common-arrow-domain-target-var0-var0-crossᵢ no-cross
    (ν occ p) (ν occ′ q) =
  no-common-arrow-domain-target-var0-var0-crossᵢ
    (ννctx-no-target-zero-zero-crossᵢ no-cross)
    p
    q
  where
    ννctx-no-target-zero-zero-crossᵢ :
      ∀ {Φ Ψ} →
      NoTargetZeroZeroCrossᵢ Φ Ψ →
      NoTargetZeroZeroCrossᵢ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
    ννctx-no-target-zero-zero-crossᵢ no-cross (here ()) w⊑0′
    ννctx-no-target-zero-zero-crossᵢ no-cross w⊑0 (here ())
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = zero}
        (there w⊑0) (there w⊑0′) =
      no-⇑ᴸᵢ-zero-left w⊑0
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = suc W}
        (there w⊑0) (there w⊑0′) =
      no-cross (un⇑ᴸᵢ-ˣ∈ w⊑0) (un⇑ᴸᵢ-ˣ∈ w⊑0′)

no-common-arrow-domain-target-var-by-occursᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴿ′ A B D Y Z} X →
  NoVarTargetAtᵢ X Y Φ →
  OnlyTargetAtᵢ X Z Ψ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ Y ⇒ A ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ ＇ Z ⇒ B ⊣ Δᴿ′)
no-common-arrow-domain-target-var-by-occursᵢ X noXY only
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-common-target-var-by-occurs′ᵢ X noXY only p₁ q₁
no-common-arrow-domain-target-var-by-occursᵢ X noXY only
    (ν occ p) (ν occ′ q) =
  no-common-arrow-domain-target-var-by-occursᵢ
    (suc X)
    (νctx-no-var-target-sucᵢ noXY)
    (νctx-only-target-sucᵢ only)
    p
    q

no-common-arrow-codomain-target-var0-var0-crossᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴿ′ A B D} →
  NoTargetZeroZeroCrossᵢ Φ Ψ →
  Φ ∣ Δᴸ ⊢ D ⊑ A ⇒ ＇ zero ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ B ⇒ ＇ zero ⊣ Δᴿ′)
no-common-arrow-codomain-target-var0-var0-crossᵢ no-cross
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-common-target-var0-var0-cross′ᵢ no-cross p₂ q₂
no-common-arrow-codomain-target-var0-var0-crossᵢ no-cross
    (ν occ p) (ν occ′ q) =
  no-common-arrow-codomain-target-var0-var0-crossᵢ
    (ννctx-no-target-zero-zero-crossᵢ no-cross)
    p
    q
  where
    ννctx-no-target-zero-zero-crossᵢ :
      ∀ {Φ Ψ} →
      NoTargetZeroZeroCrossᵢ Φ Ψ →
      NoTargetZeroZeroCrossᵢ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
    ννctx-no-target-zero-zero-crossᵢ no-cross (here ()) w⊑0′
    ννctx-no-target-zero-zero-crossᵢ no-cross w⊑0 (here ())
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = zero}
        (there w⊑0) (there w⊑0′) =
      no-⇑ᴸᵢ-zero-left w⊑0
    ννctx-no-target-zero-zero-crossᵢ no-cross {W = suc W}
        (there w⊑0) (there w⊑0′) =
      no-cross (un⇑ᴸᵢ-ˣ∈ w⊑0) (un⇑ᴸᵢ-ˣ∈ w⊑0′)

no-common-arrow-domain-target-var0-starᵢ :
  ∀ {Φ Δᴸ Δᴿ A B D} →
  NoTargetZeroStarOverlapᵢ Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ ＇ zero ⇒ A ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⇒ B ⊣ Δᴿ)
no-common-arrow-domain-target-var0-starᵢ no-overlap
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-common-target-var0-star-overlapᵢ no-overlap p₁ q₁
no-common-arrow-domain-target-var0-starᵢ no-overlap
    (ν occ p) (ν occ′ q) =
  no-common-arrow-domain-target-var0-starᵢ
    (νctx-no-target-zero-star-overlapᵢ no-overlap)
    p
    q

no-common-arrow-codomain-target-var0-starᵢ :
  ∀ {Φ Δᴸ Δᴿ A B D} →
  NoTargetZeroStarOverlapᵢ Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ A ⇒ ＇ zero ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ B ⇒ ★ ⊣ Δᴿ)
no-common-arrow-codomain-target-var0-starᵢ no-overlap
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  no-common-target-var0-star-overlapᵢ no-overlap p₂ q₂
no-common-arrow-codomain-target-var0-starᵢ no-overlap
    (ν occ p) (ν occ′ q) =
  no-common-arrow-codomain-target-var0-starᵢ
    (νctx-no-target-zero-star-overlapᵢ no-overlap)
    p
    q

no-common-forall-arrow-var-var-star-star-body-∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢
    D ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc Δᴿ →
  ¬
    (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢
      D ⊑ (★ ⇒ ★) ⊣ suc Δᴿ)
no-common-forall-arrow-var-var-star-star-body-∀∀ᵢ =
  no-common-arrow-domain-target-var0-starᵢ
    ∀ctx-no-target-zero-star-overlapᵢ

no-common-arrow-var-var-forall-star-star-∀νᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ `∀ (★ ⇒ ★) ⊣ Δᴿ)
no-common-arrow-var-var-forall-star-star-∀νᵢ
    (ν occ p) (∀ⁱ q) =
  false≠trueᵢ
    (trans
      (sym
        (⊑-to-arrow-target-vars-occurs-falseᵢ
          zero
          νctx-no-var-left-zeroᵢ
          p))
      occ)
no-common-arrow-var-var-forall-star-star-∀νᵢ
    (ν occ p) (ν occ′ q) =
  no-common-arrow-var-var-forall-star-star-∀νᵢ p q

common-forall-var-var-arrow-star-star-freshᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} X →
  NoVarLeftAtᵢ X Φ →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ →
  Ψ ∣ Δᴸ ⊢ D ⊑ (★ ⇒ ★) ⊣ suc Δᴿ →
  occurs X D ≡ false
common-forall-var-var-arrow-star-star-freshᵢ X noX (∀ⁱ p) (ν occ q) =
  ⊑-to-arrow-target-vars-occurs-falseᵢ
    (suc X)
    (∀ctx-no-var-left-sucᵢ noX)
    p
common-forall-var-var-arrow-star-star-freshᵢ X noX
    (ν occ p) (ν occ′ q) =
  common-forall-var-var-arrow-star-star-freshᵢ
    (suc X)
    (νctx-no-var-left-sucᵢ noX)
    p
    q

no-common-forall-arrow-var-var-var-star-body-∀∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢
    D ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc Δᴿ →
  ¬
    (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ⊢
      D ⊑ (＇ zero ⇒ ★) ⊣ suc Δᴿ)
no-common-forall-arrow-var-var-var-star-body-∀∀ᵢ =
  no-common-arrow-codomain-target-var0-starᵢ
    ∀ctx-no-target-zero-star-overlapᵢ

no-common-arrow-var-var-forall-var-star-∀νᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ ★) ⊣ Δᴿ)
no-common-arrow-var-var-forall-var-star-∀νᵢ
    (ν occ p) (∀ⁱ q) =
  no-common-arrow-domain-target-var0-var0-crossᵢ
    (target-zero-cross-fromᵢ
      νctx-no-target-zero-at-zeroᵢ
      ∀ctx-only-target-zero-at-zeroᵢ)
    p
    q
no-common-arrow-var-var-forall-var-star-∀νᵢ
    (ν occ p) (ν occ′ q) =
  no-common-arrow-var-var-forall-var-star-∀νᵢ p q

no-common-forall-var-var-arrow-var-star-ν∀ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ (＇ zero ⇒ ★) ⊣ suc Δᴿ)
no-common-forall-var-var-arrow-var-star-ν∀ᵢ
    (∀ⁱ p) (ν occ q) =
  no-common-arrow-domain-target-var0-var0-crossᵢ
    (target-zero-cross-from-rightᵢ
      ∀ctx-only-target-zero-at-zeroᵢ
      νctx-no-target-zero-at-zeroᵢ)
    p
    q
no-common-forall-var-var-arrow-var-star-ν∀ᵢ
    (ν occ p) (ν occ′ q) =
  no-common-forall-var-var-arrow-var-star-ν∀ᵢ p q

no-common-forall-arrow-var-var-var-starᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ ★) ⊣ Δᴿ)
no-common-forall-arrow-var-var-var-starᵢ (∀ⁱ p) (∀ⁱ q) =
  no-common-forall-arrow-var-var-var-star-body-∀∀ᵢ p q
no-common-forall-arrow-var-var-var-starᵢ (∀ⁱ p) (ν occ q) =
  no-common-arrow-var-var-forall-var-star-∀νᵢ p q
no-common-forall-arrow-var-var-var-starᵢ (ν occ p) (∀ⁱ q) =
  no-common-forall-var-var-arrow-var-star-ν∀ᵢ p q
no-common-forall-arrow-var-var-var-starᵢ (ν occ p) (ν occ′ q) =
  no-common-forall-arrow-var-var-var-starᵢ p q

no-common-forall-arrow-var-star-var-varᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ ★) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ)
no-common-forall-arrow-var-star-var-varᵢ p q =
  no-common-forall-arrow-var-var-var-starᵢ q p

no-common-forall-arrow-var-var-star-starᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (★ ⇒ ★) ⊣ Δᴿ)
no-common-forall-arrow-var-var-star-starᵢ (∀ⁱ p) (∀ⁱ q) =
  no-common-forall-arrow-var-var-star-star-body-∀∀ᵢ p q
no-common-forall-arrow-var-var-star-starᵢ (∀ⁱ p) (ν occ q) =
  no-common-arrow-var-var-forall-star-star-∀νᵢ p q
no-common-forall-arrow-var-var-star-starᵢ (ν occ p) (∀ⁱ q) =
  false≠trueᵢ
    (trans
      (sym
        (common-forall-var-var-arrow-star-star-freshᵢ
          zero
          νctx-no-var-left-zeroᵢ
          p
          q))
      occ)
no-common-forall-arrow-var-var-star-starᵢ (ν occ p) (ν occ′ q) =
  no-common-forall-arrow-var-var-star-starᵢ p q

no-common-forall-arrow-star-star-var-varᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (★ ⇒ ★) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ)
no-common-forall-arrow-star-star-var-varᵢ p q =
  no-common-forall-arrow-var-var-star-starᵢ q p

no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ (suc zero)) ⇒ (＇ zero)) ⊣ suc Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc Δᴿ)
no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ
    (∀ⁱ p) (ν occ q) =
  no-common-arrow-codomain-target-var0-var0-crossᵢ
    (target-zero-cross-from-rightᵢ
      ∀ctx-only-target-zero-at-zeroᵢ
      νctx-no-target-zero-at-zeroᵢ)
    p
    q
no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ
    (ν occ p) (ν occ′ q) =
  no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ p q

no-common-arrow-var1-var0-forall-arrow-var0-var0ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Δᴿ′ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ (＇ (suc zero) ⇒ ＇ zero) ⊣ Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ′)
no-common-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (ν occ p) (∀ⁱ q) =
  no-common-arrow-domain-target-var-by-occursᵢ
    zero
    νctx-no-var-target-zeroᵢ
    ∀ctx-only-target-zero-zeroᵢ
    p
    q
no-common-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (ν occ p) (ν occ′ q) =
  no-common-arrow-var1-var0-forall-arrow-var0-var0ᵢ p q

no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ (suc zero)) ⇒ (＇ zero)) ⊣ suc Δᴿ →
  ¬ (Ψ ∣ Δᴸ ⊢ D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ Δᴿ)
no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (∀ⁱ p) (∀ⁱ q) =
  no-common-arrow-domain-target-var-by-occursᵢ
    zero
    ∀ctx-no-var-target-zero-sucᵢ
    ∀ctx-only-target-zero-zeroᵢ
    p
    q
no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (∀ⁱ p) (ν occ q) =
  no-common-arrow-var1-var0-forall-arrow-var0-var0ᵢ p q
no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (ν occ p) (∀ⁱ q) =
  no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ p q
no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (ν occ p) (ν occ′ q) =
  no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ p q

no-common-forall-forall-arrow-var1-var0-arrow-var0-var0ᵢ :
  ∀ {Φ Ψ Δᴸ D} →
  Φ ∣ Δᴸ ⊢
    D ⊑ `∀ (`∀ ((＇ (suc zero)) ⇒ (＇ zero))) ⊣ zero →
  ¬
    (Ψ ∣ Δᴸ ⊢
      D ⊑ (＇ zero ⇒ ＇ zero) ⊣ suc zero)
no-common-forall-forall-arrow-var1-var0-arrow-var0-var0ᵢ
    (∀ⁱ p) (ν occ q) =
  no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ p q
no-common-forall-forall-arrow-var1-var0-arrow-var0-var0ᵢ
    (ν occ p) (ν occ′ q) =
  no-common-forall-forall-arrow-var1-var0-arrow-var0-var0ᵢ p q

no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ :
  ∀ {Φ Δᴸ D} →
  Φ ∣ Δᴸ ⊢
    D ⊑ `∀ (`∀ ((＇ (suc zero)) ⇒ (＇ zero))) ⊣ zero →
  ¬
    (Φ ∣ Δᴸ ⊢
      D ⊑ `∀ ((＇ zero) ⇒ (＇ zero)) ⊣ zero)
no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (∀ⁱ p) (∀ⁱ q) =
  no-common-forall-arrow-var1-var0-arrow-var0-var0ᵢ p q
no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (∀ⁱ p) (ν occ q) =
  no-common-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ p q
no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (ν occ p) (∀ⁱ q) =
  no-common-forall-forall-arrow-var1-var0-arrow-var0-var0ᵢ p q
no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
    (ν occ p) (ν occ′ q) =
  no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ p q

endpoint-failure-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ :
  EndpointMlbFailureᵢ
    0
    (`∀ (`∀ ((＇ (suc zero)) ⇒ (＇ zero))))
    (`∀ ((＇ zero) ⇒ (＇ zero)))
endpoint-failure-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {D} →
      ¬
        CommonLowerBoundᵢ
          0
          (`∀ (`∀ ((＇ (suc zero)) ⇒ (＇ zero))))
          (`∀ ((＇ zero) ⇒ (＇ zero)))
          D
    no-common (p , q) =
      no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
        p
        q

endpoint-failure-forall-arrow-var0-var0-forall-forall-arrow-var1-var0ᵢ :
  EndpointMlbFailureᵢ
    0
    (`∀ ((＇ zero) ⇒ (＇ zero)))
    (`∀ (`∀ ((＇ (suc zero)) ⇒ (＇ zero))))
endpoint-failure-forall-arrow-var0-var0-forall-forall-arrow-var1-var0ᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {D} →
      ¬
        CommonLowerBoundᵢ
          0
          (`∀ ((＇ zero) ⇒ (＇ zero)))
          (`∀ (`∀ ((＇ (suc zero)) ⇒ (＇ zero))))
          D
    no-common (p , q) =
      no-common-forall-forall-arrow-var1-var0-forall-arrow-var0-var0ᵢ
        q
        p

endpoint-failure-var-starᵢ :
  ∀ {Δ X} →
  EndpointMlbFailureᵢ Δ (＇ X) ★
endpoint-failure-var-starᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ X D} →
      ¬ CommonLowerBoundᵢ Δ (＇ X) ★ D
    no-common {Δ = Δ} (p , q) =
      no-common-var-star-overlapᵢ (id-no-var-star-overlapᵢ Δ) p q

endpoint-failure-star-varᵢ :
  ∀ {Δ X} →
  EndpointMlbFailureᵢ Δ ★ (＇ X)
endpoint-failure-star-varᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ X D} →
      ¬ CommonLowerBoundᵢ Δ ★ (＇ X) D
    no-common {Δ = Δ} (p , q) =
      no-common-star-var-overlapᵢ (id-no-var-star-overlapᵢ Δ) p q

NoStarAtᵢ : TyVar → ImpCtx → Set
NoStarAtᵢ X Φ = (X ˣ⊑★) ∈ Φ → ⊥

∀ctx-no-star-zeroᵢ :
  ∀ {Φ} →
  NoStarAtᵢ zero ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ctx-no-star-zeroᵢ (here ())
∀ctx-no-star-zeroᵢ (there x★∈) = no-⇑ᵢ-zero-star x★∈

νctx-no-star-sucᵢ :
  ∀ {Φ X} →
  NoStarAtᵢ X Φ →
  NoStarAtᵢ (suc X) ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
νctx-no-star-sucᵢ no-star (here ())
νctx-no-star-sucᵢ no-star (there x★∈) =
  no-star (un⇑ᴸᵢ-★∈ x★∈)

⊑★-freshᵢ :
  ∀ {Φ Δᴸ Δᴿ A X} →
  NoStarAtᵢ X Φ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  occurs X A ≡ false
⊑★-freshᵢ no-star id★ = refl
⊑★-freshᵢ no-star (tag ι) = refl
⊑★-freshᵢ no-star (tag p ⇛ q) =
  ∨-falseᵢ (⊑★-freshᵢ no-star p) (⊑★-freshᵢ no-star q)
⊑★-freshᵢ {X = X} no-star (tagˣ {X = Y} y★∈ _) with X ≟ Y
⊑★-freshᵢ {X = X} no-star (tagˣ {X = .X} y★∈ _) | yes refl =
  ⊥-elim (no-star y★∈)
⊑★-freshᵢ {X = X} no-star (tagˣ {X = Y} y★∈ _) | no X≢Y = refl
⊑★-freshᵢ no-star (ν occ p) =
  ⊑★-freshᵢ (νctx-no-star-sucᵢ no-star) p

⊑-to-base-occurs-falseᵢ :
  ∀ {Φ Δᴸ Δᴿ C ι} X →
  Φ ∣ Δᴸ ⊢ C ⊑ ‵ ι ⊣ Δᴿ →
  occurs X C ≡ false
⊑-to-base-occurs-falseᵢ X idι = refl
⊑-to-base-occurs-falseᵢ X (ν occ p) =
  ⊑-to-base-occurs-falseᵢ (suc X) p

⊑-to-base-arrow-occurs-falseᵢ :
  ∀ {Φ Δᴸ Δᴿ C ι κ} X →
  Φ ∣ Δᴸ ⊢ C ⊑ (‵ ι ⇒ ‵ κ) ⊣ Δᴿ →
  occurs X C ≡ false
⊑-to-base-arrow-occurs-falseᵢ X (p ↦ q) =
  ∨-falseᵢ
    (⊑-to-base-occurs-falseᵢ X p)
    (⊑-to-base-occurs-falseᵢ X q)
⊑-to-base-arrow-occurs-falseᵢ X (ν occ p) =
  ⊑-to-base-arrow-occurs-falseᵢ (suc X) p

no-common-forall-fresh-target-starᵢ :
  ∀ {Φ Δᴸ Δᴿ A D} →
  (∀ {Ψ Δᴸ′ Δᴿ′ E} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ) ∣ suc Δᴸ′ ⊢ E ⊑ A ⊣ suc Δᴿ′ →
    occurs zero E ≡ false) →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ A ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-forall-fresh-target-starᵢ fresh (∀ⁱ p) (ν occ q) =
  false≠trueᵢ (trans (sym (fresh p)) occ)
no-common-forall-fresh-target-starᵢ fresh (ν occ p) (ν occ′ q) =
  no-common-forall-fresh-target-starᵢ fresh p q

no-common-star-forall-fresh-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A D} →
  (∀ {Ψ Δᴸ′ Δᴿ′ E} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ) ∣ suc Δᴸ′ ⊢ E ⊑ A ⊣ suc Δᴿ′ →
    occurs zero E ≡ false) →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ A ⊣ Δᴿ)
no-common-star-forall-fresh-targetᵢ fresh p q =
  no-common-forall-fresh-target-starᵢ fresh q p

no-common-forall-star-starᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-forall-star-starᵢ =
  no-common-forall-fresh-target-starᵢ
    (λ p → ⊑★-freshᵢ ∀ctx-no-star-zeroᵢ p)

no-common-star-forall-starᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ ★ ⊣ Δᴿ)
no-common-star-forall-starᵢ =
  no-common-star-forall-fresh-targetᵢ
    (λ p → ⊑★-freshᵢ ∀ctx-no-star-zeroᵢ p)

no-common-forall-base-starᵢ :
  ∀ {Φ Δᴸ Δᴿ D ι} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ ι) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-forall-base-starᵢ =
  no-common-forall-fresh-target-starᵢ
    (λ p → ⊑-to-base-occurs-falseᵢ zero p)

no-common-star-forall-baseᵢ :
  ∀ {Φ Δᴸ Δᴿ D ι} →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ ι) ⊣ Δᴿ)
no-common-star-forall-baseᵢ =
  no-common-star-forall-fresh-targetᵢ
    (λ p → ⊑-to-base-occurs-falseᵢ zero p)

no-common-forall-base-mismatch-ℕ𝔹ᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ `ℕ) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ `𝔹) ⊣ Δᴿ)
no-common-forall-base-mismatch-ℕ𝔹ᵢ (∀ⁱ p) (∀ⁱ q) =
  no-common-ℕ-𝔹ᵢ p q
no-common-forall-base-mismatch-ℕ𝔹ᵢ (∀ⁱ p) (ν occ q) =
  false≠trueᵢ (trans (sym (⊑-to-base-occurs-falseᵢ zero p)) occ)
no-common-forall-base-mismatch-ℕ𝔹ᵢ (ν occ p) (∀ⁱ q) =
  false≠trueᵢ (trans (sym (⊑-to-base-occurs-falseᵢ zero q)) occ)
no-common-forall-base-mismatch-ℕ𝔹ᵢ (ν occ p) (ν occ′ q) =
  no-common-forall-base-mismatch-ℕ𝔹ᵢ p q

no-common-forall-base-mismatch-𝔹ℕᵢ :
  ∀ {Φ Δᴸ Δᴿ D} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ `𝔹) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ `ℕ) ⊣ Δᴿ)
no-common-forall-base-mismatch-𝔹ℕᵢ p q =
  no-common-forall-base-mismatch-ℕ𝔹ᵢ q p

no-common-forall-base-arrow-starᵢ :
  ∀ {Φ Δᴸ Δᴿ D ι κ} →
  Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ ι ⇒ ‵ κ) ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ)
no-common-forall-base-arrow-starᵢ =
  no-common-forall-fresh-target-starᵢ
    (λ p → ⊑-to-base-arrow-occurs-falseᵢ zero p)

no-common-star-forall-base-arrowᵢ :
  ∀ {Φ Δᴸ Δᴿ D ι κ} →
  Φ ∣ Δᴸ ⊢ D ⊑ ★ ⊣ Δᴿ →
  ¬ (Φ ∣ Δᴸ ⊢ D ⊑ `∀ (‵ ι ⇒ ‵ κ) ⊣ Δᴿ)
no-common-star-forall-base-arrowᵢ p q =
  no-common-star-forall-fresh-targetᵢ
    (λ r → ⊑-to-base-arrow-occurs-falseᵢ zero r)
    p
    q

endpoint-failure-forall-fresh-target-starᵢ :
  ∀ {Δ A} →
  endpointMlb (`∀ A) ★ ≡ nothing →
  (∀ {Ψ Δᴸ Δᴿ E} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ) ∣ suc Δᴸ ⊢ E ⊑ A ⊣ suc Δᴿ →
    occurs zero E ≡ false) →
  EndpointMlbFailureᵢ Δ (`∀ A) ★
endpoint-failure-forall-fresh-target-starᵢ {Δ = Δ} {A = A} eq fresh =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {D} →
      ¬ CommonLowerBoundᵢ Δ (`∀ A) ★ D
    no-common (p , q) =
      no-common-forall-fresh-target-starᵢ fresh p q

endpoint-failure-star-forall-fresh-targetᵢ :
  ∀ {Δ A} →
  endpointMlb ★ (`∀ A) ≡ nothing →
  (∀ {Ψ Δᴸ Δᴿ E} →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ) ∣ suc Δᴸ ⊢ E ⊑ A ⊣ suc Δᴿ →
    occurs zero E ≡ false) →
  EndpointMlbFailureᵢ Δ ★ (`∀ A)
endpoint-failure-star-forall-fresh-targetᵢ {Δ = Δ} {A = A} eq fresh =
  endpoint-failure eq no-common
  where
    no-common :
      ∀ {D} →
      ¬ CommonLowerBoundᵢ Δ ★ (`∀ A) D
    no-common (p , q) =
      no-common-star-forall-fresh-targetᵢ fresh p q

endpoint-failure-forall-star-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (`∀ ★) ★
endpoint-failure-forall-star-starᵢ =
  endpoint-failure-forall-fresh-target-starᵢ
    refl
    (λ p → ⊑★-freshᵢ ∀ctx-no-star-zeroᵢ p)

endpoint-failure-star-forall-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ ★ (`∀ ★)
endpoint-failure-star-forall-starᵢ =
  endpoint-failure-star-forall-fresh-targetᵢ
    refl
    (λ p → ⊑★-freshᵢ ∀ctx-no-star-zeroᵢ p)

endpoint-failure-forall-base-starᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ (`∀ (‵ ι)) ★
endpoint-failure-forall-base-starᵢ =
  endpoint-failure-forall-fresh-target-starᵢ
    refl
    (λ p → ⊑-to-base-occurs-falseᵢ zero p)

endpoint-failure-star-forall-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ ★ (`∀ (‵ ι))
endpoint-failure-star-forall-baseᵢ =
  endpoint-failure-star-forall-fresh-targetᵢ
    refl
    (λ p → ⊑-to-base-occurs-falseᵢ zero p)

endpoint-failure-forall-base-mismatch-ℕ𝔹ᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (`∀ (‵ `ℕ)) (`∀ (‵ `𝔹))
endpoint-failure-forall-base-mismatch-ℕ𝔹ᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (`∀ (‵ `ℕ)) (`∀ (‵ `𝔹)) D
    no-common (p , q) = no-common-forall-base-mismatch-ℕ𝔹ᵢ p q

endpoint-failure-forall-base-mismatch-𝔹ℕᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (`∀ (‵ `𝔹)) (`∀ (‵ `ℕ))
endpoint-failure-forall-base-mismatch-𝔹ℕᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ Δ (`∀ (‵ `𝔹)) (`∀ (‵ `ℕ)) D
    no-common (p , q) = no-common-forall-base-mismatch-𝔹ℕᵢ p q

endpoint-failure-forall-forall-var1-var0ᵢ :
  EndpointMlbFailureᵢ
    zero
    (`∀ (`∀ (＇ (suc zero))))
    (`∀ (`∀ (＇ zero)))
endpoint-failure-forall-forall-var1-var0ᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {D} →
      ¬ CommonLowerBoundᵢ
        zero
        (`∀ (`∀ (＇ (suc zero))))
        (`∀ (`∀ (＇ zero)))
        D
    no-common (p , q) = no-common-forall-forall-var1-var0ᵢ p q

endpoint-failure-forall-forall-var0-var1ᵢ :
  EndpointMlbFailureᵢ
    zero
    (`∀ (`∀ (＇ zero)))
    (`∀ (`∀ (＇ (suc zero))))
endpoint-failure-forall-forall-var0-var1ᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {D} →
      ¬ CommonLowerBoundᵢ
        zero
        (`∀ (`∀ (＇ zero)))
        (`∀ (`∀ (＇ (suc zero))))
        D
    no-common (p , q) = no-common-forall-forall-var0-var1ᵢ p q

endpoint-failure-forall-arrow-var-var-var-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ
    Δ
    (`∀ ((＇ zero) ⇒ (＇ zero)))
    (`∀ ((＇ zero) ⇒ ★))
endpoint-failure-forall-arrow-var-var-var-starᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ
        Δ
        (`∀ ((＇ zero) ⇒ (＇ zero)))
        (`∀ ((＇ zero) ⇒ ★))
        D
    no-common (p , q) = no-common-forall-arrow-var-var-var-starᵢ p q

endpoint-failure-forall-arrow-var-star-var-varᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ
    Δ
    (`∀ ((＇ zero) ⇒ ★))
    (`∀ ((＇ zero) ⇒ (＇ zero)))
endpoint-failure-forall-arrow-var-star-var-varᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ
        Δ
        (`∀ ((＇ zero) ⇒ ★))
        (`∀ ((＇ zero) ⇒ (＇ zero)))
        D
    no-common (p , q) = no-common-forall-arrow-var-star-var-varᵢ p q

endpoint-failure-forall-arrow-var-var-star-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ
    Δ
    (`∀ ((＇ zero) ⇒ (＇ zero)))
    (`∀ (★ ⇒ ★))
endpoint-failure-forall-arrow-var-var-star-starᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ
        Δ
        (`∀ ((＇ zero) ⇒ (＇ zero)))
        (`∀ (★ ⇒ ★))
        D
    no-common (p , q) = no-common-forall-arrow-var-var-star-starᵢ p q

endpoint-failure-forall-arrow-star-star-var-varᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ
    Δ
    (`∀ (★ ⇒ ★))
    (`∀ ((＇ zero) ⇒ (＇ zero)))
endpoint-failure-forall-arrow-star-star-var-varᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ D} →
      ¬ CommonLowerBoundᵢ
        Δ
        (`∀ (★ ⇒ ★))
        (`∀ ((＇ zero) ⇒ (＇ zero)))
        D
    no-common (p , q) = no-common-forall-arrow-star-star-var-varᵢ p q

endpoint-failure-forall-base-arrow-starᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ (`∀ (‵ ι ⇒ ‵ κ)) ★
endpoint-failure-forall-base-arrow-starᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ ι κ D} →
      ¬ CommonLowerBoundᵢ Δ (`∀ (‵ ι ⇒ ‵ κ)) ★ D
    no-common (p , q) = no-common-forall-base-arrow-starᵢ p q

endpoint-failure-star-forall-base-arrowᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ ★ (`∀ (‵ ι ⇒ ‵ κ))
endpoint-failure-star-forall-base-arrowᵢ =
  endpoint-failure refl no-common
  where
    no-common :
      ∀ {Δ ι κ D} →
      ¬ CommonLowerBoundᵢ Δ ★ (`∀ (‵ ι ⇒ ‵ κ)) D
    no-common (p , q) = no-common-star-forall-base-arrowᵢ p q

endpoint-failure-arrow-arrow-domain-forall-star-leftᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ ((`∀ ★) ⇒ ★) (★ ⇒ ★)
endpoint-failure-arrow-arrow-domain-forall-star-leftᵢ =
  endpoint-failure-arrow-arrow-domainᵢ no-common-forall-star-starᵢ refl

endpoint-failure-arrow-arrow-domain-forall-star-rightᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ★) ((`∀ ★) ⇒ ★)
endpoint-failure-arrow-arrow-domain-forall-star-rightᵢ =
  endpoint-failure-arrow-arrow-domainᵢ no-common-star-forall-starᵢ refl

endpoint-failure-arrow-arrow-codomain-forall-star-leftᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ (`∀ ★)) (★ ⇒ ★)
endpoint-failure-arrow-arrow-codomain-forall-star-leftᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ no-common-forall-star-starᵢ refl

endpoint-failure-arrow-arrow-codomain-forall-star-rightᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ★) (★ ⇒ (`∀ ★))
endpoint-failure-arrow-arrow-codomain-forall-star-rightᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ no-common-star-forall-starᵢ refl

endpoint-failure-arrow-arrow-domain-forall-base-leftᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ ((`∀ (‵ ι)) ⇒ ★) (★ ⇒ ★)
endpoint-failure-arrow-arrow-domain-forall-base-leftᵢ =
  endpoint-failure-arrow-arrow-domainᵢ no-common-forall-base-starᵢ refl

endpoint-failure-arrow-arrow-domain-forall-base-rightᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ★) ((`∀ (‵ ι)) ⇒ ★)
endpoint-failure-arrow-arrow-domain-forall-base-rightᵢ =
  endpoint-failure-arrow-arrow-domainᵢ no-common-star-forall-baseᵢ refl

endpoint-failure-arrow-arrow-codomain-forall-base-leftᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ (★ ⇒ (`∀ (‵ ι))) (★ ⇒ ★)
endpoint-failure-arrow-arrow-codomain-forall-base-leftᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ no-common-forall-base-starᵢ refl

endpoint-failure-arrow-arrow-codomain-forall-base-rightᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ★) (★ ⇒ (`∀ (‵ ι)))
endpoint-failure-arrow-arrow-codomain-forall-base-rightᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ no-common-star-forall-baseᵢ refl

endpoint-failure-arrow-arrow-domain-forall-base-arrow-leftᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ ((`∀ (‵ ι ⇒ ‵ κ)) ⇒ ★) (★ ⇒ ★)
endpoint-failure-arrow-arrow-domain-forall-base-arrow-leftᵢ =
  endpoint-failure-arrow-arrow-domainᵢ
    no-common-forall-base-arrow-starᵢ
    refl

endpoint-failure-arrow-arrow-domain-forall-base-arrow-rightᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ★) ((`∀ (‵ ι ⇒ ‵ κ)) ⇒ ★)
endpoint-failure-arrow-arrow-domain-forall-base-arrow-rightᵢ =
  endpoint-failure-arrow-arrow-domainᵢ
    no-common-star-forall-base-arrowᵢ
    refl

endpoint-failure-arrow-arrow-codomain-forall-base-arrow-leftᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ (`∀ (‵ ι ⇒ ‵ κ))) (★ ⇒ ★)
endpoint-failure-arrow-arrow-codomain-forall-base-arrow-leftᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ
    no-common-forall-base-arrow-starᵢ
    refl

endpoint-failure-arrow-arrow-codomain-forall-base-arrow-rightᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ ★) (★ ⇒ (`∀ (‵ ι ⇒ ‵ κ)))
endpoint-failure-arrow-arrow-codomain-forall-base-arrow-rightᵢ =
  endpoint-failure-arrow-arrow-codomainᵢ
    no-common-star-forall-base-arrowᵢ
    refl

endpoint-failure-arrow-star-domain-forall-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ ((`∀ ★) ⇒ ★) ★
endpoint-failure-arrow-star-domain-forall-starᵢ =
  endpoint-failure-arrow-star-domainᵢ no-common-forall-star-starᵢ refl

endpoint-failure-arrow-star-codomain-forall-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ (`∀ ★)) ★
endpoint-failure-arrow-star-codomain-forall-starᵢ =
  endpoint-failure-arrow-star-codomainᵢ no-common-forall-star-starᵢ refl

endpoint-failure-star-arrow-domain-forall-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ ★ ((`∀ ★) ⇒ ★)
endpoint-failure-star-arrow-domain-forall-starᵢ =
  endpoint-failure-star-arrow-domainᵢ no-common-star-forall-starᵢ refl

endpoint-failure-star-arrow-codomain-forall-starᵢ :
  ∀ {Δ} →
  EndpointMlbFailureᵢ Δ ★ (★ ⇒ (`∀ ★))
endpoint-failure-star-arrow-codomain-forall-starᵢ =
  endpoint-failure-star-arrow-codomainᵢ no-common-star-forall-starᵢ refl

endpoint-failure-arrow-star-domain-forall-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ ((`∀ (‵ ι)) ⇒ ★) ★
endpoint-failure-arrow-star-domain-forall-baseᵢ =
  endpoint-failure-arrow-star-domainᵢ no-common-forall-base-starᵢ refl

endpoint-failure-arrow-star-codomain-forall-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ (★ ⇒ (`∀ (‵ ι))) ★
endpoint-failure-arrow-star-codomain-forall-baseᵢ =
  endpoint-failure-arrow-star-codomainᵢ no-common-forall-base-starᵢ refl

endpoint-failure-star-arrow-domain-forall-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ ★ ((`∀ (‵ ι)) ⇒ ★)
endpoint-failure-star-arrow-domain-forall-baseᵢ =
  endpoint-failure-star-arrow-domainᵢ no-common-star-forall-baseᵢ refl

endpoint-failure-star-arrow-codomain-forall-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbFailureᵢ Δ ★ (★ ⇒ (`∀ (‵ ι)))
endpoint-failure-star-arrow-codomain-forall-baseᵢ =
  endpoint-failure-star-arrow-codomainᵢ no-common-star-forall-baseᵢ refl

endpoint-failure-arrow-star-domain-forall-base-arrowᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ ((`∀ (‵ ι ⇒ ‵ κ)) ⇒ ★) ★
endpoint-failure-arrow-star-domain-forall-base-arrowᵢ =
  endpoint-failure-arrow-star-domainᵢ
    no-common-forall-base-arrow-starᵢ
    refl

endpoint-failure-arrow-star-codomain-forall-base-arrowᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ (★ ⇒ (`∀ (‵ ι ⇒ ‵ κ))) ★
endpoint-failure-arrow-star-codomain-forall-base-arrowᵢ =
  endpoint-failure-arrow-star-codomainᵢ
    no-common-forall-base-arrow-starᵢ
    refl

endpoint-failure-star-arrow-domain-forall-base-arrowᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ ★ ((`∀ (‵ ι ⇒ ‵ κ)) ⇒ ★)
endpoint-failure-star-arrow-domain-forall-base-arrowᵢ =
  endpoint-failure-star-arrow-domainᵢ
    no-common-star-forall-base-arrowᵢ
    refl

endpoint-failure-star-arrow-codomain-forall-base-arrowᵢ :
  ∀ {Δ ι κ} →
  EndpointMlbFailureᵢ Δ ★ (★ ⇒ (`∀ (‵ ι ⇒ ‵ κ)))
endpoint-failure-star-arrow-codomain-forall-base-arrowᵢ =
  endpoint-failure-star-arrow-codomainᵢ
    no-common-star-forall-base-arrowᵢ
    refl

------------------------------------------------------------------------
-- Comparable-MLB certificates for endpoint results
------------------------------------------------------------------------

record EndpointMlbComparableᵢ (Δ : TyCtx) (A B : Ty) : Set where
  constructor endpoint-comparable
  field
    endpointComparableᵢ : ComparableMaximalLowerBoundᵢ Δ A B
    endpointComparableEqᵢ :
      endpointMlb A B ≡ just (c-lowerᵢ endpointComparableᵢ)

open EndpointMlbComparableᵢ public

endpoint-comparable-commonᵢ :
  ∀ {Δ A B} →
  (certified : EndpointMlbComparableᵢ Δ A B) →
  CommonLowerBoundᵢ Δ A B (c-lowerᵢ (endpointComparableᵢ certified))
endpoint-comparable-commonᵢ certified =
  c-lower-leftᵢ (endpointComparableᵢ certified) ,
  c-lower-rightᵢ (endpointComparableᵢ certified)

endpoint-comparable-sound-targetᵢ :
  ∀ {Δ A B} →
  EndpointMlbComparableᵢ Δ A B →
  EndpointMlbSoundᵢ Δ A B
endpoint-comparable-sound-targetᵢ certified hA hB eq
    rewrite endpointComparableEqᵢ certified
    with eq
endpoint-comparable-sound-targetᵢ certified hA hB eq | refl =
  endpoint-comparable-commonᵢ certified

endpoint-comparable-maximal-targetᵢ :
  ∀ {Δ A B} →
  EndpointMlbComparableᵢ Δ A B →
  EndpointMlbMaximalᵢ Δ A B
endpoint-comparable-maximal-targetᵢ certified hA hB eq common lower⊑D
    rewrite endpointComparableEqᵢ certified
    with eq
endpoint-comparable-maximal-targetᵢ certified hA hB eq common lower⊑D
    | refl =
  c-comparableᵢ (endpointComparableᵢ certified) common lower⊑D

endpoint-comparable-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (left : EndpointMlbComparableᵢ Δᴸ A B) →
  (right : EndpointMlbComparableᵢ Δᴿ A′ B′) →
  MaximalLowerBoundCoherenceᵢ
    (comparable⇒maximalᵢ (endpointComparableᵢ left))
    (comparable⇒maximalᵢ (endpointComparableᵢ right))
    pA
    pB →
  EndpointMlbCoherenceᵢ pA pB
endpoint-comparable-coherence-targetᵢ left right lower-coh eq eq′
    rewrite endpointComparableEqᵢ left
          | endpointComparableEqᵢ right
    with eq | eq′
endpoint-comparable-coherence-targetᵢ left right lower-coh eq eq′
    | refl | refl =
  lower-coh

endpoint-comparable-to-star-star-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ ★ ⊣ Δᴿ} →
  (left : EndpointMlbComparableᵢ Δᴸ A B) →
  Φ ∣ Δᴸ ⊢ c-lowerᵢ (endpointComparableᵢ left) ⊑ ★ ⊣ Δᴿ →
  EndpointMlbCoherenceᵢ pA pB
endpoint-comparable-to-star-star-coherence-targetᵢ left lower⊑★ eq eq′
    rewrite endpointComparableEqᵢ left
    with eq | eq′
endpoint-comparable-to-star-star-coherence-targetᵢ left lower⊑★ eq eq′
    | refl | refl =
  lower⊑★

endpoint-comparable-arrow-arrowᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂} →
  (domain : EndpointMlbComparableᵢ Δ A₁ B₁) →
  (codomain : EndpointMlbComparableᵢ Δ A₂ B₂) →
  endpointMlb (A₁ ⇒ A₂) (B₁ ⇒ B₂) ≡
    just
      (c-lowerᵢ (endpointComparableᵢ domain) ⇒
       c-lowerᵢ (endpointComparableᵢ codomain)) →
  EndpointMlbComparableᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
endpoint-comparable-arrow-arrowᵢ domain codomain eq =
  endpoint-comparable
    (comparable-arrow-arrowᵢ
      (endpointComparableᵢ domain)
      (endpointComparableᵢ codomain))
    eq

endpoint-comparable-arrow-starᵢ :
  ∀ {Δ A₁ A₂} →
  (domain : EndpointMlbComparableᵢ Δ A₁ ★) →
  (codomain : EndpointMlbComparableᵢ Δ A₂ ★) →
  endpointMlb (A₁ ⇒ A₂) ★ ≡
    just
      (c-lowerᵢ (endpointComparableᵢ domain) ⇒
       c-lowerᵢ (endpointComparableᵢ codomain)) →
  EndpointMlbComparableᵢ Δ (A₁ ⇒ A₂) ★
endpoint-comparable-arrow-starᵢ domain codomain eq =
  endpoint-comparable
    (comparable-arrow-starᵢ
      (endpointComparableᵢ domain)
      (endpointComparableᵢ codomain))
    eq

endpoint-comparable-star-arrowᵢ :
  ∀ {Δ B₁ B₂} →
  (domain : EndpointMlbComparableᵢ Δ ★ B₁) →
  (codomain : EndpointMlbComparableᵢ Δ ★ B₂) →
  endpointMlb ★ (B₁ ⇒ B₂) ≡
    just
      (c-lowerᵢ (endpointComparableᵢ domain) ⇒
       c-lowerᵢ (endpointComparableᵢ codomain)) →
  EndpointMlbComparableᵢ Δ ★ (B₁ ⇒ B₂)
endpoint-comparable-star-arrowᵢ domain codomain eq =
  endpoint-comparable
    (comparable-star-arrowᵢ
      (endpointComparableᵢ domain)
      (endpointComparableᵢ codomain))
    eq

endpoint-comparable-forall-forall-from-supportᵢ :
  ∀ {Δ A B} →
  (body : EndpointMlbComparableᵢ (suc Δ) A B) →
  ForallForallComparableSupportᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
    (c-lowerᵢ (endpointComparableᵢ body)) →
  endpointMlb (`∀ A) (`∀ B) ≡
    just (`∀ (c-lowerᵢ (endpointComparableᵢ body))) →
  EndpointMlbComparableᵢ Δ (`∀ A) (`∀ B)
endpoint-comparable-forall-forall-from-supportᵢ body support eq =
  endpoint-comparable
    (comparable-forall-forall-from-supportᵢ
      (endpointComparableᵢ body)
      support)
    eq

endpoint-forall-forall-supported-sound-targetᵢ :
  ∀ {Δ A B} →
  (body : EndpointMlbComparableᵢ (suc Δ) A B) →
  ForallForallComparableSupportᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
    (c-lowerᵢ (endpointComparableᵢ body)) →
  endpointMlb (`∀ A) (`∀ B) ≡
    just (`∀ (c-lowerᵢ (endpointComparableᵢ body))) →
  EndpointMlbSoundᵢ Δ (`∀ A) (`∀ B)
endpoint-forall-forall-supported-sound-targetᵢ body support eq =
  endpoint-comparable-sound-targetᵢ
    (endpoint-comparable-forall-forall-from-supportᵢ body support eq)

endpoint-forall-forall-supported-maximal-targetᵢ :
  ∀ {Δ A B} →
  (body : EndpointMlbComparableᵢ (suc Δ) A B) →
  ForallForallComparableSupportᵢ
    (idᵢ Δ) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B
    (c-lowerᵢ (endpointComparableᵢ body)) →
  endpointMlb (`∀ A) (`∀ B) ≡
    just (`∀ (c-lowerᵢ (endpointComparableᵢ body))) →
  EndpointMlbMaximalᵢ Δ (`∀ A) (`∀ B)
endpoint-forall-forall-supported-maximal-targetᵢ body support eq =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-comparable-forall-forall-from-supportᵢ body support eq)

endpoint-forall-forall-supported-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    {pA : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  (body : EndpointMlbComparableᵢ (suc Δᴸ) A B) →
  (body′ : EndpointMlbComparableᵢ (suc Δᴿ) A′ B′) →
  (support :
    ForallForallComparableSupportᵢ
      (idᵢ Δᴸ) (idᵢ Δᴸ) (idᵢ Δᴸ) Δᴸ Δᴸ Δᴸ A B
      (c-lowerᵢ (endpointComparableᵢ body))) →
  (support′ :
    ForallForallComparableSupportᵢ
      (idᵢ Δᴿ) (idᵢ Δᴿ) (idᵢ Δᴿ) Δᴿ Δᴿ Δᴿ A′ B′
      (c-lowerᵢ (endpointComparableᵢ body′))) →
  endpointMlb (`∀ A) (`∀ B) ≡
    just (`∀ (c-lowerᵢ (endpointComparableᵢ body))) →
  endpointMlb (`∀ A′) (`∀ B′) ≡
    just (`∀ (c-lowerᵢ (endpointComparableᵢ body′))) →
  MaximalLowerBoundCoherenceᵢ
    (comparable⇒maximalᵢ
      (comparable-forall-forall-from-supportᵢ
        (endpointComparableᵢ body)
        support))
    (comparable⇒maximalᵢ
      (comparable-forall-forall-from-supportᵢ
        (endpointComparableᵢ body′)
        support′))
    (∀ⁱ pA)
    (∀ⁱ pB) →
  EndpointMlbCoherenceᵢ (∀ⁱ pA) (∀ⁱ pB)
endpoint-forall-forall-supported-coherence-targetᵢ
    {pA = pA} {pB = pB}
    body body′ support support′ eq eq′ lower-coh =
  endpoint-comparable-coherence-targetᵢ
    {pA = ∀ⁱ pA}
    {pB = ∀ⁱ pB}
    (endpoint-comparable-forall-forall-from-supportᵢ body support eq)
    (endpoint-comparable-forall-forall-from-supportᵢ body′ support′ eq′)
    lower-coh

endpoint-arrow-arrow-sound-targetᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂ C₁ C₂} →
  EndpointMlbSoundᵢ Δ A₁ B₁ →
  EndpointMlbSoundᵢ Δ A₂ B₂ →
  endpointMlb A₁ B₁ ≡ just C₁ →
  endpointMlb A₂ B₂ ≡ just C₂ →
  endpointMlb (A₁ ⇒ A₂) (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  EndpointMlbSoundᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
endpoint-arrow-arrow-sound-targetᵢ s₁ s₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
    rewrite eqArr
    with eq
endpoint-arrow-arrow-sound-targetᵢ s₁ s₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq | refl =
  proj₁ c₁ ↦ proj₁ c₂ , proj₂ c₁ ↦ proj₂ c₂
  where
    c₁ = s₁ hA₁ hB₁ eq₁
    c₂ = s₂ hA₂ hB₂ eq₂

endpoint-arrow-star-sound-targetᵢ :
  ∀ {Δ A₁ A₂ C₁ C₂} →
  EndpointMlbSoundᵢ Δ A₁ ★ →
  EndpointMlbSoundᵢ Δ A₂ ★ →
  endpointMlb A₁ ★ ≡ just C₁ →
  endpointMlb A₂ ★ ≡ just C₂ →
  endpointMlb (A₁ ⇒ A₂) ★ ≡ just (C₁ ⇒ C₂) →
  EndpointMlbSoundᵢ Δ (A₁ ⇒ A₂) ★
endpoint-arrow-star-sound-targetᵢ s₁ s₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) wf★ eq
    rewrite eqArr
    with eq
endpoint-arrow-star-sound-targetᵢ s₁ s₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) wf★ eq | refl =
  proj₁ c₁ ↦ proj₁ c₂ , tag proj₂ c₁ ⇛ proj₂ c₂
  where
    c₁ = s₁ hA₁ wf★ eq₁
    c₂ = s₂ hA₂ wf★ eq₂

endpoint-star-arrow-sound-targetᵢ :
  ∀ {Δ B₁ B₂ C₁ C₂} →
  EndpointMlbSoundᵢ Δ ★ B₁ →
  EndpointMlbSoundᵢ Δ ★ B₂ →
  endpointMlb ★ B₁ ≡ just C₁ →
  endpointMlb ★ B₂ ≡ just C₂ →
  endpointMlb ★ (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  EndpointMlbSoundᵢ Δ ★ (B₁ ⇒ B₂)
endpoint-star-arrow-sound-targetᵢ s₁ s₂ eq₁ eq₂ eqArr
    wf★ (wf⇒ hB₁ hB₂) eq
    rewrite eqArr
    with eq
endpoint-star-arrow-sound-targetᵢ s₁ s₂ eq₁ eq₂ eqArr
    wf★ (wf⇒ hB₁ hB₂) eq | refl =
  tag proj₁ c₁ ⇛ proj₁ c₂ , proj₂ c₁ ↦ proj₂ c₂
  where
    c₁ = s₁ wf★ hB₁ eq₁
    c₂ = s₂ wf★ hB₂ eq₂

endpoint-arrow-arrow-maximal-targetᵢ :
  ∀ {Δ A₁ A₂ B₁ B₂ C₁ C₂} →
  EndpointMlbMaximalᵢ Δ A₁ B₁ →
  EndpointMlbMaximalᵢ Δ A₂ B₂ →
  endpointMlb A₁ B₁ ≡ just C₁ →
  endpointMlb A₂ B₂ ≡ just C₂ →
  endpointMlb (A₁ ⇒ A₂) (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  EndpointMlbMaximalᵢ Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
endpoint-arrow-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
    common lower⊑D
    rewrite eqArr
    with eq
endpoint-arrow-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
    common lower⊑D | refl
    with common | lower⊑D
endpoint-arrow-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
    common lower⊑D | refl
    | ((D₁⊑A₁ ↦ D₂⊑A₂) , (D₁⊑B₁ ↦ D₂⊑B₂))
    | (C₁⊑D₁ ↦ C₂⊑D₂) =
  m₁ hA₁ hB₁ eq₁ (D₁⊑A₁ , D₁⊑B₁) C₁⊑D₁ ↦
  m₂ hA₂ hB₂ eq₂ (D₂⊑A₂ , D₂⊑B₂) C₂⊑D₂
endpoint-arrow-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂) eq
    common lower⊑D | refl
    | (() , _) | (tag C₁⊑★ ⇛ C₂⊑★)

endpoint-arrow-star-maximal-targetᵢ :
  ∀ {Δ A₁ A₂ C₁ C₂} →
  EndpointMlbMaximalᵢ Δ A₁ ★ →
  EndpointMlbMaximalᵢ Δ A₂ ★ →
  endpointMlb A₁ ★ ≡ just C₁ →
  endpointMlb A₂ ★ ≡ just C₂ →
  endpointMlb (A₁ ⇒ A₂) ★ ≡ just (C₁ ⇒ C₂) →
  EndpointMlbMaximalᵢ Δ (A₁ ⇒ A₂) ★
endpoint-arrow-star-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) wf★ eq
    common lower⊑D
    rewrite eqArr
    with eq
endpoint-arrow-star-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) wf★ eq
    common lower⊑D | refl
    with common | lower⊑D
endpoint-arrow-star-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) wf★ eq
    common lower⊑D | refl
    | ((D₁⊑A₁ ↦ D₂⊑A₂) , (tag D₁⊑★ ⇛ D₂⊑★))
    | (C₁⊑D₁ ↦ C₂⊑D₂) =
  m₁ hA₁ wf★ eq₁ (D₁⊑A₁ , D₁⊑★) C₁⊑D₁ ↦
  m₂ hA₂ wf★ eq₂ (D₂⊑A₂ , D₂⊑★) C₂⊑D₂
endpoint-arrow-star-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    (wf⇒ hA₁ hA₂) wf★ eq
    common lower⊑D | refl
    | (() , _) | (tag C₁⊑★ ⇛ C₂⊑★)

endpoint-star-arrow-maximal-targetᵢ :
  ∀ {Δ B₁ B₂ C₁ C₂} →
  EndpointMlbMaximalᵢ Δ ★ B₁ →
  EndpointMlbMaximalᵢ Δ ★ B₂ →
  endpointMlb ★ B₁ ≡ just C₁ →
  endpointMlb ★ B₂ ≡ just C₂ →
  endpointMlb ★ (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  EndpointMlbMaximalᵢ Δ ★ (B₁ ⇒ B₂)
endpoint-star-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    wf★ (wf⇒ hB₁ hB₂) eq
    common lower⊑D
    rewrite eqArr
    with eq
endpoint-star-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    wf★ (wf⇒ hB₁ hB₂) eq
    common lower⊑D | refl
    with common | lower⊑D
endpoint-star-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    wf★ (wf⇒ hB₁ hB₂) eq
    common lower⊑D | refl
    | ((tag D₁⊑★ ⇛ D₂⊑★) , (D₁⊑B₁ ↦ D₂⊑B₂))
    | (C₁⊑D₁ ↦ C₂⊑D₂) =
  m₁ wf★ hB₁ eq₁ (D₁⊑★ , D₁⊑B₁) C₁⊑D₁ ↦
  m₂ wf★ hB₂ eq₂ (D₂⊑★ , D₂⊑B₂) C₂⊑D₂
endpoint-star-arrow-maximal-targetᵢ m₁ m₂ eq₁ eq₂ eqArr
    wf★ (wf⇒ hB₁ hB₂) eq
    common lower⊑D | refl
    | (_ , ()) | (tag C₁⊑★ ⇛ C₂⊑★)

endpoint-forall-forall-sound-targetᵢ :
  ∀ {Δ A B C} →
  EndpointMlbSoundᵢ (suc Δ) A B →
  endpointMlb A B ≡ just C →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  EndpointMlbSoundᵢ Δ (`∀ A) (`∀ B)
endpoint-forall-forall-sound-targetᵢ s eqBody eqForall
    (wf∀ hA) (wf∀ hB) eq
    rewrite eqForall
    with eq
endpoint-forall-forall-sound-targetᵢ s eqBody eqForall
    (wf∀ hA) (wf∀ hB) eq | refl =
  ∀ⁱ (proj₁ body-common) , ∀ⁱ (proj₂ body-common)
  where
    body-common = s hA hB eqBody

endpoint-forall-forall-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  endpointMlb A B ≡ just C →
  endpointMlb A′ B′ ≡ just C′ →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  endpointMlb (`∀ A′) (`∀ B′) ≡ just (`∀ C′) →
  EndpointMlbCoherenceᵢ pA pB →
  EndpointMlbCoherenceᵢ (∀ⁱ pA) (∀ⁱ pB)
endpoint-forall-forall-coherence-targetᵢ
    eqBody eqBody′ eqForall eqForall′ coh eq eq′
    rewrite eqForall | eqForall′
    with eq | eq′
endpoint-forall-forall-coherence-targetᵢ
    eqBody eqBody′ eqForall eqForall′ coh eq eq′
    | refl | refl =
  ∀ⁱ (coh eqBody eqBody′)

endpoint-arrow-arrow-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A₁ A₁′ A₂ A₂′ B₁ B₁′ B₂ B₂′ C₁ C₁′ C₂ C₂′}
    {pA₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ A₁′ ⊣ Δᴿ}
    {pA₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ A₂′ ⊣ Δᴿ}
    {pB₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ B₁′ ⊣ Δᴿ}
    {pB₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ B₂′ ⊣ Δᴿ} →
  endpointMlb A₁ B₁ ≡ just C₁ →
  endpointMlb A₁′ B₁′ ≡ just C₁′ →
  endpointMlb A₂ B₂ ≡ just C₂ →
  endpointMlb A₂′ B₂′ ≡ just C₂′ →
  endpointMlb (A₁ ⇒ A₂) (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  endpointMlb (A₁′ ⇒ A₂′) (B₁′ ⇒ B₂′) ≡ just (C₁′ ⇒ C₂′) →
  EndpointMlbCoherenceᵢ pA₁ pB₁ →
  EndpointMlbCoherenceᵢ pA₂ pB₂ →
  EndpointMlbCoherenceᵢ (pA₁ ↦ pA₂) (pB₁ ↦ pB₂)
endpoint-arrow-arrow-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqArr′ coh₁ coh₂ eq eq′
    rewrite eqArr | eqArr′
    with eq | eq′
endpoint-arrow-arrow-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqArr′ coh₁ coh₂ eq eq′
    | refl | refl =
  coh₁ eq₁ eq₁′ ↦ coh₂ eq₂ eq₂′

endpoint-arrow-star-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A₁ A₁′ A₂ A₂′ C₁ C₁′ C₂ C₂′}
    {pA₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ A₁′ ⊣ Δᴿ}
    {pA₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ A₂′ ⊣ Δᴿ} →
  endpointMlb A₁ ★ ≡ just C₁ →
  endpointMlb A₁′ ★ ≡ just C₁′ →
  endpointMlb A₂ ★ ≡ just C₂ →
  endpointMlb A₂′ ★ ≡ just C₂′ →
  endpointMlb (A₁ ⇒ A₂) ★ ≡ just (C₁ ⇒ C₂) →
  endpointMlb (A₁′ ⇒ A₂′) ★ ≡ just (C₁′ ⇒ C₂′) →
  EndpointMlbCoherenceᵢ pA₁ id★ →
  EndpointMlbCoherenceᵢ pA₂ id★ →
  EndpointMlbCoherenceᵢ (pA₁ ↦ pA₂) id★
endpoint-arrow-star-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqArr′ coh₁ coh₂ eq eq′
    rewrite eqArr | eqArr′
    with eq | eq′
endpoint-arrow-star-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqArr′ coh₁ coh₂ eq eq′
    | refl | refl =
  coh₁ eq₁ eq₁′ ↦ coh₂ eq₂ eq₂′

endpoint-arrow-star-to-star-star-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A₁ A₂ C₁ C₂}
    {pA₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ ★ ⊣ Δᴿ}
    {pA₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ ★ ⊣ Δᴿ} →
  endpointMlb A₁ ★ ≡ just C₁ →
  endpointMlb ★ ★ ≡ just ★ →
  endpointMlb A₂ ★ ≡ just C₂ →
  endpointMlb ★ ★ ≡ just ★ →
  endpointMlb (A₁ ⇒ A₂) ★ ≡ just (C₁ ⇒ C₂) →
  endpointMlb ★ ★ ≡ just ★ →
  EndpointMlbCoherenceᵢ pA₁ id★ →
  EndpointMlbCoherenceᵢ pA₂ id★ →
  EndpointMlbCoherenceᵢ (tag pA₁ ⇛ pA₂) id★
endpoint-arrow-star-to-star-star-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqStar coh₁ coh₂ eq eq′
    rewrite eqArr | eqStar
    with eq | eq′
endpoint-arrow-star-to-star-star-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqStar coh₁ coh₂ eq eq′
    | refl | refl =
  tag coh₁ eq₁ eq₁′ ⇛ coh₂ eq₂ eq₂′

endpoint-star-arrow-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ B₁ B₁′ B₂ B₂′ C₁ C₁′ C₂ C₂′}
    {pB₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ B₁′ ⊣ Δᴿ}
    {pB₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ B₂′ ⊣ Δᴿ} →
  endpointMlb ★ B₁ ≡ just C₁ →
  endpointMlb ★ B₁′ ≡ just C₁′ →
  endpointMlb ★ B₂ ≡ just C₂ →
  endpointMlb ★ B₂′ ≡ just C₂′ →
  endpointMlb ★ (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  endpointMlb ★ (B₁′ ⇒ B₂′) ≡ just (C₁′ ⇒ C₂′) →
  EndpointMlbCoherenceᵢ id★ pB₁ →
  EndpointMlbCoherenceᵢ id★ pB₂ →
  EndpointMlbCoherenceᵢ id★ (pB₁ ↦ pB₂)
endpoint-star-arrow-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqArr′ coh₁ coh₂ eq eq′
    rewrite eqArr | eqArr′
    with eq | eq′
endpoint-star-arrow-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqArr′ coh₁ coh₂ eq eq′
    | refl | refl =
  coh₁ eq₁ eq₁′ ↦ coh₂ eq₂ eq₂′

endpoint-star-arrow-to-star-star-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ B₁ B₂ C₁ C₂}
    {pB₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ ★ ⊣ Δᴿ}
    {pB₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ ★ ⊣ Δᴿ} →
  endpointMlb ★ B₁ ≡ just C₁ →
  endpointMlb ★ ★ ≡ just ★ →
  endpointMlb ★ B₂ ≡ just C₂ →
  endpointMlb ★ ★ ≡ just ★ →
  endpointMlb ★ (B₁ ⇒ B₂) ≡ just (C₁ ⇒ C₂) →
  endpointMlb ★ ★ ≡ just ★ →
  EndpointMlbCoherenceᵢ id★ pB₁ →
  EndpointMlbCoherenceᵢ id★ pB₂ →
  EndpointMlbCoherenceᵢ id★ (tag pB₁ ⇛ pB₂)
endpoint-star-arrow-to-star-star-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqStar coh₁ coh₂ eq eq′
    rewrite eqArr | eqStar
    with eq | eq′
endpoint-star-arrow-to-star-star-coherence-targetᵢ
    eq₁ eq₁′ eq₂ eq₂′ eqArr eqStar coh₁ coh₂ eq eq′
    | refl | refl =
  tag coh₁ eq₁ eq₁′ ⇛ coh₂ eq₂ eq₂′

endpoint-choice-id-selector-comparableᵢ :
  ∀ {Δ A B C}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)) →
  endpointMlb A B ≡
    just
      (mlb-typeᵢ
        {Γ = choice-idᵢ Δ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)) →
  EndpointMlbComparableᵢ Δ A B
endpoint-choice-id-selector-comparableᵢ route eq =
  endpoint-comparable
    (proj₁ selected)
    (trans eq (cong just (sym (proj₂ selected))))
  where
    selected = choice-id-comparable-selectorᵢ route

endpoint-choice-id-selector-sound-targetᵢ :
  ∀ {Δ A B C}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)) →
  endpointMlb A B ≡
    just
      (mlb-typeᵢ
        {Γ = choice-idᵢ Δ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)) →
  EndpointMlbSoundᵢ Δ A B
endpoint-choice-id-selector-sound-targetᵢ route eq =
  endpoint-comparable-sound-targetᵢ
    (endpoint-choice-id-selector-comparableᵢ route eq)

endpoint-choice-id-selector-maximal-targetᵢ :
  ∀ {Δ A B C}
    {p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ}
    {q : idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ} →
  (route :
    MlbTypeSelectorᵢ
      {Γ = choice-idᵢ Δ}
      (leftChoice-id-proofᵢ p)
      (rightChoice-id-proofᵢ q)) →
  endpointMlb A B ≡
    just
      (mlb-typeᵢ
        {Γ = choice-idᵢ Δ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)) →
  EndpointMlbMaximalᵢ Δ A B
endpoint-choice-id-selector-maximal-targetᵢ route eq =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-choice-id-selector-comparableᵢ route eq)

endpoint-choice-id-selector-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
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
  endpointMlb A B ≡
    just
      (mlb-typeᵢ
        {Γ = choice-idᵢ Δᴸ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)) →
  endpointMlb A′ B′ ≡
    just
      (mlb-typeᵢ
        {Γ = choice-idᵢ Δᴿ}
        (leftChoice-id-proofᵢ p′)
        (rightChoice-id-proofᵢ q′)) →
  MlbTypeSelectorCoherenceᵢ Φ route route′ →
  EndpointMlbCoherenceᵢ pA pB
endpoint-choice-id-selector-coherence-targetᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ eqCan eqCan′ route-coh eq eq′
    rewrite eqCan | eqCan′
    with eq | eq′
endpoint-choice-id-selector-coherence-targetᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {p = p} {q = q} {p′ = p′} {q′ = q′}
    route route′ eqCan eqCan′ route-coh eq eq′
    | refl | refl =
  subst
    (λ Δᴿ′ → Φ ∣ Δᴸ ⊢ lowerᴸ ⊑ lowerᴿ ⊣ Δᴿ′)
    (choice-id-commonCtxᵢ Δᴿ)
    (subst
      (λ Δᴸ′ →
        Φ ∣ Δᴸ′ ⊢ lowerᴸ ⊑ lowerᴿ
        ⊣ choiceCommonCtxᵢ (choice-idᵢ Δᴿ))
      (choice-id-commonCtxᵢ Δᴸ)
      route-coh)
  where
    lowerᴸ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴸ}
        (leftChoice-id-proofᵢ p)
        (rightChoice-id-proofᵢ q)
    lowerᴿ =
      mlb-typeᵢ
        {Γ = choice-idᵢ Δᴿ}
        (leftChoice-id-proofᵢ p′)
        (rightChoice-id-proofᵢ q′)

endpoint-canonical-comparableᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ Δ A B C →
  endpointMlb A B ≡ just C →
  EndpointMlbComparableᵢ Δ A B
endpoint-canonical-comparableᵢ can eq =
  endpoint-comparable
    (canonical-lower-comparableᵢ can)
    (trans eq (cong just (sym (canonical-lower-comparable-lowerᵢ can))))

endpoint-canonical-sound-targetᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ Δ A B C) →
  endpointMlb A B ≡ just C →
  EndpointMlbSoundᵢ Δ A B
endpoint-canonical-sound-targetᵢ can eq =
  endpoint-comparable-sound-targetᵢ
    (endpoint-canonical-comparableᵢ can eq)

endpoint-canonical-maximal-targetᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ Δ A B C) →
  endpointMlb A B ≡ just C →
  EndpointMlbMaximalᵢ Δ A B
endpoint-canonical-maximal-targetᵢ can eq =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-canonical-comparableᵢ can eq)

endpoint-canonical-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′} →
  (can : CanonicalLowerᵢ Δᴸ A B C) →
  (can′ : CanonicalLowerᵢ Δᴿ A′ B′ C′) →
  endpointMlb A B ≡ just C →
  endpointMlb A′ B′ ≡ just C′ →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  EndpointMlbCoherenceᵢ pA pB
endpoint-canonical-coherence-targetᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′} {C = C} {C′ = C′}
    can can′ eqCan eqCan′ pA pB =
  endpoint-comparable-coherence-targetᵢ
    {pA = pA}
    {pB = pB}
    (endpoint-canonical-comparableᵢ can eqCan)
    (endpoint-canonical-comparableᵢ can′ eqCan′)
    (canonical-maximal-lower-coherenceᵢ
      {Φ = Φ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {C = C}
      {C′ = C′}
      {pA = pA}
      {pB = pB}
      can
      can′)

endpoint-canonical-forall-forall-comparableᵢ :
  ∀ {Δ A B C} →
  CanonicalLowerᵢ (suc Δ) A B C →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  EndpointMlbComparableᵢ Δ (`∀ A) (`∀ B)
endpoint-canonical-forall-forall-comparableᵢ can eq =
  endpoint-comparable
    (canonical-forall-forall-comparableᵢ can)
    (trans eq
      (cong just (sym (canonical-forall-forall-comparable-lowerᵢ can))))

endpoint-canonical-forall-forall-sound-targetᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ (suc Δ) A B C) →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  EndpointMlbSoundᵢ Δ (`∀ A) (`∀ B)
endpoint-canonical-forall-forall-sound-targetᵢ can eq =
  endpoint-comparable-sound-targetᵢ
    (endpoint-canonical-forall-forall-comparableᵢ can eq)

endpoint-canonical-forall-forall-maximal-targetᵢ :
  ∀ {Δ A B C} →
  (can : CanonicalLowerᵢ (suc Δ) A B C) →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  EndpointMlbMaximalᵢ Δ (`∀ A) (`∀ B)
endpoint-canonical-forall-forall-maximal-targetᵢ can eq =
  endpoint-comparable-maximal-targetᵢ
    (endpoint-canonical-forall-forall-comparableᵢ can eq)

endpoint-canonical-forall-forall-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  (can : CanonicalLowerᵢ (suc Δᴸ) A B C) →
  (can′ : CanonicalLowerᵢ (suc Δᴿ) A′ B′ C′) →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  endpointMlb (`∀ A′) (`∀ B′) ≡ just (`∀ C′) →
  EndpointMlbCoherenceᵢ (∀ⁱ pA) (∀ⁱ pB)
endpoint-canonical-forall-forall-coherence-targetᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {pA = pA} {pB = pB}
    can can′ eqCan eqCan′ =
  endpoint-comparable-coherence-targetᵢ
    {pA = ∀ⁱ pA}
    {pB = ∀ⁱ pB}
    (endpoint-canonical-forall-forall-comparableᵢ can eqCan)
    (endpoint-canonical-forall-forall-comparableᵢ can′ eqCan′)
    (canonical-forall-forall-maximal-coherenceᵢ
      {Φ = Φ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {C = C}
      {C′ = C′}
      {pA = pA}
      {pB = pB}
      can
      can′)

endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (can : CanonicalLowerᵢ (suc Δᴸ) A B C) →
  (can′ : CanonicalLowerᵢ Δᴿ A′ B′ C′) →
  (occA : occurs zero A ≡ true) →
  (occB : occurs zero B ≡ true) →
  endpointMlb (`∀ A) (`∀ B) ≡ just (`∀ C) →
  endpointMlb A′ B′ ≡ just C′ →
  EndpointMlbCoherenceᵢ (ν occA pA) (ν occB pB)
endpoint-canonical-forall-forall-to-first-order-coherence-targetᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {C = C} {C′ = C′} {pA = pA} {pB = pB}
    can can′ occA occB eqCan eqCan′ =
  endpoint-comparable-coherence-targetᵢ
    {pA = ν occA pA}
    {pB = ν occB pB}
    (endpoint-canonical-forall-forall-comparableᵢ can eqCan)
    (endpoint-canonical-comparableᵢ can′ eqCan′)
    (canonical-forall-forall-to-first-order-maximal-coherenceᵢ
      {Φ = Φ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {C = C}
      {C′ = C′}
      {pA = pA}
      {pB = pB}
      can
      can′
      occA
      occB)

endpoint-mlb-type-from-lower-∀∀-first-order-coherence-targetᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {pB : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣
          suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ A′ ⊣ suc Δᴿ}
    {q′ : idᵢ (suc Δᴿ) ∣ suc Δᴿ ⊢ C′ ⊑ B′ ⊣ suc Δᴿ} →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ (suc Δᴸ)}
      {Δᶜ = suc Δᴸ}
      {Δᴸ = suc Δᴸ}
      {Δᴿ = suc Δᴸ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q)) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ (suc Δᴿ)}
      {Δᶜ = suc Δᴿ}
      {Δᴸ = suc Δᴿ}
      {Δᴿ = suc Δᴿ}
      (leftChoice-id-proofAtᵢ p′)
      (rightChoice-id-proofAtᵢ q′)) →
  endpointMlb (`∀ A) (`∀ B) ≡
    just (`∀ (mlb-type-from-lowerᵢ p q)) →
  endpointMlb (`∀ A′) (`∀ B′) ≡
    just (`∀ (mlb-type-from-lowerᵢ p′ q′)) →
  EndpointMlbCoherenceᵢ (∀ⁱ pA) (∀ⁱ pB)
endpoint-mlb-type-from-lower-∀∀-first-order-coherence-targetᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {pA = pA} {pB = pB}
    route route′ eq eq′ =
  endpoint-comparable-coherence-targetᵢ
    {pA = ∀ⁱ pA}
    {pB = ∀ⁱ pB}
    (endpoint-canonical-forall-forall-comparableᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route)
      eq)
    (endpoint-canonical-forall-forall-comparableᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route′)
      eq′)
    (mlb-type-from-lower-∀∀-first-order-maximal-coherenceᵢ
      {Φ = Φ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {pA = pA}
      {pB = pB}
      route
      route′)

endpoint-mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
    {pA : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : νᵢᶜ Φ ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {p : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ A ⊣ suc Δᴸ}
    {q : idᵢ (suc Δᴸ) ∣ suc Δᴸ ⊢ C ⊑ B ⊣ suc Δᴸ}
    {p′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ A′ ⊣ Δᴿ}
    {q′ : idᵢ Δᴿ ∣ Δᴿ ⊢ C′ ⊑ B′ ⊣ Δᴿ} →
  (occA : occurs zero A ≡ true) →
  (occB : occurs zero B ≡ true) →
  (route :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ (suc Δᴸ)}
      {Δᶜ = suc Δᴸ}
      {Δᴸ = suc Δᴸ}
      {Δᴿ = suc Δᴸ}
      (leftChoice-id-proofAtᵢ p)
      (rightChoice-id-proofAtᵢ q)) →
  (route′ :
    FirstOrderSelectorAtᵢ
      {Γ = choice-idᵢ Δᴿ}
      {Δᶜ = Δᴿ}
      {Δᴸ = Δᴿ}
      {Δᴿ = Δᴿ}
      (leftChoice-id-proofAtᵢ p′)
      (rightChoice-id-proofAtᵢ q′)) →
  endpointMlb (`∀ A) (`∀ B) ≡
    just (`∀ (mlb-type-from-lowerᵢ p q)) →
  endpointMlb A′ B′ ≡ just (mlb-type-from-lowerᵢ p′ q′) →
  EndpointMlbCoherenceᵢ (ν occA pA) (ν occB pB)
endpoint-mlb-type-from-lower-∀∀-first-order-target-coherenceᵢ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {pA = pA} {pB = pB}
    occA occB route route′ eq eq′ =
  endpoint-comparable-coherence-targetᵢ
    {pA = ν occA pA}
    {pB = ν occB pB}
    (endpoint-canonical-forall-forall-comparableᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route)
      eq)
    (endpoint-canonical-comparableᵢ
      (mlb-type-from-lower-first-order-canonicalᵢ route′)
      eq′)
    (mlb-type-from-lower-∀∀-first-order-target-maximal-coherenceᵢ
      {Φ = Φ}
      {Δᴸ = Δᴸ}
      {Δᴿ = Δᴿ}
      {A = A}
      {A′ = A′}
      {B = B}
      {B′ = B′}
      {pA = pA}
      {pB = pB}
      occA
      occB
      route
      route′)

endpoint-forall-var-selfᵢ :
  idᵢ 0 ∣ 0 ⊢ `∀ (＇ 0) ⊑ `∀ (＇ 0) ⊣ 0
endpoint-forall-var-selfᵢ =
  ∀ⁱ (idˣ (here refl) z<s z<s)

endpoint-forall-var-starᵢ :
  idᵢ 0 ∣ 0 ⊢ `∀ (＇ 0) ⊑ ★ ⊣ 0
endpoint-forall-var-starᵢ =
  ν refl (tagˣ (here refl) z<s)

endpoint-forall-var-star-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-selfᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-starᵢ)
endpoint-forall-var-star-routeᵢ =
  sel-∀ν-non∀ᵢ
    refl
    (sel-first-orderᵢ fo-var-starᵢ)
    non∀-＇
    non∀-★

endpoint-comparable-forall-var-starᵢ :
  EndpointMlbComparableᵢ 0 (`∀ (＇ 0)) ★
endpoint-comparable-forall-var-starᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-forall-var-star-routeᵢ
    refl

endpoint-star-forall-var-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-starᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-selfᵢ)
endpoint-star-forall-var-routeᵢ =
  sel-ν∀-non∀ᵢ
    refl
    (sel-first-orderᵢ fo-star-varᵢ)
    non∀-＇
    non∀-★

endpoint-comparable-star-forall-varᵢ :
  EndpointMlbComparableᵢ 0 ★ (`∀ (＇ 0))
endpoint-comparable-star-forall-varᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-star-forall-var-routeᵢ
    refl

endpoint-forall-var-arrow-var-selfᵢ :
  idᵢ 0 ∣ 0 ⊢
    `∀ ((＇ 0) ⇒ (＇ 0)) ⊑ `∀ ((＇ 0) ⇒ (＇ 0)) ⊣ 0
endpoint-forall-var-arrow-var-selfᵢ =
  ∀ⁱ (idˣ (here refl) z<s z<s ↦ idˣ (here refl) z<s z<s)

endpoint-forall-var-arrow-var-starᵢ :
  idᵢ 0 ∣ 0 ⊢ `∀ ((＇ 0) ⇒ (＇ 0)) ⊑ ★ ⊣ 0
endpoint-forall-var-arrow-var-starᵢ =
  ν refl (tag tagˣ (here refl) z<s ⇛ tagˣ (here refl) z<s)

endpoint-forall-var-arrow-var-star-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-arrow-var-selfᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-arrow-var-starᵢ)
endpoint-forall-var-arrow-var-star-routeᵢ =
  sel-∀ν-arrow-starᵢ
    refl
    (sel-first-orderᵢ fo-var-starᵢ)
    (sel-first-orderᵢ fo-var-starᵢ)

endpoint-comparable-forall-var-arrow-var-starᵢ :
  EndpointMlbComparableᵢ 0 (`∀ ((＇ 0) ⇒ (＇ 0))) ★
endpoint-comparable-forall-var-arrow-var-starᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-forall-var-arrow-var-star-routeᵢ
    refl

endpoint-star-forall-var-arrow-var-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-arrow-var-starᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-arrow-var-selfᵢ)
endpoint-star-forall-var-arrow-var-routeᵢ =
  sel-ν∀-star-arrowᵢ
    refl
    (sel-first-orderᵢ fo-star-varᵢ)
    (sel-first-orderᵢ fo-star-varᵢ)

endpoint-comparable-star-forall-var-arrow-varᵢ :
  EndpointMlbComparableᵢ 0 ★ (`∀ ((＇ 0) ⇒ (＇ 0)))
endpoint-comparable-star-forall-var-arrow-varᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-star-forall-var-arrow-var-routeᵢ
    refl

endpoint-first-use-exposure-selfᵢ :
  idᵢ 0 ∣ 0 ⊢
    `∀ (`∀ ((＇ 0) ⇒ (＇ 1))) ⊑ `∀ (`∀ ((＇ 0) ⇒ (＇ 1))) ⊣ 0
endpoint-first-use-exposure-selfᵢ =
  ∀ⁱ (∀ⁱ
    ( idˣ (here refl) z<s z<s
    ↦ idˣ (there (here refl)) (s<s z<s) (s<s z<s)
    ))

endpoint-first-use-exposure-starᵢ :
  idᵢ 0 ∣ 0 ⊢ `∀ (`∀ ((＇ 0) ⇒ (＇ 1))) ⊑ ★ ⊣ 0
endpoint-first-use-exposure-starᵢ =
  ν refl
    (ν refl
      ( tag tagˣ (here refl) z<s
      ⇛ tagˣ (there (here refl)) (s<s z<s)
      ))

endpoint-star-first-use-exposure-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-first-use-exposure-starᵢ)
    (rightChoice-id-proofᵢ endpoint-first-use-exposure-selfᵢ)
endpoint-star-first-use-exposure-routeᵢ =
  sel-ν∀ᵢ
    refl
    (sel-ν∀-star-arrowᵢ
      refl
      (sel-first-orderᵢ fo-star-varᵢ)
      (sel-first-orderᵢ fo-star-varᵢ))
    right-endpoint-ν∀-supportᵢ

endpoint-comparable-star-first-use-exposureᵢ :
  EndpointMlbComparableᵢ 0 ★ (`∀ (`∀ ((＇ 0) ⇒ (＇ 1))))
endpoint-comparable-star-first-use-exposureᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-star-first-use-exposure-routeᵢ
    refl

endpoint-first-use-exposure-star-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-first-use-exposure-selfᵢ)
    (rightChoice-id-proofᵢ endpoint-first-use-exposure-starᵢ)
endpoint-first-use-exposure-star-routeᵢ =
  sel-∀νᵢ
    refl
    (sel-∀ν-arrow-starᵢ
      refl
      (sel-first-orderᵢ fo-var-starᵢ)
      (sel-first-orderᵢ fo-var-starᵢ))
    left-endpoint-∀ν-supportᵢ

endpoint-comparable-first-use-exposure-starᵢ :
  EndpointMlbComparableᵢ 0 (`∀ (`∀ ((＇ 0) ⇒ (＇ 1)))) ★
endpoint-comparable-first-use-exposure-starᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-first-use-exposure-star-routeᵢ
    refl

endpoint-forall-var-arrow-base-selfᵢ :
  idᵢ 0 ∣ 0 ⊢
    `∀ ((＇ 0) ⇒ ‵ `ℕ) ⊑ `∀ ((＇ 0) ⇒ ‵ `ℕ) ⊣ 0
endpoint-forall-var-arrow-base-selfᵢ =
  ∀ⁱ (idˣ (here refl) z<s z<s ↦ idι)

endpoint-forall-var-arrow-base-starᵢ :
  idᵢ 0 ∣ 0 ⊢ `∀ ((＇ 0) ⇒ ‵ `ℕ) ⊑ ★ ⊣ 0
endpoint-forall-var-arrow-base-starᵢ =
  ν refl (tag tagˣ (here refl) z<s ⇛ tag `ℕ)

endpoint-forall-var-arrow-base-star-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-arrow-base-selfᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-arrow-base-starᵢ)
endpoint-forall-var-arrow-base-star-routeᵢ =
  sel-∀ν-arrow-starᵢ
    refl
    (sel-first-orderᵢ fo-var-starᵢ)
    (sel-first-orderᵢ fo-base-starᵢ)

endpoint-star-forall-var-arrow-base-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-arrow-base-starᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-arrow-base-selfᵢ)
endpoint-star-forall-var-arrow-base-routeᵢ =
  sel-ν∀-star-arrowᵢ
    refl
    (sel-first-orderᵢ fo-star-varᵢ)
    (sel-first-orderᵢ fo-star-baseᵢ)

endpoint-comparable-forall-var-arrow-base-starᵢ :
  EndpointMlbComparableᵢ 0 (`∀ ((＇ 0) ⇒ ‵ `ℕ)) ★
endpoint-comparable-forall-var-arrow-base-starᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-forall-var-arrow-base-star-routeᵢ
    refl

endpoint-comparable-star-forall-var-arrow-baseᵢ :
  EndpointMlbComparableᵢ 0 ★ (`∀ ((＇ 0) ⇒ ‵ `ℕ))
endpoint-comparable-star-forall-var-arrow-baseᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-star-forall-var-arrow-base-routeᵢ
    refl

endpoint-forall-var-arrow-star-selfᵢ :
  idᵢ 0 ∣ 0 ⊢
    `∀ ((＇ 0) ⇒ ★) ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0
endpoint-forall-var-arrow-star-selfᵢ =
  ∀ⁱ (idˣ (here refl) z<s z<s ↦ id★)

endpoint-forall-var-arrow-star-starᵢ :
  idᵢ 0 ∣ 0 ⊢ `∀ ((＇ 0) ⇒ ★) ⊑ ★ ⊣ 0
endpoint-forall-var-arrow-star-starᵢ =
  ν refl (tag tagˣ (here refl) z<s ⇛ id★)

endpoint-forall-var-arrow-base-to-starᵢ :
  idᵢ 0 ∣ 0 ⊢
    `∀ ((＇ 0) ⇒ ‵ `ℕ) ⊑ `∀ ((＇ 0) ⇒ ★) ⊣ 0
endpoint-forall-var-arrow-base-to-starᵢ =
  ∀ⁱ (idˣ (here refl) z<s z<s ↦ (tag `ℕ))

endpoint-forall-var-arrow-star-star-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-arrow-star-selfᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-arrow-star-starᵢ)
endpoint-forall-var-arrow-star-star-routeᵢ =
  sel-∀ν-arrow-starᵢ
    refl
    (sel-first-orderᵢ fo-var-starᵢ)
    (sel-first-orderᵢ fo-star-starᵢ)

endpoint-comparable-forall-var-arrow-star-starᵢ :
  EndpointMlbComparableᵢ 0 (`∀ ((＇ 0) ⇒ ★)) ★
endpoint-comparable-forall-var-arrow-star-starᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-forall-var-arrow-star-star-routeᵢ
    refl

endpoint-star-forall-var-arrow-star-routeᵢ :
  MlbTypeSelectorᵢ
    {Γ = choice-idᵢ 0}
    (leftChoice-id-proofᵢ endpoint-forall-var-arrow-star-starᵢ)
    (rightChoice-id-proofᵢ endpoint-forall-var-arrow-star-selfᵢ)
endpoint-star-forall-var-arrow-star-routeᵢ =
  sel-ν∀-star-arrowᵢ
    refl
    (sel-first-orderᵢ fo-star-varᵢ)
    (sel-first-orderᵢ fo-star-starᵢ)

endpoint-comparable-star-forall-var-arrow-starᵢ :
  EndpointMlbComparableᵢ 0 ★ (`∀ ((＇ 0) ⇒ ★))
endpoint-comparable-star-forall-var-arrow-starᵢ =
  endpoint-choice-id-selector-comparableᵢ
    endpoint-star-forall-var-arrow-star-routeᵢ
    refl

endpoint-comparable-star-starᵢ :
  ∀ {Δ} →
  EndpointMlbComparableᵢ Δ ★ ★
endpoint-comparable-star-starᵢ =
  endpoint-comparable comparable-star-starᵢ refl

endpoint-comparable-base-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbComparableᵢ Δ (‵ ι) (‵ ι)
endpoint-comparable-base-baseᵢ {ι = `ℕ} =
  endpoint-comparable comparable-base-baseᵢ refl
endpoint-comparable-base-baseᵢ {ι = `𝔹} =
  endpoint-comparable comparable-base-baseᵢ refl

endpoint-comparable-base-starᵢ :
  ∀ {Δ ι} →
  EndpointMlbComparableᵢ Δ (‵ ι) ★
endpoint-comparable-base-starᵢ =
  endpoint-comparable comparable-base-starᵢ refl

endpoint-comparable-star-baseᵢ :
  ∀ {Δ ι} →
  EndpointMlbComparableᵢ Δ ★ (‵ ι)
endpoint-comparable-star-baseᵢ =
  endpoint-comparable comparable-star-baseᵢ refl

endpoint-comparable-var-varᵢ :
  ∀ {Δ X} →
  X < Δ →
  EndpointMlbComparableᵢ Δ (＇ X) (＇ X)
endpoint-comparable-var-varᵢ {X = X} X<Δ =
  endpoint-comparable (comparable-var-varᵢ X<Δ) (endpointMlb-var-varᵢ X)

endpoint-comparable-var0-var0ᵢ :
  ∀ {Δ} →
  EndpointMlbComparableᵢ (suc Δ) (＇ 0) (＇ 0)
endpoint-comparable-var0-var0ᵢ =
  endpoint-comparable-var-varᵢ z<s

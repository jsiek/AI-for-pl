module proof.EndpointCanonicalMLBSimplePermutation where

-- File Charter:
--   * Proves fixed-endpoint raw routes equivalent modulo adjacent `∀`
--     permutations.
--   * Supplies route exchange, origin, path, and transport infrastructure for
--     cross-context factorization.
--   * Uses one-hole type contexts to retain whole-candidate invariants while
--     descending through wrapped routes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using
  (ℕ; _+_; _<_; _≤_; zero; suc; z≤n; s≤s; z<s; s<s)
open import Data.Nat.Properties using
  ( +-mono-≤; +-monoˡ-<; +-monoʳ-<
  ; <-≤-trans; <-irrefl; <-trans; m≤n⇒m≤1+n
  )
open import Data.Nat.Properties using (_≟_)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (¬_; no; yes)

open import Types
open import Imprecision using
  (ImpCtx; idᵢ; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf
open import ForallPermutation using
  ( _≈∀_; ≈∀-refl; ≈∀-sym; ≈∀-trans; ≈∀-⇒; ≈∀-∀)
open import proof.EndpointCanonicalMLBSimple using
  ( allEndpointMlbsAt; dedupe; enumMLB; hasStrictAbove?
  ; rawEndpointMlbsAt; varCandidate?; varCandidatesUpTo
  )
open import proof.EndpointCanonicalMLBSimpleCompleteness using
  ( dedupe-complete; hasStar-complete; hasVar-complete; impᵢ?
  ; varCandidate-star-var-complete; varCandidate-var-star-complete
  ; varCandidate-var-var-complete; varCandidatesUpTo-complete
  )
open import proof.EndpointCanonicalMLBSimpleMaximality using
  ( false≠true; hasStrictAbove?-completeᵢ
  ; pruneStrictlyBelow-no-strict-above
  )
open import proof.EndpointCanonicalMLBSimpleRoutes
open import proof.EndpointCanonicalMLBSimpleSoundness using
  ( andᵇ-true; dedupe-sound; hasStar-sound; hasVar-sound
  ; pruneStrictlyBelow-sound; ∈-++-split
  )
open import proof.ForallPermutationProperties using
  ( swap01-pres-<; ≈∀-double-swap; ≈∀-double-swap-sym)
open import proof.ImprecisionProperties using
  ( idᵢ-var-identity
  ; no-⇑ᵢ-zero-left; no-⇑ᵢ-zero-right; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left
  ; un⇑ᵢ-ˣ∈; un⇑ᵢ-★∈; un⇑ᴸᵢ-ˣ∈
  ; ⇑ᵢ-ˣ∈; ⇑ᵢ-★∈; ⇑ᴸᵢ-∈
  )
open import proof.TypeProperties using
  (TyRenameWf-ext; occurs-zero-rename-ext; rename-cong)

------------------------------------------------------------------------
-- Type contexts and contextual maximality
------------------------------------------------------------------------

data RouteCtx : Set where
  □ : RouteCtx
  under-∀ : RouteCtx → RouteCtx
  under-⇒₁ : RouteCtx → Ty → RouteCtx
  under-⇒₂ : Ty → RouteCtx → RouteCtx

plug : RouteCtx → Ty → Ty
plug □ A = A
plug (under-∀ K) A = plug K (`∀ A)
plug (under-⇒₁ K B) A = plug K (A ⇒ B)
plug (under-⇒₂ A K) B = plug K (A ⇒ B)

ContextMaximal : ℕ → RouteCtx → (Ty → Set) → Ty → Set
ContextMaximal Δ K Candidate C =
  ∀ {D} →
  Candidate D →
  idᵢ Δ ∣ Δ ⊢ plug K C ⊑ plug K D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ plug K D ⊑ plug K C ⊣ Δ

forall-count : Ty → ℕ
forall-count (＇ X) = zero
forall-count (‵ ι) = zero
forall-count ★ = zero
forall-count (A ⇒ B) = forall-count A + forall-count B
forall-count (`∀ A) = suc (forall-count A)

forall-count-monotone :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  forall-count B ≤ forall-count A
forall-count-monotone id★ = z≤n
forall-count-monotone (idˣ x∈ X<Δ Y<Δ) = z≤n
forall-count-monotone idι = z≤n
forall-count-monotone (p ↦ q) =
  +-mono-≤ (forall-count-monotone p) (forall-count-monotone q)
forall-count-monotone (∀ⁱ p) = s≤s (forall-count-monotone p)
forall-count-monotone (tag ι) = z≤n
forall-count-monotone (tag p ⇛ q) = z≤n
forall-count-monotone (tagˣ x∈ X<Δ) = z≤n
forall-count-monotone (ν occ p) =
  m≤n⇒m≤1+n (forall-count-monotone p)

no-forall-count-increase :
  ∀ {Φ Δᴸ Δᴿ A B} →
  forall-count A < forall-count B →
  ¬ (Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
no-forall-count-increase {A = A} countA<countB A⊑B =
  <-irrefl refl
    (<-≤-trans countA<countB (forall-count-monotone A⊑B))

forall-count-plug-preserves-< :
  ∀ K {A B} →
  forall-count A < forall-count B →
  forall-count (plug K A) < forall-count (plug K B)
forall-count-plug-preserves-< □ A<B = A<B
forall-count-plug-preserves-< (under-∀ K) A<B =
  forall-count-plug-preserves-< K (s<s A<B)
forall-count-plug-preserves-< (under-⇒₁ K C) A<B =
  forall-count-plug-preserves-< K (+-monoˡ-< (forall-count C) A<B)
forall-count-plug-preserves-< (under-⇒₂ C K) A<B =
  forall-count-plug-preserves-< K (+-monoʳ-< (forall-count C) A<B)

no-context-forall-count-increase :
  ∀ {Φ Δᴸ Δᴿ K A B} →
  forall-count A < forall-count B →
  ¬ (Φ ∣ Δᴸ ⊢ plug K A ⊑ plug K B ⊣ Δᴿ)
no-context-forall-count-increase {K = K} A<B =
  no-forall-count-increase (forall-count-plug-preserves-< K A<B)

context-maximal-rejects-count-drop :
  ∀ {Δ K Candidate C D} →
  ContextMaximal Δ K Candidate C →
  Candidate D →
  forall-count D < forall-count C →
  idᵢ Δ ∣ Δ ⊢ plug K C ⊑ plug K D ⊣ Δ →
  ⊥
context-maximal-rejects-count-drop {K = K} {C = C} {D = D}
    maximal D-candidate countD<countC C⊑D =
  no-context-forall-count-increase {K = K} {A = D} {B = C}
    countD<countC
    (maximal D-candidate C⊑D)

all-endpoint-context-maximal :
  ∀ {Δ A B C} →
  C ∈ allEndpointMlbsAt Δ A B →
  ContextMaximal Δ □ (RawEndpointRoute Δ A B) C
all-endpoint-context-maximal {Δ = Δ} {A = A} {B = B} {C = C}
    C∈all {D} Droute C⊑D
    with impᵢ? {Δ = Δ} {A = D} {B = C}
all-endpoint-context-maximal {Δ = Δ} {A = A} {B = B} {C = C}
    C∈all {D} Droute C⊑D | yes D⊑C =
  D⊑C
all-endpoint-context-maximal {Δ = Δ} {A = A} {B = B} {C = C}
    C∈all {D} Droute C⊑D | no ¬D⊑C =
  ⊥-elim (false≠true (trans (sym Cmax) C<D))
  where
    xs = dedupe (rawEndpointMlbsAt Δ A B)

    Cmax : hasStrictAbove? Δ C xs ≡ false
    Cmax =
      pruneStrictlyBelow-no-strict-above
        {Δ = Δ} {C = C} {xs = xs} C∈all

    D∈xs : D ∈ xs
    D∈xs = dedupe-complete (raw-endpoint-route→membership Droute)

    C<D : hasStrictAbove? Δ C xs ≡ true
    C<D = hasStrictAbove?-completeᵢ D∈xs C⊑D ¬D⊑C

record MaximalEndpointRoute (Δ : ℕ) (A B C : Ty) : Set where
  field
    endpoint-route : RawEndpointRoute Δ A B C
    endpoint-context-maximal :
      ContextMaximal Δ □ (RawEndpointRoute Δ A B) C

open MaximalEndpointRoute public

all-endpoint-maximal-route :
  ∀ {Δ A B C} →
  C ∈ allEndpointMlbsAt Δ A B →
  MaximalEndpointRoute Δ A B C
all-endpoint-maximal-route C∈ =
  record
    { endpoint-route = all-endpoint-membership→route C∈
    ; endpoint-context-maximal = all-endpoint-context-maximal C∈
    }

------------------------------------------------------------------------
-- Maximality descent through route constructors
------------------------------------------------------------------------

both-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B))
    (`∀ C) →
  ContextMaximal Δ (under-∀ K)
    (EnumRoute fuel
      (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
      (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)
    C
both-child-context-maximal maximal Droute C⊑D =
  maximal (route-both Droute) C⊑D

left-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B)
    (`∀ C) →
  ContextMaximal Δ (under-∀ K)
    (λ D →
      occurs zero D ≡ true ×
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ)
        (suc Δᶜ) (suc Δᴸ) Δᴿ A B D)
    C
left-child-context-maximal maximal Droute C⊑D =
  maximal (route-left (proj₁ Droute) (proj₂ Droute)) C⊑D

right-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B))
    (`∀ C) →
  ContextMaximal Δ (under-∀ K)
    (λ D →
      occurs zero D ≡ true ×
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
        (suc Δᶜ) Δᴸ (suc Δᴿ) A B D)
    C
right-child-context-maximal maximal Droute C⊑D =
  maximal (route-right (proj₁ Droute) (proj₂ Droute)) C⊑D

arrow-left-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      A₁ A₂ B₁ B₂ C₁ C₂} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ C₂ →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (A₁ ⇒ A₂) (B₁ ⇒ B₂))
    (C₁ ⇒ C₂) →
  ContextMaximal Δ (under-⇒₁ K C₂)
    (EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁)
    C₁
arrow-left-child-context-maximal route₂ maximal route₁ C⊑D =
  maximal (route-arrow route₁ route₂) C⊑D

arrow-right-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      A₁ A₂ B₁ B₂ C₁ C₂} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ C₁ →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (A₁ ⇒ A₂) (B₁ ⇒ B₂))
    (C₁ ⇒ C₂) →
  ContextMaximal Δ (under-⇒₂ C₁ K)
    (EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂)
    C₂
arrow-right-child-context-maximal route₁ maximal route₂ C⊑D =
  maximal (route-arrow route₁ route₂) C⊑D

arrow-star-left-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ C₂ →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) ★)
    (C₁ ⇒ C₂) →
  ContextMaximal Δ (under-⇒₁ K C₂)
    (EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★)
    C₁
arrow-star-left-child-context-maximal route₂ maximal route₁ C⊑D =
  maximal (route-arrow-star route₁ route₂) C⊑D

arrow-star-right-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ C₁ →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) ★)
    (C₁ ⇒ C₂) →
  ContextMaximal Δ (under-⇒₂ C₁ K)
    (EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★)
    C₂
arrow-star-right-child-context-maximal route₁ maximal route₂ C⊑D =
  maximal (route-arrow-star route₁ route₂) C⊑D

star-arrow-left-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ C₂ →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (B₁ ⇒ B₂))
    (C₁ ⇒ C₂) →
  ContextMaximal Δ (under-⇒₁ K C₂)
    (EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁)
    C₁
star-arrow-left-child-context-maximal route₂ maximal route₁ C⊑D =
  maximal (route-star-arrow route₁ route₂) C⊑D

star-arrow-right-child-context-maximal :
  ∀ {Δ K fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ C₁ →
  ContextMaximal Δ K
    (EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (B₁ ⇒ B₂))
    (C₁ ⇒ C₂) →
  ContextMaximal Δ (under-⇒₂ C₁ K)
    (EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂)
    C₂
star-arrow-right-child-context-maximal route₁ maximal route₂ C⊑D =
  maximal (route-star-arrow route₁ route₂) C⊑D

------------------------------------------------------------------------
-- The structural part of the paired-route induction
------------------------------------------------------------------------

data AlignedRoutes :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
    Set where
  aligned-sym :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {route : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
      {route′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
    AlignedRoutes route route′ →
    AlignedRoutes route′ route

  aligned-trans :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D E}
      {route : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
      {route′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D}
      {route″ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B E} →
    AlignedRoutes route route′ →
    AlignedRoutes route′ route″ →
    AlignedRoutes route route″

  aligned-both :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {route :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B C}
      {route′ :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B D} →
    AlignedRoutes route route′ →
    AlignedRoutes (route-both route) (route-both route′)

  aligned-left :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {route :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) Δᴿ A B C}
      {route′ :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) Δᴿ A B D} →
    AlignedRoutes route route′ →
    AlignedRoutes
      (route-left occC route)
      (route-left occD route′)

  aligned-right :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {route :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ)
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
          (suc Δᶜ) Δᴸ (suc Δᴿ) A B C}
      {route′ :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ)
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
          (suc Δᶜ) Δᴸ (suc Δᴿ) A B D} →
    AlignedRoutes route route′ →
    AlignedRoutes
      (route-right occC route)
      (route-right occD route′)

  aligned-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
        A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ C₁}
      {route₂ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ C₂}
      {route₁′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ D₁}
      {route₂′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ D₂} →
    AlignedRoutes route₁ route₁′ →
    AlignedRoutes route₂ route₂′ →
    AlignedRoutes
      (route-arrow route₁ route₂)
      (route-arrow route₁′ route₂′)

  aligned-arrow-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂ D₁ D₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ C₁}
      {route₂ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ C₂}
      {route₁′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ D₁}
      {route₂′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ D₂} →
    AlignedRoutes route₁ route₁′ →
    AlignedRoutes route₂ route₂′ →
    AlignedRoutes
      (route-arrow-star route₁ route₂)
      (route-arrow-star route₁′ route₂′)

  aligned-star-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ C₁}
      {route₂ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ C₂}
      {route₁′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ D₁}
      {route₂′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ D₂} →
    AlignedRoutes route₁ route₁′ →
    AlignedRoutes route₂ route₂′ →
    AlignedRoutes
      (route-star-arrow route₁ route₂)
      (route-star-arrow route₁′ route₂′)

  aligned-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ} →
    AlignedRoutes
      (route-star {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ})
      route-star

  aligned-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    AlignedRoutes
      (route-base {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
      route-base

  aligned-base-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    AlignedRoutes
      (route-base-star {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
      route-base-star

  aligned-star-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    AlignedRoutes
      (route-star-base {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
      route-star-base

  aligned-vars :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X Y C}
      {C∈ C∈′ :
        C ∈ proof.EndpointCanonicalMLBSimple.varCandidatesUpTo
          Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ} →
    AlignedRoutes
      (route-vars
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {Y = Y} {C = C} C∈)
      (route-vars
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {Y = Y} {C = C} C∈′)

  aligned-var-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X C}
      {C∈ C∈′ :
        C ∈ proof.EndpointCanonicalMLBSimple.varCandidatesUpTo
          Φᴸ Φᴿ (＇ X) ★ Δᶜ} →
    AlignedRoutes
      (route-var-star
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {C = C} C∈)
      (route-var-star
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {C = C} C∈′)

  aligned-star-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ Y C}
      {C∈ C∈′ :
        C ∈ proof.EndpointCanonicalMLBSimple.varCandidatesUpTo
          Φᴸ Φᴿ ★ (＇ Y) Δᶜ} →
    AlignedRoutes
      (route-star-var
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {Y = Y} {C = C} C∈)
      (route-star-var
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {Y = Y} {C = C} C∈′)

  aligned-left-right :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {occC : occurs zero C ≡ true}
      {occ∀C : occurs zero (`∀ C) ≡ true}
      {occD : occurs zero D ≡ true}
      {occ∀D : occurs zero (`∀ D) ≡ true}
      {route :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ
            (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ))
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
            (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ))
          (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B C}
      {route′ :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
            (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ))
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ
            (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ))
          (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B D} →
    renameᵗ ForallPermutation.swap01ᵗ C ≈∀ D →
    AlignedRoutes
      (route-left occ∀C (route-right occC route))
      (route-right occ∀D (route-left occD route′))

  aligned-right-left :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {occC : occurs zero C ≡ true}
      {occ∀C : occurs zero (`∀ C) ≡ true}
      {occD : occurs zero D ≡ true}
      {occ∀D : occurs zero (`∀ D) ≡ true}
      {route :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
            (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ))
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ
            (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ))
          (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B C}
      {route′ :
        EnumRoute fuel
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ
            (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ))
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
            (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ))
          (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B D} →
    C ≈∀ renameᵗ ForallPermutation.swap01ᵗ D →
    AlignedRoutes
      (route-right occ∀C (route-left occC route))
      (route-left occ∀D (route-right occD route′))

aligned-routes-≈∀ :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
    {route : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    {route′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  AlignedRoutes route route′ →
  C ≈∀ D
aligned-routes-≈∀ (aligned-sym aligned) =
  ≈∀-sym (aligned-routes-≈∀ aligned)
aligned-routes-≈∀ (aligned-trans aligned₁ aligned₂) =
  ≈∀-trans
    (aligned-routes-≈∀ aligned₁) (aligned-routes-≈∀ aligned₂)
aligned-routes-≈∀ (aligned-both aligned) =
  ≈∀-∀ (aligned-routes-≈∀ aligned)
aligned-routes-≈∀ (aligned-left aligned) =
  ≈∀-∀ (aligned-routes-≈∀ aligned)
aligned-routes-≈∀ (aligned-right aligned) =
  ≈∀-∀ (aligned-routes-≈∀ aligned)
aligned-routes-≈∀ (aligned-arrow aligned₁ aligned₂) =
  ≈∀-⇒
    (aligned-routes-≈∀ aligned₁) (aligned-routes-≈∀ aligned₂)
aligned-routes-≈∀ (aligned-arrow-star aligned₁ aligned₂) =
  ≈∀-⇒
    (aligned-routes-≈∀ aligned₁) (aligned-routes-≈∀ aligned₂)
aligned-routes-≈∀ (aligned-star-arrow aligned₁ aligned₂) =
  ≈∀-⇒
    (aligned-routes-≈∀ aligned₁) (aligned-routes-≈∀ aligned₂)
aligned-routes-≈∀ aligned-star = ≈∀-refl
aligned-routes-≈∀ aligned-base = ≈∀-refl
aligned-routes-≈∀ aligned-base-star = ≈∀-refl
aligned-routes-≈∀ aligned-star-base = ≈∀-refl
aligned-routes-≈∀ aligned-vars = ≈∀-refl
aligned-routes-≈∀ aligned-var-star = ≈∀-refl
aligned-routes-≈∀ aligned-star-var = ≈∀-refl
aligned-routes-≈∀ (aligned-left-right body≈) =
  ≈∀-double-swap body≈
aligned-routes-≈∀ (aligned-right-left body≈) =
  ≈∀-double-swap-sym body≈

left-right-route-exchange-≈∀ :
  ∀ {C D} →
  renameᵗ ForallPermutation.swap01ᵗ C ≈∀ D →
  `∀ (`∀ C) ≈∀ `∀ (`∀ D)
left-right-route-exchange-≈∀ = ≈∀-double-swap

right-left-route-exchange-≈∀ :
  ∀ {C D} →
  C ≈∀ renameᵗ ForallPermutation.swap01ᵗ D →
  `∀ (`∀ C) ≈∀ `∀ (`∀ D)
right-left-route-exchange-≈∀ = ≈∀-double-swap-sym

------------------------------------------------------------------------
-- Route alignment under an adjacent left/right exposure exchange
------------------------------------------------------------------------

data Exposure : Set where
  bothᵉ : Exposure
  leftᵉ : Exposure
  rightᵉ : Exposure

data ModeAt : List Exposure → TyVar → Exposure → Set where
  hereᵉ : ∀ {mode modes} → ModeAt (mode ∷ modes) zero mode
  thereᵉ :
    ∀ {mode other modes X} →
    ModeAt modes X mode →
    ModeAt (other ∷ modes) (suc X) mode

data LeftOrigin : List Exposure → TyVar → Exposure → TyVar → Set
    where
  left-origin-both :
    ∀ {modes} → LeftOrigin (bothᵉ ∷ modes) zero bothᵉ zero
  left-origin-left :
    ∀ {modes} → LeftOrigin (leftᵉ ∷ modes) zero leftᵉ zero
  left-origin-under-both :
    ∀ {modes X mode Y} →
    LeftOrigin modes X mode Y →
    LeftOrigin (bothᵉ ∷ modes) (suc X) mode (suc Y)
  left-origin-under-left :
    ∀ {modes X mode Y} →
    LeftOrigin modes X mode Y →
    LeftOrigin (leftᵉ ∷ modes) (suc X) mode (suc Y)
  left-origin-under-right :
    ∀ {modes X mode Y} →
    LeftOrigin modes X mode Y →
    LeftOrigin (rightᵉ ∷ modes) (suc X) mode Y

data RightOrigin : List Exposure → TyVar → Exposure → TyVar → Set
    where
  right-origin-both :
    ∀ {modes} → RightOrigin (bothᵉ ∷ modes) zero bothᵉ zero
  right-origin-right :
    ∀ {modes} → RightOrigin (rightᵉ ∷ modes) zero rightᵉ zero
  right-origin-under-both :
    ∀ {modes X mode Y} →
    RightOrigin modes X mode Y →
    RightOrigin (bothᵉ ∷ modes) (suc X) mode (suc Y)
  right-origin-under-left :
    ∀ {modes X mode Y} →
    RightOrigin modes X mode Y →
    RightOrigin (leftᵉ ∷ modes) (suc X) mode Y
  right-origin-under-right :
    ∀ {modes X mode Y} →
    RightOrigin modes X mode Y →
    RightOrigin (rightᵉ ∷ modes) (suc X) mode (suc Y)

lift-left : Exposure → ImpCtx → ImpCtx
lift-left bothᵉ Φ = proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ
lift-left leftᵉ Φ = proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ
lift-left rightᵉ Φ = proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ

lift-right : Exposure → ImpCtx → ImpCtx
lift-right bothᵉ Φ = proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ
lift-right leftᵉ Φ = proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ
lift-right rightᵉ Φ = proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ

apply-left : List Exposure → ImpCtx → ImpCtx
apply-left [] Φ = Φ
apply-left (mode ∷ modes) Φ = lift-left mode (apply-left modes Φ)

apply-right : List Exposure → ImpCtx → ImpCtx
apply-right [] Φ = Φ
apply-right (mode ∷ modes) Φ = lift-right mode (apply-right modes Φ)

left-origin-member :
  ∀ {modes Δ X mode Y} →
  LeftOrigin modes X mode Y →
  (X ˣ⊑ˣ Y) ∈ apply-left modes (idᵢ Δ)
left-origin-member left-origin-both = here refl
left-origin-member left-origin-left = here refl
left-origin-member (left-origin-under-both origin) =
  there (⇑ᵢ-ˣ∈ (left-origin-member origin))
left-origin-member (left-origin-under-left origin) =
  there (⇑ᵢ-ˣ∈ (left-origin-member origin))
left-origin-member (left-origin-under-right origin) =
  there (⇑ᴸᵢ-∈ (left-origin-member origin))

right-origin-member :
  ∀ {modes Δ X mode Y} →
  RightOrigin modes X mode Y →
  (X ˣ⊑ˣ Y) ∈ apply-right modes (idᵢ Δ)
right-origin-member right-origin-both = here refl
right-origin-member right-origin-right = here refl
right-origin-member (right-origin-under-both origin) =
  there (⇑ᵢ-ˣ∈ (right-origin-member origin))
right-origin-member (right-origin-under-left origin) =
  there (⇑ᴸᵢ-∈ (right-origin-member origin))
right-origin-member (right-origin-under-right origin) =
  there (⇑ᵢ-ˣ∈ (right-origin-member origin))

left-star-member-at-right :
  ∀ {modes Δ X} →
  ModeAt modes X rightᵉ →
  (X ˣ⊑★) ∈ apply-left modes (idᵢ Δ)
left-star-member-at-right hereᵉ = here refl
left-star-member-at-right (thereᵉ {other = bothᵉ} mode) =
  there (⇑ᵢ-★∈ (left-star-member-at-right mode))
left-star-member-at-right (thereᵉ {other = leftᵉ} mode) =
  there (⇑ᵢ-★∈ (left-star-member-at-right mode))
left-star-member-at-right (thereᵉ {other = rightᵉ} mode) =
  there (⇑ᴸᵢ-∈ (left-star-member-at-right mode))

right-star-member-at-left :
  ∀ {modes Δ X} →
  ModeAt modes X leftᵉ →
  (X ˣ⊑★) ∈ apply-right modes (idᵢ Δ)
right-star-member-at-left hereᵉ = here refl
right-star-member-at-left (thereᵉ {other = bothᵉ} mode) =
  there (⇑ᵢ-★∈ (right-star-member-at-left mode))
right-star-member-at-left (thereᵉ {other = leftᵉ} mode) =
  there (⇑ᴸᵢ-∈ (right-star-member-at-left mode))
right-star-member-at-left (thereᵉ {other = rightᵉ} mode) =
  there (⇑ᵢ-★∈ (right-star-member-at-left mode))

apply-common-depth : List Exposure → ℕ → ℕ
apply-common-depth [] Δ = Δ
apply-common-depth (mode ∷ modes) Δ =
  suc (apply-common-depth modes Δ)

apply-left-depth : List Exposure → ℕ → ℕ
apply-left-depth [] Δ = Δ
apply-left-depth (bothᵉ ∷ modes) Δ =
  suc (apply-left-depth modes Δ)
apply-left-depth (leftᵉ ∷ modes) Δ =
  suc (apply-left-depth modes Δ)
apply-left-depth (rightᵉ ∷ modes) Δ =
  apply-left-depth modes Δ

apply-right-depth : List Exposure → ℕ → ℕ
apply-right-depth [] Δ = Δ
apply-right-depth (bothᵉ ∷ modes) Δ =
  suc (apply-right-depth modes Δ)
apply-right-depth (leftᵉ ∷ modes) Δ =
  apply-right-depth modes Δ
apply-right-depth (rightᵉ ∷ modes) Δ =
  suc (apply-right-depth modes Δ)

swap-under : List Exposure → Renameᵗ
swap-under [] = ForallPermutation.swap01ᵗ
swap-under (mode ∷ modes) = extᵗ (swap-under modes)

swap-at : TyVar → Renameᵗ
swap-at zero = ForallPermutation.swap01ᵗ
swap-at (suc k) zero = zero
swap-at (suc k) (suc X) = suc (swap-at k X)

swap-at-left : ∀ k → swap-at k (suc k) ≡ k
swap-at-left zero = refl
swap-at-left (suc k) = cong suc (swap-at-left k)

swap-at-right : ∀ k → swap-at k k ≡ suc k
swap-at-right zero = refl
swap-at-right (suc k) = cong suc (swap-at-right k)

swap-at-ext-rename :
  ∀ k A →
  renameᵗ (extᵗ (swap-at k)) A ≡ renameᵗ (swap-at (suc k)) A
swap-at-ext-rename k A =
  rename-cong
    {ρ = extᵗ (swap-at k)}
    {ρ′ = swap-at (suc k)}
    (λ { zero → refl ; (suc X) → refl })
    A

∨-true-left : ∀ {a b} → a ≡ true → a ∨ b ≡ true
∨-true-left {a = true} refl = refl
∨-true-left {a = false} ()

∨-true-right : ∀ {a b} → b ≡ true → a ∨ b ≡ true
∨-true-right {a = false} refl = refl
∨-true-right {a = true} _ = refl

occurs-var-refl : ∀ X → occurs X (＇ X) ≡ true
occurs-var-refl X with X ≟ X
occurs-var-refl X | yes refl = refl
occurs-var-refl X | no X≢X = ⊥-elim (X≢X refl)

occurs-swap-at-left :
  ∀ k A →
  occurs (suc k) A ≡ true →
  occurs k (renameᵗ (swap-at k) A) ≡ true
occurs-swap-at-left k (＇ Y) occ with suc k ≟ Y
occurs-swap-at-left k (＇ .(suc k)) occ | yes refl
    rewrite swap-at-left k =
  occurs-var-refl k
occurs-swap-at-left k (＇ Y) () | no neq
occurs-swap-at-left k (‵ ι) ()
occurs-swap-at-left k ★ ()
occurs-swap-at-left k (A ⇒ B) occ with occurs (suc k) A in occA
occurs-swap-at-left k (A ⇒ B) occ | true =
  ∨-true-left (occurs-swap-at-left k A occA)
occurs-swap-at-left k (A ⇒ B) occ | false =
  ∨-true-right (occurs-swap-at-left k B occ)
occurs-swap-at-left k (`∀ A) occ rewrite swap-at-ext-rename k A =
  occurs-swap-at-left (suc k) A occ

occurs-swap-at-right :
  ∀ k A →
  occurs k A ≡ true →
  occurs (suc k) (renameᵗ (swap-at k) A) ≡ true
occurs-swap-at-right k (＇ Y) occ with k ≟ Y
occurs-swap-at-right k (＇ .k) occ | yes refl
    rewrite swap-at-right k =
  occurs-var-refl (suc k)
occurs-swap-at-right k (＇ Y) () | no neq
occurs-swap-at-right k (‵ ι) ()
occurs-swap-at-right k ★ ()
occurs-swap-at-right k (A ⇒ B) occ with occurs k A in occA
occurs-swap-at-right k (A ⇒ B) occ | true =
  ∨-true-left (occurs-swap-at-right k A occA)
occurs-swap-at-right k (A ⇒ B) occ | false =
  ∨-true-right (occurs-swap-at-right k B occ)
occurs-swap-at-right k (`∀ A) occ rewrite swap-at-ext-rename k A =
  occurs-swap-at-right (suc k) A occ

occurs-swap01-left :
  ∀ {A} →
  occurs (suc zero) A ≡ true →
  occurs zero (renameᵗ ForallPermutation.swap01ᵗ A) ≡ true
occurs-swap01-left {A} = occurs-swap-at-left zero A

occurs-swap01-right :
  ∀ {A} →
  occurs zero A ≡ true →
  occurs (suc zero) (renameᵗ ForallPermutation.swap01ᵗ A) ≡ true
occurs-swap01-right {A} = occurs-swap-at-right zero A

un⇑ᴸ-star :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ Imprecision.⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᴸ-star {Φ = []} ()
un⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸ-star x∈)
un⇑ᴸ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸ-star x∈)

no-⇑ᴸ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ Imprecision.⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸ-zero-star {Φ = []} ()
no-⇑ᴸ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸ-zero-star x∈
no-⇑ᴸ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸ-zero-star x∈

no-∀ctx-zero-left :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ suc Y) ∈
    proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ →
  ⊥
no-∀ctx-zero-left (here ())
no-∀ctx-zero-left (there x∈) = no-⇑ᵢ-zero-left x∈

no-∀ctx-zero-right :
  ∀ {Φ X} →
  (suc X ˣ⊑ˣ zero) ∈
    proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ →
  ⊥
no-∀ctx-zero-right (here ())
no-∀ctx-zero-right (there x∈) = no-⇑ᵢ-zero-right x∈

un∀-var :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ suc Y) ∈
    proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un∀-var (here ())
un∀-var (there x∈) = un⇑ᵢ-ˣ∈ x∈

no-∀ctx-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ →
  ⊥
no-∀ctx-zero-star (here ())
no-∀ctx-zero-star (there x∈) = no-⇑ᵢ-zero-star x∈

un∀-star :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ →
  (X ˣ⊑★) ∈ Φ
un∀-star (here ())
un∀-star (there x∈) = un⇑ᵢ-★∈ x∈

no-νctx-zero-var :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ Y) ∈ proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ →
  ⊥
no-νctx-zero-var (here ())
no-νctx-zero-var (there x∈) = no-⇑ᴸᵢ-zero-left x∈

unν-var :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ Y) ∈ proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
unν-var (here ())
unν-var (there x∈) = un⇑ᴸᵢ-ˣ∈ x∈

unν-star :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ →
  (X ˣ⊑★) ∈ Φ
unν-star (here ())
unν-star (there x∈) = un⇑ᴸ-star x∈

record CommonTransport
    (ρ : Renameᵗ) (Φ Ψ : ImpCtx) : Set where
  field
    transport-var :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φ →
      (ρ X ˣ⊑ˣ Y) ∈ Ψ
    transport-star :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φ →
      (ρ X ˣ⊑★) ∈ Ψ

open CommonTransport

transport-∀ :
  ∀ {ρ Φ Ψ} →
  CommonTransport ρ Φ Ψ →
  CommonTransport (extᵗ ρ)
    (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ)
    (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Ψ)
transport-∀ transport .transport-var (here refl) = here refl
transport-∀ transport .transport-var {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
transport-∀ transport .transport-var {X = suc X} {Y = zero}
    (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
transport-∀ transport .transport-var {X = suc X} {Y = suc Y}
    (there x∈) =
  there (⇑ᵢ-ˣ∈ (transport-var transport (un⇑ᵢ-ˣ∈ x∈)))
transport-∀ transport .transport-star {X = zero} (here ())
transport-∀ transport .transport-star {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
transport-∀ transport .transport-star {X = suc X} (here ())
transport-∀ transport .transport-star {X = suc X} (there x∈) =
  there (⇑ᵢ-★∈ (transport-star transport (un⇑ᵢ-★∈ x∈)))

transport-ν :
  ∀ {ρ Φ Ψ} →
  CommonTransport ρ Φ Ψ →
  CommonTransport (extᵗ ρ)
    (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ)
    (proof.EndpointCanonicalMLBSimple.νᵢᶜ Ψ)
transport-ν transport .transport-var (here ())
transport-ν transport .transport-var {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
transport-ν transport .transport-var {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-∈ (transport-var transport (un⇑ᴸᵢ-ˣ∈ x∈)))
transport-ν transport .transport-star (here refl) = here refl
transport-ν transport .transport-star {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸ-zero-star x∈)
transport-ν transport .transport-star {X = suc X} (there x∈) =
  there (⇑ᴸᵢ-∈ (transport-star transport (un⇑ᴸ-star x∈)))

transport-ν∀-to-∀ν :
  ∀ Φ →
  CommonTransport ForallPermutation.swap01ᵗ
    (proof.EndpointCanonicalMLBSimple.νᵢᶜ
      (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ))
    (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
      (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ))
transport-ν∀-to-∀ν Φ .transport-var (here ())
transport-ν∀-to-∀ν Φ .transport-var {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
transport-ν∀-to-∀ν Φ .transport-var
    {X = suc zero} {Y = zero} (there x∈) =
  here refl
transport-ν∀-to-∀ν Φ .transport-var
    {X = suc zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-∀ctx-zero-left (un⇑ᴸᵢ-ˣ∈ x∈))
transport-ν∀-to-∀ν Φ .transport-var
    {X = suc (suc X)} {Y = zero} (there x∈) =
  ⊥-elim (no-∀ctx-zero-right (un⇑ᴸᵢ-ˣ∈ x∈))
transport-ν∀-to-∀ν Φ .transport-var
    {X = suc (suc X)} {Y = suc Y} (there x∈) =
  there
    (⇑ᵢ-ˣ∈
      (there
        (⇑ᴸᵢ-∈
          (un∀-var (un⇑ᴸᵢ-ˣ∈ x∈)))))
transport-ν∀-to-∀ν Φ .transport-star (here refl) =
  there (⇑ᵢ-★∈ (here refl))
transport-ν∀-to-∀ν Φ .transport-star
    {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸ-zero-star x∈)
transport-ν∀-to-∀ν Φ .transport-star
    {X = suc zero} (there x∈) =
  ⊥-elim (no-∀ctx-zero-star (un⇑ᴸ-star x∈))
transport-ν∀-to-∀ν Φ .transport-star
    {X = suc (suc X)} (there x∈) =
  there
    (⇑ᵢ-★∈
      (there
        (⇑ᴸᵢ-∈
          (un∀-star (un⇑ᴸ-star x∈)))))

transport-∀ν-to-ν∀ :
  ∀ Φ →
  CommonTransport ForallPermutation.swap01ᵗ
    (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
      (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ))
    (proof.EndpointCanonicalMLBSimple.νᵢᶜ
      (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ))
transport-∀ν-to-ν∀ Φ .transport-var (here refl) =
  there (⇑ᴸᵢ-∈ (here refl))
transport-∀ν-to-ν∀ Φ .transport-var {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
transport-∀ν-to-ν∀ Φ .transport-var
    {X = suc zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
transport-∀ν-to-ν∀ Φ .transport-var
    {X = suc zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-νctx-zero-var (un⇑ᵢ-ˣ∈ x∈))
transport-∀ν-to-ν∀ Φ .transport-var
    {X = suc (suc X)} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
transport-∀ν-to-ν∀ Φ .transport-var
    {X = suc (suc X)} {Y = suc Y} (there x∈) =
  there
    (⇑ᴸᵢ-∈
      (there
        (⇑ᵢ-ˣ∈
          (unν-var (un⇑ᵢ-ˣ∈ x∈)))))
transport-∀ν-to-ν∀ Φ .transport-star {X = zero} (here ())
transport-∀ν-to-ν∀ Φ .transport-star {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-star x∈)
transport-∀ν-to-ν∀ Φ .transport-star
    {X = suc zero} (there x∈) =
  here refl
transport-∀ν-to-ν∀ Φ .transport-star
    {X = suc (suc X)} (there x∈) =
  there
    (⇑ᴸᵢ-∈
      (there
        (⇑ᵢ-★∈
          (unν-star (un⇑ᵢ-★∈ x∈)))))

lr-left-context : List Exposure → ImpCtx → ImpCtx
lr-left-context modes Φ =
  apply-left modes
    (proof.EndpointCanonicalMLBSimple.νᵢᶜ
      (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ))

lr-right-context : List Exposure → ImpCtx → ImpCtx
lr-right-context modes Φ =
  apply-right modes
    (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
      (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ))

rl-left-context : List Exposure → ImpCtx → ImpCtx
rl-left-context modes Φ =
  apply-left modes
    (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
      (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ))

rl-right-context : List Exposure → ImpCtx → ImpCtx
rl-right-context modes Φ =
  apply-right modes
    (proof.EndpointCanonicalMLBSimple.νᵢᶜ
      (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ))

left-context-transport :
  ∀ modes Φ →
  CommonTransport (swap-under modes)
    (lr-left-context modes Φ) (rl-left-context modes Φ)
left-context-transport [] Φ = transport-ν∀-to-∀ν Φ
left-context-transport (bothᵉ ∷ modes) Φ =
  transport-∀ (left-context-transport modes Φ)
left-context-transport (leftᵉ ∷ modes) Φ =
  transport-∀ (left-context-transport modes Φ)
left-context-transport (rightᵉ ∷ modes) Φ =
  transport-ν (left-context-transport modes Φ)

right-context-transport :
  ∀ modes Φ →
  CommonTransport (swap-under modes)
    (lr-right-context modes Φ) (rl-right-context modes Φ)
right-context-transport [] Φ = transport-∀ν-to-ν∀ Φ
right-context-transport (bothᵉ ∷ modes) Φ =
  transport-∀ (right-context-transport modes Φ)
right-context-transport (leftᵉ ∷ modes) Φ =
  transport-ν (right-context-transport modes Φ)
right-context-transport (rightᵉ ∷ modes) Φ =
  transport-∀ (right-context-transport modes Φ)

------------------------------------------------------------------------
-- Variable uniqueness in contexts generated by an exposure history
------------------------------------------------------------------------

VarTargetInjective : ImpCtx → Set
VarTargetInjective Φ =
  ∀ {W Z X} →
  (W ˣ⊑ˣ X) ∈ Φ →
  (Z ˣ⊑ˣ X) ∈ Φ →
  W ≡ Z

VarSourceFunctional : ImpCtx → Set
VarSourceFunctional Φ =
  ∀ {W X Y} →
  (W ˣ⊑ˣ X) ∈ Φ →
  (W ˣ⊑ˣ Y) ∈ Φ →
  X ≡ Y

idᵢ-var-target-injective : ∀ Δ → VarTargetInjective (idᵢ Δ)
idᵢ-var-target-injective Δ W⊑X Z⊑X =
  trans (idᵢ-var-identity W⊑X) (sym (idᵢ-var-identity Z⊑X))

idᵢ-var-source-functional : ∀ Δ → VarSourceFunctional (idᵢ Δ)
idᵢ-var-source-functional Δ W⊑X W⊑Y =
  trans (sym (idᵢ-var-identity W⊑X)) (idᵢ-var-identity W⊑Y)

∀ctx-var-source-functional :
  ∀ {Φ} →
  VarSourceFunctional Φ →
  VarSourceFunctional (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ)
∀ctx-var-source-functional functional (here refl) (here refl) = refl
∀ctx-var-source-functional functional (here refl) (there W⊑Y) =
  ⊥-elim (no-⇑ᵢ-zero-left W⊑Y)
∀ctx-var-source-functional functional (there W⊑X) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left W⊑X)
∀ctx-var-source-functional functional {W = zero}
    (there W⊑X) (there W⊑Y) =
  ⊥-elim (no-⇑ᵢ-zero-left W⊑X)
∀ctx-var-source-functional functional
    {W = suc W} {X = zero} (there W⊑X) (there W⊑Y) =
  ⊥-elim (no-⇑ᵢ-zero-right W⊑X)
∀ctx-var-source-functional functional
    {W = suc W} {X = suc X} {Y = zero}
    (there W⊑X) (there W⊑Y) =
  ⊥-elim (no-⇑ᵢ-zero-right W⊑Y)
∀ctx-var-source-functional functional
    {W = suc W} {X = suc X} {Y = suc Y}
    (there W⊑X) (there W⊑Y) =
  cong suc (functional (un⇑ᵢ-ˣ∈ W⊑X) (un⇑ᵢ-ˣ∈ W⊑Y))

νctx-var-source-functional :
  ∀ {Φ} →
  VarSourceFunctional Φ →
  VarSourceFunctional (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ)
νctx-var-source-functional functional (here ()) W⊑Y
νctx-var-source-functional functional {W = zero}
    (there W⊑X) W⊑Y =
  ⊥-elim (no-⇑ᴸᵢ-zero-left W⊑X)
νctx-var-source-functional functional {W = suc W}
    (there W⊑X) (here ())
νctx-var-source-functional functional {W = suc W}
    (there W⊑X) (there W⊑Y) =
  functional (un⇑ᴸᵢ-ˣ∈ W⊑X) (un⇑ᴸᵢ-ˣ∈ W⊑Y)

∀ctx-var-target-injective :
  ∀ {Φ} →
  VarTargetInjective Φ →
  VarTargetInjective (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φ)
∀ctx-var-target-injective injective (here refl) (here refl) = refl
∀ctx-var-target-injective injective {Z = zero}
    (here refl) (there Z⊑X) =
  ⊥-elim (no-⇑ᵢ-zero-left Z⊑X)
∀ctx-var-target-injective injective {Z = suc z}
    (here refl) (there Z⊑X) =
  ⊥-elim (no-⇑ᵢ-zero-right Z⊑X)
∀ctx-var-target-injective injective {W = zero}
    (there W⊑X) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left W⊑X)
∀ctx-var-target-injective injective {W = suc w}
    (there W⊑X) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right W⊑X)
∀ctx-var-target-injective injective {W = zero}
    (there W⊑X) (there Z⊑X) =
  ⊥-elim (no-⇑ᵢ-zero-left W⊑X)
∀ctx-var-target-injective injective {W = suc w} {Z = zero}
    (there W⊑X) (there Z⊑X) =
  ⊥-elim (no-⇑ᵢ-zero-left Z⊑X)
∀ctx-var-target-injective injective
    {W = suc w} {Z = suc z} {X = suc x}
    (there W⊑X) (there Z⊑X) =
  cong suc (injective (un⇑ᵢ-ˣ∈ W⊑X) (un⇑ᵢ-ˣ∈ Z⊑X))
∀ctx-var-target-injective injective
    {W = suc w} {Z = suc z} {X = zero}
    (there W⊑X) (there Z⊑X) =
  ⊥-elim (no-⇑ᵢ-zero-right W⊑X)

νctx-var-target-injective :
  ∀ {Φ} →
  VarTargetInjective Φ →
  VarTargetInjective (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φ)
νctx-var-target-injective injective (here ())
νctx-var-target-injective injective {W = zero}
    (there W⊑X) Z⊑X =
  ⊥-elim (no-⇑ᴸᵢ-zero-left W⊑X)
νctx-var-target-injective injective {W = suc w}
    (there W⊑X) (here ())
νctx-var-target-injective injective
    {W = suc w} {Z = zero}
    (there W⊑X) (there Z⊑X) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left Z⊑X)
νctx-var-target-injective injective
    {W = suc w} {Z = suc z}
    (there W⊑X) (there Z⊑X) =
  cong suc (injective (un⇑ᴸᵢ-ˣ∈ W⊑X) (un⇑ᴸᵢ-ˣ∈ Z⊑X))

left-history-var-target-injective :
  ∀ modes Δ → VarTargetInjective (apply-left modes (idᵢ Δ))
left-history-var-target-injective [] Δ = idᵢ-var-target-injective Δ
left-history-var-target-injective (bothᵉ ∷ modes) Δ =
  ∀ctx-var-target-injective (left-history-var-target-injective modes Δ)
left-history-var-target-injective (leftᵉ ∷ modes) Δ =
  ∀ctx-var-target-injective (left-history-var-target-injective modes Δ)
left-history-var-target-injective (rightᵉ ∷ modes) Δ =
  νctx-var-target-injective (left-history-var-target-injective modes Δ)

right-history-var-target-injective :
  ∀ modes Δ → VarTargetInjective (apply-right modes (idᵢ Δ))
right-history-var-target-injective [] Δ = idᵢ-var-target-injective Δ
right-history-var-target-injective (bothᵉ ∷ modes) Δ =
  ∀ctx-var-target-injective (right-history-var-target-injective modes Δ)
right-history-var-target-injective (leftᵉ ∷ modes) Δ =
  νctx-var-target-injective (right-history-var-target-injective modes Δ)
right-history-var-target-injective (rightᵉ ∷ modes) Δ =
  ∀ctx-var-target-injective (right-history-var-target-injective modes Δ)

left-history-var-source-functional :
  ∀ modes Δ → VarSourceFunctional (apply-left modes (idᵢ Δ))
left-history-var-source-functional [] Δ = idᵢ-var-source-functional Δ
left-history-var-source-functional (bothᵉ ∷ modes) Δ =
  ∀ctx-var-source-functional (left-history-var-source-functional modes Δ)
left-history-var-source-functional (leftᵉ ∷ modes) Δ =
  ∀ctx-var-source-functional (left-history-var-source-functional modes Δ)
left-history-var-source-functional (rightᵉ ∷ modes) Δ =
  νctx-var-source-functional (left-history-var-source-functional modes Δ)

right-history-var-source-functional :
  ∀ modes Δ → VarSourceFunctional (apply-right modes (idᵢ Δ))
right-history-var-source-functional [] Δ = idᵢ-var-source-functional Δ
right-history-var-source-functional (bothᵉ ∷ modes) Δ =
  ∀ctx-var-source-functional (right-history-var-source-functional modes Δ)
right-history-var-source-functional (leftᵉ ∷ modes) Δ =
  νctx-var-source-functional (right-history-var-source-functional modes Δ)
right-history-var-source-functional (rightᵉ ∷ modes) Δ =
  ∀ctx-var-source-functional (right-history-var-source-functional modes Δ)

right-history-no-var-at-left :
  ∀ {modes Δ X Y} →
  ModeAt modes X leftᵉ →
  (X ˣ⊑ˣ Y) ∈ apply-right modes (idᵢ Δ) →
  ⊥
right-history-no-var-at-left hereᵉ (here ())
right-history-no-var-at-left hereᵉ (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
right-history-no-var-at-left
    (thereᵉ {other = bothᵉ} mode) (here ())
right-history-no-var-at-left {Y = zero}
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
right-history-no-var-at-left {Y = suc Y}
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  right-history-no-var-at-left mode (un⇑ᵢ-ˣ∈ x∈)
right-history-no-var-at-left
    (thereᵉ {other = leftᵉ} mode) (here ())
right-history-no-var-at-left
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  right-history-no-var-at-left mode (un⇑ᴸᵢ-ˣ∈ x∈)
right-history-no-var-at-left
    (thereᵉ {other = rightᵉ} mode) (here ())
right-history-no-var-at-left {Y = zero}
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
right-history-no-var-at-left {Y = suc Y}
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  right-history-no-var-at-left mode (un⇑ᵢ-ˣ∈ x∈)

left-history-no-star-at-left :
  ∀ {modes Δ X} →
  ModeAt modes X leftᵉ →
  (X ˣ⊑★) ∈ apply-left modes (idᵢ Δ) →
  ⊥
left-history-no-star-at-left hereᵉ (here ())
left-history-no-star-at-left hereᵉ (there x∈) =
  no-⇑ᵢ-zero-star x∈
left-history-no-star-at-left
    (thereᵉ {other = bothᵉ} mode) (here ())
left-history-no-star-at-left
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  left-history-no-star-at-left mode (un⇑ᵢ-★∈ x∈)
left-history-no-star-at-left
    (thereᵉ {other = leftᵉ} mode) (here ())
left-history-no-star-at-left
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  left-history-no-star-at-left mode (un⇑ᵢ-★∈ x∈)
left-history-no-star-at-left
    (thereᵉ {other = rightᵉ} mode) (here ())
left-history-no-star-at-left
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  left-history-no-star-at-left mode (un⇑ᴸ-star x∈)

left-history-no-var-at-right :
  ∀ {modes Δ X Y} →
  ModeAt modes X rightᵉ →
  (X ˣ⊑ˣ Y) ∈ apply-left modes (idᵢ Δ) →
  ⊥
left-history-no-var-at-right hereᵉ (here ())
left-history-no-var-at-right hereᵉ (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
left-history-no-var-at-right
    (thereᵉ {other = bothᵉ} mode) (here ())
left-history-no-var-at-right {Y = zero}
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
left-history-no-var-at-right {Y = suc Y}
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  left-history-no-var-at-right mode (un⇑ᵢ-ˣ∈ x∈)
left-history-no-var-at-right
    (thereᵉ {other = leftᵉ} mode) (here ())
left-history-no-var-at-right {Y = zero}
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  no-⇑ᵢ-zero-right x∈
left-history-no-var-at-right {Y = suc Y}
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  left-history-no-var-at-right mode (un⇑ᵢ-ˣ∈ x∈)
left-history-no-var-at-right
    (thereᵉ {other = rightᵉ} mode) (here ())
left-history-no-var-at-right
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  left-history-no-var-at-right mode (un⇑ᴸᵢ-ˣ∈ x∈)

right-history-no-star-at-right :
  ∀ {modes Δ X} →
  ModeAt modes X rightᵉ →
  (X ˣ⊑★) ∈ apply-right modes (idᵢ Δ) →
  ⊥
right-history-no-star-at-right hereᵉ (here ())
right-history-no-star-at-right hereᵉ (there x∈) =
  no-⇑ᵢ-zero-star x∈
right-history-no-star-at-right
    (thereᵉ {other = bothᵉ} mode) (here ())
right-history-no-star-at-right
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  right-history-no-star-at-right mode (un⇑ᵢ-★∈ x∈)
right-history-no-star-at-right
    (thereᵉ {other = leftᵉ} mode) (here ())
right-history-no-star-at-right
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  right-history-no-star-at-right mode (un⇑ᴸ-star x∈)
right-history-no-star-at-right
    (thereᵉ {other = rightᵉ} mode) (here ())
right-history-no-star-at-right
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  right-history-no-star-at-right mode (un⇑ᵢ-★∈ x∈)

left-history-no-star-at-both :
  ∀ {modes Δ X} →
  ModeAt modes X bothᵉ →
  (X ˣ⊑★) ∈ apply-left modes (idᵢ Δ) →
  ⊥
left-history-no-star-at-both hereᵉ (here ())
left-history-no-star-at-both hereᵉ (there x∈) =
  no-⇑ᵢ-zero-star x∈
left-history-no-star-at-both
    (thereᵉ {other = bothᵉ} mode) (here ())
left-history-no-star-at-both
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  left-history-no-star-at-both mode (un⇑ᵢ-★∈ x∈)
left-history-no-star-at-both
    (thereᵉ {other = leftᵉ} mode) (here ())
left-history-no-star-at-both
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  left-history-no-star-at-both mode (un⇑ᵢ-★∈ x∈)
left-history-no-star-at-both
    (thereᵉ {other = rightᵉ} mode) (here ())
left-history-no-star-at-both
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  left-history-no-star-at-both mode (un⇑ᴸ-star x∈)

right-history-no-star-at-both :
  ∀ {modes Δ X} →
  ModeAt modes X bothᵉ →
  (X ˣ⊑★) ∈ apply-right modes (idᵢ Δ) →
  ⊥
right-history-no-star-at-both hereᵉ (here ())
right-history-no-star-at-both hereᵉ (there x∈) =
  no-⇑ᵢ-zero-star x∈
right-history-no-star-at-both
    (thereᵉ {other = bothᵉ} mode) (here ())
right-history-no-star-at-both
    (thereᵉ {other = bothᵉ} mode) (there x∈) =
  right-history-no-star-at-both mode (un⇑ᵢ-★∈ x∈)
right-history-no-star-at-both
    (thereᵉ {other = leftᵉ} mode) (here ())
right-history-no-star-at-both
    (thereᵉ {other = leftᵉ} mode) (there x∈) =
  right-history-no-star-at-both mode (un⇑ᴸ-star x∈)
right-history-no-star-at-both
    (thereᵉ {other = rightᵉ} mode) (here ())
right-history-no-star-at-both
    (thereᵉ {other = rightᵉ} mode) (there x∈) =
  right-history-no-star-at-both mode (un⇑ᵢ-★∈ x∈)

left-origin-mode :
  ∀ {modes X mode Y} →
  LeftOrigin modes X mode Y →
  ModeAt modes X mode
left-origin-mode left-origin-both = hereᵉ
left-origin-mode left-origin-left = hereᵉ
left-origin-mode (left-origin-under-both origin) =
  thereᵉ (left-origin-mode origin)
left-origin-mode (left-origin-under-left origin) =
  thereᵉ (left-origin-mode origin)
left-origin-mode (left-origin-under-right origin) =
  thereᵉ (left-origin-mode origin)

right-origin-mode :
  ∀ {modes X mode Y} →
  RightOrigin modes X mode Y →
  ModeAt modes X mode
right-origin-mode right-origin-both = hereᵉ
right-origin-mode right-origin-right = hereᵉ
right-origin-mode (right-origin-under-both origin) =
  thereᵉ (right-origin-mode origin)
right-origin-mode (right-origin-under-left origin) =
  thereᵉ (right-origin-mode origin)
right-origin-mode (right-origin-under-right origin) =
  thereᵉ (right-origin-mode origin)

swap-under-pres-< :
  ∀ {modes Δ X} →
  X < apply-common-depth modes (suc (suc Δ)) →
  swap-under modes X < apply-common-depth modes (suc (suc Δ))
swap-under-pres-< {modes = []} = swap01-pres-<
swap-under-pres-< {modes = mode ∷ modes} =
  TyRenameWf-ext (swap-under-pres-< {modes = modes})

self<suc : ∀ n → n < suc n
self<suc zero = z<s
self<suc (suc n) = s<s (self<suc n)

var-candidate-member-shape :
  ∀ {limit Φᴸ Φᴿ A B C} →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ A B limit →
  ∃[ W ]
    (C ≡ ＇ W ×
     W < limit ×
     varCandidate? Φᴸ Φᴿ A B W ≡ true)
var-candidate-member-shape {limit = zero} ()
var-candidate-member-shape
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B} C∈
    with varCandidate? Φᴸ Φᴿ A B n in ok
var-candidate-member-shape
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B} C∈
    | true
    with ∈-++-split C∈
var-candidate-member-shape
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B} C∈
    | true | inj₁ C∈old =
  let W , eq , W<n , candidate = var-candidate-member-shape C∈old in
  W , eq , <-trans W<n (self<suc n) , candidate
var-candidate-member-shape
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B} C∈
    | true | inj₂ (here refl) =
  n , refl , self<suc n , ok
var-candidate-member-shape
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B} C∈
    | true | inj₂ (there ())
var-candidate-member-shape
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B} C∈
    | false =
  let W , eq , W<n , candidate = var-candidate-member-shape C∈ in
  W , eq , <-trans W<n (self<suc n) , candidate

flip-enum-route :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C →
  EnumRoute fuel Φᴿ Φᴸ Δᶜ Δᴿ Δᴸ B A C
flip-enum-route (route-both route) =
  route-both (flip-enum-route route)
flip-enum-route (route-left occ route) =
  route-right occ (flip-enum-route route)
flip-enum-route (route-right occ route) =
  route-left occ (flip-enum-route route)
flip-enum-route (route-arrow route₁ route₂) =
  route-arrow (flip-enum-route route₁) (flip-enum-route route₂)
flip-enum-route (route-arrow-star route₁ route₂) =
  route-star-arrow (flip-enum-route route₁) (flip-enum-route route₂)
flip-enum-route (route-star-arrow route₁ route₂) =
  route-arrow-star (flip-enum-route route₁) (flip-enum-route route₂)
flip-enum-route route-star = route-star
flip-enum-route route-base = route-base
flip-enum-route route-base-star = route-star-base
flip-enum-route route-star-base = route-base-star
flip-enum-route
    {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {A = ＇ X} {B = ＇ Y} (route-vars C∈)
    with var-candidate-member-shape
      {limit = Δᶜ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {A = ＇ X} {B = ＇ Y} C∈
flip-enum-route {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = ＇ X} {B = ＇ Y}
    (route-vars C∈) | W , refl , W<Δ , ok
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasVar W X Φᴸ}
      {b = proof.EndpointCanonicalMLBSimple.hasVar W Y Φᴿ} ok
flip-enum-route {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = ＇ X} {B = ＇ Y}
    (route-vars C∈) | W , refl , W<Δ , ok
    | W⊑X , W⊑Y =
  route-vars
    (varCandidatesUpTo-complete W<Δ
      (varCandidate-var-var-complete
        { Φᴸ = Φᴿ} {Φᴿ = Φᴸ} {X = Y} {Y = X} {X′ = W}
        (hasVar-sound W⊑Y) (hasVar-sound W⊑X)))
flip-enum-route
    {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {A = ＇ X} {B = ★} (route-var-star C∈)
    with var-candidate-member-shape
      {limit = Δᶜ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {A = ＇ X} {B = ★} C∈
flip-enum-route {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = ＇ X} {B = ★}
    (route-var-star C∈) | W , refl , W<Δ , ok
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasVar W X Φᴸ}
      {b = proof.EndpointCanonicalMLBSimple.hasStar W Φᴿ} ok
flip-enum-route {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = ＇ X} {B = ★}
    (route-var-star C∈) | W , refl , W<Δ , ok
    | W⊑X , W⊑★ =
  route-star-var
    (varCandidatesUpTo-complete W<Δ
      (varCandidate-star-var-complete
        {Φᴸ = Φᴿ} {Φᴿ = Φᴸ} {Y = X} {X′ = W}
        (hasStar-sound W⊑★) (hasVar-sound W⊑X)))
flip-enum-route
    {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {A = ★} {B = ＇ Y} (route-star-var C∈)
    with var-candidate-member-shape
      {limit = Δᶜ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {A = ★} {B = ＇ Y} C∈
flip-enum-route {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = ★} {B = ＇ Y}
    (route-star-var C∈) | W , refl , W<Δ , ok
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasStar W Φᴸ}
      {b = proof.EndpointCanonicalMLBSimple.hasVar W Y Φᴿ} ok
flip-enum-route {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = ★} {B = ＇ Y}
    (route-star-var C∈) | W , refl , W<Δ , ok
    | W⊑★ , W⊑Y =
  route-var-star
    (varCandidatesUpTo-complete W<Δ
      (varCandidate-var-star-complete
        {Φᴸ = Φᴿ} {Φᴿ = Φᴸ} {X = Y} {X′ = W}
        (hasVar-sound W⊑Y) (hasStar-sound W⊑★)))

transport-star-source :
  ∀ {Φ W X} →
  W ≡ X →
  (W ˣ⊑★) ∈ Φ →
  (X ˣ⊑★) ∈ Φ
transport-star-source refl W⊑★ = W⊑★

terminal-var-star-incompatible :
  ∀ {modes Δ fuel X L R C} →
  LeftOrigin modes X bothᵉ L →
  RightOrigin modes X bothᵉ R →
  EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    (＇ L) ★ C →
  ⊥
terminal-var-star-incompatible
    {modes = modes} {Δ = Δ} left-origin right-origin
    (route-var-star C∈)
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ _} {B = ★} C∈
terminal-var-star-incompatible
    {modes = modes} {Δ = Δ} left-origin right-origin
    (route-var-star C∈)
    | W , (refl , (W<limit , candidate))
    with andᵇ-true candidate
terminal-var-star-incompatible
    {modes = modes} {Δ = Δ} left-origin right-origin
    (route-var-star C∈)
    | W , (refl , (W<limit , candidate)) | W⊑L? , W⊑★? =
  right-history-no-star-at-both
    (right-origin-mode right-origin)
    (transport-star-source
      (left-history-var-target-injective modes Δ
        (hasVar-sound W⊑L?) (left-origin-member left-origin))
      (hasStar-sound W⊑★?))

terminal-star-var-incompatible :
  ∀ {modes Δ fuel X L R C} →
  LeftOrigin modes X bothᵉ L →
  RightOrigin modes X bothᵉ R →
  EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    ★ (＇ R) C →
  ⊥
terminal-star-var-incompatible
    {modes = modes} {Δ = Δ} left-origin right-origin
    (route-star-var C∈)
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ★} {B = ＇ _} C∈
terminal-star-var-incompatible
    {modes = modes} {Δ = Δ} left-origin right-origin
    (route-star-var C∈)
    | W , (refl , (W<limit , candidate))
    with andᵇ-true candidate
terminal-star-var-incompatible
    {modes = modes} {Δ = Δ} left-origin right-origin
    (route-star-var C∈)
    | W , (refl , (W<limit , candidate)) | W⊑★? , W⊑R? =
  left-history-no-star-at-both
    (left-origin-mode left-origin)
    (transport-star-source
      (right-history-var-target-injective modes Δ
        (hasVar-sound W⊑R?) (right-origin-member right-origin))
      (hasStar-sound W⊑★?))

history-vars-candidate-unique :
  ∀ {modes Δ limit X Y C D} →
  C ∈ varCandidatesUpTo
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (＇ X) (＇ Y) limit →
  D ∈ varCandidatesUpTo
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (＇ X) (＇ Y) limit →
  C ≡ D
history-vars-candidate-unique
    {modes = modes} {Δ = Δ} {limit = limit} {X = X} {Y = Y} C∈ D∈
    with var-candidate-member-shape
      {limit = limit}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ X} {B = ＇ Y} C∈
       | var-candidate-member-shape
      {limit = limit}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ X} {B = ＇ Y} D∈
history-vars-candidate-unique {modes = modes} {Δ = Δ} C∈ D∈
    | w , (refl , (w<limit , candidateW))
    | z , (refl , (z<limit , candidateZ))
    with andᵇ-true candidateW | andᵇ-true candidateZ
history-vars-candidate-unique {modes = modes} {Δ = Δ} C∈ D∈
    | w , (refl , (w<limit , candidateW))
    | z , (refl , (z<limit , candidateZ))
    | w⊑X? , w⊑Y? | z⊑X? , z⊑Y? =
  cong (λ W → ＇ W)
    (left-history-var-target-injective modes Δ
      (hasVar-sound w⊑X?) (hasVar-sound z⊑X?))

history-var-star-candidate-unique :
  ∀ {modes Δ limit X C D} →
  C ∈ varCandidatesUpTo
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (＇ X) ★ limit →
  D ∈ varCandidatesUpTo
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (＇ X) ★ limit →
  C ≡ D
history-var-star-candidate-unique
    {modes = modes} {Δ = Δ} {limit = limit} {X = X} C∈ D∈
    with var-candidate-member-shape
      {limit = limit}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ X} {B = ★} C∈
       | var-candidate-member-shape
      {limit = limit}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ X} {B = ★} D∈
history-var-star-candidate-unique {modes = modes} {Δ = Δ} C∈ D∈
    | w , (refl , (w<limit , candidateW))
    | z , (refl , (z<limit , candidateZ))
    with andᵇ-true candidateW | andᵇ-true candidateZ
history-var-star-candidate-unique {modes = modes} {Δ = Δ} C∈ D∈
    | w , (refl , (w<limit , candidateW))
    | z , (refl , (z<limit , candidateZ))
    | w⊑X? , w⊑★? | z⊑X? , z⊑★? =
  cong (λ W → ＇ W)
    (left-history-var-target-injective modes Δ
      (hasVar-sound w⊑X?) (hasVar-sound z⊑X?))

history-star-var-candidate-unique :
  ∀ {modes Δ limit Y C D} →
  C ∈ varCandidatesUpTo
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    ★ (＇ Y) limit →
  D ∈ varCandidatesUpTo
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    ★ (＇ Y) limit →
  C ≡ D
history-star-var-candidate-unique
    {modes = modes} {Δ = Δ} {limit = limit} {Y = Y} C∈ D∈
    with var-candidate-member-shape
      {limit = limit}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ★} {B = ＇ Y} C∈
       | var-candidate-member-shape
      {limit = limit}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ★} {B = ＇ Y} D∈
history-star-var-candidate-unique {modes = modes} {Δ = Δ} C∈ D∈
    | w , (refl , (w<limit , candidateW))
    | z , (refl , (z<limit , candidateZ))
    with andᵇ-true candidateW | andᵇ-true candidateZ
history-star-var-candidate-unique {modes = modes} {Δ = Δ} C∈ D∈
    | w , (refl , (w<limit , candidateW))
    | z , (refl , (z<limit , candidateZ))
    | w⊑★? , w⊑Y? | z⊑★? , z⊑Y? =
  cong (λ W → ＇ W)
    (right-history-var-target-injective modes Δ
      (hasVar-sound w⊑Y?) (hasVar-sound z⊑Y?))

history-vars-routes-aligned :
  ∀ {modes Δ fuel X Y C D}
    {route : EnumRoute (suc fuel)
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      (＇ X) (＇ Y) C}
    {route′ : EnumRoute (suc fuel)
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      (＇ X) (＇ Y) D} →
  AlignedRoutes route route′
history-vars-routes-aligned {modes = modes} {Δ = Δ} {X = X} {Y = Y}
    {route = route-vars C∈} {route′ = route-vars D∈}
    with history-vars-candidate-unique
      {modes = modes} {Δ = Δ}
      {limit = apply-common-depth modes Δ} {X = X} {Y = Y} C∈ D∈
history-vars-routes-aligned {modes = modes} {Δ = Δ} {X = X} {Y = Y}
    {route = route-vars C∈} {route′ = route-vars D∈} | refl =
  aligned-vars

history-var-star-routes-aligned :
  ∀ {modes Δ fuel X C D}
    {route : EnumRoute (suc fuel)
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      (＇ X) ★ C}
    {route′ : EnumRoute (suc fuel)
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      (＇ X) ★ D} →
  AlignedRoutes route route′
history-var-star-routes-aligned {modes = modes} {Δ = Δ} {X = X}
    {route = route-var-star C∈} {route′ = route-var-star D∈}
    with history-var-star-candidate-unique
      {modes = modes} {Δ = Δ}
      {limit = apply-common-depth modes Δ} {X = X} C∈ D∈
history-var-star-routes-aligned {modes = modes} {Δ = Δ} {X = X}
    {route = route-var-star C∈} {route′ = route-var-star D∈}
    | refl =
  aligned-var-star

history-star-var-routes-aligned :
  ∀ {modes Δ fuel Y C D}
    {route : EnumRoute (suc fuel)
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      ★ (＇ Y) C}
    {route′ : EnumRoute (suc fuel)
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      ★ (＇ Y) D} →
  AlignedRoutes route route′
history-star-var-routes-aligned {modes = modes} {Δ = Δ} {Y = Y}
    {route = route-star-var C∈} {route′ = route-star-var D∈}
    with history-star-var-candidate-unique
      {modes = modes} {Δ = Δ}
      {limit = apply-common-depth modes Δ} {Y = Y} C∈ D∈
history-star-var-routes-aligned {modes = modes} {Δ = Δ} {Y = Y}
    {route = route-star-var C∈} {route′ = route-star-var D∈}
    | refl =
  aligned-star-var

------------------------------------------------------------------------
-- Leading-forall spine certificates
------------------------------------------------------------------------

data TerminalRoute :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C → Set where
  terminal-star : ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ} →
    TerminalRoute (route-star {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ})
  terminal-base : ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    TerminalRoute
      (route-base {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
  terminal-base-star : ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    TerminalRoute
      (route-base-star {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
  terminal-star-base : ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    TerminalRoute
      (route-star-base {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
  terminal-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ B₁ B₂ C₁ C₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ C₁}
      {route₂ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ C₂} →
    TerminalRoute (route-arrow route₁ route₂)
  terminal-arrow-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ C₁}
      {route₂ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ C₂} →
    TerminalRoute (route-arrow-star route₁ route₂)
  terminal-star-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ C₁}
      {route₂ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ C₂} →
    TerminalRoute (route-star-arrow route₁ route₂)
  terminal-vars :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X Y C}
      {C∈ : C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ} →
    TerminalRoute
      (route-vars
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {Y = Y} {C = C} C∈)
  terminal-var-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X C}
      {C∈ : C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) ★ Δᶜ} →
    TerminalRoute
      (route-var-star
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {C = C} C∈)
  terminal-star-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ Y C}
      {C∈ : C ∈ varCandidatesUpTo Φᴸ Φᴿ ★ (＇ Y) Δᶜ} →
    TerminalRoute
      (route-star-var
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {Y = Y} {C = C} C∈)

data GeneratedSpine (Δ : ℕ) :
    ∀ {modes fuel A B C}
      (route : EnumRoute fuel
        (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
        (apply-common-depth modes Δ)
        (apply-left-depth modes Δ) (apply-right-depth modes Δ)
        A B C) →
    Set where
  spine-terminal :
    ∀ {modes fuel A B C}
      {route : EnumRoute fuel
        (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
        (apply-common-depth modes Δ)
        (apply-left-depth modes Δ) (apply-right-depth modes Δ)
        A B C} →
    TerminalRoute route →
    GeneratedSpine Δ route
  spine-both :
    ∀ {modes fuel A B C}
      {route : EnumRoute fuel
        (apply-left (bothᵉ ∷ modes) (idᵢ Δ))
        (apply-right (bothᵉ ∷ modes) (idᵢ Δ))
        (apply-common-depth (bothᵉ ∷ modes) Δ)
        (apply-left-depth (bothᵉ ∷ modes) Δ)
        (apply-right-depth (bothᵉ ∷ modes) Δ) A B C} →
    GeneratedSpine Δ {modes = bothᵉ ∷ modes} route →
    GeneratedSpine Δ
      (route-both
        {Φᴸ = apply-left modes (idᵢ Δ)}
        {Φᴿ = apply-right modes (idᵢ Δ)}
        {Δᶜ = apply-common-depth modes Δ}
        {Δᴸ = apply-left-depth modes Δ}
        {Δᴿ = apply-right-depth modes Δ} route)
  spine-left :
    ∀ {modes fuel A B C occ}
      {route : EnumRoute fuel
        (apply-left (leftᵉ ∷ modes) (idᵢ Δ))
        (apply-right (leftᵉ ∷ modes) (idᵢ Δ))
        (apply-common-depth (leftᵉ ∷ modes) Δ)
        (apply-left-depth (leftᵉ ∷ modes) Δ)
        (apply-right-depth (leftᵉ ∷ modes) Δ) A B C} →
    GeneratedSpine Δ {modes = leftᵉ ∷ modes} route →
    GeneratedSpine Δ
      (route-left
        {Φᴸ = apply-left modes (idᵢ Δ)}
        {Φᴿ = apply-right modes (idᵢ Δ)}
        {Δᶜ = apply-common-depth modes Δ}
        {Δᴸ = apply-left-depth modes Δ}
        {Δᴿ = apply-right-depth modes Δ} occ route)
  spine-right :
    ∀ {modes fuel A B C occ}
      {route : EnumRoute fuel
        (apply-left (rightᵉ ∷ modes) (idᵢ Δ))
        (apply-right (rightᵉ ∷ modes) (idᵢ Δ))
        (apply-common-depth (rightᵉ ∷ modes) Δ)
        (apply-left-depth (rightᵉ ∷ modes) Δ)
        (apply-right-depth (rightᵉ ∷ modes) Δ) A B C} →
    GeneratedSpine Δ {modes = rightᵉ ∷ modes} route →
    GeneratedSpine Δ
      (route-right
        {Φᴸ = apply-left modes (idᵢ Δ)}
        {Φᴿ = apply-right modes (idᵢ Δ)}
        {Δᶜ = apply-common-depth modes Δ}
        {Δᴸ = apply-left-depth modes Δ}
        {Δᴿ = apply-right-depth modes Δ} occ route)

generated-spine :
  ∀ {modes Δ fuel A B C}
    (route : EnumRoute fuel
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ)
      A B C) →
  GeneratedSpine Δ route
generated-spine {modes = modes} (route-both route) =
  spine-both {modes = modes}
    (generated-spine {modes = bothᵉ ∷ modes} route)
generated-spine {modes = modes} (route-left occ route) =
  spine-left {modes = modes}
    (generated-spine {modes = leftᵉ ∷ modes} route)
generated-spine {modes = modes} (route-right occ route) =
  spine-right {modes = modes}
    (generated-spine {modes = rightᵉ ∷ modes} route)
generated-spine (route-arrow route₁ route₂) =
  spine-terminal terminal-arrow
generated-spine (route-arrow-star route₁ route₂) =
  spine-terminal terminal-arrow-star
generated-spine (route-star-arrow route₁ route₂) =
  spine-terminal terminal-star-arrow
generated-spine route-star = spine-terminal terminal-star
generated-spine route-base = spine-terminal terminal-base
generated-spine route-base-star = spine-terminal terminal-base-star
generated-spine route-star-base = spine-terminal terminal-star-base
generated-spine (route-vars C∈) = spine-terminal terminal-vars
generated-spine (route-var-star C∈) = spine-terminal terminal-var-star
generated-spine (route-star-var C∈) = spine-terminal terminal-star-var

------------------------------------------------------------------------
-- A used one-sided binder determines a terminal variable/star leaf
------------------------------------------------------------------------

data LeftStarPath : Ty → Ty → TyVar → Set where
  path-left-∀ :
    ∀ {A B X} →
    LeftStarPath A B (suc X) →
    LeftStarPath (`∀ A) B X
  path-right-∀ :
    ∀ {A B X} →
    LeftStarPath A B X →
    LeftStarPath A (`∀ B) X
  path-arrow₁ :
    ∀ {A₁ A₂ B₁ B₂ X} →
    LeftStarPath A₁ B₁ X →
    LeftStarPath (A₁ ⇒ A₂) (B₁ ⇒ B₂) X
  path-arrow₂ :
    ∀ {A₁ A₂ B₁ B₂ X} →
    LeftStarPath A₂ B₂ X →
    LeftStarPath (A₁ ⇒ A₂) (B₁ ⇒ B₂) X
  path-arrow-star₁ :
    ∀ {A₁ A₂ X} →
    LeftStarPath A₁ ★ X →
    LeftStarPath (A₁ ⇒ A₂) ★ X
  path-arrow-star₂ :
    ∀ {A₁ A₂ X} →
    LeftStarPath A₂ ★ X →
    LeftStarPath (A₁ ⇒ A₂) ★ X
  path-var-star : ∀ {X} → LeftStarPath (＇ X) ★ X

remove-right-path :
  ∀ {A B X} →
  LeftStarPath A (`∀ B) X →
  LeftStarPath A B X
remove-right-path (path-left-∀ path) =
  path-left-∀ (remove-right-path path)
remove-right-path (path-right-∀ path) = path

remove-left-path :
  ∀ {A B X} →
  LeftStarPath (`∀ A) B X →
  LeftStarPath A B (suc X)
remove-left-path (path-left-∀ path) = path
remove-left-path (path-right-∀ path) =
  path-right-∀ (remove-left-path path)

no-left-star-path : ∀ {B X} → LeftStarPath ★ B X → ⊥
no-left-star-path (path-right-∀ path) = no-left-star-path path

occurs-var-true→≡ :
  ∀ {X Y} →
  occurs X (＇ Y) ≡ true →
  X ≡ Y
occurs-var-true→≡ {X = X} {Y = Y} occ with X ≟ Y
occurs-var-true→≡ {X = X} {Y = .X} occ | yes refl = refl
occurs-var-true→≡ {X = X} {Y = Y} () | no neq

transport-var-source :
  ∀ {Φ W X Y} →
  W ≡ X →
  (W ˣ⊑ˣ Y) ∈ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
transport-var-source refl W⊑Y = W⊑Y

left-used-path :
  ∀ {modes Δ fuel X L A B C} →
  LeftOrigin modes X leftᵉ L →
  (route : EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A B C) →
  occurs X C ≡ true →
  LeftStarPath A B L
left-used-path origin (route-both route) occ =
  path-left-∀
    (path-right-∀
      (left-used-path
        (left-origin-under-both origin) route occ))
left-used-path origin (route-left route-occ route) occ =
  path-left-∀
    (left-used-path (left-origin-under-left origin) route occ)
left-used-path origin (route-right route-occ route) occ =
  path-right-∀
    (left-used-path (left-origin-under-right origin) route occ)
left-used-path {X = X} origin
    (route-arrow {C₁ = C₁} route₁ route₂) occ
    with occurs X C₁ in occ₁
left-used-path {X = X} origin
    (route-arrow {C₁ = C₁} route₁ route₂) occ | true =
  path-arrow₁ (left-used-path origin route₁ occ₁)
left-used-path {X = X} origin
    (route-arrow {C₁ = C₁} route₁ route₂) occ | false =
  path-arrow₂ (left-used-path origin route₂ occ)
left-used-path {X = X} origin
    (route-arrow-star {C₁ = C₁} route₁ route₂) occ
    with occurs X C₁ in occ₁
left-used-path {X = X} origin
    (route-arrow-star {C₁ = C₁} route₁ route₂) occ | true =
  path-arrow-star₁ (left-used-path origin route₁ occ₁)
left-used-path {X = X} origin
    (route-arrow-star {C₁ = C₁} route₁ route₂) occ | false =
  path-arrow-star₂ (left-used-path origin route₂ occ)
left-used-path {X = X} origin
    (route-star-arrow {C₁ = C₁} route₁ route₂) occ
    with occurs X C₁ in occ₁
left-used-path {X = X} origin
    (route-star-arrow {C₁ = C₁} route₁ route₂) occ | true =
  ⊥-elim (no-left-star-path (left-used-path origin route₁ occ₁))
left-used-path {X = X} origin
    (route-star-arrow {C₁ = C₁} route₁ route₂) occ | false =
  ⊥-elim (no-left-star-path (left-used-path origin route₂ occ))
left-used-path origin route-star ()
left-used-path origin route-base ()
left-used-path origin route-base-star ()
left-used-path origin route-star-base ()
left-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-vars {X = y} {Y = z} C∈) occ
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ y} {B = ＇ z} C∈
left-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-vars {X = y} {Y = z} C∈) occ
    | W , (refl , (W<limit , candidate))
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasVar
        W y (apply-left modes (idᵢ Δ))}
      {b = proof.EndpointCanonicalMLBSimple.hasVar
        W z (apply-right modes (idᵢ Δ))}
      candidate
left-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-vars {X = y} {Y = z} C∈) occ
    | W , (refl , (W<limit , candidate)) | W⊑Y? , W⊑Z? =
  ⊥-elim
    (right-history-no-var-at-left
      (left-origin-mode origin)
      (transport-var-source (sym (occurs-var-true→≡ occ))
        (hasVar-sound W⊑Z?)))
left-used-path {modes = modes} {Δ = Δ} {X = X} {L = L} origin
    (route-var-star {X = y} C∈) occ
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ y} {B = ★} C∈
left-used-path {modes = modes} {Δ = Δ} {X = X} {L = L} origin
    (route-var-star {X = y} C∈) occ
    | W , (refl , (W<limit , candidate))
    with andᵇ-true candidate
left-used-path {modes = modes} {Δ = Δ} {X = X} {L = L} origin
    (route-var-star {X = y} C∈) occ
    | W , (refl , (W<limit , candidate)) | W⊑Y? , W⊑★? =
  subst (λ Z → LeftStarPath (＇ Z) ★ L)
    (sym
      (left-history-var-source-functional modes Δ
        (transport-var-source (sym (occurs-var-true→≡ occ))
          (hasVar-sound W⊑Y?))
        (left-origin-member origin)))
    path-var-star
left-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-star-var {Y = y} C∈) occ
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ★} {B = ＇ y} C∈
left-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-star-var {Y = y} C∈) occ
    | W , (refl , (W<limit , candidate))
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasStar
        W (apply-left modes (idᵢ Δ))}
      {b = proof.EndpointCanonicalMLBSimple.hasVar
        W y (apply-right modes (idᵢ Δ))}
      candidate
left-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-star-var {Y = y} C∈) occ
    | W , (refl , (W<limit , candidate)) | W⊑★? , W⊑Y? =
  ⊥-elim
    (left-history-no-star-at-left
      (left-origin-mode origin)
      (transport-star-source (sym (occurs-var-true→≡ occ))
        (hasStar-sound W⊑★?)))

both-path-incompatible :
  ∀ {modes Δ fuel X L R A B C} →
  LeftOrigin modes X bothᵉ L →
  RightOrigin modes X bothᵉ R →
  (route : EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A B C) →
  LeftStarPath A B L →
  ⊥
both-path-incompatible left-origin right-origin
    (route-both route) (path-left-∀ path) =
  both-path-incompatible
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    route (remove-right-path path)
both-path-incompatible left-origin right-origin
    (route-both route) (path-right-∀ path) =
  both-path-incompatible
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    route (remove-left-path path)
both-path-incompatible left-origin right-origin
    (route-left occ route) (path-left-∀ path) =
  both-path-incompatible
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin)
    route path
both-path-incompatible left-origin right-origin
    (route-left occ route) (path-right-∀ path) =
  both-path-incompatible
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin)
    route (path-right-∀ (remove-left-path path))
both-path-incompatible left-origin right-origin
    (route-right occ route) (path-left-∀ path) =
  both-path-incompatible
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin)
    route (path-left-∀ (remove-right-path path))
both-path-incompatible left-origin right-origin
    (route-right occ route) (path-right-∀ path) =
  both-path-incompatible
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin)
    route path
both-path-incompatible left-origin right-origin
    (route-arrow route₁ route₂) (path-arrow₁ path) =
  both-path-incompatible left-origin right-origin route₁ path
both-path-incompatible left-origin right-origin
    (route-arrow route₁ route₂) (path-arrow₂ path) =
  both-path-incompatible left-origin right-origin route₂ path
both-path-incompatible left-origin right-origin
    (route-arrow-star route₁ route₂) (path-arrow-star₁ path) =
  both-path-incompatible left-origin right-origin route₁ path
both-path-incompatible left-origin right-origin
    (route-arrow-star route₁ route₂) (path-arrow-star₂ path) =
  both-path-incompatible left-origin right-origin route₂ path
both-path-incompatible left-origin right-origin
    (route-star-arrow route₁ route₂) ()
both-path-incompatible {modes = modes} {Δ = Δ} left-origin right-origin
    route@(route-var-star C∈) path-var-star =
  terminal-var-star-incompatible {modes = modes} {Δ = Δ}
    left-origin right-origin route

left-path-used :
  ∀ {modes Δ fuel X L A B C} →
  LeftOrigin modes X leftᵉ L →
  (route : EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A B C) →
  LeftStarPath A B L →
  occurs X C ≡ true
left-path-used origin (route-both route) (path-left-∀ path) =
  left-path-used (left-origin-under-both origin) route
    (remove-right-path path)
left-path-used origin (route-both route) (path-right-∀ path) =
  left-path-used (left-origin-under-both origin) route
    (remove-left-path path)
left-path-used origin (route-left occ route) (path-left-∀ path) =
  left-path-used (left-origin-under-left origin) route path
left-path-used origin (route-left occ route) (path-right-∀ path) =
  left-path-used (left-origin-under-left origin) route
    (path-right-∀ (remove-left-path path))
left-path-used origin (route-right occ route) (path-left-∀ path) =
  left-path-used (left-origin-under-right origin) route
    (path-left-∀ (remove-right-path path))
left-path-used origin (route-right occ route) (path-right-∀ path) =
  left-path-used (left-origin-under-right origin) route path
left-path-used origin (route-arrow route₁ route₂) (path-arrow₁ path) =
  ∨-true-left (left-path-used origin route₁ path)
left-path-used origin (route-arrow route₁ route₂) (path-arrow₂ path) =
  ∨-true-right (left-path-used origin route₂ path)
left-path-used origin
    (route-arrow-star route₁ route₂) (path-arrow-star₁ path) =
  ∨-true-left (left-path-used origin route₁ path)
left-path-used origin
    (route-arrow-star route₁ route₂) (path-arrow-star₂ path) =
  ∨-true-right (left-path-used origin route₂ path)
left-path-used origin (route-star-arrow route₁ route₂) ()
left-path-used {modes = modes} {Δ = Δ} {X = X} origin
    (route-var-star {X = y} C∈) path-var-star
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ y} {B = ★} C∈
left-path-used {modes = modes} {Δ = Δ} {X = X} origin
    (route-var-star {X = y} C∈) path-var-star
    | W , (refl , (W<limit , candidate))
    with andᵇ-true candidate
left-path-used {modes = modes} {Δ = Δ} {X = X} origin
    (route-var-star {X = y} C∈) path-var-star
    | W , (refl , (W<limit , candidate)) | W⊑Y? , W⊑★?
    with left-history-var-target-injective modes Δ
      (hasVar-sound W⊑Y?) (left-origin-member origin)
left-path-used {X = X} origin
    (route-var-star C∈) path-var-star
    | .X , (refl , (W<limit , candidate)) | W⊑Y? , W⊑★? | refl =
  occurs-var-refl X

both-left-routes-incompatible :
  ∀ {modes Δ fuel A B C D} →
  EnumRoute fuel
    (apply-left (bothᵉ ∷ modes) (idᵢ Δ))
    (apply-right (bothᵉ ∷ modes) (idᵢ Δ))
    (apply-common-depth (bothᵉ ∷ modes) Δ)
    (apply-left-depth (bothᵉ ∷ modes) Δ)
    (apply-right-depth (bothᵉ ∷ modes) Δ) A B C →
  (occ : occurs zero D ≡ true) →
  EnumRoute fuel
    (apply-left (leftᵉ ∷ modes) (idᵢ Δ))
    (apply-right (leftᵉ ∷ modes) (idᵢ Δ))
    (apply-common-depth (leftᵉ ∷ modes) Δ)
    (apply-left-depth (leftᵉ ∷ modes) Δ)
    (apply-right-depth (leftᵉ ∷ modes) Δ) A (`∀ B) D →
  ⊥
both-left-routes-incompatible {modes = modes} {Δ = Δ}
    both-route occ left-route =
  both-path-incompatible
    {modes = bothᵉ ∷ modes} {Δ = Δ}
    left-origin-both right-origin-both both-route
    (remove-right-path
      (left-used-path
        {modes = leftᵉ ∷ modes} {Δ = Δ}
        left-origin-left left-route occ))

data StarRightPath : Ty → Ty → TyVar → Set where
  star-path-left-∀ :
    ∀ {A B X} →
    StarRightPath A B X →
    StarRightPath (`∀ A) B X
  star-path-right-∀ :
    ∀ {A B X} →
    StarRightPath A B (suc X) →
    StarRightPath A (`∀ B) X
  star-path-arrow₁ :
    ∀ {A₁ A₂ B₁ B₂ X} →
    StarRightPath A₁ B₁ X →
    StarRightPath (A₁ ⇒ A₂) (B₁ ⇒ B₂) X
  star-path-arrow₂ :
    ∀ {A₁ A₂ B₁ B₂ X} →
    StarRightPath A₂ B₂ X →
    StarRightPath (A₁ ⇒ A₂) (B₁ ⇒ B₂) X
  star-path-star-arrow₁ :
    ∀ {B₁ B₂ X} →
    StarRightPath ★ B₁ X →
    StarRightPath ★ (B₁ ⇒ B₂) X
  star-path-star-arrow₂ :
    ∀ {B₁ B₂ X} →
    StarRightPath ★ B₂ X →
    StarRightPath ★ (B₁ ⇒ B₂) X
  star-path-star-var : ∀ {X} → StarRightPath ★ (＇ X) X

flip-left-star-path :
  ∀ {A B X} →
  LeftStarPath A B X →
  StarRightPath B A X
flip-left-star-path (path-left-∀ path) =
  star-path-right-∀ (flip-left-star-path path)
flip-left-star-path (path-right-∀ path) =
  star-path-left-∀ (flip-left-star-path path)
flip-left-star-path (path-arrow₁ path) =
  star-path-arrow₁ (flip-left-star-path path)
flip-left-star-path (path-arrow₂ path) =
  star-path-arrow₂ (flip-left-star-path path)
flip-left-star-path (path-arrow-star₁ path) =
  star-path-star-arrow₁ (flip-left-star-path path)
flip-left-star-path (path-arrow-star₂ path) =
  star-path-star-arrow₂ (flip-left-star-path path)
flip-left-star-path path-var-star = star-path-star-var

remove-right-star-path :
  ∀ {A B X} →
  StarRightPath A (`∀ B) X →
  StarRightPath A B (suc X)
remove-right-star-path (star-path-left-∀ path) =
  star-path-left-∀ (remove-right-star-path path)
remove-right-star-path (star-path-right-∀ path) = path

remove-left-star-path :
  ∀ {A B X} →
  StarRightPath (`∀ A) B X →
  StarRightPath A B X
remove-left-star-path (star-path-left-∀ path) = path
remove-left-star-path (star-path-right-∀ path) =
  star-path-right-∀ (remove-left-star-path path)

no-right-star-path : ∀ {A X} → StarRightPath A ★ X → ⊥
no-right-star-path (star-path-left-∀ path) = no-right-star-path path

right-used-path :
  ∀ {modes Δ fuel X R A B C} →
  RightOrigin modes X rightᵉ R →
  (route : EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A B C) →
  occurs X C ≡ true →
  StarRightPath A B R
right-used-path origin (route-both route) occ =
  star-path-left-∀
    (star-path-right-∀
      (right-used-path
        (right-origin-under-both origin) route occ))
right-used-path origin (route-left route-occ route) occ =
  star-path-left-∀
    (right-used-path (right-origin-under-left origin) route occ)
right-used-path origin (route-right route-occ route) occ =
  star-path-right-∀
    (right-used-path (right-origin-under-right origin) route occ)
right-used-path {X = X} origin
    (route-arrow {C₁ = C₁} route₁ route₂) occ
    with occurs X C₁ in occ₁
right-used-path {X = X} origin
    (route-arrow {C₁ = C₁} route₁ route₂) occ | true =
  star-path-arrow₁ (right-used-path origin route₁ occ₁)
right-used-path {X = X} origin
    (route-arrow {C₁ = C₁} route₁ route₂) occ | false =
  star-path-arrow₂ (right-used-path origin route₂ occ)
right-used-path {X = X} origin
    (route-arrow-star {C₁ = C₁} route₁ route₂) occ
    with occurs X C₁ in occ₁
right-used-path {X = X} origin
    (route-arrow-star {C₁ = C₁} route₁ route₂) occ | true =
  ⊥-elim (no-right-star-path (right-used-path origin route₁ occ₁))
right-used-path {X = X} origin
    (route-arrow-star {C₁ = C₁} route₁ route₂) occ | false =
  ⊥-elim (no-right-star-path (right-used-path origin route₂ occ))
right-used-path {X = X} origin
    (route-star-arrow {C₁ = C₁} route₁ route₂) occ
    with occurs X C₁ in occ₁
right-used-path {X = X} origin
    (route-star-arrow {C₁ = C₁} route₁ route₂) occ | true =
  star-path-star-arrow₁ (right-used-path origin route₁ occ₁)
right-used-path {X = X} origin
    (route-star-arrow {C₁ = C₁} route₁ route₂) occ | false =
  star-path-star-arrow₂ (right-used-path origin route₂ occ)
right-used-path origin route-star ()
right-used-path origin route-base ()
right-used-path origin route-base-star ()
right-used-path origin route-star-base ()
right-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-vars {X = y} {Y = z} C∈) occ
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ y} {B = ＇ z} C∈
right-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-vars {X = y} {Y = z} C∈) occ
    | W , (refl , (W<limit , candidate))
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasVar
        W y (apply-left modes (idᵢ Δ))}
      {b = proof.EndpointCanonicalMLBSimple.hasVar
        W z (apply-right modes (idᵢ Δ))}
      candidate
right-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-vars {X = y} {Y = z} C∈) occ
    | W , (refl , (W<limit , candidate)) | W⊑Y? , W⊑Z? =
  ⊥-elim
    (left-history-no-var-at-right
      (right-origin-mode origin)
      (transport-var-source (sym (occurs-var-true→≡ occ))
        (hasVar-sound W⊑Y?)))
right-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-var-star {X = y} C∈) occ
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ＇ y} {B = ★} C∈
right-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-var-star {X = y} C∈) occ
    | W , (refl , (W<limit , candidate))
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasVar
        W y (apply-left modes (idᵢ Δ))}
      {b = proof.EndpointCanonicalMLBSimple.hasStar
        W (apply-right modes (idᵢ Δ))}
      candidate
right-used-path {modes = modes} {Δ = Δ} {X = X} origin
    (route-var-star {X = y} C∈) occ
    | W , (refl , (W<limit , candidate)) | W⊑Y? , W⊑★? =
  ⊥-elim
    (right-history-no-star-at-right
      (right-origin-mode origin)
      (transport-star-source (sym (occurs-var-true→≡ occ))
        (hasStar-sound W⊑★?)))
right-used-path {modes = modes} {Δ = Δ} {X = X} {R = R} origin
    (route-star-var {Y = y} C∈) occ
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ★} {B = ＇ y} C∈
right-used-path {modes = modes} {Δ = Δ} {X = X} {R = R} origin
    (route-star-var {Y = y} C∈) occ
    | W , (refl , (W<limit , candidate))
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasStar
        W (apply-left modes (idᵢ Δ))}
      {b = proof.EndpointCanonicalMLBSimple.hasVar
        W y (apply-right modes (idᵢ Δ))}
      candidate
right-used-path {modes = modes} {Δ = Δ} {X = X} {R = R} origin
    (route-star-var {Y = y} C∈) occ
    | W , (refl , (W<limit , candidate)) | W⊑★? , W⊑Y? =
  subst (λ Z → StarRightPath ★ (＇ Z) R)
    (sym
      (right-history-var-source-functional modes Δ
        (transport-var-source (sym (occurs-var-true→≡ occ))
          (hasVar-sound W⊑Y?))
        (right-origin-member origin)))
    star-path-star-var

right-star-path-used :
  ∀ {modes Δ fuel X R A B C} →
  RightOrigin modes X rightᵉ R →
  (route : EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A B C) →
  StarRightPath A B R →
  occurs X C ≡ true
right-star-path-used origin (route-both route)
    (star-path-left-∀ path) =
  right-star-path-used (right-origin-under-both origin) route
    (remove-right-star-path path)
right-star-path-used origin (route-both route)
    (star-path-right-∀ path) =
  right-star-path-used (right-origin-under-both origin) route
    (remove-left-star-path path)
right-star-path-used origin (route-left occ route)
    (star-path-left-∀ path) =
  right-star-path-used (right-origin-under-left origin) route path
right-star-path-used origin (route-left occ route)
    (star-path-right-∀ path) =
  right-star-path-used (right-origin-under-left origin) route
    (star-path-right-∀ (remove-left-star-path path))
right-star-path-used origin (route-right occ route)
    (star-path-left-∀ path) =
  right-star-path-used (right-origin-under-right origin) route
    (star-path-left-∀ (remove-right-star-path path))
right-star-path-used origin (route-right occ route)
    (star-path-right-∀ path) =
  right-star-path-used (right-origin-under-right origin) route path
right-star-path-used origin (route-arrow route₁ route₂)
    (star-path-arrow₁ path) =
  ∨-true-left (right-star-path-used origin route₁ path)
right-star-path-used origin (route-arrow route₁ route₂)
    (star-path-arrow₂ path) =
  ∨-true-right (right-star-path-used origin route₂ path)
right-star-path-used origin (route-arrow-star route₁ route₂) ()
right-star-path-used origin (route-star-arrow route₁ route₂)
    (star-path-star-arrow₁ path) =
  ∨-true-left (right-star-path-used origin route₁ path)
right-star-path-used origin (route-star-arrow route₁ route₂)
    (star-path-star-arrow₂ path) =
  ∨-true-right (right-star-path-used origin route₂ path)
right-star-path-used {modes = modes} {Δ = Δ} {X = X} origin
    (route-star-var {Y = y} C∈) star-path-star-var
    with var-candidate-member-shape
      {limit = apply-common-depth modes Δ}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {A = ★} {B = ＇ y} C∈
right-star-path-used {modes = modes} {Δ = Δ} {X = X} origin
    (route-star-var {Y = y} C∈) star-path-star-var
    | W , refl , W<limit , candidate
    with andᵇ-true
      {a = proof.EndpointCanonicalMLBSimple.hasStar
        W (apply-left modes (idᵢ Δ))}
      {b = proof.EndpointCanonicalMLBSimple.hasVar
        W y (apply-right modes (idᵢ Δ))} candidate
right-star-path-used {modes = modes} {Δ = Δ} {X = X} origin
    (route-star-var C∈) star-path-star-var
    | W , refl , W<limit , candidate | W⊑★? , W⊑Y?
    with right-history-var-target-injective modes Δ
      (hasVar-sound W⊑Y?) (right-origin-member origin)
right-star-path-used {X = X} origin
    (route-star-var C∈) star-path-star-var
    | .X , refl , W<limit , candidate | W⊑★? , W⊑Y? | refl =
  occurs-var-refl X

both-star-path-incompatible :
  ∀ {modes Δ fuel X L R A B C} →
  LeftOrigin modes X bothᵉ L →
  RightOrigin modes X bothᵉ R →
  (route : EnumRoute fuel
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A B C) →
  StarRightPath A B R →
  ⊥
both-star-path-incompatible left-origin right-origin
    (route-both route) (star-path-left-∀ path) =
  both-star-path-incompatible
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    route (remove-right-star-path path)
both-star-path-incompatible left-origin right-origin
    (route-both route) (star-path-right-∀ path) =
  both-star-path-incompatible
    (left-origin-under-both left-origin)
    (right-origin-under-both right-origin)
    route (remove-left-star-path path)
both-star-path-incompatible left-origin right-origin
    (route-left occ route) (star-path-left-∀ path) =
  both-star-path-incompatible
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin)
    route path
both-star-path-incompatible left-origin right-origin
    (route-left occ route) (star-path-right-∀ path) =
  both-star-path-incompatible
    (left-origin-under-left left-origin)
    (right-origin-under-left right-origin)
    route (star-path-right-∀ (remove-left-star-path path))
both-star-path-incompatible left-origin right-origin
    (route-right occ route) (star-path-left-∀ path) =
  both-star-path-incompatible
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin)
    route (star-path-left-∀ (remove-right-star-path path))
both-star-path-incompatible left-origin right-origin
    (route-right occ route) (star-path-right-∀ path) =
  both-star-path-incompatible
    (left-origin-under-right left-origin)
    (right-origin-under-right right-origin)
    route path
both-star-path-incompatible left-origin right-origin
    (route-arrow route₁ route₂) (star-path-arrow₁ path) =
  both-star-path-incompatible left-origin right-origin route₁ path
both-star-path-incompatible left-origin right-origin
    (route-arrow route₁ route₂) (star-path-arrow₂ path) =
  both-star-path-incompatible left-origin right-origin route₂ path
both-star-path-incompatible left-origin right-origin
    (route-arrow-star route₁ route₂) ()
both-star-path-incompatible left-origin right-origin
    (route-star-arrow route₁ route₂) (star-path-star-arrow₁ path) =
  both-star-path-incompatible left-origin right-origin route₁ path
both-star-path-incompatible left-origin right-origin
    (route-star-arrow route₁ route₂) (star-path-star-arrow₂ path) =
  both-star-path-incompatible left-origin right-origin route₂ path
both-star-path-incompatible {modes = modes} {Δ = Δ}
    left-origin right-origin route@(route-star-var C∈)
    star-path-star-var =
  terminal-star-var-incompatible {modes = modes} {Δ = Δ}
    left-origin right-origin route

both-right-routes-incompatible :
  ∀ {modes Δ fuel A B C D} →
  EnumRoute fuel
    (apply-left (bothᵉ ∷ modes) (idᵢ Δ))
    (apply-right (bothᵉ ∷ modes) (idᵢ Δ))
    (apply-common-depth (bothᵉ ∷ modes) Δ)
    (apply-left-depth (bothᵉ ∷ modes) Δ)
    (apply-right-depth (bothᵉ ∷ modes) Δ) A B C →
  (occ : occurs zero D ≡ true) →
  EnumRoute fuel
    (apply-left (rightᵉ ∷ modes) (idᵢ Δ))
    (apply-right (rightᵉ ∷ modes) (idᵢ Δ))
    (apply-common-depth (rightᵉ ∷ modes) Δ)
    (apply-left-depth (rightᵉ ∷ modes) Δ)
    (apply-right-depth (rightᵉ ∷ modes) Δ) (`∀ A) B D →
  ⊥
both-right-routes-incompatible {modes = modes} {Δ = Δ}
    both-route occ right-route =
  both-star-path-incompatible
    {modes = bothᵉ ∷ modes} {Δ = Δ}
    left-origin-both right-origin-both both-route
    (remove-left-star-path
      (right-used-path
        {modes = rightᵉ ∷ modes} {Δ = Δ}
        right-origin-right right-route occ))

------------------------------------------------------------------------
-- Connectivity for routes with the same exposure schedule
------------------------------------------------------------------------

data SameSchedule :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
    Set where
  same-both :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {route : EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
        (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B C}
      {route′ : EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
        (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B D} →
    SameSchedule route route′ →
    SameSchedule (route-both route) (route-both route′)

  same-left :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {route : EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ)
        (suc Δᶜ) (suc Δᴸ) Δᴿ A B C}
      {route′ : EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ)
        (suc Δᶜ) (suc Δᴸ) Δᴿ A B D} →
    SameSchedule route route′ →
    SameSchedule
      (route-left occC route) (route-left occD route′)

  same-right :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {route : EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
        (suc Δᶜ) Δᴸ (suc Δᴿ) A B C}
      {route′ : EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ)
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ)
        (suc Δᶜ) Δᴸ (suc Δᴿ) A B D} →
    SameSchedule route route′ →
    SameSchedule
      (route-right occC route) (route-right occD route′)

  same-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
        A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ C₁}
      {route₂ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ C₂}
      {route₁′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ D₁}
      {route₂′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ D₂} →
    SameSchedule route₁ route₁′ →
    SameSchedule route₂ route₂′ →
    SameSchedule
      (route-arrow route₁ route₂) (route-arrow route₁′ route₂′)

  same-arrow-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂ D₁ D₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ C₁}
      {route₂ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ C₂}
      {route₁′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ D₁}
      {route₂′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ D₂} →
    SameSchedule route₁ route₁′ →
    SameSchedule route₂ route₂′ →
    SameSchedule
      (route-arrow-star route₁ route₂)
      (route-arrow-star route₁′ route₂′)

  same-star-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ C₁}
      {route₂ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ C₂}
      {route₁′ : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ D₁}
      {route₂′ :
        EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ D₂} →
    SameSchedule route₁ route₁′ →
    SameSchedule route₂ route₂′ →
    SameSchedule
      (route-star-arrow route₁ route₂)
      (route-star-arrow route₁′ route₂′)

  same-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ} →
    SameSchedule
      (route-star {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ}) route-star

  same-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SameSchedule
      (route-base {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
      route-base

  same-base-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SameSchedule
      (route-base-star
        {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
      route-base-star

  same-star-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SameSchedule
      (route-star-base
        {fuel} {Φᴸ} {Φᴿ} {Δᶜ} {Δᴸ} {Δᴿ} {ι})
      route-star-base

  same-vars :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X Y C D}
      {C∈ : C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ}
      {D∈ : D ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ} →
    SameSchedule
      (route-vars
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {Y = Y} {C = C} C∈)
      (route-vars
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {Y = Y} {C = D} D∈)

  same-var-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X C D}
      {C∈ : C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) ★ Δᶜ}
      {D∈ : D ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) ★ Δᶜ} →
    SameSchedule
      (route-var-star
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {C = C} C∈)
      (route-var-star
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {X = X} {C = D} D∈)

  same-star-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ Y C D}
      {C∈ : C ∈ varCandidatesUpTo Φᴸ Φᴿ ★ (＇ Y) Δᶜ}
      {D∈ : D ∈ varCandidatesUpTo Φᴸ Φᴿ ★ (＇ Y) Δᶜ} →
    SameSchedule
      (route-star-var
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {Y = Y} {C = C} C∈)
      (route-star-var
        {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
        {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        {Y = Y} {C = D} D∈)

same-schedule-aligned :
  ∀ {modes Δ fuel A B C D}
    {route : EnumRoute fuel
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ) A B C}
    {route′ : EnumRoute fuel
      (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
      (apply-common-depth modes Δ)
      (apply-left-depth modes Δ) (apply-right-depth modes Δ) A B D} →
  SameSchedule route route′ →
  AlignedRoutes route route′
same-schedule-aligned {modes = modes} {Δ = Δ} (same-both same) =
  aligned-both
    (same-schedule-aligned {modes = bothᵉ ∷ modes} {Δ = Δ} same)
same-schedule-aligned {modes = modes} {Δ = Δ} (same-left same) =
  aligned-left
    (same-schedule-aligned {modes = leftᵉ ∷ modes} {Δ = Δ} same)
same-schedule-aligned {modes = modes} {Δ = Δ} (same-right same) =
  aligned-right
    (same-schedule-aligned {modes = rightᵉ ∷ modes} {Δ = Δ} same)
same-schedule-aligned {modes = modes} {Δ = Δ}
    (same-arrow same₁ same₂) =
  aligned-arrow
    (same-schedule-aligned {modes = modes} {Δ = Δ} same₁)
    (same-schedule-aligned {modes = modes} {Δ = Δ} same₂)
same-schedule-aligned {modes = modes} {Δ = Δ}
    (same-arrow-star same₁ same₂) =
  aligned-arrow-star
    (same-schedule-aligned {modes = modes} {Δ = Δ} same₁)
    (same-schedule-aligned {modes = modes} {Δ = Δ} same₂)
same-schedule-aligned {modes = modes} {Δ = Δ}
    (same-star-arrow same₁ same₂) =
  aligned-star-arrow
    (same-schedule-aligned {modes = modes} {Δ = Δ} same₁)
    (same-schedule-aligned {modes = modes} {Δ = Δ} same₂)
same-schedule-aligned same-star = aligned-star
same-schedule-aligned same-base = aligned-base
same-schedule-aligned same-base-star = aligned-base-star
same-schedule-aligned same-star-base = aligned-star-base
same-schedule-aligned {modes = modes} {Δ = Δ} same-vars =
  history-vars-routes-aligned {modes = modes} {Δ = Δ}
same-schedule-aligned {modes = modes} {Δ = Δ} same-var-star =
  history-var-star-routes-aligned {modes = modes} {Δ = Δ}
same-schedule-aligned {modes = modes} {Δ = Δ} same-star-var =
  history-star-var-routes-aligned {modes = modes} {Δ = Δ}

transport-vars-candidate-with :
  ∀ {ρ Φᴸ Φᴿ Ψᴸ Ψᴿ Δᶜ X Y C} →
  CommonTransport ρ Φᴸ Ψᴸ →
  CommonTransport ρ Φᴿ Ψᴿ →
  (∀ {W} → W < Δᶜ → ρ W < Δᶜ) →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ →
  renameᵗ ρ C ∈ varCandidatesUpTo Ψᴸ Ψᴿ (＇ X) (＇ Y) Δᶜ
transport-vars-candidate-with
    {ρ = ρ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ} {X = X} {Y = Y}
    left-transport right-transport pres C∈
    with var-candidate-member-shape
      {limit = Δᶜ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {A = ＇ X} {B = ＇ Y} C∈
transport-vars-candidate-with
    left-transport right-transport pres C∈
    | W , (refl , (W<Δ , candidate))
    with andᵇ-true candidate
transport-vars-candidate-with
    left-transport right-transport pres C∈
    | W , (refl , (W<Δ , candidate)) | W⊑X? , W⊑Y? =
  varCandidatesUpTo-complete
    (pres W<Δ)
    (varCandidate-var-var-complete
      (transport-var left-transport (hasVar-sound W⊑X?))
      (transport-var right-transport (hasVar-sound W⊑Y?)))

transport-var-star-candidate-with :
  ∀ {ρ Φᴸ Φᴿ Ψᴸ Ψᴿ Δᶜ X C} →
  CommonTransport ρ Φᴸ Ψᴸ →
  CommonTransport ρ Φᴿ Ψᴿ →
  (∀ {W} → W < Δᶜ → ρ W < Δᶜ) →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) ★ Δᶜ →
  renameᵗ ρ C ∈ varCandidatesUpTo Ψᴸ Ψᴿ (＇ X) ★ Δᶜ
transport-var-star-candidate-with
    {ρ = ρ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ} {X = X}
    left-transport right-transport pres C∈
    with var-candidate-member-shape
      {limit = Δᶜ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {A = ＇ X} {B = ★} C∈
transport-var-star-candidate-with
    left-transport right-transport pres C∈
    | W , (refl , (W<Δ , candidate))
    with andᵇ-true candidate
transport-var-star-candidate-with
    left-transport right-transport pres C∈
    | W , (refl , (W<Δ , candidate)) | W⊑X? , W⊑★? =
  varCandidatesUpTo-complete
    (pres W<Δ)
    (varCandidate-var-star-complete
      (transport-var left-transport (hasVar-sound W⊑X?))
      (transport-star right-transport (hasStar-sound W⊑★?)))

transport-star-var-candidate-with :
  ∀ {ρ Φᴸ Φᴿ Ψᴸ Ψᴿ Δᶜ Y C} →
  CommonTransport ρ Φᴸ Ψᴸ →
  CommonTransport ρ Φᴿ Ψᴿ →
  (∀ {W} → W < Δᶜ → ρ W < Δᶜ) →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ ★ (＇ Y) Δᶜ →
  renameᵗ ρ C ∈ varCandidatesUpTo Ψᴸ Ψᴿ ★ (＇ Y) Δᶜ
transport-star-var-candidate-with
    {ρ = ρ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ} {Y = Y}
    left-transport right-transport pres C∈
    with var-candidate-member-shape
      {limit = Δᶜ} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {A = ★} {B = ＇ Y} C∈
transport-star-var-candidate-with
    left-transport right-transport pres C∈
    | W , (refl , (W<Δ , candidate))
    with andᵇ-true candidate
transport-star-var-candidate-with
    left-transport right-transport pres C∈
    | W , (refl , (W<Δ , candidate)) | W⊑★? , W⊑Y? =
  varCandidatesUpTo-complete
    (pres W<Δ)
    (varCandidate-star-var-complete
      (transport-star left-transport (hasStar-sound W⊑★?))
      (transport-var right-transport (hasVar-sound W⊑Y?)))

transport-enum-route :
  ∀ {ρ fuel Φᴸ Φᴿ Ψᴸ Ψᴿ Δᶜ Δᴸ Δᴿ A B C} →
  CommonTransport ρ Φᴸ Ψᴸ →
  CommonTransport ρ Φᴿ Ψᴿ →
  (∀ {W} → W < Δᶜ → ρ W < Δᶜ) →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C →
  EnumRoute fuel Ψᴸ Ψᴿ Δᶜ Δᴸ Δᴿ A B (renameᵗ ρ C)
transport-enum-route left-transport right-transport pres
    (route-both route) =
  route-both
    (transport-enum-route
      (transport-∀ left-transport) (transport-∀ right-transport)
      (TyRenameWf-ext pres) route)
transport-enum-route {ρ = ρ} left-transport right-transport pres
    (route-left {C = C} occ route) =
  route-left
    (trans (occurs-zero-rename-ext ρ C) occ)
    (transport-enum-route
      (transport-∀ left-transport) (transport-ν right-transport)
      (TyRenameWf-ext pres) route)
transport-enum-route {ρ = ρ} left-transport right-transport pres
    (route-right {C = C} occ route) =
  route-right
    (trans (occurs-zero-rename-ext ρ C) occ)
    (transport-enum-route
      (transport-ν left-transport) (transport-∀ right-transport)
      (TyRenameWf-ext pres) route)
transport-enum-route left-transport right-transport pres route-star =
  route-star
transport-enum-route left-transport right-transport pres route-base =
  route-base
transport-enum-route left-transport right-transport pres route-base-star =
  route-base-star
transport-enum-route left-transport right-transport pres route-star-base =
  route-star-base
transport-enum-route left-transport right-transport pres
    (route-arrow route₁ route₂) =
  route-arrow
    (transport-enum-route left-transport right-transport pres route₁)
    (transport-enum-route left-transport right-transport pres route₂)
transport-enum-route left-transport right-transport pres
    (route-arrow-star route₁ route₂) =
  route-arrow-star
    (transport-enum-route left-transport right-transport pres route₁)
    (transport-enum-route left-transport right-transport pres route₂)
transport-enum-route left-transport right-transport pres
    (route-star-arrow route₁ route₂) =
  route-star-arrow
    (transport-enum-route left-transport right-transport pres route₁)
    (transport-enum-route left-transport right-transport pres route₂)
transport-enum-route left-transport right-transport pres
    (route-vars C∈) =
  route-vars
    (transport-vars-candidate-with
      left-transport right-transport pres C∈)
transport-enum-route left-transport right-transport pres
    (route-var-star C∈) =
  route-var-star
    (transport-var-star-candidate-with
      left-transport right-transport pres C∈)
transport-enum-route left-transport right-transport pres
    (route-star-var C∈) =
  route-star-var
    (transport-star-var-candidate-with
      left-transport right-transport pres C∈)

swap-route-renamed :
  ∀ {modes fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  EnumRoute fuel
    (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
    (apply-common-depth modes (suc (suc Δᶜ)))
    (apply-left-depth modes (suc Δᴸ))
    (apply-right-depth modes (suc Δᴿ)) A B C →
  EnumRoute fuel
    (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
    (apply-common-depth modes (suc (suc Δᶜ)))
    (apply-left-depth modes (suc Δᴸ))
    (apply-right-depth modes (suc Δᴿ))
    A B (renameᵗ (swap-under modes) C)
swap-route-renamed {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} =
  transport-enum-route
    (left-context-transport modes Φᴸ)
    (right-context-transport modes Φᴿ)
    swap-under-pres-<

transport-vars-candidate :
  ∀ {modes Φᴸ Φᴿ Δᶜ X Y C} →
  C ∈ varCandidatesUpTo
    (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
    (＇ X) (＇ Y)
    (apply-common-depth modes (suc (suc Δᶜ))) →
  renameᵗ (swap-under modes) C ∈ varCandidatesUpTo
    (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
    (＇ X) (＇ Y)
    (apply-common-depth modes (suc (suc Δᶜ)))
transport-vars-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ} C∈
    with var-candidate-member-shape
      {limit = apply-common-depth modes (suc (suc Δᶜ))}
      {Φᴸ = lr-left-context modes Φᴸ}
      {Φᴿ = lr-right-context modes Φᴿ}
      C∈
transport-vars-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} C∈
    | W , (refl , (W<Δ , candidate))
    with andᵇ-true candidate
transport-vars-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} C∈
    | W , (refl , (W<Δ , candidate)) | W⊑X? , W⊑Y? =
  varCandidatesUpTo-complete
    (swap-under-pres-< W<Δ)
    (varCandidate-var-var-complete
      (transport-var (left-context-transport modes Φᴸ)
        (hasVar-sound W⊑X?))
      (transport-var (right-context-transport modes Φᴿ)
        (hasVar-sound W⊑Y?)))

transport-var-star-candidate :
  ∀ {modes Φᴸ Φᴿ Δᶜ X C} →
  C ∈ varCandidatesUpTo
    (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
    (＇ X) ★
    (apply-common-depth modes (suc (suc Δᶜ))) →
  renameᵗ (swap-under modes) C ∈ varCandidatesUpTo
    (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
    (＇ X) ★
    (apply-common-depth modes (suc (suc Δᶜ)))
transport-var-star-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ} C∈
    with var-candidate-member-shape
      {limit = apply-common-depth modes (suc (suc Δᶜ))}
      {Φᴸ = lr-left-context modes Φᴸ}
      {Φᴿ = lr-right-context modes Φᴿ}
      C∈
transport-var-star-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} C∈
    | W , (refl , (W<Δ , candidate))
    with andᵇ-true candidate
transport-var-star-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} C∈
    | W , (refl , (W<Δ , candidate)) | W⊑X? , W⊑★? =
  varCandidatesUpTo-complete
    (swap-under-pres-< W<Δ)
    (varCandidate-var-star-complete
      (transport-var (left-context-transport modes Φᴸ)
        (hasVar-sound W⊑X?))
      (transport-star (right-context-transport modes Φᴿ)
        (hasStar-sound W⊑★?)))

transport-star-var-candidate :
  ∀ {modes Φᴸ Φᴿ Δᶜ Y C} →
  C ∈ varCandidatesUpTo
    (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
    ★ (＇ Y)
    (apply-common-depth modes (suc (suc Δᶜ))) →
  renameᵗ (swap-under modes) C ∈ varCandidatesUpTo
    (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
    ★ (＇ Y)
    (apply-common-depth modes (suc (suc Δᶜ)))
transport-star-var-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ} C∈
    with var-candidate-member-shape
      {limit = apply-common-depth modes (suc (suc Δᶜ))}
      {Φᴸ = lr-left-context modes Φᴸ}
      {Φᴿ = lr-right-context modes Φᴿ}
      C∈
transport-star-var-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} C∈
    | W , (refl , (W<Δ , candidate))
    with andᵇ-true candidate
transport-star-var-candidate
    {modes = modes} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} C∈
    | W , (refl , (W<Δ , candidate)) | W⊑★? , W⊑Y? =
  varCandidatesUpTo-complete
    (swap-under-pres-< W<Δ)
    (varCandidate-star-var-complete
      (transport-star (left-context-transport modes Φᴸ)
        (hasStar-sound W⊑★?))
      (transport-var (right-context-transport modes Φᴿ)
        (hasVar-sound W⊑Y?)))

data SwapAlignedRoutes (modes : List Exposure) :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
    EnumRoute fuel
      (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
      (apply-common-depth modes (suc (suc Δᶜ)))
      (apply-left-depth modes (suc Δᴸ))
      (apply-right-depth modes (suc Δᴿ))
      A B C →
    EnumRoute fuel
      (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
      (apply-common-depth modes (suc (suc Δᶜ)))
      (apply-left-depth modes (suc Δᴸ))
      (apply-right-depth modes (suc Δᴿ))
      A B D →
    Set where
  swap-aligned-both :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
      {route :
        EnumRoute fuel
          (lr-left-context (bothᵉ ∷ modes) Φᴸ)
          (lr-right-context (bothᵉ ∷ modes) Φᴿ)
          (apply-common-depth (bothᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (bothᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (bothᵉ ∷ modes) (suc Δᴿ)) A B C}
      {route′ :
        EnumRoute fuel
          (rl-left-context (bothᵉ ∷ modes) Φᴸ)
          (rl-right-context (bothᵉ ∷ modes) Φᴿ)
          (apply-common-depth (bothᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (bothᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (bothᵉ ∷ modes) (suc Δᴿ)) A B D} →
    SwapAlignedRoutes (bothᵉ ∷ modes) route route′ →
    SwapAlignedRoutes modes (route-both route) (route-both route′)

  swap-aligned-left :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {route :
        EnumRoute fuel
          (lr-left-context (leftᵉ ∷ modes) Φᴸ)
          (lr-right-context (leftᵉ ∷ modes) Φᴿ)
          (apply-common-depth (leftᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (leftᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (leftᵉ ∷ modes) (suc Δᴿ)) A B C}
      {route′ :
        EnumRoute fuel
          (rl-left-context (leftᵉ ∷ modes) Φᴸ)
          (rl-right-context (leftᵉ ∷ modes) Φᴿ)
          (apply-common-depth (leftᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (leftᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (leftᵉ ∷ modes) (suc Δᴿ)) A B D} →
    SwapAlignedRoutes (leftᵉ ∷ modes) route route′ →
    SwapAlignedRoutes modes
      (route-left occC route) (route-left occD route′)

  swap-aligned-right :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D occC occD}
      {route :
        EnumRoute fuel
          (lr-left-context (rightᵉ ∷ modes) Φᴸ)
          (lr-right-context (rightᵉ ∷ modes) Φᴿ)
          (apply-common-depth (rightᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (rightᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (rightᵉ ∷ modes) (suc Δᴿ)) A B C}
      {route′ :
        EnumRoute fuel
          (rl-left-context (rightᵉ ∷ modes) Φᴸ)
          (rl-right-context (rightᵉ ∷ modes) Φᴿ)
          (apply-common-depth (rightᵉ ∷ modes) (suc (suc Δᶜ)))
          (apply-left-depth (rightᵉ ∷ modes) (suc Δᴸ))
          (apply-right-depth (rightᵉ ∷ modes) (suc Δᴿ)) A B D} →
    SwapAlignedRoutes (rightᵉ ∷ modes) route route′ →
    SwapAlignedRoutes modes
      (route-right occC route) (route-right occD route′)

  swap-aligned-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
        A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ B₁ C₁}
      {route₂ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ B₂ C₂}
      {route₁′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ B₁ D₁}
      {route₂′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ B₂ D₂} →
    SwapAlignedRoutes modes route₁ route₁′ →
    SwapAlignedRoutes modes route₂ route₂′ →
    SwapAlignedRoutes modes
      (route-arrow route₁ route₂) (route-arrow route₁′ route₂′)

  swap-aligned-arrow-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂ D₁ D₂}
      {route₁ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ ★ C₁}
      {route₂ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ ★ C₂}
      {route₁′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₁ ★ D₁}
      {route₂′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) A₂ ★ D₂} →
    SwapAlignedRoutes modes route₁ route₁′ →
    SwapAlignedRoutes modes route₂ route₂′ →
    SwapAlignedRoutes modes
      (route-arrow-star route₁ route₂)
      (route-arrow-star route₁′ route₂′)

  swap-aligned-star-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂ D₁ D₂}
      {route₁ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₁ C₁}
      {route₂ :
        EnumRoute fuel
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₂ C₂}
      {route₁′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₁ D₁}
      {route₂′ :
        EnumRoute fuel
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ B₂ D₂} →
    SwapAlignedRoutes modes route₁ route₁′ →
    SwapAlignedRoutes modes route₂ route₂′ →
    SwapAlignedRoutes modes
      (route-star-arrow route₁ route₂)
      (route-star-arrow route₁′ route₂′)

  swap-aligned-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ} →
    SwapAlignedRoutes modes
      (route-star
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)})
      route-star

  swap-aligned-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SwapAlignedRoutes modes
      (route-base
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)} {ι})
      route-base

  swap-aligned-base-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SwapAlignedRoutes modes
      (route-base-star
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)} {ι})
      route-base-star

  swap-aligned-star-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    SwapAlignedRoutes modes
      (route-star-base
        {fuel}
        {lr-left-context modes Φᴸ} {lr-right-context modes Φᴿ}
        {apply-common-depth modes (suc (suc Δᶜ))}
        {apply-left-depth modes (suc Δᴸ)}
        {apply-right-depth modes (suc Δᴿ)} {ι})
      route-star-base

  swap-aligned-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X Y C D}
      {route :
        EnumRoute (suc fuel)
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) (＇ Y) C}
      {route′ :
        EnumRoute (suc fuel)
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) (＇ Y) D} →
    renameᵗ (swap-under modes) C ≡ D →
    SwapAlignedRoutes modes route route′

  swap-aligned-var-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X C D}
      {route :
        EnumRoute (suc fuel)
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) ★ C}
      {route′ :
        EnumRoute (suc fuel)
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) (＇ X) ★ D} →
    renameᵗ (swap-under modes) C ≡ D →
    SwapAlignedRoutes modes route route′

  swap-aligned-star-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ Y C D}
      {route :
        EnumRoute (suc fuel)
          (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ (＇ Y) C}
      {route′ :
        EnumRoute (suc fuel)
          (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
          (apply-common-depth modes (suc (suc Δᶜ)))
          (apply-left-depth modes (suc Δᴸ))
          (apply-right-depth modes (suc Δᴿ)) ★ (＇ Y) D} →
    renameᵗ (swap-under modes) C ≡ D →
    SwapAlignedRoutes modes route route′

swap-route :
  ∀ {modes fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    (route :
      EnumRoute fuel
        (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (apply-right-depth modes (suc Δᴿ)) A B C) →
  Σ[ route′ ∈
      EnumRoute fuel
        (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (apply-right-depth modes (suc Δᴿ))
        A B (renameᵗ (swap-under modes) C) ]
    SwapAlignedRoutes modes route route′
swap-route {modes = modes} (route-both route)
    with swap-route {modes = bothᵉ ∷ modes} route
swap-route {modes = modes} (route-both route)
    | route′ , aligned =
  route-both route′ , swap-aligned-both aligned
swap-route {modes = modes} (route-left {C = C} occ route)
    with swap-route {modes = leftᵉ ∷ modes} route
swap-route {modes = modes} (route-left {C = C} occ route)
    | route′ , aligned =
  route-left
    (trans (occurs-zero-rename-ext (swap-under modes) C) occ)
    route′ ,
  swap-aligned-left aligned
swap-route {modes = modes} (route-right {C = C} occ route)
    with swap-route {modes = rightᵉ ∷ modes} route
swap-route {modes = modes} (route-right {C = C} occ route)
    | route′ , aligned =
  route-right
    (trans (occurs-zero-rename-ext (swap-under modes) C) occ)
    route′ ,
  swap-aligned-right aligned
swap-route {modes = modes} (route-arrow route₁ route₂)
    with swap-route {modes = modes} route₁
       | swap-route {modes = modes} route₂
swap-route {modes = modes} (route-arrow route₁ route₂)
    | route₁′ , aligned₁ | route₂′ , aligned₂ =
  route-arrow route₁′ route₂′ ,
  swap-aligned-arrow aligned₁ aligned₂
swap-route {modes = modes} (route-arrow-star route₁ route₂)
    with swap-route {modes = modes} route₁
       | swap-route {modes = modes} route₂
swap-route {modes = modes} (route-arrow-star route₁ route₂)
    | route₁′ , aligned₁ | route₂′ , aligned₂ =
  route-arrow-star route₁′ route₂′ ,
  swap-aligned-arrow-star aligned₁ aligned₂
swap-route {modes = modes} (route-star-arrow route₁ route₂)
    with swap-route {modes = modes} route₁
       | swap-route {modes = modes} route₂
swap-route {modes = modes} (route-star-arrow route₁ route₂)
    | route₁′ , aligned₁ | route₂′ , aligned₂ =
  route-star-arrow route₁′ route₂′ ,
  swap-aligned-star-arrow aligned₁ aligned₂
swap-route route-star = route-star , swap-aligned-star
swap-route route-base = route-base , swap-aligned-base
swap-route route-base-star = route-base-star , swap-aligned-base-star
swap-route route-star-base = route-star-base , swap-aligned-star-base
swap-route {modes = modes} (route-vars C∈) =
  route-vars (transport-vars-candidate {modes = modes} C∈) ,
  swap-aligned-var refl
swap-route {modes = modes} (route-var-star C∈) =
  route-var-star (transport-var-star-candidate {modes = modes} C∈) ,
  swap-aligned-var-star refl
swap-route {modes = modes} (route-star-var C∈) =
  route-star-var (transport-star-var-candidate {modes = modes} C∈) ,
  swap-aligned-star-var refl

swap-aligned-routes-≈∀ :
  ∀ {modes fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
    {route :
      EnumRoute fuel
        (lr-left-context modes Φᴸ) (lr-right-context modes Φᴿ)
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (apply-right-depth modes (suc Δᴿ)) A B C}
    {route′ :
      EnumRoute fuel
        (rl-left-context modes Φᴸ) (rl-right-context modes Φᴿ)
        (apply-common-depth modes (suc (suc Δᶜ)))
        (apply-left-depth modes (suc Δᴸ))
        (apply-right-depth modes (suc Δᴿ)) A B D} →
  SwapAlignedRoutes modes route route′ →
  renameᵗ (swap-under modes) C ≈∀ D
swap-aligned-routes-≈∀ (swap-aligned-both aligned) =
  ≈∀-∀ (swap-aligned-routes-≈∀ aligned)
swap-aligned-routes-≈∀ (swap-aligned-left aligned) =
  ≈∀-∀ (swap-aligned-routes-≈∀ aligned)
swap-aligned-routes-≈∀ (swap-aligned-right aligned) =
  ≈∀-∀ (swap-aligned-routes-≈∀ aligned)
swap-aligned-routes-≈∀ (swap-aligned-arrow aligned₁ aligned₂) =
  ≈∀-⇒
    (swap-aligned-routes-≈∀ aligned₁)
    (swap-aligned-routes-≈∀ aligned₂)
swap-aligned-routes-≈∀ (swap-aligned-arrow-star aligned₁ aligned₂) =
  ≈∀-⇒
    (swap-aligned-routes-≈∀ aligned₁)
    (swap-aligned-routes-≈∀ aligned₂)
swap-aligned-routes-≈∀ (swap-aligned-star-arrow aligned₁ aligned₂) =
  ≈∀-⇒
    (swap-aligned-routes-≈∀ aligned₁)
    (swap-aligned-routes-≈∀ aligned₂)
swap-aligned-routes-≈∀ swap-aligned-star = ≈∀-refl
swap-aligned-routes-≈∀ swap-aligned-base = ≈∀-refl
swap-aligned-routes-≈∀ swap-aligned-base-star = ≈∀-refl
swap-aligned-routes-≈∀ swap-aligned-star-base = ≈∀-refl
swap-aligned-routes-≈∀ (swap-aligned-var refl) = ≈∀-refl
swap-aligned-routes-≈∀ (swap-aligned-var-star refl) = ≈∀-refl
swap-aligned-routes-≈∀ (swap-aligned-star-var refl) = ≈∀-refl

left-right-swap-alignment-≈∀ :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D}
    {route :
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ))
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ))
        (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B C}
    {route′ :
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ))
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ))
        (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B D} →
  SwapAlignedRoutes [] route route′ →
  `∀ (`∀ C) ≈∀ `∀ (`∀ D)
left-right-swap-alignment-≈∀ aligned =
  ≈∀-double-swap (swap-aligned-routes-≈∀ aligned)

left-right-adjacent-connectivity :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    (occC : occurs zero C ≡ true)
    (occ∀C : occurs zero (`∀ C) ≡ true)
    (route :
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ))
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ))
        (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B C) →
  Σ[ route′ ∈
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ))
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ))
        (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ)
        A B (renameᵗ ForallPermutation.swap01ᵗ C) ]
    AlignedRoutes
      (route-left occ∀C (route-right occC route))
      (route-right
        (occurs-swap01-right {A = C} occC)
        (route-left (occurs-swap01-left {A = C} occ∀C) route′))
left-right-adjacent-connectivity occC occ∀C route
    with swap-route {modes = []} route
left-right-adjacent-connectivity occC occ∀C route
    | route′ , swap-aligned =
  route′ , aligned-left-right ≈∀-refl

right-left-adjacent-connectivity :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    (occC : occurs zero C ≡ true)
    (occ∀C : occurs zero (`∀ C) ≡ true)
    (route :
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴸ))
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴿ))
        (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ) A B C) →
  Σ[ route′ ∈
      EnumRoute fuel
        (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ
          (proof.EndpointCanonicalMLBSimple.νᵢᶜ Φᴸ))
        (proof.EndpointCanonicalMLBSimple.νᵢᶜ
          (proof.EndpointCanonicalMLBSimple.∀ᵢᶜ Φᴿ))
        (suc (suc Δᶜ)) (suc Δᴸ) (suc Δᴿ)
        A B (renameᵗ ForallPermutation.swap01ᵗ C) ]
    AlignedRoutes
      (route-right
        (occurs-swap01-right {A = C} occC)
        (route-left (occurs-swap01-left {A = C} occ∀C) route′))
      (route-left occ∀C (route-right occC route))
right-left-adjacent-connectivity occC occ∀C route
    with left-right-adjacent-connectivity occC occ∀C route
right-left-adjacent-connectivity occC occ∀C route
    | route′ , aligned =
  route′ , aligned-sym aligned

left-right-same-schedule-connectivity :
  ∀ {modes Δ fuel A B C D}
    (occC : occurs zero C ≡ true)
    (occ∀C : occurs zero (`∀ C) ≡ true)
    (occD : occurs zero D ≡ true)
    (occ∀D : occurs zero (`∀ D) ≡ true)
    (route : EnumRoute fuel
      (apply-left (rightᵉ ∷ leftᵉ ∷ modes) (idᵢ Δ))
      (apply-right (rightᵉ ∷ leftᵉ ∷ modes) (idᵢ Δ))
      (apply-common-depth (rightᵉ ∷ leftᵉ ∷ modes) Δ)
      (apply-left-depth (rightᵉ ∷ leftᵉ ∷ modes) Δ)
      (apply-right-depth (rightᵉ ∷ leftᵉ ∷ modes) Δ)
      A B C)
    (route′ : EnumRoute fuel
      (apply-left (leftᵉ ∷ rightᵉ ∷ modes) (idᵢ Δ))
      (apply-right (leftᵉ ∷ rightᵉ ∷ modes) (idᵢ Δ))
      (apply-common-depth (leftᵉ ∷ rightᵉ ∷ modes) Δ)
      (apply-left-depth (leftᵉ ∷ rightᵉ ∷ modes) Δ)
      (apply-right-depth (leftᵉ ∷ rightᵉ ∷ modes) Δ)
      A B D) →
  SameSchedule
    (swap-route-renamed
      {modes = []}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {Δᶜ = apply-common-depth modes Δ}
      {Δᴸ = apply-left-depth modes Δ}
      {Δᴿ = apply-right-depth modes Δ}
      route)
    route′ →
  AlignedRoutes
    (route-left occ∀C (route-right occC route))
    (route-right occ∀D (route-left occD route′))
left-right-same-schedule-connectivity
    {modes = modes} {Δ = Δ}
    occC occ∀C occD occ∀D route route′ same =
  aligned-left-right
    (aligned-routes-≈∀
      (same-schedule-aligned
        {modes = leftᵉ ∷ rightᵉ ∷ modes} {Δ = Δ} same))

right-left-same-schedule-connectivity :
  ∀ {modes Δ fuel A B C D}
    (occC : occurs zero C ≡ true)
    (occ∀C : occurs zero (`∀ C) ≡ true)
    (occD : occurs zero D ≡ true)
    (occ∀D : occurs zero (`∀ D) ≡ true)
    (route : EnumRoute fuel
      (apply-left (rightᵉ ∷ leftᵉ ∷ modes) (idᵢ Δ))
      (apply-right (rightᵉ ∷ leftᵉ ∷ modes) (idᵢ Δ))
      (apply-common-depth (rightᵉ ∷ leftᵉ ∷ modes) Δ)
      (apply-left-depth (rightᵉ ∷ leftᵉ ∷ modes) Δ)
      (apply-right-depth (rightᵉ ∷ leftᵉ ∷ modes) Δ)
      A B C)
    (route′ : EnumRoute fuel
      (apply-left (leftᵉ ∷ rightᵉ ∷ modes) (idᵢ Δ))
      (apply-right (leftᵉ ∷ rightᵉ ∷ modes) (idᵢ Δ))
      (apply-common-depth (leftᵉ ∷ rightᵉ ∷ modes) Δ)
      (apply-left-depth (leftᵉ ∷ rightᵉ ∷ modes) Δ)
      (apply-right-depth (leftᵉ ∷ rightᵉ ∷ modes) Δ)
      A B D) →
  SameSchedule
    (swap-route-renamed
      {modes = []}
      {Φᴸ = apply-left modes (idᵢ Δ)}
      {Φᴿ = apply-right modes (idᵢ Δ)}
      {Δᶜ = apply-common-depth modes Δ}
      {Δᴸ = apply-left-depth modes Δ}
      {Δᴿ = apply-right-depth modes Δ}
      route)
    route′ →
  AlignedRoutes
    (route-right occ∀D (route-left occD route′))
    (route-left occ∀C (route-right occC route))
right-left-same-schedule-connectivity
    {modes = modes} {Δ = Δ}
    occC occ∀C occD occ∀D route route′ same =
  aligned-sym
    (left-right-same-schedule-connectivity
      {modes = modes} {Δ = Δ}
      occC occ∀C occD occ∀D route route′ same)

same-schedule-refl :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C}
    (route : EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C) →
  SameSchedule route route
same-schedule-refl (route-both route) =
  same-both (same-schedule-refl route)
same-schedule-refl (route-left occ route) =
  same-left (same-schedule-refl route)
same-schedule-refl (route-right occ route) =
  same-right (same-schedule-refl route)
same-schedule-refl (route-arrow route₁ route₂) =
  same-arrow (same-schedule-refl route₁) (same-schedule-refl route₂)
same-schedule-refl (route-arrow-star route₁ route₂) =
  same-arrow-star
    (same-schedule-refl route₁) (same-schedule-refl route₂)
same-schedule-refl (route-star-arrow route₁ route₂) =
  same-star-arrow
    (same-schedule-refl route₁) (same-schedule-refl route₂)
same-schedule-refl route-star = same-star
same-schedule-refl route-base = same-base
same-schedule-refl route-base-star = same-base-star
same-schedule-refl route-star-base = same-star-base
same-schedule-refl (route-vars C∈) = same-vars
same-schedule-refl (route-var-star C∈) = same-var-star
same-schedule-refl (route-star-var C∈) = same-star-var

bubble-right-exposure :
  ∀ {modes Δ fuel A B C} →
  StarRightPath A B zero →
  (route : EnumRoute (suc fuel)
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    A (`∀ B) C) →
  Σ[ E ∈ Ty ]
    Σ[ body ∈ EnumRoute fuel
      (apply-left (rightᵉ ∷ modes) (idᵢ Δ))
      (apply-right (rightᵉ ∷ modes) (idᵢ Δ))
      (apply-common-depth (rightᵉ ∷ modes) Δ)
      (apply-left-depth (rightᵉ ∷ modes) Δ)
      (apply-right-depth (rightᵉ ∷ modes) Δ) A B E ]
    Σ[ occE ∈ (occurs zero E ≡ true) ]
      AlignedRoutes route (route-right occE body)
bubble-right-exposure {modes = modes} {Δ = Δ} path
    (route-both body) =
  ⊥-elim
    (both-star-path-incompatible
      {modes = bothᵉ ∷ modes} {Δ = Δ}
      left-origin-both right-origin-both body
      (remove-left-star-path path))
bubble-right-exposure {fuel = zero} path
    (route-left inner-occ ())
bubble-right-exposure
    {modes = modes} {Δ = Δ} {fuel = suc fuel} path
    (route-left inner-occ route)
    with bubble-right-exposure
      {modes = leftᵉ ∷ modes} {Δ = Δ}
      (remove-left-star-path path) route
bubble-right-exposure
    {modes = modes} {Δ = Δ} {fuel = suc fuel} path
    (route-left inner-occ route)
    | E , body , occE , aligned
    with left-right-adjacent-connectivity
      occE inner-occ′ body
  where
    inner-path =
      left-used-path
        {modes = leftᵉ ∷ modes} {Δ = Δ}
        left-origin-left route inner-occ

    inner-occ′ =
      left-path-used
        {modes = leftᵉ ∷ modes} {Δ = Δ}
        left-origin-left (route-right occE body) inner-path
bubble-right-exposure
    {modes = modes} {Δ = Δ} {fuel = suc fuel} path
    (route-left inner-occ route)
    | E , body , occE , aligned | body′ , adjacent =
  `∀ (renameᵗ ForallPermutation.swap01ᵗ E) ,
  route-left
    (occurs-swap01-left {A = E} inner-occ′) body′ ,
  occurs-swap01-right {A = E} occE ,
  aligned-trans (aligned-left aligned) adjacent
  where
    inner-path =
      left-used-path
        {modes = leftᵉ ∷ modes} {Δ = Δ}
        left-origin-left route inner-occ

    inner-occ′ =
      left-path-used
        {modes = leftᵉ ∷ modes} {Δ = Δ}
        left-origin-left (route-right occE body) inner-path
bubble-right-exposure {modes = modes} {Δ = Δ} path
    route@(route-right occ body) =
  _ , body , occ ,
  same-schedule-aligned
    {modes = modes} {Δ = Δ} (same-schedule-refl route)

bubble-left-exposure :
  ∀ {modes Δ fuel A B C} →
  LeftStarPath A B zero →
  EnumRoute (suc fuel)
    (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
    (apply-common-depth modes Δ)
    (apply-left-depth modes Δ) (apply-right-depth modes Δ)
    (`∀ A) B C →
  Σ[ E ∈ Ty ]
    Σ[ body ∈ EnumRoute fuel
      (apply-left (leftᵉ ∷ modes) (idᵢ Δ))
      (apply-right (leftᵉ ∷ modes) (idᵢ Δ))
      (apply-common-depth (leftᵉ ∷ modes) Δ)
      (apply-left-depth (leftᵉ ∷ modes) Δ)
      (apply-right-depth (leftᵉ ∷ modes) Δ) A B E ]
    occurs zero E ≡ true
bubble-left-exposure {modes = modes} {Δ = Δ} path
    (route-both body) =
  ⊥-elim
    (both-path-incompatible
      {modes = bothᵉ ∷ modes} {Δ = Δ}
      left-origin-both right-origin-both body
      (remove-right-path path))
bubble-left-exposure {fuel = zero} path
    (route-right inner-occ ())
bubble-left-exposure
    {modes = modes} {Δ = Δ} {fuel = suc fuel} path
    (route-right inner-occ route)
    with bubble-left-exposure
      {modes = rightᵉ ∷ modes} {Δ = Δ}
      (remove-right-path path) route
bubble-left-exposure
    {modes = modes} {Δ = Δ} {fuel = suc fuel} path
    (route-right inner-occ route)
    | E , body , occE
    with swap-route {modes = []} (flip-enum-route body)
bubble-left-exposure
    {modes = modes} {Δ = Δ} {fuel = suc fuel} path
    (route-right inner-occ route)
    | E , body , occE | body′ , aligned =
  `∀ (renameᵗ ForallPermutation.swap01ᵗ E) ,
  route-right
    (occurs-swap01-left {A = E} inner-occ′)
    (flip-enum-route body′) ,
  occurs-swap01-right {A = E} occE
  where
    inner-path =
      right-used-path
        {modes = rightᵉ ∷ modes} {Δ = Δ}
        right-origin-right route inner-occ

    inner-occ′ =
      right-star-path-used
        {modes = rightᵉ ∷ modes} {Δ = Δ}
        right-origin-right (route-left occE body) inner-path
bubble-left-exposure path (route-left occ body) =
  _ , body , occ

mutual
  generated-routes-aligned :
    ∀ {modes Δ fuel A B C D}
      (route : EnumRoute fuel
        (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
        (apply-common-depth modes Δ)
        (apply-left-depth modes Δ) (apply-right-depth modes Δ)
        A B C)
      (route′ : EnumRoute fuel
        (apply-left modes (idᵢ Δ)) (apply-right modes (idᵢ Δ))
        (apply-common-depth modes Δ)
        (apply-left-depth modes Δ) (apply-right-depth modes Δ)
        A B D) →
    AlignedRoutes route route′
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-both route) (route-both route′) =
    aligned-both
      (generated-routes-aligned
        {modes = bothᵉ ∷ modes} {Δ = Δ} route route′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-both route) (route-left occ route′) =
    ⊥-elim
      (both-left-routes-incompatible
        {modes = modes} {Δ = Δ} route occ route′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-both route) (route-right occ route′) =
    ⊥-elim
      (both-right-routes-incompatible
        {modes = modes} {Δ = Δ} route occ route′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-left occ route) (route-both route′) =
    ⊥-elim
      (both-left-routes-incompatible
        {modes = modes} {Δ = Δ} route′ occ route)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-left occ route) (route-left occ′ route′) =
    aligned-left
      (generated-routes-aligned
        {modes = leftᵉ ∷ modes} {Δ = Δ} route route′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-left occ route) (route-right occ′ route′) =
    left-right-routes-aligned
      {modes = modes} {Δ = Δ} occ route occ′ route′
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-right occ route) (route-both route′) =
    ⊥-elim
      (both-right-routes-incompatible
        {modes = modes} {Δ = Δ} route′ occ route)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-right occ route) (route-left occ′ route′) =
    aligned-sym
      (left-right-routes-aligned
        {modes = modes} {Δ = Δ} occ′ route′ occ route)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-right occ route) (route-right occ′ route′) =
    aligned-right
      (generated-routes-aligned
        {modes = rightᵉ ∷ modes} {Δ = Δ} route route′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-arrow route₁ route₂) (route-arrow route₁′ route₂′) =
    aligned-arrow
      (generated-routes-aligned
        {modes = modes} {Δ = Δ} route₁ route₁′)
      (generated-routes-aligned
        {modes = modes} {Δ = Δ} route₂ route₂′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-arrow-star route₁ route₂)
      (route-arrow-star route₁′ route₂′) =
    aligned-arrow-star
      (generated-routes-aligned
        {modes = modes} {Δ = Δ} route₁ route₁′)
      (generated-routes-aligned
        {modes = modes} {Δ = Δ} route₂ route₂′)
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-star-arrow route₁ route₂)
      (route-star-arrow route₁′ route₂′) =
    aligned-star-arrow
      (generated-routes-aligned
        {modes = modes} {Δ = Δ} route₁ route₁′)
      (generated-routes-aligned
        {modes = modes} {Δ = Δ} route₂ route₂′)
  generated-routes-aligned route-star route-star = aligned-star
  generated-routes-aligned route-base route-base = aligned-base
  generated-routes-aligned route-base-star route-base-star =
    aligned-base-star
  generated-routes-aligned route-star-base route-star-base =
    aligned-star-base
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-vars C∈) (route-vars D∈) =
    same-schedule-aligned
      {modes = modes} {Δ = Δ} same-vars
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-var-star C∈) (route-var-star D∈) =
    same-schedule-aligned
      {modes = modes} {Δ = Δ} same-var-star
  generated-routes-aligned {modes = modes} {Δ = Δ}
      (route-star-var C∈) (route-star-var D∈) =
    same-schedule-aligned
      {modes = modes} {Δ = Δ} same-star-var

  left-right-routes-aligned :
    ∀ {modes Δ fuel A B C D}
      (occC : occurs zero C ≡ true)
      (route : EnumRoute fuel
        (apply-left (leftᵉ ∷ modes) (idᵢ Δ))
        (apply-right (leftᵉ ∷ modes) (idᵢ Δ))
        (apply-common-depth (leftᵉ ∷ modes) Δ)
        (apply-left-depth (leftᵉ ∷ modes) Δ)
        (apply-right-depth (leftᵉ ∷ modes) Δ)
        A (`∀ B) C)
      (occD : occurs zero D ≡ true)
      (route′ : EnumRoute fuel
        (apply-left (rightᵉ ∷ modes) (idᵢ Δ))
        (apply-right (rightᵉ ∷ modes) (idᵢ Δ))
        (apply-common-depth (rightᵉ ∷ modes) Δ)
        (apply-left-depth (rightᵉ ∷ modes) Δ)
        (apply-right-depth (rightᵉ ∷ modes) Δ)
        (`∀ A) B D) →
    AlignedRoutes
      (route-left occC route) (route-right occD route′)
  left-right-routes-aligned {fuel = zero} occC () occD route′
  left-right-routes-aligned
      {modes = modes} {Δ = Δ} {fuel = suc fuel}
      occC route occD route′
      with bubble-right-exposure
        {modes = leftᵉ ∷ modes} {Δ = Δ}
        right-path route
    where
      right-path =
        remove-left-star-path
          (right-used-path
            {modes = rightᵉ ∷ modes} {Δ = Δ}
            right-origin-right route′ occD)
  left-right-routes-aligned
      {modes = modes} {Δ = Δ} {fuel = suc fuel}
      occC route occD route′
      | E , body , occE , bubbled
      with left-right-adjacent-connectivity occE occC′ body
    where
      left-path =
        left-used-path
          {modes = leftᵉ ∷ modes} {Δ = Δ}
          left-origin-left route occC

      occC′ =
        left-path-used
          {modes = leftᵉ ∷ modes} {Δ = Δ}
          left-origin-left (route-right occE body) left-path

  left-right-routes-aligned
      {modes = modes} {Δ = Δ} {fuel = suc fuel}
      occC route occD route′
      | E , body , occE , bubbled | body′ , adjacent =
    aligned-trans (aligned-left bubbled)
      (aligned-trans adjacent
        (aligned-right
          (generated-routes-aligned
            {modes = rightᵉ ∷ modes} {Δ = Δ}
            (route-left
              (occurs-swap01-left {A = E} occC′) body′)
            route′)))
    where
      left-path =
        left-used-path
          {modes = leftᵉ ∷ modes} {Δ = Δ}
          left-origin-left route occC

      occC′ =
        left-path-used
          {modes = leftᵉ ∷ modes} {Δ = Δ}
          left-origin-left (route-right occE body) left-path

rawEndpointMlbsAt-≈∀ :
  ∀ {Δ A B C D} →
  C ∈ rawEndpointMlbsAt Δ A B →
  D ∈ rawEndpointMlbsAt Δ A B →
  C ≈∀ D
rawEndpointMlbsAt-≈∀ {Δ = Δ} {A = A} {B = B} C∈ D∈ =
  aligned-routes-≈∀
    (generated-routes-aligned {modes = []} {Δ = Δ}
      (raw-endpoint-membership→route
        {Δ = Δ} {A = A} {B = B} C∈)
      (raw-endpoint-membership→route
        {Δ = Δ} {A = A} {B = B} D∈))

allEndpointMlbsAt-≈∀ :
  ∀ {Δ A B C D} →
  C ∈ allEndpointMlbsAt Δ A B →
  D ∈ allEndpointMlbsAt Δ A B →
  C ≈∀ D
allEndpointMlbsAt-≈∀ {Δ = Δ} {A = A} {B = B} C∈ D∈ =
  rawEndpointMlbsAt-≈∀
    {Δ = Δ} {A = A} {B = B}
    (dedupe-sound
      {xs = rawEndpointMlbsAt Δ A B}
      (pruneStrictlyBelow-sound C∈))
    (dedupe-sound
      {xs = rawEndpointMlbsAt Δ A B}
      (pruneStrictlyBelow-sound D∈))

module proof.EndpointCanonicalMLBSimpleRoutes where

-- File Charter:
--   * Defines proof-relevant route certificates for the simple exhaustive MLB
--     enumerator.
--   * Proves that route certificates are equivalent to list membership.
--   * Keeps route choices available for the quotient-coherence induction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Imprecision using (NonVar; ImpCtx; idᵢ)
open import proof.EndpointCanonicalMLBSimple using
  ( allEndpointMlbsAt; arrowProducts; dedupe; enumMLB; fuelFor
  ; rawEndpointMlbsAt; MLB
  ; varCandidatesUpTo
  ; wrapAll; wrapAllIfOccurs; ∀ᵢᶜ; νᵢᶜ
  )
open import proof.EndpointCanonicalMLBSimpleCompleteness using
  ( arrowProducts-complete; dedupe-complete; ∈-++-left; ∈-++-right
  ; wrapAll-complete; wrapAllIfOccurs-complete
  )
open import proof.EndpointCanonicalMLBSimpleSoundness using
  ( arrowProducts-sound; dedupe-sound; ∈-++-split
  ; first-sound
  ; forallBothCandidates; leftForallCandidates; rightForallCandidates
  ; pruneStrictlyBelow-sound; wrapAll-sound; wrapAllIfOccurs-sound
  )

------------------------------------------------------------------------
-- Proof-relevant enumeration routes
------------------------------------------------------------------------

data EnumRoute :
    ℕ → ImpCtx → ImpCtx →
    ℕ → ℕ → ℕ → Ty → Ty → Ty → Set where
  route-both :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    EnumRoute fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B C →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (`∀ A) (`∀ B) (`∀ C)

  route-left :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    {{NonVar C}} →
    occurs zero C ≡ true →
    EnumRoute fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B C →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (`∀ A) B (`∀ C)

  route-right :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    {{NonVar C}} →
    occurs zero C ≡ true →
    EnumRoute fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B C →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      A (`∀ B) (`∀ C)

  route-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ} →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ ★ ★

  route-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (‵ ι) (‵ ι) (‵ ι)

  route-base-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) ★ (‵ ι)

  route-star-base :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ι} →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (‵ ι) (‵ ι)

  route-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ B₁ B₂ C₁ C₂} →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁ C₁ →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂ C₂ →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (A₁ ⇒ A₂) (B₁ ⇒ B₂) (C₁ ⇒ C₂)

  route-arrow-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ C₁ C₂} →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★ C₁ →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★ C₂ →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (A₁ ⇒ A₂) ★ (C₁ ⇒ C₂)

  route-star-arrow :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ B₁ B₂ C₁ C₂} →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁ C₁ →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂ C₂ →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      ★ (B₁ ⇒ B₂) (C₁ ⇒ C₂)

  route-vars :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X Y C} →
    C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y) C

  route-var-star :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ X C} →
    C ∈ varCandidatesUpTo Φᴸ Φᴿ (＇ X) ★ Δᶜ →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) ★ C

  route-star-var :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ Y C} →
    C ∈ varCandidatesUpTo Φᴸ Φᴿ ★ (＇ Y) Δᶜ →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (＇ Y) C

------------------------------------------------------------------------
-- Routes imply enumeration membership
------------------------------------------------------------------------

enum-route→membership :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B
enum-route→membership {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = `∀ A} {B = `∀ B} (route-both route) =
  dedupe-complete
    (∈-++-left
      {xs = forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B}
      {ys =
        leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ++
        rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
      (wrapAll-complete (enum-route→membership route)))
enum-route→membership {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = `∀ A} {B = `∀ B} (route-left {{safe}} occ route) =
  dedupe-complete
    (∈-++-right
      {xs = forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B}
      {ys =
        leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ++
        rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
      (∈-++-left
        {xs =
          leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B)}
        {ys =
          rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
        (wrapAllIfOccurs-complete
          safe occ (enum-route→membership route))))
enum-route→membership {B = ＇ Y} (route-left {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {B = ‵ ι} (route-left {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {B = ★} (route-left {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {B = B₁ ⇒ B₂}
    (route-left {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = `∀ A} {B = `∀ B} (route-right {{safe}} occ route) =
  dedupe-complete
    (∈-++-right
      {xs = forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B}
      {ys =
        leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ++
        rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
      (∈-++-right
        {xs =
          leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B)}
        {ys =
          rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
        (wrapAllIfOccurs-complete
          safe occ (enum-route→membership route))))
enum-route→membership {A = ＇ X} (route-right {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {A = ‵ ι} (route-right {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {A = ★} (route-right {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership {A = A₁ ⇒ A₂}
    (route-right {{safe}} occ route) =
  dedupe-complete
    (wrapAllIfOccurs-complete safe occ (enum-route→membership route))
enum-route→membership route-star = here refl
enum-route→membership {A = ‵ ι} {B = ‵ .ι} route-base
    with ι ≟Base ι
enum-route→membership {A = ‵ ι} {B = ‵ .ι} route-base
    | yes refl = here refl
enum-route→membership {A = ‵ ι} {B = ‵ .ι} route-base
    | no neq = ⊥-elim (neq refl)
enum-route→membership route-base-star = here refl
enum-route→membership route-star-base = here refl
enum-route→membership
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    (route-arrow route₁ route₂) =
  arrowProducts-complete
    {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁}
    {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂}
    (enum-route→membership route₁) (enum-route→membership route₂)
enum-route→membership
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    (route-arrow-star route₁ route₂) =
  arrowProducts-complete
    {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★}
    {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★}
    (enum-route→membership route₁) (enum-route→membership route₂)
enum-route→membership
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    (route-star-arrow route₁ route₂) =
  arrowProducts-complete
    {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁}
    {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂}
    (enum-route→membership route₁) (enum-route→membership route₂)
enum-route→membership (route-vars C∈) = C∈
enum-route→membership (route-var-star C∈) = C∈
enum-route→membership (route-star-var C∈) = C∈

------------------------------------------------------------------------
-- Enumeration membership exposes a route
------------------------------------------------------------------------

mutual
  left-membership→route :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    C ∈ dedupe
      (wrapAllIfOccurs
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) Δᴿ A B)) →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B C
  left-membership→route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
      with wrapAllIfOccurs-sound
        {xs =
          enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
            (suc Δᶜ) (suc Δᴸ) Δᴿ A B}
        (dedupe-sound C∈)
  left-membership→route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
      | C₀ , refl , safe , occ , C₀∈ =
    route-left {{safe}} occ (membership→enum-route C₀∈)

  right-membership→route :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    C ∈ dedupe
      (wrapAllIfOccurs
        (enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
          (suc Δᶜ) Δᴸ (suc Δᴿ) A B)) →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) C
  right-membership→route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
      with wrapAllIfOccurs-sound
        {xs =
          enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
            (suc Δᶜ) Δᴸ (suc Δᴿ) A B}
        (dedupe-sound C∈)
  right-membership→route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
      | C₀ , refl , safe , occ , C₀∈ =
    route-right {{safe}} occ (membership→enum-route C₀∈)

  arrow-membership→route :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ A₂ B₁ B₂ C} →
    C ∈ arrowProducts
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁)
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂) →
    EnumRoute (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ
      (A₁ ⇒ A₂) (B₁ ⇒ B₂) C
  arrow-membership→route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} C∈
      with arrowProducts-sound
        {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁}
        {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂}
        C∈
  arrow-membership→route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂} C∈
      | C₁ , (C₂ , (refl , (C₁∈ , C₂∈))) =
    route-arrow
      (membership→enum-route C₁∈) (membership→enum-route C₂∈)

  membership→enum-route :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
    EnumRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C
  membership→enum-route {fuel = zero} ()
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈
      with ∈-++-split
        {xs = forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B}
        {ys =
          leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ++
          rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
        (dedupe-sound C∈)
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₁ C∈both
      with wrapAll-sound
        {xs =
          enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
            (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B}
        C∈both
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₁ C∈both
      | C₀ , (refl , C₀∈) =
    route-both (membership→enum-route C₀∈)
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₂ C∈one
      with ∈-++-split
        {xs =
          leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B)}
        {ys =
          rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
        C∈one
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₂ C∈one
      | inj₁ C∈left
      with wrapAllIfOccurs-sound
        {xs =
          enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
            (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)}
        C∈left
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₂ C∈one
      | inj₁ C∈left | C₀ , refl , safe , occ , C₀∈ =
    route-left {{safe}} occ (membership→enum-route C₀∈)
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₂ C∈one
      | inj₂ C∈right
      with wrapAllIfOccurs-sound
        {xs =
          enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
            (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B}
        C∈right
  membership→enum-route {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      {A = `∀ A} {B = `∀ B} C∈ | inj₂ C∈one
      | inj₂ C∈right | C₀ , refl , safe , occ , C₀∈ =
    route-right {{safe}} occ (membership→enum-route C₀∈)

  membership→enum-route {fuel = suc fuel} {A = `∀ A} {B = ＇ Y} C∈ =
    left-membership→route C∈
  membership→enum-route {fuel = suc fuel} {A = `∀ A} {B = ‵ ι} C∈ =
    left-membership→route C∈
  membership→enum-route {fuel = suc fuel} {A = `∀ A} {B = ★} C∈ =
    left-membership→route C∈
  membership→enum-route
      {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂} C∈ =
    left-membership→route C∈

  membership→enum-route {fuel = suc fuel} {A = ＇ X} {B = `∀ B} C∈ =
    right-membership→route C∈
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = `∀ B} C∈ =
    right-membership→route C∈
  membership→enum-route {fuel = suc fuel} {A = ★} {B = `∀ B} C∈ =
    right-membership→route C∈
  membership→enum-route
      {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B} C∈ =
    right-membership→route C∈

  membership→enum-route {fuel = suc fuel} {A = ★} {B = ★}
      (here refl) = route-star
  membership→enum-route {fuel = suc fuel} {A = ★} {B = ★} (there ())
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ‵ ι′} C∈
      with ι ≟Base ι′
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ‵ .ι}
      (here refl) | yes refl = route-base
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ‵ .ι}
      (there ()) | yes refl
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ‵ ι′}
      () | no neq
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ★}
      (here refl) = route-base-star
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ★} (there ())
  membership→enum-route {fuel = suc fuel} {A = ★} {B = ‵ ι}
      (here refl) = route-star-base
  membership→enum-route {fuel = suc fuel} {A = ★} {B = ‵ ι} (there ())

  membership→enum-route
      {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂} C∈ =
    arrow-membership→route C∈
  membership→enum-route
      {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★} C∈
      with arrowProducts-sound
        {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★}
        {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★}
        C∈
  membership→enum-route
      {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★} C∈
      | C₁ , (C₂ , (refl , (C₁∈ , C₂∈))) =
    route-arrow-star
      (membership→enum-route C₁∈) (membership→enum-route C₂∈)
  membership→enum-route
      {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂} C∈
      with arrowProducts-sound
        {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁}
        {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂}
        C∈
  membership→enum-route
      {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂} C∈
      | C₁ , (C₂ , (refl , (C₁∈ , C₂∈))) =
    route-star-arrow
      (membership→enum-route C₁∈) (membership→enum-route C₂∈)

  membership→enum-route {fuel = suc fuel} {A = ＇ X} {B = ＇ Y} C∈ =
    route-vars C∈
  membership→enum-route {fuel = suc fuel} {A = ＇ X} {B = ★} C∈ =
    route-var-star C∈
  membership→enum-route {fuel = suc fuel} {A = ★} {B = ＇ Y} C∈ =
    route-star-var C∈
  membership→enum-route {fuel = suc fuel} {A = ＇ X} {B = ‵ ι} ()
  membership→enum-route
      {fuel = suc fuel} {A = ＇ X} {B = B₁ ⇒ B₂} ()
  membership→enum-route {fuel = suc fuel} {A = ‵ ι} {B = ＇ Y} ()
  membership→enum-route
      {fuel = suc fuel} {A = ‵ ι} {B = B₁ ⇒ B₂} ()
  membership→enum-route
      {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ＇ Y} ()
  membership→enum-route
      {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ‵ ι} ()

------------------------------------------------------------------------
-- Endpoint specialization
------------------------------------------------------------------------

RawEndpointRoute : ℕ → Ty → Ty → Ty → Set
RawEndpointRoute Δ A B C =
  EnumRoute (fuelFor A B) (idᵢ Δ) (idᵢ Δ)
    Δ Δ Δ A B C

raw-endpoint-route→membership :
  ∀ {Δ A B C} →
  RawEndpointRoute Δ A B C →
  C ∈ rawEndpointMlbsAt Δ A B
raw-endpoint-route→membership = enum-route→membership

raw-endpoint-membership→route :
  ∀ {Δ A B C} →
  C ∈ rawEndpointMlbsAt Δ A B →
  RawEndpointRoute Δ A B C
raw-endpoint-membership→route = membership→enum-route

all-endpoint-membership→route :
  ∀ {Δ A B C} →
  C ∈ allEndpointMlbsAt Δ A B →
  RawEndpointRoute Δ A B C
all-endpoint-membership→route C∈ =
  raw-endpoint-membership→route
    (dedupe-sound (pruneStrictlyBelow-sound C∈))

MLB-result→route :
  ∀ {Δ A B C} →
  MLB Δ A B ≡ just C →
  RawEndpointRoute Δ A B C
MLB-result→route {Δ = Δ} {A = A} {B = B} eq =
  all-endpoint-membership→route
    (first-sound {xs = allEndpointMlbsAt Δ A B} eq)

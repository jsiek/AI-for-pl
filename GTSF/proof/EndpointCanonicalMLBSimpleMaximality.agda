module proof.EndpointCanonicalMLBSimpleMaximality where

-- File Charter:
--   * Maximality proof boundary for the simple exhaustive endpoint MLB
--     algorithm.
--   * Keeps the durable pruning-to-maximality assembly and leaves raw
--     completeness as the current semantic proof frontier.
--   * The next proof plan targets completeness: every common lower bound is
--     below some raw candidate returned by `rawEndpointMlbsAt`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary using (Dec; ¬_; no; yes)

open import Types
open import Imprecision using (ImpCtx; idᵢ)
open import ImprecisionWf
open import proof.EndpointCanonicalMLBSimple using
  ( allEndpointMlbsAt; arrowProducts; dedupe; endpointCtx; enumMLB
  ; fuelFor; hasStar; hasStrictAbove?; hasVar; pruneStrictlyBelow
  ; pruneStrictlyBelowFrom
  ; rawEndpointMlbsAt; simpleEndpointMlb; simpleEndpointMlbAt
  ; strictlyBelow?; varCandidate?; varCandidatesUpTo; wrapAll
  ; wrapAllIfOccurs; _==ᵇ_; ∀ᵢᶜ; νᵢᶜ
  )
open import proof.EndpointCanonicalMLBSimpleSoundness using
  (first-sound; pruneStrictlyBelow-sound; νᵢᶜ-wf²
  )
open import proof.ImprecisionProperties using
  ( WfImpCtx²; WfImpCtx-to²; idᵢ-lookup; idᵢ-no-star
  ; idᵢ-var-identity; idᵢ-wf; no-⇑ᵢ-zero-left; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star; ⇑ᵢ-★∈
  ; no-⇑ᴸᵢ-zero-left; un⇑ᵢ-★∈; un⇑ᵢ-ˣ∈; un⇑ᴸᵢ-ˣ∈; ∀ᵢ-wf²
  )
open import proof.MaximalLowerBoundsWf using
  ( CommonLowerBoundᵢ; no-occurs-base-lowerᵢ
  ; no-occurs-var-lower-νctxᵢ; no-⇑ᴸᵢ-zero-star
  ; un⇑ᴸᵢ-★∈; ⇑ᴸᵢ-★∈; ∨-true-leftᵢ; ∨-true-rightᵢ
  ; ⊑-trans-idᵢ
  )

------------------------------------------------------------------------
-- Layer 2: whole-list pruning facts
------------------------------------------------------------------------

false≠true : false ≡ true → ⊥
false≠true ()

pruneStrictlyBelowFrom-no-strict-above :
  ∀ {Δ C all} {xs : List Ty} →
  C ∈ pruneStrictlyBelowFrom Δ all xs →
  hasStrictAbove? Δ C all ≡ false
pruneStrictlyBelowFrom-no-strict-above {xs = []} ()
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} C∈
    with hasStrictAbove? Δ A all in aboveA
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} C∈
    | true =
  pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = As} C∈
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} (here refl)
    | false =
  aboveA
pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = A ∷ As} (there C∈)
    | false =
  pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = all} {xs = As} C∈

pruneStrictlyBelow-no-strict-above :
  ∀ {Δ C} {xs : List Ty} →
  C ∈ pruneStrictlyBelow Δ xs →
  hasStrictAbove? Δ C xs ≡ false
pruneStrictlyBelow-no-strict-above {Δ = Δ} {C = C} {xs = xs} C∈ =
  pruneStrictlyBelowFrom-no-strict-above
    {Δ = Δ} {C = C} {all = xs} {xs = xs} C∈

------------------------------------------------------------------------
-- Current proof frontier
------------------------------------------------------------------------

postulate
  dedupe-complete :
    ∀ {C : Ty} {xs : List Ty} →
    C ∈ xs →
    C ∈ dedupe xs

  strictlyBelow?-completeᵢ :
    ∀ {Δ C E} →
    idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ →
    ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ) →
    strictlyBelow? Δ C E ≡ true

  impᵢ? :
    ∀ {Δ A B} →
    Dec (idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ)

  EnoughFuel : ℕ → Ty → Ty → Set

  fuel-zero-impossible :
    ∀ {A B} →
    EnoughFuel zero A B →
    ⊥

  fuelFor-enough :
    ∀ {A B} →
    EnoughFuel (fuelFor A B) A B

  fuel-∀∀-both :
    ∀ {fuel A B} →
    EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
    EnoughFuel fuel A B

  fuel-∀∀-left :
    ∀ {fuel A B} →
    EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
    EnoughFuel fuel A (`∀ B)

  fuel-∀∀-right :
    ∀ {fuel A B} →
    EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
    EnoughFuel fuel (`∀ A) B

  fuel-∀L :
    ∀ {fuel A B} →
    EnoughFuel (suc fuel) (`∀ A) B →
    EnoughFuel fuel A B

  fuel-∀R :
    ∀ {fuel A B} →
    EnoughFuel (suc fuel) A (`∀ B) →
    EnoughFuel fuel A B

  fuel-⇒⇒-left :
    ∀ {fuel A₁ A₂ B₁ B₂} →
    EnoughFuel (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) →
    EnoughFuel fuel A₁ B₁

  fuel-⇒⇒-right :
    ∀ {fuel A₁ A₂ B₁ B₂} →
    EnoughFuel (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) →
    EnoughFuel fuel A₂ B₂

  fuel-⇒★-left :
    ∀ {fuel A₁ A₂} →
    EnoughFuel (suc fuel) (A₁ ⇒ A₂) ★ →
    EnoughFuel fuel A₁ ★

  fuel-⇒★-right :
    ∀ {fuel A₁ A₂} →
    EnoughFuel (suc fuel) (A₁ ⇒ A₂) ★ →
    EnoughFuel fuel A₂ ★

  fuel-★⇒-left :
    ∀ {fuel B₁ B₂} →
    EnoughFuel (suc fuel) ★ (B₁ ⇒ B₂) →
    EnoughFuel fuel ★ B₁

  fuel-★⇒-right :
    ∀ {fuel B₁ B₂} →
    EnoughFuel (suc fuel) ★ (B₁ ⇒ B₂) →
    EnoughFuel fuel ★ B₂

------------------------------------------------------------------------
-- Layer 3: raw completeness skeleton
------------------------------------------------------------------------

∈-++-left :
  ∀ {C : Ty} {xs ys : List Ty} →
  C ∈ xs →
  C ∈ xs ++ ys
∈-++-left {xs = []} ()
∈-++-left {xs = x ∷ xs} (here refl) = here refl
∈-++-left {xs = x ∷ xs} (there C∈) = there (∈-++-left C∈)

∈-++-right :
  ∀ {C : Ty} {xs ys : List Ty} →
  C ∈ ys →
  C ∈ xs ++ ys
∈-++-right {xs = []} C∈ = C∈
∈-++-right {xs = x ∷ xs} C∈ = there (∈-++-right C∈)

mapArrow-complete :
  ∀ {A B : Ty} {Bs : List Ty} →
  B ∈ Bs →
  A ⇒ B ∈ map (λ C → A ⇒ C) Bs
mapArrow-complete {Bs = []} ()
mapArrow-complete {Bs = B ∷ Bs} (here refl) = here refl
mapArrow-complete {Bs = B ∷ Bs} (there B∈) =
  there (mapArrow-complete B∈)

wrapAll-complete :
  ∀ {E : Ty} {xs : List Ty} →
  E ∈ xs →
  `∀ E ∈ wrapAll xs
wrapAll-complete {xs = []} ()
wrapAll-complete {xs = E ∷ xs} (here refl) = here refl
wrapAll-complete {xs = E ∷ xs} (there E∈) =
  there (wrapAll-complete E∈)

wrapAllIfOccurs-complete :
  ∀ {E : Ty} {xs : List Ty} →
  occurs zero E ≡ true →
  E ∈ xs →
  `∀ E ∈ wrapAllIfOccurs xs
wrapAllIfOccurs-complete {xs = []} occE ()
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} occE (here refl)
    rewrite occE =
  here refl
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} occE (there E∈)
    with occurs zero A
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} occE (there E∈)
    | true =
  there (wrapAllIfOccurs-complete occE E∈)
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} occE (there E∈)
    | false =
  wrapAllIfOccurs-complete occE E∈

arrowProducts-complete :
  ∀ {E₁ E₂ : Ty} {xs ys : List Ty} →
  E₁ ∈ xs →
  E₂ ∈ ys →
  E₁ ⇒ E₂ ∈ arrowProducts xs ys
arrowProducts-complete {xs = []} ()
arrowProducts-complete {E₁ = E₁} {E₂ = E₂} {xs = A ∷ As} E₁∈ E₂∈
    with E₁∈
arrowProducts-complete {E₁ = E₁} {E₂ = E₂} {xs = A ∷ As} E₁∈ E₂∈
    | here refl =
  ∈-++-left (mapArrow-complete E₂∈)
arrowProducts-complete {E₁ = E₁} {E₂ = E₂} {xs = A ∷ As} E₁∈ E₂∈
    | there E₁∈′ =
  ∈-++-right (arrowProducts-complete E₁∈′ E₂∈)

==ᵇ-refl : ∀ X → (X ==ᵇ X) ≡ true
==ᵇ-refl zero = refl
==ᵇ-refl (suc X) = ==ᵇ-refl X

hasVar-complete :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  hasVar X Y Φ ≡ true
hasVar-complete {Φ = []} ()
hasVar-complete {Φ = (z ˣ⊑★) ∷ Φ} (there x∈) =
  hasVar-complete x∈
hasVar-complete {Φ = (X ˣ⊑ˣ Y) ∷ Φ} (here refl)
    rewrite ==ᵇ-refl X | ==ᵇ-refl Y =
  refl
hasVar-complete {Φ = (z ˣ⊑ˣ w) ∷ Φ} {X = X} {Y = Y} (there x∈)
    with X ==ᵇ z | Y ==ᵇ w
hasVar-complete {Φ = (z ˣ⊑ˣ w) ∷ Φ} {X = X} {Y = Y} (there x∈)
    | true | true =
  refl
hasVar-complete {Φ = (z ˣ⊑ˣ w) ∷ Φ} {X = X} {Y = Y} (there x∈)
    | true | false =
  hasVar-complete x∈
hasVar-complete {Φ = (z ˣ⊑ˣ w) ∷ Φ} {X = X} {Y = Y} (there x∈)
    | false | true =
  hasVar-complete x∈
hasVar-complete {Φ = (z ˣ⊑ˣ w) ∷ Φ} {X = X} {Y = Y} (there x∈)
    | false | false =
  hasVar-complete x∈

hasStar-complete :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  hasStar X Φ ≡ true
hasStar-complete {Φ = []} ()
hasStar-complete {Φ = (X ˣ⊑★) ∷ Φ} (here refl)
    rewrite ==ᵇ-refl X =
  refl
hasStar-complete {Φ = (z ˣ⊑★) ∷ Φ} {X = X} (there x∈)
    with X ==ᵇ z
hasStar-complete {Φ = (z ˣ⊑★) ∷ Φ} {X = X} (there x∈) | true =
  refl
hasStar-complete {Φ = (z ˣ⊑★) ∷ Φ} {X = X} (there x∈) | false =
  hasStar-complete x∈
hasStar-complete {Φ = (z ˣ⊑ˣ w) ∷ Φ} (there x∈) =
  hasStar-complete x∈

varCandidate-var-var-complete :
  ∀ {Φᴸ Φᴿ X Y X′} →
  (X′ ˣ⊑ˣ X) ∈ Φᴸ →
  (X′ ˣ⊑ˣ Y) ∈ Φᴿ →
  varCandidate? Φᴸ Φᴿ (＇ X) (＇ Y) X′ ≡ true
varCandidate-var-var-complete X′⊑X X′⊑Y
    rewrite hasVar-complete X′⊑X | hasVar-complete X′⊑Y =
  refl

varCandidate-var-star-complete :
  ∀ {Φᴸ Φᴿ X X′} →
  (X′ ˣ⊑ˣ X) ∈ Φᴸ →
  (X′ ˣ⊑★) ∈ Φᴿ →
  varCandidate? Φᴸ Φᴿ (＇ X) ★ X′ ≡ true
varCandidate-var-star-complete X′⊑X X′⊑★
    rewrite hasVar-complete X′⊑X | hasStar-complete X′⊑★ =
  refl

varCandidate-star-var-complete :
  ∀ {Φᴸ Φᴿ Y X′} →
  (X′ ˣ⊑★) ∈ Φᴸ →
  (X′ ˣ⊑ˣ Y) ∈ Φᴿ →
  varCandidate? Φᴸ Φᴿ ★ (＇ Y) X′ ≡ true
varCandidate-star-var-complete X′⊑★ X′⊑Y
    rewrite hasStar-complete X′⊑★ | hasVar-complete X′⊑Y =
  refl

<suc-not-eq→< :
  ∀ {X n} →
  X < suc n →
  ¬ (X ≡ n) →
  X < n
<suc-not-eq→< {X = zero} {n = zero} z<s X≢n =
  ⊥-elim (X≢n refl)
<suc-not-eq→< {X = zero} {n = suc n} z<s X≢n = z<s
<suc-not-eq→< {X = suc X} {n = zero} (s<s ()) X≢n
<suc-not-eq→< {X = suc X} {n = suc n} (s<s X<n) X≢n =
  s<s (<suc-not-eq→< X<n (λ X≡n → X≢n (cong suc X≡n)))

varCandidatesUpTo-complete :
  ∀ {limit Φᴸ Φᴿ A B X′} →
  X′ < limit →
  varCandidate? Φᴸ Φᴿ A B X′ ≡ true →
  ＇ X′ ∈ varCandidatesUpTo Φᴸ Φᴿ A B limit
varCandidatesUpTo-complete {limit = zero} ()
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = X′} X′<sucn ok
    with X′ ≟ n
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = .n} X′<sucn ok | yes refl
    with varCandidate? Φᴸ Φᴿ A B n
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = .n} X′<sucn ok | yes refl | true =
  ∈-++-right {xs = varCandidatesUpTo Φᴸ Φᴿ A B n} (here refl)
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = .n} X′<sucn () | yes refl | false
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = X′} X′<sucn ok | no X′≢n
    with varCandidate? Φᴸ Φᴿ A B n
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = X′} X′<sucn ok | no X′≢n | true =
  ∈-++-left
    (varCandidatesUpTo-complete (<suc-not-eq→< X′<sucn X′≢n) ok)
varCandidatesUpTo-complete
    {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}
    {X′ = X′} X′<sucn ok | no X′≢n | false =
  varCandidatesUpTo-complete (<suc-not-eq→< X′<sucn X′≢n) ok

record StarMeetCtxᵢ (Φᴸ Φᴿ Φᶜ : ImpCtx) : Set where
  field
    meet-starᵢ :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φᴸ →
      (X ˣ⊑★) ∈ Φᴿ →
      (X ˣ⊑★) ∈ Φᶜ

open StarMeetCtxᵢ

StarMeet-idᵢ :
  ∀ Δ →
  StarMeetCtxᵢ (idᵢ Δ) (idᵢ Δ) (idᵢ Δ)
StarMeet-idᵢ Δ .meet-starᵢ x★∈ y★∈ =
  ⊥-elim (idᵢ-no-star x★∈)

StarMeet-∀∀ᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  StarMeetCtxᵢ (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᶜ)
StarMeet-∀∀ᵢ meet .meet-starᵢ {X = zero} (here ()) r★∈
StarMeet-∀∀ᵢ meet .meet-starᵢ {X = zero} (there l★∈) r★∈ =
  ⊥-elim (no-⇑ᵢ-zero-star l★∈)
StarMeet-∀∀ᵢ meet .meet-starᵢ {X = suc X} (here ()) r★∈
StarMeet-∀∀ᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (here ())
StarMeet-∀∀ᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (there r★∈) =
  there (⇑ᵢ-★∈ (meet-starᵢ meet (un⇑ᵢ-★∈ l★∈) (un⇑ᵢ-★∈ r★∈)))

StarMeet-∀νᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  StarMeetCtxᵢ (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᶜ)
StarMeet-∀νᵢ meet .meet-starᵢ {X = zero} (here ()) r★∈
StarMeet-∀νᵢ meet .meet-starᵢ {X = zero} (there l★∈) r★∈ =
  ⊥-elim (no-⇑ᵢ-zero-star l★∈)
StarMeet-∀νᵢ meet .meet-starᵢ {X = suc X} (here ()) r★∈
StarMeet-∀νᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (here ())
StarMeet-∀νᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (there r★∈) =
  there (⇑ᵢ-★∈
    (meet-starᵢ meet (un⇑ᵢ-★∈ l★∈) (un⇑ᴸᵢ-★∈ r★∈)))

StarMeet-ν∀ᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  StarMeetCtxᵢ (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ) (∀ᵢᶜ Φᶜ)
StarMeet-ν∀ᵢ meet .meet-starᵢ {X = zero} l★∈ (here ())
StarMeet-ν∀ᵢ meet .meet-starᵢ {X = zero} l★∈ (there r★∈) =
  ⊥-elim (no-⇑ᵢ-zero-star r★∈)
StarMeet-ν∀ᵢ meet .meet-starᵢ {X = suc X} l★∈ (here ())
StarMeet-ν∀ᵢ meet .meet-starᵢ {X = suc X} (here ()) (there r★∈)
StarMeet-ν∀ᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (there r★∈) =
  there (⇑ᵢ-★∈
    (meet-starᵢ meet (un⇑ᴸᵢ-★∈ l★∈) (un⇑ᵢ-★∈ r★∈)))

StarMeet-ννᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  StarMeetCtxᵢ (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (νᵢᶜ Φᶜ)
StarMeet-ννᵢ meet .meet-starᵢ {X = zero} (here refl) r★∈ =
  here refl
StarMeet-ννᵢ meet .meet-starᵢ {X = zero} (there l★∈) r★∈ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star l★∈)
StarMeet-ννᵢ meet .meet-starᵢ {X = suc X} (here ()) r★∈
StarMeet-ννᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (here ())
StarMeet-ννᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (there r★∈) =
  there (⇑ᴸᵢ-★∈
    (meet-starᵢ meet (un⇑ᴸᵢ-★∈ l★∈) (un⇑ᴸᵢ-★∈ r★∈)))

star-star-to-meetᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ Δᶜ Δᴸ Δᴿ Δᵒ D} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᴿ →
  Φᶜ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᵒ
star-star-to-meetᵢ meet id★ id★ = id★
star-star-to-meetᵢ meet (tag ι) (tag .ι) = tag ι
star-star-to-meetᵢ meet (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  tag (star-star-to-meetᵢ meet p₁ q₁) ⇛ star-star-to-meetᵢ meet p₂ q₂
star-star-to-meetᵢ meet (tagˣ x★∈ X<Δ) (tagˣ y★∈ _) =
  tagˣ (meet-starᵢ meet x★∈ y★∈) X<Δ
star-star-to-meetᵢ meet (ν occD D⊑★) (ν occD′ D⊑★′) =
  ν occD (star-star-to-meetᵢ (StarMeet-ννᵢ meet) D⊑★ D⊑★′)

∀ρᵢ : (TyVar → TyVar) → TyVar → TyVar
∀ρᵢ ρ zero = zero
∀ρᵢ ρ (suc X) = suc (ρ X)

νρᵢ : (TyVar → TyVar) → TyVar → TyVar
νρᵢ ρ zero = zero
νρᵢ ρ (suc X) = ρ X

record ForwardCtxᵢ (ρ : TyVar → TyVar) (Φ : ImpCtx) (Z : TyVar) :
    Set where
  field
    forward-varᵢ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φ →
      ρ X ≡ Y

    forward-starᵢ :
      ∀ {X} →
      (X ˣ⊑★) ∈ Φ →
      X ≡ Z →
      ⊥

open ForwardCtxᵢ

ForwardCtx-idᵢ :
  ∀ Δ Z →
  ForwardCtxᵢ (λ X → X) (idᵢ Δ) Z
ForwardCtx-idᵢ Δ z .forward-varᵢ x∈ = idᵢ-var-identity x∈
ForwardCtx-idᵢ Δ z .forward-starᵢ x★∈ eq = idᵢ-no-star x★∈

ForwardCtx-∀ᵢ :
  ∀ {ρ Φ Z} →
  ForwardCtxᵢ ρ Φ Z →
  ForwardCtxᵢ (∀ρᵢ ρ) (∀ᵢᶜ Φ) (suc Z)
ForwardCtx-∀ᵢ fwd .forward-varᵢ {X = zero} {Y = zero} (here refl) =
  refl
ForwardCtx-∀ᵢ fwd .forward-varᵢ {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
ForwardCtx-∀ᵢ fwd .forward-varᵢ {X = zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
ForwardCtx-∀ᵢ fwd .forward-varᵢ {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
ForwardCtx-∀ᵢ fwd .forward-varᵢ {X = suc X} {Y = suc Y} (there x∈) =
  cong suc (forward-varᵢ fwd (un⇑ᵢ-ˣ∈ x∈))
ForwardCtx-∀ᵢ fwd .forward-starᵢ {X = zero} (there x★∈) ()
ForwardCtx-∀ᵢ {Z = z} fwd .forward-starᵢ {X = suc .z} (there x★∈) refl =
  forward-starᵢ fwd (un⇑ᵢ-★∈ x★∈) refl

ForwardCtx-νᵢ :
  ∀ {ρ Φ Z} →
  ForwardCtxᵢ ρ Φ Z →
  ForwardCtxᵢ (νρᵢ ρ) (νᵢᶜ Φ) (suc Z)
ForwardCtx-νᵢ fwd .forward-varᵢ {X = zero} (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
ForwardCtx-νᵢ fwd .forward-varᵢ {X = suc X} (there x∈) =
  forward-varᵢ fwd (un⇑ᴸᵢ-ˣ∈ x∈)
ForwardCtx-νᵢ fwd .forward-starᵢ {X = zero} (here refl) ()
ForwardCtx-νᵢ fwd .forward-starᵢ {X = zero} (there x★∈) ()
ForwardCtx-νᵢ {Z = z} fwd .forward-starᵢ {X = suc .z} (there x★∈) refl =
  forward-starᵢ fwd (un⇑ᴸᵢ-★∈ x★∈) refl

occurs-var-forwardᵢ :
  ∀ (ρ : TyVar → TyVar) (z : TyVar) {X Y} →
  ρ X ≡ Y →
  occurs z (＇ X) ≡ true →
  occurs (ρ z) (＇ Y) ≡ true
occurs-var-forwardᵢ ρ z {X = X} {Y = Y} eq occ with z ≟ X
occurs-var-forwardᵢ ρ z {X = .z} {Y = Y} eq occ | yes refl
    rewrite sym eq with ρ z ≟ ρ z
occurs-var-forwardᵢ ρ z {X = .z} {Y = Y} eq occ
    | yes refl | yes refl =
  refl
occurs-var-forwardᵢ ρ z {X = .z} {Y = Y} eq occ
    | yes refl | no ρZ≢ρZ =
  ⊥-elim (ρZ≢ρZ refl)
occurs-var-forwardᵢ ρ z {X = X} {Y = Y} eq () | no z≢x

forward-star-occursᵢ :
  ∀ {ρ Φ Z X} →
  ForwardCtxᵢ ρ Φ Z →
  (X ˣ⊑★) ∈ Φ →
  occurs Z (＇ X) ≡ true →
  ⊥
forward-star-occursᵢ {Z = z} {X = x} fwd x★∈ occ with z ≟ x
forward-star-occursᵢ {Z = z} {X = .z} fwd x★∈ occ | yes refl =
  forward-starᵢ fwd x★∈ refl
forward-star-occursᵢ {Z = z} {X = x} fwd x★∈ () | no z≢x

occurs-forwardᵢ :
  ∀ {ρ Φ Δᴸ Δᴿ A B Z} →
  ForwardCtxᵢ ρ Φ Z →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  occurs Z A ≡ true →
  occurs (ρ Z) B ≡ true
occurs-forwardᵢ fwd id★ ()
occurs-forwardᵢ {ρ = ρ} {Z = z} fwd (idˣ x∈ _ _) occ =
  occurs-var-forwardᵢ ρ z (forward-varᵢ fwd x∈) occ
occurs-forwardᵢ fwd idι ()
occurs-forwardᵢ {Z = z} fwd (_↦_ {A = A₁} {B = A₂} p q) occ
    with occurs z A₁ in occ₁
occurs-forwardᵢ {Z = z} fwd (_↦_ {A = A₁} {B = A₂} p q) occ
    | true =
  ∨-true-leftᵢ (occurs-forwardᵢ fwd p occ₁)
occurs-forwardᵢ {Z = z} fwd (_↦_ {A = A₁} {B = A₂} p q) occ
    | false
    with occurs z A₂ in occ₂
occurs-forwardᵢ {Z = z} fwd (_↦_ {A = A₁} {B = A₂} p q) occ
    | false | true =
  ∨-true-rightᵢ (occurs-forwardᵢ fwd q occ₂)
occurs-forwardᵢ {Z = z} fwd (_↦_ {A = A₁} {B = A₂} p q) occ
    | false | false =
  ⊥-elim (false≠true occ)
occurs-forwardᵢ {Z = z} fwd (∀ⁱ p) occ =
  occurs-forwardᵢ (ForwardCtx-∀ᵢ fwd) p occ
occurs-forwardᵢ fwd (tag ι) ()
occurs-forwardᵢ {Z = z} fwd (tag_⇛_ {A₁ = A₁} {A₂ = A₂} p q) occ
    with occurs z A₁ in occ₁
occurs-forwardᵢ {Z = z} fwd (tag_⇛_ {A₁ = A₁} {A₂ = A₂} p q) occ
    | true =
  ⊥-elim (false≠true (occurs-forwardᵢ fwd p occ₁))
occurs-forwardᵢ {Z = z} fwd (tag_⇛_ {A₁ = A₁} {A₂ = A₂} p q) occ
    | false
    with occurs z A₂ in occ₂
occurs-forwardᵢ {Z = z} fwd (tag_⇛_ {A₁ = A₁} {A₂ = A₂} p q) occ
    | false | true =
  ⊥-elim (false≠true (occurs-forwardᵢ fwd q occ₂))
occurs-forwardᵢ {Z = z} fwd (tag_⇛_ {A₁ = A₁} {A₂ = A₂} p q) occ
    | false | false =
  ⊥-elim (false≠true occ)
occurs-forwardᵢ fwd (tagˣ x★∈ _) occ =
  ⊥-elim (forward-star-occursᵢ fwd x★∈ occ)
occurs-forwardᵢ fwd (ν occA p) occ =
  occurs-forwardᵢ (ForwardCtx-νᵢ fwd) p occ

occurs-forward-idᵢ :
  ∀ {Δ A B} →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  occurs zero A ≡ true →
  occurs zero B ≡ true
occurs-forward-idᵢ {Δ = Δ} p occ =
  occurs-forwardᵢ (ForwardCtx-idᵢ Δ zero) p occ

CompleteIH :
  ℕ → ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Ty → Ty → Set
CompleteIH fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B =
  StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
  ∀ {D} →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)

CompleteUsedIH :
  ℕ → ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Ty → Ty → Set
CompleteUsedIH fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B =
  StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
  ∀ {D} →
  occurs zero D ≡ true →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     (occurs zero E ≡ true × idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ))

data ννRouteCover
    (Φᴸ Φᴿ : ImpCtx) (Δᶜ Δᴸ Δᴿ : TyCtx)
    (A B D : Ty) : Set where
  cover-both :
    ∀ {R} →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ D ⊑ R ⊣ suc Δᶜ →
    ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ R ⊑ A ⊣ suc Δᴸ →
    ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ R ⊑ B ⊣ suc Δᴿ →
    ννRouteCover Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D

  cover-left :
    ∀ {R} →
    occurs zero R ≡ true →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ D ⊑ R ⊣ suc Δᶜ →
    ∀ᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ R ⊑ A ⊣ suc Δᴸ →
    νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ R ⊑ `∀ B ⊣ Δᴿ →
    ννRouteCover Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D

  cover-right :
    ∀ {R} →
    occurs zero R ≡ true →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ D ⊑ R ⊣ suc Δᶜ →
    νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ R ⊑ `∀ A ⊣ Δᴸ →
    ∀ᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ R ⊑ B ⊣ suc Δᴿ →
    ννRouteCover Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D

νν-route-cover-close :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  ννRouteCover (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (suc Δᶜ) Δᴸ Δᴿ A B C →
  ννRouteCover Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B (`∀ C)
νν-route-cover-close {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    (cover-both {R = R} C⊑R R⊑A R⊑B)
    with occurs zero R
νν-route-cover-close {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    (cover-both {R = R} C⊑R R⊑A R⊑B) | true =
  {!!}
νν-route-cover-close {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    (cover-both {R = R} C⊑R R⊑A R⊑B) | false =
  {!!}
νν-route-cover-close (cover-left occR C⊑R R⊑A R⊑∀B) =
  {!!}
νν-route-cover-close (cover-right occR C⊑R R⊑∀A R⊑B) =
  {!!}

postulate
  νν-route-cover :
    ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
    StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
    occurs zero D ≡ true →
    νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
    νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
    ννRouteCover Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D

νν-route-cover-complete :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
  CompleteIH fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
    (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B →
  CompleteUsedIH fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
    (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B) →
  CompleteUsedIH fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
    (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B →
  StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
  ννRouteCover Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D →
  ∃[ E ]
    (E ∈
      (wrapAll
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B) ++
       wrapAllIfOccurs
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)) ++
       wrapAllIfOccurs
        (enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
          (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B)) ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ `∀ D ⊑ E ⊣ Δᶜ)
νν-route-cover-complete {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    ih-both ih-left ih-right meet (cover-both D⊑R R⊑A R⊑B)
    with ih-both (StarMeet-∀∀ᵢ meet) R⊑A R⊑B
νν-route-cover-complete {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    ih-both ih-left ih-right meet (cover-both D⊑R R⊑A R⊑B)
    | E , E∈ , R⊑E =
  `∀ E ,
  ∈-++-left (wrapAll-complete E∈) ,
  ∀ⁱ (⊑-trans-idᵢ D⊑R R⊑E)
νν-route-cover-complete {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    ih-both ih-left ih-right meet (cover-left occR D⊑R R⊑A R⊑∀B)
    with ih-left (StarMeet-∀νᵢ meet) occR R⊑A R⊑∀B
νν-route-cover-complete {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    ih-both ih-left ih-right meet (cover-left occR D⊑R R⊑A R⊑∀B)
    | E , E∈ , occE , R⊑E =
  `∀ E ,
  ∈-++-right
    {xs =
      wrapAll
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)}
    (∈-++-left (wrapAllIfOccurs-complete occE E∈)) ,
  ∀ⁱ (⊑-trans-idᵢ D⊑R R⊑E)
νν-route-cover-complete {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    ih-both ih-left ih-right meet (cover-right occR D⊑R R⊑∀A R⊑B)
    with ih-right (StarMeet-ν∀ᵢ meet) occR R⊑∀A R⊑B
νν-route-cover-complete {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
    ih-both ih-left ih-right meet (cover-right occR D⊑R R⊑∀A R⊑B)
    | E , E∈ , occE , R⊑E =
  `∀ E ,
  ∈-++-right
    {xs =
      wrapAll
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)}
    (∈-++-right
      {xs = wrapAllIfOccurs
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B))}
      (wrapAllIfOccurs-complete occE E∈)) ,
  ∀ⁱ (⊑-trans-idᵢ D⊑R R⊑E)

mutual
  enumMLB-complete-used :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B} →
    EnoughFuel fuel A B →
    WfImpCtx² Δᶜ Δᴸ Φᴸ →
    WfImpCtx² Δᶜ Δᴿ Φᴿ →
    CompleteIH fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
    CompleteUsedIH fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B
  enumMLB-complete-used enough hΦᴸ hΦᴿ ih meet occD D⊑A D⊑B
      with ih meet D⊑A D⊑B
  enumMLB-complete-used enough hΦᴸ hΦᴿ ih meet occD D⊑A D⊑B
      | E , E∈ , D⊑E =
    E , E∈ , (occurs-forward-idᵢ D⊑E occD , D⊑E)

  enumMLB-νν-complete-elim :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
    EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
    WfImpCtx² Δᶜ Δᴸ Φᴸ →
    WfImpCtx² Δᶜ Δᴿ Φᴿ →
    CompleteIH fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B →
    CompleteUsedIH fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B) →
    CompleteUsedIH fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B →
    StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
    occurs zero D ≡ true →
    νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
    νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
    ∃[ E ]
      (E ∈ enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) ×
       idᵢ Δᶜ ∣ Δᶜ ⊢ `∀ D ⊑ E ⊣ Δᶜ)
  enumMLB-νν-complete-elim
      {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
      enough hΦᴸ hΦᴿ ih-both ih-left ih-right meet occD D⊑A D⊑B =
    E , dedupe-complete E∈ , D⊑E
    where
      route =
        νν-route-cover-complete
          {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Δᶜ = Δᶜ}
          {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B}
          ih-both ih-left ih-right meet
          (νν-route-cover meet occD D⊑A D⊑B)

      E = proj₁ route

      E∈ = proj₁ (proj₂ route)

      D⊑E = proj₂ (proj₂ route)

  enumMLB-complete :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
    EnoughFuel fuel A B →
    WfImpCtx² Δᶜ Δᴸ Φᴸ →
    WfImpCtx² Δᶜ Δᴿ Φᴿ →
    StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
    Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
    Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
    ∃[ E ]
      (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
       idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
  enumMLB-complete {fuel = zero} enough hΦᴸ hΦᴿ meet D⊑A D⊑B =
    ⊥-elim (fuel-zero-impossible enough)
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete (fuel-∀∀-both enough)
             (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (StarMeet-∀∀ᵢ meet) D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , D⊑E =
    `∀ E ,
    dedupe-complete (∈-++-left (wrapAll-complete E∈)) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      with enumMLB-complete-used (fuel-∀∀-left enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀∀-left enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (∈-++-right
        {xs =
          wrapAll
            (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
              (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)}
        (∈-++-left (wrapAllIfOccurs-complete occE E∈))) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀∀-right enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀∀-right enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (∈-++-right
        {xs =
          wrapAll
            (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
              (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)}
        (∈-++-right
          {xs = wrapAllIfOccurs
            (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
              (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B))}
          (wrapAllIfOccurs-complete occE E∈))) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    enumMLB-νν-complete-elim enough hΦᴸ hΦᴿ
      (λ meet′ D′⊑A D′⊑B →
        enumMLB-complete (fuel-∀∀-both enough)
          (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) meet′ D′⊑A D′⊑B)
      (λ meet′ occD′ D′⊑A D′⊑B →
        enumMLB-complete-used (fuel-∀∀-left enough)
          (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
          (λ meet″ D″⊑A D″⊑B →
            enumMLB-complete (fuel-∀∀-left enough)
              (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
              meet″ D″⊑A D″⊑B)
          meet′
          occD′ D′⊑A D′⊑B)
      (λ meet′ occD′ D′⊑A D′⊑B →
        enumMLB-complete-used (fuel-∀∀-right enough)
          (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
          (λ meet″ D″⊑A D″⊑B →
            enumMLB-complete (fuel-∀∀-right enough)
              (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
              meet″ D″⊑A D″⊑B)
          meet′
          occD′ D′⊑A D′⊑B)
      meet
      occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ★}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ★}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ＇ X}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ＇ X}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (∀ⁱ D⊑A) (ν occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete (wrapAllIfOccurs-complete occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ★}
      enough hΦᴸ hΦᴿ meet id★ id★ =
    ★ , here refl , id★
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = .(‵ ι)}
      enough hΦᴸ hΦᴿ meet idι idι
      with ι ≟Base ι
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = .(‵ ι)}
      enough hΦᴸ hΦᴿ meet idι idι | yes refl =
    ‵ ι , here refl , idι
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = .(‵ ι)}
      enough hΦᴸ hΦᴿ meet idι idι | no neq =
    ⊥-elim (neq refl)
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = ★}
      enough hΦᴸ hΦᴿ meet idι (tag .ι) =
    ‵ ι , here refl , idι
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ‵ ι}
      enough hΦᴸ hΦᴿ meet (tag .ι) idι =
    ‵ ι , here refl , idι
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂)
      with enumMLB-complete (fuel-⇒⇒-left enough)
             hΦᴸ hΦᴿ meet D₁⊑A₁ D₁⊑B₁
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁
      with enumMLB-complete (fuel-⇒⇒-right enough)
             hΦᴸ hΦᴿ meet D₂⊑A₂ D₂⊑B₂
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
    E₁ ⇒ E₂ ,
    arrowProducts-complete E₁∈ E₂∈ ,
    D₁⊑E₁ ↦ D₂⊑E₂
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ★}
      enough hΦᴸ hΦᴿ meet (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★)
      with enumMLB-complete (fuel-⇒★-left enough)
             hΦᴸ hΦᴿ meet D₁⊑A₁ D₁⊑★
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ★}
      enough hΦᴸ hΦᴿ meet (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★)
      | E₁ , E₁∈ , D₁⊑E₁
      with enumMLB-complete (fuel-⇒★-right enough)
             hΦᴸ hΦᴿ meet D₂⊑A₂ D₂⊑★
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ★}
      enough hΦᴸ hΦᴿ meet (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★)
      | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
    E₁ ⇒ E₂ ,
    arrowProducts-complete E₁∈ E₂∈ ,
    D₁⊑E₁ ↦ D₂⊑E₂
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂)
      with enumMLB-complete (fuel-★⇒-left enough)
             hΦᴸ hΦᴿ meet D₁⊑★ D₁⊑B₁
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁
      with enumMLB-complete (fuel-★⇒-right enough)
             hΦᴸ hΦᴿ meet D₂⊑★ D₂⊑B₂
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
    E₁ ⇒ E₂ ,
    arrowProducts-complete E₁∈ E₂∈ ,
    D₁⊑E₁ ↦ D₂⊑E₂
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = ＇ Y}
      enough hΦᴸ hΦᴿ meet
      (idˣ {X = X′} X′⊑X X′<Δ X<Δᴸ) (idˣ X′⊑Y _ Y<Δᴿ) =
    ＇ X′ ,
    varCandidatesUpTo-complete
      X′<Δ
      (varCandidate-var-var-complete X′⊑X X′⊑Y) ,
    idˣ (idᵢ-lookup X′<Δ) X′<Δ X′<Δ
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = ★}
      enough hΦᴸ hΦᴿ meet
      (idˣ {X = X′} X′⊑X X′<Δ X<Δᴸ) (tagˣ X′⊑★ _) =
    ＇ X′ ,
    varCandidatesUpTo-complete
      X′<Δ
      (varCandidate-var-star-complete X′⊑X X′⊑★) ,
    idˣ (idᵢ-lookup X′<Δ) X′<Δ X′<Δ
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ＇ Y}
      enough hΦᴸ hΦᴿ meet
      (tagˣ {X = X′} X′⊑★ X′<Δ) (idˣ X′⊑Y _ Y<Δᴿ) =
    ＇ X′ ,
    varCandidatesUpTo-complete
      X′<Δ
      (varCandidate-star-var-complete X′⊑★ X′⊑Y) ,
    idˣ (idᵢ-lookup X′<Δ) X′<Δ X′<Δ
  enumMLB-complete {fuel = suc fuel} {Δᶜ = Δᶜ} {A = ★} {B = ★}
      enough hΦᴸ hΦᴿ meet
      p@(tagˣ X′⊑★ X′<Δ) q@(tagˣ X′⊑★′ _) =
    ★ ,
    here refl ,
    star-star-to-meetᵢ {Δᵒ = Δᶜ} meet p q
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ★}
      enough hΦᴸ hΦᴿ meet (tag ι) (tag .ι) =
    ★ , here refl , tag ι
  enumMLB-complete {fuel = suc fuel} {Δᶜ = Δᶜ} {A = ★} {B = ★}
      enough hΦᴸ hΦᴿ meet (tag D₁⊑★ ⇛ D₂⊑★) (tag D₁⊑★′ ⇛ D₂⊑★′) =
    ★ , here refl , star-star-to-meetᵢ {Δᵒ = Δᶜ} meet
      (tag D₁⊑★ ⇛ D₂⊑★) (tag D₁⊑★′ ⇛ D₂⊑★′)
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {D = `∀ D}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    ⊥-elim (no-occurs-var-lower-νctxᵢ occD D⊑A)
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    ⊥-elim (no-occurs-base-lowerᵢ occD D⊑A)
  enumMLB-complete {fuel = suc fuel} {Δᶜ = Δᶜ}
      {A = ★} {B = ★} {D = `∀ D}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    ★ ,
    here refl ,
    ν occD (star-star-to-meetᵢ {Δᵒ = Δᶜ} (StarMeet-ννᵢ meet) D⊑A D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ＇ Y} {D = `∀ D}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    ⊥-elim (no-occurs-var-lower-νctxᵢ occD′ D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ‵ ι} {D = `∀ D}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    ⊥-elim (no-occurs-base-lowerᵢ occD′ D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = `∀ B} {D = `∀ D}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂} {D = `∀ D}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ＇ Y}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ★}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
      enough hΦᴸ hΦᴿ meet (ν occD D⊑A) (ν occD′ D⊑B) =
    {!!}

rawEndpointMlbsAt-complete :
  ∀ {Δ A B D} →
  WfTy Δ A →
  WfTy Δ B →
  CommonLowerBoundᵢ Δ A B D →
  ∃[ E ]
    (E ∈ rawEndpointMlbsAt Δ A B ×
     idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
rawEndpointMlbsAt-complete {Δ = Δ} {A = A} {B = B} hA hB commonD =
  enumMLB-complete (fuelFor-enough {A = A} {B = B})
    (WfImpCtx-to² (idᵢ-wf Δ)) (WfImpCtx-to² (idᵢ-wf Δ))
    (StarMeet-idᵢ Δ) (proj₁ commonD) (proj₂ commonD)

hasStrictAbove?-completeᵢ :
  ∀ {Δ C E} {xs : List Ty} →
  E ∈ xs →
  idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ →
  ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ) →
  hasStrictAbove? Δ C xs ≡ true
hasStrictAbove?-completeᵢ {xs = []} ()
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (here refl) C⊑E ¬E⊑C
    rewrite strictlyBelow?-completeᵢ C⊑E ¬E⊑C =
  refl
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (there E∈) C⊑E ¬E⊑C
    with strictlyBelow? Δ C B
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (there E∈) C⊑E ¬E⊑C
    | true =
  refl
hasStrictAbove?-completeᵢ
    {Δ = Δ} {C = C} {E = E} {xs = B ∷ Bs} (there E∈) C⊑E ¬E⊑C
    | false =
  hasStrictAbove?-completeᵢ E∈ C⊑E ¬E⊑C

------------------------------------------------------------------------
-- Layer 1: public maximality targets
------------------------------------------------------------------------

allEndpointMlbsAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  C ∈ allEndpointMlbsAt Δ A B →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ
allEndpointMlbsAt-maximal {Δ = Δ} {A = A} {B = B} {C = C} {D = D}
    hA hB C∈ commonD C⊑D
    with impᵢ? {Δ = Δ} {A = D} {B = C}
allEndpointMlbsAt-maximal {Δ = Δ} {A = A} {B = B} {C = C} {D = D}
    hA hB C∈ commonD C⊑D | yes D⊑C =
  D⊑C
allEndpointMlbsAt-maximal {Δ = Δ} {A = A} {B = B} {C = C} {D = D}
    hA hB C∈ commonD C⊑D | no ¬D⊑C =
  ⊥-elim (false≠true (trans (sym noAbove) above))
  where
    xs : List Ty
    xs = dedupe (rawEndpointMlbsAt Δ A B)

    C∈xs : C ∈ xs
    C∈xs = pruneStrictlyBelow-sound {Δ = Δ} {xs = xs} C∈

    noAbove : hasStrictAbove? Δ C xs ≡ false
    noAbove = pruneStrictlyBelow-no-strict-above {Δ = Δ} {xs = xs} C∈

    coverage :
      ∃[ E ]
        (E ∈ rawEndpointMlbsAt Δ A B ×
         idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
    coverage =
      rawEndpointMlbsAt-complete hA hB commonD

    E : Ty
    E = proj₁ coverage

    E∈raw : E ∈ rawEndpointMlbsAt Δ A B
    E∈raw = proj₁ (proj₂ coverage)

    D⊑E : idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ
    D⊑E = proj₂ (proj₂ coverage)

    E∈xs : E ∈ xs
    E∈xs = dedupe-complete E∈raw

    C⊑E : idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ
    C⊑E = ⊑-trans-idᵢ C⊑D D⊑E

    ¬E⊑C : ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ)
    ¬E⊑C E⊑C = ¬D⊑C (⊑-trans-idᵢ D⊑E E⊑C)

    above : hasStrictAbove? Δ C xs ≡ true
    above = hasStrictAbove?-completeᵢ E∈xs C⊑E ¬E⊑C

simpleEndpointMlbAt-maximal :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  simpleEndpointMlbAt Δ A B ≡ just C →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  idᵢ Δ ∣ Δ ⊢ D ⊑ C ⊣ Δ
simpleEndpointMlbAt-maximal {Δ = Δ} {A = A} {B = B}
    hA hB eq commonD C⊑D =
  allEndpointMlbsAt-maximal hA hB
    (first-sound {xs = allEndpointMlbsAt Δ A B} eq) commonD C⊑D

simpleEndpointMlb-maximal :
  ∀ {A B C D} →
  WfTy (endpointCtx A B) A →
  WfTy (endpointCtx A B) B →
  simpleEndpointMlb A B ≡ just C →
  CommonLowerBoundᵢ (endpointCtx A B) A B D →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ C ⊑ D ⊣ endpointCtx A B →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ D ⊑ C ⊣ endpointCtx A B
simpleEndpointMlb-maximal {A = A} {B = B} hA hB eq commonD C⊑D =
  simpleEndpointMlbAt-maximal {Δ = endpointCtx A B} hA hB eq commonD C⊑D

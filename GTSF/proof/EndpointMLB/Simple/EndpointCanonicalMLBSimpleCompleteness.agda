module proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleCompleteness where

-- File Charter:
--   * Completeness proof for the raw simple exhaustive endpoint MLB
--     enumeration.
--   * Proves `rawEndpointMlbsAt-complete` from fuel sufficiency, list/boolean
--     completeness facts, and recursive completeness of `enumMLB`.
--   * Eliminates unsupported source binders by instantiating them with `★`,
--     using separate endpoint and source fuel for termination.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using
  (ℕ; _+_; _<_; _≤_; zero; suc; z≤n; s≤s; s≤s⁻¹; z<s; s<s)
open import Data.Nat.Properties using
  ( _≟_; +-assoc; +-identityʳ; +-mono-≤; +-suc
  ; m≤m+n; m≤n+m; ≤-refl; ≤-trans
  )
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (Dec; ¬_; no; yes)

open import Types
open import Imprecision using (ImpCtx; idᵢ)
open import ImprecisionWf
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  ( arrowProducts; below?; dedupe; dedupeSeen; enumMLB
  ; fuelFor; hasStar; hasVar; memberTy?
  ; rawEndpointMlbsAt
  ; sizeTy; strictlyBelow?; varCandidate?; varCandidatesUpTo; wrapAll
  ; wrapAllIfOccurs; _==ᵇ_; ∀ᵢᶜ; νᵢᶜ
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleSoundness using
  (νᵢᶜ-wf²)
open import proof.Core.Properties.ImprecisionProperties using
  ( WfImpCtx²; WfImpCtx-to²; idᵢ-lookup; idᵢ-no-star; imp?
  ; idᵢ-var-identity; idᵢ-wf; no-⇑ᵢ-zero-left; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star; ⇑ᵢ-ˣ∈; ⇑ᵢ-★∈
  ; no-⇑ᴸᵢ-zero-left; un⇑ᵢ-★∈; un⇑ᵢ-ˣ∈; un⇑ᴸᵢ-ˣ∈
  ; ∀ᵢ-wf²; nonVar?
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( CommonLowerBoundᵢ
  ; occurs-var-true→≡ᵢ
  )
open import proof.Core.Properties.NuImprecisionBinderDropProperties using
  ( DropAtᵢ
  ; drop-zeroᵢ
  ; drop-∀ᵢ
  ; drop-νᵢ
  ; open-unused-atᵢ
  ; removeAt-Wfᵢ
  )
open import proof.Core.Properties.NuImprecisionWfBridgeProperties using
  ( old⊑→wf-idᵢ
  ; ⊑-forgetᵢ
  )
open import proof.Core.Properties.NuImprecisionTransitivityProperties using
  ( nonVar-forward-if-occursᵢ
  ; ⊑-trans-idᵢ
  ; ⊑-trans-left-idᵢ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( no-occurs-base-lowerᵢ
  ; no-occurs-var-lower-νctxᵢ
  ; no-⇑ᴸᵢ-zero-star
  ; removeAtᵗ
  ; un⇑ᴸᵢ-★∈
  ; ⇑ᴸᵢ-ˣ∈
  ; ⇑ᴸᵢ-★∈
  ; ∨-true-leftᵢ
  ; ∨-true-rightᵢ
  )
open import proof.Core.Properties.TypeProperties using (occurs-extsNᵗ-below; occurs-suc-var)

------------------------------------------------------------------------
-- Completeness support
------------------------------------------------------------------------

false≠true : false ≡ true → ⊥
false≠true ()

memberTy?-sound :
  ∀ {C : Ty} {xs : List Ty} →
  memberTy? C xs ≡ true →
  C ∈ xs
memberTy?-sound {xs = []} ()
memberTy?-sound {C = C} {xs = A ∷ As} ok with C ≟Ty A
memberTy?-sound {C = .A} {xs = A ∷ As} ok | yes refl = here refl
memberTy?-sound {C = C} {xs = A ∷ As} ok | no C≢A =
  there (memberTy?-sound ok)

∉-cons :
  ∀ {C A : Ty} {xs : List Ty} →
  ¬ (C ≡ A) →
  ¬ (C ∈ xs) →
  ¬ (C ∈ A ∷ xs)
∉-cons C≢A C∉xs (here C≡A) = C≢A C≡A
∉-cons C≢A C∉xs (there C∈xs) = C∉xs C∈xs

dedupeSeen-complete :
  ∀ {C : Ty} {seen xs : List Ty} →
  C ∈ xs →
  ¬ (C ∈ seen) →
  C ∈ dedupeSeen seen xs
dedupeSeen-complete {xs = []} () C∉seen
dedupeSeen-complete {C = C} {seen = seen} {xs = A ∷ As} C∈ C∉seen
    with memberTy? A seen in A∈seen?
dedupeSeen-complete {C = .A} {seen = seen} {xs = A ∷ As}
    (here refl) C∉seen | true =
  ⊥-elim (C∉seen (memberTy?-sound A∈seen?))
dedupeSeen-complete {C = C} {seen = seen} {xs = A ∷ As}
    (there C∈) C∉seen | true =
  dedupeSeen-complete C∈ C∉seen
dedupeSeen-complete {C = .A} {seen = seen} {xs = A ∷ As}
    (here refl) C∉seen | false =
  here refl
dedupeSeen-complete {C = C} {seen = seen} {xs = A ∷ As}
    (there C∈) C∉seen | false
    with C ≟Ty A
dedupeSeen-complete {C = .A} {seen = seen} {xs = A ∷ As}
    (there C∈) C∉seen | false | yes refl =
  here refl
dedupeSeen-complete {C = C} {seen = seen} {xs = A ∷ As}
    (there C∈) C∉seen | false | no C≢A =
  there (dedupeSeen-complete C∈ (∉-cons C≢A C∉seen))

dedupe-complete :
  ∀ {C : Ty} {xs : List Ty} →
  C ∈ xs →
  C ∈ dedupe xs
dedupe-complete C∈ = dedupeSeen-complete C∈ (λ ())

impᵢ? :
  ∀ {Δ A B} →
  Dec (idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ)
impᵢ? {Δ = Δ} {A = A} {B = B} with imp? (idᵢ Δ) A B
impᵢ? {Δ = Δ} {A = A} {B = B} | yes A⊑B =
  yes (old⊑→wf-idᵢ A⊑B)
impᵢ? {Δ = Δ} {A = A} {B = B} | no A⋢B =
  no (λ A⊑B → A⋢B (⊑-forgetᵢ A⊑B))

below?-trueᵢ :
  ∀ {Δ A B} →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  below? Δ A B ≡ true
below?-trueᵢ {Δ = Δ} {A = A} {B = B} A⊑B
    with imp? (idᵢ Δ) A B
below?-trueᵢ {Δ = Δ} {A = A} {B = B} A⊑B | yes p = refl
below?-trueᵢ {Δ = Δ} {A = A} {B = B} A⊑B | no A⋢B =
  ⊥-elim (A⋢B (⊑-forgetᵢ A⊑B))

below?-falseᵢ :
  ∀ {Δ A B} →
  ¬ (idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ) →
  below? Δ A B ≡ false
below?-falseᵢ {Δ = Δ} {A = A} {B = B} A⋢B
    with imp? (idᵢ Δ) A B
below?-falseᵢ {Δ = Δ} {A = A} {B = B} A⋢B | yes A⊑B =
  ⊥-elim (A⋢B (old⊑→wf-idᵢ A⊑B))
below?-falseᵢ {Δ = Δ} {A = A} {B = B} A⋢B | no p = refl

strictlyBelow?-completeᵢ :
  ∀ {Δ C E} →
  idᵢ Δ ∣ Δ ⊢ C ⊑ E ⊣ Δ →
  ¬ (idᵢ Δ ∣ Δ ⊢ E ⊑ C ⊣ Δ) →
  strictlyBelow? Δ C E ≡ true
strictlyBelow?-completeᵢ C⊑E E⋢C
    rewrite below?-trueᵢ C⊑E | below?-falseᵢ E⋢C =
  refl

data EnoughFuel (fuel : ℕ) (A B : Ty) : Set where
  fuel-ok :
    suc (sizeTy A + sizeTy B) ≤ fuel →
    EnoughFuel fuel A B

data SourceFuel : ℕ → Ty → Set where
  source-ok :
    ∀ {budget D} →
    sizeTy D ≤ budget →
    SourceFuel (suc budget) D

sourceFuelFor :
  ∀ {D} →
  SourceFuel (suc (sizeTy D)) D
sourceFuelFor = source-ok ≤-refl

fuel-zero-impossible :
  ∀ {A B} →
  EnoughFuel zero A B →
  ⊥
fuel-zero-impossible (fuel-ok ())

fuelFor-enough :
  ∀ {A B} →
  EnoughFuel (fuelFor A B) A B
fuelFor-enough {A = A} {B = B}
    rewrite +-assoc 20 (sizeTy A) (sizeTy B)
          | +-assoc (20 + (sizeTy A + sizeTy B)) (sizeTy A) (sizeTy B) =
  fuel-ok
    (≤-trans
      (m≤n+m (suc (sizeTy A + sizeTy B)) 19)
      (m≤m+n (20 + (sizeTy A + sizeTy B)) (sizeTy A + sizeTy B)))

weaken≤ : ∀ {m n} → m ≤ n → m ≤ suc n
weaken≤ z≤n = z≤n
weaken≤ (s≤s m≤n) = s≤s (weaken≤ m≤n)

drop-suc≤ : ∀ {m n} → suc m ≤ n → m ≤ n
drop-suc≤ {n = zero} ()
drop-suc≤ {n = suc n} m<n = weaken≤ (s≤s⁻¹ m<n)

fuel-∀∀-both :
  ∀ {fuel A B} →
  EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
  EnoughFuel fuel A B
fuel-∀∀-both {A = A} {B = B} (fuel-ok enough)
    rewrite +-suc (sizeTy A) (sizeTy B) =
  fuel-ok (drop-suc≤ (s≤s⁻¹ enough))

fuel-∀∀-left :
  ∀ {fuel A B} →
  EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
  EnoughFuel fuel A (`∀ B)
fuel-∀∀-left (fuel-ok enough) =
  fuel-ok (s≤s⁻¹ enough)

fuel-∀∀-right :
  ∀ {fuel A B} →
  EnoughFuel (suc fuel) (`∀ A) (`∀ B) →
  EnoughFuel fuel (`∀ A) B
fuel-∀∀-right {A = A} {B = B} (fuel-ok enough)
    rewrite +-suc (sizeTy A) (sizeTy B) =
  fuel-ok (s≤s⁻¹ enough)

fuel-∀L :
  ∀ {fuel A B} →
  EnoughFuel (suc fuel) (`∀ A) B →
  EnoughFuel fuel A B
fuel-∀L (fuel-ok enough) = fuel-ok (s≤s⁻¹ enough)

fuel-∀R :
  ∀ {fuel A B} →
  EnoughFuel (suc fuel) A (`∀ B) →
  EnoughFuel fuel A B
fuel-∀R {A = A} {B = B} (fuel-ok enough)
    rewrite +-suc (sizeTy A) (sizeTy B) =
  fuel-ok (s≤s⁻¹ enough)

pred-⇒⇒-sum :
  ∀ {a b c d fuel} →
  suc (suc (a + b) + suc (c + d)) ≤ suc fuel →
  suc ((a + b) + (c + d)) ≤ fuel
pred-⇒⇒-sum {a = a} {b = b} {c = c} {d = d} enough
    rewrite +-suc (a + b) (c + d) =
  drop-suc≤ (s≤s⁻¹ enough)

pred-⇒⇒-left :
  ∀ {a b c d fuel} →
  suc (suc (a + b) + suc (c + d)) ≤ suc fuel →
  suc (a + c) ≤ fuel
pred-⇒⇒-left {a = a} {b = b} {c = c} {d = d} enough =
  ≤-trans
    (s≤s (+-mono-≤ (m≤m+n a b) (m≤m+n c d)))
    (pred-⇒⇒-sum {a = a} {b = b} {c = c} {d = d} enough)

pred-⇒⇒-right :
  ∀ {a b c d fuel} →
  suc (suc (a + b) + suc (c + d)) ≤ suc fuel →
  suc (b + d) ≤ fuel
pred-⇒⇒-right {a = a} {b = b} {c = c} {d = d} enough =
  ≤-trans
    (s≤s (+-mono-≤ (m≤n+m b a) (m≤n+m d c)))
    (pred-⇒⇒-sum {a = a} {b = b} {c = c} {d = d} enough)

fuel-⇒⇒-left :
  ∀ {fuel A₁ A₂ B₁ B₂} →
  EnoughFuel (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) →
  EnoughFuel fuel A₁ B₁
fuel-⇒⇒-left {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂}
    (fuel-ok enough) =
  fuel-ok
    (pred-⇒⇒-left
      {a = sizeTy A₁} {b = sizeTy A₂}
      {c = sizeTy B₁} {d = sizeTy B₂} enough)

fuel-⇒⇒-right :
  ∀ {fuel A₁ A₂ B₁ B₂} →
  EnoughFuel (suc fuel) (A₁ ⇒ A₂) (B₁ ⇒ B₂) →
  EnoughFuel fuel A₂ B₂
fuel-⇒⇒-right {A₁ = A₁} {A₂ = A₂} {B₁ = B₁} {B₂ = B₂}
    (fuel-ok enough) =
  fuel-ok
    (pred-⇒⇒-right
      {a = sizeTy A₁} {b = sizeTy A₂}
      {c = sizeTy B₁} {d = sizeTy B₂} enough)

pred-⇒★-left :
  ∀ {a b fuel} →
  suc (suc (a + b) + 1) ≤ suc fuel →
  suc (a + 1) ≤ fuel
pred-⇒★-left {a = a} {b = b} enough
    rewrite +-suc a zero
          | +-identityʳ a
          | +-suc (suc (a + b)) zero
          | +-identityʳ (suc (a + b)) =
  ≤-trans (s≤s (s≤s (m≤m+n a b))) (s≤s⁻¹ enough)

pred-⇒★-right :
  ∀ {a b fuel} →
  suc (suc (a + b) + 1) ≤ suc fuel →
  suc (b + 1) ≤ fuel
pred-⇒★-right {a = a} {b = b} enough
    rewrite +-suc b zero
          | +-identityʳ b
          | +-suc (suc (a + b)) zero
          | +-identityʳ (suc (a + b)) =
  ≤-trans (s≤s (s≤s (m≤n+m b a))) (s≤s⁻¹ enough)

fuel-⇒★-left :
  ∀ {fuel A₁ A₂} →
  EnoughFuel (suc fuel) (A₁ ⇒ A₂) ★ →
  EnoughFuel fuel A₁ ★
fuel-⇒★-left {A₁ = A₁} {A₂ = A₂} (fuel-ok enough) =
  fuel-ok (pred-⇒★-left {a = sizeTy A₁} {b = sizeTy A₂} enough)

fuel-⇒★-right :
  ∀ {fuel A₁ A₂} →
  EnoughFuel (suc fuel) (A₁ ⇒ A₂) ★ →
  EnoughFuel fuel A₂ ★
fuel-⇒★-right {A₁ = A₁} {A₂ = A₂} (fuel-ok enough) =
  fuel-ok (pred-⇒★-right {a = sizeTy A₁} {b = sizeTy A₂} enough)

pred-★⇒-left :
  ∀ {c d fuel} →
  suc (1 + suc (c + d)) ≤ suc fuel →
  suc (1 + c) ≤ fuel
pred-★⇒-left {c = c} {d = d} enough =
  ≤-trans (s≤s (s≤s (m≤m+n c d))) (s≤s⁻¹ enough)

pred-★⇒-right :
  ∀ {c d fuel} →
  suc (1 + suc (c + d)) ≤ suc fuel →
  suc (1 + d) ≤ fuel
pred-★⇒-right {c = c} {d = d} enough =
  ≤-trans (s≤s (s≤s (m≤n+m d c))) (s≤s⁻¹ enough)

fuel-★⇒-left :
  ∀ {fuel B₁ B₂} →
  EnoughFuel (suc fuel) ★ (B₁ ⇒ B₂) →
  EnoughFuel fuel ★ B₁
fuel-★⇒-left {B₁ = B₁} {B₂ = B₂} (fuel-ok enough) =
  fuel-ok (pred-★⇒-left {c = sizeTy B₁} {d = sizeTy B₂} enough)

fuel-★⇒-right :
  ∀ {fuel B₁ B₂} →
  EnoughFuel (suc fuel) ★ (B₁ ⇒ B₂) →
  EnoughFuel fuel ★ B₂
fuel-★⇒-right {B₁ = B₁} {B₂ = B₂} (fuel-ok enough) =
  fuel-ok (pred-★⇒-right {c = sizeTy B₁} {d = sizeTy B₂} enough)

------------------------------------------------------------------------
-- Raw enumeration completeness
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
  NonVar E →
  occurs zero E ≡ true →
  E ∈ xs →
  `∀ E ∈ wrapAllIfOccurs xs
wrapAllIfOccurs-complete {xs = []} safe occE ()
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (here refl) with nonVar? E
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (here refl) | yes safe′ rewrite occE =
  here refl
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (here refl) | no ¬safe =
  ⊥-elim (¬safe safe)
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (there E∈) with nonVar? A | occurs zero A
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (there E∈) | yes safeA | true =
  there (wrapAllIfOccurs-complete safe occE E∈)
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (there E∈) | yes safeA | false =
  wrapAllIfOccurs-complete safe occE E∈
wrapAllIfOccurs-complete {E = E} {xs = A ∷ As} safe occE
    (there E∈) | no ¬safeA | occA =
  wrapAllIfOccurs-complete safe occE E∈

arrowProducts-complete :
  ∀ {E₁ E₂ : Ty} {xs ys : List Ty} →
  E₁ ∈ xs →
  E₂ ∈ ys →
  E₁ ⇒ E₂ ∈ arrowProducts xs ys
arrowProducts-complete {xs = []} ()
arrowProducts-complete
    {E₁ = E₁} {E₂ = E₂} {xs = A ∷ As} E₁∈ E₂∈
    with E₁∈
arrowProducts-complete
    {E₁ = E₁} {E₂ = E₂} {xs = A ∷ As} E₁∈ E₂∈
    | here refl =
  ∈-++-left (mapArrow-complete E₂∈)
arrowProducts-complete
    {E₁ = E₁} {E₂ = E₂} {xs = A ∷ As} E₁∈ E₂∈
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
StarMeet-∀∀ᵢ meet .meet-starᵢ {X = suc X}
    (there l★∈) (there r★∈) =
  there
    (⇑ᵢ-★∈
      (meet-starᵢ meet (un⇑ᵢ-★∈ l★∈) (un⇑ᵢ-★∈ r★∈)))

StarMeet-∀νᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  StarMeetCtxᵢ (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ) (∀ᵢᶜ Φᶜ)
StarMeet-∀νᵢ meet .meet-starᵢ {X = zero} (here ()) r★∈
StarMeet-∀νᵢ meet .meet-starᵢ {X = zero} (there l★∈) r★∈ =
  ⊥-elim (no-⇑ᵢ-zero-star l★∈)
StarMeet-∀νᵢ meet .meet-starᵢ {X = suc X} (here ()) r★∈
StarMeet-∀νᵢ meet .meet-starᵢ {X = suc X} (there l★∈) (here ())
StarMeet-∀νᵢ meet .meet-starᵢ {X = suc X}
    (there l★∈) (there r★∈) =
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
StarMeet-ν∀ᵢ meet .meet-starᵢ {X = suc X}
    (there l★∈) (there r★∈) =
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
StarMeet-ννᵢ meet .meet-starᵢ {X = suc X}
    (there l★∈) (there r★∈) =
  there (⇑ᴸᵢ-★∈
    (meet-starᵢ meet
      (un⇑ᴸᵢ-★∈ l★∈) (un⇑ᴸᵢ-★∈ r★∈)))

star-star-to-meetᵢ :
  ∀ {Φᴸ Φᴿ Φᶜ Δᶜ Δᴸ Δᴿ Δᵒ D} →
  StarMeetCtxᵢ Φᴸ Φᴿ Φᶜ →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᴿ →
  Φᶜ ∣ Δᶜ ⊢ D ⊑ ★ ⊣ Δᵒ
star-star-to-meetᵢ meet id★ id★ = id★
star-star-to-meetᵢ meet (tag ι) (tag .ι) = tag ι
star-star-to-meetᵢ meet (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  tag (star-star-to-meetᵢ meet p₁ q₁)
    ⇛ star-star-to-meetᵢ meet p₂ q₂
star-star-to-meetᵢ meet (tagˣ x★∈ X<Δ) (tagˣ y★∈ _) =
  tagˣ (meet-starᵢ meet x★∈ y★∈) X<Δ
star-star-to-meetᵢ meet
    (ν safeD occD D⊑★) (ν safeD′ occD′ D⊑★′) =
  ν safeD occD
    (star-star-to-meetᵢ (StarMeet-ννᵢ meet) D⊑★ D⊑★′)

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
ForwardCtx-∀ᵢ {Z = z} fwd .forward-starᵢ {X = suc .z}
    (there x★∈) refl =
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
ForwardCtx-νᵢ {Z = z} fwd .forward-starᵢ {X = suc .z}
    (there x★∈) refl =
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
occurs-forwardᵢ fwd (ν _ occA p) occ =
  occurs-forwardᵢ (ForwardCtx-νᵢ fwd) p occ

occurs-forward-idᵢ :
  ∀ {Δ A B} →
  idᵢ Δ ∣ Δ ⊢ A ⊑ B ⊣ Δ →
  occurs zero A ≡ true →
  occurs zero B ≡ true
occurs-forward-idᵢ {Δ = Δ} p occ =
  occurs-forwardᵢ (ForwardCtx-idᵢ Δ zero) p occ

subst-star-hit-varᵢ :
  ∀ k X →
  occurs k (＇ X) ≡ true →
  substᵗ (substVarFrom k ★) (＇ X) ≡ ★
subst-star-hit-varᵢ zero zero occ = refl
subst-star-hit-varᵢ zero (suc X) ()
subst-star-hit-varᵢ (suc k) zero ()
subst-star-hit-varᵢ (suc k) (suc X) occ =
  cong (renameᵗ suc)
    (subst-star-hit-varᵢ k X (trans (occurs-suc-var k X) occ))

subst-star-fresh-varᵢ :
  ∀ k X →
  occurs k (＇ X) ≡ false →
  substᵗ (substVarFrom k ★) (＇ X)
    ≡ renameᵗ (removeAtᵗ k) (＇ X)
subst-star-fresh-varᵢ zero zero ()
subst-star-fresh-varᵢ zero (suc X) occ = refl
subst-star-fresh-varᵢ (suc k) zero occ = refl
subst-star-fresh-varᵢ (suc k) (suc X) occ =
  cong (renameᵗ suc)
    (subst-star-fresh-varᵢ k X (trans (occurs-suc-var k X) occ))

drop-var-freshᵢ :
  ∀ {k Φ Ψ X Y} →
  DropAtᵢ k Φ Ψ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  occurs k (＇ X) ≡ false
drop-var-freshᵢ drop-zeroᵢ (here ())
drop-var-freshᵢ {X = zero} drop-zeroᵢ (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-var-freshᵢ {X = suc X} drop-zeroᵢ (there x∈) = refl
drop-var-freshᵢ {X = zero} {Y = zero} (drop-∀ᵢ d) (here refl) = refl
drop-var-freshᵢ {X = zero} {Y = suc Y} (drop-∀ᵢ d) (here ())
drop-var-freshᵢ {X = zero} (drop-∀ᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
drop-var-freshᵢ {X = suc X} {Y = zero} (drop-∀ᵢ d) (here ())
drop-var-freshᵢ {X = suc X} {Y = zero} (drop-∀ᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
drop-var-freshᵢ {X = suc X} {Y = suc Y} (drop-∀ᵢ d) (there x∈) =
  trans (sym (occurs-suc-var _ _))
    (drop-var-freshᵢ d (un⇑ᵢ-ˣ∈ x∈))
drop-var-freshᵢ (drop-νᵢ d) (here ())
drop-var-freshᵢ {X = zero} (drop-νᵢ d) (there x∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x∈)
drop-var-freshᵢ {X = suc X} (drop-νᵢ d) (there x∈) =
  trans (sym (occurs-suc-var _ _))
    (drop-var-freshᵢ d (un⇑ᴸᵢ-ˣ∈ x∈))

inst-star-atᵢ :
  ∀ {k Φ Ψ Δᴸ Δᴿ A B} →
  DropAtᵢ k Φ Ψ →
  k < suc Δᴸ →
  Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ ⊢ substᵗ (substVarFrom k ★) A ⊑ B ⊣ Δᴿ
inst-star-atᵢ d k<Δ id★ = id★
inst-star-atᵢ {k = k} d k<Δ (idˣ {X = X} x∈ X<Δ Y<Δ) =
  subst
    (λ S → _ ∣ _ ⊢ S ⊑ _ ⊣ _)
    (sym (subst-star-fresh-varᵢ k X (drop-var-freshᵢ d x∈)))
    (open-unused-atᵢ d k<Δ (drop-var-freshᵢ d x∈)
      (idˣ x∈ X<Δ Y<Δ))
inst-star-atᵢ d k<Δ idι = idι
inst-star-atᵢ d k<Δ (p ↦ q) =
  inst-star-atᵢ d k<Δ p ↦ inst-star-atᵢ d k<Δ q
inst-star-atᵢ {k = k} d k<Δ (∀ⁱ p) =
  ∀ⁱ (inst-star-atᵢ (drop-∀ᵢ d) (s<s k<Δ) p)
inst-star-atᵢ d k<Δ (tag ι) = tag ι
inst-star-atᵢ d k<Δ (tag p ⇛ q) =
  tag inst-star-atᵢ d k<Δ p ⇛ inst-star-atᵢ d k<Δ q
inst-star-atᵢ {k = k} d k<Δ (tagˣ {X = X} x∈ X<Δ)
    with occurs k (＇ X) in occX
inst-star-atᵢ {k = k} d k<Δ (tagˣ {X = X} x∈ X<Δ)
    | true =
  subst
    (λ S → _ ∣ _ ⊢ S ⊑ ★ ⊣ _)
    (sym (subst-star-hit-varᵢ k X occX))
    id★
inst-star-atᵢ {k = k} d k<Δ (tagˣ {X = X} x∈ X<Δ)
    | false =
  subst
    (λ S → _ ∣ _ ⊢ S ⊑ ★ ⊣ _)
    (sym (subst-star-fresh-varᵢ k X occX))
    (open-unused-atᵢ d k<Δ occX (tagˣ x∈ X<Δ))
inst-star-atᵢ {k = k} d k<Δ (ν {A = A} safe occA p) =
  ν (substNonVar (extsᵗ (substVarFrom k ★)) safe)
    (trans (occurs-extsNᵗ-below 1 (substVarFrom k ★) zero A z<s) occA)
    (inst-star-atᵢ (drop-νᵢ d) (s<s k<Δ) p)

inst-starᵢ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A [ ★ ]ᵗ ⊑ B ⊣ Δᴿ
inst-starᵢ = inst-star-atᵢ drop-zeroᵢ z<s

sizeTy-renameᵢ :
  ∀ ρ A →
  sizeTy (renameᵗ ρ A) ≡ sizeTy A
sizeTy-renameᵢ ρ (＇ X) = refl
sizeTy-renameᵢ ρ (‵ ι) = refl
sizeTy-renameᵢ ρ ★ = refl
sizeTy-renameᵢ ρ (A ⇒ B)
    rewrite sizeTy-renameᵢ ρ A | sizeTy-renameᵢ ρ B =
  refl
sizeTy-renameᵢ ρ (`∀ A)
    rewrite sizeTy-renameᵢ (extᵗ ρ) A =
  refl

sizeTy-subst-star-varᵢ :
  ∀ k X →
  sizeTy (substVarFrom k ★ X) ≡ 1
sizeTy-subst-star-varᵢ zero zero = refl
sizeTy-subst-star-varᵢ zero (suc X) = refl
sizeTy-subst-star-varᵢ (suc k) zero = refl
sizeTy-subst-star-varᵢ (suc k) (suc X) =
  trans (sizeTy-renameᵢ suc (substVarFrom k ★ X))
    (sizeTy-subst-star-varᵢ k X)

sizeTy-subst-starᵢ :
  ∀ k A →
  sizeTy (substᵗ (substVarFrom k ★) A) ≡ sizeTy A
sizeTy-subst-starᵢ k (＇ X) = sizeTy-subst-star-varᵢ k X
sizeTy-subst-starᵢ k (‵ ι) = refl
sizeTy-subst-starᵢ k ★ = refl
sizeTy-subst-starᵢ k (A ⇒ B)
    rewrite sizeTy-subst-starᵢ k A | sizeTy-subst-starᵢ k B =
  refl
sizeTy-subst-starᵢ k (`∀ A)
    rewrite sizeTy-subst-starᵢ (suc k) A =
  refl

record StarInstCtxᵢ (k : TyVar) (Φ : ImpCtx) (Δ : TyCtx) : Set where
  field
    star-index<ᵢ : k < suc Δ

    star-hitᵢ : (k ˣ⊑★) ∈ Φ

    star-freshᵢ :
      ∀ {X} →
      X < suc Δ →
      occurs k (＇ X) ≡ false →
      (X ˣ⊑ˣ removeAtᵗ k X) ∈ Φ

open StarInstCtxᵢ

StarInst-zeroᵢ :
  ∀ Δ →
  StarInstCtxᵢ zero (νᵢᶜ (idᵢ Δ)) Δ
StarInst-zeroᵢ Δ .star-index<ᵢ = z<s
StarInst-zeroᵢ Δ .star-hitᵢ = here refl
StarInst-zeroᵢ Δ .star-freshᵢ {X = zero} X<Δ ()
StarInst-zeroᵢ Δ .star-freshᵢ {X = suc X} (s<s X<Δ) occ =
  there (⇑ᴸᵢ-ˣ∈ (idᵢ-lookup X<Δ))

StarInst-∀ᵢ :
  ∀ {k Φ Δ} →
  StarInstCtxᵢ k Φ Δ →
  StarInstCtxᵢ (suc k) (∀ᵢᶜ Φ) (suc Δ)
StarInst-∀ᵢ inst .star-index<ᵢ = s<s (star-index<ᵢ inst)
StarInst-∀ᵢ inst .star-hitᵢ = there (⇑ᵢ-★∈ (star-hitᵢ inst))
StarInst-∀ᵢ inst .star-freshᵢ {X = zero} X<Δ occ = here refl
StarInst-∀ᵢ {k = k} inst .star-freshᵢ {X = suc X} (s<s X<Δ) occ =
  there
    (⇑ᵢ-ˣ∈
      (star-freshᵢ inst X<Δ (trans (occurs-suc-var k X) occ)))

star-inst-lower-atᵢ :
  ∀ {k Φ Δ A} →
  (inst : StarInstCtxᵢ k Φ Δ) →
  WfTy (suc Δ) A →
  Φ ∣ suc Δ ⊢ A ⊑ substᵗ (substVarFrom k ★) A ⊣ Δ
star-inst-lower-atᵢ {k = k} inst (wfVar {X = X} X<Δ)
    with occurs k (＇ X) in occX
star-inst-lower-atᵢ {k = k} inst (wfVar {X = X} X<Δ)
    | true =
  subst
    (λ T → _ ∣ _ ⊢ ＇ X ⊑ T ⊣ _)
    (sym (subst-star-hit-varᵢ k X occX))
    (tagˣ
      (subst (λ Z → (Z ˣ⊑★) ∈ _) (sym (occurs-var-true→≡ᵢ occX))
        (star-hitᵢ inst))
      X<Δ)
star-inst-lower-atᵢ {k = k} inst (wfVar {X = X} X<Δ)
    | false =
  subst
    (λ T → _ ∣ _ ⊢ ＇ X ⊑ T ⊣ _)
    (sym (subst-star-fresh-varᵢ k X occX))
    (idˣ
      (star-freshᵢ inst X<Δ occX)
      X<Δ
      (removeAt-Wfᵢ k (star-index<ᵢ inst) X<Δ occX))
star-inst-lower-atᵢ inst wfBase = idι
star-inst-lower-atᵢ inst wf★ = id★
star-inst-lower-atᵢ inst (wf⇒ hA hB) =
  star-inst-lower-atᵢ inst hA ↦ star-inst-lower-atᵢ inst hB
star-inst-lower-atᵢ inst (wf∀ hA) =
  ∀ⁱ (star-inst-lower-atᵢ (StarInst-∀ᵢ inst) hA)

star-inst-lowerᵢ :
  ∀ {Δ A} →
  WfTy (suc Δ) A →
  νᵢᶜ (idᵢ Δ) ∣ suc Δ ⊢ A ⊑ A [ ★ ]ᵗ ⊣ Δ
star-inst-lowerᵢ {Δ = Δ} = star-inst-lower-atᵢ (StarInst-zeroᵢ Δ)

close-star-lowerᵢ :
  ∀ {Δ A} →
  {{NonVar A}} →
  occurs zero A ≡ true →
  WfTy (suc Δ) A →
  idᵢ Δ ∣ Δ ⊢ `∀ A ⊑ A [ ★ ]ᵗ ⊣ Δ
close-star-lowerᵢ {{safe}} occA hA =
  ν safe occA (star-inst-lowerᵢ hA)

inst-star-commonᵢ :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ C ⊑ A ⊣ Δᴸ →
  νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ C ⊑ B ⊣ Δᴿ →
  (Φᴸ ∣ Δᶜ ⊢ C [ ★ ]ᵗ ⊑ A ⊣ Δᴸ) ×
  (Φᴿ ∣ Δᶜ ⊢ C [ ★ ]ᵗ ⊑ B ⊣ Δᴿ)
inst-star-commonᵢ C⊑A C⊑B = inst-starᵢ C⊑A , inst-starᵢ C⊑B

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

nested-used-star-lower :
  νᵢᶜ [] ∣ 1 ⊢ `∀ (★ ⇒ ＇ 1) ⊑ `∀ ★ ⊣ 0
nested-used-star-lower =
  ∀ⁱ (tag id★ ⇛ tagˣ (there (here refl)) (s<s z<s))

no-nested-used-star-lower :
  ∀ᵢᶜ [] ∣ 1 ⊢ `∀ (★ ⇒ ＇ 1) ⊑ ★ ⊣ 1 →
  ⊥
no-nested-used-star-lower (ν nonvar-fun () p)

no-nested-used-body-factor :
  ¬ (∃[ R ]
      (idᵢ 1 ∣ 1 ⊢ `∀ (★ ⇒ ＇ 1) ⊑ R ⊣ 1 ×
       ∀ᵢᶜ [] ∣ 1 ⊢ R ⊑ ★ ⊣ 1))
no-nested-used-body-factor (R , D⊑R , R⊑★) =
  no-nested-used-star-lower (⊑-trans-left-idᵢ D⊑R R⊑★)

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

  enumMLB-νν-complete :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
    {{NonVar D}} →
    (sourceFuel : ℕ) →
    SourceFuel sourceFuel (`∀ D) →
    EnoughFuel fuel A B →
    WfImpCtx² Δᶜ Δᴸ Φᴸ →
    WfImpCtx² Δᶜ Δᴿ Φᴿ →
    StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
    occurs zero D ≡ true →
    νᵢᶜ Φᴸ ∣ suc Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
    νᵢᶜ Φᴿ ∣ suc Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
    ∃[ E ]
      (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
       idᵢ Δᶜ ∣ Δᶜ ⊢ `∀ D ⊑ E ⊣ Δᶜ)
  enumMLB-νν-complete
      .(suc zero)
      (source-ok {budget = zero} ())
      enough hΦᴸ hΦᴿ meet occD D⊑A D⊑B
  enumMLB-νν-complete {D = D}
      .(suc (suc sourceFuel))
      source@(source-ok {budget = suc sourceFuel} enoughSource)
      enough hΦᴸ hΦᴿ meet occD D⊑A D⊑B
      with enumMLB-complete (suc sourceFuel)
             (source-ok
               (subst
                 (λ n → n ≤ sourceFuel)
                 (sym (sizeTy-subst-starᵢ zero D))
                 (s≤s⁻¹ enoughSource)))
             enough hΦᴸ hΦᴿ meet
             (inst-starᵢ D⊑A) (inst-starᵢ D⊑B)
  enumMLB-νν-complete {D = D}
      .(suc (suc sourceFuel))
      source@(source-ok {budget = suc sourceFuel} enoughSource)
      enough hΦᴸ hΦᴿ meet occD D⊑A D⊑B
      | E , E∈ , D★⊑E =
    E , E∈ ,
    ⊑-trans-idᵢ (close-star-lowerᵢ occD (⊑-src-wf D⊑A)) D★⊑E

  enumMLB-complete :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B D} →
    (sourceFuel : ℕ) →
    SourceFuel sourceFuel D →
    EnoughFuel fuel A B →
    WfImpCtx² Δᶜ Δᴸ Φᴸ →
    WfImpCtx² Δᶜ Δᴿ Φᴿ →
    StarMeetCtxᵢ Φᴸ Φᴿ (idᵢ Δᶜ) →
    Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
    Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
    ∃[ E ]
      (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
       idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
  enumMLB-complete {fuel = zero}
      sourceFuel source enough hΦᴸ hΦᴿ meet D⊑A D⊑B =
    ⊥-elim (fuel-zero-impossible enough)
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete _ sourceFuelFor (fuel-∀∀-both enough)
             (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (StarMeet-∀∀ᵢ meet) D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , D⊑E =
    `∀ E ,
    dedupe-complete (∈-++-left (wrapAll-complete E∈)) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      with enumMLB-complete-used (fuel-∀∀-left enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀∀-left enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (∈-++-right
        {xs =
          wrapAll
            (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
              (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)}
        (∈-++-left
          (wrapAllIfOccurs-complete
            (nonVar-forward-if-occursᵢ D⊑E safeD occE)
            occE E∈))) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀∀-right enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀∀-right enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
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
          (wrapAllIfOccurs-complete
            (nonVar-forward-if-occursᵢ D⊑E safeD occE)
            occE E∈))) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    enumMLB-νν-complete {{safeD}}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ＇ X}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ＇ X}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      with enumMLB-complete-used (fuel-∀L enough)
             (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀L enough)
                 (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-∀νᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (∀ⁱ D⊑A) (ν safeD occD D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      with enumMLB-complete-used (fuel-∀R enough)
             (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
             (λ meet′ D′⊑A D′⊑B →
               enumMLB-complete _ sourceFuelFor (fuel-∀R enough)
                 (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
                 meet′ D′⊑A D′⊑B)
             (StarMeet-ν∀ᵢ meet)
             occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (∀ⁱ D⊑B)
      | E , E∈ , occE , D⊑E =
    `∀ E ,
    dedupe-complete
      (wrapAllIfOccurs-complete
        (nonVar-forward-if-occursᵢ D⊑E safeD occE)
        occE E∈) ,
    ∀ⁱ D⊑E
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet id★ id★ =
    ★ , here refl , id★
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = .(‵ ι)}
      sourceFuel source enough hΦᴸ hΦᴿ meet idι idι
      with ι ≟Base ι
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = .(‵ ι)}
      sourceFuel source enough hΦᴸ hΦᴿ meet idι idι | yes refl =
    ‵ ι , here refl , idι
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = .(‵ ι)}
      sourceFuel source enough hΦᴸ hΦᴿ meet idι idι | no neq =
    ⊥-elim (neq refl)
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet idι (tag .ι) =
    ‵ ι , here refl , idι
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ‵ ι}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tag .ι) idι =
    ‵ ι , here refl , idι
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂)
      with enumMLB-complete _ sourceFuelFor (fuel-⇒⇒-left enough)
             hΦᴸ hΦᴿ meet D₁⊑A₁ D₁⊑B₁
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁
      with enumMLB-complete _ sourceFuelFor (fuel-⇒⇒-right enough)
             hΦᴸ hΦᴿ meet D₂⊑A₂ D₂⊑B₂
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
    E₁ ⇒ E₂ ,
    arrowProducts-complete E₁∈ E₂∈ ,
    D₁⊑E₁ ↦ D₂⊑E₂
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★)
      with enumMLB-complete _ sourceFuelFor (fuel-⇒★-left enough)
             hΦᴸ hΦᴿ meet D₁⊑A₁ D₁⊑★
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★)
      | E₁ , E₁∈ , D₁⊑E₁
      with enumMLB-complete _ sourceFuelFor (fuel-⇒★-right enough)
             hΦᴸ hΦᴿ meet D₂⊑A₂ D₂⊑★
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★)
      | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
    E₁ ⇒ E₂ ,
    arrowProducts-complete E₁∈ E₂∈ ,
    D₁⊑E₁ ↦ D₂⊑E₂
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂)
      with enumMLB-complete _ sourceFuelFor (fuel-★⇒-left enough)
             hΦᴸ hΦᴿ meet D₁⊑★ D₁⊑B₁
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁
      with enumMLB-complete _ sourceFuelFor (fuel-★⇒-right enough)
             hΦᴸ hΦᴿ meet D₂⊑★ D₂⊑B₂
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂)
      | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
    E₁ ⇒ E₂ ,
    arrowProducts-complete E₁∈ E₂∈ ,
    D₁⊑E₁ ↦ D₂⊑E₂
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = ＇ Y}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (idˣ {X = X′} X′⊑X X′<Δ X<Δᴸ) (idˣ X′⊑Y _ Y<Δᴿ) =
    ＇ X′ ,
    varCandidatesUpTo-complete
      X′<Δ
      (varCandidate-var-var-complete X′⊑X X′⊑Y) ,
    idˣ (idᵢ-lookup X′<Δ) X′<Δ X′<Δ
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (idˣ {X = X′} X′⊑X X′<Δ X<Δᴸ) (tagˣ X′⊑★ _) =
    ＇ X′ ,
    varCandidatesUpTo-complete
      X′<Δ
      (varCandidate-var-star-complete X′⊑X X′⊑★) ,
    idˣ (idᵢ-lookup X′<Δ) X′<Δ X′<Δ
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ＇ Y}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tagˣ {X = X′} X′⊑★ X′<Δ) (idˣ X′⊑Y _ Y<Δᴿ) =
    ＇ X′ ,
    varCandidatesUpTo-complete
      X′<Δ
      (varCandidate-star-var-complete X′⊑★ X′⊑Y) ,
    idˣ (idᵢ-lookup X′<Δ) X′<Δ X′<Δ
  enumMLB-complete {fuel = suc fuel} {Δᶜ = Δᶜ} {A = ★} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      p@(tagˣ X′⊑★ X′<Δ) q@(tagˣ X′⊑★′ _) =
    ★ ,
    here refl ,
    star-star-to-meetᵢ {Δᵒ = Δᶜ} meet p q
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tag ι) (tag .ι) =
    ★ , here refl , tag ι
  enumMLB-complete {fuel = suc fuel} {Δᶜ = Δᶜ} {A = ★} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (tag D₁⊑★ ⇛ D₂⊑★) (tag D₁⊑★′ ⇛ D₂⊑★′) =
    ★ , here refl , star-star-to-meetᵢ {Δᵒ = Δᶜ} meet
      (tag D₁⊑★ ⇛ D₂⊑★) (tag D₁⊑★′ ⇛ D₂⊑★′)
  enumMLB-complete {fuel = suc fuel} {A = ＇ X} {D = `∀ D}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν _ occD D⊑A) (ν _ occD′ D⊑B) =
    ⊥-elim (no-occurs-var-lower-νctxᵢ occD D⊑A)
  enumMLB-complete {fuel = suc fuel} {A = ‵ ι}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν _ occD D⊑A) (ν _ occD′ D⊑B) =
    ⊥-elim (no-occurs-base-lowerᵢ occD D⊑A)
  enumMLB-complete {fuel = suc fuel} {Δᶜ = Δᶜ}
      {A = ★} {B = ★} {D = `∀ D}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    ★ ,
    here refl ,
    ν safeD occD
      (star-star-to-meetᵢ {Δᵒ = Δᶜ}
        (StarMeet-ννᵢ meet) D⊑A D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ＇ Y} {D = `∀ D}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν _ occD D⊑A) (ν _ occD′ D⊑B) =
    ⊥-elim (no-occurs-var-lower-νctxᵢ occD′ D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = ‵ ι} {D = `∀ D}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν _ occD D⊑A) (ν _ occD′ D⊑B) =
    ⊥-elim (no-occurs-base-lowerᵢ occD′ D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = `∀ B} {D = `∀ D}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    enumMLB-νν-complete {{safeD}}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = ★} {B = B₁ ⇒ B₂} {D = `∀ D}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    enumMLB-νν-complete {{safeD}}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = A₁ ⇒ A₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    enumMLB-νν-complete {{safeD}}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ＇ Y}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν _ occD D⊑A) (ν _ occD′ D⊑B) =
    ⊥-elim (no-occurs-var-lower-νctxᵢ occD′ D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν _ occD D⊑A) (ν _ occD′ D⊑B) =
    ⊥-elim (no-occurs-base-lowerᵢ occD′ D⊑B)
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = ★}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    enumMLB-νν-complete {{safeD}}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      occD D⊑A D⊑B
  enumMLB-complete {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      (ν safeD occD D⊑A) (ν safeD′ occD′ D⊑B) =
    enumMLB-νν-complete {{safeD}}
      sourceFuel source enough hΦᴸ hΦᴿ meet
      occD D⊑A D⊑B

rawEndpointMlbsAt-complete :
  ∀ {Δ A B D} →
  WfTy Δ A →
  WfTy Δ B →
  CommonLowerBoundᵢ Δ A B D →
  ∃[ E ]
    (E ∈ rawEndpointMlbsAt Δ A B ×
     idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
rawEndpointMlbsAt-complete {Δ = Δ} {A = A} {B = B} hA hB commonD =
  enumMLB-complete _ sourceFuelFor (fuelFor-enough {A = A} {B = B})
    (WfImpCtx-to² (idᵢ-wf Δ)) (WfImpCtx-to² (idᵢ-wf Δ))
    (StarMeet-idᵢ Δ) (proj₁ commonD) (proj₂ commonD)

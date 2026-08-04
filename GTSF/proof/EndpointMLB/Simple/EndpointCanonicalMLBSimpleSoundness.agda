module proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleSoundness where

-- File Charter:
--   * Top-down soundness skeleton for
--     `proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple.enumMLB`.
--   * Establishes the full recursive case split and stitches each branch to
--     the `ImprecisionWf` constructors.
--   * Discharges the list, context-lookup, and context-well-formedness helper
--     facts needed by the raw soundness theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; z<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Relation.Nullary using (yes; no)

open import Types
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimple using
  ( _==ᵇ_
  ; _andᵇ_
  ; allEndpointMlbsAt
  ; dedupe
  ; dedupeSeen
  ; endpointCtx
  ; enumMLB
  ; first
  ; fuelFor
  ; hasStrictAbove?
  ; hasStar
  ; hasVar
  ; memberTy?
  ; pruneStrictlyBelow
  ; pruneStrictlyBelowFrom
  ; rawEndpointMlbsAt
  ; simpleEndpointMlb
  ; MLB
  ; varCandidate?
  ; varCandidatesUpTo
  ; ∀ᵢᶜ
  ; νᵢᶜ
  ; wrapAll
  ; wrapAllIfOccurs
  ; arrowProducts
  )
open import proof.Core.Properties.ImprecisionProperties using
  ( WfImpCtx²
  ; WfImpCtx-to²
  ; idᵢ-wf
  ; ∀ᵢ-wf²
  ; ⇑ᴸᵢ-wf²
  ; nonVar?
  )

------------------------------------------------------------------------
-- Layer 3 proof obligations
------------------------------------------------------------------------

==ᵇ-true :
  ∀ {X Y} →
  (X ==ᵇ Y) ≡ true →
  X ≡ Y
==ᵇ-true {X = zero} {Y = zero} refl = refl
==ᵇ-true {X = zero} {Y = suc Y} ()
==ᵇ-true {X = suc X} {Y = zero} ()
==ᵇ-true {X = suc X} {Y = suc Y} eq = cong suc (==ᵇ-true eq)

andᵇ-true :
  ∀ {a b} →
  (_andᵇ_ a b) ≡ true →
  a ≡ true × b ≡ true
andᵇ-true {a = true} {b = true} refl = refl , refl
andᵇ-true {a = true} {b = false} ()
andᵇ-true {a = false} {b = true} ()
andᵇ-true {a = false} {b = false} ()

hasVar-sound :
  ∀ {W X Φ} →
  hasVar W X Φ ≡ true →
  (W ˣ⊑ˣ X) ∈ Φ

hasVar-head-sound :
  ∀ {W X z w Φ} →
  W ≡ z →
  X ≡ w →
  (W ˣ⊑ˣ X) ∈ ((z ˣ⊑ˣ w) ∷ Φ)
hasVar-head-sound refl refl = here refl

hasStar-head-sound :
  ∀ {W z Φ} →
  W ≡ z →
  (W ˣ⊑★) ∈ ((z ˣ⊑★) ∷ Φ)
hasStar-head-sound refl = here refl

hasVar-sound {Φ = []} ()
hasVar-sound {W = W} {X = X} {Φ = (z ˣ⊑★) ∷ Φ} ok =
  there (hasVar-sound ok)
hasVar-sound {W = W} {X = X} {Φ = (z ˣ⊑ˣ w) ∷ Φ} ok
    with W ==ᵇ z in eqW | X ==ᵇ w in eqX
hasVar-sound {W = W} {X = X} {Φ = (z ˣ⊑ˣ w) ∷ Φ} ok
    | true | true =
  hasVar-head-sound (==ᵇ-true eqW) (==ᵇ-true eqX)
hasVar-sound {W = W} {X = X} {Φ = (z ˣ⊑ˣ w) ∷ Φ} ok
    | true | false =
  there (hasVar-sound ok)
hasVar-sound {W = W} {X = X} {Φ = (z ˣ⊑ˣ w) ∷ Φ} ok
    | false | true =
  there (hasVar-sound ok)
hasVar-sound {W = W} {X = X} {Φ = (z ˣ⊑ˣ w) ∷ Φ} ok
    | false | false =
  there (hasVar-sound ok)

hasStar-sound :
  ∀ {W Φ} →
  hasStar W Φ ≡ true →
  (W ˣ⊑★) ∈ Φ
hasStar-sound {Φ = []} ()
hasStar-sound {W = W} {Φ = (z ˣ⊑★) ∷ Φ} ok
    with W ==ᵇ z in eqW
hasStar-sound {W = W} {Φ = (z ˣ⊑★) ∷ Φ} ok | true =
  hasStar-head-sound (==ᵇ-true eqW)
hasStar-sound {W = W} {Φ = (z ˣ⊑★) ∷ Φ} ok | false =
  there (hasStar-sound ok)
hasStar-sound {W = W} {Φ = (z ˣ⊑ˣ w) ∷ Φ} ok =
  there (hasStar-sound ok)

∈-++-split :
  ∀ {C : Ty} {xs ys : List Ty} →
  C ∈ xs ++ ys →
  C ∈ xs ⊎ C ∈ ys
∈-++-split {xs = []} C∈ = inj₂ C∈
∈-++-split {xs = A ∷ As} (here refl) = inj₁ (here refl)
∈-++-split {xs = A ∷ As} (there C∈)
    with ∈-++-split {xs = As} C∈
∈-++-split {xs = A ∷ As} (there C∈) | inj₁ C∈As =
  inj₁ (there C∈As)
∈-++-split {xs = A ∷ As} (there C∈) | inj₂ C∈ys =
  inj₂ C∈ys

dedupeSeen-sound :
  ∀ {C : Ty} {seen xs : List Ty} →
  C ∈ dedupeSeen seen xs →
  C ∈ xs
dedupeSeen-sound {xs = []} ()
dedupeSeen-sound {seen = seen} {xs = A ∷ As} C∈
    with memberTy? A seen
dedupeSeen-sound {seen = seen} {xs = A ∷ As} C∈ | true =
  there (dedupeSeen-sound {seen = seen} {xs = As} C∈)
dedupeSeen-sound {seen = seen} {xs = A ∷ As} (here refl) | false =
  here refl
dedupeSeen-sound {seen = seen} {xs = A ∷ As} (there C∈) | false =
  there (dedupeSeen-sound {seen = A ∷ seen} {xs = As} C∈)

dedupe-sound :
  ∀ {C : Ty} {xs : List Ty} →
  C ∈ dedupe xs →
  C ∈ xs
dedupe-sound C∈ = dedupeSeen-sound C∈

wrapAll-sound :
  ∀ {C : Ty} {xs : List Ty} →
  C ∈ wrapAll xs →
  ∃[ C₀ ] (C ≡ `∀ C₀ × C₀ ∈ xs)
wrapAll-sound {xs = []} ()
wrapAll-sound {xs = A ∷ As} (here refl) =
  A , refl , here refl
wrapAll-sound {xs = A ∷ As} (there C∈)
    with wrapAll-sound {xs = As} C∈
wrapAll-sound {xs = A ∷ As} (there C∈) | C₀ , eq , C₀∈ =
  C₀ , eq , there C₀∈

wrapAllIfOccurs-sound :
  ∀ {C : Ty} {xs : List Ty} →
  C ∈ wrapAllIfOccurs xs →
  ∃[ C₀ ]
    (C ≡ `∀ C₀ × NonVar C₀ ×
      (occurs zero C₀ ≡ true) × C₀ ∈ xs)
wrapAllIfOccurs-sound {xs = []} ()
wrapAllIfOccurs-sound {xs = A ∷ As} C∈
    with nonVar? A | occurs zero A in occA
wrapAllIfOccurs-sound {xs = A ∷ As} (here refl)
    | yes safe | true =
  A , refl , safe , occA , here refl
wrapAllIfOccurs-sound {xs = A ∷ As} (there C∈)
    | yes safe | true
    with wrapAllIfOccurs-sound {xs = As} C∈
wrapAllIfOccurs-sound {xs = A ∷ As} (there C∈)
    | yes safe | true | C₀ , eq , safeC₀ , occC₀ , C₀∈ =
  C₀ , eq , safeC₀ , occC₀ , there C₀∈
wrapAllIfOccurs-sound {xs = A ∷ As} C∈ | yes safe | false
    with wrapAllIfOccurs-sound {xs = As} C∈
wrapAllIfOccurs-sound {xs = A ∷ As} C∈ | yes safe | false
    | C₀ , eq , safeC₀ , occC₀ , C₀∈ =
  C₀ , eq , safeC₀ , occC₀ , there C₀∈
wrapAllIfOccurs-sound {xs = A ∷ As} C∈ | no ¬safe | occA
    with wrapAllIfOccurs-sound {xs = As} C∈
wrapAllIfOccurs-sound {xs = A ∷ As} C∈ | no ¬safe | occA
    | C₀ , eq , safeC₀ , occC₀ , C₀∈ =
  C₀ , eq , safeC₀ , occC₀ , there C₀∈

mapArrow-sound :
  ∀ {A C : Ty} {Bs : List Ty} →
  C ∈ map (λ B → A ⇒ B) Bs →
  ∃[ B ] (C ≡ A ⇒ B × B ∈ Bs)
mapArrow-sound {Bs = []} ()
mapArrow-sound {Bs = B ∷ Bs} (here refl) =
  B , refl , here refl
mapArrow-sound {Bs = B ∷ Bs} (there C∈)
    with mapArrow-sound {Bs = Bs} C∈
mapArrow-sound {Bs = B ∷ Bs} (there C∈) | B₀ , eq , B₀∈ =
  B₀ , eq , there B₀∈

arrowProducts-sound :
  ∀ {C : Ty} {xs ys : List Ty} →
  C ∈ arrowProducts xs ys →
  ∃[ C₁ ] ∃[ C₂ ] (C ≡ C₁ ⇒ C₂ × C₁ ∈ xs × C₂ ∈ ys)
arrowProducts-sound {xs = []} ()
arrowProducts-sound {xs = A ∷ As} {ys = Bs} C∈
    with ∈-++-split {xs = map (λ B → A ⇒ B) Bs} C∈
arrowProducts-sound {xs = A ∷ As} {ys = Bs} C∈ | inj₁ C∈map
    with mapArrow-sound C∈map
arrowProducts-sound {xs = A ∷ As} {ys = Bs} C∈ | inj₁ C∈map
    | B , refl , B∈ =
  A , B , refl , here refl , B∈
arrowProducts-sound {xs = A ∷ As} {ys = Bs} C∈ | inj₂ C∈products
    with arrowProducts-sound {xs = As} {ys = Bs} C∈products
arrowProducts-sound {xs = A ∷ As} {ys = Bs} C∈ | inj₂ C∈products
    | C₁ , C₂ , eq , C₁∈ , C₂∈ =
  C₁ , C₂ , eq , there C₁∈ , C₂∈

νᵢᶜ-wf² :
  ∀ {Δᶜ Δ Φ} →
  WfImpCtx² Δᶜ Δ Φ →
  WfImpCtx² (suc Δᶜ) Δ (νᵢᶜ Φ)
νᵢᶜ-wf² hΦ (here refl) = z<s
νᵢᶜ-wf² hΦ (there a∈) = ⇑ᴸᵢ-wf² hΦ a∈

idˣ-from-hasVar :
  ∀ {W X Φ Δᶜ Δ} →
  WfImpCtx² Δᶜ Δ Φ →
  hasVar W X Φ ≡ true →
  Φ ∣ Δᶜ ⊢ ＇ W ⊑ ＇ X ⊣ Δ
idˣ-from-hasVar hΦ ok =
  idˣ W⊑X (proj₁ (hΦ W⊑X)) (proj₂ (hΦ W⊑X))
  where
    W⊑X = hasVar-sound ok

tagˣ-from-hasStar :
  ∀ {W Φ Δᶜ Δ} →
  WfImpCtx² Δᶜ Δ Φ →
  hasStar W Φ ≡ true →
  Φ ∣ Δᶜ ⊢ ＇ W ⊑ ★ ⊣ Δ
tagˣ-from-hasStar hΦ ok =
  tagˣ W⊑★ (hΦ W⊑★)
  where
    W⊑★ = hasStar-sound ok

varCandidate?-sound :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B W} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  varCandidate? Φᴸ Φᴿ A B W ≡ true →
  Φᴸ ∣ Δᶜ ⊢ ＇ W ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ ＇ W ⊑ B ⊣ Δᴿ

varCandidate?-sound {A = ＇ X} {B = ＇ Y} hΦᴸ hΦᴿ ok
    with andᵇ-true ok
varCandidate?-sound {A = ＇ X} {B = ＇ Y} hΦᴸ hΦᴿ ok
    | okᴸ , okᴿ =
  idˣ-from-hasVar hΦᴸ okᴸ , idˣ-from-hasVar hΦᴿ okᴿ

varCandidate?-sound {A = ＇ X} {B = (‵ ι)} hΦᴸ hΦᴿ ()

varCandidate?-sound {A = ＇ X} {B = ★} hΦᴸ hΦᴿ ok
    with andᵇ-true ok
varCandidate?-sound {A = ＇ X} {B = ★} hΦᴸ hΦᴿ ok
    | okᴸ , okᴿ =
  idˣ-from-hasVar hΦᴸ okᴸ , tagˣ-from-hasStar hΦᴿ okᴿ

varCandidate?-sound {A = ＇ X} {B = B₁ ⇒ B₂} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = ＇ X} {B = `∀ B} hΦᴸ hΦᴿ ()

varCandidate?-sound {A = (‵ ι)} {B = ＇ Y} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = (‵ ι)} {B = (‵ ι′)} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = (‵ ι)} {B = ★} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = (‵ ι)} {B = B₁ ⇒ B₂} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = (‵ ι)} {B = `∀ B} hΦᴸ hΦᴿ ()

varCandidate?-sound {A = ★} {B = ＇ Y} hΦᴸ hΦᴿ ok
    with andᵇ-true ok
varCandidate?-sound {A = ★} {B = ＇ Y} hΦᴸ hΦᴿ ok
    | okᴸ , okᴿ =
  tagˣ-from-hasStar hΦᴸ okᴸ , idˣ-from-hasVar hΦᴿ okᴿ

varCandidate?-sound {A = ★} {B = (‵ ι)} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = ★} {B = ★} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = ★} {B = B₁ ⇒ B₂} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = ★} {B = `∀ B} hΦᴸ hΦᴿ ()

varCandidate?-sound {A = A₁ ⇒ A₂} {B = ＇ Y} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = A₁ ⇒ A₂} {B = (‵ ι)} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = A₁ ⇒ A₂} {B = ★} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = A₁ ⇒ A₂} {B = `∀ B} hΦᴸ hΦᴿ ()

varCandidate?-sound {A = `∀ A} {B = ＇ Y} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = `∀ A} {B = (‵ ι)} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = `∀ A} {B = ★} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = `∀ A} {B = B₁ ⇒ B₂} hΦᴸ hΦᴿ ()
varCandidate?-sound {A = `∀ A} {B = `∀ B} hΦᴸ hΦᴿ ()

varCandidatesUpTo-sound-at :
  ∀ {limit Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ A B limit →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
varCandidatesUpTo-sound-at {limit = zero} hΦᴸ hΦᴿ ()
varCandidatesUpTo-sound-at {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {A = A} {B = B} hΦᴸ hΦᴿ C∈
    with varCandidate? Φᴸ Φᴿ A B n in ok
varCandidatesUpTo-sound-at {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {A = A} {B = B} hΦᴸ hΦᴿ C∈ | true
    with ∈-++-split
           {xs = varCandidatesUpTo Φᴸ Φᴿ A B n}
           {ys = ＇ n ∷ []}
           C∈
varCandidatesUpTo-sound-at {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {A = A} {B = B} hΦᴸ hΦᴿ C∈ | true | inj₁ C∈old =
  varCandidatesUpTo-sound-at {limit = n} hΦᴸ hΦᴿ C∈old
varCandidatesUpTo-sound-at {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {A = A} {B = B} hΦᴸ hΦᴿ C∈ | true | inj₂ (here refl) =
  varCandidate?-sound hΦᴸ hΦᴿ ok
varCandidatesUpTo-sound-at {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {A = A} {B = B} hΦᴸ hΦᴿ C∈ | true | inj₂ (there ())
varCandidatesUpTo-sound-at {limit = suc n} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {A = A} {B = B} hΦᴸ hΦᴿ C∈ | false =
  varCandidatesUpTo-sound-at {limit = n} hΦᴸ hΦᴿ C∈

varCandidatesUpTo-sound :
  ∀ {Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ varCandidatesUpTo Φᴸ Φᴿ A B Δᶜ →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ
varCandidatesUpTo-sound {Δᶜ = Δᶜ} hΦᴸ hΦᴿ C∈ =
  varCandidatesUpTo-sound-at {limit = Δᶜ} hΦᴸ hΦᴿ C∈

forallBothCandidates :
  ℕ → ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Ty → Ty → List Ty
forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B =
  wrapAll
    (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)

leftForallCandidates :
  ℕ → ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Ty → Ty → List Ty
leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B =
  wrapAllIfOccurs
    (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A B)

rightForallCandidates :
  ℕ → ImpCtx → ImpCtx → TyCtx → TyCtx → TyCtx → Ty → Ty → List Ty
rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B =
  wrapAllIfOccurs
    (enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) A B)

------------------------------------------------------------------------
-- Layer 2: raw enumerator soundness
------------------------------------------------------------------------

enumMLB-sound :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ C ⊑ A ⊣ Δᴸ ×
  Φᴿ ∣ Δᶜ ⊢ C ⊑ B ⊣ Δᴿ

enumMLB-sound {fuel = zero} hΦᴸ hΦᴿ ()

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈
    with ∈-++-split
           {xs = forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B}
           {ys =
             leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ++
             rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
           (dedupe-sound
             {xs =
               forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ++
               leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ++
               rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₁ C∈both
    with wrapAll-sound
           {xs =
             enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
               (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B}
           C∈both
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₁ C∈both | C₀ , refl , C₀∈
    with enumMLB-sound {fuel = fuel} (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₁ C∈both | C₀ , refl , C₀∈ | C₀⊑A , C₀⊑B =
  ∀ⁱ C₀⊑A , ∀ⁱ C₀⊑B
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight
    with ∈-++-split
           {xs = leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B)}
           {ys = rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
           C∈leftOrRight
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight | inj₁ C∈leftOnly
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
               (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B)}
           C∈leftOnly
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight | inj₁ C∈leftOnly
    | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight | inj₁ C∈leftOnly
    | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑∀B =
  ∀ⁱ C₀⊑A , ν safeC₀ occC₀ C₀⊑∀B
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight | inj₂ C∈rightOnly
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
               (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B}
           C∈rightOnly
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight | inj₂ C∈rightOnly
    | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | inj₂ C∈leftOrRight | inj₂ C∈rightOnly
    | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑∀A , C₀⊑B =
  ν safeC₀ occC₀ C₀⊑∀A , ∀ⁱ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
               (suc Δᶜ) (suc Δᴸ) Δᴿ A (＇ Y)}
           (dedupe-sound
             {xs = leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (＇ Y)}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ∀ⁱ C₀⊑A , ν safeC₀ occC₀ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = (‵ ι)}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
               (suc Δᶜ) (suc Δᴸ) Δᴿ A (‵ ι)}
           (dedupe-sound
             {xs = leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (‵ ι)}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = (‵ ι)}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = (‵ ι)}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ∀ⁱ C₀⊑A , ν safeC₀ occC₀ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = ★}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
               (suc Δᶜ) (suc Δᴸ) Δᴿ A ★}
           (dedupe-sound
             {xs = leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A ★}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = ★}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = ★}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ∀ⁱ C₀⊑A , ν safeC₀ occC₀ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
               (suc Δᶜ) (suc Δᴸ) Δᴿ A (B₁ ⇒ B₂)}
           (dedupe-sound
             {xs =
               leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (B₁ ⇒ B₂)}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ∀ⁱ C₀⊑A , ν safeC₀ occC₀ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ＇ X} {B = `∀ B}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
               (suc Δᶜ) Δᴸ (suc Δᴿ) (＇ X) B}
           (dedupe-sound
             {xs = rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) B}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ＇ X} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ＇ X} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ν safeC₀ occC₀ C₀⊑A , ∀ⁱ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = (‵ ι)} {B = `∀ B}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
               (suc Δᶜ) Δᴸ (suc Δᴿ) (‵ ι) B}
           (dedupe-sound
             {xs = rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) B}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = (‵ ι)} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = (‵ ι)} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ν safeC₀ occC₀ C₀⊑A , ∀ⁱ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = `∀ B}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
               (suc Δᶜ) Δᴸ (suc Δᴿ) ★ B}
           (dedupe-sound
             {xs = rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ν safeC₀ occC₀ C₀⊑A , ∀ⁱ C₀⊑B

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = `∀ B}
    hΦᴸ hΦᴿ C∈
    with wrapAllIfOccurs-sound
           {xs =
             enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
               (suc Δᶜ) Δᴸ (suc Δᴿ) (A₁ ⇒ A₂) B}
           (dedupe-sound
             {xs =
               rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) B}
             C∈)
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈
    with enumMLB-sound {fuel = fuel} (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ) C₀∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ | C₀ , refl , safeC₀ , occC₀ , C₀∈ | C₀⊑A , C₀⊑B =
  ν safeC₀ occC₀ C₀⊑A , ∀ⁱ C₀⊑B

enumMLB-sound {fuel = suc fuel} {A = ★} {B = ★}
    hΦᴸ hΦᴿ (here refl) =
  id★ , id★
enumMLB-sound {fuel = suc fuel} {A = ★} {B = ★}
    hΦᴸ hΦᴿ (there ())

enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = (‵ ι′)}
    hΦᴸ hΦᴿ C∈
    with ι ≟Base ι′
enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = (‵ ι′)}
    hΦᴸ hΦᴿ (here refl) | yes refl =
  idι , idι
enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = (‵ ι′)}
    hΦᴸ hΦᴿ (there ()) | yes refl
enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = (‵ ι′)}
    hΦᴸ hΦᴿ () | no neq

enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = ★}
    hΦᴸ hΦᴿ (here refl) =
  idι , tag ι
enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = ★}
    hΦᴸ hΦᴿ (there ())

enumMLB-sound {fuel = suc fuel} {A = ★} {B = (‵ ι)}
    hΦᴸ hΦᴿ (here refl) =
  tag ι , idι
enumMLB-sound {fuel = suc fuel} {A = ★} {B = (‵ ι)}
    hΦᴸ hΦᴿ (there ())

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂}
           C∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ | C₁ , C₂ , refl , C₁∈ , C₂∈
    with enumMLB-sound {fuel = fuel} hΦᴸ hΦᴿ C₁∈
       | enumMLB-sound {fuel = fuel} hΦᴸ hΦᴿ C₂∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ | C₁ , C₂ , refl , C₁∈ , C₂∈
    | C₁⊑A₁ , C₁⊑B₁ | C₂⊑A₂ , C₂⊑B₂ =
  C₁⊑A₁ ↦ C₂⊑A₂ , C₁⊑B₁ ↦ C₂⊑B₂

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★}
           C∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈ | C₁ , C₂ , refl , C₁∈ , C₂∈
    with enumMLB-sound {fuel = fuel} hΦᴸ hΦᴿ C₁∈
       | enumMLB-sound {fuel = fuel} hΦᴸ hΦᴿ C₂∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈ | C₁ , C₂ , refl , C₁∈ , C₂∈
    | C₁⊑A₁ , C₁⊑★ | C₂⊑A₂ , C₂⊑★ =
  C₁⊑A₁ ↦ C₂⊑A₂ , tag C₁⊑★ ⇛ C₂⊑★

enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂}
           C∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ | C₁ , C₂ , refl , C₁∈ , C₂∈
    with enumMLB-sound {fuel = fuel} hΦᴸ hΦᴿ C₁∈
       | enumMLB-sound {fuel = fuel} hΦᴸ hΦᴿ C₂∈
enumMLB-sound {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ | C₁ , C₂ , refl , C₁∈ , C₂∈
    | C₁⊑★ , C₁⊑B₁ | C₂⊑★ , C₂⊑B₂ =
  tag C₁⊑★ ⇛ C₂⊑★ , C₁⊑B₁ ↦ C₂⊑B₂

enumMLB-sound {fuel = suc fuel} {A = ＇ X} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ =
  varCandidatesUpTo-sound hΦᴸ hΦᴿ C∈

enumMLB-sound {fuel = suc fuel} {A = ＇ X} {B = ★}
    hΦᴸ hΦᴿ C∈ =
  varCandidatesUpTo-sound hΦᴸ hΦᴿ C∈

enumMLB-sound {fuel = suc fuel} {A = ★} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ =
  varCandidatesUpTo-sound hΦᴸ hΦᴿ C∈

enumMLB-sound {fuel = suc fuel} {A = ＇ X} {B = (‵ ι)}
    hΦᴸ hΦᴿ ()

enumMLB-sound {fuel = suc fuel} {A = ＇ X} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ ()

enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = ＇ Y}
    hΦᴸ hΦᴿ ()

enumMLB-sound {fuel = suc fuel} {A = (‵ ι)} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ ()

enumMLB-sound {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ＇ Y}
    hΦᴸ hΦᴿ ()

enumMLB-sound {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = (‵ ι)}
    hΦᴸ hΦᴿ ()

------------------------------------------------------------------------
-- Endpoint boundary for raw endpoint enumeration
------------------------------------------------------------------------

rawEndpointMlbsAt-sound :
  ∀ {Δ A B C} →
  C ∈ rawEndpointMlbsAt Δ A B →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
rawEndpointMlbsAt-sound {Δ = Δ} {A = A} {B = B} C∈ =
  enumMLB-sound
    {fuel = fuelFor A B}
    {Φᴸ = idᵢ Δ}
    {Φᴿ = idᵢ Δ}
    {Δᶜ = Δ}
    {Δᴸ = Δ}
    {Δᴿ = Δ}
    {A = A}
    {B = B}
    (WfImpCtx-to² (idᵢ-wf Δ))
    (WfImpCtx-to² (idᵢ-wf Δ))
    C∈

pruneStrictlyBelowFrom-sound :
  ∀ {Δ C all} {xs : List Ty} →
  C ∈ pruneStrictlyBelowFrom Δ all xs →
  C ∈ xs
pruneStrictlyBelowFrom-sound {xs = []} ()
pruneStrictlyBelowFrom-sound {Δ = Δ} {all = all} {xs = A ∷ As} C∈
    with hasStrictAbove? Δ A all
pruneStrictlyBelowFrom-sound {Δ = Δ} {all = all} {xs = A ∷ As} C∈
    | true =
  there (pruneStrictlyBelowFrom-sound C∈)
pruneStrictlyBelowFrom-sound {Δ = Δ} {all = all} {xs = A ∷ As} (here refl)
    | false =
  here refl
pruneStrictlyBelowFrom-sound {Δ = Δ} {all = all} {xs = A ∷ As} (there C∈)
    | false =
  there (pruneStrictlyBelowFrom-sound C∈)

pruneStrictlyBelow-sound :
  ∀ {Δ C} {xs : List Ty} →
  C ∈ pruneStrictlyBelow Δ xs →
  C ∈ xs
pruneStrictlyBelow-sound C∈ = pruneStrictlyBelowFrom-sound C∈

first-sound :
  ∀ {C xs} →
  first xs ≡ just C →
  C ∈ xs
first-sound {xs = []} ()
first-sound {xs = A ∷ As} refl = here refl

allEndpointMlbsAt-sound :
  ∀ {Δ A B C} →
  C ∈ allEndpointMlbsAt Δ A B →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
allEndpointMlbsAt-sound {Δ = Δ} {A = A} {B = B} C∈ =
  rawEndpointMlbsAt-sound
    (dedupe-sound
      {xs = rawEndpointMlbsAt Δ A B}
      (pruneStrictlyBelow-sound
        {Δ = Δ}
        {xs = dedupe (rawEndpointMlbsAt Δ A B)}
        C∈))

MLB-sound :
  ∀ {Δ A B C} →
  MLB Δ A B ≡ just C →
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
MLB-sound {Δ = Δ} {A = A} {B = B} eq =
  allEndpointMlbsAt-sound (first-sound {xs = allEndpointMlbsAt Δ A B} eq)

simpleEndpointMlb-sound :
  ∀ {A B C} →
  simpleEndpointMlb A B ≡ just C →
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ C ⊑ A ⊣ endpointCtx A B ×
  idᵢ (endpointCtx A B) ∣ endpointCtx A B ⊢ C ⊑ B ⊣ endpointCtx A B
simpleEndpointMlb-sound {A = A} {B = B} eq =
  MLB-sound {Δ = endpointCtx A B} eq

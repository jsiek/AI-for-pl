module proof.EndpointCanonicalMLBSimpleMaximality where

-- File Charter:
--   * Maximality proof boundary for the simple exhaustive endpoint MLB
--     algorithm.
--   * Keeps the durable pruning-to-maximality assembly and leaves the raw
--     upper-cone coverage theorem as the current semantic proof frontier.
--   * The next proof plan targets that coverage theorem with occurrence-based
--     elimination of the omitted `ν`/`ν` route.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary using (Dec; ¬_; no; yes)

open import Types
open import Imprecision using (ImpCtx; idᵢ)
open import ImprecisionWf
open import proof.EndpointCanonicalMLBSimple using
  ( allEndpointMlbsAt; dedupe; endpointCtx; enumMLB; fuelFor
  ; hasStrictAbove?
  ; pruneStrictlyBelow; pruneStrictlyBelowFrom; rawEndpointMlbsAt
  ; simpleEndpointMlb; simpleEndpointMlbAt; strictlyBelow?; ∀ᵢᶜ; νᵢᶜ
  )
open import proof.EndpointCanonicalMLBSimpleSoundness using
  ( arrowProducts-sound; dedupe-sound; first-sound
  ; forallBothCandidates; leftForallCandidates; pruneStrictlyBelow-sound
  ; rightForallCandidates; wrapAll-sound; wrapAllIfOccurs-sound
  ; ∈-++-split; νᵢᶜ-wf²
  )
open import proof.ImprecisionProperties using
  (WfImpCtx²; WfImpCtx-to²; idᵢ-wf; ∀ᵢ-wf²)
open import proof.MaximalLowerBoundsWf using
  (CommonLowerBoundᵢ; ⊑-trans-idᵢ)

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

data CloseNeither : Ty → Ty → Set where
  close-neither-true :
    ∀ {C} →
    occurs zero C ≡ true →
    CloseNeither C (`∀ C)

  close-neither-false :
    ∀ {C E} →
    occurs zero C ≡ false →
    E ≡ C [ zero ]ᴿ →
    CloseNeither C E

data EnumMLB⁺ :
    ℕ → ImpCtx → ImpCtx → ℕ → ℕ → ℕ → Ty → Ty → Ty → Set where
  supported⁺ :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
    C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
    EnumMLB⁺ fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C

  fourth-νν⁺ :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C E} →
    CloseNeither C E →
    EnumMLB⁺ fuel (νᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) Δᴸ Δᴿ (`∀ A) (`∀ B) C →
    EnumMLB⁺ (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) E

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

enumMLB-∀∀-route :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C} →
  C ∈ enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) →
  C ∈ forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ⊎
  (C ∈ leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) ⊎
   C ∈ rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B)
enumMLB-∀∀-route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
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
enumMLB-∀∀-route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
    | inj₁ C∈both =
  inj₁ C∈both
enumMLB-∀∀-route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
    | inj₂ C∈leftOrRight
    with ∈-++-split
           {xs = leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B)}
           {ys = rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B}
           C∈leftOrRight
enumMLB-∀∀-route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
    | inj₂ C∈leftOrRight | inj₁ C∈left =
  inj₂ (inj₁ C∈left)
enumMLB-∀∀-route {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} C∈
    | inj₂ C∈leftOrRight | inj₂ C∈right =
  inj₂ (inj₂ C∈right)

data ∀∀UpperConeRoute :
    ℕ → ImpCtx → ImpCtx → ℕ → ℕ → ℕ → Ty → Ty → Ty → Ty → Set where
  ∀∀-both-preserved :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C C₀ D} →
    C ∈ forallBothCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
    C ≡ `∀ C₀ →
    C₀ ∈ enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B →
    (∀ᵢᶜ Φᴸ) ∣ suc Δᶜ ⊢ D ⊑ A ⊣ suc Δᴸ →
    (∀ᵢᶜ Φᴿ) ∣ suc Δᶜ ⊢ D ⊑ B ⊣ suc Δᴿ →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ C₀ ⊑ D ⊣ suc Δᶜ →
    ∀∀UpperConeRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C (`∀ D)

  ∀∀-left-preserved :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C C₀ D} →
    C ∈ leftForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) →
    C ≡ `∀ C₀ →
    occurs zero C₀ ≡ true →
    C₀ ∈ enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
      (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B) →
    (∀ᵢᶜ Φᴸ) ∣ suc Δᶜ ⊢ D ⊑ A ⊣ suc Δᴸ →
    (νᵢᶜ Φᴿ) ∣ suc Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ C₀ ⊑ D ⊣ suc Δᶜ →
    ∀∀UpperConeRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C (`∀ D)

  ∀∀-right-preserved :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C C₀ D} →
    C ∈ rightForallCandidates fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B →
    C ≡ `∀ C₀ →
    occurs zero C₀ ≡ true →
    C₀ ∈ enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
      (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B →
    (νᵢᶜ Φᴸ) ∣ suc Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
    (∀ᵢᶜ Φᴿ) ∣ suc Δᶜ ⊢ D ⊑ B ⊣ suc Δᴿ →
    idᵢ (suc Δᶜ) ∣ suc Δᶜ ⊢ C₀ ⊑ D ⊣ suc Δᶜ →
    ∀∀UpperConeRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C (`∀ D)

postulate
  enumMLB-∀∀-upper-cone-route :
    ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
    WfImpCtx² Δᶜ Δᴸ Φᴸ →
    WfImpCtx² Δᶜ Δᴿ Φᴿ →
    C ∈ enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) →
    Φᴸ ∣ Δᶜ ⊢ D ⊑ `∀ A ⊣ Δᴸ →
    Φᴿ ∣ Δᶜ ⊢ D ⊑ `∀ B ⊣ Δᴿ →
    idᵢ Δᶜ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
    ∀∀UpperConeRoute fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D

enumMLB⁺-covers-upper-cone :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  ∃[ E ]
    (EnumMLB⁺ fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B E ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
enumMLB⁺-covers-upper-cone {fuel = zero} hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    with enumMLB-∀∀-upper-cone-route
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = A} {B = B}
           hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | ∀∀-both-preserved _ refl C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
    with enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = ∀ᵢᶜ Φᴸ} {Φᴿ = ∀ᵢᶜ Φᴿ}
           {Δᶜ = suc Δᶜ} {Δᴸ = suc Δᴸ} {Δᴿ = suc Δᴿ}
           {A = A} {B = B}
           (∀ᵢ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
           C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | ∀∀-both-preserved _ refl C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
    | E , E∈ , D⊑E =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | ∀∀-left-preserved _ refl _ C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
    with enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = ∀ᵢᶜ Φᴸ} {Φᴿ = νᵢᶜ Φᴿ}
           {Δᶜ = suc Δᶜ} {Δᴸ = suc Δᴸ} {Δᴿ = Δᴿ}
           {A = A} {B = `∀ B}
           (∀ᵢ-wf² hΦᴸ) (νᵢᶜ-wf² hΦᴿ)
           C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | ∀∀-left-preserved _ refl _ C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
    | E , E∈ , D⊑E =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | ∀∀-right-preserved _ refl _ C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
    with enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = νᵢᶜ Φᴸ} {Φᴿ = ∀ᵢᶜ Φᴿ}
           {Δᶜ = suc Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = suc Δᴿ}
           {A = `∀ A} {B = B}
           (νᵢᶜ-wf² hΦᴸ) (∀ᵢ-wf² hΦᴿ)
           C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = `∀ A} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | ∀∀-right-preserved _ refl _ C₀∈ D⊑A₀ D⊑B₀ C₀⊑D
    | E , E∈ , D⊑E =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = `∀ A} {B = ★}
    hΦᴸ hΦᴿ C∈ (∀ⁱ D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = `∀ A} {B = ★}
    hΦᴸ hΦᴿ C∈ (ν occD D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
    hΦᴸ hΦᴿ C∈ (∀ⁱ D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = `∀ A} {B = ‵ ι}
    hΦᴸ hΦᴿ C∈ (ν occD D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = `∀ A} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ (∀ⁱ D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = `∀ A} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ (ν occD D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (∀ⁱ D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = `∀ A} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (ν occD D⊑A) D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (∀ⁱ D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (ν occD D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (∀ⁱ D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (ν occD D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ＇ X} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (∀ⁱ D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ＇ X} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (ν occD D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (∀ⁱ D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = `∀ B}
    hΦᴸ hΦᴿ C∈ D⊑A (ν occD D⊑B) C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = ★}
    hΦᴸ hΦᴿ (here refl) D⊑A D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = ★}
    hΦᴸ hΦᴿ (there ()) D⊑A D⊑B C⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = ‵ ι}
    hΦᴸ hΦᴿ (here refl) D⊑A D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = ‵ ι}
    hΦᴸ hΦᴿ (there ()) D⊑A D⊑B C⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ★} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂}
           C∈
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈
    with C⊑D
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | C₁⊑D₁ ↦ C₂⊑D₂
    with enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = ★} {B = B₁}
           hΦᴸ hΦᴿ C₁∈ D₁⊑★ D₁⊑B₁ C₁⊑D₁
       | enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = ★} {B = B₂}
           hΦᴸ hΦᴿ C₂∈ D₂⊑★ D₂⊑B₂ C₂⊑D₂
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (tag D₁⊑★ ⇛ D₂⊑★) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | C₁⊑D₁ ↦ C₂⊑D₂
    | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂}
           C∈
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈
    with C⊑D
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = ★} {B = B₁ ⇒ B₂}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | ()
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ★}
    hΦᴸ hΦᴿ (here refl) D⊑A D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ★}
    hΦᴸ hΦᴿ (there ()) D⊑A D⊑B C⊑D
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ‵ ι′}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    with ι ≟Base ι′
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ‵ .ι}
    hΦᴸ hΦᴿ (here refl) D⊑A D⊑B C⊑D | yes refl =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ‵ .ι}
    hΦᴸ hΦᴿ (there ()) D⊑A D⊑B C⊑D | yes refl
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ‵ ι′}
    hΦᴸ hΦᴿ () D⊑A D⊑B C⊑D | no neq
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ‵ ι} {B = ＇ Y}
    hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = ‵ ι} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ＇ X} {B = ★}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ＇ X} {B = ‵ ι}
    hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone {fuel = suc fuel} {A = ＇ X} {B = ＇ Y}
    hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = ＇ X} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★) C⊑D
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★}
           C∈
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈
    with C⊑D
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | C₁⊑D₁ ↦ C₂⊑D₂
    with enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = A₁} {B = ★}
           hΦᴸ hΦᴿ C₁∈ D₁⊑A₁ D₁⊑★ C₁⊑D₁
       | enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = A₂} {B = ★}
           hΦᴸ hΦᴿ C₂∈ D₂⊑A₂ D₂⊑★ C₂⊑D₂
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (tag D₁⊑★ ⇛ D₂⊑★) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | C₁⊑D₁ ↦ C₂⊑D₂
    | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★}
           C∈
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈
    with C⊑D
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A₁ ⇒ A₂} {B = ★}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | ()
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ‵ ι}
    hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {A = A₁ ⇒ A₂} {B = ＇ Y}
    hΦᴸ hΦᴿ ()
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂}
           C∈
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈
    with C⊑D
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | C₁⊑D₁ ↦ C₂⊑D₂
    with enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = A₁} {B = B₁}
           hΦᴸ hΦᴿ C₁∈ D₁⊑A₁ D₁⊑B₁ C₁⊑D₁
       | enumMLB⁺-covers-upper-cone
           {fuel = fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
           {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
           {A = A₂} {B = B₂}
           hΦᴸ hΦᴿ C₂∈ D₂⊑A₂ D₂⊑B₂ C₂⊑D₂
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    hΦᴸ hΦᴿ C∈ (D₁⊑A₁ ↦ D₂⊑A₂) (D₁⊑B₁ ↦ D₂⊑B₂) C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | C₁⊑D₁ ↦ C₂⊑D₂
    | E₁ , E₁∈ , D₁⊑E₁ | E₂ , E₂∈ , D₂⊑E₂ =
  {!!}
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    with arrowProducts-sound
           {xs = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁}
           {ys = enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂}
           C∈
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈
    with C⊑D
enumMLB⁺-covers-upper-cone
    {fuel = suc fuel} {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
    {Δᶜ = Δᶜ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A₁ ⇒ A₂} {B = B₁ ⇒ B₂}
    {D = `∀ D} hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    | C₁ , C₂ , refl , C₁∈ , C₂∈ | ()

enumMLB⁺-upper-cone-elim :
  ∀ {fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B C D E⁺} →
  WfImpCtx² Δᶜ Δᴸ Φᴸ →
  WfImpCtx² Δᶜ Δᴿ Φᴿ →
  C ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B →
  Φᴸ ∣ Δᶜ ⊢ D ⊑ A ⊣ Δᴸ →
  Φᴿ ∣ Δᶜ ⊢ D ⊑ B ⊣ Δᴿ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ C ⊑ D ⊣ Δᶜ →
  EnumMLB⁺ fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B E⁺ →
  idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E⁺ ⊣ Δᶜ →
  ∃[ E ]
    (E ∈ enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B ×
     idᵢ Δᶜ ∣ Δᶜ ⊢ D ⊑ E ⊣ Δᶜ)
enumMLB⁺-upper-cone-elim hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    (supported⁺ E∈) D⊑E =
  _ , E∈ , D⊑E
enumMLB⁺-upper-cone-elim hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    (fourth-νν⁺ (close-neither-true occE) E⁺∈) D⊑E =
  {!!}
enumMLB⁺-upper-cone-elim hΦᴸ hΦᴿ C∈ D⊑A D⊑B C⊑D
    (fourth-νν⁺ (close-neither-false noOccE eqE) E⁺∈) D⊑E =
  {!!}

rawEndpointMlbsAt-covers-upper-cone :
  ∀ {Δ A B C D} →
  WfTy Δ A →
  WfTy Δ B →
  C ∈ rawEndpointMlbsAt Δ A B →
  CommonLowerBoundᵢ Δ A B D →
  idᵢ Δ ∣ Δ ⊢ C ⊑ D ⊣ Δ →
  ∃[ E ]
    (E ∈ rawEndpointMlbsAt Δ A B ×
     idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
rawEndpointMlbsAt-covers-upper-cone {Δ = Δ} {A = A} {B = B} {D = D}
    hA hB C∈ (D⊑A , D⊑B) C⊑D =
  enumMLB⁺-upper-cone-elim
    {fuel = fuelFor A B} {Φᴸ = idᵢ Δ} {Φᴿ = idᵢ Δ}
    {Δᶜ = Δ} {Δᴸ = Δ} {Δᴿ = Δ} {A = A} {B = B}
    (WfImpCtx-to² (idᵢ-wf Δ)) (WfImpCtx-to² (idᵢ-wf Δ))
    C∈ D⊑A D⊑B C⊑D E⁺∈ D⊑E⁺
  where
    coverage⁺ :
      ∃[ E⁺ ]
        (EnumMLB⁺ (fuelFor A B) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B E⁺ ×
         idᵢ Δ ∣ Δ ⊢ D ⊑ E⁺ ⊣ Δ)
    coverage⁺ =
      enumMLB⁺-covers-upper-cone
        {fuel = fuelFor A B} {Φᴸ = idᵢ Δ} {Φᴿ = idᵢ Δ}
        {Δᶜ = Δ} {Δᴸ = Δ} {Δᴿ = Δ} {A = A} {B = B}
        (WfImpCtx-to² (idᵢ-wf Δ)) (WfImpCtx-to² (idᵢ-wf Δ))
        C∈ D⊑A D⊑B C⊑D

    E⁺ : Ty
    E⁺ = proj₁ coverage⁺

    E⁺∈ : EnumMLB⁺ (fuelFor A B) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B E⁺
    E⁺∈ = proj₁ (proj₂ coverage⁺)

    D⊑E⁺ : idᵢ Δ ∣ Δ ⊢ D ⊑ E⁺ ⊣ Δ
    D⊑E⁺ = proj₂ (proj₂ coverage⁺)

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

    C∈raw : C ∈ rawEndpointMlbsAt Δ A B
    C∈raw = dedupe-sound C∈xs

    noAbove : hasStrictAbove? Δ C xs ≡ false
    noAbove = pruneStrictlyBelow-no-strict-above {Δ = Δ} {xs = xs} C∈

    coverage :
      ∃[ E ]
        (E ∈ rawEndpointMlbsAt Δ A B ×
         idᵢ Δ ∣ Δ ⊢ D ⊑ E ⊣ Δ)
    coverage =
      rawEndpointMlbsAt-covers-upper-cone hA hB C∈raw commonD C⊑D

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

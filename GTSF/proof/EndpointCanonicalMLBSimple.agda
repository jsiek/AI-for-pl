module proof.EndpointCanonicalMLBSimple where

-- File Charter:
--   * Simple executable endpoint maximal-lower-bound search for GTSF types.
--   * Implements the exhaustive route design from
--     `EndpointCanonicalMLBSimpleDesign.md`: try `∀ⁱ`/`∀ⁱ`, `∀ⁱ`/`ν`,
--     and `ν`/`∀ⁱ` directly, then prune strictly smaller candidates.
--   * This module is intentionally slow and proof-facing.  It does not replace
--     the efficient profile-based algorithm in `proof.EndpointCanonicalMLB`.

open import Agda.Builtin.Equality using (refl)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Relation.Nullary using (yes; no)

open import Types
open import Imprecision using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; idᵢ
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  )
open import proof.ImprecisionProperties using (genSafeSource?; imp?)

------------------------------------------------------------------------
-- Small utilities
------------------------------------------------------------------------

infix 4 _==ᵇ_

_==ᵇ_ : ℕ → ℕ → Bool
zero ==ᵇ zero = true
zero ==ᵇ suc n = false
suc m ==ᵇ zero = false
suc m ==ᵇ suc n = m ==ᵇ n

notᵇ : Bool → Bool
notᵇ true = false
notᵇ false = true

_andᵇ_ : Bool → Bool → Bool
true andᵇ b = b
false andᵇ b = false

maxℕ : ℕ → ℕ → ℕ
maxℕ zero n = n
maxℕ (suc m) zero = suc m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

mapMaybe : {A B : Set} → (A → Maybe B) → List A → List B
mapMaybe f [] = []
mapMaybe f (x ∷ xs) with f x
mapMaybe f (x ∷ xs) | nothing = mapMaybe f xs
mapMaybe f (x ∷ xs) | just y = y ∷ mapMaybe f xs

first : List Ty → Maybe Ty
first [] = nothing
first (A ∷ As) = just A

------------------------------------------------------------------------
-- Stable de-duplication
------------------------------------------------------------------------

memberTy? : Ty → List Ty → Bool
memberTy? A [] = false
memberTy? A (B ∷ Bs) with A ≟Ty B
memberTy? A (B ∷ Bs) | yes refl = true
memberTy? A (B ∷ Bs) | no neq = memberTy? A Bs

dedupeSeen : List Ty → List Ty → List Ty
dedupeSeen seen [] = []
dedupeSeen seen (A ∷ As) with memberTy? A seen
dedupeSeen seen (A ∷ As) | true = dedupeSeen seen As
dedupeSeen seen (A ∷ As) | false = A ∷ dedupeSeen (A ∷ seen) As

dedupe : List Ty → List Ty
dedupe = dedupeSeen []

------------------------------------------------------------------------
-- Context and variable lookup
------------------------------------------------------------------------

∀ᵢᶜ : ImpCtx → ImpCtx
∀ᵢᶜ Φ = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ

νᵢᶜ : ImpCtx → ImpCtx
νᵢᶜ Φ = (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ

-- X ⊑ Y ∈ Φ
hasVar : ℕ → ℕ → ImpCtx → Bool
hasVar X Y [] = false
hasVar X Y ((z ˣ⊑★) ∷ Φ) = hasVar X Y Φ
hasVar X Y ((z ˣ⊑ˣ w) ∷ Φ) with X ==ᵇ z | Y ==ᵇ w
hasVar X Y ((z ˣ⊑ˣ w) ∷ Φ) | true | true = true
hasVar X Y ((z ˣ⊑ˣ w) ∷ Φ) | _ | _ = hasVar X Y Φ

-- X ⊑ ★ ∈ Φ
hasStar : ℕ → ImpCtx → Bool
hasStar X [] = false
hasStar X ((z ˣ⊑★) ∷ Φ) with X ==ᵇ z
hasStar X ((z ˣ⊑★) ∷ Φ) | true = true
hasStar X ((z ˣ⊑★) ∷ Φ) | false = hasStar X Φ
hasStar X ((z ˣ⊑ˣ w) ∷ Φ) = hasStar X Φ

-- Do we have X′ ⊑ A and X′ ⊑ B ?
varCandidate? : ImpCtx → ImpCtx → Ty → Ty → ℕ → Bool
varCandidate? Φᴸ Φᴿ (＇ X) (＇ Y) X′ =  -- X′ ⊑ X ∈ Φᴸ  and  X′ ⊑ Y ∈ Φᴿ
  hasVar X′ X Φᴸ andᵇ hasVar X′ Y Φᴿ
varCandidate? Φᴸ Φᴿ (＇ X) ★ X′ =       -- X′ ⊑ X ∈ Φᴸ  and  X′ ⊑ ★ ∈ Φᴿ
  hasVar X′ X Φᴸ andᵇ hasStar X′ Φᴿ
varCandidate? Φᴸ Φᴿ ★ (＇ Y) X′ =       -- X′ ⊑ ★ ∈ Φᴸ  and  X′ ⊑ Y ∈ Φᴿ
  hasStar X′ Φᴸ andᵇ hasVar X′ Y Φᴿ
varCandidate? Φᴸ Φᴿ A B X′ = false

varCandidatesUpTo : ImpCtx → ImpCtx → Ty → Ty → ℕ → List Ty
varCandidatesUpTo Φᴸ Φᴿ A B zero = []
varCandidatesUpTo Φᴸ Φᴿ A B (suc n)
    with varCandidate? Φᴸ Φᴿ A B n
varCandidatesUpTo Φᴸ Φᴿ A B (suc n) | true =
  varCandidatesUpTo Φᴸ Φᴿ A B n ++ (＇ n ∷ [])
varCandidatesUpTo Φᴸ Φᴿ A B (suc n) | false =
  varCandidatesUpTo Φᴸ Φᴿ A B n

------------------------------------------------------------------------
-- Candidate construction
------------------------------------------------------------------------

wrapAll : List Ty → List Ty
wrapAll = map `∀

wrapAllIfOccurs : List Ty → List Ty
wrapAllIfOccurs [] = []
wrapAllIfOccurs (A ∷ As) with genSafeSource? A | occurs zero A
wrapAllIfOccurs (A ∷ As) | yes safe | true =
  `∀ A ∷ wrapAllIfOccurs As
wrapAllIfOccurs (A ∷ As) | yes safe | false =
  wrapAllIfOccurs As
wrapAllIfOccurs (A ∷ As) | no ¬safe | occ =
  wrapAllIfOccurs As

arrowProducts : List Ty → List Ty → List Ty
arrowProducts [] Bs = []
arrowProducts (A ∷ As) Bs =
  map (λ B → A ⇒ B) Bs ++ arrowProducts As Bs

mutual
  enumMLB :
    ℕ → ImpCtx → ImpCtx → ℕ → ℕ → ℕ → Ty → Ty → List Ty
  enumMLB zero Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A B = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) (`∀ B) =
    dedupe (both ++ leftOnly ++ rightOnly)
    where
      both =
        wrapAll
          (enumMLB fuel (∀ᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
            (suc Δᶜ) (suc Δᴸ) (suc Δᴿ) A B)
      leftOnly =
        wrapAllIfOccurs
          (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
            (suc Δᶜ) (suc Δᴸ) Δᴿ A (`∀ B))
      rightOnly =
        wrapAllIfOccurs
          (enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
            (suc Δᶜ) Δᴸ (suc Δᴿ) (`∀ A) B)
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (`∀ A) B =
    dedupe
      (wrapAllIfOccurs
        (enumMLB fuel (∀ᵢᶜ Φᴸ) (νᵢᶜ Φᴿ)
          (suc Δᶜ) (suc Δᴸ) Δᴿ A B))
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A (`∀ B) =
    dedupe
      (wrapAllIfOccurs
        (enumMLB fuel (νᵢᶜ Φᴸ) (∀ᵢᶜ Φᴿ)
          (suc Δᶜ) Δᴸ (suc Δᴿ) A B))
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ ★ = ★ ∷ []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) (‵ ι′) with ι ≟Base ι′
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) (‵ .ι) | yes refl =
    ‵ ι ∷ []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) (‵ ι′) | no neq = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) ★ = ‵ ι ∷ []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (‵ ι) = ‵ ι ∷ []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) (B₁ ⇒ B₂) =
    arrowProducts
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ B₁)
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ B₂)
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) ★ =
    arrowProducts
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₁ ★)
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ A₂ ★)
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (B₁ ⇒ B₂) =
    arrowProducts
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₁)
      (enumMLB fuel Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ B₂)
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) (＇ Y) =
    varCandidatesUpTo Φᴸ Φᴿ (＇ X) (＇ Y) Δᶜ
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) ★ =
    varCandidatesUpTo Φᴸ Φᴿ (＇ X) ★ Δᶜ
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ ★ (＇ Y) =
    varCandidatesUpTo Φᴸ Φᴿ ★ (＇ Y) Δᶜ
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) (‵ ι) = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (＇ X) (B₁ ⇒ B₂) = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) (＇ Y) = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (‵ ι) (B₁ ⇒ B₂) = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) (＇ Y) = []
  enumMLB (suc fuel) Φᴸ Φᴿ Δᶜ Δᴸ Δᴿ (A₁ ⇒ A₂) (‵ ι) = []

------------------------------------------------------------------------
-- Maximal pruning and public surface
------------------------------------------------------------------------

sizeTy : Ty → ℕ
sizeTy (＇ X) = 1
sizeTy (‵ ι) = 1
sizeTy ★ = 1
sizeTy (A ⇒ B) = suc (sizeTy A + sizeTy B)
sizeTy (`∀ A) = suc (sizeTy A)

fuelFor : Ty → Ty → ℕ
fuelFor A B = 20 + sizeTy A + sizeTy B + sizeTy A + sizeTy B

typeCtxBound : Ty → ℕ
typeCtxBound (＇ X) = suc X
typeCtxBound (‵ ι) = zero
typeCtxBound ★ = zero
typeCtxBound (A ⇒ B) = maxℕ (typeCtxBound A) (typeCtxBound B)
typeCtxBound (`∀ A) = typeCtxBound A ∸ 1

endpointCtx : Ty → Ty → ℕ
endpointCtx A B = maxℕ (typeCtxBound A) (typeCtxBound B)

below? : ℕ → Ty → Ty → Bool
below? Δ A B with imp? (idᵢ Δ) A B
below? Δ A B | yes p = true
below? Δ A B | no ¬p = false

strictlyBelow? : ℕ → Ty → Ty → Bool
strictlyBelow? Δ A B = below? Δ A B andᵇ notᵇ (below? Δ B A)

hasStrictAbove? : ℕ → Ty → List Ty → Bool
hasStrictAbove? Δ A [] = false
hasStrictAbove? Δ A (B ∷ Bs) with strictlyBelow? Δ A B
hasStrictAbove? Δ A (B ∷ Bs) | true = true
hasStrictAbove? Δ A (B ∷ Bs) | false = hasStrictAbove? Δ A Bs

pruneStrictlyBelowFrom : ℕ → List Ty → List Ty → List Ty
pruneStrictlyBelowFrom Δ all [] = []
pruneStrictlyBelowFrom Δ all (A ∷ As) with hasStrictAbove? Δ A all
pruneStrictlyBelowFrom Δ all (A ∷ As) | true =
  pruneStrictlyBelowFrom Δ all As
pruneStrictlyBelowFrom Δ all (A ∷ As) | false =
  A ∷ pruneStrictlyBelowFrom Δ all As

pruneStrictlyBelow : ℕ → List Ty → List Ty
pruneStrictlyBelow Δ xs = pruneStrictlyBelowFrom Δ xs xs

rawEndpointMlbsAt : ℕ → Ty → Ty → List Ty
rawEndpointMlbsAt Δ A B =
  enumMLB (fuelFor A B) (idᵢ Δ) (idᵢ Δ) Δ Δ Δ A B

allEndpointMlbsAt : ℕ → Ty → Ty → List Ty
allEndpointMlbsAt Δ A B =
  pruneStrictlyBelow Δ (dedupe (rawEndpointMlbsAt Δ A B))

MLB : ℕ → Ty → Ty → Maybe Ty
MLB Δ A B = first (allEndpointMlbsAt Δ A B)

rawEndpointMlbs : Ty → Ty → List Ty
rawEndpointMlbs A B = rawEndpointMlbsAt (endpointCtx A B) A B

allEndpointMlbs : Ty → Ty → List Ty
allEndpointMlbs A B = allEndpointMlbsAt (endpointCtx A B) A B

simpleEndpointMlb : Ty → Ty → Maybe Ty
simpleEndpointMlb A B = MLB (endpointCtx A B) A B

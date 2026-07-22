module proof.NuImprecisionGenUntagMismatchCounterexampleCore where

-- File Charter:
--   * Defines a source-`gen`/target-`untag` mismatch regression.
--   * Refutes source-gen target-ground agreement after `gen⊑groundᵀ` by
--     choosing distinct inner-tag and requested ground types.
--   * Exposes direct syntax, typing, QTI, runtime, and reduction witnesses.
--   * Introduces no result carrier, view, wrapper, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_)

import Coercions as C
open import ImprecisionWf using (id★; idι)
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( keep
  ; pure-step
  ; tag-untag-bad
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuTermImprecision using (seal★-tag-or-id)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-$
  ; no•-⟨⟩
  ; ok-no
  ; $
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (compatible-source-inert)
import Primitives as P
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; conv⊑convᵀ
  ; κ⊑κᵀ
  ; paired-widening
  ; ⊑cast⊒ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (cast-tag-or-id)
import Types as T
open import Relation.Binary.PropositionalEquality using (_≢_)
open import proof.NuImprecisionGenUntagCounterexampleCore using
  ( A
  ; G
  ; Φ₀
  ; Δ₀
  ; p
  ; q
  ; ρ₀
  ; exclusive₀
  ; body-cast
  ; gG
  ; source-gen
  ; source-gen-typing
  ; unique₀
  ; untag-typing
  )
open import
  proof.NuImprecisionSourceGenTargetGroundAgreementDef using
  (SourceGenTargetGroundAgreementᵀ)


HNat : T.Ty
HNat = T.‵ T.`ℕ

gNat : T.Ground HNat
gNat = T.‵ T.`ℕ

WNat : Term
WNat = $ (P.κℕ zero)

taggedNat : Term
taggedNat = WNat ⟨ HNat C.! ⟩

sourceValue : Term
sourceValue = taggedNat ⟨ source-gen ⟩

targetRedex : Term
targetRedex = taggedNat ⟨ G C.？ ⟩

nat-tag-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ HNat C.! ∶ HNat ⊑ T.★
nat-tag-typing =
  C.cast-tag T.wfBase gNat refl , NW.tag gNat

nat-tagged-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ taggedNat ⊑ taggedNat ⦂ T.★ ⊑ T.★ ∶ id★
nat-tagged-relation =
  conv⊑convᵀ
    (paired-widening
      cast-tag-or-id seal★-tag-or-id nat-tag-typing
      cast-tag-or-id seal★-tag-or-id nat-tag-typing
      (compatible-source-inert (HNat C.!)))
    (κ⊑κᵀ {n = zero})

source-value-tagged-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ sourceValue ⊑ taggedNat ⦂ A ⊑ T.★ ∶ p
source-value-tagged-relation =
  cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
    source-gen-typing nat-tagged-relation p

initial-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ sourceValue ⊑ targetRedex ⦂ A ⊑ G ∶ q
initial-relation =
  ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
    untag-typing source-value-tagged-relation q

vWNat : Value WNat
vWNat = $ (P.κℕ zero)

noWNat : No• WNat
noWNat = no•-$

vTaggedNat : Value taggedNat
vTaggedNat = vWNat ⟨ HNat C.! ⟩

noTaggedNat : No• taggedNat
noTaggedNat = no•-⟨⟩ noWNat

vSourceValue : Value sourceValue
vSourceValue = vTaggedNat ⟨ C.gen T.★ body-cast ⟩

noSourceValue : No• sourceValue
noSourceValue = no•-⟨⟩ noTaggedNat

source-runtime : RuntimeOK sourceValue
source-runtime = ok-no noSourceValue

target-runtime : RuntimeOK targetRedex
target-runtime = ok-no (no•-⟨⟩ noTaggedNat)

nat-not-function-ground : HNat ≢ G
nat-not-function-ground ()

target-blame-trace : targetRedex —↠[ keep ∷ [] ] NuTerms.blame
target-blame-trace =
  ↠-step
    (pure-step (tag-untag-bad vWNat nat-not-function-ground))
    ↠-refl

source-gen-target-ground-agreement-counterexample :
  SourceGenTargetGroundAgreementᵀ →
  ⊥
source-gen-target-ground-agreement-counterexample agreement =
  nat-not-function-ground
    (agreement exclusive₀ unique₀ gG source-gen-typing
      nat-tagged-relation q)

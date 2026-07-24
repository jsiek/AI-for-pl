module
  proof.Source.Core.NuImprecisionSourceGenTargetGroundAgreementCounterexample
  where

-- File Charter:
--   * Refutes source-`gen` target-ground agreement under the repaired
--     `GenSafe` grammar.
--   * Uses a safe function-shaped `gen` body and an unrelated active source
--     untag in the QTI premise to expose the missing source-value condition.
--   * Defines only concrete empty-world typing, QTI, and contradiction
--     witnesses; it introduces no postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_,_)

import Coercions as C
open import Coercions using (_∣_∣_⊢_∶_=⇒_)
open import ImprecisionWf using
  ( ImpCtx
  ; id★
  ; nonvar-fun
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _↦_
  ; _ˣ⊑★
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( StoreImp
  ; seal★-tag-or-id
  )
open import NuTerms using
  ( Term
  ; $
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (compatible-source-inert)
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; conv⊑convᵀ
  ; κ⊑κᵀ
  ; paired-widening
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (cast-tag-or-id)
import Primitives as P
import Types as T
open T using
  ( Ty
  ; TyCtx
  ; ★
  ; wfVar
  ; wf⇒
  ; ＇_
  ; _⇒_
  ; `∀
  )
open import Relation.Binary.PropositionalEquality using (_≢_)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.Source.Core.NuImprecisionSourceGenTargetGroundAgreementDef using
  (SourceGenTargetGroundAgreementᵀ)


Φ₀ : ImpCtx
Φ₀ = []

Δ₀ : TyCtx
Δ₀ = zero

ρ₀ : StoreImp Φ₀ Δ₀ Δ₀
ρ₀ = []

G : Ty
G = ★ ⇒ ★

X : Ty
X = ＇ zero

A : Ty
A = `∀ (X ⇒ X)

HNat : Ty
HNat = T.‵ T.`ℕ

wfG : T.WfTy zero G
wfG = wf⇒ T.wf★ T.wf★

gG : T.Ground G
gG = T.★⇒★

gNat : T.Ground HNat
gNat = T.‵ T.`ℕ

x★ : ((zero ˣ⊑★) ∷ []) ∣ suc zero ⊢ X ⊑ ★ ⊣ zero
x★ = tagˣ (here refl) z<s

q : [] ∣ zero ⊢ A ⊑ G ⊣ zero
q = ν nonvar-fun refl (x★ ↦ x★)

G⊑★ : [] ∣ zero ⊢ G ⊑ ★ ⊣ zero
G⊑★ = tag id★ ⇛ id★

body : C.Coercion
body = (X C.!) C.↦ (X C.？)

body-typing :
  C.genᵈ C.tag-or-idᵈ ∣ suc zero ∣ []
    ⊢ body ∶ G =⇒ (X ⇒ X)
body-typing =
  C.cast-fun
    (C.cast-tag (wfVar z<s) (T.＇ zero) refl)
    (C.cast-untag (wfVar z<s) (T.＇ zero) refl)

body-safe : NW.GenSafe body
body-safe = NW.safe-fun (NW.tag (T.＇ zero)) (NW.untag (T.＇ zero))

WNat : Term
WNat = $ (P.κℕ zero)

taggedNat : Term
taggedNat = WNat ⟨ HNat C.! ⟩

nat-not-function-ground : HNat ≢ G
nat-not-function-ground ()

exclusive₀ : SourceNameExclusive Φ₀
exclusive₀ ()

unique₀ : AssumptionMembershipUnique Φ₀
unique₀ ()

nat-tag-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ HNat C.! ∶ HNat ⊑ ★
nat-tag-typing =
  C.cast-tag T.wfBase gNat refl , NW.tag gNat

nat-tagged-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ taggedNat ⊑ taggedNat ⦂ ★ ⊑ ★ ∶ id★
nat-tagged-relation =
  conv⊑convᵀ
    (paired-widening
      cast-tag-or-id seal★-tag-or-id nat-tag-typing
      cast-tag-or-id seal★-tag-or-id nat-tag-typing
      (compatible-source-inert (HNat C.!)))
    (κ⊑κᵀ {n = zero})

function-untag-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ G C.？ ∶ ★ ⊒ G
function-untag-typing =
  C.cast-untag wfG gG refl , NW.untag gG

source-redex : Term
source-redex = taggedNat ⟨ G C.？ ⟩

source-target-tag-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ source-redex ⊑ taggedNat ⦂ G ⊑ ★ ∶ G⊑★
source-target-tag-relation =
  cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
    function-untag-typing nat-tagged-relation G⊑★

safe-gen-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ C.gen G body ∶ G ⊒ A
safe-gen-typing =
  C.cast-gen wfG refl body-typing , NW.gen body-safe

source-gen-target-ground-agreement-counterexample :
  SourceGenTargetGroundAgreementᵀ →
  ⊥
source-gen-target-ground-agreement-counterexample agreement =
  nat-not-function-ground
    (agreement exclusive₀ unique₀ gG safe-gen-typing
      source-target-tag-relation q)

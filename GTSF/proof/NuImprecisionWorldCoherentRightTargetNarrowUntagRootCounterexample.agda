module
  proof.NuImprecisionWorldCoherentRightTargetNarrowUntagRootCounterexample
  where

-- File Charter:
--   * Exhibits the proof-relevant index obstruction in target untagging.
--   * Inhabits the direct-tag premises with duplicate source-only assumptions.
--   * Proves that the untagged identity lambdas are not related at the
--     requested crossed pair of assumption witnesses.
--   * Proves that the strengthened reachable-world uniqueness premise rejects
--     exactly this duplicate-row context.
--   * Introduces no result carrier, postulate, hole, or permissive option.

open import Data.Empty using (⊥)
open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_,_; _×_)

import Coercions as C
open import Imprecision using (ImpCtx; _ˣ⊑★)
open import ImprecisionWf using
  ( _↦_
  ; _∣_⊢_⊑_⊣_
  ; tag_⇛_
  ; tagˣ
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( ctx-imp
  ; seal★-tag-or-id
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-`
  ; no•-ƛ
  ; no•-⟨⟩
  ; ok-no
  ; `_
  ; ƛ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; StoreImpPrefix
  ; prefix-reflⁱ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-tag-or-id
  )
open import Types using
  ( Ty
  ; wfVar
  ; wf★
  ; wf⇒
  ; ★
  ; ＇_
  ; _⇒_
  )
open import proof.NuDGGClosedWorld using (empty-store-wf)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherenceProof using
  (world-coherent-empty)


private
  Φ₂ : ImpCtx
  Φ₂ = (zero ˣ⊑★) ∷ (zero ˣ⊑★) ∷ []

  X : Ty
  X = ＇ zero

  A : Ty
  A = X ⇒ X

  H : Ty
  H = ★ ⇒ ★

  I : Term
  I = ƛ (` zero)

  a₁ : Φ₂ ∣ suc zero ⊢ X ⊑ ★ ⊣ zero
  a₁ = tagˣ (here refl) z<s

  a₂ : Φ₂ ∣ suc zero ⊢ X ⊑ ★ ⊣ zero
  a₂ = tagˣ (there (here refl)) z<s

  p : Φ₂ ∣ suc zero ⊢ A ⊑ ★ ⊣ zero
  p = tag a₁ ⇛ a₁

  q : Φ₂ ∣ suc zero ⊢ A ⊑ H ⊣ zero
  q = a₁ ↦ a₂

  vI : Value I
  vI = ƛ (` zero)

  noI : No• I
  noI = no•-ƛ no•-`

  tagged : Term
  tagged = I ⟨ (H C.!) ⟩

  v-tagged : Value tagged
  v-tagged = vI ⟨ (H C.!) ⟩

  no-tagged : No• tagged
  no-tagged = no•-⟨⟩ noI

  exclusive₂ : SourceNameExclusive Φ₂
  exclusive₂ star∈ (here ())
  exclusive₂ star∈ (there (here ()))
  exclusive₂ star∈ (there (there ()))

  coherent₂ :
    WorldCoherent
      ([] {A = NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
  coherent₂ = world-coherent-empty

  tag-typing :
    C.tag-or-idᵈ ∣ zero ∣ [] ⊢ (H C.!) ∶ H ⊑ ★
  tag-typing =
    C.cast-tag (wf⇒ wf★ wf★) Types.★⇒★ refl , NW.tag Types.★⇒★

  untag-typing :
    C.tag-or-idᵈ ∣ zero ∣ [] ⊢ (H C.？) ∶ ★ ⊒ H
  untag-typing =
    C.cast-untag (wf⇒ wf★ wf★) Types.★⇒★ refl ,
      NW.untag Types.★⇒★

  lambda-relation :
    Φ₂ ∣ suc zero ∣ zero ∣
      ([] {A = NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
      ∣ [] ⊢ᴺ I ⊑ I ⦂ A ⊑ H ∶ a₁ ↦ a₁
  lambda-relation =
    ƛ⊑ƛᵀ (wfVar z<s) wf★ (x⊑xᵀ Types.Z)

  tagged-relation :
    Φ₂ ∣ suc zero ∣ zero ∣
      ([] {A = NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
      ∣ [] ⊢ᴺ I ⊑ tagged ⦂ A ⊑ ★ ∶ p
  tagged-relation =
    ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
      tag-typing lambda-relation p

  runtime-untag : RuntimeOK (tagged ⟨ (H C.？) ⟩)
  runtime-untag = ok-no (no•-⟨⟩ no-tagged)

  variable-at-a₂-impossible :
    Φ₂ ∣ suc zero ∣ zero ∣
      ([] {A = NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
      ∣ ctx-imp X ★ a₁ ∷ []
      ⊢ᴺ ` zero ⊑ ` zero ⦂ X ⊑ ★ ∶ a₂ →
    ⊥
  variable-at-a₂-impossible (x⊑xᵀ ())
  variable-at-a₂-impossible
      (allocation-prefixᵀ prefix-reflⁱ inner
        source-typing target-typing) =
    variable-at-a₂-impossible inner


requested-untagged-relation-impossible :
  Φ₂ ∣ suc zero ∣ zero ∣
    ([] {A = NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
    ∣ [] ⊢ᴺ I ⊑ I ⦂ A ⊑ H ∶ q →
  ⊥
requested-untagged-relation-impossible
    (ƛ⊑ƛᵀ source-wf target-wf body) =
  variable-at-a₂-impossible body
requested-untagged-relation-impossible
    (allocation-prefixᵀ prefix-reflⁱ inner
      source-typing target-typing) =
  requested-untagged-relation-impossible inner


duplicate-assumptions-not-unique :
  AssumptionMembershipUnique Φ₂ →
  ⊥
duplicate-assumptions-not-unique unique
    with unique (here refl) (there (here refl))
duplicate-assumptions-not-unique unique | ()


old-untag-local-premises-are-inhabited :
  StoreImpPrefix
    ([] {A =
      NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
    [] ×
  WorldCoherent
    ([] {A =
      NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero}) ×
  SourceNameExclusive Φ₂ ×
  StoreWf zero [] ×
  RuntimeOK (tagged ⟨ (H C.？) ⟩) ×
  Value I ×
  No• I ×
  CastMode C.tag-or-idᵈ ×
  SealModeStore★ C.tag-or-idᵈ [] ×
  (C.tag-or-idᵈ ∣ zero ∣ [] ⊢ (H C.？) ∶ ★ ⊒ H) ×
  (Φ₂ ∣ suc zero ∣ zero ∣
    ([] {A =
      NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
    ∣ [] ⊢ᴺ I ⊑ tagged ⦂ A ⊑ ★ ∶ p)
old-untag-local-premises-are-inhabited =
  prefix-reflⁱ ,
  coherent₂ ,
  exclusive₂ ,
  empty-store-wf ,
  runtime-untag ,
  vI ,
  noI ,
  cast-tag-or-id ,
  seal★-tag-or-id ,
  untag-typing ,
  tagged-relation


direct-tag-premise-is-inhabited :
  Φ₂ ∣ suc zero ∣ zero ∣
    ([] {A = NuTermImprecision.StoreImpEntry Φ₂ (suc zero) zero})
    ∣ [] ⊢ᴺ I ⊑ tagged ⦂ A ⊑ ★ ∶ p
direct-tag-premise-is-inhabited = tagged-relation


untag-runtime-premise-is-inhabited :
  RuntimeOK (tagged ⟨ (H C.？) ⟩)
untag-runtime-premise-is-inhabited = runtime-untag


untag-typing-premise-is-inhabited :
  C.tag-or-idᵈ ∣ zero ∣ [] ⊢ (H C.？) ∶ ★ ⊒ H
untag-typing-premise-is-inhabited = untag-typing

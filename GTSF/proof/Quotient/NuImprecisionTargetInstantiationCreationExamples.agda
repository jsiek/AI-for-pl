module
  proof.Quotient.NuImprecisionTargetInstantiationCreationExamples
  where

-- File Charter:
--   * Tests whether target-instantiation allocation can be handled without
--     constructing the live fused post-administration QTI edge.
--   * Proves that the ordinary source-only-lambda plus target-cast
--     factorization fails on the smallest closed example.
--   * Constructs the exact target-instantiation creation residual and the
--     complete target reduction trace without using the live fused edge.
--   * Contains no postulate, hole, permissive option, or termination bypass.

import Coercions as C
import NarrowWiden as NW

open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  (shape-fun; shape-inst; shape-seal; shape-unseal)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s)
open import Data.Product using (_,_; proj₁)
open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionComposition using
  ( _↦ˢ_
  ; comp-idˣ-tagˣ
  ; comp-↦-↦
  ; comp-∀-ν
  ; tagˣˢ
  )
open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_; idˣ; tagˣ; ∀ⁱ_; ν)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( bind
  ; keep
  ; pure-step
  ; β-inst
  ; β-Λ•
  ; ν-step
  ; ξ-⟨⟩
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( lift-right-store-[]
  ; lift-store-[]
  ; store-right
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-ctx-[]
  )
open import proof.Core.Properties.SealModeProperties using
  (seal★-tag-or-id)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-`
  ; no•-ƛ
  ; no•-Λ
  ; `_
  ; ƛ_
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( ⊑cast⊑ᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; Λ⊑Λᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( cast-inst
  ; cast-tag-or-id
  ; ⊢`
  ; ⊢ƛ
  ; ⊢Λ
  ; ⊢⟨⟩⊑
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Ty
  ; wf★
  ; wf⇒
  ; ★
  ; Z
  ; ＇_
  ; _⇒_
  ; `∀
  ; ⇑ᵗ
  )
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using (⊑-target-lift-rightᵢ)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( target-instantiationᴿ
  ; x⊑xᴿ
  ; ƛ⊑ƛᴿ
  ; Λ⊑Λᴿ
  ; ⊑cast⊑ᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import proof.Core.Properties.TypePreservation using (seal★-inst)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( StoreImpPrefixᴿ
  ; TargetInstantiationCreation
  ; exact-creationᴱ
  ; prefix-reflᴿ
  ; target-instantiation-creation
  )


private
  I : Term
  I = ƛ (` zero)

  vI : Value I
  vI = ƛ (` zero)

  noI : No• I
  noI = no•-ƛ no•-`

  matched-variable-index :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ ＇ zero ⊑ ＇ zero ⊣ suc zero
  matched-variable-index =
    idˣ (here refl) z<s z<s

  matched-body-index :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero
      ⊢ (＇ zero ⇒ ＇ zero) ⊑ (＇ zero ⇒ ＇ zero)
      ⊣ suc zero
  matched-body-index =
    matched-variable-index ↦ matched-variable-index

  source-only-variable-index :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ ＇ zero ⊑ ★ ⊣ zero
  source-only-variable-index =
    tagˣ (here refl) z<s

  source-only-body-index :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero
      ⊢ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)
      ⊣ zero
  source-only-body-index =
    source-only-variable-index ↦ source-only-variable-index

  final-index :
    [] ∣ zero
      ⊢ `∀ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)
      ⊣ zero
  final-index =
    ν Imprecision.nonvar-fun refl source-only-body-index

  body-cast : C.Coercion
  body-cast =
    C.seal ★ zero C.↦ C.unseal zero ★

  matched-body-relation :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴺ I ⊑ I
      ⦂ (＇ zero ⇒ ＇ zero) ⊑ (＇ zero ⇒ ＇ zero)
      ∶ matched-body-index
  matched-body-relation =
    ƛ⊑ƛᵀ (Types.wfVar z<s) (Types.wfVar z<s)
      (x⊑xᵀ Types.Z)

  matched-body-relationᴿ :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴿ I ⊑ I
      ⦂ (＇ zero ⇒ ＇ zero) ⊑ (＇ zero ⇒ ＇ zero)
      ∶ matched-body-index
  matched-body-relationᴿ =
    ƛ⊑ƛᴿ (Types.wfVar z<s) (Types.wfVar z<s)
      (x⊑xᴿ Types.Z)

  matched-universal-relation :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴺ Λ I ⊑ Λ I
      ⦂ `∀ (＇ zero ⇒ ＇ zero)
        ⊑ `∀ (＇ zero ⇒ ＇ zero)
      ∶ ∀ⁱ matched-body-index
  matched-universal-relation =
    Λ⊑Λᵀ lift-store-[] lift-ctx-[]
      vI vI matched-body-relation

  matched-universal-relationᴿ :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴿ Λ I ⊑ Λ I
      ⦂ `∀ (＇ zero ⇒ ＇ zero)
        ⊑ `∀ (＇ zero ⇒ ＇ zero)
      ∶ ∀ⁱ matched-body-index
  matched-universal-relationᴿ =
    Λ⊑Λᴿ lift-store-[] lift-ctx-[]
      vI vI matched-body-relationᴿ

  body-cast-typing :
    C.instᵈ C.tag-or-idᵈ
      ∣ suc zero ∣ ((zero , ★) ∷ [])
      ⊢ body-cast ∶ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)
  body-cast-typing =
    C.cast-fun
      (C.cast-seal wf★ (here refl) refl)
      (C.cast-unseal wf★ (here refl) refl) ,
    NW.instSafe→widening
      (NW.safe-fun
        (NW.sealⁿ ★ zero)
        (NW.unsealʷ zero ★))

  outer-cast-typing :
    C.tag-or-idᵈ ∣ zero ∣ []
      ⊢ C.inst (★ ⇒ ★) body-cast
        ∶ `∀ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)
  outer-cast-typing =
    C.cast-inst (wf⇒ wf★ wf★) refl
      (proj₁ body-cast-typing) ,
    NW.inst
      (NW.safe-fun
        (NW.sealⁿ ★ zero)
        (NW.unsealʷ zero ★))

  allocated-I-typing :
    suc zero ∣ ((zero , ★) ∷ []) ∣ []
      ⊢ I ⦂ (＇ zero ⇒ ＇ zero)
  allocated-I-typing =
    ⊢ƛ (Types.wfVar z<s) (⊢` Z)

  source-result-typing :
    zero ∣ [] ∣ []
      ⊢ Λ I ⦂ `∀ (＇ zero ⇒ ＇ zero)
  source-result-typing =
    ⊢Λ vI (⊢ƛ (Types.wfVar z<s) (⊢` Z))

  target-result-typing :
    suc zero ∣ ((zero , ★) ∷ []) ∣ []
      ⊢ I ⟨ body-cast ⟩ ⦂ (★ ⇒ ★)
  target-result-typing =
    ⊢⟨⟩⊑ (cast-inst cast-tag-or-id)
      (seal★-inst seal★-tag-or-id)
      body-cast-typing allocated-I-typing


opened-body-structural-factorization-impossible :
  ((zero ˣ⊑★) ∷ [])
    ∣ suc zero
    ⊢ (＇ zero ⇒ ＇ zero) ⊑ (＇ zero ⇒ ＇ zero)
    ⊣ suc zero →
  ⊥
opened-body-structural-factorization-impossible
    (domain ↦ codomain)
    with domain
... | idˣ (here ()) source-bound target-bound
... | idˣ (there ()) source-bound target-bound


target-instantiation-creation-test :
  TargetInstantiationCreation
    {Φ = []} {Δᴸ = zero} {Δᴿ = zero}
    {ρ₀ = []} {ρ⁺ = []} {ρ∀ = []} {ρᴿ⁺ = []}
    {W = I} {W′ = I}
    {B = ★ ⇒ ★}
    {C = ＇ zero ⇒ ＇ zero}
    {D = ＇ zero ⇒ ＇ zero}
    {s = body-cast} {μ = C.tag-or-idᵈ}
    {r = matched-body-index} {f = final-index}
    {body-shape = tagˣˢ ↦ˢ tagˣˢ}
    (StoreImpPrefixᴿ
      {Φ = []} {Δᴸ = zero} {Δᴿ = zero} [] [])
    (((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴺ I ⊑ I
      ⦂ (＇ zero ⇒ ＇ zero) ⊑ (＇ zero ⇒ ＇ zero)
      ∶ matched-body-index)
target-instantiation-creation-test =
  target-instantiation-creation
    prefix-reflᴿ
    cast-tag-or-id
    seal★-tag-or-id
    outer-cast-typing
    lift-store-[]
    lift-right-store-[]
    vI
    noI
    vI
    noI
    (C.seal ★ zero C.↦ C.unseal zero ★)
    matched-body-relation
    (shape-inst (shape-fun shape-seal shape-unseal))
    (comp-∀-ν
      (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))
    source-result-typing
    target-result-typing


initial-target-instantiation-relation :
  [] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ Λ I
      ⊑ (Λ I) ⟨ C.inst (★ ⇒ ★) body-cast ⟩
    ⦂ `∀ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)
    ∶ final-index
initial-target-instantiation-relation =
  ⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
    outer-cast-typing matched-universal-relation final-index
    (shape-inst (shape-fun shape-seal shape-unseal))
    (comp-∀-ν
      (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))


initial-target-instantiation-relationᴿ :
  [] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴿ Λ I
      ⊑ (Λ I) ⟨ C.inst (★ ⇒ ★) body-cast ⟩
    ⦂ `∀ (＇ zero ⇒ ＇ zero) ⊑ (★ ⇒ ★)
    ∶ final-index
initial-target-instantiation-relationᴿ =
  ⊑cast⊑ᴿ cast-tag-or-id seal★-tag-or-id
    outer-cast-typing matched-universal-relationᴿ final-index
    (shape-inst (shape-fun shape-seal shape-unseal))
    (comp-∀-ν
      (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))


target-instantiation-creation-testᴿ :
  TargetInstantiationCreation
    {Φ = []} {Δᴸ = zero} {Δᴿ = zero}
    {ρ₀ = []} {ρ⁺ = []} {ρ∀ = []} {ρᴿ⁺ = []}
    {W = I} {W′ = I}
    {B = ★ ⇒ ★}
    {C = ＇ zero ⇒ ＇ zero}
    {D = ＇ zero ⇒ ＇ zero}
    {s = body-cast} {μ = C.tag-or-idᵈ}
    {r = matched-body-index} {f = final-index}
    {body-shape = tagˣˢ ↦ˢ tagˣˢ}
    (StoreImpPrefixᴿ
      {Φ = []} {Δᴸ = zero} {Δᴿ = zero} [] [])
    (((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴿ I ⊑ I
      ⦂ (＇ zero ⇒ ＇ zero) ⊑ (＇ zero ⇒ ＇ zero)
      ∶ matched-body-index)
target-instantiation-creation-testᴿ =
  target-instantiation-creation
    prefix-reflᴿ
    cast-tag-or-id
    seal★-tag-or-id
    outer-cast-typing
    lift-store-[]
    lift-right-store-[]
    vI
    noI
    vI
    noI
    (C.seal ★ zero C.↦ C.unseal zero ★)
    matched-body-relationᴿ
    (shape-inst (shape-fun shape-seal shape-unseal))
    (comp-∀-ν
      (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))
    source-result-typing
    target-result-typing


created-target-instantiation-relationᴿ :
  [] ∣ zero ∣ suc zero
    ∣ store-right zero ★ wf★ ∷ [] ∣ []
    ⊢ᴿ Λ I ⊑ I ⟨ body-cast ⟩
    ⦂ `∀ (＇ zero ⇒ ＇ zero) ⊑ ⇑ᵗ (★ ⇒ ★)
    ∶ ⊑-target-lift-rightᵢ final-index
created-target-instantiation-relationᴿ =
  target-instantiationᴿ
    (exact-creationᴱ target-instantiation-creation-testᴿ)


target-instantiation-administrative-trace :
  (Λ I) ⟨ C.inst (★ ⇒ ★) body-cast ⟩
    —↠[ keep ∷ bind ★ ∷ keep ∷ [] ]
      I ⟨ body-cast ⟩
target-instantiation-administrative-trace =
  ↠-step (pure-step (β-inst (Λ vI)))
    (↠-step
      (ν-step (Λ vI) (no•-Λ noI))
      (↠-step
        (ξ-⟨⟩ (pure-step (β-Λ• vI)))
        ↠-refl))

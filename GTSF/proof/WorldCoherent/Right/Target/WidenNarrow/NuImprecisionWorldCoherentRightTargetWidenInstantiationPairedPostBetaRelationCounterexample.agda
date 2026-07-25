module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaRelationCounterexample
  where

-- File Charter:
--   * Refutes an immediate QTI relation after target `β-inst` in the paired
--     incoming, source-only final target-instantiation case.
--   * Reuses the smallest matched/source-only index pair from the independent
--     right-opening regression and proves the runtime target `ν ★` cannot be
--     related before it reduces.
--   * Does not refute a catch-up-valued theorem whose target tail may reduce
--     the runtime allocation before establishing its final relation.
--   * Contains no result carrier, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_; refl)
open import Conversion using
  ( RevealConversion
  ; reveal-fun
  ; reveal-unseal
  ; conceal-seal
  )
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s)
open import Data.Product using (_×_; _,_)
open import Imprecision using
  ( nonvar-fun
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  )
open import ImprecisionWf using
  ( _↦_
  ; _∣_⊢_⊑_⊣_
  ; idˣ
  ; tagˣ
  ; ∀ⁱ_
  ; ν
  )
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( lift-ctx-[]
  ; lift-left-ctx-[]
  ; lift-left-store-[]
  ; lift-store-[]
  ; seal★-tag-or-id
  )
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
  ; ν
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; allocation-prefixᵀ
  ; prefix-reflⁱ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-tag-or-id
  )
open import Types using
  ( Ty
  ; wf★
  ; wf⇒
  ; ★
  ; ＇_
  ; _⇒_
  ; `∀
  )
open import proof.Core.Properties.TypePreservation using (seal★-inst)


private
  X : Ty
  X = ＇ zero

  F : Ty
  F = X ⇒ X

  H : Ty
  H = ★ ⇒ ★

  I : Term
  I = ƛ (` zero)

  vI : Value I
  vI = ƛ (` zero)

  noI : No• I
  noI = no•-ƛ no•-`

  pX :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ X ⊑ X ⊣ suc zero
  pX = idˣ (here refl) z<s z<s

  pF :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ F ⊑ F ⊣ suc zero
  pF = pX ↦ pX

  qX :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ X ⊑ ★ ⊣ zero
  qX = tagˣ (here refl) z<s

  qF :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ F ⊑ H ⊣ zero
  qF = qX ↦ qX

  body-cast : C.Coercion
  body-cast =
    C.seal ★ zero C.↦ C.unseal zero ★

  body-cast-typing :
    C.instᵈ C.tag-or-idᵈ
      ∣ suc zero ∣ ((zero , ★) ∷ [])
      ⊢ body-cast ∶ F ⊑ H
  body-cast-typing =
    C.cast-fun
      (C.cast-seal wf★ (here refl) refl)
      (C.cast-unseal wf★ (here refl) refl) ,
    NW.instSafe→widening
      (NW.safe-fun
        (NW.sealⁿ ★ zero)
        (NW.unsealʷ zero ★))

  paired-body-relation :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴺ I ⊑ I ⦂ F ⊑ F ∶ pF
  paired-body-relation =
    ƛ⊑ƛᵀ (Types.wfVar z<s) (Types.wfVar z<s)
      (x⊑xᵀ Types.Z)

  paired-universal-relation :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴺ Λ I ⊑ Λ I
      ⦂ `∀ F ⊑ `∀ F ∶ ∀ⁱ pF
  paired-universal-relation =
    Λ⊑Λᵀ lift-store-[] lift-ctx-[]
      vI vI paired-body-relation

  no-matched-variable :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ X ⊑ X ⊣ suc zero →
    ⊥
  no-matched-variable (idˣ (here ()) source-bound target-bound)
  no-matched-variable (idˣ (there ()) source-bound target-bound)

  no-independent-right-opening :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ F ⊑ F ⊣ suc zero →
    ⊥
  no-independent-right-opening (domain ↦ codomain) =
    no-matched-variable domain

  no-outer-independent-right-opening :
    [] ∣ zero ⊢ `∀ F ⊑ F ⊣ suc zero →
    ⊥
  no-outer-independent-right-opening
      (ν safe occurrence (domain ↦ codomain)) =
    no-matched-variable domain

  body-cast-source :
    ∀ {μ A} →
    C.instᵈ μ ∣ suc zero ∣ ((zero , ★) ∷ [])
      ⊢ body-cast ∶ A ⊑ H →
    A ≡ F
  body-cast-source
      (C.cast-fun
        (C.cast-seal source-wf source-member source-mode)
        (C.cast-unseal target-wf target-member target-mode) ,
        NW.cross (domain-safe NW.↦ codomain-safe)) =
    refl

  body-cast-reveal-source :
    ∀ {μ A} →
    RevealConversion μ (suc zero) ((zero , ★) ∷ [])
      zero ★ body-cast A H →
    A ≡ F
  body-cast-reveal-source
      (reveal-fun
        (conceal-seal source-wf source-member source-mode)
        (reveal-unseal target-wf target-member target-mode)) =
    refl

  no-body-post-beta-relation :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ∣ zero ∣ [] ∣ []
      ⊢ᴺ I ⊑ NuTerms.ν ★ (Λ I) body-cast
      ⦂ F ⊑ H ∶ qF →
    ⊥
  no-body-post-beta-relation
      (allocation-prefixᵀ prefix-reflⁱ inner
        source-typing target-typing) =
    no-body-post-beta-relation inner
  no-body-post-beta-relation
      (⊑νcastᵀ mode seal★ cast-typing liftρ liftγ
        opened inner shape comp)
      with body-cast-source cast-typing
  no-body-post-beta-relation
      (⊑νcastᵀ mode seal★ cast-typing liftρ liftγ
        opened inner shape comp)
      | refl =
    no-independent-right-opening opened


no-paired-post-beta-immediate-relation :
  [] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ Λ I ⊑ NuTerms.ν ★ (Λ I) body-cast
    ⦂ `∀ F ⊑ H ∶ ν nonvar-fun refl qF →
  ⊥
no-paired-post-beta-immediate-relation
    (allocation-prefixᵀ prefix-reflⁱ inner
      source-typing target-typing) =
  no-paired-post-beta-immediate-relation inner
no-paired-post-beta-immediate-relation
    (Λ⊑ᵀ occurrence lift-left-store-[]
      lift-left-ctx-[] source-value body) =
  no-body-post-beta-relation body
no-paired-post-beta-immediate-relation
    (⊑νᵀ hA h⇑A reveal liftρ liftγ opened inner replace)
    with body-cast-reveal-source reveal
no-paired-post-beta-immediate-relation
    (⊑νᵀ hA h⇑A reveal liftρ liftγ opened inner replace)
    | refl =
  no-outer-independent-right-opening opened
no-paired-post-beta-immediate-relation
    (⊑νcastᵀ mode seal★ cast-typing liftρ liftγ
      opened inner shape comp)
    with body-cast-source cast-typing
no-paired-post-beta-immediate-relation
    (⊑νcastᵀ mode seal★ cast-typing liftρ liftγ
      opened inner shape comp)
    | refl =
  no-outer-independent-right-opening opened


paired-post-beta-immediate-relation-counterexample :
  CastMode C.tag-or-idᵈ ×
  SealModeStore★ (C.instᵈ C.tag-or-idᵈ)
    ((zero , ★) ∷ []) ×
  (C.instᵈ C.tag-or-idᵈ
    ∣ suc zero ∣ ((zero , ★) ∷ [])
    ⊢ body-cast ∶ F ⊑ H) ×
  ([] ∣ zero ⊢ `∀ F ⊑ `∀ F ⊣ zero) ×
  ([] ∣ zero ⊢ `∀ F ⊑ H ⊣ zero) ×
  Value (Λ I) ×
  No• (Λ I) ×
  ([] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ Λ I ⊑ Λ I
    ⦂ `∀ F ⊑ `∀ F ∶ ∀ⁱ pF) ×
  (([] ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ Λ I ⊑ NuTerms.ν ★ (Λ I) body-cast
    ⦂ `∀ F ⊑ H ∶ ν nonvar-fun refl qF) →
    ⊥)
paired-post-beta-immediate-relation-counterexample =
  cast-tag-or-id ,
  seal★-inst seal★-tag-or-id ,
  body-cast-typing ,
  ∀ⁱ pF ,
  ν nonvar-fun refl qF ,
  Λ vI ,
  no•-Λ noI ,
  paired-universal-relation ,
  no-paired-post-beta-immediate-relation

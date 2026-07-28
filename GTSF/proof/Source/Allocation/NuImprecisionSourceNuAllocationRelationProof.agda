module
  proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationProof
  where

-- File Charter:
--   * Proves the source-only `inst` and reveal allocation bottom relations.
--   * Rebuilds the allocated bullet relation through the chosen left-store
--     lift without packaging the immediate operational reductions.
--   * Depends only on the relation contracts and canonical typing, store,
--     and QTI constructors.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using (⊑-src-wf)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTerms using (⇑ᵗᵐ; _•; _⟨_⟩)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionQuotientedTyping using
  ( nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (lift-left-ctx-[])
open import proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationDef
  using
  ( SourceInstAllocationRelationᵀ
  ; SourceRevealAllocationRelationᵀ
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( leftStoreⁱ-lift-left
  ; rightStoreⁱ-lift-left
  )
open import QuotientedTermImprecision using
  ( α⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; prefix-reflⁱ
  )
open import TermTyping using
  ( SealModeStore★
  ; _∣_∣_⊢_⦂_
  ; cast-inst
  ; ⊢•
  )
open import Types using (★; wf★; ⇑ᵗ)


source-inst-allocation-relation-proofᵀ :
  SourceInstAllocationRelationᵀ
source-inst-allocation-relation-proofᵀ
    {q = q} vN noN mode seal★ s⊑ pB
    s-shape-proof comp liftρ N⊑N′ =
  cast⊑⊑ᵀ (cast-inst mode) left-seal left-widening
    (α⊑ᵀ vN noN wf★ liftρ lift-left-ctx-[]
      N⊑N′ prefix-reflⁱ left-bullet-typing right-term-typing)
    (⊑-source-liftνᵢ pB) s-shape-proof comp
  where
  left-seal =
    subst
      (λ Σ → SealModeStore★ (instᵈ _) ((zero , ★) ∷ Σ))
      (sym (leftStoreⁱ-lift-left liftρ))
      seal★

  left-widening =
    subst
      (λ Σ → instᵈ _ ∣ suc _ ∣ (zero , ★) ∷ Σ
        ⊢ _ ∶ _ ⊑ ⇑ᵗ _)
      (sym (leftStoreⁱ-lift-left liftρ))
      s⊑

  left-bullet-typing =
    subst
      (λ Σ → suc _ ∣ (zero , ★) ∷ Σ ∣ []
        ⊢ (⇑ᵗᵐ _) • ⦂ _)
      (sym (leftStoreⁱ-lift-left liftρ))
      (⊢• refl refl (⊑-src-wf q) vN noN
        (nu-term-imprecision-source-typing N⊑N′))

  right-term-typing =
    subst
      (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (rightStoreⁱ-lift-left liftρ))
      (nu-term-imprecision-target-typing N⊑N′)


source-reveal-allocation-relation-proofᵀ :
  SourceRevealAllocationRelationᵀ
source-reveal-allocation-relation-proofᵀ
    {q = q} vN noN h⇑A s↑ pB replace liftρ N⊑N′ =
  conv↑⊑ᵀ left-reveal
    (α⊑ᵀ vN noN h⇑A liftρ lift-left-ctx-[]
      N⊑N′ prefix-reflⁱ left-bullet-typing right-term-typing)
    (⊑-source-liftνᵢ pB) replace
  where
  left-reveal =
    subst
      (λ Σ → RevealConversion _ (suc _)
        ((zero , ⇑ᵗ _) ∷ Σ) zero (⇑ᵗ _) _ _ (⇑ᵗ _))
      (sym (leftStoreⁱ-lift-left liftρ))
      s↑

  left-bullet-typing =
    subst
      (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
        ⊢ (⇑ᵗᵐ _) • ⦂ _)
      (sym (leftStoreⁱ-lift-left liftρ))
      (⊢• refl refl (⊑-src-wf q) vN noN
        (nu-term-imprecision-source-typing N⊑N′))

  right-term-typing =
    subst
      (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (rightStoreⁱ-lift-left liftρ))
      (nu-term-imprecision-target-typing N⊑N′)

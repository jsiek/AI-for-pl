module
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepProof
  where

-- File Charter:
--   * Proves synchronized matched-`ν` allocation as one indexed weak result
--     coupled with its fresh-store lineage.
--   * Keeps allocation-specific world lifting, prefix transport, type-shape,
--     and replacement calculations local.
--   * Contains no dispatcher, postulate, hole, permissive option, or legacy
--     allocation or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  ( _[_↦_⊑⟨_⟩_↤_]ᴾ_
  ; _[_↦_]ᴸ_
  ; _[_↦_]ᴿ_
  )
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; zero; s<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import ImprecisionComposition using (⌊_⌋)
open import ImprecisionWf
open import NuReduction using
  ( bind
  ; ν-step
  ; ↠-refl
  ; ↠-step
  ; _—→[_]_
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import TermTyping using (⊢•; _∣_∣_⊢_⦂_)
open import Types
open import proof.Catchup.Simulation.NuImprecisionSimulationCore
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Core.Properties.ConversionIndexCompatibilityProperties using
  ( replace-left-rename²ᵢ
  ; replace-left-target-shape
  ; replace-left-transport-endpoints
  ; replace-paired-rename²ᵢ
  ; replace-paired-target-shape
  ; replace-paired-transport-endpoints
  ; replace-right-rename²ᵢ
  ; replace-right-target-shape
  ; replace-right-transport-endpoints
  ; shape-transport-imprecision-endpoints
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-rename
  ; shape-source-liftνᵢ
  ; shape-target-lift-rightᵢ
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)
open import proof.Core.Properties.TypePreservation using
  (castModeRenamer-suc; term-weaken)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse-suc
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; predᵗ
  ; renameᵗ-ext-suc-comm
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( ∀ᵢᶜ
  ; rename-assm²-∀ᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import proof.NuCore.Misc.NuImprecisionWorldEmbeddingNoBullet using
  (rel-world-embed-no•ᵀ)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (lift-ctx-[])
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepDef
  using (MatchedNuAllocationStepᵀ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftStoreⁱ
  ; StoreImp
  ; correspondence-stored
  ; leftStoreⁱ
  ; leftStoreⁱ-lift
  ; rightStoreⁱ
  ; rightStoreⁱ-lift
  ; store-matched
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef using
  (rel-ctx-rename-[])
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (lift-store-embeddingⁱ)


private
  matched-lift-world-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
    LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
    RelWorldEmbeddingⁱ suc suc predᵗ predᵗ
      rename-assm²-∀ᵢ TyRenameWf-suc TyRenameWf-suc
      {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
  matched-lift-world-embeddingⁱ liftρ =
    rel-world-embedding RenameLeftInverse-suc RenameLeftInverse-suc
      castModeRenamer-suc castModeRenamer-suc
      (lift-store-embeddingⁱ liftρ) rel-ctx-rename-[]

  matched-lift-prefix-bodyᵀ :
    ∀ {Φ Δᴸ Δᴿ A B L L′ p}
      {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
      {ρ₁ ρ⁺ : StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)} →
    LiftStoreⁱ (∀ᵢᶜ Φ) ρ₀ ρ₁ →
    StoreImpPrefix ρ₁ ρ⁺ →
    No• L → No• L′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
      ⊢ᴺ L ⊑ L′ ⦂ A ⊑ B ∶ p →
    ∀ᵢᶜ Φ ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ⁺ ∣ []
      ⊢ᴺ ⇑ᵗᵐ L ⊑ ⇑ᵗᵐ L′ ⦂ ⇑ᵗ A ⊑ ⇑ᵗ B
        ∶ ⊑-lift∀ᵢ p
  matched-lift-prefix-bodyᵀ liftρ prefix noL noL′ L⊑L′ =
    allocation-prefixᵀ prefix body
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        noL↑ (nu-term-imprecision-source-typing body))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noL′↑ (nu-term-imprecision-target-typing body))
    where
    body = rel-world-embed-no•ᵀ
      (matched-lift-world-embeddingⁱ liftρ) L⊑L′ noL noL′
    noL↑ = renameᵗᵐ-preserves-No• suc noL
    noL′↑ = renameᵗᵐ-preserves-No• suc noL′

  ⊑-lift∀-shapeᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    ⌊ ⊑-lift∀ᵢ p ⌋ ≡ ⌊ p ⌋
  ⊑-lift∀-shapeᵢ p =
    shape-rename
      rename-assm²-∀ᵢ
      (λ X<Δ → s<s X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p

  ⊑-lift-under-∀-shapeᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
    ⌊ ⊑-lift-under-∀ᵢ p ⌋ ≡ ⌊ p ⌋
  ⊑-lift-under-∀-shapeᵢ p =
    shape-rename
      (rename-assm²-⇑ᵢ rename-assm²-∀ᵢ)
      (TyRenameWf-ext TyRenameWf-suc)
      (TyRenameWf-ext TyRenameWf-suc)
      p

  ⊑-lift-under-right-shapeᵢ :
    ∀ {Φ Δᴸ Δᴿ A B}
      (p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ) →
    ⌊ ⊑-lift-under-rightᵢ p ⌋ ≡ ⌊ p ⌋
  ⊑-lift-under-right-shapeᵢ p =
    shape-rename
      rename-assm²-paired-under-rightᵢ
      TyRenameWf-suc
      (TyRenameWf-ext TyRenameWf-suc)
      p

  replace-left-lift∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B α X}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
    p [ α ↦ X ]ᴸ q →
    ⊑-lift∀ᵢ p [ suc α ↦ ⇑ᵗ X ]ᴸ ⊑-lift∀ᵢ q
  replace-left-lift∀ᵢ =
    replace-left-rename²ᵢ
      rename-assm²-∀ᵢ TyRenameWf-suc TyRenameWf-suc

  replace-right-lift∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B′ β X′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
    p [ β ↦ X′ ]ᴿ q →
    ⊑-lift∀ᵢ p [ suc β ↦ ⇑ᵗ X′ ]ᴿ ⊑-lift∀ᵢ q
  replace-right-lift∀ᵢ =
    replace-right-rename²ᵢ
      rename-assm²-∀ᵢ TyRenameWf-suc TyRenameWf-suc

  replace-paired-lift∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ α β X X′}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
    ⊑-lift∀ᵢ p
      [ suc α ↦ ⇑ᵗ X
      ⊑⟨ ⊑-lift∀ᵢ pX ⟩
      ⇑ᵗ X′ ↤ suc β ]ᴾ
    ⊑-lift∀ᵢ q
  replace-paired-lift∀ᵢ =
    replace-paired-rename²ᵢ
      rename-assm²-∀ᵢ TyRenameWf-suc TyRenameWf-suc

  replace-paired-lift-under-∀ᵢ :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′}
      {A⇑⊑A′⇑ : ∀ᵢᶜ Φ
        ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
    q
      [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
    ⊑-lift-under-∀ᵢ q
      [ zero ↦ renameᵗ (extᵗ suc) (⇑ᵗ A)
      ⊑⟨ ⊑-lift-under-∀ᵢ A⇑⊑A′⇑ ⟩
      renameᵗ (extᵗ suc) (⇑ᵗ A′) ↤ zero ]ᴾ
    ⊑-lift∀ᵢ (⊑-lift∀ᵢ pB)
  replace-paired-lift-under-∀ᵢ
      {B = B} {B′ = B′} {pB = pB} {q = q} replace =
    replace-paired-target-shape target-shape
      endpoints-replacement
    where
    raw-output = ⊑-lift-under-∀ᵢ (⊑-lift∀ᵢ pB)

    renamed-replacement =
      replace-paired-rename²ᵢ
        (rename-assm²-⇑ᵢ rename-assm²-∀ᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        (TyRenameWf-ext TyRenameWf-suc)
        replace

    source-eq = renameᵗ-ext-suc-comm suc B
    target-eq = renameᵗ-ext-suc-comm suc B′

    endpoints-replacement =
      replace-paired-transport-endpoints
        refl refl source-eq target-eq refl refl
        renamed-replacement

    target-shape =
      trans
        (⊑-lift∀-shapeᵢ (⊑-lift∀ᵢ pB))
        (sym
          (trans
            (shape-transport-imprecision-endpoints
              source-eq target-eq raw-output)
            (⊑-lift-under-∀-shapeᵢ (⊑-lift∀ᵢ pB))))

  replace-left-lift-source-nu-bodyᵢ :
    ∀ {Φ Δᴸ Δᴿ A B B′ C}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
      (safe : NonVar C)
      (occ : occurs zero C ≡ true) →
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
    sourceNuBody (⊑-lift-source-nuᵢ safe occ q)
      [ zero ↦ renameᵗ (extᵗ suc) (⇑ᵗ A) ]ᴸ
    ⊑-source-liftνᵢ (⊑-lift∀ᵢ pB)
  replace-left-lift-source-nu-bodyᵢ
      {B = B} {pB = pB} {q = q} safe occ replace =
    replace-left-target-shape target-shape
      endpoints-replacement
    where
    raw-output =
      ⊑-renameᵗ²ᵢ
        (rename-assm²-⇑ᴸᵢ rename-assm²-∀ᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        TyRenameWf-suc
        (⊑-source-liftνᵢ pB)

    renamed-replacement =
      replace-left-rename²ᵢ
        (rename-assm²-⇑ᴸᵢ rename-assm²-∀ᵢ)
        (TyRenameWf-ext TyRenameWf-suc)
        TyRenameWf-suc
        replace

    source-eq = renameᵗ-ext-suc-comm suc B

    endpoints-replacement =
      replace-left-transport-endpoints
        refl refl source-eq refl renamed-replacement

    target-shape =
      trans
        (shape-source-liftνᵢ (⊑-lift∀ᵢ pB))
        (trans
          (⊑-lift∀-shapeᵢ pB)
          (sym
            (trans
              (shape-transport-imprecision-endpoints
                source-eq refl raw-output)
              (trans
                (shape-rename
                  (rename-assm²-⇑ᴸᵢ rename-assm²-∀ᵢ)
                  (TyRenameWf-ext TyRenameWf-suc)
                  TyRenameWf-suc
                  (⊑-source-liftνᵢ pB))
                (shape-source-liftνᵢ pB)))))

  replace-right-lift-under-rightᵢ :
    ∀ {Φ Δᴸ Δᴿ A B B′ C′}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
    pC [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
    ⊑-lift-under-rightᵢ pC
      [ zero ↦ renameᵗ (extᵗ suc) (⇑ᵗ A) ]ᴿ
    ⊑-target-lift-rightᵢ (⊑-lift∀ᵢ pB)
  replace-right-lift-under-rightᵢ
      {B′ = B′} {pB = pB} {pC = pC} replace =
    replace-right-target-shape target-shape
      endpoints-replacement
    where
    raw-output =
      ⊑-renameᵗ²ᵢ
        rename-assm²-paired-under-rightᵢ
        TyRenameWf-suc
        (TyRenameWf-ext TyRenameWf-suc)
        (⊑-target-lift-rightᵢ pB)

    renamed-replacement =
      replace-right-rename²ᵢ
        rename-assm²-paired-under-rightᵢ
        TyRenameWf-suc
        (TyRenameWf-ext TyRenameWf-suc)
        replace

    target-eq = renameᵗ-ext-suc-comm suc B′

    endpoints-replacement =
      replace-right-transport-endpoints
        refl refl target-eq refl renamed-replacement

    target-shape =
      trans
        (shape-target-lift-rightᵢ (⊑-lift∀ᵢ pB))
        (trans
          (⊑-lift∀-shapeᵢ pB)
          (sym
            (trans
              (shape-transport-imprecision-endpoints
                refl target-eq raw-output)
              (trans
                (shape-rename
                  rename-assm²-paired-under-rightᵢ
                  TyRenameWf-suc
                  (TyRenameWf-ext TyRenameWf-suc)
                  (⊑-target-lift-rightᵢ pB))
                (shape-target-lift-rightᵢ pB)))))

  matched-nu-allocation :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)} →
    Value N →
    No• N →
    Value N′ →
    No• N′ →
    RevealConversion μ (suc Δᴸ)
      ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
      zero (⇑ᵗ A) s C (⇑ᵗ B) →
    RevealConversion μ′ (suc Δᴿ)
      ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
      zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
    (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
    q
      [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
    (ν A N s —→[ bind A ] ((⇑ᵗᵐ N) •) ⟨ s ⟩) ×
    (ν A′ N′ s′
      —→[ bind A′ ] ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩) ×
    (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
      store-matched zero (⇑ᵗ A) zero (⇑ᵗ A′) A⇑⊑A′⇑ ∷ ρ′
      ∣ []
      ⊢ᴺ ((⇑ᵗᵐ N) •) ⟨ s ⟩
        ⊑ ((⇑ᵗᵐ N′) •) ⟨ s′ ⟩
      ⦂ ⇑ᵗ B ⊑ ⇑ᵗ B′ ∶ ⊑-lift∀ᵢ pB)
  matched-nu-allocation {q = q} vN noN vN′ noN′ s↑ s′↑ pB
      A⇑⊑A′⇑ replace liftρ N⊑N′ =
    ν-step vN noN ,
    ν-step vN′ noN′ ,
    paired-revealᵀ
      (correspondence-stored (here refl))
      left-reveal
      right-reveal
      replace
      (α⊑αᵀ vN noN vN′ noN′ A⇑⊑A′⇑ liftρ lift-ctx-[]
        N⊑N′ left-bullet-typing right-bullet-typing)
    where
    left-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (leftStoreⁱ-lift liftρ))
        s↑

    right-reveal =
      subst
        (λ Σ → RevealConversion _ (suc _) ((zero , ⇑ᵗ _) ∷ Σ)
          zero (⇑ᵗ _) _ _ (⇑ᵗ _))
        (sym (rightStoreⁱ-lift liftρ))
        s′↑

    left-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (leftStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-src-wf q) vN noN
          (nu-term-imprecision-source-typing N⊑N′))

    right-bullet-typing =
      subst
        (λ Σ → suc _ ∣ (zero , ⇑ᵗ _) ∷ Σ ∣ []
          ⊢ (⇑ᵗᵐ _) • ⦂ _)
        (sym (rightStoreⁱ-lift liftρ))
        (⊢• refl refl (⊑-tgt-wf q) vN′ noN′
          (nu-term-imprecision-target-typing N⊑N′))

  matched-nu-step :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)} →
    Value N →
    No• N →
    Value N′ →
    No• N′ →
    RevealConversion μ (suc Δᴸ)
      ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
      zero (⇑ᵗ A) s C (⇑ᵗ B) →
    RevealConversion μ′ (suc Δᴿ)
      ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
      zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
    (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
    q
      [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q →
    WeakOneStepResult ρ
      (ν A N s) (((⇑ᵗᵐ N′) •) ⟨ s′ ⟩)
      B B′ (bind A′)
  matched-nu-step
      {A = A} {A′ = A′} {B = B} {B′ = B′} {ρ′ = ρ′}
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
      with matched-nu-allocation vN noN vN′ noN′ s↑ s′↑
        pB A⇑⊑A′⇑ replace liftρ N⊑N′
  matched-nu-step
      {A = A} {A′ = A′} {B = B} {B′ = B′} {ρ′ = ρ′}
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
      | source→ , _ , result =
    record
      { sourceChanges = bind A ∷ []
      ; targetTailChanges = []
      ; sourceResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
      ; targetResult = ((⇑ᵗᵐ _) •) ⟨ _ ⟩
      ; resultCtx = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ _
      ; resultLeftCtx = _
      ; resultRightCtx = _
      ; sourceCtxResult = refl
      ; targetCtxResult = refl
      ; resultStore =
          store-matched zero (⇑ᵗ A) zero (⇑ᵗ A′)
            A⇑⊑A′⇑ ∷ ρ′
      ; resultSourceType = ⇑ᵗ B
      ; resultTargetType = ⇑ᵗ B′
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = ⊑-lift∀ᵢ
      ; transportAllBody = ⊑-lift-under-∀ᵢ
      ; transportRightBody = ⊑-lift-under-rightᵢ
      ; transportSourceNu = ⊑-lift-source-nuᵢ
      ; resultType = ⊑-lift∀ᵢ pB
      ; sourceCatchup = ↠-step source→ ↠-refl
      ; targetTail = ↠-refl
      ; sourceStoreResult =
          cong ((zero , ⇑ᵗ A) ∷_) (leftStoreⁱ-lift liftρ)
      ; targetStoreResult =
          cong ((zero , ⇑ᵗ A′) ∷_) (rightStoreⁱ-lift liftρ)
      ; relatedResults = result
      }

  matched-nu-step-transport :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      (vN : Value N) (noN : No• N)
      (vN′ : Value N′) (noN′ : No• N′)
      (s↑ : RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B))
      (s′↑ : RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′))
      (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ)
      (replace : q
        [ zero ↦ ⇑ᵗ A
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ pB)
      (liftρ : LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′)
      (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
    WeakOneStepTransport
      (matched-nu-step vN noN vN′ noN′ s↑ s′↑ pB
        A⇑⊑A′⇑ replace liftρ N⊑N′)
  matched-nu-step-transport
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
      with matched-nu-allocation vN noN vN′ noN′ s↑ s′↑
        pB A⇑⊑A′⇑ replace liftρ N⊑N′
  matched-nu-step-transport
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
      | source→ , target→ , result =
    weak-step-transport
      (matched-lift-prefix-bodyᵀ liftρ (prefix-∷ⁱ prefix-reflⁱ))

  matched-nu-step-type-coherence :
    ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ N N′ s s′ μ μ′ q}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
      (vN : Value N) (noN : No• N)
      (vN′ : Value N′) (noN′ : No• N′)
      (s↑ : RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
        zero (⇑ᵗ A) s C (⇑ᵗ B))
      (s′↑ : RevealConversion μ′ (suc Δᴿ)
        ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
        zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′))
      (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ)
      (replace : q
        [ zero ↦ ⇑ᵗ A
        ⊑⟨ A⇑⊑A′⇑ ⟩
        ⇑ᵗ A′ ↤ zero ]ᴾ
        ⊑-lift∀ᵢ pB)
      (liftρ : LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′)
      (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q) →
    WeakOneStepTypeCoherence
      (matched-nu-step vN noN vN′ noN′ s↑ s′↑ pB
        A⇑⊑A′⇑ replace liftρ N⊑N′)
  matched-nu-step-type-coherence
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
      with matched-nu-allocation vN noN vN′ noN′ s↑ s′↑
        pB A⇑⊑A′⇑ replace liftρ N⊑N′
  matched-nu-step-type-coherence
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
      | source→ , target→ , result =
    weak-step-type-coherence
      (λ pC pD → refl)
      (λ q′ → refl)
      ⊑-lift∀-shapeᵢ
      ⊑-lift-under-right-shapeᵢ
      replace-left-lift∀ᵢ
      replace-right-lift∀ᵢ
      replace-paired-lift∀ᵢ
      replace-paired-lift-under-∀ᵢ
      replace-left-lift-source-nu-bodyᵢ
      replace-right-lift-under-rightᵢ


matched-nu-allocation-step-proofᵀ : MatchedNuAllocationStepᵀ
matched-nu-allocation-step-proofᵀ
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′ =
  indexed ,
  (weak-step-store-lineage _
     (lift-store-embeddingⁱ liftρ)
     (prefix-∷ⁱ prefix-reflⁱ)) ,
  refl ,
  refl ,
  refl
  where
  result = matched-nu-step
    vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑ replace liftρ N⊑N′
  indexed = weak-indexed-result
    result
    (relatedResults result)
    (matched-nu-step-transport
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑
      replace liftρ N⊑N′)
    (matched-nu-step-type-coherence
      vN noN vN′ noN′ s↑ s′↑ pB A⇑⊑A′⇑
      replace liftρ N⊑N′)

module proof.NuImprecisionParallelTermSubstitutionProof where

-- File Charter:
--   * Proves prefix-aware framed parallel term substitution by mutual
--     structural recursion over ordinary and quotiented term imprecision.
--   * Extends substitution frames under binders and transports every
--     store-indexed constructor premise through the ambient prefix.
--   * Contains no postulate, hole, catch-all, termination pragma, or
--     permissive option.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)

open import Coercions using (id-onlyᵈ)
open import Conversion using
  (weaken-conceal-conversion; weaken-reveal-conversion)
open import NarrowWiden using (narrow-weaken; widen-weaken)
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Substˣ
  ; Term
  ; no•-`
  ; no•-$
  ; no•-ƛ
  ; no•-Λ
  ; no•-·
  ; no•-ν
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-blame
  ; substˣᵐ
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; cast⊒⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; gen⊑groundᵀ
  ; ordinary-down-applicationᵖᵀ
  ; quotient-down-applicationᵖᵀ
  ; quotient-id-down-applicationᵖᵀ
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; ·⊑·ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑αᵀ
  ; ⊑νcastᵀ
  ; ⊑νᵀ
  ; ⊕⊑⊕ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Store using (StoreIncl-cons)
open import TermTyping using (SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.NuImprecisionParallelTermSubstitutionBlameProof using
  (quotiented-parallel-term-substitution-blame-proofᵀ)
open import proof.NuImprecisionParallelTermSubstitutionDef using
  (QuotientedParallelTermSubstitutionFramedᵀ)
open import
  proof.NuImprecisionParallelTermSubstitutionEnvironmentProof using
  ( pointwise-substitution-no•ᵀ
  ; quotiented-substitution-target-wfᵀ
  )
open import proof.NuImprecisionRightBinderContextLiftProof using
  (lift-right-ctx-result)
open import proof.NuImprecisionSourceNuPairedBinderSupport using
  (lift-ctx-result; lift-left-ctx-result)
open import proof.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.NuImprecisionStorePrefixEvidenceProof using
  ( paired-cast-prefix-proofᵀ
  ; quotient-widening-pair-prefix-proofᵀ
  )
open import proof.NuImprecisionStorePrefixLiftProof using
  ( left-store-prefix-lift-proofᵀ
  ; paired-store-prefix-lift-proofᵀ
  ; right-store-prefix-lift-proofᵀ
  )
open import proof.NuImprecisionSubstitutionFrame using
  ( QuotientedSubstitutionEnvironmentFamily
  ; QuotientedSubstitutionFrame
  ; substitution-frame-ƛ
  ; substitution-frame-Λ
  ; substitution-frame-Λ-left
  )
open import proof.NuTermProperties using
  (substˣᵐ-preserves-Value)
open import proof.StoreProperties using (renameStoreᵗ-incl)
open import proof.TypePreservation using
  (seal★-weaken; term-weaken; typing-substˣ)


mutual
  quotiented-parallel-term-substitution-framed-proofᵀ :
    QuotientedParallelTermSubstitutionFramedᵀ

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix no•-blame noM′
      (blame⊑ᵀ M′⊢)
      with environment frame
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix no•-blame noM′
      (blame⊑ᵀ M′⊢)
      | related , noτ , noτ′ =
    quotiented-parallel-term-substitution-blame-proofᵀ
      prefix related noτ′ noM′ M′⊢

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix no•-` no•-` (x⊑xᵀ x∈)
      with environment frame
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix no•-` no•-` (x⊑xᵀ x∈)
      | related , noτ , noτ′ =
    related x∈

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ƛ noN) (no•-ƛ noN′)
      (ƛ⊑ƛᵀ hA hA′ body) =
    ƛ⊑ƛᵀ hA hA′
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment (substitution-frame-ƛ frame)
        prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-· noL noM) (no•-· noL′ noM′)
      (·⊑·ᵀ fun arg) =
    ·⊑·ᵀ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noL noL′ fun)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ arg)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noN) (no•-⟨⟩ noN′)
      (up⊑upᵀ body widening p) =
    up⊑upᵀ
      (quotiented-parallel-term-substitution-quotient-proofᵀ
        environment frame prefix noN noN′ body)
      (quotient-widening-pair-prefix-proofᵀ prefix widening) p

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᵀ liftρ liftγ vV vV′ body)
      with paired-store-prefix-lift-proofᵀ prefix liftρ
         | lift-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-Λ noV) (no•-Λ noV′)
      (Λ⊑Λᵀ liftρ liftγ vV vV′ body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    Λ⊑Λᵀ liftρ⁺ liftδ
      (substˣᵐ-preserves-Value _ vV)
      (substˣᵐ-preserves-Value _ vV′)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment
        (substitution-frame-Λ frame liftρ⁺ liftγ liftδ)
        prefix↑ noV noV′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-Λ noV) noN′
      (Λ⊑ᵀ occ liftρ liftγ vV body)
      with left-store-prefix-lift-proofᵀ prefix liftρ
         | lift-left-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-Λ noV) noN′
      (Λ⊑ᵀ occ liftρ liftγ vV body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    Λ⊑ᵀ occ liftρ⁺ liftδ
      (substˣᵐ-preserves-Value _ vV)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment
        (substitution-frame-Λ-left frame liftρ⁺ liftγ liftδ)
        prefix↑ noV noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix () noN′
      (α⊑αᵀ vL noL vL′ noL′ p liftρ liftγ body L⊢ L′⊢)
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix () noN′
      (α⊑ᵀ vL noL hA liftρ liftγ body L⊢ N′⊢)
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noN ()
      (⊑αᵀ vL′ noL′ hA liftρ liftγ body p N⊢ L′⊢)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noN noN′
      (allocation-prefixᵀ inner-prefix body N⊢ N′⊢) =
    quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame
      (store-imp-prefix-transⁱ inner-prefix prefix)
      noN noN′ body

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) (no•-ν noN′)
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ body)
      with paired-store-prefix-lift-proofᵀ prefix liftρ
         | lift-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) (no•-ν noN′)
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    ν⊑νᵀ hA hA′
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix)))
        s↑)
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix)))
        s′↑)
      A⊑A′ A↑⊑A′↑ liftρ⁺ liftδ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) noN′
      (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ body)
      with left-store-prefix-lift-proofᵀ prefix liftρ
         | lift-left-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) noN′
      (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    ν⊑ᵀ hA hA↑
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix)))
        s↑)
      liftρ⁺ liftδ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noN (no•-ν noN′)
      (⊑νᵀ hA hA↑ s↑ liftρ liftγ p body)
      with right-store-prefix-lift-proofᵀ prefix liftρ
         | lift-right-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noN (no•-ν noN′)
      (⊑νᵀ hA hA↑ s↑ liftρ liftγ p body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    ⊑νᵀ hA hA↑
      (weaken-reveal-conversion
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix)))
        s↑)
      liftρ⁺ liftδ p
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) (no•-ν noN′)
      (νcast⊑νcastᵀ
        mode seal★ mode′ seal★′ s⊑ s′⊑ compatible
        liftρ liftγ body)
      with paired-store-prefix-lift-proofᵀ prefix liftρ
         | lift-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) (no•-ν noN′)
      (νcast⊑νcastᵀ
        mode seal★ mode′ seal★′ s⊑ s′⊑ compatible
        liftρ liftγ body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    νcast⊑νcastᵀ mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix)))
        seal★)
      mode′
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix)))
        seal★′)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix)))
        s⊑)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix)))
        s′⊑)
      compatible liftρ⁺ liftδ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) noN′
      (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ body)
      with left-store-prefix-lift-proofᵀ prefix liftρ
         | lift-left-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) noN′
      (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    νcast⊑ᵀ mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix)))
        seal★)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix)))
        s⊑)
      liftρ⁺ liftδ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noN (no•-ν noN′)
      (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ p body)
      with right-store-prefix-lift-proofᵀ prefix liftρ
         | lift-right-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noN (no•-ν noN′)
      (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ p body)
      | ρ⁺↑ , liftρ⁺ , prefix↑
      | δ↑ , liftδ =
    ⊑νcastᵀ mode
      (seal★-weaken
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix)))
        seal★)
      (widen-weaken ≤-refl
        (StoreIncl-cons
          (renameStoreᵗ-incl suc (rightStoreⁱ-prefix-inclusion prefix)))
        s⊑)
      liftρ⁺ liftδ p
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noN noN′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix no•-$ no•-$ κ⊑κᵀ =
    κ⊑κᵀ

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⊕ noL noM) (no•-⊕ noL′ noM′)
      (⊕⊑⊕ᵀ left right) =
    ⊕⊑⊕ᵀ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noL noL′ left)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ right)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noV) noW
      (gen⊑groundᵀ mode seal★ c⊒ ground vV vW W⊢ body q)
      with environment frame
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noV) noW
      (gen⊑groundᵀ mode seal★ c⊒ ground vV vW W⊢ body q)
      | related , noτ , noτ′ =
    gen⊑groundᵀ mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊒)
      ground
      (substˣᵐ-preserves-Value _ vV)
      (substˣᵐ-preserves-Value _ vW)
      (typing-substˣ
        (quotiented-substitution-target-wfᵀ related)
        (pointwise-substitution-no•ᵀ noτ′) noW
        (term-weaken ≤-refl
          (rightStoreⁱ-prefix-inclusion prefix) noW W⊢))
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noV (no•-⟨⟩ noW) body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (cast⊒⊑ᵀ mode seal★ c⊒ body q) =
    cast⊒⊑ᵀ mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊒)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (cast⊑⊑ᵀ mode seal★ c⊑ body q) =
    cast⊑⊑ᵀ mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊒ᵀ mode seal★ c⊒ body q) =
    ⊑cast⊒ᵀ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊒)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊑ᵀ mode seal★ c⊑ body q) =
    ⊑cast⊑ᵀ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊑idᵀ seal★ c⊑ body q) =
    ⊑cast⊑idᵀ
      (seal★-weaken {μ = id-onlyᵈ}
        (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (conv⊑convᵀ cast body) =
    conv⊑convᵀ
      (paired-cast-prefix-proofᵀ prefix cast)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (conv↑⊑ᵀ conversion body q) =
    conv↑⊑ᵀ
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (conv↓⊑ᵀ conversion body q) =
    conv↓⊑ᵀ
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑conv↑ᵀ conversion body q) =
    ⊑conv↑ᵀ
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑conv↓ᵀ conversion body q) =
    ⊑conv↓ᵀ
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q


  quotiented-parallel-term-substitution-quotient-proofᵀ :
    ∀ {Φ₀ Δ₀ᴸ Δ₀ᴿ ρ⁺₀ γ₀ δ₀ τ₀ τ₀′} →
    (environment : QuotientedSubstitutionEnvironmentFamily
      {Φ₀} {Δ₀ᴸ} {Δ₀ᴿ} ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
    ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ γ δ τ τ′ N N′ D D′ q} →
    QuotientedSubstitutionFrame ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
      {Φ} {Δᴸ} {Δᴿ} ρ⁺ γ δ τ τ′ →
    StoreImpPrefix ρ₀ ρ⁺ →
    No• N → No• N′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
      ⊢ᴺᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
      ⊢ᴺᵖ substˣᵐ τ N ⊑ substˣᵐ τ′ N′
      ⦂ D ⊑ᵖ D′ ∶ q

  quotiented-parallel-term-substitution-quotient-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (down⊑downᵀ source target body q) =
    down⊑downᵀ
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-quotient-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (gen-down⊑gen-downᵀ source target body q) =
    gen-down⊑gen-downᵀ
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q

  quotiented-parallel-term-substitution-quotient-proofᵀ
      environment frame prefix
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′))
      (ordinary-down-applicationᵖᵀ
        mode seal★ source mode′ seal★′ target function argument) =
    ordinary-down-applicationᵖᵀ
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noL noL′ function)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ argument)
  quotiented-parallel-term-substitution-quotient-proofᵀ
      environment frame prefix
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′))
      (quotient-id-down-applicationᵖᵀ
        source target function argument) =
    quotient-id-down-applicationᵖᵀ
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      (quotiented-parallel-term-substitution-quotient-proofᵀ
        environment frame prefix noL noL′ function)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ argument)
  quotiented-parallel-term-substitution-quotient-proofᵀ
      environment frame prefix
      (no•-· noL (no•-⟨⟩ noM))
      (no•-· noL′ (no•-⟨⟩ noM′))
      (quotient-down-applicationᵖᵀ
        mode seal★ source mode′ seal★′ target function argument) =
    quotient-down-applicationᵖᵀ
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      (quotiented-parallel-term-substitution-quotient-proofᵀ
        environment frame prefix noL noL′ function)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ argument)

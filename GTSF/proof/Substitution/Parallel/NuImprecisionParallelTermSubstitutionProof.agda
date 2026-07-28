module proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionProof where

-- File Charter:
--   * Proves prefix-aware framed parallel term substitution by mutual
--     structural recursion over ordinary and quotiented term imprecision.
--   * Extends substitution frames under binders and transports every
--     store-indexed constructor premise through the ambient prefix.
--   * Contains no postulate, hole, catch-all, termination pragma, or
--     permissive option.

open import proof.Store.Prefix.NuImprecisionTermStorePrefixLemma using
  (term-imprecision-store-prefixᵀ)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Coercions using (id-onlyᵈ)
open import Conversion using
  (weaken-conceal-conversion; weaken-reveal-conversion)
open import NarrowWiden using (narrow-weaken; widen-weaken)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Substˣ
  ; Term
  ; Value
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
  ; blame⊑ᵀ
  ; cast⊑⊑ᵀ
  ; cast⊒⊑ᵀ
  ; closeᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; gen⊑groundᵀ
  ; paired-concealᵀ
  ; paired-downᵀ
  ; paired-revealᵀ
  ; paired-wideningᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; ·⊑·ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; κ⊑κᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊕⊑⊕ᵀ
  ; target-instantiationᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import proof.Core.Properties.NuTermProperties using
  (substˣᵐ-preserves-Value)
open import Store using (StoreIncl-cons)
open import TermTyping using (SealModeStore★; forget; _∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionBlameProof using
  (quotiented-parallel-term-substitution-blame-proofᵀ)
open import proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionDef using
  (QuotientedParallelTermSubstitutionFramedᵀ)
open import
  proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionEnvironmentProof using
  ( pointwise-substitution-no•ᵀ
  ; quotiented-substitution-target-wfᵀ
  )
open import proof.Right.Core.NuImprecisionRightBinderContextLiftProof using
  (lift-right-ctx-result)
open import proof.Source.NuPaired.NuImprecisionSourceNuPairedBinderSupport using
  (lift-ctx-result; lift-left-ctx-result)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  ; store-imp-prefix-transⁱ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefixEvidenceProof using
  ( quotient-widening-pair-prefix-proofᵀ
  ; spine-cast-mode-prefix-proofᵀ
  ; store-corresponds-prefix-proofᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefixLiftProof using
  ( left-store-prefix-lift-proofᵀ
  ; paired-store-prefix-lift-proofᵀ
  ; right-store-prefix-lift-proofᵀ
  )
open import proof.Substitution.Term.NuImprecisionSubstitutionFrame using
  ( QuotientedSubstitutionEnvironmentFamily
  ; QuotientedSubstitutionFrame
  ; substitution-frame-ƛ
  ; substitution-frame-Λ
  ; substitution-frame-Λ-left
  )
open import proof.Core.Properties.NuTermProperties using
  ( closed-refined-typing-recontextualize
  ; subst-closedᵐ
  ; substˣᵐ-preserves-Value
  ; typing-closedᵐ
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using
  (seal★-weaken; term-weaken; typing-substˣ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-no-bulletᴱ
  ; embedded-creation-source-typingᴱ
  ; embedded-creation-target-no-bulletᴱ
  ; embedded-creation-target-typingᴱ
  )


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
      (closeᵀ body widening p u-shape u′-shape square compatible) =
    closeᵀ
      (quotiented-parallel-term-substitution-quotient-proofᵀ
        environment frame prefix noN noN′ body)
      (quotient-widening-pair-prefix-proofᵀ prefix widening)
      p u-shape u′-shape square compatible

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
      environment {τ = τ} {τ′ = τ′}
      frame prefix noM noM′
      (target-instantiationᵀ embedded)
      rewrite subst-closedᵐ
                (typing-closedᵐ
                  (forget
                    (embedded-creation-source-typingᴱ embedded)))
                τ
            | subst-closedᵐ
                (typing-closedᵐ
                  (forget
                    (embedded-creation-target-typingᴱ embedded)))
                τ′ =
    term-imprecision-store-prefixᵀ prefix
      (target-instantiationᵀ embedded)
      (term-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix)
        (embedded-creation-source-no-bulletᴱ embedded)
        (closed-refined-typing-recontextualize
          (typing-closedᵐ
            (forget
              (embedded-creation-source-typingᴱ embedded)))
          (embedded-creation-source-typingᴱ embedded)))
      (term-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix)
        (embedded-creation-target-no-bulletᴱ embedded)
        (closed-refined-typing-recontextualize
          (typing-closedᵐ
            (forget
              (embedded-creation-target-typingᴱ embedded)))
          (embedded-creation-target-typingᴱ embedded)))

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix () noN′
      (α⊑αᵀ vL noL vL′ noL′ p liftρ liftγ body
        allocation-prefix L⊢ L′⊢)
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix () noN′
      (α⊑ᵀ vL noL hA liftρ liftγ body
        allocation-prefix L⊢ N′⊢)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) (no•-ν noN′)
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ body replace)
      with paired-store-prefix-lift-proofᵀ prefix liftρ
         | lift-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) (no•-ν noN′)
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ body replace)
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
      replace

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) noN′
      (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ body replace)
      with left-store-prefix-lift-proofᵀ prefix liftρ
         | lift-left-ctx-result _
  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-ν noN) noN′
      (ν⊑ᵀ hA hA↑ s↑ liftρ liftγ body replace)
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
      replace

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
      (cast⊒⊑ᵀ mode seal★ c⊒ body q c-shape comp) =
    cast⊒⊑ᵀ mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊒)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q c-shape comp

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (cast⊑⊑ᵀ mode seal★ c⊑ body q c-shape comp) =
    cast⊑⊑ᵀ mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q c-shape comp

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊒ᵀ mode seal★ c⊒ body q c-shape comp) =
    ⊑cast⊒ᵀ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊒)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q c-shape comp

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑cast⊑ᵀ mode seal★ c⊑ body q c-shape comp) =
    ⊑cast⊑ᵀ mode
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) c⊑)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q c-shape comp

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-revealᵀ corresponds source target replace body) =
    paired-revealᵀ
      (store-corresponds-prefix-proofᵀ prefix corresponds)
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) target)
      replace
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-concealᵀ corresponds source target replace body) =
    paired-concealᵀ
      (store-corresponds-prefix-proofᵀ prefix corresponds)
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) target)
      replace
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) (no•-⟨⟩ noM′)
      (paired-wideningᵀ
        mode seal★ source source-shape
        mode′ seal★′ target target-shape
        left-square right-square compatible body) =
    paired-wideningᵀ
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      source-shape
      mode′
      (seal★-weaken (rightStoreⁱ-prefix-inclusion prefix) seal★′)
      (widen-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      target-shape left-square right-square compatible
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (conv↑⊑ᵀ conversion body q replace) =
    conv↑⊑ᵀ
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q replace

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix (no•-⟨⟩ noM) noM′
      (conv↓⊑ᵀ conversion body q replace) =
    conv↓⊑ᵀ
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q replace

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑conv↑ᵀ conversion body q replace) =
    ⊑conv↑ᵀ
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q replace

  quotiented-parallel-term-substitution-framed-proofᵀ
      environment frame prefix noM (no•-⟨⟩ noM′)
      (⊑conv↓ᵀ conversion body q replace) =
    ⊑conv↓ᵀ
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) conversion)
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      q replace


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
      (paired-downᵀ
        body source-mode source source-shape
        target-mode target target-shape square elimination) =
    paired-downᵀ
      (quotiented-parallel-term-substitution-framed-proofᵀ
        environment frame prefix noM noM′ body)
      (spine-cast-mode-prefix-proofᵀ
        (leftStoreⁱ-prefix-inclusion prefix) source-mode)
      (narrow-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) source)
      source-shape
      (spine-cast-mode-prefix-proofᵀ
        (rightStoreⁱ-prefix-inclusion prefix) target-mode)
      (narrow-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) target)
      target-shape square elimination

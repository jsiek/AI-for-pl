{-# OPTIONS --safe #-}

module proof.DGG.SimBackPairedFunValuesProof where

-- File Charter:
--   * Develops value-level backward simulation for paired function roots by
--     induction on the function-imprecision derivation.
--   * Is parameterized by CTI transport, source value catch-up, and the
--     separate substitution and target-rebase inductions needed by function
--     reduction.
--   * Exports a goal-free parameterized proof with no postulates or metas.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; subst; sym; trans)

open import Types using (Ty; TyCtx; TyVar; ★; _⇒_)
open import TyStore using (TyStore)
open import Consistency using (_↪ᵗ_; _↦_; toRenameᵗ; wk↪ᵗ)
open import CastTerms using
  ( Term; Value; blame; ⟨_,_,_⟩; `_; ƛ_; _·_; Λ_; _⦂∀_[_]
  ; $; _⊕[_]_; _[_]; _⟨_⟩; _《_》; _↑_; _↓_; fun; renameᵗᵐ
  )
open import Reduction
open import Imprecision using (⇒⊑⇒)
  renaming (X⊑★ to X⊑★ᵐ)
open import Primitives using (κℕ; κ𝔹)
open import Conversion using (_↦↑_; _↦↓_)
import Conversion as Conv
open import proof.DGG.CastTermImprecision
open import proof.DGG.CatchupToLessPreciseDef using
  (CatchupToLessPrecise)
open import proof.DGG.World
open import proof.DGG.SourceRebase using
  (source-rebase-count≢zero)
open import proof.DGG.SimBackPairedFunValuesDef using
  (SimBackPairedFunValuesᵀ)
open import proof.DGG.SimBackRebasedConversionDef using
  (SimBackTargetRevealRebaseFunValuesᵀ)
open import proof.DGG.TermImprecisionSubstitutionDef using
  (TermImprecisionSubstitutionᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.ConversionPivotAlignment using
  ( GeneratorPosition
  ; generator-absent
  ; generator-here
  ; generator-⇒-left
  ; generator-⇒-right
  ; generator-⇒-both
  ; generator-∀
  ; revealGeneratorPosition
  ; concealGeneratorPosition
  ; joinGeneratorPositions-absent-left
  ; joinGeneratorPositions-absent-right
  ; joinGeneratorPositions-equal-left
  ; joinGeneratorPositions-equal-right
  )
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; composeMultiWorldEvolution
  ; evolutions-refl
  ; evolutions-step-left
  ; evolutions-step-right
  ; evolutions-step-both
  ; multi-no-source-rebase
  ; multi-⊑ᵀ
  ; multi-source-mark
  ; multi-source-disaligned
  ; multi-source-reveal
  ; multi-source-conceal
  ; multi-source-reveal-position
  ; multi-source-conceal-position
  )
open import proof.Reduction
import proof.Imprecision as PI


private
  sourceFunctionLayers : ∀ {Δ} → Term Δ → Nat.ℕ
  sourceFunctionLayers (` x) = Nat.zero
  sourceFunctionLayers (ƛ M) = Nat.zero
  sourceFunctionLayers (L · M) = Nat.zero
  sourceFunctionLayers (Λ V) = Nat.zero
  sourceFunctionLayers (M ⦂∀ C [ A ]) = Nat.zero
  sourceFunctionLayers ($ κ) = Nat.zero
  sourceFunctionLayers (L ⊕[ op ] M) = Nat.zero
  sourceFunctionLayers (M ⟨ c ⟩) = Nat.suc (sourceFunctionLayers M)
  sourceFunctionLayers (M ↑ c) = Nat.suc (sourceFunctionLayers M)
  sourceFunctionLayers (M ↓ c) = Nat.suc (sourceFunctionLayers M)
  sourceFunctionLayers blame = Nat.zero

  sourceFunctionLayers-rename : ∀ {Δ Δ′}
      (ρ : Δ ↪ᵗ Δ′) (M : Term Δ)
    → sourceFunctionLayers (renameᵗᵐ ρ M) ≡ sourceFunctionLayers M
  sourceFunctionLayers-rename ρ (` x) = refl
  sourceFunctionLayers-rename ρ (ƛ M) = refl
  sourceFunctionLayers-rename ρ (L · M) = refl
  sourceFunctionLayers-rename ρ (Λ V) = refl
  sourceFunctionLayers-rename ρ (M ⦂∀ C [ A ]) = refl
  sourceFunctionLayers-rename ρ ($ κ) = refl
  sourceFunctionLayers-rename ρ (L ⊕[ op ] M) = refl
  sourceFunctionLayers-rename ρ (M ⟨ c ⟩) =
    cong Nat.suc (sourceFunctionLayers-rename ρ M)
  sourceFunctionLayers-rename ρ (M ↑ c) =
    cong Nat.suc (sourceFunctionLayers-rename ρ M)
  sourceFunctionLayers-rename ρ (M ↓ c) =
    cong Nat.suc (sourceFunctionLayers-rename ρ M)
  sourceFunctionLayers-rename ρ blame = refl

  sourceFunctionLayers-applyTerms : ∀ {Δ Δ′}
      (χs : StoreChanges Δ Δ′) (M : Term Δ)
    → sourceFunctionLayers (applyTerms χs M) ≡ sourceFunctionLayers M
  sourceFunctionLayers-applyTerms [] M = refl
  sourceFunctionLayers-applyTerms (keep ∷ χs) M =
    sourceFunctionLayers-applyTerms χs M
  sourceFunctionLayers-applyTerms (bind A ∷ χs) M =
    trans
      (sourceFunctionLayers-applyTerms χs (renameᵗᵐ wk↪ᵗ M))
      (sourceFunctionLayers-rename wk↪ᵗ M)


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-less-precise : CatchupToLessPrecise)
    (term-imprecision-substitution : TermImprecisionSubstitutionᵀ)
    (sim-back-target-reveal-rebase-fun-values :
      SimBackTargetRevealRebaseFunValuesᵀ)
  where

  generator-here≢absent : generator-here ≢ generator-absent
  generator-here≢absent ()

  generator-left≢absent : ∀ {position : GeneratorPosition}
    → generator-⇒-left position ≢ generator-absent
  generator-left≢absent ()

  generator-right≢absent : ∀ {position : GeneratorPosition}
    → generator-⇒-right position ≢ generator-absent
  generator-right≢absent ()

  generator-both≢absent : ∀ {left right : GeneratorPosition}
    → generator-⇒-both left right ≢ generator-absent
  generator-both≢absent ()

  generator-all≢absent : ∀ {position : GeneratorPosition}
    → generator-∀ position ≢ generator-absent
  generator-all≢absent ()

  source-reveal-one-sided : ∀ {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv.Conv↑ Δᴸ A A′}
    → (c⊢ : Σᴸ Conv.⊢↑[ X ⦂ R ] c)
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) X) ≡ X⊑★ᵐ
    → (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y ≢ toRenameⁱ (ηᴸᶜ γ) X)
    → R ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → γ ⊢² M ↑ c ⊑ M′ ∶ q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
      with revealGeneratorPosition c⊢ in position-eq
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-absent = reveal⊑-identity c⊢ position-eq rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-here =
      reveal⊑-only² c⊢
        (λ absent → generator-here≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-left position =
      reveal⊑-only² c⊢
        (λ absent → generator-left≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-right position =
      reveal⊑-only² c⊢
        (λ absent → generator-right≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-both left right =
      reveal⊑-only² c⊢
        (λ absent → generator-both≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-∀ position =
      reveal⊑-only² c⊢
        (λ absent → generator-all≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q

  source-conceal-one-sided : ∀ {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv.Conv↓ Δᴸ A A′}
    → (c⊢ : Σᴸ Conv.⊢↓[ X ⦂ R ] c)
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) X) ≡ X⊑★ᵐ
    → (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y ≢ toRenameⁱ (ηᴸᶜ γ) X)
    → R ⊑ᵀ⟨ γ ⟩ ★
    → γ ⊢² M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ γ ⟩ B)
    → γ ⊢² M ↓ c ⊑ M′ ∶ q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
      with concealGeneratorPosition c⊢ in position-eq
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-absent = conceal⊑-identity c⊢ position-eq rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-here =
      conceal⊑-only² c⊢
        (λ absent → generator-here≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-left position =
      conceal⊑-only² c⊢
        (λ absent → generator-left≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-right position =
      conceal⊑-only² c⊢
        (λ absent → generator-right≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-both left right =
      conceal⊑-only² c⊢
        (λ absent → generator-both≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-∀ position =
      conceal⊑-only² c⊢
        (λ absent → generator-all≢absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q

  worker : ∀ {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {V W : Term Δᴸ} {V′ W′ N′ : Term Δᴿ}
      {C : Ty Δᴸ} {C′ : Ty Δᴿ}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {p : C ⊑ᵀ⟨ γ ⟩ C′}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    → sourceRebaseCountᶜ γ ≡ 0
    → (fuel : Nat.ℕ)
    → sourceFunctionLayers V < fuel
    → γ ⊢² V ⊑ V′ ∶ p
    → C ≡ (A ⇒ B)
    → C′ ≡ (A′ ⇒ B′)
    → γ ⊢² W ⊑ W′ ∶ pA
    → Value V
    → Value W
    → Value V′
    → Value W′
    → V′ · W′ —→ N′
    → (Σ[ Δᴸ′ ∈ TyCtx ]
        Σ[ Σᴸ′ ∈ TyStore Δᴸ′ ]
        Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
        Σ[ N ∈ Term Δᴸ′ ]
        Σ[ γ′ ∈
          ⟨ Δᴸ′ , Σᴸ′ , [] ⟩ ⊑ᶜ
          ⟨ Δᴿ , applyStore keep Σᴿ , [] ⟩ ]
        Σ[ q ∈ applyTys χsᴸ B ⊑ᵀ⟨ γ′ ⟩ applyTy keep B′ ]
          (V · W —↠[ χsᴸ ] N)
          × MultiWorldEvolution
              {W = γ} {W′ = γ′} χsᴸ (keep ∷ [])
          × (γ′ ⊢² N ⊑ N′ ∶ q))
      ⊎ (∃[ Δᴸ′ ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
          (V · W —↠[ χsᴸ ] blame))

  worker no-rebase Nat.zero ()

  worker no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-rebase² c′⊢ rebase related q)
      source-arrow target-arrow arg-rel source-fun-value source-arg-value
      target-fun-value target-arg-value target-step =
    ⊥-elim (source-rebase-count≢zero rebase no-rebase)

  worker {Σᴸ = Σᴸ} {γ = γ} {W = W} {pA = pA} {pB = pB}
      no-rebase (Nat.suc fuel) size-bound
      (ƛ⊑ƛ² {M = M} {M′ = M′} {pA = pA₁} {pB = pB₁} body-rel)
      refl refl arg-rel
      source-fun-value source-arg-value target-fun-value target-arg-value
      (β root-arg-value)
      rewrite PI.⊑-unique pA₁ pA | PI.⊑-unique pB₁ pB =
    inj₁
      (_ , Σᴸ , (keep ∷ []) , M [ W ] , γ , _ ,
        ((ƛ M) · W
          —→[ keep ]⟨ pure-step (β source-arg-value) ⟩
         M [ W ] ∎[]) ,
        evolutions-step-both refl refl evolution-keep evolutions-refl ,
        term-imprecision-substitution arg-rel body-rel)

  worker no-rebase (Nat.suc fuel) size-bound
      (κ⊑κ² (κℕ n) p) () target-arrow arg-rel
      source-fun-value source-arg-value target-fun-value target-arg-value
      target-step

  worker no-rebase (Nat.suc fuel) size-bound
      (κ⊑κ² (κ𝔹 b) p) () target-arrow arg-rel
      source-fun-value source-arg-value target-fun-value target-arg-value
      target-step

  worker {Σᴸ = Σᴸ} {γ = γ} {W = W} {pA = pA} {pB = pB}
      no-rebase (Nat.suc fuel) size-bound
      (cast⊑cast² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast)
        (target-domain-cast ↦ target-result-cast) body-rel q)
      refl refl arg-rel
      (source-body-value 《 fun 》) source-arg-value
      (target-body-value 《 fun 》) target-arg-value
      (β-⇒ target-root-fun-value target-root-arg-value) =
    inj₁
      (_ , Σᴸ , (keep ∷ []) ,
        (M · (W ⟨ source-domain-cast ⟩)) ⟨ source-result-cast ⟩ ,
        γ , pB ,
        (((M ⟨ source-domain-cast ↦ source-result-cast ⟩) · W)
          —→[ keep ]⟨ pure-step
            (β-⇒ source-body-value source-arg-value) ⟩
         (M · (W ⟨ source-domain-cast ⟩))
           ⟨ source-result-cast ⟩ ∎[]) ,
        evolutions-step-both refl refl evolution-keep evolutions-refl ,
        cast⊑cast² source-result-cast target-result-cast
          (·⊑·² body-rel
            (cast⊑cast² source-domain-cast target-domain-cast
              arg-rel inner-argument-rel))
          pB)

  worker {Σᴸ = Σᴸ} {γ = γ} {V = V} {W = W}
      {pA = pA} {pB = pB} no-rebase (Nat.suc fuel) size-bound
      (⊑cast² {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (target-domain-cast ↦ target-result-cast) body-rel q)
      refl refl arg-rel source-fun-value source-arg-value
      (target-body-value 《 fun 》) target-arg-value
      (β-⇒ root-fun-value root-arg-value) =
    inj₁
      (_ , Σᴸ , [] , V · W , γ , pB ,
        (V · W ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        ⊑cast² target-result-cast
          (·⊑·² body-rel
            (⊑cast² target-domain-cast arg-rel inner-argument-rel))
          pB)

  worker {Σᴸ = Σᴸ} {γ = γ} {V = V} {W = W}
      {pA = pA} {pB = pB} no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-identity {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ target-domain⊢ target-result⊢) absent
        body-rel q)
      refl refl arg-rel source-fun-value source-arg-value
      (target-body-value ↑ fun) target-arg-value
      (β-reveal-⇒ target-root-fun-value target-root-arg-value) =
    inj₁
      (_ , Σᴸ , [] , V · W , γ , pB ,
        (V · W ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        ⊑reveal-identity target-result⊢
          (joinGeneratorPositions-absent-right absent)
          (·⊑·² body-rel
            (⊑conceal-identity target-domain⊢
              (joinGeneratorPositions-absent-left absent)
              arg-rel inner-argument-rel))
          pB)

  worker {Σᴸ = Σᴸ} {γ = γ} {V = V} {W = W}
      {pA = pA} {pB = pB} no-rebase (Nat.suc fuel) size-bound
      (⊑conceal-identity {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ target-domain⊢ target-result⊢) absent
        body-rel q)
      refl refl arg-rel source-fun-value source-arg-value
      (target-body-value ↓ fun) target-arg-value
      (β-conceal-⇒ target-root-fun-value target-root-arg-value) =
    inj₁
      (_ , Σᴸ , [] , V · W , γ , pB ,
        (V · W ∎[]) ,
        evolutions-step-right refl evolution-keep evolutions-refl ,
        ⊑conceal-identity target-result⊢
          (joinGeneratorPositions-absent-right absent)
          (·⊑·² body-rel
            (⊑reveal-identity target-domain⊢
              (joinGeneratorPositions-absent-left absent)
              arg-rel inner-argument-rel))
          pB)

  worker {W = W} {pB = pB} no-rebase (Nat.suc fuel) (s≤s smaller)
      (cast⊑² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast) body-rel q)
      refl refl arg-rel
      (source-body-value 《 fun 》) source-arg-value
      target-fun-value target-arg-value target-step
      with catchup-to-less-precise no-rebase
        (cast⊑² source-domain-cast arg-rel inner-argument-rel)
        target-arg-value
  worker {W = W} {N′ = N′} {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (cast⊑² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast) body-rel q)
      refl refl arg-rel
      (source-body-value 《 fun 》) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₂
        (argument-Δ , _ , argument-changes , _ ,
          argument-blame-steps , argument-evolution) =
    inj₂
      (argument-Δ ,
        keep ∷
          ((argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])) ,
        ((M ⟨ source-domain-cast ↦ source-result-cast ⟩) · W
          —→[ keep ]⟨ pure-step
            (β-⇒ source-body-value source-arg-value) ⟩
         (M · (W ⟨ source-domain-cast ⟩)) ⟨ source-result-cast ⟩
          —↠[
            (argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])
          ]⟨ cast-blame-↠ source-result-cast
            (appR-blame-↠ source-body-value argument-blame-steps) ⟩
         blame ∎[]))
  worker {W = W} {N′ = N′} {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (cast⊑² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast) body-rel q)
      refl refl arg-rel
      (source-body-value 《 fun 》) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
      with worker
        {pA = argument-type-rel}
        {pB = multi-⊑ᵀ argument-evolution inner-result-rel}
        (multi-no-source-rebase argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (sourceFunctionLayers-applyTerms argument-changes M))
          smaller)
        (transport-CTI no-rebase argument-evolution body-rel)
        (applyTys-⇒ argument-changes _ _) refl argument-rel
        (applyTerms-preserves-Value argument-changes source-body-value)
        source-argument-value target-fun-value target-arg-value target-step
  worker {W = W} {N′ = N′} {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (cast⊑² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast) body-rel q)
      refl refl arg-rel
      (source-body-value 《 fun 》) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₁
        (result-Δ , result-store , result-changes , result , result-world ,
          result-type-rel , result-steps , result-evolution , result-rel) =
    let normalized-result =
          subst
            (λ S →
              Σ[ r ∈ S ⊑ᵀ⟨ result-world ⟩ _ ]
                result-world ⊢² result ⊑ N′ ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel , result-rel)
        total-evolution =
          composeMultiWorldEvolution
            (evolutions-step-left refl evolution-keep argument-evolution)
            result-evolution
    in inj₁
      (result-Δ , result-store ,
        keep ∷ (argument-changes ++χ result-changes) ,
        result ⟨ applyConsistencies
          (argument-changes ++χ result-changes) source-result-cast ⟩ ,
        result-world ,
        multi-⊑ᵀ total-evolution pB ,
        subst
          (λ final →
            (M ⟨ source-domain-cast ↦ source-result-cast ⟩) · W
              —↠[
                keep ∷ (argument-changes ++χ result-changes)
              ] final)
          (cast-applyConsistencies-++ argument-changes result-changes
            source-result-cast result)
          (((M ⟨ source-domain-cast ↦ source-result-cast ⟩) · W
            —→[ keep ]⟨ pure-step
              (β-⇒ source-body-value source-arg-value) ⟩
           (M · (W ⟨ source-domain-cast ⟩)) ⟨ source-result-cast ⟩
            —↠+[ argument-changes ]⟨
              cast-↠ source-result-cast
                (appR-↠ source-body-value argument-steps) ⟩
           (applyTerms argument-changes M · source-argument)
             ⟨ applyConsistencies argument-changes source-result-cast ⟩
            —↠[ result-changes ]⟨
              cast-↠
                (applyConsistencies argument-changes source-result-cast)
                result-steps ⟩
           result ⟨ applyConsistencies result-changes
             (applyConsistencies argument-changes
               source-result-cast) ⟩ ∎[])) ,
        total-evolution ,
        cast⊑²
          (applyConsistencies
            (argument-changes ++χ result-changes) source-result-cast)
          (proj₂ normalized-result)
          (multi-⊑ᵀ total-evolution pB))
  worker {W = W} {pB = pB} no-rebase (Nat.suc fuel) (s≤s smaller)
      (cast⊑² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast) body-rel q)
      refl refl arg-rel
      (source-body-value 《 fun 》) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₂ (result-Δ , result-changes , result-blame-steps) =
    inj₂
      (result-Δ ,
        keep ∷
          (argument-changes ++χ
            (result-changes ++χ (keep ∷ []))) ,
        ((M ⟨ source-domain-cast ↦ source-result-cast ⟩) · W
          —→[ keep ]⟨ pure-step
            (β-⇒ source-body-value source-arg-value) ⟩
         (M · (W ⟨ source-domain-cast ⟩)) ⟨ source-result-cast ⟩
          —↠+[ argument-changes ]⟨
            cast-↠ source-result-cast
              (appR-↠ source-body-value argument-steps) ⟩
         (applyTerms argument-changes M · source-argument)
           ⟨ applyConsistencies argument-changes source-result-cast ⟩
          —↠[
            result-changes ++χ (keep ∷ [])
          ]⟨ cast-blame-↠
            (applyConsistencies argument-changes source-result-cast)
            result-blame-steps ⟩
         blame ∎[]))

  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
      with catchup-to-less-precise no-rebase
        (conceal⊑-identity source-domain⊢
          (joinGeneratorPositions-absent-left absent)
          arg-rel inner-argument-rel)
        target-arg-value
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₂
        (argument-Δ , _ , argument-changes , _ ,
          argument-blame-steps , argument-evolution) =
    inj₂
      (argument-Δ ,
        keep ∷
          ((argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])) ,
        (((M ↑
            (source-domain-conversion ↦↑ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-reveal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↓ source-domain-conversion))
           ↑ source-result-conversion
          —↠[
            (argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])
          ]⟨ reveal-blame-↠ source-result-conversion
            (appR-blame-↠ source-body-value argument-blame-steps) ⟩
         blame ∎[]))
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
      with worker
        {pA = argument-type-rel}
        {pB = multi-⊑ᵀ argument-evolution inner-result-rel}
        (multi-no-source-rebase argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (sourceFunctionLayers-applyTerms argument-changes M))
          smaller)
        (transport-CTI no-rebase argument-evolution body-rel)
        (applyTys-⇒ argument-changes _ _) refl argument-rel
        (applyTerms-preserves-Value argument-changes source-body-value)
        source-argument-value target-fun-value target-arg-value target-step
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₁
        (result-Δ , result-store , result-changes , result , result-world ,
          result-type-rel , result-steps , result-evolution , result-rel) =
    let normalized-result =
          subst
            (λ S →
              Σ[ r ∈ S ⊑ᵀ⟨ result-world ⟩ _ ]
                result-world ⊢² result ⊑ N′ ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          composeMultiWorldEvolution
            (evolutions-step-left refl evolution-keep argument-evolution)
            result-evolution
    in inj₁
      (result-Δ , result-store ,
        keep ∷ (argument-changes ++χ result-changes) ,
        result ↑ applyReveals
          (argument-changes ++χ result-changes)
          source-result-conversion ,
        result-world ,
        multi-⊑ᵀ total-evolution pB ,
        subst
          (λ final →
            ((M ↑
              (source-domain-conversion ↦↑ source-result-conversion)) · W)
              —↠[
                keep ∷ (argument-changes ++χ result-changes)
              ] final)
          (reveal-applyReveals-++ argument-changes result-changes
            source-result-conversion result)
          ((((M ↑
              (source-domain-conversion ↦↑ source-result-conversion)) · W)
            —→[ keep ]⟨ pure-step
              (β-reveal-⇒ source-body-value source-arg-value) ⟩
           (M · (W ↓ source-domain-conversion))
             ↑ source-result-conversion
            —↠+[ argument-changes ]⟨
              reveal-↠ source-result-conversion
                (appR-↠ source-body-value argument-steps) ⟩
           (applyTerms argument-changes M · source-argument)
             ↑ applyReveals argument-changes source-result-conversion
            —↠[ result-changes ]⟨
              reveal-↠
                (applyReveals argument-changes source-result-conversion)
                result-steps ⟩
           result ↑ applyReveals result-changes
             (applyReveals argument-changes
               source-result-conversion) ∎[])) ,
        total-evolution ,
        reveal⊑-identity
          (multi-source-reveal payload-evolution source-result⊢)
          (trans
            (multi-source-reveal-position payload-evolution source-result⊢)
            (joinGeneratorPositions-absent-right absent))
          (proj₂ normalized-result)
          (multi-⊑ᵀ total-evolution pB))
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₂ (result-Δ , result-changes , result-blame-steps) =
    inj₂
      (result-Δ ,
        keep ∷
          (argument-changes ++χ
            (result-changes ++χ (keep ∷ []))) ,
        (((M ↑
            (source-domain-conversion ↦↑ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-reveal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↓ source-domain-conversion))
           ↑ source-result-conversion
          —↠+[ argument-changes ]⟨
            reveal-↠ source-result-conversion
              (appR-↠ source-body-value argument-steps) ⟩
         (applyTerms argument-changes M · source-argument)
           ↑ applyReveals argument-changes source-result-conversion
          —↠[ result-changes ++χ (keep ∷ []) ]⟨
            reveal-blame-↠
              (applyReveals argument-changes source-result-conversion)
              result-blame-steps ⟩
         blame ∎[]))

  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-only²
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
      with catchup-to-less-precise no-rebase
        (source-conceal-one-sided source-domain⊢ marked unoccupied
          represented arg-rel inner-argument-rel)
        target-arg-value
  worker {V = M ↑ c} {W = W} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-only²
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₂
        (argument-Δ , _ , argument-changes , _ ,
          argument-blame-steps , argument-evolution) =
    inj₂
      (argument-Δ ,
        keep ∷
          ((argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])) ,
        (((M ↑
            (source-domain-conversion ↦↑ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-reveal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↓ source-domain-conversion))
           ↑ source-result-conversion
          —↠[
            (argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])
          ]⟨ reveal-blame-↠ source-result-conversion
            (appR-blame-↠ source-body-value argument-blame-steps) ⟩
         blame ∎[]))
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-only²
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
      with worker
        {pA = argument-type-rel}
        {pB = multi-⊑ᵀ argument-evolution inner-result-rel}
        (multi-no-source-rebase argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (sourceFunctionLayers-applyTerms argument-changes M))
          smaller)
        (transport-CTI no-rebase argument-evolution body-rel)
        (applyTys-⇒ argument-changes _ _) refl argument-rel
        (applyTerms-preserves-Value argument-changes source-body-value)
        source-argument-value target-fun-value target-arg-value target-step
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-only²
        {Rᴸ = Rᴸ} {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₁
        (result-Δ , result-store , result-changes , result , result-world ,
          result-type-rel , result-steps , result-evolution , result-rel) =
    let normalized-result =
          subst
            (λ S →
              Σ[ r ∈ S ⊑ᵀ⟨ result-world ⟩ _ ]
                result-world ⊢² result ⊑ N′ ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          composeMultiWorldEvolution
            (evolutions-step-left refl evolution-keep argument-evolution)
            result-evolution
    in inj₁
      (result-Δ , result-store ,
        keep ∷ (argument-changes ++χ result-changes) ,
        result ↑ applyReveals
          (argument-changes ++χ result-changes)
          source-result-conversion ,
        result-world ,
        multi-⊑ᵀ total-evolution pB ,
        subst
          (λ final →
            ((M ↑
              (source-domain-conversion ↦↑ source-result-conversion)) · W)
              —↠[
                keep ∷ (argument-changes ++χ result-changes)
              ] final)
          (reveal-applyReveals-++ argument-changes result-changes
            source-result-conversion result)
          ((((M ↑
              (source-domain-conversion ↦↑ source-result-conversion)) · W)
            —→[ keep ]⟨ pure-step
              (β-reveal-⇒ source-body-value source-arg-value) ⟩
           (M · (W ↓ source-domain-conversion))
             ↑ source-result-conversion
            —↠+[ argument-changes ]⟨
              reveal-↠ source-result-conversion
                (appR-↠ source-body-value argument-steps) ⟩
           (applyTerms argument-changes M · source-argument)
             ↑ applyReveals argument-changes source-result-conversion
            —↠[ result-changes ]⟨
              reveal-↠
                (applyReveals argument-changes source-result-conversion)
                result-steps ⟩
           result ↑ applyReveals result-changes
             (applyReveals argument-changes
               source-result-conversion) ∎[])) ,
        total-evolution ,
        source-reveal-one-sided
          (multi-source-reveal payload-evolution source-result⊢)
          (multi-source-mark payload-evolution marked)
          (multi-source-disaligned payload-evolution unoccupied)
          (subst
            (λ T → applyTys
              (argument-changes ++χ result-changes) Rᴸ
                ⊑ᵀ⟨ result-world ⟩ T)
            (applyTys-★ (keep ∷ []))
            (multi-⊑ᵀ payload-evolution represented))
          (proj₂ normalized-result)
          (multi-⊑ᵀ total-evolution pB))
  worker {V = M ↑ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (reveal⊑-only²
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₂ (result-Δ , result-changes , result-blame-steps) =
    inj₂
      (result-Δ ,
        keep ∷
          (argument-changes ++χ
            (result-changes ++χ (keep ∷ []))) ,
        (((M ↑
            (source-domain-conversion ↦↑ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-reveal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↓ source-domain-conversion))
           ↑ source-result-conversion
          —↠+[ argument-changes ]⟨
            reveal-↠ source-result-conversion
              (appR-↠ source-body-value argument-steps) ⟩
         (applyTerms argument-changes M · source-argument)
           ↑ applyReveals argument-changes source-result-conversion
          —↠[ result-changes ++χ (keep ∷ []) ]⟨
            reveal-blame-↠
              (applyReveals argument-changes source-result-conversion)
              result-blame-steps ⟩
         blame ∎[]))

  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
      with catchup-to-less-precise no-rebase
        (reveal⊑-identity source-domain⊢
          (joinGeneratorPositions-absent-left absent)
          arg-rel inner-argument-rel)
        target-arg-value
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₂
        (argument-Δ , _ , argument-changes , _ ,
          argument-blame-steps , argument-evolution) =
    inj₂
      (argument-Δ ,
        keep ∷
          ((argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])) ,
        (((M ↓
            (source-domain-conversion ↦↓ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-conceal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↑ source-domain-conversion))
           ↓ source-result-conversion
          —↠[
            (argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])
          ]⟨ conceal-blame-↠ source-result-conversion
            (appR-blame-↠ source-body-value argument-blame-steps) ⟩
         blame ∎[]))
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
      with worker
        {pA = argument-type-rel}
        {pB = multi-⊑ᵀ argument-evolution inner-result-rel}
        (multi-no-source-rebase argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (sourceFunctionLayers-applyTerms argument-changes M))
          smaller)
        (transport-CTI no-rebase argument-evolution body-rel)
        (applyTys-⇒ argument-changes _ _) refl argument-rel
        (applyTerms-preserves-Value argument-changes source-body-value)
        source-argument-value target-fun-value target-arg-value target-step
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₁
        (result-Δ , result-store , result-changes , result , result-world ,
          result-type-rel , result-steps , result-evolution , result-rel) =
    let normalized-result =
          subst
            (λ S →
              Σ[ r ∈ S ⊑ᵀ⟨ result-world ⟩ _ ]
                result-world ⊢² result ⊑ N′ ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          composeMultiWorldEvolution
            (evolutions-step-left refl evolution-keep argument-evolution)
            result-evolution
    in inj₁
      (result-Δ , result-store ,
        keep ∷ (argument-changes ++χ result-changes) ,
        result ↓ applyConceals
          (argument-changes ++χ result-changes)
          source-result-conversion ,
        result-world ,
        multi-⊑ᵀ total-evolution pB ,
        subst
          (λ final →
            ((M ↓
              (source-domain-conversion ↦↓ source-result-conversion)) · W)
              —↠[
                keep ∷ (argument-changes ++χ result-changes)
              ] final)
          (conceal-applyConceals-++ argument-changes result-changes
            source-result-conversion result)
          ((((M ↓
              (source-domain-conversion ↦↓ source-result-conversion)) · W)
            —→[ keep ]⟨ pure-step
              (β-conceal-⇒ source-body-value source-arg-value) ⟩
           (M · (W ↑ source-domain-conversion))
             ↓ source-result-conversion
            —↠+[ argument-changes ]⟨
              conceal-↠ source-result-conversion
                (appR-↠ source-body-value argument-steps) ⟩
           (applyTerms argument-changes M · source-argument)
             ↓ applyConceals argument-changes source-result-conversion
            —↠[ result-changes ]⟨
              conceal-↠
                (applyConceals argument-changes source-result-conversion)
                result-steps ⟩
           result ↓ applyConceals result-changes
             (applyConceals argument-changes
               source-result-conversion) ∎[])) ,
        total-evolution ,
        conceal⊑-identity
          (multi-source-conceal payload-evolution source-result⊢)
          (trans
            (multi-source-conceal-position payload-evolution source-result⊢)
            (joinGeneratorPositions-absent-right absent))
          (proj₂ normalized-result)
          (multi-⊑ᵀ total-evolution pB))
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        absent
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₂ (result-Δ , result-changes , result-blame-steps) =
    inj₂
      (result-Δ ,
        keep ∷
          (argument-changes ++χ
            (result-changes ++χ (keep ∷ []))) ,
        (((M ↓
            (source-domain-conversion ↦↓ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-conceal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↑ source-domain-conversion))
           ↓ source-result-conversion
          —↠+[ argument-changes ]⟨
            conceal-↠ source-result-conversion
              (appR-↠ source-body-value argument-steps) ⟩
         (applyTerms argument-changes M · source-argument)
           ↓ applyConceals argument-changes source-result-conversion
          —↠[ result-changes ++χ (keep ∷ []) ]⟨
            conceal-blame-↠
              (applyConceals argument-changes source-result-conversion)
              result-blame-steps ⟩
         blame ∎[]))

  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-only²
        {Rᴸ = Rᴸ} {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
      with catchup-to-less-precise no-rebase
        (source-reveal-one-sided source-domain⊢ marked unoccupied
          represented arg-rel inner-argument-rel)
        target-arg-value
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-only²
        {Rᴸ = Rᴸ} {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₂
        (argument-Δ , _ , argument-changes , _ ,
          argument-blame-steps , argument-evolution) =
    inj₂
      (argument-Δ ,
        keep ∷
          ((argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])) ,
        (((M ↓
            (source-domain-conversion ↦↓ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-conceal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↑ source-domain-conversion))
           ↓ source-result-conversion
          —↠[
            (argument-changes ++χ (keep ∷ [])) ++χ (keep ∷ [])
          ]⟨ conceal-blame-↠ source-result-conversion
            (appR-blame-↠ source-body-value argument-blame-steps) ⟩
         blame ∎[]))
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-only²
        {Rᴸ = Rᴸ} {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
      with worker
        {pA = argument-type-rel}
        {pB = multi-⊑ᵀ argument-evolution inner-result-rel}
        (multi-no-source-rebase argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (sourceFunctionLayers-applyTerms argument-changes M))
          smaller)
        (transport-CTI no-rebase argument-evolution body-rel)
        (applyTys-⇒ argument-changes _ _) refl argument-rel
        (applyTerms-preserves-Value argument-changes source-body-value)
        source-argument-value target-fun-value target-arg-value target-step
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-only²
        {Rᴸ = Rᴸ} {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₁
        (result-Δ , result-store , result-changes , result , result-world ,
          result-type-rel , result-steps , result-evolution , result-rel) =
    let normalized-result =
          subst
            (λ S →
              Σ[ r ∈ S ⊑ᵀ⟨ result-world ⟩ _ ]
                result-world ⊢² result ⊑ N′ ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          composeMultiWorldEvolution
            (evolutions-step-left refl evolution-keep argument-evolution)
            result-evolution
    in inj₁
      (result-Δ , result-store ,
        keep ∷ (argument-changes ++χ result-changes) ,
        result ↓ applyConceals
          (argument-changes ++χ result-changes)
          source-result-conversion ,
        result-world ,
        multi-⊑ᵀ total-evolution pB ,
        subst
          (λ final →
            ((M ↓
              (source-domain-conversion ↦↓ source-result-conversion)) · W)
              —↠[
                keep ∷ (argument-changes ++χ result-changes)
              ] final)
          (conceal-applyConceals-++ argument-changes result-changes
            source-result-conversion result)
          ((((M ↓
              (source-domain-conversion ↦↓ source-result-conversion)) · W)
            —→[ keep ]⟨ pure-step
              (β-conceal-⇒ source-body-value source-arg-value) ⟩
           (M · (W ↑ source-domain-conversion))
             ↓ source-result-conversion
            —↠+[ argument-changes ]⟨
              conceal-↠ source-result-conversion
                (appR-↠ source-body-value argument-steps) ⟩
           (applyTerms argument-changes M · source-argument)
             ↓ applyConceals argument-changes source-result-conversion
            —↠[ result-changes ]⟨
              conceal-↠
                (applyConceals argument-changes source-result-conversion)
                result-steps ⟩
           result ↓ applyConceals result-changes
             (applyConceals argument-changes
               source-result-conversion) ∎[])) ,
        total-evolution ,
        source-conceal-one-sided
          (multi-source-conceal payload-evolution source-result⊢)
          (multi-source-mark payload-evolution marked)
          (multi-source-disaligned payload-evolution unoccupied)
          (subst
            (λ T → applyTys
              (argument-changes ++χ result-changes) Rᴸ
                ⊑ᵀ⟨ result-world ⟩ T)
            (applyTys-★ (keep ∷ []))
            (multi-⊑ᵀ payload-evolution represented))
          (proj₂ normalized-result)
          (multi-⊑ᵀ total-evolution pB))
  worker {V = M ↓ c} {W = W} {N′ = N′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      (conceal⊑-only²
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        present marked unoccupied represented
        body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      target-fun-value target-arg-value target-step
    | inj₁
        (_ , _ , argument-changes , source-argument , argument-world ,
          argument-type-rel , argument-steps , source-argument-value ,
          argument-evolution , argument-rel)
    | inj₂ (result-Δ , result-changes , result-blame-steps) =
    inj₂
      (result-Δ ,
        keep ∷
          (argument-changes ++χ
            (result-changes ++χ (keep ∷ []))) ,
        (((M ↓
            (source-domain-conversion ↦↓ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-conceal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↑ source-domain-conversion))
           ↓ source-result-conversion
          —↠+[ argument-changes ]⟨
            conceal-↠ source-result-conversion
              (appR-↠ source-body-value argument-steps) ⟩
         (applyTerms argument-changes M · source-argument)
           ↓ applyConceals argument-changes source-result-conversion
          —↠[ result-changes ++χ (keep ∷ []) ]⟨
            conceal-blame-↠
              (applyConceals argument-changes source-result-conversion)
              result-blame-steps ⟩
         blame ∎[]))

  worker {Σᴸ = Σᴸ} {γ = γ} {W = W} {pB = pB}
      no-rebase (Nat.suc fuel) size-bound
      (reveal⊑reveal² {M = M}
        (Conv.⊢↑-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        positions aligned represented
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel} body-rel q)
      refl refl arg-rel
      (source-body-value ↑ fun) source-arg-value
      (target-body-value ↑ fun) target-arg-value
      (β-reveal-⇒ target-root-fun-value target-root-arg-value) =
    inj₁
      (_ , Σᴸ , (keep ∷ []) ,
        (M · (W ↓ source-domain-conversion)) ↑ source-result-conversion ,
        γ , pB ,
        (((M ↑
            (source-domain-conversion ↦↑ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-reveal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↓ source-domain-conversion))
           ↑ source-result-conversion ∎[]) ,
        evolutions-step-both refl refl evolution-keep evolutions-refl ,
        reveal⊑reveal² source-result⊢ target-result⊢
          (joinGeneratorPositions-equal-right positions)
          aligned represented
          (·⊑·² body-rel
            (conceal⊑conceal² source-domain⊢ target-domain⊢
              (joinGeneratorPositions-equal-left positions)
              aligned represented arg-rel inner-argument-rel))
          pB)

  worker {Σᴸ = Σᴸ} {γ = γ} {W = W} {pB = pB}
      no-rebase (Nat.suc fuel) size-bound
      (conceal⊑conceal² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = source-domain-conversion}
          {d = source-result-conversion} source-domain⊢ source-result⊢)
        (Conv.⊢↓-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        positions aligned represented body-rel q)
      refl refl arg-rel
      (source-body-value ↓ fun) source-arg-value
      (target-body-value ↓ fun) target-arg-value
      (β-conceal-⇒ target-root-fun-value target-root-arg-value) =
    inj₁
      (_ , Σᴸ , (keep ∷ []) ,
        (M · (W ↑ source-domain-conversion))
          ↓ source-result-conversion , γ , pB ,
        (((M ↓
            (source-domain-conversion ↦↓ source-result-conversion)) · W)
          —→[ keep ]⟨ pure-step
            (β-conceal-⇒ source-body-value source-arg-value) ⟩
         (M · (W ↑ source-domain-conversion))
           ↓ source-result-conversion ∎[]) ,
        evolutions-step-both refl refl evolution-keep evolutions-refl ,
        conceal⊑conceal² source-result⊢ target-result⊢
          (joinGeneratorPositions-equal-right positions)
          aligned represented
          (·⊑·² body-rel
            (reveal⊑reveal² source-domain⊢ target-domain⊢
              (joinGeneratorPositions-equal-left positions)
              aligned represented arg-rel inner-argument-rel))
          pB)

  worker {pA = pA} {pB = pB} no-rebase (Nat.suc fuel) size-bound
      (⊑reveal-rebase²
        (Conv.⊢↑-⇒ target-domain⊢ target-result⊢)
        rebase
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel} body-rel q)
      refl refl arg-rel source-fun-value source-arg-value
      (target-body-value ↑ fun) target-arg-value
      (β-reveal-⇒ target-root-fun-value target-root-arg-value) =
    sim-back-target-reveal-rebase-fun-values {pA = pA} {pB = pB} no-rebase
      (Conv.⊢↑-⇒ target-domain⊢ target-result⊢)
      rebase inner-argument-rel inner-result-rel
      body-rel arg-rel source-fun-value source-arg-value target-body-value
      target-arg-value

  sim-back-paired-fun-values : SimBackPairedFunValuesᵀ
  sim-back-paired-fun-values {V = V} {pA = pA} {pB = pB}
      no-rebase fun-rel
      arg-rel source-fun-value source-arg-value target-fun-value
      target-arg-value target-step =
    worker {pA = pA} {pB = pB} no-rebase
      (Nat.suc (sourceFunctionLayers V))
      (n<1+n (sourceFunctionLayers V)) fun-rel refl refl arg-rel
      source-fun-value
      source-arg-value target-fun-value target-arg-value target-step

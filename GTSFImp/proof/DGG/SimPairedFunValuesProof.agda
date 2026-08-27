{-# OPTIONS --safe #-}

module proof.DGG.SimPairedFunValuesProof where

-- File Charter:
--   * Proves value-level forward simulation for the nine paired function
--     root cases selected by the source reduction.
--   * Is parameterized by CTI transport, target value catch-up, substitution,
--     and target reveal-rebase closing.
--   * Uses direct zero- or one-step target traces and introduces no root
--     classifier or residual-family interface.

open import Data.List using ([])
import Data.Nat as Nat
open import Data.Nat using (_<_ ; s≤s)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_,_; _×_; proj₂; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; refl; subst; sym; trans)

open import Types using (Ty; TyCtx; TyVar; ★; _⇒_)
open import TyStore using (TyStore)
open import Consistency using (_↪ᵗ_; _↦_; wk↪ᵗ)
open import CastTerms using
  ( Term; Value; ⟨_,_,_⟩; `_; _·_; ƛ_; Λ_; _⦂∀_[_]; $; _⊕[_]_
  ; _[_]; _⟨_⟩; _《_》; _↑_; _↓_; fun; blame; renameᵗᵐ
  )
open import Reduction
open import Imprecision using (⇒⊑⇒)
  renaming (X⊑★ to X⊑★ᵐ)
import Conversion as Conv
open import proof.DGG.CastTermImprecision
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupToMorePrecise)
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
open import proof.DGG.SimPairedFunValuesDef using
  (SimPairedFunValuesᵀ)
open import proof.DGG.SimTargetRevealRebaseClosingDef using
  (SimTargetRevealRebaseClosingᵀ)
open import proof.DGG.SourceRebase using
  (open-source-rebase-nonempty)
open import proof.DGG.TermImprecisionSubstitutionDef using
  (TermImprecisionSubstitutionᵀ)
open import proof.DGG.TransportTermImprecisionDef using
  (TransportTermImprecisionᵀ)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  ( MultiWorldEvolution
  ; evolutions-refl
  ; evolutions-step-left
  ; evolutions-step-right
  ; evolutions-step-both
  ; composeMultiWorldEvolution
  ; multi-no-open-frames
  ; multi-⊑ᵀ
  ; multi-target-reveal
  ; multi-target-conceal
  ; multi-target-reveal-position
  ; multi-target-conceal-position
  )
open import proof.Reduction
import proof.Imprecision as PI


private
  targetFunctionLayers : ∀ {Δ} → Term Δ → Nat.ℕ
  targetFunctionLayers (` x) = Nat.zero
  targetFunctionLayers (ƛ M) = Nat.zero
  targetFunctionLayers (L · M) = Nat.zero
  targetFunctionLayers (Λ V) = Nat.zero
  targetFunctionLayers (M ⦂∀ C [ A ]) = Nat.zero
  targetFunctionLayers ($ κ) = Nat.zero
  targetFunctionLayers (L ⊕[ op ] M) = Nat.zero
  targetFunctionLayers (M ⟨ c ⟩) = Nat.suc (targetFunctionLayers M)
  targetFunctionLayers (M ↑ c) = Nat.suc (targetFunctionLayers M)
  targetFunctionLayers (M ↓ c) = Nat.suc (targetFunctionLayers M)
  targetFunctionLayers blame = Nat.zero

  targetFunctionLayers-rename : ∀ {Δ Δ′}
      (ρ : Δ ↪ᵗ Δ′) (M : Term Δ)
    → targetFunctionLayers (renameᵗᵐ ρ M) ≡ targetFunctionLayers M
  targetFunctionLayers-rename ρ (` x) = refl
  targetFunctionLayers-rename ρ (ƛ M) = refl
  targetFunctionLayers-rename ρ (L · M) = refl
  targetFunctionLayers-rename ρ (Λ V) = refl
  targetFunctionLayers-rename ρ (M ⦂∀ C [ A ]) = refl
  targetFunctionLayers-rename ρ ($ κ) = refl
  targetFunctionLayers-rename ρ (L ⊕[ op ] M) = refl
  targetFunctionLayers-rename ρ (M ⟨ c ⟩) =
    cong Nat.suc (targetFunctionLayers-rename ρ M)
  targetFunctionLayers-rename ρ (M ↑ c) =
    cong Nat.suc (targetFunctionLayers-rename ρ M)
  targetFunctionLayers-rename ρ (M ↓ c) =
    cong Nat.suc (targetFunctionLayers-rename ρ M)
  targetFunctionLayers-rename ρ blame = refl

  targetFunctionLayers-applyTerms : ∀ {Δ Δ′}
      (χs : StoreChanges Δ Δ′) (M : Term Δ)
    → targetFunctionLayers (applyTerms χs M) ≡ targetFunctionLayers M
  targetFunctionLayers-applyTerms [] M = refl
  targetFunctionLayers-applyTerms (keep ∷ χs) M =
    targetFunctionLayers-applyTerms χs M
  targetFunctionLayers-applyTerms (bind A ∷ χs) M =
    trans
      (targetFunctionLayers-applyTerms χs (renameᵗᵐ wk↪ᵗ M))
      (targetFunctionLayers-rename wk↪ᵗ M)

  type-application-not-value : ∀ {Δ C A} {M : Term Δ}
    → Value (M ⦂∀ C [ A ])
    → ⊥
  type-application-not-value ()


module _
    (transport-CTI : TransportTermImprecisionᵀ)
    (catchup-to-more-precise : CatchupToMorePrecise)
    (term-imprecision-substitution : TermImprecisionSubstitutionᵀ)
    (sim-target-reveal-rebase-closing :
      SimTargetRevealRebaseClosingᵀ)
  where

  generator-here≠absent : generator-here ≢ generator-absent
  generator-here≠absent ()

  generator-left≠absent : ∀ {position : GeneratorPosition}
    → generator-⇒-left position ≢ generator-absent
  generator-left≠absent ()

  generator-right≠absent : ∀ {position : GeneratorPosition}
    → generator-⇒-right position ≢ generator-absent
  generator-right≠absent ()

  generator-both≠absent : ∀ {left right : GeneratorPosition}
    → generator-⇒-both left right ≢ generator-absent
  generator-both≠absent ()

  generator-all≠absent : ∀ {position : GeneratorPosition}
    → generator-∀ position ≢ generator-absent
  generator-all≠absent ()

  source-reveal-one-sided : ∀ {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {M : Term Δᴸ} {M′ : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {c : Conv.Conv↑ Δᴸ A A′}
    → (c⊢ : Σᴸ Conv.⊢↑[ X ⦂ R ] c)
    → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) X) ≡ X⊑★ᵐ
    → (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y
        ≢ toRenameⁱ (ηᴸᶜ γ) X)
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
        (λ absent → generator-here≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-left position =
      reveal⊑-only² c⊢
        (λ absent → generator-left≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-right position =
      reveal⊑-only² c⊢
        (λ absent → generator-right≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-both left right =
      reveal⊑-only² c⊢
        (λ absent → generator-both≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-reveal-one-sided c⊢ marked unoccupied represented rel q
    | generator-∀ position =
      reveal⊑-only² c⊢
        (λ absent → generator-all≠absent
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
    → (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y
        ≢ toRenameⁱ (ηᴸᶜ γ) X)
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
        (λ absent → generator-here≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-left position =
      conceal⊑-only² c⊢
        (λ absent → generator-left≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-right position =
      conceal⊑-only² c⊢
        (λ absent → generator-right≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-⇒-both left right =
      conceal⊑-only² c⊢
        (λ absent → generator-both≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q
  source-conceal-one-sided c⊢ marked unoccupied represented rel q
    | generator-∀ position =
      conceal⊑-only² c⊢
        (λ absent → generator-all≠absent
          (trans (sym position-eq) absent))
        marked unoccupied represented rel q

  worker : ∀ {Δᴸ Δᴿ : TyCtx}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {γ : ⟨ Δᴸ , Σᴸ , [] ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , [] ⟩}
      {V W N : Term Δᴸ} {V′ W′ : Term Δᴿ}
      {C : Ty Δᴸ} {C′ : Ty Δᴿ}
      {A B : Ty Δᴸ} {A′ B′ : Ty Δᴿ}
      {p : C ⊑ᵀ⟨ γ ⟩ C′}
      {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pB : B ⊑ᵀ⟨ γ ⟩ B′}
    → openFramesᶜ γ ≡ []
    → (fuel : Nat.ℕ)
    → targetFunctionLayers V′ < fuel
    → Value V
    → Value W
    → V · W —→ N
    → C ≡ (A ⇒ B)
    → C′ ≡ (A′ ⇒ B′)
    → γ ⊢² V ⊑ V′ ∶ p
    → γ ⊢² W ⊑ W′ ∶ pA
    → Value V′
    → Value W′
    → Σ[ Δᴿ′ ∈ TyCtx ]
      Σ[ Σᴿ′ ∈ TyStore Δᴿ′ ]
      Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
      Σ[ γ′ ∈
        ⟨ Δᴸ , applyStore keep Σᴸ , [] ⟩ ⊑ᶜ
        ⟨ Δᴿ′ , Σᴿ′ , [] ⟩ ]
      Σ[ q ∈ applyTy keep B ⊑ᵀ⟨ γ′ ⟩ applyTys χsᴿ B′ ]
        (V′ · W′ —↠[ χsᴿ ] N′)
        × MultiWorldEvolution
            {W = γ} {W′ = γ′} (keep ∷ []) χsᴿ
        × (γ′ ⊢² N ⊑ N′ ∶ q)

  worker no-rebase Nat.zero ()

  worker no-rebase (Nat.suc fuel) size-bound
      source-fun-value source-arg-value source-step
      source-arrow target-arrow
      (•⊑² p∀ related argument-rel result-rel)
      arg-rel target-fun-value target-arg-value =
    ⊥-elim (type-application-not-value source-fun-value)

  worker no-rebase (Nat.suc fuel) size-bound
      source-fun-value source-arg-value source-step refl refl
      (⊑conceal-rebase² c′⊢ rebase related q)
      arg-rel target-fun-value target-arg-value =
    ⊥-elim (open-source-rebase-nonempty rebase no-rebase)

  worker {V = M ⦂∀ C [ A ]}
      no-rebase (Nat.suc fuel) size-bound
      source-fun-value source-arg-value source-step
      source-arrow target-arrow fun-rel arg-rel
      target-fun-value target-arg-value =
    ⊥-elim (type-application-not-value source-fun-value)

  worker {V = Λ V} {W = blame}
      no-rebase (Nat.suc fuel) size-bound
      source-fun-value ()

  worker {V = $ κ} {W = blame}
      no-rebase (Nat.suc fuel) size-bound
      source-fun-value ()

  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value
      source-step
      refl refl
      (⊑cast² {M′ = M′}
        {p = inner-function-rel}
        (target-domain-cast ↦ target-result-cast) body-rel q)
      arg-rel
      (target-body-value 《 fun 》) target-arg-value
      with inner-function-rel
  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value
      source-step
      refl refl
      (⊑cast² {M′ = M′}
        {p = inner-function-rel}
        (target-domain-cast ↦ target-result-cast) body-rel q)
      arg-rel
      (target-body-value 《 fun 》) target-arg-value
    | ⇒⊑⇒ inner-argument-rel inner-result-rel
      with catchup-to-more-precise no-rebase
        (⊑cast² target-domain-cast arg-rel inner-argument-rel)
        source-arg-value
  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value
      source-step
      refl refl
      (⊑cast² {M′ = M′}
        {p = inner-function-rel}
        (target-domain-cast ↦ target-result-cast) body-rel q)
      arg-rel
      (target-body-value 《 fun 》) target-arg-value
    | ⇒⊑⇒ inner-argument-rel inner-result-rel
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
      with subst
        (λ T →
          Σ[ r ∈ ( _ ⇒ _ ) ⊑ᵀ⟨ argument-world ⟩ T ]
            argument-world ⊢² V ⊑ applyTerms argument-changes M′ ∶ r)
        (applyTys-⇒ argument-changes _ _)
        (multi-⊑ᵀ argument-evolution
            (⇒⊑⇒ inner-argument-rel inner-result-rel) ,
          transport-CTI argument-evolution body-rel)
  worker {V = V} {W = W} {N = N} {W′ = W′}
      {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value
      source-step
      refl refl
      (⊑cast² {M′ = M′}
        {p = inner-function-rel}
        (target-domain-cast ↦ target-result-cast) body-rel q)
      arg-rel
      (target-body-value 《 fun 》) target-arg-value
    | ⇒⊑⇒ inner-argument-rel inner-result-rel
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
    | (⇒⊑⇒ argument-type-rel′ result-type-rel) , body-rel′
      with worker
        {pA = argument-type-rel′} {pB = result-type-rel}
        (multi-no-open-frames argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (targetFunctionLayers-applyTerms argument-changes M′))
          smaller)
        source-fun-value source-arg-value
        source-step
        refl refl
        body-rel′
        (subst (λ r → argument-world ⊢² W ⊑ target-argument ∶ r)
          (PI.⊑-unique argument-type-rel argument-type-rel′)
          argument-rel)
        (applyTerms-preserves-Value argument-changes target-body-value)
        target-argument-value
  worker {V = V} {W = W} {N = N} {W′ = W′}
      {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value
      source-step
      refl refl
      (⊑cast² {M′ = M′}
        {p = inner-function-rel}
        (target-domain-cast ↦ target-result-cast) body-rel q)
      arg-rel
      (target-body-value 《 fun 》) target-arg-value
    | ⇒⊑⇒ inner-argument-rel inner-result-rel
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
    | (⇒⊑⇒ argument-type-rel′ result-type-rel) , body-rel′
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel′ , result-steps , result-evolution , result-rel =
    let normalized-result =
          subst
            (λ T →
              Σ[ r ∈ applyTy keep B ⊑ᵀ⟨ result-world ⟩ T ]
                result-world ⊢² N ⊑ result ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel′ , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          evolutions-step-right refl evolution-keep payload-evolution
    in
      result-Δ , result-store ,
      keep ∷ (argument-changes ++χ result-changes) ,
      result ⟨ applyConsistencies
        (argument-changes ++χ result-changes) target-result-cast ⟩ ,
      result-world , multi-⊑ᵀ total-evolution pB ,
      subst
        (λ final →
          (M′ ⟨ target-domain-cast ↦ target-result-cast ⟩) · W′
            —↠[
              keep ∷ (argument-changes ++χ result-changes)
            ] final)
        (cast-applyConsistencies-++ argument-changes result-changes
          target-result-cast result)
        (((M′ ⟨ target-domain-cast ↦ target-result-cast ⟩) · W′
          —→[ keep ]⟨ pure-step
            (β-⇒ target-body-value target-arg-value) ⟩
         (M′ · (W′ ⟨ target-domain-cast ⟩)) ⟨ target-result-cast ⟩
          —↠+[ argument-changes ]⟨
            cast-↠ target-result-cast
              (appR-↠ target-body-value argument-steps) ⟩
         (applyTerms argument-changes M′ · target-argument)
           ⟨ applyConsistencies argument-changes target-result-cast ⟩
          —↠[ result-changes ]⟨
            cast-↠
              (applyConsistencies argument-changes target-result-cast)
              result-steps ⟩
         result ⟨ applyConsistencies result-changes
           (applyConsistencies argument-changes
             target-result-cast) ⟩ ∎[])) ,
      total-evolution ,
      ⊑cast²
        (applyConsistencies
          (argument-changes ++χ result-changes) target-result-cast)
        (proj₂ normalized-result)
        (multi-⊑ᵀ total-evolution pB)

  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑reveal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value
      with catchup-to-more-precise no-rebase
        (⊑conceal-identity target-domain⊢
          (joinGeneratorPositions-absent-left absent)
          arg-rel inner-argument-rel)
        source-arg-value
  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑reveal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
      with subst
        (λ T →
          Σ[ r ∈ (_ ⇒ _) ⊑ᵀ⟨ argument-world ⟩ T ]
            argument-world ⊢² V ⊑ applyTerms argument-changes M′ ∶ r)
        (applyTys-⇒ argument-changes _ _)
        (multi-⊑ᵀ argument-evolution
            (⇒⊑⇒ inner-argument-rel inner-result-rel) ,
          transport-CTI argument-evolution body-rel)
  worker {V = V} {W = W} {N = N} {W′ = W′}
      {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑reveal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
    | (⇒⊑⇒ argument-type-rel′ result-type-rel) , body-rel′
      with worker
        {pA = argument-type-rel′} {pB = result-type-rel}
        (multi-no-open-frames argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (targetFunctionLayers-applyTerms argument-changes M′))
          smaller)
        source-fun-value source-arg-value source-step
        refl refl body-rel′
        (subst (λ r → argument-world ⊢² W ⊑ target-argument ∶ r)
          (PI.⊑-unique argument-type-rel argument-type-rel′)
          argument-rel)
        (applyTerms-preserves-Value argument-changes target-body-value)
        target-argument-value
  worker {V = V} {W = W} {N = N} {W′ = W′}
      {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑reveal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
    | (⇒⊑⇒ argument-type-rel′ result-type-rel) , body-rel′
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel′ , result-steps , result-evolution , result-rel =
    let normalized-result =
          subst
            (λ T →
              Σ[ r ∈ applyTy keep B ⊑ᵀ⟨ result-world ⟩ T ]
                result-world ⊢² N ⊑ result ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel′ , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          evolutions-step-right refl evolution-keep payload-evolution
    in
      result-Δ , result-store ,
      keep ∷ (argument-changes ++χ result-changes) ,
      result ↑ applyReveals
        (argument-changes ++χ result-changes) target-result-conversion ,
      result-world , multi-⊑ᵀ total-evolution pB ,
      subst
        (λ final →
          ((M′ ↑
            (target-domain-conversion Conv.↦↑
              target-result-conversion)) · W′)
            —↠[
              keep ∷ (argument-changes ++χ result-changes)
            ] final)
        (reveal-applyReveals-++ argument-changes result-changes
          target-result-conversion result)
        ((((M′ ↑
            (target-domain-conversion Conv.↦↑
              target-result-conversion)) · W′)
          —→[ keep ]⟨ pure-step
            (β-reveal-⇒ target-body-value target-arg-value) ⟩
         (M′ · (W′ ↓ target-domain-conversion))
           ↑ target-result-conversion
          —↠+[ argument-changes ]⟨
            reveal-↠ target-result-conversion
              (appR-↠ target-body-value argument-steps) ⟩
         (applyTerms argument-changes M′ · target-argument)
           ↑ applyReveals argument-changes target-result-conversion
          —↠[ result-changes ]⟨
            reveal-↠
              (applyReveals argument-changes target-result-conversion)
              result-steps ⟩
         result ↑ applyReveals result-changes
           (applyReveals argument-changes
             target-result-conversion) ∎[])) ,
      total-evolution ,
      ⊑reveal-identity
        (multi-target-reveal payload-evolution target-result⊢)
        (trans
          (multi-target-reveal-position payload-evolution target-result⊢)
          (joinGeneratorPositions-absent-right absent))
        (proj₂ normalized-result)
        (multi-⊑ᵀ total-evolution pB)

  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑conceal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↓ fun) target-arg-value
      with catchup-to-more-precise no-rebase
        (⊑reveal-identity target-domain⊢
          (joinGeneratorPositions-absent-left absent)
          arg-rel inner-argument-rel)
        source-arg-value
  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑conceal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↓ fun) target-arg-value
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
      with subst
        (λ T →
          Σ[ r ∈ (_ ⇒ _) ⊑ᵀ⟨ argument-world ⟩ T ]
            argument-world ⊢² V ⊑ applyTerms argument-changes M′ ∶ r)
        (applyTys-⇒ argument-changes _ _)
        (multi-⊑ᵀ argument-evolution
            (⇒⊑⇒ inner-argument-rel inner-result-rel) ,
          transport-CTI argument-evolution body-rel)
  worker {V = V} {W = W} {N = N} {W′ = W′}
      {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑conceal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↓ fun) target-arg-value
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
    | (⇒⊑⇒ argument-type-rel′ result-type-rel) , body-rel′
      with worker
        {pA = argument-type-rel′} {pB = result-type-rel}
        (multi-no-open-frames argument-evolution no-rebase)
        fuel
        (subst (λ n → n < fuel)
          (sym (targetFunctionLayers-applyTerms argument-changes M′))
          smaller)
        source-fun-value source-arg-value source-step
        refl refl body-rel′
        (subst (λ r → argument-world ⊢² W ⊑ target-argument ∶ r)
          (PI.⊑-unique argument-type-rel argument-type-rel′)
          argument-rel)
        (applyTerms-preserves-Value argument-changes target-body-value)
        target-argument-value
  worker {V = V} {W = W} {N = N} {W′ = W′}
      {B = B} {pB = pB}
      no-rebase (Nat.suc fuel) (s≤s smaller)
      source-fun-value source-arg-value source-step
      refl refl
      (⊑conceal-identity {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        absent body-rel q)
      arg-rel (target-body-value ↓ fun) target-arg-value
    | argument-Δ , argument-store , argument-changes , target-argument ,
      argument-world , argument-type-rel , argument-steps ,
      target-argument-value , argument-evolution , argument-rel
    | (⇒⊑⇒ argument-type-rel′ result-type-rel) , body-rel′
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel′ , result-steps , result-evolution , result-rel =
    let normalized-result =
          subst
            (λ T →
              Σ[ r ∈ applyTy keep B ⊑ᵀ⟨ result-world ⟩ T ]
                result-world ⊢² N ⊑ result ∶ r)
            (applyTys-++ argument-changes result-changes _)
            (result-type-rel′ , result-rel)
        payload-evolution =
          composeMultiWorldEvolution argument-evolution result-evolution
        total-evolution =
          evolutions-step-right refl evolution-keep payload-evolution
    in
      result-Δ , result-store ,
      keep ∷ (argument-changes ++χ result-changes) ,
      result ↓ applyConceals
        (argument-changes ++χ result-changes) target-result-conversion ,
      result-world , multi-⊑ᵀ total-evolution pB ,
      subst
        (λ final →
          ((M′ ↓
            (target-domain-conversion Conv.↦↓
              target-result-conversion)) · W′)
            —↠[
              keep ∷ (argument-changes ++χ result-changes)
            ] final)
        (conceal-applyConceals-++ argument-changes result-changes
          target-result-conversion result)
        ((((M′ ↓
            (target-domain-conversion Conv.↦↓
              target-result-conversion)) · W′)
          —→[ keep ]⟨ pure-step
            (β-conceal-⇒ target-body-value target-arg-value) ⟩
         (M′ · (W′ ↑ target-domain-conversion))
           ↓ target-result-conversion
          —↠+[ argument-changes ]⟨
            conceal-↠ target-result-conversion
              (appR-↠ target-body-value argument-steps) ⟩
         (applyTerms argument-changes M′ · target-argument)
           ↓ applyConceals argument-changes target-result-conversion
          —↠[ result-changes ]⟨
            conceal-↠
              (applyConceals argument-changes target-result-conversion)
              result-steps ⟩
         result ↓ applyConceals result-changes
           (applyConceals argument-changes
             target-result-conversion) ∎[])) ,
      total-evolution ,
      ⊑conceal-identity
        (multi-target-conceal payload-evolution target-result⊢)
        (trans
          (multi-target-conceal-position payload-evolution target-result⊢)
          (joinGeneratorPositions-absent-right absent))
        (proj₂ normalized-result)
        (multi-⊑ᵀ total-evolution pB)

  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) size-bound
      source-fun-value source-arg-value source-step
      refl refl
      (⊑reveal-rebase² {M′ = M′}
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        rebase
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value
      with sim-target-reveal-rebase-closing no-rebase
        target-result⊢ rebase
        (·⊑·² body-rel
          (⊑conceal-rebase² target-domain⊢ rebase
            arg-rel inner-argument-rel))
        pB (pure-step source-step)
  worker {V = V} {W = W} {N = N} {W′ = W′} {pB = pB}
      no-rebase (Nat.suc fuel) size-bound
      source-fun-value source-arg-value source-step
      refl refl
      (⊑reveal-rebase² {M′ = M′}
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        rebase
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value
    | result-Δ , result-store , result-changes , result , result-world ,
      result-type-rel , result-steps , result-evolution , result-rel =
    let total-evolution =
          evolutions-step-right refl evolution-keep result-evolution
    in
      result-Δ , result-store , keep ∷ result-changes , result ,
      result-world , result-type-rel ,
      ((M′ ↑
          (target-domain-conversion Conv.↦↑
            target-result-conversion)) · W′
        —→[ keep ]⟨ pure-step
          (β-reveal-⇒ target-body-value target-arg-value) ⟩
       (M′ · (W′ ↓ target-domain-conversion))
         ↑ target-result-conversion
        —↠[ result-changes ]⟨ result-steps ⟩
       result ∎[]) ,
      total-evolution , result-rel

  worker {Σᴿ = Σᴿ} {W = W} {W′ = W′}
      {pA = pA} {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      source-fun-value source-arg-value
      (β root-arg-value)
      refl refl
      (ƛ⊑ƛ² {M = M} {M′ = M′} {pA = pA₁} {pB = pB₁} body-rel)
      arg-rel target-fun-value target-arg-value
      rewrite PI.⊑-unique pA₁ pA | PI.⊑-unique pB₁ pB =
    _ , Σᴿ , (keep ∷ []) , M′ [ W′ ] , _ , pB ,
    (((ƛ M′) · W′
      —→[ keep ]⟨ pure-step (β target-arg-value) ⟩
     M′ [ W′ ] ∎[])) ,
    evolutions-step-both refl refl evolution-keep evolutions-refl ,
    term-imprecision-substitution arg-rel body-rel

  worker {Σᴿ = Σᴿ} {W = W} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value 《 fun 》) source-arg-value
      (β-⇒ root-fun-value root-arg-value)
      refl refl
      (cast⊑cast² {M = M} {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast)
        (target-domain-cast ↦ target-result-cast) body-rel q)
      arg-rel (target-body-value 《 fun 》) target-arg-value =
    _ , Σᴿ , (keep ∷ []) ,
    (M′ · (W′ ⟨ target-domain-cast ⟩)) ⟨ target-result-cast ⟩ ,
    _ , pB ,
    ((((M′ ⟨ target-domain-cast ↦ target-result-cast ⟩) · W′)
      —→[ keep ]⟨ pure-step
        (β-⇒ target-body-value target-arg-value) ⟩
     (M′ · (W′ ⟨ target-domain-cast ⟩))
       ⟨ target-result-cast ⟩ ∎[])) ,
    evolutions-step-both refl refl evolution-keep evolutions-refl ,
    cast⊑cast² source-result-cast target-result-cast
      (·⊑·² body-rel
        (cast⊑cast² source-domain-cast target-domain-cast
          arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {V′ = V′} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value 《 fun 》) source-arg-value
      (β-⇒ root-fun-value root-arg-value)
      refl refl
      (cast⊑² {M = M}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (source-domain-cast ↦ source-result-cast) body-rel q)
      arg-rel target-fun-value target-arg-value =
    _ , Σᴿ , [] , V′ · W′ , _ , pB ,
    (V′ · W′ ∎[]) ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    cast⊑² source-result-cast
      (·⊑·² body-rel
        (cast⊑² source-domain-cast arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {V′ = V′} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value ↑ fun) source-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value)
      refl refl
      (reveal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ source-domain⊢ source-result⊢) absent
        body-rel q)
      arg-rel target-fun-value target-arg-value =
    _ , Σᴿ , [] , V′ · W′ , _ , pB ,
    (V′ · W′ ∎[]) ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    reveal⊑-identity source-result⊢
      (joinGeneratorPositions-absent-right absent)
      (·⊑·² body-rel
        (conceal⊑-identity source-domain⊢
          (joinGeneratorPositions-absent-left absent)
          arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {V′ = V′} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value ↑ fun) source-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value)
      refl refl
      (reveal⊑-only² {Rᴸ = Rᴸ}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↑-⇒ source-domain⊢ source-result⊢)
        present marked unoccupied represented body-rel q)
      arg-rel target-fun-value target-arg-value =
    _ , Σᴿ , [] , V′ · W′ , _ , pB ,
    (V′ · W′ ∎[]) ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    source-reveal-one-sided source-result⊢ marked unoccupied represented
      (·⊑·² body-rel
        (source-conceal-one-sided source-domain⊢ marked unoccupied
          represented arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value ↑ fun) source-arg-value
      (β-reveal-⇒ root-fun-value root-arg-value)
      refl refl
      (reveal⊑reveal² {M = M} {M′ = M′}
        (Conv.⊢↑-⇒ source-domain⊢ source-result⊢)
        (Conv.⊢↑-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        positions aligned represented
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel} body-rel q)
      arg-rel (target-body-value ↑ fun) target-arg-value =
    _ , Σᴿ , (keep ∷ []) ,
    (M′ · (W′ ↓ target-domain-conversion))
      ↑ target-result-conversion , _ , pB ,
    ((((M′ ↑ (target-domain-conversion Conv.↦↑
          target-result-conversion)) · W′)
      —→[ keep ]⟨ pure-step
        (β-reveal-⇒ target-body-value target-arg-value) ⟩
     (M′ · (W′ ↓ target-domain-conversion))
       ↑ target-result-conversion ∎[])) ,
    evolutions-step-both refl refl evolution-keep evolutions-refl ,
    reveal⊑reveal² source-result⊢ target-result⊢
      (joinGeneratorPositions-equal-right positions)
      aligned represented
      (·⊑·² body-rel
        (conceal⊑conceal² source-domain⊢ target-domain⊢
          (joinGeneratorPositions-equal-left positions)
          aligned represented arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {V′ = V′} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value ↓ fun) source-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value)
      refl refl
      (conceal⊑-identity
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ source-domain⊢ source-result⊢) absent
        body-rel q)
      arg-rel target-fun-value target-arg-value =
    _ , Σᴿ , [] , V′ · W′ , _ , pB ,
    (V′ · W′ ∎[]) ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    conceal⊑-identity source-result⊢
      (joinGeneratorPositions-absent-right absent)
      (·⊑·² body-rel
        (reveal⊑-identity source-domain⊢
          (joinGeneratorPositions-absent-left absent)
          arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {V′ = V′} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value ↓ fun) source-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value)
      refl refl
      (conceal⊑-only² {Rᴸ = Rᴸ}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ source-domain⊢ source-result⊢)
        present marked unoccupied represented body-rel q)
      arg-rel target-fun-value target-arg-value =
    _ , Σᴿ , [] , V′ · W′ , _ , pB ,
    (V′ · W′ ∎[]) ,
    evolutions-step-left refl evolution-keep evolutions-refl ,
    source-conceal-one-sided source-result⊢ marked unoccupied represented
      (·⊑·² body-rel
        (source-reveal-one-sided source-domain⊢ marked unoccupied
          represented arg-rel inner-argument-rel))
      pB

  worker {Σᴿ = Σᴿ} {W = W} {W′ = W′}
      {pB = pB} no-rebase
      (Nat.suc fuel) size-bound
      (source-body-value ↓ fun) source-arg-value
      (β-conceal-⇒ root-fun-value root-arg-value)
      refl refl
      (conceal⊑conceal² {M = M} {M′ = M′}
        {p = ⇒⊑⇒ inner-argument-rel inner-result-rel}
        (Conv.⊢↓-⇒ source-domain⊢ source-result⊢)
        (Conv.⊢↓-⇒ {c = target-domain-conversion}
          {d = target-result-conversion} target-domain⊢ target-result⊢)
        positions aligned represented body-rel q)
      arg-rel (target-body-value ↓ fun) target-arg-value =
    _ , Σᴿ , (keep ∷ []) ,
    (M′ · (W′ ↑ target-domain-conversion))
      ↓ target-result-conversion , _ , pB ,
    ((((M′ ↓ (target-domain-conversion Conv.↦↓
          target-result-conversion)) · W′)
      —→[ keep ]⟨ pure-step
        (β-conceal-⇒ target-body-value target-arg-value) ⟩
     (M′ · (W′ ↑ target-domain-conversion))
       ↓ target-result-conversion ∎[])) ,
    evolutions-step-both refl refl evolution-keep evolutions-refl ,
    conceal⊑conceal² source-result⊢ target-result⊢
      (joinGeneratorPositions-equal-right positions)
      aligned represented
      (·⊑·² body-rel
        (reveal⊑reveal² source-domain⊢ target-domain⊢
          (joinGeneratorPositions-equal-left positions)
          aligned represented arg-rel inner-argument-rel))
      pB

  sim-paired-fun-values : SimPairedFunValuesᵀ
  sim-paired-fun-values {V′ = V′}
      {A = A} {B = B} {A′ = A′} {B′ = B′}
      {pA = pA} {pB = pB}
      no-rebase fun-rel arg-rel
      source-fun-value source-arg-value
      target-fun-value target-arg-value source-step =
    worker {C = A ⇒ B} {C′ = A′ ⇒ B′}
      {A = A} {B = B} {A′ = A′} {B′ = B′}
      {p = ⇒⊑⇒ pA pB} {pA = pA} {pB = pB}
      no-rebase
      (Nat.suc (targetFunctionLayers V′))
      (n<1+n (targetFunctionLayers V′))
      source-fun-value source-arg-value source-step
      refl refl fun-rel arg-rel target-fun-value target-arg-value

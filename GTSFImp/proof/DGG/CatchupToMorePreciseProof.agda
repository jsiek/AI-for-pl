{-# OPTIONS --safe #-}

module proof.DGG.CatchupToMorePreciseProof where

-- File Charter:
--   * Develops CatchupToMorePrecise by direct induction on current CTI.
--   * Covers the complete primary case split, with every recursive case
--     structured around its induction hypothesis.
--   * Is parameterized only by separately named semantic inductions.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym; trans)

import CastTerms as CT
open import CastTerms using (Ctx; Term; Value; _⟨_⟩; _《_》; _↑_; _↓_)
open import Types using (Ty)
open import Reduction using
  ([]; ↠-refl; applyConsistencies; _—↠[_]⟨_⟩_; _∎[])
open import proof.Reduction using
  ( _++χ_; _—↠+[_]⟨_⟩_; applyTys-++; applyTys-★; cast-↠
  ; applyReveals; applyConceals; reveal-↠; conceal-↠
  )
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.Catchup.MorePreciseTargetIdentityConversionLemma
  using
    ( target-identity-reveal-catchup
    ; target-identity-conceal-catchup
    )
open import proof.DGG.Catchup.MorePrecisePairedConversionValueLemma
  using
    ( paired-reveal-value-catchup
    ; paired-conceal-value-catchup
    )
open import proof.DGG.Catchup.MorePreciseTargetCastValueCatchupDef
  using (MorePreciseTargetCastValueCatchupᵀ)
open import proof.DGG.Catchup.MorePreciseSourceLambdaClosingDef
  using (MorePreciseSourceLambdaClosingᵀ)
open import proof.DGG.Catchup.MorePreciseTargetRevealRebaseCatchupDef
  using (MorePreciseTargetRevealRebaseCatchupᵀ)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupToMorePrecise)
open import proof.DGG.SourceRebase using (open-source-rebase-frames)
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; renameOpenFrames-empty)
open import proof.DGG.WorldEvolutionSequence using
  ( evolutions-refl
  ; composeMultiWorldEvolution
  ; multi-no-open-frames
  ; multi-aligned
  ; multi-⊑ᵀ
  ; multi-source-reveal
  ; multi-source-conceal
  ; multi-source-reveal-position
  ; multi-source-conceal-position
  ; multi-source-mark
  ; multi-source-disaligned
  ; multi-target-reveal
  ; multi-target-conceal
  ; multi-target-reveal-position
  ; multi-target-conceal-position
  )
transport-target-type-and-relation : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {V : Term (CT.Δᵉ Γᴸ)}
    {V′ : Term (CT.Δᵉ Γᴿ)} {A : Ty (CT.Δᵉ Γᴸ)}
    {B B′ : Ty (CT.Δᵉ Γᴿ)}
  → B ≡ B′
  → Σ[ p ∈ A ⊑ᵀ⟨ γ ⟩ B ] (γ CTI.⊢² V ⊑ V′ ∶ p)
  → Σ[ q ∈ A ⊑ᵀ⟨ γ ⟩ B′ ] (γ CTI.⊢² V ⊑ V′ ∶ q)
transport-target-type-and-relation refl related = related


module _
    (target-reveal-rebase-catchup :
      MorePreciseTargetRevealRebaseCatchupᵀ)
    (target-cast-value-catchup :
      MorePreciseTargetCastValueCatchupᵀ)
    (source-lambda-closing :
      MorePreciseSourceLambdaClosingᵀ)
  where

  catchup-to-more-precise : CatchupToMorePrecise
  catchup-to-more-precise no-rebase (CTI.x⊑x² _ _) ()

  catchup-to-more-precise {γ = γ} {M′ = M′} {p = p} no-rebase
      rel@(CTI.ƛ⊑ƛ² prem) (CT.ƛ _) =
    _ , _ , [] , M′ , γ , p , ↠-refl , CT.ƛ _ ,
      evolutions-refl , rel

  catchup-to-more-precise no-rebase (CTI.·⊑·² prem₁ prem₂) ()

  catchup-to-more-precise {γ = γ} {M′ = M′} {p = p} no-rebase
      rel@(CTI.Λ⊑Λ² vV vV′ prem q) (CT.Λ source-value) =
    _ , _ , [] , M′ , γ , p , ↠-refl , CT.Λ vV′ ,
      evolutions-refl , rel

  catchup-to-more-precise no-rebase
      (CTI.Λ⊑² Anv zero∈A vV target⊢ prem q) (CT.Λ source-value)
      with catchup-to-more-precise
        (renameOpenFrames-empty no-rebase) prem vV
  catchup-to-more-precise no-rebase
      (CTI.Λ⊑² Anv zero∈A vV target⊢ prem q) (CT.Λ source-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γᵇ , r , M′↠V′ , vV′ , evolᵇ ,
      related
      with source-lambda-closing no-rebase Anv zero∈A vV evolᵇ related q
  catchup-to-more-precise no-rebase
      (CTI.Λ⊑² Anv zero∈A vV target⊢ prem q) (CT.Λ source-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γᵇ , r , M′↠V′ , vV′ , evolᵇ ,
      related
    | γ′ , final-q , evol , final-related =
    Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , final-q , M′↠V′ , vV′ ,
      evol , final-related

  catchup-to-more-precise no-rebase
      (CTI.•⊑•² p∀ prem q r) ()

  catchup-to-more-precise no-rebase
      (CTI.•⊑² p∀ prem q r) ()

  catchup-to-more-precise {γ = γ} {M′ = M′} {p = p} no-rebase
      rel@(CTI.κ⊑κ² κ q) (CT.$ .κ) =
    _ , _ , [] , M′ , γ , p , ↠-refl , CT.$ κ ,
      evolutions-refl , rel

  catchup-to-more-precise no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      source-value@(vV CT.《 inert 》)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      source-value@(vV CT.《 inert 》)
    | Δᴿ¹ , Σᴿ¹ , χsᴿ , V′ , γ¹ , r , M′↠V′ , vV′ , evol¹ ,
      related
      with target-cast-value-catchup
        (multi-no-open-frames evol¹ no-rebase)
        (CTI.cast⊑cast² c (applyConsistencies χsᴿ c′) related
          (multi-⊑ᵀ evol¹ q))
        source-value vV′
  catchup-to-more-precise no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      source-value@(vV CT.《 inert 》)
    | Δᴿ¹ , Σᴿ¹ , χsᴿ , V′ , γ¹ , r , M′↠V′ , vV′ , evol¹ ,
      related
    | Δᴿ² , Σᴿ² , ψsᴿ , W′ , γ² , s , cast↠W′ , vW′ , evol² ,
      final-related
      with transport-target-type-and-relation
        (applyTys-++ χsᴿ ψsᴿ _)
        (s , final-related)
  catchup-to-more-precise no-rebase
      (CTI.cast⊑cast² {M′ = M′} c c′ prem q)
      source-value@(vV CT.《 inert 》)
    | Δᴿ¹ , Σᴿ¹ , χsᴿ , V′ , γ¹ , r , M′↠V′ , vV′ , evol¹ ,
      related
    | Δᴿ² , Σᴿ² , ψsᴿ , W′ , γ² , s , cast↠W′ , vW′ , evol² ,
      final-related
    | final-q , final-related′ =
    Δᴿ² , Σᴿ² , χsᴿ ++χ ψsᴿ , W′ , γ² , final-q ,
      (M′ ⟨ c′ ⟩
        —↠+[ χsᴿ ]⟨ cast-↠ {M = M′} c′ M′↠V′ ⟩
       V′ ⟨ applyConsistencies χsᴿ c′ ⟩
        —↠[ ψsᴿ ]⟨ cast↠W′ ⟩
       W′ ∎[]) , vW′ ,
      composeMultiWorldEvolution evol¹ evol² , final-related′

  catchup-to-more-precise no-rebase
      (CTI.⊑cast² {M′ = M′} c′ prem q) vV
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.⊑cast² {M′ = M′} c′ prem q) vV
    | Δᴿ¹ , Σᴿ¹ , χsᴿ , V′ , γ¹ , r , M′↠V′ , vV′ , evol¹ ,
      related
      with target-cast-value-catchup
        (multi-no-open-frames evol¹ no-rebase)
        (CTI.⊑cast² (applyConsistencies χsᴿ c′) related
          (multi-⊑ᵀ evol¹ q))
        vV vV′
  catchup-to-more-precise no-rebase
      (CTI.⊑cast² {M′ = M′} c′ prem q) vV
    | Δᴿ¹ , Σᴿ¹ , χsᴿ , V′ , γ¹ , r , M′↠V′ , vV′ , evol¹ ,
      related
    | Δᴿ² , Σᴿ² , ψsᴿ , W′ , γ² , s , cast↠W′ , vW′ , evol² ,
      final-related
      with transport-target-type-and-relation
        (applyTys-++ χsᴿ ψsᴿ _)
        (s , final-related)
  catchup-to-more-precise no-rebase
      (CTI.⊑cast² {M′ = M′} c′ prem q) vV
    | Δᴿ¹ , Σᴿ¹ , χsᴿ , V′ , γ¹ , r , M′↠V′ , vV′ , evol¹ ,
      related
    | Δᴿ² , Σᴿ² , ψsᴿ , W′ , γ² , s , cast↠W′ , vW′ , evol² ,
      final-related
    | final-q , final-related′ =
    Δᴿ² , Σᴿ² , χsᴿ ++χ ψsᴿ , W′ , γ² , final-q ,
      (M′ ⟨ c′ ⟩
        —↠+[ χsᴿ ]⟨ cast-↠ {M = M′} c′ M′↠V′ ⟩
       V′ ⟨ applyConsistencies χsᴿ c′ ⟩
        —↠[ ψsᴿ ]⟨ cast↠W′ ⟩
       W′ ∎[]) , vW′ ,
      composeMultiWorldEvolution evol¹ evol² , final-related′

  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑reveal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑reveal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related
      with target-identity-reveal-catchup
        (multi-target-reveal evol c′⊢)
        (trans (multi-target-reveal-position evol c′⊢) absent)
        related (multi-⊑ᵀ evol q) vV′
  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑reveal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame↝W′ , vW′ , frame-evol , types-id ,
      frame-related
      with transport-target-type-and-relation
        (trans (sym (types-id _)) (applyTys-++ χsᴿ ψsᴿ _))
        (multi-⊑ᵀ evol q , frame-related)
  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑reveal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame↝W′ , vW′ , frame-evol , types-id ,
      frame-related
    | final-q , final-related =
    Δᴿ′ , Σᴿ′ , χsᴿ ++χ ψsᴿ , W′ , γ′ ,
      final-q ,
      (M′ ↑ c′
        —↠+[ χsᴿ ]⟨ reveal-↠ c′ M′↝V′ ⟩
       V′ ↑ applyReveals χsᴿ c′
        —↠[ ψsᴿ ]⟨ frame↝W′ ⟩
       W′ ∎[]) , vW′ ,
      composeMultiWorldEvolution evol frame-evol ,
      final-related

  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑conceal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑conceal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related
      with target-identity-conceal-catchup
        (multi-target-conceal evol c′⊢)
        (trans (multi-target-conceal-position evol c′⊢) absent)
        related (multi-⊑ᵀ evol q) vV′
  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑conceal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame↝W′ , vW′ , frame-evol , types-id ,
      frame-related
      with transport-target-type-and-relation
        (trans (sym (types-id _)) (applyTys-++ χsᴿ ψsᴿ _))
        (multi-⊑ᵀ evol q , frame-related)
  catchup-to-more-precise {V = V} no-rebase
      (CTI.⊑conceal-identity {M′ = M′} {c′ = c′}
        c′⊢ absent prem q) vV
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame↝W′ , vW′ , frame-evol , types-id ,
      frame-related
    | final-q , final-related =
    Δᴿ′ , Σᴿ′ , χsᴿ ++χ ψsᴿ , W′ , γ′ ,
      final-q ,
      (M′ ↓ c′
        —↠+[ χsᴿ ]⟨ conceal-↠ c′ M′↝V′ ⟩
       V′ ↓ applyConceals χsᴿ c′
        —↠[ ψsᴿ ]⟨ frame↝W′ ⟩
       W′ ∎[]) , vW′ ,
      composeMultiWorldEvolution evol frame-evol ,
      final-related

  catchup-to-more-precise no-rebase
      (CTI.cast⊑² c prem q) (vV CT.《 inert 》)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.cast⊑² c prem q) (vV CT.《 inert 》)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related =
    Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , multi-⊑ᵀ evol q ,
      M′↝V′ , vV′ , evol ,
      CTI.cast⊑² c related (multi-⊑ᵀ evol q)

  catchup-to-more-precise no-rebase
      (CTI.reveal⊑-identity c⊢ absent prem q) (vV CT.↑ reveal-value)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.reveal⊑-identity c⊢ absent prem q) (vV CT.↑ reveal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related =
    Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , multi-⊑ᵀ evol q ,
      M′↝V′ , vV′ , evol ,
      CTI.reveal⊑-identity (multi-source-reveal evol c⊢)
        (trans (multi-source-reveal-position evol c⊢) absent)
        related (multi-⊑ᵀ evol q)

  catchup-to-more-precise no-rebase
      (CTI.reveal⊑-only² c⊢ present mark free represented prem q)
      (vV CT.↑ reveal-value)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.reveal⊑-only² c⊢ present mark free represented prem q)
      (vV CT.↑ reveal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related =
    Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , multi-⊑ᵀ evol q ,
      M′↝V′ , vV′ , evol ,
      CTI.reveal⊑-only²
        (multi-source-reveal evol c⊢)
        (λ absent → present
          (trans (sym (multi-source-reveal-position evol c⊢)) absent))
        (multi-source-mark evol mark)
        (multi-source-disaligned evol free)
        (subst (λ T → _ ⊑ᵀ⟨ γ′ ⟩ T)
          (applyTys-★ χsᴿ) (multi-⊑ᵀ evol represented))
        related (multi-⊑ᵀ evol q)

  catchup-to-more-precise no-rebase
      (CTI.conceal⊑-identity c⊢ absent prem q) (vV CT.↓ conceal-value)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.conceal⊑-identity c⊢ absent prem q) (vV CT.↓ conceal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related =
    Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , multi-⊑ᵀ evol q ,
      M′↝V′ , vV′ , evol ,
      CTI.conceal⊑-identity (multi-source-conceal evol c⊢)
        (trans (multi-source-conceal-position evol c⊢) absent)
        related (multi-⊑ᵀ evol q)

  catchup-to-more-precise no-rebase
      (CTI.conceal⊑-only² c⊢ present mark free represented prem q)
      (vV CT.↓ conceal-value)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.conceal⊑-only² c⊢ present mark free represented prem q)
      (vV CT.↓ conceal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′↝V′ , vV′ , evol ,
      related =
    Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , multi-⊑ᵀ evol q ,
      M′↝V′ , vV′ , evol ,
      CTI.conceal⊑-only²
        (multi-source-conceal evol c⊢)
        (λ absent → present
          (trans (sym (multi-source-conceal-position evol c⊢)) absent))
        (multi-source-mark evol mark)
        (multi-source-disaligned evol free)
        (subst (λ T → _ ⊑ᵀ⟨ γ′ ⟩ T)
          (applyTys-★ χsᴿ) (multi-⊑ᵀ evol represented))
        related (multi-⊑ᵀ evol q)

  catchup-to-more-precise no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↑ reveal-value)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↑ reveal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′⇝V′ , vV′ , evol ,
      related
      with paired-reveal-value-catchup
        (multi-source-reveal evol c⊢)
        (multi-target-reveal evol c′⊢)
        (trans (multi-source-reveal-position evol c⊢)
          (trans positions
            (sym (multi-target-reveal-position evol c′⊢))))
        (multi-aligned evol aligned)
        (multi-⊑ᵀ evol represented)
        related (multi-⊑ᵀ evol q) reveal-value vV′
  catchup-to-more-precise no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↑ reveal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′⇝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame⇝W′ , vW′ , frame-evol , types-id ,
      frame-related
      with transport-target-type-and-relation
        (trans (sym (types-id _)) (applyTys-++ χsᴿ ψsᴿ _))
        (multi-⊑ᵀ evol q , frame-related)
  catchup-to-more-precise no-rebase
      (CTI.reveal⊑reveal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↑ reveal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′⇝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame⇝W′ , vW′ , frame-evol , types-id ,
      frame-related
    | final-q , final-related =
    Δᴿ′ , Σᴿ′ , χsᴿ ++χ ψsᴿ , W′ , γ′ , final-q ,
      (M′ ↑ c′
        —↠+[ χsᴿ ]⟨ reveal-↠ c′ M′⇝V′ ⟩
       V′ ↑ applyReveals χsᴿ c′
        —↠[ ψsᴿ ]⟨ frame⇝W′ ⟩
       W′ ∎[]) , vW′ ,
      composeMultiWorldEvolution evol frame-evol , final-related

  catchup-to-more-precise no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↓ conceal-value)
      with catchup-to-more-precise no-rebase prem vV
  catchup-to-more-precise no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↓ conceal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′⇝V′ , vV′ , evol ,
      related
      with paired-conceal-value-catchup
        (multi-source-conceal evol c⊢)
        (multi-target-conceal evol c′⊢)
        (trans (multi-source-conceal-position evol c⊢)
          (trans positions
            (sym (multi-target-conceal-position evol c′⊢))))
        (multi-aligned evol aligned)
        (multi-⊑ᵀ evol represented)
        related (multi-⊑ᵀ evol q) conceal-value vV′
  catchup-to-more-precise no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↓ conceal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′⇝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame⇝W′ , vW′ , frame-evol , types-id ,
      frame-related
      with transport-target-type-and-relation
        (trans (sym (types-id _)) (applyTys-++ χsᴿ ψsᴿ _))
        (multi-⊑ᵀ evol q , frame-related)
  catchup-to-more-precise no-rebase
      (CTI.conceal⊑conceal² {M′ = M′} {c′ = c′}
        c⊢ c′⊢ positions aligned represented prem q)
      (vV CT.↓ conceal-value)
    | Δᴿ′ , Σᴿ′ , χsᴿ , V′ , γ′ , r , M′⇝V′ , vV′ , evol ,
      related
    | ψsᴿ , W′ , frame⇝W′ , vW′ , frame-evol , types-id ,
      frame-related
    | final-q , final-related =
    Δᴿ′ , Σᴿ′ , χsᴿ ++χ ψsᴿ , W′ , γ′ , final-q ,
      (M′ ↓ c′
        —↠+[ χsᴿ ]⟨ conceal-↠ c′ M′⇝V′ ⟩
       V′ ↓ applyConceals χsᴿ c′
        —↠[ ψsᴿ ]⟨ frame⇝W′ ⟩
       W′ ∎[]) , vW′ ,
      composeMultiWorldEvolution evol frame-evol , final-related

  catchup-to-more-precise no-rebase
      (CTI.⊑reveal-rebase² c′⊢ rebase prem q) vV =
    target-reveal-rebase-catchup no-rebase c′⊢ rebase prem q vV

  catchup-to-more-precise no-rebase
      (CTI.⊑conceal-rebase² c′⊢ rebase prem q) vV
      with trans (sym no-rebase) (open-source-rebase-frames rebase)
  catchup-to-more-precise no-rebase
      (CTI.⊑conceal-rebase² c′⊢ rebase prem q) vV | ()

  catchup-to-more-precise no-rebase (CTI.blame⊑² target⊢ p) ()

  catchup-to-more-precise no-rebase
      (CTI.⊕⊑⊕² op prem₁ prem₂ r) ()

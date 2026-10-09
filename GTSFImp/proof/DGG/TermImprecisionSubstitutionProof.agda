{-# OPTIONS --safe #-}

module proof.DGG.TermImprecisionSubstitutionProof where

-- File Charter:
--   * Proves canonical CTI preservation under a typed parallel term
--     substitution by a complete induction on the CTI derivation.
--   * Is parameterized by the genuine scope inductions for term binders,
--     type binders, and balanced source-rebase push/pop.
--   * Derives the public single-variable theorem from the parallel proof and
--     the canonical head-substitution scope.

open import Data.Product using (_,_)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import Types using (Ty)
open import TyStore using (TyStore)
open import TermCtx using (TermCtx; _∋_⦂_; Z; S)
open import CastTerms using
  ( singleSub
  ; subst
  )
open import proof.TermInTermSubst using
  (subst-preserves-Value; typing-subst; singleSubstWf)
open import proof.DGG.TermImprecisionSubstitutionDef
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecisionTyping using
  (source-typing; target-typing)
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; bind-termᶜ)
open import Imprecision using (_⊢_⊑_; ⇒⊑⇒)
open import CastTerms using (Ctx; Δᵉ; Term; _[_])
import proof.Imprecision as PI


⊢²-retarget : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term _} {M′ : Term _} {A B}
    {p q : A ⊑ᵀ⟨ γ ⟩ B}
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → γ CTI.⊢² M ⊑ M′ ∶ q
⊢²-retarget {p = p} {q = q} related
    rewrite PI.⊑-unique p q = related


head-variable : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {V : Term Δᴸ} {V′ : Term Δᴿ}
    {A C : Ty Δᴸ} {A′ C′ : Ty Δᴿ}
    {pA : A ⊑ᵀ⟨ γ ⟩ A′} {pC : C ⊑ᵀ⟨ γ ⟩ C′} {x}
  → γ CTI.⊢² V ⊑ V′ ∶ pA
  → (A ∷ Γᴸ) ∋ x ⦂ C
  → (A′ ∷ Γᴿ) ∋ x ⦂ C′
  → γ CTI.⊢² singleSub V x ⊑ singleSub V′ x ∶ pC
head-variable related Z Z = ⊢²-retarget related
head-variable related (S source-member) (S target-member) =
  CTI.x⊑x² source-member target-member


head-term-subst-scope : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {V : Term (Δᵉ Γᴸ)} {V′ : Term (Δᵉ Γᴿ)}
    {A : _} {A′ : _} {pA : A ⊑ᵀ⟨ γ ⟩ A′}
  → γ CTI.⊢² V ⊑ V′ ∶ pA
  → TermSubstScope (bind-termᶜ γ pA) γ
      (singleSub V) (singleSub V′)
head-term-subst-scope related = record
  { scope-⊑ᵀ = λ p → p
  ; scope-source-wf = singleSubstWf (source-typing related)
  ; scope-target-wf = singleSubstWf (target-typing related)
  ; scope-variable = head-variable related
  ; scope-source-mark = λ marked → marked
  ; scope-source-unoccupied = λ unoccupied → unoccupied
  ; scope-aligned = λ aligned → aligned
  }


module _
    (extend-term-scope : ExtendTermSubstScopeᵀ)
    (lift-both-term-scope : LiftBothTermSubstScopeᵀ)
    (lift-left-term-scope : LiftLeftTermSubstScopeᵀ)
    (push-term-rebase : PushTermSubstRebaseᵀ)
    (pop-term-rebase : PopTermSubstRebaseᵀ)
  where

  term-imprecision-parallel-substitution :
    TermImprecisionParallelSubstitutionᵀ
  term-imprecision-parallel-substitution scope
      (CTI.x⊑x² source-member target-member) =
    scope-variable scope source-member target-member

  term-imprecision-parallel-substitution scope
      (CTI.ƛ⊑ƛ² {pA = pA} {pB = pB} related) =
    ⊢²-retarget (CTI.ƛ⊑ƛ²
      (term-imprecision-parallel-substitution
        (extend-term-scope scope) related))

  term-imprecision-parallel-substitution scope
      (CTI.·⊑·² {pA = pA} {pB = pB} function-rel argument-rel) =
    CTI.·⊑·²
      (⊢²-retarget
        (term-imprecision-parallel-substitution scope function-rel))
      (term-imprecision-parallel-substitution scope argument-rel)

  term-imprecision-parallel-substitution scope
      (CTI.Λ⊑Λ² source-value target-value related q) =
    CTI.Λ⊑Λ²
      (subst-preserves-Value _ source-value)
      (subst-preserves-Value _ target-value)
      (term-imprecision-parallel-substitution
        (lift-both-term-scope scope) related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.Λ⊑² source-nonvar source-occurs source-value target-typing
        related q) =
    CTI.Λ⊑² source-nonvar source-occurs
      (subst-preserves-Value _ source-value)
      (typing-subst (scope-target-wf scope) target-typing)
      (term-imprecision-parallel-substitution
        (lift-left-term-scope scope) related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.•⊑•² p∀ related q r) =
    CTI.•⊑•² (scope-⊑ᵀ scope p∀)
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q) (scope-⊑ᵀ scope r)

  term-imprecision-parallel-substitution scope
      (CTI.•⊑² p∀ related q r) =
    CTI.•⊑² (scope-⊑ᵀ scope p∀)
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q) (scope-⊑ᵀ scope r)

  term-imprecision-parallel-substitution scope
      (CTI.κ⊑κ² constant p) =
    CTI.κ⊑κ² constant (scope-⊑ᵀ scope p)

  term-imprecision-parallel-substitution scope
      (CTI.cast⊑cast² source-cast target-cast related q) =
    CTI.cast⊑cast² source-cast target-cast
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.⊑cast² target-cast related q) =
    CTI.⊑cast² target-cast
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.⊑reveal-identity target-reveal position related q) =
    CTI.⊑reveal-identity target-reveal position
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.⊑conceal-identity target-conceal position related q) =
    CTI.⊑conceal-identity target-conceal position
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.cast⊑² source-cast related q) =
    CTI.cast⊑² source-cast
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.reveal⊑-identity source-reveal position related q) =
    CTI.reveal⊑-identity source-reveal position
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.reveal⊑-only² source-reveal position marked unoccupied
        represented related q) =
    CTI.reveal⊑-only² source-reveal position
      (scope-source-mark scope marked)
      (scope-source-unoccupied scope unoccupied)
      (scope-⊑ᵀ scope represented)
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.conceal⊑-identity source-conceal position related q) =
    CTI.conceal⊑-identity source-conceal position
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.conceal⊑-only² source-conceal position marked unoccupied
        represented related q) =
    CTI.conceal⊑-only² source-conceal position
      (scope-source-mark scope marked)
      (scope-source-unoccupied scope unoccupied)
      (scope-⊑ᵀ scope represented)
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.reveal⊑reveal² source-reveal target-reveal positions aligned
        represented related q) =
    CTI.reveal⊑reveal² source-reveal target-reveal positions
      (scope-aligned scope aligned)
      (scope-⊑ᵀ scope represented)
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.conceal⊑conceal² source-conceal target-conceal positions aligned
        represented related q) =
    CTI.conceal⊑conceal² source-conceal target-conceal positions
      (scope-aligned scope aligned)
      (scope-⊑ᵀ scope represented)
      (term-imprecision-parallel-substitution scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.⊑reveal-rebase² target-reveal rebase related q)
      with push-term-rebase scope rebase
  term-imprecision-parallel-substitution scope
      (CTI.⊑reveal-rebase² target-reveal rebase related q)
      | rebound-world , rebound-scope , rebound-rebase =
    CTI.⊑reveal-rebase² target-reveal rebound-rebase
      (term-imprecision-parallel-substitution rebound-scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.⊑conceal-rebase² target-conceal rebase related q)
      with pop-term-rebase scope rebase
  term-imprecision-parallel-substitution scope
      (CTI.⊑conceal-rebase² target-conceal rebase related q)
      | rebound-world , rebound-scope , rebound-rebase =
    CTI.⊑conceal-rebase² target-conceal rebound-rebase
      (term-imprecision-parallel-substitution rebound-scope related)
      (scope-⊑ᵀ scope q)

  term-imprecision-parallel-substitution scope
      (CTI.blame⊑² target-typing p) =
    CTI.blame⊑² (typing-subst (scope-target-wf scope) target-typing)
      (scope-⊑ᵀ scope p)

  term-imprecision-parallel-substitution scope
      (CTI.⊕⊑⊕² operation left-rel right-rel r) =
    CTI.⊕⊑⊕² operation
      (term-imprecision-parallel-substitution scope left-rel)
      (term-imprecision-parallel-substitution scope right-rel)
      (scope-⊑ᵀ scope r)


  term-imprecision-substitution : TermImprecisionSubstitutionᵀ
  term-imprecision-substitution value-rel body-rel =
    term-imprecision-parallel-substitution
      (head-term-subst-scope value-rel) body-rel

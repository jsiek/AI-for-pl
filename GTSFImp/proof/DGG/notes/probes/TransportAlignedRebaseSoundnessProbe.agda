{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TransportAlignedRebaseSoundnessProbe where

-- File Charter:
--   * Tests the arbitrary source-bind/target-reveal-rebase interface against
--     the trusted TargetIdentityReveal aligned allocation under a protected
--     source type binder.
--   * Pins the collision between the protected open-frame pivot and the
--     newly aligned source-store pivot when both select target alpha.
--   * Changes no live definition and exports no production interface.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import Consistency using (keep; wk↪ᵗ; renameᵐᶜ)
open import TermCtx using (Z)
open import TyStore using (store-empty; store-bind; Z∋)
open import Conversion using (seal; id↑; _↦↑_; _⊢↑[_⦂_]_)
open import CastTerms using (Term; renameᵗᵐ; _↑_)
import CastTerms as C
import Imprecision as I
import proof.Imprecision as PI
import Conversion as Conv
open import Types using (★; ＇_; _⇒_)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition-unique)
import proof.DGG.Examples.TargetIdentityReveal as TIR
open import proof.ImprecisionConsistency using (fin-suc-injective)
open import proof.DGG.SourceRebase using
  ( SourceRebaseᶜ
  ; source-rebase-now
  ; source-rebase-lift-left
  )
open import proof.DGG.TransportSourceBindDef
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportAlignedSourceBindᵀ)
open import proof.DGG.World


protected-aligned-plan :
  SourceBindScope (keep wk↪ᵗ)
    TIR.checkpoint₁-outside-world
    (liftLeftᶜ TIR.checkpoint₃-world)
protected-aligned-plan =
  source-scope-left
    (source-scope-root-aligned refl
      TIR.checkpoint₃-alpha-ok
      TIR.checkpoint₃-alpha-boundary
      TIR.checkpoint₃-alpha-representation)


checkpoint₁-source-function : Term 1
checkpoint₁-source-function =
  C.ƛ ((C.ƛ (C.` 0)) C.·
    (C.` 0 C.⟨ TIR.checkpoint₁-source-X-to-star ⟩))


transported-alpha-frame :
  TransportSourceBindTargetRevealRebaseᵀ
  → liftLeftᶜ TIR.checkpoint₃-world CTI.⊢²
      renameᵗᵐ (keep wk↪ᵗ) checkpoint₁-source-function
      ⊑ TIR.checkpoint₁-target-payload
      ∶ source-scope-⊑ᵀ protected-aligned-plan
          (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)
transported-alpha-frame transport =
  transport protected-aligned-plan
    TIR.checkpoint₁-alpha-reveal⊢
    (source-rebase-now TIR.checkpoint₁-alpha-ok
      TIR.checkpoint₁-alpha-representation)
    (CTI.⊑reveal-rebase²
      TIR.checkpoint₁-beta-reveal⊢
      (source-rebase-now TIR.checkpoint₁-beta-ok
        TIR.checkpoint₁-beta-representation)
      TIR.checkpoint₁-function-imprecision
      (I.⇒⊑⇒ I.X⊑X I.★⊑★))
    (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)


checkpoint₃-alpha-aligned :
  toRenameⁱ (ηᴸᶜ TIR.checkpoint₃-world) Fin.zero
    ≡ toRenameⁱ (ηᴿᶜ TIR.checkpoint₃-world)
        (Fin.suc Fin.zero)
checkpoint₃-alpha-aligned =
  pivot-alignedᵗ TIR.checkpoint₃-alpha-ok


protected-stored-alpha-aligned :
  toRenameⁱ (ηᴸᶜ (liftLeftᶜ TIR.checkpoint₃-world))
      (Fin.suc Fin.zero)
    ≡ toRenameⁱ (ηᴿᶜ (liftLeftᶜ TIR.checkpoint₃-world))
        (Fin.suc Fin.zero)
protected-stored-alpha-aligned =
  cong Fin.suc checkpoint₃-alpha-aligned


no-protected-alpha-update : ∀ X
  → PivotUpdateᵗ
      (ηᴸᶜ (liftLeftᶜ TIR.checkpoint₃-world)) X
      (toRenameⁱ (ηᴿᶜ (liftLeftᶜ TIR.checkpoint₃-world))
        (Fin.suc Fin.zero))
  → ⊥
no-protected-alpha-update Fin.zero update
    with toRenameⁱ-injective (pivot-afterᵗ update)
      (trans (pivot-alignedᵗ update)
        (sym (trans
          (off-pivot-fixedᵗ update (Fin.suc Fin.zero) (λ ()))
          protected-stored-alpha-aligned)))
... | ()
no-protected-alpha-update (Fin.suc Fin.zero) update =
  pivot-before-apartᵗ update protected-stored-alpha-aligned
no-protected-alpha-update (Fin.suc (Fin.suc ())) update


no-stored-alpha-update : ∀ X
  → PivotUpdateᵗ (ηᴸᶜ TIR.checkpoint₃-world) X
      (toRenameⁱ (ηᴿᶜ TIR.checkpoint₃-world)
        (Fin.suc Fin.zero))
  → ⊥
no-stored-alpha-update Fin.zero update =
  pivot-before-apartᵗ update checkpoint₃-alpha-aligned
no-stored-alpha-update (Fin.suc ()) update


no-stored-alpha-rebase : ∀ {γᵖ} {X}
  → SourceRebaseᶜ TIR.checkpoint₃-world γᵖ X
      (Fin.suc Fin.zero)
  → ⊥
no-stored-alpha-rebase (source-rebase-now update represented) =
  no-stored-alpha-update _ update


no-protected-alpha-rebase : ∀ {γᵖ} {X}
  → SourceRebaseᶜ (liftLeftᶜ TIR.checkpoint₃-world) γᵖ X
      (Fin.suc Fin.zero)
  → ⊥
no-protected-alpha-rebase (source-rebase-now update represented) =
  no-protected-alpha-update _ update
no-protected-alpha-rebase (source-rebase-lift-left rebase) =
  no-stored-alpha-rebase rebase


transported-alpha-frame-impossible :
  ∀ {p : (＇ Fin.zero ⇒ ★) ⊑ᵀ⟨
      liftLeftᶜ TIR.checkpoint₃-world ⟩ (★ ⇒ ★)}
  →
  liftLeftᶜ TIR.checkpoint₃-world CTI.⊢²
      renameᵗᵐ (keep wk↪ᵗ) checkpoint₁-source-function
      ⊑ TIR.checkpoint₁-target-payload
      ∶ p
  → ⊥
transported-alpha-frame-impossible
    (CTI.⊑reveal-identity
      (Conv.⊢↑-⇒ (Conv.⊢↓-seal member)
        (Conv.⊢↑-id-star member′)) () related q)
transported-alpha-frame-impossible
    (CTI.⊑reveal-rebase²
      (Conv.⊢↑-⇒ (Conv.⊢↓-seal member)
        (Conv.⊢↑-id-star member′)) rebase related q) =
  no-protected-alpha-rebase rebase


arbitrary-source-reveal-transport-is-false :
  TransportSourceBindTargetRevealRebaseᵀ → ⊥
arbitrary-source-reveal-transport-is-false transport =
  transported-alpha-frame-impossible (transported-alpha-frame transport)


------------------------------------------------------------------------
-- The same collision at a runtime-allocation root
------------------------------------------------------------------------

root-alpha-open-world =
  TIR.checkpoint₃-allocation-world ▻ᶜ
    rebase-source-changeᶜ Fin.zero (Fin.suc Fin.zero)
      TIR.checkpoint₃-alpha-ok open-frameᶜ
      TIR.checkpoint₃-alpha-representation

root-alpha-rebase :
  SourceRebaseᶜ TIR.checkpoint₃-allocation-world
    root-alpha-open-world Fin.zero (Fin.suc Fin.zero)
root-alpha-rebase =
  source-rebase-now TIR.checkpoint₃-alpha-ok
    TIR.checkpoint₃-alpha-representation

root-beta-open-world =
  root-alpha-open-world ▻ᶜ
    rebase-source-changeᶜ Fin.zero Fin.zero
      TIR.checkpoint₃-beta-ok open-frameᶜ
      TIR.checkpoint₃-beta-representation

root-beta-rebase :
  SourceRebaseᶜ root-alpha-open-world root-beta-open-world
    Fin.zero Fin.zero
root-beta-rebase =
  source-rebase-now TIR.checkpoint₃-beta-ok
    TIR.checkpoint₃-beta-representation

root-body-imprecision :
  bind-termᶜ root-beta-open-world I.X⊑X CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ TIR.checkpoint₁-source-X-to-star ⟩)
    ⊑ (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ TIR.checkpoint₁-target-X-to-star ⟩)
    ∶ I.★⊑★
root-body-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
      (CTI.x⊑x² {p = I.★⊑★} Z Z))
    (CTI.cast⊑cast²
      TIR.checkpoint₁-source-X-to-star
      TIR.checkpoint₁-target-X-to-star
      (CTI.x⊑x² {p = I.X⊑X} Z Z)
      I.★⊑★)


root-function-imprecision :
  root-beta-open-world CTI.⊢²
    checkpoint₁-source-function
    ⊑ TIR.checkpoint₁-target-function
    ∶ I.⇒⊑⇒ I.X⊑X I.★⊑★
root-function-imprecision = CTI.ƛ⊑ƛ² root-body-imprecision

root-beta-imprecision :
  root-alpha-open-world CTI.⊢²
    checkpoint₁-source-function
    ⊑ TIR.checkpoint₁-target-beta-reveal
    ∶ I.⇒⊑⇒ I.X⊑X I.★⊑★
root-beta-imprecision =
  CTI.⊑reveal-rebase² TIR.checkpoint₁-beta-reveal⊢
    root-beta-rebase root-function-imprecision
    (I.⇒⊑⇒ I.X⊑X I.★⊑★)

root-alpha-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    checkpoint₁-source-function
    ⊑ TIR.checkpoint₁-target-payload
    ∶ I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★
root-alpha-imprecision =
  CTI.⊑reveal-rebase² TIR.checkpoint₁-alpha-reveal⊢
    root-alpha-rebase root-beta-imprecision
    (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)


second-allocation-world =
  TIR.checkpoint₃-allocation-world ▻ᶜ
    bind-left-changeᶜ TIR.ℕᵗ refl

second-alpha-ok :
  PivotUpdateᵗ (ηᴸᶜ second-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ second-allocation-world)
      (Fin.suc Fin.zero))
second-alpha-ok =
  repointⁱ (ηᴸᶜ second-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ second-allocation-world)
      (Fin.suc Fin.zero))
    (λ ())
    (λ
      { Fin.zero zero≠zero eq → zero≠zero refl
      ; (Fin.suc Fin.zero) _ eq →
          pivot-before-apartᵗ TIR.checkpoint₃-alpha-ok
            (fin-suc-injective eq)
      ; (Fin.suc (Fin.suc ()))
      })

second-source-reveal⊢ :
  store-bind (store-bind store-empty TIR.ℕᵗ) TIR.ℕᵗ
    ⊢↑[ Fin.zero ⦂ TIR.ℕᵗ ]
      (seal Fin.zero TIR.ℕᵗ ↦↑ id↑ ★)
second-source-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal (Z∋ refl))
    (Conv.⊢↑-id-star (Z∋ refl))

second-alpha-boundary :
  AlignmentBoundaryᶜ second-allocation-world Fin.zero
    (Fin.suc Fin.zero) second-alpha-ok
second-alpha-boundary =
  paired-reveal-alignmentᶜ
    second-source-reveal⊢ TIR.checkpoint₁-alpha-reveal⊢
    refl I.ι⊑★

second-aligned-world =
  second-allocation-world ▻ᶜ
    rebase-source-changeᶜ Fin.zero (Fin.suc Fin.zero)
      second-alpha-ok (alignment-onlyᶜ second-alpha-boundary)
      (I.X⊑★ refl)


root-aligned-plan :
  SourceBindScope wk↪ᵗ TIR.checkpoint₃-allocation-world
    second-aligned-world
root-aligned-plan =
  source-scope-root-aligned refl second-alpha-ok
    second-alpha-boundary (I.X⊑★ refl)


second-source-function : Term 2
second-source-function =
  C.ƛ ((C.ƛ (C.` 0)) C.·
    (C.` 0 C.⟨ renameᵐᶜ wk↪ᵗ
      TIR.checkpoint₁-source-X-to-star ⟩))

second-source-function-eq :
  renameᵗᵐ wk↪ᵗ checkpoint₁-source-function
    ≡ second-source-function
second-source-function-eq = refl


no-second-alpha-update : ∀ X
  → PivotUpdateᵗ (ηᴸᶜ second-aligned-world) X
      (toRenameⁱ (ηᴿᶜ second-aligned-world)
        (Fin.suc Fin.zero))
  → ⊥
no-second-alpha-update Fin.zero update =
  pivot-before-apartᵗ update (pivot-alignedᵗ second-alpha-ok)
no-second-alpha-update (Fin.suc Fin.zero) update
    with toRenameⁱ-injective (pivot-afterᵗ update)
      (trans (pivot-alignedᵗ update)
        (sym (trans
          (off-pivot-fixedᵗ update Fin.zero (λ ()))
          (pivot-alignedᵗ second-alpha-ok))))
... | ()
no-second-alpha-update (Fin.suc (Fin.suc ())) update


no-second-alpha-rebase : ∀ {γᵖ} {X}
  → SourceRebaseᶜ second-aligned-world γᵖ X
      (Fin.suc Fin.zero)
  → ⊥
no-second-alpha-rebase (source-rebase-now update represented) =
  no-second-alpha-update _ update


transported-root-alpha-frame-impossible : ∀ {M A B}
    {p : A ⊑ᵀ⟨ second-aligned-world ⟩ B}
  → M ≡ second-source-function
  → second-aligned-world CTI.⊢²
      M ⊑ TIR.checkpoint₁-target-payload ∶ p
  → ⊥
transported-root-alpha-frame-impossible
    eq (CTI.⊑reveal-identity
      (Conv.⊢↑-⇒ (Conv.⊢↓-seal member)
        (Conv.⊢↑-id-star member′)) () related q)
transported-root-alpha-frame-impossible
    () (CTI.reveal⊑reveal²
      source-reveal target-reveal positions aligned
      represented related q)
transported-root-alpha-frame-impossible
    eq (CTI.⊑reveal-rebase²
      (Conv.⊢↑-⇒ (Conv.⊢↓-seal member)
        (Conv.⊢↑-id-star member′)) rebase related q) =
  no-second-alpha-rebase rebase


root-aligned-source-transport-is-false :
  TransportAlignedSourceBindᵀ → ⊥
root-aligned-source-transport-is-false transport =
  transported-root-alpha-frame-impossible
    second-source-function-eq
    (transport refl second-alpha-ok second-alpha-boundary
      (I.X⊑★ refl) root-alpha-imprecision)

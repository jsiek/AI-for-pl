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
  (_≡_; refl; sym; trans; cong)

open import Consistency using (keep; wk↪ᵗ)
open import CastTerms using (Term; renameᵗᵐ; _↑_)
import CastTerms as C
import Imprecision as I
import Conversion as Conv
open import Types using (★; ＇_; _⇒_)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition-unique)
import proof.DGG.Examples.TargetIdentityReveal as TIR
open import proof.DGG.SourceRebase using
  ( SourceRebaseᶜ
  ; source-rebase-now
  ; source-rebase-lift-left
  )
open import proof.DGG.TransportSourceBindDef
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

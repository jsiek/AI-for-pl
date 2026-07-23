module proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewProof where

-- File Charter:
--   * Classifies value-shaped, canonical-all source relations into a terminal
--     polymorphic leaf and a proof-relevant spine of surrounding frames.
--   * Recurses mutually over ordinary and quotiented term imprecision.
--   * Contains no semantic catch-up proof, postulate, or permissive option.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
open import Agda.Builtin.Equality using (refl)
open import Coercions using
  ( id-onlyᵈ
  ; ModeIncl
  ; tag-or-idᵈ
  )
open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; $
  ; ƛ_
  ; Λ_
  ; _⟨_⟩
  ; no•-Λ
  ; no•-⟨⟩
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  ; allocation-prefixᵀ
  ; blame⊑ᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; nu-term-imprecision-source-typing
  ; quotient-cast-widening
  ; quotient-id-widening
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; up⊑upᵀ
  ; x⊑xᵀ
  ; Λ⊑Λᵀ
  ; Λ⊑ᵀ
  ; α⊑αᵀ
  ; α⊑ᵀ
  ; ⊑αᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ν⊑νᵀ
  ; ν⊑ᵀ
  ; ⊑νᵀ
  ; νcast⊑νcastᵀ
  ; νcast⊑ᵀ
  ; ⊑νcastᵀ
  ; κ⊑κᵀ
  ; ⊕⊑⊕ᵀ
  ; ·⊑·ᵀ
  ; ƛ⊑ƛᵀ
  )
open import TermTyping using (forget)
open import proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
open import proof.DGG.Core.NuProgress using
  ( AllView
  ; av-gen
  ; av-Λ
  ; av-∀
  ; canonical-∀
  )
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_; ∀ⁱ_; ν)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import NuTermImprecision using (StoreImp)
open import Types using (Ty; TyCtx; `∀)


id-only≤gen-tag-or-idᵈ : ModeIncl id-onlyᵈ (C.genᵈ tag-or-idᵈ)
id-only≤gen-tag-or-idᵈ zero = refl
id-only≤gen-tag-or-idᵈ (suc X) = refl


mutual
  paired-lambda-target-closing-frame-viewᵀ :
    PairedLambdaTargetClosingFrameViewᵀ

  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW (blame⊑ᵀ W′⊢)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW (x⊑xᵀ x∈)
  paired-lambda-target-closing-frame-viewᵀ
      (ƛ N) noW vW′ noW′ (av-Λ ())
      (ƛ⊑ƛᵀ hA hA′ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      (ƛ N) noW vW′ noW′ (av-∀ vN ())
      (ƛ⊑ƛᵀ hA hA′ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      (ƛ N) noW vW′ noW′ (av-gen vN ())
      (ƛ⊑ƛᵀ hA hA′ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW (·⊑·ᵀ L⊑L′ M⊑M′)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-d ⟩ ⟨ inert-u ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM))
      (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM′))
      (av-Λ ())
      (up⊑upᵀ down widening pA)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-d ⟩ ⟨ inert-u ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM))
      (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM′))
      (av-∀ vMd refl)
      (up⊑upᵀ {qD = qD} down
        widening@(quotient-id-widening {D′ = D′} {A′ = B′}
          (C.cast-all {A = D} {B = B} u⊢ ,
            NW.cross (NW.`∀ {s = u} uʷ)) u′⊑)
        pA) =
    paired-lambda-target-closing-frame-viewᵖ
      {D = D} {D′ = D′} {B = B} {B′ = B′}
      {u = u} {qD = qD}
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      down widening pA
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-d ⟩ ⟨ inert-u ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM))
      (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM′))
      (av-∀ vMd refl)
      (up⊑upᵀ {qD = qD} down
        widening@(quotient-cast-widening {D′ = D′} {A′ = B′}
          mode seal★
          (C.cast-all {A = D} {B = B} u⊢ ,
            NW.cross (NW.`∀ {s = u} uʷ))
          mode′ seal★′ u′⊑)
        pA) =
    paired-lambda-target-closing-frame-viewᵖ
      {D = D} {D′ = D′} {B = B} {B′ = B′}
      {u = u} {qD = qD}
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      down widening pA
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-d ⟩ ⟨ inert-u ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM))
      (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM′))
      (av-gen vMd refl)
      (up⊑upᵀ down
        (quotient-id-widening (_ , NW.cross ()) u′⊑) pA)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-d ⟩ ⟨ inert-u ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM))
      (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noM′))
      (av-gen vMd refl)
      (up⊑upᵀ down
        (quotient-cast-widening mode seal★ (_ , NW.cross ())
          mode′ seal★′ u′⊑)
        pA)
  paired-lambda-target-closing-frame-viewᵀ
      (Λ vV) (no•-Λ noV) (Λ vV′) (no•-Λ noV′)
      (av-Λ refl) (Λ⊑Λᵀ liftρ liftγ vR vR′ V⊑V′) =
    closing-frame-view
      (leaf-ΛΛ liftρ liftγ vV noV vV′ noV′ V⊑V′)
      frame-refl
  paired-lambda-target-closing-frame-viewᵀ
      (Λ vV) (no•-Λ noV) vN′ noN′
      (av-Λ refl) (Λ⊑ᵀ occ liftρ liftγ vR V⊑N′) =
    closing-frame-view
      (leaf-Λ occ liftρ liftγ vV noV vN′ noN′ V⊑N′)
      frame-refl
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW
      (α⊑αᵀ vL noL vL′ noL′ p liftρ liftγ L⊑L′ L⊢ L′⊢)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW
      (α⊑ᵀ vL noL hA liftρ liftγ L⊑N′ L⊢ N′⊢)
  paired-lambda-target-closing-frame-viewᵀ
      vW noW () noW′ allW
      (⊑αᵀ vL′ noL′ hA liftρ liftγ N⊑L′ p N⊢ L′⊢)
  paired-lambda-target-closing-frame-viewᵀ
      vW noW vW′ noW′ allW
      (allocation-prefixᵀ prefix rel W⊢ W′⊢)
      with paired-lambda-target-closing-frame-viewᵀ
        vW noW vW′ noW′ allW rel
  paired-lambda-target-closing-frame-viewᵀ
      vW noW vW′ noW′ allW
      (allocation-prefixᵀ prefix rel W⊢ W′⊢)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-prefix frames prefix W⊢ W′⊢)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A↑⊑A′↑
        liftρ liftγ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW
      (ν⊑ᵀ hA h↑A s↑ liftρ liftγ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      vW noW () noW′ allW
      (⊑νᵀ hA h↑A s↑ liftρ liftγ p N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW
      (νcast⊑νcastᵀ mode seal★ mode′ seal★′ s⊑ s′⊑
        compat liftρ liftγ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW
      (νcast⊑ᵀ mode seal★ s⊑ liftρ liftγ N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      vW noW () noW′ allW
      (⊑νcastᵀ mode seal★ s⊑ liftρ liftγ p N⊑N′)
  paired-lambda-target-closing-frame-viewᵀ
      ($ k) noW vW′ noW′ (av-Λ ()) κ⊑κᵀ
  paired-lambda-target-closing-frame-viewᵀ
      ($ k) noW vW′ noW′ (av-∀ vK ()) κ⊑κᵀ
  paired-lambda-target-closing-frame-viewᵀ
      ($ k) noW vW′ noW′ (av-gen vK ()) κ⊑κᵀ
  paired-lambda-target-closing-frame-viewᵀ
      () noW vW′ noW′ allW (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-Λ ()) (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl)
      (cast⊒⊑ᵀ mode seal★
        c⊒@(C.cast-all c⊢ , NW.cross (NW.`∀ cⁿ)) M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl)
      (cast⊒⊑ᵀ mode seal★
        c⊒@(C.cast-all c⊢ , NW.cross (NW.`∀ cⁿ)) M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-cast⊒⊑ frames mode seal★ c⊒ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊒⊑ᵀ {p = p} mode seal★
        (C.cast-gen hA occ c⊢ , NW.gen cⁿ) M⊑M′ (∀ⁱ q))
      with p
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊒⊑ᵀ mode seal★
        (C.cast-gen hA occ c⊢ , NW.gen cⁿ) M⊑M′ (∀ⁱ q))
      | ∀ⁱ p
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊒⊑ᵀ mode seal★
        (C.cast-gen hA occ c⊢ , NW.gen cⁿ) M⊑M′ (∀ⁱ q))
      | ∀ⁱ p | closing-frame-view leaf frames =
    closing-frame-view
      leaf
      (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊒⊑ᵀ mode seal★
        (C.cast-gen hA occ c⊢ , NW.gen cⁿ) M⊑M′ (∀ⁱ q))
      | ν _ occ-p p
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊒⊑ᵀ mode seal★
        (C.cast-gen hA occ c⊢ , NW.gen cⁿ) M⊑M′ (∀ⁱ q))
      | ν _ occ-p p | closing-frame-view leaf frames =
    closing-frame-view
      leaf
      (frame-gen-all frames mode seal★ hA occ c⊢ cⁿ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊒⊑ᵀ mode seal★
        (C.cast-gen hA occ c⊢ , NW.gen cⁿ) M⊑M′ (ν _ occ-r r)) =
    closing-frame-view
      (leaf-gen-ν vM noM vM′ noM′ mode seal★
        hA occ c⊢ cⁿ M⊑M′ occ-r r)
      frame-refl
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-Λ ()) (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl)
      (cast⊑⊑ᵀ mode seal★
        c⊑@(C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl)
      (cast⊑⊑ᵀ mode seal★
        c⊑@(C.cast-all c⊢ , NW.cross (NW.`∀ cʷ)) M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-cast⊑⊑ frames mode seal★ c⊑ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl)
      (cast⊑⊑ᵀ mode seal★ (_ , NW.cross ()) M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′ allM M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf
      (frame-⊑cast⊒ frames inert-c′ mode′ seal★′ c′⊒ q)
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′ allM M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf
      (frame-⊑cast⊑ frames inert-c′ mode′ seal★′ c′⊑ q)
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑cast⊑idᵀ seal★′ c′⊑ M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′ allM M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑cast⊑idᵀ seal★′ c′⊑ M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf
      (frame-⊑cast⊑id frames inert-c′ seal★′ c′⊑ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-Λ ()) (conv⊑convᵀ paired M⊑M′)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-∀ vR refl)
      (conv⊑convᵀ
        paired@(paired-conversion
          (paired-reveal corr (CV.reveal-all c↑) c′↑))
        M⊑M′)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-∀ vR refl)
      (conv⊑convᵀ
        paired@(paired-conversion
          (paired-reveal corr (CV.reveal-all c↑) c′↑))
        M⊑M′)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-conv⊑conv frames inert-c′ paired)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-∀ vR refl)
      (conv⊑convᵀ
        paired@(paired-conversion
          (paired-conceal corr (CV.conceal-all c↓) c′↓))
        M⊑M′)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-∀ vR refl)
      (conv⊑convᵀ
        paired@(paired-conversion
          (paired-conceal corr (CV.conceal-all c↓) c′↓))
        M⊑M′)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-conv⊑conv frames inert-c′ paired)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-∀ vR refl)
      (conv⊑convᵀ
        paired@(paired-widening mode seal★
          (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
          mode′ seal★′ c′⊑ compat)
        M⊑M′)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-∀ vR refl)
      (conv⊑convᵀ
        paired@(paired-widening mode seal★
          (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
          mode′ seal★′ c′⊑ compat)
        M⊑M′)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-conv⊑conv frames inert-c′ paired)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-gen vR refl)
      (conv⊑convᵀ
        (paired-conversion (paired-reveal corr () c′↑)) M⊑M′)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-gen vR refl)
      (conv⊑convᵀ
        (paired-conversion (paired-conceal corr () c′↓)) M⊑M′)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM)
      (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′)
      (av-gen vR refl)
      (conv⊑convᵀ
        (paired-widening mode seal★ (_ , NW.cross ())
          mode′ seal★′ c′⊑ compat)
        M⊑M′)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-Λ ()) (conv↑⊑ᵀ c↑ M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl) (conv↑⊑ᵀ c↑@(CV.reveal-all inner) M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl) (conv↑⊑ᵀ c↑@(CV.reveal-all inner) M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-conv↑⊑ frames c↑ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl) (conv↑⊑ᵀ () M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-Λ ()) (conv↓⊑ᵀ c↓ M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl) (conv↓⊑ᵀ c↓@(CV.conceal-all inner) M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-∀ vR refl) (conv↓⊑ᵀ c↓@(CV.conceal-all inner) M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-conv↓⊑ frames c↓ q)
  paired-lambda-target-closing-frame-viewᵀ
      (vM ⟨ inert-c ⟩) (no•-⟨⟩ noM) vM′ noM′
      (av-gen vR refl) (conv↓⊑ᵀ () M⊑M′ q)
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑conv↑ᵀ c′↑ M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′ allM M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑conv↑ᵀ c′↑ M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-⊑conv↑ frames inert-c′ c′↑ q)
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑conv↓ᵀ c′↓ M⊑M′ q)
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′ allM M⊑M′
  paired-lambda-target-closing-frame-viewᵀ
      vM noM (vM′ ⟨ inert-c′ ⟩) (no•-⟨⟩ noM′) allM
      (⊑conv↓ᵀ c′↓ M⊑M′ q)
      | closing-frame-view leaf frames =
    closing-frame-view leaf (frame-⊑conv↓ frames inert-c′ c′↓ q)

  paired-lambda-target-closing-frame-viewᵖ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {D D′ B B′ : Ty}
        {d d′ u u′ : C.Coercion}
        {qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Value M → No• M →
    Value M′ → No• M′ →
    C.Inert d → C.Inert d′ → C.Inert (C.`∀ u) → C.Inert u′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺᵖ M ⟨ d ⟩ ⊑ M′ ⟨ d′ ⟩
        ⦂ `∀ D ⊑ᵖ D′ ∶ qD →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (pB : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    PairedLambdaTargetClosingFrameView ρ
      ((M ⟨ d ⟩) ⟨ C.`∀ u ⟩) ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩)
      (`∀ B) B′ pB

  paired-lambda-target-closing-frame-viewᵖ
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      (down⊑downᵀ
        d⊒@(C.cast-all d⊢ , NW.cross (NW.`∀ dⁿ))
        d′⊒ M⊑M′ qD)
      widening pB
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵖ
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      (down⊑downᵀ
        d⊒@(C.cast-all d⊢ , NW.cross (NW.`∀ dⁿ))
        d′⊒ M⊑M′ qD)
      widening pB
      | closing-frame-view leaf frames =
    closing-frame-view leaf
      (frame-up-id frames inert-d′ inert-u′ d⊒ d′⊒ qD widening pB)
  paired-lambda-target-closing-frame-viewᵖ
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      (down⊑downᵀ
        (C.cast-gen hC occ d⊢ , NW.gen dⁿ)
        d′⊒ M⊑M′ qD)
      widening pB =
    closing-frame-view
      (leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′
        (NW.narrow-mode-relax id-only≤gen-tag-or-idᵈ
          (C.cast-gen hC occ d⊢ , NW.gen dⁿ))
        (NW.narrow-mode-relax id-only≤gen-tag-or-idᵈ d′⊒)
        M⊑M′ qD widening pB)
      frame-refl
  paired-lambda-target-closing-frame-viewᵖ
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      (gen-down⊑gen-downᵀ
        d⊒@(C.cast-all d⊢ , NW.cross (NW.`∀ dⁿ))
        d′⊒ M⊑M′ qD)
      widening pB
      with paired-lambda-target-closing-frame-viewᵀ
        vM noM vM′ noM′
        (canonical-∀ vM
          (forget
            (nu-term-imprecision-source-typing {γ = []} M⊑M′)))
        M⊑M′
  paired-lambda-target-closing-frame-viewᵖ
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      (gen-down⊑gen-downᵀ
        d⊒@(C.cast-all d⊢ , NW.cross (NW.`∀ dⁿ))
        d′⊒ M⊑M′ qD)
      widening pB
      | closing-frame-view leaf frames =
    closing-frame-view leaf
      (frame-up-gen-all frames inert-d′ inert-u′
        d⊒ d′⊒ qD widening pB)
  paired-lambda-target-closing-frame-viewᵖ
      vM noM vM′ noM′ inert-d inert-d′ inert-u inert-u′
      (gen-down⊑gen-downᵀ
        (C.cast-gen hC occ d⊢ , NW.gen dⁿ)
        d′⊒ M⊑M′ qD)
      widening pB =
    closing-frame-view
      (leaf-up-gen vM noM vM′ noM′ inert-d′ inert-u′
        (C.cast-gen hC occ d⊢ , NW.gen dⁿ)
        d′⊒ M⊑M′ qD widening pB)
      frame-refl


paired-lambda-target-closing-frame-view-proofᵀ :
  PairedLambdaTargetClosingFrameViewᵀ
paired-lambda-target-closing-frame-view-proofᵀ =
  paired-lambda-target-closing-frame-viewᵀ

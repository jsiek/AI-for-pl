module proof.Target.SealTag.NuImprecisionTargetTagCancellationProof where

-- File Charter:
--   * Proves cancellation of one terminal target ground tag.
--   * Pushes cancellation through source-only binders, inert source casts,
--     paired widenings, quotient-up boundaries, and allocation prefixes.
--   * Uses source-name exclusivity and proof-index uniqueness explicitly.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)

import Coercions as C
import Conversion as CV
open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( id★
  ; tagˣ
  ; idˣ
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( lift-left-ctx-[]
  ; seal★-tag-or-id
  )
open import NuTerms using
  ( Term
  ; Value
  ; no•-Λ
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; quotient-cast-widening
  ; quotient-id-widening
  ; up⊑upᵀ
  ; Λ⊑instβᵀ
  ; Λ⊑ᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; cast-tag-or-id
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
import Types as T
open import proof.Compilation.GenSafeProperties using
  ( genSafe-source-shape
  ; genSafe-target-shape
  ; narrowing-inert-view
  ; shape-all
  ; shape-fun
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-source)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import
 proof.Target.GroundValue.NuImprecisionTargetGroundValueQuotientEliminationLemma
  using (target-ground-value-quotient-eliminationᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetGroundUniqueness using
  ( gen-safe-shape-ground-function
  ; gen-safe-shape-star-to-function
  ; target-ground-unique
  )
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationDef using
  (TargetTagCancellationᵀ)


target-tag-typing⁻¹ :
  ∀ {Δ Σ Γ W G} →
  Δ ∣ Σ ∣ Γ ⊢ W ⟨ G C.! ⟩ ⦂ T.★ →
  Δ ∣ Σ ∣ Γ ⊢ W ⦂ G
target-tag-typing⁻¹ (⊢⟨⟩↑ () W⊢)
target-tag-typing⁻¹ (⊢⟨⟩↓ () W⊢)
target-tag-typing⁻¹
    (⊢⟨⟩⊒ mode seal★ (c⊢ , NW.cross ()) W⊢)
target-tag-typing⁻¹
    (⊢⟨⟩⊑ mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) W⊢) =
  W⊢


source-variable-ground-impossible :
  ∀ {Φ Δᴸ Δᴿ α H} →
  (∀ {β} →
    (α ˣ⊑★) ∈ Φ →
    (α ˣ⊑ˣ β) ∈ Φ →
    ⊥) →
  Φ ∣ Δᴸ ⊢ T.＇ α ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ T.＇ α ⊑ H ⊣ Δᴿ →
  T.Ground H →
  ⊥
source-variable-ground-impossible exclusive
    (tagˣ source-only α<) (idˣ matched α<′ β<)
    (T.＇ β) =
  exclusive source-only matched


star-ground-impossible :
  ∀ {Φ Δᴸ Δᴿ H} →
  Φ ∣ Δᴸ ⊢ T.★ ⊑ H ⊣ Δᴿ →
  T.Ground H →
  ⊥
star-ground-impossible id★ ()


source-inert-narrowing-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B H} →
  (∀ {α β} →
    (α ˣ⊑★) ∈ Φ →
    (α ˣ⊑ˣ β) ∈ Φ →
    ⊥) →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊒ B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    with narrowing-inert-view narrowing inert
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    | inj₁ safe =
  gen-safe-shape-star-to-function
    (genSafe-source-shape c⊢ safe) inner-index ,
  gen-safe-shape-ground-function
    (genSafe-target-shape c⊢ safe) requested ground
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    | inj₂ (D , α , refl)
    with c⊢
source-inert-narrowing-route exclusive inert (c⊢ , narrowing)
    inner-index outer-index requested ground
    | inj₂ (D , α , refl)
    | C.cast-seal hD α∈Σ ok =
  ⊥-elim
    (source-variable-ground-impossible exclusive
      outer-index requested ground)


source-inert-widening-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B H} →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-widening-route
    (G C.!) (C.cast-tag hG gG ok , NW.tag gG′)
    inner-index requested ground =
  ⊥-elim (star-ground-impossible requested ground)
source-inert-widening-route
    (s C.↦ t)
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ))
    inner-index requested T.★⇒★ =
  gen-safe-shape-star-to-function
    shape-fun inner-index ,
  refl
source-inert-widening-route
    (C.`∀ c) (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
    inner-index requested ground =
  gen-safe-shape-star-to-function
    shape-all inner-index ,
  gen-safe-shape-ground-function
    shape-all requested ground
source-inert-widening-route
    (C.seal A α) (c⊢ , NW.cross ())
    inner-index requested ground
source-inert-widening-route
    (C.gen A c) (c⊢ , NW.cross ())
    inner-index requested ground


source-inert-widening-ground-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ c A B G H} →
  C.Inert c →
  μ ∣ Δᴸ ∣ Σ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ →
  T.Ground G →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  G ≡ T.★ T.⇒ T.★ × H ≡ T.★ T.⇒ T.★
source-inert-widening-ground-route
    (G₀ C.!) (C.cast-tag hG₀ gG₀ ok , NW.tag gG₀′)
    inner groundG requested groundH =
  ⊥-elim (star-ground-impossible requested groundH)
source-inert-widening-ground-route
    (s C.↦ t)
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ))
    inner T.★⇒★ requested T.★⇒★ =
  refl , refl
source-inert-widening-ground-route
    (C.`∀ c) (C.cast-all c⊢ , NW.cross (NW.`∀ cʷ))
    inner groundG requested groundH =
  gen-safe-shape-ground-function shape-all inner groundG ,
  gen-safe-shape-ground-function shape-all requested groundH
source-inert-widening-ground-route
    (C.seal A α) (c⊢ , NW.cross ())
    inner groundG requested groundH
source-inert-widening-ground-route
    (C.gen A c) (c⊢ , NW.cross ())
    inner groundG requested groundH


source-inert-reveal-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ α X c A B H} →
  C.Inert c →
  CV.RevealConversion μ Δᴸ Σ α X c A B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-reveal-route () (CV.reveal-id-var hY ok)
    inner requested ground
source-inert-reveal-route () CV.reveal-id-base
    inner requested ground
source-inert-reveal-route () CV.reveal-id-★
    inner requested ground
source-inert-reveal-route () (CV.reveal-unseal hX α∈Σ ok)
    inner requested ground
source-inert-reveal-route (s C.↦ t) (CV.reveal-fun s↓ t↑)
    inner requested T.★⇒★ =
  gen-safe-shape-star-to-function shape-fun inner , refl
source-inert-reveal-route (C.`∀ c) (CV.reveal-all c↑)
    inner requested ground =
  gen-safe-shape-star-to-function shape-all inner ,
  gen-safe-shape-ground-function shape-all requested ground


source-inert-conceal-route :
  ∀ {Φ Δᴸ Δᴿ μ Σ α X c A B H} →
  (∀ {β γ} →
    (β ˣ⊑★) ∈ Φ →
    (β ˣ⊑ˣ γ) ∈ Φ →
    ⊥) →
  C.Inert c →
  CV.ConcealConversion μ Δᴸ Σ α X c A B →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
  T.Ground H →
  (Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) ×
  H ≡ T.★ T.⇒ T.★
source-inert-conceal-route exclusive ()
    (CV.conceal-id-var hY ok) inner outer requested ground
source-inert-conceal-route exclusive () CV.conceal-id-base
    inner outer requested ground
source-inert-conceal-route exclusive () CV.conceal-id-★
    inner outer requested ground
source-inert-conceal-route exclusive
    (C.seal X α) (CV.conceal-seal hX α∈Σ ok)
    inner outer requested ground =
  ⊥-elim
    (source-variable-ground-impossible exclusive
      outer requested ground)
source-inert-conceal-route exclusive
    (s C.↦ t) (CV.conceal-fun s↑ t↓)
    inner outer requested T.★⇒★ =
  gen-safe-shape-star-to-function shape-fun inner , refl
source-inert-conceal-route exclusive
    (C.`∀ c) (CV.conceal-all c↓)
    inner outer requested ground =
  gen-safe-shape-star-to-function shape-all inner ,
  gen-safe-shape-ground-function shape-all requested ground


cast-coercion-injective :
  ∀ {M M′ : Term} {c c′ : C.Coercion} →
  M ⟨ c ⟩ ≡ M′ ⟨ c′ ⟩ →
  c ≡ c′
cast-coercion-injective refl = refl


inst-inert-target-tag-impossible :
  ∀ {σ B s G} →
  NW.Widening (C.inst B s) →
  C.Inert s →
  C.renameᶜ σ s ≡ G C.! →
  ⊥
inst-inert-target-tag-impossible (NW.inst ()) (G C.!) eq
inst-inert-target-tag-impossible (NW.inst ())
    (C.seal A α) eq
inst-inert-target-tag-impossible (NW.inst safe)
    (c C.↦ d) ()
inst-inert-target-tag-impossible (NW.inst safe)
    (C.`∀ c) ()
inst-inert-target-tag-impossible (NW.inst ())
    (C.gen A c) eq


target-tag-cancellation-proofᵀ : TargetTagCancellationᵀ
target-tag-cancellation-proofᵀ
    {p = ν safe-old occ-old inner-index}
    exclusive unique gH (Value.Λ vBody) (no•-Λ noBody) vW
    (Λ⊑ᵀ .occ-old liftρ lift-left-ctx-[] vBody′ inner)
    (ν safe-new occ-new requested-inner)
    with target-tag-cancellation-proofᵀ
      (source-name-exclusive-source-only-head exclusive)
      (assumption-membership-unique-source unique)
      gH vBody noBody vW inner requested-inner
target-tag-cancellation-proofᵀ
    {p = ν safe-old occ-old inner-index}
    exclusive unique gH (Value.Λ vBody) (no•-Λ noBody) vW
    (Λ⊑ᵀ .occ-old liftρ lift-left-ctx-[] vBody′ inner)
    (ν safe-new occ-new requested-inner)
    | observed-eq , canceled =
  observed-eq ,
  Λ⊑ᵀ {{safe = safe-new}} occ-new
    liftρ lift-left-ctx-[] vBody canceled
target-tag-cancellation-proofᵀ exclusive unique gH
    (Value.Λ vBody) (no•-Λ noBody) vW
    (Λ⊑instβᵀ
      prefix mode seal★ (inst-typing , widening)
      liftρ liftρᴿ vBody₀ noBody₀ vBody′ noBody′ inert body f
      assm hτ hσ store-emb
      source-eq target-eq source-type-eq target-type-eq
      outer-index final-v final-no final-closed
      final-v′ final-no′ final-closed′
      source-typing target-typing)
    requested =
  ⊥-elim
    (inst-inert-target-tag-impossible widening inert
      (cast-coercion-injective target-eq))
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊒⊑ᵀ {p = inner-index} mode seal★ c⊒
      inner outer-index)
    requested
    with source-inert-narrowing-route exclusive inert c⊒
      inner-index outer-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊒⊑ᵀ {p = inner-index} mode seal★ c⊒
      inner outer-index)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊒⊑ᵀ {p = inner-index} mode seal★ c⊒
      inner outer-index)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  cast⊒⊑ᵀ mode seal★ c⊒ canceled requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊑⊑ᵀ {p = inner-index} mode seal★ c⊑
      inner outer-index)
    requested
    with source-inert-widening-route inert c⊑
      inner-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊑⊑ᵀ {p = inner-index} mode seal★ c⊑
      inner outer-index)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (cast⊑⊑ᵀ {p = inner-index} mode seal★ c⊑
      inner outer-index)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  cast⊑⊑ᵀ mode seal★ c⊑ canceled requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↑⊑ᵀ {p = inner-index} reveal inner outer-index)
    requested
    with source-inert-reveal-route inert reveal
      inner-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↑⊑ᵀ {p = inner-index} reveal inner outer-index)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↑⊑ᵀ {p = inner-index} reveal inner outer-index)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  conv↑⊑ᵀ reveal canceled requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↓⊑ᵀ {p = inner-index} conceal inner outer-index)
    requested
    with source-inert-conceal-route exclusive inert conceal
      inner-index outer-index requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↓⊑ᵀ {p = inner-index} conceal inner outer-index)
    requested | function-index , refl
    with target-tag-cancellation-proofᵀ exclusive unique
      T.★⇒★ vM noM vW inner function-index
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv↓⊑ᵀ {p = inner-index} conceal inner outer-index)
    requested | function-index , refl
    | observed-eq , canceled =
  observed-eq ,
  conv↓⊑ᵀ conceal canceled requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊒ᵀ mode seal★
      (C.cast-tag hG gG ok , NW.cross ()) inner old-index)
    requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑idᵀ {p = inner-index} seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index)
    requested
    with target-ground-unique exclusive old-index
      inner-index requested gG gH
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑idᵀ {p = inner-index} seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index)
    requested | refl
    with assumption-membership-unique→precision-index-unique unique
      inner-index requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑idᵀ {p = inner-index} seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index)
    requested | refl | refl =
  refl , inner
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv⊑convᵀ
      (paired-conversion (paired-reveal corr reveal ())) inner)
    requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv⊑convᵀ
      (paired-conversion (paired-conceal corr conceal ())) inner)
    requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv⊑convᵀ {p = inner-index}
      (paired-widening mode seal★ c⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′) compat)
      inner)
    requested
    with source-inert-widening-ground-route inert c⊑
      inner-index gG requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) vW
    (conv⊑convᵀ {p = inner-index}
      (paired-widening mode seal★ c⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′) compat)
      inner)
    requested | refl , refl =
  refl ,
  cast⊑⊑ᵀ mode seal★ c⊑ inner requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (up⊑upᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index)
    requested
    with target-ground-value-quotient-eliminationᵀ
      gG vN vW quotient
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (up⊑upᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index)
    requested | ordinary-index , ordinary
    with source-inert-widening-ground-route inert u⊑
      ordinary-index gG requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (up⊑upᵀ quotient
      (quotient-id-widening u⊑
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index)
    requested | ordinary-index , ordinary | refl , refl =
  refl ,
  cast⊑⊑ᵀ cast-tag-or-id seal★-tag-or-id
    (NW.widen-mode-relax C.id-only≤tag-or-idᵈ u⊑)
    ordinary requested
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (up⊑upᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index)
    requested
    with target-ground-value-quotient-eliminationᵀ
      gG vN vW quotient
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (up⊑upᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index)
    requested | ordinary-index , ordinary
    with source-inert-widening-ground-route inert u⊑
      ordinary-index gG requested gH
target-tag-cancellation-proofᵀ exclusive unique gH
    (vN ⟨ inert ⟩) (no•-⟨⟩ noN) vW
    (up⊑upᵀ quotient
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′
        (C.cast-tag hG gG ok , NW.tag gG′))
      outer-index)
    requested | ordinary-index , ordinary | refl , refl =
  refl ,
  cast⊑⊑ᵀ mode seal★ u⊑ ordinary requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (allocation-prefixᵀ prefix inner V⊢ Wtag⊢) requested
    with target-tag-cancellation-proofᵀ exclusive unique
      gH vV noV vW inner requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (allocation-prefixᵀ prefix inner V⊢ Wtag⊢) requested
    | refl , canceled =
  refl ,
  allocation-prefixᵀ prefix canceled V⊢
    (target-tag-typing⁻¹ Wtag⊢)
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index)
    requested
    with target-ground-unique exclusive old-index
      inner-index requested gG gH
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index)
    requested | refl
    with assumption-membership-unique→precision-index-unique unique
      inner-index requested
target-tag-cancellation-proofᵀ exclusive unique gH vV noV vW
    (⊑cast⊑ᵀ {p = inner-index} mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) inner old-index)
    requested | refl | refl =
  refl , inner

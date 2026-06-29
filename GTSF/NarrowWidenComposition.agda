{-# OPTIONS --warning=noUnreachableClauses #-}

-- File Charter:
--   * Public composition operators for well-typed narrowings and widenings.
--   * Exposes term-narrowing side conditions for narrowing composition.
--   * Depends on `NarrowWiden` plus proof-only exclusion lemmas needed for
--     coverage under the `StoreDetWf` invariant.
--   * The positive strict grammar needs explicit indexed-impossible coverage
--     clauses for tag/unseal composition; Agda also reports those clauses as
--     unreachable, so this module locally disables that warning.

module NarrowWidenComposition where

open import Data.Bool using (true)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import Types
open import Store using (StoreIncl-drop)
open import Coercions
open import NarrowWiden
open import proof.NarrowWidenProperties
  using
    ( StoreDetWf
    ; StoreDetWf-⟰ᵗ
    ; StoreDetWf-inst
    ; narrowing-cross-ground-target-star⊥
    ; widening-cross-ground-source-star⊥
    )

narrowing-cross-var-source-fun⊥ :
  ∀ {μ Δ Σ α C s t} →
  μ ∣ Δ ∣ Σ ⊢ s ↦ t ∶ ＇ α =⇒ C →
  CrossNarrowing (s ↦ t) →
  ⊥
narrowing-cross-var-source-fun⊥ ()

narrowing-cross-var-source-all⊥ :
  ∀ {μ Δ Σ α C s} →
  μ ∣ Δ ∣ Σ ⊢ `∀ s ∶ ＇ α =⇒ C →
  CrossNarrowing (`∀ s) →
  ⊥
narrowing-cross-var-source-all⊥ ()

widening-cross-star-source-fun⊥ :
  ∀ {μ Δ Σ C s t} →
  μ ∣ Δ ∣ Σ ⊢ s ↦ t ∶ ★ =⇒ C →
  CrossWidening (s ↦ t) →
  ⊥
widening-cross-star-source-fun⊥ ()

widening-cross-star-source-all⊥ :
  ∀ {μ Δ Σ C s} →
  μ ∣ Δ ∣ Σ ⊢ `∀ s ∶ ★ =⇒ C →
  CrossWidening (`∀ s) →
  ⊥
widening-cross-star-source-all⊥ ()

widening-inst-star-source⊥ :
  ∀ {μ Δ Σ B C s} →
  μ ∣ Δ ∣ Σ ⊢ inst B s ∶ ★ =⇒ C →
  Widening (inst B s) →
  ⊥
widening-inst-star-source⊥ ()

narrowing-cross-target-star⊥ :
  ∀ {μ Δ Σ A s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ ★ →
  CrossNarrowing s →
  ⊥
narrowing-cross-target-star⊥ () (id-＇ α)
narrowing-cross-target-star⊥ () (id-‵ ι)
narrowing-cross-target-star⊥ () (sʷ ↦ tⁿ)
narrowing-cross-target-star⊥ () (`∀ sⁿ)

------------------------------------------------------------------------
-- Identity/strict views for the positive grammar
------------------------------------------------------------------------

mutual
  data IdCrossNarrowing : Coercion → Set where
    idcn-＇ : (α : TyVar) →
      IdCrossNarrowing (id (＇ α))

    idcn-‵ : (ι : Base) →
      IdCrossNarrowing (id (‵ ι))

    idcn-fun : ∀ {s t} →
      IdWidening s →
      IdNarrowing t →
      IdCrossNarrowing (s ↦ t)

    idcn-all : ∀ {s} →
      IdNarrowing s →
      IdCrossNarrowing (`∀ s)

  data IdNarrowing : Coercion → Set where
    idn-cross : ∀ {g} →
      IdCrossNarrowing g →
      IdNarrowing g

    idn-★ :
      IdNarrowing (id ★)

  data IdCrossWidening : Coercion → Set where
    idcw-＇ : (α : TyVar) →
      IdCrossWidening (id (＇ α))

    idcw-‵ : (ι : Base) →
      IdCrossWidening (id (‵ ι))

    idcw-fun : ∀ {s t} →
      IdNarrowing s →
      IdWidening t →
      IdCrossWidening (s ↦ t)

    idcw-all : ∀ {s} →
      IdWidening s →
      IdCrossWidening (`∀ s)

  data IdWidening : Coercion → Set where
    idw-cross : ∀ {g} →
      IdCrossWidening g →
      IdWidening g

    idw-★ :
      IdWidening (id ★)

mutual
  narrowing-view :
    ∀ {c} →
    Narrowing c →
    StrictNarrowing c ⊎ IdNarrowing c
  narrowing-view (cross cⁿ) with cross-narrowing-view cⁿ
  narrowing-view (cross cⁿ) | inj₁ cˢ =
    inj₁ (strict-crossⁿ cˢ)
  narrowing-view (cross cⁿ) | inj₂ cⁱ =
    inj₂ (idn-cross cⁱ)
  narrowing-view id★ = inj₂ idn-★
  narrowing-view (gen cⁿ) = inj₁ (strict-gen cⁿ)
  narrowing-view (untag gG) = inj₁ (strict-untag gG)
  narrowing-view (gG ？︔ cˢ) = inj₁ (strict-untag-seq gG cˢ)
  narrowing-view (sealⁿ A α) = inj₁ (strict-seal A α)
  narrowing-view (cˢ ︔seal α) = inj₁ (strict-seal-seq cˢ α)

  cross-narrowing-view :
    ∀ {c} →
    CrossNarrowing c →
    StrictCrossNarrowing c ⊎ IdCrossNarrowing c
  cross-narrowing-view (id-＇ α) =
    inj₂ (idcn-＇ α)
  cross-narrowing-view (id-‵ ι) =
    inj₂ (idcn-‵ ι)
  cross-narrowing-view (sʷ ↦ tⁿ) with widening-view sʷ | narrowing-view tⁿ
  cross-narrowing-view (sʷ ↦ tⁿ) | inj₁ sˢ | _ =
    inj₁ (cn-funˡ sˢ tⁿ)
  cross-narrowing-view (sʷ ↦ tⁿ) | inj₂ sⁱ | inj₁ tˢ =
    inj₁ (cn-funʳ sʷ tˢ)
  cross-narrowing-view (sʷ ↦ tⁿ) | inj₂ sⁱ | inj₂ tⁱ =
    inj₂ (idcn-fun sⁱ tⁱ)
  cross-narrowing-view (`∀ cⁿ) with narrowing-view cⁿ
  cross-narrowing-view (`∀ cⁿ) | inj₁ cˢ =
    inj₁ (cn-all cˢ)
  cross-narrowing-view (`∀ cⁿ) | inj₂ cⁱ =
    inj₂ (idcn-all cⁱ)

  widening-view :
    ∀ {c} →
    Widening c →
    StrictWidening c ⊎ IdWidening c
  widening-view (cross cʷ) with cross-widening-view cʷ
  widening-view (cross cʷ) | inj₁ cˢ =
    inj₁ (strict-crossʷ cˢ)
  widening-view (cross cʷ) | inj₂ cⁱ =
    inj₂ (idw-cross cⁱ)
  widening-view id★ = inj₂ idw-★
  widening-view (inst cʷ) = inj₁ (strict-inst cʷ)
  widening-view (tag gG) = inj₁ (strict-tag gG)
  widening-view (cˢ ︔ gG !) = inj₁ (strict-tag-seq cˢ gG)
  widening-view (unsealʷ α A) = inj₁ (strict-unseal α A)
  widening-view (unseal︔_ α cˢ) = inj₁ (strict-unseal-seq α cˢ)

  cross-widening-view :
    ∀ {c} →
    CrossWidening c →
    StrictCrossWidening c ⊎ IdCrossWidening c
  cross-widening-view (id-＇ α) =
    inj₂ (idcw-＇ α)
  cross-widening-view (id-‵ ι) =
    inj₂ (idcw-‵ ι)
  cross-widening-view (sⁿ ↦ tʷ) with narrowing-view sⁿ | widening-view tʷ
  cross-widening-view (sⁿ ↦ tʷ) | inj₁ sˢ | _ =
    inj₁ (cw-funˡ sˢ tʷ)
  cross-widening-view (sⁿ ↦ tʷ) | inj₂ sⁱ | inj₁ tˢ =
    inj₁ (cw-funʳ sⁿ tˢ)
  cross-widening-view (sⁿ ↦ tʷ) | inj₂ sⁱ | inj₂ tⁱ =
    inj₂ (idcw-fun sⁱ tⁱ)
  cross-widening-view (`∀ cʷ) with widening-view cʷ
  cross-widening-view (`∀ cʷ) | inj₁ cˢ =
    inj₁ (cw-all cˢ)
  cross-widening-view (`∀ cʷ) | inj₂ cⁱ =
    inj₂ (idcw-all cⁱ)

mutual
  id-narrowing-src≡tgt :
    ∀ {μ Δ Σ A B c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    IdNarrowing c →
    A ≡ B
  id-narrowing-src≡tgt c⊢ (idn-cross cⁱ) =
    id-cross-narrowing-src≡tgt c⊢ cⁱ
  id-narrowing-src≡tgt (cast-id hA ok) idn-★ = refl

  id-cross-narrowing-src≡tgt :
    ∀ {μ Δ Σ A B c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    IdCrossNarrowing c →
    A ≡ B
  id-cross-narrowing-src≡tgt (cast-id hA ok) (idcn-＇ α) = refl
  id-cross-narrowing-src≡tgt (cast-id hA ok) (idcn-‵ ι) = refl
  id-cross-narrowing-src≡tgt (cast-fun s⊢ t⊢) (idcn-fun sⁱ tⁱ) =
    cong₂ _⇒_
      (sym (id-widening-src≡tgt s⊢ sⁱ))
      (id-narrowing-src≡tgt t⊢ tⁱ)
  id-cross-narrowing-src≡tgt (cast-all c⊢) (idcn-all cⁱ) =
    cong `∀ (id-narrowing-src≡tgt c⊢ cⁱ)

  id-widening-src≡tgt :
    ∀ {μ Δ Σ A B c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    IdWidening c →
    A ≡ B
  id-widening-src≡tgt c⊢ (idw-cross cⁱ) =
    id-cross-widening-src≡tgt c⊢ cⁱ
  id-widening-src≡tgt (cast-id hA ok) idw-★ = refl

  id-cross-widening-src≡tgt :
    ∀ {μ Δ Σ A B c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    IdCrossWidening c →
    A ≡ B
  id-cross-widening-src≡tgt (cast-id hA ok) (idcw-＇ α) = refl
  id-cross-widening-src≡tgt (cast-id hA ok) (idcw-‵ ι) = refl
  id-cross-widening-src≡tgt (cast-fun s⊢ t⊢) (idcw-fun sⁱ tⁱ) =
    cong₂ _⇒_
      (sym (id-narrowing-src≡tgt s⊢ sⁱ))
      (id-widening-src≡tgt t⊢ tⁱ)
  id-cross-widening-src≡tgt (cast-all c⊢) (idcw-all cⁱ) =
    cong `∀ (id-widening-src≡tgt c⊢ cⁱ)

wrap-untagⁿ :
  ∀ {μ Δ Σ G C c} →
  WfTy Δ G →
  (gG : Ground G) →
  tagTyAllowed μ G ≡ true →
  μ ∣ Δ ∣ Σ ⊢ᶜ c ∶ G ⊒ C →
  ∃[ u ] μ ∣ Δ ∣ Σ ⊢ u ∶ ★ ⊒ C
wrap-untagⁿ hG gG okG (c⊢ , cⁿ) with cross-narrowing-view cⁿ
wrap-untagⁿ hG gG okG (c⊢ , cⁿ) | inj₁ cˢ =
  _ , (cast-seq (cast-untag hG gG okG) c⊢ , gG ？︔ cˢ)
wrap-untagⁿ hG gG okG (c⊢ , cⁿ) | inj₂ cⁱ
    with id-cross-narrowing-src≡tgt c⊢ cⁱ
wrap-untagⁿ hG gG okG (c⊢ , cⁿ) | inj₂ cⁱ | refl =
  _ , (cast-untag hG gG okG , untag gG)

wrap-sealⁿ :
  ∀ {μ Δ Σ A B α c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  WfTy Δ B →
  (α , B) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  ∃[ u ] μ ∣ Δ ∣ Σ ⊢ u ∶ A ⊒ ＇ α
wrap-sealⁿ (c⊢ , cⁿ) hB α∈Σ ok with narrowing-view cⁿ
wrap-sealⁿ (c⊢ , cⁿ) hB α∈Σ ok | inj₁ cˢ =
  _ , (cast-seq c⊢ (cast-seal hB α∈Σ ok) , cˢ ︔seal _)
wrap-sealⁿ (c⊢ , cⁿ) hB α∈Σ ok | inj₂ cⁱ
    with id-narrowing-src≡tgt c⊢ cⁱ
wrap-sealⁿ (c⊢ , cⁿ) hB α∈Σ ok | inj₂ cⁱ | refl =
  _ , (cast-seal hB α∈Σ ok , sealⁿ _ _)

wrap-tagʷ :
  ∀ {μ Δ Σ A G c} →
  μ ∣ Δ ∣ Σ ⊢ᶜ c ∶ A ⊑ G →
  WfTy Δ G →
  (gG : Ground G) →
  tagTyAllowed μ G ≡ true →
  ∃[ u ] μ ∣ Δ ∣ Σ ⊢ u ∶ A ⊑ ★
wrap-tagʷ (c⊢ , cʷ) hG gG okG with cross-widening-view cʷ
wrap-tagʷ (c⊢ , cʷ) hG gG okG | inj₁ cˢ =
  _ , (cast-seq c⊢ (cast-tag hG gG okG) , cˢ ︔ gG !)
wrap-tagʷ (c⊢ , cʷ) hG gG okG | inj₂ cⁱ
    with id-cross-widening-src≡tgt c⊢ cⁱ
wrap-tagʷ (c⊢ , cʷ) hG gG okG | inj₂ cⁱ | refl =
  _ , (cast-tag hG gG okG , tag gG)

wrap-unsealʷ :
  ∀ {μ Δ Σ A B α c} →
  WfTy Δ A →
  (α , A) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  ∃[ u ] μ ∣ Δ ∣ Σ ⊢ u ∶ ＇ α ⊑ B
wrap-unsealʷ hA α∈Σ ok (c⊢ , cʷ) with widening-view cʷ
wrap-unsealʷ hA α∈Σ ok (c⊢ , cʷ) | inj₁ cˢ =
  _ , (cast-seq (cast-unseal hA α∈Σ ok) c⊢ , unseal︔_ _ cˢ)
wrap-unsealʷ hA α∈Σ ok (c⊢ , cʷ) | inj₂ cⁱ
    with id-widening-src≡tgt c⊢ cⁱ
wrap-unsealʷ hA α∈Σ ok (c⊢ , cʷ) | inj₂ cⁱ | refl =
  _ , (cast-unseal hA α∈Σ ok , unsealʷ _ _)

------------------------------------------------------------------------
-- Composition for narrowing and widening
------------------------------------------------------------------------

infixl 7 _⨟ⁿ_
infixl 7 _⨟ʷ_
infixl 7 _⨟ᶜⁿ_
infixl 7 _⨟ᶜʷ_

{-# TERMINATING #-}
mutual
  _⨟ⁿ_ :
    ∀ {μ Δ Σ A B C s t} →
    {wfΣ : StoreDetWf Δ Σ} →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊒ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ B ⊒ C →
    ∃[ u ] μ ∣ Δ ∣ Σ ⊢ u ∶ A ⊒ C
  _⨟ⁿ_ {wfΣ = wfΣ} s⊒ (cast-id hB ok , id★) = _ , s⊒
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★) (cast-id hB okB , cross ())
  _⨟ⁿ_ {wfΣ = wfΣ} (s⊢ , cross sⁿ) (t⊢ , cross tⁿ)
      with _⨟ᶜⁿ_ {wfΣ = wfΣ} (s⊢ , sⁿ) (t⊢ , tⁿ)
  _⨟ⁿ_ {wfΣ = wfΣ} (s⊢ , cross sⁿ) (t⊢ , cross tⁿ)
      | u , u⊒ =
    u , (proj₁ u⊒ , cross (proj₂ u⊒))
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★)
      (cast-untag hG gG okG , untag gG′) =
    _ , (cast-untag hG gG okG , untag gG′)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-untag hG gG okG , untag gG′)
      (t⊢ , cross tᶜ) =
    wrap-untagⁿ hG gG okG (t⊢ , tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-untag hG () okG , untag gG′)
      (cast-untag hH gH okH , untag gH′)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (s⊢ , cross sᶜ)
      (cast-untag hG gG okG , untag gG′) =
    ⊥-elim (narrowing-cross-target-star⊥ s⊢ sᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (s⊢ , cross sᶜ)
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ) =
    ⊥-elim (narrowing-cross-target-star⊥ s⊢ sᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-untag hG () okG , untag gG′)
      (cast-seq (cast-untag hH gH okH) t⊢ , hG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★)
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ) =
    _ , (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (t⊢ , cross tᶜ)
      with _⨟ᶜⁿ_ {wfΣ = wfΣ}
             (s⊢ , strictCrossⁿ→cross sᶜ) (t⊢ , tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (t⊢ , cross tᶜ) | u , u⊒ =
    wrap-untagⁿ hG gG okG u⊒
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (cast-untag hH gH okH , untag gH′) =
    ⊥-elim
      (narrowing-cross-ground-target-star⊥ gG
        (s⊢ , strictCrossⁿ→cross sᶜ))
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , hG′ ？︔ tᶜ) =
    ⊥-elim
      (narrowing-cross-ground-target-star⊥ gG
        (s⊢ , strictCrossⁿ→cross sᶜ))
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seal hA α∈Σ ok , sealⁿ A α)
      (cast-id hB okB , cross (id-＇ β)) =
    _ , (cast-seal hA α∈Σ ok , sealⁿ A α)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seal hA α∈Σ ok , sealⁿ A α)
      (cast-seq () t⊢ , hG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq s⊢ (cast-seal hA α∈Σ ok) , _︔seal_ sⁿ α)
      (cast-id hB okB , cross (id-＇ β)) =
    _ , (cast-seq s⊢ (cast-seal hA α∈Σ ok) , sⁿ ︔seal α)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq s⊢ (cast-seal hA α∈Σ ok) , _︔seal_ sⁿ α)
      (cast-seq () t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (s⊢ , _︔seal_ sⁿ α)
      (t⊢ , cross (sʷ ↦ tⁿ))
      with s⊢
  _⨟ⁿ_ {wfΣ = wfΣ}
      (s⊢ , _︔seal_ sⁿ α)
      (t⊢ , cross (sʷ ↦ tⁿ))
      | cast-seq s⊢′ (cast-seal hA α∈Σ ok) =
    ⊥-elim (narrowing-cross-var-source-fun⊥ t⊢ (sʷ ↦ tⁿ))
  _⨟ⁿ_ {wfΣ = wfΣ}
      (s⊢ , _︔seal_ sⁿ α)
      (t⊢ , cross (`∀ tⁿ))
      with s⊢
  _⨟ⁿ_ {wfΣ = wfΣ}
      (s⊢ , _︔seal_ sⁿ α)
      (t⊢ , cross (`∀ tⁿ))
      | cast-seq s⊢′ (cast-seal hA α∈Σ ok) =
    ⊥-elim (narrowing-cross-var-source-all⊥ t⊢ (`∀ tⁿ))
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-gen hA occ s⊢ , gen sⁿ)
      (cast-id hB okB , cross ())
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-gen hA occ s⊢ , gen sⁿ)
      (cast-seq () t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-gen hA occ s⊢ , gen sⁿ)
      (cast-all t⊢ , cross (`∀ tⁿ))
      with _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ}
             (s⊢ , sⁿ)
             (narrow-mode-relax modeIncl-ext-gen (t⊢ , tⁿ))
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-gen hA occ s⊢ , gen sⁿ)
      (cast-all t⊢ , cross (`∀ tⁿ)) | u , u⊒ =
    _ , (cast-gen hA
           (narrowing-source-occurs StoreNoOccurs-zero-⟰ᵗ
             (t⊢ , tⁿ) occ)
           (proj₁ u⊒) ,
         gen (proj₂ u⊒))
  _⨟ⁿ_ {wfΣ = wfΣ} s⊒ (cast-gen hB occ t⊢ , gen tⁿ)
      with _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ}
             (narrow-⇑ᵗ-gen s⊒) (t⊢ , tⁿ)
  _⨟ⁿ_ {wfΣ = wfΣ} s⊒ (cast-gen hB occ t⊢ , gen tⁿ)
      | u , u⊒ =
    _ , (cast-gen (narrow-src-wf s⊒) occ (proj₁ u⊒) ,
         gen (proj₂ u⊒))
  _⨟ⁿ_ {wfΣ = wfΣ}
      s⊒ (cast-seal hC α∈Σ ok , sealⁿ A α) =
    wrap-sealⁿ s⊒ hC α∈Σ ok
  _⨟ⁿ_ {wfΣ = wfΣ}
      s⊒ (cast-seq t⊢ (cast-seal hC α∈Σ ok) , _︔seal_ tⁿ α)
      with _⨟ⁿ_ {wfΣ = wfΣ} s⊒ (t⊢ , strictⁿ→narrow tⁿ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      s⊒ (cast-seq t⊢ (cast-seal hC α∈Σ ok) ,
      _︔seal_ tⁿ α) | u , u⊒ =
    wrap-sealⁿ u⊒ hC α∈Σ ok

  _⨟ᶜⁿ_ :
    ∀ {μ Δ Σ A B C s t} →
    {wfΣ : StoreDetWf Δ Σ} →
    μ ∣ Δ ∣ Σ ⊢ᶜ s ∶ A ⊒ B →
    μ ∣ Δ ∣ Σ ⊢ᶜ t ∶ B ⊒ C →
    ∃[ u ] μ ∣ Δ ∣ Σ ⊢ᶜ u ∶ A ⊒ C
  _⨟ᶜⁿ_ {wfΣ = wfΣ}
      (cast-id hA ok , id-＇ α) (cast-id hB okB , id-＇ β) =
    _ , (cast-id hA ok , id-＇ α)
  _⨟ᶜⁿ_ {wfΣ = wfΣ}
      (cast-id hA ok , id-‵ ι) (cast-id hB okB , id-‵ ι′) =
    _ , (cast-id hA ok , id-‵ ι)
  _⨟ᶜⁿ_ {wfΣ = wfΣ}
      (cast-fun s⊢ t⊢ , sʷ ↦ tⁿ)
      (cast-fun s⊢′ t⊢′ , sʷ′ ↦ tⁿ′)
      with _⨟ʷ_ {wfΣ = wfΣ} (s⊢′ , sʷ′) (s⊢ , sʷ)
         | _⨟ⁿ_ {wfΣ = wfΣ} (t⊢ , tⁿ) (t⊢′ , tⁿ′)
  _⨟ᶜⁿ_ {wfΣ = wfΣ}
      (cast-fun s⊢ t⊢ , sʷ ↦ tⁿ)
      (cast-fun s⊢′ t⊢′ , sʷ′ ↦ tⁿ′) | u , u⊑ | v , v⊒ =
    _ , (cast-fun (proj₁ u⊑) (proj₁ v⊒) ,
         proj₂ u⊑ ↦ proj₂ v⊒)
  _⨟ᶜⁿ_ {wfΣ = wfΣ}
      (cast-all s⊢ , `∀ sⁿ) (cast-all t⊢ , `∀ tⁿ)
      with _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} (s⊢ , sⁿ) (t⊢ , tⁿ)
  _⨟ᶜⁿ_ {wfΣ = wfΣ}
      (cast-all s⊢ , `∀ sⁿ) (cast-all t⊢ , `∀ tⁿ) | u , u⊒ =
    _ , (cast-all (proj₁ u⊒) , `∀ (proj₂ u⊒))

  _⨟ʷ_ :
    ∀ {μ Δ Σ A B C s t} →
    {wfΣ : StoreDetWf Δ Σ} →
    μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B →
    μ ∣ Δ ∣ Σ ⊢ t ∶ B ⊑ C →
    ∃[ u ] μ ∣ Δ ∣ Σ ⊢ u ∶ A ⊑ C
  _⨟ʷ_ {wfΣ = wfΣ} s⊑ (cast-id hB ok , id★) = _ , s⊑
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★) (cast-id hB okB , cross ())
  _⨟ʷ_ {wfΣ = wfΣ} (s⊢ , cross sʷ) (t⊢ , cross tʷ)
      with _⨟ᶜʷ_ {wfΣ = wfΣ} (s⊢ , sʷ) (t⊢ , tʷ)
  _⨟ʷ_ {wfΣ = wfΣ} (s⊢ , cross sʷ) (t⊢ , cross tʷ)
      | u , u⊑ =
    u , (proj₁ u⊑ , cross (proj₂ u⊑))
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross sᶜ)
      (cast-tag hG gG okG , tag gG′) =
    wrap-tagʷ (s⊢ , sᶜ) hG gG okG
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★)
      (cast-tag hG () okG , tag gG′)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-tag hG gG okG , tag gG′)
      (t⊢ , cross (sⁿ ↦ tʷ)) =
    ⊥-elim (widening-cross-star-source-fun⊥ t⊢ (sⁿ ↦ tʷ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-tag hG gG okG , tag gG′)
      (t⊢ , cross (`∀ tʷ)) =
    ⊥-elim (widening-cross-star-source-all⊥ t⊢ (`∀ tʷ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-tag hG gG okG , tag gG′)
      (t⊢ , inst tʷ) =
    ⊥-elim (widening-inst-star-source⊥ t⊢ (inst tʷ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-tag hG gG okG , tag gG′)
      (cast-seq t⊢ (cast-tag hH gH okH) , tᶜ ︔ hG′ !) =
    ⊥-elim
      (widening-cross-ground-source-star⊥ gH
        (t⊢ , strictCrossʷ→cross tᶜ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-tag hG gG okG , tag gG′)
      (cast-tag hH () okH , tag hG′)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq s⊢ (cast-tag hG gG okG) , sᶜ ︔ gG′ !)
      (cast-tag hH () okH , tag hG′)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★)
      (cast-seq t⊢ (cast-tag hG gG okG) , tᶜ ︔ gG′ !) =
    _ , (cast-seq t⊢ (cast-tag hG gG okG) , tᶜ ︔ gG′ !)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq s⊢ (cast-tag hG gG okG) , sᶜ ︔ gG′ !)
      (cast-id hB okB , cross ())
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , sᶜ ︔ gG !)
      (t⊢ , cross (sⁿ ↦ tʷ))
      with s⊢
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , sᶜ ︔ gG !)
      (t⊢ , cross (sⁿ ↦ tʷ))
      | cast-seq s⊢′ (cast-tag hG gG′ okG) =
    ⊥-elim (widening-cross-star-source-fun⊥ t⊢ (sⁿ ↦ tʷ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , sᶜ ︔ gG !)
      (t⊢ , cross (`∀ tʷ))
      with s⊢
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , sᶜ ︔ gG !)
      (t⊢ , cross (`∀ tʷ))
      | cast-seq s⊢′ (cast-tag hG gG′ okG) =
    ⊥-elim (widening-cross-star-source-all⊥ t⊢ (`∀ tʷ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , sᶜ ︔ gG !)
      (t⊢ , inst tʷ)
      with s⊢
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , sᶜ ︔ gG !)
      (t⊢ , inst tʷ)
      | cast-seq s⊢′ (cast-tag hG gG′ okG) =
    ⊥-elim (widening-inst-star-source⊥ t⊢ (inst tʷ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq s⊢ (cast-tag hG gG okG) , sᶜ ︔ gG′ !)
      (cast-seq t⊢ (cast-tag hH gH okH) , tᶜ ︔ hG′ !) =
    ⊥-elim
      (widening-cross-ground-source-star⊥ gH
        (t⊢ , strictCrossʷ→cross tᶜ))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , cross (id-＇ α))
      (cast-unseal hB β∈Σ β-ok , unsealʷ β B) =
    _ , (cast-unseal hB β∈Σ β-ok , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , cross (id-‵ ι))
      (() , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★)
      (() , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-fun s⊢ t⊢ , cross (sⁿ ↦ tʷ))
      (() , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-all s⊢ , cross (`∀ sʷ))
      (() , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq s⊢ (cast-tag hG gG okG) , sᶜ ︔ gG′ !)
      (() , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ)
      (cast-unseal hB β∈Σ β-ok , unsealʷ β B)
      with _⨟ʷ_ {wfΣ = wfΣ}
             (s⊢ , strictʷ→widen sʷ)
             (cast-unseal hB β∈Σ β-ok , unsealʷ β B)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ)
      (cast-unseal hB β∈Σ β-ok , unsealʷ β B) | u , u⊑ =
    wrap-unsealʷ hA α∈Σ ok u⊑
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , cross (id-＇ α))
      (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ ,
      unseal︔_ β tʷ) =
    _ , (cast-seq (cast-unseal hB β∈Σ β-ok) t⊢ ,
         unseal︔_ β tʷ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , cross (id-‵ ι))
      (cast-seq () t⊢ , unseal︔_ β tʷ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-fun s⊢ t⊢ , cross (sⁿ ↦ tʷ))
      (cast-seq () u⊢ , unseal︔_ β uʷ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-seq () t⊢ , unseal︔_ β tʷ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , id★)
      (t⊢ , inst tʷ)
      with s⊢
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , id★)
      (() , inst tʷ)
      | cast-id hA ok
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross (id-＇ α))
      (t⊢ , inst tʷ)
      with s⊢
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross (id-＇ α))
      (() , inst tʷ)
      | cast-id hA ok
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross (id-‵ ι))
      (t⊢ , inst tʷ)
      with s⊢
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross (id-‵ ι))
      (() , inst tʷ)
      | cast-id hA ok
  _⨟ʷ_ {wfΣ = wfΣ} (cast-inst hB occ s⊢ , inst sʷ) t⊑
      with _⨟ʷ_ {wfΣ = StoreDetWf-inst wfΣ}
             (s⊢ , sʷ) (widen-⇑ᵗ-inst-cons t⊑)
  _⨟ʷ_ {wfΣ = wfΣ} (cast-inst hB occ s⊢ , inst sʷ) t⊑
      | u , u⊑ =
    _ , (cast-inst (widen-tgt-wf t⊑) occ (proj₁ u⊑) ,
         inst (proj₂ u⊑))
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-unseal hA α∈Σ ok , unsealʷ α A)
      t⊑ =
    wrap-unsealʷ hA α∈Σ ok t⊑
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ)
      t⊑
      with _⨟ʷ_ {wfΣ = wfΣ} (s⊢ , strictʷ→widen sʷ) t⊑
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ)
      t⊑ | u , u⊑ =
    wrap-unsealʷ hA α∈Σ ok u⊑
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-inst hC occ t⊢ , inst tʷ)
      with _⨟ʷ_ {wfΣ = StoreDetWf-inst wfΣ}
             (widen-weaken ≤-refl StoreIncl-drop
               (widen-mode-relax modeIncl-ext-inst (s⊢ , sʷ)))
             (t⊢ , tʷ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-all s⊢ , cross (`∀ sʷ))
      (cast-inst hC occ t⊢ , inst tʷ) | u , u⊑ =
    _ , (cast-inst hC
           (widening-target-occurs StoreNoOccurs-zero-⟰ᵗ
             (s⊢ , sʷ) occ)
           (proj₁ u⊑) ,
         inst (proj₂ u⊑))
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross sᶜ)
      (cast-seq t⊢ (cast-tag hG gG okG) , tᶜ ︔ gG′ !)
      with _⨟ᶜʷ_ {wfΣ = wfΣ}
             (s⊢ , sᶜ) (t⊢ , strictCrossʷ→cross tᶜ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross sᶜ)
      (cast-seq t⊢ (cast-tag hG gG okG) ,
      tᶜ ︔ gG′ !) | u , u⊑ =
    wrap-tagʷ u⊑ hG gG okG

  _⨟ᶜʷ_ :
    ∀ {μ Δ Σ A B C s t} →
    {wfΣ : StoreDetWf Δ Σ} →
    μ ∣ Δ ∣ Σ ⊢ᶜ s ∶ A ⊑ B →
    μ ∣ Δ ∣ Σ ⊢ᶜ t ∶ B ⊑ C →
    ∃[ u ] μ ∣ Δ ∣ Σ ⊢ᶜ u ∶ A ⊑ C
  _⨟ᶜʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , id-＇ α) (cast-id hB okB , id-＇ β) =
    _ , (cast-id hA ok , id-＇ α)
  _⨟ᶜʷ_ {wfΣ = wfΣ}
      (cast-id hA ok , id-‵ ι) (cast-id hB okB , id-‵ ι′) =
    _ , (cast-id hA ok , id-‵ ι)
  _⨟ᶜʷ_ {wfΣ = wfΣ}
      (cast-fun s⊢ t⊢ , sⁿ ↦ tʷ)
      (cast-fun s⊢′ t⊢′ , sⁿ′ ↦ tʷ′)
      with _⨟ⁿ_ {wfΣ = wfΣ} (s⊢′ , sⁿ′) (s⊢ , sⁿ)
         | _⨟ʷ_ {wfΣ = wfΣ} (t⊢ , tʷ) (t⊢′ , tʷ′)
  _⨟ᶜʷ_ {wfΣ = wfΣ}
      (cast-fun s⊢ t⊢ , sⁿ ↦ tʷ)
      (cast-fun s⊢′ t⊢′ , sⁿ′ ↦ tʷ′) | u , u⊒ | v , v⊑ =
    _ , (cast-fun (proj₁ u⊒) (proj₁ v⊑) ,
         proj₂ u⊒ ↦ proj₂ v⊑)
  _⨟ᶜʷ_ {wfΣ = wfΣ}
      (cast-all s⊢ , `∀ sʷ) (cast-all t⊢ , `∀ tʷ)
      with _⨟ʷ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} (s⊢ , sʷ) (t⊢ , tʷ)
  _⨟ᶜʷ_ {wfΣ = wfΣ}
      (cast-all s⊢ , `∀ sʷ) (cast-all t⊢ , `∀ tʷ) | u , u⊑ =
    _ , (cast-all (proj₁ u⊑) , `∀ (proj₂ u⊑))

------------------------------------------------------------------------
-- Term-narrowing cast side-condition composition
------------------------------------------------------------------------

infix 4 _∣_⊢_⨾ⁿ_≈_∶_⊒_
infix 4 _∣_⊢_≈_⨾ⁿ_∶_⊒_

data _∣_⊢_⨾ⁿ_≈_∶_⊒_ :
    TyCtx → StoreNrw → Coercion → Coercion → Coercion →
    Ty → Ty → Set₁ where

  compose-leftⁿ : ∀ {Δ σ Σ μ A B C q s r}
    → (wfΣ : StoreDetWf Δ Σ)
    → (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C)
    → (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B)
    → Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
     --------------------------------
    → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B

data _∣_⊢_≈_⨾ⁿ_∶_⊒_ :
    TyCtx → StoreNrw → Coercion → Coercion → Coercion →
    Ty → Ty → Set₁ where

  compose-rightⁿ : ∀ {Δ σ Σ μ A B C r t p}
    → (wfΣ : StoreDetWf Δ Σ)
    → (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ C)
    → (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ C ⊒ B)
    → Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B
     --------------------------------
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B

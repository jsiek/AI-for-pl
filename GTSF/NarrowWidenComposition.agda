-- File Charter:
--   * Public composition operators for well-typed narrowings and widenings.
--   * Exposes term-narrowing side conditions for narrowing composition.
--   * Depends on `NarrowWiden` plus proof-only exclusion lemmas needed for
--     coverage under the `StoreDetWf` invariant.

module NarrowWidenComposition where

open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)

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
      (() , cross (id-＇ α))
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (() , cross (id-‵ ι))
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (() , cross (sʷ ↦ tⁿ))
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (() , cross (`∀ sⁿ))
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-id hA ok , id★)
      (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ) =
    _ , (cast-seq (cast-untag hG gG okG) t⊢ , gG′ ？︔ tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (t⊢ , cross tᶜ)
      with _⨟ᶜⁿ_ {wfΣ = wfΣ} (s⊢ , sᶜ) (t⊢ , tᶜ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (t⊢ , cross tᶜ) | u , u⊒ =
    _ , (cast-seq (cast-untag hG gG okG) (proj₁ u⊒) ,
         gG′ ？︔ proj₂ u⊒)
  _⨟ⁿ_ {wfΣ = wfΣ}
      (cast-seq (cast-untag hG gG okG) s⊢ , gG′ ？︔ sᶜ)
      (cast-seq (cast-untag hH gH okH) t⊢ , hG′ ？︔ tᶜ) =
    ⊥-elim (narrowing-cross-ground-target-star⊥ gG (s⊢ , sᶜ))
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
      s⊒ (cast-seq t⊢ (cast-seal hC α∈Σ ok) , _︔seal_ tⁿ α)
      with _⨟ⁿ_ {wfΣ = wfΣ} s⊒ (t⊢ , tⁿ)
  _⨟ⁿ_ {wfΣ = wfΣ}
      s⊒ (cast-seq t⊢ (cast-seal hC α∈Σ ok) ,
      _︔seal_ tⁿ α) | u , u⊒ =
    _ , (cast-seq (proj₁ u⊒) (cast-seal hC α∈Σ ok) ,
         proj₂ u⊒ ︔seal α)

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
    ⊥-elim (widening-cross-ground-source-star⊥ gH (t⊢ , tᶜ))
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
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ)
      t⊑
      with _⨟ʷ_ {wfΣ = wfΣ} (s⊢ , sʷ) t⊑
  _⨟ʷ_ {wfΣ = wfΣ}
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ)
      t⊑ | u , u⊑ =
    _ , (cast-seq (cast-unseal hA α∈Σ ok) (proj₁ u⊑) ,
         unseal︔_ α (proj₂ u⊑))
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
      with _⨟ᶜʷ_ {wfΣ = wfΣ} (s⊢ , sᶜ) (t⊢ , tᶜ)
  _⨟ʷ_ {wfΣ = wfΣ}
      (s⊢ , cross sᶜ)
      (cast-seq t⊢ (cast-tag hG gG okG) ,
      tᶜ ︔ gG′ !) | u , u⊑ =
    _ , (cast-seq (proj₁ u⊑) (cast-tag hG gG okG) ,
         proj₂ u⊑ ︔ gG′ !)

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
    TyCtx → StoreWid → Coercion → Coercion → Coercion →
    Ty → Ty → Set₁ where

  compose-leftⁿ : ∀ {Δ σ Σ μ A B C q s r}
    → (wfΣ : StoreDetWf Δ Σ)
    → (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C)
    → (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B)
    → Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
     --------------------------------
    → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B

data _∣_⊢_≈_⨾ⁿ_∶_⊒_ :
    TyCtx → StoreWid → Coercion → Coercion → Coercion →
    Ty → Ty → Set₁ where

  compose-rightⁿ : ∀ {Δ σ Σ μ A B C r t p}
    → (wfΣ : StoreDetWf Δ Σ)
    → (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ C)
    → (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ C ⊒ B)
    → Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B
     --------------------------------
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B

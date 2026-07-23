module proof.Compilation.GenSafeComposition where

-- File charter:
--   * Proves closure of `GenSafe` and `InstSafe` under typed composition.
--   * Shows that composition leaves the function projection outside `gen`,
--     with the dual statement for `inst` followed by a function tag.
--   * Gives the canonical factorization of star-to-all narrowings and its
--     all-to-star widening dual.

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Coercions
import Coercions as C
open import NarrowWiden
open import NarrowWidenComposition
open import proof.Compilation.GenSafeProperties
open import proof.Core.Properties.NarrowWidenProperties
  using
    ( StoreDetWf
    ; narrowing-cross-ground-target-all⊥
    ; widening-cross-ground-source-all⊥
    )

genSafe-composition :
  ∀ {μ Δ Σ A B C s t} →
  {wfΣ : StoreDetWf Δ Σ} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B →
  GenSafe s →
  μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C →
  GenSafe t →
  ∃[ u ] (μ ∣ Δ ∣ Σ ⊢ u ∶ A =⇒ C) × GenSafe u
genSafe-composition {wfΣ = wfΣ} s⊢ sᵍ t⊢ tᵍ
    with _⨟ⁿ_ {wfΣ = wfΣ}
           (s⊢ , genSafe→narrowing sᵍ)
           (t⊢ , genSafe→narrowing tᵍ)
genSafe-composition {wfΣ = wfΣ} s⊢ sᵍ t⊢ tᵍ
    | u , u⊢ , uⁿ =
  u , u⊢ ,
  narrowing-between-genSafe-shapes
    (genSafe-source-shape s⊢ sᵍ)
    (genSafe-target-shape t⊢ tᵍ)
    u⊢ uⁿ

instSafe-composition :
  ∀ {μ Δ Σ A B C s t} →
  {wfΣ : StoreDetWf Δ Σ} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ B →
  InstSafe s →
  μ ∣ Δ ∣ Σ ⊢ t ∶ B =⇒ C →
  InstSafe t →
  ∃[ u ] (μ ∣ Δ ∣ Σ ⊢ u ∶ A =⇒ C) × InstSafe u
instSafe-composition {wfΣ = wfΣ} s⊢ sᵍ t⊢ tᵍ
    with _⨟ʷ_ {wfΣ = wfΣ}
           (s⊢ , instSafe→widening sᵍ)
           (t⊢ , instSafe→widening tᵍ)
instSafe-composition {wfΣ = wfΣ} s⊢ sᵍ t⊢ tᵍ
    | u , u⊢ , uʷ =
  u , u⊢ ,
  widening-between-genSafe-shapes
    (instSafe-source-shape s⊢ sᵍ)
    (instSafe-target-shape t⊢ tᵍ)
    u⊢ uʷ

fun-untag-gen-composition :
  ∀ {μ Δ Σ B t} →
  {wfΣ : StoreDetWf Δ Σ} →
  (hG : WfTy Δ (★ ⇒ ★)) →
  (ok : tagTyAllowed μ (★ ⇒ ★) ≡ true) →
  (occ : occurs zero B ≡ true) →
  (t⊢ : genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ
    ⊢ t ∶ ⇑ᵗ (★ ⇒ ★) =⇒ B) →
  (safe : GenSafe t) →
  proj₁
    (_⨟ⁿ_ {wfΣ = wfΣ}
      (cast-untag hG ★⇒★ ok , untag ★⇒★)
      (cast-gen hG occ t⊢ , gen safe))
    ≡ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) t
fun-untag-gen-composition hG ok occ t⊢ safe = refl

inst-fun-tag-composition :
  ∀ {μ Δ Σ A t} →
  {wfΣ : StoreDetWf Δ Σ} →
  (hG : WfTy Δ (★ ⇒ ★)) →
  (ok : tagTyAllowed μ (★ ⇒ ★) ≡ true) →
  (occ : occurs zero A ≡ true) →
  (t⊢ : instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ t ∶ A =⇒ ⇑ᵗ (★ ⇒ ★)) →
  (safe : InstSafe t) →
  proj₁
    (_⨟ʷ_ {wfΣ = wfΣ}
      (cast-inst hG occ t⊢ , inst safe)
      (cast-tag hG ★⇒★ ok , tag ★⇒★))
    ≡ inst (★ ⇒ ★) t ︔ ((★ ⇒ ★) !)
inst-fun-tag-composition hG ok occ t⊢ safe = refl

narrowing-cross-star-all⊥ :
  ∀ {μ Δ Σ A c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ =⇒ `∀ A →
  CrossNarrowing c →
  ⊥
narrowing-cross-star-all⊥ () (id-＇ α)
narrowing-cross-star-all⊥ () (id-‵ ι)
narrowing-cross-star-all⊥ () (sʷ ↦ tⁿ)
narrowing-cross-star-all⊥ () (`∀ sⁿ)

widening-cross-all-star⊥ :
  ∀ {μ Δ Σ A c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ `∀ A =⇒ ★ →
  CrossWidening c →
  ⊥
widening-cross-all-star⊥ () (id-＇ α)
widening-cross-all-star⊥ () (id-‵ ι)
widening-cross-all-star⊥ () (sⁿ ↦ tʷ)
widening-cross-all-star⊥ () (`∀ sʷ)

narrowing-star-all-canonical-factorization :
  ∀ {μ Δ Σ B c} →
  StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ `∀ B →
  ∃[ s ] (c ≡ (((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s)) × GenSafe s
narrowing-star-all-canonical-factorization wfΣ (c⊢ , cross cⁿ) =
  ⊥-elim (narrowing-cross-star-all⊥ c⊢ cⁿ)
narrowing-star-all-canonical-factorization wfΣ (() , id★)
narrowing-star-all-canonical-factorization wfΣ
    (cast-gen hA occ c⊢ , gen safe) =
  ⊥-elim (genSafe-star-source⊥ c⊢ safe)
narrowing-star-all-canonical-factorization wfΣ
    (cast-untag hG () ok , untag gG)
narrowing-star-all-canonical-factorization wfΣ
    (cast-seq (cast-untag hG gG ok) c⊢ , gG′ ？︔ cⁿ) =
  ⊥-elim
    (narrowing-cross-ground-target-all⊥
      gG (c⊢ , strictCrossⁿ→cross cⁿ))
narrowing-star-all-canonical-factorization wfΣ
    (cast-seq (cast-untag hG ★⇒★ ok)
              (cast-gen hA occ c⊢) ,
     fun-untag-gen safe) =
  _ , refl , safe
narrowing-star-all-canonical-factorization wfΣ (() , sealⁿ A α)
narrowing-star-all-canonical-factorization wfΣ
    (cast-seq c⊢ () , cⁿ ︔seal α)

narrowing-canonical-factorization :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  GenSafe c
  ⊎ ((∃[ α ] c ≡ C.id (＇ α))
    ⊎ ((∃[ ι ] c ≡ C.id (‵ ι))
      ⊎ c ≡ C.id ★))
  ⊎ ((∃[ G ] Ground G × c ≡ (G ？))
    ⊎ ((∃[ G ] ∃[ s ] Ground G ×
          StrictCrossNarrowing s × c ≡ ((G ？) ︔ s))
      ⊎ (∃[ D ] ∃[ s ]
          GenSafe s × c ≡ (((★ ⇒ ★) ？) ︔ gen D s))))
  ⊎ ((∃[ D ] ∃[ α ] c ≡ seal D α)
    ⊎ (∃[ D ] ∃[ s ] ∃[ α ]
        StrictNarrowing s × c ≡ (s ︔ seal D α)))
narrowing-canonical-factorization (c⊢ , cross (id-＇ α)) =
  inj₂ (inj₁ (inj₁ (α , refl)))
narrowing-canonical-factorization (c⊢ , cross (id-‵ ι)) =
  inj₂ (inj₁ (inj₂ (inj₁ (ι , refl))))
narrowing-canonical-factorization (c⊢ , cross (sʷ ↦ tⁿ)) =
  inj₁ (safe-fun sʷ tⁿ)
narrowing-canonical-factorization (c⊢ , cross (`∀ sⁿ)) =
  inj₁ (safe-all sⁿ)
narrowing-canonical-factorization (c⊢ , id★) =
  inj₂ (inj₁ (inj₂ (inj₂ refl)))
narrowing-canonical-factorization (c⊢ , gen safe) =
  inj₁ (safe-gen safe)
narrowing-canonical-factorization (c⊢ , untag gG) =
  inj₂ (inj₂ (inj₁ (inj₁ (_ , gG , refl))))
narrowing-canonical-factorization (c⊢ , gG ？︔ sⁿ) =
  inj₂
    (inj₂
      (inj₁ (inj₂ (inj₁ (_ , _ , gG , sⁿ , refl)))))
narrowing-canonical-factorization (c⊢ , fun-untag-gen safe) =
  inj₂
    (inj₂
      (inj₁ (inj₂ (inj₂ (_ , _ , safe , refl)))))
narrowing-canonical-factorization (c⊢ , sealⁿ D α) =
  inj₂ (inj₂ (inj₂ (inj₁ (D , α , refl))))
narrowing-canonical-factorization (c⊢ , sⁿ ︔seal α) =
  inj₂
    (inj₂ (inj₂ (inj₂ (_ , _ , α , sⁿ , refl))))

widening-canonical-factorization :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  InstSafe c
  ⊎ ((∃[ α ] c ≡ C.id (＇ α))
    ⊎ ((∃[ ι ] c ≡ C.id (‵ ι))
      ⊎ c ≡ C.id ★))
  ⊎ ((∃[ G ] Ground G × c ≡ (G !))
    ⊎ ((∃[ G ] ∃[ s ] Ground G ×
          StrictCrossWidening s × c ≡ (s ︔ (G !)))
      ⊎ (∃[ D ] ∃[ s ]
          InstSafe s × c ≡ (inst D s ︔ ((★ ⇒ ★) !)))))
  ⊎ ((∃[ α ] ∃[ D ] c ≡ unseal α D)
    ⊎ (∃[ α ] ∃[ D ] ∃[ s ]
        StrictWidening s × c ≡ (unseal α D ︔ s)))
widening-canonical-factorization (c⊢ , cross (id-＇ α)) =
  inj₂ (inj₁ (inj₁ (α , refl)))
widening-canonical-factorization (c⊢ , cross (id-‵ ι)) =
  inj₂ (inj₁ (inj₂ (inj₁ (ι , refl))))
widening-canonical-factorization (c⊢ , cross (sⁿ ↦ tʷ)) =
  inj₁ (safe-fun sⁿ tʷ)
widening-canonical-factorization (c⊢ , cross (`∀ sʷ)) =
  inj₁ (safe-all sʷ)
widening-canonical-factorization (c⊢ , id★) =
  inj₂ (inj₁ (inj₂ (inj₂ refl)))
widening-canonical-factorization (c⊢ , inst safe) =
  inj₁ (safe-inst safe)
widening-canonical-factorization (c⊢ , tag gG) =
  inj₂ (inj₂ (inj₁ (inj₁ (_ , gG , refl))))
widening-canonical-factorization (c⊢ , sʷ ︔ gG !) =
  inj₂
    (inj₂
      (inj₁ (inj₂ (inj₁ (_ , _ , gG , sʷ , refl)))))
widening-canonical-factorization (c⊢ , inst-fun-tag safe) =
  inj₂
    (inj₂
      (inj₁ (inj₂ (inj₂ (_ , _ , safe , refl)))))
widening-canonical-factorization (c⊢ , unsealʷ α D) =
  inj₂ (inj₂ (inj₂ (inj₁ (α , D , refl))))
widening-canonical-factorization (c⊢ , unseal︔_ α sʷ) =
  inj₂
    (inj₂ (inj₂ (inj₂ (α , _ , _ , sʷ , refl))))

widening-all-star-canonical-factorization :
  ∀ {μ Δ Σ A c} →
  StoreDetWf Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ `∀ A ⊑ ★ →
  ∃[ s ] (c ≡ (inst (★ ⇒ ★) s ︔ ((★ ⇒ ★) !))) × InstSafe s
widening-all-star-canonical-factorization wfΣ (c⊢ , cross cʷ) =
  ⊥-elim (widening-cross-all-star⊥ c⊢ cʷ)
widening-all-star-canonical-factorization wfΣ (() , id★)
widening-all-star-canonical-factorization wfΣ
    (cast-inst hB occ c⊢ , inst safe) =
  ⊥-elim (instSafe-star-target⊥ c⊢ safe)
widening-all-star-canonical-factorization wfΣ
    (cast-tag hG () ok , tag gG)
widening-all-star-canonical-factorization wfΣ
    (cast-seq c⊢ (cast-tag hG gG ok) , cʷ ︔ gG′ !) =
  ⊥-elim
    (widening-cross-ground-source-all⊥
      gG (c⊢ , strictCrossʷ→cross cʷ))
widening-all-star-canonical-factorization wfΣ
    (cast-seq (cast-inst hB occ c⊢)
              (cast-tag hG ★⇒★ ok) ,
     inst-fun-tag safe) =
  _ , refl , safe
widening-all-star-canonical-factorization wfΣ (() , unsealʷ α A)
widening-all-star-canonical-factorization wfΣ
    (cast-seq () c⊢ , unseal︔_ α cʷ)

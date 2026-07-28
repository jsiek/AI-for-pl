module proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisProof where

-- File Charter:
--   * Proves direct synthesis of target administration plans from typed
--     narrowing and widening evidence.
--   * Threads the supplied cast shapes and composition triangles into every
--     direct, fused, and sequence component plan.
--   * Splits sequence triangles only by inversion of the supplied exact
--     composition evidence.
--   * Contains no simulation result, outcome carrier, permissive option,
--     compatibility wrapper, or catch-all proof case.

open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; narrowing
  ; widening
  ; shape-sequence-narrowing
  ; shape-sequence-widening
  ; shape-tag-fun
  ; shape-untag-fun
  )
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using
  (_×_; _,_; proj₁; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)

import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
  )
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; id★ˢ
  ; tag_⇛ˢ_
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-ν
  ; compose-right-id★
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; id★
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuStore using (StoreWf; unique)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; _⇒_)
import Types as T
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-assoc-left)
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef using
  ( TargetAdministrationPlan
  ; plan-id
  ; plan-inert
  ; plan-fun-untag-gen
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-narrow-seq
  ; plan-widen-seq
  ; plan-id-widen-seq
  ; plan-unseal
  ; plan-untag
  )
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisDef using
  (TargetAdministrationPlanSynthesis)


strict-cross-narrowing-to-star⊥ :
  ∀ {μ Δ Σ A s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ T.★ →
  NW.StrictCrossNarrowing s →
  ⊥
strict-cross-narrowing-to-star⊥ () (NW.cn-funˡ sʷ tⁿ)
strict-cross-narrowing-to-star⊥ () (NW.cn-funʳ sʷ tⁿ)
strict-cross-narrowing-to-star⊥ () (NW.cn-all tⁿ)


strict-cross-widening-from-star⊥ :
  ∀ {μ Δ Σ B s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ T.★ =⇒ B →
  NW.StrictCrossWidening s →
  ⊥
strict-cross-widening-from-star⊥ () (NW.cw-funˡ sⁿ tʷ)
strict-cross-widening-from-star⊥ () (NW.cw-funʳ sⁿ tʷ)
strict-cross-widening-from-star⊥ () (NW.cw-all tʷ)


strict-narrowing-to-star⊥ :
  ∀ {μ Δ Σ A s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ T.★ →
  NW.StrictNarrowing s →
  ⊥
strict-narrowing-to-star⊥ ()
  (NW.strict-crossⁿ (NW.cn-funˡ sʷ tⁿ))
strict-narrowing-to-star⊥ ()
  (NW.strict-crossⁿ (NW.cn-funʳ sʷ tⁿ))
strict-narrowing-to-star⊥ ()
  (NW.strict-crossⁿ (NW.cn-all sⁿ))
strict-narrowing-to-star⊥ () (NW.strict-gen sⁿ)
strict-narrowing-to-star⊥
    (C.cast-untag hG () tag-ok) (NW.strict-untag gG)
strict-narrowing-to-star⊥
    (C.cast-seq s⊢ t⊢) (NW.strict-untag-seq gG gⁿ) =
  strict-cross-narrowing-to-star⊥ t⊢ gⁿ
strict-narrowing-to-star⊥ () (NW.strict-seal A α)
strict-narrowing-to-star⊥
    (C.cast-seq s⊢ ()) (NW.strict-seal-seq sⁿ α)


strict-widening-from-star⊥ :
  ∀ {μ Δ Σ B t} →
  μ ∣ Δ ∣ Σ ⊢ t ∶ T.★ =⇒ B →
  NW.StrictWidening t →
  ⊥
strict-widening-from-star⊥ ()
  (NW.strict-crossʷ (NW.cw-funˡ sⁿ tʷ))
strict-widening-from-star⊥ ()
  (NW.strict-crossʷ (NW.cw-funʳ sⁿ tʷ))
strict-widening-from-star⊥ ()
  (NW.strict-crossʷ (NW.cw-all tʷ))
strict-widening-from-star⊥ () (NW.strict-inst tʷ)
strict-widening-from-star⊥
    (C.cast-tag hG () tag-ok) (NW.strict-tag gG)
strict-widening-from-star⊥
    (C.cast-seq s⊢ t⊢) (NW.strict-tag-seq gʷ gG) =
  strict-cross-widening-from-star⊥ s⊢ gʷ
strict-widening-from-star⊥ () (NW.strict-unseal α A)
strict-widening-from-star⊥
    (C.cast-seq () t⊢) (NW.strict-unseal-seq α tʷ)


strict-narrowing-seal-seq⊥ :
  ∀ {Φ Δᴸ Δᴿ μ B C s α}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
  (α , C) ∈ rightStoreⁱ ρ₀ →
  C.sealModeAllowed (μ α) ≡ true →
  NW.StrictNarrowing s →
  ⊥
strict-narrowing-seal-seq⊥ prefix wfΣ seal★ s⊢ αC∈Σ ok sⁿ
    rewrite unique wfΣ
      (rightStoreⁱ-prefix-inclusion prefix αC∈Σ)
      (rightStoreⁱ-prefix-inclusion prefix (seal★ _ ok)) =
  strict-narrowing-to-star⊥ s⊢ sⁿ


strict-widening-unseal-seq⊥ :
  ∀ {Φ Δᴸ Δᴿ μ B C s α}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  (α , B) ∈ rightStoreⁱ ρ₀ →
  C.sealModeAllowed (μ α) ≡ true →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ s ∶ B =⇒ C →
  NW.StrictWidening s →
  ⊥
strict-widening-unseal-seq⊥ prefix wfΣ seal★ αB∈Σ ok s⊢ sʷ
    rewrite unique wfΣ
      (rightStoreⁱ-prefix-inclusion prefix αB∈Σ)
      (rightStoreⁱ-prefix-inclusion prefix (seal★ _ ok)) =
  strict-widening-from-star⊥ s⊢ sʷ


target-star-arrow-midpoint :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⇒ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
target-star-arrow-midpoint id★ ()
target-star-arrow-midpoint (tag ι) ()
target-star-arrow-midpoint (tag p ⇛ q) (r ↦ s) = p ↦ q
target-star-arrow-midpoint (tagˣ X⊑★ X<Δᴸ) ()
target-star-arrow-midpoint (ν safe occ p) (ν safe′ occ′ q) =
  ν safe occ (target-star-arrow-midpoint p q)


target-arrow-star-midpoint :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⇒ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
target-arrow-star-midpoint (p ↦ q) (tag r ⇛ s) = r ↦ s
target-arrow-star-midpoint (ν safe occ p) (ν safe′ occ′ q) =
  ν safe occ (target-arrow-star-midpoint p q)


target-untag-function-right-triangle :
  ∀ {Φ Δᴸ Δᴿ A B C t-shape sequence-shape}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ A ⊑ B ⇒ C ⊣ Δᴿ) →
  t-shape ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ sequence-shape →
  ⌊ q ⌋ ； sequence-shape ≋ ⌊ p ⌋ →
  ⌊ q ⌋ ； t-shape ≋ ⌊ target-star-arrow-midpoint p q ⌋
target-untag-function-right-triangle id★ ()
  sequence-comp outer-comp
target-untag-function-right-triangle (tag ι) ()
  sequence-comp outer-comp
target-untag-function-right-triangle
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂)
    (comp-↦-tag t₁-id t₂-id)
    (comp-↦-tag outer₁ outer₂)
    with compose-right-id★ t₁-id
       | compose-right-id★ t₂-id
target-untag-function-right-triangle
    (tag p₁ ⇛ p₂) (q₁ ↦ q₂)
    (comp-↦-tag t₁-id t₂-id)
    (comp-↦-tag outer₁ outer₂)
    | refl | refl =
  comp-↦-↦ outer₁ outer₂
target-untag-function-right-triangle
    (tagˣ X⊑★ X<Δᴸ) ()
    sequence-comp outer-comp
target-untag-function-right-triangle
    (ν safe occ p) (ν safe′ occ′ q)
    sequence-comp (comp-ν outer-comp) =
  comp-ν
    (target-untag-function-right-triangle
      p q sequence-comp outer-comp)


target-function-tag-left-triangle :
  ∀ {Φ Δᴸ Δᴿ A B C s-shape sequence-shape}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⇒ C ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  s-shape ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ sequence-shape →
  ⌊ p ⌋ ； sequence-shape ≋ ⌊ q ⌋ →
  ⌊ p ⌋ ； s-shape ≋ ⌊ target-arrow-star-midpoint p q ⌋
target-function-tag-left-triangle
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂)
    (comp-↦-tag s₁-id s₂-id)
    (comp-↦-tag outer₁ outer₂)
    with compose-right-id★ s₁-id
       | compose-right-id★ s₂-id
target-function-tag-left-triangle
    (p₁ ↦ p₂) (tag q₁ ⇛ q₂)
    (comp-↦-tag s₁-id s₂-id)
    (comp-↦-tag outer₁ outer₂)
    | refl | refl =
  comp-↦-↦ outer₁ outer₂
target-function-tag-left-triangle
    (ν safe occ p) (ν safe′ occ′ q)
    sequence-comp (comp-ν outer-comp) =
  comp-ν
    (target-function-tag-left-triangle
      p q sequence-comp outer-comp)


target-strict-cross-narrowing-ground-midpoint :
  ∀ {Φ Δᴸ Δᴿ μ Σ A G C g} →
  T.Ground G →
  μ ∣ Δᴿ ∣ Σ ⊢ g ∶ G =⇒ C →
  NW.StrictCrossNarrowing g →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ
target-strict-cross-narrowing-ground-midpoint
    (T.＇ α) () (NW.cn-funˡ sʷ tⁿ) p q
target-strict-cross-narrowing-ground-midpoint
    (T.＇ α) () (NW.cn-funʳ sʷ tⁿ) p q
target-strict-cross-narrowing-ground-midpoint
    (T.＇ α) () (NW.cn-all tⁿ) p q
target-strict-cross-narrowing-ground-midpoint
    (T.‵ ι) () (NW.cn-funˡ sʷ tⁿ) p q
target-strict-cross-narrowing-ground-midpoint
    (T.‵ ι) () (NW.cn-funʳ sʷ tⁿ) p q
target-strict-cross-narrowing-ground-midpoint
    (T.‵ ι) () (NW.cn-all tⁿ) p q
target-strict-cross-narrowing-ground-midpoint
    T.★⇒★ (C.cast-fun s⊢ t⊢) (NW.cn-funˡ sʷ tⁿ) p q =
  target-star-arrow-midpoint p q
target-strict-cross-narrowing-ground-midpoint
    T.★⇒★ (C.cast-fun s⊢ t⊢) (NW.cn-funʳ sʷ tⁿ) p q =
  target-star-arrow-midpoint p q
target-strict-cross-narrowing-ground-midpoint
    T.★⇒★ () (NW.cn-all tⁿ) p q


target-strict-cross-widening-ground-midpoint :
  ∀ {Φ Δᴸ Δᴿ μ Σ A B G g} →
  T.Ground G →
  μ ∣ Δᴿ ∣ Σ ⊢ g ∶ B =⇒ G →
  NW.StrictCrossWidening g →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ
target-strict-cross-widening-ground-midpoint
    (T.＇ α) () (NW.cw-funˡ sⁿ tʷ) p q
target-strict-cross-widening-ground-midpoint
    (T.＇ α) () (NW.cw-funʳ sⁿ tʷ) p q
target-strict-cross-widening-ground-midpoint
    (T.＇ α) () (NW.cw-all tʷ) p q
target-strict-cross-widening-ground-midpoint
    (T.‵ ι) () (NW.cw-funˡ sⁿ tʷ) p q
target-strict-cross-widening-ground-midpoint
    (T.‵ ι) () (NW.cw-funʳ sⁿ tʷ) p q
target-strict-cross-widening-ground-midpoint
    (T.‵ ι) () (NW.cw-all tʷ) p q
target-strict-cross-widening-ground-midpoint
    T.★⇒★ (C.cast-fun s⊢ t⊢) (NW.cw-funˡ sⁿ tʷ) p q =
  target-arrow-star-midpoint p q
target-strict-cross-widening-ground-midpoint
    T.★⇒★ (C.cast-fun s⊢ t⊢) (NW.cw-funʳ sⁿ tʷ) p q =
  target-arrow-star-midpoint p q
target-strict-cross-widening-ground-midpoint
    T.★⇒★ () (NW.cw-all tʷ) p q


target-narrowing-ground-sequence-evidence :
  ∀ {Φ Δᴸ Δᴿ μ Σ A G C g
      untag-shape g-shape sequence-shape}
    (gG : T.Ground G)
    (g⊢ : μ ∣ Δᴿ ∣ Σ ⊢ g ∶ G =⇒ C)
    (gⁿ : NW.StrictCrossNarrowing g)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ) →
  narrowing ⊢ᶜ G C.？ ⦂ untag-shape →
  narrowing ⊢ᶜ g ⦂ g-shape →
  g-shape ； untag-shape ≋ sequence-shape →
  ⌊ q ⌋ ； sequence-shape ≋ ⌊ p ⌋ →
  Σ[ r ∈ (Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ) ]
    (⌊ r ⌋ ； untag-shape ≋ ⌊ p ⌋) ×
    (⌊ q ⌋ ； g-shape ≋ ⌊ r ⌋)
target-narrowing-ground-sequence-evidence
    (T.＇ α) () (NW.cn-funˡ sʷ tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    (T.＇ α) () (NW.cn-funʳ sʷ tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    (T.＇ α) () (NW.cn-all tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    (T.‵ ι) () (NW.cn-funˡ sʷ tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    (T.‵ ι) () (NW.cn-funʳ sʷ tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    (T.‵ ι) () (NW.cn-all tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    T.★⇒★ g⊢@(C.cast-fun s⊢ t⊢)
    gⁿ@(NW.cn-funˡ sʷ tⁿ)
    p q shape-untag-fun g-shape sequence-comp outer-comp =
  r ,
  compose-assoc-left right-triangle sequence-comp outer-comp ,
  right-triangle
  where
  r = target-strict-cross-narrowing-ground-midpoint
    T.★⇒★ g⊢ gⁿ p q
  right-triangle =
    target-untag-function-right-triangle
      p q sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    T.★⇒★ g⊢@(C.cast-fun s⊢ t⊢)
    gⁿ@(NW.cn-funʳ sʷ tⁿ)
    p q shape-untag-fun g-shape sequence-comp outer-comp =
  r ,
  compose-assoc-left right-triangle sequence-comp outer-comp ,
  right-triangle
  where
  r = target-strict-cross-narrowing-ground-midpoint
    T.★⇒★ g⊢ gⁿ p q
  right-triangle =
    target-untag-function-right-triangle
      p q sequence-comp outer-comp
target-narrowing-ground-sequence-evidence
    T.★⇒★ () (NW.cn-all tⁿ)
    p q untag-shape g-shape sequence-comp outer-comp


target-widening-ground-sequence-evidence :
  ∀ {Φ Δᴸ Δᴿ μ Σ A B G g
      g-shape tag-shape sequence-shape}
    (gG : T.Ground G)
    (g⊢ : μ ∣ Δᴿ ∣ Σ ⊢ g ∶ B =⇒ G)
    (gʷ : NW.StrictCrossWidening g)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  widening ⊢ᶜ g ⦂ g-shape →
  widening ⊢ᶜ G C.! ⦂ tag-shape →
  g-shape ； tag-shape ≋ sequence-shape →
  ⌊ p ⌋ ； sequence-shape ≋ ⌊ q ⌋ →
  Σ[ r ∈ (Φ ∣ Δᴸ ⊢ A ⊑ G ⊣ Δᴿ) ]
    (⌊ p ⌋ ； g-shape ≋ ⌊ r ⌋) ×
    (⌊ r ⌋ ； tag-shape ≋ ⌊ q ⌋)
target-widening-ground-sequence-evidence
    (T.＇ α) () (NW.cw-funˡ sⁿ tʷ)
    p q g-shape tag-shape sequence-comp outer-comp
target-widening-ground-sequence-evidence
    (T.＇ α) () (NW.cw-funʳ sⁿ tʷ)
    p q g-shape tag-shape sequence-comp outer-comp
target-widening-ground-sequence-evidence
    (T.＇ α) () (NW.cw-all tʷ)
    p q g-shape tag-shape sequence-comp outer-comp
target-widening-ground-sequence-evidence
    (T.‵ ι) () (NW.cw-funˡ sⁿ tʷ)
    p q g-shape tag-shape sequence-comp outer-comp
target-widening-ground-sequence-evidence
    (T.‵ ι) () (NW.cw-funʳ sⁿ tʷ)
    p q g-shape tag-shape sequence-comp outer-comp
target-widening-ground-sequence-evidence
    (T.‵ ι) () (NW.cw-all tʷ)
    p q g-shape tag-shape sequence-comp outer-comp
target-widening-ground-sequence-evidence
    T.★⇒★ g⊢@(C.cast-fun s⊢ t⊢)
    gʷ@(NW.cw-funˡ sⁿ tʷ)
    p q g-shape shape-tag-fun sequence-comp outer-comp =
  r ,
  left-triangle ,
  compose-assoc-left left-triangle sequence-comp outer-comp
  where
  r = target-strict-cross-widening-ground-midpoint
    T.★⇒★ g⊢ gʷ p q
  left-triangle =
    target-function-tag-left-triangle
      p q sequence-comp outer-comp
target-widening-ground-sequence-evidence
    T.★⇒★ g⊢@(C.cast-fun s⊢ t⊢)
    gʷ@(NW.cw-funʳ sⁿ tʷ)
    p q g-shape shape-tag-fun sequence-comp outer-comp =
  r ,
  left-triangle ,
  compose-assoc-left left-triangle sequence-comp outer-comp
  where
  r = target-strict-cross-widening-ground-midpoint
    T.★⇒★ g⊢ gʷ p q
  left-triangle =
    target-function-tag-left-triangle
      p q sequence-comp outer-comp
target-widening-ground-sequence-evidence
    T.★⇒★ () (NW.cw-all tʷ)
    p q g-shape tag-shape sequence-comp outer-comp


target-strict-cross-narrowing-plan :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {shape : ImprecisionShape} →
  NW.StrictCrossNarrowing c →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  (c⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊒ C) →
  narrowing ⊢ᶜ c ⦂ shape →
  ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
  TargetAdministrationPlan ρ A (proj₁ c⊒) p q
target-strict-cross-narrowing-plan
    (NW.cn-funˡ {s = s} {t = t} sʷ tⁿ)
    mode seal★ c⊒
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-strict-cross-narrowing-plan
    (NW.cn-funʳ {s = s} {t = t} sʷ tⁿ)
    mode seal★ c⊒
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-strict-cross-narrowing-plan
    (NW.cn-all {s = s} sⁿ) mode seal★ c⊒
    c-shape comp =
  plan-inert (C.`∀ s)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))


target-strict-cross-widening-plan :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {shape : ImprecisionShape} →
  NW.StrictCrossWidening c →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  (c⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊑ C) →
  widening ⊢ᶜ c ⦂ shape →
  ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
  TargetAdministrationPlan ρ A (proj₁ c⊑) p q
target-strict-cross-widening-plan
    (NW.cw-funˡ {s = s} {t = t} sⁿ tʷ)
    mode seal★ c⊑
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-strict-cross-widening-plan
    (NW.cw-funʳ {s = s} {t = t} sⁿ tʷ)
    mode seal★ c⊑
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-strict-cross-widening-plan
    (NW.cw-all {s = s} sʷ) mode seal★ c⊑
    c-shape comp =
  plan-inert (C.`∀ s)
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))


target-strict-cross-id-widening-plan :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {shape : ImprecisionShape} →
  NW.StrictCrossWidening c →
  SealModeStore★ C.id-onlyᵈ (rightStoreⁱ ρ) →
  (c⊑ : C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ c ∶ B ⊑ C) →
  widening ⊢ᶜ c ⦂ shape →
  ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
  TargetAdministrationPlan ρ A (proj₁ c⊑) p q
target-strict-cross-id-widening-plan
    (NW.cw-funˡ {s = s} {t = t} sⁿ tʷ)
    seal★ c⊑
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-strict-cross-id-widening-plan
    (NW.cw-funʳ {s = s} {t = t} sⁿ tʷ)
    seal★ c⊑
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-strict-cross-id-widening-plan
    (NW.cw-all {s = s} sʷ) seal★ c⊑
    c-shape comp =
  plan-inert (C.`∀ s)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))


target-narrowing-administration-plan :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  (c⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊒ C) →
  narrowing ⊢ᶜ c ⦂ shape →
  ⌊ q ⌋ ； shape ≋ ⌊ p ⌋ →
  TargetAdministrationPlan ρ₀ A (proj₁ c⊒) p q
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-id hB ok , NW.cross (NW.id-＇ α))
    c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-id hB ok , NW.cross (NW.id-‵ ι))
    c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-fun {s = s} {t = t} s⊢ t⊢ ,
      NW.cross (sʷ NW.↦ tⁿ))
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-all {s = s} c⊢ , NW.cross (NW.`∀ sⁿ))
    c-shape comp =
  plan-inert (C.`∀ s)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-id hB ok , NW.id★) c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-gen {A = B₀} {s = s} hA occ s⊢ ,
      NW.gen {A = B₁} sⁿ)
    c-shape comp =
  plan-inert (C.gen B₁ s)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-untag hG gG ok , NW.untag gG′)
    c-shape comp =
  plan-untag mode seal★ c⊒ c-shape comp
target-narrowing-administration-plan {p = p} {q = q}
    prefix wfΣ mode seal★
    c⊒@(C.cast-seq (C.cast-untag hG gG ok) t⊢ ,
      gG′ NW.？︔ gⁿ)
    (shape-sequence-narrowing
      untag-shape g-shape sequence-comp)
    outer-comp
    with target-narrowing-ground-sequence-evidence
      gG t⊢ gⁿ p q
      untag-shape g-shape sequence-comp outer-comp
target-narrowing-administration-plan {p = p} {q = q}
    prefix wfΣ mode seal★
    c⊒@(C.cast-seq (C.cast-untag hG gG ok) t⊢ ,
      gG′ NW.？︔ gⁿ)
    (shape-sequence-narrowing
      untag-shape g-shape sequence-comp)
    outer-comp
    | r , untag-comp , g-comp =
  plan-narrow-seq
    mode seal★ c⊒
    (gG′ NW.？︔ gⁿ)
    (shape-sequence-narrowing
      untag-shape g-shape sequence-comp)
    outer-comp
    untag-shape untag-comp
    g-shape g-comp
    (plan-untag {q = r} mode seal★
      (C.cast-untag hG gG ok , NW.untag gG′)
      untag-shape untag-comp)
    (target-strict-cross-narrowing-plan
      {p = r} {q = q}
      gⁿ mode seal★
      (t⊢ , NW.cross (NW.strictCrossⁿ→cross gⁿ))
      g-shape g-comp)
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-seq (C.cast-untag hG gG ok)
      (C.cast-gen {A = B₀} {s = s} hA occ s⊢) ,
      NW.fun-untag-gen {A = B₁} safe)
    c-shape comp =
  plan-fun-untag-gen
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    c⊒@(C.cast-seal {α = α} {A = B₀} hB αB∈Σ ok ,
      NW.sealⁿ B₁ α′)
    c-shape comp =
  plan-inert (C.seal B₁ α′)
    (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊒ , c-shape , comp))))
target-narrowing-administration-plan prefix wfΣ mode seal★
    (C.cast-seq s⊢ (C.cast-seal hX αX∈Σ seal-ok) ,
      sⁿ NW.︔seal α)
    c-shape comp
  = ⊥-elim
      (strict-narrowing-seal-seq⊥
        prefix wfΣ seal★ s⊢ αX∈Σ seal-ok sⁿ)


target-widening-administration-plan :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  (c⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C) →
  widening ⊢ᶜ c ⦂ shape →
  ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
  TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-id hB ok , NW.cross (NW.id-＇ α))
    c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-id hB ok , NW.cross (NW.id-‵ ι))
    c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-fun {s = s} {t = t} s⊢ t⊢ ,
      NW.cross (sⁿ NW.↦ tʷ))
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-all {s = s} c⊢ , NW.cross (NW.`∀ sʷ))
    c-shape comp =
  plan-inert (C.`∀ s)
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-id hB ok , NW.id★) c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-inst {s = s} hB occ s⊢ , NW.inst sʷ)
    c-shape comp =
  plan-inst
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-tag {G = G} hG gG⊢ ok , NW.tag gG)
    c-shape comp =
  plan-inert (G C.!)
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan {p = p} {q = q}
    prefix wfΣ mode seal★
    c⊑@(C.cast-seq s⊢ (C.cast-tag {G = G} hG gG ok) ,
      gʷ NW.︔ gG′ !)
    (shape-sequence-widening
      g-shape tag-shape sequence-comp)
    outer-comp
    with target-widening-ground-sequence-evidence
      gG s⊢ gʷ p q
      g-shape tag-shape sequence-comp outer-comp
target-widening-administration-plan {p = p} {q = q}
    prefix wfΣ mode seal★
    c⊑@(C.cast-seq s⊢ (C.cast-tag {G = G} hG gG ok) ,
      gʷ NW.︔ gG′ !)
    (shape-sequence-widening
      g-shape tag-shape sequence-comp)
    outer-comp
    | r , g-comp , tag-comp =
  plan-widen-seq
    mode seal★ c⊑
    (gʷ NW.︔ gG′ !)
    (shape-sequence-widening
      g-shape tag-shape sequence-comp)
    outer-comp
    g-shape g-comp
    tag-shape tag-comp
    (target-strict-cross-widening-plan
      {p = p} {q = r}
      gʷ mode seal★
      (s⊢ , NW.cross (NW.strictCrossʷ→cross gʷ))
      g-shape g-comp)
    (plan-inert {p = r} (G C.!)
      (inj₂ (inj₂ (inj₂ (inj₁
        (_ , _ , mode , seal★ ,
         (C.cast-tag hG gG ok , NW.tag gG′) ,
         tag-shape , tag-comp))))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-seq (C.cast-inst {s = s} hB occ s⊢)
      (C.cast-tag {G = G} hG gG ok) ,
      NW.inst-fun-tag {B = B₀} safe)
    c-shape comp =
  plan-inst-fun-tag
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    c⊑@(C.cast-unseal {α = α} {A = B₀} hB αB∈Σ seal-ok ,
      NW.unsealʷ α′ B₁)
    c-shape comp =
  plan-unseal
    (inj₂ (inj₂ (inj₂ (inj₁
      (_ , _ , mode , seal★ , c⊑ , c-shape , comp)))))
target-widening-administration-plan prefix wfΣ mode seal★
    (C.cast-seq (C.cast-unseal hX αX∈Σ seal-ok) t⊢ ,
      NW.unseal︔_ α tʷ)
    c-shape comp
  = ⊥-elim
      (strict-widening-unseal-seq⊥
        prefix wfΣ seal★ αX∈Σ seal-ok t⊢ tʷ)


target-id-widening-administration-plan :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  SealModeStore★ C.id-onlyᵈ (rightStoreⁱ ρ₀) →
  (c⊑ : C.id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ c ∶ B ⊑ C) →
  widening ⊢ᶜ c ⦂ shape →
  ⌊ p ⌋ ； shape ≋ ⌊ q ⌋ →
  TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-id hB ok , NW.cross (NW.id-＇ α))
    c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-id hB ok , NW.cross (NW.id-‵ ι))
    c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-fun {s = s} {t = t} s⊢ t⊢ ,
      NW.cross (sⁿ NW.↦ tʷ))
    c-shape comp =
  plan-inert (s C.↦ t)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-all {s = s} c⊢ , NW.cross (NW.`∀ sʷ))
    c-shape comp =
  plan-inert (C.`∀ s)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-id hB ok , NW.id★) c-shape comp =
  plan-id
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-inst {s = s} hB occ s⊢ , NW.inst sʷ)
    c-shape comp =
  plan-inst
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-tag {G = G} hG gG⊢ ok , NW.tag gG)
    c-shape comp =
  plan-inert (G C.!)
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan {p = p} {q = q}
    prefix wfΣ seal★
    c⊑@(C.cast-seq s⊢ (C.cast-tag {G = G} hG gG ok) ,
      gʷ NW.︔ gG′ !)
    (shape-sequence-widening
      g-shape tag-shape sequence-comp)
    outer-comp
    with target-widening-ground-sequence-evidence
      gG s⊢ gʷ p q
      g-shape tag-shape sequence-comp outer-comp
target-id-widening-administration-plan {p = p} {q = q}
    prefix wfΣ seal★
    c⊑@(C.cast-seq s⊢ (C.cast-tag {G = G} hG gG ok) ,
      gʷ NW.︔ gG′ !)
    (shape-sequence-widening
      g-shape tag-shape sequence-comp)
    outer-comp
    | r , g-comp , tag-comp =
  plan-id-widen-seq
    seal★ c⊑
    (gʷ NW.︔ gG′ !)
    (shape-sequence-widening
      g-shape tag-shape sequence-comp)
    outer-comp
    g-shape g-comp
    tag-shape tag-comp
    (target-strict-cross-id-widening-plan
      {p = p} {q = r}
      gʷ seal★
      (s⊢ , NW.cross (NW.strictCrossʷ→cross gʷ))
      g-shape g-comp)
    (plan-inert {p = r} (G C.!)
      (inj₂ (inj₂ (inj₂ (inj₂
        (_ , seal★ ,
         (C.cast-tag hG gG ok , NW.tag gG′) ,
         tag-shape , tag-comp))))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-seq (C.cast-inst {s = s} hB occ s⊢)
      (C.cast-tag {G = G} hG gG ok) ,
      NW.inst-fun-tag {B = B₀} safe)
    c-shape comp =
  plan-inst-fun-tag
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    c⊑@(C.cast-unseal {α = α} {A = B₀} hB αB∈Σ seal-ok ,
      NW.unsealʷ α′ B₁)
    c-shape comp =
  plan-unseal
    (inj₂ (inj₂ (inj₂ (inj₂
      (_ , seal★ , c⊑ , c-shape , comp)))))
target-id-widening-administration-plan prefix wfΣ seal★
    (C.cast-seq (C.cast-unseal hX αX∈Σ seal-ok) t⊢ ,
      NW.unseal︔_ α tʷ)
    c-shape comp
  = ⊥-elim
      (strict-widening-unseal-seq⊥
        prefix wfΣ seal★ αX∈Σ seal-ok t⊢ tʷ)


target-administration-plan-synthesis-proofᵀ :
  TargetAdministrationPlanSynthesis
target-administration-plan-synthesis-proofᵀ =
  record
    { targetNarrowingAdministrationPlan =
        target-narrowing-administration-plan
    ; targetWideningAdministrationPlan =
        target-widening-administration-plan
    ; targetIdWideningAdministrationPlan =
        target-id-widening-administration-plan
    }

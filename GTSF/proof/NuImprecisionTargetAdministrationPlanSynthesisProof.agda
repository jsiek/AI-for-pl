module proof.NuImprecisionTargetAdministrationPlanSynthesisProof where

-- File Charter:
--   * Proves direct synthesis of target administration plans from typed
--     narrowing and widening evidence.
--   * Recovers sequence midpoint precision locally, using only right-store
--     prefix inclusion, final sparse-store uniqueness, and seal-mode evidence.
--   * Contains no simulation result, outcome carrier, permissive option,
--     compatibility wrapper, or catch-all proof case.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_; proj₁)

import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
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
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (SealModeStore★)
open import Types using (Ty; TyCtx; ★; _⇒_)
import Types as T
open import proof.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionTargetAdministrationPlanDef using
  ( TargetAdministrationPlan
  ; plan-id
  ; plan-inert
  ; plan-inst
  ; plan-seq
  ; plan-unseal
  ; plan-untag
  )
open import proof.NuImprecisionTargetAdministrationPlanSynthesisDef using
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
target-star-arrow-midpoint (ν _ occ p) (ν _ occ′ q) =
  ν _ occ (target-star-arrow-midpoint p q)


target-arrow-star-midpoint :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⇒ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ
target-arrow-star-midpoint (p ↦ q) (tag r ⇛ s) = r ↦ s
target-arrow-star-midpoint (ν _ occ p) (ν _ occ′ q) =
  ν _ occ (target-arrow-star-midpoint p q)


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


target-strict-cross-narrowing-plan :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    (c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C) →
  NW.StrictCrossNarrowing c →
  TargetAdministrationPlan ρ A c⊢ p q
target-strict-cross-narrowing-plan c⊢
    (NW.cn-funˡ {s = s} {t = t} sʷ tⁿ) =
  plan-inert (s C.↦ t)
target-strict-cross-narrowing-plan c⊢
    (NW.cn-funʳ {s = s} {t = t} sʷ tⁿ) =
  plan-inert (s C.↦ t)
target-strict-cross-narrowing-plan c⊢
    (NW.cn-all {s = s} sⁿ) =
  plan-inert (C.`∀ s)


target-strict-cross-widening-plan :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    (c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C) →
  NW.StrictCrossWidening c →
  TargetAdministrationPlan ρ A c⊢ p q
target-strict-cross-widening-plan c⊢
    (NW.cw-funˡ {s = s} {t = t} sⁿ tʷ) =
  plan-inert (s C.↦ t)
target-strict-cross-widening-plan c⊢
    (NW.cw-funʳ {s = s} {t = t} sⁿ tʷ) =
  plan-inert (s C.↦ t)
target-strict-cross-widening-plan c⊢
    (NW.cw-all {s = s} sʷ) =
  plan-inert (C.`∀ s)


target-narrowing-administration-plan :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  (c⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊒ C) →
  TargetAdministrationPlan ρ₀ A (proj₁ c⊒) p q
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-id hB ok , NW.cross (NW.id-＇ α)) =
  plan-id
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-id hB ok , NW.cross (NW.id-‵ ι)) =
  plan-id
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-fun {s = s} {t = t} s⊢ t⊢ ,
     NW.cross (sʷ NW.↦ tⁿ)) =
  plan-inert (s C.↦ t)
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-all {s = s} c⊢ , NW.cross (NW.`∀ sⁿ)) =
  plan-inert (C.`∀ s)
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-id hB ok , NW.id★) =
  plan-id
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-gen {A = B₀} {s = s} hA occ s⊢ ,
     NW.gen {A = B₁} sⁿ) =
  plan-inert (C.gen B₁ s)
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-untag hG gG ok , NW.untag gG′) =
  plan-untag
target-narrowing-administration-plan {p = p} {q = q}
    prefix wfΣ seal★
    (C.cast-seq (C.cast-untag hG gG ok) t⊢ ,
     gG′ NW.？︔ gⁿ) =
  plan-seq (plan-untag {q = r})
    (target-strict-cross-narrowing-plan {p = r} {q = q} t⊢ gⁿ)
  where
    r = target-strict-cross-narrowing-ground-midpoint gG t⊢ gⁿ p q
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-seal {α = α} {A = B₀} hB αB∈Σ ok ,
     NW.sealⁿ B₁ α′) =
  plan-inert (C.seal B₁ α′)
target-narrowing-administration-plan prefix wfΣ seal★
    (C.cast-seq s⊢ (C.cast-seal hX αX∈Σ seal-ok) ,
     sⁿ NW.︔seal α)
  = ⊥-elim
      (strict-narrowing-seal-seq⊥
        prefix wfΣ seal★ s⊢ αX∈Σ seal-ok sⁿ)


target-widening-administration-plan :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  (c⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C) →
  TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-id hB ok , NW.cross (NW.id-＇ α)) =
  plan-id
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-id hB ok , NW.cross (NW.id-‵ ι)) =
  plan-id
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-fun {s = s} {t = t} s⊢ t⊢ ,
     NW.cross (sⁿ NW.↦ tʷ)) =
  plan-inert (s C.↦ t)
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-all {s = s} c⊢ , NW.cross (NW.`∀ sʷ)) =
  plan-inert (C.`∀ s)
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-id hB ok , NW.id★) =
  plan-id
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-inst {s = s} hB occ s⊢ , NW.inst sʷ) =
  plan-inst
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-tag {G = G} hG gG⊢ ok , NW.tag gG) =
  plan-inert (G C.!)
target-widening-administration-plan {p = p} {q = q}
    prefix wfΣ seal★
    (C.cast-seq s⊢ (C.cast-tag {G = G} hG gG ok) ,
     gʷ NW.︔ gG′ !) =
  plan-seq
    (target-strict-cross-widening-plan {p = p} {q = r} s⊢ gʷ)
    (plan-inert {p = r} (G C.!))
  where
    r = target-strict-cross-widening-ground-midpoint gG s⊢ gʷ p q
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-unseal {α = α} {A = B₀} hB αB∈Σ seal-ok ,
     NW.unsealʷ α′ B₁) =
  plan-unseal
target-widening-administration-plan prefix wfΣ seal★
    (C.cast-seq (C.cast-unseal hX αX∈Σ seal-ok) t⊢ ,
     NW.unseal︔_ α tʷ)
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
    }

module proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointProof where

-- File Charter:
--   * Proves source narrowing/widening sequence midpoint recovery.
--   * Uses sparse final-store uniqueness and ambient-prefix inclusion to
--     eliminate terminal seal/unseal sequence shapes.
--   * Handles every strict-cross shape explicitly and has no catch-up
--     implementation dependency.

open import Data.Empty using (⊥; ⊥-elim)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; _!
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
  )
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; widening
  ; shape-tag-var
  ; shape-tag-base
  ; shape-tag-fun
  )
open import Data.Product using (_,_; _×_; Σ-syntax)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; id★ˢ
  ; comp-id★
  ; comp-tag-id★
  ; comp-tag-⇛-id★
  ; comp-tagˣ-id★
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; id★
  ; tag_⇛_
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( Narrowing
  ; StrictCrossNarrowing
  ; StrictCrossWidening
  ; StrictNarrowing
  ; StrictWidening
  ; Widening
  ; fun-untag-gen
  ; inst-fun-tag
  ; cn-all
  ; cn-funˡ
  ; cn-funʳ
  ; cw-all
  ; cw-funˡ
  ; cw-funʳ
  ; strict-crossⁿ
  ; strict-crossʷ
  ; strict-gen
  ; strict-inst
  ; strict-seal
  ; strict-seal-seq
  ; strict-tag
  ; strict-tag-seq
  ; strict-unseal
  ; strict-unseal-seq
  ; strict-untag
  ; strict-untag-seq
  ; unseal︔_
  ; _︔seal_
  ; _？︔_
  ; _︔_!
  )
open import NuStore using (StoreWf; unique)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Source.CastSequence.NuImprecisionSourceCastSequenceMidpointDef using
  (SourceCastSequenceMidpointᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-assoc-right)
import Types as T


strict-cross-narrowing-to-star⊥ :
  ∀ {μ Δ Σ A s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ T.★ →
  StrictCrossNarrowing s →
  ⊥
strict-cross-narrowing-to-star⊥ () (cn-funˡ sʷ tⁿ)
strict-cross-narrowing-to-star⊥ () (cn-funʳ sʷ tⁿ)
strict-cross-narrowing-to-star⊥ () (cn-all tⁿ)


strict-cross-widening-from-star⊥ :
  ∀ {μ Δ Σ B s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ T.★ =⇒ B →
  StrictCrossWidening s →
  ⊥
strict-cross-widening-from-star⊥ () (cw-funˡ sⁿ tʷ)
strict-cross-widening-from-star⊥ () (cw-funʳ sⁿ tʷ)
strict-cross-widening-from-star⊥ () (cw-all tʷ)


strict-narrowing-to-star⊥ :
  ∀ {μ Δ Σ A s} →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A =⇒ T.★ →
  StrictNarrowing s →
  ⊥
strict-narrowing-to-star⊥ ()
  (strict-crossⁿ (cn-funˡ sʷ tⁿ))
strict-narrowing-to-star⊥ ()
  (strict-crossⁿ (cn-funʳ sʷ tⁿ))
strict-narrowing-to-star⊥ ()
  (strict-crossⁿ (cn-all sⁿ))
strict-narrowing-to-star⊥ () (strict-gen sⁿ)
strict-narrowing-to-star⊥
    (C.cast-untag hG () tag-ok) (strict-untag gG)
strict-narrowing-to-star⊥
    (C.cast-seq s⊢ t⊢) (strict-untag-seq gG gⁿ) =
  strict-cross-narrowing-to-star⊥ t⊢ gⁿ
strict-narrowing-to-star⊥ () (strict-seal A α)
strict-narrowing-to-star⊥
    (C.cast-seq s⊢ ()) (strict-seal-seq sⁿ α)


strict-widening-from-star⊥ :
  ∀ {μ Δ Σ B t} →
  μ ∣ Δ ∣ Σ ⊢ t ∶ T.★ =⇒ B →
  StrictWidening t →
  ⊥
strict-widening-from-star⊥ ()
  (strict-crossʷ (cw-funˡ sⁿ tʷ))
strict-widening-from-star⊥ ()
  (strict-crossʷ (cw-funʳ sⁿ tʷ))
strict-widening-from-star⊥ ()
  (strict-crossʷ (cw-all tʷ))
strict-widening-from-star⊥ () (strict-inst tʷ)
strict-widening-from-star⊥
    (C.cast-tag hG () tag-ok) (strict-tag gG)
strict-widening-from-star⊥
    (C.cast-seq s⊢ t⊢) (strict-tag-seq gʷ gG) =
  strict-cross-widening-from-star⊥ s⊢ gʷ
strict-widening-from-star⊥ () (strict-unseal α A)
strict-widening-from-star⊥
    (C.cast-seq () t⊢) (strict-unseal-seq α tʷ)


strict-cross-narrowing-ground-midpoint :
  ∀ {Φ Δᴸ Δᴿ μ Σ G B t} →
  T.Ground G →
  μ ∣ Δᴸ ∣ Σ ⊢ t ∶ G =⇒ B →
  StrictCrossNarrowing t →
  Φ ∣ Δᴸ ⊢ G ⊑ T.★ ⊣ Δᴿ
strict-cross-narrowing-ground-midpoint
    (T.＇ α) () (cn-funˡ sʷ tⁿ)
strict-cross-narrowing-ground-midpoint
    (T.＇ α) () (cn-funʳ sʷ tⁿ)
strict-cross-narrowing-ground-midpoint
    (T.＇ α) () (cn-all tⁿ)
strict-cross-narrowing-ground-midpoint
    (T.‵ ι) () (cn-funˡ sʷ tⁿ)
strict-cross-narrowing-ground-midpoint
    (T.‵ ι) () (cn-funʳ sʷ tⁿ)
strict-cross-narrowing-ground-midpoint
    (T.‵ ι) () (cn-all tⁿ)
strict-cross-narrowing-ground-midpoint
    T.★⇒★ t⊢ (cn-funˡ sʷ tⁿ) =
  tag id★ ⇛ id★
strict-cross-narrowing-ground-midpoint
    T.★⇒★ t⊢ (cn-funʳ sʷ tⁿ) =
  tag id★ ⇛ id★
strict-cross-narrowing-ground-midpoint
    T.★⇒★ () (cn-all tⁿ)


strict-cross-widening-ground-midpoint :
  ∀ {Φ Δᴸ Δᴿ μ Σ A G s} →
  T.Ground G →
  μ ∣ Δᴸ ∣ Σ ⊢ s ∶ A =⇒ G →
  StrictCrossWidening s →
  Φ ∣ Δᴸ ⊢ G ⊑ T.★ ⊣ Δᴿ
strict-cross-widening-ground-midpoint
    (T.＇ α) () (cw-funˡ sⁿ tʷ)
strict-cross-widening-ground-midpoint
    (T.＇ α) () (cw-funʳ sⁿ tʷ)
strict-cross-widening-ground-midpoint
    (T.＇ α) () (cw-all tʷ)
strict-cross-widening-ground-midpoint
    (T.‵ ι) () (cw-funˡ sⁿ tʷ)
strict-cross-widening-ground-midpoint
    (T.‵ ι) () (cw-funʳ sⁿ tʷ)
strict-cross-widening-ground-midpoint
    (T.‵ ι) () (cw-all tʷ)
strict-cross-widening-ground-midpoint
    T.★⇒★ s⊢ (cw-funˡ sⁿ tʷ) =
  tag id★ ⇛ id★
strict-cross-widening-ground-midpoint
    T.★⇒★ s⊢ (cw-funʳ sⁿ tʷ) =
  tag id★ ⇛ id★
strict-cross-widening-ground-midpoint
    T.★⇒★ () (cw-all tʷ)


tag-widening-midpoint-right-triangle :
  ∀ {Φ Δᴸ Δᴿ μ Σ A G s t-shape}
    (gG : T.Ground G)
    (s⊢ : μ ∣ Δᴸ ∣ Σ ⊢ s ∶ A =⇒ G)
    (sʷ : StrictCrossWidening s) →
  widening ⊢ᶜ G ! ⦂ t-shape →
  t-shape ； id★ˢ ≋
    ⌊ strict-cross-widening-ground-midpoint
        {Φ = Φ} {Δᴿ = Δᴿ} gG s⊢ sʷ ⌋
tag-widening-midpoint-right-triangle
    (T.＇ α) () (cw-funˡ sⁿ tʷ) tag-shape
tag-widening-midpoint-right-triangle
    (T.＇ α) () (cw-funʳ sⁿ tʷ) tag-shape
tag-widening-midpoint-right-triangle
    (T.＇ α) () (cw-all tʷ) tag-shape
tag-widening-midpoint-right-triangle
    (T.‵ ι) () (cw-funˡ sⁿ tʷ) tag-shape
tag-widening-midpoint-right-triangle
    (T.‵ ι) () (cw-funʳ sⁿ tʷ) tag-shape
tag-widening-midpoint-right-triangle
    (T.‵ ι) () (cw-all tʷ) tag-shape
tag-widening-midpoint-right-triangle
    T.★⇒★ s⊢ (cw-funˡ sⁿ tʷ) shape-tag-fun =
  comp-tag-⇛-id★ comp-id★ comp-id★
tag-widening-midpoint-right-triangle
    T.★⇒★ s⊢ (cw-funʳ sⁿ tʷ) shape-tag-fun =
  comp-tag-⇛-id★ comp-id★ comp-id★
tag-widening-midpoint-right-triangle
    T.★⇒★ () (cw-all tʷ) tag-shape


source-narrowing-sequence-midpoint :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A C B B′ : Ty} {s t : Coercion} {μ : ModeEnv} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A =⇒ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C =⇒ B →
  Narrowing (s ︔ t) →
  Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ
source-narrowing-sequence-midpoint
    prefix coherent exclusive wfΣ mode seal★
    (C.cast-untag hG gG tag-ok) t⊢
    (gG′ ？︔ tⁿ) id★ q =
  strict-cross-narrowing-ground-midpoint gG t⊢ tⁿ
source-narrowing-sequence-midpoint
    prefix coherent exclusive wfΣ mode seal★
    (C.cast-untag hG gG tag-ok)
    (C.cast-gen hA occ s⊢)
    (fun-untag-gen safe) id★ q =
  tag_⇛_ id★ id★
source-narrowing-sequence-midpoint
    prefix coherent exclusive wfΣ mode seal★ s⊢
    (C.cast-seal hX αX∈Σ seal-ok)
    (sⁿ ︔seal α) p q
    rewrite unique wfΣ
      (leftStoreⁱ-prefix-inclusion prefix αX∈Σ)
      (leftStoreⁱ-prefix-inclusion prefix (seal★ α seal-ok)) =
  ⊥-elim (strict-narrowing-to-star⊥ s⊢ sⁿ)


source-widening-sequence-midpoint :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {A C B B′ : Ty} {s t : Coercion} {μ : ModeEnv}
    {s-shape t-shape sequence-shape : ImprecisionShape} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ A =⇒ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C =⇒ B →
  Widening (s ︔ t) →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ s ⦂ s-shape →
  widening ⊢ᶜ t ⦂ t-shape →
  s-shape ； t-shape ≋ sequence-shape →
  sequence-shape ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Σ[ middle ∈ (Φ ∣ Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) ]
    (s-shape ； ⌊ middle ⌋ ≋ ⌊ p ⌋) ×
    (t-shape ； ⌊ q ⌋ ≋ ⌊ middle ⌋)
source-widening-sequence-midpoint
    prefix coherent exclusive wfΣ mode seal★ s⊢
    (C.cast-tag hG gG tag-ok)
    (sʷ ︔ gG′ !) p id★
    s-shape-proof tag-shape sequence-comp outer-comp =
  middle ,
  compose-assoc-right sequence-comp outer-comp right-triangle ,
  right-triangle
  where
  middle =
    strict-cross-widening-ground-midpoint gG s⊢ sʷ
  right-triangle =
    tag-widening-midpoint-right-triangle
      gG s⊢ sʷ tag-shape
source-widening-sequence-midpoint
    prefix coherent exclusive wfΣ mode seal★
    (C.cast-inst hB occ s⊢)
    (C.cast-tag hG gG tag-ok)
    (inst-fun-tag safe) p id★
    s-shape-proof shape-tag-fun sequence-comp outer-comp =
  tag_⇛_ id★ id★ ,
  compose-assoc-right sequence-comp outer-comp right-triangle ,
  right-triangle
  where
  right-triangle =
    comp-tag-⇛-id★ comp-id★ comp-id★
source-widening-sequence-midpoint
    prefix coherent exclusive wfΣ mode seal★
    (C.cast-unseal hX αX∈Σ seal-ok) t⊢
    (unseal︔_ α tʷ) p q
    s-shape-proof t-shape-proof sequence-comp outer-comp
    rewrite unique wfΣ
      (leftStoreⁱ-prefix-inclusion prefix αX∈Σ)
      (leftStoreⁱ-prefix-inclusion prefix (seal★ α seal-ok)) =
  ⊥-elim (strict-widening-from-star⊥ t⊢ tʷ)


source-cast-sequence-midpoint-proofᵀ :
  SourceCastSequenceMidpointᵀ
source-cast-sequence-midpoint-proofᵀ =
  record
    { narrowing-midpoint = source-narrowing-sequence-midpoint
    ; widening-midpoint = source-widening-sequence-midpoint
    }

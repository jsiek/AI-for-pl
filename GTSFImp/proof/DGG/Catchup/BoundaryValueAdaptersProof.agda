module proof.DGG.Catchup.BoundaryValueAdaptersProof where

-- File Charter:
--   * Adapts structural right catch-up results to every public boundary kind.
--   * Pulls structural target extensions back through forward tag rebases.
--   * Embeds the resulting enclosing trace into parked evolution.

open import Data.List using ([])
open import Data.Maybe using (Maybe; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import Types using (Ty; TyCtx; TyVar)
open import CastTerms using (Term)
open import Consistency using (wk↪ᵗ)
open import Reduction using
  (StoreChanges; _∷_; keep; bind; applyStore)
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Parked.ParkedWorldDef using (ParkedWorld)
open import proof.DGG.CatchupToMorePreciseDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (structural-world-extendᴿ)
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof using
  (structural-tag-rebase-atᴸ-pullback)
open import proof.DGG.Catchup.StructuralRightParkedEvolveProof using
  (StructuralRightParkedEvolveᵀ)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (StructuralCatchupRightResult)


record StructuralForwardTagRebaseAtᴸPullbackResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    (rb : CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?) : Set₁ where
  field
    W′ : CTI2.World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.TagRebaseAtᴸ W′ Wᵖ′ Xᴸ?
      (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


structural-forward-tag-rebase-atᴸ-pullback :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → StructuralForwardTagRebaseAtᴸPullbackResult planᵖ rb
structural-forward-tag-rebase-atᴸ-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-forward-tag-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    with structural-forward-tag-rebase-atᴸ-pullback planᵖ rb
structural-forward-tag-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-forward-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    CTI2.tag-rebase-idᴸ
    with structural-forward-tag-rebase-atᴸ-pullback
      planᵖ CTI2.tag-rebase-idᴸ
structural-forward-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    CTI2.tag-rebase-idᴸ
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }
structural-forward-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-varᴸ rb)
    with structural-forward-tag-rebase-atᴸ-pullback planᵖ
      (CTI2.tag-rebase-varᴸ (TE.pullbackRebaseAt insᵖ rb))
structural-forward-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-varᴸ rb)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  ins = TE.pullbackRebaseTargetInsert insᵖ rb

  follows =
    trans followsᵖ
      (cong (applyStore (bind B)) (CTI2T.rebase-target-store rb))
structural-forward-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    with structural-forward-tag-rebase-atᴸ-pullback planᵖ
      (CTI2.tag-rebase-onlyᴸ
        (TE.insert-to-starᴸ insᵖ to-star)
        (TE.insert-disalignedᴸ insᵖ disaligned)
        (TE.insert-represented★ᴸ insᵖ represented))
structural-forward-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }


mapPivotChanges-nothing : ∀ {Δ Δ′}
  → (χs : StoreChanges Δ Δ′)
  → mapPivotChanges χs nothing ≡ nothing
mapPivotChanges-nothing R.[] = refl
mapPivotChanges-nothing (keep ∷ χs) = mapPivotChanges-nothing χs
mapPivotChanges-nothing (bind B ∷ χs) = mapPivotChanges-nothing χs


same-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → StructuralCatchupRightResult W [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = W} {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {V = V} {M′ = M′} {A = A} {B = B}
same-boundary-value-adapter embed parked child =
  StructuralCatchupRightResult.Δᴿ′ child ,
  χs ,
  StructuralCatchupRightResult.N′ child ,
  StructuralCatchupRightResult.Δ′ child ,
  StructuralCatchupRightResult.W′ child ,
  StructuralCatchupRightResult.W′ child ,
  nothing ,
  boundary-refl ,
  q′ ,
  sym (mapPivotChanges-nothing χs) ,
  StructuralCatchupRightResult.post-reduction child ,
  StructuralCatchupRightResult.final-value child ,
  embed parked plan ,
  plan ,
  plan ,
  StructuralCatchupRightResult.final-relation child
  where
  χs = StructuralCatchupRightResult.χs child
  plan = StructuralCatchupRightResult.structural-ext child
  q′ = ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _


source-reveal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-reveal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
source-reveal-boundary-value-adapter embed parked mono rb child
    with structural-forward-tag-rebase-atᴸ-pullback planᵖ rb
  where
  planᵖ = StructuralCatchupRightResult.structural-ext child
source-reveal-boundary-value-adapter embed parked mono rb child
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  StructuralCatchupRightResult.Δᴿ′ child ,
  χs ,
  StructuralCatchupRightResult.N′ child ,
  StructuralCatchupRightResult.Δ′ child ,
  W′ ,
  StructuralCatchupRightResult.W′ child ,
  mapPivotChanges χs _ ,
  boundary-source-reveal (mono′ mono) rb′ ,
  q′ ,
  refl ,
  StructuralCatchupRightResult.post-reduction child ,
  StructuralCatchupRightResult.final-value child ,
  embed parked plan ,
  plan ,
  planᵖ ,
  StructuralCatchupRightResult.final-relation child
  where
  χs = StructuralCatchupRightResult.χs child
  planᵖ = StructuralCatchupRightResult.structural-ext child
  q′ = ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) _


target-reveal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = target-reveal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
target-reveal-boundary-value-adapter embed parked mono rb child
    with structural-forward-tag-rebase-atᴸ-pullback planᵖ rb
  where
  planᵖ = StructuralCatchupRightResult.structural-ext child
target-reveal-boundary-value-adapter embed parked mono rb child
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  StructuralCatchupRightResult.Δᴿ′ child ,
  χs ,
  StructuralCatchupRightResult.N′ child ,
  StructuralCatchupRightResult.Δ′ child ,
  W′ ,
  StructuralCatchupRightResult.W′ child ,
  mapPivotChanges χs _ ,
  boundary-target-reveal (mono′ mono) rb′ ,
  q′ ,
  refl ,
  StructuralCatchupRightResult.post-reduction child ,
  StructuralCatchupRightResult.final-value child ,
  embed parked plan ,
  plan ,
  planᵖ ,
  StructuralCatchupRightResult.final-relation child
  where
  χs = StructuralCatchupRightResult.χs child
  planᵖ = StructuralCatchupRightResult.structural-ext child
  q′ = ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) _


source-conceal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = source-conceal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
source-conceal-boundary-value-adapter embed parked mono rb child
    with structural-tag-rebase-atᴸ-pullback planᵖ rb
  where
  planᵖ = StructuralCatchupRightResult.structural-ext child
source-conceal-boundary-value-adapter embed parked mono rb child
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  StructuralCatchupRightResult.Δᴿ′ child ,
  χs ,
  StructuralCatchupRightResult.N′ child ,
  StructuralCatchupRightResult.Δ′ child ,
  W′ ,
  StructuralCatchupRightResult.W′ child ,
  mapPivotChanges χs _ ,
  boundary-source-conceal (mono′ mono) rb′ ,
  q′ ,
  refl ,
  StructuralCatchupRightResult.post-reduction child ,
  StructuralCatchupRightResult.final-value child ,
  embed parked plan ,
  plan ,
  planᵖ ,
  StructuralCatchupRightResult.final-relation child
  where
  χs = StructuralCatchupRightResult.χs child
  planᵖ = StructuralCatchupRightResult.structural-ext child
  q′ = ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) _


target-conceal-boundary-value-adapter : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ B}
  → StructuralRightParkedEvolveᵀ
  → ParkedWorld W
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → StructuralCatchupRightResult Wᵖ [] V M′ p
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = target-conceal-boundary}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
target-conceal-boundary-value-adapter embed parked mono rb child
    with structural-tag-rebase-atᴸ-pullback planᵖ rb
  where
  planᵖ = StructuralCatchupRightResult.structural-ext child
target-conceal-boundary-value-adapter embed parked mono rb child
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  StructuralCatchupRightResult.Δᴿ′ child ,
  χs ,
  StructuralCatchupRightResult.N′ child ,
  StructuralCatchupRightResult.Δ′ child ,
  W′ ,
  StructuralCatchupRightResult.W′ child ,
  mapPivotChanges χs _ ,
  boundary-target-conceal (mono′ mono) rb′ ,
  q′ ,
  refl ,
  StructuralCatchupRightResult.post-reduction child ,
  StructuralCatchupRightResult.final-value child ,
  embed parked plan ,
  plan ,
  planᵖ ,
  StructuralCatchupRightResult.final-relation child
  where
  χs = StructuralCatchupRightResult.χs child
  planᵖ = StructuralCatchupRightResult.structural-ext child
  q′ = ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) _

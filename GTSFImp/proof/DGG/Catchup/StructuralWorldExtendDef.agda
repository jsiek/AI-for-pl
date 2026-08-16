module proof.DGG.Catchup.StructuralWorldExtendDef where

-- File Charter:
--   * Records the keep/bind insertion history of a right-world extension.
--   * Retains center insertion evidence needed by source-wrapper recursion.

import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe)

open import Types using (Ty; TyVar)
open import Consistency using (_↪ᵗ_; keep; wk↪ᵗ; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTys)
open import proof.Reduction using (_++χ_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open CTI2 using (World)


mapPivotChanges : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → Maybe (TyVar Δ)
  → Maybe (TyVar Δ′)
mapPivotChanges [] pivot = pivot
mapPivotChanges (keep ∷ χs) pivot = mapPivotChanges χs pivot
mapPivotChanges (bind A ∷ χs) pivot =
  mapPivotChanges χs (TE.mapPivot (toRenameᵗ wk↪ᵗ) pivot)


mapVarChanges : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → TyVar Δ
  → TyVar Δ′
mapVarChanges [] X = X
mapVarChanges (keep ∷ χs) X = mapVarChanges χs X
mapVarChanges (bind A ∷ χs) X =
  mapVarChanges χs (toRenameᵗ wk↪ᵗ X)


mapRevealChanges : ∀ {Δ Δ′} {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → Conv↑ Δ A B
  → Conv↑ Δ′ (applyTys χs A) (applyTys χs B)
mapRevealChanges [] c = c
mapRevealChanges (keep ∷ χs) c = mapRevealChanges χs c
mapRevealChanges (bind A ∷ χs) c =
  mapRevealChanges χs (rename↑ Fin.suc c)


mapConcealChanges : ∀ {Δ Δ′} {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → Conv↓ Δ A B
  → Conv↓ Δ′ (applyTys χs A) (applyTys χs B)
mapConcealChanges [] c = c
mapConcealChanges (keep ∷ χs) c = mapConcealChanges χs c
mapConcealChanges (bind A ∷ χs) c =
  mapConcealChanges χs (rename↓ Fin.suc c)


mapPivotChanges-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → (pivot : Maybe (TyVar Δ₀))
  → mapPivotChanges (χs ++χ ψs) pivot
      ≡ mapPivotChanges ψs (mapPivotChanges χs pivot)
mapPivotChanges-++ [] ψs pivot = refl
mapPivotChanges-++ (keep ∷ χs) ψs pivot =
  mapPivotChanges-++ χs ψs pivot
mapPivotChanges-++ (bind A ∷ χs) ψs pivot =
  mapPivotChanges-++ χs ψs (TE.mapPivot (toRenameᵗ wk↪ᵗ) pivot)



data StructuralWorldExtendᴿ {Δᴸ} :
    ∀ {Δᴿ Δᴿ′ Δ Δ′}
    → StoreChanges Δᴿ Δᴿ′
    → World Δᴸ Δᴿ Δ
    → World Δᴸ Δᴿ′ Δ′
    → Set₁ where

  structural-[] : ∀ {Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    → StructuralWorldExtendᴿ [] W W

  structural-keep : ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    → StructuralWorldExtendᴿ χs W W′
    → StructuralWorldExtendᴿ (keep ∷ χs) W W′

  structural-bind : ∀ {Δᴿ Δᴿ′ Δ Δ₁ Δ′}
      {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
      {χs : StoreChanges (suc Δᴿ) Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ (suc Δᴿ) Δ₁}
      {W′ : World Δᴸ Δᴿ′ Δ′}
    → TE.TargetInsert wk↪ᵗ π W W₁
    → CTI2.targetStoreʷ W₁ ≡
        applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)
    → StructuralWorldExtendᴿ χs W₁ W′
    → StructuralWorldExtendᴿ (bind B ∷ χs) W W′


data FrozenEmbedding : ℕ → ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Set where
  frozen-embedding-zero : ∀ {Δ Δ′} {π : Δ ↪ᵗ Δ′}
    → FrozenEmbedding zero π

  frozen-embedding-keep : ∀ {k Δ Δ′} {π : Δ ↪ᵗ Δ′}
    → FrozenEmbedding k π
    → FrozenEmbedding (suc k) (keep π)


data FrozenStructuralTraceᴿ {Δᴸ} :
    ∀ {Δᴿ Δᴿ′ Δ Δ′}
    → {χs : StoreChanges Δᴿ Δᴿ′}
    → {W : World Δᴸ Δᴿ Δ}
    → {W′ : World Δᴸ Δᴿ′ Δ′}
    → ℕ
    → StructuralWorldExtendᴿ χs W W′
    → Set₁ where

  frozen-trace-[] : ∀ {k Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    → FrozenStructuralTraceᴿ k (structural-[] {W = W})

  frozen-trace-keep : ∀ {k Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
      {plan : StructuralWorldExtendᴿ χs W W′}
    → FrozenStructuralTraceᴿ k plan
    → FrozenStructuralTraceᴿ k (structural-keep plan)

  frozen-trace-bind : ∀ {k Δᴿ Δᴿ′ Δ Δ₁ Δ′}
      {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
      {χs : StoreChanges (suc Δᴿ) Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ (suc Δᴿ) Δ₁}
      {W′ : World Δᴸ Δᴿ′ Δ′}
      {ins : TE.TargetInsert wk↪ᵗ π W W₁}
      {follows : CTI2.targetStoreʷ W₁ ≡
        applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)}
      {plan : StructuralWorldExtendᴿ χs W₁ W′}
    → FrozenEmbedding k π
    → FrozenStructuralTraceᴿ k plan
    → FrozenStructuralTraceᴿ k (structural-bind ins follows plan)


frozen-trace-zero : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → FrozenStructuralTraceᴿ zero plan
frozen-trace-zero structural-[] = frozen-trace-[]
frozen-trace-zero (structural-keep plan) =
  frozen-trace-keep (frozen-trace-zero plan)
frozen-trace-zero (structural-bind ins follows plan) =
  frozen-trace-bind frozen-embedding-zero (frozen-trace-zero plan)


record StructuralRebaseAtᴸResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : World Δᴸ Δᴿ Δ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?) : Set₁ where
  field
    Wᵖ′ : World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.RebaseAtᴸ W′ Wᵖ′ Xᴸ?
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralRebaseAtᴸPullbackResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ} {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : World Δᴸ Δᴿ Δ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?) : Set₁ where
  field
    W′ : World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.RebaseAtᴸ W′ Wᵖ′ Xᴸ?
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralRebaseAtᴿResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : World Δᴸ Δᴿ Δ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    (rb : CTI2.RebaseAtᴿ W Wᵖ Xᴿ?) : Set₁ where
  field
    Wᵖ′ : World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.RebaseAtᴿ W′ Wᵖ′ (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralRebaseAtᴿPullbackResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ} {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : World Δᴸ Δᴿ Δ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    (rb : CTI2.RebaseAtᴿ W Wᵖ Xᴿ?) : Set₁ where
  field
    W′ : World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.RebaseAtᴿ W′ Wᵖ′ (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralReverseRebaseAtᴿResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : World Δᴸ Δᴿ Δ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    (rb : CTI2.RebaseAtᴿ Wᵖ W Xᴿ?) : Set₁ where
  field
    Wᵖ′ : World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.RebaseAtᴿ Wᵖ′ W′ (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralReverseRebaseAtᴿPullbackResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ} {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : World Δᴸ Δᴿ Δ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    (rb : CTI2.RebaseAtᴿ Wᵖ W Xᴿ?) : Set₁ where
  field
    W′ : World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.RebaseAtᴿ Wᵖ′ W′ (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralRebaseAtResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ) : Set₁ where
  field
    Wᵖ′ : World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.RebaseAt W′ Wᵖ′ Xᴸ (mapVarChanges χs Xᴿ)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralRebaseAtPullbackResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ} {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ) : Set₁ where
  field
    W′ : World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.RebaseAt W′ Wᵖ′ Xᴸ (mapVarChanges χs Xᴿ)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralReverseRebaseAtResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ) : Set₁ where
  field
    Wᵖ′ : World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.RebaseAt Wᵖ′ W′ Xᴸ (mapVarChanges χs Xᴿ)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralReverseRebaseAtPullbackResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : World Δᴸ Δᴿ Δ} {Wᵖ′ : World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : World Δᴸ Δᴿ Δ} {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ) : Set₁ where
  field
    W′ : World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.RebaseAt Wᵖ′ W′ Xᴸ (mapVarChanges χs Xᴿ)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′

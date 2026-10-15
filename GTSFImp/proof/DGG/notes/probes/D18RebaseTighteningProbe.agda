module D18RebaseTighteningProbe where

-- File Charter:
--   * Drafts D18's functional-origin version of RebaseAt and its one-sided
--     wrappers without changing the live DGG relation.
--   * Checks exact origin uniqueness, source-pivot and mark coherence, and
--     the generic transport that closes the T12 W/Wcore cycle.
--   * Checks that unqualified functional origin determination cannot retain
--     both live Instance-B rebases, identifying the required migration split.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types using (TyCtx; TyVar; ★)
open import Consistency using (toRenameᵗ)
open import Imprecision using (X⊑★)
import proof.DGG.CtxImp as CTX
import proof.DGG.TerminusRebuildProbe as T6


------------------------------------------------------------------------
-- Functional origin schedule
------------------------------------------------------------------------

record OriginPolicy : Set₁ where
  field
    originAt : ∀ {Δᴸ Δᴿ Δ}
      → CTX.World Δᴸ Δᴿ Δ
      → TyVar Δᴸ
      → TyVar Δᴿ
      → CTX.World Δᴸ Δᴿ Δ

open OriginPolicy public


------------------------------------------------------------------------
-- Verbatim D18 draft surface
------------------------------------------------------------------------

record RebaseAt (policy : OriginPolicy) {Δᴸ Δᴿ Δ}
    (W W′ : CTX.World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-at
  field
    origin-determined : W ≡ originAt policy W′ Xᴸ Xᴿ
    sameRuntime : CTX.SameRuntime W W′
    ηᴸ-off-pivot : ∀ {Y} → Y ≢ Xᴸ
      → toRenameᵗ (CTX.ηᴸʷ W′) Y ≡ toRenameᵗ (CTX.ηᴸʷ W) Y
    ηᴿ-frozen : ∀ Y
      → toRenameᵗ (CTX.ηᴿʷ W′) Y ≡ toRenameᵗ (CTX.ηᴿʷ W) Y
    pivotAligned :
      toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ ≡
        toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ
    storeRepresentations : CTX.StoreRepImp W′ Xᴸ Xᴿ

open RebaseAt public

sameWorldRebaseAt : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → W ≡ originAt policy W Xᴸ Xᴿ
  → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≡
      toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → RebaseAt policy W W Xᴸ Xᴿ
sameWorldRebaseAt origin aligned reps =
  rebase-at origin (CTX.same-runtime refl refl)
    (λ _ → refl) (λ _ → refl) aligned reps

data RebaseAtᴸ (policy : OriginPolicy) {Δᴸ Δᴿ Δ} :
    CTX.World Δᴸ Δᴿ Δ → CTX.World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Set where
  rebase-idᴸ : ∀ {W}
    → RebaseAtᴸ policy W W nothing

  rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt policy W W′ Xᴸ Xᴿ
    → RebaseAtᴸ policy W W′ (just Xᴸ)

  rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≢
          toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
    → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ CTX.⊑ᵂ⟨ W ⟩ ★
    → RebaseAtᴸ policy W W (just Xᴸ)

data TagRebaseAtᴸ (policy : OriginPolicy) {Δᴸ Δᴿ Δ} :
    CTX.World Δᴸ Δᴿ Δ → CTX.World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) → Set where
  tag-rebase-idᴸ : ∀ {W}
    → TagRebaseAtᴸ policy W W nothing nothing

  tag-rebase-varᴸ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt policy W W′ Xᴸ Xᴿ
    → TagRebaseAtᴸ policy W W′ (just Xᴸ) (just Xᴿ)

  tag-rebase-onlyᴸ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≢
          toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
    → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ CTX.⊑ᵂ⟨ W ⟩ ★
    → TagRebaseAtᴸ policy W W (just Xᴸ) nothing

forgetTagRebaseᴸ : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W W′ : CTX.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → TagRebaseAtᴸ policy W W′ Xᴸ? Xᴿ?
  → RebaseAtᴸ policy W W′ Xᴸ?
forgetTagRebaseᴸ tag-rebase-idᴸ = rebase-idᴸ
forgetTagRebaseᴸ (tag-rebase-varᴸ rb) = rebase-varᴸ rb
forgetTagRebaseᴸ (tag-rebase-onlyᴸ to-star disaligned represented) =
  rebase-onlyᴸ to-star disaligned represented

data RebaseAtᴿ (policy : OriginPolicy) {Δᴸ Δᴿ Δ} :
    CTX.World Δᴸ Δᴿ Δ → CTX.World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴿ) → Set where
  rebase-idᴿ : ∀ {W}
    → RebaseAtᴿ policy W W nothing

  rebase-varᴿ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAt policy W W′ Xᴸ Xᴿ
    → RebaseAtᴿ policy W W′ (just Xᴿ)


------------------------------------------------------------------------
-- Checked D18 payoffs
------------------------------------------------------------------------

origin-unique : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → RebaseAt policy W Wmid Xᴸ Xᴿ
  → RebaseAt policy Wcore Wmid Xᴸ Xᴿ
  → W ≡ Wcore
origin-unique outer inner =
  trans (origin-determined outer) (sym (origin-determined inner))

origin-source-pivot-unique : ∀ {Δᴸ Δᴿ Δ}
    {policy : OriginPolicy}
    {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → RebaseAt policy W Wmid Xᴸ Xᴿ
  → RebaseAt policy Wcore Wmid Xᴸ Xᴿ
  → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≡
      toRenameᵗ (CTX.ηᴸʷ Wcore) Xᴸ
origin-source-pivot-unique outer inner =
  cong (λ W′ → toRenameᵗ (CTX.ηᴸʷ W′) _)
    (origin-unique outer inner)

origin-marks-unique : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → RebaseAt policy W Wmid Xᴸ Xᴿ
  → RebaseAt policy Wcore Wmid Xᴸ Xᴿ
  → CTX.impEnvʷ W ≡ CTX.impEnvʷ Wcore
origin-marks-unique outer inner =
  cong CTX.impEnvʷ (origin-unique outer inner)

world-cycle-close : ∀ {Δᴸ Δᴿ Δ} {policy : OriginPolicy}
    {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    (P : CTX.World Δᴸ Δᴿ Δ → Set)
  → RebaseAt policy W Wmid Xᴸ Xᴿ
  → RebaseAt policy Wcore Wmid Xᴸ Xᴿ
  → P Wcore
  → P W
world-cycle-close P outer inner payload =
  subst P (sym (origin-unique outer inner)) payload


------------------------------------------------------------------------
-- Checked obstruction to applying the global form without migration
------------------------------------------------------------------------

zero≢suc : ∀ {n} {X : Fin.Fin n} → Fin.zero ≢ Fin.suc X
zero≢suc ()

instance-B-worlds-differ : T6.InstanceB.W ≢ T6.InstanceB.Wᵖ
instance-B-worlds-differ eq =
  zero≢suc
    (cong
      (λ W → toRenameᵗ (CTX.ηᴸʷ W) T6.InstanceB.X)
      eq)

current-global-origin-uniqueness-refuted :
  (∀ {Δᴸ Δᴿ Δ}
      {W Wcore Wmid : CTX.World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    → CTX.RebaseAt W Wmid Xᴸ Xᴿ
    → CTX.RebaseAt Wcore Wmid Xᴸ Xᴿ
    → W ≡ Wcore)
  → ⊥
current-global-origin-uniqueness-refuted unique =
  instance-B-worlds-differ
    (unique T6.InstanceB.rb-X-Y T6.InstanceB.rb-chain)

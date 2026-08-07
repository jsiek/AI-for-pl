module proof.DGG.Parked.ParkedWorldProof where

-- File Charter:
--   * Proves parked-world closure, context transport, obligation transport,
--     and geometry for the parked evolution interface.
--   * Builds the stage-1 right-extension record from right-only parked
--     evolution.
--   * Contains only total checked definitions and no permissive option.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Nat using (_≤_; s≤s; z≤n)
import Data.Nat as Nat
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using
  ( Ty
  ; TyVar
  ; _⇒_
  ; `∀
  ; ★
  ; ⇑ᵗ
  ; renameᵗ
  ; renameᵗ-comp
  ; renameᵗ-cong
  ; renameᵗ-shift
  )
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Imprecision using (X⊑X; X⊑★; _⊢_⊑_)
open import Reduction using (StoreChanges)
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Parked.ParkedWorldDef using
  ( MapCtxᴾᵀ
  ; ParkedEvolve
  ; ParkedFreshBothᴸᵀ
  ; ParkedFreshBothᴿᵀ
  ; ParkedFreshLeftᴸᵀ
  ; ParkedFreshRightᴿᵀ
  ; ParkedFreshZeroᵀ
  ; ParkedNoCrossingᵀ
  ; ParkedTargetIdentityᵀ
  ; ParkedTargetStableᵀ
  ; ParkedWorld
  ; ParkedWorldClosedᵀ
  ; RightOnlyParked→WorldExtendᴿᵀ
  ; Transport⊑ᴾᵀ
  ; WorldExtendᴿ→RightOnlyParkedᵀ
  ; _▶ᵛ_
  ; centerVarᴾ
  ; evolve-both-bind
  ; evolve-keepᴸ
  ; evolve-keepᴿ
  ; evolve-left-bind
  ; evolve-refl
  ; evolve-right-bind
  ; parked-both-bind
  ; parked-initial
  ; parked-left-bind
  ; parked-right-bind
  )
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑)
open import proof.TypeInTermSubst using
  (toRename-id-eq; toRename-keep-eq)

open CTI2 using
  ( CtxImp
  ; World
  ; ctx-imp
  ; embedᴸ
  ; embedᴿ
  ; impEnvʷ
  ; sourceStoreʷ
  ; targetStoreʷ
  ; _⊑ᵂ⟨_⟩_
  )


renameᵗ-skip-eq : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (skip η)) B
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
renameᵗ-skip-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))


embed-keep-shift : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
  → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
embed-keep-shift η A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
    (renameᵗ-shift (toRenameᵗ η) A)


≤-step : ∀ {m n} → m ≤ n → m ≤ Nat.suc n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)


embed≤ : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Δ ≤ Δ′
embed≤ empty = z≤n
embed≤ (keep η) = s≤s (embed≤ η)
embed≤ (skip η) = ≤-step (embed≤ η)


no-suc≤ : ∀ {Δ} → Nat.suc Δ ≤ Δ → ⊥
no-suc≤ {Nat.zero} ()
no-suc≤ {Nat.suc Δ} (s≤s sucΔ≤Δ) = no-suc≤ sucΔ≤Δ


no-suc↪ᵗ : ∀ {Δ} → Nat.suc Δ ↪ᵗ Δ → ⊥
no-suc↪ᵗ η = no-suc≤ (embed≤ η)


both-bind-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {C : Ty Δᴸ} {D : Ty Δᴿ}
  → C ⊑ᵂ⟨ W ⟩ D
  → ⇑ᵗ C ⊑ᵂ⟨ CTI2.bothBindWorld X⊑X W A B ⟩ ⇑ᵗ D
both-bind-⊑ᵂ {W = W} {A = A} {B = B} {C = C} {D = D} p =
  subst≡
    (λ L → impEnvʷ (CTI2.bothBindWorld X⊑X W A B) ⊢ L ⊑
      embedᴿ (CTI2.bothBindWorld X⊑X W A B) (⇑ᵗ D))
    (sym (embed-keep-shift (CTI2.ηᴸʷ W) C))
    (subst≡
      (λ R → impEnvʷ (CTI2.bothBindWorld X⊑X W A B) ⊢
        ⇑ᵗ (embedᴸ W C) ⊑ R)
      (sym (embed-keep-shift (CTI2.ηᴿʷ W) D))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))


right-bind-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ CTI2.rightOnlyWorld W B′ ⟩ ⇑ᵗ B
right-bind-⊑ᵂ {W = W} {B′ = B′} {A = A} {B = B} p =
  subst≡
    (λ L → impEnvʷ (CTI2.rightOnlyWorld W B′) ⊢ L ⊑
      embedᴿ (CTI2.rightOnlyWorld W B′) (⇑ᵗ B))
    (sym (renameᵗ-skip-eq (CTI2.ηᴸʷ W) A))
    (subst≡
      (λ R → impEnvʷ (CTI2.rightOnlyWorld W B′) ⊢
        ⇑ᵗ (embedᴸ W A) ⊑ R)
      (sym (embed-keep-shift (CTI2.ηᴿʷ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))


left-bind-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A′ : Ty Δᴸ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → ⇑ᵗ A ⊑ᵂ⟨ CTI2.leftOnlyWorld X⊑★ W A′ ⟩ B
left-bind-⊑ᵂ {W = W} {A′ = A′} {A = A} {B = B} p =
  subst≡
    (λ L → impEnvʷ (CTI2.leftOnlyWorld X⊑★ W A′) ⊢ L ⊑
      embedᴿ (CTI2.leftOnlyWorld X⊑★ W A′) B)
    (sym (embed-keep-shift (CTI2.ηᴸʷ W) A))
    (subst≡
      (λ R → impEnvʷ (CTI2.leftOnlyWorld X⊑★ W A′) ⊢
        ⇑ᵗ (embedᴸ W A) ⊑ R)
      (sym (renameᵗ-skip-eq (CTI2.ηᴿʷ W) B))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))


transport⊑ᴾ-proofᵀ : Transport⊑ᴾᵀ
transport⊑ᴾ-proofᵀ evolve-refl p = p
transport⊑ᴾ-proofᵀ (evolve-keepᴸ evol) p =
  transport⊑ᴾ-proofᵀ evol p
transport⊑ᴾ-proofᵀ (evolve-keepᴿ evol) p =
  transport⊑ᴾ-proofᵀ evol p
transport⊑ᴾ-proofᵀ {W = W} {W′ = W′} {A = C} {B = D}
    (evolve-both-bind {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {W = W} {W′ = W′} {A = A} {B = B} evol) p =
  transport⊑ᴾ-proofᵀ {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
    {W = CTI2.bothBindWorld X⊑X W A B} {W′ = W′}
    {A = ⇑ᵗ C} {B = ⇑ᵗ D} evol
    (both-bind-⊑ᵂ {W = W} {A = A} {B = B} {C = C} {D = D} p)
transport⊑ᴾ-proofᵀ {W = W} {W′ = W′} {A = C} {B = D}
    (evolve-left-bind {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {W = W} {W′ = W′} {A = A} evol) p =
  transport⊑ᴾ-proofᵀ {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
    {W = CTI2.leftOnlyWorld X⊑★ W A} {W′ = W′}
    {A = ⇑ᵗ C} {B = D} evol
    (left-bind-⊑ᵂ {W = W} {A′ = A} {A = C} {B = D} p)
transport⊑ᴾ-proofᵀ {W = W} {W′ = W′} {A = A} {B = B}
    (evolve-right-bind {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
      {W = W} {W′ = W′} {B = B′} evol) p =
  transport⊑ᴾ-proofᵀ {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
    {W = CTI2.rightOnlyWorld W B′} {W′ = W′}
    {A = A} {B = ⇑ᵗ B} evol
    (right-bind-⊑ᵂ {W = W} {B′ = B′} {A = A} {B = B} p)


mapCtxᴾ-proofᵀ : MapCtxᴾᵀ
mapCtxᴾ-proofᵀ evol [] = []
mapCtxᴾ-proofᵀ {χsᴸ = χsᴸ} {χsᴿ = χsᴿ} evol
    (ctx-imp A B p ∷ γ) =
  ctx-imp (R.applyTys χsᴸ A) (R.applyTys χsᴿ B)
    (transport⊑ᴾ-proofᵀ evol p) ∷ mapCtxᴾ-proofᵀ evol γ


parked-world-closed-proofᵀ : ParkedWorldClosedᵀ
parked-world-closed-proofᵀ pw evolve-refl = pw
parked-world-closed-proofᵀ pw (evolve-keepᴸ evol) =
  parked-world-closed-proofᵀ pw evol
parked-world-closed-proofᵀ pw (evolve-keepᴿ evol) =
  parked-world-closed-proofᵀ pw evol
parked-world-closed-proofᵀ pw (evolve-both-bind evol) =
  parked-world-closed-proofᵀ (parked-both-bind pw) evol
parked-world-closed-proofᵀ pw (evolve-left-bind evol) =
  parked-world-closed-proofᵀ (parked-left-bind pw) evol
parked-world-closed-proofᵀ pw (evolve-right-bind evol) =
  parked-world-closed-proofᵀ (parked-right-bind pw) evol


parked-target-stable-proofᵀ : ParkedTargetStableᵀ
parked-target-stable-proofᵀ evolve-refl Y = refl
parked-target-stable-proofᵀ (evolve-keepᴸ evol) Y =
  parked-target-stable-proofᵀ evol Y
parked-target-stable-proofᵀ (evolve-keepᴿ evol) Y =
  parked-target-stable-proofᵀ evol Y
parked-target-stable-proofᵀ (evolve-both-bind evol) Y =
  parked-target-stable-proofᵀ evol (Fin.suc Y)
parked-target-stable-proofᵀ (evolve-left-bind evol) Y =
  parked-target-stable-proofᵀ evol Y
parked-target-stable-proofᵀ (evolve-right-bind evol) Y =
  parked-target-stable-proofᵀ evol (Fin.suc Y)


parked-source-stable : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → (X : TyVar Δᴸ)
  → toRenameᵗ (CTI2.ηᴸʷ W′) (χsᴸ ▶ᵛ X)
      ≡ centerVarᴾ evol (toRenameᵗ (CTI2.ηᴸʷ W) X)
parked-source-stable evolve-refl X = refl
parked-source-stable (evolve-keepᴸ evol) X =
  parked-source-stable evol X
parked-source-stable (evolve-keepᴿ evol) X =
  parked-source-stable evol X
parked-source-stable (evolve-both-bind evol) X =
  parked-source-stable evol (Fin.suc X)
parked-source-stable (evolve-left-bind evol) X =
  parked-source-stable evol (Fin.suc X)
parked-source-stable (evolve-right-bind evol) X =
  parked-source-stable evol X


parked-target-identity-proofᵀ : ParkedTargetIdentityᵀ
parked-target-identity-proofᵀ parked-initial Y = toRename-id-eq Y
parked-target-identity-proofᵀ (parked-both-bind pw) zero = refl
parked-target-identity-proofᵀ (parked-both-bind pw) (Fin.suc Y) =
  cong Fin.suc (parked-target-identity-proofᵀ pw Y)
parked-target-identity-proofᵀ (parked-left-bind {W = W} pw) Y =
  ⊥-elim (no-suc↪ᵗ (CTI2.ηᴿʷ W))
parked-target-identity-proofᵀ (parked-right-bind pw) zero = refl
parked-target-identity-proofᵀ (parked-right-bind pw) (Fin.suc Y) =
  cong Fin.suc (parked-target-identity-proofᵀ pw Y)


parked-fresh-bothᴸ-proofᵀ : ParkedFreshBothᴸᵀ
parked-fresh-bothᴸ-proofᵀ evol =
  parked-source-stable evol zero


parked-fresh-bothᴿ-proofᵀ : ParkedFreshBothᴿᵀ
parked-fresh-bothᴿ-proofᵀ evol =
  parked-target-stable-proofᵀ evol zero


parked-fresh-rightᴿ-proofᵀ : ParkedFreshRightᴿᵀ
parked-fresh-rightᴿ-proofᵀ evol =
  parked-target-stable-proofᵀ evol zero


parked-fresh-leftᴸ-proofᵀ : ParkedFreshLeftᴸᵀ
parked-fresh-leftᴸ-proofᵀ evol =
  parked-source-stable evol zero


parked-fresh-zero-proofᵀ : ParkedFreshZeroᵀ
parked-fresh-zero-proofᵀ =
  parked-fresh-bothᴸ-proofᵀ ,
  parked-fresh-bothᴿ-proofᵀ ,
  parked-fresh-leftᴸ-proofᵀ ,
  parked-fresh-rightᴿ-proofᵀ


parked-no-crossing-proofᵀ : ParkedNoCrossingᵀ
parked-no-crossing-proofᵀ pw pw′ rb moved =
  moved (trans (parked-target-identity-proofᵀ pw′ _)
    (sym (parked-target-identity-proofᵀ pw _)))


right-source-kept : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ParkedEvolve R.[] χsᴿ W W′
  → sourceStoreʷ W′ ≡ sourceStoreʷ W
right-source-kept evolve-refl = refl
right-source-kept (evolve-keepᴿ evol) = right-source-kept evol
right-source-kept (evolve-right-bind evol) = right-source-kept evol


right-target-follows : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ParkedEvolve R.[] χsᴿ W W′
  → targetStoreʷ W′ ≡ R.applyStores χsᴿ (targetStoreʷ W)
right-target-follows evolve-refl = refl
right-target-follows (evolve-keepᴿ evol) = right-target-follows evol
right-target-follows (evolve-right-bind evol) =
  right-target-follows evol


right-only-parked→world-extendᴿ-proofᵀ :
  RightOnlyParked→WorldExtendᴿᵀ
right-only-parked→world-extendᴿ-proofᵀ evol = record
  { sourceStore-kept = right-source-kept evol
  ; targetStore-follows = right-target-follows evol
  ; transport⊑ᵂ = λ p → transport⊑ᴾ-proofᵀ evol p
  }


world-extendᴿ→right-only-parked-proofᵀ :
  WorldExtendᴿ→RightOnlyParkedᵀ
world-extendᴿ→right-only-parked-proofᵀ ext evol = evol

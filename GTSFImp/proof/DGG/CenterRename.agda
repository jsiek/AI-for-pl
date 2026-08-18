module proof.DGG.CenterRename where

-- File Charter:
--   * Transports cast-term-imprecision derivations along an
--     order-preserving injection of their center type context.
--   * Composes world embeddings, fills fresh centers with X⊑★, and
--     transports contexts, rebasing evidence, and recursive worlds.
--   * Exports the general center-renaming theorem and its weakening
--     specialization.

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
open import Conversion using (Conv↓)
open import Imprecision
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (rename-⊑; subst-⊑; toRenameᵗ-injective)
import proof.Imprecision as PI

------------------------------------------------------------------------
-- Embedding composition
------------------------------------------------------------------------

infixr 9 _∘↪_

_∘↪_ : ∀ {Δ₁ Δ₂ Δ₃}
  → Δ₂ ↪ᵗ Δ₃
  → Δ₁ ↪ᵗ Δ₂
  → Δ₁ ↪ᵗ Δ₃
π ∘↪ empty = empty
(skip π) ∘↪ η = skip (π ∘↪ η)
(keep π) ∘↪ (keep η) = keep (π ∘↪ η)
(keep π) ∘↪ (skip η) = skip (π ∘↪ η)

toRenameᵗ-∘ : ∀ {Δ₁ Δ₂ Δ₃}
  → (π : Δ₂ ↪ᵗ Δ₃)
  → (η : Δ₁ ↪ᵗ Δ₂)
  → ∀ X
  → toRenameᵗ (π ∘↪ η) X ≡ toRenameᵗ π (toRenameᵗ η X)
toRenameᵗ-∘ π empty ()
toRenameᵗ-∘ (skip π) (keep η) X =
  cong Fin.suc (toRenameᵗ-∘ π (keep η) X)
toRenameᵗ-∘ (skip π) (skip η) X =
  cong Fin.suc (toRenameᵗ-∘ π (skip η) X)
toRenameᵗ-∘ (keep π) (keep η) Fin.zero = refl
toRenameᵗ-∘ (keep π) (keep η) (Fin.suc X) =
  cong Fin.suc (toRenameᵗ-∘ π η X)
toRenameᵗ-∘ (keep π) (skip η) X =
  cong Fin.suc (toRenameᵗ-∘ π η X)

record EmbeddingPushout {Δ Δ′ Δᵐ}
    (π : Δ ↪ᵗ Δ′) (old : Δ ↪ᵗ Δᵐ) : Set where
  constructor pushout
  field
    {Δᵐ′} : TyCtx
    premise : Δᵐ ↪ᵗ Δᵐ′
    old′ : Δ′ ↪ᵗ Δᵐ′
    commutes : ∀ X
      → toRenameᵗ premise (toRenameᵗ old X)
        ≡ toRenameᵗ old′ (toRenameᵗ π X)

-- A one-slot window extends an embedding by placing its distinguished
-- slot before every point in the old embedding.  Keeping this structural
-- witness, rather than only its pointwise action, matters at an empty
-- source context, where several syntactically different OPEs act on no
-- points at all.

data EmbeddingWindow : ∀ {Δ Δ′ : TyCtx}
    → Δ ↪ᵗ Δ′ → Nat.suc Δ ↪ᵗ Δ′ → Set where
  window-here : ∀ {Δ Δ′} {π : Δ ↪ᵗ Δ′}
    → EmbeddingWindow (skip π) (keep π)

  window-skip : ∀ {Δ Δ′} {π : Δ ↪ᵗ Δ′}
      {κ : Nat.suc Δ ↪ᵗ Δ′}
    → EmbeddingWindow π κ
    → EmbeddingWindow (skip π) (skip κ)


record EmbeddingPair (Δ₁ Δ₂ : TyCtx) : Set where
  constructor pair
  field
    {ΔΣ} : TyCtx
    left : Δ₁ ↪ᵗ ΔΣ
    right : Δ₂ ↪ᵗ ΔΣ

embeddingPair : ∀ Δ₁ Δ₂ → EmbeddingPair Δ₁ Δ₂
embeddingPair Nat.zero Δ₂ = pair empty id↪ᵗ
embeddingPair (Nat.suc Δ₁) Δ₂
    with embeddingPair Δ₁ Δ₂
embeddingPair (Nat.suc Δ₁) Δ₂
    | pair left right =
  pair (keep left) (skip right)

embeddingPushout : ∀ {Δ Δ′ Δᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (old : Δ ↪ᵗ Δᵐ)
  → EmbeddingPushout π old
embeddingPushout {Δ′ = Δ′} {Δᵐ = Δᵐ} empty empty
    with embeddingPair Δᵐ Δ′
embeddingPushout {Δ′ = Δ′} {Δᵐ = Δᵐ} empty empty
    | pair premise old′ =
  pushout premise old′ (λ ())
embeddingPushout empty (skip old)
    with embeddingPushout empty old
embeddingPushout empty (skip old)
    | pushout premise old′ commutes =
  pushout (keep premise) (skip old′) (λ ())
embeddingPushout (skip π) old
    with embeddingPushout π old
embeddingPushout (skip π) old
    | pushout premise old′ commutes =
  pushout (skip premise) (keep old′) (λ X → cong Fin.suc (commutes X))
embeddingPushout (keep π) (skip old)
    with embeddingPushout (keep π) old
embeddingPushout (keep π) (skip old)
    | pushout premise old′ commutes =
  pushout (keep premise) (skip old′) (λ X → cong Fin.suc (commutes X))
embeddingPushout (keep π) (keep old)
    with embeddingPushout π old
embeddingPushout (keep π) (keep old)
    | pushout premise old′ commutes =
  pushout (keep premise) (keep old′) commutes′
  where
  commutes′ : ∀ X
    → toRenameᵗ (keep premise) (toRenameᵗ (keep old) X)
      ≡ toRenameᵗ (keep old′) (toRenameᵗ (keep π) X)
  commutes′ Fin.zero = refl
  commutes′ (Fin.suc X) = cong Fin.suc (commutes X)


record EmbeddingPushoutWindow {Δ Δ′ Δᵐ : TyCtx}
    (π : Δ ↪ᵗ Δ′) (old : Δ ↪ᵗ Δᵐ)
    (κ : Nat.suc Δ ↪ᵗ Δ′)
    (po : EmbeddingPushout π old) : Set where
  constructor pushout-window
  field
    window : Nat.suc Δᵐ ↪ᵗ EmbeddingPushout.Δᵐ′ po
    window-embedding :
      EmbeddingWindow (EmbeddingPushout.premise po) window
    window-zero-commutes :
      toRenameᵗ (EmbeddingPushout.old′ po)
          (toRenameᵗ κ Fin.zero)
        ≡ toRenameᵗ window Fin.zero
    window-old-commutes : ∀ Z
      → toRenameᵗ (EmbeddingPushout.premise po) Z
        ≡ toRenameᵗ window (Fin.suc Z)


embeddingPushoutWindow : ∀ {Δ Δ′ Δᵐ : TyCtx}
    {π : Δ ↪ᵗ Δ′} {κ : Nat.suc Δ ↪ᵗ Δ′}
  → (old : Δ ↪ᵗ Δᵐ)
  → EmbeddingWindow π κ
  → EmbeddingPushoutWindow π old κ (embeddingPushout π old)
embeddingPushoutWindow {π = skip π} old window-here
    with embeddingPushout π old
embeddingPushoutWindow {π = skip π} old window-here
    | pushout premise old′ commutes =
  pushout-window (keep premise) window-here refl (λ Z → refl)
embeddingPushoutWindow {π = skip π} old (window-skip window-ok)
    with embeddingPushout π old | embeddingPushoutWindow old window-ok
embeddingPushoutWindow {π = skip π} old (window-skip window-ok)
    | pushout premise old′ commutes
    | pushout-window κᵐ window-okᵐ zero-commutes old-commutes =
  pushout-window (skip κᵐ) (window-skip window-okᵐ)
    (cong Fin.suc zero-commutes)
    (λ Z → cong Fin.suc (old-commutes Z))

------------------------------------------------------------------------
-- Preimages and imprecision environments
------------------------------------------------------------------------

sucMaybe : ∀ {Δ} → Maybe (TyVar Δ) → Maybe (TyVar (Nat.suc Δ))
sucMaybe (just X) = just (Fin.suc X)
sucMaybe nothing = nothing

sucMaybe-nothing : ∀ {Δ} (m : Maybe (TyVar Δ))
  → sucMaybe m ≡ nothing
  → m ≡ nothing
sucMaybe-nothing (just X) ()
sucMaybe-nothing nothing eq = refl

preimage? : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′
  → TyVar Δ′
  → Maybe (TyVar Δ)
preimage? empty Z = nothing
preimage? (keep π) Fin.zero = just Fin.zero
preimage? (keep π) (Fin.suc Z) = sucMaybe (preimage? π Z)
preimage? (skip π) Fin.zero = nothing
preimage? (skip π) (Fin.suc Z) = preimage? π Z

preimage?-image : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) (Z : TyVar Δ)
  → preimage? π (toRenameᵗ π Z) ≡ just Z
preimage?-image empty ()
preimage?-image (keep π) Fin.zero = refl
preimage?-image (keep π) (Fin.suc Z)
    rewrite preimage?-image π Z =
  refl
preimage?-image (skip π) Z = preimage?-image π Z

just≢nothing : ∀ {A : Set} {x : A} → just x ≢ nothing
just≢nothing ()

sucMaybe-just-suc : ∀ {Δ} {m : Maybe (TyVar Δ)} {Z}
  → sucMaybe m ≡ just (Fin.suc Z)
  → m ≡ just Z
sucMaybe-just-suc {m = just Z} refl = refl
sucMaybe-just-suc {m = nothing} ()

preimage?-sound : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) {Z′ Z}
  → preimage? π Z′ ≡ just Z
  → Z′ ≡ toRenameᵗ π Z
preimage?-sound empty ()
preimage?-sound (keep π) {Z′ = Fin.zero} {Z = Fin.zero} refl =
  refl
preimage?-sound (keep π) {Z′ = Fin.zero} {Z = Fin.suc Z} ()
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.zero} eq
    with preimage? π Z′
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.zero} ()
    | just Y
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.zero} ()
    | nothing
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.suc Z} eq =
  cong Fin.suc (preimage?-sound π (sucMaybe-just-suc eq))
preimage?-sound (skip π) {Z′ = Fin.zero} ()
preimage?-sound (skip π) {Z′ = Fin.suc Z′} eq =
  cong Fin.suc (preimage?-sound π eq)

fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
  → Fin.suc X ≡ Fin.suc Y
  → X ≡ Y
fin-suc-injective refl = refl

embeddingPair-disjoint : ∀ Δ₁ Δ₂
    {Z₁ : TyVar Δ₁} {Z₂ : TyVar Δ₂}
  → toRenameᵗ (EmbeddingPair.right (embeddingPair Δ₁ Δ₂)) Z₂
    ≢ toRenameᵗ (EmbeddingPair.left (embeddingPair Δ₁ Δ₂)) Z₁
embeddingPair-disjoint Nat.zero Δ₂ {Z₁ = ()}
embeddingPair-disjoint (Nat.suc Δ₁) Δ₂ {Z₁ = Fin.zero} ()
embeddingPair-disjoint (Nat.suc Δ₁) Δ₂ {Z₁ = Fin.suc Z₁} eq =
  embeddingPair-disjoint Δ₁ Δ₂ (fin-suc-injective eq)

pushout-off-image-disjoint : ∀ {Δ Δ′ Δᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (old : Δ ↪ᵗ Δᵐ)
  → {Z′ : TyVar Δ′} {Zᵐ : TyVar Δᵐ}
  → preimage? π Z′ ≡ nothing
  → toRenameᵗ (EmbeddingPushout.old′ (embeddingPushout π old)) Z′
    ≢ toRenameᵗ (EmbeddingPushout.premise (embeddingPushout π old)) Zᵐ
pushout-off-image-disjoint {Δ′ = Δ′} {Δᵐ = Δᵐ} empty empty pre eq =
  embeddingPair-disjoint Δᵐ Δ′ eq
pushout-off-image-disjoint empty (skip old)
    {Zᵐ = Fin.zero} pre ()
pushout-off-image-disjoint empty (skip old)
    {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint empty old pre (fin-suc-injective eq)
pushout-off-image-disjoint (skip π) old
    {Z′ = Fin.zero} pre ()
pushout-off-image-disjoint (skip π) old
    {Z′ = Fin.suc Z′} pre eq =
  pushout-off-image-disjoint π old pre (fin-suc-injective eq)
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.zero} pre eq =
  just≢nothing pre
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.zero} pre ()
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint (keep π) old pre
    (fin-suc-injective eq)
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.zero} pre eq =
  just≢nothing pre
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.zero} pre ()
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint π old
    (sucMaybe-nothing (preimage? π Z′) pre)
    (fin-suc-injective eq)

pushout-old-off-premise : ∀ {Δ Δ′ Δᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (old : Δ ↪ᵗ Δᵐ)
  → {Z′ : TyVar Δ′}
  → preimage? π Z′ ≡ nothing
  → preimage?
      (EmbeddingPushout.premise (embeddingPushout π old))
      (toRenameᵗ (EmbeddingPushout.old′ (embeddingPushout π old)) Z′)
    ≡ nothing
pushout-old-off-premise π old {Z′ = Z′} off
    with preimage?
      (EmbeddingPushout.premise (embeddingPushout π old))
      (toRenameᵗ (EmbeddingPushout.old′ (embeddingPushout π old)) Z′) in pre
pushout-old-off-premise π old {Z′ = Z′} off
    | nothing = refl
pushout-old-off-premise π old {Z′ = Z′} off
    | just Zᵐ =
  ⊥-elim (pushout-off-image-disjoint π old off
    (preimage?-sound
      (EmbeddingPushout.premise (embeddingPushout π old)) pre))

renameEnv : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → ImpEnv Δ → ImpEnv Δ′
renameEnv empty μ = λ Z → X⊑★
renameEnv (keep π) μ =
  extendᵐ (μ Fin.zero) (renameEnv π (λ X → μ (Fin.suc X)))
renameEnv (skip π) μ = extendᵐ X⊑★ (renameEnv π μ)

renameEnv-image : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) (μ : ImpEnv Δ)
  → ∀ Z → renameEnv π μ (toRenameᵗ π Z) ≡ μ Z
renameEnv-image empty μ ()
renameEnv-image (keep π) μ Fin.zero = refl
renameEnv-image (keep π) μ (Fin.suc Z) =
  renameEnv-image π (λ X → μ (Fin.suc X)) Z
renameEnv-image (skip π) μ Z = renameEnv-image π μ Z

renameEnv-off : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) (μ : ImpEnv Δ)
    {Z′ : TyVar Δ′}
  → preimage? π Z′ ≡ nothing
  → renameEnv π μ Z′ ≡ X⊑★
renameEnv-off empty μ eq = refl
renameEnv-off (keep π) μ {Z′ = Fin.zero} ()
renameEnv-off (keep π) μ {Z′ = Fin.suc Z} eq =
  renameEnv-off π (λ X → μ (Fin.suc X))
    (sucMaybe-nothing (preimage? π Z) eq)
renameEnv-off (skip π) μ {Z′ = Fin.zero} eq = refl
renameEnv-off (skip π) μ {Z′ = Fin.suc Z} eq =
  renameEnv-off π μ eq

------------------------------------------------------------------------
-- Worlds, obligations, and contexts
------------------------------------------------------------------------

renameWorld : ∀ {Δᴸ Δᴿ Δ Δ′}
  → Δ ↪ᵗ Δ′
  → CTI2.World Δᴸ Δᴿ Δ
  → CTI2.World Δᴸ Δᴿ Δ′
renameWorld π W =
  CTI2.world (π ∘↪ CTI2.ηᴸʷ W) (π ∘↪ CTI2.ηᴿʷ W)
    (renameEnv π (CTI2.impEnvʷ W))
    (CTI2.sourceStoreʷ W) (CTI2.targetStoreʷ W)

embedᴸ-rename : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ)
  → CTI2.embedᴸ (renameWorld π W) A
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴸ W A)
embedᴸ-rename π W A =
  trans (renameᵗ-cong A (toRenameᵗ-∘ π (CTI2.ηᴸʷ W)))
    (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴸʷ W))
      (toRenameᵗ π) A))

embedᴿ-rename : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTI2.World Δᴸ Δᴿ Δ) (B : Ty Δᴿ)
  → CTI2.embedᴿ (renameWorld π W) B
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴿ W B)
embedᴿ-rename π W B =
  trans (renameᵗ-cong B (toRenameᵗ-∘ π (CTI2.ηᴿʷ W)))
    (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴿʷ W))
      (toRenameᵗ π) B))

rename-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → A CTI2.⊑ᵂ⟨ W ⟩ B
  → A CTI2.⊑ᵂ⟨ renameWorld π W ⟩ B
rename-⊑ᵂ {W = W} {A = A} {B = B} π p =
  subst≡
    (λ L → CTI2.impEnvʷ (renameWorld π W) ⊢
      L ⊑ CTI2.embedᴿ (renameWorld π W) B)
    (sym (embedᴸ-rename π W A))
    (subst≡
      (λ R → CTI2.impEnvʷ (renameWorld π W) ⊢
        renameᵗ (toRenameᵗ π) (CTI2.embedᴸ W A) ⊑ R)
      (sym (embedᴿ-rename π W B))
      (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
        (λ X eq → trans (renameEnv-image π (CTI2.impEnvʷ W) X) eq)
        p))

preimageSubst : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′
  → Δ′ ⇒ˢ Δ
preimageSubst π Z′ with preimage? π Z′
preimageSubst π Z′ | just Z = ＇ Z
preimageSubst π Z′ | nothing = ★

preimageSubst-image : ∀ {Δ Δ′}
  → (π : Δ ↪ᵗ Δ′)
  → ∀ Z
  → preimageSubst π (toRenameᵗ π Z) ≡ ＇ Z
preimageSubst-image π Z rewrite preimage?-image π Z = refl

preimageSubst-rename : ∀ {Δ Δ′}
  → (π : Δ ↪ᵗ Δ′)
  → (A : Ty Δ)
  → substᵗ (preimageSubst π) (renameᵗ (toRenameᵗ π) A) ≡ A
preimageSubst-rename π A =
  trans (substᵗ-rename (preimageSubst π) (toRenameᵗ π) A)
    (trans (substᵗ-cong A (preimageSubst-image π))
      (substᵗ-id A))

preimageSubst-star : ∀ {Δ Δ′}
    {μ : ImpEnv Δ}
  → (π : Δ ↪ᵗ Δ′)
  → ∀ Z′
  → renameEnv π μ Z′ ≡ X⊑★
  → μ ⊢ preimageSubst π Z′ ⊑ ★
preimageSubst-star {μ = μ} π Z′ star with preimage? π Z′ in pre
preimageSubst-star {μ = μ} π Z′ star | just Z =
  X⊑★ (trans (sym (renameEnv-image π μ Z))
    (subst≡ (λ C → renameEnv π μ C ≡ X⊑★)
      (preimage?-sound π pre) star))
preimageSubst-star π Z′ star | nothing = ★⊑★

unrename-⊑ : ∀ {Δ Δ′}
    {μ : ImpEnv Δ} {A B : Ty Δ}
  → (π : Δ ↪ᵗ Δ′)
  → renameEnv π μ ⊢ renameᵗ (toRenameᵗ π) A
      ⊑ renameᵗ (toRenameᵗ π) B
  → μ ⊢ A ⊑ B
unrename-⊑ {μ = μ} {A = A} {B = B} π p =
  subst≡ (λ L → μ ⊢ L ⊑ B) (preimageSubst-rename π A)
    (subst≡
      (λ R → μ ⊢ substᵗ (preimageSubst π)
        (renameᵗ (toRenameᵗ π) A) ⊑ R)
      (preimageSubst-rename π B)
      (subst-⊑ (preimageSubst-star π) p))

unrename-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → A CTI2.⊑ᵂ⟨ renameWorld π W ⟩ B
  → A CTI2.⊑ᵂ⟨ W ⟩ B
unrename-⊑ᵂ {W = W} {A = A} {B = B} π p =
  unrename-⊑ π
    (subst≡
      (λ L → CTI2.impEnvʷ (renameWorld π W) ⊢
        L ⊑ renameᵗ (toRenameᵗ π) (CTI2.embedᴿ W B))
      (embedᴸ-rename π W A)
      (subst≡
        (λ R → CTI2.impEnvʷ (renameWorld π W) ⊢
          CTI2.embedᴸ (renameWorld π W) A ⊑ R)
        (embedᴿ-rename π W B)
        p))

renameCtx : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTI2.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.CtxImp W
  → CTI2.CtxImp (renameWorld π W)
renameCtx {W = W} π [] = []
renameCtx {W = W} π (CTI2.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A B (rename-⊑ᵂ {W = W} π p) ∷
    renameCtx {W = W} π γ

rename-∋ʷ : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {x A B} {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (π : Δ ↪ᵗ Δ′)
  → γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B p
  → renameCtx {W = W} π γ CTI2.∋ʷ x ⦂
      CTI2.ctx-imp A B (rename-⊑ᵂ {W = W} π p)
rename-∋ʷ {W = W} π CTI2.Zʷ = CTI2.Zʷ
rename-∋ʷ {W = W} π (CTI2.Sʷ x∈) =
  CTI2.Sʷ (rename-∋ʷ {W = W} π x∈)

renameSameCtx : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {γ′ : CTI2.CtxImp W′}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.SameCtx γ γ′
  → CTI2.SameCtx (renameCtx {W = W} π γ)
      (renameCtx {W = W′} π γ′)
renameSameCtx π CTI2.same-[] = CTI2.same-[]
renameSameCtx π (CTI2.same-∷ sc) =
  CTI2.same-∷ (renameSameCtx π sc)

------------------------------------------------------------------------
-- Binder commutation
------------------------------------------------------------------------

renameWorld-liftBoth : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → (v : VarImp)
  → renameWorld (keep π) (CTI2.liftWorldBoth v W)
      ≡ CTI2.liftWorldBoth v (renameWorld π W)
renameWorld-liftBoth π v = refl

renameWorld-liftLeft : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → (v : VarImp)
  → renameWorld (keep π) (CTI2.liftWorldLeft v W)
      ≡ CTI2.liftWorldLeft v (renameWorld π W)
renameWorld-liftLeft π v = refl

renameLiftCtx : ∀ {Δᴸ Δᴿ Δ Δ′} {v}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldBoth v W)}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.LiftCtx v γ γ′
  → CTI2.LiftCtx v (renameCtx {W = W} π γ)
      (renameCtx {W = CTI2.liftWorldBoth v W} (keep π) γ′)
renameLiftCtx π CTI2.lift-[] = CTI2.lift-[]
renameLiftCtx π (CTI2.lift-∷ liftγ) =
  CTI2.lift-∷ (renameLiftCtx π liftγ)

renameLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δ′} {v}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldLeft v W)}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.LiftCtxᴸ v (renameCtx {W = W} π γ)
      (renameCtx {W = CTI2.liftWorldLeft v W} (keep π) γ′)
renameLiftCtxᴸ π CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
renameLiftCtxᴸ π (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (renameLiftCtxᴸ π liftγ)

renameSmartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ Δ′ Δᵐ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (πᵐ : Δᵐ ↪ᵗ Δᵐ′)
  → CTI2.SmartLiftCtxᴸ γ γᵐ
  → CTI2.SmartLiftCtxᴸ
      (renameCtx {W = W} π γ)
      (renameCtx {W = Wᵐ} πᵐ γᵐ)
renameSmartLiftCtxᴸ π πᵐ CTI2.smart-lift-[] = CTI2.smart-lift-[]
renameSmartLiftCtxᴸ π πᵐ (CTI2.smart-lift-∷ liftγ) =
  CTI2.smart-lift-∷ (renameSmartLiftCtxᴸ π πᵐ liftγ)

renameCtx-tgt : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTI2.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → (γ : CTI2.CtxImp W)
  → CTI2.tgtCtxʷ (renameCtx {W = W} π γ) ≡ CTI2.tgtCtxʷ γ
renameCtx-tgt π [] = refl
renameCtx-tgt π (CTI2.ctx-imp A B p ∷ γ) =
  cong (B ∷_) (renameCtx-tgt π γ)

------------------------------------------------------------------------
-- Runtime and rebasing records
------------------------------------------------------------------------

renameSameRuntime : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.SameRuntime W W′
  → CTI2.SameRuntime (renameWorld π W) (renameWorld π W′)
renameSameRuntime π (CTI2.same-runtime source-eq target-eq) =
  CTI2.same-runtime source-eq target-eq

renameStoreRep : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp (renameWorld π W) Xᴸ Xᴿ
renameStoreRep {W = W} π (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp (rename-⊑ᵂ {W = W} π represented)

rename-embedding-eq : ∀ {Δ₁ Δ₂ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) {η₁ : Δ₁ ↪ᵗ Δ} {η₂ : Δ₂ ↪ᵗ Δ}
    {X₁ : TyVar Δ₁} {X₂ : TyVar Δ₂}
  → toRenameᵗ η₁ X₁ ≡ toRenameᵗ η₂ X₂
  → toRenameᵗ (π ∘↪ η₁) X₁ ≡ toRenameᵗ (π ∘↪ η₂) X₂
rename-embedding-eq π {η₁ = η₁} {η₂ = η₂}
    {X₁ = X₁} {X₂ = X₂} eq =
  trans (toRenameᵗ-∘ π η₁ X₁)
    (trans (cong (toRenameᵗ π) eq)
      (sym (toRenameᵗ-∘ π η₂ X₂)))

renameRebaseAt : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.RebaseAt (renameWorld π W) (renameWorld π W′) Xᴸ Xᴿ
renameRebaseAt {Δᴸ = Δᴸ} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} π
    (CTI2.rebase-at runtime offL frozenR aligned reps) =
  CTI2.rebase-at (renameSameRuntime π runtime)
    (λ Y≢ → rename-embedding-eq π (offL Y≢))
    (λ Y → rename-embedding-eq π (frozenR Y))
    (rename-embedding-eq π aligned)
    (renameStoreRep π reps)

rename-mark-image : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTI2.World Δᴸ Δᴿ Δ)
    {Xᴸ : TyVar Δᴸ}
  → CTI2.impEnvʷ (renameWorld π W)
      (toRenameᵗ (CTI2.ηᴸʷ (renameWorld π W)) Xᴸ)
      ≡ CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
rename-mark-image π W {Xᴸ} =
  trans (cong (renameEnv π (CTI2.impEnvʷ W))
      (toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ))
    (renameEnv-image π (CTI2.impEnvʷ W)
      (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ))

rename-target-mark-image : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTI2.World Δᴸ Δᴿ Δ)
    {Xᴿ : TyVar Δᴿ}
  → CTI2.impEnvʷ (renameWorld π W)
      (toRenameᵗ (CTI2.ηᴿʷ (renameWorld π W)) Xᴿ)
      ≡ CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
rename-target-mark-image π W {Xᴿ} =
  trans (cong (renameEnv π (CTI2.impEnvʷ W))
      (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Xᴿ))
    (renameEnv-image π (CTI2.impEnvʷ W)
      (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ))

rename-disaligned : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTI2.World Δᴸ Δᴿ Δ)
    {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ ≢
      toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ (renameWorld π W)) Xᴿ ≢
      toRenameᵗ (CTI2.ηᴸʷ (renameWorld π W)) Xᴸ
rename-disaligned π W {Xᴸ} disaligned Xᴿ eq =
  disaligned Xᴿ (toRenameᵗ-injective π
    (trans (sym (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Xᴿ))
      (trans eq (toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ))))

renameRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → CTI2.RebaseAtᴸ (renameWorld π W) (renameWorld π W′) Xᴸ?
renameRebaseAtᴸ π CTI2.rebase-idᴸ = CTI2.rebase-idᴸ
renameRebaseAtᴸ π (CTI2.rebase-varᴸ rb) =
  CTI2.rebase-varᴸ (renameRebaseAt π rb)
renameRebaseAtᴸ {W = W} π
    (CTI2.rebase-onlyᴸ to-star disaligned represented) =
  CTI2.rebase-onlyᴸ
    (trans (rename-mark-image π W) to-star)
    (rename-disaligned π W disaligned)
    (rename-⊑ᵂ {W = W} π represented)

renameTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
  → CTI2.TagRebaseAtᴸ (renameWorld π W) (renameWorld π W′) Xᴸ? Xᴿ?
renameTagRebaseAtᴸ π CTI2.tag-rebase-idᴸ = CTI2.tag-rebase-idᴸ
renameTagRebaseAtᴸ π (CTI2.tag-rebase-varᴸ rb) =
  CTI2.tag-rebase-varᴸ (renameRebaseAt π rb)
renameTagRebaseAtᴸ {W = W} π
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
  CTI2.tag-rebase-onlyᴸ
    (trans (rename-mark-image π W) to-star)
    (rename-disaligned π W disaligned)
    (rename-⊑ᵂ {W = W} π represented)

renameRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → CTI2.RebaseAtᴿ (renameWorld π W) (renameWorld π W′) Xᴿ?
renameRebaseAtᴿ π CTI2.rebase-idᴿ = CTI2.rebase-idᴿ
renameRebaseAtᴿ π (CTI2.rebase-varᴿ rb) =
  CTI2.rebase-varᴿ (renameRebaseAt π rb)

renameRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.Rep★PartnerOK W X P Xᴿ? M′
  → CTI2.Rep★PartnerOK (renameWorld π W) X P Xᴿ? M′
renameRep★PartnerOK π (CTI2.rep★-untagged nt) =
  CTI2.rep★-untagged nt
renameRep★PartnerOK π (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
renameRep★PartnerOK π (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag (rename-embedding-eq π aligned)
renameRep★PartnerOK π (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X (rename-embedding-eq π aligned)
renameRep★PartnerOK π (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (renameRep★PartnerOK π ok)

renameNoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.NoTargetOccupantAtSource W X
  → CTI2.NoTargetOccupantAtSource (renameWorld π W) X
renameNoTargetOccupantAtSource {W = W} {X = X} π no-target
    (Y , eq) =
  no-target (Y , target-eq)
  where
  target-eq :
    toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ toRenameᵗ (CTI2.ηᴸʷ W) X
  target-eq =
    toRenameᵗ-injective π
      (trans (sym (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Y))
        (trans eq (toRenameᵗ-∘ π (CTI2.ηᴸʷ W) X)))

renameSourceConcealOK : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.SourceConcealOK W M c Xᴿ? M′
  → CTI2.SourceConcealOK (renameWorld π W) M c Xᴿ? M′
renameSourceConcealOK π
    (CTI2.seal-nonstar-plain-ok Rns nt) =
  CTI2.seal-nonstar-plain-ok Rns nt
renameSourceConcealOK π
    (CTI2.seal-nonstar-name-protected-ok Rns aligned) =
  CTI2.seal-nonstar-name-protected-ok Rns
    (rename-embedding-eq π aligned)
renameSourceConcealOK π CTI2.fun-conceal-ok =
  CTI2.fun-conceal-ok
renameSourceConcealOK π CTI2.all-conceal-ok =
  CTI2.all-conceal-ok
renameSourceConcealOK π CTI2.id-conceal-ok =
  CTI2.id-conceal-ok

renameMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Y M′}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.MatchedConcealPartnerOK W M c Y M′
  → CTI2.MatchedConcealPartnerOK (renameWorld π W) M c Y M′
renameMatchedConcealPartnerOK π
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner (renameRep★PartnerOK π ok)
renameMatchedConcealPartnerOK π (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
renameMatchedConcealPartnerOK π CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
renameMatchedConcealPartnerOK π CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
renameMatchedConcealPartnerOK π CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target

renameEnvMono : ∀ {Δ Δ′} {μ ν : ImpEnv Δ}
  → (π : Δ ↪ᵗ Δ′)
  → (∀ Z → μ Z ≡ X⊑★ → ν Z ≡ X⊑★)
  → ∀ Z′ → renameEnv π μ Z′ ≡ X⊑★
      → renameEnv π ν Z′ ≡ X⊑★
renameEnvMono empty mono Z eq = refl
renameEnvMono (keep π) mono Fin.zero eq = mono Fin.zero eq
renameEnvMono (keep π) mono (Fin.suc Z) eq =
  renameEnvMono π (λ X → mono (Fin.suc X)) Z eq
renameEnvMono (skip π) mono Fin.zero eq = refl
renameEnvMono (skip π) mono (Fin.suc Z) eq =
  renameEnvMono π mono Z eq

renameImpEnvMono : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.ImpEnvMono W W′
  → CTI2.ImpEnvMono (renameWorld π W) (renameWorld π W′)
renameImpEnvMono π mono = renameEnvMono π mono

renameSmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.SmartAliasMergeGuard W Wᵐ β α
  → CTI2.SmartAliasMergeGuard (renameWorld π W)
      (renameWorld π Wᵐ) β α
renameSmartAliasMergeGuard {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {W = W} {Wᵐ = Wᵐ} {β = β} {α = α} π guard =
  CTI2.smart-alias-merge-guard
    (CTI2.SmartAliasMergeGuard.β:=＇α guard)
    (CTI2.SmartAliasMergeGuard.α:=★ guard)
    (CTI2.SmartAliasMergeGuard.sourceStore-lifted guard)
    (CTI2.SmartAliasMergeGuard.targetStore-same guard)
    transport′
    old-mark-mono′
    (λ Xᴿ → rename-embedding-eq π
      (CTI2.SmartAliasMergeGuard.target-frozen guard Xᴿ))
    (rename-embedding-eq π
      (CTI2.SmartAliasMergeGuard.pending-at-alias guard))
    (λ Xᴸ → rename-embedding-eq π
      (CTI2.SmartAliasMergeGuard.old-source-frozen guard Xᴸ))
    no-old-source-at-alias′
    (trans (cong (renameEnv π (CTI2.impEnvʷ Wᵐ))
      (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) β))
      (trans (renameEnv-image π (CTI2.impEnvʷ Wᵐ)
        (toRenameᵗ (CTI2.ηᴿʷ W) β))
        (CTI2.SmartAliasMergeGuard.alias-mark-dynamic guard)))
    (trans (cong (renameEnv π (CTI2.impEnvʷ Wᵐ))
      (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) α))
      (trans (renameEnv-image π (CTI2.impEnvʷ Wᵐ)
        (toRenameᵗ (CTI2.ηᴿʷ W) α))
        (CTI2.SmartAliasMergeGuard.name-mark-dynamic guard)))
    target-mark-off-footprint′
  where
  no-old-source-at-alias′ : ∀ Xᴸ
    → toRenameᵗ (CTI2.ηᴸʷ (renameWorld π W)) Xᴸ
      ≢ toRenameᵗ (CTI2.ηᴿʷ (renameWorld π W)) β
  no-old-source-at-alias′ Xᴸ eq =
    CTI2.SmartAliasMergeGuard.no-old-source-at-alias guard Xᴸ
      (toRenameᵗ-injective π
        (trans (sym (toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ))
        (trans eq (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) β))))

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ (renameWorld π W) ⟩ B
    → A CTI2.⊑ᵂ⟨ renameWorld π Wᵐ ⟩ B
  transport′ p =
    rename-⊑ᵂ {W = Wᵐ} π
      (CTI2.SmartAliasMergeGuard.transport⊑ᵂ guard
        (unrename-⊑ᵂ {W = CTI2.liftWorldLeft X⊑★ W} (keep π) p))

  old-mark-mono′ : ∀ Z′
    → CTI2.impEnvʷ (renameWorld π W) Z′ ≡ X⊑★
    → CTI2.impEnvʷ (renameWorld π Wᵐ) Z′ ≡ X⊑★
  old-mark-mono′ Z′ star with preimage? π Z′ in pre
  old-mark-mono′ Z′ star | nothing =
    renameEnv-off π (CTI2.impEnvʷ Wᵐ) pre
  old-mark-mono′ Z′ star | just Z =
    subst≡
      (λ C → CTI2.impEnvʷ (renameWorld π Wᵐ) C ≡ X⊑★)
      (sym image-eq)
      (trans (renameEnv-image π (CTI2.impEnvʷ Wᵐ) Z)
        (CTI2.SmartAliasMergeGuard.old-mark-mono guard Z old-star))
    where
    image-eq : Z′ ≡ toRenameᵗ π Z
    image-eq = preimage?-sound π pre

    old-star : CTI2.impEnvʷ W Z ≡ X⊑★
    old-star =
      trans (sym (renameEnv-image π (CTI2.impEnvʷ W) Z))
        (subst≡
          (λ C → CTI2.impEnvʷ (renameWorld π W) C ≡ X⊑★)
          image-eq star)

  target-mark-off-footprint′ : ∀ Xᴿ
    → Xᴿ ≢ β
    → Xᴿ ≢ α
    → CTI2.impEnvʷ (renameWorld π W)
        (toRenameᵗ (CTI2.ηᴿʷ (renameWorld π W)) Xᴿ) ≡ X⊑★
    → CTI2.impEnvʷ (renameWorld π Wᵐ)
        (toRenameᵗ (CTI2.ηᴿʷ (renameWorld π Wᵐ)) Xᴿ) ≡ X⊑★
  target-mark-off-footprint′ Xᴿ Xᴿ≢β Xᴿ≢α star =
    trans (rename-target-mark-image π Wᵐ)
      (CTI2.SmartAliasMergeGuard.target-mark-off-footprint guard
        Xᴿ Xᴿ≢β Xᴿ≢α
        (trans (sym (rename-target-mark-image π W)) star))

renameSmartFreshBehindGuard : ∀ {Δᴸ Δᴿ Δ Δᵐ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → CTI2.SmartFreshBehindGuard (renameWorld π W)
      (renameWorld
        (EmbeddingPushout.premise
          (embeddingPushout π
            (CTI2.SmartFreshBehindGuard.oldCenters guard)))
        Wᵐ)
renameSmartFreshBehindGuard {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {W = W} {Wᵐ = Wᵐ} π guard =
  CTI2.smart-fresh-behind-guard old′
    (CTI2.SmartFreshBehindGuard.sourceStore-lifted guard)
    (CTI2.SmartFreshBehindGuard.targetStore-same guard)
    transport′ old-mark-mono′ target-frozen′ old-source-frozen′
    fresh-not-target′ fresh-mark′ target-mark-frozen′
  where
  old = CTI2.SmartFreshBehindGuard.oldCenters guard
  po = embeddingPushout π old
  πᵐ = EmbeddingPushout.premise po
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ (renameWorld π W) ⟩ B
    → A CTI2.⊑ᵂ⟨ renameWorld πᵐ Wᵐ ⟩ B
  transport′ p =
    rename-⊑ᵂ {W = Wᵐ} πᵐ
      (CTI2.SmartFreshBehindGuard.transport⊑ᵂ guard
        (unrename-⊑ᵂ {W = CTI2.liftWorldLeft X⊑★ W} (keep π) p))

  old-mark-mono′ : ∀ Z′
    → CTI2.impEnvʷ (renameWorld π W) Z′ ≡ X⊑★
    → CTI2.impEnvʷ (renameWorld πᵐ Wᵐ) (toRenameᵗ old′ Z′)
        ≡ X⊑★
  old-mark-mono′ Z′ star with preimage? π Z′ in pre
  old-mark-mono′ Z′ star | nothing =
    renameEnv-off πᵐ (CTI2.impEnvʷ Wᵐ)
      (pushout-old-off-premise π old pre)
  old-mark-mono′ Z′ star | just Z =
    subst≡
      (λ C → CTI2.impEnvʷ (renameWorld πᵐ Wᵐ) C ≡ X⊑★)
      (sym smart-image-eq)
      (trans (renameEnv-image πᵐ (CTI2.impEnvʷ Wᵐ)
          (toRenameᵗ old Z))
        (CTI2.SmartFreshBehindGuard.old-mark-mono guard Z old-star))
    where
    image-eq : Z′ ≡ toRenameᵗ π Z
    image-eq = preimage?-sound π pre

    old-star : CTI2.impEnvʷ W Z ≡ X⊑★
    old-star =
      trans (sym (renameEnv-image π (CTI2.impEnvʷ W) Z))
        (subst≡
          (λ C → CTI2.impEnvʷ (renameWorld π W) C ≡ X⊑★)
          image-eq star)

    smart-image-eq :
      toRenameᵗ old′ Z′ ≡ toRenameᵗ πᵐ (toRenameᵗ old Z)
    smart-image-eq =
      trans (cong (toRenameᵗ old′) image-eq) (sym (commutes Z))

  target-frozen′ : ∀ Xᴿ
    → toRenameᵗ
        (CTI2.ηᴿʷ (renameWorld πᵐ Wᵐ)) Xᴿ
      ≡ toRenameᵗ old′
        (toRenameᵗ (CTI2.ηᴿʷ (renameWorld π W)) Xᴿ)
  target-frozen′ Xᴿ =
    trans (toRenameᵗ-∘ πᵐ (CTI2.ηᴿʷ Wᵐ) Xᴿ)
      (trans (cong (toRenameᵗ πᵐ)
        (CTI2.SmartFreshBehindGuard.target-frozen guard Xᴿ))
        (trans (commutes (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ))
          (cong (toRenameᵗ old′)
            (sym (toRenameᵗ-∘ π (CTI2.ηᴿʷ W) Xᴿ)))))

  old-source-frozen′ : ∀ Xᴸ
    → toRenameᵗ
        (CTI2.ηᴸʷ (renameWorld πᵐ Wᵐ)) (Fin.suc Xᴸ)
      ≡ toRenameᵗ old′
        (toRenameᵗ (CTI2.ηᴸʷ (renameWorld π W)) Xᴸ)
  old-source-frozen′ Xᴸ =
    trans (toRenameᵗ-∘ πᵐ (CTI2.ηᴸʷ Wᵐ) (Fin.suc Xᴸ))
      (trans (cong (toRenameᵗ πᵐ)
        (CTI2.SmartFreshBehindGuard.old-source-frozen guard Xᴸ))
        (trans (commutes (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ))
          (cong (toRenameᵗ old′)
            (sym (toRenameᵗ-∘ π (CTI2.ηᴸʷ W) Xᴸ)))))

  fresh-not-target′ : ∀ Xᴿ
    → toRenameᵗ
        (CTI2.ηᴿʷ (renameWorld πᵐ Wᵐ)) Xᴿ
      ≢ toRenameᵗ
        (CTI2.ηᴸʷ (renameWorld πᵐ Wᵐ)) Fin.zero
  fresh-not-target′ Xᴿ eq =
    CTI2.SmartFreshBehindGuard.fresh-not-target guard Xᴿ
      (toRenameᵗ-injective πᵐ
        (trans (sym (toRenameᵗ-∘ πᵐ (CTI2.ηᴿʷ Wᵐ) Xᴿ))
          (trans eq
            (toRenameᵗ-∘ πᵐ (CTI2.ηᴸʷ Wᵐ) Fin.zero))))

  fresh-mark′ :
    CTI2.impEnvʷ (renameWorld πᵐ Wᵐ)
      (toRenameᵗ (CTI2.ηᴸʷ (renameWorld πᵐ Wᵐ)) Fin.zero)
      ≡ X⊑★
  fresh-mark′ =
    trans (rename-mark-image πᵐ Wᵐ {Fin.zero})
      (CTI2.SmartFreshBehindGuard.fresh-mark-dynamic guard)

  target-mark-frozen′ : ∀ Xᴿ
    → CTI2.impEnvʷ (renameWorld π W)
        (toRenameᵗ (CTI2.ηᴿʷ (renameWorld π W)) Xᴿ) ≡ X⊑★
    → CTI2.impEnvʷ (renameWorld πᵐ Wᵐ)
        (toRenameᵗ (CTI2.ηᴿʷ (renameWorld πᵐ Wᵐ)) Xᴿ) ≡ X⊑★
  target-mark-frozen′ Xᴿ star =
    trans (rename-target-mark-image πᵐ Wᵐ)
      (CTI2.SmartFreshBehindGuard.target-mark-mono guard Xᴿ
        (trans (sym (rename-target-mark-image π W)) star))

------------------------------------------------------------------------
-- Derivation transport
------------------------------------------------------------------------

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d

⊢²-rename-center : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (π : Δ ↪ᵗ Δ′)
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → (p′ : A CTI2.⊑ᵂ⟨ renameWorld π W ⟩ B)
  → renameWorld π W ∣ renameCtx {W = W} π γ ⊢² M ⊑ N ∶ p′
⊢²-rename-center {W = W} π (CTI2.x⊑x² x∈) p′ =
  ⊢²-retarget (CTI2.x⊑x² (rename-∋ʷ {W = W} π x∈))
⊢²-rename-center {W = W} π
    (CTI2.ƛ⊑ƛ² {pA = pA} {pB = pB} M⊑N) p′ =
  ⊢²-retarget (CTI2.ƛ⊑ƛ²
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π pB)))
⊢²-rename-center {W = W} π
    (CTI2.·⊑·² {pA = pA} {pB = pB} L⊑L′ M⊑M′) p′ =
  ⊢²-retarget (CTI2.·⊑·²
    (⊢²-rename-center {W = W} π L⊑L′
      (⇒⊑⇒ (rename-⊑ᵂ {W = W} π pA)
        (rename-⊑ᵂ {W = W} π pB)))
    (⊢²-rename-center {W = W} π M⊑M′
      (rename-⊑ᵂ {W = W} π pA)))
⊢²-rename-center {W = W} π
    (CTI2.Λ⊑Λ² {p = p} liftγ vV vV′ V⊑V′ q) p′ =
  CTI2.Λ⊑Λ² (renameLiftCtx π liftγ) vV vV′
    (⊢²-rename-center {W = CTI2.liftWorldBoth X⊑X W}
      (keep π) V⊑V′
      (rename-⊑ᵂ {W = CTI2.liftWorldBoth X⊑X W} (keep π) p)) p′
⊢²-rename-center {W = W} {γ = γ} π
    (CTI2.Λ⊑² {p = p} Anv zero∈A liftγ vV N⊢ V⊑N q) p′ =
  CTI2.Λ⊑² Anv zero∈A (renameLiftCtxᴸ π liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (renameCtx-tgt π γ)) N⊢)
    (⊢²-rename-center {W = CTI2.liftWorldLeft X⊑★ W}
      (keep π) V⊑N
      (rename-⊑ᵂ {W = CTI2.liftWorldLeft X⊑★ W} (keep π) p)) p′
⊢²-rename-center {W = W} {γ = γ} π
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {γᵐ = γᵐ} {p = p}
      Anv zero∈A (CTI2.smart-merge-alias guard) liftγ vV N⊢
      V⊑N q) p′ =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTI2.smart-merge-alias (renameSmartAliasMergeGuard π guard))
    (renameSmartLiftCtxᴸ π π liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (renameCtx-tgt π γ)) N⊢)
    (⊢²-rename-center {W = Wᵐ} π V⊑N
      (rename-⊑ᵂ {W = Wᵐ} π p)) p′
⊢²-rename-center {W = W} {γ = γ} π
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {γᵐ = γᵐ} {p = p}
      Anv zero∈A (CTI2.smart-fresh-behind guard) liftγ vV N⊢
      V⊑N q) p′ =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTI2.smart-fresh-behind
      (renameSmartFreshBehindGuard π guard))
    (renameSmartLiftCtxᴸ π (EmbeddingPushout.premise po) liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (renameCtx-tgt π γ)) N⊢)
    (⊢²-rename-center {W = Wᵐ} (EmbeddingPushout.premise po)
      V⊑N
      (rename-⊑ᵂ {W = Wᵐ} (EmbeddingPushout.premise po) p)) p′
  where
  po = embeddingPushout π
    (CTI2.SmartFreshBehindGuard.oldCenters guard)
⊢²-rename-center {W = W} π (CTI2.•⊑•² p∀ M⊑N q r) p′ =
  CTI2.•⊑•² (rename-⊑ᵂ {W = W} π p∀)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p∀))
    (rename-⊑ᵂ {W = W} π q) p′
⊢²-rename-center {W = W} π (CTI2.•⊑² p∀ M⊑N q r) p′ =
  CTI2.•⊑² (rename-⊑ᵂ {W = W} π p∀)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p∀))
    (rename-⊑ᵂ {W = W} π q) p′
⊢²-rename-center {W = W} π (CTI2.κ⊑κ² κ p) p′ =
  CTI2.κ⊑κ² κ p′
⊢²-rename-center {W = W} π
    (CTI2.cast⊑cast² {p = p} c c′ M⊑N q) p′ =
  CTI2.cast⊑cast² c c′
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.⊑cast² {p = p} c′ M⊑N q) p′ =
  CTI2.⊑cast² c′
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.cast⊑² {p = p} c M⊑N q) p′ =
  CTI2.cast⊑² c
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.⊑reveal² {W′ = W′} {p = p} mono rb sc c′⊢ M⊑N q) p′ =
  CTI2.⊑reveal² (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameRebaseAtᴿ {W = W} {W′ = W′} π rb)
    (renameSameCtx {W = W} {W′ = W′} π sc) c′⊢
    (⊢²-rename-center {W = W′} π M⊑N
      (rename-⊑ᵂ {W = W′} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.⊑conceal² {W′ = W′} {p = p} mono rb sc c′⊢ M⊑N q) p′ =
  CTI2.⊑conceal² (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameRebaseAtᴿ {W = W′} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = W′} π sc) c′⊢
    (⊢²-rename-center {W = W′} π M⊑N
      (rename-⊑ᵂ {W = W′} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.reveal⊑² {W′ = W′} {p = p} mono rb sc c⊢ M⊑N q) p′ =
  CTI2.reveal⊑² (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameRebaseAtᴸ {W = W} {W′ = W′} π rb)
    (renameSameCtx {W = W} {W′ = W′} π sc) c⊢
    (⊢²-rename-center {W = W′} π M⊑N
      (rename-⊑ᵂ {W = W′} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.conceal⊑²-seal-star-open {W′ = W′} {p = p}
      no-target mono rb sc c⊢ M⊑N q) p′ =
  CTI2.conceal⊑²-seal-star-open
    (renameNoTargetOccupantAtSource {W = W′} π no-target)
    (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameTagRebaseAtᴸ {W = W′} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = W′} π sc) c⊢
    (⊢²-rename-center {W = W′} π M⊑N
      (rename-⊑ᵂ {W = W′} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.conceal⊑²-source-ok {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑N q) p′ =
  CTI2.conceal⊑²-source-ok (renameSourceConcealOK π ok)
    (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameTagRebaseAtᴸ {W = W′} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = W′} π sc) c⊢
    (⊢²-rename-center {W = W′} π M⊑N
      (rename-⊑ᵂ {W = W′} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc c⊢ c′⊢ M⊑N q) p′ =
  CTI2.reveal⊑reveal²
    (renameImpEnvMono {W = W} {W′ = Wᵖ} π mono)
    (renameRebaseAt {W = W} {W′ = Wᵖ} π rb)
    (renameSameCtx {W = W} {W′ = Wᵖ} π sc) c⊢ c′⊢
    (⊢²-rename-center {W = Wᵖ} π M⊑N
      (rename-⊑ᵂ {W = Wᵖ} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc c⊢ c′⊢ M⊑N q) p′ =
  CTI2.conceal⊑conceal²
    (renameMatchedConcealPartnerOK π ok)
    (renameImpEnvMono {W = W} {W′ = Wᵖ} π mono)
    (renameRebaseAt {W = Wᵖ} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = Wᵖ} π sc) c⊢ c′⊢
    (⊢²-rename-center {W = Wᵖ} π M⊑N
      (rename-⊑ᵂ {W = Wᵖ} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ} {p★ = p★}
      {qᵖ = qᵖ} ok mono rb sc c⊢ c′⊢ M⊑N sourcePrem q) p′ =
  CTI2.packaged-seal-star²
    (renameMatchedConcealPartnerOK π ok)
    (renameImpEnvMono {W = W} {W′ = Wᵖ} π mono)
    (renameRebaseAt {W = Wᵖ} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = Wᵖ} π sc) c⊢ c′⊢
    (⊢²-rename-center {W = Wᵖ} π M⊑N
      (rename-⊑ᵂ {W = Wᵖ} π p★))
    (⊢²-rename-center {W = Wᵖ} π sourcePrem
      (rename-⊑ᵂ {W = Wᵖ} π qᵖ))
    p′
⊢²-rename-center {W = W} {γ = γ} π (CTI2.blame⊑² M′⊢ p) p′ =
  CTI2.blame⊑²
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (renameCtx-tgt π γ)) M′⊢)
    p′
⊢²-rename-center {W = W} π
    (CTI2.⊕⊑⊕² op {p = p} {q = q} L⊑L′ M⊑M′ r) p′ =
  CTI2.⊕⊑⊕² op
    (⊢²-rename-center {W = W} π L⊑L′
      (rename-⊑ᵂ {W = W} π p))
    (⊢²-rename-center {W = W} π M⊑M′
      (rename-⊑ᵂ {W = W} π q)) p′

⊢²-extend-center : ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → (p′ : A CTI2.⊑ᵂ⟨ renameWorld wk↪ᵗ W ⟩ B)
  → renameWorld wk↪ᵗ W ∣ renameCtx {W = W} wk↪ᵗ γ
      ⊢² M ⊑ N ∶ p′
⊢²-extend-center = ⊢²-rename-center wk↪ᵗ

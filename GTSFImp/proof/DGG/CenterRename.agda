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
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (lookupStore; store-empty; store-lift; store-bind; _∋_⦂_)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ; wk↪ᵗ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.ConversionPivotAlignment using
  (GeneratorPosition; generator-absent; revealGeneratorPosition;
   concealGeneratorPosition; revealGeneratorPosition-store-transport;
   concealGeneratorPosition-store-transport)
open CTX public using (_∘↪_; toRenameᵗ-∘; renameEnv; renameEnv-image)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (rename-⊑; subst-⊑; toRenameᵗ-injective)
import proof.Imprecision as PI

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

rename-composed : ∀ {Δ₀ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
  → renameᵗ (toRenameᵗ (π ∘↪ η)) A
    ≡ renameᵗ (toRenameᵗ π) (renameᵗ (toRenameᵗ η) A)
rename-composed π η A =
  trans (renameᵗ-cong A (toRenameᵗ-∘ π η))
    (sym (renameᵗ-comp (toRenameᵗ η) (toRenameᵗ π) A))

renameWorld-invariants : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
  → CTX.WorldInvariants
      (π ∘↪ CTX.ηᴸʷ W) (π ∘↪ CTX.ηᴿʷ W)
      (renameEnv π (CTX.impEnvʷ W))
      (CTX.sourceStoreʷ W) (CTX.targetStoreʷ W)
renameWorld-invariants π W =
  CTX.world-invariants precise reps unmatched unoccupied
  where
  inv = CTX.invariantsʷ W

  precise : ∀ Xᴸ
    → renameEnv π (CTX.impEnvʷ W)
        (toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar _ ]
        toRenameᵗ (π ∘↪ CTX.ηᴿʷ W) Xᴿ
          ≡ toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ
  precise Xᴸ mark with CTX.preciseMarksAligned inv Xᴸ old-mark
    where
    old-mark :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
    old-mark =
      trans
        (sym (renameEnv-image π (CTX.impEnvʷ W)
          (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)))
        (trans (cong (renameEnv π (CTX.impEnvʷ W))
          (sym (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ))) mark)
  precise Xᴸ mark | Xᴿ , aligned =
    Xᴿ , trans (toRenameᵗ-∘ π (CTX.ηᴿʷ W) Xᴿ)
      (trans (cong (toRenameᵗ π) aligned)
        (sym (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ)))

  reps : ∀ {Xᴸ Xᴿ}
    → toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ
        ≡ toRenameᵗ (π ∘↪ CTX.ηᴿʷ W) Xᴿ
    → renameEnv π (CTX.impEnvʷ W) ⊢
        renameᵗ (toRenameᵗ (π ∘↪ CTX.ηᴸʷ W))
          (lookupStore (CTX.sourceStoreʷ W) Xᴸ)
        ⊑ renameᵗ (toRenameᵗ (π ∘↪ CTX.ηᴿʷ W))
          (lookupStore (CTX.targetStoreʷ W) Xᴿ)
  reps {Xᴸ} {Xᴿ} aligned =
    CTX.imprecision-cong
      (sym (rename-composed π (CTX.ηᴸʷ W)
        (lookupStore (CTX.sourceStoreʷ W) Xᴸ)))
      (sym (rename-composed π (CTX.ηᴿʷ W)
        (lookupStore (CTX.targetStoreʷ W) Xᴿ)))
      (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
        (λ X eq → trans (renameEnv-image π (CTX.impEnvʷ W) X) eq)
        (CTX.representationsImprecise inv old-aligned))
    where
    old-aligned :
      toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
    old-aligned = toRenameᵗ-injective π
      (trans (sym (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ))
        (trans aligned (toRenameᵗ-∘ π (CTX.ηᴿʷ W) Xᴿ)))

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ
          ≢ toRenameᵗ (π ∘↪ CTX.ηᴿʷ W) Xᴿ)
    → lookupStore (CTX.targetStoreʷ W) Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar _ ]
          (lookupStore (CTX.targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ
              ≢ toRenameᵗ (π ∘↪ CTX.ηᴿʷ W) Yᴿ)
  unmatched Xᴿ no-source
      with CTX.unmatchedTargetsDynamic inv Xᴿ
        (λ Xᴸ aligned → no-source Xᴸ
          (trans (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ)
            (trans (cong (toRenameᵗ π) aligned)
              (sym (toRenameᵗ-∘ π (CTX.ηᴿʷ W) Xᴿ)))))
  unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
  unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , head-no-source) =
    inj₂ (Yᴿ , entry , renamed-head-no-source)
    where
    renamed-head-no-source : ∀ Xᴸ
      → toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (π ∘↪ CTX.ηᴿʷ W) Yᴿ
    renamed-head-no-source Xᴸ aligned =
      head-no-source Xᴸ
        (toRenameᵗ-injective π
          (trans (sym (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ))
            (trans aligned
              (toRenameᵗ-∘ π (CTX.ηᴿʷ W) Yᴿ))))

  unoccupied : ∀ Xᴸ
    → renameEnv π (CTX.impEnvʷ W)
        (toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → lookupStore (CTX.sourceStoreʷ W) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (π ∘↪ CTX.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (π ∘↪ CTX.ηᴸʷ W) Xᴸ
  unoccupied Xᴸ mark entry Xᴿ aligned =
    CTX.dynamicStarSourcesUnoccupied inv Xᴸ old-mark entry Xᴿ
      old-aligned
    where
    old-mark :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    old-mark =
      trans
        (sym (renameEnv-image π (CTX.impEnvʷ W)
          (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)))
        (trans (cong (renameEnv π (CTX.impEnvʷ W))
          (sym (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ))) mark)

    old-aligned :
      toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≡ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ
    old-aligned = toRenameᵗ-injective π
      (trans (sym (toRenameᵗ-∘ π (CTX.ηᴿʷ W) Xᴿ))
        (trans aligned (toRenameᵗ-∘ π (CTX.ηᴸʷ W) Xᴸ)))

rename-bind-imprecision : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A CTX.⊑ᵂ⟨ W ⟩ B
  → renameEnv π (CTX.impEnvʷ W) ⊢
      renameᵗ (toRenameᵗ (π ∘↪ CTX.ηᴸʷ W)) A
      ⊑ renameᵗ (toRenameᵗ (π ∘↪ CTX.ηᴿʷ W)) B
rename-bind-imprecision π W {A} {B} A⊑B =
  CTX.imprecision-cong
    (sym (rename-composed π (CTX.ηᴸʷ W) A))
    (sym (rename-composed π (CTX.ηᴿʷ W) B))
    (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
      (λ X eq → trans (renameEnv-image π (CTX.impEnvʷ W) X) eq)
      A⊑B)

rename-fresh-classification : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    (B : Ty Δᴿ)
  → ⇑ᵗ B ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar (Nat.suc Δᴿ) ]
        (⇑ᵗ B ≡ ＇ Yᴿ)
      × (∀ Xᴸ
          → toRenameᵗ (skip (CTX.ηᴸʷ W)) Xᴸ
            ≢ toRenameᵗ (keep (CTX.ηᴿʷ W)) Yᴿ)
  → ⇑ᵗ B ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar (Nat.suc Δᴿ) ]
        (⇑ᵗ B ≡ ＇ Yᴿ)
      × (∀ Xᴸ
          → toRenameᵗ (skip (π ∘↪ CTX.ηᴸʷ W)) Xᴸ
            ≢ toRenameᵗ (keep (π ∘↪ CTX.ηᴿʷ W)) Yᴿ)
rename-fresh-classification π W B (inj₁ dynamic) = inj₁ dynamic
rename-fresh-classification π W B
    (inj₂ (Yᴿ , entry , no-source)) =
  inj₂ (Yᴿ , entry , renamed-no-source)
  where
  renamed-no-source : ∀ Xᴸ
    → toRenameᵗ (skip (π ∘↪ CTX.ηᴸʷ W)) Xᴸ
      ≢ toRenameᵗ (keep (π ∘↪ CTX.ηᴿʷ W)) Yᴿ
  renamed-no-source Xᴸ aligned =
    no-source Xᴸ
      (toRenameᵗ-injective (keep π)
        (trans (sym (toRenameᵗ-∘ (keep π) (skip (CTX.ηᴸʷ W)) Xᴸ))
          (trans aligned
            (toRenameᵗ-∘ (keep π) (keep (CTX.ηᴿʷ W)) Yᴿ))))

empty-center-env : (Delta : TyCtx) (Z : TyVar Delta)
  → CTX.impEnvʷ (CTX.emptyCenterWorld Delta) Z ≡ X⊑★
empty-center-env Nat.zero ()
empty-center-env (Nat.suc Delta) Fin.zero = refl
empty-center-env (Nat.suc Delta) (Fin.suc Z) = empty-center-env Delta Z

mutual
  renameWorld : ∀ {Δᴸ Δᴿ Δ Δ′}
    → Δ ↪ᵗ Δ′
    → CTX.World Δᴸ Δᴿ Δ
    → CTX.World Δᴸ Δᴿ Δ′
  renameWorld {Δ′ = Δ′} empty CTX.emptyʷ = CTX.emptyCenterWorld Δ′
  renameWorld empty W@(CTX.honestifyʷ W₀) =
    CTX.mix-renamed-targetʷ empty empty W W
      (renameWorld-invariants empty W)
  renameWorld empty
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) =
    CTX.mix-renamed-targetʷ empty empty W W
      (renameWorld-invariants empty W)
  renameWorld empty W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) =
    CTX.mix-renamed-targetʷ empty empty W W
      (renameWorld-invariants empty W)
  renameWorld empty W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    CTX.mix-renamed-targetʷ empty empty W W
      (renameWorld-invariants empty W)
  renameWorld (skip π) W = CTX.skip-centerʷ (renameWorld π W)
  renameWorld (keep π) (CTX.skip-centerʷ W) =
    CTX.skip-centerʷ (renameWorld π W)
  renameWorld (keep π) (CTX.lift-bothʷ v W) =
    CTX.lift-bothʷ v (renameWorld π W)
  renameWorld (keep π) (CTX.lift-leftʷ W) =
    CTX.lift-leftʷ (renameWorld π W)
  renameWorld (keep π) (CTX.bind-leftʷ W A) =
    CTX.bind-leftʷ (renameWorld π W) A
  renameWorld (keep π) (CTX.bind-rightʷ W B fresh) =
    CTX.bind-rightʷ (renameWorld π W) B
      (rename-fresh-classification-at π W B fresh)
  renameWorld (keep π) (CTX.bind-bothʷ W A B A⊑B) =
    CTX.bind-bothʷ (renameWorld π W) A B
      (rename-bind-imprecision-at π W A⊑B)
  renameWorld (keep π) (CTX.bind-both-starʷ W A B A⊑B A≢★) =
    CTX.bind-both-starʷ (renameWorld π W) A B
      (rename-bind-imprecision-at π W A⊑B) A≢★
  renameWorld (keep π) W@(CTX.honestifyʷ W₀) =
    CTX.mix-renamed-targetʷ (keep π) (keep π) W W
      (renameWorld-invariants (keep π) W)
  renameWorld (keep π)
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) =
    CTX.mix-renamed-targetʷ (keep π) (keep π) W W
      (renameWorld-invariants (keep π) W)
  renameWorld (keep π) W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) =
    CTX.mix-renamed-targetʷ (keep π) (keep π) W W
      (renameWorld-invariants (keep π) W)
  renameWorld (keep π)
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) =
    CTX.mix-renamed-targetʷ (keep π) (keep π) W W
      (renameWorld-invariants (keep π) W)

  rename-ηᴸ-image : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ)
    → toRenameᵗ (CTX.ηᴸʷ (renameWorld π W)) X
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) X)
  rename-ηᴸ-image empty CTX.emptyʷ ()
  rename-ηᴸ-image empty W@(CTX.honestifyʷ W₀) X =
    toRenameᵗ-∘ empty (CTX.ηᴸʷ W) X
  rename-ηᴸ-image empty
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) X =
    toRenameᵗ-∘ empty (CTX.ηᴸʷ W) X
  rename-ηᴸ-image empty W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ empty (CTX.ηᴸʷ W) X
  rename-ηᴸ-image empty
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ empty (CTX.ηᴸʷ W) X
  rename-ηᴸ-image (skip π) W X =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.skip-centerʷ W) X =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.lift-bothʷ v W) Fin.zero = refl
  rename-ηᴸ-image (keep π) (CTX.lift-bothʷ v W) (Fin.suc X) =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.lift-leftʷ W) Fin.zero = refl
  rename-ηᴸ-image (keep π) (CTX.lift-leftʷ W) (Fin.suc X) =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.bind-leftʷ W A) Fin.zero = refl
  rename-ηᴸ-image (keep π) (CTX.bind-leftʷ W A) (Fin.suc X) =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.bind-rightʷ W B fresh) X =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.bind-bothʷ W A B p) Fin.zero = refl
  rename-ηᴸ-image (keep π) (CTX.bind-bothʷ W A B p)
      (Fin.suc X) =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) (CTX.bind-both-starʷ W A B p A≢★)
      Fin.zero = refl
  rename-ηᴸ-image (keep π) (CTX.bind-both-starʷ W A B p A≢★)
      (Fin.suc X) =
    cong Fin.suc (rename-ηᴸ-image π W X)
  rename-ηᴸ-image (keep π) W@(CTX.honestifyʷ W₀) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴸʷ W) X
  rename-ηᴸ-image (keep π)
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴸʷ W) X
  rename-ηᴸ-image (keep π)
      W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴸʷ W) X
  rename-ηᴸ-image (keep π)
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴸʷ W) X

  rename-ηᴿ-image : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ) (X : TyVar Δᴿ)
    → toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) X
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) X)
  rename-ηᴿ-image empty CTX.emptyʷ ()
  rename-ηᴿ-image empty W@(CTX.honestifyʷ W₀) X =
    toRenameᵗ-∘ empty (CTX.ηᴿʷ W) X
  rename-ηᴿ-image empty
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) X =
    toRenameᵗ-∘ empty (CTX.ηᴿʷ W) X
  rename-ηᴿ-image empty W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ empty (CTX.ηᴿʷ W) X
  rename-ηᴿ-image empty
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ empty (CTX.ηᴿʷ W) X
  rename-ηᴿ-image (skip π) W X =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.skip-centerʷ W) X =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.lift-bothʷ v W) Fin.zero = refl
  rename-ηᴿ-image (keep π) (CTX.lift-bothʷ v W) (Fin.suc X) =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.lift-leftʷ W) X =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.bind-leftʷ W A) X =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.bind-rightʷ W B fresh) Fin.zero = refl
  rename-ηᴿ-image (keep π) (CTX.bind-rightʷ W B fresh)
      (Fin.suc X) =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.bind-bothʷ W A B p) Fin.zero = refl
  rename-ηᴿ-image (keep π) (CTX.bind-bothʷ W A B p)
      (Fin.suc X) =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) (CTX.bind-both-starʷ W A B p A≢★)
      Fin.zero = refl
  rename-ηᴿ-image (keep π) (CTX.bind-both-starʷ W A B p A≢★)
      (Fin.suc X) =
    cong Fin.suc (rename-ηᴿ-image π W X)
  rename-ηᴿ-image (keep π) W@(CTX.honestifyʷ W₀) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴿʷ W) X
  rename-ηᴿ-image (keep π)
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴿʷ W) X
  rename-ηᴿ-image (keep π)
      W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴿʷ W) X
  rename-ηᴿ-image (keep π)
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) X =
    toRenameᵗ-∘ (keep π) (CTX.ηᴿʷ W) X

  rename-env-image : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ) (Z : TyVar Δ)
    → CTX.impEnvʷ (renameWorld π W) (toRenameᵗ π Z)
      ≡ CTX.impEnvʷ W Z
  rename-env-image empty CTX.emptyʷ ()
  rename-env-image empty (CTX.honestifyʷ W) ()
  rename-env-image empty
      (CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) ()
  rename-env-image empty (CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) ()
  rename-env-image empty
      (CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) ()
  rename-env-image (skip π) W Z = rename-env-image π W Z
  rename-env-image (keep π) (CTX.skip-centerʷ W) Fin.zero = refl
  rename-env-image (keep π) (CTX.skip-centerʷ W) (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) (CTX.lift-bothʷ v W) Fin.zero = refl
  rename-env-image (keep π) (CTX.lift-bothʷ v W) (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) (CTX.lift-leftʷ W) Fin.zero = refl
  rename-env-image (keep π) (CTX.lift-leftʷ W) (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) (CTX.bind-leftʷ W A) Fin.zero = refl
  rename-env-image (keep π) (CTX.bind-leftʷ W A) (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) (CTX.bind-rightʷ W B fresh) Fin.zero = refl
  rename-env-image (keep π) (CTX.bind-rightʷ W B fresh) (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) (CTX.bind-bothʷ W A B A⊑B) Fin.zero = refl
  rename-env-image (keep π) (CTX.bind-bothʷ W A B A⊑B)
      (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) (CTX.bind-both-starʷ W A B p A≢★)
      Fin.zero = refl
  rename-env-image (keep π) (CTX.bind-both-starʷ W A B p A≢★)
      (Fin.suc Z) =
    rename-env-image π W Z
  rename-env-image (keep π) W@(CTX.honestifyʷ W₀) Z =
    renameEnv-image (keep π) (CTX.impEnvʷ W) Z
  rename-env-image (keep π)
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) Z =
    renameEnv-image (keep π) (CTX.impEnvʷ W) Z
  rename-env-image (keep π)
      W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) Z =
    renameEnv-image (keep π) (CTX.impEnvʷ W) Z
  rename-env-image (keep π)
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) Z =
    renameEnv-image (keep π) (CTX.impEnvʷ W) Z

  rename-env-pointwise : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ) (Z : TyVar Δ′)
    → CTX.impEnvʷ (renameWorld π W) Z
      ≡ renameEnv π (CTX.impEnvʷ W) Z
  rename-env-pointwise {Δ′ = Δ′} empty CTX.emptyʷ Z =
    empty-center-env Δ′ Z
  rename-env-pointwise empty W@(CTX.honestifyʷ W₀) Z = refl
  rename-env-pointwise empty
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) Z = refl
  rename-env-pointwise empty
      W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) Z = refl
  rename-env-pointwise empty
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) Z = refl
  rename-env-pointwise (skip π) W Fin.zero = refl
  rename-env-pointwise (skip π) W (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) (CTX.skip-centerʷ W) Fin.zero = refl
  rename-env-pointwise (keep π) (CTX.skip-centerʷ W) (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) (CTX.lift-bothʷ v W) Fin.zero = refl
  rename-env-pointwise (keep π) (CTX.lift-bothʷ v W) (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) (CTX.lift-leftʷ W) Fin.zero = refl
  rename-env-pointwise (keep π) (CTX.lift-leftʷ W) (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) (CTX.bind-leftʷ W A) Fin.zero = refl
  rename-env-pointwise (keep π) (CTX.bind-leftʷ W A) (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) (CTX.bind-rightʷ W B fresh) Fin.zero = refl
  rename-env-pointwise (keep π) (CTX.bind-rightʷ W B fresh)
      (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) (CTX.bind-bothʷ W A B p) Fin.zero = refl
  rename-env-pointwise (keep π) (CTX.bind-bothʷ W A B p)
      (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π)
      (CTX.bind-both-starʷ W A B p A≢★) Fin.zero = refl
  rename-env-pointwise (keep π)
      (CTX.bind-both-starʷ W A B p A≢★) (Fin.suc Z) =
    rename-env-pointwise π W Z
  rename-env-pointwise (keep π) W@(CTX.honestifyʷ W₀) Z = refl
  rename-env-pointwise (keep π)
      W@(CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) Z = refl
  rename-env-pointwise (keep π)
      W@(CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) Z = refl
  rename-env-pointwise (keep π)
      W@(CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) Z = refl

  rename-skip-ηᴸ-image : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
      (X : TyVar Δᴸ)
    → toRenameᵗ (skip (CTX.ηᴸʷ (renameWorld π W))) X
      ≡ toRenameᵗ (keep π) (toRenameᵗ (skip (CTX.ηᴸʷ W)) X)
  rename-skip-ηᴸ-image π W X =
    cong Fin.suc (rename-ηᴸ-image π W X)

  rename-keep-ηᴿ-image : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
      (X : TyVar (Nat.suc Δᴿ))
    → toRenameᵗ (keep (CTX.ηᴿʷ (renameWorld π W))) X
      ≡ toRenameᵗ (keep π) (toRenameᵗ (keep (CTX.ηᴿʷ W)) X)
  rename-keep-ηᴿ-image π W Fin.zero = refl
  rename-keep-ηᴿ-image π W (Fin.suc X) =
    cong Fin.suc (rename-ηᴿ-image π W X)

  rename-fresh-classification-at : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
      (B : Ty Δᴿ)
    → ⇑ᵗ B ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar (Nat.suc Δᴿ) ]
          (⇑ᵗ B ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (CTX.ηᴸʷ W)) Xᴸ
              ≢ toRenameᵗ (keep (CTX.ηᴿʷ W)) Yᴿ)
    → ⇑ᵗ B ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar (Nat.suc Δᴿ) ]
          (⇑ᵗ B ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → toRenameᵗ (skip (CTX.ηᴸʷ (renameWorld π W))) Xᴸ
              ≢ toRenameᵗ (keep (CTX.ηᴿʷ (renameWorld π W))) Yᴿ)
  rename-fresh-classification-at π W B (inj₁ dynamic) = inj₁ dynamic
  rename-fresh-classification-at π W B
      (inj₂ (Yᴿ , entry , no-source)) =
    inj₂ (Yᴿ , entry , renamed-no-source)
    where
    renamed-no-source : ∀ Xᴸ
      → toRenameᵗ (skip (CTX.ηᴸʷ (renameWorld π W))) Xᴸ
        ≢ toRenameᵗ (keep (CTX.ηᴿʷ (renameWorld π W))) Yᴿ
    renamed-no-source Xᴸ aligned =
      no-source Xᴸ
        (toRenameᵗ-injective (keep π)
          (trans (sym (rename-skip-ηᴸ-image π W Xᴸ))
            (trans aligned (rename-keep-ηᴿ-image π W Yᴿ))))

  embedᴸ-rename : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ)
    → CTX.embedᴸ (renameWorld π W) A
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A)
  embedᴸ-rename π W A =
    trans (renameᵗ-cong A (rename-ηᴸ-image π W))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ W))
        (toRenameᵗ π) A))

  embedᴿ-rename : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ) (B : Ty Δᴿ)
    → CTX.embedᴿ (renameWorld π W) B
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W B)
  embedᴿ-rename π W B =
    trans (renameᵗ-cong B (rename-ηᴿ-image π W))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ W))
        (toRenameᵗ π) B))

  rename-bind-imprecision-at : ∀ {Δᴸ Δᴿ Δ Δ′}
      (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ W ⟩ B
    → A CTX.⊑ᵂ⟨ renameWorld π W ⟩ B
  rename-bind-imprecision-at π W {A} {B} p =
    CTX.imprecision-cong
      (sym (embedᴸ-rename π W A))
      (sym (embedᴿ-rename π W B))
      (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
        (λ X eq → trans (rename-env-image π W X) eq) p)

rename-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTX.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → A CTX.⊑ᵂ⟨ W ⟩ B
  → A CTX.⊑ᵂ⟨ renameWorld π W ⟩ B
rename-⊑ᵂ {W = W} π p = rename-bind-imprecision-at π W p

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

preimageSubst-world-star : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → ∀ Z′
  → CTX.impEnvʷ (renameWorld π W) Z′ ≡ X⊑★
  → CTX.impEnvʷ W ⊢ preimageSubst π Z′ ⊑ ★
preimageSubst-world-star {W = W} π Z′ star
    with preimage? π Z′ in pre
preimageSubst-world-star {W = W} π Z′ star | just Z =
  X⊑★ (trans (sym (rename-env-image π W Z))
    (subst≡
      (λ C → CTX.impEnvʷ (renameWorld π W) C ≡ X⊑★)
      (preimage?-sound π pre) star))
preimageSubst-world-star π Z′ star | nothing = ★⊑★

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
    {W : CTX.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → A CTX.⊑ᵂ⟨ renameWorld π W ⟩ B
  → A CTX.⊑ᵂ⟨ W ⟩ B
unrename-⊑ᵂ {W = W} {A = A} {B = B} π p =
  subst≡ (λ L → CTX.impEnvʷ W ⊢ L ⊑ CTX.embedᴿ W B)
    (preimageSubst-rename π (CTX.embedᴸ W A))
    (subst≡
      (λ R → CTX.impEnvʷ W ⊢
        substᵗ (preimageSubst π)
          (renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A)) ⊑ R)
      (preimageSubst-rename π (CTX.embedᴿ W B))
      (subst-⊑ (preimageSubst-world-star {W = W} π)
        (subst≡
          (λ L → CTX.impEnvʷ (renameWorld π W) ⊢
            L ⊑ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W B))
          (embedᴸ-rename π W A)
          (subst≡
            (λ R → CTX.impEnvʷ (renameWorld π W) ⊢
              CTX.embedᴸ (renameWorld π W) A ⊑ R)
            (embedᴿ-rename π W B) p))))

renameCtx : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTX.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.CtxImp W
  → CTX.CtxImp (renameWorld π W)
renameCtx {W = W} π [] = []
renameCtx {W = W} π (CTX.ctx-imp A B p ∷ γ) =
  CTX.ctx-imp A B (rename-⊑ᵂ {W = W} π p) ∷
    renameCtx {W = W} π γ

rename-∋ʷ : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {x A B} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (π : Δ ↪ᵗ Δ′)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → renameCtx {W = W} π γ CTX.∋ʷ x ⦂
      CTX.ctx-imp A B (rename-⊑ᵂ {W = W} π p)
rename-∋ʷ {W = W} π CTX.Zʷ = CTX.Zʷ
rename-∋ʷ {W = W} π (CTX.Sʷ x∈) =
  CTX.Sʷ (rename-∋ʷ {W = W} π x∈)

renameSameCtx : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γ′ : CTX.CtxImp W′}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.SameCtx γ γ′
  → CTX.SameCtx (renameCtx {W = W} π γ)
      (renameCtx {W = W′} π γ′)
renameSameCtx π CTX.same-[] = CTX.same-[]
renameSameCtx π (CTX.same-∷ sc) =
  CTX.same-∷ (renameSameCtx π sc)

------------------------------------------------------------------------
-- Binder transport
------------------------------------------------------------------------

renameLiftCtx : ∀ {Δᴸ Δᴿ Δ Δ′} {v}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {γ′ : CTX.CtxImp (CTX.liftWorldBoth v W)}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.LiftCtx v γ γ′
  → CTX.LiftCtx v (renameCtx {W = W} π γ)
      (renameCtx {W = CTX.liftWorldBoth v W} (keep π) γ′)
renameLiftCtx π CTX.lift-[] = CTX.lift-[]
renameLiftCtx π (CTX.lift-∷ liftγ) =
  CTX.lift-∷ (renameLiftCtx π liftγ)

renameLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δ′} {v}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {γ′ : CTX.CtxImp (CTX.liftWorldLeft W)}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.LiftCtxᴸ v γ γ′
  → CTX.LiftCtxᴸ v (renameCtx {W = W} π γ)
      (renameCtx {W = CTX.liftWorldLeft W} (keep π) γ′)
renameLiftCtxᴸ π CTX.liftᴸ-[] = CTX.liftᴸ-[]
renameLiftCtxᴸ π (CTX.liftᴸ-∷ liftγ) =
  CTX.liftᴸ-∷ (renameLiftCtxᴸ π liftγ)

renameSmartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ Δ′ Δᵐ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTX.CtxImp W} {γᵐ : CTX.CtxImp Wᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (πᵐ : Δᵐ ↪ᵗ Δᵐ′)
  → CTX.SmartLiftCtxᴸ γ γᵐ
  → CTX.SmartLiftCtxᴸ
      (renameCtx {W = W} π γ)
      (renameCtx {W = Wᵐ} πᵐ γᵐ)
renameSmartLiftCtxᴸ π πᵐ CTX.smart-lift-[] = CTX.smart-lift-[]
renameSmartLiftCtxᴸ π πᵐ (CTX.smart-lift-∷ liftγ) =
  CTX.smart-lift-∷ (renameSmartLiftCtxᴸ π πᵐ liftγ)

renameCtx-tgt : ∀ {Δᴸ Δᴿ Δ Δ′} {W : CTX.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → (γ : CTX.CtxImp W)
  → CTX.tgtCtxʷ (renameCtx {W = W} π γ) ≡ CTX.tgtCtxʷ γ
renameCtx-tgt π [] = refl
renameCtx-tgt π (CTX.ctx-imp A B p ∷ γ) =
  cong (B ∷_) (renameCtx-tgt π γ)

------------------------------------------------------------------------
-- Runtime and rebasing records
------------------------------------------------------------------------

empty-center-source-store : (Delta : TyCtx)
  → CTX.sourceStoreʷ (CTX.emptyCenterWorld Delta) ≡ store-empty
empty-center-source-store Nat.zero = refl
empty-center-source-store (Nat.suc Delta) =
  empty-center-source-store Delta

empty-center-target-store : (Delta : TyCtx)
  → CTX.targetStoreʷ (CTX.emptyCenterWorld Delta) ≡ store-empty
empty-center-target-store Nat.zero = refl
empty-center-target-store (Nat.suc Delta) =
  empty-center-target-store Delta

rename-source-store : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
  → CTX.sourceStoreʷ (renameWorld π W) ≡ CTX.sourceStoreʷ W
rename-source-store {Δ′ = Δ′} empty CTX.emptyʷ =
  empty-center-source-store Δ′
rename-source-store (skip π) W = rename-source-store π W
rename-source-store empty (CTX.honestifyʷ W) = refl
rename-source-store (keep π) (CTX.honestifyʷ W) = refl
rename-source-store empty
    (CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = refl
rename-source-store (keep π)
    (CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = refl
rename-source-store (keep π) (CTX.skip-centerʷ W) =
  rename-source-store π W
rename-source-store (keep π) (CTX.lift-bothʷ v W) =
  cong store-lift (rename-source-store π W)
rename-source-store (keep π) (CTX.lift-leftʷ W) =
  cong store-lift (rename-source-store π W)
rename-source-store (keep π) (CTX.bind-leftʷ W A) =
  cong (λ Σ → store-bind Σ A) (rename-source-store π W)
rename-source-store (keep π) (CTX.bind-rightʷ W B fresh) =
  rename-source-store π W
rename-source-store (keep π) (CTX.bind-bothʷ W A B p) =
  cong (λ Σ → store-bind Σ A) (rename-source-store π W)
rename-source-store (keep π) (CTX.bind-both-starʷ W A B p A≢★) =
  cong (λ Σ → store-bind Σ A) (rename-source-store π W)
rename-source-store empty (CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) = refl
rename-source-store empty
    (CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) = refl
rename-source-store (keep π) (CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) = refl
rename-source-store (keep π)
    (CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) = refl

rename-target-store : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
  → CTX.targetStoreʷ (renameWorld π W) ≡ CTX.targetStoreʷ W
rename-target-store {Δ′ = Δ′} empty CTX.emptyʷ =
  empty-center-target-store Δ′
rename-target-store (skip π) W = rename-target-store π W
rename-target-store empty (CTX.honestifyʷ W) = refl
rename-target-store (keep π) (CTX.honestifyʷ W) = refl
rename-target-store empty
    (CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = refl
rename-target-store (keep π)
    (CTX.lower-leftʷ W₁ Wᴸ ηᴸ ηᴿ keep-eq skip-eq stores inv) = refl
rename-target-store (keep π) (CTX.skip-centerʷ W) =
  rename-target-store π W
rename-target-store (keep π) (CTX.lift-bothʷ v W) =
  cong store-lift (rename-target-store π W)
rename-target-store (keep π) (CTX.lift-leftʷ W) =
  rename-target-store π W
rename-target-store (keep π) (CTX.bind-leftʷ W A) =
  rename-target-store π W
rename-target-store (keep π) (CTX.bind-rightʷ W B fresh) =
  cong (λ Σ → store-bind Σ B) (rename-target-store π W)
rename-target-store (keep π) (CTX.bind-bothʷ W A B p) =
  cong (λ Σ → store-bind Σ B) (rename-target-store π W)
rename-target-store (keep π) (CTX.bind-both-starʷ W A B p A≢★) =
  cong (λ Σ → store-bind Σ B) (rename-target-store π W)
rename-target-store empty (CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) = refl
rename-target-store empty
    (CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) = refl
rename-target-store (keep π) (CTX.mix-targetʷ π₀ Wˢ Wᵗ inv) = refl
rename-target-store (keep π)
    (CTX.mix-renamed-targetʷ πˢ πᵗ Wˢ Wᵗ inv) = refl

rename-target-typing : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {N : Term Δᴿ} {B : Ty Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ N ⦂ B
  → ⟨ Δᴿ , CTX.targetStoreʷ (renameWorld π W) ,
      CTX.tgtCtxʷ (renameCtx {W = W} π γ) ⟩ ⊢ N ⦂ B
rename-target-typing {W = W} {γ = γ} {N = N} {B = B} π N⊢ =
  subst≡
    (λ Σ → ⟨ _ , Σ , CTX.tgtCtxʷ (renameCtx {W = W} π γ) ⟩
      ⊢ N ⦂ B)
    (sym (rename-target-store π W))
    (subst≡
      (λ Γ → ⟨ _ , CTX.targetStoreʷ W , Γ ⟩ ⊢ N ⦂ B)
      (sym (renameCtx-tgt π γ)) N⊢)

rename-source-⊢↑ : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴸ Rᴸ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↑ Δᴸ A B}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c
  → CTX.sourceStoreʷ (renameWorld π W) ⊢↑[ Xᴸ ⦂ Rᴸ ] c
rename-source-⊢↑ {W = W} {c = c} π c⊢ =
  subst≡ (λ Σ → Σ ⊢↑[ _ ⦂ _ ] c)
    (sym (rename-source-store π W)) c⊢

rename-source-⊢↓ : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴸ Rᴸ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↓ Δᴸ A B}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c
  → CTX.sourceStoreʷ (renameWorld π W) ⊢↓[ Xᴸ ⦂ Rᴸ ] c
rename-source-⊢↓ {W = W} {c = c} π c⊢ =
  subst≡ (λ Σ → Σ ⊢↓[ _ ⦂ _ ] c)
    (sym (rename-source-store π W)) c⊢

rename-target-⊢↑ : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴿ Rᴿ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↑ Δᴿ A B}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.targetStoreʷ W ⊢↑[ Xᴿ ⦂ Rᴿ ] c
  → CTX.targetStoreʷ (renameWorld π W) ⊢↑[ Xᴿ ⦂ Rᴿ ] c
rename-target-⊢↑ {W = W} {c = c} π c⊢ =
  subst≡ (λ Σ → Σ ⊢↑[ _ ⦂ _ ] c)
    (sym (rename-target-store π W)) c⊢

rename-target-⊢↓ : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴿ Rᴿ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↓ Δᴿ A B}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.targetStoreʷ W ⊢↓[ Xᴿ ⦂ Rᴿ ] c
  → CTX.targetStoreʷ (renameWorld π W) ⊢↓[ Xᴿ ⦂ Rᴿ ] c
rename-target-⊢↓ {W = W} {c = c} π c⊢ =
  subst≡ (λ Σ → Σ ⊢↓[ _ ⦂ _ ] c)
    (sym (rename-target-store π W)) c⊢

rename-source-reveal-position : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴸ Rᴸ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↑ Δᴸ A B}
  → (π : Δ ↪ᵗ Δ′)
  → (c⊢ : CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (P : GeneratorPosition)
  → revealGeneratorPosition c⊢ ≡ P
  → revealGeneratorPosition (rename-source-⊢↑ π c⊢) ≡ P
rename-source-reveal-position {W = W} π c⊢ P eq =
  trans
    (revealGeneratorPosition-store-transport
      (sym (rename-source-store π W)) c⊢)
    eq

rename-source-conceal-position : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴸ Rᴸ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↓ Δᴸ A B}
  → (π : Δ ↪ᵗ Δ′)
  → (c⊢ : CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → (P : GeneratorPosition)
  → concealGeneratorPosition c⊢ ≡ P
  → concealGeneratorPosition (rename-source-⊢↓ π c⊢) ≡ P
rename-source-conceal-position {W = W} π c⊢ P eq =
  trans
    (concealGeneratorPosition-store-transport
      (sym (rename-source-store π W)) c⊢)
    eq

rename-target-reveal-position : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴿ Rᴿ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↑ Δᴿ A B}
  → (π : Δ ↪ᵗ Δ′)
  → (c⊢ : CTX.targetStoreʷ W ⊢↑[ Xᴿ ⦂ Rᴿ ] c)
  → (P : GeneratorPosition)
  → revealGeneratorPosition c⊢ ≡ P
  → revealGeneratorPosition (rename-target-⊢↑ π c⊢) ≡ P
rename-target-reveal-position {W = W} π c⊢ P eq =
  trans
    (revealGeneratorPosition-store-transport
      (sym (rename-target-store π W)) c⊢)
    eq

rename-target-conceal-position : ∀ {Δᴸ Δᴿ Δ Δ′ A B Xᴿ Rᴿ}
    {W : CTX.World Δᴸ Δᴿ Δ} {c : Conv↓ Δᴿ A B}
  → (π : Δ ↪ᵗ Δ′)
  → (c⊢ : CTX.targetStoreʷ W ⊢↓[ Xᴿ ⦂ Rᴿ ] c)
  → (P : GeneratorPosition)
  → concealGeneratorPosition c⊢ ≡ P
  → concealGeneratorPosition (rename-target-⊢↓ π c⊢) ≡ P
rename-target-conceal-position {W = W} π c⊢ P eq =
  trans
    (concealGeneratorPosition-store-transport
      (sym (rename-target-store π W)) c⊢)
    eq

renameSameRuntime : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.SameRuntime W W′
  → CTX.SameRuntime (renameWorld π W) (renameWorld π W′)
renameSameRuntime {W = W} {W′ = W′} π
    (CTX.same-runtime source-eq target-eq) =
  CTX.same-runtime
    (trans (rename-source-store π W′)
      (trans source-eq (sym (rename-source-store π W))))
    (trans (rename-target-store π W′)
      (trans target-eq (sym (rename-target-store π W))))

renameStoreRep : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp (renameWorld π W) Xᴸ Xᴿ
renameStoreRep {W = W} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} π
    (CTX.store-rep-imp represented) =
  CTX.store-rep-imp
    (subst≡
      (λ A → A CTX.⊑ᵂ⟨ renameWorld π W ⟩
        CTX.resolveVar (CTX.targetStoreʷ (renameWorld π W)) Xᴿ)
      (sym (cong (λ Σ → CTX.resolveVar Σ Xᴸ)
        (rename-source-store π W)))
      (subst≡
        (λ B → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
          CTX.⊑ᵂ⟨ renameWorld π W ⟩ B)
        (sym (cong (λ Σ → CTX.resolveVar Σ Xᴿ)
          (rename-target-store π W)))
        (rename-⊑ᵂ {W = W} π represented)))

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

rename-left-eq : ∀ {Δ₁ᴸ Δ₁ᴿ Δ₂ᴸ Δ₂ᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W₁ : CTX.World Δ₁ᴸ Δ₁ᴿ Δ)
    (W₂ : CTX.World Δ₂ᴸ Δ₂ᴿ Δ)
    {X₁ : TyVar Δ₁ᴸ} {X₂ : TyVar Δ₂ᴸ}
  → toRenameᵗ (CTX.ηᴸʷ W₁) X₁ ≡ toRenameᵗ (CTX.ηᴸʷ W₂) X₂
  → toRenameᵗ (CTX.ηᴸʷ (renameWorld π W₁)) X₁
      ≡ toRenameᵗ (CTX.ηᴸʷ (renameWorld π W₂)) X₂
rename-left-eq π W₁ W₂ eq =
  trans (rename-ηᴸ-image π W₁ _)
    (trans (cong (toRenameᵗ π) eq)
      (sym (rename-ηᴸ-image π W₂ _)))

rename-right-eq : ∀ {Δ₁ᴸ Δ₁ᴿ Δ₂ᴸ Δ₂ᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W₁ : CTX.World Δ₁ᴸ Δ₁ᴿ Δ)
    (W₂ : CTX.World Δ₂ᴸ Δ₂ᴿ Δ)
    {X₁ : TyVar Δ₁ᴿ} {X₂ : TyVar Δ₂ᴿ}
  → toRenameᵗ (CTX.ηᴿʷ W₁) X₁ ≡ toRenameᵗ (CTX.ηᴿʷ W₂) X₂
  → toRenameᵗ (CTX.ηᴿʷ (renameWorld π W₁)) X₁
      ≡ toRenameᵗ (CTX.ηᴿʷ (renameWorld π W₂)) X₂
rename-right-eq π W₁ W₂ eq =
  trans (rename-ηᴿ-image π W₁ _)
    (trans (cong (toRenameᵗ π) eq)
      (sym (rename-ηᴿ-image π W₂ _)))

rename-left-right-eq : ∀ {Δ₁ᴸ Δ₁ᴿ Δ₂ᴸ Δ₂ᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W₁ : CTX.World Δ₁ᴸ Δ₁ᴿ Δ)
    (W₂ : CTX.World Δ₂ᴸ Δ₂ᴿ Δ)
    {Xᴸ : TyVar Δ₁ᴸ} {Xᴿ : TyVar Δ₂ᴿ}
  → toRenameᵗ (CTX.ηᴸʷ W₁) Xᴸ ≡ toRenameᵗ (CTX.ηᴿʷ W₂) Xᴿ
  → toRenameᵗ (CTX.ηᴸʷ (renameWorld π W₁)) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ (renameWorld π W₂)) Xᴿ
rename-left-right-eq π W₁ W₂ eq =
  trans (rename-ηᴸ-image π W₁ _)
    (trans (cong (toRenameᵗ π) eq)
      (sym (rename-ηᴿ-image π W₂ _)))

renameRebaseAt : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTX.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.RebaseAt W W′ Xᴸ Xᴿ
  → CTX.RebaseAt (renameWorld π W) (renameWorld π W′) Xᴸ Xᴿ
renameRebaseAt {Δᴸ = Δᴸ} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} π
    (CTX.rebase-at runtime offL frozenR aligned reps) =
  CTX.rebase-at (renameSameRuntime π runtime)
    (λ Y≢ → rename-left-eq π W′ W (offL Y≢))
    (λ Y → rename-right-eq π W′ W (frozenR Y))
    (rename-left-right-eq π W′ W′ aligned)
    (renameStoreRep π reps)

rename-mark-image : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    {Xᴸ : TyVar Δᴸ}
  → CTX.impEnvʷ (renameWorld π W)
      (toRenameᵗ (CTX.ηᴸʷ (renameWorld π W)) Xᴸ)
      ≡ CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
rename-mark-image π W {Xᴸ} =
  trans (cong (CTX.impEnvʷ (renameWorld π W))
      (rename-ηᴸ-image π W Xᴸ))
    (rename-env-image π W
      (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))

rename-target-mark-image : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    {Xᴿ : TyVar Δᴿ}
  → CTX.impEnvʷ (renameWorld π W)
      (toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) Xᴿ)
      ≡ CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)
rename-target-mark-image π W {Xᴿ} =
  trans (cong (CTX.impEnvʷ (renameWorld π W))
      (rename-ηᴿ-image π W Xᴿ))
    (rename-env-image π W
      (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ))

rename-disaligned : ∀ {Δᴸ Δᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ ≢
      toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) Xᴿ ≢
      toRenameᵗ (CTX.ηᴸʷ (renameWorld π W)) Xᴸ
rename-disaligned π W {Xᴸ} disaligned Xᴿ eq =
  disaligned Xᴿ (toRenameᵗ-injective π
    (trans (sym (rename-ηᴿ-image π W Xᴿ))
      (trans eq (rename-ηᴸ-image π W Xᴸ))))

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

renameEnvPrecise : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) {μ ν : ImpEnv Δ}
  → (∀ Z → μ Z ≡ X⊑X → ν Z ≡ X⊑X)
  → ∀ Z′ → renameEnv π μ Z′ ≡ X⊑X
      → renameEnv π ν Z′ ≡ X⊑X
renameEnvPrecise empty mono Z ()
renameEnvPrecise (keep π) mono Fin.zero eq = mono Fin.zero eq
renameEnvPrecise (keep π) mono (Fin.suc Z) eq =
  renameEnvPrecise π (λ X → mono (Fin.suc X)) Z eq
renameEnvPrecise (skip π) mono Fin.zero ()
renameEnvPrecise (skip π) mono (Fin.suc Z) eq =
  renameEnvPrecise π mono Z eq

renameEnvMono-world : ∀ {Δᴸ Δᴿ Δ₁ᴸ Δ₁ᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    (W′ : CTX.World Δ₁ᴸ Δ₁ᴿ Δ)
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★ → CTX.impEnvʷ W′ Z ≡ X⊑★)
  → ∀ Z → CTX.impEnvʷ (renameWorld π W) Z ≡ X⊑★
  → CTX.impEnvʷ (renameWorld π W′) Z ≡ X⊑★
renameEnvMono-world π W W′ mono Z star =
  trans (rename-env-pointwise π W′ Z)
    (renameEnvMono π mono Z
      (trans (sym (rename-env-pointwise π W Z)) star))

renameEnvPrecise-world : ∀ {Δᴸ Δᴿ Δ₁ᴸ Δ₁ᴿ Δ Δ′}
    (π : Δ ↪ᵗ Δ′) (W : CTX.World Δᴸ Δᴿ Δ)
    (W′ : CTX.World Δ₁ᴸ Δ₁ᴿ Δ)
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑X → CTX.impEnvʷ W′ Z ≡ X⊑X)
  → ∀ Z → CTX.impEnvʷ (renameWorld π W) Z ≡ X⊑X
  → CTX.impEnvʷ (renameWorld π W′) Z ≡ X⊑X
renameEnvPrecise-world π W W′ mono Z precise =
  trans (rename-env-pointwise π W′ Z)
    (renameEnvPrecise π mono Z
      (trans (sym (rename-env-pointwise π W Z)) precise))

renameImpEnvMono : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTX.World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.ImpEnvMono W W′
  → CTX.ImpEnvMono (renameWorld π W) (renameWorld π W′)
renameImpEnvMono {W = W} {W′ = W′} π mono =
  CTX.imp-env-mono
    (renameEnvMono-world π W W′ (CTX.dynamic-preserved mono))
    (renameEnvPrecise-world π W W′ (CTX.precise-preserved mono))

renameSmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (Nat.suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (π : Δ ↪ᵗ Δ′)
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → CTX.SmartAliasMergeGuard (renameWorld π W)
      (renameWorld π Wᵐ) β α
renameSmartAliasMergeGuard {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {W = W} {Wᵐ = Wᵐ} {β = β} {α = α} π guard =
  CTX.smart-alias-merge-guard
    (subst≡ (λ Σ → Σ ∋ β ⦂ ＇ α)
      (sym (rename-target-store π W))
      (CTX.SmartAliasMergeGuard.β:=＇α guard))
    (subst≡ (λ Σ → Σ ∋ α ⦂ ★)
      (sym (rename-target-store π W))
      (CTX.SmartAliasMergeGuard.α:=★ guard))
    (trans (rename-source-store π Wᵐ)
      (trans (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)
        (cong store-lift (sym (rename-source-store π W)))))
    (trans (rename-target-store π Wᵐ)
      (trans (CTX.SmartAliasMergeGuard.targetStore-same guard)
        (sym (rename-target-store π W))))
    transport′
    old-mark-mono′
    (λ Xᴿ → rename-right-eq π Wᵐ W
      (CTX.SmartAliasMergeGuard.target-frozen guard Xᴿ))
    (rename-left-right-eq π Wᵐ W
      (CTX.SmartAliasMergeGuard.pending-at-alias guard))
    (λ Xᴸ → rename-left-eq π Wᵐ W
      (CTX.SmartAliasMergeGuard.old-source-frozen guard Xᴸ))
    no-old-source-at-alias′
    (trans (cong (CTX.impEnvʷ (renameWorld π Wᵐ))
      (rename-ηᴿ-image π W β))
      (trans (rename-env-image π Wᵐ
        (toRenameᵗ (CTX.ηᴿʷ W) β))
        (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard)))
    (trans (cong (CTX.impEnvʷ (renameWorld π Wᵐ))
      (rename-ηᴿ-image π W α))
      (trans (rename-env-image π Wᵐ
        (toRenameᵗ (CTX.ηᴿʷ W) α))
        (CTX.SmartAliasMergeGuard.name-mark-dynamic guard)))
    target-mark-off-footprint′
  where
  no-old-source-at-alias′ : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ (renameWorld π W)) Xᴸ
      ≢ toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) β
  no-old-source-at-alias′ Xᴸ eq =
    CTX.SmartAliasMergeGuard.no-old-source-at-alias guard Xᴸ
      (toRenameᵗ-injective π
        (trans (sym (rename-ηᴸ-image π W Xᴸ))
          (trans eq (rename-ηᴿ-image π W β))))

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft (renameWorld π W) ⟩ B
    → A CTX.⊑ᵂ⟨ renameWorld π Wᵐ ⟩ B
  transport′ p =
    rename-⊑ᵂ {W = Wᵐ} π
      (CTX.SmartAliasMergeGuard.transport⊑ᵂ guard
        (unrename-⊑ᵂ {W = CTX.liftWorldLeft W} (keep π) p))

  old-mark-mono′ : ∀ Z′
    → CTX.impEnvʷ (renameWorld π W) Z′ ≡ X⊑★
    → CTX.impEnvʷ (renameWorld π Wᵐ) Z′ ≡ X⊑★
  old-mark-mono′ = renameEnvMono-world π W Wᵐ
    (CTX.SmartAliasMergeGuard.old-mark-mono guard)

  target-mark-off-footprint′ : ∀ Xᴿ
    → Xᴿ ≢ β
    → Xᴿ ≢ α
    → CTX.impEnvʷ (renameWorld π W)
        (toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) Xᴿ) ≡ X⊑★
    → CTX.impEnvʷ (renameWorld π Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ (renameWorld π Wᵐ)) Xᴿ) ≡ X⊑★
  target-mark-off-footprint′ Xᴿ Xᴿ≢β Xᴿ≢α star =
    trans (rename-target-mark-image π Wᵐ)
      (CTX.SmartAliasMergeGuard.target-mark-off-footprint guard
        Xᴿ Xᴿ≢β Xᴿ≢α
        (trans (sym (rename-target-mark-image π W)) star))

renameSmartFreshBehindGuard : ∀ {Δᴸ Δᴿ Δ Δᵐ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → CTX.SmartFreshBehindGuard (renameWorld π W)
      (renameWorld
        (EmbeddingPushout.premise
          (embeddingPushout π
            (CTX.SmartFreshBehindGuard.oldCenters guard)))
        Wᵐ)
renameSmartFreshBehindGuard {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {W = W} {Wᵐ = Wᵐ} π guard =
  CTX.smart-fresh-behind-guard old′
    (trans (rename-source-store πᵐ Wᵐ)
      (trans (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
        (cong store-lift (sym (rename-source-store π W)))))
    (trans (rename-target-store πᵐ Wᵐ)
      (trans (CTX.SmartFreshBehindGuard.targetStore-same guard)
        (sym (rename-target-store π W))))
    transport′ old-mark-mono′ target-frozen′ old-source-frozen′
    fresh-not-target′ fresh-mark′ target-mark-frozen′
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  po = embeddingPushout π old
  πᵐ = EmbeddingPushout.premise po
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft (renameWorld π W) ⟩ B
    → A CTX.⊑ᵂ⟨ renameWorld πᵐ Wᵐ ⟩ B
  transport′ p =
    rename-⊑ᵂ {W = Wᵐ} πᵐ
      (CTX.SmartFreshBehindGuard.transport⊑ᵂ guard
        (unrename-⊑ᵂ {W = CTX.liftWorldLeft W} (keep π) p))

  old-mark-mono′ : ∀ Z′
    → CTX.impEnvʷ (renameWorld π W) Z′ ≡ X⊑★
    → CTX.impEnvʷ (renameWorld πᵐ Wᵐ) (toRenameᵗ old′ Z′)
        ≡ X⊑★
  old-mark-mono′ Z′ star with preimage? π Z′ in pre
  old-mark-mono′ Z′ star | nothing =
    trans (rename-env-pointwise πᵐ Wᵐ (toRenameᵗ old′ Z′))
      (renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ)
        (pushout-old-off-premise π old pre))
  old-mark-mono′ Z′ star | just Z =
    trans (rename-env-pointwise πᵐ Wᵐ (toRenameᵗ old′ Z′))
      (trans (cong (renameEnv πᵐ (CTX.impEnvʷ Wᵐ)) smart-image-eq)
        (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
            (toRenameᵗ old Z))
          (CTX.SmartFreshBehindGuard.old-mark-mono guard Z old-star)))
    where
    image-eq : Z′ ≡ toRenameᵗ π Z
    image-eq = preimage?-sound π pre

    old-star : CTX.impEnvʷ W Z ≡ X⊑★
    old-star =
      trans (sym (rename-env-image π W Z))
        (subst≡
          (λ C → CTX.impEnvʷ (renameWorld π W) C ≡ X⊑★)
          image-eq star)

    smart-image-eq :
      toRenameᵗ old′ Z′ ≡ toRenameᵗ πᵐ (toRenameᵗ old Z)
    smart-image-eq =
      trans (cong (toRenameᵗ old′) image-eq) (sym (commutes Z))

  target-frozen′ : ∀ Xᴿ
    → toRenameᵗ
        (CTX.ηᴿʷ (renameWorld πᵐ Wᵐ)) Xᴿ
      ≡ toRenameᵗ old′
        (toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) Xᴿ)
  target-frozen′ Xᴿ =
    trans (rename-ηᴿ-image πᵐ Wᵐ Xᴿ)
      (trans (cong (toRenameᵗ πᵐ)
        (CTX.SmartFreshBehindGuard.target-frozen guard Xᴿ))
        (trans (commutes (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ))
          (cong (toRenameᵗ old′)
            (sym (rename-ηᴿ-image π W Xᴿ)))))

  old-source-frozen′ : ∀ Xᴸ
    → toRenameᵗ
        (CTX.ηᴸʷ (renameWorld πᵐ Wᵐ)) (Fin.suc Xᴸ)
      ≡ toRenameᵗ old′
        (toRenameᵗ (CTX.ηᴸʷ (renameWorld π W)) Xᴸ)
  old-source-frozen′ Xᴸ =
    trans (rename-ηᴸ-image πᵐ Wᵐ (Fin.suc Xᴸ))
      (trans (cong (toRenameᵗ πᵐ)
        (CTX.SmartFreshBehindGuard.old-source-frozen guard Xᴸ))
        (trans (commutes (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))
          (cong (toRenameᵗ old′)
            (sym (rename-ηᴸ-image π W Xᴸ)))))

  fresh-not-target′ : ∀ Xᴿ
    → toRenameᵗ
        (CTX.ηᴿʷ (renameWorld πᵐ Wᵐ)) Xᴿ
      ≢ toRenameᵗ
        (CTX.ηᴸʷ (renameWorld πᵐ Wᵐ)) Fin.zero
  fresh-not-target′ Xᴿ eq =
    CTX.SmartFreshBehindGuard.fresh-not-target guard Xᴿ
      (toRenameᵗ-injective πᵐ
        (trans (sym (rename-ηᴿ-image πᵐ Wᵐ Xᴿ))
          (trans eq
            (rename-ηᴸ-image πᵐ Wᵐ Fin.zero))))

  fresh-mark′ :
    CTX.impEnvʷ (renameWorld πᵐ Wᵐ)
      (toRenameᵗ (CTX.ηᴸʷ (renameWorld πᵐ Wᵐ)) Fin.zero)
      ≡ X⊑★
  fresh-mark′ =
    trans (rename-mark-image πᵐ Wᵐ {Fin.zero})
      (CTX.SmartFreshBehindGuard.fresh-mark-dynamic guard)

  target-mark-frozen′ : ∀ Xᴿ
    → CTX.impEnvʷ (renameWorld π W)
        (toRenameᵗ (CTX.ηᴿʷ (renameWorld π W)) Xᴿ) ≡ X⊑★
    → CTX.impEnvʷ (renameWorld πᵐ Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ (renameWorld πᵐ Wᵐ)) Xᴿ) ≡ X⊑★
  target-mark-frozen′ Xᴿ star =
    trans (rename-target-mark-image πᵐ Wᵐ)
      (CTX.SmartFreshBehindGuard.target-mark-mono guard Xᴿ
        (trans (sym (rename-target-mark-image π W)) star))

------------------------------------------------------------------------
-- Derivation transport
------------------------------------------------------------------------

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d

⊢²-rename-center : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (π : Δ ↪ᵗ Δ′)
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → (p′ : A CTX.⊑ᵂ⟨ renameWorld π W ⟩ B)
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
    (⊢²-rename-center {W = CTX.liftWorldBoth X⊑X W}
      (keep π) V⊑V′
      (rename-⊑ᵂ {W = CTX.liftWorldBoth X⊑X W} (keep π) p)) p′
⊢²-rename-center {W = W} {γ = γ} π
    (CTI2.Λ⊑² {p = p} Anv zero∈A liftγ vV N⊢ V⊑N q) p′ =
  CTI2.Λ⊑² Anv zero∈A (renameLiftCtxᴸ π liftγ) vV
    (rename-target-typing π N⊢)
    (⊢²-rename-center {W = CTX.liftWorldLeft W}
      (keep π) V⊑N
      (rename-⊑ᵂ {W = CTX.liftWorldLeft W} (keep π) p)) p′
⊢²-rename-center {W = W} {γ = γ} π
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {γᵐ = γᵐ} {p = p}
      Anv zero∈A (CTX.smart-merge-alias guard) liftγ vV N⊢
      V⊑N q) p′ =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-merge-alias (renameSmartAliasMergeGuard π guard))
    (renameSmartLiftCtxᴸ π π liftγ) vV
    (rename-target-typing π N⊢)
    (⊢²-rename-center {W = Wᵐ} π V⊑N
      (rename-⊑ᵂ {W = Wᵐ} π p)) p′
⊢²-rename-center {W = W} {γ = γ} π
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {γᵐ = γᵐ} {p = p}
      Anv zero∈A (CTX.smart-fresh-behind guard) liftγ vV N⊢
      V⊑N q) p′ =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-fresh-behind
      (renameSmartFreshBehindGuard π guard))
    (renameSmartLiftCtxᴸ π (EmbeddingPushout.premise po) liftγ) vV
    (rename-target-typing π N⊢)
    (⊢²-rename-center {W = Wᵐ} (EmbeddingPushout.premise po)
      V⊑N
      (rename-⊑ᵂ {W = Wᵐ} (EmbeddingPushout.premise po) p)) p′
  where
  po = embeddingPushout π
    (CTX.SmartFreshBehindGuard.oldCenters guard)
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
    (CTI2.⊑reveal² {p = p} c′⊢ at-absent M⊑N q) p′ =
  CTI2.⊑reveal² (rename-target-⊢↑ π c′⊢)
    (rename-target-reveal-position π c′⊢ generator-absent at-absent)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.⊑conceal² {p = p} c′⊢ at-absent M⊑N q) p′ =
  CTI2.⊑conceal² (rename-target-⊢↓ π c′⊢)
    (rename-target-conceal-position π c′⊢ generator-absent at-absent)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.reveal⊑-neutral² {p = p} c⊢ at-absent M⊑N q) p′ =
  CTI2.reveal⊑-neutral² (rename-source-⊢↑ π c⊢)
    (rename-source-reveal-position π c⊢ generator-absent at-absent)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.reveal⊑-only² {p = p} c⊢ not-absent dynamic disaligned
      represented M⊑N q) p′ =
  CTI2.reveal⊑-only² (rename-source-⊢↑ π c⊢)
    (λ absent → not-absent
      (trans
        (sym (rename-source-reveal-position π c⊢
          (revealGeneratorPosition c⊢) refl)) absent))
    (trans (rename-mark-image π W) dynamic)
    (rename-disaligned π W disaligned)
    (rename-⊑ᵂ {W = W} π represented)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.reveal⊑² {W′ = W′} {p = p} c⊢ not-absent Xᴿ∈
      represented mono rb sc M⊑N q) p′ =
  CTI2.reveal⊑² (rename-source-⊢↑ π c⊢)
    (λ absent → not-absent
      (trans
        (sym (rename-source-reveal-position π c⊢
          (revealGeneratorPosition c⊢) refl)) absent))
    (subst≡ (λ Σ → Σ ∋ _ ⦂ _) (sym (rename-target-store π W)) Xᴿ∈)
    (rename-⊑ᵂ {W = W′} π represented)
    (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameRebaseAt {W = W} {W′ = W′} π rb)
    (renameSameCtx {W = W} {W′ = W′} π sc)
    (⊢²-rename-center {W = W′} π M⊑N
      (rename-⊑ᵂ {W = W′} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.conceal⊑-neutral² {p = p} c⊢ at-absent M⊑N q) p′ =
  CTI2.conceal⊑-neutral² (rename-source-⊢↓ π c⊢)
    (rename-source-conceal-position π c⊢ generator-absent at-absent)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.conceal⊑² {p = p} c⊢ not-absent dynamic disaligned
      represented M⊑N q) p′ =
  CTI2.conceal⊑² (rename-source-⊢↓ π c⊢)
    (λ absent → not-absent
      (trans
        (sym (rename-source-conceal-position π c⊢
          (concealGeneratorPosition c⊢) refl)) absent))
    (trans (rename-mark-image π W) dynamic)
    (rename-disaligned π W disaligned)
    (rename-⊑ᵂ {W = W} π represented)
    (⊢²-rename-center {W = W} π M⊑N
      (rename-⊑ᵂ {W = W} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      c⊢ c′⊢ positions not-absent represented mono rb sc M⊑N q) p′ =
  CTI2.reveal⊑reveal²
    (rename-source-⊢↑ π c⊢) (rename-target-⊢↑ π c′⊢)
    (trans
      (rename-source-reveal-position π c⊢
        (revealGeneratorPosition c⊢) refl)
      (trans positions
        (sym (rename-target-reveal-position π c′⊢
          (revealGeneratorPosition c′⊢) refl))))
    (λ absent → not-absent
      (trans
        (sym (rename-source-reveal-position π c⊢
          (revealGeneratorPosition c⊢) refl)) absent))
    (rename-⊑ᵂ {W = Wᵖ} π represented)
    (renameImpEnvMono {W = W} {W′ = Wᵖ} π mono)
    (renameRebaseAt {W = W} {W′ = Wᵖ} π rb)
    (renameSameCtx {W = W} {W′ = Wᵖ} π sc)
    (⊢²-rename-center {W = Wᵖ} π M⊑N
      (rename-⊑ᵂ {W = Wᵖ} π p)) p′
⊢²-rename-center {W = W} π
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      c⊢ c′⊢ positions not-absent represented mono rb sc M⊑N q) p′ =
  CTI2.conceal⊑conceal²
    (rename-source-⊢↓ π c⊢) (rename-target-⊢↓ π c′⊢)
    (trans
      (rename-source-conceal-position π c⊢
        (concealGeneratorPosition c⊢) refl)
      (trans positions
        (sym (rename-target-conceal-position π c′⊢
          (concealGeneratorPosition c′⊢) refl))))
    (λ absent → not-absent
      (trans
        (sym (rename-source-conceal-position π c⊢
          (concealGeneratorPosition c⊢) refl)) absent))
    (rename-⊑ᵂ {W = Wᵖ} π represented)
    (renameImpEnvMono {W = W} {W′ = Wᵖ} π mono)
    (renameRebaseAt {W = Wᵖ} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = Wᵖ} π sc)
    (⊢²-rename-center {W = Wᵖ} π M⊑N
      (rename-⊑ᵂ {W = Wᵖ} π p)) p′
⊢²-rename-center {W = W} {γ = γ} π (CTI2.blame⊑² M′⊢ p) p′ =
  CTI2.blame⊑² (rename-target-typing π M′⊢) p′
⊢²-rename-center {W = W} π
    (CTI2.⊕⊑⊕² op {p = p} {q = q} L⊑L′ M⊑M′ r) p′ =
  CTI2.⊕⊑⊕² op
    (⊢²-rename-center {W = W} π L⊑L′
      (rename-⊑ᵂ {W = W} π p))
    (⊢²-rename-center {W = W} π M⊑M′
      (rename-⊑ᵂ {W = W} π q)) p′

⊢²-extend-center : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → (p′ : A CTX.⊑ᵂ⟨ renameWorld wk↪ᵗ W ⟩ B)
  → renameWorld wk↪ᵗ W ∣ renameCtx {W = W} wk↪ᵗ γ
      ⊢² M ⊑ N ∶ p′
⊢²-extend-center = ⊢²-rename-center wk↪ᵗ

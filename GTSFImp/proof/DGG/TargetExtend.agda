module proof.DGG.TargetExtend where

-- File Charter:
--   * Transports version-2 cast-term-imprecision derivations across
--     right-only target store extension.
--   * Provides the target-side weakening helpers for indexed conversions,
--     partner predicates, and derivation-level target extension.
--   * Derives relation-indexed insertion provenance when every target entry
--     outside the old-center image has direct `★` representation.
--   * The public theorem specializes to the parked single right bind used by
--     the DGG instantiation cases; internal helpers keep target weakening
--     separate from source-side structure.

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
import Data.Nat as Nat
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (TyStore; store-lift; lookupStore; lookupStore-∋; _∋_⦂_)
open import Imprecision
open import Primitives using
  (Prim; addℕ; and𝔹; constTy; primArgTy; primResultTy;
   constTy-renameᵗ)
import TermCtx as T
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ; wk↪ᵗ;
   renameᵐᶜ)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; renameᵗᵐ)
import Reduction
open import Reduction using (bind; _∷_; [])
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-ext; StoreRename-keep; StoreRename-wk-bind;
   renameᵗᵐ-preserves-Value; renameᵗ-wk-eq; toRename-id-eq;
   toRename-keep-eq; toRename-wk-eq; typing-renameᵗ; rename-openᵗ;
   reveal-renameᵗ; conceal-renameᵗ)
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; rename-⊑; subst-⊑;
   toRenameᵗ-injective)
open import proof.DGG.Parked.ParkedBindImprecisionProof using (right-bind-⊑ᵂ)
open import proof.DGG.CenterRename using
  (_∘↪_; toRenameᵗ-∘; sucMaybe; preimage?; sucMaybe-nothing;
   preimage?-image; EmbeddingPair; pair; embeddingPair; EmbeddingPushout;
   pushout; embeddingPushout; EmbeddingWindow; window-here;
   pushout-window; embeddingPushoutWindow;
   pushout-old-off-premise; renameEnv;
   renameEnv-image; renameEnv-off)
import proof.DGG.CenterRename as CR
import proof.Imprecision as PI
open import proof.DGG.ConversionPivotAlignment using
  (GeneratorPosition; generator-absent; revealGeneratorPosition;
   concealGeneratorPosition; revealGeneratorPosition-store-transport;
   concealGeneratorPosition-store-transport)

open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Optional world-rebase pivots
------------------------------------------------------------------------

mapPivot : ∀ {Δ Δ′}
  → (TyVar Δ → TyVar Δ′)
  → Maybe (TyVar Δ)
  → Maybe (TyVar Δ′)
mapPivot ρ (just X) = just (ρ X)
mapPivot ρ nothing = nothing

record TargetInsertView {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    (ρ : Δᴿ ↪ᵗ Δᴿ′)
    (π : Δ ↪ᵗ Δ′)
    (W : World Δᴸ Δᴿ Δ)
    (ηᴸ′ : Δᴸ ↪ᵗ Δ′) (ηᴿ′ : Δᴿ′ ↪ᵗ Δ′)
    (μ′ : ImpEnv Δ′) (Σᴸ′ : TyStore Δᴸ) (Σᴿ′ : TyStore Δᴿ′) : Set where
  field
    sourceStore-kept : Σᴸ′ ≡ CTX.sourceStoreʷ W

    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → μ′ ⊢ renameᵗ (toRenameᵗ ηᴸ′) A
          ⊑ renameᵗ (toRenameᵗ ηᴿ′)
              (renameᵗ (toRenameᵗ ρ) B)

    targetStore-rename :
      StoreRename (toRenameᵗ ρ) (CTX.targetStoreʷ W)
        Σᴿ′

    source-resolve : ∀ Xᴸ
      → CTX.resolveVar Σᴸ′ Xᴸ
          ≡ CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ

    target-resolve : ∀ Xᴿ
      → CTX.resolveVar Σᴿ′ (toRenameᵗ ρ Xᴿ)
          ≡ renameᵗ (toRenameᵗ ρ)
              (CTX.resolveVar (CTX.targetStoreʷ W) Xᴿ)

    align-insert : ∀ {Xᴸ Xᴿ}
      → CTX.CenterAligned W Xᴸ Xᴿ
      → toRenameᵗ ηᴸ′ Xᴸ ≡ toRenameᵗ ηᴿ′ (toRenameᵗ ρ Xᴿ)

    source-insert : ∀ Xᴸ
      → toRenameᵗ ηᴸ′ Xᴸ
          ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)

    target-insert : ∀ Xᴿ
      → toRenameᵗ ηᴿ′ (toRenameᵗ ρ Xᴿ)
          ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)

    impEnv-insert : ∀ Z
      → μ′ (toRenameᵗ π Z) ≡ CTX.impEnvʷ W Z

    impEnv-off-insert : ∀ {Z′}
      → preimage? π Z′ ≡ nothing
      → μ′ Z′ ≡ X⊑★

    target-center-reflect : ∀ {Y′ Z}
      → toRenameᵗ ηᴿ′ Y′ ≡ toRenameᵗ π Z
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y ×
          toRenameᵗ (CTX.ηᴿʷ W) Y ≡ Z

    target-source-reflect : ∀ {Xᴸ Y′}
      → toRenameᵗ ηᴸ′ Xᴸ ≡ toRenameᵗ ηᴿ′ Y′
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned W Xᴸ Y

    targetLookup-insert : ∀ Xᴿ
      → lookupStore Σᴿ′ (toRenameᵗ ρ Xᴿ)
        ≡ renameᵗ (toRenameᵗ ρ)
            (lookupStore (CTX.targetStoreʷ W) Xᴿ)

    targetLookup-off : ∀ Xᴿ′
      → preimage? π (toRenameᵗ ηᴿ′ Xᴿ′) ≡ nothing
      → (lookupStore Σᴿ′ Xᴿ′ ≡ ★)
        ⊎ (Σ[ Yᴿ′ ∈ TyVar Δᴿ′ ]
            (lookupStore Σᴿ′ Xᴿ′ ≡ ＇ Yᴿ′)
          × (∀ Xᴸ → toRenameᵗ ηᴸ′ Xᴸ
              ≡ toRenameᵗ ηᴿ′ Yᴿ′ → ⊥))

open TargetInsertView public
  renaming
    ( sourceStore-kept to view-sourceStore-kept
    ; transport⊑ᵂ to view-transport⊑ᵂ
    ; targetStore-rename to view-targetStore-rename
    ; source-resolve to view-source-resolve
    ; target-resolve to view-target-resolve
    ; align-insert to view-align-insert
    ; source-insert to view-source-insert
    ; target-insert to view-target-insert
    ; impEnv-insert to view-impEnv-insert
    ; impEnv-off-insert to view-impEnv-off-insert
    ; target-center-reflect to view-target-center-reflect
    ; target-source-reflect to view-target-source-reflect
    ; targetLookup-insert to view-targetLookup-insert
    ; targetLookup-off to view-targetLookup-off
    )

record TargetInsert {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    (ρ : Δᴿ ↪ᵗ Δᴿ′)
    (π : Δ ↪ᵗ Δ′)
    (W : World Δᴸ Δᴿ Δ)
    (W′ : World Δᴸ Δᴿ′ Δ′) : Set where
  constructor target-insert-view
  field
    targetInsertView : TargetInsertView ρ π W
      (CTX.ηᴸʷ W′) (CTX.ηᴿʷ W′) (CTX.impEnvʷ W′)
      (CTX.sourceStoreʷ W′) (CTX.targetStoreʷ W′)

  open TargetInsertView targetInsertView public

open TargetInsert public

targetInsertView-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {ηᴸ′ : Δᴸ ↪ᵗ Δ′} {ηᴿ′ : Δᴿ′ ↪ᵗ Δ′}
    {μ′ : ImpEnv Δ′} {Σᴸ′ : TyStore Δᴸ} {Σᴿ′ : TyStore Δᴿ′}
  → TargetInsertView ρ π W ηᴸ′ ηᴿ′ μ′ Σᴸ′ Σᴿ′
  → CTX.WorldInvariants (CTX.ηᴸʷ W) (CTX.ηᴿʷ W)
      (CTX.impEnvʷ W) (CTX.sourceStoreʷ W) (CTX.targetStoreʷ W)
  → CTX.WorldInvariants ηᴸ′ ηᴿ′ μ′ Σᴸ′ Σᴿ′
targetInsertView-invariants
    {ρ = ρ} {π = π} {W = W} {ηᴸ′ = ηᴸ′} {ηᴿ′ = ηᴿ′}
    {μ′ = μ′} {Σᴸ′ = Σᴸ′} {Σᴿ′ = Σᴿ′} view inv =
  CTX.world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → μ′ (toRenameᵗ ηᴸ′ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ′ ∈ TyVar _ ]
        toRenameᵗ ηᴿ′ Xᴿ′ ≡ toRenameᵗ ηᴸ′ Xᴸ
  precise Xᴸ mark with CTX.preciseMarksAligned inv Xᴸ old-mark
    where
    old-mark :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑X
    old-mark = trans
      (sym (view-impEnv-insert view (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)))
      (subst≡ (λ Z → μ′ Z ≡ X⊑X) (view-source-insert view Xᴸ) mark)
  precise Xᴸ mark | Xᴿ , aligned =
    toRenameᵗ ρ Xᴿ , sym (view-align-insert view (sym aligned))

  reps : ∀ {Xᴸ Xᴿ′}
    → toRenameᵗ ηᴸ′ Xᴸ ≡ toRenameᵗ ηᴿ′ Xᴿ′
    → μ′ ⊢
        renameᵗ (toRenameᵗ ηᴸ′) (lookupStore Σᴸ′ Xᴸ)
        ⊑ renameᵗ (toRenameᵗ ηᴿ′) (lookupStore Σᴿ′ Xᴿ′)
  reps {Xᴸ} {Xᴿ′} aligned
      with view-target-source-reflect view aligned
  reps {Xᴸ} {Xᴿ′} aligned | Xᴿ , refl , old-aligned =
    CTX.imprecision-cong source-eq target-eq
      (view-transport⊑ᵂ view
        (CTX.representationsImprecise inv old-aligned))
    where
    source-eq :
      renameᵗ (toRenameᵗ ηᴸ′)
          (lookupStore (CTX.sourceStoreʷ W) Xᴸ)
        ≡ renameᵗ (toRenameᵗ ηᴸ′) (lookupStore Σᴸ′ Xᴸ)
    source-eq = cong (renameᵗ (toRenameᵗ ηᴸ′))
      (sym (cong (λ Σ → lookupStore Σ Xᴸ)
        (view-sourceStore-kept view)))

    target-eq :
      renameᵗ (toRenameᵗ ηᴿ′)
          (renameᵗ (toRenameᵗ ρ)
            (lookupStore (CTX.targetStoreʷ W) Xᴿ))
        ≡ renameᵗ (toRenameᵗ ηᴿ′)
            (lookupStore Σᴿ′ (toRenameᵗ ρ Xᴿ))
    target-eq = cong (renameᵗ (toRenameᵗ ηᴿ′))
      (sym (view-targetLookup-insert view Xᴿ))

  unmatched : ∀ Xᴿ′
    → (∀ Xᴸ → toRenameᵗ ηᴸ′ Xᴸ ≢ toRenameᵗ ηᴿ′ Xᴿ′)
    → lookupStore Σᴿ′ Xᴿ′ ≡ ★
      ⊎ Σ[ Yᴿ′ ∈ TyVar _ ]
          (lookupStore Σᴿ′ Xᴿ′ ≡ ＇ Yᴿ′)
        × (∀ Xᴸ → toRenameᵗ ηᴸ′ Xᴸ ≢ toRenameᵗ ηᴿ′ Yᴿ′)
  unmatched Xᴿ′ no-source
      with preimage? π (toRenameᵗ ηᴿ′ Xᴿ′) in pre
  unmatched Xᴿ′ no-source | nothing =
    view-targetLookup-off view Xᴿ′ pre
  unmatched Xᴿ′ no-source | just Z
      with view-target-center-reflect view (CR.preimage?-sound π pre)
  unmatched Xᴿ′ no-source | just Z
      | Xᴿ , xᴿ′-eq , old-center =
    subst≡
      (λ Y →
        lookupStore Σᴿ′ Y ≡ ★
        ⊎ Σ[ Yᴿ′ ∈ TyVar _ ]
            (lookupStore Σᴿ′ Y ≡ ＇ Yᴿ′)
          × (∀ Xᴸ → toRenameᵗ ηᴸ′ Xᴸ ≢ toRenameᵗ ηᴿ′ Yᴿ′))
      (sym xᴿ′-eq) old-result
    where
    old-no-source : ∀ Xᴸ → CTX.CenterAligned W Xᴸ Xᴿ → ⊥
    old-no-source Xᴸ aligned = no-source Xᴸ
      (subst≡ (λ Y → toRenameᵗ ηᴸ′ Xᴸ ≡ toRenameᵗ ηᴿ′ Y)
        (sym xᴿ′-eq) (view-align-insert view aligned))

    old-result :
      lookupStore Σᴿ′ (toRenameᵗ ρ Xᴿ) ≡ ★
      ⊎ Σ[ Yᴿ′ ∈ TyVar _ ]
          (lookupStore Σᴿ′ (toRenameᵗ ρ Xᴿ) ≡ ＇ Yᴿ′)
        × (∀ Xᴸ → toRenameᵗ ηᴸ′ Xᴸ ≢ toRenameᵗ ηᴿ′ Yᴿ′)
    old-result with CTX.unmatchedTargetsDynamic inv Xᴿ old-no-source
    old-result | inj₁ dynamic =
      inj₁ (trans (view-targetLookup-insert view Xᴿ)
        (cong (renameᵗ (toRenameᵗ ρ)) dynamic))
    old-result | inj₂ (Yᴿ , entry , head-no-source) =
      inj₂
        ( toRenameᵗ ρ Yᴿ
        , trans (view-targetLookup-insert view Xᴿ)
            (cong (renameᵗ (toRenameᵗ ρ)) entry)
        , inserted-head-no-source )
      where
      inserted-head-no-source : ∀ Xᴸ
        → toRenameᵗ ηᴸ′ Xᴸ ≡ toRenameᵗ ηᴿ′ (toRenameᵗ ρ Yᴿ)
        → ⊥
      inserted-head-no-source Xᴸ aligned
          with view-target-source-reflect view aligned
      inserted-head-no-source Xᴸ aligned
          | Yᴿ′ , mapped-eq , old-aligned =
        head-no-source Xᴸ
          (subst≡ (CTX.CenterAligned W Xᴸ)
            (sym (toRenameᵗ-injective ρ mapped-eq)) old-aligned)

  unoccupied : ∀ Xᴸ
    → μ′ (toRenameᵗ ηᴸ′ Xᴸ) ≡ X⊑★
    → lookupStore Σᴸ′ Xᴸ ≡ ★
    → ∀ Xᴿ′
    → toRenameᵗ ηᴿ′ Xᴿ′ ≢ toRenameᵗ ηᴸ′ Xᴸ
  unoccupied Xᴸ mark entry Xᴿ′ aligned
      with view-target-source-reflect view (sym aligned)
  unoccupied Xᴸ mark entry Xᴿ′ aligned
      | Xᴿ , Xᴿ′-eq , old-aligned =
    CTX.dynamicStarSourcesUnoccupied inv Xᴸ old-mark old-entry Xᴿ
      (sym old-aligned)
    where
    old-mark :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    old-mark = trans
      (sym (view-impEnv-insert view
        (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)))
      (trans (cong μ′ (sym (view-source-insert view Xᴸ))) mark)

    old-entry : lookupStore (CTX.sourceStoreʷ W) Xᴸ ≡ ★
    old-entry = trans
      (sym (cong (λ Σ → lookupStore Σ Xᴸ)
        (view-sourceStore-kept view)))
      entry


record TargetWindowInsert {Δᴸ Δᴿ Δ Δ′}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ (Nat.suc Δᴿ) Δ′}
    (ins : TargetInsert wk↪ᵗ π W W′)
    (κ : Nat.suc Δ ↪ᵗ Δ′) : Set where
  field
    windowEmbedding : EmbeddingWindow π κ
    window-zero :
      toRenameᵗ (CTX.ηᴿʷ W′) Fin.zero ≡ toRenameᵗ κ Fin.zero
    window-old : ∀ Z
      → toRenameᵗ π Z ≡ toRenameᵗ κ (Fin.suc Z)

open TargetWindowInsert public


target-source-reflect-from-center : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned W′ Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned W Xᴸ Y
target-source-reflect-from-center {π = π} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins aligned
    with target-center-reflect ins target-image
  where
  target-image : toRenameᵗ (CTX.ηᴿʷ W′) Y′
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  target-image = trans (sym aligned) (source-insert ins Xᴸ)
target-source-reflect-from-center ins aligned
    | Y , y′-eq , target-eq =
  Y , y′-eq , sym target-eq

mapCtxᵀ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W′
  → CtxImp W
  → CtxImp W′
mapCtxᵀ ins [] = []
mapCtxᵀ {ρ = ρ} ins (CTX.ctx-imp A B p ∷ γ) =
  CTX.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p) ∷
    mapCtxᵀ ins γ

mapCtxᵀ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ π W W′)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → mapCtxᵀ ins γ CTX.∋ʷ x ⦂
      CTX.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p)
mapCtxᵀ-∋ ins CTX.Zʷ = CTX.Zʷ
mapCtxᵀ-∋ ins (CTX.Sʷ x∈) = CTX.Sʷ (mapCtxᵀ-∋ ins x∈)

mapCtxᵀ-same : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.SameCtx γ γᵖ
  → CTX.SameCtx (mapCtxᵀ ins γ) (mapCtxᵀ insᵖ γᵖ)
mapCtxᵀ-same ins insᵖ CTX.same-[] = CTX.same-[]
mapCtxᵀ-same ins insᵖ (CTX.same-∷ sc) =
  CTX.same-∷ (mapCtxᵀ-same ins insᵖ sc)

mapCtxᵀ-tgt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (γ : CtxImp W)
  → CTX.tgtCtxʷ (mapCtxᵀ ins γ)
      ≡ T.renameCtx (toRenameᵗ ρ) (CTX.tgtCtxʷ γ)
mapCtxᵀ-tgt ins [] = refl
mapCtxᵀ-tgt ins (CTX.ctx-imp A B p ∷ γ) =
  cong (renameᵗ _ B ∷_) (mapCtxᵀ-tgt ins γ)

source-embed-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (A : Ty Δᴸ)
  → CTX.embedᴸ W′ A
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A)
source-embed-insert {π = π} {W = W} ins A =
  trans (renameᵗ-cong A (source-insert ins))
    (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ W)) (toRenameᵗ π) A))

target-embed-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W B)
target-embed-insert {ρ = ρ} {π = π} {W = W} {W′ = W′} ins B =
  trans (renameᵗ-comp (toRenameᵗ ρ) (toRenameᵗ (CTX.ηᴿʷ W′)) B)
    (trans (renameᵗ-cong B (target-insert ins))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ W))
        (toRenameᵗ π) B)))

transport⊑ᵂ-from-geometry : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (∀ C → CTX.embedᴸ W′ C
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ W C))
  → (∀ C → CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) C)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W C))
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★
      → CTX.impEnvʷ W′ (toRenameᵗ π Z) ≡ X⊑★)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B
transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} source-eq target-eq env-star p =
  subst≡
    (λ L → CTX.impEnvʷ W′ ⊢
      L ⊑ CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) B))
    (sym (source-eq A))
    (subst≡
      (λ R → CTX.impEnvʷ W′ ⊢
        renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A) ⊑ R)
      (sym (target-eq B))
      (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
        env-star p))

transport⊑ᵂ-geometry : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B
transport⊑ᵂ-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} ins p =
  transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} (source-embed-insert ins)
    (target-embed-insert ins)
    (λ Z eq → trans (impEnv-insert ins Z) eq)
    p

rename-as-subst : ∀ {Δ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
rename-as-subst ρ (＇ X) = refl
rename-as-subst ρ (‵ ι) = refl
rename-as-subst ρ ★ = refl
rename-as-subst ρ (A ⇒ B)
    rewrite rename-as-subst ρ A | rename-as-subst ρ B =
  refl
rename-as-subst ρ (`∀ A) =
  cong `∀
    (trans (substᵗ-cong A exts-eq)
      (rename-as-subst (extᵗ ρ) A))
  where
  exts-eq : ∀ X
    → extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
  exts-eq Fin.zero = refl
  exts-eq (Fin.suc X) = refl

transport⊑ᵂ-by-subst : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (σ : Δ ⇒ˢ Δ′)
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★
      → CTX.impEnvʷ W′ ⊢ σ Z ⊑ ★)
  → (∀ C → substᵗ σ (CTX.embedᴸ W C) ≡ CTX.embedᴸ W′ C)
  → (∀ C → substᵗ σ (CTX.embedᴿ W C) ≡ CTX.embedᴿ W′ C)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ B
transport⊑ᵂ-by-subst {W = W} {W′ = W′} {A = A} {B = B}
    σ star-map source-eq target-eq p =
  subst≡
    (λ L → CTX.impEnvʷ W′ ⊢ L ⊑ CTX.embedᴿ W′ B)
    (source-eq A)
    (subst≡
      (λ R → CTX.impEnvʷ W′ ⊢ substᵗ σ (CTX.embedᴸ W A) ⊑ R)
      (target-eq B)
      (subst-⊑ star-map p))

storeRep-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp W′ Xᴸ (toRenameᵗ ρ Xᴿ)
storeRep-insert {ρ = ρ} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins
    (CTX.store-rep-imp represented) =
  CTX.store-rep-imp
    (subst≡
      (λ A → A ⊑ᵂ⟨ W′ ⟩
        CTX.resolveVar (CTX.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ))
      (sym (source-resolve ins Xᴸ))
      (subst≡
        (λ B → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
          ⊑ᵂ⟨ W′ ⟩ B)
        (sym (target-resolve ins Xᴿ))
        (transport⊑ᵂ ins represented)))

renameᵗ-keep-shift : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) A)
renameᵗ-keep-shift ρ A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
    (renameᵗ-shift (toRenameᵗ ρ) A)

ctx-imp-target-eq : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → B ≡ B′
  → CTX.ctx-imp {W = W} A B p ≡ CTX.ctx-imp {W = W} A B′ q
ctx-imp-target-eq {W = W} {A = A} {B = B} {p = p} {q = q} refl =
  cong (λ r → CTX.ctx-imp {W = W} A B r) (PI.⊑-unique p q)

just≢nothing : ∀ {A : Set} {x : A} → just x ≢ nothing
just≢nothing ()

zero≢suc : ∀ {Δ} {X : TyVar Δ}
  → Fin.zero ≢ Fin.suc X
zero≢suc ()

suc≢zero : ∀ {Δ} {X : TyVar Δ}
  → Fin.suc X ≢ Fin.zero
suc≢zero ()

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

preimage-id↪ : ∀ {Δ} (Z : TyVar Δ)
  → preimage? id↪ᵗ Z ≡ just Z
preimage-id↪ {Nat.zero} ()
preimage-id↪ {Nat.suc Δ} Fin.zero = refl
preimage-id↪ {Nat.suc Δ} (Fin.suc Z)
    rewrite preimage-id↪ Z =
  refl

embeddingPair-disjoint : ∀ Δ₁ Δ₂
    {Z₁ : TyVar Δ₁} {Z₂ : TyVar Δ₂}
  → toRenameᵗ (EmbeddingPair.right (embeddingPair Δ₁ Δ₂)) Z₂
    ≢ toRenameᵗ (EmbeddingPair.left (embeddingPair Δ₁ Δ₂)) Z₁
embeddingPair-disjoint Nat.zero Δ₂ {Z₁ = ()}
embeddingPair-disjoint (Nat.suc Δ₁) Δ₂ {Z₁ = Fin.zero} eq =
  suc≢zero eq
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
    {Zᵐ = Fin.zero} pre eq =
  suc≢zero eq
pushout-off-image-disjoint empty (skip old)
    {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint empty old pre (fin-suc-injective eq)
pushout-off-image-disjoint (skip π) old
    {Z′ = Fin.zero} pre eq =
  zero≢suc eq
pushout-off-image-disjoint (skip π) old
    {Z′ = Fin.suc Z′} pre eq =
  pushout-off-image-disjoint π old pre (fin-suc-injective eq)
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.zero} pre eq =
  just≢nothing pre
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.zero} pre eq =
  suc≢zero eq
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint (keep π) old pre
    (fin-suc-injective eq)
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.zero} pre eq =
  just≢nothing pre
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.zero} pre eq =
  suc≢zero eq
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint π old
    (sucMaybe-nothing (preimage? π Z′) pre)
    (fin-suc-injective eq)

target-insert-off-image-center : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Y′ : TyVar Δᴿ′}
  → (ins : TargetInsert ρ π W W′)
  → preimage? ρ Y′ ≡ nothing
  → preimage? π (toRenameᵗ (CTX.ηᴿʷ W′) Y′) ≡ nothing
target-insert-off-image-center {ρ = ρ} {π = π} {W′ = W′} {Y′ = Y′}
    ins off
    with preimage? π (toRenameᵗ (CTX.ηᴿʷ W′) Y′) in pre
target-insert-off-image-center {ρ = ρ} {π = π} {Y′ = Y′} ins off
    | nothing = refl
target-insert-off-image-center {ρ = ρ} {π = π} {Y′ = Y′} ins off
    | just Z with target-center-reflect ins (preimage?-sound π pre)
target-insert-off-image-center {ρ = ρ} {π = π} {Y′ = Y′} ins off
    | just Z | Y , y′-eq , target-eq =
  ⊥-elim (just≢nothing just-eq)
  where
  just-eq : just Y ≡ nothing
  just-eq =
    trans (sym (preimage?-image ρ Y))
      (trans (sym (cong (preimage? ρ) y′-eq)) off)

liftBoth-source-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldBoth v W′)) X
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldBoth v W)) X)
liftBoth-source-insert ins Fin.zero = refl
liftBoth-source-insert ins (Fin.suc X) =
  cong Fin.suc (source-insert ins X)

liftBoth-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) X)
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W)) X)
liftBoth-target-insert ins Fin.zero = refl
liftBoth-target-insert ins (Fin.suc X) =
  cong Fin.suc (target-insert ins X)

liftBoth-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Y′ : TyVar (Nat.suc Δᴿ′)}
    {Z : TyVar (Nat.suc Δ)}
  → (ins : TargetInsert ρ π W W′)
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′)) Y′
      ≡ toRenameᵗ (keep π) Z
  → Σ[ Y ∈ TyVar (Nat.suc Δᴿ) ]
      Y′ ≡ toRenameᵗ (keep ρ) Y ×
      toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W)) Y ≡ Z
liftBoth-target-center-reflect {Y′ = Fin.zero} {Z = Fin.zero}
    ins eq =
  Fin.zero , refl , refl
liftBoth-target-center-reflect {Y′ = Fin.zero} {Z = Fin.suc Z}
    ins eq =
  ⊥-elim (zero≢suc eq)
liftBoth-target-center-reflect {Y′ = Fin.suc Y′} {Z = Fin.zero}
    ins eq =
  ⊥-elim (suc≢zero eq)
liftBoth-target-center-reflect {Y′ = Fin.suc Y′} {Z = Fin.suc Z}
    ins eq with target-center-reflect ins (fin-suc-injective eq)
liftBoth-target-center-reflect {Y′ = Fin.suc Y′} {Z = Fin.suc Z}
    ins eq | Y , y′-eq , target-eq =
  Fin.suc Y , cong Fin.suc y′-eq , cong Fin.suc target-eq

liftBoth-impEnv-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Z
  → CTX.impEnvʷ (CTX.liftWorldBoth v W′) (toRenameᵗ (keep π) Z)
      ≡ CTX.impEnvʷ (CTX.liftWorldBoth v W) Z
liftBoth-impEnv-insert ins Fin.zero = refl
liftBoth-impEnv-insert ins (Fin.suc Z) =
  impEnv-insert ins Z

liftBoth-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Z′ : TyVar (Nat.suc Δ′)}
  → (ins : TargetInsert ρ π W W′)
  → preimage? (keep π) Z′ ≡ nothing
  → CTX.impEnvʷ (CTX.liftWorldBoth v W′) Z′ ≡ X⊑★
liftBoth-impEnv-off-insert {Z′ = Fin.zero} ins ()
liftBoth-impEnv-off-insert {π = π} {Z′ = Fin.suc Z′} ins eq =
  impEnv-off-insert ins (sucMaybe-nothing (preimage? π Z′) eq)

liftBoth-source-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldBoth v W′)) X
      ≡ CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldBoth v W)) X
liftBoth-source-resolve ins Fin.zero = refl
liftBoth-source-resolve ins (Fin.suc X) =
  cong ⇑ᵗ (source-resolve ins X)

liftBoth-target-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTX.resolveVar (CTX.targetStoreʷ (CTX.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) X)
      ≡ renameᵗ (toRenameᵗ (keep ρ))
          (CTX.resolveVar
            (CTX.targetStoreʷ (CTX.liftWorldBoth v W)) X)
liftBoth-target-resolve ins Fin.zero = refl
liftBoth-target-resolve {ρ = ρ} {W = W} ins (Fin.suc X) =
  trans (cong ⇑ᵗ (target-resolve ins X))
    (sym (renameᵗ-keep-shift ρ
      (CTX.resolveVar (CTX.targetStoreʷ W) X)))

liftBoth-align-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Xᴿ : TyVar (Nat.suc Δᴿ)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned (CTX.liftWorldBoth v W) Xᴸ Xᴿ
  → CTX.CenterAligned (CTX.liftWorldBoth v W′) Xᴸ
      (toRenameᵗ (keep ρ) Xᴿ)
liftBoth-align-insert {Xᴸ = Fin.zero} {Xᴿ = Fin.zero} ins aligned =
  refl
liftBoth-align-insert {Xᴸ = Fin.zero} {Xᴿ = Fin.suc Xᴿ} ins ()
liftBoth-align-insert {Xᴸ = Fin.suc Xᴸ} {Xᴿ = Fin.zero} ins ()
liftBoth-align-insert {Xᴸ = Fin.suc Xᴸ} {Xᴿ = Fin.suc Xᴿ} ins aligned =
  cong Fin.suc (align-insert ins (fin-suc-injective aligned))

liftBoth-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Y′ : TyVar (Nat.suc Δᴿ′)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned (CTX.liftWorldBoth v W′) Xᴸ Y′
  → Σ[ Y ∈ TyVar (Nat.suc Δᴿ) ]
      Y′ ≡ toRenameᵗ (keep ρ) Y ×
      CTX.CenterAligned (CTX.liftWorldBoth v W) Xᴸ Y
liftBoth-target-source-reflect {Xᴸ = Fin.zero} {Y′ = Fin.zero}
    ins aligned =
  Fin.zero , refl , refl
liftBoth-target-source-reflect {Xᴸ = Fin.zero} {Y′ = Fin.suc Y′}
    ins ()
liftBoth-target-source-reflect {Xᴸ = Fin.suc Xᴸ} {Y′ = Fin.zero}
    ins ()
liftBoth-target-source-reflect {Xᴸ = Fin.suc Xᴸ} {Y′ = Fin.suc Y′}
    ins
    aligned with target-source-reflect ins (fin-suc-injective aligned)
liftBoth-target-source-reflect {Xᴸ = Fin.suc Xᴸ} {Y′ = Fin.suc Y′}
    ins aligned | Y , y′-eq , aligned₀ =
  Fin.suc Y , cong Fin.suc y′-eq , cong Fin.suc aligned₀

liftBoth-targetLookup-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Xᴿ
  → lookupStore (CTX.targetStoreʷ (CTX.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) Xᴿ)
    ≡ renameᵗ (toRenameᵗ (keep ρ))
        (lookupStore
          (CTX.targetStoreʷ (CTX.liftWorldBoth v W)) Xᴿ)
liftBoth-targetLookup-insert ins Fin.zero = refl
liftBoth-targetLookup-insert {ρ = ρ} {W = W} ins (Fin.suc Xᴿ) =
  trans (cong ⇑ᵗ (targetLookup-insert ins Xᴿ))
    (sym (renameᵗ-keep-shift ρ
      (lookupStore (CTX.targetStoreʷ W) Xᴿ)))

liftBoth-targetLookup-off : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Xᴿ′
  → preimage? (keep π)
      (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′)) Xᴿ′)
      ≡ nothing
  → (lookupStore
        (CTX.targetStoreʷ (CTX.liftWorldBoth v W′)) Xᴿ′ ≡ ★)
    ⊎ ( Σ[ Yᴿ′ ∈ TyVar (Nat.suc Δᴿ′) ]
        (lookupStore
          (CTX.targetStoreʷ (CTX.liftWorldBoth v W′)) Xᴿ′
          ≡ ＇ Yᴿ′)
      × (∀ Xᴸ
          → CTX.CenterAligned (CTX.liftWorldBoth v W′) Xᴸ Yᴿ′
          → ⊥))
liftBoth-targetLookup-off ins Fin.zero ()
liftBoth-targetLookup-off {π = π} {W′ = W′} ins (Fin.suc Xᴿ′) off
    with targetLookup-off ins Xᴿ′
      (sucMaybe-nothing (preimage? π
        (toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ′)) off)
liftBoth-targetLookup-off ins (Fin.suc Xᴿ′) off
    | inj₁ dynamic =
  inj₁ (cong ⇑ᵗ dynamic)
liftBoth-targetLookup-off {W′ = W′} {v = v}
    ins (Fin.suc Xᴿ′) off
    | inj₂ (Yᴿ′ , entry , head-no-source) =
  inj₂ (Fin.suc Yᴿ′ , cong ⇑ᵗ entry , no-lifted-source)
  where
  no-lifted-source : ∀ Xᴸ
    → CTX.CenterAligned (CTX.liftWorldBoth v W′)
        Xᴸ (Fin.suc Yᴿ′)
    → ⊥
  no-lifted-source Fin.zero ()
  no-lifted-source (Fin.suc Xᴸ) aligned =
    head-no-source Xᴸ (fin-suc-injective aligned)

liftBothTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → TargetInsert ρ π W W′
  → TargetInsert (keep ρ) (keep π)
      (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v W′)
liftBothTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′} {v = v} ins =
  target-insert-view record
    { sourceStore-kept = cong store-lift (sourceStore-kept ins)
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = keep ρ} {π = keep π}
          {W = CTX.liftWorldBoth v W}
          {W′ = CTX.liftWorldBoth v W′}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (liftBoth-source-insert {v = v} ins))
            (sym (renameᵗ-comp
              (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldBoth v W)))
              (toRenameᵗ (keep π)) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ (keep ρ))
              (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′))) C)
            (trans
              (renameᵗ-cong C (liftBoth-target-insert {v = v} ins))
              (sym (renameᵗ-comp
                (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W)))
                (toRenameᵗ (keep π)) C))))
          (λ Z eq → trans (liftBoth-impEnv-insert {v = v} ins Z) eq)
          p
    ; targetStore-rename = StoreRename-keep (targetStore-rename ins)
    ; source-resolve = liftBoth-source-resolve {v = v} ins
    ; target-resolve = liftBoth-target-resolve {v = v} ins
    ; align-insert = liftBoth-align-insert {v = v} ins
    ; source-insert = liftBoth-source-insert {v = v} ins
    ; target-insert = liftBoth-target-insert {v = v} ins
    ; impEnv-insert = liftBoth-impEnv-insert {v = v} ins
    ; impEnv-off-insert =
        λ {Z′} eq →
          liftBoth-impEnv-off-insert {v = v} {Z′ = Z′} ins eq
    ; target-center-reflect =
        liftBoth-target-center-reflect {v = v} ins
    ; target-source-reflect = liftBoth-target-source-reflect {v = v} ins
    ; targetLookup-insert = liftBoth-targetLookup-insert {v = v} ins
    ; targetLookup-off = liftBoth-targetLookup-off {v = v} ins
    }

liftLeft-source-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldLeft W′)) X
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldLeft W)) X)
liftLeft-source-insert ins Fin.zero = refl
liftLeft-source-insert ins (Fin.suc X) =
  cong Fin.suc (source-insert ins X)

liftLeft-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W′))
      (toRenameᵗ ρ X)
      ≡ toRenameᵗ (keep π)
      (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W)) X)
liftLeft-target-insert ins X = cong Fin.suc (target-insert ins X)

liftLeft-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Y′ : TyVar Δᴿ′} {Z : TyVar (Nat.suc Δ)}
  → (ins : TargetInsert ρ π W W′)
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W′)) Y′
      ≡ toRenameᵗ (keep π) Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W)) Y ≡ Z
liftLeft-target-center-reflect {Z = Fin.zero} ins eq =
  ⊥-elim (suc≢zero eq)
liftLeft-target-center-reflect {Z = Fin.suc Z} ins eq
    with target-center-reflect ins (fin-suc-injective eq)
liftLeft-target-center-reflect {Z = Fin.suc Z} ins eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , cong Fin.suc target-eq

liftLeft-impEnv-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Z
  → CTX.impEnvʷ (CTX.liftWorldLeft W′) (toRenameᵗ (keep π) Z)
      ≡ CTX.impEnvʷ (CTX.liftWorldLeft W) Z
liftLeft-impEnv-insert ins Fin.zero = refl
liftLeft-impEnv-insert ins (Fin.suc Z) =
  impEnv-insert ins Z

liftLeft-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Z′ : TyVar (Nat.suc Δ′)}
  → (ins : TargetInsert ρ π W W′)
  → preimage? (keep π) Z′ ≡ nothing
  → CTX.impEnvʷ (CTX.liftWorldLeft W′) Z′ ≡ X⊑★
liftLeft-impEnv-off-insert {Z′ = Fin.zero} ins ()
liftLeft-impEnv-off-insert {π = π} {Z′ = Fin.suc Z′} ins eq =
  impEnv-off-insert ins (sucMaybe-nothing (preimage? π Z′) eq)

liftLeft-source-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldLeft W′)) X
      ≡ CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldLeft W)) X
liftLeft-source-resolve ins Fin.zero = refl
liftLeft-source-resolve ins (Fin.suc X) =
  cong ⇑ᵗ (source-resolve ins X)

liftLeft-align-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned (CTX.liftWorldLeft W) Xᴸ Xᴿ
  → CTX.CenterAligned (CTX.liftWorldLeft W′) Xᴸ
      (toRenameᵗ ρ Xᴿ)
liftLeft-align-insert {Xᴸ = Fin.zero} ins ()
liftLeft-align-insert {Xᴸ = Fin.suc Xᴸ} ins aligned =
  cong Fin.suc (align-insert ins (fin-suc-injective aligned))

liftLeft-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Y′ : TyVar Δᴿ′}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned (CTX.liftWorldLeft W′) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      CTX.CenterAligned (CTX.liftWorldLeft W) Xᴸ Y
liftLeft-target-source-reflect {Xᴸ = Fin.zero} ins ()
liftLeft-target-source-reflect {Xᴸ = Fin.suc Xᴸ} ins aligned
    with target-source-reflect ins (fin-suc-injective aligned)
liftLeft-target-source-reflect {Xᴸ = Fin.suc Xᴸ} ins aligned
    | Y , y′-eq , aligned₀ =
  Y , y′-eq , cong Fin.suc aligned₀

liftLeft-targetLookup-off : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Xᴿ′
  → preimage? (keep π)
      (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W′)) Xᴿ′)
      ≡ nothing
  → (lookupStore (CTX.targetStoreʷ (CTX.liftWorldLeft W′)) Xᴿ′
        ≡ ★)
    ⊎ ( Σ[ Yᴿ′ ∈ TyVar Δᴿ′ ]
        (lookupStore (CTX.targetStoreʷ (CTX.liftWorldLeft W′)) Xᴿ′
          ≡ ＇ Yᴿ′)
      × (∀ Xᴸ
          → CTX.CenterAligned (CTX.liftWorldLeft W′) Xᴸ Yᴿ′
          → ⊥))
liftLeft-targetLookup-off {π = π} {W′ = W′} ins Xᴿ′ off
    with targetLookup-off ins Xᴿ′
      (sucMaybe-nothing (preimage? π
        (toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ′)) off)
liftLeft-targetLookup-off ins Xᴿ′ off | inj₁ dynamic = inj₁ dynamic
liftLeft-targetLookup-off {W′ = W′} ins Xᴿ′ off
    | inj₂ (Yᴿ′ , entry , head-no-source) =
  inj₂ (Yᴿ′ , entry , no-lifted-source)
  where
  no-lifted-source : ∀ Xᴸ
    → CTX.CenterAligned (CTX.liftWorldLeft W′) Xᴸ Yᴿ′
    → ⊥
  no-lifted-source Fin.zero ()
  no-lifted-source (Fin.suc Xᴸ) aligned =
    head-no-source Xᴸ (fin-suc-injective aligned)

liftLeftTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → TargetInsert ρ π W W′
  → TargetInsert ρ (keep π)
      (CTX.liftWorldLeft W) (CTX.liftWorldLeft W′)
liftLeftTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′} {v = v} ins =
  target-insert-view record
    { sourceStore-kept = cong store-lift (sourceStore-kept ins)
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = ρ} {π = keep π}
          {W = CTX.liftWorldLeft W}
          {W′ = CTX.liftWorldLeft W′}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (liftLeft-source-insert {v = v} ins))
            (sym (renameᵗ-comp
              (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldLeft W)))
              (toRenameᵗ (keep π)) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ ρ)
              (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W′))) C)
            (trans
              (renameᵗ-cong C (liftLeft-target-insert {v = v} ins))
              (sym (renameᵗ-comp
                (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft W)))
                (toRenameᵗ (keep π)) C))))
          (λ Z eq → trans (liftLeft-impEnv-insert {v = v} ins Z) eq)
          p
    ; targetStore-rename = targetStore-rename ins
    ; source-resolve = liftLeft-source-resolve {v = v} ins
    ; target-resolve = target-resolve ins
    ; align-insert = liftLeft-align-insert {v = v} ins
    ; source-insert = liftLeft-source-insert {v = v} ins
    ; target-insert = liftLeft-target-insert {v = v} ins
    ; impEnv-insert = liftLeft-impEnv-insert {v = v} ins
    ; impEnv-off-insert =
        λ {Z′} eq →
          liftLeft-impEnv-off-insert {v = v} {Z′ = Z′} ins eq
    ; target-center-reflect =
        liftLeft-target-center-reflect {v = v} ins
    ; target-source-reflect = liftLeft-target-source-reflect {v = v} ins
    ; targetLookup-insert = targetLookup-insert ins
    ; targetLookup-off = liftLeft-targetLookup-off {v = v} ins
    }

targetLiftCtxBoth : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {γ : CtxImp W}
    {γ′ : CtxImp (CTX.liftWorldBoth v W)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.LiftCtx v γ γ′
  → CTX.LiftCtx v (mapCtxᵀ ins γ)
      (mapCtxᵀ (liftBothTargetInsert {v = v} ins) γ′)
targetLiftCtxBoth ins CTX.lift-[] = CTX.lift-[]
targetLiftCtxBoth {ρ = ρ} {W′ = W′} {v = v} ins
    (CTX.lift-∷ {γ = γ} {γ′ = γ′} {A = A} {B = B}
      {p = p} {p′ = p′} liftγ) =
  subst≡
    (λ e → CTX.LiftCtx v
      (mapCtxᵀ ins (CTX.ctx-imp A B p ∷ γ))
      (e ∷ mapCtxᵀ (liftBothTargetInsert {v = v} ins) γ′))
    entry-eq
    (CTX.lift-∷ (targetLiftCtxBoth ins liftγ))
  where
  insBoth = liftBothTargetInsert {v = v} ins

  shift-eq :
      renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)
  shift-eq = renameᵗ-keep-shift ρ B

  p-trans :
      ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩
        renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)
  p-trans = transport⊑ᵂ insBoth p′

  p-shift :
      ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩
        ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)
  p-shift = subst≡
    (λ T → ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩ T)
    shift-eq p-trans

  entry-eq =
    ctx-imp-target-eq {W = CTX.liftWorldBoth v W′}
      {A = ⇑ᵗ A} {B = ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)}
      {B′ = renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)}
      {p = p-shift} {q = p-trans}
      (sym (renameᵗ-keep-shift ρ B))

targetLiftCtxLeft : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {γ : CtxImp W}
    {γ′ : CtxImp (CTX.liftWorldLeft W)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.LiftCtxᴸ v γ γ′
  → CTX.LiftCtxᴸ v (mapCtxᵀ ins γ)
      (mapCtxᵀ (liftLeftTargetInsert {v = v} ins) γ′)
targetLiftCtxLeft ins CTX.liftᴸ-[] = CTX.liftᴸ-[]
targetLiftCtxLeft ins (CTX.liftᴸ-∷ liftγ) =
  CTX.liftᴸ-∷ (targetLiftCtxLeft ins liftγ)

targetSmartLiftCtxLeft : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ Δᵐ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′} {πᵐ : Δᵐ ↪ᵗ Δᵐ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {Wᵐ′ : World (Nat.suc Δᴸ) Δᴿ′ Δᵐ′}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (insᵐ : TargetInsert ρ πᵐ Wᵐ Wᵐ′)
  → CTX.SmartLiftCtxᴸ γ γᵐ
  → CTX.SmartLiftCtxᴸ (mapCtxᵀ ins γ) (mapCtxᵀ insᵐ γᵐ)
targetSmartLiftCtxLeft ins insᵐ CTX.smart-lift-[] =
  CTX.smart-lift-[]
targetSmartLiftCtxLeft ins insᵐ (CTX.smart-lift-∷ liftγ) =
  CTX.smart-lift-∷ (targetSmartLiftCtxLeft ins insᵐ liftγ)

smartAliasGuard-impossible : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → ⊥
smartAliasGuard-impossible {W = W} {Wᵐ = Wᵐ} {β = β} {α = α}
    guard =
  CTX.variable≢star variable-equals-star
  where
  inv = CTX.invariantsʷ Wᵐ

  fresh-aligned : CTX.CenterAligned Wᵐ Fin.zero β
  fresh-aligned =
    trans (CTX.SmartAliasMergeGuard.pending-at-alias guard)
      (sym (CTX.SmartAliasMergeGuard.target-frozen guard β))

  source-entry : lookupStore (CTX.sourceStoreʷ Wᵐ) Fin.zero
      ≡ ＇ Fin.zero
  source-entry = cong (λ Σ → lookupStore Σ Fin.zero)
    (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)

  target-entry : lookupStore (CTX.targetStoreʷ Wᵐ) β ≡ ＇ α
  target-entry =
    trans
      (cong (λ Σ → lookupStore Σ β)
        (CTX.SmartAliasMergeGuard.targetStore-same guard))
      (lookupStore-∋ (CTX.SmartAliasMergeGuard.β:=＇α guard))

  heads-equal :
    toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵐ) α
  heads-equal = CTX.variableHeadsAlign
    (CTX.imprecision-cong
      (cong (renameᵗ (toRenameᵗ (CTX.ηᴸʷ Wᵐ))) source-entry)
      (cong (renameᵗ (toRenameᵗ (CTX.ηᴿʷ Wᵐ))) target-entry)
      (CTX.representationsImprecise inv fresh-aligned))

  β-equals-α : β ≡ α
  β-equals-α = toRenameᵗ-injective (CTX.ηᴿʷ Wᵐ)
    (trans (sym fresh-aligned) heads-equal)

  β-entry : lookupStore (CTX.targetStoreʷ W) β ≡ ＇ α
  β-entry = lookupStore-∋ (CTX.SmartAliasMergeGuard.β:=＇α guard)

  α-entry : lookupStore (CTX.targetStoreʷ W) α ≡ ★
  α-entry = lookupStore-∋ (CTX.SmartAliasMergeGuard.α:=★ guard)

  variable-equals-star : ＇ α ≡ ★
  variable-equals-star =
    trans (sym β-entry)
      (trans (cong (lookupStore (CTX.targetStoreʷ W)) β-equals-α)
        α-entry)

smartAliasInsertWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → TargetInsert ρ π W W′
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → World (Nat.suc Δᴸ) Δᴿ′ Δ′
smartAliasInsertWorld ins guard =
  ⊥-elim (smartAliasGuard-impossible guard)

smartAlias-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → ∀ Y
  → toRenameᵗ (CTX.ηᴿʷ (smartAliasInsertWorld ins guard))
      (toRenameᵗ ρ Y)
    ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
smartAlias-target-insert ins guard Y =
  ⊥-elim (smartAliasGuard-impossible guard)

smartAliasTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → TargetInsert ρ π Wᵐ (smartAliasInsertWorld ins guard)
smartAliasTargetInsert ins guard =
  ⊥-elim (smartAliasGuard-impossible guard)


smartAliasTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δ′}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ (Nat.suc Δᴿ) Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
    {κ : Nat.suc Δ ↪ᵗ Δ′}
  → (ins : TargetInsert wk↪ᵗ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → TargetWindowInsert ins κ
  → TargetWindowInsert (smartAliasTargetInsert ins guard) κ
smartAliasTargetWindowInsert ins guard win =
  ⊥-elim (smartAliasGuard-impossible guard)

smartAliasGuardInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → CTX.SmartAliasMergeGuard W′ (smartAliasInsertWorld ins guard)
      (toRenameᵗ ρ β) (toRenameᵗ ρ α)
smartAliasGuardInsert ins guard =
  ⊥-elim (smartAliasGuard-impossible guard)

smartFreshInsertView : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetInsertView ρ
      (EmbeddingPushout.premise
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard))) Wᵐ
      (EmbeddingPushout.premise
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)) ∘↪ CTX.ηᴸʷ Wᵐ)
      (EmbeddingPushout.old′
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)) ∘↪ CTX.ηᴿʷ W′)
      (renameEnv
        (EmbeddingPushout.premise
          (embeddingPushout π
            (CTX.SmartFreshBehindGuard.oldCenters guard)))
        (CTX.impEnvʷ Wᵐ))
      (CTX.sourceStoreʷ Wᵐ) (CTX.targetStoreʷ W′)
smartFreshInsertView {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δᴿ′ = Δᴿ′}
    {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard =
  record
    { sourceStore-kept = refl
    ; transport⊑ᵂ = transport′
    ; targetStore-rename =
        subst≡ (λ Σ → StoreRename (toRenameᵗ ρ) Σ
          (CTX.targetStoreʷ W′))
          (sym (CTX.SmartFreshBehindGuard.targetStore-same guard))
          (targetStore-rename ins)
    ; source-resolve = λ X → refl
    ; target-resolve = λ X →
        trans (target-resolve ins X)
          (cong (λ Σ → renameᵗ (toRenameᵗ ρ)
            (CTX.resolveVar Σ X))
            (sym (CTX.SmartFreshBehindGuard.targetStore-same guard)))
    ; align-insert = align′
    ; source-insert = toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ)
    ; target-insert = target′
    ; impEnv-insert = renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
    ; impEnv-off-insert = renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ)
    ; target-center-reflect = target-center-reflect′
    ; target-source-reflect = target-source-reflect′
    ; targetLookup-insert = old-entry
    ; targetLookup-off = fresh-entry
    }
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  po = embeddingPushout π old
  πᵐ = EmbeddingPushout.premise po
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

  target′ : ∀ Y
    → toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
  target′ Y =
    trans (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) (toRenameᵗ ρ Y))
      (trans (cong (toRenameᵗ old′) (target-insert ins Y))
        (trans (sym (commutes (toRenameᵗ (CTX.ηᴿʷ W) Y)))
          (cong (toRenameᵗ πᵐ)
            (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y)))))

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ Wᵐ ⟩ B
    → renameEnv πᵐ (CTX.impEnvʷ Wᵐ) ⊢
        renameᵗ (toRenameᵗ (πᵐ ∘↪ CTX.ηᴸʷ Wᵐ)) A
        ⊑ renameᵗ (toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′))
            (renameᵗ (toRenameᵗ ρ) B)
  transport′ {A = A} {B = B} p =
    CTX.imprecision-cong (sym source-eq) (sym target-eq)
      (rename-⊑ (toRenameᵗ πᵐ) (toRenameᵗ-injective πᵐ)
        (λ Z eq → trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ) Z) eq)
        p)
    where
    source-eq :
      renameᵗ (toRenameᵗ (πᵐ ∘↪ CTX.ηᴸʷ Wᵐ)) A
        ≡ renameᵗ (toRenameᵗ πᵐ)
            (renameᵗ (toRenameᵗ (CTX.ηᴸʷ Wᵐ)) A)
    source-eq = trans
      (renameᵗ-cong A (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ)))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ Wᵐ))
        (toRenameᵗ πᵐ) A))

    target-eq :
      renameᵗ (toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′))
          (renameᵗ (toRenameᵗ ρ) B)
        ≡ renameᵗ (toRenameᵗ πᵐ)
            (renameᵗ (toRenameᵗ (CTX.ηᴿʷ Wᵐ)) B)
    target-eq = trans
      (renameᵗ-comp (toRenameᵗ ρ)
        (toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′)) B)
      (trans (renameᵗ-cong B target′)
        (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵐ))
          (toRenameᵗ πᵐ) B)))

  align′ : ∀ {Xᴸ Xᴿ}
    → CTX.CenterAligned Wᵐ Xᴸ Xᴿ
    → toRenameᵗ (πᵐ ∘↪ CTX.ηᴸʷ Wᵐ) Xᴸ
      ≡ toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) (toRenameᵗ ρ Xᴿ)
  align′ {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} aligned =
    trans (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Xᴸ)
      (trans (cong (toRenameᵗ πᵐ) aligned) (sym (target′ Xᴿ)))

  target-center-reflect′ : ∀ {Y′ Z}
    → toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) Y′ ≡ toRenameᵗ πᵐ Z
    → Σ[ Y ∈ TyVar Δᴿ ]
        Y′ ≡ toRenameᵗ ρ Y × toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y ≡ Z
  target-center-reflect′ {Y′ = Y′} {Z = Z} eq
      with preimage? ρ Y′ in pre
  target-center-reflect′ {Y′ = Y′} {Z = Z} eq | nothing =
    ⊥-elim (pushout-off-image-disjoint π old
      (target-insert-off-image-center ins pre) nested-eq)
    where
    nested-eq : toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
      ≡ toRenameᵗ πᵐ Z
    nested-eq = trans
      (sym (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) Y′)) eq
  target-center-reflect′ {Y′ = Y′} {Z = Z} eq | just Y =
    Y , preimage?-sound ρ pre ,
      toRenameᵗ-injective πᵐ (trans (sym left-image) nested-eq)
    where
    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = preimage?-sound ρ pre

    nested-eq : toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
      ≡ toRenameᵗ πᵐ Z
    nested-eq = trans
      (sym (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) Y′)) eq

    left-image : toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
      ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
    left-image =
      trans (cong (λ T →
          toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) T)) y′-eq)
        (trans (cong (toRenameᵗ old′) (target-insert ins Y))
          (trans (sym (commutes (toRenameᵗ (CTX.ηᴿʷ W) Y)))
            (cong (toRenameᵗ πᵐ)
              (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y)))))

  target-source-reflect′ : ∀ {Xᴸ Y′}
    → toRenameᵗ (πᵐ ∘↪ CTX.ηᴸʷ Wᵐ) Xᴸ
      ≡ toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) Y′
    → Σ[ Y ∈ TyVar Δᴿ ]
        Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵐ Xᴸ Y
  target-source-reflect′ {Xᴸ = Xᴸ} aligned
      with target-center-reflect′ target-image
    where
    target-image :
      toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) _
        ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Xᴸ)
    target-image = trans (sym aligned)
      (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Xᴸ)
  target-source-reflect′ aligned | Y , y′-eq , target-eq =
    Y , y′-eq , sym target-eq

  old-entry : ∀ Xᴿ
    → lookupStore (CTX.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ)
      ≡ renameᵗ (toRenameᵗ ρ) (lookupStore (CTX.targetStoreʷ Wᵐ) Xᴿ)
  old-entry Xᴿ = trans (targetLookup-insert ins Xᴿ)
    (cong (renameᵗ (toRenameᵗ ρ))
      (sym (cong (λ Σ → lookupStore Σ Xᴿ)
        (CTX.SmartFreshBehindGuard.targetStore-same guard))))

  input-center-off : ∀ Xᴿ′
    → preimage? ρ Xᴿ′ ≡ nothing
    → preimage? π (toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ′) ≡ nothing
  input-center-off Xᴿ′ no-old
      with preimage? π (toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ′) in preπ
  input-center-off Xᴿ′ no-old | nothing = refl
  input-center-off Xᴿ′ no-old | just Z
      with target-center-reflect ins (preimage?-sound π preπ)
  input-center-off Xᴿ′ no-old | just Z
      | Xᴿ , xᴿ′-eq , old-center = ⊥-elim (just≢nothing impossible)
    where
    impossible : just Xᴿ ≡ nothing
    impossible = trans (sym (preimage?-image ρ Xᴿ))
      (trans (cong (preimage? ρ) (sym xᴿ′-eq)) no-old)

  fresh-entry : ∀ Xᴿ′
    → preimage? πᵐ (toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) Xᴿ′) ≡ nothing
    → (lookupStore (CTX.targetStoreʷ W′) Xᴿ′ ≡ ★)
      ⊎ (Σ[ Yᴿ′ ∈ TyVar Δᴿ′ ]
          (lookupStore (CTX.targetStoreʷ W′) Xᴿ′ ≡ ＇ Yᴿ′)
        × (∀ Xᴸ → toRenameᵗ (πᵐ ∘↪ CTX.ηᴸʷ Wᵐ) Xᴸ
            ≡ toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) Yᴿ′ → ⊥))
  fresh-entry Xᴿ′ off with preimage? ρ Xᴿ′ in preρ
  fresh-entry Xᴿ′ off | just Xᴿ = ⊥-elim (just≢nothing impossible)
    where
    xᴿ′-eq : Xᴿ′ ≡ toRenameᵗ ρ Xᴿ
    xᴿ′-eq = preimage?-sound ρ preρ

    center-eq :
      toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) Xᴿ′
        ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ)
    center-eq = trans
      (cong (toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′)) xᴿ′-eq)
      (target′ Xᴿ)

    impossible : just (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ) ≡ nothing
    impossible = trans
      (sym (preimage?-image πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Xᴿ)))
      (trans (cong (preimage? πᵐ) (sym center-eq)) off)
  fresh-entry Xᴿ′ off | nothing
      with targetLookup-off ins Xᴿ′ (input-center-off Xᴿ′ preρ)
  fresh-entry Xᴿ′ off | nothing | inj₁ dynamic = inj₁ dynamic
  fresh-entry Xᴿ′ off | nothing
      | inj₂ (Yᴿ′ , entry , head-no-source) =
    inj₂ (Yᴿ′ , entry , inserted-head-no-source)
    where
    inserted-head-no-source : ∀ Xᴸ
      → toRenameᵗ (πᵐ ∘↪ CTX.ηᴸʷ Wᵐ) Xᴸ
        ≡ toRenameᵗ (old′ ∘↪ CTX.ηᴿʷ W′) Yᴿ′
      → ⊥
    inserted-head-no-source Xᴸ aligned
        with target-source-reflect′ aligned
    inserted-head-no-source Fin.zero aligned
        | Yᴿ , yᴿ′-eq , source-aligned =
      CTX.SmartFreshBehindGuard.fresh-not-target guard Yᴿ
        (sym source-aligned)
    inserted-head-no-source (Fin.suc Xᴸ) aligned
        | Yᴿ , yᴿ′-eq , source-aligned =
      head-no-source Xᴸ
        (subst≡ (CTX.CenterAligned W′ Xᴸ) (sym yᴿ′-eq)
          (align-insert ins old-aligned))
      where
      old-aligned : CTX.CenterAligned W Xᴸ Yᴿ
      old-aligned = toRenameᵗ-injective old
        (trans
          (sym (CTX.SmartFreshBehindGuard.old-source-frozen guard Xᴸ))
          (trans source-aligned
            (CTX.SmartFreshBehindGuard.target-frozen guard Yᴿ)))

smartFreshInsertWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → World (Nat.suc Δᴸ) Δᴿ′
      (EmbeddingPushout.Δᵐ′
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)))
smartFreshInsertWorld {π = π} {W′ = W′} {Wᵐ = Wᵐ} ins guard =
  CTX.mix-renamed-targetʷ πᵐ old′ Wᵐ W′
    (targetInsertView-invariants (smartFreshInsertView ins guard)
      (CTX.invariantsʷ Wᵐ))
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)
  πᵐ = EmbeddingPushout.premise po
  old′ = EmbeddingPushout.old′ po

smartFresh-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → ∀ Y
  → toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard))
      (toRenameᵗ ρ Y)
    ≡ toRenameᵗ (EmbeddingPushout.premise
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)))
        (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
smartFresh-target-insert {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard Y =
  trans (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) (toRenameᵗ ρ Y))
    (trans (cong (toRenameᵗ old′) (target-insert ins Y))
      (trans (sym (commutes (toRenameᵗ (CTX.ηᴿʷ W) Y)))
        (cong (toRenameᵗ πᵐ)
          (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y)))))
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)
  πᵐ = EmbeddingPushout.premise po
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

smartFreshTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetInsert ρ (EmbeddingPushout.premise
      (embeddingPushout π
        (CTX.SmartFreshBehindGuard.oldCenters guard))) Wᵐ
      (smartFreshInsertWorld ins guard)
smartFreshTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard =
  target-insert-view (smartFreshInsertView ins guard)

smartFreshGuardInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → CTX.SmartFreshBehindGuard W′ (smartFreshInsertWorld ins guard)
smartFreshGuardInsert {Δᴸ = Δᴸ} {Δᴿ′ = Δᴿ′} {Δ′ = Δ′}
    {ρ = ρ} {π = π} {W = W} {W′ = W′} {Wᵐ = Wᵐ}
    ins guard =
  CTX.smart-fresh-behind-guard old′
    source-store target-store transport′ old-mark-mono′
    target-frozen′ old-source-frozen′ fresh-not-target′ fresh-mark′
    target-mark-mono′
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)
  πᵐ = EmbeddingPushout.premise po
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

  source-store : CTX.sourceStoreʷ (smartFreshInsertWorld ins guard)
      ≡ store-lift (CTX.sourceStoreʷ W′)
  source-store =
    trans (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
      (cong store-lift (sym (sourceStore-kept ins)))

  target-store : CTX.targetStoreʷ (smartFreshInsertWorld ins guard)
      ≡ CTX.targetStoreʷ W′
  target-store = refl

  target-frozen′ : ∀ Y′
    → toRenameᵗ
        (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
      ≡ toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
  target-frozen′ = toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′)

  smartSubst : Nat.suc Δ′ ⇒ˢ EmbeddingPushout.Δᵐ′ po
  smartSubst Fin.zero =
    ＇ (toRenameᵗ
      (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) Fin.zero)
  smartSubst (Fin.suc Z′) = ＇ (toRenameᵗ old′ Z′)

  old-source-frozen′ : ∀ Xᴸ
    → toRenameᵗ
        (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) (Fin.suc Xᴸ)
      ≡ toRenameᵗ old′ (toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ)
  old-source-frozen′ Xᴸ =
    trans (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) (Fin.suc Xᴸ))
      (trans (cong (toRenameᵗ πᵐ)
        (CTX.SmartFreshBehindGuard.old-source-frozen guard Xᴸ))
        (trans (commutes (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))
          (cong (toRenameᵗ old′) (sym (source-insert ins Xᴸ)))))

  fresh-not-target′ : ∀ Y′
    → toRenameᵗ
        (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
      ≢ toRenameᵗ
        (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) Fin.zero
  fresh-not-target′ Y′ eq
      with target-center-reflect
        (smartFreshTargetInsert ins guard) target-image
    where
    target-image :
      toRenameᵗ
        (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
      ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero)
    target-image =
      trans eq (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Fin.zero)
  fresh-not-target′ Y′ eq | Y , y′-eq , target-eq =
    CTX.SmartFreshBehindGuard.fresh-not-target guard Y target-eq

  fresh-mark′ :
    CTX.impEnvʷ (smartFreshInsertWorld ins guard)
      (toRenameᵗ
        (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) Fin.zero)
      ≡ X⊑★
  fresh-mark′ =
    trans (cong (renameEnv πᵐ (CTX.impEnvʷ Wᵐ))
        (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Fin.zero))
      (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
        (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero))
        (CTX.SmartFreshBehindGuard.fresh-mark-dynamic guard))

  old-mark-mono′ : ∀ Z′
    → CTX.impEnvʷ W′ Z′ ≡ X⊑★
    → CTX.impEnvʷ (smartFreshInsertWorld ins guard)
        (toRenameᵗ old′ Z′) ≡ X⊑★
  old-mark-mono′ Z′ star with preimage? π Z′ in pre
  old-mark-mono′ Z′ star | nothing =
    renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ)
      (pushout-old-off-premise π old pre)
  old-mark-mono′ Z′ star | just Z =
    subst≡
      (λ C → CTX.impEnvʷ (smartFreshInsertWorld ins guard) C
        ≡ X⊑★)
      (sym smart-image-eq)
      (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
          (toRenameᵗ old Z))
        (CTX.SmartFreshBehindGuard.old-mark-mono guard Z old-star))
    where
    image-eq : Z′ ≡ toRenameᵗ π Z
    image-eq = preimage?-sound π pre

    old-star : CTX.impEnvʷ W Z ≡ X⊑★
    old-star =
      trans (sym (impEnv-insert ins Z))
        (subst≡ (λ C → CTX.impEnvʷ W′ C ≡ X⊑★)
          image-eq star)

    smart-image-eq :
      toRenameᵗ old′ Z′ ≡ toRenameᵗ πᵐ (toRenameᵗ old Z)
    smart-image-eq =
      trans (cong (toRenameᵗ old′) image-eq) (sym (commutes Z))

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft W′) Z ≡ X⊑★
    → CTX.impEnvʷ (smartFreshInsertWorld ins guard)
        ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star = X⊑★ fresh-mark′
  smartStar (Fin.suc Z) star = X⊑★ (old-mark-mono′ Z star)

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W′)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) X)
  source-point Fin.zero = refl
  source-point (Fin.suc X) = cong ＇_ (sym (old-source-frozen′ X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W′)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y)
  target-point Y = cong ＇_ (sym (target-frozen′ Y))

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft W′) C)
      ≡ CTX.embedᴸ (smartFreshInsertWorld ins guard) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W′))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst
          (toRenameᵗ (CTX.ηᴸʷ (smartFreshInsertWorld ins guard))) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft W′) C)
      ≡ CTX.embedᴿ (smartFreshInsertWorld ins guard) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W′))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst
          (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard))) C))

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ′}
    → A ⊑ᵂ⟨ CTX.liftWorldLeft W′ ⟩ B
    → A ⊑ᵂ⟨ smartFreshInsertWorld ins guard ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft W′}
      {W′ = smartFreshInsertWorld ins guard}
      smartSubst smartStar source-eq target-eq

  target-mark-mono′ : ∀ Y′
    → CTX.impEnvʷ W′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′) ≡ X⊑★
    → CTX.impEnvʷ (smartFreshInsertWorld ins guard)
        (toRenameᵗ
          (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′)
      ≡ X⊑★
  target-mark-mono′ Y′ star with preimage? ρ Y′ in pre
  target-mark-mono′ Y′ star | nothing
      with preimage? πᵐ
        (toRenameᵗ
          (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′) in preᵐ
  target-mark-mono′ Y′ star | nothing | nothing =
    renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ) preᵐ
  target-mark-mono′ Y′ star | nothing | just Z =
    ⊥-elim (just≢nothing just-eq)
    where
    reflected :
      Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y ×
        toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y ≡ Z
    reflected =
      target-center-reflect (smartFreshTargetInsert ins guard)
        (preimage?-sound πᵐ preᵐ)

    Y = proj₁ reflected

    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = proj₁ (proj₂ reflected)

    just-eq : just Y ≡ nothing
    just-eq =
      trans (sym (preimage?-image ρ Y))
        (trans (cong (preimage? ρ) (sym y′-eq)) pre)
  target-mark-mono′ Y′ star | just Y =
    subst≡
      (λ C → CTX.impEnvʷ (smartFreshInsertWorld ins guard) C
        ≡ X⊑★)
      (sym smart-image-eq)
      (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
          (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y))
        (CTX.SmartFreshBehindGuard.target-mark-mono guard Y old-star))
    where
    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = preimage?-sound ρ pre

    old-center-eq :
      toRenameᵗ (CTX.ηᴿʷ W′) Y′
        ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Y)
    old-center-eq =
      trans (cong (toRenameᵗ (CTX.ηᴿʷ W′)) y′-eq)
        (target-insert ins Y)

    old-star :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴿʷ W) Y) ≡ X⊑★
    old-star =
      trans (sym (impEnv-insert ins
          (toRenameᵗ (CTX.ηᴿʷ W) Y)))
        (subst≡
          (λ C → CTX.impEnvʷ W′ C ≡ X⊑★)
          old-center-eq star)

    smart-image-eq :
      toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
        ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
    smart-image-eq =
      trans
        (cong
          (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)))
          y′-eq)
        (smartFresh-target-insert ins guard Y)


smartFreshTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δ′ Δᵐ}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ (Nat.suc Δᴿ) Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {κ : Nat.suc Δ ↪ᵗ Δ′}
  → (ins : TargetInsert wk↪ᵗ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetWindowInsert ins κ
  → Σ[ κᵐ ∈ Nat.suc Δᵐ ↪ᵗ
      EmbeddingPushout.Δᵐ′
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)) ]
      TargetWindowInsert (smartFreshTargetInsert ins guard) κᵐ
smartFreshTargetWindowInsert {π = π} {W′ = W′} ins guard win
    with embeddingPushoutWindow old (TargetWindowInsert.windowEmbedding win)
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard
smartFreshTargetWindowInsert {π = π} {W′ = W′} ins guard win
    | pushout-window κᵐ window-ok zero-commutes old-commutes =
  κᵐ , record
    { windowEmbedding = window-ok
    ; window-zero =
        trans (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) Fin.zero)
          (trans
            (cong (toRenameᵗ old′)
              (TargetWindowInsert.window-zero win))
            zero-commutes)
    ; window-old = old-commutes
    }
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  old′ = EmbeddingPushout.old′ (embeddingPushout π old)


rightPushoutWindow : ∀ {Δ Δᵐ}
  → (old : Δ ↪ᵗ Δᵐ)
  → Nat.suc Δᵐ ↪ᵗ
      (EmbeddingPushout.Δᵐ′ (embeddingPushout wk↪ᵗ old))
rightPushoutWindow old =
  keep (EmbeddingPushout.premise (embeddingPushout id↪ᵗ old))

record RebaseInsertOK {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    (ins : TargetInsert ρ π W W⁺) : Set where
  constructor rebase-insert-ok
  field
    rebaseInsertView : TargetInsertView ρ π Wᵖ
      (π ∘↪ CTX.ηᴸʷ Wᵖ) (CTX.ηᴿʷ W⁺)
      (renameEnv π (CTX.impEnvʷ Wᵖ))
      (CTX.sourceStoreʷ Wᵖ) (CTX.targetStoreʷ W⁺)

open RebaseInsertOK public

record TargetInsertDirectStarOff {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    (ins : TargetInsert ρ π W W⁺) : Set where
  constructor target-insert-direct-star-off
  field
    targetDirectStarOff : ∀ Y′
      → preimage? π (toRenameᵗ (CTX.ηᴿʷ W⁺) Y′) ≡ nothing
      → lookupStore (CTX.targetStoreʷ W⁺) Y′ ≡ ★

open TargetInsertDirectStarOff public

bindStarTargetInsertDirectStarOff : ∀ {Δᴸ Δᴿ Δ Δ′}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ (Nat.suc Δᴿ) Δ′}
  → (ins : TargetInsert wk↪ᵗ π W W⁺)
  → CTX.targetStoreʷ W⁺ ≡
      Reduction.applyStores (bind ★ ∷ []) (CTX.targetStoreʷ W)
  → TargetInsertDirectStarOff ins
bindStarTargetInsertDirectStarOff {π = π} {W = W} {W⁺ = W⁺}
    ins follows = target-insert-direct-star-off dynamic
  where
  dynamic : ∀ Y′
    → preimage? π (toRenameᵗ (CTX.ηᴿʷ W⁺) Y′) ≡ nothing
    → lookupStore (CTX.targetStoreʷ W⁺) Y′ ≡ ★
  dynamic Fin.zero off =
    cong (λ Σ → lookupStore Σ Fin.zero) follows
  dynamic (Fin.suc Y) off = ⊥-elim (just≢nothing impossible)
    where
    center-eq : toRenameᵗ (CTX.ηᴿʷ W⁺) (Fin.suc Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Y)
    center-eq = trans
      (cong (toRenameᵗ (CTX.ηᴿʷ W⁺)) (sym (toRename-wk-eq Y)))
      (target-insert ins Y)

    impossible : just (toRenameᵗ (CTX.ηᴿʷ W) Y) ≡ nothing
    impossible = trans
      (sym (preimage?-image π (toRenameᵗ (CTX.ηᴿʷ W) Y)))
      (trans (cong (preimage? π) (sym center-eq)) off)

liftBothTargetInsertDirectStarOff : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W⁺)
  → TargetInsertDirectStarOff ins
  → TargetInsertDirectStarOff (liftBothTargetInsert {v = v} ins)
liftBothTargetInsertDirectStarOff {π = π} {W⁺ = W⁺} {v = v} ins dynamic =
  target-insert-direct-star-off lifted
  where
  lifted : ∀ Y′
    → preimage? (keep π)
        (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W⁺)) Y′)
        ≡ nothing
    → lookupStore (CTX.targetStoreʷ (CTX.liftWorldBoth v W⁺)) Y′ ≡ ★
  lifted Fin.zero ()
  lifted (Fin.suc Y′) off =
    cong ⇑ᵗ (targetDirectStarOff dynamic Y′
      (sucMaybe-nothing
        (preimage? π (toRenameᵗ (CTX.ηᴿʷ W⁺) Y′)) off))

liftLeftTargetInsertDirectStarOff : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W⁺)
  → TargetInsertDirectStarOff ins
  → TargetInsertDirectStarOff (liftLeftTargetInsert {v = v} ins)
liftLeftTargetInsertDirectStarOff {π = π} {W⁺ = W⁺} ins dynamic =
  target-insert-direct-star-off λ Y′ off →
    targetDirectStarOff dynamic Y′
      (sucMaybe-nothing
        (preimage? π (toRenameᵗ (CTX.ηᴿʷ W⁺) Y′)) off)

smartFreshTargetDirectStarOff : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W⁺)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetInsertDirectStarOff ins
  → ∀ Y′
  → preimage? (EmbeddingPushout.premise
      (embeddingPushout π
        (CTX.SmartFreshBehindGuard.oldCenters guard)))
      (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′)
      ≡ nothing
  → lookupStore (CTX.targetStoreʷ (smartFreshInsertWorld ins guard)) Y′ ≡ ★
smartFreshTargetDirectStarOff {ρ = ρ} {π = π} {W⁺ = W⁺}
    ins guard dynamic Y′ off with preimage? ρ Y′ in pre
smartFreshTargetDirectStarOff ins guard dynamic Y′ off | nothing =
  targetDirectStarOff dynamic Y′ (target-insert-off-image-center ins pre)
smartFreshTargetDirectStarOff {ρ = ρ} {π = π} {Wᵐ = Wᵐ}
    ins guard dynamic Y′ off | just Y =
  ⊥-elim (just≢nothing impossible)
  where
  πᵐ = EmbeddingPushout.premise
    (embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard))

  y′-eq : Y′ ≡ toRenameᵗ ρ Y
  y′-eq = preimage?-sound ρ pre

  center-eq : toRenameᵗ
      (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
    ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
  center-eq = trans
    (cong (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)))
      y′-eq)
    (smartFresh-target-insert ins guard Y)

  impossible : just (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y) ≡ nothing
  impossible = trans
    (sym (preimage?-image πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)))
    (trans (cong (preimage? πᵐ) (sym center-eq)) off)

smartFreshTargetInsertDirectStarOff : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W⁺)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetInsertDirectStarOff ins
  → TargetInsertDirectStarOff (smartFreshTargetInsert ins guard)
smartFreshTargetInsertDirectStarOff ins guard dynamic =
  target-insert-direct-star-off
    (smartFreshTargetDirectStarOff ins guard dynamic)

directStarOffRebaseInsertOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → TargetInsertDirectStarOff ins
  → CTX.targetStoreʷ Wᵖ ≡ CTX.targetStoreʷ W
  → (∀ Y → toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ W) Y)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
directStarOffRebaseInsertOK {ρ = ρ} {π = π} {W = W} {Wᵖ = Wᵖ}
    {W⁺ = W⁺} ins direct-star-off target-store-same target-frozen =
  rebase-insert-ok record
    { sourceStore-kept = refl
    ; transport⊑ᵂ = transport
    ; targetStore-rename = target-store-rename
    ; source-resolve = λ X → refl
    ; target-resolve = target-resolveᵖ
    ; align-insert = align-insertᵖ
    ; source-insert = toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵖ)
    ; target-insert = target-point
    ; impEnv-insert = renameEnv-image π (CTX.impEnvʷ Wᵖ)
    ; impEnv-off-insert = renameEnv-off π (CTX.impEnvʷ Wᵖ)
    ; target-center-reflect = target-center-reflectᵖ
    ; target-source-reflect = target-source-reflectᵖ
    ; targetLookup-insert = target-lookup-insertᵖ
    ; targetLookup-off = target-lookup-offᵖ
    }
  where
  source-eq : ∀ A
    → renameᵗ (toRenameᵗ (π ∘↪ CTX.ηᴸʷ Wᵖ)) A
      ≡ renameᵗ (toRenameᵗ π)
          (renameᵗ (toRenameᵗ (CTX.ηᴸʷ Wᵖ)) A)
  source-eq A = trans
    (renameᵗ-cong A (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵖ)))
    (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ Wᵖ))
      (toRenameᵗ π) A))

  target-point : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ W⁺) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y)
  target-point Y = trans (target-insert ins Y)
    (cong (toRenameᵗ π) (sym (target-frozen Y)))

  target-eq : ∀ B
    → renameᵗ (toRenameᵗ (CTX.ηᴿʷ W⁺))
        (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π)
          (renameᵗ (toRenameᵗ (CTX.ηᴿʷ Wᵖ)) B)
  target-eq B = trans
    (renameᵗ-comp (toRenameᵗ ρ) (toRenameᵗ (CTX.ηᴿʷ W⁺)) B)
    (trans (renameᵗ-cong B target-point)
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵖ))
        (toRenameᵗ π) B)))

  transport : ∀ {A : Ty _} {B : Ty _}
    → A ⊑ᵂ⟨ Wᵖ ⟩ B
    → renameEnv π (CTX.impEnvʷ Wᵖ) ⊢
        renameᵗ (toRenameᵗ (π ∘↪ CTX.ηᴸʷ Wᵖ)) A
          ⊑ renameᵗ (toRenameᵗ (CTX.ηᴿʷ W⁺))
              (renameᵗ (toRenameᵗ ρ) B)
  transport {A = A} {B = B} p =
    CTX.imprecision-cong (sym (source-eq A)) (sym (target-eq B))
      (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
        (λ Z eq → trans (renameEnv-image π (CTX.impEnvʷ Wᵖ) Z) eq) p)

  target-store-rename : StoreRename (toRenameᵗ ρ)
      (CTX.targetStoreʷ Wᵖ) (CTX.targetStoreʷ W⁺)
  target-store-rename =
    subst≡
      (λ Σ → StoreRename (toRenameᵗ ρ) Σ (CTX.targetStoreʷ W⁺))
      (sym target-store-same)
      (targetStore-rename ins)

  target-resolveᵖ : ∀ Y
    → CTX.resolveVar (CTX.targetStoreʷ W⁺) (toRenameᵗ ρ Y)
      ≡ renameᵗ (toRenameᵗ ρ)
          (CTX.resolveVar (CTX.targetStoreʷ Wᵖ) Y)
  target-resolveᵖ Y = trans (target-resolve ins Y)
    (cong (renameᵗ (toRenameᵗ ρ))
      (sym (cong (λ Σ → CTX.resolveVar Σ Y)
        target-store-same)))

  align-insertᵖ : ∀ {Yᴸ Yᴿ}
    → CTX.CenterAligned Wᵖ Yᴸ Yᴿ
    → toRenameᵗ (π ∘↪ CTX.ηᴸʷ Wᵖ) Yᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) (toRenameᵗ ρ Yᴿ)
  align-insertᵖ {Yᴸ} {Yᴿ} aligned =
    trans (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵖ) Yᴸ)
      (trans (cong (toRenameᵗ π) aligned)
        (trans (cong (toRenameᵗ π) (target-frozen Yᴿ))
          (sym (target-insert ins Yᴿ))))

  target-center-reflectᵖ : ∀ {Y′ Z}
    → toRenameᵗ (CTX.ηᴿʷ W⁺) Y′ ≡ toRenameᵗ π Z
    → Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y × toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y ≡ Z
  target-center-reflectᵖ eq with target-center-reflect ins eq
  target-center-reflectᵖ eq | Y , mapped , old =
    Y , mapped , trans (target-frozen Y) old

  target-source-reflectᵖ : ∀ {Yᴸ Y′}
    → toRenameᵗ (π ∘↪ CTX.ηᴸʷ Wᵖ) Yᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) Y′
    → Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵖ Yᴸ Y
  target-source-reflectᵖ {Yᴸ} aligned
      with target-center-reflect ins target-image
    where
    target-image : toRenameᵗ (CTX.ηᴿʷ W⁺) _
        ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ Wᵖ) Yᴸ)
    target-image = trans (sym aligned)
      (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵖ) Yᴸ)
  target-source-reflectᵖ aligned | Y , mapped , old =
    Y , mapped , trans (sym old) (sym (target-frozen Y))

  target-lookup-insertᵖ : ∀ Y
    → lookupStore (CTX.targetStoreʷ W⁺) (toRenameᵗ ρ Y)
      ≡ renameᵗ (toRenameᵗ ρ)
          (lookupStore (CTX.targetStoreʷ Wᵖ) Y)
  target-lookup-insertᵖ Y = trans (targetLookup-insert ins Y)
    (cong (renameᵗ (toRenameᵗ ρ))
      (sym (cong (λ Σ → lookupStore Σ Y)
        target-store-same)))

  target-lookup-offᵖ : ∀ Y′
    → preimage? π (toRenameᵗ (CTX.ηᴿʷ W⁺) Y′) ≡ nothing
    → lookupStore (CTX.targetStoreʷ W⁺) Y′ ≡ ★
      ⊎ Σ[ Z′ ∈ TyVar _ ]
          lookupStore (CTX.targetStoreʷ W⁺) Y′ ≡ ＇ Z′
        × (∀ Zᴸ → toRenameᵗ (π ∘↪ CTX.ηᴸʷ Wᵖ) Zᴸ
            ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) Z′ → ⊥)
  target-lookup-offᵖ Y′ off =
    inj₁ (targetDirectStarOff direct-star-off Y′ off)

directStarOffForwardInsertOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → TargetInsertDirectStarOff ins
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
directStarOffForwardInsertOK ins dynamic rb =
  directStarOffRebaseInsertOK ins dynamic
    (CTX.SameRuntime.targetStore-same (CTX.RebaseAt.sameRuntime rb))
    (CTX.RebaseAt.ηᴿ-frozen rb)

directStarOffReverseInsertOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → TargetInsertDirectStarOff ins
  → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
directStarOffReverseInsertOK ins dynamic rb =
  directStarOffRebaseInsertOK ins dynamic
    (sym (CTX.SameRuntime.targetStore-same runtime))
    (λ Y → sym (CTX.RebaseAt.ηᴿ-frozen rb Y))
  where
  runtime = CTX.RebaseAt.sameRuntime rb

targetInsertDirectStarOffForward : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W₁ W₂ : World Δᴸ Δᴿ Δ}
    {W₁⁺ W₂⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ′ : TyVar Δᴿ′}
  → (ins₁ : TargetInsert ρ π W₁ W₁⁺)
  → (ins₂ : TargetInsert ρ π W₂ W₂⁺)
  → TargetInsertDirectStarOff ins₁
  → CTX.RebaseAt W₁⁺ W₂⁺ Xᴸ Xᴿ′
  → TargetInsertDirectStarOff ins₂
targetInsertDirectStarOffForward {π = π} {W₁⁺ = W₁⁺} {W₂⁺ = W₂⁺}
    ins₁ ins₂ dynamic rb = target-insert-direct-star-off transferred
  where
  runtime = CTX.RebaseAt.sameRuntime rb
  target-store : CTX.targetStoreʷ W₂⁺ ≡ CTX.targetStoreʷ W₁⁺
  target-store = CTX.SameRuntime.targetStore-same runtime

  transferred : ∀ Y′
    → preimage? π (toRenameᵗ (CTX.ηᴿʷ W₂⁺) Y′) ≡ nothing
    → lookupStore (CTX.targetStoreʷ W₂⁺) Y′ ≡ ★
  transferred Y′ off =
    subst≡ (λ Σ → lookupStore Σ Y′ ≡ ★) (sym target-store)
      (targetDirectStarOff dynamic Y′ old-off)
    where
    old-off : preimage? π (toRenameᵗ (CTX.ηᴿʷ W₁⁺) Y′) ≡ nothing
    old-off = trans
      (sym (cong (preimage? π) (CTX.RebaseAt.ηᴿ-frozen rb Y′))) off

targetInsertDirectStarOffReverse : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W₁ W₂ : World Δᴸ Δᴿ Δ}
    {W₁⁺ W₂⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ′ : TyVar Δᴿ′}
  → (ins₁ : TargetInsert ρ π W₁ W₁⁺)
  → (ins₂ : TargetInsert ρ π W₂ W₂⁺)
  → TargetInsertDirectStarOff ins₁
  → CTX.RebaseAt W₂⁺ W₁⁺ Xᴸ Xᴿ′
  → TargetInsertDirectStarOff ins₂
targetInsertDirectStarOffReverse {π = π} {W₁⁺ = W₁⁺} {W₂⁺ = W₂⁺}
    ins₁ ins₂ dynamic rb = target-insert-direct-star-off transferred
  where
  runtime = CTX.RebaseAt.sameRuntime rb
  target-store : CTX.targetStoreʷ W₁⁺ ≡ CTX.targetStoreʷ W₂⁺
  target-store = CTX.SameRuntime.targetStore-same runtime

  transferred : ∀ Y′
    → preimage? π (toRenameᵗ (CTX.ηᴿʷ W₂⁺) Y′) ≡ nothing
    → lookupStore (CTX.targetStoreʷ W₂⁺) Y′ ≡ ★
  transferred Y′ off =
    subst≡ (λ Σ → lookupStore Σ Y′ ≡ ★) target-store
      (targetDirectStarOff dynamic Y′ old-off)
    where
    old-off : preimage? π (toRenameᵗ (CTX.ηᴿʷ W₁⁺) Y′) ≡ nothing
    old-off = trans
      (cong (preimage? π) (CTX.RebaseAt.ηᴿ-frozen rb Y′)) off

insertRebaseWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (Wᵖ : World Δᴸ Δᴿ Δ)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
  → World Δᴸ Δᴿ′ Δ′
insertRebaseWorld {π = π} {W⁺ = W⁺} ins Wᵖ ok =
  CTX.mix-targetʷ π Wᵖ W⁺
    (targetInsertView-invariants (rebaseInsertView ok)
      (CTX.invariantsʷ Wᵖ))

insertRebase-source : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → ∀ Xᴸ
  → toRenameᵗ (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ ok)) Xᴸ
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ Wᵖ) Xᴸ)
insertRebase-source ins ok =
  view-source-insert (rebaseInsertView ok)

insertRebase-target : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → ∀ Y
  → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ ok))
      (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y)
insertRebase-target ins ok =
  view-target-insert (rebaseInsertView ok)

insertRebase-impEnv : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → ∀ Z
  → CTX.impEnvʷ (insertRebaseWorld ins Wᵖ ok) (toRenameᵗ π Z)
      ≡ CTX.impEnvʷ Wᵖ Z
insertRebase-impEnv ins ok =
  view-impEnv-insert (rebaseInsertView ok)

insertRebase-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′} {Y′ Z}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ ok)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y ≡ Z
insertRebase-target-center-reflect ins ok =
  view-target-center-reflect (rebaseInsertView ok)

insertRebase-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′} {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → CTX.CenterAligned (insertRebaseWorld ins Wᵖ ok) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵖ Xᴸ Y
insertRebase-target-source-reflect ins ok =
  view-target-source-reflect (rebaseInsertView ok)

insertRebase-source-embed : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → (A : Ty Δᴸ)
  → CTX.embedᴸ (insertRebaseWorld ins Wᵖ ok) A
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ Wᵖ A)
insertRebase-source-embed {π = π} {Wᵖ = Wᵖ} ins ok A =
  trans (renameᵗ-cong A (insertRebase-source ins ok))
    (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ Wᵖ))
      (toRenameᵗ π) A))

insertRebase-target-embed : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ (insertRebaseWorld ins Wᵖ ok)
      (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ Wᵖ B)
insertRebase-target-embed {ρ = ρ} {π = π} {Wᵖ = Wᵖ} ins ok B =
  trans
    (renameᵗ-comp (toRenameᵗ ρ)
      (toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ ok))) B)
    (trans (renameᵗ-cong B (insertRebase-target ins ok))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵖ))
        (toRenameᵗ π) B)))

insertRebaseTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → TargetInsert ρ π Wᵖ (insertRebaseWorld ins Wᵖ ok)
insertRebaseTargetInsert ins ok =
  target-insert-view (rebaseInsertView ok)

insertRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
insertRebaseAt {ρ = ρ} {π = π} {Wᵖ = Wᵖ} {W⁺ = W⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins rb ok =
  insertRebaseWorld ins Wᵖ ok , insᵖ ,
    CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  insᵖ = insertRebaseTargetInsert ins ok

  runtime : CTX.SameRuntime W⁺ (insertRebaseWorld ins Wᵖ ok)
  runtime =
    CTX.same-runtime
      (trans
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb))
        (sym (sourceStore-kept ins)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ
        (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ ok)) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ W⁺) Y
  off-left {Y} Y≢ =
    trans (insertRebase-source ins ok Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (source-insert ins Y)))

  frozen-target : ∀ Y
    → toRenameᵗ
        (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ ok)) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) Y
  frozen-target Y = refl

  aligned : toRenameᵗ
      (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ ok)) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ ok))
          (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (insertRebase-source ins ok Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (trans (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴿ-frozen rb Xᴿ))
          (sym (target-insert ins Xᴿ))))

  reps : CTX.StoreRepImp (insertRebaseWorld ins Wᵖ ok)
      Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert insᵖ (CTX.RebaseAt.storeRepresentations rb)

reverseRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
  → (ok : RebaseInsertOK {Wᵖ = Wᵖ} ins)
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt Wᵖ⁺ W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
reverseRebaseAt {ρ = ρ} {π = π} {Wᵖ = Wᵖ} {W⁺ = W⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins rb ok =
  insertRebaseWorld ins Wᵖ ok , insᵖ ,
    CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  insᵖ = insertRebaseTargetInsert ins ok

  runtime : CTX.SameRuntime (insertRebaseWorld ins Wᵖ ok) W⁺
  runtime =
    CTX.same-runtime
      (trans (sourceStore-kept ins)
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ W⁺) Y
      ≡ toRenameᵗ
          (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ ok)) Y
  off-left {Y} Y≢ =
    trans (source-insert ins Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (insertRebase-source ins ok Y)))

  frozen-target : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ W⁺) Y
      ≡ toRenameᵗ
          (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ ok)) Y
  frozen-target Y = refl

  aligned : toRenameᵗ (CTX.ηᴸʷ W⁺) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (source-insert ins Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (sym (target-insert ins Xᴿ)))

  reps : CTX.StoreRepImp W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert ins (CTX.RebaseAt.storeRepresentations rb)

pullbackRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → (ok : RebaseInsertOK {Wᵖ = W} insᵖ)
  → CTX.RebaseAt (insertRebaseWorld insᵖ W ok) Wᵖ⁺
      Xᴸ (toRenameᵗ ρ Xᴿ)
pullbackRebaseAt {ρ = ρ} {π = π} {W = W} {Wᵖ = Wᵖ}
    {Wᵖ⁺ = Wᵖ⁺} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} insᵖ rb ok =
  CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  ins = insertRebaseTargetInsert insᵖ ok

  runtime : CTX.SameRuntime (insertRebaseWorld insᵖ W ok) Wᵖ⁺
  runtime =
    CTX.same-runtime
      (trans (sourceStore-kept insᵖ)
        (trans
          (CTX.SameRuntime.sourceStore-same
            (CTX.RebaseAt.sameRuntime rb))
          (sym (sourceStore-kept ins))))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵖ⁺) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ (insertRebaseWorld insᵖ W ok)) Y
  off-left {Y} Y≢ =
    trans (source-insert insᵖ Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (source-insert ins Y)))

  frozen-target : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ Wᵖ⁺) Y
      ≡ toRenameᵗ
          (CTX.ηᴿʷ (insertRebaseWorld insᵖ W ok)) Y
  frozen-target Y = refl

  aligned : toRenameᵗ (CTX.ηᴸʷ Wᵖ⁺) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵖ⁺) (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (source-insert insᵖ Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (sym (target-insert insᵖ Xᴿ)))

  reps : CTX.StoreRepImp Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert insᵖ (CTX.RebaseAt.storeRepresentations rb)

pullbackReverseRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → (ok : RebaseInsertOK {Wᵖ = W} insᵖ)
  → CTX.RebaseAt Wᵖ⁺ (insertRebaseWorld insᵖ W ok)
      Xᴸ (toRenameᵗ ρ Xᴿ)
pullbackReverseRebaseAt
    {ρ = ρ} {π = π} {W = W} {Wᵖ = Wᵖ} {Wᵖ⁺ = Wᵖ⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} insᵖ rb ok =
  CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  ins = insertRebaseTargetInsert insᵖ ok

  runtime : CTX.SameRuntime Wᵖ⁺ (insertRebaseWorld insᵖ W ok)
  runtime =
    CTX.same-runtime
      (trans (sourceStore-kept ins)
        (trans
          (CTX.SameRuntime.sourceStore-same
            (CTX.RebaseAt.sameRuntime rb))
          (sym (sourceStore-kept insᵖ))))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ (insertRebaseWorld insᵖ W ok)) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ Wᵖ⁺) Y
  off-left {Y} Y≢ =
    trans (source-insert ins Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (source-insert insᵖ Y)))

  frozen-target : ∀ Y
    → toRenameᵗ
        (CTX.ηᴿʷ (insertRebaseWorld insᵖ W ok)) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵖ⁺) Y
  frozen-target Y = refl

  aligned : toRenameᵗ
      (CTX.ηᴸʷ (insertRebaseWorld insᵖ W ok)) Xᴸ
      ≡ toRenameᵗ
          (CTX.ηᴿʷ (insertRebaseWorld insᵖ W ok))
          (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (source-insert ins Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (sym (target-insert ins Xᴿ)))

  reps : CTX.StoreRepImp (insertRebaseWorld insᵖ W ok)
      Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert ins (CTX.RebaseAt.storeRepresentations rb)

TargetInsertProvenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (W′ : World Δᴸ Δᴿ′ Δ′)
  → (ins : TargetInsert ρ π W W′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Set
TargetInsertProvenance W⁺ ins (CTI2.x⊑x² x∈) = ⊤
TargetInsertProvenance W⁺ ins (CTI2.ƛ⊑ƛ² M⊑M′) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins (CTI2.·⊑·² L⊑L′ M⊑M′) =
  TargetInsertProvenance W⁺ ins L⊑L′
    × TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
  TargetInsertProvenance
    (CTX.liftWorldBoth X⊑X W⁺)
    (liftBothTargetInsert {v = X⊑X} ins) V⊑V′
TargetInsertProvenance W⁺ ins
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  TargetInsertProvenance
    (CTX.liftWorldLeft W⁺)
    (liftLeftTargetInsert {v = X⊑★} ins) V⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.Λ⊑²-smart-comma Anv zero∈A
      (CTX.smart-merge-alias guard) liftγ vV M′⊢ V⊑M′ q) =
  ⊤
TargetInsertProvenance W⁺ ins
    (CTI2.Λ⊑²-smart-comma Anv zero∈A
      (CTX.smart-fresh-behind guard) liftγ vV M′⊢ V⊑M′ q) =
  TargetInsertProvenance (smartFreshInsertWorld ins guard)
    (smartFreshTargetInsert ins guard) V⊑M′
TargetInsertProvenance W⁺ ins (CTI2.•⊑•² p∀ M⊑M′ q r) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins (CTI2.•⊑² p∀ M⊑M′ q r) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins (CTI2.κ⊑κ² κ p) = ⊤
TargetInsertProvenance W⁺ ins (CTI2.cast⊑cast² c c′ M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins (CTI2.⊑cast² c′ M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.⊑reveal² c′⊢ at-absent M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.⊑conceal² c′⊢ at-absent M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins (CTI2.cast⊑² c M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.reveal⊑-neutral² c⊢ at-absent M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.reveal⊑-only² c⊢ not-absent dynamic disaligned
      represented M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance
    {Δᴸ = Δᴸ} {Δᴿ′ = Δᴿ′} {Δ′ = Δ′}
    {ρ = ρ} {π = π} W⁺ ins
    (CTI2.reveal⊑² {W′ = Wᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
      c⊢ not-absent Xᴿ∈ represented mono rb sc M⊑M′ q) =
  Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ insᵖ ∈ TargetInsert ρ π Wᵖ Wᵖ⁺ ]
      (CTX.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
      × TargetInsertProvenance Wᵖ⁺ insᵖ M⊑M′)
TargetInsertProvenance W⁺ ins
    (CTI2.conceal⊑-neutral² c⊢ at-absent M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance W⁺ ins
    (CTI2.conceal⊑² c⊢ not-absent dynamic disaligned
      represented M⊑M′ q) =
  TargetInsertProvenance W⁺ ins M⊑M′
TargetInsertProvenance
    {Δᴸ = Δᴸ} {Δᴿ′ = Δᴿ′} {Δ′ = Δ′}
    {ρ = ρ} {π = π} W⁺ ins
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
      c⊢ c′⊢ positions not-absent represented mono rb sc M⊑M′ q) =
  Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ insᵖ ∈ TargetInsert ρ π Wᵖ Wᵖ⁺ ]
      (CTX.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
      × TargetInsertProvenance Wᵖ⁺ insᵖ M⊑M′)
TargetInsertProvenance
    {Δᴸ = Δᴸ} {Δᴿ′ = Δᴿ′} {Δ′ = Δ′}
    {ρ = ρ} {π = π} W⁺ ins
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
      c⊢ c′⊢ positions not-absent represented mono rb sc M⊑M′ q) =
  Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ insᵖ ∈ TargetInsert ρ π Wᵖ Wᵖ⁺ ]
      (CTX.RebaseAt Wᵖ⁺ W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
      × TargetInsertProvenance Wᵖ⁺ insᵖ M⊑M′)
TargetInsertProvenance W⁺ ins (CTI2.blame⊑² M′⊢ p) = ⊤
TargetInsertProvenance W⁺ ins (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
  TargetInsertProvenance W⁺ ins L⊑L′
    × TargetInsertProvenance W⁺ ins M⊑M′

TargetExtendOPEᵀ : Set
TargetExtendOPEᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (W′ : World Δᴸ Δᴿ′ Δ′)
  → (ins : TargetInsert ρ π W W′)
  → (M⊑M′ : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → TargetInsertProvenance W′ ins M⊑M′
  → W′ ∣ mapCtxᵀ ins γ
      ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ transport⊑ᵂ ins p

RebaseAtᴸInsertCommuteᵀ : Set
RebaseAtᴸInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?

TagRebaseAtᴸInsertCommuteᵀ : Set
TagRebaseAtᴸInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.TagRebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)

RebaseAtInsertCommuteᵀ : Set
RebaseAtInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)

ImpEnvMonoInsertCommuteᵀ : Set
ImpEnvMonoInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W⁺
  → TargetInsert ρ π Wᵖ Wᵖ⁺
  → CTX.ImpEnvMono W Wᵖ
  → CTX.ImpEnvMono W⁺ Wᵖ⁺

insert-to-starᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
  → CTX.impEnvʷ W⁺ (toRenameᵗ (CTX.ηᴸʷ W⁺) Xᴸ) ≡ X⊑★
insert-to-starᴸ {W = W} {W⁺ = W⁺} {Xᴸ = Xᴸ} ins to-star =
  trans (cong (CTX.impEnvʷ W⁺) (source-insert ins Xᴸ))
    (trans (impEnv-insert ins (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))
      to-star)

insert-disalignedᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → (∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ′ → toRenameᵗ (CTX.ηᴿʷ W⁺) Xᴿ′
      ≢ toRenameᵗ (CTX.ηᴸʷ W⁺) Xᴸ
insert-disalignedᴸ ins disaligned Xᴿ′ eq
    with target-source-reflect ins (sym eq)
insert-disalignedᴸ ins disaligned Xᴿ′ eq
    | Xᴿ , xᴿ′-eq , aligned =
  disaligned Xᴿ (sym aligned)

insert-source-member : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Rᴸ : Ty Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.sourceStoreʷ W ∋ Xᴸ ⦂ Rᴸ
  → CTX.sourceStoreʷ W⁺ ∋ Xᴸ ⦂ Rᴸ
insert-source-member ins member =
  subst≡ (λ Σ → Σ ∋ _ ⦂ _) (sym (sourceStore-kept ins)) member

insertRebaseAtᴸ : RebaseAtᴸInsertCommuteᵀ
insertRebaseAtᴸ ins CTX.rebase-idᴸ ok =
  _ , ins , CTX.rebase-idᴸ
insertRebaseAtᴸ ins (CTX.rebase-varᴸ rb) ok
    with insertRebaseAt ins rb ok
insertRebaseAtᴸ ins (CTX.rebase-varᴸ rb) ok
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.rebase-varᴸ rb⁺
insertRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ}
      member to-star disaligned represented) ok =
  W⁺ , ins ,
    CTX.rebase-onlyᴸ
      (insert-source-member ins member)
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (transport⊑ᵂ ins represented)

insertTagRebaseAtᴸ : TagRebaseAtᴸInsertCommuteᵀ
insertTagRebaseAtᴸ ins CTX.tag-rebase-idᴸ ok =
  _ , ins , CTX.tag-rebase-idᴸ
insertTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb) ok
    with insertRebaseAt ins rb ok
insertTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb) ok
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.tag-rebase-varᴸ rb⁺
insertTagRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      member to-star disaligned represented) ok =
  W⁺ , ins ,
    CTX.tag-rebase-onlyᴸ
      (insert-source-member ins member)
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (transport⊑ᵂ ins represented)

pullbackRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
  → RebaseInsertOK {Wᵖ = W} insᵖ
  → Σ[ W⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π W W⁺ ×
      CTX.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?
pullbackRebaseAtᴸInsert insᵖ CTX.rebase-idᴸ ok =
  _ , insᵖ , CTX.rebase-idᴸ
pullbackRebaseAtᴸInsert {W = W} insᵖ (CTX.rebase-varᴸ rb) ok =
  insertRebaseWorld insᵖ W ok ,
  insertRebaseTargetInsert insᵖ ok ,
  CTX.rebase-varᴸ (pullbackRebaseAt insᵖ rb ok)
pullbackRebaseAtᴸInsert {Wᵖ⁺ = Wᵖ⁺} insᵖ
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ}
      member to-star disaligned represented) ok =
  Wᵖ⁺ , insᵖ ,
    CTX.rebase-onlyᴸ
      (insert-source-member insᵖ member)
      (insert-to-starᴸ insᵖ to-star)
      (insert-disalignedᴸ insᵖ disaligned)
      (transport⊑ᵂ insᵖ represented)

pullbackTagRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → RebaseInsertOK {Wᵖ = W} insᵖ
  → Σ[ W⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π W W⁺ ×
      CTX.TagRebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)
pullbackTagRebaseAtᴸInsert insᵖ CTX.tag-rebase-idᴸ ok =
  _ , insᵖ , CTX.tag-rebase-idᴸ
pullbackTagRebaseAtᴸInsert {W = W} insᵖ
    (CTX.tag-rebase-varᴸ rb) ok =
  insertRebaseWorld insᵖ W ok ,
  insertRebaseTargetInsert insᵖ ok ,
  CTX.tag-rebase-varᴸ (pullbackReverseRebaseAt insᵖ rb ok)
pullbackTagRebaseAtᴸInsert {Wᵖ⁺ = Wᵖ⁺} insᵖ
    (CTX.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      member to-star disaligned represented) ok =
  Wᵖ⁺ , insᵖ ,
    CTX.tag-rebase-onlyᴸ
      (insert-source-member insᵖ member)
      (insert-to-starᴸ insᵖ to-star)
      (insert-disalignedᴸ insᵖ disaligned)
      (transport⊑ᵂ insᵖ represented)

reverseRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAtᴸ Wᵖ W Xᴸ?)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
reverseRebaseAtᴸ ins CTX.rebase-idᴸ ok =
  _ , ins , CTX.rebase-idᴸ
reverseRebaseAtᴸ ins (CTX.rebase-varᴸ rb) ok
    with reverseRebaseAt ins rb ok
reverseRebaseAtᴸ ins (CTX.rebase-varᴸ rb) ok
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.rebase-varᴸ rb⁺
reverseRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ}
      member to-star disaligned represented) ok =
  W⁺ , ins ,
    CTX.rebase-onlyᴸ
      (insert-source-member ins member)
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (transport⊑ᵂ ins represented)

reverseTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → RebaseInsertOK {Wᵖ = Wᵖ} ins
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.TagRebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)
reverseTagRebaseAtᴸ ins CTX.tag-rebase-idᴸ ok =
  _ , ins , CTX.tag-rebase-idᴸ
reverseTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb) ok
    with reverseRebaseAt ins rb ok
reverseTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb) ok
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.tag-rebase-varᴸ rb⁺
reverseTagRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      member to-star disaligned represented) ok =
  W⁺ , ins ,
    CTX.tag-rebase-onlyᴸ
      (insert-source-member ins member)
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (transport⊑ᵂ ins represented)

impEnvMono-insert-pre : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.ImpEnvMono W Wᵖ
  → (Z′ : TyVar Δ′)
  → CTX.impEnvʷ W⁺ Z′ ≡ X⊑★
  → (m : Maybe (TyVar Δ))
  → preimage? π Z′ ≡ m
  → CTX.impEnvʷ Wᵖ⁺ Z′ ≡ X⊑★
impEnvMono-insert-pre {π = π} {W = W} {W⁺ = W⁺} {Wᵖ⁺ = Wᵖ⁺}
    ins insᵖ mono Z′ star (just Z) pre =
  trans (cong (CTX.impEnvʷ Wᵖ⁺) image-eq)
    (trans (impEnv-insert insᵖ Z)
      (CTX.dynamic-preserved mono Z old-star))
  where
  image-eq : Z′ ≡ toRenameᵗ π Z
  image-eq = preimage?-sound π pre

  image-star : CTX.impEnvʷ W⁺ (toRenameᵗ π Z) ≡ X⊑★
  image-star =
    trans (sym (cong (CTX.impEnvʷ W⁺) image-eq)) star

  old-star : CTX.impEnvʷ W Z ≡ X⊑★
  old-star =
    trans (sym (impEnv-insert ins Z)) image-star
impEnvMono-insert-pre ins insᵖ mono Z′ star nothing pre =
  impEnv-off-insert insᵖ pre

impEnvPrecise-insert-pre : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.ImpEnvMono W Wᵖ
  → (Z′ : TyVar Δ′)
  → CTX.impEnvʷ W⁺ Z′ ≡ X⊑X
  → (m : Maybe (TyVar Δ))
  → preimage? π Z′ ≡ m
  → CTX.impEnvʷ Wᵖ⁺ Z′ ≡ X⊑X
impEnvPrecise-insert-pre
    {π = π} {W = W} {W⁺ = W⁺} {Wᵖ⁺ = Wᵖ⁺}
    ins insᵖ mono Z′ precise (just Z) pre =
  trans (cong (CTX.impEnvʷ Wᵖ⁺) image-eq)
    (trans (impEnv-insert insᵖ Z)
      (CTX.precise-preserved mono Z old-precise))
  where
  image-eq : Z′ ≡ toRenameᵗ π Z
  image-eq = preimage?-sound π pre

  image-precise : CTX.impEnvʷ W⁺ (toRenameᵗ π Z) ≡ X⊑X
  image-precise =
    trans (sym (cong (CTX.impEnvʷ W⁺) image-eq)) precise

  old-precise : CTX.impEnvʷ W Z ≡ X⊑X
  old-precise = trans (sym (impEnv-insert ins Z)) image-precise
impEnvPrecise-insert-pre ins insᵖ mono Z′ precise nothing pre
    with trans (sym (impEnv-off-insert ins pre)) precise
impEnvPrecise-insert-pre ins insᵖ mono Z′ precise nothing pre | ()

impEnvMono-insert : ImpEnvMonoInsertCommuteᵀ
impEnvMono-insert {π = π} ins insᵖ mono =
  CTX.imp-env-mono dynamic precise
  where
  dynamic = λ Z′ star →
    impEnvMono-insert-pre ins insᵖ mono Z′ star (preimage? π Z′) refl
  precise = λ Z′ mark →
    impEnvPrecise-insert-pre ins insᵖ mono Z′ mark
      (preimage? π Z′) refl

------------------------------------------------------------------------
-- Rebasing evidence across one root right bind
------------------------------------------------------------------------

right-target-map : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ)
  → ∀ Y
  → toRenameᵗ (keep η) (toRenameᵗ wk↪ᵗ Y)
      ≡ Fin.suc (toRenameᵗ η Y)
right-target-map η Y =
  cong (toRenameᵗ (keep η)) (toRename-wk-eq Y)

right-bind-transport⊑ᵂᵀ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ CTX.rightOnlyWorld W B′ fresh ⟩
      renameᵗ (toRenameᵗ wk↪ᵗ) B
right-bind-transport⊑ᵂᵀ
    {W = W} {B′ = B′} {fresh = fresh} {A = A} {B = B} p =
  subst≡
    (λ C → A ⊑ᵂ⟨ CTX.rightOnlyWorld W B′ fresh ⟩ C)
    (sym (renameᵗ-wk-eq B))
    (right-bind-⊑ᵂ {W = W} {B′ = B′} {fresh = fresh} p)

right-bind-align : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B} {Xᴸ Xᴿ}
  → CTX.CenterAligned W Xᴸ Xᴿ
  → CTX.CenterAligned (CTX.rightOnlyWorld W B fresh)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-bind-align {W = W} {Xᴿ = Xᴿ} aligned =
  trans (cong Fin.suc aligned)
    (sym (right-target-map (CTX.ηᴿʷ W) Xᴿ))

right-bind-source-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Xᴸ
  → toRenameᵗ
      (CTX.ηᴸʷ (CTX.rightOnlyWorld W B fresh)) Xᴸ
      ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
right-bind-source-insert {W = W} Xᴸ =
  sym (toRename-wk-eq (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))

right-bind-target-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Xᴿ
  → toRenameᵗ
      (CTX.ηᴿʷ (CTX.rightOnlyWorld W B fresh))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)
right-bind-target-insert {W = W} Xᴿ =
  trans (right-target-map (CTX.ηᴿʷ W) Xᴿ)
    (sym (toRename-wk-eq (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)))

right-bind-impEnv-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Z
  → CTX.impEnvʷ (CTX.rightOnlyWorld W B fresh)
      (toRenameᵗ wk↪ᵗ Z)
      ≡ CTX.impEnvʷ W Z
right-bind-impEnv-insert Z
    rewrite toRename-id-eq Z =
  refl

right-bind-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
    {Z′ : TyVar (Nat.suc Δ)}
  → preimage? wk↪ᵗ Z′ ≡ nothing
  → CTX.impEnvʷ (CTX.rightOnlyWorld W B fresh) Z′ ≡ X⊑★
right-bind-impEnv-off-insert {Z′ = Fin.zero} eq = refl
right-bind-impEnv-off-insert {Z′ = Fin.suc Z′} eq
    rewrite preimage-id↪ Z′ =
  ⊥-elim (just≢nothing eq)

right-bind-target-center-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B} {Y′ Z}
  → toRenameᵗ
      (CTX.ηᴿʷ (CTX.rightOnlyWorld W B fresh)) Y′
      ≡ toRenameᵗ wk↪ᵗ Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ wk↪ᵗ Y ×
      toRenameᵗ (CTX.ηᴿʷ W) Y ≡ Z
right-bind-target-center-reflect {Y′ = Fin.zero} {Z = Z} eq =
  ⊥-elim (zero≢suc (trans eq (toRename-wk-eq Z)))
right-bind-target-center-reflect {Y′ = Fin.suc Y} {Z = Z} eq =
  Y , sym (toRename-wk-eq Y) ,
    fin-suc-injective (trans eq (toRename-wk-eq Z))

right-bind-target-source-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B} {Xᴸ Y′}
  → CTX.CenterAligned (CTX.rightOnlyWorld W B fresh) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ wk↪ᵗ Y × CTX.CenterAligned W Xᴸ Y
right-bind-target-source-reflect {Y′ = Fin.zero} ()
right-bind-target-source-reflect {Y′ = Fin.suc Y} aligned =
  Y , sym (toRename-wk-eq Y) , fin-suc-injective aligned

right-resolveVar-map : ∀ {Δ} (Σ : TyStore Δ) (B : Ty Δ)
  → ∀ Y
  → CTX.resolveVar (TyStore.store-bind Σ B) (toRenameᵗ wk↪ᵗ Y)
      ≡ ⇑ᵗ (CTX.resolveVar Σ Y)
right-resolveVar-map Σ B Y =
  cong (CTX.resolveVar (TyStore.store-bind Σ B)) (toRename-wk-eq Y)

right-bind-source-resolve : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Xᴸ
  → CTX.resolveVar
      (CTX.sourceStoreʷ (CTX.rightOnlyWorld W B fresh)) Xᴸ
      ≡ CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
right-bind-source-resolve Xᴸ = refl

right-bind-target-resolve : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Xᴿ
  → CTX.resolveVar
      (CTX.targetStoreʷ (CTX.rightOnlyWorld W B fresh))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ renameᵗ (toRenameᵗ wk↪ᵗ)
          (CTX.resolveVar (CTX.targetStoreʷ W) Xᴿ)
right-bind-target-resolve {W = W} {B = B} Xᴿ =
  trans (right-resolveVar-map (CTX.targetStoreʷ W) B Xᴿ)
    (sym (renameᵗ-wk-eq (CTX.resolveVar (CTX.targetStoreʷ W) Xᴿ)))

right-bind-targetLookup-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Xᴿ
  → lookupStore
      (CTX.targetStoreʷ (CTX.rightOnlyWorld W B fresh))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ renameᵗ (toRenameᵗ wk↪ᵗ)
          (lookupStore (CTX.targetStoreʷ W) Xᴿ)
right-bind-targetLookup-insert {W = W} {B = B} {fresh = fresh} Xᴿ =
  trans
    (cong (lookupStore
      (CTX.targetStoreʷ (CTX.rightOnlyWorld W B fresh)))
      (toRename-wk-eq Xᴿ))
    (sym (renameᵗ-wk-eq
      (lookupStore (CTX.targetStoreʷ W) Xᴿ)))

right-bind-targetLookup-off : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B}
  → ∀ Xᴿ′
  → preimage? wk↪ᵗ
      (toRenameᵗ
        (CTX.ηᴿʷ (CTX.rightOnlyWorld W B fresh)) Xᴿ′)
      ≡ nothing
  → lookupStore
      (CTX.targetStoreʷ (CTX.rightOnlyWorld W B fresh)) Xᴿ′
      ≡ ★
    ⊎ Σ[ Yᴿ′ ∈ TyVar (Nat.suc Δᴿ) ]
        (lookupStore
          (CTX.targetStoreʷ (CTX.rightOnlyWorld W B fresh)) Xᴿ′
          ≡ ＇ Yᴿ′)
      × (∀ Xᴸ
          → CTX.CenterAligned
              (CTX.rightOnlyWorld W B fresh) Xᴸ Yᴿ′
          → ⊥)
right-bind-targetLookup-off {fresh = fresh} Fin.zero off = fresh
right-bind-targetLookup-off {W = W} (Fin.suc Xᴿ) off
    rewrite preimage-id↪ (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ) =
  ⊥-elim (just≢nothing off)

rightBindTargetInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → (fresh : CTX.RightBindFresh W B)
  → TargetInsert wk↪ᵗ wk↪ᵗ W
      (CTX.rightOnlyWorld W B fresh)
rightBindTargetInsert {W = W} {B = B} fresh = target-insert-view record
  { sourceStore-kept = refl
  ; transport⊑ᵂ = λ p →
      right-bind-transport⊑ᵂᵀ
        {W = W} {B′ = B} {fresh = fresh} p
  ; targetStore-rename = StoreRename-wk-bind {C = B}
  ; source-resolve =
      right-bind-source-resolve {W = W} {B = B} {fresh = fresh}
  ; target-resolve =
      right-bind-target-resolve {W = W} {B = B} {fresh = fresh}
  ; align-insert = λ aligned →
      right-bind-align {W = W} {B = B} {fresh = fresh} aligned
  ; source-insert =
      right-bind-source-insert {W = W} {B = B} {fresh = fresh}
  ; target-insert =
      right-bind-target-insert {W = W} {B = B} {fresh = fresh}
  ; impEnv-insert =
      right-bind-impEnv-insert {W = W} {B = B} {fresh = fresh}
  ; impEnv-off-insert =
      λ {Z′} eq →
        right-bind-impEnv-off-insert
          {W = W} {B = B} {fresh = fresh} {Z′ = Z′} eq
  ; target-center-reflect =
      right-bind-target-center-reflect
        {W = W} {B = B} {fresh = fresh}
  ; target-source-reflect =
      right-bind-target-source-reflect
        {W = W} {B = B} {fresh = fresh}
  ; targetLookup-insert =
      right-bind-targetLookup-insert
        {W = W} {B = B} {fresh = fresh}
  ; targetLookup-off =
      right-bind-targetLookup-off
        {W = W} {B = B} {fresh = fresh}
  }

rightBindTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → (fresh : CTX.RightBindFresh W B)
  → TargetWindowInsert
      (rightBindTargetInsert {W = W} {B = B} fresh) id↪ᵗ
rightBindTargetWindowInsert fresh = record
  { windowEmbedding = window-here
  ; window-zero = refl
  ; window-old = λ Z → refl
  }

smartFreshRightBindTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {B : Ty Δᴿ}
  → (fresh : CTX.RightBindFresh W B)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetWindowInsert
      (smartFreshTargetInsert
        (rightBindTargetInsert fresh) guard)
      (rightPushoutWindow
        (CTX.SmartFreshBehindGuard.oldCenters guard))
smartFreshRightBindTargetWindowInsert fresh guard =
  record
    { windowEmbedding = window-here
    ; window-zero = refl
    ; window-old = λ Z → refl
    }

keepRightBindTargetInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {v : VarImp}
  → (fresh : CTX.RightBindFresh W B)
  → TargetInsert (keep wk↪ᵗ) (keep wk↪ᵗ)
      (CTX.liftWorldBoth v W)
      (CTX.liftWorldBoth v (CTX.rightOnlyWorld W B fresh))
keepRightBindTargetInsert {v = v} fresh =
  liftBothTargetInsert {v = v} (rightBindTargetInsert fresh)

right-storeRep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B} {Xᴸ Xᴿ}
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp (CTX.rightOnlyWorld W B fresh)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-storeRep
    {W = W} {B = B} {fresh = fresh} {Xᴿ = Xᴿ}
    (CTX.store-rep-imp represented) =
  CTX.store-rep-imp
    (subst≡
      (λ R → CTX.resolveVar (CTX.sourceStoreʷ W) _
        ⊑ᵂ⟨ CTX.rightOnlyWorld W B fresh ⟩ R)
      (sym (right-resolveVar-map (CTX.targetStoreʷ W) B Xᴿ))
      (right-bind-⊑ᵂ
        {W = W} {B′ = B} {fresh = fresh} represented))

rightRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → (fresh : CTX.RightBindFresh W B)
  → (fresh′ : CTX.RightBindFresh W′ B)
  → CTX.RebaseAt W W′ Xᴸ Xᴿ
  → CTX.RebaseAt (CTX.rightOnlyWorld W B fresh)
      (CTX.rightOnlyWorld W′ B fresh′)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
rightRebaseAt {W = W} {W′ = W′} {B = B} {Xᴸ = Xᴸ}
    {Xᴿ = Xᴿ} fresh fresh′
    (CTX.rebase-at
      (CTX.same-runtime source-eq target-eq)
      offL frozenR aligned reps) =
  CTX.rebase-at
    (CTX.same-runtime source-eq
      (cong (λ Σ → TyStore.store-bind Σ B) target-eq))
    (λ Y≢ → cong Fin.suc (offL Y≢))
    frozenR′
    (trans (cong Fin.suc aligned)
      (sym (right-target-map (CTX.ηᴿʷ W′) Xᴿ)))
    (right-storeRep {fresh = fresh′} reps)
  where
  frozenR′ : ∀ Y
    → toRenameᵗ
        (CTX.ηᴿʷ (CTX.rightOnlyWorld W′ B fresh′)) Y
      ≡ toRenameᵗ
          (CTX.ηᴿʷ (CTX.rightOnlyWorld W B fresh)) Y
  frozenR′ Fin.zero = refl
  frozenR′ (Fin.suc Y) = cong Fin.suc (frozenR Y)

right-disaligned : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) {B : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B} {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ
  → toRenameᵗ
      (CTX.ηᴿʷ (CTX.rightOnlyWorld W B fresh)) Xᴿ
      ≢ toRenameᵗ
          (CTX.ηᴸʷ (CTX.rightOnlyWorld W B fresh)) Xᴸ
right-disaligned W disaligned Fin.zero ()
right-disaligned W disaligned (Fin.suc Xᴿ) eq =
  disaligned Xᴿ (fin-suc-injective eq)

------------------------------------------------------------------------
-- Retargeting derivations
------------------------------------------------------------------------

mapCtxᴿ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → ECR.mapCtxᴿ ext γ CTX.∋ʷ x ⦂
      CTX.ctx-imp A (χs Reduction.▶ᵗ B) (ECR.transport⊑ᵂ ext p)
mapCtxᴿ-∋ ext CTX.Zʷ = CTX.Zʷ
mapCtxᴿ-∋ ext (CTX.Sʷ x∈) = CTX.Sʷ (mapCtxᴿ-∋ ext x∈)

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d

⊢²-retargetᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B C : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ C}
  → B ≡ C
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retargetᴿ refl d = ⊢²-retarget d

source-reveal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTX.sourceStoreʷ W Conv.⊢↑[ X ⦂ R ] c
  → CTX.sourceStoreʷ W′ Conv.⊢↑[ X ⦂ R ] c
source-reveal-insert ins c⊢ =
  subst≡ (λ Σ → Σ Conv.⊢↑[ _ ⦂ _ ] _)
    (sym (sourceStore-kept ins)) c⊢

source-conceal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTX.sourceStoreʷ W Conv.⊢↓[ X ⦂ R ] c
  → CTX.sourceStoreʷ W′ Conv.⊢↓[ X ⦂ R ] c
source-conceal-insert ins c⊢ =
  subst≡ (λ Σ → Σ Conv.⊢↓[ _ ⦂ _ ] _)
    (sym (sourceStore-kept ins)) c⊢

source-reveal-insert-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ} {c : Conv↑ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → (c⊢ : CTX.sourceStoreʷ W Conv.⊢↑[ X ⦂ R ] c)
  → (P : GeneratorPosition)
  → revealGeneratorPosition c⊢ ≡ P
  → revealGeneratorPosition (source-reveal-insert ins c⊢) ≡ P
source-reveal-insert-position ins c⊢ P eq =
  trans
    (revealGeneratorPosition-store-transport
      (sym (sourceStore-kept ins)) c⊢)
    eq

source-conceal-insert-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ} {c : Conv↓ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → (c⊢ : CTX.sourceStoreʷ W Conv.⊢↓[ X ⦂ R ] c)
  → (P : GeneratorPosition)
  → concealGeneratorPosition c⊢ ≡ P
  → concealGeneratorPosition (source-conceal-insert ins c⊢) ≡ P
source-conceal-insert-position ins c⊢ P eq =
  trans
    (concealGeneratorPosition-store-transport
      (sym (sourceStore-kept ins)) c⊢)
    eq

mutual
  reveal-rename-position : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X R A B}
      {c : Conv↑ Δ A B}
    → (injective : ∀ {Y Z} → rho Y ≡ rho Z → Y ≡ Z)
    → (hΣ : StoreRename rho Σ Σ′)
    → (c⊢ : Σ Conv.⊢↑[ X ⦂ R ] c)
    → revealGeneratorPosition (reveal-renameᵗ injective hΣ c⊢)
      ≡ revealGeneratorPosition c⊢
  reveal-rename-position injective hΣ (Conv.⊢↑-unseal X∈) = refl
  reveal-rename-position injective hΣ (Conv.⊢↑-⇒ c⊢ d⊢)
    rewrite conceal-rename-position injective hΣ c⊢
      | reveal-rename-position injective hΣ d⊢ =
    refl
  reveal-rename-position injective hΣ (Conv.⊢↑-∀ eq c⊢)
    rewrite reveal-rename-position (ext-injective injective)
      (StoreRename-ext hΣ) c⊢ =
    refl
  reveal-rename-position injective hΣ (Conv.⊢↑-id-var X∈ X≢Y) = refl
  reveal-rename-position injective hΣ (Conv.⊢↑-id-base X∈) = refl
  reveal-rename-position injective hΣ (Conv.⊢↑-id-star X∈) = refl

  conceal-rename-position : ∀ {Δ Δ′} {rho : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X R A B}
      {c : Conv↓ Δ A B}
    → (injective : ∀ {Y Z} → rho Y ≡ rho Z → Y ≡ Z)
    → (hΣ : StoreRename rho Σ Σ′)
    → (c⊢ : Σ Conv.⊢↓[ X ⦂ R ] c)
    → concealGeneratorPosition (conceal-renameᵗ injective hΣ c⊢)
      ≡ concealGeneratorPosition c⊢
  conceal-rename-position injective hΣ (Conv.⊢↓-seal X∈) = refl
  conceal-rename-position injective hΣ (Conv.⊢↓-⇒ c⊢ d⊢)
    rewrite reveal-rename-position injective hΣ c⊢
      | conceal-rename-position injective hΣ d⊢ =
    refl
  conceal-rename-position injective hΣ (Conv.⊢↓-∀ eq c⊢)
    rewrite conceal-rename-position (ext-injective injective)
      (StoreRename-ext hΣ) c⊢ =
    refl
  conceal-rename-position injective hΣ (Conv.⊢↓-id-var X∈ X≢Y) = refl
  conceal-rename-position injective hΣ (Conv.⊢↓-id-base X∈) = refl
  conceal-rename-position injective hΣ (Conv.⊢↓-id-star X∈) = refl

target-reveal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ} {c : Conv↑ Δᴿ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTX.targetStoreʷ W Conv.⊢↑[ X ⦂ R ] c
  → CTX.targetStoreʷ W′ Conv.⊢↑[
      toRenameᵗ ρ X ⦂ renameᵗ (toRenameᵗ ρ) R ]
      Conv.rename↑ (toRenameᵗ ρ) c
target-reveal-insert {ρ = ρ} ins c⊢ =
  reveal-renameᵗ (toRenameᵗ-injective ρ) (targetStore-rename ins) c⊢

target-conceal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ} {c : Conv↓ Δᴿ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTX.targetStoreʷ W Conv.⊢↓[ X ⦂ R ] c
  → CTX.targetStoreʷ W′ Conv.⊢↓[
      toRenameᵗ ρ X ⦂ renameᵗ (toRenameᵗ ρ) R ]
      Conv.rename↓ (toRenameᵗ ρ) c
target-conceal-insert {ρ = ρ} ins c⊢ =
  conceal-renameᵗ (toRenameᵗ-injective ρ) (targetStore-rename ins) c⊢

target-reveal-insert-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ} {c : Conv↑ Δᴿ A B}
  → (ins : TargetInsert ρ π W W′)
  → (c⊢ : CTX.targetStoreʷ W Conv.⊢↑[ X ⦂ R ] c)
  → (P : GeneratorPosition)
  → revealGeneratorPosition c⊢ ≡ P
  → revealGeneratorPosition (target-reveal-insert ins c⊢) ≡ P
target-reveal-insert-position {ρ = ρ} ins c⊢ P eq =
  trans
    (reveal-rename-position (toRenameᵗ-injective ρ)
      (targetStore-rename ins) c⊢)
    eq

target-conceal-insert-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ} {c : Conv↓ Δᴿ A B}
  → (ins : TargetInsert ρ π W W′)
  → (c⊢ : CTX.targetStoreʷ W Conv.⊢↓[ X ⦂ R ] c)
  → (P : GeneratorPosition)
  → concealGeneratorPosition c⊢ ≡ P
  → concealGeneratorPosition (target-conceal-insert ins c⊢) ≡ P
target-conceal-insert-position {ρ = ρ} ins c⊢ P eq =
  trans
    (conceal-rename-position (toRenameᵗ-injective ρ)
      (targetStore-rename ins) c⊢)
    eq

target-typing-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {M : Term Δᴿ} {B : Ty Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ′ , CTX.targetStoreʷ W′ ,
        CTX.tgtCtxʷ (mapCtxᵀ ins γ) ⟩
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) B
target-typing-insert {ρ = ρ} {γ = γ} ins M⊢ =
  subst≡
    (λ Γ → ⟨ _ , _ , Γ ⟩
      ⊢ renameᵗᵐ ρ _ ⦂ renameᵗ (toRenameᵗ ρ) _)
    (sym (mapCtxᵀ-tgt ins γ))
    (typing-renameᵗ (targetStore-rename ins) M⊢)

rename-open↪ᵗ : ∀ {Δ Δ′}
    (ρ : Δ ↪ᵗ Δ′) (C : Ty (Nat.suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (C [ A ]ᵗ)
      ≡ renameᵗ (toRenameᵗ (keep ρ)) C
          [ renameᵗ (toRenameᵗ ρ) A ]ᵗ
rename-open↪ᵗ ρ C A =
  trans (rename-openᵗ (toRenameᵗ ρ) C A)
    (cong (λ T → T [ renameᵗ (toRenameᵗ ρ) A ]ᵗ)
      (renameᵗ-cong C (λ X → sym (toRename-keep-eq ρ X))))

primArgTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) op
  → primArgTy {Δ′} op ≡ renameᵗ ρ (primArgTy {Δ} op)
primArgTy-renameᵗ ρ addℕ = refl
primArgTy-renameᵗ ρ and𝔹 = refl

primResultTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) op
  → primResultTy {Δ′} op ≡ renameᵗ ρ (primResultTy {Δ} op)
primResultTy-renameᵗ ρ addℕ = refl
primResultTy-renameᵗ ρ and𝔹 = refl

directStarOffTargetInsertProvenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ π W W⁺)
  → TargetInsertDirectStarOff ins
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → TargetInsertProvenance W⁺ ins rel
directStarOffTargetInsertProvenance ins dynamic (CTI2.x⊑x² x∈) = tt
directStarOffTargetInsertProvenance ins dynamic (CTI2.ƛ⊑ƛ² rel) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic (CTI2.·⊑·² rel₁ rel₂) =
  directStarOffTargetInsertProvenance ins dynamic rel₁ ,
  directStarOffTargetInsertProvenance ins dynamic rel₂
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  directStarOffTargetInsertProvenance
    (liftBothTargetInsert {v = X⊑X} ins)
    (liftBothTargetInsertDirectStarOff ins dynamic) rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ rel q) =
  directStarOffTargetInsertProvenance
    (liftLeftTargetInsert {v = X⊑★} ins)
    (liftLeftTargetInsertDirectStarOff {v = X⊑★} ins dynamic) rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.Λ⊑²-smart-comma Anv zero∈A
      (CTX.smart-merge-alias guard) liftγ vV M′⊢ rel q) =
  tt
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.Λ⊑²-smart-comma Anv zero∈A
      (CTX.smart-fresh-behind guard) liftγ vV M′⊢ rel q) =
  directStarOffTargetInsertProvenance
    (smartFreshTargetInsert ins guard)
    (smartFreshTargetInsertDirectStarOff ins guard dynamic) rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.•⊑•² p∀ rel q r) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.•⊑² p∀ rel q r) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic (CTI2.κ⊑κ² κ p) = tt
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.cast⊑cast² c c′ rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic (CTI2.⊑cast² c′ rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.⊑reveal² c′⊢ at-absent rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.⊑conceal² c′⊢ at-absent rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.cast⊑² c rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.reveal⊑-neutral² c⊢ at-absent rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.reveal⊑-only² c⊢ not-absent to-star disaligned represented
      rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.reveal⊑² c⊢ not-absent Xᴿ∈ represented mono rb sc rel q)
    with insertRebaseAt ins rb (directStarOffForwardInsertOK ins dynamic rb)
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.reveal⊑² c⊢ not-absent Xᴿ∈ represented mono rb sc rel q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , rb⁺ ,
  directStarOffTargetInsertProvenance insᵖ
    (targetInsertDirectStarOffForward ins insᵖ dynamic rb⁺) rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.conceal⊑-neutral² c⊢ at-absent rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.conceal⊑² c⊢ not-absent to-star disaligned represented
      rel q) =
  directStarOffTargetInsertProvenance ins dynamic rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.reveal⊑reveal² c⊢ c′⊢ positions not-absent represented
      mono rb sc rel q)
    with insertRebaseAt ins rb (directStarOffForwardInsertOK ins dynamic rb)
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.reveal⊑reveal² c⊢ c′⊢ positions not-absent represented
      mono rb sc rel q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , rb⁺ ,
  directStarOffTargetInsertProvenance insᵖ
    (targetInsertDirectStarOffForward ins insᵖ dynamic rb⁺) rel
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.conceal⊑conceal² c⊢ c′⊢ positions not-absent represented
      mono rb sc rel q)
    with reverseRebaseAt ins rb (directStarOffReverseInsertOK ins dynamic rb)
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.conceal⊑conceal² c⊢ c′⊢ positions not-absent represented
      mono rb sc rel q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , rb⁺ ,
  directStarOffTargetInsertProvenance insᵖ
    (targetInsertDirectStarOffReverse ins insᵖ dynamic rb⁺) rel
directStarOffTargetInsertProvenance ins dynamic (CTI2.blame⊑² M′⊢ p) = tt
directStarOffTargetInsertProvenance ins dynamic
    (CTI2.⊕⊑⊕² op rel₁ rel₂ r) =
  directStarOffTargetInsertProvenance ins dynamic rel₁ ,
  directStarOffTargetInsertProvenance ins dynamic rel₂

⊢²-target-insert : TargetExtendOPEᵀ
⊢²-target-insert W′ ins (CTI2.x⊑x² x∈) provenance =
  CTI2.x⊑x² (mapCtxᵀ-∋ ins x∈)
⊢²-target-insert {W = W} W′ ins
    (CTI2.ƛ⊑ƛ² {pA = pA} {pB = pB} M⊑M′) provenance =
  ⊢²-retarget
    (CTI2.ƛ⊑ƛ²
      (⊢²-target-insert W′ ins M⊑M′ provenance))
⊢²-target-insert {W = W} W′ ins
    (CTI2.·⊑·² {pA = pA} {pB = pB} L⊑L′ M⊑M′)
    (provenanceL , provenanceM) =
  CTI2.·⊑·²
    (⊢²-retarget (⊢²-target-insert W′ ins L⊑L′ provenanceL))
    (⊢²-target-insert W′ ins M⊑M′ provenanceM)
⊢²-target-insert {ρ = ρ} W′ ins
    (CTI2.Λ⊑Λ² {A = A} {B = B} {p = p}
      liftγ vV vV′ V⊑V′ q) provenance =
  ⊢²-retargetᴿ (cong `∀ body-eq)
    (CTI2.Λ⊑Λ² (targetLiftCtxBoth ins liftγ) vV
      (renameᵗᵐ-preserves-Value _ vV′)
      (⊢²-target-insert (CTX.liftWorldBoth X⊑X W′)
        (liftBothTargetInsert {v = X⊑X} ins)
        V⊑V′ provenance)
      q-keep)
  where
  body-eq : renameᵗ (toRenameᵗ (keep ρ)) B
      ≡ renameᵗ (extᵗ (toRenameᵗ ρ)) B
  body-eq = renameᵗ-cong B (toRename-keep-eq ρ)

  q-keep : `∀ A ⊑ᵂ⟨ W′ ⟩ `∀ (renameᵗ (toRenameᵗ (keep ρ)) B)
  q-keep =
    subst≡ (λ T → `∀ A ⊑ᵂ⟨ W′ ⟩ `∀ T)
      (sym body-eq) (transport⊑ᵂ ins q)
⊢²-target-insert {W = W} {γ = γ} W′ ins
    (CTI2.Λ⊑² {p = p} Anv zero∈A liftγ vV M′⊢ V⊑M′ q)
    provenance =
  CTI2.Λ⊑² Anv zero∈A (targetLiftCtxLeft ins liftγ) vV
    (target-typing-insert ins M′⊢)
    (⊢²-target-insert (CTX.liftWorldLeft W′)
      (liftLeftTargetInsert {v = X⊑★} ins)
      V⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {W = W} {γ = γ} W′ ins
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {p = p}
      Anv zero∈A (CTX.smart-merge-alias guard) liftγ vV M′⊢
      V⊑M′ q) provenance =
  ⊥-elim (smartAliasGuard-impossible guard)
⊢²-target-insert {W = W} {γ = γ} W′ ins
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {p = p}
      Anv zero∈A (CTX.smart-fresh-behind guard) liftγ vV M′⊢
      V⊑M′ q) provenance =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-fresh-behind (smartFreshGuardInsert ins guard))
    (targetSmartLiftCtxLeft ins (smartFreshTargetInsert ins guard) liftγ)
    vV (target-typing-insert ins M′⊢)
    (⊢²-target-insert (smartFreshInsertWorld ins guard)
      (smartFreshTargetInsert ins guard)
      V⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} W′ ins
    (CTI2.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
      p∀ M⊑M′ q r) provenance =
  ⊢²-retargetᴿ (sym open-eq)
    (CTI2.•⊑•² p∀-keep
      (⊢²-retargetᴿ (sym (cong `∀ body-eq))
        (⊢²-target-insert W′ ins M⊑M′ provenance))
      (transport⊑ᵂ ins q) r-open)
  where
  body-eq : renameᵗ (toRenameᵗ (keep ρ)) C′
      ≡ renameᵗ (extᵗ (toRenameᵗ ρ)) C′
  body-eq = renameᵗ-cong C′ (toRename-keep-eq ρ)

  open-eq = rename-open↪ᵗ ρ C′ A′

  p∀-keep : `∀ C ⊑ᵂ⟨ W′ ⟩
      `∀ (renameᵗ (toRenameᵗ (keep ρ)) C′)
  p∀-keep =
    subst≡ (λ T → `∀ C ⊑ᵂ⟨ W′ ⟩ `∀ T)
      (sym body-eq) (transport⊑ᵂ ins p∀)

  r-open : (C [ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩
      (renameᵗ (toRenameᵗ (keep ρ)) C′
        [ renameᵗ (toRenameᵗ ρ) A′ ]ᵗ)
  r-open =
    subst≡
      (λ T → (C [ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩ T)
      open-eq
      (transport⊑ᵂ ins r)
⊢²-target-insert {W = W} W′ ins
    (CTI2.•⊑² p∀ M⊑M′ q r) provenance =
  CTI2.•⊑² (transport⊑ᵂ ins p∀)
    (⊢²-target-insert W′ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q) (transport⊑ᵂ ins r)
⊢²-target-insert {ρ = ρ} W′ ins
    (CTI2.κ⊑κ² κ p) provenance =
  ⊢²-retargetᴿ const-eq (CTI2.κ⊑κ² κ p-const)
  where
  const-eq = constTy-renameᵗ (toRenameᵗ ρ) κ

  p-const =
    subst≡
      (λ T → constTy κ ⊑ᵂ⟨ W′ ⟩ T)
      (sym const-eq)
      (transport⊑ᵂ ins p)
⊢²-target-insert {ρ = ρ} W′ ins
    (CTI2.cast⊑cast² {p = p} c c′ M⊑M′ q) provenance =
  CTI2.cast⊑cast² c (renameᵐᶜ ρ c′)
    (⊢²-target-insert W′ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} W′ ins
    (CTI2.⊑cast² {p = p} c′ M⊑M′ q) provenance =
  CTI2.⊑cast² (renameᵐᶜ ρ c′)
    (⊢²-target-insert W′ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} W⁺ ins
    (CTI2.⊑reveal² {p = p} c′⊢ at-absent M⊑M′ q) provenance =
  CTI2.⊑reveal² (target-reveal-insert ins c′⊢)
    (target-reveal-insert-position ins c′⊢ generator-absent at-absent)
    (⊢²-target-insert W⁺ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} W⁺ ins
    (CTI2.⊑conceal² {p = p} c′⊢ at-absent M⊑M′ q) provenance =
  CTI2.⊑conceal² (target-conceal-insert ins c′⊢)
    (target-conceal-insert-position ins c′⊢ generator-absent at-absent)
    (⊢²-target-insert W⁺ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert W′ ins
    (CTI2.cast⊑² {p = p} c M⊑M′ q) provenance =
  CTI2.cast⊑² c
    (⊢²-target-insert W′ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert W⁺ ins
    (CTI2.reveal⊑-neutral² {p = p} c⊢ at-absent M⊑M′ q)
    provenance =
  CTI2.reveal⊑-neutral² (source-reveal-insert ins c⊢)
    (source-reveal-insert-position ins c⊢ generator-absent at-absent)
    (⊢²-target-insert W⁺ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert W⁺ ins
    (CTI2.reveal⊑-only² {p = p} c⊢ not-absent dynamic disaligned
      represented M⊑M′ q) provenance =
  CTI2.reveal⊑-only² (source-reveal-insert ins c⊢)
    (λ absent → not-absent
      (trans
        (sym (source-reveal-insert-position ins c⊢
          (revealGeneratorPosition c⊢) refl)) absent))
    (insert-to-starᴸ ins dynamic)
    (insert-disalignedᴸ ins disaligned)
    (transport⊑ᵂ ins represented)
    (⊢²-target-insert W⁺ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert W⁺ ins
    (CTI2.reveal⊑² {W′ = W′} {p = p}
      c⊢ not-absent Xᴿ∈ represented mono rb sc M⊑M′ q)
    (Wᵖ⁺ , insᵖ , rb⁺ , provenance) =
  CTI2.reveal⊑² (source-reveal-insert ins c⊢)
    (λ absent → not-absent
      (trans
        (sym (source-reveal-insert-position ins c⊢
          (revealGeneratorPosition c⊢) refl)) absent))
    (targetStore-rename ins Xᴿ∈)
    (transport⊑ᵂ insᵖ represented)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (⊢²-target-insert Wᵖ⁺ insᵖ M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert W⁺ ins
    (CTI2.conceal⊑-neutral² {p = p} c⊢ at-absent M⊑M′ q)
    provenance =
  CTI2.conceal⊑-neutral² (source-conceal-insert ins c⊢)
    (source-conceal-insert-position ins c⊢ generator-absent at-absent)
    (⊢²-target-insert W⁺ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert W⁺ ins
    (CTI2.conceal⊑² {p = p} c⊢ not-absent dynamic disaligned
      represented M⊑M′ q) provenance =
  CTI2.conceal⊑² (source-conceal-insert ins c⊢)
    (λ absent → not-absent
      (trans
        (sym (source-conceal-insert-position ins c⊢
          (concealGeneratorPosition c⊢) refl)) absent))
    (insert-to-starᴸ ins dynamic)
    (insert-disalignedᴸ ins disaligned)
    (transport⊑ᵂ ins represented)
    (⊢²-target-insert W⁺ ins M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} W⁺ ins
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      c⊢ c′⊢ positions not-absent represented mono rb sc M⊑M′ q)
    (Wᵖ⁺ , insᵖ , rb⁺ , provenance) =
  CTI2.reveal⊑reveal²
    (source-reveal-insert ins c⊢) (target-reveal-insert ins c′⊢)
    (trans
      (source-reveal-insert-position ins c⊢
        (revealGeneratorPosition c⊢) refl)
      (trans positions
        (sym (target-reveal-insert-position ins c′⊢
          (revealGeneratorPosition c′⊢) refl))))
    (λ absent → not-absent
      (trans
        (sym (source-reveal-insert-position ins c⊢
          (revealGeneratorPosition c⊢) refl)) absent))
    (transport⊑ᵂ insᵖ represented)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (⊢²-target-insert Wᵖ⁺ insᵖ M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} W⁺ ins
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      c⊢ c′⊢ positions not-absent represented mono rb sc M⊑M′ q)
    (Wᵖ⁺ , insᵖ , rb⁺ , provenance) =
  CTI2.conceal⊑conceal²
    (source-conceal-insert ins c⊢) (target-conceal-insert ins c′⊢)
    (trans
      (source-conceal-insert-position ins c⊢
        (concealGeneratorPosition c⊢) refl)
      (trans positions
        (sym (target-conceal-insert-position ins c′⊢
          (concealGeneratorPosition c′⊢) refl))))
    (λ absent → not-absent
      (trans
        (sym (source-conceal-insert-position ins c⊢
          (concealGeneratorPosition c⊢) refl)) absent))
    (transport⊑ᵂ insᵖ represented)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (⊢²-target-insert Wᵖ⁺ insᵖ M⊑M′ provenance)
    (transport⊑ᵂ ins q)
⊢²-target-insert {W = W} {γ = γ} W′ ins
    (CTI2.blame⊑² M′⊢ p) provenance =
  CTI2.blame⊑²
    (target-typing-insert ins M′⊢)
    (transport⊑ᵂ ins p)
⊢²-target-insert {Δᴿ = Δᴿ} {Δᴿ′ = Δᴿ′} {ρ = ρ}
    {γ = γ} W′ ins
    (CTI2.⊕⊑⊕² op {L = L} {L′ = L′} {M = M} {M′ = M′}
      {p = p} {q = q} L⊑L′ M⊑M′ r)
    (provenanceL , provenanceM) =
  ⊢²-retargetᴿ result-eq
    (CTI2.⊕⊑⊕² op
      L-arg
      M-arg
      r-result)
  where
  arg-eq : primArgTy {Δᴿ′} op
      ≡ renameᵗ (toRenameᵗ ρ) (primArgTy {Δᴿ} op)
  arg-eq = primArgTy-renameᵗ (toRenameᵗ ρ) op

  result-eq : primResultTy {Δᴿ′} op
      ≡ renameᵗ (toRenameᵗ ρ) (primResultTy {Δᴿ} op)
  result-eq = primResultTy-renameᵗ (toRenameᵗ ρ) op

  p-arg : primArgTy op ⊑ᵂ⟨ W′ ⟩ primArgTy op
  p-arg =
    subst≡
      (λ T → primArgTy op ⊑ᵂ⟨ W′ ⟩ T)
      (sym arg-eq)
      (transport⊑ᵂ ins p)

  q-arg : primArgTy op ⊑ᵂ⟨ W′ ⟩ primArgTy op
  q-arg =
    subst≡
      (λ T → primArgTy op ⊑ᵂ⟨ W′ ⟩ T)
      (sym arg-eq)
      (transport⊑ᵂ ins q)

  L-arg : W′ ∣ mapCtxᵀ ins γ
      ⊢² L ⊑ renameᵗᵐ ρ L′ ∶ p-arg
  L-arg =
    ⊢²-retargetᴿ {q = p-arg}
      (sym arg-eq) (⊢²-target-insert W′ ins L⊑L′ provenanceL)

  M-arg : W′ ∣ mapCtxᵀ ins γ
      ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ q-arg
  M-arg =
    ⊢²-retargetᴿ {q = q-arg}
      (sym arg-eq) (⊢²-target-insert W′ ins M⊑M′ provenanceM)

  r-result =
    subst≡
      (λ T → primResultTy op ⊑ᵂ⟨ W′ ⟩ T)
      (sym result-eq)
      (transport⊑ᵂ ins r)

------------------------------------------------------------------------
-- Public single-bind surface
------------------------------------------------------------------------

TargetExtendBindᵀ : Set
TargetExtendBindᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
    {fresh : CTX.RightBindFresh W B′}
  → (ext : ECR.WorldExtendᴿ (bind B′ ∷ []) W
      (CTX.rightOnlyWorld W B′ fresh))
  → (M⊑M′ : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → TargetInsertProvenance (CTX.rightOnlyWorld W B′ fresh)
      (rightBindTargetInsert fresh) M⊑M′
  → CTX.rightOnlyWorld W B′ fresh
      ∣ ECR.mapCtxᴿ ext γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p

mapCtx-rightBind-ECR : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {fresh : CTX.RightBindFresh W B′}
    (ext : ECR.WorldExtendᴿ (bind B′ ∷ []) W
      (CTX.rightOnlyWorld W B′ fresh))
    (γ : CtxImp W)
  → ECR.mapCtxᴿ ext γ ≡ mapCtxᵀ (rightBindTargetInsert fresh) γ
mapCtx-rightBind-ECR ext [] = refl
mapCtx-rightBind-ECR {W = W} {B′ = B′} {fresh = fresh} ext
    (CTX.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ entry-eq (mapCtx-rightBind-ECR ext γ)
  where
  entry-eq :
      CTX.ctx-imp A (⇑ᵗ B) (ECR.transport⊑ᵂ ext p)
      ≡ CTX.ctx-imp A (renameᵗ (toRenameᵗ wk↪ᵗ) B)
          (transport⊑ᵂ
            (rightBindTargetInsert {W = W} {B = B′} fresh) p)
  entry-eq =
    ctx-imp-target-eq {W = CTX.rightOnlyWorld W B′ fresh}
      {A = A} {B = ⇑ᵗ B}
      {B′ = renameᵗ (toRenameᵗ wk↪ᵗ) B}
      {p = ECR.transport⊑ᵂ ext p}
      {q = transport⊑ᵂ
        (rightBindTargetInsert {W = W} {B = B′} fresh) p}
      (sym (renameᵗ-wk-eq B))

⊢²-target-extend-bind : TargetExtendBindᵀ
⊢²-target-extend-bind {W = W} {γ = γ} {M = M} {M′ = M′}
    {B = B} {B′ = B′} {p = p} {fresh = fresh}
    ext M⊑M′ provenance =
  subst≡
    (λ γ′ → CTX.rightOnlyWorld W B′ fresh ∣ γ′
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p)
    (sym (mapCtx-rightBind-ECR ext γ))
    (⊢²-retargetᴿ {q = ECR.transport⊑ᵂ ext p}
      (renameᵗ-wk-eq B)
      (⊢²-target-insert
        (CTX.rightOnlyWorld W B′ fresh)
        (rightBindTargetInsert fresh) M⊑M′ provenance))

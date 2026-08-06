module proof.DGG.Repark where

-- File Charter:
--   * Re-parks one target variable at a hereditarily fresh center by
--     inserting that center at the variable's old center position.
--   * Exports the insertion and re-parked embeddings, their pointwise laws,
--     avoidance predicates, and transport for obligations and contexts.
--   * Stage 2b-ii builds on exactly these embedding and transport laws for
--     its derivation induction, stopping capture at rebases pivoted on Yₚ.

open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (nothing)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ)
open import Imprecision using (X⊑★; _⊢_⊑_)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; ηᴸʷ; ηᴿʷ; impEnvʷ; sourceStoreʷ; targetStoreʷ;
   _⊑ᵂ⟨_⟩_; CtxImp; ctx-imp; _∋ʷ_⦂_; Zʷ; Sʷ)
import proof.DGG.CenterRename as CR
open CR using
  (_∘↪_; toRenameᵗ-∘; preimage?; renameEnv; renameEnv-image;
   renameEnv-off; rename-⊑ᵂ)
open import proof.DGG.WorldSupport using (renameᵗ-support)

------------------------------------------------------------------------
-- Insertion injections
------------------------------------------------------------------------

insertᶜ : ∀ {Δ} (k : Fin.Fin (Nat.suc Δ)) → Δ ↪ᵗ Nat.suc Δ
insertᶜ {Nat.zero} Fin.zero = skip empty
insertᶜ {Nat.suc Δ} Fin.zero = skip id↪ᵗ
insertᶜ {Nat.suc Δ} (Fin.suc k) = keep (insertᶜ k)

insertᶜ-misses : ∀ {Δ} (k : Fin.Fin (Nat.suc Δ)) (Z : TyVar Δ)
  → toRenameᵗ (insertᶜ k) Z ≢ k
insertᶜ-misses {Nat.zero} Fin.zero ()
insertᶜ-misses {Nat.suc Δ} Fin.zero Z ()
insertᶜ-misses {Nat.suc Δ} (Fin.suc k) Fin.zero ()
insertᶜ-misses {Nat.suc Δ} (Fin.suc k) (Fin.suc Z) eq =
  insertᶜ-misses k Z (fin-suc-injective eq)
  where
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

private
  toRename-id : ∀ {Δ} (X : TyVar Δ) → toRenameᵗ id↪ᵗ X ≡ X
  toRename-id {Nat.zero} ()
  toRename-id {Nat.suc Δ} Fin.zero = refl
  toRename-id {Nat.suc Δ} (Fin.suc X) =
    cong Fin.suc (toRename-id X)

  insertᶜ-preimage : ∀ {Δ} (k : Fin.Fin (Nat.suc Δ))
    → preimage? (insertᶜ k) k ≡ nothing
  insertᶜ-preimage {Nat.zero} Fin.zero = refl
  insertᶜ-preimage {Nat.suc Δ} Fin.zero = refl
  insertᶜ-preimage {Nat.suc Δ} (Fin.suc k)
      rewrite insertᶜ-preimage k =
    refl

------------------------------------------------------------------------
-- Re-parked target embedding
------------------------------------------------------------------------

-- reparkIndex is the constructor-preserving inclusion of ηᴿ(Yₚ) into
-- Fin (suc Δ).  Thus it has the same de Bruijn number as the old image;
-- insertion shifts the old center at that number up by one.

reparkIndex : ∀ {Δᴿ Δ}
  → (ηᴿ : Δᴿ ↪ᵗ Δ)
  → TyVar Δᴿ
  → TyVar (Nat.suc Δ)
reparkIndex empty ()
reparkIndex (keep ηᴿ) Fin.zero = Fin.zero
reparkIndex (keep ηᴿ) (Fin.suc Y) = Fin.suc (reparkIndex ηᴿ Y)
reparkIndex (skip ηᴿ) Y = Fin.suc (reparkIndex ηᴿ Y)

reparkEmbedᴿ : ∀ {Δᴿ Δ}
  → (ηᴿ : Δᴿ ↪ᵗ Δ)
  → TyVar Δᴿ
  → Δᴿ ↪ᵗ Nat.suc Δ
reparkEmbedᴿ empty ()
reparkEmbedᴿ (keep ηᴿ) Fin.zero = keep (skip ηᴿ)
reparkEmbedᴿ (keep ηᴿ) (Fin.suc Y) = keep (reparkEmbedᴿ ηᴿ Y)
reparkEmbedᴿ (skip ηᴿ) Y = skip (reparkEmbedᴿ ηᴿ Y)

reparkEmbedᴿ-off : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
    (Yₚ Y : TyVar Δᴿ)
  → Y ≢ Yₚ
  → toRenameᵗ (reparkEmbedᴿ ηᴿ Yₚ) Y
      ≡ toRenameᵗ (insertᶜ (reparkIndex ηᴿ Yₚ))
          (toRenameᵗ ηᴿ Y)
reparkEmbedᴿ-off empty ()
reparkEmbedᴿ-off (keep ηᴿ) Fin.zero Fin.zero Y≢ =
  ⊥-elim (Y≢ refl)
reparkEmbedᴿ-off (keep ηᴿ) Fin.zero (Fin.suc Y) Y≢ =
  cong Fin.suc (cong Fin.suc (sym (toRename-id (toRenameᵗ ηᴿ Y))))
reparkEmbedᴿ-off (keep ηᴿ) (Fin.suc Yₚ) Fin.zero Y≢ = refl
reparkEmbedᴿ-off (keep ηᴿ) (Fin.suc Yₚ) (Fin.suc Y) Y≢ =
  cong Fin.suc
    (reparkEmbedᴿ-off ηᴿ Yₚ Y
      (λ eq → Y≢ (cong Fin.suc eq)))
reparkEmbedᴿ-off (skip ηᴿ) Yₚ Y Y≢ =
  cong Fin.suc (reparkEmbedᴿ-off ηᴿ Yₚ Y Y≢)

reparkEmbedᴿ-park : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
    (Yₚ : TyVar Δᴿ)
  → toRenameᵗ (reparkEmbedᴿ ηᴿ Yₚ) Yₚ ≡ reparkIndex ηᴿ Yₚ
reparkEmbedᴿ-park empty ()
reparkEmbedᴿ-park (keep ηᴿ) Fin.zero = refl
reparkEmbedᴿ-park (keep ηᴿ) (Fin.suc Yₚ) =
  cong Fin.suc (reparkEmbedᴿ-park ηᴿ Yₚ)
reparkEmbedᴿ-park (skip ηᴿ) Yₚ =
  cong Fin.suc (reparkEmbedᴿ-park ηᴿ Yₚ)

------------------------------------------------------------------------
-- Re-parked world and marks
------------------------------------------------------------------------

reparkWorld : ∀ {Δᴸ Δᴿ Δ}
  → (W : World Δᴸ Δᴿ Δ)
  → TyVar Δᴿ
  → World Δᴸ Δᴿ (Nat.suc Δ)
reparkWorld W Yₚ =
  world (insertᶜ k ∘↪ ηᴸʷ W) (reparkEmbedᴿ (ηᴿʷ W) Yₚ)
    (renameEnv (insertᶜ k) (impEnvʷ W))
    (sourceStoreʷ W) (targetStoreʷ W)
  where
  k = reparkIndex (ηᴿʷ W) Yₚ

repark-mark-image : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (Yₚ : TyVar Δᴿ) (Z : TyVar Δ)
  → impEnvʷ (reparkWorld W Yₚ)
      (toRenameᵗ (insertᶜ (reparkIndex (ηᴿʷ W) Yₚ)) Z)
      ≡ impEnvʷ W Z
repark-mark-image W Yₚ Z =
  renameEnv-image (insertᶜ (reparkIndex (ηᴿʷ W) Yₚ))
    (impEnvʷ W) Z

repark-mark-inserted : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (Yₚ : TyVar Δᴿ)
  → impEnvʷ (reparkWorld W Yₚ) (reparkIndex (ηᴿʷ W) Yₚ)
      ≡ X⊑★
repark-mark-inserted W Yₚ =
  renameEnv-off (insertᶜ k) (impEnvʷ W) (insertᶜ-preimage k)
  where
  k = reparkIndex (ηᴿʷ W) Yₚ

------------------------------------------------------------------------
-- Avoidance predicates
------------------------------------------------------------------------

data CtxAvoidᴿ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    (Yₚ : TyVar Δᴿ) : CtxImp W → Set where
  ctx-avoid-[] : CtxAvoidᴿ Yₚ []

  ctx-avoid-∷ : ∀ {γ A B p}
    → ¬ (Yₚ ∈ᵗ B)
    → CtxAvoidᴿ Yₚ γ
    → CtxAvoidᴿ Yₚ (ctx-imp A B p ∷ γ)

data StoreAvoidᴿ : ∀ {Δ} → TyVar Δ → TyStore Δ → Set where
  store-avoid-lift-zero : ∀ {Δ} {Σ : TyStore Δ}
    → StoreAvoidᴿ Fin.zero (store-lift Σ)

  store-avoid-lift-suc : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ}
    → StoreAvoidᴿ Y Σ
    → StoreAvoidᴿ (Fin.suc Y) (store-lift Σ)

  store-avoid-bind-zero : ∀ {Δ} {Σ : TyStore Δ} {A : Ty Δ}
    → StoreAvoidᴿ Fin.zero (store-bind Σ A)

  store-avoid-bind-suc : ∀ {Δ} {Σ : TyStore Δ}
      {A : Ty Δ} {Y : TyVar Δ}
    → ¬ (Y ∈ᵗ A)
    → StoreAvoidᴿ Y Σ
    → StoreAvoidᴿ (Fin.suc Y) (store-bind Σ A)

------------------------------------------------------------------------
-- Obligation and context transport
------------------------------------------------------------------------

repark-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Yₚ : TyVar Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
  → ¬ (Yₚ ∈ᵗ B)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ reparkWorld W Yₚ ⟩ B
repark-⊑ᵂ {W = W} {Yₚ} {A} {B} Yₚ∉B A⊑B =
  subst
    (λ R → impEnvʷ (reparkWorld W Yₚ) ⊢
      CTI2.embedᴸ (reparkWorld W Yₚ) A ⊑ R)
    target-eq
    (rename-⊑ᵂ {W = W} (insertᶜ k) A⊑B)
  where
  k = reparkIndex (ηᴿʷ W) Yₚ

  target-eq : CTI2.embedᴿ (CR.renameWorld (insertᶜ k) W) B
    ≡ CTI2.embedᴿ (reparkWorld W Yₚ) B
  target-eq = renameᵗ-support B λ Y Y∈B →
    trans (toRenameᵗ-∘ (insertᶜ k) (ηᴿʷ W) Y)
      (sym (reparkEmbedᴿ-off (ηᴿʷ W) Yₚ Y
        (λ eq → Yₚ∉B (subst (λ Z → Z ∈ᵗ B) eq Y∈B))))

ctxAvoid-∋ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Yₚ : TyVar Δᴿ} {γ : CtxImp W} {x A B p}
  → (avoid : CtxAvoidᴿ Yₚ γ)
  → γ ∋ʷ x ⦂ ctx-imp A B p
  → ¬ (Yₚ ∈ᵗ B)
ctxAvoid-∋ (ctx-avoid-∷ Yₚ∉B avoid) Zʷ = Yₚ∉B
ctxAvoid-∋ (ctx-avoid-∷ Yₚ∉B avoid) (Sʷ x∈) =
  ctxAvoid-∋ avoid x∈

reparkCtx : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Yₚ : TyVar Δᴿ} {γ : CtxImp W}
  → CtxAvoidᴿ Yₚ γ
  → CtxImp (reparkWorld W Yₚ)
reparkCtx ctx-avoid-[] = []
reparkCtx {W = W} {Yₚ} (ctx-avoid-∷ {A = A} {B} {p} Yₚ∉B avoid) =
  ctx-imp A B (repark-⊑ᵂ {W = W} {Yₚ = Yₚ} Yₚ∉B p) ∷
    reparkCtx avoid

repark-∋ʷ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Yₚ : TyVar Δᴿ} {γ : CtxImp W} {x A B p}
  → (avoid : CtxAvoidᴿ Yₚ γ)
  → (x∈ : γ ∋ʷ x ⦂ ctx-imp A B p)
  → reparkCtx avoid ∋ʷ x ⦂
      ctx-imp A B
        (repark-⊑ᵂ {W = W} {Yₚ = Yₚ} (ctxAvoid-∋ avoid x∈) p)
repark-∋ʷ (ctx-avoid-∷ Yₚ∉B avoid) Zʷ = Zʷ
repark-∋ʷ (ctx-avoid-∷ Yₚ∉B avoid) (Sʷ x∈) =
  Sʷ (repark-∋ʷ avoid x∈)

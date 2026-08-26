module proof.DGG.WorldInsert where

-- File Charter:
--   * Defines both-sided center insertion between cast-term imprecision
--     worlds: endpoint OPEs, a center OPE, and the coherence fields that
--     make the world embeddings, imprecision environment, and stores commute.
--   * Transports type imprecision and term-context imprecision along an
--     insertion, and records the lookup and endpoint-context equations.
--   * Provides the identity insertion, composition, and lifting of an
--     insertion under a universal binder on both sides or on the source side.
--   * Contains no derivation-level transport of term imprecision.

open import Data.List using ([]; _∷_)
open import Data.Nat as Nat using (ℕ)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-lift; store-bind)
open import Imprecision using (VarImp; X⊑X; X⊑★; extendᵐ)
import TermCtx as T
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ)
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-keep; StoreRename-id; toRename-keep-eq;
   toRename-id-eq)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
import proof.DGG.CtxImp as CTX
open CTX using (World; CtxImp; _⊑ᵂ⟨_⟩_)

------------------------------------------------------------------------
-- Insertion
------------------------------------------------------------------------

record WorldInsert {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    (ρᴸ : Δᴸ ↪ᵗ Δᴸ′)
    (ρᴿ : Δᴿ ↪ᵗ Δᴿ′)
    (π : Δ ↪ᵗ Δ′)
    (W : World Δᴸ Δᴿ Δ)
    (W′ : World Δᴸ′ Δᴿ′ Δ′) : Set where
  field
    source-insert : ∀ Xᴸ
      → toRenameᵗ (CTX.ηᴸʷ W′) (toRenameᵗ ρᴸ Xᴸ)
          ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)

    target-insert : ∀ Xᴿ
      → toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρᴿ Xᴿ)
          ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)

    impEnv-insert : ∀ Z
      → CTX.impEnvʷ W′ (toRenameᵗ π Z) ≡ CTX.impEnvʷ W Z

    sourceStore-rename :
      StoreRename (toRenameᵗ ρᴸ) (CTX.sourceStoreʷ W)
        (CTX.sourceStoreʷ W′)

    targetStore-rename :
      StoreRename (toRenameᵗ ρᴿ) (CTX.targetStoreʷ W)
        (CTX.targetStoreʷ W′)

open WorldInsert public

------------------------------------------------------------------------
-- Transport of embedded types and type imprecision
------------------------------------------------------------------------

source-embed-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → (A : Ty Δᴸ)
  → CTX.embedᴸ W′ (renameᵗ (toRenameᵗ ρᴸ) A)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A)
source-embed-insert {ρᴸ = ρᴸ} {π = π} {W = W} {W′ = W′} ins A =
  trans (renameᵗ-comp (toRenameᵗ ρᴸ) (toRenameᵗ (CTX.ηᴸʷ W′)) A)
    (trans (renameᵗ-cong A (source-insert ins))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ W)) (toRenameᵗ π) A)))

target-embed-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρᴿ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W B)
target-embed-insert {ρᴿ = ρᴿ} {π = π} {W = W} {W′ = W′} ins B =
  trans (renameᵗ-comp (toRenameᵗ ρᴿ) (toRenameᵗ (CTX.ηᴿʷ W′)) B)
    (trans (renameᵗ-cong B (target-insert ins))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ W)) (toRenameᵗ π) B)))

insert⊑ᶜ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A B : Ty Δ}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → CTX.impEnvʷ W Imprecision.⊢ A ⊑ B
  → CTX.impEnvʷ W′ Imprecision.⊢
      renameᵗ (toRenameᵗ π) A ⊑ renameᵗ (toRenameᵗ π) B
insert⊑ᶜ {π = π} ins p =
  rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
    (λ Z eq → trans (impEnv-insert ins Z) eq) p

insert⊑ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → A ⊑ᵂ⟨ W ⟩ B
  → renameᵗ (toRenameᵗ ρᴸ) A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρᴿ) B
insert⊑ {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} ins p =
  subst≡
    (λ L → CTX.impEnvʷ W′ Imprecision.⊢
      L ⊑ CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρᴿ) B))
    (sym (source-embed-insert ins A))
    (subst≡
      (λ R → CTX.impEnvʷ W′ Imprecision.⊢
        renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A) ⊑ R)
      (sym (target-embed-insert ins B))
      (insert⊑ᶜ ins p))

------------------------------------------------------------------------
-- Transport of term-context imprecision
------------------------------------------------------------------------

insertCtx : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → WorldInsert ρᴸ ρᴿ π W W′
  → CtxImp W
  → CtxImp W′
insertCtx ins [] = []
insertCtx {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} ins (CTX.ctx-imp A B p ∷ γ) =
  CTX.ctx-imp (renameᵗ (toRenameᵗ ρᴸ) A) (renameᵗ (toRenameᵗ ρᴿ) B)
    (insert⊑ ins p) ∷ insertCtx ins γ

insertCtx-∋ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → insertCtx ins γ CTX.∋ʷ x ⦂
      CTX.ctx-imp (renameᵗ (toRenameᵗ ρᴸ) A)
        (renameᵗ (toRenameᵗ ρᴿ) B) (insert⊑ ins p)
insertCtx-∋ ins CTX.Zʷ = CTX.Zʷ
insertCtx-∋ ins (CTX.Sʷ x∈) = CTX.Sʷ (insertCtx-∋ ins x∈)

insertCtx-src : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → (γ : CtxImp W)
  → CTX.srcCtxʷ (insertCtx ins γ)
      ≡ T.renameCtx (toRenameᵗ ρᴸ) (CTX.srcCtxʷ γ)
insertCtx-src ins [] = refl
insertCtx-src ins (CTX.ctx-imp A B p ∷ γ) =
  cong (renameᵗ _ A ∷_) (insertCtx-src ins γ)

insertCtx-tgt : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (ins : WorldInsert ρᴸ ρᴿ π W W′)
  → (γ : CtxImp W)
  → CTX.tgtCtxʷ (insertCtx ins γ)
      ≡ T.renameCtx (toRenameᵗ ρᴿ) (CTX.tgtCtxʷ γ)
insertCtx-tgt ins [] = refl
insertCtx-tgt ins (CTX.ctx-imp A B p ∷ γ) =
  cong (renameᵗ _ B ∷_) (insertCtx-tgt ins γ)

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

id-insert : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → WorldInsert id↪ᵗ id↪ᵗ id↪ᵗ W W
id-insert W = record
  { source-insert = λ Xᴸ →
      trans (cong (toRenameᵗ (CTX.ηᴸʷ W)) (toRename-id-eq Xᴸ))
        (sym (toRename-id-eq _))
  ; target-insert = λ Xᴿ →
      trans (cong (toRenameᵗ (CTX.ηᴿʷ W)) (toRename-id-eq Xᴿ))
        (sym (toRename-id-eq _))
  ; impEnv-insert = λ Z → cong (CTX.impEnvʷ W) (toRename-id-eq Z)
  ; sourceStore-rename = λ {X} {A} X∈ →
      subst≡ (λ Y → CTX.sourceStoreʷ W TyStore.∋ Y ⦂ _)
        (sym (toRename-id-eq X))
        (subst≡ (λ B → CTX.sourceStoreʷ W TyStore.∋ X ⦂ B)
          (sym (renameᵗ-cong A toRename-id-eq))
          (StoreRename-id X∈))
  ; targetStore-rename = λ {X} {A} X∈ →
      subst≡ (λ Y → CTX.targetStoreʷ W TyStore.∋ Y ⦂ _)
        (sym (toRename-id-eq X))
        (subst≡ (λ B → CTX.targetStoreʷ W TyStore.∋ X ⦂ B)
          (sym (renameᵗ-cong A toRename-id-eq))
          (StoreRename-id X∈))
  }

compose-insert : ∀ {Δᴸ Δᴸ′ Δᴸ″ Δᴿ Δᴿ′ Δᴿ″ Δ Δ′ Δ″}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴸ′ : Δᴸ′ ↪ᵗ Δᴸ″}
    {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {ρᴿ′ : Δᴿ′ ↪ᵗ Δᴿ″}
    {π : Δ ↪ᵗ Δ′} {π′ : Δ′ ↪ᵗ Δ″}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {W″ : World Δᴸ″ Δᴿ″ Δ″}
  → WorldInsert ρᴸ ρᴿ π W W′
  → WorldInsert ρᴸ′ ρᴿ′ π′ W′ W″
  → WorldInsert (ρᴸ′ ∘↪ ρᴸ) (ρᴿ′ ∘↪ ρᴿ) (π′ ∘↪ π) W W″
compose-insert {ρᴸ = ρᴸ} {ρᴸ′ = ρᴸ′} {ρᴿ = ρᴿ} {ρᴿ′ = ρᴿ′}
    {π = π} {π′ = π′} {W = W} {W′ = W′} {W″ = W″} ins ins′ = record
  { source-insert = λ Xᴸ →
      trans (cong (toRenameᵗ (CTX.ηᴸʷ W″)) (toRenameᵗ-∘ ρᴸ′ ρᴸ Xᴸ))
        (trans (source-insert ins′ (toRenameᵗ ρᴸ Xᴸ))
          (trans (cong (toRenameᵗ π′) (source-insert ins Xᴸ))
            (sym (toRenameᵗ-∘ π′ π _))))
  ; target-insert = λ Xᴿ →
      trans (cong (toRenameᵗ (CTX.ηᴿʷ W″)) (toRenameᵗ-∘ ρᴿ′ ρᴿ Xᴿ))
        (trans (target-insert ins′ (toRenameᵗ ρᴿ Xᴿ))
          (trans (cong (toRenameᵗ π′) (target-insert ins Xᴿ))
            (sym (toRenameᵗ-∘ π′ π _))))
  ; impEnv-insert = λ Z →
      trans (cong (CTX.impEnvʷ W″) (toRenameᵗ-∘ π′ π Z))
        (trans (impEnv-insert ins′ (toRenameᵗ π Z))
          (impEnv-insert ins Z))
  ; sourceStore-rename = λ {X} {A} X∈ →
      subst≡ (λ Y → CTX.sourceStoreʷ W″ TyStore.∋ Y ⦂ _)
        (sym (toRenameᵗ-∘ ρᴸ′ ρᴸ X))
        (subst≡ (λ B → CTX.sourceStoreʷ W″ TyStore.∋ _ ⦂ B)
          (trans
            (renameᵗ-comp (toRenameᵗ ρᴸ) (toRenameᵗ ρᴸ′) A)
            (sym (renameᵗ-cong A (toRenameᵗ-∘ ρᴸ′ ρᴸ))))
          (sourceStore-rename ins′ (sourceStore-rename ins X∈)))
  ; targetStore-rename = λ {X} {A} X∈ →
      subst≡ (λ Y → CTX.targetStoreʷ W″ TyStore.∋ Y ⦂ _)
        (sym (toRenameᵗ-∘ ρᴿ′ ρᴿ X))
        (subst≡ (λ B → CTX.targetStoreʷ W″ TyStore.∋ _ ⦂ B)
          (trans
            (renameᵗ-comp (toRenameᵗ ρᴿ) (toRenameᵗ ρᴿ′) A)
            (sym (renameᵗ-cong A (toRenameᵗ-∘ ρᴿ′ ρᴿ))))
          (targetStore-rename ins′ (targetStore-rename ins X∈)))
  }

------------------------------------------------------------------------
-- Lifting under a universal binder
------------------------------------------------------------------------

-- A paired syntactic binder (unbound on both endpoints) inserts into a
-- paired bound allocation: the fresh center stays at zero on both sides and
-- the old centers are shifted behind it.

liftBoth-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    (v : VarImp) (A : Ty Δᴸ′) (B : Ty Δᴿ′)
  → WorldInsert ρᴸ ρᴿ π W W′
  → WorldInsert (keep ρᴸ) (keep ρᴿ) (keep π)
      (CTX.liftWorldBoth v W) (CTX.bothBindWorld v W′ A B)
liftBoth-insert {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {π = π} {W = W} {W′ = W′}
    v A B ins = record
  { source-insert = source-lift
  ; target-insert = target-lift
  ; impEnv-insert = impEnv-lift
  ; sourceStore-rename = λ X∈ →
      bind-lift-source (StoreRename-keep (sourceStore-rename ins) X∈)
  ; targetStore-rename = λ X∈ →
      bind-lift-target (StoreRename-keep (targetStore-rename ins) X∈)
  }
  where
  source-lift : ∀ Xᴸ
    → toRenameᵗ (keep (CTX.ηᴸʷ W′)) (toRenameᵗ (keep ρᴸ) Xᴸ)
        ≡ toRenameᵗ (keep π) (toRenameᵗ (keep (CTX.ηᴸʷ W)) Xᴸ)
  source-lift Fin.zero = refl
  source-lift (Fin.suc Xᴸ) = cong Fin.suc (source-insert ins Xᴸ)

  target-lift : ∀ Xᴿ
    → toRenameᵗ (keep (CTX.ηᴿʷ W′)) (toRenameᵗ (keep ρᴿ) Xᴿ)
        ≡ toRenameᵗ (keep π) (toRenameᵗ (keep (CTX.ηᴿʷ W)) Xᴿ)
  target-lift Fin.zero = refl
  target-lift (Fin.suc Xᴿ) = cong Fin.suc (target-insert ins Xᴿ)

  impEnv-lift : ∀ Z
    → extendᵐ v (CTX.impEnvʷ W′) (toRenameᵗ (keep π) Z)
        ≡ extendᵐ v (CTX.impEnvʷ W) Z
  impEnv-lift Fin.zero = refl
  impEnv-lift (Fin.suc Z) = impEnv-insert ins Z

  bind-lift-source : ∀ {X C}
    → store-lift (CTX.sourceStoreʷ W′) TyStore.∋ X ⦂ C
    → store-bind (CTX.sourceStoreʷ W′) A TyStore.∋ X ⦂ C
  bind-lift-source (TyStore.S-lift∋ X∈ eq) = TyStore.S-bind∋ X∈ eq

  bind-lift-target : ∀ {X C}
    → store-lift (CTX.targetStoreʷ W′) TyStore.∋ X ⦂ C
    → store-bind (CTX.targetStoreʷ W′) B TyStore.∋ X ⦂ C
  bind-lift-target (TyStore.S-lift∋ X∈ eq) = TyStore.S-bind∋ X∈ eq

-- A source-only syntactic binder inserts into a source-only bound
-- allocation: the target context, embedding, and store are unchanged.

liftLeft-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    (v : VarImp) (A : Ty Δᴸ′)
  → WorldInsert ρᴸ ρᴿ π W W′
  → WorldInsert (keep ρᴸ) ρᴿ (keep π)
      (CTX.liftWorldLeft v W) (CTX.leftOnlyWorld v W′ A)
liftLeft-insert {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {π = π} {W = W} {W′ = W′}
    v A ins = record
  { source-insert = source-lift
  ; target-insert = λ Xᴿ → cong Fin.suc (target-insert ins Xᴿ)
  ; impEnv-insert = impEnv-lift
  ; sourceStore-rename = λ X∈ →
      bind-lift-source (StoreRename-keep (sourceStore-rename ins) X∈)
  ; targetStore-rename = targetStore-rename ins
  }
  where
  source-lift : ∀ Xᴸ
    → toRenameᵗ (keep (CTX.ηᴸʷ W′)) (toRenameᵗ (keep ρᴸ) Xᴸ)
        ≡ toRenameᵗ (keep π) (toRenameᵗ (keep (CTX.ηᴸʷ W)) Xᴸ)
  source-lift Fin.zero = refl
  source-lift (Fin.suc Xᴸ) = cong Fin.suc (source-insert ins Xᴸ)

  impEnv-lift : ∀ Z
    → extendᵐ v (CTX.impEnvʷ W′) (toRenameᵗ (keep π) Z)
        ≡ extendᵐ v (CTX.impEnvʷ W) Z
  impEnv-lift Fin.zero = refl
  impEnv-lift (Fin.suc Z) = impEnv-insert ins Z

  bind-lift-source : ∀ {X C}
    → store-lift (CTX.sourceStoreʷ W′) TyStore.∋ X ⦂ C
    → store-bind (CTX.sourceStoreʷ W′) A TyStore.∋ X ⦂ C
  bind-lift-source (TyStore.S-lift∋ X∈ eq) = TyStore.S-bind∋ X∈ eq

------------------------------------------------------------------------
-- Shifting an insertion behind a fresh allocation in the target world
------------------------------------------------------------------------

-- Allocating a fresh center in the target world of an insertion, on both
-- endpoints or on one endpoint, shifts the insertion behind it.

shift-bound : ∀ {Δ Δ′} {ρ : Δ ↪ᵗ Δ′} {Σ : TyStore Δ} {Σ′ : TyStore Δ′}
    (A : Ty Δ′)
  → StoreRename (toRenameᵗ ρ) Σ Σ′
  → StoreRename (toRenameᵗ (skip ρ)) Σ (store-bind Σ′ A)
shift-bound {ρ = ρ} {Σ′ = Σ′} A h {X} {B} X∈ =
  subst≡ (λ T → store-bind Σ′ A TyStore.∋ Fin.suc (toRenameᵗ ρ X) ⦂ T)
    (renameᵗ-comp (toRenameᵗ ρ) Fin.suc B)
    (TyStore.S-bind∋ (h X∈) refl)

shiftBoth-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    (v : VarImp) (A : Ty Δᴸ′) (B : Ty Δᴿ′)
  → WorldInsert ρᴸ ρᴿ π W W′
  → WorldInsert (skip ρᴸ) (skip ρᴿ) (skip π) W (CTX.bothBindWorld v W′ A B)
shiftBoth-insert v A B ins = record
  { source-insert = λ Xᴸ → cong Fin.suc (source-insert ins Xᴸ)
  ; target-insert = λ Xᴿ → cong Fin.suc (target-insert ins Xᴿ)
  ; impEnv-insert = λ Z → impEnv-insert ins Z
  ; sourceStore-rename = shift-bound A (sourceStore-rename ins)
  ; targetStore-rename = shift-bound B (targetStore-rename ins)
  }

shiftLeft-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    (v : VarImp) (A : Ty Δᴸ′)
  → WorldInsert ρᴸ ρᴿ π W W′
  → WorldInsert (skip ρᴸ) ρᴿ (skip π) W (CTX.leftOnlyWorld v W′ A)
shiftLeft-insert v A ins = record
  { source-insert = λ Xᴸ → cong Fin.suc (source-insert ins Xᴸ)
  ; target-insert = λ Xᴿ → cong Fin.suc (target-insert ins Xᴿ)
  ; impEnv-insert = λ Z → impEnv-insert ins Z
  ; sourceStore-rename = shift-bound A (sourceStore-rename ins)
  ; targetStore-rename = targetStore-rename ins
  }

shiftRight-insert : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {ρᴸ : Δᴸ ↪ᵗ Δᴸ′} {ρᴿ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    (B : Ty Δᴿ′)
  → WorldInsert ρᴸ ρᴿ π W W′
  → WorldInsert ρᴸ (skip ρᴿ) (skip π) W (CTX.rightOnlyWorld W′ B)
shiftRight-insert B ins = record
  { source-insert = λ Xᴸ → cong Fin.suc (source-insert ins Xᴸ)
  ; target-insert = λ Xᴿ → cong Fin.suc (target-insert ins Xᴿ)
  ; impEnv-insert = λ Z → impEnv-insert ins Z
  ; sourceStore-rename = sourceStore-rename ins
  ; targetStore-rename = shift-bound B (targetStore-rename ins)
  }

module proof.DGG.Repark where

-- File Charter:
--   * Re-parks one target variable at a hereditarily fresh center by
--     inserting that center at the variable's old center position.
--   * Exports the insertion and re-parked embeddings, their pointwise laws,
--     avoidance predicates, and transport for obligations and contexts.
--   * Transports derivations whose target types avoid the parked variable and
--     whose rebases are never pivoted on that variable.

open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ)
open import Imprecision using
  (VarImp; ImpEnv; X⊑X; X⊑★; ⇒⊑⇒; _⊢_⊑_)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_)
open import Primitives using
  (Const; Prim; constTy; primArgTy; primResultTy)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; ηᴸʷ; ηᴿʷ; impEnvʷ; sourceStoreʷ; targetStoreʷ;
   _⊑ᵂ⟨_⟩_; CtxImp; ctx-imp; _∋ʷ_⦂_; Zʷ; Sʷ;
   _∣_⊢²_⊑_∶_)
import proof.DGG.CenterRename as CR
open CR using
  (_∘↪_; toRenameᵗ-∘; preimage?; renameEnv; renameEnv-image;
   renameEnv-off; rename-⊑ᵂ)
open import proof.DGG.WorldSupport using (renameᵗ-support)
open import proof.DGG.ConvImp using (occurs-absent-⊥)
open import proof.ImprecisionConsistency using
  (shift-not-occurs; toRenameᵗ-injective; unshift-occurs;
   zero-not-shift)

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

-- A rebase avoids Yₚ exactly when its target pivot, if it has one, is
-- different from Yₚ.  The one-sided forms make the condition explicit
-- without splitting each term-imprecision rule into several constructors.

AvoidRebaseᴿ : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ} {Xᴿ?}
  → TyVar Δᴿ
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → Set
AvoidRebaseᴿ Yₚ CTI2.rebase-idᴿ = ⊤
AvoidRebaseᴿ Yₚ (CTI2.rebase-varᴿ {Xᴿ = Xᴿ} rb) = Xᴿ ≢ Yₚ

AvoidRebaseᴸ : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ?}
  → TyVar Δᴿ
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → Set
AvoidRebaseᴸ Yₚ CTI2.rebase-idᴸ = ⊤
AvoidRebaseᴸ Yₚ (CTI2.rebase-varᴸ {Xᴿ = Xᴿ} rb) = Xᴿ ≢ Yₚ
AvoidRebaseᴸ Yₚ (CTI2.rebase-onlyᴸ mark disaligned represented) = ⊤

data AvoidᴿD {Δᴸ Δᴿ Δ} (Yₚ : TyVar Δᴿ) :
    ∀ {W : World Δᴸ Δᴿ Δ} {γ M N A B} {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p → Set where
  avoid-x⊑x² : ∀ {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      {x∈ : γ ∋ʷ x ⦂ ctx-imp A B p}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidᴿD Yₚ (CTI2.x⊑x² x∈)

  avoid-ƛ⊑ƛ² : ∀ {W γ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      {D : W ∣ ctx-imp A A′ pA ∷ γ ⊢² M ⊑ M′ ∶ pB}
    → ¬ (Yₚ ∈ᵗ A′ ⇒ B′)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.ƛ⊑ƛ² D)

  avoid-·⊑·² : ∀ {W γ L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      {D₁ : W ∣ γ ⊢² L ⊑ L′ ∶ ⇒⊑⇒ pA pB}
      {D₂ : W ∣ γ ⊢² M ⊑ M′ ∶ pA}
    → ¬ (Yₚ ∈ᵗ B′)
    → AvoidᴿD Yₚ D₁
    → AvoidᴿD Yₚ D₂
    → AvoidᴿD Yₚ (CTI2.·⊑·² D₁ D₂)

  avoid-Λ⊑Λ² : ∀ {W γ γ′ V V′ A B}
      {p : A ⊑ᵂ⟨ CTI2.liftWorldBoth X⊑X W ⟩ B}
      {liftγ : CTI2.LiftCtx X⊑X γ γ′}
      {vV : Value V} {vV′ : Value V′}
      {D : CTI2.liftWorldBoth X⊑X W ∣ γ′ ⊢² V ⊑ V′ ∶ p}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B}
    → ¬ (Yₚ ∈ᵗ `∀ B)
    → AvoidᴿD (Fin.suc Yₚ) D
    → AvoidᴿD Yₚ (CTI2.Λ⊑Λ² liftγ vV vV′ D q)

  avoid-Λ⊑² : ∀ {W γ γ′ V M A B}
      {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B}
      {Anv : NonVar A} {zero∈A : Fin.zero ∈ᵗ A}
      {liftγ : CTI2.LiftCtxᴸ X⊑★ γ γ′} {vV : Value V}
      {M⊢ : ⟨ _ , targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩ ⊢ M ⦂ B}
      {D : CTI2.liftWorldLeft X⊑★ W ∣ γ′ ⊢² V ⊑ M ∶ p}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ B}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ
        (CTI2.Λ⊑² Anv zero∈A liftγ vV M⊢ D q)

  avoid-•⊑•² : ∀ {W γ M M′ C C′ A A′}
      {p∀ : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      {r : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ C′ [ A′ ]ᵗ}
      {D : W ∣ γ ⊢² M ⊑ M′ ∶ p∀}
    → ¬ (Yₚ ∈ᵗ C′ [ A′ ]ᵗ)
    → ¬ (Yₚ ∈ᵗ A′)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.•⊑•² p∀ D q r)

  avoid-•⊑² : ∀ {W γ M M′ C A B}
      {p∀ : `∀ C ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ ★}
      {r : C [ A ]ᵗ ⊑ᵂ⟨ W ⟩ B}
      {D : W ∣ γ ⊢² M ⊑ M′ ∶ p∀}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.•⊑² p∀ D q r)

  avoid-κ⊑κ² : ∀ {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {κ : Const}
      {p : constTy κ ⊑ᵂ⟨ W ⟩ constTy κ}
    → ¬ (Yₚ ∈ᵗ constTy κ)
    → AvoidᴿD Yₚ (CTI2.κ⊑κ² {W = W} {γ = γ} κ p)

  avoid-cast⊑cast² : ∀ {W γ M M′ C C′ A A′ ν ν′}
      {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      {c : ν ⊢ C ∼ A} {c′ : ν′ ⊢ C′ ∼ A′}
      {D : W ∣ γ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ A′)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.cast⊑cast² c c′ D q)

  avoid-⊑cast² : ∀ {W γ M M′ A B B′ ν}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
      {c′ : ν ⊢ B ∼ B′}
      {D : W ∣ γ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B′)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.⊑cast² c′ D q)

  avoid-⊑reveal² : ∀ {W W′ γ γ′ M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
      {c′ : Conv↑ _ B B′}
      {mono : CTI2.ImpEnvMono W W′}
      {rb : CTI2.RebaseAtᴿ W W′ Xᴿ?}
      {sc : CTI2.SameCtx γ γ′}
      {c′⊢ : targetStoreʷ W CTI2.⊢↑[ Xᴿ? ] c′}
      {D : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B′)
    → AvoidRebaseᴿ Yₚ rb
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.⊑reveal² mono rb sc c′⊢ D q)

  avoid-⊑conceal² : ∀ {W W′ γ γ′ M M′ A B B′ Xᴿ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
      {c′ : Conv↓ _ B B′}
      {mono : CTI2.ImpEnvMono W W′}
      {rb : CTI2.RebaseAtᴿ W′ W Xᴿ?}
      {sc : CTI2.SameCtx γ γ′}
      {c′⊢ : targetStoreʷ W CTI2.⊢↓[ Xᴿ? ] c′}
      {D : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B′)
    → AvoidRebaseᴿ Yₚ rb
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.⊑conceal² mono rb sc c′⊢ D q)

  avoid-cast⊑² : ∀ {W γ M M′ A A′ B ν}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
      {c : ν ⊢ A ∼ A′}
      {D : W ∣ γ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.cast⊑² c D q)

  avoid-reveal⊑² : ∀ {W W′ γ γ′ M M′ A A′ B Xᴸ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
      {c : Conv↑ _ A A′}
      {mono : CTI2.ImpEnvMono W W′}
      {rb : CTI2.RebaseAtᴸ W W′ Xᴸ?}
      {sc : CTI2.SameCtx γ γ′}
      {c⊢ : sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c}
      {D : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidRebaseᴸ Yₚ rb
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.reveal⊑² mono rb sc c⊢ D q)

  avoid-conceal⊑² : ∀ {W W′ γ γ′ M M′ A A′ B Xᴸ?}
      {p : A ⊑ᵂ⟨ W′ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
      {c : Conv↓ _ A A′}
      {mono : CTI2.ImpEnvMono W W′}
      {rb : CTI2.RebaseAtᴸ W′ W Xᴸ?}
      {sc : CTI2.SameCtx γ γ′}
      {c⊢ : sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c}
      {D : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidRebaseᴸ Yₚ rb
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ (CTI2.conceal⊑² mono rb sc c⊢ D q)

  avoid-reveal⊑reveal² : ∀
      {W Wᵖ γ γᵖ M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′} {q : B ⊑ᵂ⟨ W ⟩ B′}
      {c : Conv↑ _ A B} {c′ : Conv↑ _ A′ B′}
      {mono : CTI2.ImpEnvMono W Wᵖ}
      {rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ}
      {sc : CTI2.SameCtx γ γᵖ}
      {c⊢ : sourceStoreʷ W CTI2.⊢↑[ just Xᴸ ] c}
      {c′⊢ : targetStoreʷ W CTI2.⊢↑[ just Xᴿ ] c′}
      {D : Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B′)
    → Xᴿ ≢ Yₚ
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ
        (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ D q)

  avoid-conceal⊑conceal² : ∀
      {W Wᵖ γ γᵖ M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′} {q : B ⊑ᵂ⟨ W ⟩ B′}
      {c : Conv↓ _ A B} {c′ : Conv↓ _ A′ B′}
      {mono : CTI2.ImpEnvMono W Wᵖ}
      {rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ}
      {sc : CTI2.SameCtx γ γᵖ}
      {c⊢ : sourceStoreʷ W CTI2.⊢↓[ just Xᴸ ] c}
      {c′⊢ : targetStoreʷ W CTI2.⊢↓[ just Xᴿ ] c′}
      {D : Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p}
    → ¬ (Yₚ ∈ᵗ B′)
    → Xᴿ ≢ Yₚ
    → AvoidᴿD Yₚ D
    → AvoidᴿD Yₚ
        (CTI2.conceal⊑conceal² mono rb sc c⊢ c′⊢ D q)

  avoid-blame⊑² : ∀ {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M′ A B}
      {M′⊢ : ⟨ _ , targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩ ⊢ M′ ⦂ B}
      {p : A ⊑ᵂ⟨ W ⟩ B}
    → ¬ (Yₚ ∈ᵗ B)
    → AvoidᴿD Yₚ (CTI2.blame⊑² M′⊢ p)

  avoid-⊕⊑⊕² : ∀ {W γ} {op : Prim} {L L′ M M′}
      {p q : primArgTy op ⊑ᵂ⟨ W ⟩ primArgTy op}
      {r : primResultTy op ⊑ᵂ⟨ W ⟩ primResultTy op}
      {D₁ : W ∣ γ ⊢² L ⊑ L′ ∶ p}
      {D₂ : W ∣ γ ⊢² M ⊑ M′ ∶ q}
    → ¬ (Yₚ ∈ᵗ primResultTy op)
    → AvoidᴿD Yₚ D₁
    → AvoidᴿD Yₚ D₂
    → AvoidᴿD Yₚ (CTI2.⊕⊑⊕² op D₁ D₂ r)

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

------------------------------------------------------------------------
-- Avoidance under binders
------------------------------------------------------------------------

notOccurs→absent : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → ¬ (X ∈ᵗ A)
  → X ∉ᵗ A
notOccurs→absent {X = X} {A} X∉A with occurs? X A
notOccurs→absent X∉A | present X∈A = ⊥-elim (X∉A X∈A)
notOccurs→absent X∉A | absent X∉A′ = X∉A′

notOccurs-shift : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → ¬ (X ∈ᵗ A)
  → ¬ (Fin.suc X ∈ᵗ ⇑ᵗ A)
notOccurs-shift X∉A X∈⇑A =
  occurs-absent-⊥ X∈⇑A (shift-not-occurs (notOccurs→absent X∉A))

storeAvoid-lift : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ}
  → StoreAvoidᴿ Y Σ
  → StoreAvoidᴿ (Fin.suc Y) (store-lift Σ)
storeAvoid-lift = store-avoid-lift-suc

storeBound-lift : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ} {S}
  → Σ ∋ Y ⦂ S
  → store-lift Σ ∋ Fin.suc Y ⦂ ⇑ᵗ S
storeBound-lift Y∈ = S-lift∋ Y∈ refl

ctxAvoid-lift : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {γ′ : CtxImp (CTI2.liftWorldBoth v W)} {Y : TyVar Δᴿ}
  → CtxAvoidᴿ Y γ
  → CTI2.LiftCtx v γ γ′
  → CtxAvoidᴿ (Fin.suc Y) γ′
ctxAvoid-lift ctx-avoid-[] CTI2.lift-[] = ctx-avoid-[]
ctxAvoid-lift (ctx-avoid-∷ Y∉B avoid) (CTI2.lift-∷ liftγ) =
  ctx-avoid-∷ (notOccurs-shift Y∉B) (ctxAvoid-lift avoid liftγ)

ctxAvoid-liftᴸ : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {γ′ : CtxImp (CTI2.liftWorldLeft v W)} {Y : TyVar Δᴿ}
  → CtxAvoidᴿ Y γ
  → CTI2.LiftCtxᴸ v γ γ′
  → CtxAvoidᴿ Y γ′
ctxAvoid-liftᴸ ctx-avoid-[] CTI2.liftᴸ-[] = ctx-avoid-[]
ctxAvoid-liftᴸ (ctx-avoid-∷ Y∉B avoid) (CTI2.liftᴸ-∷ liftγ) =
  ctx-avoid-∷ Y∉B (ctxAvoid-liftᴸ avoid liftγ)

------------------------------------------------------------------------
-- Binder and context commutations
------------------------------------------------------------------------

reparkWorld-liftLeft : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → (Y : TyVar Δᴿ)
  → CTI2.liftWorldLeft v (reparkWorld W Y)
      ≡ reparkWorld (CTI2.liftWorldLeft v W) Y
reparkWorld-liftLeft v Y = refl

reparkWorld-liftBoth : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → (v : VarImp)
  → (Y : TyVar Δᴿ)
  → CTI2.liftWorldBoth v (reparkWorld W Y)
      ≡ reparkWorld (CTI2.liftWorldBoth v W) (Fin.suc Y)
reparkWorld-liftBoth v Y = refl

reparkLiftCtx : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {γ′ : CtxImp (CTI2.liftWorldBoth v W)} {Y : TyVar Δᴿ}
  → (avoid : CtxAvoidᴿ Y γ)
  → (liftγ : CTI2.LiftCtx v γ γ′)
  → CTI2.LiftCtx v (reparkCtx avoid)
      (reparkCtx (ctxAvoid-lift avoid liftγ))
reparkLiftCtx ctx-avoid-[] CTI2.lift-[] = CTI2.lift-[]
reparkLiftCtx (ctx-avoid-∷ Y∉B avoid) (CTI2.lift-∷ liftγ) =
  CTI2.lift-∷ (reparkLiftCtx avoid liftγ)

reparkLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {γ′ : CtxImp (CTI2.liftWorldLeft v W)} {Y : TyVar Δᴿ}
  → (avoid : CtxAvoidᴿ Y γ)
  → (liftγ : CTI2.LiftCtxᴸ v γ γ′)
  → CTI2.LiftCtxᴸ v (reparkCtx avoid)
      (reparkCtx (ctxAvoid-liftᴸ avoid liftγ))
reparkLiftCtxᴸ ctx-avoid-[] CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
reparkLiftCtxᴸ (ctx-avoid-∷ Y∉B avoid) (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (reparkLiftCtxᴸ avoid liftγ)

reparkCtx-tgt : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Y : TyVar Δᴿ} {γ : CtxImp W}
  → (avoid : CtxAvoidᴿ Y γ)
  → CTI2.tgtCtxʷ (reparkCtx avoid) ≡ CTI2.tgtCtxʷ γ
reparkCtx-tgt ctx-avoid-[] = refl
reparkCtx-tgt (ctx-avoid-∷ {B = B} Y∉B avoid) =
  cong (B ∷_) (reparkCtx-tgt avoid)

sameCtxAvoid : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′} {Y : TyVar Δᴿ}
  → CtxAvoidᴿ Y γ
  → CTI2.SameCtx γ γ′
  → CtxAvoidᴿ Y γ′
sameCtxAvoid ctx-avoid-[] CTI2.same-[] = ctx-avoid-[]
sameCtxAvoid (ctx-avoid-∷ Y∉B avoid) (CTI2.same-∷ sc) =
  ctx-avoid-∷ Y∉B (sameCtxAvoid avoid sc)

reparkSameCtx : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′} {Y : TyVar Δᴿ}
  → (avoid : CtxAvoidᴿ Y γ)
  → (sc : CTI2.SameCtx γ γ′)
  → CTI2.SameCtx (reparkCtx avoid)
      (reparkCtx (sameCtxAvoid avoid sc))
reparkSameCtx ctx-avoid-[] CTI2.same-[] = CTI2.same-[]
reparkSameCtx (ctx-avoid-∷ Y∉B avoid) (CTI2.same-∷ sc) =
  CTI2.same-∷ (reparkSameCtx avoid sc)

transportStoreBound : ∀ {Δ} {Σ Σ′ : TyStore Δ}
    {Y : TyVar Δ} {S : Ty Δ}
  → Σ ≡ Σ′
  → Σ ∋ Y ⦂ S
  → Σ′ ∋ Y ⦂ S
transportStoreBound refl Y∈ = Y∈

transportStoreAvoid : ∀ {Δ} {Σ Σ′ : TyStore Δ}
    {Y : TyVar Δ}
  → Σ ≡ Σ′
  → StoreAvoidᴿ Y Σ
  → StoreAvoidᴿ Y Σ′
transportStoreAvoid refl avoid = avoid

------------------------------------------------------------------------
-- Avoidance of canonical store representations
------------------------------------------------------------------------

mutual
  resolveVar-avoid : ∀ {Δ} {Σ : TyStore Δ} {Y X : TyVar Δ} {S₀}
    → Σ ∋ Y ⦂ S₀
    → StoreAvoidᴿ Y Σ
    → X ≢ Y
    → ¬ (Y ∈ᵗ CTI2.resolveVar Σ X)
  resolveVar-avoid {X = Fin.zero}
      (S-lift∋ Y∈ refl) (store-avoid-lift-suc avoid) X≠Y ()
  resolveVar-avoid {X = Fin.suc X}
      (S-lift∋ Y∈ refl) (store-avoid-lift-suc avoid) X≠Y Y∈R =
    resolveVar-avoid Y∈ avoid
      (λ eq → X≠Y (cong Fin.suc eq)) (unshift-occurs Y∈R)
  resolveVar-avoid {X = Fin.zero}
      (Z∋ refl) store-avoid-bind-zero X≠Y Y∈R =
    ⊥-elim (X≠Y refl)
  resolveVar-avoid {X = Fin.suc X}
      (Z∋ refl) store-avoid-bind-zero X≠Y Y∈R =
    zero-not-shift Y∈R
  resolveVar-avoid {X = Fin.zero}
      (S-bind∋ Y∈ refl) (store-avoid-bind-suc Y∉A avoid)
      X≠Y Y∈R =
    resolveRep-avoid Y∈ avoid Y∉A (unshift-occurs Y∈R)
  resolveVar-avoid {X = Fin.suc X}
      (S-bind∋ Y∈ refl) (store-avoid-bind-suc Y∉A avoid)
      X≠Y Y∈R =
    resolveVar-avoid Y∈ avoid
      (λ eq → X≠Y (cong Fin.suc eq)) (unshift-occurs Y∈R)

  resolveRep-avoid : ∀ {Δ} {Σ : TyStore Δ} {Y : TyVar Δ}
      {S₀ A}
    → Σ ∋ Y ⦂ S₀
    → StoreAvoidᴿ Y Σ
    → ¬ (Y ∈ᵗ A)
    → ¬ (Y ∈ᵗ CTI2.resolveRep Σ A)
  resolveRep-avoid {Y = Y} {A = ＇ X} Y∈ avoid Y∉X Y∈R
      with Fin._≟_ X Y
  resolveRep-avoid {Y = Y} {A = ＇ .Y} Y∈ avoid Y∉X Y∈R
      | yes refl = ⊥-elim (Y∉X var-∈)
  resolveRep-avoid {Y = Y} {A = ＇ X} Y∈ avoid Y∉X Y∈R
      | no X≠Y = resolveVar-avoid Y∈ avoid X≠Y Y∈R
  resolveRep-avoid {A = ‵ ι} Y∈ avoid Y∉A Y∈R = Y∉A Y∈R
  resolveRep-avoid {A = ★} Y∈ avoid Y∉A Y∈R = Y∉A Y∈R
  resolveRep-avoid {A = A ⇒ B} Y∈ avoid Y∉AB Y∈R = Y∉AB Y∈R
  resolveRep-avoid {A = `∀ A} Y∈ avoid Y∉A Y∈R = Y∉A Y∈R

------------------------------------------------------------------------
-- Rebase transport
------------------------------------------------------------------------

reparkIndex-toRename : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
    (Y : TyVar Δᴿ)
  → reparkIndex ηᴿ Y ≡ Fin.inject₁ (toRenameᵗ ηᴿ Y)
reparkIndex-toRename empty ()
reparkIndex-toRename (keep ηᴿ) Fin.zero = refl
reparkIndex-toRename (keep ηᴿ) (Fin.suc Y) =
  cong Fin.suc (reparkIndex-toRename ηᴿ Y)
reparkIndex-toRename (skip ηᴿ) Y =
  cong Fin.suc (reparkIndex-toRename ηᴿ Y)

reparkIndex-eq : ∀ {Δᴿ Δ} {η₁ η₂ : Δᴿ ↪ᵗ Δ}
    {Y : TyVar Δᴿ}
  → toRenameᵗ η₁ Y ≡ toRenameᵗ η₂ Y
  → reparkIndex η₁ Y ≡ reparkIndex η₂ Y
reparkIndex-eq {η₁ = η₁} {η₂} {Y} eq =
  trans (reparkIndex-toRename η₁ Y)
    (trans (cong Fin.inject₁ eq) (sym (reparkIndex-toRename η₂ Y)))

insert-map-eq : ∀ {Δ} {k₁ k₂ : TyVar (Nat.suc Δ)}
    {X₁ X₂ : TyVar Δ}
  → k₁ ≡ k₂
  → X₁ ≡ X₂
  → toRenameᵗ (insertᶜ k₁) X₁ ≡ toRenameᵗ (insertᶜ k₂) X₂
insert-map-eq refl refl = refl

rebaseIndex-off : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ} {Y : TyVar Δᴿ}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → Xᴿ ≢ Y
  → reparkIndex (ηᴿʷ W′) Y ≡ reparkIndex (ηᴿʷ W) Y
rebaseIndex-off rb Xᴿ≠Y =
  reparkIndex-eq (CTI2.RebaseAt.ηᴿ-off-pivot rb
    (λ eq → Xᴿ≠Y (sym eq)))

renameEnvMono-insert : ∀ {Δ} {μ ν : ImpEnv Δ}
    {k₁ k₂ : TyVar (Nat.suc Δ)}
  → k₁ ≡ k₂
  → (∀ Z → μ Z ≡ X⊑★ → ν Z ≡ X⊑★)
  → ∀ Z → renameEnv (insertᶜ k₁) μ Z ≡ X⊑★
  → renameEnv (insertᶜ k₂) ν Z ≡ X⊑★
renameEnvMono-insert {k₁ = k} refl mono =
  CR.renameEnvMono (insertᶜ k) mono

reparkImpEnvMono : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Y : TyVar Δᴿ}
  → reparkIndex (ηᴿʷ W) Y ≡ reparkIndex (ηᴿʷ W′) Y
  → CTI2.ImpEnvMono W W′
  → CTI2.ImpEnvMono (reparkWorld W Y) (reparkWorld W′ Y)
reparkImpEnvMono {W = W} {W′} {Y} k-eq mono =
  renameEnvMono-insert k-eq mono

reparkRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ} {Y : TyVar Δᴿ}
    {S₀ : Ty Δᴿ}
  → targetStoreʷ W′ ∋ Y ⦂ S₀
  → StoreAvoidᴿ Y (targetStoreʷ W′)
  → Xᴿ ≢ Y
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.RebaseAt (reparkWorld W Y) (reparkWorld W′ Y) Xᴸ Xᴿ
reparkRebaseAt {Δᴸ = Δᴸ} {W = W} {W′} {Xᴸ} {Xᴿ} {Y}
    Y∈ avoid Xᴿ≠Y
    (CTI2.rebase-at (CTI2.same-runtime source-eq target-eq)
      offL offR aligned anchor (CTI2.store-rep-imp represented)) =
  CTI2.rebase-at (CTI2.same-runtime source-eq target-eq)
    left-off right-off repark-aligned
    repark-anchor
    (CTI2.store-rep-imp
      (repark-⊑ᵂ {W = W′} {Yₚ = Y}
        (resolveVar-avoid Y∈ avoid Xᴿ≠Y) represented))
  where
  k-eq : reparkIndex (ηᴿʷ W′) Y ≡ reparkIndex (ηᴿʷ W) Y
  k-eq = reparkIndex-eq (offR (λ eq → Xᴿ≠Y (sym eq)))

  left-off : ∀ {Z} → Z ≢ Xᴸ
    → toRenameᵗ (ηᴸʷ (reparkWorld W′ Y)) Z
        ≡ toRenameᵗ (ηᴸʷ (reparkWorld W Y)) Z
  left-off {Z} Z≠Xᴸ =
    trans (toRenameᵗ-∘ (insertᶜ (reparkIndex (ηᴿʷ W′) Y))
        (ηᴸʷ W′) Z)
      (trans (insert-map-eq k-eq (offL Z≠Xᴸ))
        (sym (toRenameᵗ-∘
          (insertᶜ (reparkIndex (ηᴿʷ W) Y)) (ηᴸʷ W) Z)))

  right-off : ∀ {Z} → Z ≢ Xᴿ
    → toRenameᵗ (ηᴿʷ (reparkWorld W′ Y)) Z
        ≡ toRenameᵗ (ηᴿʷ (reparkWorld W Y)) Z
  right-off {Z} Z≠Xᴿ with Fin._≟_ Z Y
  right-off {.Y} Z≠Xᴿ | yes refl =
    trans (reparkEmbedᴿ-park (ηᴿʷ W′) Y)
      (trans k-eq (sym (reparkEmbedᴿ-park (ηᴿʷ W) Y)))
  right-off {Z} Z≠Xᴿ | no Z≠Y =
    trans (reparkEmbedᴿ-off (ηᴿʷ W′) Y Z Z≠Y)
      (trans (insert-map-eq k-eq (offR Z≠Xᴿ))
        (sym (reparkEmbedᴿ-off (ηᴿʷ W) Y Z Z≠Y)))

  repark-aligned :
    toRenameᵗ (ηᴸʷ (reparkWorld W′ Y)) Xᴸ
      ≡ toRenameᵗ (ηᴿʷ (reparkWorld W′ Y)) Xᴿ
  repark-aligned =
    trans (toRenameᵗ-∘ (insertᶜ (reparkIndex (ηᴿʷ W′) Y))
        (ηᴸʷ W′) Xᴸ)
      (trans (cong
          (toRenameᵗ (insertᶜ (reparkIndex (ηᴿʷ W′) Y)))
          aligned)
        (sym (reparkEmbedᴿ-off (ηᴿʷ W′) Y Xᴿ Xᴿ≠Y)))

  repark-anchor :
      toRenameᵗ (ηᴿʷ (reparkWorld W Y)) Xᴿ
        ≢ toRenameᵗ (ηᴿʷ (reparkWorld W′ Y)) Xᴿ
    → Σ[ Xₒ ∈ TyVar Δᴸ ]
        toRenameᵗ (ηᴸʷ (reparkWorld W Y)) Xₒ
          ≡ toRenameᵗ (ηᴿʷ (reparkWorld W Y)) Xᴿ
  repark-anchor moved with anchor
      (λ eq → moved
        (trans (reparkEmbedᴿ-off (ηᴿʷ W) Y Xᴿ Xᴿ≠Y)
          (trans (insert-map-eq (sym k-eq) eq)
            (sym (reparkEmbedᴿ-off (ηᴿʷ W′) Y Xᴿ Xᴿ≠Y)))))
  repark-anchor moved | Xₒ , eq = Xₒ ,
    trans (toRenameᵗ-∘
        (insertᶜ (reparkIndex (ηᴿʷ W) Y)) (ηᴸʷ W) Xₒ)
      (trans (cong
          (toRenameᵗ (insertᶜ (reparkIndex (ηᴿʷ W) Y))) eq)
        (sym (reparkEmbedᴿ-off (ηᴿʷ W) Y Xᴿ Xᴿ≠Y)))

repark-source-mark : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (Y : TyVar Δᴿ)
    (Xᴸ : TyVar Δᴸ)
  → impEnvʷ (reparkWorld W Y)
      (toRenameᵗ (ηᴸʷ (reparkWorld W Y)) Xᴸ)
      ≡ impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ)
repark-source-mark W Y Xᴸ =
  trans (cong (impEnvʷ (reparkWorld W Y))
      (toRenameᵗ-∘ (insertᶜ (reparkIndex (ηᴿʷ W) Y))
        (ηᴸʷ W) Xᴸ))
    (repark-mark-image W Y (toRenameᵗ (ηᴸʷ W) Xᴸ))

repark-disaligned : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (Y : TyVar Δᴿ)
    {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (ηᴿʷ W) Xᴿ ≢
      toRenameᵗ (ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (ηᴿʷ (reparkWorld W Y)) Xᴿ ≢
      toRenameᵗ (ηᴸʷ (reparkWorld W Y)) Xᴸ
repark-disaligned W Y {Xᴸ} disaligned Xᴿ eq with Fin._≟_ Xᴿ Y
repark-disaligned W Y {Xᴸ} disaligned .Y eq | yes refl =
  insertᶜ-misses (reparkIndex (ηᴿʷ W) Y)
    (toRenameᵗ (ηᴸʷ W) Xᴸ)
    (trans (sym source-image)
      (trans (sym eq) (reparkEmbedᴿ-park (ηᴿʷ W) Y)))
  where
  source-image :
    toRenameᵗ (ηᴸʷ (reparkWorld W Y)) Xᴸ ≡
      toRenameᵗ (insertᶜ (reparkIndex (ηᴿʷ W) Y))
        (toRenameᵗ (ηᴸʷ W) Xᴸ)
  source-image =
    toRenameᵗ-∘ (insertᶜ (reparkIndex (ηᴿʷ W) Y))
      (ηᴸʷ W) Xᴸ
repark-disaligned W Y {Xᴸ} disaligned Xᴿ eq | no Xᴿ≠Y =
  disaligned Xᴿ
    (toRenameᵗ-injective (insertᶜ (reparkIndex (ηᴿʷ W) Y))
      (trans (sym (reparkEmbedᴿ-off (ηᴿʷ W) Y Xᴿ Xᴿ≠Y))
        (trans eq
          (toRenameᵗ-∘ (insertᶜ (reparkIndex (ηᴿʷ W) Y))
            (ηᴸʷ W) Xᴸ))))

reparkRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴿ?} {Y : TyVar Δᴿ}
    {S₀ : Ty Δᴿ}
  → targetStoreʷ W′ ∋ Y ⦂ S₀
  → StoreAvoidᴿ Y (targetStoreʷ W′)
  → (rb : CTI2.RebaseAtᴿ W W′ Xᴿ?)
  → AvoidRebaseᴿ Y rb
  → CTI2.RebaseAtᴿ (reparkWorld W Y) (reparkWorld W′ Y) Xᴿ?
reparkRebaseAtᴿ Y∈ avoid CTI2.rebase-idᴿ tt = CTI2.rebase-idᴿ
reparkRebaseAtᴿ Y∈ avoid (CTI2.rebase-varᴿ rb) Xᴿ≠Y =
  CTI2.rebase-varᴿ (reparkRebaseAt Y∈ avoid Xᴿ≠Y rb)

reparkRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ?} {Y : TyVar Δᴿ}
    {S₀ : Ty Δᴿ}
  → targetStoreʷ W′ ∋ Y ⦂ S₀
  → StoreAvoidᴿ Y (targetStoreʷ W′)
  → (rb : CTI2.RebaseAtᴸ W W′ Xᴸ?)
  → AvoidRebaseᴸ Y rb
  → CTI2.RebaseAtᴸ (reparkWorld W Y) (reparkWorld W′ Y) Xᴸ?
reparkRebaseAtᴸ Y∈ avoid CTI2.rebase-idᴸ tt = CTI2.rebase-idᴸ
reparkRebaseAtᴸ Y∈ avoid (CTI2.rebase-varᴸ rb) Xᴿ≠Y =
  CTI2.rebase-varᴸ (reparkRebaseAt Y∈ avoid Xᴿ≠Y rb)
reparkRebaseAtᴸ {W = W} {Y = Y} Y∈ avoid
    (CTI2.rebase-onlyᴸ {Xᴸ = Xᴸ} mark disaligned represented) tt =
  CTI2.rebase-onlyᴸ
    (trans (repark-source-mark W Y Xᴸ) mark)
    (repark-disaligned W Y disaligned)
    (repark-⊑ᵂ {W = W} {Yₚ = Y} (λ ()) represented)

rebaseAt-target-eq : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → targetStoreʷ W′ ≡ targetStoreʷ W
rebaseAt-target-eq rb =
  CTI2.SameRuntime.targetStore-same (CTI2.RebaseAt.sameRuntime rb)

rebaseAtᴿ-target-eq : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴿ?}
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → targetStoreʷ W′ ≡ targetStoreʷ W
rebaseAtᴿ-target-eq CTI2.rebase-idᴿ = refl
rebaseAtᴿ-target-eq (CTI2.rebase-varᴿ rb) = rebaseAt-target-eq rb

rebaseAtᴸ-target-eq : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → targetStoreʷ W′ ≡ targetStoreʷ W
rebaseAtᴸ-target-eq CTI2.rebase-idᴸ = refl
rebaseAtᴸ-target-eq (CTI2.rebase-varᴸ rb) = rebaseAt-target-eq rb
rebaseAtᴸ-target-eq (CTI2.rebase-onlyᴸ mark disaligned represented) = refl

rebaseIndexᴿ-off : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴿ?} {Y : TyVar Δᴿ}
  → (rb : CTI2.RebaseAtᴿ W W′ Xᴿ?)
  → AvoidRebaseᴿ Y rb
  → reparkIndex (ηᴿʷ W′) Y ≡ reparkIndex (ηᴿʷ W) Y
rebaseIndexᴿ-off CTI2.rebase-idᴿ tt = refl
rebaseIndexᴿ-off (CTI2.rebase-varᴿ rb) Xᴿ≠Y =
  rebaseIndex-off rb Xᴿ≠Y

rebaseIndexᴸ-off : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ?} {Y : TyVar Δᴿ}
  → (rb : CTI2.RebaseAtᴸ W W′ Xᴸ?)
  → AvoidRebaseᴸ Y rb
  → reparkIndex (ηᴿʷ W′) Y ≡ reparkIndex (ηᴿʷ W) Y
rebaseIndexᴸ-off CTI2.rebase-idᴸ tt = refl
rebaseIndexᴸ-off (CTI2.rebase-varᴸ rb) Xᴿ≠Y =
  rebaseIndex-off rb Xᴿ≠Y
rebaseIndexᴸ-off (CTI2.rebase-onlyᴸ mark disaligned represented) tt =
  refl

avoid-right : ∀ {Δᴸ Δᴿ Δ} {Y : TyVar Δᴿ}
    {W : World Δᴸ Δᴿ Δ} {γ M N A B} {p : A ⊑ᵂ⟨ W ⟩ B}
    {D : W ∣ γ ⊢² M ⊑ N ∶ p}
  → AvoidᴿD Y D
  → ¬ (Y ∈ᵗ B)
avoid-right (avoid-x⊑x² Y∉B) = Y∉B
avoid-right (avoid-ƛ⊑ƛ² Y∉B avoid) = Y∉B
avoid-right (avoid-·⊑·² Y∉B avoid₁ avoid₂) = Y∉B
avoid-right (avoid-Λ⊑Λ² Y∉B avoid) = Y∉B
avoid-right (avoid-Λ⊑² Y∉B avoid) = Y∉B
avoid-right (avoid-•⊑•² Y∉B Y∉A′ avoid) = Y∉B
avoid-right (avoid-•⊑² Y∉B avoid) = Y∉B
avoid-right (avoid-κ⊑κ² Y∉B) = Y∉B
avoid-right (avoid-cast⊑cast² Y∉B avoid) = Y∉B
avoid-right (avoid-⊑cast² Y∉B avoid) = Y∉B
avoid-right (avoid-⊑reveal² Y∉B rb-avoid avoid) = Y∉B
avoid-right (avoid-⊑conceal² Y∉B rb-avoid avoid) = Y∉B
avoid-right (avoid-cast⊑² Y∉B avoid) = Y∉B
avoid-right (avoid-reveal⊑² Y∉B rb-avoid avoid) = Y∉B
avoid-right (avoid-conceal⊑² Y∉B rb-avoid avoid) = Y∉B
avoid-right (avoid-reveal⊑reveal² Y∉B Xᴿ≠Y avoid) = Y∉B
avoid-right (avoid-conceal⊑conceal² Y∉B Xᴿ≠Y avoid) = Y∉B
avoid-right (avoid-blame⊑² Y∉B) = Y∉B
avoid-right (avoid-⊕⊑⊕² Y∉B avoid₁ avoid₂) = Y∉B

notOccurs-fun-left : ∀ {Δ} {Y : TyVar Δ} {A B : Ty Δ}
  → ¬ (Y ∈ᵗ A ⇒ B)
  → ¬ (Y ∈ᵗ A)
notOccurs-fun-left Y∉AB Y∈A = Y∉AB (∈-fun-left Y∈A)

------------------------------------------------------------------------
-- Derivation transport
------------------------------------------------------------------------

⊢²-repark : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {Yₚ : TyVar Δᴿ} {S₀ : Ty Δᴿ} {M N A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → targetStoreʷ W ∋ Yₚ ⦂ S₀
  → StoreAvoidᴿ Yₚ (targetStoreʷ W)
  → (avoid : CtxAvoidᴿ Yₚ γ)
  → (D : W ∣ γ ⊢² M ⊑ N ∶ p)
  → AvoidᴿD Yₚ D
  → (p′ : A ⊑ᵂ⟨ reparkWorld W Yₚ ⟩ B)
  → reparkWorld W Yₚ ∣ reparkCtx avoid ⊢² M ⊑ N ∶ p′
⊢²-repark {W = W} Y∈ store-avoid avoid (CTI2.x⊑x² x∈)
    (avoid-x⊑x² Y∉B) p′ =
  CR.⊢²-retarget (CTI2.x⊑x² (repark-∋ʷ avoid x∈))
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.ƛ⊑ƛ² {pA = pA} {pB = pB} D)
    (avoid-ƛ⊑ƛ² Y∉A′⇒B′ avoid-D) p′ =
  CR.⊢²-retarget (CTI2.ƛ⊑ƛ²
    (⊢²-repark {W = W} Y∈ store-avoid
      (ctx-avoid-∷ (notOccurs-fun-left Y∉A′⇒B′) avoid)
      D avoid-D (repark-⊑ᵂ {W = W} (avoid-right avoid-D) pB)))
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.·⊑·² {pA = pA} {pB = pB} D₁ D₂)
    (avoid-·⊑·² Y∉B′ avoid₁ avoid₂) p′ =
  CR.⊢²-retarget (CTI2.·⊑·²
    (⊢²-repark {W = W} Y∈ store-avoid avoid D₁ avoid₁
      (⇒⊑⇒ (repark-⊑ᵂ {W = W} (avoid-right avoid₂) pA)
        (repark-⊑ᵂ {W = W} Y∉B′ pB)))
    (⊢²-repark {W = W} Y∈ store-avoid avoid D₂ avoid₂
      (repark-⊑ᵂ {W = W} (avoid-right avoid₂) pA)))
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.Λ⊑Λ² {p = p} liftγ vV vV′ D q)
    (avoid-Λ⊑Λ² Y∉∀B avoid-D) p′ =
  CTI2.Λ⊑Λ² (reparkLiftCtx avoid liftγ) vV vV′
    (⊢²-repark {W = CTI2.liftWorldBoth X⊑X W}
      (storeBound-lift Y∈) (storeAvoid-lift store-avoid)
      (ctxAvoid-lift avoid liftγ) D avoid-D
      (repark-⊑ᵂ {W = CTI2.liftWorldBoth X⊑X W}
        (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {B = B} Y∈ store-avoid avoid
    (CTI2.Λ⊑² {p = p} Anv zero∈A liftγ vV M⊢ D q)
    (avoid-Λ⊑² Y∉B avoid-D) p′ =
  CTI2.Λ⊑² Anv zero∈A (reparkLiftCtxᴸ avoid liftγ) vV
    (subst (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ B)
      (sym (reparkCtx-tgt avoid)) M⊢)
    (⊢²-repark {W = CTI2.liftWorldLeft X⊑★ W}
      Y∈ store-avoid (ctxAvoid-liftᴸ avoid liftγ) D avoid-D
      (repark-⊑ᵂ {W = CTI2.liftWorldLeft X⊑★ W}
        (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.•⊑•² p∀ D q r)
    (avoid-•⊑•² Y∉R Y∉A′ avoid-D) p′ =
  CTI2.•⊑•² (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p∀)
    (⊢²-repark {W = W} Y∈ store-avoid avoid D avoid-D
      (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p∀))
    (repark-⊑ᵂ {W = W} Y∉A′ q) p′
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.•⊑² p∀ D q r) (avoid-•⊑² Y∉B avoid-D) p′ =
  CTI2.•⊑² (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p∀)
    (⊢²-repark {W = W} Y∈ store-avoid avoid D avoid-D
      (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p∀))
    (repark-⊑ᵂ {W = W} (λ ()) q) p′
⊢²-repark {W = W} Y∈ store-avoid avoid (CTI2.κ⊑κ² κ p)
    (avoid-κ⊑κ² Y∉B) p′ =
  CTI2.κ⊑κ² κ p′
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.cast⊑cast² {p = p} c c′ D q)
    (avoid-cast⊑cast² Y∉A′ avoid-D) p′ =
  CTI2.cast⊑cast² c c′
    (⊢²-repark {W = W} Y∈ store-avoid avoid D avoid-D
      (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.⊑cast² {p = p} c′ D q)
    (avoid-⊑cast² Y∉B′ avoid-D) p′ =
  CTI2.⊑cast² c′
    (⊢²-repark {W = W} Y∈ store-avoid avoid D avoid-D
      (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.cast⊑² {p = p} c D q)
    (avoid-cast⊑² Y∉B avoid-D) p′ =
  CTI2.cast⊑² c
    (⊢²-repark {W = W} Y∈ store-avoid avoid D avoid-D
      (repark-⊑ᵂ {W = W} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {B = B} Y∈ store-avoid avoid
    (CTI2.blame⊑² M′⊢ p) (avoid-blame⊑² Y∉B) p′ =
  CTI2.blame⊑²
    (subst (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ B)
      (sym (reparkCtx-tgt avoid)) M′⊢)
    p′
⊢²-repark {W = W} Y∈ store-avoid avoid
    (CTI2.⊕⊑⊕² op {p = p} {q = q} D₁ D₂ r)
    (avoid-⊕⊑⊕² Y∉R avoid₁ avoid₂) p′ =
  CTI2.⊕⊑⊕² op
    (⊢²-repark {W = W} Y∈ store-avoid avoid D₁ avoid₁
      (repark-⊑ᵂ {W = W} (avoid-right avoid₁) p))
    (⊢²-repark {W = W} Y∈ store-avoid avoid D₂ avoid₂
      (repark-⊑ᵂ {W = W} (avoid-right avoid₂) q)) p′
⊢²-repark {W = W} {Yₚ = Y} Y∈ store-avoid avoid
    (CTI2.⊑reveal² {W′ = W′} {p = p} mono rb sc c′⊢ D q)
    (avoid-⊑reveal² Y∉B′ rb-avoid avoid-D) p′ =
  CTI2.⊑reveal²
    (reparkImpEnvMono {W = W} {W′ = W′} {Y = Y}
      (sym (rebaseIndexᴿ-off rb rb-avoid)) mono)
    (reparkRebaseAtᴿ
      (transportStoreBound (sym (rebaseAtᴿ-target-eq rb)) Y∈)
      (transportStoreAvoid (sym (rebaseAtᴿ-target-eq rb)) store-avoid)
      rb rb-avoid)
    (reparkSameCtx avoid sc) c′⊢
    (⊢²-repark {W = W′}
      (transportStoreBound (sym (rebaseAtᴿ-target-eq rb)) Y∈)
      (transportStoreAvoid (sym (rebaseAtᴿ-target-eq rb)) store-avoid)
      (sameCtxAvoid avoid sc) D avoid-D
      (repark-⊑ᵂ {W = W′} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {Yₚ = Y} Y∈ store-avoid avoid
    (CTI2.⊑conceal² {W′ = W′} {p = p} mono rb sc c′⊢ D q)
    (avoid-⊑conceal² Y∉B′ rb-avoid avoid-D) p′ =
  CTI2.⊑conceal²
    (reparkImpEnvMono {W = W} {W′ = W′} {Y = Y}
      (rebaseIndexᴿ-off rb rb-avoid) mono)
    (reparkRebaseAtᴿ Y∈ store-avoid rb rb-avoid)
    (reparkSameCtx avoid sc) c′⊢
    (⊢²-repark {W = W′}
      (transportStoreBound (rebaseAtᴿ-target-eq rb) Y∈)
      (transportStoreAvoid (rebaseAtᴿ-target-eq rb) store-avoid)
      (sameCtxAvoid avoid sc) D avoid-D
      (repark-⊑ᵂ {W = W′} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {Yₚ = Y} Y∈ store-avoid avoid
    (CTI2.reveal⊑² {W′ = W′} {p = p} mono rb sc c⊢ D q)
    (avoid-reveal⊑² Y∉B rb-avoid avoid-D) p′ =
  CTI2.reveal⊑²
    (reparkImpEnvMono {W = W} {W′ = W′} {Y = Y}
      (sym (rebaseIndexᴸ-off rb rb-avoid)) mono)
    (reparkRebaseAtᴸ
      (transportStoreBound (sym (rebaseAtᴸ-target-eq rb)) Y∈)
      (transportStoreAvoid (sym (rebaseAtᴸ-target-eq rb)) store-avoid)
      rb rb-avoid)
    (reparkSameCtx avoid sc) c⊢
    (⊢²-repark {W = W′}
      (transportStoreBound (sym (rebaseAtᴸ-target-eq rb)) Y∈)
      (transportStoreAvoid (sym (rebaseAtᴸ-target-eq rb)) store-avoid)
      (sameCtxAvoid avoid sc) D avoid-D
      (repark-⊑ᵂ {W = W′} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {Yₚ = Y} Y∈ store-avoid avoid
    (CTI2.conceal⊑² {W′ = W′} {p = p} mono rb sc c⊢ D q)
    (avoid-conceal⊑² Y∉B rb-avoid avoid-D) p′ =
  CTI2.conceal⊑²
    (reparkImpEnvMono {W = W} {W′ = W′} {Y = Y}
      (rebaseIndexᴸ-off rb rb-avoid) mono)
    (reparkRebaseAtᴸ Y∈ store-avoid rb rb-avoid)
    (reparkSameCtx avoid sc) c⊢
    (⊢²-repark {W = W′}
      (transportStoreBound (rebaseAtᴸ-target-eq rb) Y∈)
      (transportStoreAvoid (rebaseAtᴸ-target-eq rb) store-avoid)
      (sameCtxAvoid avoid sc) D avoid-D
      (repark-⊑ᵂ {W = W′} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {Yₚ = Y} Y∈ store-avoid avoid
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc c⊢ c′⊢ D q)
    (avoid-reveal⊑reveal² Y∉B′ Xᴿ≠Y avoid-D) p′ =
  CTI2.reveal⊑reveal²
    (reparkImpEnvMono {W = W} {W′ = Wᵖ} {Y = Y}
      (sym (rebaseIndex-off rb Xᴿ≠Y)) mono)
    (reparkRebaseAt
      (transportStoreBound (sym (rebaseAt-target-eq rb)) Y∈)
      (transportStoreAvoid (sym (rebaseAt-target-eq rb)) store-avoid)
      Xᴿ≠Y rb)
    (reparkSameCtx avoid sc) c⊢ c′⊢
    (⊢²-repark {W = Wᵖ}
      (transportStoreBound (sym (rebaseAt-target-eq rb)) Y∈)
      (transportStoreAvoid (sym (rebaseAt-target-eq rb)) store-avoid)
      (sameCtxAvoid avoid sc) D avoid-D
      (repark-⊑ᵂ {W = Wᵖ} (avoid-right avoid-D) p)) p′
⊢²-repark {W = W} {Yₚ = Y} Y∈ store-avoid avoid
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc c⊢ c′⊢ D q)
    (avoid-conceal⊑conceal² Y∉B′ Xᴿ≠Y avoid-D) p′ =
  CTI2.conceal⊑conceal²
    (reparkImpEnvMono {W = W} {W′ = Wᵖ} {Y = Y}
      (rebaseIndex-off rb Xᴿ≠Y) mono)
    (reparkRebaseAt Y∈ store-avoid Xᴿ≠Y rb)
    (reparkSameCtx avoid sc) c⊢ c′⊢
    (⊢²-repark {W = Wᵖ}
      (transportStoreBound (rebaseAt-target-eq rb) Y∈)
      (transportStoreAvoid (rebaseAt-target-eq rb) store-avoid)
      (sameCtxAvoid avoid sc) D avoid-D
      (repark-⊑ᵂ {W = Wᵖ} (avoid-right avoid-D) p)) p′

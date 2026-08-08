module proof.DGG.CenterRename where

-- File Charter:
--   * Transports cast-term-imprecision derivations along an
--     order-preserving injection of their center type context.
--   * Composes world embeddings, fills fresh centers with X⊑★, and
--     transports contexts, rebasing evidence, and recursive worlds.
--   * Exports the general center-renaming theorem and its weakening
--     specialization.

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
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; wk↪ᵗ)
open import Imprecision
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)
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

renameRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (π : Δ ↪ᵗ Δ′)
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → CTI2.RebaseAtᴿ (renameWorld π W) (renameWorld π W′) Xᴿ?
renameRebaseAtᴿ π CTI2.rebase-idᴿ = CTI2.rebase-idᴿ
renameRebaseAtᴿ π (CTI2.rebase-varᴿ rb) =
  CTI2.rebase-varᴿ (renameRebaseAt π rb)

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
    (CTI2.conceal⊑² {W′ = W′} {p = p} mono rb sc c⊢ M⊑N q) p′ =
  CTI2.conceal⊑² (renameImpEnvMono {W = W} {W′ = W′} π mono)
    (renameRebaseAtᴸ {W = W′} {W′ = W} π rb)
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
      mono rb sc c⊢ c′⊢ M⊑N q) p′ =
  CTI2.conceal⊑conceal²
    (renameImpEnvMono {W = W} {W′ = Wᵖ} π mono)
    (renameRebaseAt {W = Wᵖ} {W′ = W} π rb)
    (renameSameCtx {W = W} {W′ = Wᵖ} π sc) c⊢ c′⊢
    (⊢²-rename-center {W = Wᵖ} π M⊑N
      (rename-⊑ᵂ {W = Wᵖ} π p)) p′
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

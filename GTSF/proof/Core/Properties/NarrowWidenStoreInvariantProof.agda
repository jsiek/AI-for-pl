module proof.Core.Properties.NarrowWidenStoreInvariantProof where

-- File Charter:
--   * Constructs and preserves the deterministic store invariant used by
--     narrowing and widening metatheory.
--   * Reuses the canonical Nu-store lift, membership, and uniqueness lemmas.
--   * Depends only on the invariant definitions and core store/type
--     properties, not on narrowing or widening proof implementations.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
import Store
open import Store using (StoreWf; StoreWfAt; bound; wfTy)
open import proof.Core.Properties.NarrowWidenStoreInvariantDef
open import proof.Core.Properties.NuStoreProperties
  using
    ( StoreUnique-bind
    ; StoreUnique-⟰ᵗ
    ; StoreWfAt-cons
    ; StoreWfAt-⟰ᵗ
    ; ∈-⟰ᵗ-inv
    ; ∈-⟰ᵗ-zero
    ; ∈-renameStoreᵗ
    )
open import proof.Core.Properties.TypeProperties
  using
    ( TyRenameWf-suc
    ; WfTy-un⇑ᵗ
    ; predᵗ
    ; renameᵗ-pred-suc
    ; renameᵗ-preserves-WfTy
    )

StoreWf⇒det :
  ∀ {Δ Σ} →
  StoreWf Δ Σ →
  StoreDetWf Δ Σ
StoreWf⇒det wfΣ =
  record
    { at = Store.at wfΣ
    ; wfOlder = Store.wfOlder wfΣ
    ; unique = Store.unique wfΣ
    }

StoreUnique-⟰ᵗ-inv :
  ∀ {Σ} →
  StoreUnique (⟰ᵗ Σ) →
  StoreUnique Σ
StoreUnique-⟰ᵗ-inv uniqueΣ {A = A} {B = B} h₁ h₂ =
  trans (sym (renameᵗ-pred-suc A))
    (trans
      (cong (renameᵗ predᵗ)
        (uniqueΣ (∈-renameStoreᵗ suc h₁) (∈-renameStoreᵗ suc h₂)))
      (renameᵗ-pred-suc B))

private
  <-suc-inv :
    ∀ {α Δ} →
    suc α < suc Δ →
    α < Δ
  <-suc-inv (s<s α<Δ) = α<Δ

StoreDetWf-⟰ᵗ :
  ∀ {Δ Σ} →
  StoreDetWf Δ Σ →
  StoreDetWf (suc Δ) (⟰ᵗ Σ)
StoreDetWf-⟰ᵗ wfΣ =
  record
    { at = StoreWfAt-⟰ᵗ (at wfΣ)
    ; wfOlder = wfOlder′
    ; unique = StoreUnique-⟰ᵗ (unique wfΣ)
    }
  where
    wfOlder′ :
      ∀ {α A} →
      (α , A) ∈ ⟰ᵗ _ →
      WfTy α A
    wfOlder′ {zero} h =
      ⊥-elim (∈-⟰ᵗ-zero h)
    wfOlder′ {suc α} h with ∈-⟰ᵗ-inv h
    wfOlder′ {suc α} h | A , eq , h′ =
      subst (WfTy (suc α)) (sym eq)
        (renameᵗ-preserves-WfTy (wfOlder wfΣ h′) TyRenameWf-suc)

StoreDetWf-⟰ᵗ-inv :
  ∀ {Δ Σ} →
  StoreDetWf (suc Δ) (⟰ᵗ Σ) →
  StoreDetWf Δ Σ
StoreDetWf-⟰ᵗ-inv wfΣ =
  record
    { at =
        record
          { bound = λ h →
              <-suc-inv
                (StoreWfAt.bound (at wfΣ) (∈-renameStoreᵗ suc h))
          ; wfTy = λ h →
              WfTy-un⇑ᵗ
                (StoreWfAt.wfTy (at wfΣ) (∈-renameStoreᵗ suc h))
          }
    ; wfOlder = λ h →
        WfTy-un⇑ᵗ (wfOlder wfΣ (∈-renameStoreᵗ suc h))
    ; unique = StoreUnique-⟰ᵗ-inv (unique wfΣ)
    }

StoreDetWf-inst :
  ∀ {Δ Σ} →
  StoreDetWf Δ Σ →
  StoreDetWf (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ)
StoreDetWf-inst wfΣ =
  record
    { at = StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ (at wfΣ))
    ; wfOlder = wfOlder′
    ; unique = StoreUnique-bind (unique wfΣ)
    }
  where
    shifted : StoreDetWf _ _
    shifted = StoreDetWf-⟰ᵗ wfΣ

    wfOlder′ :
      ∀ {α A} →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _) →
      WfTy α A
    wfOlder′ (here refl) = wf★
    wfOlder′ (there h) = wfOlder shifted h

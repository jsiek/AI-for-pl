module proof.TypeInTypeSubst where

-- File Charter:
--   * Renaming and substitution properties for GTPLC types.
--   * Supplies well-formedness transport, renaming algebra, and binder
--     cancellation used by coercion and term metatheory.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_<_; suc; zero; z<s; s<s)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)

open import Types

------------------------------------------------------------------------
-- Well-formed renamings
------------------------------------------------------------------------

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ′ ρ = ∀ {X} → X < Δ → ρ X < Δ′

TyRenameWf-ext : ∀ {Δ Δ′ ρ}
  → TyRenameWf Δ Δ′ ρ
  → TyRenameWf (suc Δ) (suc Δ′) (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s X<Δ) = s<s (hρ X<Δ)

TyRenameWf-suc : ∀ {Δ}
  → TyRenameWf Δ (suc Δ) suc
TyRenameWf-suc X<Δ = s<s X<Δ

renameᵗ-preserves-WfTy : ∀ {Δ Δ′ A ρ}
  → WfTy Δ A
  → TyRenameWf Δ Δ′ ρ
  → WfTy Δ′ (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfVar X<Δ) hρ = wfVar (hρ X<Δ)
renameᵗ-preserves-WfTy wfBase hρ = wfBase
renameᵗ-preserves-WfTy wf★ hρ = wf★
renameᵗ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy hA hρ)
      (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf∀ hA) hρ =
  wf∀ (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))

renameᵍ-preserves-WfTag : ∀ {Δ Δ′ G ρ}
  → WfTag Δ G
  → TyRenameWf Δ Δ′ ρ
  → WfTag Δ′ (renameᵍ ρ G)
renameᵍ-preserves-WfTag (wfTagVar X<Δ) hρ = wfTagVar (hρ X<Δ)
renameᵍ-preserves-WfTag wfTagBase hρ = wfTagBase
renameᵍ-preserves-WfTag wf★⇒★ hρ = wf★⇒★

rename-preserves-tagged : ∀ {G A}
  → (ρ : Renameᵗ)
  → G ꞉ A
  → renameᵍ ρ G ꞉ renameᵗ ρ A
rename-preserves-tagged ρ (tag-var X) = tag-var (ρ X)
rename-preserves-tagged ρ (tag-base ι) = tag-base ι
rename-preserves-tagged ρ tag-fun = tag-fun

tagged-wf : ∀ {Δ G A}
  → WfTag Δ G
  → G ꞉ A
  → WfTy Δ A
tagged-wf (wfTagVar X<Δ) (tag-var X) = wfVar X<Δ
tagged-wf wfTagBase (tag-base ι) = wfBase
tagged-wf wf★⇒★ tag-fun = wf⇒ wf★ wf★

tagged-unique : ∀ {G A B}
  → G ꞉ A
  → G ꞉ B
  → A ≡ B
tagged-unique (tag-var X) (tag-var .X) = refl
tagged-unique (tag-base ι) (tag-base .ι) = refl
tagged-unique tag-fun tag-fun = refl

------------------------------------------------------------------------
-- Renaming inverses and algebra
------------------------------------------------------------------------

RenameLeftInverse : Renameᵗ → Renameᵗ → Set
RenameLeftInverse ρ ψ = ∀ X → ψ (ρ X) ≡ X

RenameLeftInverse-ext : ∀ {ρ ψ}
  → RenameLeftInverse ρ ψ
  → RenameLeftInverse (extᵗ ρ) (extᵗ ψ)
RenameLeftInverse-ext inv zero = refl
RenameLeftInverse-ext inv (suc X) = cong suc (inv X)

predᵗ : Renameᵗ
predᵗ zero = zero
predᵗ (suc X) = X

RenameLeftInverse-suc : RenameLeftInverse suc predᵗ
RenameLeftInverse-suc X = refl

open0-ext-suc-inv : RenameLeftInverse
  (extᵗ suc) (singleRenameᵗ zero)
open0-ext-suc-inv zero = refl
open0-ext-suc-inv (suc X) = refl

renameᵗ-cong : ∀ {ρ ψ}
  → (∀ X → ρ X ≡ ψ X)
  → ∀ A
  → renameᵗ ρ A ≡ renameᵗ ψ A
renameᵗ-cong eq (＇ X) = cong ＇_ (eq X)
renameᵗ-cong eq (‵ ι) = refl
renameᵗ-cong eq ★ = refl
renameᵗ-cong eq (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-cong eq A) (renameᵗ-cong eq B)
renameᵗ-cong eq (`∀ A) =
  cong `∀ (renameᵗ-cong ext-eq A)
  where
    ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
    ext-eq zero = refl
    ext-eq (suc X) = cong suc (eq X)

renameᵗ-id : ∀ A
  → renameᵗ (λ X → X) A ≡ A
renameᵗ-id (＇ X) = refl
renameᵗ-id (‵ ι) = refl
renameᵗ-id ★ = refl
renameᵗ-id (A ⇒ B) = cong₂ _⇒_ (renameᵗ-id A) (renameᵗ-id B)
renameᵗ-id (`∀ A) =
  cong `∀ (trans (renameᵗ-cong ext-id A) (renameᵗ-id A))
  where
    ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
    ext-id zero = refl
    ext-id (suc X) = refl

renameᵗ-compose : ∀ ρ ψ A
  → renameᵗ ψ (renameᵗ ρ A) ≡ renameᵗ (λ X → ψ (ρ X)) A
renameᵗ-compose ρ ψ (＇ X) = refl
renameᵗ-compose ρ ψ (‵ ι) = refl
renameᵗ-compose ρ ψ ★ = refl
renameᵗ-compose ρ ψ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-compose ρ ψ A) (renameᵗ-compose ρ ψ B)
renameᵗ-compose ρ ψ (`∀ A) =
  cong `∀
    (trans (renameᵗ-compose (extᵗ ρ) (extᵗ ψ) A)
      (renameᵗ-cong ext-compose A))
  where
    ext-compose : ∀ X
      → extᵗ ψ (extᵗ ρ X) ≡ extᵗ (λ Y → ψ (ρ Y)) X
    ext-compose zero = refl
    ext-compose (suc X) = refl

renameᵗ-left-inverse : ∀ {ρ ψ}
  → RenameLeftInverse ρ ψ
  → ∀ A
  → renameᵗ ψ (renameᵗ ρ A) ≡ A
renameᵗ-left-inverse {ρ = ρ} {ψ = ψ} inv A =
  trans (renameᵗ-compose ρ ψ A)
    (trans (renameᵗ-cong inv A) (renameᵗ-id A))

renameᵍ-cong : ∀ {ρ ψ}
  → (∀ X → ρ X ≡ ψ X)
  → ∀ G
  → renameᵍ ρ G ≡ renameᵍ ψ G
renameᵍ-cong eq (＇ X) = cong ＇_ (eq X)
renameᵍ-cong eq (‵ ι) = refl
renameᵍ-cong eq ★⇒★ = refl

renameᵍ-id : ∀ G
  → renameᵍ (λ X → X) G ≡ G
renameᵍ-id (＇ X) = refl
renameᵍ-id (‵ ι) = refl
renameᵍ-id ★⇒★ = refl

renameᵍ-compose : ∀ ρ ψ G
  → renameᵍ ψ (renameᵍ ρ G) ≡ renameᵍ (λ X → ψ (ρ X)) G
renameᵍ-compose ρ ψ (＇ X) = refl
renameᵍ-compose ρ ψ (‵ ι) = refl
renameᵍ-compose ρ ψ ★⇒★ = refl

renameᵍ-left-inverse : ∀ {ρ ψ}
  → RenameLeftInverse ρ ψ
  → ∀ G
  → renameᵍ ψ (renameᵍ ρ G) ≡ G
renameᵍ-left-inverse {ρ = ρ} {ψ = ψ} inv G =
  trans (renameᵍ-compose ρ ψ G)
    (trans (renameᵍ-cong inv G) (renameᵍ-id G))

open0-ext-suc-cancelᵗ : ∀ A
  → renameᵗ (singleRenameᵗ zero) (renameᵗ (extᵗ suc) A) ≡ A
open0-ext-suc-cancelᵗ =
  renameᵗ-left-inverse open0-ext-suc-inv

renameᵗ-ext-suc-comm : ∀ ρ A
  → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-ext-suc-comm ρ A =
  trans (renameᵗ-compose suc (extᵗ ρ) A)
    (trans (renameᵗ-cong commute A)
      (sym (renameᵗ-compose ρ suc A)))
  where
    commute : ∀ X → extᵗ ρ (suc X) ≡ suc (ρ X)
    commute X = refl

------------------------------------------------------------------------
-- Occurrence and shift inversion
------------------------------------------------------------------------

rename-preserves-∈ᵗ : ∀ ρ {X A}
  → X ∈ᵗ A
  → ρ X ∈ᵗ renameᵗ ρ A
rename-preserves-∈ᵗ ρ var-∈ = var-∈
rename-preserves-∈ᵗ ρ (∈-fun-left occ) =
  ∈-fun-left (rename-preserves-∈ᵗ ρ occ)
rename-preserves-∈ᵗ ρ (∈-fun-right occ) =
  ∈-fun-right (rename-preserves-∈ᵗ ρ occ)
rename-preserves-∈ᵗ ρ (∈-all occ) =
  ∈-all (rename-preserves-∈ᵗ (extᵗ ρ) occ)

rename-ext-preserves-zero∈ : ∀ ρ {A}
  → zero ∈ᵗ A
  → zero ∈ᵗ renameᵗ (extᵗ ρ) A
rename-ext-preserves-zero∈ ρ occ =
  rename-preserves-∈ᵗ (extᵗ ρ) occ

TyRenameReflectsWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameReflectsWf Δ Δ′ ρ = ∀ {X} → ρ X < Δ′ → X < Δ

TyRenameReflectsWf-ext : ∀ {Δ Δ′ ρ}
  → TyRenameReflectsWf Δ Δ′ ρ
  → TyRenameReflectsWf (suc Δ) (suc Δ′) (extᵗ ρ)
TyRenameReflectsWf-ext hρ {zero} z<s = z<s
TyRenameReflectsWf-ext hρ {suc X} (s<s ρX<Δ′) = s<s (hρ ρX<Δ′)

renameᵗ-reflects-WfTy : ∀ {Δ Δ′ A ρ}
  → WfTy Δ′ (renameᵗ ρ A)
  → TyRenameReflectsWf Δ Δ′ ρ
  → WfTy Δ A
renameᵗ-reflects-WfTy {A = ＇ X} (wfVar ρX<Δ′) hρ =
  wfVar (hρ ρX<Δ′)
renameᵗ-reflects-WfTy {A = ‵ ι} wfBase hρ = wfBase
renameᵗ-reflects-WfTy {A = ★} wf★ hρ = wf★
renameᵗ-reflects-WfTy {A = A ⇒ B} (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-reflects-WfTy hA hρ)
      (renameᵗ-reflects-WfTy hB hρ)
renameᵗ-reflects-WfTy {A = `∀ A} (wf∀ hA) hρ =
  wf∀ (renameᵗ-reflects-WfTy hA (TyRenameReflectsWf-ext hρ))

suc-reflects-Wf : ∀ {Δ}
  → TyRenameReflectsWf Δ (suc Δ) suc
suc-reflects-Wf (s<s X<Δ) = X<Δ

WfTy-un⇑ᵗ : ∀ {Δ A}
  → WfTy (suc Δ) (⇑ᵗ A)
  → WfTy Δ A
WfTy-un⇑ᵗ hA = renameᵗ-reflects-WfTy hA suc-reflects-Wf

module PreservationFresh where

-- File Charter:
--   * Type preservation for extrinsic-inst PolyUpDown one-step reduction
--   * under the `ReductionFresh` semantics (fresh seals use `length Σ`).
--   * Reuses raw one-step preservation via a translation to `Reduction`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; length; _∷_; _++_; [])
open import Data.Nat using (zero; suc; _+_; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; n<1+n; <-irrefl)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Store
open import Ctx
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties
open import ReductionFresh
open import Reduction using (_—→_)

import Preservation as OldPreservation

------------------------------------------------------------------------
-- Raw-step translation and preservation
------------------------------------------------------------------------

preservation :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  Uniqueˢ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ N ⦂ A
preservation uΣ M⊢ red =
  OldPreservation.preservation uΣ M⊢ red

------------------------------------------------------------------------
-- Permission append helpers (fresh seal at the end)
------------------------------------------------------------------------

length-append-tag :
  (Φ : List CastPerm) →
  length (Φ ++ cast-tag ∷ []) ≡ suc (length Φ)
length-append-tag [] = refl
length-append-tag (_ ∷ Φ) = cong suc (length-append-tag Φ)

length-append-seal :
  (Φ : List CastPerm) →
  length (Φ ++ cast-seal ∷ []) ≡ suc (length Φ)
length-append-seal [] = refl
length-append-seal (_ ∷ Φ) = cong suc (length-append-seal Φ)

member-append-tag :
  ∀ {α}{Φ : List CastPerm} →
  α ∈ Φ →
  α ∈ (Φ ++ cast-tag ∷ [])
member-append-tag {Φ = []} ()
member-append-tag {Φ = conv ∷ Φ} here-conv = here-conv
member-append-tag {Φ = cast-seal ∷ Φ} here-seal = here-seal
member-append-tag {Φ = conv ∷ Φ} (there p) = there (member-append-tag p)
member-append-tag {Φ = cast-seal ∷ Φ} (there p) = there (member-append-tag p)
member-append-tag {Φ = cast-tag ∷ Φ} (there p) = there (member-append-tag p)

member-append-seal :
  ∀ {α}{Φ : List CastPerm} →
  α ∈ Φ →
  α ∈ (Φ ++ cast-seal ∷ [])
member-append-seal {Φ = []} ()
member-append-seal {Φ = conv ∷ Φ} here-conv = here-conv
member-append-seal {Φ = cast-seal ∷ Φ} here-seal = here-seal
member-append-seal {Φ = conv ∷ Φ} (there p) = there (member-append-seal p)
member-append-seal {Φ = cast-seal ∷ Φ} (there p) = there (member-append-seal p)
member-append-seal {Φ = cast-tag ∷ Φ} (there p) = there (member-append-seal p)

conv-append-tag :
  ∀ {α}{Φ : List CastPerm} →
  α ∈conv Φ →
  α ∈conv (Φ ++ cast-tag ∷ [])
conv-append-tag {Φ = []} ()
conv-append-tag {Φ = conv ∷ Φ} here-conv-only = here-conv-only
conv-append-tag {Φ = conv ∷ Φ} (there-conv p) = there-conv (conv-append-tag p)
conv-append-tag {Φ = cast-seal ∷ Φ} (there-conv p) = there-conv (conv-append-tag p)
conv-append-tag {Φ = cast-tag ∷ Φ} (there-conv p) = there-conv (conv-append-tag p)

cast-append-tag :
  ∀ {α}{Φ : List CastPerm} →
  α ∈cast Φ →
  α ∈cast (Φ ++ cast-tag ∷ [])
cast-append-tag {Φ = []} ()
cast-append-tag {Φ = cast-seal ∷ Φ} here-cast-only = here-cast-only
cast-append-tag {Φ = cast-seal ∷ Φ} (there-cast p) = there-cast (cast-append-tag p)
cast-append-tag {Φ = conv ∷ Φ} (there-cast p) = there-cast (cast-append-tag p)
cast-append-tag {Φ = cast-tag ∷ Φ} (there-cast p) = there-cast (cast-append-tag p)

conv-append-seal :
  ∀ {α}{Φ : List CastPerm} →
  α ∈conv Φ →
  α ∈conv (Φ ++ cast-seal ∷ [])
conv-append-seal {Φ = []} ()
conv-append-seal {Φ = conv ∷ Φ} here-conv-only = here-conv-only
conv-append-seal {Φ = conv ∷ Φ} (there-conv p) = there-conv (conv-append-seal p)
conv-append-seal {Φ = cast-seal ∷ Φ} (there-conv p) = there-conv (conv-append-seal p)
conv-append-seal {Φ = cast-tag ∷ Φ} (there-conv p) = there-conv (conv-append-seal p)

cast-append-seal :
  ∀ {α}{Φ : List CastPerm} →
  α ∈cast Φ →
  α ∈cast (Φ ++ cast-seal ∷ [])
cast-append-seal {Φ = []} ()
cast-append-seal {Φ = cast-seal ∷ Φ} here-cast-only = here-cast-only
cast-append-seal {Φ = cast-seal ∷ Φ} (there-cast p) = there-cast (cast-append-seal p)
cast-append-seal {Φ = conv ∷ Φ} (there-cast p) = there-cast (cast-append-seal p)
cast-append-seal {Φ = cast-tag ∷ Φ} (there-cast p) = there-cast (cast-append-seal p)

tag-append-tag :
  ∀ {α}{Φ : List CastPerm} →
  α ∈tag Φ →
  α ∈tag (Φ ++ cast-tag ∷ [])
tag-append-tag {Φ = []} ()
tag-append-tag {Φ = cast-tag ∷ Φ} here-tag-only = here-tag-only
tag-append-tag {Φ = cast-tag ∷ Φ} (there-tag p) = there-tag (tag-append-tag p)
tag-append-tag {Φ = conv ∷ Φ} (there-tag p) = there-tag (tag-append-tag p)
tag-append-tag {Φ = cast-seal ∷ Φ} (there-tag p) = there-tag (tag-append-tag p)

tag-append-seal :
  ∀ {α}{Φ : List CastPerm} →
  α ∈tag Φ →
  α ∈tag (Φ ++ cast-seal ∷ [])
tag-append-seal {Φ = []} ()
tag-append-seal {Φ = cast-tag ∷ Φ} here-tag-only = here-tag-only
tag-append-seal {Φ = cast-tag ∷ Φ} (there-tag p) = there-tag (tag-append-seal p)
tag-append-seal {Φ = conv ∷ Φ} (there-tag p) = there-tag (tag-append-seal p)
tag-append-seal {Φ = cast-seal ∷ Φ} (there-tag p) = there-tag (tag-append-seal p)

tag-at-end :
  (Φ : List CastPerm) →
  length Φ ∈tag (Φ ++ cast-tag ∷ [])
tag-at-end [] = here-tag-only
tag-at-end (_ ∷ Φ) = there-tag (tag-at-end Φ)

seal-at-end :
  (Φ : List CastPerm) →
  length Φ ∈ (Φ ++ cast-seal ∷ [])
seal-at-end [] = here-seal
seal-at-end (_ ∷ Φ) = there (seal-at-end Φ)

cast-at-end :
  (Φ : List CastPerm) →
  length Φ ∈cast (Φ ++ cast-seal ∷ [])
cast-at-end [] = here-cast-only
cast-at-end (_ ∷ Φ) = there-cast (cast-at-end Φ)

member-unappend-tag :
  ∀ {α}{Φ : List CastPerm} →
  α ∈ (Φ ++ cast-tag ∷ []) →
  α ∈ Φ
member-unappend-tag {Φ = []} (there ())
member-unappend-tag {Φ = conv ∷ Φ} here-conv = here-conv
member-unappend-tag {Φ = cast-seal ∷ Φ} here-seal = here-seal
member-unappend-tag {Φ = conv ∷ Φ} (there p) = there (member-unappend-tag p)
member-unappend-tag {Φ = cast-seal ∷ Φ} (there p) = there (member-unappend-tag p)
member-unappend-tag {Φ = cast-tag ∷ Φ} (there p) = there (member-unappend-tag p)

RenOkConv-append-tag :
  ∀ {Φ : List CastPerm} →
  RenOkConv (λ α → α) Φ (Φ ++ cast-tag ∷ [])
RenOkConv-append-tag = conv-append-tag

RenOkCast-append-tag :
  ∀ {Φ : List CastPerm} →
  RenOkCast (λ α → α) Φ (Φ ++ cast-tag ∷ [])
RenOkCast-append-tag = cast-append-tag

RenOkTag-append-tag :
  ∀ {Φ : List CastPerm} →
  RenOkTag (λ α → α) Φ (Φ ++ cast-tag ∷ [])
RenOkTag-append-tag = tag-append-tag

RenNotIn-append-tag :
  ∀ {Φ : List CastPerm} →
  RenNotIn (λ α → α) Φ (Φ ++ cast-tag ∷ [])
RenNotIn-append-tag α∉ p = α∉ (member-unappend-tag p)

append-tag-⊑ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
  Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ ∣ (Φ ++ cast-tag ∷ []) ⊢ p ⦂ A ⊑ B
castWt⊑-term :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p q : Up} →
  p ≡ q →
  Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ ∣ Φ ⊢ q ⦂ A ⊑ B
castWt⊑-term refl h = h

append-tag-⊑ {Σ = Σ} {A = A} {B = B} {p = p} h =
  castWt⊑
    (renameStoreˢ-id {Σ = Σ})
    refl
    (castWt⊑-term
      (OldPreservation.rename⊑ˢ-pointwise (λ α → α) (λ α → refl) p)
      (castWt⊑-raw
        (renameˢ-id-store {A = A})
        (renameˢ-id-store {A = B})
        (⊑-renameˢ-wt
          (λ α → α)
          RenOkConv-append-tag
          RenOkCast-append-tag
          RenOkTag-append-tag
          h)))

append-tag-⊒ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
  Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ ∣ (Φ ++ cast-tag ∷ []) ⊢ p ⦂ A ⊒ B
append-tag-⊒ {Σ = Σ} {A = A} {B = B} {p = p} h =
  castWt⊒
    (renameStoreˢ-id {Σ = Σ})
    refl
    (OldPreservation.castWt⊒-term
      (OldPreservation.rename⊒ˢ-pointwise (λ α → α) (λ α → refl) p)
      (castWt⊒-raw
        (renameˢ-id-store {A = A})
        (renameˢ-id-store {A = B})
        (⊒-renameˢ-wt
          (λ α → α)
          RenOkConv-append-tag
          RenOkCast-append-tag
          RenOkTag-append-tag
          h)))

------------------------------------------------------------------------
-- Seal-context monotonicity on term typing (+1 fresh seal)
------------------------------------------------------------------------

wkΨ-term-suc :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ suc Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
wkΨ-term-suc (⊢` h) = ⊢` h
wkΨ-term-suc (⊢ƛ wfA M⊢) =
  ⊢ƛ (WfTy-weakenˢ wfA (n≤1+n _)) (wkΨ-term-suc M⊢)
wkΨ-term-suc (⊢· L⊢ M⊢) = ⊢· (wkΨ-term-suc L⊢) (wkΨ-term-suc M⊢)
wkΨ-term-suc (⊢Λ M⊢) = ⊢Λ (wkΨ-term-suc M⊢)
wkΨ-term-suc (⊢• {B = B} M⊢ wfT) =
  ⊢• {B = B} (wkΨ-term-suc M⊢) (WfTy-weakenˢ wfT (n≤1+n _))
wkΨ-term-suc (⊢$ κ) = ⊢$ κ
wkΨ-term-suc (⊢⊕ L⊢ op M⊢) =
  ⊢⊕ (wkΨ-term-suc L⊢) op (wkΨ-term-suc M⊢)
wkΨ-term-suc (⊢up Φ lenΦ M⊢ p⊢) =
  ⊢up
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-term-suc M⊢)
    (append-tag-⊑ p⊢)
wkΨ-term-suc (⊢down Φ lenΦ M⊢ p⊢) =
  ⊢down
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    (wkΨ-term-suc M⊢)
    (append-tag-⊒ p⊢)
wkΨ-term-suc (⊢blame ℓ) = ⊢blame ℓ

len<suc-StoreWf :
  ∀ {Δ Ψ}{Σ : Store} →
  StoreWf Δ Ψ Σ →
  length Σ < suc Ψ
len<suc-StoreWf {Ψ = Ψ} wfΣ rewrite storeWf-length wfΣ = n<1+n Ψ

length∉dom-StoreWf :
  ∀ {Δ Ψ}{Σ : Store} →
  StoreWf Δ Ψ Σ →
  length Σ ∉domˢ Σ
length∉dom-StoreWf {Ψ = Ψ} {Σ = Σ} wfΣ {A} h
  rewrite storeWf-length wfΣ =
  <-irrefl refl (storeWf-dom< wfΣ h)

------------------------------------------------------------------------
-- Preservation for store-threaded one-step reduction
------------------------------------------------------------------------

data StepCtxShape : Set where
  shape-id : StepCtxShape
  shape-suc : StepCtxShape

StepCtxExact : StepCtxShape → SealCtx → SealCtx → Set
StepCtxExact shape-id Ψ Ψ′ = Ψ′ ≡ Ψ
StepCtxExact shape-suc Ψ Ψ′ = Ψ′ ≡ suc Ψ

step-ctx-shape :
  ∀ {Σ Σ′ : Store}{M M′ : Term} →
  Σ ∣ M —→ Σ′ ∣ M′ →
  StepCtxShape
step-ctx-shape (id-step red) = shape-id
step-ctx-shape β-Λ = shape-suc
step-ctx-shape (β-down-∀ vV) = shape-suc
step-ctx-shape (β-down-ν vV) = shape-suc
step-ctx-shape (β-up-ν vV) = shape-suc
step-ctx-shape (ξ-·₁ red) = step-ctx-shape red
step-ctx-shape (ξ-·₂ vV red) = step-ctx-shape red
step-ctx-shape (ξ-·α red) = step-ctx-shape red
step-ctx-shape (ξ-up red) = step-ctx-shape red
step-ctx-shape (ξ-down red) = step-ctx-shape red
step-ctx-shape (ξ-⊕₁ red) = step-ctx-shape red
step-ctx-shape (ξ-⊕₂ vL red) = step-ctx-shape red

stepCtxLe :
  ∀ {shape Ψ Ψ′} →
  StepCtxExact shape Ψ Ψ′ →
  Ψ ≤ Ψ′
stepCtxLe {shape-id} eq rewrite eq = ≤-refl
stepCtxLe {shape-suc} {Ψ = Ψ} eq rewrite eq = n≤1+n Ψ

step-wk-term :
  ∀ {shape Δ Ψ Ψ′}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  StepCtxExact shape Ψ Ψ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ′ ∣ Σ ∣ Γ ⊢ M ⦂ A
step-wk-term {shape-id} eq M⊢ rewrite eq = M⊢
step-wk-term {shape-suc} eq M⊢ rewrite eq = wkΨ-term-suc M⊢

preservation-step :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  (red : Σ ∣ M —→ Σ′ ∣ M′) →
  Sigma.Σ SealCtx
    (λ Ψ′ →
      StepCtxExact (step-ctx-shape red) Ψ Ψ′ ×
      (Δ ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A))

open-fresh-ν⊒ : ∀ {Δ Ψ}{Σ : Store}{Aν Bν T : Ty} {p : Down}{Φ : List CastPerm} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (lenΦ : length Φ ≡ Ψ) →
  ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ p ⦂ ⇑ˢ Bν ⊒ ((⇑ˢ Aν) [ α₀ ]ᵗ) →
  ((length Σ , T) ∷ Σ) ∣ (Φ ++ cast-tag ∷ [])
    ⊢ (p [ length Σ ]⊒) ⦂ Bν ⊒ (Aν [ ｀ (length Σ) ]ᵗ)
open-fresh-ν⊒ {Σ = Σ}{Aν = Aν}{Bν = Bν}{T = T}{p = p}{Φ} wfΣ lenΦ ⊢p =
  wk⊒
    (drop ⊆ˢ-refl)
    (OldPreservation.drop★⊒-seal-preserving top★ top∉ ⊢p★)
  where
    tag-∉ :
      ∀ {α}{P : List CastPerm} →
      α ∈tag P →
      α ∈ P →
      ⊥
    tag-∉ here-tag-only ()
    tag-∉ (there-tag p) (there q) = tag-∉ p q

    top-tag : length Σ ∈tag (Φ ++ cast-tag ∷ [])
    top-tag rewrite storeWf-length wfΣ | sym lenΦ = tag-at-end Φ

    okConv :
      RenOkConv (singleSealEnv (length Σ)) (cast-tag ∷ Φ) (Φ ++ cast-tag ∷ [])
    okConv {zero} ()
    okConv {suc α} (there-conv p) = conv-append-tag p

    okCast :
      RenOkCast (singleSealEnv (length Σ)) (cast-tag ∷ Φ) (Φ ++ cast-tag ∷ [])
    okCast {zero} ()
    okCast {suc α} (there-cast p) = cast-append-tag p

    okTag :
      RenOkTag (singleSealEnv (length Σ)) (cast-tag ∷ Φ) (Φ ++ cast-tag ∷ [])
    okTag {zero} here-tag-only = top-tag
    okTag {suc α} (there-tag p) = tag-append-tag p

    ⊢p′ :
      renameStoreˢ (singleSealEnv (length Σ)) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
        ∣ (Φ ++ cast-tag ∷ [])
        ⊢ p [ length Σ ]⊒
          ⦂ renameˢ (singleSealEnv (length Σ)) (⇑ˢ Bν)
          ⊒ renameˢ (singleSealEnv (length Σ)) ((⇑ˢ Aν) [ α₀ ]ᵗ)
    ⊢p′ =
      ⊒-renameˢ-wt
        {Φ′ = Φ ++ cast-tag ∷ []}
        (singleSealEnv (length Σ))
        okConv
        okCast
        okTag
        ⊢p

    eq-store★ :
      renameStoreˢ (singleSealEnv (length Σ)) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
        ≡ ((length Σ , ★) ∷ Σ)
    eq-store★ =
      cong₂
        _∷_
        (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id (length Σ) ★))
        (renameStoreˢ-single-⟰ˢ (length Σ) Σ)

    eq-src : renameˢ (singleSealEnv (length Σ)) (⇑ˢ Bν) ≡ Bν
    eq-src = renameˢ-single-⇑ˢ-id (length Σ) Bν

    eq-tgt :
      renameˢ (singleSealEnv (length Σ)) ((⇑ˢ Aν) [ α₀ ]ᵗ)
        ≡ (Aν [ ｀ (length Σ) ]ᵗ)
    eq-tgt =
      trans
        (renameˢ-[]ᵗ-seal (singleSealEnv (length Σ)) (⇑ˢ Aν) zero)
        (cong
          (λ X → X [ ｀ (length Σ) ]ᵗ)
          (renameˢ-single-⇑ˢ-id (length Σ) Aν))

    ⊢p★ :
      ((length Σ , ★) ∷ Σ) ∣ (Φ ++ cast-tag ∷ [])
        ⊢ p [ length Σ ]⊒ ⦂ Bν ⊒ (Aν [ ｀ (length Σ) ]ᵗ)
    ⊢p★ =
      castWt⊒
        eq-store★
        refl
        (castWt⊒-raw eq-src eq-tgt ⊢p′)

    top★ : ((length Σ , ★) ∷ Σ) ∋ˢ length Σ ⦂ ★
    top★ = Z∋ˢ refl refl

    top∉ : length Σ ∉ (Φ ++ cast-tag ∷ [])
    top∉ α∈ = tag-∉ top-tag α∈

open-fresh-ν⊑ :
  ∀ {Δ Ψ}{Σ : Store}{Aν Bν : Ty} {p : Up}{Φ : List CastPerm} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  (lenΦ : length Φ ≡ Ψ) →
  ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ p ⦂ ((⇑ˢ Aν) [ α₀ ]ᵗ) ⊑ ⇑ˢ Bν →
  ((length Σ , ★) ∷ Σ) ∣ (Φ ++ cast-seal ∷ [])
    ⊢ (p [ length Σ ]⊑) ⦂ (Aν [ ｀ (length Σ) ]ᵗ) ⊑ Bν
open-fresh-ν⊑ {Σ = Σ}{Aν = Aν}{Bν = Bν}{p = p}{Φ} wfΣ lenΦ ⊢p =
  castWt⊑
    eq-store★
    refl
    (castWt⊑-raw eq-src eq-tgt ⊢p′)
  where
    top-cast : length Σ ∈cast (Φ ++ cast-seal ∷ [])
    top-cast rewrite storeWf-length wfΣ | sym lenΦ = cast-at-end Φ

    okConv :
      RenOkConv (singleSealEnv (length Σ)) (cast-seal ∷ Φ) (Φ ++ cast-seal ∷ [])
    okConv {zero} ()
    okConv {suc α} (there-conv p) = conv-append-seal p

    okCast :
      RenOkCast (singleSealEnv (length Σ)) (cast-seal ∷ Φ) (Φ ++ cast-seal ∷ [])
    okCast {zero} here-cast-only = top-cast
    okCast {suc α} (there-cast p) = cast-append-seal p

    okTag :
      RenOkTag (singleSealEnv (length Σ)) (cast-seal ∷ Φ) (Φ ++ cast-seal ∷ [])
    okTag {zero} ()
    okTag {suc α} (there-tag p) = tag-append-seal p

    ⊢p′ :
      renameStoreˢ (singleSealEnv (length Σ)) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
        ∣ (Φ ++ cast-seal ∷ [])
        ⊢ p [ length Σ ]⊑
          ⦂ renameˢ (singleSealEnv (length Σ)) ((⇑ˢ Aν) [ α₀ ]ᵗ)
          ⊑ renameˢ (singleSealEnv (length Σ)) (⇑ˢ Bν)
    ⊢p′ =
      ⊑-renameˢ-wt
        {Φ′ = Φ ++ cast-seal ∷ []}
        (singleSealEnv (length Σ))
        okConv
        okCast
        okTag
        ⊢p

    eq-store★ :
      renameStoreˢ (singleSealEnv (length Σ)) ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
        ≡ ((length Σ , ★) ∷ Σ)
    eq-store★ =
      cong₂
        _∷_
        (cong₂ _,_ refl (renameˢ-single-⇑ˢ-id (length Σ) ★))
        (renameStoreˢ-single-⟰ˢ (length Σ) Σ)

    eq-src :
      renameˢ (singleSealEnv (length Σ)) ((⇑ˢ Aν) [ α₀ ]ᵗ)
        ≡ (Aν [ ｀ (length Σ) ]ᵗ)
    eq-src =
      trans
        (renameˢ-[]ᵗ-seal (singleSealEnv (length Σ)) (⇑ˢ Aν) zero)
        (cong
          (λ X → X [ ｀ (length Σ) ]ᵗ)
          (renameˢ-single-⇑ˢ-id (length Σ) Aν))

    eq-tgt : renameˢ (singleSealEnv (length Σ)) (⇑ˢ Bν) ≡ Bν
    eq-tgt = renameˢ-single-⇑ˢ-id (length Σ) Bν

preservation-step-β-down-ν :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{Aν T : Ty}
    {V : Term}{p : Down} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ((V down (ν p)) ⦂∀ Aν [ T ]) ⦂ Aν [ T ]ᵗ →
  Sigma.Σ SealCtx
    (λ Ψ′ →
      StepCtxExact shape-suc Ψ Ψ′ ×
      (Δ ∣ Ψ′ ∣ ((length Σ , T) ∷ Σ) ∣ Γ ⊢
        ((V down (p [ length Σ ]⊒))
           up (instCast⊑ {A = T} {B = Aν} {α = length Σ}))
        ⦂ Aν [ T ]ᵗ))
preservation-step-β-down-ν {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
  {Aν = Aν} {T = T} {V = V} {p = p} wfΣ
  (⊢• {B = Aν} {T = T}
    (⊢down {A = Bν} {B = `∀ Aν} Φ lenΦ V⊢ (wt-ν {A = Aν} {B = Bν} {p = p} p⊢))
    wfT) =
  suc Ψ , refl ,
  ⊢up
    (every (suc Ψ))
    (length-every (suc Ψ))
    (⊢down
      (Φ ++ cast-tag ∷ [])
      (trans (length-append-tag Φ) (cong suc lenΦ))
      V⊢↑
      p⊢′)
    (instCast⊑-wt
      {A = T}
      {B = Aν}
      {α = length Σ}
      top
      (every-member-conv (length Σ) (len<suc-StoreWf wfΣ)))
  where
    p⊢′ : ((length Σ , T) ∷ Σ) ∣ (Φ ++ cast-tag ∷ [])
      ⊢ (p [ length Σ ]⊒) ⦂ Bν ⊒ (Aν [ ｀ (length Σ) ]ᵗ)
    p⊢′ = open-fresh-ν⊒ {Aν = Aν} {Bν = Bν} {T = T} wfΣ lenΦ p⊢

    V⊢↑ : Δ ∣ suc Ψ ∣ ((length Σ , T) ∷ Σ) ∣ Γ ⊢ V ⦂ Bν
    V⊢↑ = wkΣ-term (drop ⊆ˢ-refl) (wkΨ-term-suc V⊢)

    top : ((length Σ , T) ∷ Σ) ∋ˢ length Σ ⦂ T
    top = Z∋ˢ refl refl

preservation-step-β-up-ν :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{Bν : Ty}
    {V : Term}{p : Up} →
  (wfΣ : StoreWf Δ Ψ Σ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (V up (ν p)) ⦂ Bν →
  Δ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ Γ ⊢
    ((V ⦂∀
        ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)
        [ ｀ (length Σ) ])
       up (p [ length Σ ]⊑))
    ⦂ Bν
preservation-step-β-up-ν {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
  {Bν = Bν} {V = V} {p = p} wfΣ
  (⊢up {A = `∀ Aν} {B = Bν} Φ lenΦ V⊢ (wt-ν {A = Aν} {B = Bν} {p = p} p⊢)) =
  ⊢up
    (Φ ++ cast-seal ∷ [])
    (trans (length-append-seal Φ) (cong suc lenΦ))
    (⊢• {B = ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)}
      V⊢′
      (wfSeal (len<suc-StoreWf wfΣ)))
    p⊢′
  where
    eq-src : up-src ((zero , ★) ∷ ⟰ˢ Σ) p ≡ (⇑ˢ Aν) [ α₀ ]ᵗ
    eq-src = up-src-align p⊢

    eq-close : ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ) ≡ Aν
    eq-close =
      trans
        (cong (λ X → (⇑ᵗ X) [ ＇ zero ]ˢᵗ) eq-src)
        (closeν-inline-open Aν)

    eq-open :
      (((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ) [ ｀ (length Σ) ]ᵗ)
        ≡ (Aν [ ｀ (length Σ) ]ᵗ)
    eq-open = cong (λ X → X [ ｀ (length Σ) ]ᵗ) eq-close

    V⊢↑ : Δ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ Γ ⊢ V ⦂ `∀ Aν
    V⊢↑ = wkΣ-term (drop ⊆ˢ-refl) (wkΨ-term-suc V⊢)

    V⊢′ : Δ ∣ suc Ψ ∣ ((length Σ , ★) ∷ Σ) ∣ Γ
        ⊢ V ⦂ `∀ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)
    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-close)) V⊢↑

    p⊢base : ((length Σ , ★) ∷ Σ) ∣ (Φ ++ cast-seal ∷ [])
      ⊢ (p [ length Σ ]⊑) ⦂ (Aν [ ｀ (length Σ) ]ᵗ) ⊑ Bν
    p⊢base = open-fresh-ν⊑ {Aν = Aν} {Bν = Bν} wfΣ lenΦ p⊢

    p⊢′ : ((length Σ , ★) ∷ Σ) ∣ (Φ ++ cast-seal ∷ [])
      ⊢ (p [ length Σ ]⊑)
        ⦂ (((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ) [ ｀ (length Σ) ]ᵗ)
        ⊑ Bν
    p⊢′ = castWt⊑-raw (sym eq-open) refl p⊢base

preservation-step {Ψ = Ψ} wfΣ M⊢ (id-step red) =
  Ψ , refl ,
  preservation (storeWf-unique wfΣ) M⊢ red

preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} wfΣ
  (⊢• {B = B} {T = T} (⊢Λ V⊢) wfT)
  (β-Λ {V = V}) =
  suc Ψ , refl ,
  ⊢up
    (every (suc Ψ))
    (length-every (suc Ψ))
    (wkΣ-term
      (drop ⊆ˢ-refl)
      ([]ᵀ-wt
        (wkΨ-term-suc V⊢)
        (｀ (length Σ))
        (wfSeal (len<suc-StoreWf wfΣ))))
    (instCast⊑-wt
      {A = T}
      {B = B}
      {α = length Σ}
      (Z∋ˢ refl refl)
      (every-member-conv (length Σ) (len<suc-StoreWf wfΣ)))

preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} wfΣ
  (⊢• {B = B} {T = T}
    (⊢down {A = `∀ C} {B = `∀ B} Φ lenΦ V⊢ (wt-∀ {A = C} {B = B} {p = p} p⊢))
    wfT)
  (β-down-∀ {A = T} {B = B} {V = V} {p = p} vV) =
  suc Ψ , refl ,
  cong-⊢⦂
    refl
    refl
    refl
    (cong (λ X → X [ T ]ᵗ) (down-tgt-align p⊢))
    (⊢up
      (every (suc Ψ))
      (length-every (suc Ψ))
      (wkΣ-term
        (drop ⊆ˢ-refl)
        (⊢down
          (Φ ++ cast-tag ∷ [])
          (trans (length-append-tag Φ) (cong suc lenΦ))
          (⊢• {B = down-src (⟰ᵗ Σ) p}
            (cong-⊢⦂
              refl
              refl
              refl
              (cong `∀ (sym (down-src-align (storeWf-unique (storeWf-⟰ᵗ wfΣ)) p⊢)))
              (wkΨ-term-suc V⊢))
            (wfSeal (len<suc-StoreWf wfΣ)))
          (append-tag-⊒
            (OldPreservation.openCast⊒
              (castWt⊒-raw
                (sym (down-src-align (storeWf-unique (storeWf-⟰ᵗ wfΣ)) p⊢))
                (sym (down-tgt-align p⊢))
                p⊢)
              (｀ (length Σ))))))
      (instCast⊑-wt
        {A = T}
        {B = down-tgt (⟰ᵗ Σ) p}
        {α = length Σ}
        (Z∋ˢ refl refl)
        (every-member-conv (length Σ) (len<suc-StoreWf wfΣ))))

preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} wfΣ
  (M⊢@(⊢• {B = Aν} {T = T}
    (⊢down {A = Bν} {B = `∀ Aν} Φ lenΦ V⊢ (wt-ν {A = Aν} {B = Bν} {p = p} p⊢))
    wfT))
  (β-down-ν {A = T} {B = Aν} {V = V} {p = p} vV) =
  preservation-step-β-down-ν wfΣ M⊢

preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} wfΣ
  (M⊢@(⊢up {A = `∀ Aν} {B = Bν} Φ lenΦ V⊢ (wt-ν {A = Aν} {B = Bν} {p = p} p⊢)))
  (β-up-ν {V = V} {p = p} vV) =
  suc Ψ , refl , preservation-step-β-up-ν wfΣ M⊢

preservation-step wfΣ (⊢· L⊢ M⊢) (ξ-·₁ red)
  with preservation-step wfΣ L⊢ red
... | Ψ′ , eqΨ′ , L′⊢ =
  Ψ′ , eqΨ′ ,
  ⊢·
    L′⊢
    (wkΣ-term (store-growth red) (step-wk-term eqΨ′ M⊢))

preservation-step wfΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ′ , M′⊢ =
  Ψ′ , eqΨ′ ,
  ⊢·
    (wkΣ-term (store-growth red) (step-wk-term eqΨ′ L⊢))
    M′⊢

preservation-step wfΣ (⊢• {B = B} {T = T} M⊢ wfT) (ξ-·α red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ′ , M′⊢ =
  Ψ′ , eqΨ′ ,
  ⊢• {B = B} M′⊢ (WfTy-weakenˢ wfT (stepCtxLe eqΨ′))

preservation-step {Ψ = Ψ} wfΣ (⊢up Φ lenΦ M⊢ hp) (ξ-up red)
  with step-ctx-shape red | preservation-step wfΣ M⊢ red
... | shape-id | .Ψ , refl , M′⊢ =
  Ψ , refl ,
  ⊢up
    Φ
    lenΦ
    M′⊢
    (wk⊑ (store-growth red) hp)
... | shape-suc | .(suc Ψ) , refl , M′⊢ =
  suc Ψ , refl ,
  ⊢up
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    M′⊢
    (wk⊑ (store-growth red) (append-tag-⊑ hp))

preservation-step {Ψ = Ψ} wfΣ (⊢down Φ lenΦ M⊢ hp) (ξ-down red)
  with step-ctx-shape red | preservation-step wfΣ M⊢ red
... | shape-id | .Ψ , refl , M′⊢ =
  Ψ , refl ,
  ⊢down
    Φ
    lenΦ
    M′⊢
    (wk⊒ (store-growth red) hp)
... | shape-suc | .(suc Ψ) , refl , M′⊢ =
  suc Ψ , refl ,
  ⊢down
    (Φ ++ cast-tag ∷ [])
    (trans (length-append-tag Φ) (cong suc lenΦ))
    M′⊢
    (wk⊒ (store-growth red) (append-tag-⊒ hp))

preservation-step wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
  with preservation-step wfΣ L⊢ red
... | Ψ′ , eqΨ′ , L′⊢ =
  Ψ′ , eqΨ′ ,
  ⊢⊕
    L′⊢
    op
    (wkΣ-term (store-growth red) (step-wk-term eqΨ′ M⊢))

preservation-step wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
  with preservation-step wfΣ M⊢ red
... | Ψ′ , eqΨ′ , M′⊢ =
  Ψ′ , eqΨ′ ,
  ⊢⊕
    (wkΣ-term (store-growth red) (step-wk-term eqΨ′ L⊢))
    op
    M′⊢

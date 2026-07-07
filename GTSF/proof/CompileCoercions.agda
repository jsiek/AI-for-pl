module proof.CompileCoercions where

-- File Charter:
--   * Coercion synthesis for the GTSF compiler.
--   * Defines realization of imprecision-assumption contexts by target-store
--     coercions, plus `coerce-up` and `coerce-down` for type-imprecision proofs.
--   * This file deliberately does not choose maximal lower bounds; it only
--     turns a chosen imprecision witness into typed target coercions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open import Types
open import Store using (StoreIncl; StoreIncl-drop)
open import Coercions
  using
    ( Coercion
    ; ModeEnv
    ; id-only
    ; tag-or-id
    ; seal-or-id
    ; id-onlyᵈ
    ; extᵈ
    ; genᵈ
    ; instᵈ
    ; _∣_∣_⊢_∶_=⇒_
    ; _∣_⊢_∶_=⇒_
    ; idTyAllowed
    ; cast-id
    ; cast-seq
    ; cast-tag
    ; cast-untag
    ; cast-fun
    ; cast-all
    ; cast-seal
    ; cast-unseal
    ; cast-inst
    ; cast-gen
    )
  renaming
    ( id to idᶜ
    ; _︔_ to _︔ᶜ_
    ; _↦_ to _↦ᶜ_
    ; `∀ to `∀ᶜ
    ; _! to _!ᶜ
    ; _？ to _？ᶜ
    ; seal to sealᶜ
    ; unseal to unsealᶜ
    ; inst to instᶜ
    ; gen to genᶜ
    )
open import Imprecision
open import NarrowWiden
  using
    ( _∣_∣_⊢_∶_⊒_
    ; _∣_∣_⊢_∶_⊑_
    ; _∣_⊢_∶_⊒_
    ; narrow-renameᵗ
    ; widen-renameᵗ
    ; narrow-weaken
    ; widen-weaken
    )
  renaming
    ( cross to nw-cross
    ; id-＇ to id-＇ⁿʷ
    ; id-‵ to id-‵ⁿʷ
    ; id★ to nw-id★
    ; _↦_ to _↦ⁿʷ_
    ; `∀ to ∀ⁿʷ
    ; gen to genⁿ
    ; untag to untagⁿ
    ; sealⁿ to sealⁿ
    ; inst to instʷ
    ; tag to tagʷ
    ; unsealʷ to unsealʷ
    )
open import NarrowWidenComposition using
  ( wrap-untagⁿ
  ; wrap-tagʷ
  )
open import proof.CoercionProperties
  using
    ( ModeRename
    ; coercion-renameᵗᵐ
    ; coercion-weakenᵐ
    ; modeRename-idTyAllowed
    )
open import proof.TypeProperties
  using (TyRenameWf-suc; renameᵗ-preserves-WfTy)

------------------------------------------------------------------------
-- Realizing imprecision assumptions as target coercions
------------------------------------------------------------------------

ModeRename-suc-ext :
  ∀ {μ} →
  ModeRename suc μ (extᵈ μ)
ModeRename-suc-ext {μ} X with μ X
ModeRename-suc-ext X | id-only = refl
ModeRename-suc-ext X | tag-or-id = refl
ModeRename-suc-ext X | seal-or-id = refl

ModeRename-suc-gen :
  ∀ {μ} →
  ModeRename suc μ (genᵈ μ)
ModeRename-suc-gen {μ} X with μ X
ModeRename-suc-gen X | id-only = refl
ModeRename-suc-gen X | tag-or-id = refl
ModeRename-suc-gen X | seal-or-id = refl

ModeRename-suc-inst :
  ∀ {μ} →
  ModeRename suc μ (instᵈ μ)
ModeRename-suc-inst {μ} X with μ X
ModeRename-suc-inst X | id-only = refl
ModeRename-suc-inst X | tag-or-id = refl
ModeRename-suc-inst X | seal-or-id = refl

ModeRename-suc-id-only :
  ModeRename suc id-onlyᵈ id-onlyᵈ
ModeRename-suc-id-only X = refl

AllIdMode : ModeEnv → Set
AllIdMode μ = ∀ X → μ X ≡ id-only

AllIdMode-ext :
  ∀ {μ} →
  AllIdMode μ →
  AllIdMode (extᵈ μ)
AllIdMode-ext all-id zero = refl
AllIdMode-ext all-id (suc X) = all-id X

idTyAllowed-all-id :
  ∀ {μ A} →
  AllIdMode μ →
  idTyAllowed μ A ≡ true
idTyAllowed-all-id {A = ＇ α} all-id rewrite all-id α = refl
idTyAllowed-all-id {A = ‵ ι} all-id = refl
idTyAllowed-all-id {A = ★} all-id = refl
idTyAllowed-all-id {A = A ⇒ B} all-id
    rewrite idTyAllowed-all-id {A = A} all-id
          | idTyAllowed-all-id {A = B} all-id =
  refl
idTyAllowed-all-id {A = `∀ A} all-id =
  idTyAllowed-all-id {A = A} (AllIdMode-ext all-id)

idTyAllowed-id-only :
  ∀ A →
  idTyAllowed id-onlyᵈ A ≡ true
idTyAllowed-id-only A = idTyAllowed-all-id {A = A} (λ X → refl)

idTyAllowed-shift-gen :
  ∀ {μ B} →
  idTyAllowed μ B ≡ true →
  idTyAllowed (genᵈ μ) (⇑ᵗ B) ≡ true
idTyAllowed-shift-gen {μ = μ} {B = B} ok =
  modeRename-idTyAllowed {ρ = suc} {μ = μ} {ν = genᵈ μ} {A = B}
    ModeRename-suc-gen ok

idTyAllowed-shift-inst :
  ∀ {μ B} →
  idTyAllowed μ B ≡ true →
  idTyAllowed (instᵈ μ) (⇑ᵗ B) ≡ true
idTyAllowed-shift-inst {μ = μ} {B = B} ok =
  modeRename-idTyAllowed {ρ = suc} {μ = μ} {ν = instᵈ μ} {A = B}
    ModeRename-suc-inst ok

data Realizesᵐ (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) : ImpCtx → Set₁ where
  real-[] :
    Realizesᵐ μ Δ Σ []

  real-xx : ∀ {Φ X Y c d} →
    WfTy Δ (＇ X) →
    WfTy Δ (＇ Y) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ Y →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ＇ Y =⇒ ＇ X →
    Realizesᵐ μ Δ Σ Φ →
    Realizesᵐ μ Δ Σ ((X ˣ⊑ˣ Y) ∷ Φ)

  real-star : ∀ {Φ X c d} →
    WfTy Δ (＇ X) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ★ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ★ =⇒ ＇ X →
    Realizesᵐ μ Δ Σ Φ →
    Realizesᵐ μ Δ Σ ((X ˣ⊑★) ∷ Φ)

Realizes : TyCtx → Store → ImpCtx → Set₁
Realizes Δ Σ Φ = Realizesᵐ id-onlyᵈ Δ Σ Φ

data RealizesCastᵐ
    (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) : ImpCtx → Set₁ where
  real-cast-[] :
    RealizesCastᵐ μ Δ Σ []

  real-cast-xx : ∀ {Φ X Y c d} →
    WfTy Δ (＇ X) →
    WfTy Δ (＇ Y) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ＇ Y →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ＇ Y ⊒ ＇ X →
    RealizesCastᵐ μ Δ Σ Φ →
    RealizesCastᵐ μ Δ Σ ((X ˣ⊑ˣ Y) ∷ Φ)

  real-cast-star : ∀ {Φ X c d} →
    WfTy Δ (＇ X) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ★ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ★ ⊒ ＇ X →
    RealizesCastᵐ μ Δ Σ Φ →
    RealizesCastᵐ μ Δ Σ ((X ˣ⊑★) ∷ Φ)

RealizesCast : TyCtx → Store → ImpCtx → Set₁
RealizesCast Δ Σ Φ = RealizesCastᵐ id-onlyᵈ Δ Σ Φ

realizes-xx-up :
  ∀ {μ Δ Σ Φ X Y} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ Y
realizes-xx-up (real-xx hX hY c⊢ d⊢ r) (here refl) = _ , c⊢
realizes-xx-up (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-xx-up r x∈
realizes-xx-up (real-star hX c⊢ d⊢ r) (here ())
realizes-xx-up (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-xx-up r x∈

realizes-xx-down :
  ∀ {μ Δ Σ Φ X Y} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ Y =⇒ ＇ X
realizes-xx-down (real-xx hX hY c⊢ d⊢ r) (here refl) = _ , d⊢
realizes-xx-down (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-xx-down r x∈
realizes-xx-down (real-star hX c⊢ d⊢ r) (here ())
realizes-xx-down (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-xx-down r x∈

realizes-star-up :
  ∀ {μ Δ Σ Φ X} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ★
realizes-star-up (real-xx hX hY c⊢ d⊢ r) (here ())
realizes-star-up (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-star-up r x∈
realizes-star-up (real-star hX c⊢ d⊢ r) (here refl) = _ , c⊢
realizes-star-up (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-star-up r x∈

realizes-star-down :
  ∀ {μ Δ Σ Φ X} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ★ =⇒ ＇ X
realizes-star-down (real-xx hX hY c⊢ d⊢ r) (here ())
realizes-star-down (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-star-down r x∈
realizes-star-down (real-star hX c⊢ d⊢ r) (here refl) = _ , d⊢
realizes-star-down (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-star-down r x∈

realizes-cast-xx-up :
  ∀ {μ Δ Σ Φ X Y} →
  RealizesCastᵐ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ＇ Y
realizes-cast-xx-up (real-cast-xx hX hY c⊑ d⊒ r) (here refl) = _ , c⊑
realizes-cast-xx-up (real-cast-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-cast-xx-up r x∈
realizes-cast-xx-up (real-cast-star hX c⊑ d⊒ r) (here ())
realizes-cast-xx-up (real-cast-star hX c⊑ d⊒ r) (there x∈) =
  realizes-cast-xx-up r x∈

realizes-cast-xx-down :
  ∀ {μ Δ Σ Φ X Y} →
  RealizesCastᵐ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ Y ⊒ ＇ X
realizes-cast-xx-down (real-cast-xx hX hY c⊑ d⊒ r) (here refl) = _ , d⊒
realizes-cast-xx-down (real-cast-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-cast-xx-down r x∈
realizes-cast-xx-down (real-cast-star hX c⊑ d⊒ r) (here ())
realizes-cast-xx-down (real-cast-star hX c⊑ d⊒ r) (there x∈) =
  realizes-cast-xx-down r x∈

realizes-cast-star-up :
  ∀ {μ Δ Σ Φ X} →
  RealizesCastᵐ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ★
realizes-cast-star-up (real-cast-xx hX hY c⊑ d⊒ r) (here ())
realizes-cast-star-up (real-cast-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-cast-star-up r x∈
realizes-cast-star-up (real-cast-star hX c⊑ d⊒ r) (here refl) = _ , c⊑
realizes-cast-star-up (real-cast-star hX c⊑ d⊒ r) (there x∈) =
  realizes-cast-star-up r x∈

realizes-cast-star-down :
  ∀ {μ Δ Σ Φ X} →
  RealizesCastᵐ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ ＇ X
realizes-cast-star-down (real-cast-xx hX hY c⊑ d⊒ r) (here ())
realizes-cast-star-down (real-cast-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-cast-star-down r x∈
realizes-cast-star-down (real-cast-star hX c⊑ d⊒ r) (here refl) = _ , d⊒
realizes-cast-star-down (real-cast-star hX c⊑ d⊒ r) (there x∈) =
  realizes-cast-star-down r x∈

Realizes-store-weaken :
  ∀ {μ Δ Σ Σ′ Φ} →
  StoreIncl Σ Σ′ →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ μ Δ Σ′ Φ
Realizes-store-weaken incl real-[] = real-[]
Realizes-store-weaken incl (real-xx hX hY c⊢ d⊢ r) =
  real-xx
    hX
    hY
    (coercion-weakenᵐ ≤-refl incl c⊢)
    (coercion-weakenᵐ ≤-refl incl d⊢)
    (Realizes-store-weaken incl r)
Realizes-store-weaken incl (real-star hX c⊢ d⊢ r) =
  real-star
    hX
    (coercion-weakenᵐ ≤-refl incl c⊢)
    (coercion-weakenᵐ ≤-refl incl d⊢)
    (Realizes-store-weaken incl r)

RealizesCast-store-weaken :
  ∀ {μ Δ Σ Σ′ Φ} →
  StoreIncl Σ Σ′ →
  RealizesCastᵐ μ Δ Σ Φ →
  RealizesCastᵐ μ Δ Σ′ Φ
RealizesCast-store-weaken incl real-cast-[] = real-cast-[]
RealizesCast-store-weaken incl (real-cast-xx hX hY c⊑ d⊒ r) =
  real-cast-xx
    hX
    hY
    (widen-weaken ≤-refl incl c⊑)
    (narrow-weaken ≤-refl incl d⊒)
    (RealizesCast-store-weaken incl r)
RealizesCast-store-weaken incl (real-cast-star hX c⊑ d⊒ r) =
  real-cast-star
    hX
    (widen-weaken ≤-refl incl c⊑)
    (narrow-weaken ≤-refl incl d⊒)
    (RealizesCast-store-weaken incl r)

Realizes-rename-suc :
  ∀ {μ ν Δ Σ Φ} →
  ModeRename suc μ ν →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ ν (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizes-rename-suc rel real-[] = real-[]
Realizes-rename-suc rel (real-xx hX hY c⊢ d⊢ r) =
  real-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hY TyRenameWf-suc)
    (coercion-renameᵗᵐ TyRenameWf-suc rel c⊢)
    (coercion-renameᵗᵐ TyRenameWf-suc rel d⊢)
    (Realizes-rename-suc rel r)
Realizes-rename-suc rel (real-star hX c⊢ d⊢ r) =
  real-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (coercion-renameᵗᵐ TyRenameWf-suc rel c⊢)
    (coercion-renameᵗᵐ TyRenameWf-suc rel d⊢)
    (Realizes-rename-suc rel r)

RealizesCast-rename-suc :
  ∀ {μ ν Δ Σ Φ} →
  ModeRename suc μ ν →
  RealizesCastᵐ μ Δ Σ Φ →
  RealizesCastᵐ ν (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
RealizesCast-rename-suc rel real-cast-[] = real-cast-[]
RealizesCast-rename-suc rel (real-cast-xx hX hY c⊑ d⊒ r) =
  real-cast-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hY TyRenameWf-suc)
    (widen-renameᵗ TyRenameWf-suc rel c⊑)
    (narrow-renameᵗ TyRenameWf-suc rel d⊒)
    (RealizesCast-rename-suc rel r)
RealizesCast-rename-suc rel (real-cast-star hX c⊑ d⊒ r) =
  real-cast-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (widen-renameᵗ TyRenameWf-suc rel c⊑)
    (narrow-renameᵗ TyRenameWf-suc rel d⊒)
    (RealizesCast-rename-suc rel r)

Realizes-⇑ᵢ :
  ∀ {μ Δ Σ Φ} →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizes-⇑ᵢ = Realizes-rename-suc ModeRename-suc-ext

RealizesCast-⇑ᵢ :
  ∀ {μ Δ Σ Φ} →
  RealizesCastᵐ μ Δ Σ Φ →
  RealizesCastᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
RealizesCast-⇑ᵢ = RealizesCast-rename-suc ModeRename-suc-ext

Realizes-∀ⁱ :
  ∀ {μ Δ Σ Φ} →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
Realizes-∀ⁱ r =
  real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl)
    (cast-id (wfVar z<s) refl)
    (Realizes-⇑ᵢ r)

RealizesCast-∀ⁱ :
  ∀ {μ Δ Σ Φ} →
  RealizesCastᵐ μ Δ Σ Φ →
  RealizesCastᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
RealizesCast-∀ⁱ r =
  real-cast-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl , nw-cross (id-＇ⁿʷ zero))
    (cast-id (wfVar z<s) refl , nw-cross (id-＇ⁿʷ zero))
    (RealizesCast-⇑ᵢ r)

Realizes-ν-inst :
  ∀ {μ Δ Σ Φ} →
  (ℓ : Label) →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (instᵈ μ) (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ)
    ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
Realizes-ν-inst ℓ r =
  real-star
    (wfVar z<s)
    (cast-unseal wf★ (here refl) refl)
    (cast-seal wf★ (here refl) refl)
    (Realizes-store-weaken StoreIncl-drop
      (Realizes-rename-suc ModeRename-suc-inst r))

RealizesCast-ν-inst :
  ∀ {μ Δ Σ Φ} →
  (ℓ : Label) →
  RealizesCastᵐ μ Δ Σ Φ →
  RealizesCastᵐ (instᵈ μ) (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ)
    ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
RealizesCast-ν-inst ℓ r =
  real-cast-star
    (wfVar z<s)
    (cast-unseal wf★ (here refl) refl , unsealʷ zero ★)
    (cast-seal wf★ (here refl) refl , sealⁿ ★ zero)
    (RealizesCast-store-weaken StoreIncl-drop
      (RealizesCast-rename-suc ModeRename-suc-inst r))

Realizes-ν-gen :
  ∀ {μ Δ Σ Φ} →
  (ℓ : Label) →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (genᵈ μ) (suc Δ) (⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
Realizes-ν-gen ℓ r =
  real-star
    (wfVar z<s)
    (cast-tag (wfVar z<s) (＇ zero) refl)
    (cast-untag (wfVar z<s) (＇ zero) refl)
    (Realizes-rename-suc ModeRename-suc-gen r)

RealizesCast-ν-gen :
  ∀ {μ Δ Σ Φ} →
  (ℓ : Label) →
  RealizesCastᵐ μ Δ Σ Φ →
  RealizesCastᵐ (genᵈ μ) (suc Δ) (⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
RealizesCast-ν-gen ℓ r =
  real-cast-star
    (wfVar z<s)
    (cast-tag (wfVar z<s) (＇ zero) refl , tagʷ (＇ zero))
    (cast-untag (wfVar z<s) (＇ zero) refl , untagⁿ (＇ zero))
    (RealizesCast-rename-suc ModeRename-suc-gen r)

realizes-idᵢ :
  ∀ Δ →
  Realizes Δ [] (idᵢ Δ)
realizes-idᵢ zero = real-[]
realizes-idᵢ (suc Δ) =
  real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) (idTyAllowed-id-only (＇ zero)))
    (cast-id (wfVar z<s) (idTyAllowed-id-only (＇ zero)))
    (Realizes-rename-suc ModeRename-suc-id-only (realizes-idᵢ Δ))

realizesCast-idᵢ :
  ∀ Δ →
  RealizesCast Δ [] (idᵢ Δ)
realizesCast-idᵢ zero = real-cast-[]
realizesCast-idᵢ (suc Δ) =
  real-cast-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) (idTyAllowed-id-only (＇ zero)) ,
      nw-cross (id-＇ⁿʷ zero))
    (cast-id (wfVar z<s) (idTyAllowed-id-only (＇ zero)) ,
      nw-cross (id-＇ⁿʷ zero))
    (RealizesCast-rename-suc ModeRename-suc-id-only (realizesCast-idᵢ Δ))

------------------------------------------------------------------------
-- Coercion synthesis from imprecision
------------------------------------------------------------------------

mutual
  coerce-upᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    idTyAllowed μ A ≡ true →
    Realizesᵐ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ C =⇒ A
  coerce-upᵐ ℓ wf★ wf★ ok r id★ =
    idᶜ ★ , cast-id wf★ refl
  coerce-upᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY ok r (idˣ X⊑Y) =
    realizes-xx-up r X⊑Y
  coerce-upᵐ {C = ‵ ι} ℓ wfBase wfBase ok r idι =
    idᶜ (‵ ι) , cast-id wfBase refl
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      with idTyAllowed μ A′ in okA′ | idTyAllowed μ B′ in okB′
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true
      with coerce-downᵐ ℓ hA hA′ okA′ r p
         | coerce-upᵐ ℓ hB hB′ okB′ r q
  coerce-upᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true | s , s⊢ | t , t⊢ =
    (s ↦ᶜ t) , cast-fun s⊢ t⊢
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | false | b
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | true | false
  coerce-upᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      with coerce-upᵐ ℓ hA hB ok (Realizes-∀ⁱ r) p
  coerce-upᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      | c , c⊢ =
    `∀ᶜ c , cast-all c⊢
  coerce-upᵐ {C = ‵ ι} ℓ wfBase wf★ ok r (tag ι) =
    ((‵ ι) !ᶜ) , cast-tag wfBase (‵ ι) refl
  coerce-upᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      with coerce-downᵐ ℓ hA wf★ refl r p
         | coerce-upᵐ ℓ hB wf★ refl r q
  coerce-upᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      | s , s⊢ | t , t⊢ =
    ((s ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    cast-seq (cast-fun s⊢ t⊢) (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl)
  coerce-upᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-star-up r X⊑★
  coerce-upᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      with coerce-upᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-inst {μ = μ} {B = B} ok)
             (Realizes-ν-inst ℓ r)
             p
  coerce-upᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      | c , c⊢ =
    instᶜ B c , cast-inst hB occ c⊢

  coerce-downᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    idTyAllowed μ A ≡ true →
    Realizesᵐ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ C
  coerce-downᵐ ℓ wf★ wf★ ok r id★ =
    idᶜ ★ , cast-id wf★ refl
  coerce-downᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY ok r (idˣ X⊑Y) =
    realizes-xx-down r X⊑Y
  coerce-downᵐ {C = ‵ ι} ℓ wfBase wfBase ok r idι =
    idᶜ (‵ ι) , cast-id wfBase refl
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      with idTyAllowed μ A′ in okA′ | idTyAllowed μ B′ in okB′
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true
      with coerce-upᵐ ℓ hA hA′ okA′ r p
         | coerce-downᵐ ℓ hB hB′ okB′ r q
  coerce-downᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true | s , s⊢ | t , t⊢ =
    (s ↦ᶜ t) , cast-fun s⊢ t⊢
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | false | b
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | true | false
  coerce-downᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      with coerce-downᵐ ℓ hA hB ok (Realizes-∀ⁱ r) p
  coerce-downᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      | c , c⊢ =
    `∀ᶜ c , cast-all c⊢
  coerce-downᵐ {C = ‵ ι} ℓ wfBase wf★ ok r (tag ι) =
    ((‵ ι) ？ᶜ) , cast-untag wfBase (‵ ι) refl
  coerce-downᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      with coerce-upᵐ ℓ hA wf★ refl r p
         | coerce-downᵐ ℓ hB wf★ refl r q
  coerce-downᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      | s , s⊢ | t , t⊢ =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ t)) ,
    cast-seq (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl) (cast-fun s⊢ t⊢)
  coerce-downᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-star-down r X⊑★
  coerce-downᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      with coerce-downᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-gen {μ = μ} {B = B} ok)
             (Realizes-ν-gen ℓ r)
             p
  coerce-downᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      | c , c⊢ =
    genᶜ B c , cast-gen hB occ c⊢

mutual
  coerce-upʷᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    idTyAllowed μ A ≡ true →
    RealizesCastᵐ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊑ A
  coerce-upʷᵐ ℓ wf★ wf★ ok r id★ =
    idᶜ ★ , cast-id wf★ refl , nw-id★
  coerce-upʷᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY ok r (idˣ X⊑Y) =
    realizes-cast-xx-up r X⊑Y
  coerce-upʷᵐ {C = ‵ ι} ℓ wfBase wfBase ok r idι =
    idᶜ (‵ ι) , cast-id wfBase refl , nw-cross (id-‵ⁿʷ ι)
  coerce-upʷᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      with idTyAllowed μ A′ in okA′ | idTyAllowed μ B′ in okB′
  coerce-upʷᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true
      with coerce-downⁿᵐ ℓ hA hA′ okA′ r p
         | coerce-upʷᵐ ℓ hB hB′ okB′ r q
  coerce-upʷᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true | s , s⊒ | t , t⊑ =
    (s ↦ᶜ t) , cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
    nw-cross (proj₂ s⊒ ↦ⁿʷ proj₂ t⊑)
  coerce-upʷᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | false | b
  coerce-upʷᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | true | false
  coerce-upʷᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      with coerce-upʷᵐ ℓ hA hB ok (RealizesCast-∀ⁱ r) p
  coerce-upʷᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      | c , c⊑ =
    `∀ᶜ c , cast-all (proj₁ c⊑) , nw-cross (∀ⁿʷ (proj₂ c⊑))
  coerce-upʷᵐ {C = ‵ ι} ℓ wfBase wf★ ok r (tag ι) =
    (‵ ι) !ᶜ , cast-tag wfBase (‵ ι) refl , tagʷ (‵ ι)
  coerce-upʷᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      with coerce-downⁿᵐ ℓ hA wf★ refl r p
         | coerce-upʷᵐ ℓ hB wf★ refl r q
  coerce-upʷᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      | s , s⊒ | t , t⊑ =
    wrap-tagʷ
      (cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
        proj₂ s⊒ ↦ⁿʷ proj₂ t⊑)
      (wf⇒ wf★ wf★)
      ★⇒★
      refl
  coerce-upʷᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-cast-star-up r X⊑★
  coerce-upʷᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      with coerce-upʷᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-inst {μ = μ} {B = B} ok)
             (RealizesCast-ν-inst ℓ r)
             p
  coerce-upʷᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      | c , c⊑ =
    instᶜ B c , cast-inst hB occ (proj₁ c⊑) , instʷ (proj₂ c⊑)

  coerce-downⁿᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    idTyAllowed μ A ≡ true →
    RealizesCastᵐ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ C
  coerce-downⁿᵐ ℓ wf★ wf★ ok r id★ =
    idᶜ ★ , cast-id wf★ refl , nw-id★
  coerce-downⁿᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY ok r (idˣ X⊑Y) =
    realizes-cast-xx-down r X⊑Y
  coerce-downⁿᵐ {C = ‵ ι} ℓ wfBase wfBase ok r idι =
    idᶜ (‵ ι) , cast-id wfBase refl , nw-cross (id-‵ⁿʷ ι)
  coerce-downⁿᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      with idTyAllowed μ A′ in okA′ | idTyAllowed μ B′ in okB′
  coerce-downⁿᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true
      with coerce-upʷᵐ ℓ hA hA′ okA′ r p
         | coerce-downⁿᵐ ℓ hB hB′ okB′ r q
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true | s , s⊑ | t , t⊒ =
    (s ↦ᶜ t) , cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
    nw-cross (proj₂ s⊑ ↦ⁿʷ proj₂ t⊒)
  coerce-downⁿᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | false | b
  coerce-downⁿᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | true | false
  coerce-downⁿᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      with coerce-downⁿᵐ ℓ hA hB ok (RealizesCast-∀ⁱ r) p
  coerce-downⁿᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      | c , c⊒ =
    `∀ᶜ c , cast-all (proj₁ c⊒) , nw-cross (∀ⁿʷ (proj₂ c⊒))
  coerce-downⁿᵐ {C = ‵ ι} ℓ wfBase wf★ ok r (tag ι) =
    (‵ ι) ？ᶜ , cast-untag wfBase (‵ ι) refl , untagⁿ (‵ ι)
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      with coerce-upʷᵐ ℓ hA wf★ refl r p
         | coerce-downⁿᵐ ℓ hB wf★ refl r q
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      | s , s⊑ | t , t⊒ =
    wrap-untagⁿ
      (wf⇒ wf★ wf★)
      ★⇒★
      refl
      (cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
        proj₂ s⊑ ↦ⁿʷ proj₂ t⊒)
  coerce-downⁿᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-cast-star-down r X⊑★
  coerce-downⁿᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      with coerce-downⁿᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-gen {μ = μ} {B = B} ok)
             (RealizesCast-ν-gen ℓ r)
             p
  coerce-downⁿᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      | c , c⊒ =
    genᶜ B c , cast-gen hB occ (proj₁ c⊒) , genⁿ (proj₂ c⊒)

coerce-up :
  ∀ {Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  Realizes Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ C =⇒ A
coerce-up {A = A} ℓ hC hA r p =
  result
  where
    result : Σ[ c ∈ Coercion ] _ ∣ _ ⊢ c ∶ _ =⇒ A
    result with coerce-upᵐ ℓ hC hA (idTyAllowed-id-only A) r p
    result | c , c⊢ = c , id-onlyᵈ , c⊢

coerce-down :
  ∀ {Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  Realizes Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ A =⇒ C
coerce-down {A = A} ℓ hC hA r p =
  result
  where
    result : Σ[ c ∈ Coercion ] _ ∣ _ ⊢ c ∶ A =⇒ _
    result with coerce-downᵐ ℓ hC hA (idTyAllowed-id-only A) r p
    result | c , c⊢ = c , id-onlyᵈ , c⊢

coerce-upʷ :
  ∀ {Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  RealizesCast Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] Σ[ μ ∈ ModeEnv ] μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊑ A
coerce-upʷ {A = A} ℓ hC hA r p =
  result
  where
    result :
      Σ[ c ∈ Coercion ] Σ[ μ ∈ ModeEnv ] μ ∣ _ ∣ _ ⊢ c ∶ _ ⊑ A
    result with coerce-upʷᵐ ℓ hC hA (idTyAllowed-id-only A) r p
    result | c , c⊑ = c , id-onlyᵈ , c⊑

coerce-downⁿ :
  ∀ {Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  RealizesCast Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ A ⊒ C
coerce-downⁿ {A = A} ℓ hC hA r p =
  result
  where
    result : Σ[ c ∈ Coercion ] _ ∣ _ ⊢ c ∶ A ⊒ _
    result with coerce-downⁿᵐ ℓ hC hA (idTyAllowed-id-only A) r p
    result | c , c⊒ = c , id-onlyᵈ , c⊒

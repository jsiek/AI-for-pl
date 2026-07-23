module Conversion where

-- File Charter:
--   * Typed conversion fragment for GTSF coercions produced by reveal/conceal.
--   * Conversions reuse raw `Coercion` syntax but expose only identity,
--     seal/unseal, arrow, and forall structure.
--   * The embedding lemmas recover ordinary coercion typing, while the
--     reveal/conceal provenance predicates track one seal name through arrows,
--     forall binders, store extension, renaming, and binder opening.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_; n≤1+n; n<1+n; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; subst; sym)
open import Relation.Nullary using (yes; no)

open import Types
open import Store using (StoreIncl)
open import Coercions
open import proof.Core.Properties.CoercionProperties
  using
    ( ModeRename
    ; ModeRename-ext
    ; RevealEnv
    ; RevealEnv-ext
    ; RevealMode
    ; RevealMode-ext
    ; RevealVar
    ; rv-hit
    ; rv-miss
    ; singleRevealEnv
    ; singleSealᵈ
    ; singleSealMode
    ; modeRename-idTyAllowed
    ; modeRename-sealModeAllowed
    ; single-mode-rename-lower
    )
open import proof.Core.Properties.StoreProperties using
  ( ∈-renameStoreᵗ
  ; renameStoreᵗ-incl
  )
open import proof.Core.Properties.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; TySubstWf
    ; TySubstWf-exts
    ; WfTy-weakenᵗ
    ; renameᵗ-preserves-WfTy
    ; renameStoreᵗ-ext-suc-comm
    ; renameStoreᵗ-single-suc-cancel
    ; renameᵗ-ext-suc-comm
    ; renameᵗ-single-suc-cancel
    ; singleRenameᵗ-Wf
    ; singleRenameᵗ-Wf-<
    )

------------------------------------------------------------------------
-- Conversion typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_↑ˢ_ _∣_∣_⊢_∶_↓ˢ_

mutual
  data _∣_∣_⊢_∶_↑ˢ_
      (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) :
      Coercion → Ty → Ty → Set where
    conv↑-id : ∀ {A} →
      WfTy Δ A →
      idTyAllowed μ A ≡ true →
      μ ∣ Δ ∣ Σ ⊢ id A ∶ A ↑ˢ A

    conv↑-unseal : ∀ {α A} →
      WfTy Δ A →
      (α , A) ∈ Σ →
      sealModeAllowed (μ α) ≡ true →
      μ ∣ Δ ∣ Σ ⊢ unseal α A ∶ ＇ α ↑ˢ A

    conv↑-fun : ∀ {A A′ B B′ s t} →
      μ ∣ Δ ∣ Σ ⊢ s ∶ A′ ↓ˢ A →
      μ ∣ Δ ∣ Σ ⊢ t ∶ B ↑ˢ B′ →
      μ ∣ Δ ∣ Σ ⊢ s ↦ t ∶ (A ⇒ B) ↑ˢ (A′ ⇒ B′)

    conv↑-all : ∀ {A B s} →
      extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ↑ˢ B →
      μ ∣ Δ ∣ Σ ⊢ `∀ s ∶ `∀ A ↑ˢ `∀ B

  data _∣_∣_⊢_∶_↓ˢ_
      (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) :
      Coercion → Ty → Ty → Set where
    conv↓-id : ∀ {A} →
      WfTy Δ A →
      idTyAllowed μ A ≡ true →
      μ ∣ Δ ∣ Σ ⊢ id A ∶ A ↓ˢ A

    conv↓-seal : ∀ {α A} →
      WfTy Δ A →
      (α , A) ∈ Σ →
      sealModeAllowed (μ α) ≡ true →
      μ ∣ Δ ∣ Σ ⊢ seal A α ∶ A ↓ˢ ＇ α

    conv↓-fun : ∀ {A A′ B B′ s t} →
      μ ∣ Δ ∣ Σ ⊢ s ∶ A′ ↑ˢ A →
      μ ∣ Δ ∣ Σ ⊢ t ∶ B ↓ˢ B′ →
      μ ∣ Δ ∣ Σ ⊢ s ↦ t ∶ (A ⇒ B) ↓ˢ (A′ ⇒ B′)

    conv↓-all : ∀ {A B s} →
      extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ↓ˢ B →
      μ ∣ Δ ∣ Σ ⊢ `∀ s ∶ `∀ A ↓ˢ `∀ B

infix 4 _∣_⊢_∶_↑ˢ_ _∣_⊢_∶_↓ˢ_

_∣_⊢_∶_↑ˢ_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A ↑ˢ B =
  ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B

_∣_⊢_∶_↓ˢ_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A ↓ˢ B =
  ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B

------------------------------------------------------------------------
-- Single-name reveal/conceal provenance
------------------------------------------------------------------------

mutual
  data RevealConversion
      (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) (α : TyVar) (C : Ty) :
      Coercion → Ty → Ty → Set where
    reveal-id-var : ∀ {Y} →
      WfTy Δ (＇ Y) →
      idModeAllowed (μ Y) ≡ true →
      RevealConversion μ Δ Σ α C (id (＇ Y)) (＇ Y) (＇ Y)

    reveal-id-base : ∀ {ι} →
      RevealConversion μ Δ Σ α C (id (‵ ι)) (‵ ι) (‵ ι)

    reveal-id-★ :
      RevealConversion μ Δ Σ α C (id ★) ★ ★

    reveal-unseal :
      WfTy Δ C →
      (α , C) ∈ Σ →
      sealModeAllowed (μ α) ≡ true →
      RevealConversion μ Δ Σ α C (unseal α C) (＇ α) C

    reveal-fun : ∀ {A A′ B B′ s t} →
      ConcealConversion μ Δ Σ α C s A′ A →
      RevealConversion μ Δ Σ α C t B B′ →
      RevealConversion μ Δ Σ α C (s ↦ t) (A ⇒ B) (A′ ⇒ B′)

    reveal-all : ∀ {A B s} →
      RevealConversion (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
        (suc α) (⇑ᵗ C) s A B →
      RevealConversion μ Δ Σ α C (`∀ s) (`∀ A) (`∀ B)

  data ConcealConversion
      (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) (α : TyVar) (C : Ty) :
      Coercion → Ty → Ty → Set where
    conceal-id-var : ∀ {Y} →
      WfTy Δ (＇ Y) →
      idModeAllowed (μ Y) ≡ true →
      ConcealConversion μ Δ Σ α C (id (＇ Y)) (＇ Y) (＇ Y)

    conceal-id-base : ∀ {ι} →
      ConcealConversion μ Δ Σ α C (id (‵ ι)) (‵ ι) (‵ ι)

    conceal-id-★ :
      ConcealConversion μ Δ Σ α C (id ★) ★ ★

    conceal-seal :
      WfTy Δ C →
      (α , C) ∈ Σ →
      sealModeAllowed (μ α) ≡ true →
      ConcealConversion μ Δ Σ α C (seal C α) C (＇ α)

    conceal-fun : ∀ {A A′ B B′ s t} →
      RevealConversion μ Δ Σ α C s A′ A →
      ConcealConversion μ Δ Σ α C t B B′ →
      ConcealConversion μ Δ Σ α C (s ↦ t) (A ⇒ B) (A′ ⇒ B′)

    conceal-all : ∀ {A B s} →
      ConcealConversion (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
        (suc α) (⇑ᵗ C) s A B →
      ConcealConversion μ Δ Σ α C (`∀ s) (`∀ A) (`∀ B)

mutual
  reveal-conversion-typing :
    ∀ {μ Δ Σ α C c A B} →
    RevealConversion μ Δ Σ α C c A B →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B
  reveal-conversion-typing (reveal-id-var hY ok) = conv↑-id hY ok
  reveal-conversion-typing reveal-id-base = conv↑-id wfBase refl
  reveal-conversion-typing reveal-id-★ = conv↑-id wf★ refl
  reveal-conversion-typing (reveal-unseal hC α∈Σ ok) =
    conv↑-unseal hC α∈Σ ok
  reveal-conversion-typing (reveal-fun s↓ t↑) =
    conv↑-fun (conceal-conversion-typing s↓)
      (reveal-conversion-typing t↑)
  reveal-conversion-typing (reveal-all s↑) =
    conv↑-all (reveal-conversion-typing s↑)

  conceal-conversion-typing :
    ∀ {μ Δ Σ α C c A B} →
    ConcealConversion μ Δ Σ α C c A B →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B
  conceal-conversion-typing (conceal-id-var hY ok) = conv↓-id hY ok
  conceal-conversion-typing conceal-id-base = conv↓-id wfBase refl
  conceal-conversion-typing conceal-id-★ = conv↓-id wf★ refl
  conceal-conversion-typing (conceal-seal hC α∈Σ ok) =
    conv↓-seal hC α∈Σ ok
  conceal-conversion-typing (conceal-fun s↑ t↓) =
    conv↓-fun (reveal-conversion-typing s↑)
      (conceal-conversion-typing t↓)
  conceal-conversion-typing (conceal-all s↓) =
    conv↓-all (conceal-conversion-typing s↓)

mutual
  reveal↑ :
    ∀ {μ Δ Σ α C A B} →
    μ ∣ Δ ∣ Σ ⊢ reveal A α C ∶ A ↑ˢ B →
    RevealConversion μ Δ Σ α C (reveal A α C) A B
  reveal↑ {α = α} {A = ＇ Y} c↑ with α ≟ Y
  reveal↑ {α = α} {A = ＇ .α} (conv↑-unseal hC α∈Σ ok)
      | yes refl =
    reveal-unseal hC α∈Σ ok
  reveal↑ {α = α} {A = ＇ Y} (conv↑-id hY ok) | no α≢Y =
    reveal-id-var hY ok
  reveal↑ {A = ‵ ι} (conv↑-id hι ok) = reveal-id-base
  reveal↑ {A = ★} (conv↑-id h★ ok) = reveal-id-★
  reveal↑ {A = A ⇒ B} (conv↑-fun s↓ t↑) =
    reveal-fun (conceal↓ s↓) (reveal↑ t↑)
  reveal↑ {A = `∀ A} (conv↑-all s↑) = reveal-all (reveal↑ s↑)

  conceal↓ :
    ∀ {μ Δ Σ α C A B} →
    μ ∣ Δ ∣ Σ ⊢ conceal B α C ∶ A ↓ˢ B →
    ConcealConversion μ Δ Σ α C (conceal B α C) A B
  conceal↓ {α = α} {B = ＇ Y} c↓ with α ≟ Y
  conceal↓ {α = α} {B = ＇ .α} (conv↓-seal hC α∈Σ ok)
      | yes refl =
    conceal-seal hC α∈Σ ok
  conceal↓ {α = α} {B = ＇ Y} (conv↓-id hY ok) | no α≢Y =
    conceal-id-var hY ok
  conceal↓ {B = ‵ ι} (conv↓-id hι ok) = conceal-id-base
  conceal↓ {B = ★} (conv↓-id h★ ok) = conceal-id-★
  conceal↓ {B = A ⇒ B} (conv↓-fun s↑ t↓) =
    conceal-fun (reveal↑ s↑) (conceal↓ t↓)
  conceal↓ {B = `∀ B} (conv↓-all s↓) = conceal-all (conceal↓ s↓)

mutual
  rename-reveal-conversion :
    ∀ {μ ν Δ Δ′ Σ α C c A B ρ} →
    TyRenameWf Δ Δ′ ρ →
    ModeRename ρ μ ν →
    RevealConversion μ Δ Σ α C c A B →
    RevealConversion ν Δ′ (renameStoreᵗ ρ Σ) (ρ α)
      (renameᵗ ρ C) (renameᶜ ρ c) (renameᵗ ρ A) (renameᵗ ρ B)
  rename-reveal-conversion {μ = μ} {ν = ν} {ρ = ρ} hρ hμ
      (reveal-id-var {Y = Y} hY ok) =
    reveal-id-var
      (renameᵗ-preserves-WfTy hY hρ)
      (modeRename-idTyAllowed
        {ρ = ρ} {μ = μ} {ν = ν} {A = ＇ Y} hμ ok)
  rename-reveal-conversion hρ hμ reveal-id-base = reveal-id-base
  rename-reveal-conversion hρ hμ reveal-id-★ = reveal-id-★
  rename-reveal-conversion {μ = μ} {ν = ν} {ρ = ρ} hρ hμ
      (reveal-unseal hC α∈Σ ok) =
    reveal-unseal
      (renameᵗ-preserves-WfTy hC hρ)
      (∈-renameStoreᵗ ρ α∈Σ)
      (modeRename-sealModeAllowed
        {ρ = ρ} {μ = μ} {ν = ν} hμ ok)
  rename-reveal-conversion hρ hμ (reveal-fun s↓ t↑) =
    reveal-fun
      (rename-conceal-conversion hρ hμ s↓)
      (rename-reveal-conversion hρ hμ t↑)
  rename-reveal-conversion {ρ = ρ} hρ hμ (reveal-all s↑) =
    reveal-all
      (subst
        (λ D → RevealConversion _ _ _ _ D _ _ _)
        (renameᵗ-ext-suc-comm ρ _)
        (subst
          (λ Σ′ → RevealConversion _ _ Σ′ _ _ _ _ _)
          (renameStoreᵗ-ext-suc-comm ρ _)
          (rename-reveal-conversion
            (TyRenameWf-ext hρ) (ModeRename-ext hμ) s↑)))

  rename-conceal-conversion :
    ∀ {μ ν Δ Δ′ Σ α C c A B ρ} →
    TyRenameWf Δ Δ′ ρ →
    ModeRename ρ μ ν →
    ConcealConversion μ Δ Σ α C c A B →
    ConcealConversion ν Δ′ (renameStoreᵗ ρ Σ) (ρ α)
      (renameᵗ ρ C) (renameᶜ ρ c) (renameᵗ ρ A) (renameᵗ ρ B)
  rename-conceal-conversion {μ = μ} {ν = ν} {ρ = ρ} hρ hμ
      (conceal-id-var {Y = Y} hY ok) =
    conceal-id-var
      (renameᵗ-preserves-WfTy hY hρ)
      (modeRename-idTyAllowed
        {ρ = ρ} {μ = μ} {ν = ν} {A = ＇ Y} hμ ok)
  rename-conceal-conversion hρ hμ conceal-id-base = conceal-id-base
  rename-conceal-conversion hρ hμ conceal-id-★ = conceal-id-★
  rename-conceal-conversion {μ = μ} {ν = ν} {ρ = ρ} hρ hμ
      (conceal-seal hC α∈Σ ok) =
    conceal-seal
      (renameᵗ-preserves-WfTy hC hρ)
      (∈-renameStoreᵗ ρ α∈Σ)
      (modeRename-sealModeAllowed
        {ρ = ρ} {μ = μ} {ν = ν} hμ ok)
  rename-conceal-conversion hρ hμ (conceal-fun s↑ t↓) =
    conceal-fun
      (rename-reveal-conversion hρ hμ s↑)
      (rename-conceal-conversion hρ hμ t↓)
  rename-conceal-conversion {ρ = ρ} hρ hμ (conceal-all s↓) =
    conceal-all
      (subst
        (λ D → ConcealConversion _ _ _ _ D _ _ _)
        (renameᵗ-ext-suc-comm ρ _)
        (subst
          (λ Σ′ → ConcealConversion _ _ Σ′ _ _ _ _ _)
          (renameStoreᵗ-ext-suc-comm ρ _)
          (rename-conceal-conversion
            (TyRenameWf-ext hρ) (ModeRename-ext hμ) s↓)))

mutual
  weaken-reveal-conversion :
    ∀ {μ Δ Σ Σ′ α C c A B} →
    StoreIncl Σ Σ′ →
    RevealConversion μ Δ Σ α C c A B →
    RevealConversion μ Δ Σ′ α C c A B
  weaken-reveal-conversion incl (reveal-id-var hY ok) =
    reveal-id-var hY ok
  weaken-reveal-conversion incl reveal-id-base = reveal-id-base
  weaken-reveal-conversion incl reveal-id-★ = reveal-id-★
  weaken-reveal-conversion incl (reveal-unseal hC α∈Σ ok) =
    reveal-unseal hC (incl α∈Σ) ok
  weaken-reveal-conversion incl (reveal-fun s↓ t↑) =
    reveal-fun
      (weaken-conceal-conversion incl s↓)
      (weaken-reveal-conversion incl t↑)
  weaken-reveal-conversion incl (reveal-all s↑) =
    reveal-all
      (weaken-reveal-conversion (renameStoreᵗ-incl suc incl) s↑)

  weaken-conceal-conversion :
    ∀ {μ Δ Σ Σ′ α C c A B} →
    StoreIncl Σ Σ′ →
    ConcealConversion μ Δ Σ α C c A B →
    ConcealConversion μ Δ Σ′ α C c A B
  weaken-conceal-conversion incl (conceal-id-var hY ok) =
    conceal-id-var hY ok
  weaken-conceal-conversion incl conceal-id-base = conceal-id-base
  weaken-conceal-conversion incl conceal-id-★ = conceal-id-★
  weaken-conceal-conversion incl (conceal-seal hC α∈Σ ok) =
    conceal-seal hC (incl α∈Σ) ok
  weaken-conceal-conversion incl (conceal-fun s↑ t↓) =
    conceal-fun
      (weaken-reveal-conversion incl s↑)
      (weaken-conceal-conversion incl t↓)
  weaken-conceal-conversion incl (conceal-all s↓) =
    conceal-all
      (weaken-conceal-conversion (renameStoreᵗ-incl suc incl) s↓)

open-reveal-conversion :
  ∀ {μ Δ Σ α C c A B} →
  α < Δ →
  RevealConversion (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    (suc α) (⇑ᵗ C) c A B →
  RevealConversion μ Δ Σ α C
    (c [ α ]ᶜ) (A [ α ]ᴿ) (B [ α ]ᴿ)
open-reveal-conversion {μ = μ} {Σ = Σ} {α = α} {C = C}
    α<Δ c↑ =
  subst
    (λ D → RevealConversion μ _ Σ α D _ _ _)
    (renameᵗ-single-suc-cancel α C)
    (subst
      (λ Σ′ → RevealConversion μ _ Σ′ α _ _ _ _)
      (renameStoreᵗ-single-suc-cancel α Σ)
      (rename-reveal-conversion
        (singleRenameᵗ-Wf-< α<Δ)
        (single-mode-rename-lower μ α)
        c↑))

open-conceal-conversion :
  ∀ {μ Δ Σ α C c A B} →
  α < Δ →
  ConcealConversion (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    (suc α) (⇑ᵗ C) c A B →
  ConcealConversion μ Δ Σ α C
    (c [ α ]ᶜ) (A [ α ]ᴿ) (B [ α ]ᴿ)
open-conceal-conversion {μ = μ} {Σ = Σ} {α = α} {C = C}
    α<Δ c↓ =
  subst
    (λ D → ConcealConversion μ _ Σ α D _ _ _)
    (renameᵗ-single-suc-cancel α C)
    (subst
      (λ Σ′ → ConcealConversion μ _ Σ′ α _ _ _ _)
      (renameStoreᵗ-single-suc-cancel α Σ)
      (rename-conceal-conversion
        (singleRenameᵗ-Wf-< α<Δ)
        (single-mode-rename-lower μ α)
        c↓))

------------------------------------------------------------------------
-- Embedding into ordinary coercion typing
------------------------------------------------------------------------

mutual
  conversion↑⇒coercion :
    ∀ {μ Δ Σ c A B} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  conversion↑⇒coercion (conv↑-id hA ok) =
    cast-id hA ok
  conversion↑⇒coercion (conv↑-unseal hA α∈Σ ok) =
    cast-unseal hA α∈Σ ok
  conversion↑⇒coercion (conv↑-fun s⊢ t⊢) =
    cast-fun (conversion↓⇒coercion s⊢) (conversion↑⇒coercion t⊢)
  conversion↑⇒coercion (conv↑-all s⊢) =
    cast-all (conversion↑⇒coercion s⊢)

  conversion↓⇒coercion :
    ∀ {μ Δ Σ c A B} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  conversion↓⇒coercion (conv↓-id hA ok) =
    cast-id hA ok
  conversion↓⇒coercion (conv↓-seal hA α∈Σ ok) =
    cast-seal hA α∈Σ ok
  conversion↓⇒coercion (conv↓-fun s⊢ t⊢) =
    cast-fun (conversion↑⇒coercion s⊢) (conversion↓⇒coercion t⊢)
  conversion↓⇒coercion (conv↓-all s⊢) =
    cast-all (conversion↓⇒coercion s⊢)

conversion↑⇒coercion∃ :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
conversion↑⇒coercion∃ (μ , c⊢) =
  μ , conversion↑⇒coercion c⊢

conversion↓⇒coercion∃ :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B
conversion↓⇒coercion∃ (μ , c⊢) =
  μ , conversion↓⇒coercion c⊢

------------------------------------------------------------------------
-- Reveal/conceal conversions
------------------------------------------------------------------------

reveal-var-hit :
  ∀ {μ Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ reveal (＇ α) α C ∶ ＇ α ↑ˢ C
reveal-var-hit {α = α} hC α∈Σ α-ok with α ≟ α
reveal-var-hit {α = α} hC α∈Σ α-ok | yes refl =
  conv↑-unseal hC α∈Σ α-ok
reveal-var-hit {α = α} hC α∈Σ α-ok | no α≢α =
  ⊥-elim (α≢α refl)

conceal-var-hit :
  ∀ {μ Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ conceal (＇ α) α C ∶ C ↓ˢ ＇ α
conceal-var-hit {α = α} hC α∈Σ α-ok with α ≟ α
conceal-var-hit {α = α} hC α∈Σ α-ok | yes refl =
  conv↓-seal hC α∈Σ α-ok
conceal-var-hit {α = α} hC α∈Σ α-ok | no α≢α =
  ⊥-elim (α≢α refl)

reveal-var-miss :
  ∀ {μ Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  idModeAllowed (μ Y) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ reveal (＇ Y) α C ∶ ＇ Y ↑ˢ ＇ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY Y-id with α ≟ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
reveal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | no α≢Y =
  conv↑-id hY Y-id

conceal-var-miss :
  ∀ {μ Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  idModeAllowed (μ Y) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ conceal (＇ Y) α C ∶ ＇ Y ↓ˢ ＇ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY Y-id with α ≟ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
conceal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | no α≢Y =
  conv↓-id hY Y-id

mutual
  reveal-conversion-env :
    ∀ {μ Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    RevealMode μ α →
    μ ∣ Δ ∣ Σ ⊢ reveal (renameᵗ ρ B) α C
      ∶ renameᵗ ρ B ↑ˢ substᵗ σ B
  reveal-conversion-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      with env X<Θ
  reveal-conversion-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    reveal-var-hit hC α∈Σ (proj₁ mode)
  reveal-conversion-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    reveal-var-miss ρX≢α (wfVar (hρ X<Θ)) (proj₂ mode ρX≢α)
  reveal-conversion-env wfBase hρ hσ env hC α∈Σ mode =
    conv↑-id wfBase refl
  reveal-conversion-env wf★ hρ hσ env hC α∈Σ mode =
    conv↑-id wf★ refl
  reveal-conversion-env (wf⇒ hA hB) hρ hσ env hC α∈Σ mode =
    conv↑-fun
      (conceal-conversion-env hA hρ hσ env hC α∈Σ mode)
      (reveal-conversion-env hB hρ hσ env hC α∈Σ mode)
  reveal-conversion-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ mode =
    conv↑-all
      (reveal-conversion-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ)
        (RevealMode-ext mode))

  conceal-conversion-env :
    ∀ {μ Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    RevealMode μ α →
    μ ∣ Δ ∣ Σ ⊢ conceal (renameᵗ ρ B) α C
      ∶ substᵗ σ B ↓ˢ renameᵗ ρ B
  conceal-conversion-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      with env X<Θ
  conceal-conversion-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    conceal-var-hit hC α∈Σ (proj₁ mode)
  conceal-conversion-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    conceal-var-miss ρX≢α (wfVar (hρ X<Θ)) (proj₂ mode ρX≢α)
  conceal-conversion-env wfBase hρ hσ env hC α∈Σ mode =
    conv↓-id wfBase refl
  conceal-conversion-env wf★ hρ hσ env hC α∈Σ mode =
    conv↓-id wf★ refl
  conceal-conversion-env (wf⇒ hA hB) hρ hσ env hC α∈Σ mode =
    conv↓-fun
      (reveal-conversion-env hA hρ hσ env hC α∈Σ mode)
      (conceal-conversion-env hB hρ hσ env hC α∈Σ mode)
  conceal-conversion-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ mode =
    conv↓-all
      (conceal-conversion-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ)
        (RevealMode-ext mode))

reveal-fresh-conversion :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ reveal (B [ Δ ]ᴿ) Δ A
    ∶ B [ Δ ]ᴿ ↑ˢ B [ A ]ᵗ
reveal-fresh-conversion {Δ = Δ} hA hB =
  singleSealᵈ Δ ,
    reveal-conversion-env
      hB
      (singleRenameᵗ-Wf (n<1+n Δ))
      singleTyEnv-Wf-suc
      singleRevealEnv
      (WfTy-weakenᵗ hA (n≤1+n Δ))
      (here refl)
      singleSealMode
  where
    singleTyEnv-Wf-suc :
      TySubstWf (suc Δ) (suc Δ) (singleTyEnv _)
    singleTyEnv-Wf-suc {zero} z<s =
      WfTy-weakenᵗ hA (n≤1+n Δ)
    singleTyEnv-Wf-suc {suc X} (s<s X<Δ) =
      wfVar (m<n⇒m<1+n X<Δ)

conceal-fresh-conversion :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ conceal (B [ Δ ]ᴿ) Δ A
    ∶ B [ A ]ᵗ ↓ˢ B [ Δ ]ᴿ
conceal-fresh-conversion {Δ = Δ} hA hB =
  singleSealᵈ Δ ,
    conceal-conversion-env
      hB
      (singleRenameᵗ-Wf (n<1+n Δ))
      singleTyEnv-Wf-suc
      singleRevealEnv
      (WfTy-weakenᵗ hA (n≤1+n Δ))
      (here refl)
      singleSealMode
  where
    singleTyEnv-Wf-suc :
      TySubstWf (suc Δ) (suc Δ) (singleTyEnv _)
    singleTyEnv-Wf-suc {zero} z<s =
      WfTy-weakenᵗ hA (n≤1+n Δ)
    singleTyEnv-Wf-suc {suc X} (s<s X<Δ) =
      wfVar (m<n⇒m<1+n X<Δ)

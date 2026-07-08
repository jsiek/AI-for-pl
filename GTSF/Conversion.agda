module Conversion where

-- File Charter:
--   * Typed conversion fragment for GTSF coercions produced by reveal/conceal.
--   * Conversions reuse raw `Coercion` syntax but expose only identity,
--     seal/unseal, arrow, and forall structure.
--   * The embedding lemmas recover ordinary coercion typing, while the
--     reveal/conceal lemmas give a finer-grained surface for ν-generated casts.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_; n≤1+n; n<1+n; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; subst; sym)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions
open import proof.CoercionProperties
  using
    ( RevealEnv
    ; RevealEnv-ext
    ; RevealMode
    ; RevealMode-ext
    ; RevealVar
    ; rv-hit
    ; rv-miss
    ; singleRevealEnv
    ; singleSealᵈ
    ; singleSealMode
    )
open import proof.StoreProperties using (∈-renameStoreᵗ)
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; TySubstWf
    ; TySubstWf-exts
    ; WfTy-weakenᵗ
    ; renameᵗ-preserves-WfTy
    ; singleRenameᵗ-Wf
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

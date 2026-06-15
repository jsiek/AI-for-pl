module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF coercion typing.
--   * Coercion weakening, type-renaming, endpoint well-formedness, and
--     reveal/conceal typing lemmas used by term preservation.
--   * Store-specific lemmas belong in `proof.StoreProperties`.
--   * Term substitution/renaming lemmas belong in `proof.TermProperties`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; ≤-refl; n≤1+n; n<1+n; <-≤-trans; <-irrefl;
         m<n⇒m<1+n; suc-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import Store
open import Coercions
open import proof.TypeProperties
open import proof.StoreProperties

------------------------------------------------------------------------
-- Inert coercions
------------------------------------------------------------------------

renameᶜ-preserves-Inert :
  ∀ ρ {c} →
  Inert c →
  Inert (renameᶜ ρ c)
renameᶜ-preserves-Inert ρ (G !) = renameᵗ ρ G !
renameᶜ-preserves-Inert ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ-preserves-Inert ρ (c ↦ d) = renameᶜ ρ c ↦ renameᶜ ρ d
renameᶜ-preserves-Inert ρ (`∀ c) = `∀ (renameᶜ (extᵗ ρ) c)
renameᶜ-preserves-Inert ρ (gen A c) =
  gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) c)

------------------------------------------------------------------------
-- Coercion typing under store/type-context weakening
------------------------------------------------------------------------

coercion-weaken :
  ∀ {Δ Δ′ Σ Σ′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ Σ′ ⊢ c ∶ A =⇒ B
coercion-weaken Δ≤Δ′ incl (cast-id hA) =
  cast-id (WfTy-weakenᵗ hA Δ≤Δ′)
coercion-weaken Δ≤Δ′ incl (cast-seal hA α∈Σ) =
  cast-seal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
coercion-weaken Δ≤Δ′ incl (cast-unseal hA α∈Σ) =
  cast-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
coercion-weaken Δ≤Δ′ incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-weaken Δ≤Δ′ incl c⊢)
           (coercion-weaken Δ≤Δ′ incl d⊢)
coercion-weaken Δ≤Δ′ incl (cast-tag hG gG) =
  cast-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG
coercion-weaken Δ≤Δ′ incl (cast-untag hH gH) =
  cast-untag (WfTy-weakenᵗ hH Δ≤Δ′) gH
coercion-weaken Δ≤Δ′ incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-weaken Δ≤Δ′ incl c⊢)
           (coercion-weaken Δ≤Δ′ incl d⊢)
coercion-weaken Δ≤Δ′ incl (cast-all c⊢) =
  cast-all
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)
coercion-weaken Δ≤Δ′ incl (cast-inst hB c⊢) =
  cast-inst
    (WfTy-weakenᵗ hB Δ≤Δ′)
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
coercion-weaken Δ≤Δ′ incl (cast-gen hA c⊢) =
  cast-gen
    (WfTy-weakenᵗ hA Δ≤Δ′)
    (coercion-weaken
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)

coercion-weaken-suc :
  ∀ {Δ Σ c A B α C} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c ∶ A =⇒ B
coercion-weaken-suc {Δ = Δ} c⊢ =
  coercion-weaken (n≤1+n Δ) StoreIncl-drop c⊢

------------------------------------------------------------------------
-- Coercion typing under type renaming
------------------------------------------------------------------------

coercion-renameᵗ :
  ∀ {Δ Δ′ Σ c A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗ hρ (cast-id hA) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
coercion-renameᵗ hρ (cast-seal hA α∈Σ) =
  cast-seal (renameᵗ-preserves-WfTy hA hρ)
            (∈-renameStoreᵗ _ α∈Σ)
coercion-renameᵗ hρ (cast-unseal hA α∈Σ) =
  cast-unseal (renameᵗ-preserves-WfTy hA hρ)
              (∈-renameStoreᵗ _ α∈Σ)
coercion-renameᵗ hρ (cast-seq c⊢ d⊢) =
  cast-seq (coercion-renameᵗ hρ c⊢)
           (coercion-renameᵗ hρ d⊢)
coercion-renameᵗ hρ (cast-tag hG gG) =
  cast-tag (renameᵗ-preserves-WfTy hG hρ) (renameᵗ-ground _ gG)
coercion-renameᵗ hρ (cast-untag hH gH) =
  cast-untag (renameᵗ-preserves-WfTy hH hρ) (renameᵗ-ground _ gH)
coercion-renameᵗ hρ (cast-fun c⊢ d⊢) =
  cast-fun (coercion-renameᵗ hρ c⊢)
           (coercion-renameᵗ hρ d⊢)
coercion-renameᵗ {ρ = ρ} hρ
    (cast-all {A = A} {B = B} c⊢) =
  cast-all
    (subst
      (λ Σ′ → _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
      (renameStoreᵗ-ext-suc-comm ρ _)
      (coercion-renameᵗ (TyRenameWf-ext hρ) c⊢))
coercion-renameᵗ {ρ = ρ} hρ
    (cast-inst {B = B} hB c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    (subst
      (λ T → _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ → _ ∣ (0 , ★) ∷ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗ (TyRenameWf-ext hρ) c⊢)))
coercion-renameᵗ {ρ = ρ} hρ
    (cast-gen {A = A} hA c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    (subst
      (λ T → _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ T =⇒ _)
      (renameᵗ-ext-suc-comm ρ A)
      (subst
        (λ Σ′ → _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗ (TyRenameWf-ext hρ) c⊢)))

coercion-open :
  ∀ {Δ Σ c A B α C} →
  α < suc Δ →
  suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open {Σ = Σ} {α = α} α<sucΔ c⊢ =
  coercion-weaken ≤-refl StoreIncl-drop
    (subst
      (λ Σ′ → _ ∣ Σ′ ⊢ _ ∶ _ =⇒ _)
      (renameStoreᵗ-single-suc-cancel α Σ)
      (coercion-renameᵗ (singleRenameᵗ-Wf α<sucΔ) c⊢))

coercion-open-head :
  ∀ {Δ Σ c A B α C} →
  α < suc Δ →
  suc Δ ∣ (0 , C) ∷ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , renameᵗ (singleRenameᵗ α) C) ∷ Σ
    ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-head
    {Δ = Δ} {Σ = Σ} {c = c} {A = A} {B = B} {α = α} α<sucΔ c⊢ =
  subst
    (λ Σ′ → suc Δ ∣ Σ′ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ)
    (cong₂ _∷_ refl (renameStoreᵗ-single-suc-cancel α Σ))
    (coercion-renameᵗ (singleRenameᵗ-Wf α<sucΔ) c⊢)

------------------------------------------------------------------------
-- Coercion endpoint well-formedness
------------------------------------------------------------------------

coercion-wf :
  ∀ {Δ Σ c A B} →
  StoreWfAt Δ Σ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wf wfΣ (cast-id hA) = hA , hA
coercion-wf wfΣ (cast-seal hA α∈Σ) =
  hA , wfVar (bound wfΣ α∈Σ)
coercion-wf wfΣ (cast-unseal hA α∈Σ) =
  wfVar (bound wfΣ α∈Σ) , hA
coercion-wf wfΣ (cast-seq c⊢ d⊢)
    with coercion-wf wfΣ c⊢ | coercion-wf wfΣ d⊢
coercion-wf wfΣ (cast-seq c⊢ d⊢)
    | hA , hB | hB′ , hC =
  hA , hC
coercion-wf wfΣ (cast-tag hG gG) = hG , wf★
coercion-wf wfΣ (cast-untag hH gH) = wf★ , hH
coercion-wf wfΣ (cast-fun c⊢ d⊢)
    with coercion-wf wfΣ c⊢ | coercion-wf wfΣ d⊢
coercion-wf wfΣ (cast-fun c⊢ d⊢)
    | hA′ , hA | hB , hB′ =
  wf⇒ hA hB , wf⇒ hA′ hB′
coercion-wf wfΣ (cast-all c⊢)
    with coercion-wf (StoreWfAt-⟰ᵗ wfΣ) c⊢
coercion-wf wfΣ (cast-all c⊢) | hA , hB =
  wf∀ hA , wf∀ hB
coercion-wf wfΣ (cast-inst hB c⊢)
    with coercion-wf
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
      c⊢
coercion-wf wfΣ (cast-inst hB c⊢) | hA , hB′ =
  wf∀ hA , hB
coercion-wf wfΣ (cast-gen hA c⊢)
    with coercion-wf (StoreWfAt-⟰ᵗ wfΣ) c⊢
coercion-wf wfΣ (cast-gen hA c⊢) | hA′ , hB =
  hA , wf∀ hB

------------------------------------------------------------------------
-- Typing the reveal/conceal coercions generated after fresh allocation
------------------------------------------------------------------------

data RevealVar
    (α : TyVar) (C : Ty) (ρ : Renameᵗ) (σ : Substᵗ)
    (X : TyVar) : Set where
  rv-hit :
    ρ X ≡ α →
    σ X ≡ C →
    RevealVar α C ρ σ X

  rv-miss :
    ρ X ≢ α →
    σ X ≡ ＇ (ρ X) →
    RevealVar α C ρ σ X

RevealEnv : TyCtx → TyVar → Ty → Renameᵗ → Substᵗ → Set
RevealEnv Θ α C ρ σ = ∀ {X} → X < Θ → RevealVar α C ρ σ X

RevealEnv-ext :
  ∀ {Θ α C ρ σ} →
  RevealEnv Θ α C ρ σ →
  RevealEnv (suc Θ) (suc α) (⇑ᵗ C) (extᵗ ρ) (extsᵗ σ)
RevealEnv-ext env {X = zero} z<s =
  rv-miss (λ ()) refl
RevealEnv-ext env {X = suc X} (s<s X<Θ) with env X<Θ
RevealEnv-ext env {X = suc X} (s<s X<Θ)
    | rv-hit ρX≡α σX≡C =
  rv-hit (cong suc ρX≡α) (cong (renameᵗ suc) σX≡C)
RevealEnv-ext env {X = suc X} (s<s X<Θ)
    | rv-miss ρX≢α σX≡var =
  rv-miss
    (λ eq → ρX≢α (suc-injective eq))
    (cong (renameᵗ suc) σX≡var)

singleRevealEnv :
  ∀ {Δ C} →
  RevealEnv (suc Δ) Δ C (singleRenameᵗ Δ) (singleTyEnv C)
singleRevealEnv {Δ = Δ} {X = zero} z<s =
  rv-hit refl refl
singleRevealEnv {Δ = Δ} {X = suc X} (s<s X<Δ) =
  rv-miss X≢Δ refl
  where
    X≢Δ : X ≢ Δ
    X≢Δ X≡Δ =
      <-irrefl refl (subst (λ Y → Y < Δ) X≡Δ X<Δ)

reveal-var-hit :
  ∀ {Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  Δ ∣ Σ ⊢ reveal (＇ α) α C ∶ ＇ α =⇒ C
reveal-var-hit {α = α} hC α∈Σ with α ≟ α
reveal-var-hit {α = α} hC α∈Σ | yes refl =
  cast-unseal hC α∈Σ
reveal-var-hit {α = α} hC α∈Σ | no α≢α =
  ⊥-elim (α≢α refl)

conceal-var-hit :
  ∀ {Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  Δ ∣ Σ ⊢ conceal (＇ α) α C ∶ C =⇒ ＇ α
conceal-var-hit {α = α} hC α∈Σ with α ≟ α
conceal-var-hit {α = α} hC α∈Σ | yes refl =
  cast-seal hC α∈Σ
conceal-var-hit {α = α} hC α∈Σ | no α≢α =
  ⊥-elim (α≢α refl)

reveal-var-miss :
  ∀ {Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  Δ ∣ Σ ⊢ reveal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
reveal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY

conceal-var-miss :
  ∀ {Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  Δ ∣ Σ ⊢ conceal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
conceal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY

mutual
  reveal-typing-env :
    ∀ {Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    Δ ∣ Σ ⊢ reveal (renameᵗ ρ B) α C
      ∶ renameᵗ ρ B =⇒ substᵗ σ B
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      with env X<Θ
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    reveal-var-hit hC α∈Σ
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    reveal-var-miss ρX≢α (wfVar (hρ X<Θ))
  reveal-typing-env wfBase hρ hσ env hC α∈Σ =
    cast-id wfBase
  reveal-typing-env wf★ hρ hσ env hC α∈Σ =
    cast-id wf★
  reveal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ =
    cast-fun
      (conceal-typing-env hA hρ hσ env hC α∈Σ)
      (reveal-typing-env hB hρ hσ env hC α∈Σ)
  reveal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ =
    cast-all
      (reveal-typing-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ))

  conceal-typing-env :
    ∀ {Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    Δ ∣ Σ ⊢ conceal (renameᵗ ρ B) α C
      ∶ substᵗ σ B =⇒ renameᵗ ρ B
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      with env X<Θ
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    conceal-var-hit hC α∈Σ
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    conceal-var-miss ρX≢α (wfVar (hρ X<Θ))
  conceal-typing-env wfBase hρ hσ env hC α∈Σ =
    cast-id wfBase
  conceal-typing-env wf★ hρ hσ env hC α∈Σ =
    cast-id wf★
  conceal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ =
    cast-fun
      (reveal-typing-env hA hρ hσ env hC α∈Σ)
      (conceal-typing-env hB hρ hσ env hC α∈Σ)
  conceal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ =
    cast-all
      (conceal-typing-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ))

reveal-fresh-typing :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ reveal (B [ Δ ]ᴿ) Δ A
    ∶ B [ Δ ]ᴿ =⇒ B [ A ]ᵗ
reveal-fresh-typing {Δ = Δ} hA hB =
  reveal-typing-env
    hB
    (singleRenameᵗ-Wf (n<1+n Δ))
    singleTyEnv-Wf-suc
    singleRevealEnv
    (WfTy-weakenᵗ hA (n≤1+n Δ))
    (here refl)
  where
    singleTyEnv-Wf-suc :
      TySubstWf (suc Δ) (suc Δ) (singleTyEnv _)
    singleTyEnv-Wf-suc {zero} z<s =
      WfTy-weakenᵗ hA (n≤1+n Δ)
    singleTyEnv-Wf-suc {suc X} (s<s X<Δ) =
      wfVar (m<n⇒m<1+n X<Δ)

conceal-fresh-typing :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ conceal (B [ Δ ]ᴿ) Δ A
    ∶ B [ A ]ᵗ =⇒ B [ Δ ]ᴿ
conceal-fresh-typing {Δ = Δ} hA hB =
  conceal-typing-env
    hB
    (singleRenameᵗ-Wf (n<1+n Δ))
    singleTyEnv-Wf-suc
    singleRevealEnv
    (WfTy-weakenᵗ hA (n≤1+n Δ))
    (here refl)
  where
    singleTyEnv-Wf-suc :
      TySubstWf (suc Δ) (suc Δ) (singleTyEnv _)
    singleTyEnv-Wf-suc {zero} z<s =
      WfTy-weakenᵗ hA (n≤1+n Δ)
    singleTyEnv-Wf-suc {suc X} (s<s X<Δ) =
      wfVar (m<n⇒m<1+n X<Δ)

------------------------------------------------------------------------
-- Syntactic endpoints agree with typed endpoints
------------------------------------------------------------------------

coercion-src-tgt :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgt (cast-id hA) = refl , refl
coercion-src-tgt (cast-seal hA α∈Σ) = refl , refl
coercion-src-tgt (cast-unseal hA α∈Σ) = refl , refl
coercion-src-tgt (cast-seq c⊢ d⊢)
    with coercion-src-tgt c⊢ | coercion-src-tgt d⊢
coercion-src-tgt (cast-seq c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite src-c | tgt-d =
  refl , refl
coercion-src-tgt (cast-tag hG gG) = refl , refl
coercion-src-tgt (cast-untag hH gH) = refl , refl
coercion-src-tgt (cast-fun c⊢ d⊢)
    with coercion-src-tgt c⊢ | coercion-src-tgt d⊢
coercion-src-tgt (cast-fun c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite tgt-c | src-d | src-c | tgt-d =
  refl , refl
coercion-src-tgt (cast-all c⊢)
    with coercion-src-tgt c⊢
coercion-src-tgt (cast-all c⊢) | src-c , tgt-c rewrite src-c | tgt-c =
  refl , refl
coercion-src-tgt (cast-inst hB c⊢)
    with coercion-src-tgt c⊢
coercion-src-tgt (cast-inst hB c⊢) | src-c , tgt-c rewrite src-c =
  refl , refl
coercion-src-tgt (cast-gen hA c⊢)
    with coercion-src-tgt c⊢
coercion-src-tgt (cast-gen hA c⊢) | src-c , tgt-c rewrite tgt-c =
  refl , refl

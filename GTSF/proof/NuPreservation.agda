module proof.NuPreservation where

-- File Charter:
--   * Type preservation for the Nu GTSF store-change reduction.
--   * Proves one-step and multi-step preservation for closed `RuntimeOK`
--     terms, including the active runtime bullet introduced by `ν-step`.
--   * Also proves preservation of the runtime-bullet invariant and Nu store
--     well-formedness across emitted store changes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s; s≤s; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product as Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx
open import NuStore
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import proof.TypeProperties
open import proof.NuStoreProperties
open import proof.CoercionProperties
open import proof.NuTermProperties

------------------------------------------------------------------------
-- Small renaming equalities
------------------------------------------------------------------------

open0-ext-suc-cancel :
  ∀ A →
  renameᵗ (singleRenameᵗ zero) (renameᵗ (extᵗ suc) A) ≡ A
open0-ext-suc-cancel A =
  trans (renameᵗ-compose (extᵗ suc) (singleRenameᵗ zero) A)
        (trans (rename-cong env-eq A) (renameᵗ-id A))
  where
    env-eq :
      ∀ X →
      singleRenameᵗ zero (extᵗ suc X) ≡ X
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗ-left-inverse :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  ∀ A →
  renameᵗ ψ (renameᵗ ρ A) ≡ A
renameᵗ-left-inverse {ρ = ρ} {ψ = ψ} inv A =
  trans (renameᵗ-compose ρ ψ A)
        (trans (rename-cong inv A) (renameᵗ-id A))

open0-ext-suc-inv :
  RenameLeftInverse (extᵗ suc) (singleRenameᵗ zero)
open0-ext-suc-inv zero = refl
open0-ext-suc-inv (suc X) = refl

renameᶜ-left-inverse :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  ∀ c →
  renameᶜ ψ (renameᶜ ρ c) ≡ c
renameᶜ-left-inverse inv (id A) =
  cong id (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (p ︔ q) =
  cong₂ _︔_ (renameᶜ-left-inverse inv p)
             (renameᶜ-left-inverse inv q)
renameᶜ-left-inverse inv (A !) =
  cong _! (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (A ？) =
  cong _？ (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (unseal α A) =
  cong₂ unseal (inv α) (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (seal A α) =
  cong₂ seal (renameᵗ-left-inverse inv A) (inv α)
renameᶜ-left-inverse inv (p ↦ q) =
  cong₂ _↦_ (renameᶜ-left-inverse inv p)
             (renameᶜ-left-inverse inv q)
renameᶜ-left-inverse inv (`∀ p) =
  cong `∀ (renameᶜ-left-inverse (RenameLeftInverse-ext inv) p)
renameᶜ-left-inverse inv (gen A p) =
  cong₂ gen (renameᵗ-left-inverse inv A)
             (renameᶜ-left-inverse (RenameLeftInverse-ext inv) p)
renameᶜ-left-inverse inv (inst B p) =
  cong₂ inst (renameᵗ-left-inverse inv B)
              (renameᶜ-left-inverse (RenameLeftInverse-ext inv) p)

renameᵗᵐ-left-inverse :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  ∀ M →
  renameᵗᵐ ψ (renameᵗᵐ ρ M) ≡ M
renameᵗᵐ-left-inverse inv (` x) = refl
renameᵗᵐ-left-inverse inv (ƛ M) =
  cong ƛ_ (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (L · M) =
  cong₂ _·_ (renameᵗᵐ-left-inverse inv L)
             (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (Λ M) =
  cong Λ_ (renameᵗᵐ-left-inverse (RenameLeftInverse-ext inv) M)
renameᵗᵐ-left-inverse inv (M •) =
  cong _• (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (ν A L c) =
  trans
    (cong₂ (λ A′ L′ →
       ν A′ L′ (renameᶜ _ (renameᶜ _ c)))
      (renameᵗ-left-inverse inv A)
      (renameᵗᵐ-left-inverse inv L))
    (cong (ν A L) (renameᶜ-left-inverse (RenameLeftInverse-ext inv) c))
renameᵗᵐ-left-inverse inv ($ κ) = refl
renameᵗᵐ-left-inverse inv (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
        (renameᵗᵐ-left-inverse inv L)
        (renameᵗᵐ-left-inverse inv M)
renameᵗᵐ-left-inverse inv (M ⟨ c ⟩) =
  cong₂ _⟨_⟩ (renameᵗᵐ-left-inverse inv M)
              (renameᶜ-left-inverse inv c)
renameᵗᵐ-left-inverse inv blame = refl

open0-ext-suc-cancelᵐ :
  ∀ M →
  renameᵗᵐ (singleRenameᵗ zero) (renameᵗᵐ (extᵗ suc) M) ≡ M
open0-ext-suc-cancelᵐ = renameᵗᵐ-left-inverse open0-ext-suc-inv

open0-ext-suc-cancelᶜ :
  ∀ c →
  renameᶜ (singleRenameᵗ zero) (renameᶜ (extᵗ suc) c) ≡ c
open0-ext-suc-cancelᶜ = renameᶜ-left-inverse open0-ext-suc-inv

------------------------------------------------------------------------
-- Typing under an emitted store change
------------------------------------------------------------------------

closedCtxWf : ∀ {Δ} → CtxWf Δ []
closedCtxWf ()

applyTerm-typing :
  ∀ {χ : StoreChange}{Δ Σ M A} →
  StoreWfAt Δ Σ →
  No• M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ applyTerm χ M ⦂ applyTy χ A
applyTerm-typing {χ = keep} wfΣ noM M⊢ = M⊢
applyTerm-typing {χ = bind Aν} {Δ = Δ} wfΣ noM M⊢ =
  term-weaken ≤-refl StoreIncl-drop
    (renameᵗᵐ-preserves-No• suc noM)
    (typing-renameᵀ
      {ρ = suc} {ψ = predᵗ}
      TyRenameWf-suc
      RenameLeftInverse-suc
      noM
      M⊢)

⊢·-applyTy :
  ∀ χ {Δ Σ L M A B} →
  Δ ∣ Σ ∣ [] ⊢ L ⦂ applyTy χ (A ⇒ B) →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ applyTy χ A →
  Δ ∣ Σ ∣ [] ⊢ L · M ⦂ applyTy χ B
⊢·-applyTy keep hL hM = ⊢· hL hM
⊢·-applyTy (bind Aχ) hL hM = ⊢· hL hM

⊢⊕-applyTy :
  ∀ χ {Δ Σ L M} →
  Δ ∣ Σ ∣ [] ⊢ L ⦂ applyTy χ (‵ `ℕ) →
  (op : Prim) →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ applyTy χ (‵ `ℕ) →
  Δ ∣ Σ ∣ [] ⊢ L ⊕[ op ] M ⦂ applyTy χ (‵ `ℕ)
⊢⊕-applyTy keep hL op hM = ⊢⊕ hL op hM
⊢⊕-applyTy (bind Aχ) hL op hM = ⊢⊕ hL op hM

applyTyUnderTyBinder : StoreChange → Ty → Ty
applyTyUnderTyBinder keep A = A
applyTyUnderTyBinder (bind B) A = renameᵗ (extᵗ suc) A

⊢ν-applyTy :
  ∀ χ {Δ Σ A B C L c μ} →
  WfTy (applyTyCtx χ Δ) (applyTy χ A) →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ L ⦂ applyTy χ (`∀ C) →
  μ ∣ suc (applyTyCtx χ Δ)
    ∣ (zero , ⇑ᵗ (applyTy χ A)) ∷ ⟰ᵗ (applyStore χ Σ)
    ⊢ c ∶ applyTyUnderTyBinder χ C =⇒ ⇑ᵗ (applyTy χ B) →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ []
    ⊢ ν (applyTy χ A) L c ⦂ applyTy χ B
⊢ν-applyTy keep hA hL c⊢ = ⊢ν hA hL c⊢
⊢ν-applyTy (bind Aχ) hA hL c⊢ = ⊢ν hA hL c⊢

applyCoercion-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c A B} →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Product.Σ ModeEnv
    (λ ν →
      ν ∣ applyTyCtx χ Δ ∣ applyStore χ Σ
        ⊢ applyCoercion χ c ∶ applyTy χ A =⇒ applyTy χ B)
applyCoercion-typing {χ = keep} {μ = μ} wfΣ c⊢ = μ , c⊢
applyCoercion-typing {χ = bind Aν} {μ = μ} wfΣ c⊢ =
  (λ Y → μ (predᵗ Y)) ,
    coercion-weakenᵐ ≤-refl StoreIncl-drop
      (coercion-renameᵗᵐ
        TyRenameWf-suc
        (modeRename-left-inverse
          {ρ = suc} {ψ = predᵗ}
          RenameLeftInverse-suc)
        c⊢)

applyCoercionUnderTyBinder-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c B C Aν} →
  StoreWfAt Δ Σ →
  WfTy Δ Aν →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
  Product.Σ ModeEnv
    (λ ν →
      ν ∣ suc (applyTyCtx χ Δ)
        ∣ (zero , ⇑ᵗ (applyTy χ Aν)) ∷ ⟰ᵗ (applyStore χ Σ)
        ⊢ applyCoercionUnderTyBinder χ c
        ∶ applyTyUnderTyBinder χ C =⇒ ⇑ᵗ (applyTy χ B))
applyCoercionUnderTyBinder-typing {χ = keep} {μ = μ} wfΣ hA c⊢ =
  μ , c⊢
applyCoercionUnderTyBinder-typing {χ = bind Aχ} {μ = μ}
    {Δ = Δ} {Σ = Σ}
    {c = c} {B = Bout} {C = C} {Aν = Aν} wfΣ hA c⊢ =
  νmode ,
    subst
      (λ T →
        νmode ∣ suc (suc Δ)
          ∣ (zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ)
          ⊢ renameᶜ (extᵗ suc) c ∶ renameᵗ (extᵗ suc) C =⇒ T)
      (renameᵗ-ext-suc-comm suc Bout)
      (coercion-weakenᵐ
        ≤-refl
        incl
        renamed-store)
  where
    νmode : ModeEnv
    νmode Y = μ (extᵗ predᵗ Y)

    renamed-store :
      νmode ∣ suc (suc Δ)
        ∣ (zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ (⟰ᵗ Σ)
        ⊢ renameᶜ (extᵗ suc) c
        ∶ renameᵗ (extᵗ suc) C =⇒ renameᵗ (extᵗ suc) (⇑ᵗ Bout)
    renamed-store =
      subst
        (λ Σ′ →
          νmode ∣ suc (suc Δ) ∣ Σ′
            ⊢ renameᶜ (extᵗ suc) c
            ∶ renameᵗ (extᵗ suc) C =⇒ renameᵗ (extᵗ suc) (⇑ᵗ Bout))
        (renameStoreᵗ-ext-suc-cons-comm suc Σ Aν)
        (coercion-renameᵗᵐ
          (TyRenameWf-ext TyRenameWf-suc)
          (modeRename-left-inverse
            {ρ = extᵗ suc} {ψ = extᵗ predᵗ}
            (RenameLeftInverse-ext RenameLeftInverse-suc))
          c⊢)

    incl :
      StoreIncl
        ((zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ (⟰ᵗ Σ))
        ((zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ))
    incl (here refl) = here refl
    incl (there h) = there (there h)

typing-wf-∀-body :
  ∀ {Δ Σ V C} →
  StoreWfAt Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ `∀ C →
  WfTy (suc Δ) C
typing-wf-∀-body wfΣ V⊢ with typing-wf wfΣ closedCtxWf V⊢
typing-wf-∀-body wfΣ V⊢ | wf∀ hC = hC

StoreWfAt-tail :
  ∀ {Δ α A Σ} →
  StoreWfAt Δ ((α , A) ∷ Σ) →
  StoreWfAt Δ Σ
StoreWfAt-tail wfΣ =
  record
    { bound = λ x∈ → bound wfΣ (there x∈)
    ; wfTy = λ x∈ → wfTy wfΣ (there x∈)
    }

ν-step-typing :
  ∀ {Δ : TyCtx}{Σ : Store}{A B C : Ty}{V : Term}
    {c : Coercion}{μ : ModeEnv} →
  StoreWfAt Δ Σ →
  WfTy Δ A →
  No• V →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ `∀ C →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
  suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ∣ []
    ⊢ ((⇑ᵗᵐ V) •) ⟨ c ⟩ ⦂ ⇑ᵗ B
ν-step-typing {C = C} wfΣ hA noV vV V⊢ c⊢ =
  ⊢⟨⟩ c⊢ bullet⊢
  where
    bullet⊢ :
      _ ∣ _ ∣ [] ⊢ (⇑ᵗᵐ _) • ⦂ C
    bullet⊢ =
      ⊢• refl refl
        (typing-wf-∀-body wfΣ V⊢)
        vV
        noV
        V⊢

------------------------------------------------------------------------
-- Raw redex preservation for bullet-free source redexes
------------------------------------------------------------------------

pure-preservation :
  ∀ {Δ Σ M N A} →
  StoreWf Δ Σ →
  No• M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Σ ∣ [] ⊢ N ⦂ A
pure-preservation wfΣ (no•-⊕ noL noM)
    (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n)))
    δ-⊕ =
  ⊢$ _
pure-preservation wfΣ (no•-· (no•-ƛ noN) noV)
    (⊢· (⊢ƛ hA hN) hV) (β vV) =
  typing-single-subst noN noV hN hV
pure-preservation wfΣ () M⊢ (β-Λ• vV′)
pure-preservation wfΣ () M⊢ (β-∀• vV′)
pure-preservation wfΣ () M⊢ (β-gen• vV′)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩ (cast-id hA _) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩ (cast-seq p⊢ q⊢) hV) (β-seq vV) =
  ⊢⟨⟩ q⊢ (⊢⟨⟩ p⊢ hV)
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩ (cast-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩ q⊢ (⊢· hV (⊢⟨⟩ p⊢ hW))
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩ {M = V}
      (cast-inst {A = A} {B = B} {s = c} hB occ c⊢) V⊢)
    (β-inst vV) =
  ⊢ν wf★ V⊢ c⊢
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩ (cast-unseal hB αB∈Σ _)
      (⊢⟨⟩ (cast-seal hA αA∈Σ _) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩ (cast-untag hG gG _) (⊢⟨⟩ (cast-tag hG′ gG′ _) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩ (cast-untag hH gH _) (⊢⟨⟩ (cast-tag hG gG _) hV))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH
pure-preservation wfΣ (no•-· noB noM)
    (⊢· (⊢blame (wf⇒ hA hB)) hM) blame-·₁ =
  ⊢blame hB
pure-preservation wfΣ (no•-· noV noB)
    (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    with typing-wf (at wfΣ) closedCtxWf hV
pure-preservation wfΣ (no•-· noV noB)
    (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    | wf⇒ hA′ hB =
  ⊢blame hB
pure-preservation wfΣ () M⊢ blame-•
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wfᵐ (at wfΣ) c⊢
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ (no•-⊕ noB noM)
    (⊢⊕ (⊢blame hA) op hM) blame-⊕₁ =
  ⊢blame wfBase
pure-preservation wfΣ (no•-⊕ noL noB)
    (⊢⊕ hL op (⊢blame hA)) (blame-⊕₂ vL) =
  ⊢blame wfBase

pure-preserves-No•-typed :
  ∀ {Δ Σ M N A} →
  StoreWf Δ Σ →
  No• M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→ N →
  No• N
pure-preserves-No•-typed wfΣ (no•-⊕ noL noM)
    (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n)))
    δ-⊕ =
  no•-$
pure-preserves-No•-typed wfΣ (no•-· (no•-ƛ noN) noV)
    (⊢· (⊢ƛ hA hN) hV) (β vV) =
  substˣᵐ-preserves-No•-typed (singleSubstNo• noV) noN hN
pure-preserves-No•-typed wfΣ () M⊢ (β-Λ• vV)
pure-preserves-No•-typed wfΣ () M⊢ (β-∀• vV)
pure-preserves-No•-typed wfΣ () M⊢ (β-gen• vV)
pure-preserves-No•-typed wfΣ (no•-⟨⟩ noV) M⊢ (β-id vV) =
  noV
pure-preserves-No•-typed wfΣ (no•-⟨⟩ noV) M⊢ (β-seq vV) =
  no•-⟨⟩ (no•-⟨⟩ noV)
pure-preserves-No•-typed wfΣ (no•-· (no•-⟨⟩ noV) noW)
    M⊢ (β-↦ vV vW) =
  no•-⟨⟩ (no•-· noV (no•-⟨⟩ noW))
pure-preserves-No•-typed wfΣ (no•-⟨⟩ noV) M⊢ (β-inst vV) =
  no•-ν noV
pure-preserves-No•-typed wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    M⊢ (tag-untag-ok vV) =
  noV
pure-preserves-No•-typed wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    M⊢ (tag-untag-bad vV G≢H) =
  no•-blame
pure-preserves-No•-typed wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    M⊢ (seal-unseal vV) =
  noV
pure-preserves-No•-typed wfΣ (no•-· noB noM) M⊢ blame-·₁ =
  no•-blame
pure-preserves-No•-typed wfΣ (no•-· noV noB) M⊢
    (blame-·₂ vV) =
  no•-blame
pure-preserves-No•-typed wfΣ () M⊢ blame-•
pure-preserves-No•-typed wfΣ (no•-⟨⟩ noB) M⊢ blame-⟨⟩ =
  no•-blame
pure-preserves-No•-typed wfΣ (no•-⊕ noB noM) M⊢ blame-⊕₁ =
  no•-blame
pure-preserves-No•-typed wfΣ (no•-⊕ noL noB) M⊢
    (blame-⊕₂ vL) =
  no•-blame

pure-preservation-runtime :
  ∀ {Δ Σ M N A} →
  StoreWf Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  RuntimeOK M →
  M —→ N →
  Δ ∣ Σ ∣ [] ⊢ N ⦂ A

bullet-pure-preservation :
  ∀ {Δ Σ Aν V C N} →
  StoreWf (suc Δ) ((zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ) →
  WfTy (suc Δ) C →
  Value V →
  No• V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ `∀ C →
  ((⇑ᵗᵐ V) •) —→ N →
  suc Δ ∣ (zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ ∣ [] ⊢ N ⦂ C
bullet-pure-preservation wfΣ hC (ƛ N) noV () red
bullet-pure-preservation {C = C} wfΣ hC
    (Λ vW) (no•-Λ noW) (⊢Λ vW′ W⊢) (β-Λ• vW↑) =
  subst
    (λ T → _ ∣ _ ∣ [] ⊢ T ⦂ C)
    (sym (open0-ext-suc-cancelᵐ _))
    (term-weaken ≤-refl StoreIncl-drop noW W⊢)
bullet-pure-preservation wfΣ hC ($ (κℕ n)) noV () red
bullet-pure-preservation wfΣ hC (vW ⟨ G ! ⟩) noV (⊢⟨⟩ () W⊢) red
bullet-pure-preservation wfΣ hC (vW ⟨ seal A α ⟩) noV
    (⊢⟨⟩ () W⊢) red
bullet-pure-preservation wfΣ hC (vW ⟨ c ↦ d ⟩) noV
    (⊢⟨⟩ () W⊢) red
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩ (cast-all c⊢) W⊢) (β-∀• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ ((⇑ᵗᵐ W) •) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩
      (coercion-weakenᵐ ≤-refl StoreIncl-drop c⊢)
      (⊢• refl refl hA vW noW W⊢))
  where
    hA : WfTy _ _
    hA with coercion-wfᵐ (StoreWfAt-tail (at wfΣ)) c⊢
    hA | hA′ , hC′ = hA′
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩ (cast-gen hA occ c⊢) W⊢) (β-gen• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ (⇑ᵗᵐ W) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩
      (coercion-weakenᵐ ≤-refl StoreIncl-drop c⊢)
      (term-weaken ≤-refl StoreIncl-drop
        (renameᵗᵐ-preserves-No• suc noW)
        (typing-renameᵀ {ρ = suc} {ψ = predᵗ}
          TyRenameWf-suc RenameLeftInverse-suc noW W⊢)))

bullet-runtime-preservation :
  ∀ {Δ Σ Aν V C N} →
  StoreWf (suc Δ) ((zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ) →
  WfTy (suc Δ) C →
  Value V →
  No• V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ `∀ C →
  ((⇑ᵗᵐ V) •) —→ N →
  RuntimeOK N
bullet-runtime-preservation wfΣ hC (ƛ N) noV () red
bullet-runtime-preservation wfΣ hC
    (Λ vW) (no•-Λ noW) (⊢Λ vW′ W⊢) (β-Λ• vW↑) =
  subst RuntimeOK (sym (open0-ext-suc-cancelᵐ _)) (ok-no noW)
bullet-runtime-preservation wfΣ hC ($ (κℕ n)) noV () red
bullet-runtime-preservation wfΣ hC (vW ⟨ G ! ⟩) noV
    (⊢⟨⟩ () W⊢) red
bullet-runtime-preservation wfΣ hC (vW ⟨ seal A α ⟩) noV
    (⊢⟨⟩ () W⊢) red
bullet-runtime-preservation wfΣ hC (vW ⟨ c ↦ d ⟩) noV
    (⊢⟨⟩ () W⊢) red
bullet-runtime-preservation wfΣ hC
    (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩ (cast-all c⊢) W⊢) (β-∀• vW↑) =
  ok-⟨⟩ (ok-• vW noW)
bullet-runtime-preservation wfΣ hC
    (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩ (cast-gen hA occ c⊢) W⊢) (β-gen• vW↑) =
  ok-no (no•-⟨⟩ (renameᵗᵐ-preserves-No• suc noW))

value-runtime-No• :
  ∀ {V} →
  Value V →
  RuntimeOK V →
  No• V
value-runtime-No• vV (ok-no noV) = noV
value-runtime-No• (vV ⟨ i ⟩) (ok-⟨⟩ okV) =
  no•-⟨⟩ (value-runtime-No• vV okV)

pure-runtime-preservation :
  ∀ {Δ Σ M N A} →
  StoreWf Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  RuntimeOK M →
  M —→ N →
  RuntimeOK N
pure-runtime-preservation wfΣ
    (⊢• refl refl hC vV noV V⊢) okM red =
  bullet-runtime-preservation wfΣ hC vV noV V⊢ red
pure-runtime-preservation wfΣ M⊢ (ok-no noM) red =
  ok-no (pure-preserves-No•-typed wfΣ noM M⊢ red)
pure-runtime-preservation wfΣ M⊢ (ok-·₁ okL noM) (β vV) =
  ok-no
    (pure-preserves-No•-typed wfΣ
      (no•-· (value-runtime-No• (ƛ _) okL) noM) M⊢ (β vV))
pure-runtime-preservation wfΣ M⊢ (ok-·₁ okL noM)
    (β-↦ vV vW) =
  ok-no
    (pure-preserves-No•-typed wfΣ
      (no•-· (value-runtime-No• (vV ⟨ _ ↦ _ ⟩) okL) noM)
      M⊢
      (β-↦ vV vW))
pure-runtime-preservation wfΣ M⊢ (ok-·₁ okL noM) blame-·₁ =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-· no•-blame noM) M⊢ blame-·₁)
pure-runtime-preservation wfΣ M⊢ (ok-·₁ okL noM)
    (blame-·₂ vV) =
  ok-no
    (pure-preserves-No•-typed wfΣ
      (no•-· (value-runtime-No• vV okL) noM) M⊢ (blame-·₂ vV))
pure-runtime-preservation wfΣ M⊢ (ok-·₂ vV noV okM) (β vW) =
  ok-no
    (pure-preserves-No•-typed wfΣ
      (no•-· noV (value-runtime-No• vW okM)) M⊢ (β vW))
pure-runtime-preservation wfΣ M⊢ (ok-·₂ vV noV okM)
    (β-↦ vV′ vW) =
  ok-no
    (pure-preserves-No•-typed wfΣ
      (no•-· noV (value-runtime-No• vW okM)) M⊢ (β-↦ vV′ vW))
pure-runtime-preservation wfΣ M⊢ (ok-·₂ vV noV okM)
    (blame-·₂ vV′) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-· noV no•-blame) M⊢ (blame-·₂ vV′))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM) (β-id vV) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ (value-runtime-No• vV okM)) M⊢ (β-id vV))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM) (β-seq vV) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ (value-runtime-No• vV okM)) M⊢ (β-seq vV))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM) (β-inst vV) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ (value-runtime-No• vV okM)) M⊢ (β-inst vV))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM) (seal-unseal vV) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ (value-runtime-No• (vV ⟨ seal _ _ ⟩) okM))
    M⊢
    (seal-unseal vV))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM) (tag-untag-ok vV) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ (value-runtime-No• (vV ⟨ _ ! ⟩) okM))
    M⊢
    (tag-untag-ok vV))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM)
    (tag-untag-bad vV G≢H) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ (value-runtime-No• (vV ⟨ _ ! ⟩) okM))
    M⊢
    (tag-untag-bad vV G≢H))
pure-runtime-preservation wfΣ M⊢ (ok-⟨⟩ okM) blame-⟨⟩ =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⟨⟩ no•-blame) M⊢ blame-⟨⟩)
pure-runtime-preservation wfΣ M⊢ (ok-⊕₁ okL noM) δ-⊕ =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⊕ (value-runtime-No• ($ _) okL) noM) M⊢ δ-⊕)
pure-runtime-preservation wfΣ M⊢ (ok-⊕₁ okL noM) blame-⊕₁ =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⊕ no•-blame noM) M⊢ blame-⊕₁)
pure-runtime-preservation wfΣ M⊢ (ok-⊕₁ okL noM)
    (blame-⊕₂ vL) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⊕ (value-runtime-No• vL okL) noM) M⊢ (blame-⊕₂ vL))
pure-runtime-preservation wfΣ M⊢ (ok-⊕₂ vL noL okM) δ-⊕ =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⊕ noL (value-runtime-No• ($ _) okM)) M⊢ δ-⊕)
pure-runtime-preservation wfΣ M⊢ (ok-⊕₂ vL noL okM)
    (blame-⊕₂ vL′) =
  ok-no (pure-preserves-No•-typed wfΣ
    (no•-⊕ noL no•-blame) M⊢ (blame-⊕₂ vL′))

pure-preservation-runtime wfΣ
    (⊢• refl refl hC vV noV V⊢) okM red =
  bullet-pure-preservation wfΣ hC vV noV V⊢ red
pure-preservation-runtime wfΣ M⊢ (ok-no noM) red =
  pure-preservation wfΣ noM M⊢ red
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM) (β vV) =
  pure-preservation wfΣ
    (no•-· (value-runtime-No• (ƛ _) okL) noM) M⊢ (β vV)
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM)
    (β-↦ vV vW) =
  pure-preservation wfΣ
    (no•-· (value-runtime-No• (vV ⟨ _ ↦ _ ⟩) okL) noM)
    M⊢
    (β-↦ vV vW)
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM) blame-·₁ =
  pure-preservation wfΣ (no•-· no•-blame noM) M⊢ blame-·₁
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM)
    (blame-·₂ vV) =
  pure-preservation wfΣ
    (no•-· (value-runtime-No• vV okL) noM) M⊢ (blame-·₂ vV)
pure-preservation-runtime wfΣ M⊢ (ok-·₂ vV noV okM) (β vW) =
  pure-preservation wfΣ
    (no•-· noV (value-runtime-No• vW okM)) M⊢ (β vW)
pure-preservation-runtime wfΣ M⊢ (ok-·₂ vV noV okM)
    (β-↦ vV′ vW) =
  pure-preservation wfΣ
    (no•-· noV (value-runtime-No• vW okM)) M⊢ (β-↦ vV′ vW)
pure-preservation-runtime wfΣ M⊢ (ok-·₂ vV noV okM)
    (blame-·₂ vV′) =
  pure-preservation wfΣ (no•-· noV no•-blame) M⊢ (blame-·₂ vV′)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (β-id vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (value-runtime-No• vV okM)) M⊢ (β-id vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (β-seq vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (value-runtime-No• vV okM)) M⊢ (β-seq vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (β-inst vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (value-runtime-No• vV okM)) M⊢ (β-inst vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (seal-unseal vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (value-runtime-No• (vV ⟨ seal _ _ ⟩) okM))
    M⊢
    (seal-unseal vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (tag-untag-ok vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (value-runtime-No• (vV ⟨ _ ! ⟩) okM))
    M⊢
    (tag-untag-ok vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM)
    (tag-untag-bad vV G≢H) =
  pure-preservation wfΣ
    (no•-⟨⟩ (value-runtime-No• (vV ⟨ _ ! ⟩) okM))
    M⊢
    (tag-untag-bad vV G≢H)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) blame-⟨⟩ =
  pure-preservation wfΣ (no•-⟨⟩ no•-blame) M⊢ blame-⟨⟩
pure-preservation-runtime wfΣ M⊢ (ok-⊕₁ okL noM) δ-⊕ =
  pure-preservation wfΣ
    (no•-⊕ (value-runtime-No• ($ _) okL) noM) M⊢ δ-⊕
pure-preservation-runtime wfΣ M⊢ (ok-⊕₁ okL noM) blame-⊕₁ =
  pure-preservation wfΣ (no•-⊕ no•-blame noM) M⊢ blame-⊕₁
pure-preservation-runtime wfΣ M⊢ (ok-⊕₁ okL noM)
    (blame-⊕₂ vL) =
  pure-preservation wfΣ
    (no•-⊕ (value-runtime-No• vL okL) noM) M⊢ (blame-⊕₂ vL)
pure-preservation-runtime wfΣ M⊢ (ok-⊕₂ vL noL okM) δ-⊕ =
  pure-preservation wfΣ
    (no•-⊕ noL (value-runtime-No• ($ _) okM)) M⊢ δ-⊕
pure-preservation-runtime wfΣ M⊢ (ok-⊕₂ vL noL okM)
    (blame-⊕₂ vL′) =
  pure-preservation wfΣ (no•-⊕ noL no•-blame) M⊢ (blame-⊕₂ vL′)

applyTerm-typing-shiftable :
  ∀ {χ : StoreChange}{Δ Σ M A} →
  StoreWfAt Δ Σ →
  Shiftable χ M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ applyTerm χ M ⦂ applyTy χ A
applyTerm-typing-shiftable wfΣ shift-keep M⊢ = M⊢
applyTerm-typing-shiftable wfΣ (shift-bind noM) M⊢ =
  applyTerm-typing wfΣ noM M⊢

runtime-·₁ :
  ∀ {L M} →
  RuntimeOK (L · M) →
  RuntimeOK L
runtime-·₁ (ok-no (no•-· noL noM)) = ok-no noL
runtime-·₁ (ok-·₁ okL noM) = okL
runtime-·₁ (ok-·₂ vL noL okM) = ok-no noL

runtime-·₂ :
  ∀ {L M} →
  Value L →
  RuntimeOK (L · M) →
  RuntimeOK M
runtime-·₂ vL (ok-no (no•-· noL noM)) = ok-no noM
runtime-·₂ vL (ok-·₁ okL noM) = ok-no noM
runtime-·₂ vL (ok-·₂ vL′ noL okM) = okM

runtime-⟨⟩ :
  ∀ {M c} →
  RuntimeOK (M ⟨ c ⟩) →
  RuntimeOK M
runtime-⟨⟩ (ok-no (no•-⟨⟩ noM)) = ok-no noM
runtime-⟨⟩ (ok-⟨⟩ okM) = okM

runtime-ν :
  ∀ {A L c} →
  RuntimeOK (ν A L c) →
  RuntimeOK L
runtime-ν (ok-no (no•-ν noL)) = ok-no noL
runtime-ν (ok-ν okL) = okL

runtime-⊕₁ :
  ∀ {L op M} →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK L
runtime-⊕₁ (ok-no (no•-⊕ noL noM)) = ok-no noL
runtime-⊕₁ (ok-⊕₁ okL noM) = okL
runtime-⊕₁ (ok-⊕₂ vL noL okM) = ok-no noL

runtime-⊕₂ :
  ∀ {L op M} →
  Value L →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK M
runtime-⊕₂ vL (ok-no (no•-⊕ noL noM)) = ok-no noM
runtime-⊕₂ vL (ok-⊕₁ okL noM) = ok-no noM
runtime-⊕₂ vL (ok-⊕₂ vL′ noL okM) = okM

applyTerm-preserves-No• :
  ∀ {χ M} →
  No• M →
  Shiftable χ M →
  No• (applyTerm χ M)
applyTerm-preserves-No• noM shift-keep = noM
applyTerm-preserves-No• noM (shift-bind noM′) =
  renameᵗᵐ-preserves-No• suc noM′

applyTerm-preserves-Value :
  ∀ {χ V} →
  Shiftable χ V →
  Value V →
  Value (applyTerm χ V)
applyTerm-preserves-Value shift-keep vV = vV
applyTerm-preserves-Value (shift-bind noV) vV =
  renameᵗᵐ-preserves-Value suc vV

value-no-pure-step :
  ∀ {V N} →
  Value V →
  V —→ N →
  ⊥
value-no-pure-step (ƛ N) ()
value-no-pure-step (Λ vV) ()
value-no-pure-step ($ κ) ()
value-no-pure-step (() ⟨ G ! ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ seal A α ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ c ↦ d ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ `∀ c ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ gen A c ⟩) blame-⟨⟩

value-no-step :
  ∀ {χ V N} →
  Value V →
  V —→[ χ ] N →
  ⊥
value-no-step vV (pure-step red) =
  value-no-pure-step vV red
value-no-step (vV ⟨ i ⟩) (ξ-⟨⟩ red) =
  value-no-step vV red

runtime-preservation :
  ∀ {Δ Σ M N A χ} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  RuntimeOK N
runtime-preservation wfΣ okM M⊢ (pure-step red) =
  pure-runtime-preservation wfΣ M⊢ okM red
runtime-preservation wfΣ okM (⊢ν hA V⊢ c⊢)
    (ν-step vV noV) =
  ok-⟨⟩ (ok-• vV noV)
runtime-preservation wfΣ (ok-no (no•-· noL noM)) (⊢· L⊢ M⊢)
    (ξ-·₁ red shiftM) =
  ok-·₁
    (runtime-preservation wfΣ (ok-no noL) L⊢ red)
    (applyTerm-preserves-No• noM shiftM)
runtime-preservation wfΣ (ok-·₁ okL noM) (⊢· L⊢ M⊢)
    (ξ-·₁ red shiftM) =
  ok-·₁
    (runtime-preservation wfΣ okL L⊢ red)
    (applyTerm-preserves-No• noM shiftM)
runtime-preservation wfΣ (ok-·₂ vL noL okM) (⊢· L⊢ M⊢)
    (ξ-·₁ red shiftM) =
  ⊥-elim (value-no-step vL red)
runtime-preservation wfΣ okM (⊢· V⊢ M⊢)
    (ξ-·₂ vV shiftV red) =
  ok-·₂
    (applyTerm-preserves-Value shiftV vV)
    (applyTerm-preserves-No•
      (value-runtime-No• vV (runtime-·₁ okM))
      shiftV)
    (runtime-preservation wfΣ (runtime-·₂ vV okM) M⊢ red)
runtime-preservation wfΣ okM (⊢⟨⟩ c⊢ M⊢)
    (ξ-⟨⟩ red) =
  ok-⟨⟩ (runtime-preservation wfΣ (runtime-⟨⟩ okM) M⊢ red)
runtime-preservation wfΣ okM (⊢ν hA L⊢ c⊢)
    (ξ-ν red) =
  ok-ν (runtime-preservation wfΣ (runtime-ν okM) L⊢ red)
runtime-preservation wfΣ okM (⊢ν hA (⊢blame hB) c⊢) blame-ν =
  ok-no no•-blame
runtime-preservation wfΣ (ok-no (no•-⊕ noL noM)) (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₁ red shiftM) =
  ok-⊕₁
    (runtime-preservation wfΣ (ok-no noL) L⊢ red)
    (applyTerm-preserves-No• noM shiftM)
runtime-preservation wfΣ (ok-⊕₁ okL noM) (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₁ red shiftM) =
  ok-⊕₁
    (runtime-preservation wfΣ okL L⊢ red)
    (applyTerm-preserves-No• noM shiftM)
runtime-preservation wfΣ (ok-⊕₂ vL noL okM) (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₁ red shiftM) =
  ⊥-elim (value-no-step vL red)
runtime-preservation wfΣ okM (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₂ vL shiftL red) =
  ok-⊕₂
    (applyTerm-preserves-Value shiftL vL)
    (applyTerm-preserves-No•
      (value-runtime-No• vL (runtime-⊕₁ okM))
      shiftL)
    (runtime-preservation wfΣ (runtime-⊕₂ vL okM) M⊢ red)

store-preservation :
  ∀ {Δ Σ M N A χ} →
  StoreWf Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  StoreWf (applyTyCtx χ Δ) (applyStore χ Σ)
store-preservation wfΣ M⊢ (pure-step red) = wfΣ
store-preservation wfΣ (⊢ν hA V⊢ c⊢) (ν-step vV noV) =
  StoreWf-bind wfΣ hA
store-preservation wfΣ (⊢· L⊢ M⊢) (ξ-·₁ red shiftM) =
  store-preservation wfΣ L⊢ red
store-preservation wfΣ (⊢· V⊢ M⊢) (ξ-·₂ vV shiftV red) =
  store-preservation wfΣ M⊢ red
store-preservation wfΣ (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ red) =
  store-preservation wfΣ M⊢ red
store-preservation wfΣ (⊢ν hA L⊢ c⊢) (ξ-ν red) =
  store-preservation wfΣ L⊢ red
store-preservation wfΣ (⊢ν hA (⊢blame hB) c⊢) blame-ν = wfΣ
store-preservation wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red shiftM) =
  store-preservation wfΣ L⊢ red
store-preservation wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL shiftL red) =
  store-preservation wfΣ M⊢ red

------------------------------------------------------------------------
-- Store-change preservation
------------------------------------------------------------------------

preservation :
  ∀ {Δ Σ M N A χ} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ N ⦂ applyTy χ A
preservation wfΣ okM M⊢ (pure-step red) =
  pure-preservation-runtime wfΣ M⊢ okM red
preservation wfΣ okM (⊢ν hA V⊢ c⊢)
    (ν-step vV noV′) =
  ν-step-typing (at wfΣ) hA noV′ vV V⊢ c⊢
preservation wfΣ okM (⊢· L⊢ M⊢)
    (ξ-·₁ {χ = χ} red shiftM) =
  ⊢·-applyTy χ
    (preservation wfΣ (runtime-·₁ okM) L⊢ red)
    (applyTerm-typing-shiftable (at wfΣ) shiftM M⊢)
preservation wfΣ okM (⊢· V⊢ M⊢)
    (ξ-·₂ {χ = χ} vV shiftV red) =
  ⊢·-applyTy χ
    (applyTerm-typing-shiftable (at wfΣ) shiftV V⊢)
    (preservation wfΣ (runtime-·₂ vV okM) M⊢ red)
preservation wfΣ okM (⊢⟨⟩ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    with applyCoercion-typing {χ = χ} (at wfΣ) c⊢
... | μ′ , c′⊢ =
  ⊢⟨⟩ c′⊢ (preservation wfΣ (runtime-⟨⟩ okM) M⊢ red)
preservation wfΣ okM (⊢ν hA L⊢ c⊢)
    (ξ-ν {χ = χ} red)
    with applyCoercionUnderTyBinder-typing {χ = χ} (at wfΣ) hA c⊢
... | μ′ , c′⊢ =
  ⊢ν-applyTy χ
    (renameA χ hA)
    (preservation wfΣ (runtime-ν okM) L⊢ red)
    c′⊢
  where
    renameA : ∀ χ → WfTy _ _ → WfTy (applyTyCtx χ _) (applyTy χ _)
    renameA keep h = h
    renameA (bind Aχ) h = renameᵗ-preserves-WfTy h TyRenameWf-suc
preservation wfΣ okM (⊢ν hA (⊢blame (wf∀ hC)) c⊢)
    blame-ν =
  ⊢blame (typing-wf (at wfΣ) closedCtxWf (⊢ν hA (⊢blame (wf∀ hC)) c⊢))
preservation wfΣ okM (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₁ {χ = χ} red shiftM) =
  ⊢⊕-applyTy χ
    (preservation wfΣ (runtime-⊕₁ okM) L⊢ red) op
    (applyTerm-typing-shiftable (at wfΣ) shiftM M⊢)
preservation wfΣ okM (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₂ {χ = χ} vL shiftL red) =
  ⊢⊕-applyTy χ
    (applyTerm-typing-shiftable (at wfΣ) shiftL L⊢) op
    (preservation wfΣ (runtime-⊕₂ vL okM) M⊢ red)

multi-preservation :
  ∀ {Δ Σ M N A χs} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —↠[ χs ] N →
  applyTyCtxs χs Δ ∣ applyStores χs Σ ∣ [] ⊢ N ⦂ applyTys χs A
multi-preservation wfΣ okM M⊢ ↠-refl = M⊢
multi-preservation wfΣ okM M⊢ (↠-step red reds) =
  multi-preservation
    (store-preservation wfΣ M⊢ red)
    (runtime-preservation wfΣ okM M⊢ red)
    (preservation wfΣ okM M⊢ red)
    reds

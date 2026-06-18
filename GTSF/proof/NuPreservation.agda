module proof.NuPreservation where

-- File Charter:
--   * Type preservation for Nu GTSF one-step reduction.
--   * Keeps store growth, fresh type-variable allocation, and redex typing
--     obligations local to preservation.
--   * Uses the type/coercion/term metatheory factored into sibling proof files.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Binary.Sublist.Propositional
  renaming ([] to []⊆; _∷_ to _∷⊆_; _∷ʳ_ to _∷ʳ⊆_)
  using ()
open import Data.Nat using (suc; _<_; _≤_; _⊔_; zero; z<s; s<s; s≤s)
open import Data.Nat.Properties
  using (≤-refl; n≤1+n; <-≤-trans; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Ctx
open import NuStore
open import Store using (⊆-trans; complement; lookup)
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import proof.TypeProperties
open import proof.NuStoreProperties
open import proof.CoercionProperties
open import proof.NuTermProperties

------------------------------------------------------------------------
-- Preservation result for store-threaded steps
------------------------------------------------------------------------

record PreservationResult
    (Δ : TyCtx) (Σ : Store) (Γ : Ctx)
    (Σ′ : Store) (N : Term) (A : Ty) : Set₁ where
  constructor preserve
  field
    Δ′ : TyCtx
    storeWf : StoreWf Δ′ Σ′
    ctx≤ : Δ ≤ Δ′
    storeIncl : StoreIncl Σ Σ′
    ctxWf : CtxWf Δ′ Γ
    typed : Δ′ ∣ Σ′ ∣ Γ ⊢ N ⦂ A

open PreservationResult public

structural-refl :
  ∀ {Σ} →
  StoreIncl Σ Σ
structural-refl {Σ = []} = []⊆
structural-refl {Σ = x ∷ Σ} = refl ∷⊆ structural-refl

structural-refl-complement :
  ∀ Σ →
  complement (structural-refl {Σ = Σ}) ≡ []
structural-refl-complement [] = refl
structural-refl-complement (x ∷ Σ) = structural-refl-complement Σ

coercion-open-existing :
  ∀ {Δ Σ Π c A B α} →
  α < Δ →
  suc Δ ∣ ⟰ᵗ Σ ∣ ⟰ᵗ Π ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ∣ Π ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-existing {Σ = Σ} {Π = Π} {α = α} α<Δ c⊢ =
  subst
    (λ Π′ → _ ∣ Σ ∣ Π′ ⊢ _ ∶ _ =⇒ _)
    (renameStoreᵗ-single-suc-cancel α Π)
    (subst
      (λ Σ′ →
        _ ∣ Σ′ ∣ renameStoreᵗ (singleRenameᵗ α) (⟰ᵗ Π)
          ⊢ _ ∶ _ =⇒ _)
      (renameStoreᵗ-single-suc-cancel α Σ)
      (coercion-renameᵗ (singleRenameᵗ-Wf-< α<Δ) c⊢))

------------------------------------------------------------------------
-- Raw redex preservation
------------------------------------------------------------------------

pure-preservation :
  ∀ {Δ Σ Γ M N A} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Σ ∣ Γ ⊢ N ⦂ A
pure-preservation wfΣ hΓ
    (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n)))
    δ-⊕ =
  ⊢$ _
pure-preservation wfΣ hΓ (⊢· (⊢ƛ hA hN) hV) (β vV) =
  typing-single-subst hN hV
pure-preservation wfΣ hΓ
    (⊢• {B = B} (⊢Λ {A = B′} vV V⊢) α<Δ)
    β-Λ =
  typing-open-existingᵀ α<Δ V⊢
pure-preservation wfΣ hΓ (⊢⟨⟩ d (cast-id hA) hV) (β-id vV) =
  hV
pure-preservation wfΣ hΓ (⊢⟨⟩ d (cast-seq p⊢ q⊢) hV) (β-seq vV) =
  ⊢⟨⟩ d q⊢ (⊢⟨⟩ d p⊢ hV)
pure-preservation wfΣ hΓ
    (⊢· (⊢⟨⟩ d (cast-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩ d q⊢ (⊢· hV (⊢⟨⟩ d p⊢ hW))
pure-preservation wfΣ hΓ
    (⊢• {α = α}
      (⊢⟨⟩ {M = V} d (`∀⊢@(cast-all {A = A₀} {s = c} c⊢)) V⊢)
      α<Δ)
    (β-∀ vV) =
  ⊢⟨⟩
    d
    (coercion-open-existing α<Δ c⊢)
    app-src⊢
  where
    src-open-eq :
      (src c) [ α ]ᴿ ≡ A₀ [ α ]ᴿ
    src-open-eq with coercion-src-tgtᵐ c⊢
    src-open-eq | src-eq , tgt-eq =
      cong (λ T → T [ α ]ᴿ) src-eq

    V-src⊢ :
      _ ∣ _ ∣ _ ⊢ V ⦂ `∀ (src c)
    V-src⊢ with coercion-src-tgtᵐ c⊢
    V-src⊢ | src-eq , tgt-eq =
      subst (λ U → _ ∣ _ ∣ _ ⊢ V ⦂ `∀ U) (sym src-eq) V⊢

    app-src⊢ :
      _ ∣ _ ∣ _ ⊢ V • α ⦂ A₀ [ α ]ᴿ
    app-src⊢ =
      subst
        (λ U → _ ∣ _ ∣ _ ⊢ V • α ⦂ U)
        src-open-eq
        (⊢• V-src⊢ α<Δ)
pure-preservation wfΣ hΓ
    (⊢⟨⟩ {M = V} d (cast-inst {A = A} {B = B} {s = c} hB _ c⊢) V⊢)
    (β-inst vV) =
  ⊢ν
    wf★
    (⊢⟨⟩
      (StoreIncl-cons (renameStoreᵗ-incl suc d))
      (subst
        (λ Σ′ → _ ∣ Σ′ ∣ _ ⊢ c ∶ _ =⇒ _)
        (complement-rename suc d)
        c⊢)
      app-src⊢)
  where
    app-src-eq :
      (renameᵗ (extᵗ suc) A) [ zero ]ᴿ ≡ A
    app-src-eq =
      trans
        (renameᵗ-compose (extᵗ suc) (singleRenameᵗ zero) A)
        (trans
          (rename-cong
            (λ { zero → refl
               ; (suc X) → refl})
            A)
          (renameᵗ-id A))

    shifted-V⊢ :
      _ ∣ _ ∣ _ ⊢ ⇑ᵗᵐ V ⦂ `∀ (renameᵗ (extᵗ suc) A)
    shifted-V⊢ =
      term-weaken ≤-refl StoreIncl-drop (typing-renameᵀ TyRenameWf-suc V⊢)

    app-src⊢ :
      _ ∣ _ ∣ _ ⊢ ⇑ᵗᵐ V • zero ⦂ A
    app-src⊢ =
      subst
        (λ T → _ ∣ _ ∣ _ ⊢ ⇑ᵗᵐ V • zero ⦂ T)
        app-src-eq
        (⊢• shifted-V⊢ z<s)
pure-preservation wfΣ hΓ
    (⊢⟨⟩ dB (cast-unseal hB αB∈Σ)
      (⊢⟨⟩ dA (cast-seal hA αA∈Σ) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ (lookup dA αA∈Σ) (lookup dB αB∈Σ))
        hV
pure-preservation wfΣ hΓ
    (⊢⟨⟩ dH (cast-untag hG gG _) (⊢⟨⟩ dG (cast-tag hG′ gG′ _) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ hΓ
    (⊢⟨⟩ dH (cast-untag hH gH _) (⊢⟨⟩ dG (cast-tag hG gG _) hV))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH
pure-preservation wfΣ hΓ (⊢· (⊢blame (wf⇒ hA hB)) hM) blame-·₁ =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    with typing-wf (at wfΣ) hΓ hV
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    | wf⇒ hA′ hB =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢• (⊢blame (wf∀ hB)) α<Δ) blame-·α =
  ⊢blame (renameᵗ-preserves-WfTy hB (singleRenameᵗ-Wf-< α<Δ))
pure-preservation wfΣ hΓ (⊢⟨⟩ d c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wf (at wfΣ) d c⊢
pure-preservation wfΣ hΓ (⊢⟨⟩ d c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢⊕ (⊢blame hA) op hM) blame-⊕₁ =
  ⊢blame wfBase
pure-preservation wfΣ hΓ (⊢⊕ hL op (⊢blame hA)) (blame-⊕₂ vL) =
  ⊢blame wfBase

------------------------------------------------------------------------
-- Store-threaded preservation
------------------------------------------------------------------------

preservation :
  ∀ {Δ Σ Σ′ Γ M N A} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ M —→ Σ′ ∣ N →
  PreservationResult Δ Σ Γ Σ′ N A
preservation wfΣ hΓ M⊢ (pure-step red) =
  preserve _ wfΣ ≤-refl StoreIncl-refl hΓ
    (pure-preservation wfΣ hΓ M⊢ red)
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢ν {A = A} hA hN)
    (ν-step {α = α} Δ≤α) =
  preserve
    (suc (α ⊔ Δ))
    (StoreWf-fresh-ext
      wfΣ
      (≤-trans (m≤n⊔m α Δ) (n≤1+n (α ⊔ Δ)))
      (s≤s (m≤m⊔n α Δ))
      hA
      (StoreWfAt-≥-fresh (at wfΣ) Δ≤α))
    (≤-trans (m≤n⊔m α Δ) (n≤1+n (α ⊔ Δ)))
    StoreIncl-drop
    (CtxWf-weaken hΓ (≤-trans (m≤n⊔m α Δ) (n≤1+n (α ⊔ Δ))))
    (typing-open-headᵀ
      (s≤s (m≤m⊔n α Δ))
      (term-weaken (s≤s (m≤n⊔m α Δ)) StoreIncl-refl hN))
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢• {α = α}
      (⊢⟨⟩ {M = V} {Π = Π} d
        (cast-gen {A = C} {B = B} {s = c} hC _ c⊢)
        V⊢)
      α<Δ)
    (gen-step {β = β₀} vV Δ≤β) =
  preserve
    Δ₁
    wfΣ′
    Δ≤Δ₁
    StoreIncl-drop
    (CtxWf-weaken hΓ Δ≤Δ₁)
    reduct⊢
  where
    Δ₁ : TyCtx
    Δ₁ = suc (β₀ ⊔ Δ)

    Δ≤Δ₁ : Δ ≤ Δ₁
    Δ≤Δ₁ = ≤-trans (m≤n⊔m β₀ Δ) (n≤1+n (β₀ ⊔ Δ))

    β<Δ₁ : β₀ < Δ₁
    β<Δ₁ = s≤s (m≤m⊔n β₀ Δ)

    α<Δ₁ : α < Δ₁
    α<Δ₁ = <-≤-trans α<Δ Δ≤Δ₁

    β∉Σ : β₀ ∉ domˢ Σ
    β∉Σ = StoreWfAt-≥-fresh (at wfΣ) Δ≤β

    hρ : TyRenameWf (suc Δ) Δ₁ (singleRenameᵗ β₀)
    hρ {zero} z<s = β<Δ₁
    hρ {suc X} (s<s X<Δ) = <-≤-trans X<Δ Δ≤Δ₁

    wfΣ′ : StoreWf Δ₁ ((β₀ , ＇ α) ∷ Σ)
    wfΣ′ =
      StoreWf-fresh-ext wfΣ Δ≤Δ₁ β<Δ₁ (wfVar α<Δ) β∉Σ

    d′ : StoreIncl Π ((β₀ , ＇ α) ∷ Σ)
    d′ = (β₀ , ＇ α) ∷ʳ⊆ d

    V⊢′ : Δ₁ ∣ (β₀ , ＇ α) ∷ Σ ∣ Γ ⊢ V ⦂ C
    V⊢′ = term-weaken Δ≤Δ₁ StoreIncl-drop V⊢

    cβ⊢ :
      Δ₁ ∣ (β₀ , ＇ α) ∷ complement d ∣ Π
        ⊢ c [ β₀ ]ᶜ ∶ C =⇒ B [ β₀ ]ᴿ
    cβ⊢ = coercion-open-gen-fresh hρ c⊢

    casted⊢ :
      Δ₁ ∣ (β₀ , ＇ α) ∷ Σ ∣ Γ
        ⊢ V ⟨ c [ β₀ ]ᶜ ⟩ ⦂ B [ β₀ ]ᴿ
    casted⊢ = ⊢⟨⟩ d′ cβ⊢ V⊢′

    tagWf :
      StoreWfAt (suc Δ) ((zero , ★) ∷ ⟰ᵗ (complement d))
    tagWf =
      StoreWfAt-cons z<s wf★
        (StoreWfAt-⟰ᵗ (StoreWfAt-complement (at wfΣ) d))

    sealWf : StoreWfAt (suc Δ) (⟰ᵗ Π)
    sealWf = StoreWfAt-⟰ᵗ (StoreWfAt-⊆ (at wfΣ) d)

    hTgt : WfTy (suc Δ) (tgt c)
    hTgt with coercion-wf-stores tagWf sealWf c⊢ | coercion-src-tgtᵐ c⊢
    hTgt | hSrc , hB | src-eq , tgt-eq =
      subst (WfTy (suc Δ)) (sym tgt-eq) hB

    noβ : occurs (suc β₀) (tgt c) ≡ false
    noβ = occurs-above-WfTy hTgt (s≤s Δ≤β)

    tgt-eq : tgt c ≡ B
    tgt-eq with coercion-src-tgtᵐ c⊢
    tgt-eq | src-eq , tgt-eq′ = tgt-eq′

    revealRaw :
      Δ₁ ∣ [] ∣ (β₀ , ＇ α) ∷ Σ
        ⊢ reveal ((tgt c) [ β₀ ]ᴿ) β₀ (＇ α)
          ∶ (tgt c) [ β₀ ]ᴿ =⇒ (tgt c) [ ＇ α ]ᵗ
    revealRaw =
      reveal-open-typing hTgt hρ noβ (wfVar α<Δ₁) (here refl)

    reveal-src-eq : (tgt c) [ β₀ ]ᴿ ≡ B [ β₀ ]ᴿ
    reveal-src-eq = cong (λ T → T [ β₀ ]ᴿ) tgt-eq

    reveal-tgt-eq : (tgt c) [ ＇ α ]ᵗ ≡ B [ α ]ᴿ
    reveal-tgt-eq =
      trans (subst-var-rename α (tgt c))
            (cong (λ T → T [ α ]ᴿ) tgt-eq)

    reveal⊢ :
      Δ₁ ∣ [] ∣ (β₀ , ＇ α) ∷ Σ
        ⊢ reveal ((tgt c) [ β₀ ]ᴿ) β₀ (＇ α)
          ∶ B [ β₀ ]ᴿ =⇒ B [ α ]ᴿ
    reveal⊢ =
      subst
        (λ T →
          Δ₁ ∣ [] ∣ (β₀ , ＇ α) ∷ Σ
            ⊢ reveal ((tgt c) [ β₀ ]ᴿ) β₀ (＇ α)
              ∶ B [ β₀ ]ᴿ =⇒ T)
        reveal-tgt-eq
        (subst
          (λ S →
            Δ₁ ∣ [] ∣ (β₀ , ＇ α) ∷ Σ
              ⊢ reveal ((tgt c) [ β₀ ]ᴿ) β₀ (＇ α)
                ∶ S =⇒ (tgt c) [ ＇ α ]ᵗ)
          reveal-src-eq
          revealRaw)

    reduct⊢ :
      Δ₁ ∣ (β₀ , ＇ α) ∷ Σ ∣ Γ
        ⊢ V ⟨ c [ β₀ ]ᶜ ⟩
            ⟨ reveal ((tgt c) [ β₀ ]ᴿ) β₀ (＇ α) ⟩
          ⦂ B [ α ]ᴿ
    reduct⊢ =
      ⊢⟨⟩
        structural-refl
        (subst
          (λ Σtag →
            Δ₁ ∣ Σtag ∣ (β₀ , ＇ α) ∷ Σ
              ⊢ reveal ((tgt c) [ β₀ ]ᴿ) β₀ (＇ α)
                ∶ B [ β₀ ]ᴿ =⇒ B [ α ]ᴿ)
          (sym (structural-refl-complement ((β₀ , ＇ α) ∷ Σ)))
          reveal⊢)
        casted⊢
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₁ red)
    with preservation wfΣ hΓ L⊢ red
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₁ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢· L′⊢ (term-weaken Δ≤Δ′ incl M⊢))
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢· (term-weaken Δ≤Δ′ incl L⊢) M′⊢)
preservation wfΣ hΓ (⊢• M⊢ α<Δ) (ξ-·α red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢• M⊢ α<Δ) (ξ-·α red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢• M′⊢ (<-≤-trans α<Δ Δ≤Δ′))
preservation wfΣ hΓ (⊢⟨⟩ d c⊢ M⊢) (ξ-⟨⟩ red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢⟨⟩ d c⊢ M⊢) (ξ-⟨⟩ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⟨⟩
      (⊆-trans d incl)
      (coercion-weaken Δ≤Δ′ (complement-incl d incl) StoreIncl-refl c⊢)
      M′⊢)
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
    with preservation wfΣ hΓ L⊢ red
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⊕ L′⊢ op (term-weaken Δ≤Δ′ incl M⊢))
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⊕ (term-weaken Δ≤Δ′ incl L⊢) op M′⊢)

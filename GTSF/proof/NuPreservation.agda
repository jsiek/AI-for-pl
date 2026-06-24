module proof.NuPreservation where

-- File Charter:
--   * Type preservation for Nu GTSF one-step reduction.
--   * Keeps store growth, fresh type-variable allocation, and redex typing
--     obligations local to preservation.
--   * Uses the type/coercion/term metatheory factored into sibling proof files.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Nat using (suc; _<_; _≤_; _⊔_; zero; z<s; s≤s)
open import Data.Nat.Properties
  using (≤-refl; n≤1+n; <-≤-trans; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

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
-- Preservation result for store-threaded steps
------------------------------------------------------------------------

record PreservationResult
    (Δ : TyCtx) (Σ : Store) (Γ : Ctx) (Δ′ : TyCtx)
    (Σ′ : Store) (N : Term) (A : Ty) : Set₁ where
  constructor preserve
  field
    storeWf : StoreWf Δ′ Σ′
    ctx≤ : Δ ≤ Δ′
    storeIncl : StoreIncl Σ Σ′
    ctxWf : CtxWf Δ′ Γ
    typed : Δ′ ∣ Σ′ ∣ Γ ⊢ N ⦂ A

open PreservationResult public

------------------------------------------------------------------------
-- Typing the type-application machine
------------------------------------------------------------------------

data CastStack (Δ : TyCtx) (Σ : Store) :
    List Coercion → Ty → Ty → Set₁ where

  stack[] : ∀ {A} →
      --------------------
      CastStack Δ Σ [] A A

  stack∷ : ∀ {μ c cs A B C}
    → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
    → CastStack Δ Σ cs B C
      -------------------------------
    → CastStack Δ Σ (c ∷ cs) A C

applyCoercions-typing :
  ∀ {Δ Σ Γ M cs A B} →
  CastStack Δ Σ cs A B →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ Γ ⊢ applyCoercions M cs ⦂ B
applyCoercions-typing stack[] M⊢ = M⊢
applyCoercions-typing (stack∷ c⊢ cs⊢) M⊢ =
  applyCoercions-typing cs⊢ (⊢⟨⟩ c⊢ M⊢)

data TypeAppTyping
    (Δ₀ Δ′ : TyCtx) (Σ : Store) (Γ : Ctx) (α : TyVar)
    (Aν : Ty) :
    TypeApp → Ty → Set₁ where

  app⊢ : ∀ {L C cs B}
    → Δ₀ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C
    → CastStack Δ′ ((α , Aν) ∷ Σ) cs (C [ α ]ᴿ) B
      ------------------------------------
    → TypeAppTyping Δ₀ Δ′ Σ Γ α Aν (app L α cs) B

  val⊢ : ∀ {V cs A B}
    → Δ′ ∣ (α , Aν) ∷ Σ ∣ Γ ⊢ V ⦂ A
    → CastStack Δ′ ((α , Aν) ∷ Σ) cs A B
      ------------------------------------
    → TypeAppTyping Δ₀ Δ′ Σ Γ α Aν (val V cs) B

type-app-preservation-step :
  ∀ {Δ Δ′ Σ Γ α A S T B} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  α ∉ domˢ Σ →
  StoreWf Δ′ ((α , A) ∷ Σ) →
  CtxWf Δ′ Γ →
  TypeAppTyping Δ Δ′ Σ Γ α A S B →
  S —→ᵀ T →
  TypeAppTyping Δ Δ′ Σ Γ α A T B
type-app-preservation-step wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′
    (app⊢ (⊢Λ vV V⊢) stack⊢)
    (β-Λᵀ vV′) =
  val⊢
    (typing-open-freshᵀ wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ V⊢)
    stack⊢
type-app-preservation-step wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′
    (app⊢ (⊢⟨⟩ (cast-all c⊢) V⊢) stack⊢)
    (β-∀ᵀ vV)
    with coercion-open-store-fresh wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢
... | μ′ , cα⊢ =
  app⊢ V⊢ (stack∷ cα⊢ stack⊢)
type-app-preservation-step wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′
    (app⊢ (⊢⟨⟩ (cast-gen hA occ c⊢) V⊢) stack⊢)
    (β-genᵀ vV)
    with coercion-open-shift-fresh wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢
... | μ′ , cα⊢ =
  val⊢
    (term-weaken Δ≤Δ′ StoreIncl-drop V⊢)
    (stack∷ cα⊢ stack⊢)

type-app-preservation-closure :
  ∀ {Δ Δ′ Σ Γ α A S T B} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  α ∉ domˢ Σ →
  StoreWf Δ′ ((α , A) ∷ Σ) →
  CtxWf Δ′ Γ →
  TypeAppTyping Δ Δ′ Σ Γ α A S B →
  S —↠ᵀ T →
  TypeAppTyping Δ Δ′ Σ Γ α A T B
type-app-preservation-closure
    wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′ S⊢ doneᵀ = S⊢
type-app-preservation-closure
    wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′ S⊢ (stepᵀ S→T T↠U) =
  type-app-preservation-closure
    wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′
    (type-app-preservation-step
      wfΣ hΓ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′ S⊢ S→T)
    T↠U

type-app-initial :
  ∀ {Δ Δ′ Σ Γ A B C L c α μ} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  α ∉ domˢ Σ →
  StoreWf Δ′ ((α , A) ∷ Σ) →
  CtxWf Δ′ Γ →
  WfTy Δ A →
  Δ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
  TypeAppTyping Δ Δ′ Σ Γ α A
    (app L α ((c [ α ]ᶜ) ∷ [])) B
type-app-initial wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′ hA hL c⊢
    with coercion-open-fresh wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ hA c⊢
... | μ′ , cα⊢ =
  app⊢
    hL
    (stack∷ cα⊢ stack[])

type-app-preservation :
  ∀ {Δ Δ′ Σ Γ A B C L c V cs α μ} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  α ∉ domˢ Σ →
  StoreWf Δ′ ((α , A) ∷ Σ) →
  CtxWf Δ Γ →
  CtxWf Δ′ Γ →
  WfTy Δ A →
  Δ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
  app L α ((c [ α ]ᶜ) ∷ []) —↠ᵀ val V cs →
  Δ′ ∣ (α , A) ∷ Σ ∣ Γ ⊢ applyCoercions V cs ⦂ B
type-app-preservation {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {A = A}
    {B = B} {C = C} {L = L} {c = c} {V = V} {cs = cs}
    {α = α} wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ hΓ′ hA hL c⊢ L↠V
    with type-app-preservation-closure
      wfΣ
      hΓ
      Δ≤Δ′
      Δ≤α
      α<Δ′
      α∉Σ
      wfΣ′
      hΓ′
      (type-app-initial
        wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ wfΣ′ hΓ′ hA hL c⊢)
      L↠V
... | val⊢ V⊢ stack⊢ = applyCoercions-typing stack⊢ V⊢

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
pure-preservation wfΣ hΓ (⊢⟨⟩ (cast-id hA _) hV) (β-id vV) =
  hV
pure-preservation wfΣ hΓ (⊢⟨⟩ (cast-seq p⊢ q⊢) hV) (β-seq vV) =
  ⊢⟨⟩ q⊢ (⊢⟨⟩ p⊢ hV)
pure-preservation wfΣ hΓ
    (⊢· (⊢⟨⟩ (cast-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩ q⊢ (⊢· hV (⊢⟨⟩ p⊢ hW))
pure-preservation wfΣ hΓ
    (⊢⟨⟩ {M = V}
      (cast-inst {A = A} {B = B} {s = c} hB occ c⊢) V⊢)
    (β-inst vV) =
  ⊢ν wf★ V⊢ c⊢
pure-preservation wfΣ hΓ
    (⊢⟨⟩ (cast-unseal hB αB∈Σ _)
      (⊢⟨⟩ (cast-seal hA αA∈Σ _) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ hΓ
    (⊢⟨⟩ (cast-untag hG gG _) (⊢⟨⟩ (cast-tag hG′ gG′ _) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ hΓ
    (⊢⟨⟩ (cast-untag hH gH _) (⊢⟨⟩ (cast-tag hG gG _) hV))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH
pure-preservation wfΣ hΓ (⊢· (⊢blame (wf⇒ hA hB)) hM) blame-·₁ =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    with typing-wf (at wfΣ) hΓ hV
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    | wf⇒ hA′ hB =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wfᵐ (at wfΣ) c⊢
pure-preservation wfΣ hΓ (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
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
  ∀ {Δ Δ′ Σ Σ′ Γ M N A} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ M —→ Δ′ ∣ Σ′ ∣ N →
  PreservationResult Δ Σ Γ Δ′ Σ′ N A
preservation wfΣ hΓ M⊢ (pure-step red) =
  preserve wfΣ ≤-refl StoreIncl-refl hΓ
    (pure-preservation wfΣ hΓ M⊢ red)
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢ν {A = A} hA hL c⊢)
    (ν-step {α = α} Δ≤α α∉Σ L↠V) =
  let
    Δ≤sα = ≤-trans Δ≤α (n≤1+n α)
    α<sα = s≤s ≤-refl
    wfΣ′ = StoreWf-fresh-ext wfΣ Δ≤sα Δ≤α α<sα hA α∉Σ
    hΓ′ = CtxWf-weaken hΓ Δ≤sα
  in
  preserve
    wfΣ′
    Δ≤sα
    StoreIncl-drop
    hΓ′
    (type-app-preservation
      (at wfΣ)
      Δ≤sα
      Δ≤α
      α<sα
      α∉Σ
      wfΣ′
      hΓ
      hΓ′
      hA
      hL
      c⊢
      L↠V)
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₁ red)
    with preservation wfΣ hΓ L⊢ red
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₁ red)
    | preserve wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢· L′⊢ (term-weaken Δ≤Δ′ incl M⊢))
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
    | preserve wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢· (term-weaken Δ≤Δ′ incl L⊢) M′⊢)
preservation wfΣ hΓ (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ red)
    | preserve wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⟨⟩ (coercion-weakenᵐ Δ≤Δ′ incl c⊢) M′⊢)
preservation wfΣ hΓ (⊢ν hA hL c⊢) (ξ-ν red)
    with preservation wfΣ hΓ hL red
preservation wfΣ hΓ (⊢ν hA hL c⊢) (ξ-ν red)
    | preserve wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢ν
      (WfTy-weakenᵗ hA Δ≤Δ′)
      L′⊢
      (coercion-weakenᵐ
        (s≤s Δ≤Δ′)
        (StoreIncl-cons (renameStoreᵗ-incl suc incl))
        c⊢))
preservation wfΣ hΓ (⊢ν hA (⊢blame (wf∀ hC)) c⊢) blame-ν =
  preserve wfΣ ≤-refl StoreIncl-refl hΓ
    (⊢blame (typing-wf (at wfΣ) hΓ (⊢ν hA (⊢blame (wf∀ hC)) c⊢)))
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
    with preservation wfΣ hΓ L⊢ red
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
    | preserve wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⊕ L′⊢ op (term-weaken Δ≤Δ′ incl M⊢))
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
    | preserve wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⊕ (term-weaken Δ≤Δ′ incl L⊢) op M′⊢)

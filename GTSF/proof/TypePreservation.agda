module proof.TypePreservation where

-- File Charter:
--   * Type preservation for the refined `TermTyping` judgment.
--   * The proof follows `proof.NuPreservation`, but each cast case preserves
--     the refined conversion/narrowing/widening class instead of falling back
--     to ordinary coercion typing.
--   * Runtime and store invariants are reused through the forgetful embedding
--     from `TermTyping` to `NuTerms`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s; s<s; z≤n; s≤s; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx
open import Store using
  ( StoreIncl
  ; StoreIncl-drop
  ; StoreIncl-cons
  )
open import NuStore
open import Coercions
open import Conversion
open import NarrowWiden
open import Primitives
open import NuTerms
  using
    ( Term
    ; Value
    ; RuntimeOK
    ; No•
    ; `_
    ; ƛ_
    ; _·_
    ; Λ_
    ; _•
    ; ν
    ; $
    ; _⊕[_]_
    ; _⟨_⟩
    ; blame
    ; no•-`
    ; no•-ƛ
    ; no•-·
    ; no•-Λ
    ; no•-ν
    ; no•-$
    ; no•-⊕
    ; no•-⟨⟩
    ; no•-blame
    ; ok-no
    ; ok-•
    ; ok-·₁
    ; ok-·₂
    ; ok-ν
    ; ok-⊕₁
    ; ok-⊕₂
    ; ok-⟨⟩
    ; ⇑ᵗᵐ
    ; renameᵗᵐ
    ; renameˣᵐ
    ; substˣᵐ
    ; Substˣ
    ; extˢˣ
    ; ↑ᵗᵐ
    ; singleEnv
    ; _[_]
    )
open import NuReduction
open import TermTyping
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; RenameLeftInverse
    ; RenameLeftInverse-suc
    ; RenameLeftInverse-ext
    ; predᵗ
    ; WfTy-weakenᵗ
    ; renameᵗ-preserves-WfTy
    ; renameᵗ-ext-suc-comm
    ; renameStoreᵗ-ext-suc-comm
    )
open import proof.StoreProperties
  using
    ( StoreWfAt-⟰ᵗ
    ; ∈-renameStoreᵗ
    ; renameStoreᵗ-incl
    )
open import proof.CoercionProperties
  using
    ( ModeRename
    ; ModeRename-ext
    ; ModeRename-gen
    ; ModeRename-inst
    ; coercion-weakenᵐ
    ; coercion-renameᵗᵐ
    ; modeRename-idTyAllowed
    ; modeRename-sealModeAllowed
    ; coercion-wfᵐ
    ; open0-ext-suc-cancelᶜ
    )
open import proof.NuTermProperties
  using
    ( RenameWf
    ; RenameWf-ext
    ; RenameWf-⤊
    ; lookup-map-renameᵗ
    ; lookup-⤊-elim
    ; lookup-⤊-elim₀
    ; CtxWf-⤊
    ; map-renameᵗ-⤊
    ; renameStoreᵗ-ext-suc-cons-comm
    ; renameˣ-renameᵗᵐ
    ; renameᵗᵐ-preserves-No•
    ; renameᵗᵐ-preserves-Value
    ; renameˣᵐ-preserves-No•
    ; renameˣᵐ-preserves-Value
    ; substˣᵐ-preserves-Value
    ; modeRename-left-inverse
    ; substˣᵐ-preserves-No•-typed
    ; singleSubstNo•
    ; open0-ext-suc-cancelᵐ
    )
import proof.NuTermProperties as NuTermProperties
import proof.NuPreservation as NuPreservation

------------------------------------------------------------------------
-- Basic context facts
------------------------------------------------------------------------

closedCtxWf : ∀ {Δ} → CtxWf Δ []
closedCtxWf ()

typing-wf :
  ∀ {Δ Σ Γ M A} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  WfTy Δ A
typing-wf wfΣ hΓ M⊢ =
  NuTermProperties.typing-wf wfΣ hΓ (forget M⊢)

typing-wf-∀-body :
  ∀ {Δ Σ V C} →
  StoreWfAt Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ `∀ C →
  WfTy (suc Δ) C
typing-wf-∀-body wfΣ V⊢ with typing-wf wfΣ closedCtxWf V⊢
typing-wf-∀-body wfΣ V⊢ | wf∀ hC = hC

------------------------------------------------------------------------
-- Refined cast evidence under weakening and renaming
------------------------------------------------------------------------

modeRename-suc-weakenCast :
  ∀ {μ} →
  ModeRename suc μ (weakenCastᵈ μ)
modeRename-suc-weakenCast {μ = μ} X with μ X
modeRename-suc-weakenCast X | id-only = refl
modeRename-suc-weakenCast X | tag-or-id = refl
modeRename-suc-weakenCast X | seal-or-id = refl

seal★-weaken :
  ∀ {μ Σ Σ′} →
  StoreIncl Σ Σ′ →
  SealModeStore★ μ Σ →
  SealModeStore★ μ Σ′
seal★-weaken incl seal★ α ok = incl (seal★ α ok)

seal★-inst :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ)
seal★-inst seal★ zero ok = here refl
seal★-inst seal★ (suc α) ok =
  there (∈-renameStoreᵗ suc (seal★ α ok))

seal★-ext-shift :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (extᵈ μ) (⟰ᵗ Σ)
seal★-ext-shift seal★ zero ()
seal★-ext-shift seal★ (suc α) ok =
  ∈-renameStoreᵗ suc (seal★ α ok)

seal★-gen-shift :
  ∀ {μ Σ} →
  SealModeStore★ μ Σ →
  SealModeStore★ (genᵈ μ) (⟰ᵗ Σ)
seal★-gen-shift seal★ zero ()
seal★-gen-shift seal★ (suc α) ok =
  ∈-renameStoreᵗ suc (seal★ α ok)

seal★-weakenCast-bind :
  ∀ {μ Σ A} →
  SealModeStore★ μ Σ →
  SealModeStore★ (weakenCastᵈ μ) ((zero , A) ∷ ⟰ᵗ Σ)
seal★-weakenCast-bind seal★ zero ()
seal★-weakenCast-bind seal★ (suc α) ok =
  there (∈-renameStoreᵗ suc (seal★ α ok))

seal★-inst-weakenCast-bind :
  ∀ {μ Σ A} →
  SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ) →
  SealModeStore★
    (instᵈ (weakenCastᵈ μ))
    ((zero , ★) ∷ ⟰ᵗ ((zero , A) ∷ ⟰ᵗ Σ))
seal★-inst-weakenCast-bind seal★ zero ok = here refl
seal★-inst-weakenCast-bind seal★ (suc zero) ()
seal★-inst-weakenCast-bind seal★ (suc (suc α)) ok
    with seal★ (suc α) ok
seal★-inst-weakenCast-bind seal★ (suc (suc α)) ok | here ()
seal★-inst-weakenCast-bind seal★ (suc (suc α)) ok | there α∈ =
  there (there (∈-renameStoreᵗ suc α∈))

seal★-rename-preimage :
  ∀ {ρ μ ν Σ} →
  (∀ α → sealModeAllowed (ν α) ≡ true →
    Product.Σ TyVar
      (λ b → sealModeAllowed (μ b) ≡ true × ρ b ≡ α)) →
  SealModeStore★ μ Σ →
  SealModeStore★ ν (renameStoreᵗ ρ Σ)
seal★-rename-preimage pre seal★ α ok with pre α ok
seal★-rename-preimage {ρ = ρ} {Σ = Σ} pre seal★ α ok
    | b , b-ok , b↦α =
  subst (λ X → (X , ★) ∈ renameStoreᵗ ρ Σ) b↦α
    (∈-renameStoreᵗ ρ (seal★ b b-ok))

mutual
  conversion↑-weaken :
    ∀ {μ Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
    μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A ↑ˢ B

  conversion↓-weaken :
    ∀ {μ Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
    μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A ↓ˢ B

  conversion↑-weaken Δ≤Δ′ incl (conv↑-id hA ok) =
    conv↑-id (WfTy-weakenᵗ hA Δ≤Δ′) ok
  conversion↑-weaken Δ≤Δ′ incl (conv↑-unseal hA α∈Σ ok) =
    conv↑-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ) ok
  conversion↑-weaken Δ≤Δ′ incl (conv↑-fun s⊢ t⊢) =
    conv↑-fun (conversion↓-weaken Δ≤Δ′ incl s⊢)
              (conversion↑-weaken Δ≤Δ′ incl t⊢)
  conversion↑-weaken Δ≤Δ′ incl (conv↑-all c⊢) =
    conv↑-all
      (conversion↑-weaken (s≤s Δ≤Δ′) (renameStoreᵗ-incl suc incl) c⊢)

  conversion↓-weaken Δ≤Δ′ incl (conv↓-id hA ok) =
    conv↓-id (WfTy-weakenᵗ hA Δ≤Δ′) ok
  conversion↓-weaken Δ≤Δ′ incl (conv↓-seal hA α∈Σ ok) =
    conv↓-seal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ) ok
  conversion↓-weaken Δ≤Δ′ incl (conv↓-fun s⊢ t⊢) =
    conv↓-fun (conversion↑-weaken Δ≤Δ′ incl s⊢)
              (conversion↓-weaken Δ≤Δ′ incl t⊢)
  conversion↓-weaken Δ≤Δ′ incl (conv↓-all c⊢) =
    conv↓-all
      (conversion↓-weaken (s≤s Δ≤Δ′) (renameStoreᵗ-incl suc incl) c⊢)

mutual
  conversion↑-renameᵗ :
    ∀ {μ ν Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    ModeRename ρ μ ν →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
    ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ↑ˢ renameᵗ ρ B

  conversion↓-renameᵗ :
    ∀ {μ ν Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    ModeRename ρ μ ν →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
    ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ↓ˢ renameᵗ ρ B

  conversion↑-renameᵗ {ν = ν′} {ρ = ρ} hρ rel
      (conv↑-id {A = A} hA ok) =
    conv↑-id
      (renameᵗ-preserves-WfTy hA hρ)
      (modeRename-idTyAllowed {ρ = ρ} {ν = ν′} {A = A} rel ok)
  conversion↑-renameᵗ {ν = ν′} {ρ = ρ} hρ rel
      (conv↑-unseal {α = α} hA α∈Σ ok) =
    conv↑-unseal
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ ρ α∈Σ)
      (modeRename-sealModeAllowed {ρ = ρ} {ν = ν′} {α = α} rel ok)
  conversion↑-renameᵗ hρ rel (conv↑-fun s⊢ t⊢) =
    conv↑-fun (conversion↓-renameᵗ hρ rel s⊢)
              (conversion↑-renameᵗ hρ rel t⊢)
  conversion↑-renameᵗ {ρ = ρ} hρ rel (conv↑-all {s = s} c⊢) =
    conv↑-all
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) s ∶ _ ↑ˢ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (conversion↑-renameᵗ
          (TyRenameWf-ext hρ)
          (ModeRename-ext rel)
          c⊢))

  conversion↓-renameᵗ {ν = ν′} {ρ = ρ} hρ rel
      (conv↓-id {A = A} hA ok) =
    conv↓-id
      (renameᵗ-preserves-WfTy hA hρ)
      (modeRename-idTyAllowed {ρ = ρ} {ν = ν′} {A = A} rel ok)
  conversion↓-renameᵗ {ν = ν′} {ρ = ρ} hρ rel
      (conv↓-seal {α = α} hA α∈Σ ok) =
    conv↓-seal
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameStoreᵗ ρ α∈Σ)
      (modeRename-sealModeAllowed {ρ = ρ} {ν = ν′} {α = α} rel ok)
  conversion↓-renameᵗ hρ rel (conv↓-fun s⊢ t⊢) =
    conv↓-fun (conversion↑-renameᵗ hρ rel s⊢)
              (conversion↓-renameᵗ hρ rel t⊢)
  conversion↓-renameᵗ {ρ = ρ} hρ rel (conv↓-all {s = s} c⊢) =
    conv↓-all
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) s ∶ _ ↓ˢ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (conversion↓-renameᵗ
          (TyRenameWf-ext hρ)
          (ModeRename-ext rel)
          c⊢))

record CastModeRenamer (ρ : Renameᵗ) : Set₁ where
  field
    targetᵈ :
      ∀ {μ} →
      CastMode μ →
      ModeEnv

    target-mode :
      ∀ {μ} →
      (mode : CastMode μ) →
      CastMode (targetᵈ mode)

    target-rename :
      ∀ {μ} →
      (mode : CastMode μ) →
      ModeRename ρ μ (targetᵈ mode)

    target-seal-source :
      ∀ {μ} →
      (mode : CastMode μ) →
      (α : TyVar) →
      sealModeAllowed (targetᵈ mode α) ≡ true →
      Product.Σ TyVar
        (λ b → sealModeAllowed (μ b) ≡ true × ρ b ≡ α)

castModeRenamer-seal★ :
  ∀ {ρ μ Σ} →
  (η : CastModeRenamer ρ) →
  (mode : CastMode μ) →
  SealModeStore★ μ Σ →
  SealModeStore★ (CastModeRenamer.targetᵈ η mode) (renameStoreᵗ ρ Σ)
castModeRenamer-seal★ η mode =
  seal★-rename-preimage (CastModeRenamer.target-seal-source η mode)

castModeRenamer-suc : CastModeRenamer suc
castModeRenamer-suc =
  record
    { targetᵈ = λ {μ} mode → weakenCastᵈ μ
    ; target-mode = λ mode → cast-weaken mode
    ; target-rename = λ mode → modeRename-suc-weakenCast
    ; target-seal-source = seal-source-suc
    }
  where
    seal-source-suc :
      ∀ {μ} →
      (mode : CastMode μ) →
      (α : TyVar) →
      sealModeAllowed (weakenCastᵈ μ α) ≡ true →
      Product.Σ TyVar
        (λ b → sealModeAllowed (μ b) ≡ true × suc b ≡ α)
    seal-source-suc mode zero ()
    seal-source-suc mode (suc α) ok = α , ok , refl

castModeRenamer-ext :
  ∀ {ρ} →
  CastModeRenamer ρ →
  CastModeRenamer (extᵗ ρ)
castModeRenamer-ext {ρ = ρ} η =
  record
    { targetᵈ = target-ext
    ; target-mode = mode-ext
    ; target-rename = rename-ext
    ; target-seal-source = seal-source-ext
    }
  where
    target-ext : ∀ {μ} → CastMode μ → ModeEnv
    target-ext cast-tag-or-id = tag-or-idᵈ
    target-ext (cast-ext mode) =
      extᵈ (CastModeRenamer.targetᵈ η mode)
    target-ext (cast-gen mode) =
      genᵈ (CastModeRenamer.targetᵈ η mode)
    target-ext (cast-inst mode) =
      instᵈ (CastModeRenamer.targetᵈ η mode)
    target-ext (cast-weaken mode) =
      weakenCastᵈ (CastModeRenamer.targetᵈ η mode)

    mode-ext :
      ∀ {μ} →
      (mode : CastMode μ) →
      CastMode (target-ext mode)
    mode-ext cast-tag-or-id = cast-tag-or-id
    mode-ext (cast-ext mode) =
      cast-ext (CastModeRenamer.target-mode η mode)
    mode-ext (cast-gen mode) =
      cast-gen (CastModeRenamer.target-mode η mode)
    mode-ext (cast-inst mode) =
      cast-inst (CastModeRenamer.target-mode η mode)
    mode-ext (cast-weaken mode) =
      cast-weaken (CastModeRenamer.target-mode η mode)

    rename-ext :
      ∀ {μ} →
      (mode : CastMode μ) →
      ModeRename (extᵗ ρ) μ (target-ext mode)
    rename-ext cast-tag-or-id X = refl
    rename-ext (cast-ext mode) =
      ModeRename-ext (CastModeRenamer.target-rename η mode)
    rename-ext (cast-gen mode) =
      ModeRename-gen (CastModeRenamer.target-rename η mode)
    rename-ext (cast-inst mode) =
      ModeRename-inst (CastModeRenamer.target-rename η mode)
    rename-ext (cast-weaken mode) zero =
      refl
    rename-ext (cast-weaken mode) (suc X) =
      CastModeRenamer.target-rename η mode X

    seal-source-ext :
      ∀ {μ} →
      (mode : CastMode μ) →
      (α : TyVar) →
      sealModeAllowed (target-ext mode α) ≡ true →
      Product.Σ TyVar
        (λ b → sealModeAllowed (μ b) ≡ true × extᵗ ρ b ≡ α)
    seal-source-ext cast-tag-or-id α ()
    seal-source-ext (cast-ext mode) zero ()
    seal-source-ext (cast-ext mode) (suc α) ok
        with CastModeRenamer.target-seal-source η mode α ok
    seal-source-ext (cast-ext mode) (suc α) ok
        | b , b-ok , b↦α =
      suc b , b-ok , cong suc b↦α
    seal-source-ext (cast-gen mode) zero ()
    seal-source-ext (cast-gen mode) (suc α) ok
        with CastModeRenamer.target-seal-source η mode α ok
    seal-source-ext (cast-gen mode) (suc α) ok
        | b , b-ok , b↦α =
      suc b , b-ok , cong suc b↦α
    seal-source-ext (cast-inst mode) zero ok =
      zero , refl , refl
    seal-source-ext (cast-inst mode) (suc α) ok
        with CastModeRenamer.target-seal-source η mode α ok
    seal-source-ext (cast-inst mode) (suc α) ok
        | b , b-ok , b↦α =
      suc b , b-ok , cong suc b↦α
    seal-source-ext (cast-weaken mode) zero ()
    seal-source-ext (cast-weaken mode) (suc α) ok
        with CastModeRenamer.target-seal-source η mode α ok
    seal-source-ext (cast-weaken mode) (suc α) ok
        | b , b-ok , b↦α =
      suc b , b-ok , cong suc b↦α

------------------------------------------------------------------------
-- Structural properties of refined term typing
------------------------------------------------------------------------

term-weaken :
  ∀ {Δ Δ′ Σ Σ′ Γ M A} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
term-weaken Δ≤Δ′ incl no•-` (⊢` h) = ⊢` h
term-weaken Δ≤Δ′ incl (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ (WfTy-weakenᵗ hA Δ≤Δ′) (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-· noL noM) (⊢· hL hM) =
  ⊢· (term-weaken Δ≤Δ′ incl noL hL)
     (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-Λ noM) (⊢Λ vV hV) =
  ⊢Λ vV
    (term-weaken (s≤s Δ≤Δ′) (renameStoreᵗ-incl suc incl) noM hV)
term-weaken Δ≤Δ′ incl (no•-ν noL) (⊢ν↑ hA hL c⊢) =
  ⊢ν↑
    (WfTy-weakenᵗ hA Δ≤Δ′)
    (term-weaken Δ≤Δ′ incl noL hL)
    (conversion↑-weaken
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
term-weaken Δ≤Δ′ incl (no•-ν noL) (⊢ν⊑ mode seal★ hL c⊢) =
  ⊢ν⊑ mode
    (seal★-weaken (StoreIncl-cons (renameStoreᵗ-incl suc incl)) seal★)
    (term-weaken Δ≤Δ′ incl noL hL)
    (widen-weaken
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
term-weaken Δ≤Δ′ incl no•-$ (⊢$ κ) = ⊢$ κ
term-weaken Δ≤Δ′ incl (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (term-weaken Δ≤Δ′ incl noL hL) op
      (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩↑ c⊢ hM) =
  ⊢⟨⟩↑ (conversion↑-weaken Δ≤Δ′ incl c⊢)
        (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩↓ c⊢ hM) =
  ⊢⟨⟩↓ (conversion↓-weaken Δ≤Δ′ incl c⊢)
        (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩⊒ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊒ mode (seal★-weaken incl seal★)
           (narrow-weaken Δ≤Δ′ incl c⊢)
           (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩⊑ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊑ mode (seal★-weaken incl seal★)
           (widen-weaken Δ≤Δ′ incl c⊢)
           (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl no•-blame (⊢blame hA) =
  ⊢blame (WfTy-weakenᵗ hA Δ≤Δ′)

term-weaken-suc :
  ∀ {Δ Σ Γ M A α C} →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  suc Δ ∣ (α , C) ∷ Σ ∣ Γ ⊢ M ⦂ A
term-weaken-suc {Δ = Δ} noM hM =
  term-weaken (n≤1+n Δ) StoreIncl-drop noM hM

typing-renameᵀ :
  ∀ {Δ Δ′ Σ Γ M A ρ ψ} →
  TyRenameWf Δ Δ′ ρ →
  RenameLeftInverse ρ ψ →
  CastModeRenamer ρ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ
    ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η no•-` (⊢` h) =
  ⊢` (lookup-map-renameᵗ h)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η (no•-ƛ noM)
    (⊢ƛ hA hM) =
  ⊢ƛ (renameᵗ-preserves-WfTy hA hρ)
      (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η
    (no•-· noL noM) (⊢· hL hM) =
  ⊢· (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noL hL)
     (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    {ψ = ψ} hρ inv η (no•-Λ noM)
    (⊢Λ {M = M} {A = A} vM hM) =
  ⊢Λ
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vM)
    (subst
      (λ Γ′ → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Γ′
        ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameᵗ-⤊ ρ Γ)
      (subst
        (λ Σ′ →
          suc Δ′ ∣ Σ′ ∣ map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ)
          ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (typing-renameᵀ
          {ρ = extᵗ ρ} {ψ = extᵗ ψ}
          (TyRenameWf-ext hρ)
          (RenameLeftInverse-ext inv)
          (castModeRenamer-ext η)
          noM
          hM)))
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    {ψ = ψ} hρ inv η (no•-ν noL)
    (⊢ν↑ {L = L} {A = A} {B = B} {C = C} {c = c} {μ = μ}
      hA hL c⊢) =
  ⊢ν↑ {μ = λ Y → μ (extᵗ ψ Y)}
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noL hL)
    (subst
      (λ T →
        (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′
          ∣ (zero , ⇑ᵗ (renameᵗ ρ A)) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) C ↑ˢ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ →
          (λ Y → μ (extᵗ ψ Y)) ∣ suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) C ↑ˢ renameᵗ (extᵗ ρ) (⇑ᵗ B))
        (renameStoreᵗ-ext-suc-cons-comm ρ Σ A)
        (conversion↑-renameᵗ
          (TyRenameWf-ext hρ)
          (modeRename-left-inverse
            {ρ = extᵗ ρ} {ψ = extᵗ ψ} (RenameLeftInverse-ext inv))
          c⊢)))
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    {ψ = ψ} hρ inv η (no•-ν noL)
    (⊢ν⊑ {L = L} {B = B} {C = C} {c = c} {μ = μ}
      mode seal★ hL c⊢) =
  ⊢ν⊑ (CastModeRenamer.target-mode η mode)
    (subst
      (λ Σ′ →
        SealModeStore★ (instᵈ (CastModeRenamer.targetᵈ η mode)) Σ′)
      (renameStoreᵗ-ext-suc-cons-comm ρ Σ ★)
      (castModeRenamer-seal★ (castModeRenamer-ext η)
        (cast-inst mode) seal★))
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noL hL)
    (subst
      (λ T →
        instᵈ (CastModeRenamer.targetᵈ η mode) ∣ suc Δ′
          ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
          ∶ renameᵗ (extᵗ ρ) C ⊑ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ →
          instᵈ (CastModeRenamer.targetᵈ η mode) ∣ suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) c
            ∶ renameᵗ (extᵗ ρ) C ⊑ renameᵗ (extᵗ ρ) (⇑ᵗ B))
        (renameStoreᵗ-ext-suc-cons-comm ρ Σ ★)
        (widen-renameᵗ
          (TyRenameWf-ext hρ)
          (ModeRename-inst (CastModeRenamer.target-rename η mode))
          c⊢)))
typing-renameᵀ {ρ = ρ} hρ inv η no•-$ (⊢$ κ) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ $ κ ⦂ T)
        (constTy-renameᵗ ρ κ)
        (⊢$ κ)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η
    (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noL hL) op
      (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η
    (no•-⟨⟩ noM) (⊢⟨⟩↑ {μ = μ} c⊢ hM) =
  ⊢⟨⟩↑ {μ = λ Y → μ (ψ Y)}
    (conversion↑-renameᵗ hρ
      (modeRename-left-inverse {ρ = ρ} {ψ = ψ} inv)
      c⊢)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η
    (no•-⟨⟩ noM) (⊢⟨⟩↓ {μ = μ} c⊢ hM) =
  ⊢⟨⟩↓ {μ = λ Y → μ (ψ Y)}
    (conversion↓-renameᵗ hρ
      (modeRename-left-inverse {ρ = ρ} {ψ = ψ} inv)
      c⊢)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η (no•-⟨⟩ noM)
    (⊢⟨⟩⊒ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊒
    (CastModeRenamer.target-mode η mode)
    (castModeRenamer-seal★ η mode seal★)
    (narrow-renameᵗ hρ (CastModeRenamer.target-rename η mode) c⊢)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η (no•-⟨⟩ noM)
    (⊢⟨⟩⊑ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊑
    (CastModeRenamer.target-mode η mode)
    (castModeRenamer-seal★ η mode seal★)
    (widen-renameᵗ hρ (CastModeRenamer.target-rename η mode) c⊢)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η no•-blame (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

typing-renameˣ :
  ∀ {Δ Σ Γ Γ′ M A ρ} →
  RenameWf Γ Γ′ ρ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ Γ′ ⊢ renameˣᵐ ρ M ⦂ A
typing-renameˣ hρ (⊢` h) = ⊢` (hρ h)
typing-renameˣ hρ (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-renameˣ (RenameWf-ext hρ) hM)
typing-renameˣ hρ (⊢· hL hM) =
  ⊢· (typing-renameˣ hρ hL) (typing-renameˣ hρ hM)
typing-renameˣ {ρ = ρ} hρ (⊢Λ vM hM) =
  ⊢Λ (renameˣᵐ-preserves-Value ρ vM)
      (typing-renameˣ (RenameWf-⤊ hρ) hM)
typing-renameˣ {ρ = ρ} hρ (⊢• {V = V} eqΔ eqΣ hC vV noV hV) =
  subst
    (λ M → _ ∣ _ ∣ _ ⊢ M • ⦂ _)
    (sym (renameˣ-renameᵗᵐ ρ suc V))
    (⊢• eqΔ eqΣ hC
      (renameˣᵐ-preserves-Value ρ vV)
      (renameˣᵐ-preserves-No• ρ noV)
      (typing-renameˣ hρ hV))
typing-renameˣ hρ (⊢ν↑ hA hL c⊢) =
  ⊢ν↑ hA (typing-renameˣ hρ hL) c⊢
typing-renameˣ hρ (⊢ν⊑ mode seal★ hL c⊢) =
  ⊢ν⊑ mode seal★ (typing-renameˣ hρ hL) c⊢
typing-renameˣ hρ (⊢$ κ) = ⊢$ κ
typing-renameˣ hρ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩↑ c⊢ hM) =
  ⊢⟨⟩↑ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩↓ c⊢ hM) =
  ⊢⟨⟩↓ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩⊒ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊒ mode seal★ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩⊑ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊑ mode seal★ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢blame hA) = ⊢blame hA

typing-renameˣ-shift :
  ∀ {Δ Σ Γ M A B} →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ (B ∷ Γ) ⊢ renameˣᵐ suc M ⦂ A
typing-renameˣ-shift hM =
  typing-renameˣ (λ h → S h) hM

SubstWf : TyCtx → Store → Ctx → Ctx → Substˣ → Set₁
SubstWf Δ Σ Γ Γ′ σ =
  ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

SubstNo• : Ctx → Substˣ → Set₁
SubstNo• Γ σ = ∀ {x A} → Γ ∋ x ⦂ A → No• (σ x)

SubstWf-exts :
  ∀ {Δ Σ Γ Γ′ B σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstWf Δ Σ (B ∷ Γ) (B ∷ Γ′) (extˢˣ σ)
SubstWf-exts hσ Z = ⊢` Z
SubstWf-exts hσ (S h) = typing-renameˣ-shift (hσ h)

SubstNo•-exts :
  ∀ {Γ B σ} →
  SubstNo• Γ σ →
  SubstNo• (B ∷ Γ) (extˢˣ σ)
SubstNo•-exts hσ Z = no•-`
SubstNo•-exts hσ (S h) = renameˣᵐ-preserves-No• suc (hσ h)

SubstNo•-⇑ :
  ∀ {Γ σ} →
  SubstNo• Γ σ →
  SubstNo• (⤊ᵗ Γ) (↑ᵗᵐ σ)
SubstNo•-⇑ hσ h =
  lookup-⤊-elim₀
    (λ hA eq → renameᵗᵐ-preserves-No• suc (hσ hA))
    h

SubstWf-⇑ :
  ∀ {Δ Σ Γ Γ′ σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstNo• Γ σ →
  SubstWf (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) (⤊ᵗ Γ′) (↑ᵗᵐ σ)
SubstWf-⇑ hσ noσ h =
  lookup-⤊-elim
    (λ hA eq →
      subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
            (sym eq)
            (typing-renameᵀ {ρ = suc} {ψ = predᵗ}
              TyRenameWf-suc RenameLeftInverse-suc castModeRenamer-suc
              (noσ hA)
              (hσ hA)))
    h

substˣᵐ-preserves-No•-typed′ :
  ∀ {Δ Σ Γ M A σ} →
  SubstNo• Γ σ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  No• (substˣᵐ σ M)
substˣᵐ-preserves-No•-typed′ noσ noM M⊢ =
  substˣᵐ-preserves-No•-typed noσ noM (forget M⊢)

typing-substˣ :
  ∀ {Δ Σ Γ Γ′ M A σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstNo• Γ σ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ Γ′ ⊢ substˣᵐ σ M ⦂ A
typing-substˣ hσ noσ no•-` (⊢` h) = hσ h
typing-substˣ hσ noσ (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-substˣ (SubstWf-exts hσ) (SubstNo•-exts noσ) noM hM)
typing-substˣ hσ noσ (no•-· noL noM) (⊢· hL hM) =
  ⊢· (typing-substˣ hσ noσ noL hL)
     (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-Λ noM) (⊢Λ vM hM) =
  ⊢Λ (substˣᵐ-preserves-Value _ vM)
    (typing-substˣ
      (SubstWf-⇑ hσ noσ)
      (SubstNo•-⇑ noσ)
      noM
      hM)
typing-substˣ hσ noσ (no•-ν noL) (⊢ν↑ hA hL c⊢) =
  ⊢ν↑ hA (typing-substˣ hσ noσ noL hL) c⊢
typing-substˣ hσ noσ (no•-ν noL) (⊢ν⊑ mode seal★ hL c⊢) =
  ⊢ν⊑ mode seal★ (typing-substˣ hσ noσ noL hL) c⊢
typing-substˣ hσ noσ no•-$ (⊢$ κ) = ⊢$ κ
typing-substˣ hσ noσ (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (typing-substˣ hσ noσ noL hL) op
      (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩↑ c⊢ hM) =
  ⊢⟨⟩↑ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩↓ c⊢ hM) =
  ⊢⟨⟩↓ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩⊒ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊒ mode seal★ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩⊑ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊑ mode seal★ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ no•-blame (⊢blame hA) = ⊢blame hA

singleSubstWf :
  ∀ {Δ Σ Γ A V} →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  SubstWf Δ Σ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢` h

typing-single-subst :
  ∀ {Δ Σ Γ N V A B} →
  No• N →
  No• V →
  Δ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Δ ∣ Σ ∣ Γ ⊢ N [ V ] ⦂ B
typing-single-subst noN noV hN hV =
  typing-substˣ (singleSubstWf hV) (singleSubstNo• noV) noN hN

conversion↑-wf :
  ∀ {μ Δ Σ A B c} →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
  WfTy Δ A × WfTy Δ B
conversion↑-wf wfΣ c⊢ =
  coercion-wfᵐ wfΣ (conversion↑⇒coercion c⊢)

conversion↓-wf :
  ∀ {μ Δ Σ A B c} →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
  WfTy Δ A × WfTy Δ B
conversion↓-wf wfΣ c⊢ =
  coercion-wfᵐ wfΣ (conversion↓⇒coercion c⊢)

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
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩↑ (conv↑-id hA ok) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩↓ (conv↓-id hA ok) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★ (cast-id hA ok , cross (id-＇ α)) hV)
    (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★ (cast-id hA ok , cross (id-‵ ι)) hV)
    (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★ (cast-id hA ok , id★) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★ (cast-id hA ok , cross (id-＇ α)) hV)
    (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★ (cast-id hA ok , cross (id-‵ ι)) hV)
    (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★ (cast-id hA ok , id★) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★
      (cast-seq p⊢ q⊢ , gG ？︔ gⁿ) hV)
    (β-seq vV) =
  ⊢⟨⟩⊒ mode seal★ (q⊢ , cross (strictCrossⁿ→cross gⁿ))
    (⊢⟨⟩⊒ mode seal★ (p⊢ , untag gG) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★
      (cast-seq p⊢ q⊢ , fun-untag-gen safe) hV)
    (β-seq vV) =
  ⊢⟨⟩⊒ mode seal★ (q⊢ , gen safe)
    (⊢⟨⟩⊒ mode seal★ (p⊢ , untag ★⇒★) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ {μ = μ} mode seal★
      (cast-seq p⊢ (cast-seal hA α∈Σ ok) , sⁿ ︔seal α) hV)
    (β-seq vV) =
  ⊢⟨⟩↓ (conv↓-seal {μ = μ} hA α∈Σ ok)
    (⊢⟨⟩⊒ mode seal★ (p⊢ , strictⁿ→narrow sⁿ) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★
      (cast-seq p⊢ q⊢ , gʷ ︔ gG !) hV)
    (β-seq vV) =
  ⊢⟨⟩⊑ mode seal★ (q⊢ , tag gG)
    (⊢⟨⟩⊑ mode seal★ (p⊢ , cross (strictCrossʷ→cross gʷ)) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★
      (cast-seq p⊢ q⊢ , inst-fun-tag safe) hV)
    (β-seq vV) =
  ⊢⟨⟩⊑ mode seal★ (q⊢ , tag ★⇒★)
    (⊢⟨⟩⊑ mode seal★ (p⊢ , inst safe) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ {μ = μ} mode seal★
      (cast-seq (cast-unseal hA α∈Σ ok) q⊢ , unseal︔_ α sʷ) hV)
    (β-seq vV) =
  ⊢⟨⟩⊑ mode seal★ (q⊢ , strictʷ→widen sʷ)
    (⊢⟨⟩↑ (conv↑-unseal {μ = μ} hA α∈Σ ok) hV)
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩↑ (conv↑-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩↑ q⊢ (⊢· hV (⊢⟨⟩↓ p⊢ hW))
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩↓ (conv↓-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩↓ q⊢ (⊢· hV (⊢⟨⟩↑ p⊢ hW))
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩⊒ mode seal★
      (cast-fun p⊢ q⊢ , cross (pʷ ↦ qⁿ)) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩⊒ mode seal★ (q⊢ , qⁿ)
    (⊢· hV (⊢⟨⟩⊑ mode seal★ (p⊢ , pʷ) hW))
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩⊑ mode seal★
      (cast-fun p⊢ q⊢ , cross (pⁿ ↦ qʷ)) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩⊑ mode seal★ (q⊢ , qʷ)
    (⊢· hV (⊢⟨⟩⊒ mode seal★ (p⊢ , pⁿ) hW))
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★
      (cast-inst {A = A} {B = B} {s = c} hB occ c⊢ , inst cʷ) V⊢)
    (β-inst vV) =
  ⊢ν⊑ mode (seal★-inst seal★) V⊢
    (c⊢ , dualGenSafe→widening cʷ)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★ (cast-inst hB occ c⊢ , cross ()) V⊢)
    (β-inst vV)
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩↑ (conv↑-unseal hB αB∈Σ _)
      (⊢⟨⟩↓ (conv↓-seal hA αA∈Σ _) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩↑ (conv↑-unseal hB αB∈Σ _)
      (⊢⟨⟩⊒ mode seal★ (cast-seal hA αA∈Σ _ , sealⁿ A α) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩↑ (conv↑-unseal hB αB∈Σ _)
      (⊢⟨⟩⊑ mode seal★ (c⊢ , cross ()) hV))
    (seal-unseal vV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode seal★ (cast-unseal hB αB∈Σ _ , cross ()) hV)
    (seal-unseal vV)
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊑ mode seal★ (cast-unseal hB αB∈Σ _ , unsealʷ α B)
      (⊢⟨⟩↓ (conv↓-seal hA αA∈Σ _) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊑ mode seal★ (cast-unseal hB αB∈Σ _ , unsealʷ α B)
      (⊢⟨⟩⊒ mode′ seal★′ (cast-seal hA αA∈Σ _ , sealⁿ A α) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊑ mode seal★ (cast-unseal hB αB∈Σ _ , unsealʷ α B)
      (⊢⟨⟩⊑ mode′ seal★′ (c⊢ , cross ()) hV))
    (seal-unseal vV)
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊒ mode seal★ (cast-untag hG gG _ , untag gG′)
      (⊢⟨⟩⊑ mode′ seal★′ (cast-tag hG′ gG″ _ , tag gG‴) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊒ mode seal★ (cast-untag hG gG _ , untag gG′)
      (⊢⟨⟩⊒ mode′ seal★′ (c⊢ , cross ()) hV))
    (tag-untag-ok vV)
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊒ mode seal★ (cast-untag hH gH _ , untag gH′)
      (⊢⟨⟩⊑ mode′ seal★′ (cast-tag hG gG _ , tag gG′) hV))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊒ mode seal★ (cast-untag hH gH _ , untag gH′)
      (⊢⟨⟩⊒ mode′ seal★′ (c⊢ , cross ()) hV))
    (tag-untag-bad vV G≢H)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★ (cast-untag hH gH _ , cross ()) hV)
    (tag-untag-ok vV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode seal★ (cast-untag hH gH _ , cross ()) hV)
    (tag-untag-bad vV G≢H)
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
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩↑ c⊢ (⊢blame hA)) blame-⟨⟩
    with conversion↑-wf (at wfΣ) c⊢
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩↑ c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩↓ c⊢ (⊢blame hA)) blame-⟨⟩
    with conversion↓-wf (at wfΣ) c⊢
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩↓ c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊒ mode seal★ c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wfᵐ (at wfΣ) (proj₁ c⊢)
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊒ mode seal★ c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊑ mode seal★ c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wfᵐ (at wfΣ) (proj₁ c⊢)
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊑ mode seal★ c⊢ (⊢blame hA)) blame-⟨⟩
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
pure-preserves-No•-typed wfΣ noM M⊢ red =
  NuPreservation.pure-preserves-No•-typed wfΣ noM (forget M⊢) red

StoreWfAt-tail :
  ∀ {Δ α A Σ} →
  StoreWfAt Δ ((α , A) ∷ Σ) →
  StoreWfAt Δ Σ
StoreWfAt-tail wfΣ =
  record
    { bound = λ x∈ → bound wfΣ (there x∈)
    ; wfTy = λ x∈ → wfTy wfΣ (there x∈)
    }

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
bullet-pure-preservation wfΣ hC (vW ⟨ G ! ⟩) noV W⊢ ()
bullet-pure-preservation wfΣ hC (vW ⟨ seal A α ⟩) noV W⊢ ()
bullet-pure-preservation wfΣ hC (vW ⟨ c ↦ d ⟩) noV W⊢ ()
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩↑ (conv↑-all c⊢) W⊢) (β-∀• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ ((⇑ᵗᵐ W) •) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩↑
      (conversion↑-weaken ≤-refl StoreIncl-drop c⊢)
      (⊢• refl refl hA vW noW W⊢))
  where
    hA : WfTy _ _
    hA = proj₁ (conversion↑-wf (StoreWfAt-tail (at wfΣ)) c⊢)
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩↓ (conv↓-all c⊢) W⊢) (β-∀• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ ((⇑ᵗᵐ W) •) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩↓
      (conversion↓-weaken ≤-refl StoreIncl-drop c⊢)
      (⊢• refl refl hA vW noW W⊢))
  where
    hA : WfTy _ _
    hA = proj₁ (conversion↓-wf (StoreWfAt-tail (at wfΣ)) c⊢)
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩⊒ mode seal★ (cast-all c⊢ , cross (`∀ cⁿ)) W⊢)
    (β-∀• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ ((⇑ᵗᵐ W) •) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩⊒
      (cast-ext mode)
      (seal★-weaken StoreIncl-drop (seal★-ext-shift seal★))
      (narrow-weaken ≤-refl StoreIncl-drop (c⊢ , cⁿ))
      (⊢• refl refl hA vW noW W⊢))
  where
    hA : WfTy _ _
    hA = proj₁ (coercion-wfᵐ (StoreWfAt-tail (at wfΣ)) c⊢)
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩⊑ mode seal★ (cast-all c⊢ , cross (`∀ cʷ)) W⊢)
    (β-∀• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ ((⇑ᵗᵐ W) •) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩⊑
      (cast-ext mode)
      (seal★-weaken StoreIncl-drop (seal★-ext-shift seal★))
      (widen-weaken ≤-refl StoreIncl-drop (c⊢ , cʷ))
      (⊢• refl refl hA vW noW W⊢))
  where
    hA : WfTy _ _
    hA = proj₁ (coercion-wfᵐ (StoreWfAt-tail (at wfΣ)) c⊢)
bullet-pure-preservation {C = C} wfΣ hC
    (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩⊒ mode seal★ (cast-gen hA occ c⊢ , gen cⁿ) W⊢)
    (β-gen• vW↑) =
  subst
    (λ d → _ ∣ _ ∣ [] ⊢ (⇑ᵗᵐ W) ⟨ d ⟩ ⦂ C)
    (sym (open0-ext-suc-cancelᶜ c))
    (⊢⟨⟩⊒
      (cast-gen mode)
      (seal★-weaken StoreIncl-drop (seal★-gen-shift seal★))
      (narrow-weaken ≤-refl StoreIncl-drop
        (c⊢ , genSafe→narrowing cⁿ))
      (term-weaken ≤-refl StoreIncl-drop
        (renameᵗᵐ-preserves-No• suc noW)
        (typing-renameᵀ {ρ = suc} {ψ = predᵗ}
          TyRenameWf-suc RenameLeftInverse-suc castModeRenamer-suc
          noW
          W⊢)))
bullet-pure-preservation wfΣ hC
    (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩↑ () W⊢) (β-gen• vW↑)
bullet-pure-preservation wfΣ hC
    (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩↓ () W⊢) (β-gen• vW↑)
bullet-pure-preservation wfΣ hC
    (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩⊑ mode seal★ (c⊢ , cross ()) W⊢) (β-gen• vW↑)

pure-preservation-runtime :
  ∀ {Δ Σ M N A} →
  StoreWf Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  RuntimeOK M →
  M —→ N →
  Δ ∣ Σ ∣ [] ⊢ N ⦂ A
pure-preservation-runtime wfΣ
    (⊢• refl refl hC vV noV V⊢) okM red =
  bullet-pure-preservation wfΣ hC vV noV V⊢ red
pure-preservation-runtime wfΣ M⊢ (ok-no noM) red =
  pure-preservation wfΣ noM M⊢ red
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM) (β vV) =
  pure-preservation wfΣ
    (no•-· (NuPreservation.value-runtime-No• (ƛ _) okL) noM)
    M⊢
    (β vV)
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM)
    (β-↦ vV vW) =
  pure-preservation wfΣ
    (no•-·
      (NuPreservation.value-runtime-No• (vV ⟨ _ ↦ _ ⟩) okL)
      noM)
    M⊢
    (β-↦ vV vW)
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM) blame-·₁ =
  pure-preservation wfΣ (no•-· no•-blame noM) M⊢ blame-·₁
pure-preservation-runtime wfΣ M⊢ (ok-·₁ okL noM)
    (blame-·₂ vV) =
  pure-preservation wfΣ
    (no•-· (NuPreservation.value-runtime-No• vV okL) noM)
    M⊢
    (blame-·₂ vV)
pure-preservation-runtime wfΣ M⊢ (ok-·₂ vV noV okM) (β vW) =
  pure-preservation wfΣ
    (no•-· noV (NuPreservation.value-runtime-No• vW okM))
    M⊢
    (β vW)
pure-preservation-runtime wfΣ M⊢ (ok-·₂ vV noV okM)
    (β-↦ vV′ vW) =
  pure-preservation wfΣ
    (no•-· noV (NuPreservation.value-runtime-No• vW okM))
    M⊢
    (β-↦ vV′ vW)
pure-preservation-runtime wfΣ M⊢ (ok-·₂ vV noV okM)
    (blame-·₂ vV′) =
  pure-preservation wfΣ
    (no•-· noV no•-blame)
    M⊢
    (blame-·₂ vV′)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (β-id vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (NuPreservation.value-runtime-No• vV okM))
    M⊢
    (β-id vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (β-seq vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (NuPreservation.value-runtime-No• vV okM))
    M⊢
    (β-seq vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (β-inst vV) =
  pure-preservation wfΣ
    (no•-⟨⟩ (NuPreservation.value-runtime-No• vV okM))
    M⊢
    (β-inst vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (seal-unseal vV) =
  pure-preservation wfΣ
    (no•-⟨⟩
      (NuPreservation.value-runtime-No• (vV ⟨ seal _ _ ⟩) okM))
    M⊢
    (seal-unseal vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) (tag-untag-ok vV) =
  pure-preservation wfΣ
    (no•-⟨⟩
      (NuPreservation.value-runtime-No• (vV ⟨ _ ! ⟩) okM))
    M⊢
    (tag-untag-ok vV)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM)
    (tag-untag-bad vV G≢H) =
  pure-preservation wfΣ
    (no•-⟨⟩
      (NuPreservation.value-runtime-No• (vV ⟨ _ ! ⟩) okM))
    M⊢
    (tag-untag-bad vV G≢H)
pure-preservation-runtime wfΣ M⊢ (ok-⟨⟩ okM) blame-⟨⟩ =
  pure-preservation wfΣ (no•-⟨⟩ no•-blame) M⊢ blame-⟨⟩
pure-preservation-runtime wfΣ M⊢ (ok-⊕₁ okL noM) δ-⊕ =
  pure-preservation wfΣ
    (no•-⊕ (NuPreservation.value-runtime-No• ($ _) okL) noM)
    M⊢
    δ-⊕
pure-preservation-runtime wfΣ M⊢ (ok-⊕₁ okL noM) blame-⊕₁ =
  pure-preservation wfΣ (no•-⊕ no•-blame noM) M⊢ blame-⊕₁
pure-preservation-runtime wfΣ M⊢ (ok-⊕₁ okL noM)
    (blame-⊕₂ vL) =
  pure-preservation wfΣ
    (no•-⊕ (NuPreservation.value-runtime-No• vL okL) noM)
    M⊢
    (blame-⊕₂ vL)
pure-preservation-runtime wfΣ M⊢ (ok-⊕₂ vL noL okM) δ-⊕ =
  pure-preservation wfΣ
    (no•-⊕ noL (NuPreservation.value-runtime-No• ($ _) okM))
    M⊢
    δ-⊕
pure-preservation-runtime wfΣ M⊢ (ok-⊕₂ vL noL okM)
    (blame-⊕₂ vL′) =
  pure-preservation wfΣ
    (no•-⊕ noL no•-blame)
    M⊢
    (blame-⊕₂ vL′)

------------------------------------------------------------------------
-- Store-change preservation
------------------------------------------------------------------------

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
      castModeRenamer-suc
      noM
      M⊢)

applyTerm-typing-shiftable :
  ∀ {χ : StoreChange}{Δ Σ M A} →
  StoreWfAt Δ Σ →
  Shiftable χ M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ applyTerm χ M ⦂ applyTy χ A
applyTerm-typing-shiftable wfΣ shift-keep M⊢ = M⊢
applyTerm-typing-shiftable wfΣ (shift-bind noM) M⊢ =
  applyTerm-typing wfΣ noM M⊢

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

⊢ν↑-applyTy :
  ∀ χ {μ Δ Σ A B C L c} →
  WfTy (applyTyCtx χ Δ) (applyTy χ A) →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ L ⦂ applyTy χ (`∀ C) →
  μ ∣ suc (applyTyCtx χ Δ)
    ∣ (zero , ⇑ᵗ (applyTy χ A)) ∷ ⟰ᵗ (applyStore χ Σ)
    ⊢ c ∶ applyTyUnderTyBinder χ C ↑ˢ ⇑ᵗ (applyTy χ B) →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ []
    ⊢ ν (applyTy χ A) L c ⦂ applyTy χ B
⊢ν↑-applyTy keep hA hL c⊢ = ⊢ν↑ hA hL c⊢
⊢ν↑-applyTy (bind Aχ) hA hL c⊢ = ⊢ν↑ hA hL c⊢

⊢ν⊑-applyTy :
  ∀ χ {μ Δ Σ B C L c} →
  CastMode μ →
  SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ (applyStore χ Σ)) →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ L ⦂ applyTy χ (`∀ C) →
  instᵈ μ ∣ suc (applyTyCtx χ Δ)
    ∣ (zero , ★) ∷ ⟰ᵗ (applyStore χ Σ)
    ⊢ c ∶ applyTyUnderTyBinder χ C ⊑ ⇑ᵗ (applyTy χ B) →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ []
    ⊢ ν (applyTy χ ★) L c ⦂ applyTy χ B
⊢ν⊑-applyTy keep mode seal★ hL c⊢ = ⊢ν⊑ mode seal★ hL c⊢
⊢ν⊑-applyTy (bind Aχ) mode seal★ hL c⊢ = ⊢ν⊑ mode seal★ hL c⊢

applyConversion↑-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
  Product.Σ ModeEnv
    (λ ν →
      ν ∣ applyTyCtx χ Δ ∣ applyStore χ Σ
        ⊢ applyCoercion χ c ∶ applyTy χ A ↑ˢ applyTy χ B)
applyConversion↑-typing {χ = keep} {μ = μ} c⊢ = μ , c⊢
applyConversion↑-typing {χ = bind Aν} {μ = μ} c⊢ =
  weakenCastᵈ μ ,
    conversion↑-weaken ≤-refl StoreIncl-drop
      (conversion↑-renameᵗ
        TyRenameWf-suc
        modeRename-suc-weakenCast
        c⊢)

applyConversion↓-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
  Product.Σ ModeEnv
    (λ ν →
      ν ∣ applyTyCtx χ Δ ∣ applyStore χ Σ
        ⊢ applyCoercion χ c ∶ applyTy χ A ↓ˢ applyTy χ B)
applyConversion↓-typing {χ = keep} {μ = μ} c⊢ = μ , c⊢
applyConversion↓-typing {χ = bind Aν} {μ = μ} c⊢ =
  weakenCastᵈ μ ,
    conversion↓-weaken ≤-refl StoreIncl-drop
      (conversion↓-renameᵗ
        TyRenameWf-suc
        modeRename-suc-weakenCast
        c⊢)

applyNarrow-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c A B} →
  CastMode μ →
  SealModeStore★ μ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Product.Σ ModeEnv
    (λ ν →
      CastMode ν ×
      SealModeStore★ ν (applyStore χ Σ) ×
      ν ∣ applyTyCtx χ Δ ∣ applyStore χ Σ
        ⊢ applyCoercion χ c ∶ applyTy χ A ⊒ applyTy χ B)
applyNarrow-typing {χ = keep} {μ = μ} mode seal★ c⊢ =
  μ , mode , seal★ , c⊢
applyNarrow-typing {χ = bind Aν} {μ = μ} mode seal★ c⊢ =
  weakenCastᵈ μ ,
    cast-weaken mode ,
    seal★-weakenCast-bind seal★ ,
    narrow-weaken ≤-refl StoreIncl-drop
      (narrow-renameᵗ TyRenameWf-suc modeRename-suc-weakenCast c⊢)

applyWiden-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c A B} →
  CastMode μ →
  SealModeStore★ μ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  Product.Σ ModeEnv
    (λ ν →
      CastMode ν ×
      SealModeStore★ ν (applyStore χ Σ) ×
      ν ∣ applyTyCtx χ Δ ∣ applyStore χ Σ
        ⊢ applyCoercion χ c ∶ applyTy χ A ⊑ applyTy χ B)
applyWiden-typing {χ = keep} {μ = μ} mode seal★ c⊢ =
  μ , mode , seal★ , c⊢
applyWiden-typing {χ = bind Aν} {μ = μ} mode seal★ c⊢ =
  weakenCastᵈ μ ,
    cast-weaken mode ,
    seal★-weakenCast-bind seal★ ,
    widen-weaken ≤-refl StoreIncl-drop
      (widen-renameᵗ TyRenameWf-suc modeRename-suc-weakenCast c⊢)

applyConversion↑UnderTyBinder-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c B C Aν} →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ Aν) ∷ ⟰ᵗ Σ ⊢ c ∶ C ↑ˢ ⇑ᵗ B →
  Product.Σ ModeEnv
    (λ ν →
      ν ∣ suc (applyTyCtx χ Δ)
        ∣ (zero , ⇑ᵗ (applyTy χ Aν)) ∷ ⟰ᵗ (applyStore χ Σ)
        ⊢ applyCoercionUnderTyBinder χ c
        ∶ applyTyUnderTyBinder χ C ↑ˢ ⇑ᵗ (applyTy χ B))
applyConversion↑UnderTyBinder-typing {χ = keep} {μ = μ} c⊢ =
  μ , c⊢
applyConversion↑UnderTyBinder-typing {χ = bind Aχ} {μ = μ}
    {Δ = Δ} {Σ = Σ} {c = c} {B = Bout} {C = C} {Aν = Aν} c⊢ =
  νmode ,
    subst
      (λ T →
        νmode ∣ suc (suc Δ)
          ∣ (zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ)
          ⊢ renameᶜ (extᵗ suc) c ∶ renameᵗ (extᵗ suc) C ↑ˢ T)
      (renameᵗ-ext-suc-comm suc Bout)
      (conversion↑-weaken ≤-refl incl renamed-store)
  where
    νmode : ModeEnv
    νmode Y = μ (extᵗ predᵗ Y)

    renamed-store :
      νmode ∣ suc (suc Δ)
        ∣ (zero , ⇑ᵗ (⇑ᵗ Aν)) ∷ ⟰ᵗ (⟰ᵗ Σ)
        ⊢ renameᶜ (extᵗ suc) c
        ∶ renameᵗ (extᵗ suc) C ↑ˢ renameᵗ (extᵗ suc) (⇑ᵗ Bout)
    renamed-store =
      subst
        (λ Σ′ →
          νmode ∣ suc (suc Δ) ∣ Σ′
            ⊢ renameᶜ (extᵗ suc) c
            ∶ renameᵗ (extᵗ suc) C ↑ˢ renameᵗ (extᵗ suc) (⇑ᵗ Bout))
        (renameStoreᵗ-ext-suc-cons-comm suc Σ Aν)
        (conversion↑-renameᵗ
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

applyWidenInstUnderTyBinder-typing :
  ∀ {χ : StoreChange}{μ Δ Σ c B C} →
  CastMode μ →
  SealModeStore★ (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ) →
  instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ c ∶ C ⊑ ⇑ᵗ B →
  Product.Σ ModeEnv
    (λ ν →
      CastMode ν ×
      SealModeStore★ (instᵈ ν) ((zero , ★) ∷ ⟰ᵗ (applyStore χ Σ)) ×
      instᵈ ν ∣ suc (applyTyCtx χ Δ)
        ∣ (zero , ★) ∷ ⟰ᵗ (applyStore χ Σ)
        ⊢ applyCoercionUnderTyBinder χ c
        ∶ applyTyUnderTyBinder χ C ⊑ ⇑ᵗ (applyTy χ B))
applyWidenInstUnderTyBinder-typing {χ = keep} {μ = μ} mode seal★ c⊢ =
  μ , mode , seal★ , c⊢
applyWidenInstUnderTyBinder-typing {χ = bind Aχ} {μ = μ}
    {Δ = Δ} {Σ = Σ} {c = c} {B = Bout} {C = C} mode seal★ c⊢ =
  weakenCastᵈ μ ,
    cast-weaken mode ,
    seal★-inst-weakenCast-bind seal★ ,
    subst
      (λ T →
        instᵈ (weakenCastᵈ μ) ∣ suc (suc Δ)
          ∣ (zero , ★) ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ)
          ⊢ renameᶜ (extᵗ suc) c ∶ renameᵗ (extᵗ suc) C ⊑ T)
      (renameᵗ-ext-suc-comm suc Bout)
      (widen-weaken ≤-refl incl renamed-store)
  where
    renamed-store :
      instᵈ (weakenCastᵈ μ) ∣ suc (suc Δ)
        ∣ (zero , ★) ∷ ⟰ᵗ (⟰ᵗ Σ)
        ⊢ renameᶜ (extᵗ suc) c
        ∶ renameᵗ (extᵗ suc) C ⊑ renameᵗ (extᵗ suc) (⇑ᵗ Bout)
    renamed-store =
      subst
        (λ Σ′ →
          instᵈ (weakenCastᵈ μ) ∣ suc (suc Δ) ∣ Σ′
            ⊢ renameᶜ (extᵗ suc) c
            ∶ renameᵗ (extᵗ suc) C ⊑ renameᵗ (extᵗ suc) (⇑ᵗ Bout))
        (renameStoreᵗ-ext-suc-cons-comm suc Σ ★)
        (widen-renameᵗ
          (TyRenameWf-ext TyRenameWf-suc)
          (ModeRename-inst modeRename-suc-weakenCast)
          c⊢)

    incl :
      StoreIncl
        ((zero , ★) ∷ ⟰ᵗ (⟰ᵗ Σ))
        ((zero , ★) ∷ ⟰ᵗ ((zero , ⇑ᵗ Aχ) ∷ ⟰ᵗ Σ))
    incl (here refl) = here refl
    incl (there h) = there (there h)

runtime-preservation :
  ∀ {Δ Σ M N A χ} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  RuntimeOK N
runtime-preservation wfΣ okM M⊢ red =
  NuPreservation.runtime-preservation wfΣ okM (forget M⊢) red

store-preservation :
  ∀ {Δ Σ M N A χ} →
  StoreWf Δ Σ →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  StoreWf (applyTyCtx χ Δ) (applyStore χ Σ)
store-preservation wfΣ M⊢ red =
  NuPreservation.store-preservation wfΣ (forget M⊢) red

preservation :
  ∀ {Δ Σ M N A χ} →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  M —→[ χ ] N →
  applyTyCtx χ Δ ∣ applyStore χ Σ ∣ [] ⊢ N ⦂ applyTy χ A
preservation wfΣ okM M⊢ (pure-step red) =
  pure-preservation-runtime wfΣ M⊢ okM red
preservation wfΣ okM (⊢ν↑ hA V⊢ c⊢)
    (ν-step vV noV′) =
  ⊢⟨⟩↑ c⊢
    (⊢• refl refl (typing-wf-∀-body (at wfΣ) V⊢) vV noV′ V⊢)
preservation wfΣ okM (⊢ν⊑ mode seal★ V⊢ c⊢)
    (ν-step vV noV′) =
  ⊢⟨⟩⊑ (cast-inst mode) seal★ c⊢
    (⊢• refl refl (typing-wf-∀-body (at wfΣ) V⊢) vV noV′ V⊢)
preservation wfΣ okM (⊢· L⊢ M⊢)
    (ξ-·₁ {χ = χ} red shiftM) =
  ⊢·-applyTy χ
    (preservation wfΣ (NuPreservation.runtime-·₁ okM) L⊢ red)
    (applyTerm-typing-shiftable (at wfΣ) shiftM M⊢)
preservation wfΣ okM (⊢· V⊢ M⊢)
    (ξ-·₂ {χ = χ} vV shiftV red) =
  ⊢·-applyTy χ
    (applyTerm-typing-shiftable (at wfΣ) shiftV V⊢)
    (preservation wfΣ (NuPreservation.runtime-·₂ vV okM) M⊢ red)
preservation wfΣ okM (⊢⟨⟩↑ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    with applyConversion↑-typing {χ = χ} c⊢
preservation wfΣ okM (⊢⟨⟩↑ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    | μ′ , c′⊢ =
  ⊢⟨⟩↑ c′⊢ (preservation wfΣ (NuPreservation.runtime-⟨⟩ okM) M⊢ red)
preservation wfΣ okM (⊢⟨⟩↓ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    with applyConversion↓-typing {χ = χ} c⊢
preservation wfΣ okM (⊢⟨⟩↓ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    | μ′ , c′⊢ =
  ⊢⟨⟩↓ c′⊢ (preservation wfΣ (NuPreservation.runtime-⟨⟩ okM) M⊢ red)
preservation wfΣ okM (⊢⟨⟩⊒ mode seal★ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    with applyNarrow-typing {χ = χ} mode seal★ c⊢
preservation wfΣ okM (⊢⟨⟩⊒ mode seal★ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    | μ′ , mode′ , seal★′ , c′⊢ =
  ⊢⟨⟩⊒ mode′ seal★′ c′⊢
    (preservation wfΣ (NuPreservation.runtime-⟨⟩ okM) M⊢ red)
preservation wfΣ okM (⊢⟨⟩⊑ mode seal★ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    with applyWiden-typing {χ = χ} mode seal★ c⊢
preservation wfΣ okM (⊢⟨⟩⊑ mode seal★ c⊢ M⊢)
    (ξ-⟨⟩ {χ = χ} red)
    | μ′ , mode′ , seal★′ , c′⊢ =
  ⊢⟨⟩⊑ mode′ seal★′ c′⊢
    (preservation wfΣ (NuPreservation.runtime-⟨⟩ okM) M⊢ red)
preservation wfΣ okM (⊢ν↑ hA L⊢ c⊢)
    (ξ-ν {χ = χ} red)
    with applyConversion↑UnderTyBinder-typing {χ = χ} c⊢
preservation wfΣ okM (⊢ν↑ hA L⊢ c⊢)
    (ξ-ν {χ = χ} red)
    | μ′ , c′⊢ =
  ⊢ν↑-applyTy χ (renameA χ hA)
    (preservation wfΣ (NuPreservation.runtime-ν okM) L⊢ red)
    c′⊢
  where
    renameA : ∀ χ → WfTy _ _ → WfTy (applyTyCtx χ _) (applyTy χ _)
    renameA keep h = h
    renameA (bind Aχ) h = renameᵗ-preserves-WfTy h TyRenameWf-suc
preservation wfΣ okM (⊢ν⊑ mode seal★ L⊢ c⊢)
    (ξ-ν {χ = χ} red)
    with applyWidenInstUnderTyBinder-typing {χ = χ} mode seal★ c⊢
preservation wfΣ okM (⊢ν⊑ mode seal★ L⊢ c⊢)
    (ξ-ν {χ = χ} red)
    | μ′ , mode′ , seal★′ , c′⊢ =
  ⊢ν⊑-applyTy χ mode′ seal★′
    (preservation wfΣ (NuPreservation.runtime-ν okM) L⊢ red)
    c′⊢
preservation wfΣ okM (⊢ν↑ hA (⊢blame (wf∀ hC)) c⊢)
    blame-ν =
  ⊢blame
    (typing-wf (at wfΣ) closedCtxWf (⊢ν↑ hA (⊢blame (wf∀ hC)) c⊢))
preservation wfΣ okM (⊢ν⊑ mode seal★ (⊢blame (wf∀ hC)) c⊢)
    blame-ν =
  ⊢blame
    (typing-wf (at wfΣ) closedCtxWf
      (⊢ν⊑ mode seal★ (⊢blame (wf∀ hC)) c⊢))
preservation wfΣ okM (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₁ {χ = χ} red shiftM) =
  ⊢⊕-applyTy χ
    (preservation wfΣ (NuPreservation.runtime-⊕₁ okM) L⊢ red) op
    (applyTerm-typing-shiftable (at wfΣ) shiftM M⊢)
preservation wfΣ okM (⊢⊕ L⊢ op M⊢)
    (ξ-⊕₂ {χ = χ} vL shiftL red) =
  ⊢⊕-applyTy χ
    (applyTerm-typing-shiftable (at wfΣ) shiftL L⊢) op
    (preservation wfΣ (NuPreservation.runtime-⊕₂ vL okM) M⊢ red)

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

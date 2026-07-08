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
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero; z<s; s<s; z≤n; s≤s; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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

    target-zero :
      ∀ {μ} →
      (mode : CastMode μ) →
      mode≤ (μ zero) (targetᵈ mode zero) ≡ true

castModeRenamer-suc : CastModeRenamer suc
castModeRenamer-suc =
  record
    { targetᵈ = λ {μ} mode → weakenCastᵈ μ
    ; target-mode = λ mode → cast-weaken mode
    ; target-rename = λ mode → modeRename-suc-weakenCast
    ; target-zero = λ {μ} mode → modeIncl-refl {μ = μ} zero
    }

castModeRenamer-ext :
  ∀ {ρ} →
  CastModeRenamer ρ →
  CastModeRenamer (extᵗ ρ)
castModeRenamer-ext {ρ = ρ} η =
  record
    { targetᵈ = target-ext
    ; target-mode = mode-ext
    ; target-rename = rename-ext
    ; target-zero = zero-ext
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
      CastModeRenamer.target-zero η mode
    rename-ext (cast-weaken mode) (suc X) =
      CastModeRenamer.target-rename η mode X

    zero-ext :
      ∀ {μ} →
      (mode : CastMode μ) →
      mode≤ (μ zero) (target-ext mode zero) ≡ true
    zero-ext cast-tag-or-id = refl
    zero-ext (cast-ext mode) = refl
    zero-ext (cast-gen mode) = refl
    zero-ext (cast-inst mode) = refl
    zero-ext (cast-weaken mode) =
      CastModeRenamer.target-zero η mode

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
term-weaken Δ≤Δ′ incl (no•-ν noL) (⊢ν⊑ mode hL c⊢) =
  ⊢ν⊑ mode
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
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩⊒ mode c⊢ hM) =
  ⊢⟨⟩⊒ mode (narrow-weaken Δ≤Δ′ incl c⊢)
           (term-weaken Δ≤Δ′ incl noM hM)
term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩⊑ mode c⊢ hM) =
  ⊢⟨⟩⊑ mode (widen-weaken Δ≤Δ′ incl c⊢)
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
      mode hL c⊢) =
  ⊢ν⊑ (CastModeRenamer.target-mode η mode)
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
    (⊢⟨⟩⊒ mode c⊢ hM) =
  ⊢⟨⟩⊒
    (CastModeRenamer.target-mode η mode)
    (narrow-renameᵗ hρ (CastModeRenamer.target-rename η mode) c⊢)
    (typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η noM hM)
typing-renameᵀ {ρ = ρ} {ψ = ψ} hρ inv η (no•-⟨⟩ noM)
    (⊢⟨⟩⊑ mode c⊢ hM) =
  ⊢⟨⟩⊑
    (CastModeRenamer.target-mode η mode)
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
typing-renameˣ hρ (⊢ν⊑ mode hL c⊢) =
  ⊢ν⊑ mode (typing-renameˣ hρ hL) c⊢
typing-renameˣ hρ (⊢$ κ) = ⊢$ κ
typing-renameˣ hρ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩↑ c⊢ hM) =
  ⊢⟨⟩↑ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩↓ c⊢ hM) =
  ⊢⟨⟩↓ c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩⊒ mode c⊢ hM) =
  ⊢⟨⟩⊒ mode c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢⟨⟩⊑ mode c⊢ hM) =
  ⊢⟨⟩⊑ mode c⊢ (typing-renameˣ hρ hM)
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
typing-substˣ hσ noσ (no•-ν noL) (⊢ν⊑ mode hL c⊢) =
  ⊢ν⊑ mode (typing-substˣ hσ noσ noL hL) c⊢
typing-substˣ hσ noσ no•-$ (⊢$ κ) = ⊢$ κ
typing-substˣ hσ noσ (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (typing-substˣ hσ noσ noL hL) op
      (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩↑ c⊢ hM) =
  ⊢⟨⟩↑ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩↓ c⊢ hM) =
  ⊢⟨⟩↓ c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩⊒ mode c⊢ hM) =
  ⊢⟨⟩⊒ mode c⊢ (typing-substˣ hσ noσ noM hM)
typing-substˣ hσ noσ (no•-⟨⟩ noM) (⊢⟨⟩⊑ mode c⊢ hM) =
  ⊢⟨⟩⊑ mode c⊢ (typing-substˣ hσ noσ noM hM)
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
    (⊢⟨⟩⊒ mode (cast-id hA ok , cross (id-＇ α)) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode (cast-id hA ok , cross (id-‵ ι)) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode (cast-id hA ok , id★) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode (cast-id hA ok , cross (id-＇ α)) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode (cast-id hA ok , cross (id-‵ ι)) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode (cast-id hA ok , id★) hV) (β-id vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩↑ () hV) (β-seq vV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩↓ () hV) (β-seq vV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode
      (cast-seq p⊢ q⊢ , gG ？︔ gⁿ) hV)
    (β-seq vV) =
  ⊢⟨⟩⊒ mode (q⊢ , cross (strictCrossⁿ→cross gⁿ))
    (⊢⟨⟩⊒ mode (p⊢ , untag gG) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊒ mode
      (cast-seq p⊢ (cast-seal hA α∈Σ ok) , sⁿ ︔seal α) hV)
    (β-seq vV) =
  ⊢⟨⟩↓ (conv↓-seal hA α∈Σ ok)
    (⊢⟨⟩⊒ mode (p⊢ , strictⁿ→narrow sⁿ) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode
      (cast-seq p⊢ q⊢ , gʷ ︔ gG !) hV)
    (β-seq vV) =
  ⊢⟨⟩⊑ mode (q⊢ , tag gG)
    (⊢⟨⟩⊑ mode (p⊢ , cross (strictCrossʷ→cross gʷ)) hV)
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode
      (cast-seq (cast-unseal hA α∈Σ ok) q⊢ , unseal︔_ α sʷ) hV)
    (β-seq vV) =
  ⊢⟨⟩⊑ mode (q⊢ , strictʷ→widen sʷ)
    (⊢⟨⟩↑ (conv↑-unseal hA α∈Σ ok) hV)
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩↑ (conv↑-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩↑ q⊢ (⊢· hV (⊢⟨⟩↓ p⊢ hW))
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩↓ (conv↓-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩↓ q⊢ (⊢· hV (⊢⟨⟩↑ p⊢ hW))
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩⊒ mode
      (cast-fun p⊢ q⊢ , cross (pʷ ↦ qⁿ)) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩⊒ mode (q⊢ , qⁿ)
    (⊢· hV (⊢⟨⟩⊑ mode (p⊢ , pʷ) hW))
pure-preservation wfΣ (no•-· (no•-⟨⟩ noV) noW)
    (⊢· (⊢⟨⟩⊑ mode
      (cast-fun p⊢ q⊢ , cross (pⁿ ↦ qʷ)) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩⊑ mode (q⊢ , qʷ)
    (⊢· hV (⊢⟨⟩⊒ mode (p⊢ , pⁿ) hW))
pure-preservation wfΣ (no•-⟨⟩ noV)
    (⊢⟨⟩⊑ mode
      (cast-inst {A = A} {B = B} {s = c} hB occ c⊢ , inst cʷ) V⊢)
    (β-inst vV) =
  ⊢ν⊑ mode V⊢ (c⊢ , cʷ)
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩↑ (conv↑-unseal hB αB∈Σ _)
      (⊢⟨⟩↓ (conv↓-seal hA αA∈Σ _) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩↑ (conv↑-unseal hB αB∈Σ _)
      (⊢⟨⟩⊒ mode (cast-seal hA αA∈Σ _ , sealⁿ A α) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊑ mode (cast-unseal hB αB∈Σ _ , unsealʷ α B)
      (⊢⟨⟩↓ (conv↓-seal hA αA∈Σ _) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊑ mode (cast-unseal hB αB∈Σ _ , unsealʷ α B)
      (⊢⟨⟩⊒ mode′ (cast-seal hA αA∈Σ _ , sealⁿ A α) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊒ mode (cast-untag hG gG _ , untag gG′)
      (⊢⟨⟩⊑ mode′ (cast-tag hG′ gG″ _ , tag gG‴) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ (no•-⟨⟩ (no•-⟨⟩ noV))
    (⊢⟨⟩⊒ mode (cast-untag hH gH _ , untag gH′)
      (⊢⟨⟩⊑ mode′ (cast-tag hG gG _ , tag gG′) hV))
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
    (⊢⟨⟩⊒ mode c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wfᵐ (at wfΣ) (proj₁ c⊢)
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊒ mode c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊑ mode c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wfᵐ (at wfΣ) (proj₁ c⊢)
pure-preservation wfΣ (no•-⟨⟩ noB)
    (⊢⟨⟩⊑ mode c⊢ (⊢blame hA)) blame-⟨⟩
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

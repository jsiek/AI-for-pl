module proof.InterpreterTermTypingWeakening where

-- File Charter:
--   * Proves relational-store weakening for refined, no-bullet term typing.
--   * Keeps conversion, narrowing, widening, and seal-mode evidence in their
--     refined classes.
--   * Is a reduction-free extraction of the structural weakening argument.

open import Data.Nat using (_≤_; suc; s≤s)

open import Conversion using
  ( _∣_∣_⊢_∶_↑ˢ_
  ; _∣_∣_⊢_∶_↓ˢ_
  ; conv↑-id
  ; conv↑-unseal
  ; conv↑-fun
  ; conv↑-all
  ; conv↓-id
  ; conv↓-seal
  ; conv↓-fun
  ; conv↓-all
  )
open import NarrowWiden using (narrow-weaken; widen-weaken)
open import NuTerms using
  ( No•
  ; no•-`
  ; no•-ƛ
  ; no•-·
  ; no•-Λ
  ; no•-ν
  ; no•-$
  ; no•-⊕
  ; no•-⟨⟩
  ; no•-blame
  )
open import Store using (StoreIncl; StoreIncl-cons)
open import TermTyping using
  ( SealModeStore★
  ; _∣_∣_⊢_⦂_
  ; ⊢`
  ; ⊢ƛ
  ; ⊢·
  ; ⊢Λ
  ; ⊢ν↑
  ; ⊢ν⊑
  ; ⊢$
  ; ⊢⊕
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; ⊢blame
  )
open import Types using (WfTy; renameStoreᵗ)
open import proof.StoreProperties using (renameStoreᵗ-incl)
open import proof.TypeProperties using (WfTy-weakenᵗ)

seal-mode-store-weaken :
  ∀ {μ Σ Σ′} →
  StoreIncl Σ Σ′ →
  SealModeStore★ μ Σ →
  SealModeStore★ μ Σ′
seal-mode-store-weaken incl seal★ α ok =
  incl (seal★ α ok)

mutual
  conversion-up-weaken :
    ∀ {μ Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↑ˢ B →
    μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A ↑ˢ B

  conversion-down-weaken :
    ∀ {μ Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ↓ˢ B →
    μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A ↓ˢ B

  conversion-up-weaken Δ≤Δ′ incl (conv↑-id hA ok) =
    conv↑-id (WfTy-weakenᵗ hA Δ≤Δ′) ok
  conversion-up-weaken Δ≤Δ′ incl (conv↑-unseal hA α∈Σ ok) =
    conv↑-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ) ok
  conversion-up-weaken Δ≤Δ′ incl (conv↑-fun s⊢ t⊢) =
    conv↑-fun (conversion-down-weaken Δ≤Δ′ incl s⊢)
      (conversion-up-weaken Δ≤Δ′ incl t⊢)
  conversion-up-weaken Δ≤Δ′ incl (conv↑-all c⊢) =
    conv↑-all
      (conversion-up-weaken (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl) c⊢)

  conversion-down-weaken Δ≤Δ′ incl (conv↓-id hA ok) =
    conv↓-id (WfTy-weakenᵗ hA Δ≤Δ′) ok
  conversion-down-weaken Δ≤Δ′ incl (conv↓-seal hA α∈Σ ok) =
    conv↓-seal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ) ok
  conversion-down-weaken Δ≤Δ′ incl (conv↓-fun s⊢ t⊢) =
    conv↓-fun (conversion-up-weaken Δ≤Δ′ incl s⊢)
      (conversion-down-weaken Δ≤Δ′ incl t⊢)
  conversion-down-weaken Δ≤Δ′ incl (conv↓-all c⊢) =
    conv↓-all
      (conversion-down-weaken (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl) c⊢)

refined-term-weaken :
  ∀ {Δ Δ′ Σ Σ′ Γ M A} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  No• M →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
refined-term-weaken Δ≤Δ′ incl no•-` (⊢` h) =
  ⊢` h
refined-term-weaken Δ≤Δ′ incl (no•-ƛ noM) (⊢ƛ hA hM) =
  ⊢ƛ (WfTy-weakenᵗ hA Δ≤Δ′)
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-· noL noM) (⊢· hL hM) =
  ⊢· (refined-term-weaken Δ≤Δ′ incl noL hL)
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-Λ noM) (⊢Λ vM hM) =
  ⊢Λ vM
    (refined-term-weaken (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl) noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-ν noL) (⊢ν↑ hA hL c⊢) =
  ⊢ν↑
    (WfTy-weakenᵗ hA Δ≤Δ′)
    (refined-term-weaken Δ≤Δ′ incl noL hL)
    (conversion-up-weaken (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl)) c⊢)
refined-term-weaken Δ≤Δ′ incl (no•-ν noL)
    (⊢ν⊑ mode seal★ hL c⊢) =
  ⊢ν⊑ mode
    (seal-mode-store-weaken
      (StoreIncl-cons (renameStoreᵗ-incl suc incl)) seal★)
    (refined-term-weaken Δ≤Δ′ incl noL hL)
    (widen-weaken (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl)) c⊢)
refined-term-weaken Δ≤Δ′ incl no•-$ (⊢$ κ) =
  ⊢$ κ
refined-term-weaken Δ≤Δ′ incl (no•-⊕ noL noM) (⊢⊕ hL op hM) =
  ⊢⊕ (refined-term-weaken Δ≤Δ′ incl noL hL) op
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩↑ c⊢ hM) =
  ⊢⟨⟩↑ (conversion-up-weaken Δ≤Δ′ incl c⊢)
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM) (⊢⟨⟩↓ c⊢ hM) =
  ⊢⟨⟩↓ (conversion-down-weaken Δ≤Δ′ incl c⊢)
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM)
    (⊢⟨⟩⊒ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊒ mode (seal-mode-store-weaken incl seal★)
    (narrow-weaken Δ≤Δ′ incl c⊢)
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl (no•-⟨⟩ noM)
    (⊢⟨⟩⊑ mode seal★ c⊢ hM) =
  ⊢⟨⟩⊑ mode (seal-mode-store-weaken incl seal★)
    (widen-weaken Δ≤Δ′ incl c⊢)
    (refined-term-weaken Δ≤Δ′ incl noM hM)
refined-term-weaken Δ≤Δ′ incl no•-blame (⊢blame hA) =
  ⊢blame (WfTy-weakenᵗ hA Δ≤Δ′)

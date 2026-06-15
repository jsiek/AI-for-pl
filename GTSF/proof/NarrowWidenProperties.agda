module proof.NarrowWidenProperties where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; _<_; _≤_; zero; suc; z<s; s<s; s≤s)
open import Data.Nat.Properties using (_≟_; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store
open import Coercions
open import NarrowWiden
open import proof.StoreProperties using (∈-renameStoreᵗ; renameStoreᵗ-incl)
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; WfTy-weakenᵗ
    ; renameᵗ-ground
    ; renameᵗ-preserves-WfTy
    ; renameᵗ-ext-suc-comm
    ; renameStoreᵗ-ext-suc-comm
    )

------------------------------------------------------------------------
-- Basic structural lemmas
------------------------------------------------------------------------

renameᵗ-atom :
  ∀ ρ {A} →
  Atom A →
  Atom (renameᵗ ρ A)
renameᵗ-atom ρ (＇ α) = ＇ (ρ α)
renameᵗ-atom ρ (‵ ι) = ‵ ι
renameᵗ-atom ρ ★ = ★

mutual
  narrow-src-wf :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    WfTy Δ A
  narrow-src-wf (nrw-id hA atA) = hA
  narrow-src-wf (nrw-fun s t) =
    wf⇒ (widen-tgt-wf s) (narrow-src-wf t)
  narrow-src-wf (nrw-all s) = wf∀ (narrow-src-wf s)
  narrow-src-wf (nrw-gen hA s) = hA
  narrow-src-wf (nrw-untag hG gG s) = wf★
  narrow-src-wf (nrw-seal hA′ α∈Σ s) = narrow-src-wf s

  widen-tgt-wf :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    WfTy Δ B
  widen-tgt-wf (wid-id hA atA) = hA
  widen-tgt-wf (wid-fun s t) =
    wf⇒ (narrow-src-wf s) (widen-tgt-wf t)
  widen-tgt-wf (wid-all s) = wf∀ (widen-tgt-wf s)
  widen-tgt-wf (wid-inst hB s) = hB
  widen-tgt-wf (wid-tag hG gG s) = wf★
  widen-tgt-wf (wid-unseal hA′ α∈Σ s) = widen-tgt-wf s

mutual
  narrow-weaken :
    ∀ {Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Δ′ ∣ Σ′ ⊢ c ∶ A ⊒ B
  narrow-weaken Δ≤Δ′ incl (nrw-id hA atA) =
    nrw-id (WfTy-weakenᵗ hA Δ≤Δ′) atA
  narrow-weaken Δ≤Δ′ incl (nrw-fun s t) =
    nrw-fun (widen-weaken Δ≤Δ′ incl s) (narrow-weaken Δ≤Δ′ incl t)
  narrow-weaken Δ≤Δ′ incl (nrw-all s) =
    nrw-all
      (narrow-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  narrow-weaken Δ≤Δ′ incl (nrw-gen hA s) =
    nrw-gen
      (WfTy-weakenᵗ hA Δ≤Δ′)
      (narrow-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  narrow-weaken Δ≤Δ′ incl (nrw-untag hG gG s) =
    nrw-untag (WfTy-weakenᵗ hG Δ≤Δ′) gG
      (narrow-weaken Δ≤Δ′ incl s)
  narrow-weaken Δ≤Δ′ incl (nrw-seal hA′ α∈Σ s) =
    nrw-seal (WfTy-weakenᵗ hA′ Δ≤Δ′) (incl α∈Σ)
      (narrow-weaken Δ≤Δ′ incl s)

  widen-weaken :
    ∀ {Δ Δ′ Σ Σ′ A B c} →
    Δ ≤ Δ′ →
    StoreIncl Σ Σ′ →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Δ′ ∣ Σ′ ⊢ c ∶ A ⊑ B
  widen-weaken Δ≤Δ′ incl (wid-id hA atA) =
    wid-id (WfTy-weakenᵗ hA Δ≤Δ′) atA
  widen-weaken Δ≤Δ′ incl (wid-fun s t) =
    wid-fun (narrow-weaken Δ≤Δ′ incl s) (widen-weaken Δ≤Δ′ incl t)
  widen-weaken Δ≤Δ′ incl (wid-all s) =
    wid-all
      (widen-weaken
        (s≤s Δ≤Δ′)
        (renameStoreᵗ-incl suc incl)
        s)
  widen-weaken Δ≤Δ′ incl (wid-inst hB s) =
    wid-inst
      (WfTy-weakenᵗ hB Δ≤Δ′)
      (widen-weaken
        (s≤s Δ≤Δ′)
        (StoreIncl-cons (renameStoreᵗ-incl suc incl))
        s)
  widen-weaken Δ≤Δ′ incl (wid-tag hG gG s) =
    wid-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG
      (widen-weaken Δ≤Δ′ incl s)
  widen-weaken Δ≤Δ′ incl (wid-unseal hA′ α∈Σ s) =
    wid-unseal (WfTy-weakenᵗ hA′ Δ≤Δ′) (incl α∈Σ)
      (widen-weaken Δ≤Δ′ incl s)

mutual
  narrow-renameᵗ :
    ∀ {Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
  narrow-renameᵗ hρ (nrw-id hA atA) =
    nrw-id (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-atom _ atA)
  narrow-renameᵗ hρ (nrw-fun s t) =
    nrw-fun (widen-renameᵗ hρ s) (narrow-renameᵗ hρ t)
  narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (nrw-all s) =
    nrw-all
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (narrow-renameᵗ (TyRenameWf-ext hρ) s))
  narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {A = A} {ρ = ρ}
      hρ (nrw-gen hA s) =
    nrw-gen
      (renameᵗ-preserves-WfTy hA hρ)
      (subst
        (λ T → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ∶ T ⊒ _)
        (renameᵗ-ext-suc-comm ρ A)
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (narrow-renameᵗ (TyRenameWf-ext hρ) s)))
  narrow-renameᵗ hρ (nrw-untag hG gG s) =
    nrw-untag
      (renameᵗ-preserves-WfTy hG hρ)
      (renameᵗ-ground _ gG)
      (narrow-renameᵗ hρ s)
  narrow-renameᵗ hρ (nrw-seal hA′ α∈Σ s) =
    nrw-seal
      (renameᵗ-preserves-WfTy hA′ hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (narrow-renameᵗ hρ s)

  widen-renameᵗ :
    ∀ {Δ Δ′ Σ A B c ρ} →
    TyRenameWf Δ Δ′ ρ →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    Δ′ ∣ renameStoreᵗ ρ Σ
      ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊑ renameᵗ ρ B
  widen-renameᵗ hρ (wid-id hA atA) =
    wid-id (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-atom _ atA)
  widen-renameᵗ hρ (wid-fun s t) =
    wid-fun (narrow-renameᵗ hρ s) (widen-renameᵗ hρ t)
  widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (wid-all s) =
    wid-all
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (widen-renameᵗ (TyRenameWf-ext hρ) s))
  widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {B = B} {ρ = ρ}
      hρ (wid-inst hB s) =
    wid-inst
      (renameᵗ-preserves-WfTy hB hρ)
      (subst
        (λ T → suc Δ′
          ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ T)
        (renameᵗ-ext-suc-comm ρ B)
        (subst
          (λ Σ′ → suc Δ′ ∣ (zero , ★) ∷ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (widen-renameᵗ (TyRenameWf-ext hρ) s)))
  widen-renameᵗ hρ (wid-tag hG gG s) =
    wid-tag
      (renameᵗ-preserves-WfTy hG hρ)
      (renameᵗ-ground _ gG)
      (widen-renameᵗ hρ s)
  widen-renameᵗ hρ (wid-unseal hA′ α∈Σ s) =
    wid-unseal
      (renameᵗ-preserves-WfTy hA′ hρ)
      (∈-renameStoreᵗ _ α∈Σ)
      (widen-renameᵗ hρ s)

narrow-⇑ᵗ :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ = narrow-renameᵗ TyRenameWf-suc

widen-⇑ᵗ :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ = widen-renameᵗ TyRenameWf-suc

widen-⇑ᵗ-cons :
  ∀ {Δ Σ A B c} →
  Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ-cons p =
  widen-weaken ≤-refl StoreIncl-drop (widen-⇑ᵗ p)

------------------------------------------------------------------------
-- Composition (aka. transitivity)
------------------------------------------------------------------------

mutual 
  _⨟ⁿ_ : ∀{Δ Σ A B C}{s t : Coercion} → (Δ ∣ Σ ⊢ s ∶ A ⊒ B) → (Δ ∣ Σ ⊢ t ∶ B ⊒ C)
        → ∃[ u ] (Δ ∣ Σ ⊢ u ∶ A ⊒ C)
  s ⨟ⁿ nrw-id wfB atB = _ , s
  nrw-fun s t ⨟ⁿ nrw-fun s′ t′
      with s′ ⨟ʷ s | t ⨟ⁿ t′
  ... | _ , s″ | _ , t″ = _ , nrw-fun s″ t″
  nrw-untag {ℓ = ℓ} wfG gG s ⨟ⁿ q@(nrw-fun s′ t′)
      with s ⨟ⁿ q
  ... | _ , s″ = _ , nrw-untag {ℓ = ℓ} wfG gG s″
  nrw-all s ⨟ⁿ nrw-all t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-all s′
  nrw-gen wfA s ⨟ⁿ nrw-all t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-gen wfA s′
  nrw-untag {ℓ = ℓ} wfG gG s ⨟ⁿ q@(nrw-all t)
      with s ⨟ⁿ q
  ... | _ , s′ = _ , nrw-untag {ℓ = ℓ} wfG gG s′
  s ⨟ⁿ nrw-gen wfB t
      with narrow-⇑ᵗ s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-gen (narrow-src-wf s) s′
  nrw-id wf★ at★ ⨟ⁿ nrw-untag {ℓ = ℓ} wfG gG t =
    _ , nrw-untag {ℓ = ℓ} wfG gG t
  nrw-untag {ℓ = ℓ′} wfG′ gG′ s
      ⨟ⁿ q@(nrw-untag {ℓ = ℓ} wfG gG t)
      with s ⨟ⁿ q
  ... | _ , s′ = _ , nrw-untag {ℓ = ℓ′} wfG′ gG′ s′
  s ⨟ⁿ nrw-seal wfA′ ∈Σ t
      with s ⨟ⁿ t
  ... | _ , s′ = _ , nrw-seal wfA′ ∈Σ s′

  _⨟ʷ_ : ∀{Δ Σ A B C}{s t : Coercion} → (Δ ∣ Σ ⊢ s ∶ A ⊑ B) → (Δ ∣ Σ ⊢ t ∶ B ⊑ C)
        → ∃[ u ] (Δ ∣ Σ ⊢ u ∶ A ⊑ C)
  s ⨟ʷ wid-id wfB atB = _ , s
  wid-fun s t ⨟ʷ wid-fun s′ t′
      with s′ ⨟ⁿ s | t ⨟ʷ t′
  ... | _ , s″ | _ , t″ = _ , wid-fun s″ t″
  wid-inst wfB s ⨟ʷ q@(wid-fun s′ t′)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s″ = _ , wid-inst (widen-tgt-wf q) s″
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-fun s′ t′)
      with s ⨟ʷ q
  ... | _ , s″ = _ , wid-unseal wfA′ α∈Σ s″
  wid-all s ⨟ʷ wid-all t
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-all s′
  wid-inst wfB s ⨟ʷ q@(wid-all t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s″ = _ , wid-inst (widen-tgt-wf q) s″
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-all t)
      with s ⨟ʷ q
  ... | _ , s″ = _ , wid-unseal wfA′ α∈Σ s″
  wid-all s ⨟ʷ wid-inst wfC t
      with widen-weaken ≤-refl StoreIncl-drop s ⨟ʷ t
  ... | _ , s′ = _ , wid-inst wfC s′
  wid-inst wfB s ⨟ʷ q@(wid-inst wfC t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s′ = _ , wid-inst wfC s′
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-inst wfC t)
      with s ⨟ʷ q
  ... | _ , s′ = _ , wid-unseal wfA′ α∈Σ s′
  s ⨟ʷ wid-tag wfG gG t
      with s ⨟ʷ t
  ... | _ , s′ = _ , wid-tag wfG gG s′
  wid-id wfA atA ⨟ʷ wid-unseal wfA′ α∈Σ t =
    _ , wid-unseal wfA′ α∈Σ t
  wid-inst wfB s ⨟ʷ q@(wid-unseal wfA′ α∈Σ t)
      with s ⨟ʷ widen-⇑ᵗ-cons q
  ... | _ , s′ = _ , wid-inst (widen-tgt-wf q) s′
  wid-unseal wfA′ α∈Σ s ⨟ʷ q@(wid-unseal wfA″ β∈Σ t)
      with s ⨟ʷ q
  ... | _ , s′ = _ , wid-unseal wfA′ α∈Σ s′

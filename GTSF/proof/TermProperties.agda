module proof.TermProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF terms.
--   * Context lookup through mapped contexts, value preservation, type-context
--     weakening, type renaming of typing derivations, and term substitution.
--   * Reduction-specific preservation cases belong in `proof.Preservation`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ; _,_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong₂; subst; sym; trans)

open import Types
open import Ctx
open import Store
open import Coercions
open import Primitives
open import Terms
open import proof.TypeProperties
open import proof.StoreProperties
open import proof.CoercionProperties

------------------------------------------------------------------------
-- Context lookup under mapped contexts
------------------------------------------------------------------------

lookup-map-renameᵗ :
  ∀ {Γ x A ρ} →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
lookup-map-renameᵗ Z = Z
lookup-map-renameᵗ (S h) = S (lookup-map-renameᵗ h)

lookup-map-inv :
  ∀ {Γ x} {B : Ty} {f : Ty → Ty} →
  map f Γ ∋ x ⦂ B →
  Sigma.Σ Ty (λ A → (Γ ∋ x ⦂ A) × (B ≡ f A))
lookup-map-inv {Γ = A ∷ Γ} {x = zero} Z = A , (Z , refl)
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h)
    with lookup-map-inv h
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h)
    | A′ , (hA′ , eq) = A′ , (S hA′ , eq)

lookup-⤊-elim :
  ∀ {Γ x B} {R : Set₁} →
  (∀ {A} → Γ ∋ x ⦂ A → B ≡ ⇑ᵗ A → R) →
  ⤊ᵗ Γ ∋ x ⦂ B →
  R
lookup-⤊-elim {Γ = []} k ()
lookup-⤊-elim {Γ = A ∷ Γ} {x = zero} k Z = k Z refl
lookup-⤊-elim {Γ = A ∷ Γ} {x = suc x} k (S h) =
  lookup-⤊-elim (λ hA eq → k (S hA) eq) h

map-renameᵗ-⤊ :
  ∀ ρ Γ →
  map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ) ≡ ⤊ᵗ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ ρ [] = refl
map-renameᵗ-⤊ ρ (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-ext-suc-comm ρ A) (map-renameᵗ-⤊ ρ Γ)

map-singleRenameᵗ-⤊-cancel :
  ∀ α Γ →
  map (renameᵗ (singleRenameᵗ α)) (⤊ᵗ Γ) ≡ Γ
map-singleRenameᵗ-⤊-cancel α [] = refl
map-singleRenameᵗ-⤊-cancel α (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-single-suc-cancel α A)
             (map-singleRenameᵗ-⤊-cancel α Γ)

------------------------------------------------------------------------
-- Context well-formedness
------------------------------------------------------------------------

CtxWf-weaken :
  ∀ {Δ Δ′ Γ} →
  CtxWf Δ Γ →
  Δ ≤ Δ′ →
  CtxWf Δ′ Γ
CtxWf-weaken hΓ Δ≤Δ′ h =
  WfTy-weakenᵗ (hΓ h) Δ≤Δ′

CtxWf-⤊ :
  ∀ {Δ Γ} →
  CtxWf Δ Γ →
  CtxWf (suc Δ) (⤊ᵗ Γ)
CtxWf-⤊ {Γ = []} hΓ ()
CtxWf-⤊ {Γ = A ∷ Γ} hΓ Z =
  renameᵗ-preserves-WfTy (hΓ Z) TyRenameWf-suc
CtxWf-⤊ {Γ = A ∷ Γ} hΓ (S h) =
  CtxWf-⤊ (λ hA → hΓ (S hA)) h

------------------------------------------------------------------------
-- Values under renaming and substitution
------------------------------------------------------------------------

renameᵗᵐ-preserves-Value :
  ∀ ρ {V} →
  Value V →
  Value (renameᵗᵐ ρ V)
renameᵗᵐ-preserves-Value ρ (ƛ N) = ƛ _
renameᵗᵐ-preserves-Value ρ (Λ vV) =
  Λ (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
renameᵗᵐ-preserves-Value ρ ($ κ) = $ κ
renameᵗᵐ-preserves-Value ρ (vV ⟨ i ⟩) =
  renameᵗᵐ-preserves-Value ρ vV ⟨ renameᶜ-preserves-Inert ρ i ⟩

renameˣᵐ-preserves-Value :
  ∀ ρ {V} →
  Value V →
  Value (renameˣᵐ ρ V)
renameˣᵐ-preserves-Value ρ (ƛ N) = ƛ _
renameˣᵐ-preserves-Value ρ (Λ vV) =
  Λ (renameˣᵐ-preserves-Value ρ vV)
renameˣᵐ-preserves-Value ρ ($ κ) = $ κ
renameˣᵐ-preserves-Value ρ (vV ⟨ i ⟩) =
  renameˣᵐ-preserves-Value ρ vV ⟨ i ⟩

substˣᵐ-preserves-Value :
  ∀ σ {V} →
  Value V →
  Value (substˣᵐ σ V)
substˣᵐ-preserves-Value σ (ƛ N) = ƛ _
substˣᵐ-preserves-Value σ (Λ vV) =
  Λ (substˣᵐ-preserves-Value (↑ᵗᵐ σ) vV)
substˣᵐ-preserves-Value σ ($ κ) = $ κ
substˣᵐ-preserves-Value σ (vV ⟨ i ⟩) =
  substˣᵐ-preserves-Value σ vV ⟨ i ⟩

------------------------------------------------------------------------
-- Weakening over type-context and store growth
------------------------------------------------------------------------

term-weaken :
  ∀ {Δ Δ′ Σ Σ′ Γ M A} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
term-weaken Δ≤Δ′ incl (⊢` h) = ⊢` h
term-weaken Δ≤Δ′ incl (⊢ƛ hA hM) =
  ⊢ƛ (WfTy-weakenᵗ hA Δ≤Δ′) (term-weaken Δ≤Δ′ incl hM)
term-weaken Δ≤Δ′ incl (⊢· hL hM) =
  ⊢· (term-weaken Δ≤Δ′ incl hL) (term-weaken Δ≤Δ′ incl hM)
term-weaken Δ≤Δ′ incl (⊢Λ {occ = occ} vV hV) =
  ⊢Λ {occ = occ} vV
    (term-weaken (s≤s Δ≤Δ′) (renameStoreᵗ-incl suc incl) hV)
term-weaken Δ≤Δ′ incl (⊢• hM hA) =
  ⊢• (term-weaken Δ≤Δ′ incl hM) (WfTy-weakenᵗ hA Δ≤Δ′)
term-weaken Δ≤Δ′ incl (⊢$ κ) = ⊢$ κ
term-weaken Δ≤Δ′ incl (⊢⊕ hL op hM) =
  ⊢⊕ (term-weaken Δ≤Δ′ incl hL) op (term-weaken Δ≤Δ′ incl hM)
term-weaken Δ≤Δ′ incl (⊢up c⊢ hM) =
  ⊢up (coercion-weaken Δ≤Δ′ incl c⊢) (term-weaken Δ≤Δ′ incl hM)
term-weaken Δ≤Δ′ incl (⊢blame hA ℓ) =
  ⊢blame (WfTy-weakenᵗ hA Δ≤Δ′) ℓ

term-weaken-suc :
  ∀ {Δ Σ Γ M A α C} →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  suc Δ ∣ (α , C) ∷ Σ ∣ Γ ⊢ M ⦂ A
term-weaken-suc {Δ = Δ} hM =
  term-weaken (n≤1+n Δ) StoreIncl-drop hM

------------------------------------------------------------------------
-- Renaming type variables in typing derivations
------------------------------------------------------------------------

typing-renameᵀ :
  ∀ {Δ Δ′ Σ Γ M A ρ} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ
    ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ hρ (⊢` h) =
  ⊢` (lookup-map-renameᵗ h)
typing-renameᵀ hρ (⊢ƛ hA hM) =
  ⊢ƛ (renameᵗ-preserves-WfTy hA hρ) (typing-renameᵀ hρ hM)
typing-renameᵀ hρ (⊢· hL hM) =
  ⊢· (typing-renameᵀ hρ hL) (typing-renameᵀ hρ hM)
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    hρ (⊢Λ {M = M} {A = A} {occ = occ} vM hM) =
  ⊢Λ
    {occ = trans (occurs-zero-rename-ext ρ A) occ}
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vM)
    (subst
      (λ Γ′ → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ) ∣ Γ′
        ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
      (map-renameᵗ-⤊ ρ Γ)
      (subst
        (λ Σ′ → suc Δ′ ∣ Σ′ ∣ map (renameᵗ (extᵗ ρ)) (⤊ᵗ Γ)
          ⊢ renameᵗᵐ (extᵗ ρ) M ⦂ renameᵗ (extᵗ ρ) A)
        (renameStoreᵗ-ext-suc-comm ρ Σ)
        (typing-renameᵀ (TyRenameWf-ext hρ) hM)))
typing-renameᵀ {Δ′ = Δ′} {Σ = Σ} {Γ = Γ} {ρ = ρ}
    hρ (⊢• {M = M} {B = B} {A = A} hM hA) =
  subst
    (λ T → Δ′ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂∀ renameᵗ (extᵗ ρ) B • renameᵗ ρ A ⦂ T)
    (sym (rename-[]ᵗ-commute ρ B A))
    (⊢• (typing-renameᵀ hρ hM) (renameᵗ-preserves-WfTy hA hρ))
typing-renameᵀ {ρ = ρ} hρ (⊢$ κ) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ $ κ ⦂ T)
        (constTy-renameᵗ ρ κ)
        (⊢$ κ)
typing-renameᵀ hρ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameᵀ hρ hL) op (typing-renameᵀ hρ hM)
typing-renameᵀ hρ (⊢up c⊢ hM) =
  ⊢up (coercion-renameᵗ hρ c⊢) (typing-renameᵀ hρ hM)
typing-renameᵀ hρ (⊢blame hA ℓ) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ) ℓ

typing-openᵀ :
  ∀ {Δ Σ Γ M A α C} →
  α < suc Δ →
  suc Δ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ M ⦂ A →
  suc Δ ∣ (α , C) ∷ Σ ∣ Γ ⊢ M [ α ]ᵀ ⦂ A [ α ]ᴿ
typing-openᵀ {Σ = Σ} {Γ = Γ} {α = α} α<sucΔ hM =
  term-weaken ≤-refl StoreIncl-drop
    (subst
      (λ Γ′ → _ ∣ Σ ∣ Γ′ ⊢ _ ⦂ _)
      (map-singleRenameᵗ-⤊-cancel α Γ)
      (subst
        (λ Σ′ → _ ∣ Σ′ ∣ map (renameᵗ (singleRenameᵗ α)) (⤊ᵗ Γ)
          ⊢ _ ⦂ _)
        (renameStoreᵗ-single-suc-cancel α Σ)
        (typing-renameᵀ (singleRenameᵗ-Wf α<sucΔ) hM)))

------------------------------------------------------------------------
-- Typing derivations produce well-formed result types
------------------------------------------------------------------------

constTy-wf :
  ∀ {Δ} κ →
  WfTy Δ (constTy κ)
constTy-wf (κℕ n) = wfBase

typing-wf :
  ∀ {Δ Σ Γ M A} →
  StoreWfAt Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  WfTy Δ A
typing-wf wfΣ hΓ (⊢` h) = hΓ h
typing-wf wfΣ hΓ (⊢ƛ hA hM) =
  wf⇒ hA (typing-wf wfΣ (ctxWf-∷ hA hΓ) hM)
typing-wf wfΣ hΓ (⊢· hL hM) with typing-wf wfΣ hΓ hL
typing-wf wfΣ hΓ (⊢· hL hM) | wf⇒ hA hB = hB
typing-wf wfΣ hΓ (⊢Λ {occ = occ} vM hM) =
  wf∀ {occ = occ}
    (typing-wf (StoreWfAt-⟰ᵗ wfΣ) (CtxWf-⤊ hΓ) hM)
typing-wf wfΣ hΓ (⊢• hM hA) with typing-wf wfΣ hΓ hM
typing-wf wfΣ hΓ (⊢• hM hA) | wf∀ hB =
  substᵗ-preserves-WfTy hB (singleTyEnv-Wf hA)
typing-wf wfΣ hΓ (⊢$ κ) = constTy-wf κ
typing-wf wfΣ hΓ (⊢⊕ hL op hM) = wfBase
typing-wf wfΣ hΓ (⊢up c⊢ hM) with coercion-wf wfΣ c⊢
typing-wf wfΣ hΓ (⊢up c⊢ hM) | hA , hB = hB
typing-wf wfΣ hΓ (⊢blame hA ℓ) = hA

------------------------------------------------------------------------
-- Renaming and substituting term variables
------------------------------------------------------------------------

RenameWf : Ctx → Ctx → Renameˣ → Set₁
RenameWf Γ Γ′ ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A

SubstWf : TyCtx → Store → Ctx → Ctx → Substˣ → Set₁
SubstWf Δ Σ Γ Γ′ σ =
  ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Σ ∣ Γ′ ⊢ σ x ⦂ A

RenameWf-ext :
  ∀ {Γ Γ′ B ρ} →
  RenameWf Γ Γ′ ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ′) (extʳ ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

RenameWf-⤊ :
  ∀ {Γ Γ′ ρ} →
  RenameWf Γ Γ′ ρ →
  RenameWf (⤊ᵗ Γ) (⤊ᵗ Γ′) ρ
RenameWf-⤊ hρ h =
  lookup-⤊-elim
    (λ hA eq →
      subst (λ T → _ ∋ _ ⦂ T) (sym eq) (lookup-map-renameᵗ (hρ hA)))
    h

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
typing-renameˣ {Γ = Γ} {Γ′ = Γ′} {ρ = ρ} hρ
    (⊢Λ {occ = occ} vM hM) =
  ⊢Λ {occ = occ} (renameˣᵐ-preserves-Value ρ vM)
    (typing-renameˣ (RenameWf-⤊ hρ) hM)
typing-renameˣ hρ (⊢• hM hA) =
  ⊢• (typing-renameˣ hρ hM) hA
typing-renameˣ hρ (⊢$ κ) = ⊢$ κ
typing-renameˣ hρ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-renameˣ hρ hL) op (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢up c⊢ hM) =
  ⊢up c⊢ (typing-renameˣ hρ hM)
typing-renameˣ hρ (⊢blame hA ℓ) = ⊢blame hA ℓ

typing-renameˣ-shift :
  ∀ {Δ Σ Γ M A B} →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ (B ∷ Γ) ⊢ renameˣᵐ suc M ⦂ A
typing-renameˣ-shift hM =
  typing-renameˣ (λ h → S h) hM

SubstWf-exts :
  ∀ {Δ Σ Γ Γ′ B σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstWf Δ Σ (B ∷ Γ) (B ∷ Γ′) (extˢˣ σ)
SubstWf-exts hσ Z = ⊢` Z
SubstWf-exts hσ (S h) = typing-renameˣ-shift (hσ h)

SubstWf-⇑ :
  ∀ {Δ Σ Γ Γ′ σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  SubstWf (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) (⤊ᵗ Γ′) (↑ᵗᵐ σ)
SubstWf-⇑ hσ h =
  lookup-⤊-elim
    (λ hA eq →
      subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
            (sym eq)
            (typing-renameᵀ TyRenameWf-suc (hσ hA)))
    h

typing-substˣ :
  ∀ {Δ Σ Γ Γ′ M A σ} →
  SubstWf Δ Σ Γ Γ′ σ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ Γ′ ⊢ substˣᵐ σ M ⦂ A
typing-substˣ hσ (⊢` h) = hσ h
typing-substˣ hσ (⊢ƛ hA hM) =
  ⊢ƛ hA (typing-substˣ (SubstWf-exts hσ) hM)
typing-substˣ hσ (⊢· hL hM) =
  ⊢· (typing-substˣ hσ hL) (typing-substˣ hσ hM)
typing-substˣ hσ (⊢Λ {occ = occ} vM hM) =
  ⊢Λ {occ = occ} (substˣᵐ-preserves-Value _ vM)
    (typing-substˣ (SubstWf-⇑ hσ) hM)
typing-substˣ hσ (⊢• hM hA) =
  ⊢• (typing-substˣ hσ hM) hA
typing-substˣ hσ (⊢$ κ) = ⊢$ κ
typing-substˣ hσ (⊢⊕ hL op hM) =
  ⊢⊕ (typing-substˣ hσ hL) op (typing-substˣ hσ hM)
typing-substˣ hσ (⊢up c⊢ hM) =
  ⊢up c⊢ (typing-substˣ hσ hM)
typing-substˣ hσ (⊢blame hA ℓ) = ⊢blame hA ℓ

singleSubstWf :
  ∀ {Δ Σ Γ A V} →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  SubstWf Δ Σ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢` h

typing-single-subst :
  ∀ {Δ Σ Γ N V A B} →
  Δ ∣ Σ ∣ (A ∷ Γ) ⊢ N ⦂ B →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ A →
  Δ ∣ Σ ∣ Γ ⊢ N [ V ] ⦂ B
typing-single-subst hN hV =
  typing-substˣ (singleSubstWf hV) hN

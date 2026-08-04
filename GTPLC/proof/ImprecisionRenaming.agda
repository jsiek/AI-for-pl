module proof.ImprecisionRenaming where

-- File Charter:
--   * Renames one-context narrowing and widening derivations.
--   * Preserves non-identity side conditions using an inverse renaming.
--   * Exposes the two weakening shifts used by factored term narrowing.

open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym; trans)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden
open import proof.TypeInTypeSubst
open import proof.TypeInCoercionSubst
  using
    ( ModeRename
    ; ModeRename-ext
    ; ModeRename-gen
    ; ModeRename-inst
    ; modeRename-tagAllowed
    ; modeRename-sealAllowed
    )
open import proof.TyStore using
  ( ∈-renameTyStoreᵗ
  ; renameTyStoreᵗ-ext-suc-comm
  )

rename-atom : ∀ ρ {A} → Atom A → Atom (renameᵗ ρ A)
rename-atom ρ (＇ X) = ＇ ρ X
rename-atom ρ (‵ ι) = ‵ ι
rename-atom ρ ★ = ★

rename-≢ : ∀ ρ ψ {A B}
  → RenameLeftInverse ρ ψ
  → A ≢ B
  → renameᵗ ρ A ≢ renameᵗ ρ B
rename-≢ ρ ψ {A = A} {B = B} inv A≢B eq =
  A≢B
    (trans (sym (renameᵗ-left-inverse inv A))
      (trans (cong (renameᵗ ψ) eq)
        (renameᵗ-left-inverse inv B)))

mutual

  renameʷ : ∀ (ρ ψ : Renameᵗ) {μ ν Δ Δ′ Σ c A B}
    → TyRenameWf Δ Δ′ ρ
    → ModeRename ρ μ ν
    → RenameLeftInverse ρ ψ
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → ν ∣ Δ′ ∣ renameTyStoreᵗ ρ Σ
        ⊢ renameᶜ ρ c ⦂ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameʷ ρ ψ hρ rel inv (idᵃ a hA) =
    idᵃ (rename-atom ρ a) (renameᵗ-preserves-WfTy hA hρ)
  renameʷ ρ ψ hρ rel inv (p ↦ q) =
    renameⁿ ρ ψ hρ rel inv p ↦ renameʷ ρ ψ hρ rel inv q
  renameʷ ρ ψ hρ rel inv (∀ʷ p) =
    ∀ʷ
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _
          ⦂ _ ⊑ _)
        (renameTyStoreᵗ-ext-suc-comm ρ _)
        (renameʷ (extᵗ ρ) (extᵗ ψ)
          (TyRenameWf-ext hρ) (ModeRename-ext rel)
          (RenameLeftInverse-ext inv) p))
  renameʷ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (tag G hG allowed G꞉A) =
    tag (renameᵍ ρ G)
      (renameᵍ-preserves-WfTag hG hρ)
      (modeRename-tagAllowed {μ = μ} {ν = ν} {G = G} rel allowed)
      (rename-preserves-tagged ρ G꞉A)
  renameʷ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (tag-seq G p hG allowed G꞉B nonvarA A≢B) =
    tag-seq (renameᵍ ρ G)
      (renameʷ ρ ψ hρ rel inv p)
      (renameᵍ-preserves-WfTag hG hρ)
      (modeRename-tagAllowed {μ = μ} {ν = ν} {G = G} rel allowed)
      (rename-preserves-tagged ρ G꞉B)
      (renameNonVar ρ nonvarA)
      (rename-≢ ρ ψ inv A≢B)
  renameʷ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (unseal {X = X} X<Δ hA X,A∈Σ allowed) =
    unseal (hρ X<Δ)
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameTyStoreᵗ ρ X,A∈Σ)
      (modeRename-sealAllowed {μ = μ} {ν = ν} rel allowed)
  renameʷ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (unseal-seq {X = X} X<Δ X,A∈Σ allowed p A≢B) =
    unseal-seq (hρ X<Δ)
      (∈-renameTyStoreᵗ ρ X,A∈Σ)
      (modeRename-sealAllowed {μ = μ} {ν = ν} rel allowed)
      (renameʷ ρ ψ hρ rel inv p)
      (rename-≢ ρ ψ inv A≢B)
  renameʷ ρ ψ {ν = ν} {Δ′ = Δ′} {Σ = Σ}
      {c = Coercions.inst c} {A = `∀ A} {B = B}
      hρ rel inv
      (NarrowWiden.inst nonvarA zero∈A hB p B≢★) =
    NarrowWiden.inst (renameNonVar (extᵗ ρ) nonvarA)
      (rename-ext-preserves-zero∈ ρ zero∈A)
      (renameᵗ-preserves-WfTy hB hρ)
      (subst
        (λ T → instᵈ _ ∣ suc _
          ∣ (zero , ★) ∷ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) c
            ⦂ renameᵗ (extᵗ ρ) A ⊑ T)
        (renameᵗ-ext-suc-comm ρ B)
        renamed-store)
      (rename-≢ ρ ψ inv B≢★)
    where
    renamed :
      instᵈ ν ∣ suc Δ′
        ∣ (zero , ★) ∷ renameTyStoreᵗ (extᵗ ρ) (⟰ᵗ Σ)
        ⊢ renameᶜ (extᵗ ρ) c
          ⦂ renameᵗ (extᵗ ρ) A
          ⊑ renameᵗ (extᵗ ρ) (⇑ᵗ B)
    renamed =
      renameʷ (extᵗ ρ) (extᵗ ψ)
        (TyRenameWf-ext hρ) (ModeRename-inst rel)
        (RenameLeftInverse-ext inv) p

    renamed-store :
      instᵈ ν ∣ suc Δ′
        ∣ (zero , ★) ∷ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
        ⊢ renameᶜ (extᵗ ρ) c
          ⦂ renameᵗ (extᵗ ρ) A
          ⊑ renameᵗ (extᵗ ρ) (⇑ᵗ B)
    renamed-store =
      subst
        (λ Σ′ → instᵈ ν ∣ suc Δ′ ∣ Σ′
          ⊢ renameᶜ (extᵗ ρ) c
            ⦂ renameᵗ (extᵗ ρ) A
            ⊑ renameᵗ (extᵗ ρ) (⇑ᵗ B))
        (cong ((zero , ★) ∷_)
          (renameTyStoreᵗ-ext-suc-comm ρ Σ))
        renamed

  renameⁿ : ∀ (ρ ψ : Renameᵗ) {μ ν Δ Δ′ Σ c A B}
    → TyRenameWf Δ Δ′ ρ
    → ModeRename ρ μ ν
    → RenameLeftInverse ρ ψ
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → ν ∣ Δ′ ∣ renameTyStoreᵗ ρ Σ
        ⊢ renameᶜ ρ c ⦂ renameᵗ ρ A ⊒ renameᵗ ρ B
  renameⁿ ρ ψ hρ rel inv (idᵃ a hA) =
    idᵃ (rename-atom ρ a) (renameᵗ-preserves-WfTy hA hρ)
  renameⁿ ρ ψ hρ rel inv (p ↦ q) =
    renameʷ ρ ψ hρ rel inv p ↦ renameⁿ ρ ψ hρ rel inv q
  renameⁿ ρ ψ hρ rel inv (∀ⁿ p) =
    ∀ⁿ
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _
          ⦂ _ ⊒ _)
        (renameTyStoreᵗ-ext-suc-comm ρ _)
        (renameⁿ (extᵗ ρ) (extᵗ ψ)
          (TyRenameWf-ext hρ) (ModeRename-ext rel)
          (RenameLeftInverse-ext inv) p))
  renameⁿ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (untag G hG allowed G꞉B) =
    untag (renameᵍ ρ G)
      (renameᵍ-preserves-WfTag hG hρ)
      (modeRename-tagAllowed {μ = μ} {ν = ν} {G = G} rel allowed)
      (rename-preserves-tagged ρ G꞉B)
  renameⁿ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (untag-seq G hG allowed G꞉A p nonvarB A≢B) =
    untag-seq (renameᵍ ρ G)
      (renameᵍ-preserves-WfTag hG hρ)
      (modeRename-tagAllowed {μ = μ} {ν = ν} {G = G} rel allowed)
      (rename-preserves-tagged ρ G꞉A)
      (renameⁿ ρ ψ hρ rel inv p)
      (renameNonVar ρ nonvarB)
      (rename-≢ ρ ψ inv A≢B)
  renameⁿ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (seal {X = X} X<Δ hA X,A∈Σ allowed) =
    seal (hρ X<Δ)
      (renameᵗ-preserves-WfTy hA hρ)
      (∈-renameTyStoreᵗ ρ X,A∈Σ)
      (modeRename-sealAllowed {μ = μ} {ν = ν} rel allowed)
  renameⁿ ρ ψ {μ = μ} {ν = ν} hρ rel inv
      (seal-seq {X = X} p X<Δ X,B∈Σ allowed A≢B) =
    seal-seq (renameⁿ ρ ψ hρ rel inv p)
      (hρ X<Δ)
      (∈-renameTyStoreᵗ ρ X,B∈Σ)
      (modeRename-sealAllowed {μ = μ} {ν = ν} rel allowed)
      (rename-≢ ρ ψ inv A≢B)
  renameⁿ ρ ψ {Σ = Σ} {A = B} {B = `∀ A}
      hρ rel inv
      (NarrowWiden.gen nonvarA zero∈A hB p B≢★) =
    NarrowWiden.gen (renameNonVar (extᵗ ρ) nonvarA)
      (rename-ext-preserves-zero∈ ρ zero∈A)
      (renameᵗ-preserves-WfTy hB hρ)
      (subst
        (λ T → genᵈ _ ∣ suc _
          ∣ ⟰ᵗ (renameTyStoreᵗ ρ Σ)
          ⊢ renameᶜ (extᵗ ρ) _ ⦂ T ⊒ _)
        (renameᵗ-ext-suc-comm ρ B)
        (subst
          (λ Σ′ → genᵈ _ ∣ suc _ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ⦂ _ ⊒ _)
          (renameTyStoreᵗ-ext-suc-comm ρ Σ)
          (renameⁿ (extᵗ ρ) (extᵗ ψ)
            (TyRenameWf-ext hρ) (ModeRename-gen rel)
            (RenameLeftInverse-ext inv) p)))
      (rename-≢ ρ ψ inv B≢★)

modeRename-suc-ext : ∀ {μ} → ModeRename suc μ (extᵈ μ)
modeRename-suc-ext X = refl

modeRename-suc-gen : ∀ {μ} → ModeRename suc μ (genᵈ μ)
modeRename-suc-gen X = refl

modeRename-suc-inst : ∀ {μ} → ModeRename suc μ (instᵈ μ)
modeRename-suc-inst X = refl

⇑ⁿ-ext : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᵗ A ⊒ ⇑ᵗ B
⇑ⁿ-ext (c , c⊒) =
  ⇑ᶜ c , renameⁿ suc predᵗ TyRenameWf-suc modeRename-suc-ext
    RenameLeftInverse-suc c⊒

⇑ⁿ-gen : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᵗ A ⊒ ⇑ᵗ B
⇑ⁿ-gen (c , c⊒) =
  ⇑ᶜ c , renameⁿ suc predᵗ TyRenameWf-suc modeRename-suc-gen
    RenameLeftInverse-suc c⊒

⇑ʷ-inst : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → instᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
⇑ʷ-inst (c , c⊑) =
  ⇑ᶜ c , renameʷ suc predᵗ TyRenameWf-suc modeRename-suc-inst
    RenameLeftInverse-suc c⊑

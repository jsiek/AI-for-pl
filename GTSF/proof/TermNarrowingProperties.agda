module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Provides constructor-level type-context shifting helpers and the two
--     cambridge23 two-sided cast derived rules.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Data.List using ([]; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; subst; sym)

open import Types
open import Coercions
open import NuTerms
open import Primitives using (Const; addℕ; constTy; constTy-renameᵗ)
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing using
  ( _∣_∣_⊢_⊒_∶_
  ; ⇑ᵍ
  ; ⊒blame
  ; x⊒x
  ; ƛ⊒ƛ
  ; ·⊒·
  ; Λ⊒Λ
  ; ⊒Λ
  ; κ⊒κ
  ; ⊕⊒⊕
  ; ⊒cast+
  ; ⊒cast-
  ; cast+⊒
  ; cast-⊒
  )
open import proof.CoercionProperties
  using
    ( ModeRename
    ; renameᶜ-dual-normal
    ; renameᶜ-ext-suc-comm
    ; src-renameᶜ
    )
open import proof.NarrowWidenProperties using (narrow-⇑ᵗ-ᶜ-srcStoreⁿ)
open import proof.NuTermProperties
  using (renameᵗᵐ-ext-suc-comm; renameᵗᵐ-preserves-Value)
open import proof.TypeProperties using (TyRenameWf; renameᵗ-ext-suc-comm)

variable
  Δ : TyCtx
  Δ′ : TyCtx
  σ : StoreNrw
  γ : CtxNrw
  A B : Ty
  κ : Const
  p q r s t : Coercion
  M M′ : Term

------------------------------------------------------------------------
-- Type-context shifting
------------------------------------------------------------------------

modeRename-tag-or-id :
  ∀ {ρ} →
  ModeRename ρ tag-or-idᵈ tag-or-idᵈ
modeRename-tag-or-id X = refl

renameStNrw : Renameᵗ → StNrw → StNrw
renameStNrw ρ (X ꞉ p) = ρ X ꞉ renameᶜ ρ p
renameStNrw ρ (X ꞉= A ⊒) = ρ X ꞉= renameᵗ ρ A ⊒
renameStNrw ρ (⊒ X ꞉=☆) = ⊒ ρ X ꞉=☆

renameStoreNrw : Renameᵗ → StoreNrw → StoreNrw
renameStoreNrw ρ σ = map (renameStNrw ρ) σ

renameCtxNrw : Renameᵗ → CtxNrw → CtxNrw
renameCtxNrw ρ γ = map (renameᶜ ρ) γ

renameStNrw-ext-suc-comm :
  ∀ ρ entry →
  renameStNrw (extᵗ ρ) (⇑ʷ entry) ≡ ⇑ʷ (renameStNrw ρ entry)
renameStNrw-ext-suc-comm ρ (X ꞉ p) =
  cong (λ c → suc (ρ X) ꞉ c) (renameᶜ-ext-suc-comm ρ p)
renameStNrw-ext-suc-comm ρ (X ꞉= A ⊒) =
  cong (λ B → suc (ρ X) ꞉= B ⊒) (renameᵗ-ext-suc-comm ρ A)
renameStNrw-ext-suc-comm ρ (⊒ X ꞉=☆) = refl

renameStoreNrw-ext-suc-comm :
  ∀ ρ σ →
  renameStoreNrw (extᵗ ρ) (⇑ˢ σ) ≡ ⇑ˢ (renameStoreNrw ρ σ)
renameStoreNrw-ext-suc-comm ρ [] = refl
renameStoreNrw-ext-suc-comm ρ (entry ∷ σ) =
  cong₂ _∷_
    (renameStNrw-ext-suc-comm ρ entry)
    (renameStoreNrw-ext-suc-comm ρ σ)

renameStoreNrw-open-star-comm :
  ∀ ρ σ →
  renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ≡
    (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ)
renameStoreNrw-open-star-comm ρ σ =
  cong ((zero ꞉= ★ ⊒) ∷_) (renameStoreNrw-ext-suc-comm ρ σ)

renameCtxNrw-ext-suc-comm :
  ∀ ρ γ →
  renameCtxNrw (extᵗ ρ) (⇑ᵍ γ) ≡ ⇑ᵍ (renameCtxNrw ρ γ)
renameCtxNrw-ext-suc-comm ρ [] = refl
renameCtxNrw-ext-suc-comm ρ (p ∷ γ) =
  cong₂ _∷_
    (renameᶜ-ext-suc-comm ρ p)
    (renameCtxNrw-ext-suc-comm ρ γ)

srcStoreⁿ-renameStoreNrw :
  ∀ ρ σ →
  srcStoreⁿ (renameStoreNrw ρ σ) ≡ renameStoreᵗ ρ (srcStoreⁿ σ)
srcStoreⁿ-renameStoreNrw ρ [] = refl
srcStoreⁿ-renameStoreNrw ρ ((X ꞉ p) ∷ σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (src-renameᶜ ρ p))
    (srcStoreⁿ-renameStoreNrw ρ σ)
srcStoreⁿ-renameStoreNrw ρ ((X ꞉= A ⊒) ∷ σ) =
  srcStoreⁿ-renameStoreNrw ρ σ
srcStoreⁿ-renameStoreNrw ρ ((⊒ X ꞉=☆) ∷ σ) =
  cong₂ _∷_ refl (srcStoreⁿ-renameStoreNrw ρ σ)

lookup-renameCtxNrw :
  ∀ ρ {γ x p} →
  γ ∋ x ⦂ p →
  renameCtxNrw ρ γ ∋ x ⦂ renameᶜ ρ p
lookup-renameCtxNrw ρ Z = Z
lookup-renameCtxNrw ρ (S h) = S (lookup-renameCtxNrw ρ h)

rename-cast-srcStore :
  ∀ {ρ Δ Δ′ σ p A B} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ′ ∣ srcStoreⁿ (renameStoreNrw ρ σ)
    ⊢ renameᶜ ρ p ∶ᶜ renameᵗ ρ A ⊒ renameᵗ ρ B
rename-cast-srcStore {ρ = ρ} {Δ′ = Δ′} {σ = σ} {p = p}
    {A = A} {B = B} hρ pᶜ =
  subst (λ Σ → Δ′ ∣ Σ ⊢ renameᶜ ρ p ∶ᶜ renameᵗ ρ A ⊒ renameᵗ ρ B)
    (sym (srcStoreⁿ-renameStoreNrw ρ σ))
    (narrow-renameᵗ {ρ = ρ} hρ (modeRename-tag-or-id {ρ = ρ}) pᶜ)

rename-blame :
  ∀ {ρ Δ Δ′ σ γ M p A B} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ blame ∶ renameᶜ ρ p
rename-blame {σ = σ} hρ pᶜ =
  ⊒blame (rename-cast-srcStore {σ = σ} hρ pᶜ)

rename-var :
  ∀ {ρ Δ Δ′ σ γ x p A B} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  γ ∋ x ⦂ p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ ` x ⊒ ` x ∶ renameᶜ ρ p
rename-var {ρ = ρ} {σ = σ} hρ pᶜ h =
  x⊒x (rename-cast-srcStore {σ = σ} hρ pᶜ)
    (lookup-renameCtxNrw ρ h)

rename-dual-index :
  ∀ {ρ Δ′ σ γ M M′ p} →
  Δ′ ∣ renameStoreNrw ρ σ ∣ γ ⊢ M ⊒ M′ ∶ renameᶜ ρ (- p) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ γ ⊢ M ⊒ M′ ∶ - renameᶜ ρ p
rename-dual-index {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {M = M} {M′ = M′} {p = p} M⊒M′ =
  subst (λ c → Δ′ ∣ renameStoreNrw ρ σ ∣ γ ⊢ M ⊒ M′ ∶ c)
    (renameᶜ-dual-normal ρ p)
    M⊒M′

rename-dual-context :
  ∀ {ρ Δ′ σ γ M M′ p q} →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ ((- p) ∷ γ)
    ⊢ M ⊒ M′ ∶ q →
  Δ′ ∣ renameStoreNrw ρ σ ∣ (- renameᶜ ρ p) ∷ renameCtxNrw ρ γ
    ⊢ M ⊒ M′ ∶ q
rename-dual-context {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {M = M} {M′ = M′} {p = p} {q = q} M⊒M′ =
  subst (λ γ′ → Δ′ ∣ renameStoreNrw ρ σ ∣ γ′ ⊢ M ⊒ M′ ∶ q)
    (cong (λ c → c ∷ renameCtxNrw ρ γ) (renameᶜ-dual-normal ρ p))
    M⊒M′

rename-ƛ :
  ∀ {ρ Δ Δ′ σ γ N N′ p q A A′ B B′} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ ((- p) ∷ γ)
    ⊢ renameᵗᵐ ρ N ⊒ renameᵗᵐ ρ N′ ∶ renameᶜ ρ q →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ ƛ renameᵗᵐ ρ N ⊒ ƛ renameᵗᵐ ρ N′ ∶ renameᶜ ρ (p ↦ q)
rename-ƛ {ρ = ρ} {σ = σ} {p = p} hρ p↦qᶜ N⊒N′ =
  ƛ⊒ƛ (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ p↦qᶜ)
    (rename-dual-context {ρ = ρ} {p = p} N⊒N′)

rename-· :
  ∀ {ρ Δ Δ′ σ γ L L′ M M′ p q A B} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ B →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ L ⊒ renameᵗᵐ ρ L′ ∶ renameᶜ ρ (p ↦ q) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ (- p) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ L · renameᵗᵐ ρ M
      ⊒ renameᵗᵐ ρ L′ · renameᵗᵐ ρ M′ ∶ renameᶜ ρ q
rename-· {ρ = ρ} {σ = σ} {p = p} hρ qᶜ L⊒L′ M⊒M′ =
  ·⊒· (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ qᶜ)
    L⊒L′
    (rename-dual-index {ρ = ρ} {p = p} M⊒M′)

rename-Λ :
  ∀ {ρ Δ Δ′ σ γ V V′ p A B} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ `∀ p ∶ᶜ `∀ A ⊒ `∀ B →
  Value V →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ) (⇑ˢ σ)
    ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) V ⊒ renameᵗᵐ (extᵗ ρ) V′
    ∶ renameᶜ (extᵗ ρ) p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ Λ (renameᵗᵐ (extᵗ ρ) V)
      ⊒ Λ (renameᵗᵐ (extᵗ ρ) V′)
    ∶ renameᶜ ρ (`∀ p)
rename-Λ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ} {V = V}
    {V′ = V′} {p = p} hρ ∀pᶜ vV V⊒V′ =
  Λ⊒Λ (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ ∀pᶜ)
    (renameᵗᵐ-preserves-Value (extᵗ ρ) vV)
    (subst
      (λ γ′ →
        suc Δ′ ∣ ⇑ˢ (renameStoreNrw ρ σ) ∣ γ′
          ⊢ renameᵗᵐ (extᵗ ρ) V ⊒ renameᵗᵐ (extᵗ ρ) V′
          ∶ renameᶜ (extᵗ ρ) p)
      (renameCtxNrw-ext-suc-comm ρ γ)
      (subst
        (λ σ′ →
          suc Δ′ ∣ σ′ ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
            ⊢ renameᵗᵐ (extᵗ ρ) V ⊒ renameᵗᵐ (extᵗ ρ) V′
            ∶ renameᶜ (extᵗ ρ) p)
        (renameStoreNrw-ext-suc-comm ρ σ)
        V⊒V′))

rename-⊒Λ :
  ∀ {ρ Δ Δ′ σ γ A B N V′ p} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)
    ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
      ⊒ renameᵗᵐ (extᵗ ρ) V′ ∶ renameᶜ (extᵗ ρ) p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ N ⊒ Λ (renameᵗᵐ (extᵗ ρ) V′)
    ∶ renameᶜ ρ (gen A p)
rename-⊒Λ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ} {N = N}
    {V′ = V′} {p = p} hρ genpᶜ N⊒V′ =
  ⊒Λ (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ genpᶜ)
    (subst
      (λ L →
        suc Δ′ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ)
          ∣ ⇑ᵍ (renameCtxNrw ρ γ)
          ⊢ L ⊒ renameᵗᵐ (extᵗ ρ) V′ ∶ renameᶜ (extᵗ ρ) p)
      (renameᵗᵐ-ext-suc-comm ρ N)
      (subst
        (λ γ′ →
          suc Δ′ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ) ∣ γ′
            ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
              ⊒ renameᵗᵐ (extᵗ ρ) V′ ∶ renameᶜ (extᵗ ρ) p)
        (renameCtxNrw-ext-suc-comm ρ γ)
        (subst
          (λ σ′ →
            suc Δ′ ∣ σ′ ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
              ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
                ⊒ renameᵗᵐ (extᵗ ρ) V′ ∶ renameᶜ (extᵗ ρ) p)
          (renameStoreNrw-open-star-comm ρ σ)
          N⊒V′)))

rename-κ :
  ∀ {ρ Δ′ σ γ κ} →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ $ κ ⊒ $ κ ∶ renameᶜ ρ (id (constTy κ))
rename-κ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ} {κ = κ} =
  subst (λ c → Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
      ⊢ $ κ ⊒ $ κ ∶ c)
    (cong id (constTy-renameᵗ ρ κ))
    (κ⊒κ κ)

rename-⊕ :
  ∀ {ρ Δ′ σ γ M M′ N N′} →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ (id (‵ `ℕ)) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ N ⊒ renameᵗᵐ ρ N′ ∶ renameᶜ ρ (id (‵ `ℕ)) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊕[ addℕ ] renameᵗᵐ ρ N
      ⊒ renameᵗᵐ ρ M′ ⊕[ addℕ ] renameᵗᵐ ρ N′
    ∶ renameᶜ ρ (id (‵ `ℕ))
rename-⊕ M⊒M′ N⊒N′ =
  ⊕⊒⊕ M⊒M′ N⊒N′

lookup-⇑ᵍ :
  ∀ {γ x p} →
  γ ∋ x ⦂ p →
  ⇑ᵍ γ ∋ x ⦂ ⇑ᶜ p
lookup-⇑ᵍ Z = Z
lookup-⇑ᵍ (S h) = S (lookup-⇑ᵍ h)

shift-blame :
  ∀ {Δ σ γ M p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ M ⊒ blame ∶ ⇑ᶜ p
shift-blame {σ = σ} pᶜ =
  ⊒blame (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} pᶜ)

shift-var :
  ∀ {Δ σ γ x p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  γ ∋ x ⦂ p →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ` x ⊒ ` x ∶ ⇑ᶜ p
shift-var {σ = σ} pᶜ h =
  x⊒x (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} pᶜ) (lookup-⇑ᵍ h)

shift-dual-index :
  ∀ {Δ σ γ M M′ p} →
  suc Δ ∣ ⇑ˢ σ ∣ γ ⊢ M ⊒ M′ ∶ ⇑ᶜ (- p) →
  suc Δ ∣ ⇑ˢ σ ∣ γ ⊢ M ⊒ M′ ∶ - ⇑ᶜ p
shift-dual-index {Δ = Δ} {σ = σ} {γ = γ} {M = M} {M′ = M′}
    {p = p} M⊒M′ =
  subst (λ c → suc Δ ∣ ⇑ˢ σ ∣ γ ⊢ M ⊒ M′ ∶ c)
    (renameᶜ-dual-normal suc p)
    M⊒M′

shift-dual-context :
  ∀ {Δ σ γ M M′ p q} →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ ((- p) ∷ γ) ⊢ M ⊒ M′ ∶ q →
  suc Δ ∣ ⇑ˢ σ ∣ (- ⇑ᶜ p) ∷ ⇑ᵍ γ ⊢ M ⊒ M′ ∶ q
shift-dual-context {Δ = Δ} {σ = σ} {γ = γ} {M = M} {M′ = M′}
    {p = p} {q = q} M⊒M′ =
  subst (λ γ′ → suc Δ ∣ ⇑ˢ σ ∣ γ′ ⊢ M ⊒ M′ ∶ q)
    (cong (λ c → c ∷ ⇑ᵍ γ) (renameᶜ-dual-normal suc p))
    M⊒M′

shift-ƛ :
  ∀ {Δ σ γ N N′ p q A A′ B B′} →
  Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ ((- p) ∷ γ)
    ⊢ ⇑ᵗᵐ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ q →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ƛ ⇑ᵗᵐ N ⊒ ƛ ⇑ᵗᵐ N′ ∶ ⇑ᶜ (p ↦ q)
shift-ƛ {σ = σ} {p = p} p↦qᶜ N⊒N′ =
  ƛ⊒ƛ (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} p↦qᶜ)
    (shift-dual-context {p = p} N⊒N′)

shift-· :
  ∀ {Δ σ γ L L′ M M′ p q A B} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ L ⊒ ⇑ᵗᵐ L′ ∶ ⇑ᶜ (p ↦ q) →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ (- p) →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ L · ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ L′ · ⇑ᵗᵐ M′ ∶ ⇑ᶜ q
shift-· {σ = σ} {p = p} qᶜ L⊒L′ M⊒M′ =
  ·⊒· (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
    L⊒L′
    (shift-dual-index {p = p} M⊒M′)

------------------------------------------------------------------------
-- Derived cast rules
------------------------------------------------------------------------

-- cambridge23 states these with the side condition `q ⨾ s ≈ t ⨾ p`.
-- This formalization exposes the intermediate coercion `r`, matching the
-- displayed derivations and avoiding a dependency on general transitivity for
-- coercion equivalence.
-- The compact one-premise version should be derivable once coercion
-- equivalence has enough transitivity/reflexivity infrastructure to bridge
-- `q ⨾ s ≈ r` and `r ≈ t ⨾ p` from `q ⨾ s ≈ t ⨾ p`.

cast-⊒cast- : ∀ {M M′ p q r s t A B Ap Bp Aq Bq}
  → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp
  → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq
  → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
  → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q
    --------------------------------------
  → Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ M′ ⟨ s ⟩ ∶ p
cast-⊒cast- {p = p} {q = q} {r = r} {s = s} {t = t}
    pᶜ qᶜ q⨟s≈r r≈t⨟p M⊒M′ =
  cast-⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p
    (⊒cast- {q = q} {r = r} {s = s} qᶜ q⨟s≈r M⊒M′)

cast+⊒cast+ : ∀ {M M′ p q r s t A B Ap Bp Aq Bq}
  → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp
  → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq
  → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
  → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p
    ------------------------------------------
  → Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ M′ ⟨ - s ⟩ ∶ q
cast+⊒cast+ {p = p} {q = q} {r = r} {s = s} {t = t}
    pᶜ qᶜ q⨟s≈r r≈t⨟p M⊒M′ =
  ⊒cast+ {q = q} {r = r} {s = s} qᶜ q⨟s≈r
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒M′)

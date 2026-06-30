module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Provides constructor-level type-context shifting helpers, composition
--     shifting for cast side conditions, and the two cambridge23 two-sided
--     cast derived rules.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Data.List using ([]; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import Primitives using (Const; addℕ; constTy; constTy-renameᵗ)
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing using
  ( _∣_∣_⊢_⊒_∶_
  ; _•_
  ; ⇑ᵍ
  ; ⊒blame
  ; x⊒x
  ; ƛ⊒ƛ
  ; ·⊒·
  ; Λ⊒Λ
  ; ⊒Λ
  ; ⊒⟨ν⟩
  ; α⊒α
  ; ⊒α
  ; ν⊒ν
  ; ⊒ν
  ; ν⊒
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
    ; renameᶜ-preserves-Inert
    ; renameᶜ-dual-normal
    ; renameᶜ-ext-suc-comm
    ; renameᶜ-open-commute
    ; src-renameᶜ
    ; tgt-renameᶜ
    )
open import proof.NarrowWidenProperties
  using
    ( StoreDetWf
    ; StoreDetWf-⟰ᵗ
    ; WfTyˢ-rename
    ; WfTyˢ-⇑ᵗ
    ; narrowing-determinedᵐ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ
    ; narrow-⇑ᵗ-any
    ; ⊒ˢ-⇑ˢ
    )
open import proof.NuTermProperties
  using (renameᵗᵐ-ext-suc-comm; renameᵗᵐ-preserves-Value)
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; renameᵗ-ext-suc-comm
    ; renameᵗ-preserves-WfTy
    )

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

tailᵈ : ModeEnv → ModeEnv
tailᵈ μ X = μ (suc X)

consᵈ : Mode → ModeEnv → ModeEnv
consᵈ m ν′ zero = m
consᵈ m ν′ (suc X) = ν′ X

AllModeRename : Renameᵗ → Set
AllModeRename ρ = ∀ μ → ∃[ ν′ ] ModeRename ρ μ ν′

allModeRename-suc :
  AllModeRename suc
allModeRename-suc μ = genᵈ μ , modeRename-suc-gen

allModeRename-ext :
  ∀ {ρ} →
  AllModeRename ρ →
  AllModeRename (extᵗ ρ)
allModeRename-ext all μ
    with all (tailᵈ μ)
allModeRename-ext all μ | ν′ , rel =
  consᵈ (μ zero) ν′ , rel′
  where
    rel′ : ModeRename (extᵗ _) μ (consᵈ (μ zero) ν′)
    rel′ zero = modeIncl-refl {μ = μ} zero
    rel′ (suc X) = rel X

narrow-renameᵗ-any :
  ∀ {ρ Δ Δ′ Σ A B c} →
  TyRenameWf Δ Δ′ ρ →
  AllModeRename ρ →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Δ′ ∣ renameStoreᵗ ρ Σ
    ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
narrow-renameᵗ-any hρ all (μ , c⊒)
    with all μ
narrow-renameᵗ-any hρ all (μ , c⊒) | ν′ , rel =
  ν′ , narrow-renameᵗ hρ rel c⊒

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

renameStoreNrw-open-coercion-comm :
  ∀ ρ q σ →
  renameStoreNrw (extᵗ ρ) ((zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ) ≡
    (zero ꞉ ⇑ᶜ (renameᶜ ρ q)) ∷ ⇑ˢ (renameStoreNrw ρ σ)
renameStoreNrw-open-coercion-comm ρ q σ =
  cong₂ _∷_
    (cong (zero ꞉_) (renameᶜ-ext-suc-comm ρ q))
    (renameStoreNrw-ext-suc-comm ρ σ)

renameStoreNrw-open-widen-comm :
  ∀ ρ A σ →
  renameStoreNrw (extᵗ ρ) ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ) ≡
    (zero ꞉= ⇑ᵗ (renameᵗ ρ A) ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ)
renameStoreNrw-open-widen-comm ρ A σ =
  cong₂ _∷_
    (cong (λ B → zero ꞉= B ⊒) (renameᵗ-ext-suc-comm ρ A))
    (renameStoreNrw-ext-suc-comm ρ σ)

renameStoreNrw-open-left-star-comm :
  ∀ ρ σ →
  renameStoreNrw (extᵗ ρ) ((⊒ zero ꞉=☆) ∷ ⇑ˢ σ) ≡
    (⊒ zero ꞉=☆) ∷ ⇑ˢ (renameStoreNrw ρ σ)
renameStoreNrw-open-left-star-comm ρ σ =
  cong ((⊒ zero ꞉=☆) ∷_) (renameStoreNrw-ext-suc-comm ρ σ)

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

⊒ˢ-rename :
  ∀ {ρ Δ Δ′ σ Σ Σ′} →
  TyRenameWf Δ Δ′ ρ →
  AllModeRename ρ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ′ ⊢ renameStoreNrw ρ σ
    ꞉ renameStoreᵗ ρ Σ ⊒ˢ renameStoreᵗ ρ Σ′
⊒ˢ-rename hρ all ⊒ˢ-nil = ⊒ˢ-nil
⊒ˢ-rename {ρ = ρ} hρ all (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right
    (renameᵗ-preserves-WfTy hA hρ)
    (⊒ˢ-rename hρ all σ⊒)
⊒ˢ-rename hρ all (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (⊒ˢ-rename hρ all σ⊒)
⊒ˢ-rename hρ all (⊒ˢ-both hA hA′ s⊒ σ⊒) =
  ⊒ˢ-both
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hA′ hρ)
    (narrow-renameᵗ-any hρ all s⊒)
    (⊒ˢ-rename hρ all σ⊒)

≈ⁿ-rename :
  ∀ {ρ Δ Δ′ σ s t A B} →
  TyRenameWf Δ Δ′ ρ →
  AllModeRename ρ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ s ≈ renameᶜ ρ t ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
≈ⁿ-rename {ρ = ρ} hρ all (endpointsⁿ {s = s} {t = t}
    srcs tgts srct tgtt σ⊒ (hA , hB) (hA′ , hB′) s⊒ t⊒) =
  endpointsⁿ
    (trans (src-renameᶜ ρ s) (cong (renameᵗ ρ) srcs))
    (trans (tgt-renameᶜ ρ s) (cong (renameᵗ ρ) tgts))
    (trans (src-renameᶜ ρ t) (cong (renameᵗ ρ) srct))
    (trans (tgt-renameᶜ ρ t) (cong (renameᵗ ρ) tgtt))
    (⊒ˢ-rename hρ all σ⊒)
    (WfTyˢ-rename hρ hA , WfTyˢ-rename hρ hB)
    (WfTyˢ-rename hρ hA′ , WfTyˢ-rename hρ hB′)
    (narrow-renameᵗ-any hρ all s⊒)
    (narrow-renameᵗ-any hρ all t⊒)

compose-leftⁿ-rename :
  ∀ {ρ Δ Δ′ σ q s r A B} →
  TyRenameWf Δ Δ′ ρ →
  AllModeRename ρ →
  (∀ {Σ} → StoreDetWf Δ Σ → StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s ≈ renameᶜ ρ r
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-leftⁿ-rename {ρ = ρ} hρ all det
    (compose-leftⁿ {μ = μ} wfΣ q⊒ s⊒ q⨟s≈r)
    with all μ
compose-leftⁿ-rename {ρ = ρ} hρ all det
    (compose-leftⁿ {μ = μ} wfΣ q⊒ s⊒ q⨟s≈r)
    | ν′ , rel =
  let
    wfΣ′ = det wfΣ
    q⊒′ = narrow-renameᵗ {ν = ν′} {ρ = ρ} hρ rel q⊒
    s⊒′ = narrow-renameᵗ {ν = ν′} {ρ = ρ} hρ rel s⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒
    new = _⨟ⁿ_ {wfΣ = wfΣ′} q⊒′ s⊒′
    u≡ =
      narrowing-determinedᵐ wfΣ′
        (proj₂ new)
        (narrow-renameᵗ {ν = ν′} {ρ = ρ} hρ rel (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ u ≈ renameᶜ ρ _ ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-rename hρ all q⨟s≈r)
  in
  compose-leftⁿ wfΣ′ q⊒′ s⊒′ eq′

compose-rightⁿ-rename :
  ∀ {ρ Δ Δ′ σ r t p A B} →
  TyRenameWf Δ Δ′ ρ →
  AllModeRename ρ →
  (∀ {Σ} → StoreDetWf Δ Σ → StoreDetWf Δ′ (renameStoreᵗ ρ Σ)) →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ r ≈ renameᶜ ρ t ⨾ⁿ renameᶜ ρ p
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
compose-rightⁿ-rename {ρ = ρ} hρ all det
    (compose-rightⁿ {μ = μ} wfΣ t⊒ p⊒ r≈t⨟p)
    with all μ
compose-rightⁿ-rename {ρ = ρ} hρ all det
    (compose-rightⁿ {μ = μ} wfΣ t⊒ p⊒ r≈t⨟p)
    | ν′ , rel =
  let
    wfΣ′ = det wfΣ
    t⊒′ = narrow-renameᵗ {ν = ν′} {ρ = ρ} hρ rel t⊒
    p⊒′ = narrow-renameᵗ {ν = ν′} {ρ = ρ} hρ rel p⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒
    new = _⨟ⁿ_ {wfΣ = wfΣ′} t⊒′ p⊒′
    u≡ =
      narrowing-determinedᵐ wfΣ′
        (proj₂ new)
        (narrow-renameᵗ {ν = ν′} {ρ = ρ} hρ rel (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ renameᶜ ρ _ ≈ u ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-rename hρ all r≈t⨟p)
  in
  compose-rightⁿ wfΣ′ t⊒′ p⊒′ eq′

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

rename-⊒⟨ν⟩ :
  ∀ {ρ Δ Δ′ σ γ A B N V′ p s} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Inert s →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ) ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ)
    ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
      ⊒ renameᵗᵐ (extᵗ ρ) (V′ ⟨ s ⟩)
      ∶ renameᶜ (extᵗ ρ) p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ N
      ⊒ renameᵗᵐ (extᵗ ρ) V′
          ⟨ gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) s) ⟩
    ∶ renameᶜ ρ (gen A p)
rename-⊒⟨ν⟩ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {A = A} {N = N} {V′ = V′} {p = p} {s = s}
    hρ genpᶜ inert-s N⊒V′s =
  ⊒⟨ν⟩ (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ genpᶜ)
    (renameᶜ-preserves-Inert (extᵗ ρ) inert-s)
    (subst
      (λ L →
        suc Δ′ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ)
          ∣ ⇑ᵍ (renameCtxNrw ρ γ)
          ⊢ L ⊒ renameᵗᵐ (extᵗ ρ) (V′ ⟨ s ⟩)
          ∶ renameᶜ (extᵗ ρ) p)
      (renameᵗᵐ-ext-suc-comm ρ N)
      (subst
        (λ γ′ →
          suc Δ′ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (renameStoreNrw ρ σ) ∣ γ′
            ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
              ⊒ renameᵗᵐ (extᵗ ρ) (V′ ⟨ s ⟩)
              ∶ renameᶜ (extᵗ ρ) p)
        (renameCtxNrw-ext-suc-comm ρ γ)
        (subst
          (λ σ′ →
            suc Δ′ ∣ σ′ ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
              ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
                ⊒ renameᵗᵐ (extᵗ ρ) (V′ ⟨ s ⟩)
                ∶ renameᶜ (extᵗ ρ) p)
          (renameStoreNrw-open-star-comm ρ σ)
          N⊒V′s)))

rename-ν⊒ν :
  ∀ {ρ Δ Δ′ σ γ A A′ B B′ N N′ p q} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ B ⊒ B′ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ A′ →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ) ((zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ)
    ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) N ⊒ renameᵗᵐ (extᵗ ρ) N′
    ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ ν (renameᵗ ρ A) (renameᵗᵐ (extᵗ ρ) N)
        (⇑ᶜ (renameᶜ ρ p))
      ⊒ ν (renameᵗ ρ A′) (renameᵗᵐ (extᵗ ρ) N′)
        (⇑ᶜ (renameᶜ ρ p))
    ∶ renameᶜ ρ p
rename-ν⊒ν {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {N = N} {N′ = N′} {p = p} {q = q} hρ pᶜ qᶜ N⊒N′ =
  ν⊒ν
    (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ pᶜ)
    (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ qᶜ)
    (subst
      (λ c →
        suc Δ′ ∣ (zero ꞉ ⇑ᶜ (renameᶜ ρ q))
          ∷ ⇑ˢ (renameStoreNrw ρ σ)
          ∣ ⇑ᵍ (renameCtxNrw ρ γ)
          ⊢ renameᵗᵐ (extᵗ ρ) N ⊒ renameᵗᵐ (extᵗ ρ) N′ ∶ c)
      (renameᶜ-ext-suc-comm ρ p)
      (subst
        (λ γ′ →
          suc Δ′ ∣ (zero ꞉ ⇑ᶜ (renameᶜ ρ q))
            ∷ ⇑ˢ (renameStoreNrw ρ σ) ∣ γ′
            ⊢ renameᵗᵐ (extᵗ ρ) N ⊒ renameᵗᵐ (extᵗ ρ) N′
            ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p))
        (renameCtxNrw-ext-suc-comm ρ γ)
        (subst
          (λ σ′ →
            suc Δ′ ∣ σ′ ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
              ⊢ renameᵗᵐ (extᵗ ρ) N ⊒ renameᵗᵐ (extᵗ ρ) N′
              ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p))
          (renameStoreNrw-open-coercion-comm ρ q σ)
          N⊒N′)))

rename-⊒ν :
  ∀ {ρ Δ Δ′ σ γ A B B′ N N′ p} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ B ⊒ B′ →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ)
      ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ)
    ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N) ⊒ renameᵗᵐ (extᵗ ρ) N′
    ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ N
      ⊒ ν (renameᵗ ρ A) (renameᵗᵐ (extᵗ ρ) N′)
        (⇑ᶜ (renameᶜ ρ p))
    ∶ renameᶜ ρ p
rename-⊒ν {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {A = A} {N = N} {N′ = N′} {p = p} hρ pᶜ N⊒N′ =
  ⊒ν (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ pᶜ)
    (subst
      (λ L →
        suc Δ′ ∣ (zero ꞉= ⇑ᵗ (renameᵗ ρ A) ⊒)
          ∷ ⇑ˢ (renameStoreNrw ρ σ)
          ∣ ⇑ᵍ (renameCtxNrw ρ γ)
          ⊢ L ⊒ renameᵗᵐ (extᵗ ρ) N′
          ∶ ⇑ᶜ (renameᶜ ρ p))
      (renameᵗᵐ-ext-suc-comm ρ N)
      (subst
        (λ c →
          suc Δ′ ∣ (zero ꞉= ⇑ᵗ (renameᵗ ρ A) ⊒)
            ∷ ⇑ˢ (renameStoreNrw ρ σ)
            ∣ ⇑ᵍ (renameCtxNrw ρ γ)
            ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
              ⊒ renameᵗᵐ (extᵗ ρ) N′ ∶ c)
        (renameᶜ-ext-suc-comm ρ p)
        (subst
          (λ γ′ →
            suc Δ′ ∣ (zero ꞉= ⇑ᵗ (renameᵗ ρ A) ⊒)
              ∷ ⇑ˢ (renameStoreNrw ρ σ) ∣ γ′
              ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
                ⊒ renameᵗᵐ (extᵗ ρ) N′
              ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p))
          (renameCtxNrw-ext-suc-comm ρ γ)
          (subst
            (λ σ′ →
              suc Δ′ ∣ σ′ ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
                ⊢ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N)
                  ⊒ renameᵗᵐ (extᵗ ρ) N′
                ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p))
            (renameStoreNrw-open-widen-comm ρ A σ)
            N⊒N′))))

rename-ν⊒ :
  ∀ {ρ Δ Δ′ σ γ N N′ p A B} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  suc Δ′ ∣ renameStoreNrw (extᵗ ρ) ((⊒ zero ꞉=☆) ∷ ⇑ˢ σ)
    ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
    ⊢ renameᵗᵐ (extᵗ ρ) N
      ⊒ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N′)
    ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p) →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ ν ★ (renameᵗᵐ (extᵗ ρ) N) (⇑ᶜ (renameᶜ ρ p))
      ⊒ renameᵗᵐ ρ N′ ∶ renameᶜ ρ p
rename-ν⊒ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {N = N} {N′ = N′} {p = p} hρ pᶜ N⊒N′ =
  ν⊒ (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ pᶜ)
    (subst
      (λ R →
        suc Δ′ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ (renameStoreNrw ρ σ)
          ∣ ⇑ᵍ (renameCtxNrw ρ γ)
          ⊢ renameᵗᵐ (extᵗ ρ) N ⊒ R ∶ ⇑ᶜ (renameᶜ ρ p))
      (renameᵗᵐ-ext-suc-comm ρ N′)
      (subst
        (λ c →
          suc Δ′ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ (renameStoreNrw ρ σ)
            ∣ ⇑ᵍ (renameCtxNrw ρ γ)
            ⊢ renameᵗᵐ (extᵗ ρ) N
              ⊒ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N′) ∶ c)
        (renameᶜ-ext-suc-comm ρ p)
        (subst
          (λ γ′ →
            suc Δ′ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ (renameStoreNrw ρ σ) ∣ γ′
              ⊢ renameᵗᵐ (extᵗ ρ) N
                ⊒ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N′)
              ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p))
          (renameCtxNrw-ext-suc-comm ρ γ)
          (subst
            (λ σ′ →
              suc Δ′ ∣ σ′ ∣ renameCtxNrw (extᵗ ρ) (⇑ᵍ γ)
                ⊢ renameᵗᵐ (extᵗ ρ) N
                  ⊒ renameᵗᵐ (extᵗ ρ) (⇑ᵗᵐ N′)
                ∶ renameᶜ (extᵗ ρ) (⇑ᶜ p))
            (renameStoreNrw-open-left-star-comm ρ σ)
            N⊒N′))))

rename-open-cast-srcStore :
  ∀ {ρ Δ Δ′ σ α q p C D} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ′ ∣ srcStoreⁿ ((ρ α ꞉ renameᶜ ρ q) ∷ renameStoreNrw ρ σ)
    ⊢ renameᶜ (extᵗ ρ) p [ ρ α ]ᶜ
    ∶ᶜ renameᵗ ρ C ⊒ renameᵗ ρ D
rename-open-cast-srcStore {ρ = ρ} {σ = σ} {α = α} {q = q}
    {p = p} hρ pαᶜ =
  subst
    (λ c → _ ∣ srcStoreⁿ ((ρ α ꞉ renameᶜ ρ q) ∷ renameStoreNrw ρ σ)
      ⊢ c ∶ᶜ _ ⊒ _)
    (renameᶜ-open-commute ρ p α)
    (rename-cast-srcStore {ρ = ρ} {σ = (α ꞉ q) ∷ σ} hρ pαᶜ)

rename-open-widen-cast-srcStore :
  ∀ {ρ Δ Δ′ σ α A p C D} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ′ ∣ srcStoreⁿ ((ρ α ꞉= renameᵗ ρ A ⊒) ∷ renameStoreNrw ρ σ)
    ⊢ renameᶜ (extᵗ ρ) p [ ρ α ]ᶜ
    ∶ᶜ renameᵗ ρ C ⊒ renameᵗ ρ D
rename-open-widen-cast-srcStore {ρ = ρ} {σ = σ} {α = α}
    {A = A} {p = p} hρ pαᶜ =
  subst
    (λ c → _ ∣ srcStoreⁿ ((ρ α ꞉= renameᵗ ρ A ⊒)
      ∷ renameStoreNrw ρ σ) ⊢ c ∶ᶜ _ ⊒ _)
    (renameᶜ-open-commute ρ p α)
    (rename-cast-srcStore {ρ = ρ} {σ = (α ꞉= A ⊒) ∷ σ} hρ pαᶜ)

rename-α⊒α :
  ∀ {ρ Δ Δ′ σ γ L L′ p q A B C D α} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ A ⊒ B →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ L ⊒ renameᵗᵐ ρ L′
    ∶ renameᶜ ρ (`∀ p) →
  Δ′ ∣ (ρ α ꞉ renameᶜ ρ q) ∷ renameStoreNrw ρ σ
    ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ L • ρ α ⊒ renameᵗᵐ ρ L′ • ρ α
    ∶ renameᶜ ρ (p [ α ]ᶜ)
rename-α⊒α {ρ = ρ} {σ = σ} {γ = γ} {L = L} {L′ = L′}
    {p = p} {q = q} {α = α} hρ qᶜ pαᶜ L⊒L′ =
  subst
    (λ c → _ ∣ (ρ α ꞉ renameᶜ ρ q) ∷ renameStoreNrw ρ σ
      ∣ renameCtxNrw ρ γ
      ⊢ renameᵗᵐ ρ L • ρ α ⊒ renameᵗᵐ ρ L′ • ρ α ∶ c)
    (sym (renameᶜ-open-commute ρ p α))
    (α⊒α
      (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ qᶜ)
      (rename-open-cast-srcStore
        {ρ = ρ} {σ = σ} {α = α} {q = q} {p = p} hρ pαᶜ)
      L⊒L′)

rename-⊒α :
  ∀ {ρ Δ Δ′ σ γ L L′ p A B C D α} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ L ⊒ renameᵗᵐ ρ L′
    ∶ renameᶜ ρ (gen B p) →
  Δ′ ∣ (ρ α ꞉= renameᵗ ρ A ⊒) ∷ renameStoreNrw ρ σ
    ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ L ⊒ renameᵗᵐ ρ L′ • ρ α
    ∶ renameᶜ ρ (p [ α ]ᶜ)
rename-⊒α {ρ = ρ} {σ = σ} {γ = γ} {L = L} {L′ = L′}
    {p = p} {A = A} {α = α} hρ pαᶜ L⊒L′ =
  subst
    (λ c → _ ∣ (ρ α ꞉= renameᵗ ρ A ⊒) ∷ renameStoreNrw ρ σ
      ∣ renameCtxNrw ρ γ
      ⊢ renameᵗᵐ ρ L ⊒ renameᵗᵐ ρ L′ • ρ α ∶ c)
    (sym (renameᶜ-open-commute ρ p α))
    (⊒α
      (rename-open-widen-cast-srcStore
        {ρ = ρ} {σ = σ} {α = α} {A = A} {p = p} hρ pαᶜ)
      L⊒L′)

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

rename-⊒cast+ :
  ∀ {ρ Δ Δ′ σ γ M M′ q r s A B C D} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s ≈ renameᶜ ρ r
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ r →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ (M′ ⟨ - s ⟩) ∶ renameᶜ ρ q
rename-⊒cast+ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {M = M} {M′ = M′} {q = q} {s = s} hρ qᶜ q⨟s≈r M⊒M′ =
  subst
    (λ T → Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
      ⊢ renameᵗᵐ ρ M ⊒ T ∶ renameᶜ ρ q)
    (sym (cong (λ c → renameᵗᵐ ρ M′ ⟨ c ⟩)
               (renameᶜ-dual-normal ρ s)))
    (⊒cast+
      (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ qᶜ)
      q⨟s≈r
      M⊒M′)

rename-⊒cast- :
  ∀ {ρ Δ Δ′ σ γ M M′ q r s A B C D} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ q ⨾ⁿ renameᶜ ρ s ≈ renameᶜ ρ r
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ q →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ (M′ ⟨ s ⟩) ∶ renameᶜ ρ r
rename-⊒cast- {ρ = ρ} {σ = σ} hρ qᶜ q⨟s≈r M⊒M′ =
  ⊒cast-
    (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ qᶜ)
    q⨟s≈r
    M⊒M′

rename-cast+⊒ :
  ∀ {ρ Δ Δ′ σ γ M M′ p r t A B C D} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ r ≈ renameᶜ ρ t ⨾ⁿ renameᶜ ρ p
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ p →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ (M ⟨ - t ⟩) ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ r
rename-cast+⊒ {ρ = ρ} {Δ′ = Δ′} {σ = σ} {γ = γ}
    {M = M} {M′ = M′} {p = p} {r = r} {t = t}
    hρ pᶜ r≈t⨟p M⊒M′ =
  subst
    (λ T → Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
      ⊢ T ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ r)
    (sym (cong (λ c → renameᵗᵐ ρ M ⟨ c ⟩)
               (renameᶜ-dual-normal ρ t)))
    (cast+⊒
      (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ pᶜ)
      r≈t⨟p
      M⊒M′)

rename-cast-⊒ :
  ∀ {ρ Δ Δ′ σ γ M M′ p r t A B C D} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ′ ∣ renameStoreNrw ρ σ
    ⊢ renameᶜ ρ r ≈ renameᶜ ρ t ⨾ⁿ renameᶜ ρ p
    ∶ renameᵗ ρ A ⊒ renameᵗ ρ B →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ r →
  Δ′ ∣ renameStoreNrw ρ σ ∣ renameCtxNrw ρ γ
    ⊢ renameᵗᵐ ρ (M ⟨ t ⟩) ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ p
rename-cast-⊒ {ρ = ρ} {σ = σ} hρ pᶜ r≈t⨟p M⊒M′ =
  cast-⊒
    (rename-cast-srcStore {ρ = ρ} {σ = σ} hρ pᶜ)
    r≈t⨟p
    M⊒M′

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

≈ⁿ-⇑ˢ :
  ∀ {Δ σ s t A B} →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ s ≈ ⇑ᶜ t ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
≈ⁿ-⇑ˢ (endpointsⁿ {s = s} {t = t}
    srcs tgts srct tgtt σ⊒ (hA , hB) (hA′ , hB′) s⊒ t⊒) =
  endpointsⁿ
    (trans (src-renameᶜ suc s) (cong ⇑ᵗ srcs))
    (trans (tgt-renameᶜ suc s) (cong ⇑ᵗ tgts))
    (trans (src-renameᶜ suc t) (cong ⇑ᵗ srct))
    (trans (tgt-renameᶜ suc t) (cong ⇑ᵗ tgtt))
    (⊒ˢ-⇑ˢ σ⊒)
    (WfTyˢ-⇑ᵗ hA , WfTyˢ-⇑ᵗ hB)
    (WfTyˢ-⇑ᵗ hA′ , WfTyˢ-⇑ᵗ hB′)
    (narrow-⇑ᵗ-any s⊒)
    (narrow-⇑ᵗ-any t⊒)

compose-leftⁿ-⇑ˢ :
  ∀ {Δ σ q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ q ⨾ⁿ ⇑ᶜ s ≈ ⇑ᶜ r ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
compose-leftⁿ-⇑ˢ (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  let
    q⊒′ = narrow-⇑ᵗ-gen q⊒
    s⊒′ = narrow-⇑ᵗ-gen s⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒
    new = _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} q⊒′ s⊒′
    u≡ =
      narrowing-determinedᵐ (StoreDetWf-⟰ᵗ wfΣ)
        (proj₂ new)
        (narrow-⇑ᵗ-gen (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ u ≈ ⇑ᶜ _ ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-⇑ˢ q⨟s≈r)
  in
  compose-leftⁿ (StoreDetWf-⟰ᵗ wfΣ) q⊒′ s⊒′ eq′

compose-rightⁿ-⇑ˢ :
  ∀ {Δ σ r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ r ≈ ⇑ᶜ t ⨾ⁿ ⇑ᶜ p ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
compose-rightⁿ-⇑ˢ (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  let
    t⊒′ = narrow-⇑ᵗ-gen t⊒
    p⊒′ = narrow-⇑ᵗ-gen p⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒
    new = _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} t⊒′ p⊒′
    u≡ =
      narrowing-determinedᵐ (StoreDetWf-⟰ᵗ wfΣ)
        (proj₂ new)
        (narrow-⇑ᵗ-gen (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ ⇑ᶜ _ ≈ u ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-⇑ˢ r≈t⨟p)
  in
  compose-rightⁿ (StoreDetWf-⟰ᵗ wfΣ) t⊒′ p⊒′ eq′

shift-⊒cast+ :
  ∀ {Δ σ γ M M′ q r s A B C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ r →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ (M′ ⟨ - s ⟩) ∶ ⇑ᶜ q
shift-⊒cast+ {Δ = Δ} {σ = σ} {γ = γ} {M = M} {M′ = M′}
    {q = q} {s = s} qᶜ q⨟s≈r M⊒M′ =
  subst
    (λ T → suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ ⇑ᵗᵐ M ⊒ T ∶ ⇑ᶜ q)
    (sym (cong (λ c → ⇑ᵗᵐ M′ ⟨ c ⟩) (renameᶜ-dual-normal suc s)))
    (⊒cast+
      (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
      (compose-leftⁿ-⇑ˢ q⨟s≈r)
      M⊒M′)

shift-⊒cast- :
  ∀ {Δ σ γ M M′ q r s A B C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ q →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ (M′ ⟨ s ⟩) ∶ ⇑ᶜ r
shift-⊒cast- {σ = σ} qᶜ q⨟s≈r M⊒M′ =
  ⊒cast-
    (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
    (compose-leftⁿ-⇑ˢ q⨟s≈r)
    M⊒M′

shift-cast+⊒ :
  ∀ {Δ σ γ M M′ p r t A B C D} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ p →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ (M ⟨ - t ⟩) ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ r
shift-cast+⊒ {Δ = Δ} {σ = σ} {γ = γ} {M = M} {M′ = M′}
    {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒M′ =
  subst
    (λ T → suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ T ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ r)
    (sym (cong (λ c → ⇑ᵗᵐ M ⟨ c ⟩) (renameᶜ-dual-normal suc t)))
    (cast+⊒
      (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} pᶜ)
      (compose-rightⁿ-⇑ˢ r≈t⨟p)
      M⊒M′)

shift-cast-⊒ :
  ∀ {Δ σ γ M M′ p r t A B C D} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ ⇑ᵗᵐ M ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ r →
  suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ
    ⊢ ⇑ᵗᵐ (M ⟨ t ⟩) ⊒ ⇑ᵗᵐ M′ ∶ ⇑ᶜ p
shift-cast-⊒ {σ = σ} pᶜ r≈t⨟p M⊒M′ =
  cast-⊒
    (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} pᶜ)
    (compose-rightⁿ-⇑ˢ r≈t⨟p)
    M⊒M′

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

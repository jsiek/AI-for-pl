module proof.TermRenamingMediated where

-- File Charter:
--   * Term-variable renaming for the mediated term-narrowing relation.
--   * Provides context-renaming frames and the main
--     `term-renaming-narrowingᵐ` theorem.
--   * Kept separate so substitution and beta proof helpers can import this
--     without growing the main DGG module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym)

open import Types
open import Coercions
open import NuTerms
open import StoreCorrespondence
open import MediatedNarrowing
open import TermNarrowingSeparated using
  ( CtxCorr
  ; CtxCorrEntry
  ; ctx-entry
  ; leftCtx
  ; rightCtx
  ; ⇑ᵍᶜ
  ; leftCtx-⇑ᵍᶜ
  ; rightCtx-⇑ᵍᶜ
  ; shiftCtxCorrEntry
  )
open import proof.NuTermProperties using
  ( RenameWf
  ; RenameWf-ext
  ; RenameWf-⤊
  ; renameˣ-renameᵗᵐ
  ; renameˣᵐ-preserves-Value
  ; renameˣᵐ-preserves-No•
  ; typing-renameˣ
  )

------------------------------------------------------------------------
-- Lookup through mapped correspondence contexts
------------------------------------------------------------------------

lookup-mapᶜ :
  ∀ {γ x entry} {f : CtxCorrEntry → CtxCorrEntry} →
  γ ∋ x ⦂ entry →
  map f γ ∋ x ⦂ f entry
lookup-mapᶜ Z = Z
lookup-mapᶜ (S h) = S (lookup-mapᶜ h)

lookup-map-invᶜ :
  ∀ {γ x entry′} {f : CtxCorrEntry → CtxCorrEntry} →
  map f γ ∋ x ⦂ entry′ →
  ∃[ entry ] (γ ∋ x ⦂ entry × entry′ ≡ f entry)
lookup-map-invᶜ {γ = entry ∷ γ} {x = zero} Z = entry , Z , refl
lookup-map-invᶜ {γ = entry ∷ γ} {x = suc x} (S h)
    with lookup-map-invᶜ h
lookup-map-invᶜ {γ = entry ∷ γ} {x = suc x} (S h)
    | entry′ , h′ , eq = entry′ , S h′ , eq

------------------------------------------------------------------------
-- Context renamings
------------------------------------------------------------------------

record RenameCtxᵐ (γ γ′ : CtxCorr) (ρˣ : Renameˣ) : Set₁ where
  constructor rename-ctxᵐ
  field
    corr-ren :
      ∀ {x A B p} →
      γ ∋ x ⦂ ctx-entry A B p →
      γ′ ∋ ρˣ x ⦂ ctx-entry A B p
    left-ren : RenameWf (leftCtx γ) (leftCtx γ′) ρˣ
    right-ren : RenameWf (rightCtx γ) (rightCtx γ′) ρˣ

open RenameCtxᵐ

RenameCtx-ext :
  ∀ {γ γ′ ρˣ entry} →
  RenameCtxᵐ γ γ′ ρˣ →
  RenameCtxᵐ (entry ∷ γ) (entry ∷ γ′) (extʳ ρˣ)
RenameCtx-ext ρᶜ = rename-ctxᵐ corr left right
  where
    corr :
      ∀ {x A B p} →
      _ ∋ x ⦂ ctx-entry A B p →
      _ ∋ extʳ _ x ⦂ ctx-entry A B p
    corr Z = Z
    corr (S h) = S (corr-ren ρᶜ h)

    left : RenameWf _ _ (extʳ _)
    left = RenameWf-ext (left-ren ρᶜ)

    right : RenameWf _ _ (extʳ _)
    right = RenameWf-ext (right-ren ρᶜ)

RenameCtx-map-corr :
  ∀ {γ γ′ ρˣ} {f : CtxCorrEntry → CtxCorrEntry} →
  RenameCtxᵐ γ γ′ ρˣ →
  ∀ {x entry} →
  map f γ ∋ x ⦂ entry →
  map f γ′ ∋ ρˣ x ⦂ entry
RenameCtx-map-corr ρᶜ h with lookup-map-invᶜ h
RenameCtx-map-corr ρᶜ h | ctx-entry A B p , h′ , refl =
  lookup-mapᶜ (corr-ren ρᶜ h′)

RenameCtx-⇑ᵍᶜ :
  ∀ {γ γ′ ρˣ} →
  RenameCtxᵐ γ γ′ ρˣ →
  RenameCtxᵐ (⇑ᵍᶜ γ) (⇑ᵍᶜ γ′) ρˣ
RenameCtx-⇑ᵍᶜ {γ = γ} {γ′ = γ′} {ρˣ = ρˣ} ρᶜ =
  rename-ctxᵐ corr left right
  where
    corr :
      ∀ {x A B p} →
      ⇑ᵍᶜ γ ∋ x ⦂ ctx-entry A B p →
      ⇑ᵍᶜ γ′ ∋ ρˣ x ⦂ ctx-entry A B p
    corr = RenameCtx-map-corr ρᶜ

    left : RenameWf (leftCtx (⇑ᵍᶜ γ)) (leftCtx (⇑ᵍᶜ γ′)) ρˣ
    left h =
      subst
        (λ Γ → Γ ∋ ρˣ _ ⦂ _)
        (sym (leftCtx-⇑ᵍᶜ γ′))
        (RenameWf-⤊ (left-ren ρᶜ)
          (subst (λ Γ → Γ ∋ _ ⦂ _) (leftCtx-⇑ᵍᶜ γ) h))

    right : RenameWf (rightCtx (⇑ᵍᶜ γ)) (rightCtx (⇑ᵍᶜ γ′)) ρˣ
    right h =
      subst
        (λ Γ → Γ ∋ ρˣ _ ⦂ _)
        (sym (rightCtx-⇑ᵍᶜ γ′))
        (RenameWf-⤊ (right-ren ρᶜ)
          (subst (λ Γ → Γ ∋ _ ⦂ _) (rightCtx-⇑ᵍᶜ γ) h))

RenameCtx-⇑ʳᵍᶜ :
  ∀ {γ γ′ ρˣ} →
  RenameCtxᵐ γ γ′ ρˣ →
  RenameCtxᵐ (⇑ʳᵍᶜ γ) (⇑ʳᵍᶜ γ′) ρˣ
RenameCtx-⇑ʳᵍᶜ {γ = γ} {γ′ = γ′} {ρˣ = ρˣ} ρᶜ =
  rename-ctxᵐ corr left right
  where
    corr :
      ∀ {x A B p} →
      ⇑ʳᵍᶜ γ ∋ x ⦂ ctx-entry A B p →
      ⇑ʳᵍᶜ γ′ ∋ ρˣ x ⦂ ctx-entry A B p
    corr = RenameCtx-map-corr ρᶜ

    left : RenameWf (leftCtx (⇑ʳᵍᶜ γ)) (leftCtx (⇑ʳᵍᶜ γ′)) ρˣ
    left h =
      subst
        (λ Γ → Γ ∋ ρˣ _ ⦂ _)
        (sym (leftCtx-⇑ʳᵍᶜ γ′))
        (left-ren ρᶜ
          (subst (λ Γ → Γ ∋ _ ⦂ _) (leftCtx-⇑ʳᵍᶜ γ) h))

    right : RenameWf (rightCtx (⇑ʳᵍᶜ γ)) (rightCtx (⇑ʳᵍᶜ γ′)) ρˣ
    right h =
      subst
        (λ Γ → Γ ∋ ρˣ _ ⦂ _)
        (sym (rightCtx-⇑ʳᵍᶜ γ′))
        (RenameWf-⤊ (right-ren ρᶜ)
          (subst (λ Γ → Γ ∋ _ ⦂ _) (rightCtx-⇑ʳᵍᶜ γ) h))

renameˣ-⇑ᵗᵐ• :
  ∀ ρˣ M →
  renameˣᵐ ρˣ (⇑ᵗᵐ M •) ≡ ⇑ᵗᵐ (renameˣᵐ ρˣ M) •
renameˣ-⇑ᵗᵐ• ρˣ M = cong _• (renameˣ-renameᵗᵐ ρˣ suc M)

------------------------------------------------------------------------
-- Renaming preserves mediated term narrowing
------------------------------------------------------------------------

term-renaming-narrowingᵐ :
  ∀ {ΔL ΔR ρ γ γ′ M M′ p A B ρˣ} →
  RenameCtxᵐ γ γ′ ρˣ →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ΔL ∣ ΔR ∣ ρ ∣ γ′ ⊢ renameˣᵐ ρˣ M ⊒ renameˣᵐ ρˣ M′
    ∶ p ⦂ A ⊒ᵐ B
term-renaming-narrowingᵐ ρᶜ (⊒blameᵗ M⊢ p⊒) =
  ⊒blameᵗ (typing-renameˣ (left-ren ρᶜ) M⊢) p⊒
term-renaming-narrowingᵐ ρᶜ (x⊒xᵗ pᶜ x∋p) =
  x⊒xᵗ pᶜ (corr-ren ρᶜ x∋p)
term-renaming-narrowingᵐ ρᶜ (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  ƛ⊒ƛᵗ p↦qᶜ (term-renaming-narrowingᵐ (RenameCtx-ext ρᶜ) N⊒N′)
term-renaming-narrowingᵐ ρᶜ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  ·⊒·ᵗ p↦qᶜ
    (term-renaming-narrowingᵐ ρᶜ L⊒L′)
    (term-renaming-narrowingᵐ ρᶜ M⊒M′)
term-renaming-narrowingᵐ ρᶜ (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′) =
  Λ⊒Λᵗ allᶜ
    (renameˣᵐ-preserves-Value _ vV)
    (renameˣᵐ-preserves-Value _ vV′)
    (term-renaming-narrowingᵐ (RenameCtx-⇑ᵍᶜ ρᶜ) V⊒V′)
term-renaming-narrowingᵐ ρᶜ (⊒Λᵗ N⊢ genᶜ vV′ N⊒V′) =
  ⊒Λᵗ
    (typing-renameˣ (left-ren ρᶜ) N⊢)
    genᶜ
    (renameˣᵐ-preserves-Value _ vV′)
    (term-renaming-narrowingᵐ (RenameCtx-⇑ʳᵍᶜ ρᶜ) N⊒V′)
term-renaming-narrowingᵐ ρᶜ
    (⊒⟨ν⟩ᵗ N⊢ genS⊢ V′⊢ genᶜ i N⊒V′s) =
  ⊒⟨ν⟩ᵗ
    (typing-renameˣ (left-ren ρᶜ) N⊢)
    genS⊢
    (typing-renameˣ (right-ren ρᶜ) V′⊢)
    genᶜ
    i
    (term-renaming-narrowingᵐ (RenameCtx-⇑ʳᵍᶜ ρᶜ) N⊒V′s)
term-renaming-narrowingᵐ {γ′ = γ′} {ρˣ = ρˣ} ρᶜ
    (α⊒αᵗ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {L = L} {L′ = L′}
      {p = p} {A = A} {B = B} {C = C} {D = D}
      vL noL vL′ noL′ qᶜ pᶜ L⊒L′) =
  subst
    (λ L₀ →
      suc ΔL ∣ suc ΔR
        ∣ matched zero (⇑ᵗ A) zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ ∣ γ′
        ⊢ L₀ ⊒ renameˣᵐ ρˣ (⇑ᵗᵐ L′ •) ∶ p ⦂ C ⊒ᵐ D)
    (sym (renameˣ-⇑ᵗᵐ• ρˣ L))
    (subst
      (λ L₀′ →
        suc ΔL ∣ suc ΔR
          ∣ matched zero (⇑ᵗ A) zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ ∣ γ′
          ⊢ ⇑ᵗᵐ (renameˣᵐ ρˣ L) • ⊒ L₀′ ∶ p ⦂ C ⊒ᵐ D)
      (sym (renameˣ-⇑ᵗᵐ• ρˣ L′))
      (α⊒αᵗ
        (renameˣᵐ-preserves-Value ρˣ vL)
        (renameˣᵐ-preserves-No• ρˣ noL)
        (renameˣᵐ-preserves-Value ρˣ vL′)
        (renameˣᵐ-preserves-No• ρˣ noL′)
        qᶜ
        pᶜ
        (term-renaming-narrowingᵐ ρᶜ L⊒L′)))
term-renaming-narrowingᵐ {γ′ = γ′} {ρˣ = ρˣ} ρᶜ
    (⊒αᵗ {ΔL = ΔL} {ΔR = ΔR} {ρ = ρ} {L = L} {L′ = L′}
      {p = p} {A = A} {B = B} {D = D} vL′ noL′ pᶜ L⊒L′) =
  subst
    (λ L₀′ →
      ΔL ∣ suc ΔR ∣ right-only zero (⇑ᵗ A) ∷ ⇑ʳᶜorr ρ ∣ γ′
        ⊢ renameˣᵐ ρˣ L ⊒ L₀′ ∶ p ⦂ B ⊒ᵐ D)
    (sym (renameˣ-⇑ᵗᵐ• ρˣ L′))
    (⊒αᵗ
      (renameˣᵐ-preserves-Value ρˣ vL′)
      (renameˣᵐ-preserves-No• ρˣ noL′)
      pᶜ
      (term-renaming-narrowingᵐ ρᶜ L⊒L′))
term-renaming-narrowingᵐ ρᶜ
    (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′) =
  ν⊒νᵗ
    hA
    hA′
    (typing-renameˣ (left-ren ρᶜ) N⊢)
    (typing-renameˣ (right-ren ρᶜ) N′⊢)
    sₗ⊢
    sᵣ⊢
    pᶜ
    qᶜ
    (term-renaming-narrowingᵐ (RenameCtx-⇑ᵍᶜ ρᶜ) N⊒N′)
term-renaming-narrowingᵐ ρᶜ
    (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′) =
  ⊒νᵗ
    (typing-renameˣ (left-ren ρᶜ) N⊢)
    hA
    (typing-renameˣ (right-ren ρᶜ) N′⊢)
    s⊢
    pᶜ
    (term-renaming-narrowingᵐ ρᶜ N⊒N′)
term-renaming-narrowingᵐ ρᶜ (κ⊒κᵗ κ pᶜ) = κ⊒κᵗ κ pᶜ
term-renaming-narrowingᵐ ρᶜ (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′) =
  ⊕⊒⊕ᵗ pᶜ
    (term-renaming-narrowingᵐ ρᶜ M⊒M′)
    (term-renaming-narrowingᵐ ρᶜ N⊒N′)
term-renaming-narrowingᵐ ρᶜ (⊒cast+ᵗ pᶜ r⊒ t⊒ʳ M⊒M′) =
  ⊒cast+ᵗ pᶜ r⊒ t⊒ʳ (term-renaming-narrowingᵐ ρᶜ M⊒M′)
term-renaming-narrowingᵐ ρᶜ (⊒cast-ᵗ pᶜ r⊒ t⊒ʳ M⊒M′) =
  ⊒cast-ᵗ pᶜ r⊒ t⊒ʳ (term-renaming-narrowingᵐ ρᶜ M⊒M′)
term-renaming-narrowingᵐ ρᶜ (cast+⊒ᵗ qᶜ r⊒ s⊒ˡ M⊒M′) =
  cast+⊒ᵗ qᶜ r⊒ s⊒ˡ (term-renaming-narrowingᵐ ρᶜ M⊒M′)
term-renaming-narrowingᵐ ρᶜ (cast-⊒ᵗ qᶜ r⊒ s⊒ˡ M⊒M′) =
  cast-⊒ᵗ qᶜ r⊒ s⊒ˡ (term-renaming-narrowingᵐ ρᶜ M⊒M′)

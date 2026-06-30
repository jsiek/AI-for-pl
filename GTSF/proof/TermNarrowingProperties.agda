module proof.TermNarrowingProperties where

-- File Charter:
--   * Admissible rules and structural lemmas for term narrowing.
--   * Currently provides the two cambridge23 two-sided cast derived rules.
--   * Depends on the public definitions in `TermNarrowing` and `NarrowWiden`.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing using
  (_∣_∣_⊢_⊒_∶_; ⇑ᵍ; ·⊒·; ƛ⊒ƛ; x⊒x; ⊒blame; ⊒cast+;
   ⊒cast-; cast+⊒; cast-⊒)
open import proof.CoercionProperties using (renameᶜ-dual-normal)
open import proof.NarrowWidenProperties using (narrow-⇑ᵗ-ᶜ-srcStoreⁿ)

variable
  Δ : TyCtx
  σ : StoreNrw
  γ : CtxNrw
  A B : Ty
  p q r s t : Coercion
  M M′ : Term

------------------------------------------------------------------------
-- Constructor-level type-context shifting
------------------------------------------------------------------------

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
    ⊢ ⇑ᵗᵐ L · ⇑ᵗᵐ M
      ⊒ ⇑ᵗᵐ L′ · ⇑ᵗᵐ M′ ∶ ⇑ᶜ q
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

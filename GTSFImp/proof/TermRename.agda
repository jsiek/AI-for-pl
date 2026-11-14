module proof.TermRename where

-- File Charter:
--   * Renaming the type variables of a term along an embedding is the
--     identity at the identity embedding and respects composition of
--     embeddings (notes/logrel-dgg.md, Section 7, item 1).
--   * No function extensionality: environments are vectors, and every
--     other piece of evidence inside a cast is first-order data or a
--     negation (definitionally unique, since ⊥ is proof irrelevant).
--   * Casts and conversions with different endpoint types are compared
--     by packing them with their endpoints and using plain _≡_.

open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (zero; suc)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Types
open import Consistency
open import Conversion
open import CastTerms
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
open import proof.Imprecision using (∈ᵗ-unique)
open import proof.TypeInTermSubst using (toRename-id-eq; renameᵗ-id)

------------------------------------------------------------------------
-- Packing a cast or conversion with its endpoints
------------------------------------------------------------------------

record Packed {Δ} (R : Ty Δ → Ty Δ → Set) : Set where
  constructor ⟪_⟫
  field
    {src tgt} : Ty Δ
    elem : R src tgt

infix 4 _≈ᶜ_ _≈↑_ _≈↓_

_≈ᶜ_ : ∀ {Δ} {μ : Env∼ Δ} {A B A′ B′ : Ty Δ}
  → μ ⊢ A ∼ B → μ ⊢ A′ ∼ B′ → Set
_≈ᶜ_ {μ = μ} c c′ = ⟪_⟫ {R = μ ⊢_∼_} c ≡ ⟪ c′ ⟫

_≈↑_ : ∀ {Δ} {A B A′ B′ : Ty Δ} → Conv↑ Δ A B → Conv↑ Δ A′ B′ → Set
_≈↑_ {Δ} c c′ = ⟪_⟫ {R = Conv↑ Δ} c ≡ ⟪ c′ ⟫

_≈↓_ : ∀ {Δ} {A B A′ B′ : Ty Δ} → Conv↓ Δ A B → Conv↓ Δ A′ B′ → Set
_≈↓_ {Δ} c c′ = ⟪_⟫ {R = Conv↓ Δ} c ≡ ⟪ c′ ⟫

------------------------------------------------------------------------
-- Renamings: composition and identity, pointwise
------------------------------------------------------------------------

ext-∘ : ∀ {Δ₁ Δ₂ Δ₃}
    {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ : Δ₁ ⇒ʳ Δ₃}
  → (∀ X → ρ₂ (ρ₁ X) ≡ ρ X)
  → ∀ X → extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ ρ X
ext-∘ h Fin.zero = refl
ext-∘ h (Fin.suc X) = cong Fin.suc (h X)

ext-id : ∀ {Δ} {ρ : Δ ⇒ʳ Δ}
  → (∀ X → ρ X ≡ X)
  → ∀ X → extᵗ ρ X ≡ X
ext-id h Fin.zero = refl
ext-id h (Fin.suc X) = cong Fin.suc (h X)

ty-∘ : ∀ {Δ₁ Δ₂ Δ₃}
    {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ : Δ₁ ⇒ʳ Δ₃}
  → (∀ X → ρ₂ (ρ₁ X) ≡ ρ X)
  → (A : Ty Δ₁)
  → renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ ρ A
ty-∘ {ρ₁ = ρ₁} {ρ₂} h A =
  trans (renameᵗ-comp ρ₁ ρ₂ A) (renameᵗ-cong A h)

ty-id : ∀ {Δ} {ρ : Δ ⇒ʳ Δ}
  → (∀ X → ρ X ≡ X)
  → (A : Ty Δ)
  → renameᵗ ρ A ≡ A
ty-id h A = trans (renameᵗ-cong A h) (renameᵗ-id A)

------------------------------------------------------------------------
-- Uniqueness of the gate evidence
------------------------------------------------------------------------

X∼★≢★∼X∼★ : X∼★ ≡ ★∼X∼★ → ⊥
X∼★≢★∼X∼★ ()

★∼X≢★∼X∼★ : ★∼X ≡ ★∼X∼★ → ⊥
★∼X≢★∼X∼★ ()

∼★-unique : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ} (p q : μ ⊢ G ∼★) → p ≡ q
∼★-unique ⇒∼★ ⇒∼★ = refl
∼★-unique ι∼★ ι∼★ = refl
∼★-unique (X∼★ᵍ e) (X∼★ᵍ e′) = cong X∼★ᵍ (uip e e′)
∼★-unique (X∼★ᵍ e) (X∼★ᶜ e′) = ⊥-elim (X∼★≢★∼X∼★ (trans (sym e) e′))
∼★-unique (X∼★ᶜ e) (X∼★ᵍ e′) = ⊥-elim (X∼★≢★∼X∼★ (trans (sym e′) e))
∼★-unique (X∼★ᶜ e) (X∼★ᶜ e′) = cong X∼★ᶜ (uip e e′)
∼★-unique ∀∼★ ∀∼★ = refl

★∼-unique : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ} (p q : μ ⊢★∼ G) → p ≡ q
★∼-unique ★∼⇒ ★∼⇒ = refl
★∼-unique ★∼ι ★∼ι = refl
★∼-unique (★∼Xᵍ e) (★∼Xᵍ e′) = cong ★∼Xᵍ (uip e e′)
★∼-unique (★∼Xᵍ e) (★∼Xᶜ e′) = ⊥-elim (★∼X≢★∼X∼★ (trans (sym e) e′))
★∼-unique (★∼Xᶜ e) (★∼Xᵍ e′) = ⊥-elim (★∼X≢★∼X∼★ (trans (sym e′) e))
★∼-unique (★∼Xᶜ e) (★∼Xᶜ e′) = cong ★∼Xᶜ (uip e e′)
★∼-unique ★∼∀ ★∼∀ = refl

------------------------------------------------------------------------
-- Congruences for packed casts
------------------------------------------------------------------------

private
  variable
    Δ Δ′ Δ₁ Δ₂ Δ₃ : TyCtx

id-var-≈ : ∀ {μ : Env∼ Δ} {X Y : TyVar Δ}
  → X ≡ Y → id {μ = μ} (＇ X) ≈ᶜ id (＇ Y)
id-var-≈ refl = refl

↦-≈ : ∀ {μ : Env∼ Δ} {A A′ B B′ C C′ D D′ : Ty Δ}
    {c : flipᵐ μ ⊢ A′ ∼ A} {c′ : flipᵐ μ ⊢ C′ ∼ C}
    {d : μ ⊢ B ∼ B′} {d′ : μ ⊢ D ∼ D′}
  → c ≈ᶜ c′ → d ≈ᶜ d′ → (c ↦ d) ≈ᶜ (c′ ↦ d′)
↦-≈ refl refl = refl

∀-≈ : ∀ {μ : Env∼ Δ} {A B A′ B′ : Ty (suc Δ)}
    {c : extᵐ μ ⊢ A ∼ B} {c′ : extᵐ μ ⊢ A′ ∼ B′}
  → c ≈ᶜ c′ → (∀ᶜ c) ≈ᶜ (∀ᶜ c′)
∀-≈ refl = refl

!-≈ : ∀ {μ : Env∼ Δ} {A A′ G G′ : Ty Δ}
    {g : Ground G} {g′ : Ground G′}
    {s : μ ⊢ G ∼★} {s′ : μ ⊢ G′ ∼★}
    {n : NonStar A} {n′ : NonStar A′}
    {c : μ ⊢ A ∼ G} {c′ : μ ⊢ A′ ∼ G′}
  → c ≈ᶜ c′
  → (_! ⦃ g ⦄ ⦃ s ⦄ c ⦃ n ⦄) ≈ᶜ (_! ⦃ g′ ⦄ ⦃ s′ ⦄ c′ ⦃ n′ ⦄)
!-≈ {g = g} {g′} {s} {s′} {n} {n′} refl
  rewrite ground-unique g g′ | ∼★-unique s s′ | nonStar-unique n n′ =
  refl

？-≈ : ∀ {μ : Env∼ Δ} {B B′ G G′ : Ty Δ}
    {g : Ground G} {g′ : Ground G′}
    {s : μ ⊢★∼ G} {s′ : μ ⊢★∼ G′}
    {n : NonStar B} {n′ : NonStar B′}
    {c : μ ⊢ G ∼ B} {c′ : μ ⊢ G′ ∼ B′}
  → c ≈ᶜ c′
  → (？_ ⦃ g ⦄ ⦃ s ⦄ c ⦃ n ⦄) ≈ᶜ (？_ ⦃ g′ ⦄ ⦃ s′ ⦄ c′ ⦃ n′ ⦄)
？-≈ {g = g} {g′} {s} {s′} {n} {n′} refl
  rewrite ground-unique g g′ | ★∼-unique s s′ | nonStar-unique n n′ =
  refl

inst-≈ : ∀ {μ : Env∼ Δ} {A A′ : Ty (suc Δ)} {B B′ : Ty Δ}
    {v : NonVar A} {v′ : NonVar A′}
    {z : Fin.zero ∈ᵗ A} {z′ : Fin.zero ∈ᵗ A′}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B} {c′ : instᵐ μ ⊢ A′ ∼ ⇑ᵗ B′}
    {h : B ≢ ★} {h′ : B′ ≢ ★}
  → B ≡ B′
  → c ≈ᶜ c′
  → (inst_ ⦃ v ⦄ ⦃ z ⦄ c h) ≈ᶜ (inst_ ⦃ v′ ⦄ ⦃ z′ ⦄ c′ h′)
inst-≈ {v = v} {v′} {z} {z′} refl refl
  rewrite nonVar-unique v v′ | ∈ᵗ-unique z z′ =
  refl

gen-≈ : ∀ {μ : Env∼ Δ} {A A′ : Ty Δ} {B B′ : Ty (suc Δ)}
    {v : NonVar B} {v′ : NonVar B′}
    {z : Fin.zero ∈ᵗ B} {z′ : Fin.zero ∈ᵗ B′}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B} {c′ : genᵐ μ ⊢ ⇑ᵗ A′ ∼ B′}
    {h : A ≢ ★} {h′ : A′ ≢ ★}
  → A ≡ A′
  → c ≈ᶜ c′
  → (gen_ ⦃ v ⦄ ⦃ z ⦄ c h) ≈ᶜ (gen_ ⦃ v′ ⦄ ⦃ z′ ⦄ c′ h′)
gen-≈ {v = v} {v′} {z} {z′} refl refl
  rewrite nonVar-unique v v′ | ∈ᵗ-unique z z′ =
  refl

subst-right-≈ : ∀ {μ : Env∼ Δ} {A B B′ : Ty Δ}
  → (e : B ≡ B′) (c : μ ⊢ A ∼ B)
  → subst-right-∼ e c ≈ᶜ c
subst-right-≈ refl c = refl

subst-left-≈ : ∀ {μ : Env∼ Δ} {A A′ B : Ty Δ}
  → (e : A ≡ A′) (c : μ ⊢ A ∼ B)
  → subst-left-∼ e c ≈ᶜ c
subst-left-≈ refl c = refl

rename-subst-right-≈ : ∀ {μ : Env∼ Δ₁} {μ′ : Env∼ Δ₂} {A B B′ : Ty Δ₁}
  → (ρ : Δ₁ ⇒ʳ Δ₂) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X)
  → (e : B ≡ B′) (c : μ ⊢ A ∼ B)
  → rename∼ {μ′ = μ′} ρ eq (subst-right-∼ e c)
    ≈ᶜ rename∼ {μ′ = μ′} ρ eq c
rename-subst-right-≈ ρ eq refl c = refl

rename-subst-left-≈ : ∀ {μ : Env∼ Δ₁} {μ′ : Env∼ Δ₂} {A A′ B : Ty Δ₁}
  → (ρ : Δ₁ ⇒ʳ Δ₂) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X)
  → (e : A ≡ A′) (c : μ ⊢ A ∼ B)
  → rename∼ {μ′ = μ′} ρ eq (subst-left-∼ e c)
    ≈ᶜ rename∼ {μ′ = μ′} ρ eq c
rename-subst-left-≈ ρ eq refl c = refl

------------------------------------------------------------------------
-- Renaming casts
------------------------------------------------------------------------

rename∼-∘ : ∀ {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {μ₃ : Env∼ Δ₃} {A B}
    (ρ₁ : Δ₁ ⇒ʳ Δ₂) (ρ₂ : Δ₂ ⇒ʳ Δ₃) (ρ : Δ₁ ⇒ʳ Δ₃)
    (eq₁ : ∀ X → μ₂ ‼ (ρ₁ X) ≡ μ₁ ‼ X)
    (eq₂ : ∀ X → μ₃ ‼ (ρ₂ X) ≡ μ₂ ‼ X)
    (eq : ∀ X → μ₃ ‼ (ρ X) ≡ μ₁ ‼ X)
  → (∀ X → ρ₂ (ρ₁ X) ≡ ρ X)
  → (c : μ₁ ⊢ A ∼ B)
  → rename∼ {μ′ = μ₃} ρ₂ eq₂ (rename∼ {μ′ = μ₂} ρ₁ eq₁ c)
    ≈ᶜ rename∼ {μ′ = μ₃} ρ eq c
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (id ★) = refl
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (id (‵ ι)) = refl
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (id (＇ X)) = id-var-≈ (h X)
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (c ↦ d) =
  ↦-≈ (rename∼-∘ ρ₁ ρ₂ ρ _ _ _ h c) (rename∼-∘ ρ₁ ρ₂ ρ _ _ _ h d)
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (∀ᶜ c) =
  ∀-≈ (rename∼-∘ (extᵗ ρ₁) (extᵗ ρ₂) (extᵗ ρ) _ _ _ (ext-∘ h) c)
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (c !) =
  !-≈ (rename∼-∘ ρ₁ ρ₂ ρ _ _ _ h c)
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h (？ c) =
  ？-≈ (rename∼-∘ ρ₁ ρ₂ ρ _ _ _ h c)
rename∼-∘ {μ₃ = μ₃} ρ₁ ρ₂ ρ eq₁ eq₂ eq h
    (inst_ {B = B} c B≢★) =
  inst-≈ (ty-∘ h B)
    (trans (subst-right-≈ (renameᵗ-shift ρ₂ (renameᵗ ρ₁ B)) _)
    (trans (rename-subst-right-≈ (extᵗ ρ₂) (instᵐ-rename ρ₂ eq₂)
              (renameᵗ-shift ρ₁ B) _)
    (trans (rename∼-∘ (extᵗ ρ₁) (extᵗ ρ₂) (extᵗ ρ) _ _ _ (ext-∘ h) c)
      (sym (subst-right-≈ (renameᵗ-shift ρ B) _)))))
rename∼-∘ {μ₃ = μ₃} ρ₁ ρ₂ ρ eq₁ eq₂ eq h
    (gen_ {A = A} c A≢★) =
  gen-≈ (ty-∘ h A)
    (trans (subst-left-≈ (renameᵗ-shift ρ₂ (renameᵗ ρ₁ A)) _)
    (trans (rename-subst-left-≈ (extᵗ ρ₂) (genᵐ-rename ρ₂ eq₂)
              (renameᵗ-shift ρ₁ A) _)
    (trans (rename∼-∘ (extᵗ ρ₁) (extᵗ ρ₂) (extᵗ ρ) _ _ _ (ext-∘ h) c)
      (sym (subst-left-≈ (renameᵗ-shift ρ A) _)))))
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h bot-elim = refl
rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h bot-intro = refl

rename∼-id : ∀ {μ : Env∼ Δ} {A B}
    (ρ : Δ ⇒ʳ Δ) (eq : ∀ X → μ ‼ (ρ X) ≡ μ ‼ X)
  → (∀ X → ρ X ≡ X)
  → (c : μ ⊢ A ∼ B)
  → rename∼ {μ′ = μ} ρ eq c ≈ᶜ c
rename∼-id ρ eq h (id ★) = refl
rename∼-id ρ eq h (id (‵ ι)) = refl
rename∼-id ρ eq h (id (＇ X)) = id-var-≈ (h X)
rename∼-id ρ eq h (c ↦ d) =
  ↦-≈ (rename∼-id ρ _ h c) (rename∼-id ρ _ h d)
rename∼-id ρ eq h (∀ᶜ c) = ∀-≈ (rename∼-id (extᵗ ρ) _ (ext-id h) c)
rename∼-id ρ eq h (c !) = !-≈ (rename∼-id ρ _ h c)
rename∼-id ρ eq h (？ c) = ？-≈ (rename∼-id ρ _ h c)
rename∼-id ρ eq h (inst_ {B = B} c B≢★) =
  inst-≈ (ty-id h B)
    (trans (subst-right-≈ (renameᵗ-shift ρ B) _)
      (rename∼-id (extᵗ ρ) _ (ext-id h) c))
rename∼-id ρ eq h (gen_ {A = A} c A≢★) =
  gen-≈ (ty-id h A)
    (trans (subst-left-≈ (renameᵗ-shift ρ A) _)
      (rename∼-id (extᵗ ρ) _ (ext-id h) c))
rename∼-id ρ eq h bot-elim = refl
rename∼-id ρ eq h bot-intro = refl

------------------------------------------------------------------------
-- Renaming conversions
------------------------------------------------------------------------

mutual
  rename↑-∘ : ∀ {A B}
      {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ : Δ₁ ⇒ʳ Δ₃}
    → (∀ X → ρ₂ (ρ₁ X) ≡ ρ X)
    → (c : Conv↑ Δ₁ A B)
    → rename↑ ρ₂ (rename↑ ρ₁ c) ≈↑ rename↑ ρ c
  rename↑-∘ h (unseal X R) =
    cong₂ (λ Y S → ⟪ unseal Y S ⟫) (h X) (ty-∘ h R)
  rename↑-∘ h (c ↦↑ d) = ↦↑-≈ (rename↓-∘ h c) (rename↑-∘ h d)
  rename↑-∘ h (`∀↑ c) = ∀↑-≈ (rename↑-∘ (ext-∘ h) c)
  rename↑-∘ h (id↑ A) = cong (λ T → ⟪ id↑ T ⟫) (ty-∘ h A)

  rename↓-∘ : ∀ {A B}
      {ρ₁ : Δ₁ ⇒ʳ Δ₂} {ρ₂ : Δ₂ ⇒ʳ Δ₃} {ρ : Δ₁ ⇒ʳ Δ₃}
    → (∀ X → ρ₂ (ρ₁ X) ≡ ρ X)
    → (c : Conv↓ Δ₁ A B)
    → rename↓ ρ₂ (rename↓ ρ₁ c) ≈↓ rename↓ ρ c
  rename↓-∘ h (seal X R) =
    cong₂ (λ Y S → ⟪ seal Y S ⟫) (h X) (ty-∘ h R)
  rename↓-∘ h (c ↦↓ d) = ↦↓-≈ (rename↑-∘ h c) (rename↓-∘ h d)
  rename↓-∘ h (`∀↓ c) = ∀↓-≈ (rename↓-∘ (ext-∘ h) c)
  rename↓-∘ h (id↓ A) = cong (λ T → ⟪ id↓ T ⟫) (ty-∘ h A)

  ↦↑-≈ : ∀ {A A′ B B′ C C′ D D′ : Ty Δ}
      {c : Conv↓ Δ A′ A} {c′ : Conv↓ Δ C′ C}
      {d : Conv↑ Δ B B′} {d′ : Conv↑ Δ D D′}
    → c ≈↓ c′ → d ≈↑ d′ → (c ↦↑ d) ≈↑ (c′ ↦↑ d′)
  ↦↑-≈ refl refl = refl

  ↦↓-≈ : ∀ {A A′ B B′ C C′ D D′ : Ty Δ}
      {c : Conv↑ Δ A′ A} {c′ : Conv↑ Δ C′ C}
      {d : Conv↓ Δ B B′} {d′ : Conv↓ Δ D D′}
    → c ≈↑ c′ → d ≈↓ d′ → (c ↦↓ d) ≈↓ (c′ ↦↓ d′)
  ↦↓-≈ refl refl = refl

  ∀↑-≈ : ∀ {A B A′ B′ : Ty (suc Δ)}
      {c : Conv↑ (suc Δ) A B} {c′ : Conv↑ (suc Δ) A′ B′}
    → c ≈↑ c′ → (`∀↑ c) ≈↑ (`∀↑ c′)
  ∀↑-≈ refl = refl

  ∀↓-≈ : ∀ {A B A′ B′ : Ty (suc Δ)}
      {c : Conv↓ (suc Δ) A B} {c′ : Conv↓ (suc Δ) A′ B′}
    → c ≈↓ c′ → (`∀↓ c) ≈↓ (`∀↓ c′)
  ∀↓-≈ refl = refl

mutual
  rename↑-id : ∀ {A B} {ρ : Δ ⇒ʳ Δ}
    → (∀ X → ρ X ≡ X)
    → (c : Conv↑ Δ A B)
    → rename↑ ρ c ≈↑ c
  rename↑-id h (unseal X R) =
    cong₂ (λ Y S → ⟪ unseal Y S ⟫) (h X) (ty-id h R)
  rename↑-id h (c ↦↑ d) = ↦↑-≈ (rename↓-id h c) (rename↑-id h d)
  rename↑-id h (`∀↑ c) = ∀↑-≈ (rename↑-id (ext-id h) c)
  rename↑-id h (id↑ A) = cong (λ T → ⟪ id↑ T ⟫) (ty-id h A)

  rename↓-id : ∀ {A B} {ρ : Δ ⇒ʳ Δ}
    → (∀ X → ρ X ≡ X)
    → (c : Conv↓ Δ A B)
    → rename↓ ρ c ≈↓ c
  rename↓-id h (seal X R) =
    cong₂ (λ Y S → ⟪ seal Y S ⟫) (h X) (ty-id h R)
  rename↓-id h (c ↦↓ d) = ↦↓-≈ (rename↑-id h c) (rename↓-id h d)
  rename↓-id h (`∀↓ c) = ∀↓-≈ (rename↓-id (ext-id h) c)
  rename↓-id h (id↓ A) = cong (λ T → ⟪ id↓ T ⟫) (ty-id h A)

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

renameEnv∼-∘ : (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂) (μ : Env∼ Δ₁)
  → renameEnv∼ π (renameEnv∼ η μ) ≡ renameEnv∼ (π ∘↪ η) μ
renameEnv∼-∘ π empty [] = refl
renameEnv∼-∘ (skip π) (keep η) (v ∷ μ) =
  cong (X∼X ∷_) (renameEnv∼-∘ π (keep η) (v ∷ μ))
renameEnv∼-∘ (skip π) (skip η) μ =
  cong (X∼X ∷_) (renameEnv∼-∘ π (skip η) μ)
renameEnv∼-∘ (keep π) (keep η) (v ∷ μ) =
  cong (v ∷_) (renameEnv∼-∘ π η μ)
renameEnv∼-∘ (keep π) (skip η) μ = cong (X∼X ∷_) (renameEnv∼-∘ π η μ)

renameEnv∼-id : ∀ (μ : Env∼ Δ) → renameEnv∼ id↪ᵗ μ ≡ μ
renameEnv∼-id [] = refl
renameEnv∼-id (v ∷ μ) = cong (v ∷_) (renameEnv∼-id μ)

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

castPacked : ∀ {μ : Env∼ Δ} → Term Δ → Packed (μ ⊢_∼_) → Term Δ
castPacked M ⟪ c ⟫ = M ⟨ c ⟩

cast-∘ : ∀ {μ₁ : Env∼ Δ₁} {μ₂ : Env∼ Δ₂} {ν ν′ : Env∼ Δ₃} {A B}
    {M M′ : Term Δ₃}
    (ρ₁ : Δ₁ ⇒ʳ Δ₂) (ρ₂ : Δ₂ ⇒ʳ Δ₃) (ρ : Δ₁ ⇒ʳ Δ₃)
    (eq₁ : ∀ X → μ₂ ‼ (ρ₁ X) ≡ μ₁ ‼ X)
    (eq₂ : ∀ X → ν ‼ (ρ₂ X) ≡ μ₂ ‼ X)
    (eq : ∀ X → ν′ ‼ (ρ X) ≡ μ₁ ‼ X)
  → M ≡ M′
  → ν ≡ ν′
  → (∀ X → ρ₂ (ρ₁ X) ≡ ρ X)
  → (c : μ₁ ⊢ A ∼ B)
  → M ⟨ rename∼ {μ′ = ν} ρ₂ eq₂ (rename∼ {μ′ = μ₂} ρ₁ eq₁ c) ⟩
    ≡ M′ ⟨ rename∼ {μ′ = ν′} ρ eq c ⟩
cast-∘ {ν = ν} {M = M} ρ₁ ρ₂ ρ eq₁ eq₂ eq refl refl h c =
  cong (castPacked {μ = ν} M) (rename∼-∘ ρ₁ ρ₂ ρ eq₁ eq₂ eq h c)

cast-id : ∀ {μ ν : Env∼ Δ} {A B} {M M′ : Term Δ}
    (ρ : Δ ⇒ʳ Δ) (eq : ∀ X → ν ‼ (ρ X) ≡ μ ‼ X)
  → M ≡ M′
  → ν ≡ μ
  → (∀ X → ρ X ≡ X)
  → (c : μ ⊢ A ∼ B)
  → M ⟨ rename∼ {μ′ = ν} ρ eq c ⟩ ≡ M′ ⟨ c ⟩
cast-id {μ = μ} {M = M} ρ eq refl refl h c =
  cong (castPacked {μ = μ} M) (rename∼-id ρ eq h c)

⦂∀-cong : ∀ {L L′ : Term Δ} {C C′ : Ty (suc Δ)} {A A′ : Ty Δ}
  → L ≡ L′ → C ≡ C′ → A ≡ A′ → (L ⦂∀ C [ A ]) ≡ (L′ ⦂∀ C′ [ A′ ])
⦂∀-cong refl refl refl = refl

↑-cong : ∀ {M M′ : Term Δ} {A B A′ B′}
    {c : Conv↑ Δ A B} {c′ : Conv↑ Δ A′ B′}
  → M ≡ M′ → c ≈↑ c′ → (M ↑ c) ≡ (M′ ↑ c′)
↑-cong refl refl = refl

↓-cong : ∀ {M M′ : Term Δ} {A B A′ B′}
    {c : Conv↓ Δ A B} {c′ : Conv↓ Δ A′ B′}
  → M ≡ M′ → c ≈↓ c′ → (M ↓ c) ≡ (M′ ↓ c′)
↓-cong refl refl = refl

toRenameᵗ-∘′ : (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂)
  → ∀ X → toRenameᵗ π (toRenameᵗ η X) ≡ toRenameᵗ (π ∘↪ η) X
toRenameᵗ-∘′ π η X = sym (toRenameᵗ-∘ π η X)

renameᵗᵐ-∘ : (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂) (M : Term Δ₁)
  → renameᵗᵐ π (renameᵗᵐ η M) ≡ renameᵗᵐ (π ∘↪ η) M
renameᵗᵐ-∘ π η (` x) = refl
renameᵗᵐ-∘ π η (ƛ M) = cong ƛ_ (renameᵗᵐ-∘ π η M)
renameᵗᵐ-∘ π η (L · M) = cong₂ _·_ (renameᵗᵐ-∘ π η L) (renameᵗᵐ-∘ π η M)
renameᵗᵐ-∘ π η (Λ M) = cong Λ_ (renameᵗᵐ-∘ (keep π) (keep η) M)
renameᵗᵐ-∘ π η (L ⦂∀ C [ A ]) =
  ⦂∀-cong (renameᵗᵐ-∘ π η L)
    (ty-∘ (toRenameᵗ-∘′ (keep π) (keep η)) C)
    (ty-∘ (toRenameᵗ-∘′ π η) A)
renameᵗᵐ-∘ π η ($ κ) = refl
renameᵗᵐ-∘ π η (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′) (renameᵗᵐ-∘ π η L) (renameᵗᵐ-∘ π η M)
renameᵗᵐ-∘ π η (_⟨_⟩ M {μ = μ} c) =
  cast-∘ {μ₂ = renameEnv∼ η μ} {ν = renameEnv∼ π (renameEnv∼ η μ)}
    {ν′ = renameEnv∼ (π ∘↪ η) μ}
    (toRenameᵗ η) (toRenameᵗ π) (toRenameᵗ (π ∘↪ η))
    (renameEnv∼-preserves η μ)
    (renameEnv∼-preserves π (renameEnv∼ η μ))
    (renameEnv∼-preserves (π ∘↪ η) μ)
    (renameᵗᵐ-∘ π η M) (renameEnv∼-∘ π η μ) (toRenameᵗ-∘′ π η) c
renameᵗᵐ-∘ π η (M ↑ c) =
  ↑-cong (renameᵗᵐ-∘ π η M) (rename↑-∘ (toRenameᵗ-∘′ π η) c)
renameᵗᵐ-∘ π η (M ↓ c) =
  ↓-cong (renameᵗᵐ-∘ π η M) (rename↓-∘ (toRenameᵗ-∘′ π η) c)
renameᵗᵐ-∘ π η blame = refl

renameᵗᵐ-id : (M : Term Δ) → renameᵗᵐ id↪ᵗ M ≡ M
renameᵗᵐ-id (` x) = refl
renameᵗᵐ-id (ƛ M) = cong ƛ_ (renameᵗᵐ-id M)
renameᵗᵐ-id (L · M) = cong₂ _·_ (renameᵗᵐ-id L) (renameᵗᵐ-id M)
renameᵗᵐ-id (Λ M) = cong Λ_ (renameᵗᵐ-id M)
renameᵗᵐ-id (L ⦂∀ C [ A ]) =
  ⦂∀-cong (renameᵗᵐ-id L) (ty-id toRename-id-eq C)
    (ty-id toRename-id-eq A)
renameᵗᵐ-id ($ κ) = refl
renameᵗᵐ-id (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′) (renameᵗᵐ-id L) (renameᵗᵐ-id M)
renameᵗᵐ-id (_⟨_⟩ M {μ = μ} c) =
  cast-id {ν = renameEnv∼ id↪ᵗ μ} (toRenameᵗ id↪ᵗ) (renameEnv∼-preserves id↪ᵗ μ)
    (renameᵗᵐ-id M) (renameEnv∼-id μ) toRename-id-eq c
renameᵗᵐ-id (M ↑ c) =
  ↑-cong (renameᵗᵐ-id M) (rename↑-id toRename-id-eq c)
renameᵗᵐ-id (M ↓ c) =
  ↓-cong (renameᵗᵐ-id M) (rename↓-id toRename-id-eq c)
renameᵗᵐ-id blame = refl

------------------------------------------------------------------------
-- Renaming along pointwise-equal renamings
------------------------------------------------------------------------

rename∼-≈ : ∀ {μ : Env∼ Δ₁} {μ′ : Env∼ Δ₂} {A B A′ B′ : Ty Δ₁}
    (ρ : Δ₁ ⇒ʳ Δ₂) (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X)
    {c : μ ⊢ A ∼ B} {c′ : μ ⊢ A′ ∼ B′}
  → c ≈ᶜ c′ → rename∼ {μ′ = μ′} ρ eq c ≈ᶜ rename∼ {μ′ = μ′} ρ eq c′
rename∼-≈ ρ eq refl = refl

rename∼-cong : ∀ {μ : Env∼ Δ₁} {μ′ : Env∼ Δ₂} {A B}
    (ρ ρ′ : Δ₁ ⇒ʳ Δ₂)
    (eq : ∀ X → μ′ ‼ (ρ X) ≡ μ ‼ X) (eq′ : ∀ X → μ′ ‼ (ρ′ X) ≡ μ ‼ X)
  → (∀ X → ρ X ≡ ρ′ X)
  → (c : μ ⊢ A ∼ B)
  → rename∼ {μ′ = μ′} ρ eq c ≈ᶜ rename∼ {μ′ = μ′} ρ′ eq′ c
rename∼-cong {μ = μ} ρ ρ′ eq eq′ h c =
  trans
    (sym (rename∼-≈ ρ eq
      (rename∼-id (λ X → X) (λ X → refl) (λ X → refl) c)))
    (rename∼-∘ {μ₂ = μ} (λ X → X) ρ ρ′ (λ X → refl) eq eq′ h c)

cast-cong : ∀ {μ : Env∼ Δ₁} {ν ν′ : Env∼ Δ₂} {A B} {M M′ : Term Δ₂}
    (ρ ρ′ : Δ₁ ⇒ʳ Δ₂)
    (eq : ∀ X → ν ‼ (ρ X) ≡ μ ‼ X) (eq′ : ∀ X → ν′ ‼ (ρ′ X) ≡ μ ‼ X)
  → M ≡ M′
  → ν ≡ ν′
  → (∀ X → ρ X ≡ ρ′ X)
  → (c : μ ⊢ A ∼ B)
  → M ⟨ rename∼ {μ′ = ν} ρ eq c ⟩ ≡ M′ ⟨ rename∼ {μ′ = ν′} ρ′ eq′ c ⟩
cast-cong {ν = ν} {M = M} ρ ρ′ eq eq′ refl refl h c =
  cong (castPacked {μ = ν} M) (rename∼-cong ρ ρ′ eq eq′ h c)

ext-cong : ∀ {ρ ρ′ : Δ ⇒ʳ Δ′}
  → (∀ X → ρ X ≡ ρ′ X) → ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
ext-cong h Fin.zero = refl
ext-cong h (Fin.suc X) = cong Fin.suc (h X)

mutual
  rename↑-cong : ∀ {A B : Ty Δ} {ρ ρ′ : Δ ⇒ʳ Δ′}
    → (∀ X → ρ X ≡ ρ′ X)
    → (c : Conv↑ Δ A B)
    → rename↑ ρ c ≈↑ rename↑ ρ′ c
  rename↑-cong h (unseal X R) =
    cong₂ (λ Y S → ⟪ unseal Y S ⟫) (h X) (renameᵗ-cong R h)
  rename↑-cong h (c ↦↑ d) = ↦↑-≈ (rename↓-cong h c) (rename↑-cong h d)
  rename↑-cong h (`∀↑ c) = ∀↑-≈ (rename↑-cong (ext-cong h) c)
  rename↑-cong h (id↑ A) = cong (λ T → ⟪ id↑ T ⟫) (renameᵗ-cong A h)

  rename↓-cong : ∀ {A B : Ty Δ} {ρ ρ′ : Δ ⇒ʳ Δ′}
    → (∀ X → ρ X ≡ ρ′ X)
    → (c : Conv↓ Δ A B)
    → rename↓ ρ c ≈↓ rename↓ ρ′ c
  rename↓-cong h (seal X R) =
    cong₂ (λ Y S → ⟪ seal Y S ⟫) (h X) (renameᵗ-cong R h)
  rename↓-cong h (c ↦↓ d) = ↦↓-≈ (rename↑-cong h c) (rename↓-cong h d)
  rename↓-cong h (`∀↓ c) = ∀↓-≈ (rename↓-cong (ext-cong h) c)
  rename↓-cong h (id↓ A) = cong (λ T → ⟪ id↓ T ⟫) (renameᵗ-cong A h)

module proof.LR-narrow.TermRenamingComposition where

-- File Charter:
--   * Composition of two order-preserving type-variable renamings of a cast
--     term is the renaming by the composite embedding.
--   * Handles the dependent consistency and conversion evidence carried by
--     casts through heterogeneous equality.
--   * Relates the LR's future lifting of endpoint terms and types to the
--     renaming by the future's endpoint embeddings.

import Data.Fin as Fin
import Data.Nat as Nat
import Relation.Binary.HeterogeneousEquality as HE
open import proof.LR-narrow.FunExt using (funext)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Types
open import Consistency
open import Conversion
open import CastTerms
open import proof.TypeInTermSubst using (toRename-wk-eq)
open import proof.Imprecision using (∈ᵗ-unique)
open import proof.LR-narrow.TypeRenamingComposition

------------------------------------------------------------------------
-- Composite embeddings
------------------------------------------------------------------------

-- The composite of two type renamings, pointwise.

comp : ∀ {Δ₀ Δ₁ Δ₂} → Δ₀ ⇒ʳ Δ₁ → Δ₁ ⇒ʳ Δ₂ → Δ₀ ⇒ʳ Δ₂
comp rho₁ rho₂ X = rho₂ (rho₁ X)

ext-comp-pointwise : ∀ {Δ₀ Δ₁ Δ₂}
    (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
  → ∀ X → extᵗ rho₂ (extᵗ rho₁ X) ≡ extᵗ (comp rho₁ rho₂) X
ext-comp-pointwise rho₁ rho₂ Fin.zero = refl
ext-comp-pointwise rho₁ rho₂ (Fin.suc X) = refl

renameᵗ-∘ : ∀ {Δ₀ Δ₁ Δ₂}
    (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂) (A : Ty Δ₀)
  → renameᵗ rho₂ (renameᵗ rho₁ A) ≡ renameᵗ (comp rho₁ rho₂) A
renameᵗ-∘ rho₁ rho₂ A = renameᵗ-comp rho₁ rho₂ A

------------------------------------------------------------------------
-- Conversion evidence
------------------------------------------------------------------------

mutual
  reveal-pointwise : ∀ {Δ Δ′} (rho tau : Δ ⇒ʳ Δ′)
      (eq : ∀ X → rho X ≡ tau X)
      {A B : Ty Δ} (c : Conv↑ Δ A B)
    → pack↑ (rename↑ rho c) ≡ pack↑ (rename↑ tau c)
  reveal-pointwise rho tau eq (unseal X R)
      rewrite eq X | renameᵗ-cong R eq = refl
  reveal-pointwise rho tau eq (c ↦↑ d) =
    cong₂ pack-↦↑ (conceal-pointwise rho tau eq c)
      (reveal-pointwise rho tau eq d)
  reveal-pointwise rho tau eq (`∀↑ c) =
    cong pack-∀↑
      (reveal-pointwise (extᵗ rho) (extᵗ tau) (ext-pointwise eq) c)
  reveal-pointwise rho tau eq (id↑ A)
      rewrite renameᵗ-cong A eq = refl

  conceal-pointwise : ∀ {Δ Δ′} (rho tau : Δ ⇒ʳ Δ′)
      (eq : ∀ X → rho X ≡ tau X)
      {A B : Ty Δ} (c : Conv↓ Δ A B)
    → pack↓ (rename↓ rho c) ≡ pack↓ (rename↓ tau c)
  conceal-pointwise rho tau eq (seal X R)
      rewrite eq X | renameᵗ-cong R eq = refl
  conceal-pointwise rho tau eq (c ↦↓ d) =
    cong₂ pack-↦↓ (reveal-pointwise rho tau eq c)
      (conceal-pointwise rho tau eq d)
  conceal-pointwise rho tau eq (`∀↓ c) =
    cong pack-∀↓
      (conceal-pointwise (extᵗ rho) (extᵗ tau) (ext-pointwise eq) c)
  conceal-pointwise rho tau eq (id↓ A)
      rewrite renameᵗ-cong A eq = refl

mutual
  reveal-∘ : ∀ {Δ₀ Δ₁ Δ₂}
      (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
      {A B : Ty Δ₀} (c : Conv↑ Δ₀ A B)
    → pack↑ (rename↑ rho₂ (rename↑ rho₁ c))
      ≡ pack↑ (rename↑ (comp rho₁ rho₂) c)
  reveal-∘ rho₁ rho₂ (unseal X R)
      rewrite renameᵗ-∘ rho₁ rho₂ R = refl
  reveal-∘ rho₁ rho₂ (c ↦↑ d) =
    cong₂ pack-↦↑ (conceal-∘ rho₁ rho₂ c) (reveal-∘ rho₁ rho₂ d)
  reveal-∘ rho₁ rho₂ (`∀↑ c) =
    cong pack-∀↑
      (trans (reveal-∘ (extᵗ rho₁) (extᵗ rho₂) c)
        (reveal-pointwise _ _ (ext-comp-pointwise rho₁ rho₂) c))
  reveal-∘ rho₁ rho₂ (id↑ A)
      rewrite renameᵗ-∘ rho₁ rho₂ A = refl

  conceal-∘ : ∀ {Δ₀ Δ₁ Δ₂}
      (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
      {A B : Ty Δ₀} (c : Conv↓ Δ₀ A B)
    → pack↓ (rename↓ rho₂ (rename↓ rho₁ c))
      ≡ pack↓ (rename↓ (comp rho₁ rho₂) c)
  conceal-∘ rho₁ rho₂ (seal X R)
      rewrite renameᵗ-∘ rho₁ rho₂ R = refl
  conceal-∘ rho₁ rho₂ (c ↦↓ d) =
    cong₂ pack-↦↓ (reveal-∘ rho₁ rho₂ c) (conceal-∘ rho₁ rho₂ d)
  conceal-∘ rho₁ rho₂ (`∀↓ c) =
    cong pack-∀↓
      (trans (conceal-∘ (extᵗ rho₁) (extᵗ rho₂) c)
        (conceal-pointwise _ _ (ext-comp-pointwise rho₁ rho₂) c))
  conceal-∘ rho₁ rho₂ (id↓ A)
      rewrite renameᵗ-∘ rho₁ rho₂ A = refl

------------------------------------------------------------------------
-- Consistency evidence
------------------------------------------------------------------------

-- Environment coherence of a composite renaming below a binder, stated
-- for the composite of the extended renamings.

ext-comp-env : ∀ {Δ₀ Δ₂} {mu : Env∼ Δ₀} {mu′ : Env∼ Δ₂}
    {Δ₁} (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
  → (∀ X → mu′ (comp rho₁ rho₂ X) ≡ mu X)
  → ∀ X → extᵐ mu′ (comp (extᵗ rho₁) (extᵗ rho₂) X) ≡ extᵐ mu X
ext-comp-env rho₁ rho₂ eq Fin.zero = refl
ext-comp-env rho₁ rho₂ eq (Fin.suc X) = eq X

inst-comp-env : ∀ {Δ₀ Δ₂} {mu : Env∼ Δ₀} {mu′ : Env∼ Δ₂}
    {Δ₁} (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
  → (∀ X → mu′ (comp rho₁ rho₂ X) ≡ mu X)
  → ∀ X → instᵐ mu′ (comp (extᵗ rho₁) (extᵗ rho₂) X) ≡ instᵐ mu X
inst-comp-env rho₁ rho₂ eq Fin.zero = refl
inst-comp-env rho₁ rho₂ eq (Fin.suc X) = eq X

gen-comp-env : ∀ {Δ₀ Δ₂} {mu : Env∼ Δ₀} {mu′ : Env∼ Δ₂}
    {Δ₁} (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
  → (∀ X → mu′ (comp rho₁ rho₂ X) ≡ mu X)
  → ∀ X → genᵐ mu′ (comp (extᵗ rho₁) (extᵗ rho₂) X) ≡ genᵐ mu X
gen-comp-env rho₁ rho₂ eq Fin.zero = refl
gen-comp-env rho₁ rho₂ eq (Fin.suc X) = eq X

-- Renaming consistency evidence twice is renaming it once by the
-- composite, heterogeneously over the composite types and environment.

rename∼-∘≅ : ∀ {Δ₀ Δ₁ Δ₂}
    {mu₀ : Env∼ Δ₀} {mu₁ : Env∼ Δ₁} {mu₂ mu₂′ : Env∼ Δ₂}
    (rho₁ : Δ₀ ⇒ʳ Δ₁) (rho₂ : Δ₁ ⇒ʳ Δ₂)
    (eq₁ : ∀ X → mu₁ (rho₁ X) ≡ mu₀ X)
    (eq₂ : ∀ X → mu₂ (rho₂ X) ≡ mu₁ X)
    (eq : ∀ X → mu₂′ (comp rho₁ rho₂ X) ≡ mu₀ X)
  → mu₂ ≡ mu₂′
  → ∀ {A B} (c : mu₀ ⊢ A ∼ B)
  → HE._≅_ (rename∼ rho₂ eq₂ (rename∼ rho₁ eq₁ c))
      (rename∼ (comp rho₁ rho₂) eq c)
rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu (id ★) =
  Hcong₁ mk-id-star (HE.≡-to-≅ eq-mu)
rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu (id (‵ ι)) =
  Hcong₂ mk-id-base (HE.≡-to-≅ eq-mu) HE.refl
rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu (id (＇ X)) =
  Hcong₂ mk-id-var (HE.≡-to-≅ eq-mu) HE.refl
rename∼-∘≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂} {mu₂′ = mu₂′}
    rho₁ rho₂ eq₁ eq₂ eq eq-mu
    (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} c d) =
  Hcong₇ mk-arrow (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (renameᵗ-∘ rho₁ rho₂ A))
    (HE.≡-to-≅ (renameᵗ-∘ rho₁ rho₂ A′))
    (HE.≡-to-≅ (renameᵗ-∘ rho₁ rho₂ B))
    (HE.≡-to-≅ (renameᵗ-∘ rho₁ rho₂ B′))
    (rename∼-∘≅ {mu₀ = flipᵐ mu₀} {mu₁ = flipᵐ mu₁}
      {mu₂ = flipᵐ mu₂} {mu₂′ = flipᵐ mu₂′} rho₁ rho₂
      (flip-rename-env {μ = mu₀} {μ′ = mu₁} rho₁ eq₁)
      (flip-rename-env {μ = mu₁} {μ′ = mu₂} rho₂ eq₂)
      (flip-rename-env {μ = mu₀} {μ′ = mu₂′} (comp rho₁ rho₂) eq)
      (cong flipᵐ eq-mu) c)
    (rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu d)
rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu (∀ᶜ_ {A = A} {B = B} c) =
  Hcong₄ mk-all (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ (ext-type-eq A))
    (HE.≡-to-≅ (ext-type-eq B))
    (HE.trans
      (rename∼-∘≅ (extᵗ rho₁) (extᵗ rho₂)
        (extᵐ-rename rho₁ eq₁) (extᵐ-rename rho₂ eq₂)
        (ext-comp-env rho₁ rho₂ eq) (cong extᵐ eq-mu) c)
      (rename∼-parallel≅ (comp (extᵗ rho₁) (extᵗ rho₂))
        (extᵗ (comp rho₁ rho₂))
        (ext-comp-env rho₁ rho₂ eq)
        (extᵐ-rename (comp rho₁ rho₂) eq)
        refl (ext-comp-pointwise rho₁ rho₂) c))
  where
  ext-type-eq : ∀ (T : Ty _)
    → renameᵗ (extᵗ rho₂) (renameᵗ (extᵗ rho₁) T)
        ≡ renameᵗ (extᵗ (comp rho₁ rho₂)) T
  ext-type-eq T = trans (renameᵗ-∘ (extᵗ rho₁) (extᵗ rho₂) T)
    (renameᵗ-cong T (ext-comp-pointwise rho₁ rho₂))
rename∼-∘≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂} {mu₂′ = mu₂′}
    rho₁ rho₂ eq₁ eq₂ eq eq-mu
    (_! {A = A} {G = G} ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
  Hcong₇ mk-bang (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ G-eq)
    (transport-unique≅ (cong Ground G-eq) _ _ ground-unique)
    (transport-unique≅
      (cong₂ (λ nu T → nu ⊢ T ∼★) eq-mu G-eq)
      (rename∼★ rho₂ eq₂ (rename∼★ rho₁ eq₁ G∼★))
      (rename∼★ (comp rho₁ rho₂) eq G∼★) ∼★-unique)
    (rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu c)
    (transport-unique≅ (cong NonStar A-eq) _ _ nonStar-unique)
  where
  A-eq = renameᵗ-∘ rho₁ rho₂ A
  G-eq = renameᵗ-∘ rho₁ rho₂ G
rename∼-∘≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂} {mu₂′ = mu₂′}
    rho₁ rho₂ eq₁ eq₂ eq eq-mu
    (？_ {G = G} {B = B} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
  Hcong₇ mk-query (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ G-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong Ground G-eq) _ _ ground-unique)
    (transport-unique≅
      (cong₂ (λ nu T → nu ⊢★∼ T) eq-mu G-eq)
      (rename★∼ rho₂ eq₂ (rename★∼ rho₁ eq₁ ★∼G))
      (rename★∼ (comp rho₁ rho₂) eq ★∼G) ★∼-unique)
    (rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu c)
    (transport-unique≅ (cong NonStar B-eq) _ _ nonStar-unique)
  where
  G-eq = renameᵗ-∘ rho₁ rho₂ G
  B-eq = renameᵗ-∘ rho₁ rho₂ B
rename∼-∘≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂} {mu₂′ = mu₂′}
    rho₁ rho₂ eq₁ eq₂ eq eq-mu
    (inst_ {A = A} {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) =
  Hcong₇ mk-inst (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong NonVar A-eq) _ _ nonVar-unique)
    (transport-unique≅ (cong (Fin.zero ∈ᵗ_) A-eq) _ _ ∈ᵗ-unique)
    premise-heq
    (transport-unique≅ (cong (_≢ ★) B-eq) _ _ ¬-unique)
  where
  A-eq = trans (renameᵗ-∘ (extᵗ rho₁) (extᵗ rho₂) A)
    (renameᵗ-cong A (ext-comp-pointwise rho₁ rho₂))
  B-eq = renameᵗ-∘ rho₁ rho₂ B
  inner₁ = rename∼ (extᵗ rho₁) (instᵐ-rename rho₁ eq₁) c
  inner₂ = rename∼ (extᵗ rho₂) (instᵐ-rename rho₂ eq₂)
    (subst-right-∼ (renameᵗ-shift rho₁ B) inner₁)
  inner = rename∼ (extᵗ (comp rho₁ rho₂))
    (instᵐ-rename (comp rho₁ rho₂) eq) c
  step₁ = subst-right≅ (renameᵗ-shift rho₂ (renameᵗ rho₁ B)) inner₂
  step₂ : HE._≅_ inner₂
    (rename∼ (extᵗ rho₂) (instᵐ-rename rho₂ eq₂) inner₁)
  step₂ = rename∼-cong≅ (extᵗ rho₂) (instᵐ-rename rho₂ eq₂)
    HE.refl (HE.≡-to-≅ (sym (renameᵗ-shift rho₁ B)))
    (subst-right≅ (renameᵗ-shift rho₁ B) inner₁)
  step₃ = rename∼-∘≅ (extᵗ rho₁) (extᵗ rho₂)
    (instᵐ-rename rho₁ eq₁) (instᵐ-rename rho₂ eq₂)
    (inst-comp-env rho₁ rho₂ eq) (cong instᵐ eq-mu) c
  step₄ = rename∼-parallel≅ (comp (extᵗ rho₁) (extᵗ rho₂))
    (extᵗ (comp rho₁ rho₂))
    (inst-comp-env rho₁ rho₂ eq)
    (instᵐ-rename (comp rho₁ rho₂) eq)
    refl (ext-comp-pointwise rho₁ rho₂) c
  step₅ = subst-right≅ (renameᵗ-shift (comp rho₁ rho₂) B) inner
  premise-heq = HE.trans step₁
    (HE.trans step₂ (HE.trans step₃ (HE.trans step₄ (HE.sym step₅))))
rename∼-∘≅ {mu₀ = mu₀} {mu₁ = mu₁} {mu₂ = mu₂} {mu₂′ = mu₂′}
    rho₁ rho₂ eq₁ eq₂ eq eq-mu
    (gen_ {A = A} {B = B} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  Hcong₇ mk-gen (HE.≡-to-≅ eq-mu)
    (HE.≡-to-≅ A-eq) (HE.≡-to-≅ B-eq)
    (transport-unique≅ (cong NonVar B-eq) _ _ nonVar-unique)
    (transport-unique≅ (cong (Fin.zero ∈ᵗ_) B-eq) _ _ ∈ᵗ-unique)
    premise-heq
    (transport-unique≅ (cong (_≢ ★) A-eq) _ _ ¬-unique)
  where
  A-eq = renameᵗ-∘ rho₁ rho₂ A
  B-eq = trans (renameᵗ-∘ (extᵗ rho₁) (extᵗ rho₂) B)
    (renameᵗ-cong B (ext-comp-pointwise rho₁ rho₂))
  inner₁ = rename∼ (extᵗ rho₁) (genᵐ-rename rho₁ eq₁) c
  inner₂ = rename∼ (extᵗ rho₂) (genᵐ-rename rho₂ eq₂)
    (subst-left-∼ (renameᵗ-shift rho₁ A) inner₁)
  inner = rename∼ (extᵗ (comp rho₁ rho₂))
    (genᵐ-rename (comp rho₁ rho₂) eq) c
  step₁ = subst-left≅ (renameᵗ-shift rho₂ (renameᵗ rho₁ A)) inner₂
  step₂ : HE._≅_ inner₂
    (rename∼ (extᵗ rho₂) (genᵐ-rename rho₂ eq₂) inner₁)
  step₂ = rename∼-cong≅ (extᵗ rho₂) (genᵐ-rename rho₂ eq₂)
    (HE.≡-to-≅ (sym (renameᵗ-shift rho₁ A))) HE.refl
    (subst-left≅ (renameᵗ-shift rho₁ A) inner₁)
  step₃ = rename∼-∘≅ (extᵗ rho₁) (extᵗ rho₂)
    (genᵐ-rename rho₁ eq₁) (genᵐ-rename rho₂ eq₂)
    (gen-comp-env rho₁ rho₂ eq) (cong genᵐ eq-mu) c
  step₄ = rename∼-parallel≅ (comp (extᵗ rho₁) (extᵗ rho₂))
    (extᵗ (comp rho₁ rho₂))
    (gen-comp-env rho₁ rho₂ eq)
    (genᵐ-rename (comp rho₁ rho₂) eq)
    refl (ext-comp-pointwise rho₁ rho₂) c
  step₅ = subst-left≅ (renameᵗ-shift (comp rho₁ rho₂) A) inner
  premise-heq = HE.trans step₁
    (HE.trans step₂ (HE.trans step₃ (HE.trans step₄ (HE.sym step₅))))
rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu bot-elim =
  Hcong₁ mk-bot-elim (HE.≡-to-≅ eq-mu)
rename∼-∘≅ rho₁ rho₂ eq₁ eq₂ eq eq-mu bot-intro =
  Hcong₁ mk-bot-intro (HE.≡-to-≅ eq-mu)

------------------------------------------------------------------------
-- One weakening step after an order-preserving embedding
------------------------------------------------------------------------

-- Composition of embeddings is not canonical on the consistency
-- environments carried by casts (`empty` and `skip` fill off-image
-- variables differently), so no general composition law holds for
-- terms.  One weakening step after an embedding, possibly below type
-- binders, is the skipped embedding; this is all the LR's future
-- lifting needs.

data ShiftSquare : ∀ {Δ Δ′ Δ″}
    → Δ ↪ᵗ Δ′ → Δ′ ↪ᵗ Δ″ → Δ ↪ᵗ Δ″ → Set where
  shift-base : ∀ {Δ Δ′} (sigma : Δ ↪ᵗ Δ′)
    → ShiftSquare sigma wk↪ᵗ (skip sigma)
  shift-under : ∀ {Δ Δ′ Δ″}
      {sigma : Δ ↪ᵗ Δ′} {w : Δ′ ↪ᵗ Δ″} {xi : Δ ↪ᵗ Δ″}
    → ShiftSquare sigma w xi
    → ShiftSquare (keep sigma) (keep w) (keep xi)

renameEnv∼-id : ∀ {Δ} (mu : Env∼ Δ) X
  → renameEnv∼ id↪ᵗ mu X ≡ mu X
renameEnv∼-id {Nat.zero} mu ()
renameEnv∼-id {Nat.suc Δ} mu Fin.zero = refl
renameEnv∼-id {Nat.suc Δ} mu (Fin.suc X) =
  renameEnv∼-id (λ Y → mu (Fin.suc Y)) X

shift-pointwise : ∀ {Δ Δ′ Δ″}
    {sigma : Δ ↪ᵗ Δ′} {w : Δ′ ↪ᵗ Δ″} {xi : Δ ↪ᵗ Δ″}
  → ShiftSquare sigma w xi
  → ∀ X → comp (toRenameᵗ sigma) (toRenameᵗ w) X ≡ toRenameᵗ xi X
shift-pointwise (shift-base sigma) X = toRename-wk-eq (toRenameᵗ sigma X)
shift-pointwise (shift-under square) Fin.zero = refl
shift-pointwise (shift-under square) (Fin.suc X) =
  cong Fin.suc (shift-pointwise square X)

shift-env : ∀ {Δ Δ′ Δ″}
    {sigma : Δ ↪ᵗ Δ′} {w : Δ′ ↪ᵗ Δ″} {xi : Δ ↪ᵗ Δ″}
  → ShiftSquare sigma w xi
  → (mu : Env∼ Δ)
  → ∀ X → renameEnv∼ w (renameEnv∼ sigma mu) X ≡ renameEnv∼ xi mu X
shift-env (shift-base sigma) mu Fin.zero = refl
shift-env (shift-base sigma) mu (Fin.suc X) =
  renameEnv∼-id (renameEnv∼ sigma mu) X
shift-env (shift-under square) mu Fin.zero = refl
shift-env (shift-under square) mu (Fin.suc X) =
  shift-env square (λ Y → mu (Fin.suc Y)) X

renameᵐᶜ-shift≅ : ∀ {Δ Δ′ Δ″}
    {sigma : Δ ↪ᵗ Δ′} {w : Δ′ ↪ᵗ Δ″} {xi : Δ ↪ᵗ Δ″}
  → (square : ShiftSquare sigma w xi)
  → {mu : Env∼ Δ} {A B : Ty Δ} (c : mu ⊢ A ∼ B)
  → HE._≅_ (renameᵐᶜ w (renameᵐᶜ sigma c)) (renameᵐᶜ xi c)
renameᵐᶜ-shift≅ {sigma = sigma} {w = w} {xi = xi} square {mu = mu} c =
  HE.trans
    (rename∼-∘≅ (toRenameᵗ sigma) (toRenameᵗ w)
      (renameEnv∼-preserves sigma mu)
      (renameEnv∼-preserves w (renameEnv∼ sigma mu))
      composite-preserves
      (funext (shift-env square mu)) c)
    (rename∼-parallel≅
      (comp (toRenameᵗ sigma) (toRenameᵗ w))
      (toRenameᵗ xi)
      composite-preserves
      (renameEnv∼-preserves xi mu)
      refl (shift-pointwise square) c)
  where
  composite-preserves : ∀ X
    → renameEnv∼ xi mu (toRenameᵗ w (toRenameᵗ sigma X)) ≡ mu X
  composite-preserves X =
    trans (cong (renameEnv∼ xi mu) (shift-pointwise square X))
      (renameEnv∼-preserves xi mu X)

renameᵗ-shift↪ : ∀ {Δ Δ′ Δ″}
    {sigma : Δ ↪ᵗ Δ′} {w : Δ′ ↪ᵗ Δ″} {xi : Δ ↪ᵗ Δ″}
  → ShiftSquare sigma w xi
  → (A : Ty Δ)
  → renameᵗ (toRenameᵗ w) (renameᵗ (toRenameᵗ sigma) A)
      ≡ renameᵗ (toRenameᵗ xi) A
renameᵗ-shift↪ {sigma = sigma} {w = w} square A =
  trans (renameᵗ-∘ (toRenameᵗ sigma) (toRenameᵗ w) A)
    (renameᵗ-cong A (shift-pointwise square))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

renameᵗᵐ-shift : ∀ {Δ Δ′ Δ″}
    {sigma : Δ ↪ᵗ Δ′} {w : Δ′ ↪ᵗ Δ″} {xi : Δ ↪ᵗ Δ″}
  → ShiftSquare sigma w xi
  → (M : Term Δ)
  → renameᵗᵐ w (renameᵗᵐ sigma M) ≡ renameᵗᵐ xi M
renameᵗᵐ-shift square (` x) = refl
renameᵗᵐ-shift square (ƛ M) = cong ƛ_ (renameᵗᵐ-shift square M)
renameᵗᵐ-shift square (L · M) =
  cong₂ _·_ (renameᵗᵐ-shift square L) (renameᵗᵐ-shift square M)
renameᵗᵐ-shift square (Λ M) =
  cong Λ_ (renameᵗᵐ-shift (shift-under square) M)
renameᵗᵐ-shift square (M ⦂∀ C [ A ])
    rewrite renameᵗ-shift↪ (shift-under square) C
      | renameᵗ-shift↪ square A =
  cong (λ N → N ⦂∀ _ [ _ ]) (renameᵗᵐ-shift square M)
renameᵗᵐ-shift square ($ κ) = refl
renameᵗᵐ-shift square (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (renameᵗᵐ-shift square L) (renameᵗᵐ-shift square M)
renameᵗᵐ-shift square (M ⟨ c ⟩) =
  HE.≅-to-≡
    (Hcong₅ mk-cast-term
      (HE.≡-to-≅ (funext (shift-env square _)))
      (HE.≡-to-≅ (renameᵗ-shift↪ square _))
      (HE.≡-to-≅ (renameᵗ-shift↪ square _))
      (HE.≡-to-≅ (renameᵗᵐ-shift square M))
      (renameᵐᶜ-shift≅ square c))
renameᵗᵐ-shift {sigma = sigma} {w = w} square (M ↑ c) =
  cong₂ apply↑ (renameᵗᵐ-shift square M)
    (trans (reveal-∘ (toRenameᵗ sigma) (toRenameᵗ w) c)
      (reveal-pointwise _ _ (shift-pointwise square) c))
renameᵗᵐ-shift {sigma = sigma} {w = w} square (M ↓ c) =
  cong₂ apply↓ (renameᵗᵐ-shift square M)
    (trans (conceal-∘ (toRenameᵗ sigma) (toRenameᵗ w) c)
      (conceal-pointwise _ _ (shift-pointwise square) c))
renameᵗᵐ-shift square blame = refl

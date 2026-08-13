module LR-narrow.World where

-- File Charter:
--   * Adds mode-indexed semantic entries to a three-context GTSFImp world.
--   * Defines paired and precise-only future-world extensions.
--   * Lifts endpoint syntax and center imprecision through future worlds.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import Types
open import TyStore using (store-empty)
open import CastTerms using (Term; ⇑ᵗᵐ)
open import Primitives using (Const; κℕ; κ𝔹; constTy)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
import Imprecision as I
open import proof.ImprecisionConsistency
  using (ext-injective; fin-suc-injective; rename-⊑; subst-⊑)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import LR-narrow.WorldCore public
open import LR-narrow.Atoms public

record World (Δᴾ Δᴵ Δᶜ : TyCtx) : Set₁ where
  constructor world
  field
    core : CoreWorld Δᴾ Δᴵ Δᶜ
    semanticEntry : (Z : TyVar Δᶜ)
      → SemanticEntry core Z (impEnv core Z)

open World public

emptyWorld : World 0 0 0
emptyWorld = world
  (core-world empty empty (λ ()) store-empty store-empty) (λ ())

pairedBindWorld : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → SemanticAtom (pairedBindCore (core W) Aᴾ Aᴵ) Fin.zero
  → World (suc Δᴾ) (suc Δᴵ) (suc Δᶜ)
pairedBindWorld W Aᴾ Aᴵ fresh =
  world (pairedBindCore (core W) Aᴾ Aᴵ) atoms
  where
  atoms : (Z : TyVar _)
    → SemanticEntry (pairedBindCore (core W) Aᴾ Aᴵ) Z
        (impEnv (pairedBindCore (core W) Aᴾ Aᴵ) Z)
  atoms Fin.zero = paired-entry fresh
  atoms (Fin.suc Z) = weaken-entry Aᴾ Aᴵ (semanticEntry W Z)

preciseBindWorld : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (Aᴾ : Ty Δᴾ)
  → DynamicSemanticAtom (preciseBindCore (core W) Aᴾ) Fin.zero
  → World (suc Δᴾ) Δᴵ (suc Δᶜ)
preciseBindWorld W Aᴾ fresh =
  world (preciseBindCore (core W) Aᴾ) atoms
  where
  atoms : (Z : TyVar _)
    → SemanticEntry (preciseBindCore (core W) Aᴾ) Z
        (impEnv (preciseBindCore (core W) Aᴾ) Z)
  atoms Fin.zero = dynamic-entry fresh
  atoms (Fin.suc Z) = weaken-entry-precise Aᴾ (semanticEntry W Z)

data Future {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
    → World Δᴾ′ Δᴵ′ Δᶜ′
    → Set₁ where
  future-refl : Future W W

  future-paired : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Aᴾ : Ty Δᴾ′} {Aᴵ : Ty Δᴵ′}
    → Future W W′
    → Aᴾ ⊑ᵂ⟨ core W′ ⟩ Aᴵ
    → (fresh : SemanticAtom (pairedBindCore (core W′) Aᴾ Aᴵ) Fin.zero)
    → Future W (pairedBindWorld W′ Aᴾ Aᴵ fresh)

  future-precise : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {Aᴾ : Ty Δᴾ′}
    → Future W W′
    → (fresh : DynamicSemanticAtom
        (preciseBindCore (core W′) Aᴾ) Fin.zero)
    → Future W (preciseBindWorld W′ Aᴾ fresh)

future-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
  → Future W₀ W₁
  → Future W₁ W₂
  → Future W₀ W₂
future-trans W₀≼W₁ future-refl = W₀≼W₁
future-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) =
  future-paired (future-trans W₀≼W₁ W₁≼W₂) related fresh
future-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) =
  future-precise (future-trans W₀≼W₁ W₁≼W₂) fresh

liftPreciseTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴾ
  → Ty Δᴾ′
liftPreciseTy future-refl A = A
liftPreciseTy (future-paired W≼W′ related fresh) A =
  ⇑ᵗ (liftPreciseTy W≼W′ A)
liftPreciseTy (future-precise W≼W′ fresh) A =
  ⇑ᵗ (liftPreciseTy W≼W′ A)

liftImpreciseTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴵ
  → Ty Δᴵ′
liftImpreciseTy future-refl A = A
liftImpreciseTy (future-paired W≼W′ related fresh) A =
  ⇑ᵗ (liftImpreciseTy W≼W′ A)
liftImpreciseTy (future-precise W≼W′ fresh) A =
  liftImpreciseTy W≼W′ A

liftCenterTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᶜ
  → Ty Δᶜ′
liftCenterTy future-refl A = A
liftCenterTy (future-paired W≼W′ related fresh) A =
  ⇑ᵗ (liftCenterTy W≼W′ A)
liftCenterTy (future-precise W≼W′ fresh) A =
  ⇑ᵗ (liftCenterTy W≼W′ A)

liftCenterVariable : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TyVar Δᶜ
  → TyVar Δᶜ′
liftCenterVariable future-refl X = X
liftCenterVariable (future-paired W≼W′ related fresh) X =
  Fin.suc (liftCenterVariable W≼W′ X)
liftCenterVariable (future-precise W≼W′ fresh) X =
  Fin.suc (liftCenterVariable W≼W′ X)

liftCenterMode : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᶜ)
  → impEnv (core W′) (liftCenterVariable W≼W′ X)
      ≡ impEnv (core W) X
liftCenterMode future-refl X = refl
liftCenterMode (future-paired W≼W′ related fresh) X =
  liftCenterMode W≼W′ X
liftCenterMode (future-precise W≼W′ fresh) X =
  liftCenterMode W≼W′ X

liftPreciseTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term Δᴾ
  → Term Δᴾ′
liftPreciseTerm future-refl M = M
liftPreciseTerm (future-paired W≼W′ related fresh) M =
  ⇑ᵗᵐ (liftPreciseTerm W≼W′ M)
liftPreciseTerm (future-precise W≼W′ fresh) M =
  ⇑ᵗᵐ (liftPreciseTerm W≼W′ M)

liftImpreciseTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term Δᴵ
  → Term Δᴵ′
liftImpreciseTerm future-refl M = M
liftImpreciseTerm (future-paired W≼W′ related fresh) M =
  ⇑ᵗᵐ (liftImpreciseTerm W≼W′ M)
liftImpreciseTerm (future-precise W≼W′ fresh) M =
  liftImpreciseTerm W≼W′ M

liftPreciseTerm-variable : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) x
  → liftPreciseTerm W≼W′ (CastTerms.` x) ≡ CastTerms.` x
liftPreciseTerm-variable future-refl x = refl
liftPreciseTerm-variable (future-paired W≼W′ related fresh) x
    rewrite liftPreciseTerm-variable W≼W′ x = refl
liftPreciseTerm-variable (future-precise W≼W′ fresh) x
    rewrite liftPreciseTerm-variable W≼W′ x = refl

liftImpreciseTerm-variable : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) x
  → liftImpreciseTerm W≼W′ (CastTerms.` x) ≡ CastTerms.` x
liftImpreciseTerm-variable future-refl x = refl
liftImpreciseTerm-variable (future-paired W≼W′ related fresh) x
    rewrite liftImpreciseTerm-variable W≼W′ x = refl
liftImpreciseTerm-variable (future-precise W≼W′ fresh) x =
  liftImpreciseTerm-variable W≼W′ x

liftPreciseTerm-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftPreciseTerm W≼W′ (CastTerms.$ κ) ≡ CastTerms.$ κ
liftPreciseTerm-constant future-refl κ = refl
liftPreciseTerm-constant (future-paired W≼W′ related fresh) κ
    rewrite liftPreciseTerm-constant W≼W′ κ = refl
liftPreciseTerm-constant (future-precise W≼W′ fresh) κ
    rewrite liftPreciseTerm-constant W≼W′ κ = refl

liftImpreciseTerm-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftImpreciseTerm W≼W′ (CastTerms.$ κ) ≡ CastTerms.$ κ
liftImpreciseTerm-constant future-refl κ = refl
liftImpreciseTerm-constant (future-paired W≼W′ related fresh) κ
    rewrite liftImpreciseTerm-constant W≼W′ κ = refl
liftImpreciseTerm-constant (future-precise W≼W′ fresh) κ =
  liftImpreciseTerm-constant W≼W′ κ

liftPreciseTy-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (κ : Const)
  → liftPreciseTy W≼W′ (constTy κ) ≡ constTy κ
liftPreciseTy-constant future-refl κ = refl
liftPreciseTy-constant (future-paired W≼W′ related fresh) (κℕ n)
    rewrite liftPreciseTy-constant W≼W′ (κℕ n) = refl
liftPreciseTy-constant (future-paired W≼W′ related fresh) (κ𝔹 b)
    rewrite liftPreciseTy-constant W≼W′ (κ𝔹 b) = refl
liftPreciseTy-constant (future-precise W≼W′ fresh) (κℕ n)
    rewrite liftPreciseTy-constant W≼W′ (κℕ n) = refl
liftPreciseTy-constant (future-precise W≼W′ fresh) (κ𝔹 b)
    rewrite liftPreciseTy-constant W≼W′ (κ𝔹 b) = refl

liftImpreciseTy-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (κ : Const)
  → liftImpreciseTy W≼W′ (constTy κ) ≡ constTy κ
liftImpreciseTy-constant future-refl κ = refl
liftImpreciseTy-constant (future-paired W≼W′ related fresh) (κℕ n)
    rewrite liftImpreciseTy-constant W≼W′ (κℕ n) = refl
liftImpreciseTy-constant (future-paired W≼W′ related fresh) (κ𝔹 b)
    rewrite liftImpreciseTy-constant W≼W′ (κ𝔹 b) = refl
liftImpreciseTy-constant (future-precise W≼W′ fresh) κ =
  liftImpreciseTy-constant W≼W′ κ

liftCenterTy-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (κ : Const)
  → liftCenterTy W≼W′ (constTy κ) ≡ constTy κ
liftCenterTy-constant future-refl κ = refl
liftCenterTy-constant (future-paired W≼W′ related fresh) (κℕ n)
    rewrite liftCenterTy-constant W≼W′ (κℕ n) = refl
liftCenterTy-constant (future-paired W≼W′ related fresh) (κ𝔹 b)
    rewrite liftCenterTy-constant W≼W′ (κ𝔹 b) = refl
liftCenterTy-constant (future-precise W≼W′ fresh) (κℕ n)
    rewrite liftCenterTy-constant W≼W′ (κℕ n) = refl
liftCenterTy-constant (future-precise W≼W′ fresh) (κ𝔹 b)
    rewrite liftCenterTy-constant W≼W′ (κ𝔹 b) = refl

liftCenterTy-arrow : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A B : Ty Δᶜ)
  → liftCenterTy W≼W′ (A ⇒ B) ≡
      (liftCenterTy W≼W′ A ⇒ liftCenterTy W≼W′ B)
liftCenterTy-arrow future-refl A B = refl
liftCenterTy-arrow (future-paired W≼W′ related fresh) A B
    rewrite liftCenterTy-arrow W≼W′ A B = refl
liftCenterTy-arrow (future-precise W≼W′ fresh) A B
    rewrite liftCenterTy-arrow W≼W′ A B = refl

liftPreciseBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᴾ)
  → Ty (suc Δᴾ′)
liftPreciseBody future-refl A = A
liftPreciseBody (future-paired W≼W′ related fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ A)
liftPreciseBody (future-precise W≼W′ fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ A)

liftImpreciseBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᴵ)
  → Ty (suc Δᴵ′)
liftImpreciseBody future-refl A = A
liftImpreciseBody (future-paired W≼W′ related fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftImpreciseBody W≼W′ A)
liftImpreciseBody (future-precise W≼W′ fresh) A =
  liftImpreciseBody W≼W′ A

liftCenterBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᶜ)
  → Ty (suc Δᶜ′)
liftCenterBody future-refl A = A
liftCenterBody (future-paired W≼W′ related fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftCenterBody W≼W′ A)
liftCenterBody (future-precise W≼W′ fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftCenterBody W≼W′ A)

liftCenterImprecision : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty Δᶜ}
  → (W≼W′ : Future W W′)
  → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W′) I.⊢ liftCenterTy W≼W′ Aᴾ
      ⊑ liftCenterTy W≼W′ Aᴵ
liftCenterImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftCenterImprecision (future-paired W≼W′ related fresh) Aᴾ⊑Aᴵ =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)
    (liftCenterImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterImprecision (future-precise W≼W′ fresh) Aᴾ⊑Aᴵ =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)
    (liftCenterImprecision W≼W′ Aᴾ⊑Aᴵ)

liftCenterBodyImprecision :
    ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Aᴾ Aᴵ : Ty (suc Δᶜ)}
  → (W≼W′ : Future W W′)
  → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → I.extᵐ (impEnv (core W′)) I.⊢ liftCenterBody W≼W′ Aᴾ
      ⊑ liftCenterBody W≼W′ Aᴵ
liftCenterBodyImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftCenterBodyImprecision
    (future-paired W≼W′ related fresh) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero () ; (Fin.suc X) eq → eq })
    (liftCenterBodyImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterBodyImprecision (future-precise W≼W′ fresh) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero () ; (Fin.suc X) eq → eq })
    (liftCenterBodyImprecision W≼W′ Aᴾ⊑Aᴵ)

liftCenterDynamicBodyImprecision :
    ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Aᴾ Aᴵ : Ty (suc Δᶜ)}
  → (W≼W′ : Future W W′)
  → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → I.instᵐ (impEnv (core W′)) I.⊢ liftCenterBody W≼W′ Aᴾ
      ⊑ liftCenterBody W≼W′ Aᴵ
liftCenterDynamicBodyImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftCenterDynamicBodyImprecision
    (future-paired W≼W′ related fresh) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero eq → eq ; (Fin.suc X) eq → eq })
    (liftCenterDynamicBodyImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterDynamicBodyImprecision
    (future-precise W≼W′ fresh) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero eq → eq ; (Fin.suc X) eq → eq })
    (liftCenterDynamicBodyImprecision W≼W′ Aᴾ⊑Aᴵ)

openFreshImprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ (suc Δᶜ)} {Aᴾ Aᴵ : Ty (suc (suc Δᶜ))}
  → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W) I.⊢ Aᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ Aᴵ [ ＇ Fin.zero ]ᵗ
openFreshImprecision Aᴾ⊑Aᴵ =
  subst-⊑ (λ { Fin.zero () ; (Fin.suc X) eq → I.X⊑★ eq }) Aᴾ⊑Aᴵ

openFreshDynamicImprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ (suc Δᶜ)} {Aᴾ Aᴵ : Ty (suc (suc Δᶜ))}
  → impEnv (core W) Fin.zero ≡ I.X⊑★
  → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W) I.⊢ Aᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ Aᴵ [ ＇ Fin.zero ]ᵗ
openFreshDynamicImprecision fresh-mode Aᴾ⊑Aᴵ =
  subst-⊑
    (λ { Fin.zero eq → I.X⊑★ fresh-mode
       ; (Fin.suc X) eq → I.X⊑★ eq })
    Aᴾ⊑Aᴵ

embed-keep-shift : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
embed-keep-shift η A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
    (renameᵗ-shift (toRenameᵗ η) A)

renameᵗ-skip-eq : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (skip η)) A
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
renameᵗ-skip-eq η A =
  trans (renameᵗ-cong A (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc A))

embedPrecise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A : Ty Δᴾ)
  → embedPrecise (core W′) (liftPreciseTy W≼W′ A)
      ≡ liftCenterTy W≼W′ (embedPrecise (core W) A)
embedPrecise-lift future-refl A = refl
embedPrecise-lift
    (future-paired {W′ = W′} W≼W′ related fresh) A =
  trans (embed-keep-shift (preciseEmbedding (core W′))
      (liftPreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedPrecise-lift W≼W′ A))
embedPrecise-lift
    (future-precise {W′ = W′} W≼W′ fresh) A =
  trans (embed-keep-shift (preciseEmbedding (core W′))
      (liftPreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedPrecise-lift W≼W′ A))

embedImprecise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A : Ty Δᴵ)
  → embedImprecise (core W′) (liftImpreciseTy W≼W′ A)
      ≡ liftCenterTy W≼W′ (embedImprecise (core W) A)
embedImprecise-lift future-refl A = refl
embedImprecise-lift
    (future-paired {W′ = W′} W≼W′ related fresh) A =
  trans (embed-keep-shift (impreciseEmbedding (core W′))
      (liftImpreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedImprecise-lift W≼W′ A))

embedImprecise-lift
    (future-precise {W′ = W′} W≼W′ fresh) A =
  trans (renameᵗ-skip-eq (impreciseEmbedding (core W′))
      (liftImpreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedImprecise-lift W≼W′ A))

paired-atom-holds-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Z : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → PairedAtomHolds (semanticEntry W Z) k Vᴵ Vᴾ
  → PairedAtomHolds
      (semanticEntry W′ (liftCenterVariable W≼W′ Z)) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
paired-atom-holds-future future-refl related = related
paired-atom-holds-future
    (future-paired {W′ = W′} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
      W≼W′ related fresh) holds =
  paired-holds-weaken Aᴾ Aᴵ
    (semanticEntry W′ (liftCenterVariable W≼W′ _))
    (paired-atom-holds-future W≼W′ holds)
paired-atom-holds-future
    (future-precise {W′ = W′} {Aᴾ = Aᴾ} W≼W′ fresh) holds =
  paired-holds-weaken-precise Aᴾ
    (semanticEntry W′ (liftCenterVariable W≼W′ _))
    (paired-atom-holds-future W≼W′ holds)

dynamic-atom-holds-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Z : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (W≼W′ : Future W W′) (eq : impEnv (core W) Z ≡ I.X⊑★)
  → DynamicAtomHolds (semanticEntry W Z) eq k Vᴵ Vᴾ
  → DynamicAtomHolds
      (semanticEntry W′ (liftCenterVariable W≼W′ Z))
      (trans (liftCenterMode W≼W′ Z) eq) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
dynamic-atom-holds-future future-refl eq related = related
dynamic-atom-holds-future
    (future-paired {W′ = W′} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
      W≼W′ related fresh) eq holds =
  dynamic-holds-weaken Aᴾ Aᴵ
    (semanticEntry W′ (liftCenterVariable W≼W′ _))
    (trans (liftCenterMode W≼W′ _) eq)
    (dynamic-atom-holds-future W≼W′ eq holds)
dynamic-atom-holds-future
    (future-precise {W′ = W′} {Aᴾ = Aᴾ} W≼W′ fresh) eq holds =
  dynamic-holds-weaken-precise Aᴾ
    (semanticEntry W′ (liftCenterVariable W≼W′ _))
    (trans (liftCenterMode W≼W′ _) eq)
    (dynamic-atom-holds-future W≼W′ eq holds)

paired-local-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
    (fresh : SemanticAtom (pairedBindCore (core W) Bᴾ Bᴵ) Fin.zero)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → ⇑ᵗ Aᴾ
      ⊑ᵂ⟨ core (pairedBindWorld W Bᴾ Bᴵ fresh) ⟩ ⇑ᵗ Aᴵ
paired-local-imprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} fresh p =
  subst
    (λ L → impEnv (pairedBindCore (core W) Bᴾ Bᴵ) I.⊢ L ⊑
      embedImprecise (pairedBindCore (core W) Bᴾ Bᴵ) (⇑ᵗ Aᴵ))
    (sym (embed-keep-shift (preciseEmbedding (core W)) Aᴾ))
    (subst
      (λ R → impEnv (pairedBindCore (core W) Bᴾ Bᴵ) I.⊢
        ⇑ᵗ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (embed-keep-shift (impreciseEmbedding (core W)) Aᴵ))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))

precise-local-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {Bᴾ : Ty Δᴾ}
    (fresh : DynamicSemanticAtom
      (preciseBindCore (core W) Bᴾ) Fin.zero)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → ⇑ᵗ Aᴾ ⊑ᵂ⟨ core (preciseBindWorld W Bᴾ fresh) ⟩ Aᴵ
precise-local-imprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} fresh p =
  subst
    (λ L → impEnv (preciseBindCore (core W) Bᴾ) I.⊢ L ⊑
      embedImprecise (preciseBindCore (core W) Bᴾ) Aᴵ)
    (sym (embed-keep-shift (preciseEmbedding (core W)) Aᴾ))
    (subst
      (λ R → impEnv (preciseBindCore (core W) Bᴾ) I.⊢
        ⇑ᵗ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (renameᵗ-skip-eq (impreciseEmbedding (core W)) Aᴵ))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))

liftLocalImprecision : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → (W≼W′ : Future W W′)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → liftPreciseTy W≼W′ Aᴾ ⊑ᵂ⟨ core W′ ⟩
      liftImpreciseTy W≼W′ Aᴵ
liftLocalImprecision future-refl p = p
liftLocalImprecision
    (future-paired {W′ = W′} {Aᴾ = Bᴾ} {Aᴵ = Bᴵ}
      W≼W′ related fresh) p =
  paired-local-imprecision {W = W′}
    {Aᴾ = liftPreciseTy W≼W′ _} {Aᴵ = liftImpreciseTy W≼W′ _}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} fresh (liftLocalImprecision W≼W′ p)
liftLocalImprecision
    (future-precise {W′ = W′} {Aᴾ = Bᴾ} W≼W′ fresh) p =
  precise-local-imprecision {W = W′}
    {Aᴾ = liftPreciseTy W≼W′ _} {Aᴵ = liftImpreciseTy W≼W′ _}
    {Bᴾ = Bᴾ} fresh (liftLocalImprecision W≼W′ p)

liftCenterVariable-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (X : TyVar Δᶜ₀)
  → liftCenterVariable (future-trans W₀≼W₁ W₁≼W₂) X
      ≡ liftCenterVariable W₁≼W₂ (liftCenterVariable W₀≼W₁ X)
liftCenterVariable-trans W₀≼W₁ future-refl X = refl
liftCenterVariable-trans W₀≼W₁
    (future-paired W₁≼W₂ related fresh) X =
  cong Fin.suc (liftCenterVariable-trans W₀≼W₁ W₁≼W₂ X)
liftCenterVariable-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) X =
  cong Fin.suc (liftCenterVariable-trans W₀≼W₁ W₁≼W₂ X)

liftPreciseTy-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty Δᴾ₀)
  → liftPreciseTy (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftPreciseTy W₁≼W₂ (liftPreciseTy W₀≼W₁ A)
liftPreciseTy-trans W₀≼W₁ future-refl A = refl
liftPreciseTy-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) A =
  cong ⇑ᵗ (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ A)
liftPreciseTy-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) A =
  cong ⇑ᵗ (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ A)

liftImpreciseTy-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty Δᴵ₀)
  → liftImpreciseTy (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftImpreciseTy W₁≼W₂ (liftImpreciseTy W₀≼W₁ A)
liftImpreciseTy-trans W₀≼W₁ future-refl A = refl
liftImpreciseTy-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) A =
  cong ⇑ᵗ (liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ A)
liftImpreciseTy-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) A =
  liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ A

liftCenterTy-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty Δᶜ₀)
  → liftCenterTy (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftCenterTy W₁≼W₂ (liftCenterTy W₀≼W₁ A)
liftCenterTy-trans W₀≼W₁ future-refl A = refl
liftCenterTy-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) A =
  cong ⇑ᵗ (liftCenterTy-trans W₀≼W₁ W₁≼W₂ A)
liftCenterTy-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) A =
  cong ⇑ᵗ (liftCenterTy-trans W₀≼W₁ W₁≼W₂ A)

liftPreciseTerm-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (M : Term Δᴾ₀)
  → liftPreciseTerm (future-trans W₀≼W₁ W₁≼W₂) M
      ≡ liftPreciseTerm W₁≼W₂ (liftPreciseTerm W₀≼W₁ M)
liftPreciseTerm-trans W₀≼W₁ future-refl M = refl
liftPreciseTerm-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) M =
  cong ⇑ᵗᵐ (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)
liftPreciseTerm-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) M =
  cong ⇑ᵗᵐ (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)

liftImpreciseTerm-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (M : Term Δᴵ₀)
  → liftImpreciseTerm (future-trans W₀≼W₁ W₁≼W₂) M
      ≡ liftImpreciseTerm W₁≼W₂ (liftImpreciseTerm W₀≼W₁ M)
liftImpreciseTerm-trans W₀≼W₁ future-refl M = refl
liftImpreciseTerm-trans W₀≼W₁
    (future-paired W₁≼W₂ related fresh) M =
  cong ⇑ᵗᵐ (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)
liftImpreciseTerm-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) M =
  liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M

liftPreciseBody-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty (suc Δᴾ₀))
  → liftPreciseBody (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftPreciseBody W₁≼W₂ (liftPreciseBody W₀≼W₁ A)
liftPreciseBody-trans W₀≼W₁ future-refl A = refl
liftPreciseBody-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftPreciseBody-trans W₀≼W₁ W₁≼W₂ A)
liftPreciseBody-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftPreciseBody-trans W₀≼W₁ W₁≼W₂ A)

liftImpreciseBody-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty (suc Δᴵ₀))
  → liftImpreciseBody (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftImpreciseBody W₁≼W₂ (liftImpreciseBody W₀≼W₁ A)
liftImpreciseBody-trans W₀≼W₁ future-refl A = refl
liftImpreciseBody-trans W₀≼W₁
    (future-paired W₁≼W₂ related fresh) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftImpreciseBody-trans W₀≼W₁ W₁≼W₂ A)
liftImpreciseBody-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) A =
  liftImpreciseBody-trans W₀≼W₁ W₁≼W₂ A

liftCenterBody-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty (suc Δᶜ₀))
  → liftCenterBody (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftCenterBody W₁≼W₂ (liftCenterBody W₀≼W₁ A)
liftCenterBody-trans W₀≼W₁ future-refl A = refl
liftCenterBody-trans W₀≼W₁ (future-paired W₁≼W₂ related fresh) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-trans W₀≼W₁ W₁≼W₂ A)
liftCenterBody-trans W₀≼W₁ (future-precise W₁≼W₂ fresh) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-trans W₀≼W₁ W₁≼W₂ A)

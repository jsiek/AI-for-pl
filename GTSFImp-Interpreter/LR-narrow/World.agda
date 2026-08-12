module LR-narrow.World where

-- File Charter:
--   * Adds semantic atoms to a three-context GTSFImp world.
--   * Defines paired future worlds with fresh related representation types.
--   * Lifts endpoint syntax and center imprecision through future worlds.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import Types
open import TyStore using (store-empty)
open import CastTerms using (Term; ⇑ᵗᵐ)
open import Consistency using (_↪ᵗ_; empty; keep; toRenameᵗ)
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
    semanticAtom : (Z : TyVar Δᶜ) → SemanticAtom core Z

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
  atoms : (Z : TyVar _) → SemanticAtom (pairedBindCore (core W) Aᴾ Aᴵ) Z
  atoms Fin.zero = fresh
  atoms (Fin.suc Z) = weaken-semantic-atom Aᴾ Aᴵ (semanticAtom W Z)

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

liftPreciseTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴾ
  → Ty Δᴾ′
liftPreciseTy future-refl A = A
liftPreciseTy (future-paired W≼W′ related fresh) A =
  ⇑ᵗ (liftPreciseTy W≼W′ A)

liftImpreciseTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴵ
  → Ty Δᴵ′
liftImpreciseTy future-refl A = A
liftImpreciseTy (future-paired W≼W′ related fresh) A =
  ⇑ᵗ (liftImpreciseTy W≼W′ A)

liftCenterTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᶜ
  → Ty Δᶜ′
liftCenterTy future-refl A = A
liftCenterTy (future-paired W≼W′ related fresh) A =
  ⇑ᵗ (liftCenterTy W≼W′ A)

liftCenterVariable : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TyVar Δᶜ
  → TyVar Δᶜ′
liftCenterVariable future-refl X = X
liftCenterVariable (future-paired W≼W′ related fresh) X =
  Fin.suc (liftCenterVariable W≼W′ X)

liftPreciseTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term Δᴾ
  → Term Δᴾ′
liftPreciseTerm future-refl M = M
liftPreciseTerm (future-paired W≼W′ related fresh) M =
  ⇑ᵗᵐ (liftPreciseTerm W≼W′ M)

liftImpreciseTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term Δᴵ
  → Term Δᴵ′
liftImpreciseTerm future-refl M = M
liftImpreciseTerm (future-paired W≼W′ related fresh) M =
  ⇑ᵗᵐ (liftImpreciseTerm W≼W′ M)

liftPreciseBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᴾ)
  → Ty (suc Δᴾ′)
liftPreciseBody future-refl A = A
liftPreciseBody (future-paired W≼W′ related fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ A)

liftImpreciseBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᴵ)
  → Ty (suc Δᴵ′)
liftImpreciseBody future-refl A = A
liftImpreciseBody (future-paired W≼W′ related fresh) A =
  renameᵗ (extᵗ Fin.suc) (liftImpreciseBody W≼W′ A)

liftCenterBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᶜ)
  → Ty (suc Δᶜ′)
liftCenterBody future-refl A = A
liftCenterBody (future-paired W≼W′ related fresh) A =
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

openFreshImprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ (suc Δᶜ)} {Aᴾ Aᴵ : Ty (suc (suc Δᶜ))}
  → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W) I.⊢ Aᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ Aᴵ [ ＇ Fin.zero ]ᵗ
openFreshImprecision Aᴾ⊑Aᴵ =
  subst-⊑ (λ { Fin.zero () ; (Fin.suc X) eq → I.X⊑★ eq }) Aᴾ⊑Aᴵ

embed-keep-shift : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
embed-keep-shift η A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
    (renameᵗ-shift (toRenameᵗ η) A)

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

atom-holds-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Z : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → AtomHolds (semanticAtom W Z) k Vᴵ Vᴾ
  → AtomHolds (semanticAtom W′ (liftCenterVariable W≼W′ Z)) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
atom-holds-future future-refl related = related
atom-holds-future
    (future-paired {W′ = W′} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
      W≼W′ related fresh) (atom-holds holds) =
  atom-holds (lift-related
    (relation-holds (atom-holds-future W≼W′ (atom-holds holds))))

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

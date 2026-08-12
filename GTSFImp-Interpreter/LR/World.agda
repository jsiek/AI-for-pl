module LR.World where

-- File Charter:
--   * Defines paired logical-relation worlds over GTSFImp stores.
--   * Defines future-world evidence generated only by fresh paired bindings.
--   * Lifts types, terms, and imprecision derivations through future worlds.

import Data.Fin as Fin
open import Data.Nat using (suc)

open import Types
open import TyStore
open import CastTerms using (Term; ⇑ᵗᵐ)
import Imprecision as I
open import proof.ImprecisionConsistency
  using (ext-injective; fin-suc-injective; rename-⊑; subst-⊑)

record World (Δ : TyCtx) : Set where
  constructor world
  field
    impEnv : I.ImpEnv Δ
    preciseStore : TyStore Δ
    impreciseStore : TyStore Δ

open World public

pairedBindWorld : ∀ {Δ}
  → World Δ
  → Ty Δ
  → Ty Δ
  → World (suc Δ)
pairedBindWorld W Aᴾ Aᴵ =
  world (I.extᵐ (impEnv W))
    (store-bind (preciseStore W) Aᴾ)
    (store-bind (impreciseStore W) Aᴵ)

data Future {Δ : TyCtx} (W : World Δ) :
    ∀ {Δ′} → World Δ′ → Set where
  future-refl : Future W W

  future-paired : ∀ {Δ′} {W′ : World Δ′} {Aᴾ Aᴵ : Ty Δ′}
    → Future W W′
    → impEnv W′ I.⊢ Aᴾ ⊑ Aᴵ
    → Future W (pairedBindWorld W′ Aᴾ Aᴵ)

future-trans : ∀ {Δ₀ Δ₁ Δ₂}
    {W₀ : World Δ₀} {W₁ : World Δ₁} {W₂ : World Δ₂}
  → Future W₀ W₁
  → Future W₁ W₂
  → Future W₀ W₂
future-trans W₀≼W₁ future-refl = W₀≼W₁
future-trans W₀≼W₁ (future-paired W₁≼W₂ Aᴾ⊑Aᴵ) =
  future-paired (future-trans W₀≼W₁ W₁≼W₂) Aᴾ⊑Aᴵ

liftTy : ∀ {Δ Δ′} {W : World Δ} {W′ : World Δ′}
  → Future W W′
  → Ty Δ
  → Ty Δ′
liftTy future-refl A = A
liftTy (future-paired W≼W′ Aᴾ⊑Aᴵ) A = ⇑ᵗ (liftTy W≼W′ A)

liftTerm : ∀ {Δ Δ′} {W : World Δ} {W′ : World Δ′}
  → Future W W′
  → Term Δ
  → Term Δ′
liftTerm future-refl M = M
liftTerm (future-paired W≼W′ Aᴾ⊑Aᴵ) M =
  ⇑ᵗᵐ (liftTerm W≼W′ M)

liftBody : ∀ {Δ Δ′} {W : World Δ} {W′ : World Δ′}
  → Future W W′
  → Ty (suc Δ)
  → Ty (suc Δ′)
liftBody future-refl A = A
liftBody (future-paired W≼W′ Aᴾ⊑Aᴵ) A =
  renameᵗ (extᵗ Fin.suc) (liftBody W≼W′ A)

liftImprecision : ∀ {Δ Δ′} {W : World Δ} {W′ : World Δ′}
    {Aᴾ Aᴵ : Ty Δ}
  → (W≼W′ : Future W W′)
  → impEnv W I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv W′ I.⊢ liftTy W≼W′ Aᴾ ⊑ liftTy W≼W′ Aᴵ
liftImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftImprecision (future-paired W≼W′ Bᴾ⊑Bᴵ) Aᴾ⊑Aᴵ =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)
    (liftImprecision W≼W′ Aᴾ⊑Aᴵ)

liftBodyImprecision : ∀ {Δ Δ′} {W : World Δ} {W′ : World Δ′}
    {Aᴾ Aᴵ : Ty (suc Δ)}
  → (W≼W′ : Future W W′)
  → I.extᵐ (impEnv W) I.⊢ Aᴾ ⊑ Aᴵ
  → I.extᵐ (impEnv W′) I.⊢ liftBody W≼W′ Aᴾ
      ⊑ liftBody W≼W′ Aᴵ
liftBodyImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftBodyImprecision (future-paired W≼W′ Bᴾ⊑Bᴵ) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero () ; (Fin.suc X) eq → eq })
    (liftBodyImprecision W≼W′ Aᴾ⊑Aᴵ)

openFreshImprecision : ∀ {Δ} {W : World (suc Δ)}
    {Aᴾ Aᴵ : Ty (suc (suc Δ))}
  → I.extᵐ (impEnv W) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv W I.⊢ Aᴾ [ ＇ Fin.zero ]ᵗ ⊑ Aᴵ [ ＇ Fin.zero ]ᵗ
openFreshImprecision Aᴾ⊑Aᴵ =
  subst-⊑ (λ { Fin.zero () ; (Fin.suc X) eq → I.X⊑★ eq }) Aᴾ⊑Aᴵ

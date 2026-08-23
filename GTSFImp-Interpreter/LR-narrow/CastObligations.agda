module LR-narrow.CastObligations where

-- File Charter:
--   * States the value-level cast compatibilities that the cast
--     compatibility lemmas consume but that are not yet proven: the
--     one-sided cast-on-value lemmas and the listed paired cast cases.
--   * Earlier revisions closed these cases by self-referential proofs
--     under a TERMINATING pragma; those proofs were circular (the
--     continuation was the lemma itself at the same arguments), so the
--     cases are reopened here as explicit obligations.
--   * `OpenPairedCastCase` enumerates exactly the paired cases that are
--     open; every other paired case is proven in proof.LR-narrow.Cast.

open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import CastTerms
import Consistency as C
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation

------------------------------------------------------------------------
-- The open paired cases
------------------------------------------------------------------------

data OpenPairedCastCase {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} :
    ∀ {Aᴾ Aᴵ : Ty Δᶜ} {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
    → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
    → μᴾ C.⊢ Cᴾ ∼ Dᴾ
    → μᴵ C.⊢ Cᴵ ∼ Dᴵ
    → Set where

  -- A paired function cast against the injection of `★ ⇒ ★`.
  open-function-injection : ∀ {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
      {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
      {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
      {Aᴾ₀ Bᴾ₀ Aᴾ₁ Bᴾ₁ : Ty Δᴾ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {c₁ᴾ : C.flipᵐ μᴾ C.⊢ Aᴾ₁ ∼ Aᴾ₀} {c₂ᴾ : μᴾ C.⊢ Bᴾ₀ ∼ Bᴾ₁}
      {nsᴵ : NonStar (★ ⇒ ★)}
    → OpenPairedCastCase (I.⇒⊑⇒ p q) (c₁ᴾ C.↦ c₂ᴾ)
        (C._! {μ = μᴵ} {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄
          ⦃ G∼★ = C.⇒∼★ ⦄ (C.id ★ C.↦ C.id ★) ⦃ Ans = nsᴵ ⦄)

  -- A precise injection under a paired function imprecision.
  open-function-precise-injection : ∀ {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
      {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
      {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
      {Cᴾ Gᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      ⦃ Gᵍ : Ground Gᴾ ⦄ ⦃ G∼★ : μᴾ C.⊢ Gᴾ ∼★ ⦄
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Gᴾ} ⦃ Ans : NonStar Cᴾ ⦄
      {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.⇒⊑⇒ p q) (cᴾ C.!) cᴵ

  -- A precise generalization under a paired function imprecision.
  open-function-precise-generalization : ∀ {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
      {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
      {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
      {Aᴾ′ : Ty Δᴾ} {Bᴾ′ : Ty (suc Δᴾ)} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      ⦃ Bnv : NonVar Bᴾ′ ⦄ ⦃ z∈B : Fin.zero ∈ᵗ Bᴾ′ ⦄
      {cᴾ : C.genᵐ μᴾ C.⊢ ⇑ᵗ Aᴾ′ ∼ Bᴾ′} {A≢★ : Aᴾ′ ≢ ★}
      {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.⇒⊑⇒ p q) ((C.gen cᴾ) A≢★) cᴵ

  -- Every cast pair under these imprecision forms.
  open-universals : ∀ {Aᴾ Aᴵ : Ty (suc Δᶜ)}
      {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
      {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.∀⊑∀ p) cᴾ cᴵ

  open-function-dynamic : ∀ {Aᴾ Bᴾ : Ty Δᶜ}
      {p : impEnv (core W) I.⊢ Aᴾ ⊑ ★}
      {q : impEnv (core W) I.⊢ Bᴾ ⊑ ★}
      {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.⇒⊑★ p q) cᴾ cᴵ

  open-base-dynamic : ∀ {ι}
      {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.ι⊑★ {ι = ι}) cᴾ cᴵ

  open-variable-dynamic : ∀ {X : TyVar Δᶜ}
      {mode : impEnv (core W) X ≡ I.X⊑★}
      {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.X⊑★ mode) cᴾ cᴵ

  open-right-universal : ∀ {Aᴾ : Ty (suc Δᶜ)} {Aᴵ : Ty Δᶜ}
      {nonvar : NonVar Aᴾ} {occurs : Fin.zero ∈ᵗ Aᴾ}
      {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ ⇑ᵗ Aᴵ}
      {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.∀⊑ nonvar occurs p) cᴾ cᴵ

  open-universal-dynamic : ∀ {Aᴾ : Ty (suc Δᶜ)}
      {nonstar : NonStar Aᴾ}
      {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ ★}
      {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
      {μᴾ : C.Env∼ Δᴾ} {μᴵ : C.Env∼ Δᴵ}
      {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    → OpenPairedCastCase (I.∀⊑★ nonstar p) cᴾ cᴵ

------------------------------------------------------------------------
-- The obligations
------------------------------------------------------------------------

record CastValueObligations : Set₂ where
  field

    -- A precise cast on related values, the imprecise value unchanged.
    precise-cast-values : ∀
        {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
        {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
        {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
        (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
        (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
        (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
        {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
        (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
        (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
        (targetᴵ : embedImprecise (core W) Cᴵ ≡ Bᴵ)
        {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation q) k
          Vᴵ (Vᴾ ⟨ cᴾ ⟩)

    -- An imprecise cast on related values, the precise value unchanged.
    imprecise-cast-values : ∀
        {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
        {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
        {Cᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
        (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
        (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
        (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
        {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
        (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
        (targetᴾ : embedPrecise (core W) Cᴾ ≡ Bᴾ)
        (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
        {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation q) k
          (Vᴵ ⟨ cᴵ ⟩) Vᴾ

    -- Paired casts on related values in the open cases.
    paired-cast-values : ∀
        {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
        {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
        {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
        (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
        (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
        (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
        {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
        {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
      → OpenPairedCastCase {W = W} p cᴾ cᴵ
      → (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
      → (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
      → (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
      → {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W p k Vᴵ Vᴾ
      → ComputationsRelated W (FutureValueRelation q) k
          (Vᴵ ⟨ cᴵ ⟩) (Vᴾ ⟨ cᴾ ⟩)

open CastValueObligations public

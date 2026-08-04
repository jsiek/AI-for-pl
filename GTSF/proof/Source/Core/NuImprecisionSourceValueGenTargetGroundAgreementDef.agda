module
  proof.Source.Core.NuImprecisionSourceValueGenTargetGroundAgreementDef
  where

-- File Charter:
--   * Defines ground-label agreement when a terminal source value is about to
--     be framed by an inert `gen` cast and is related to a tagged target
--     value.
--   * Retains the source-value and no-runtime-bullet hypotheses that exclude
--     the known active-source-untag counterexample.
--   * Contains no implementation, simulation result, outcome, postulate,
--     hole, permissive option, or wrapper alias.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; gen; _!)
open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ground; Ty; ★; `∀)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)


SourceValueGenTargetGroundAgreementᵀ : Set₁
SourceValueGenTargetGroundAgreementᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A B G H : Ty} {c : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ} →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  Ground H →
  Value V →
  No• V →
  Value W →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ gen A c ∶ A ⊒ `∀ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⟨ G ! ⟩ ⦂ A ⊑ ★ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ) →
  G ≡ H

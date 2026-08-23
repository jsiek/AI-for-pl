module LR-narrow.FutureInsertion where

-- File Charter:
--   * Composes a world insertion with an LR future: every future is a
--     sequence of fresh allocations, so an insertion into a world inserts
--     into each of its futures behind the allocated centers.
--   * Relates the LR's future lifting of renamed endpoint terms and types
--     to renaming by the shifted embeddings.
--   * Delegates the proofs to proof.LR-narrow.FutureInsertion.

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Nat using (suc)
open import Types
open import CastTerms using (Term; renameᵗᵐ)
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ)
import Imprecision as I
import proof.DGG.CtxImp as CTI
open import proof.DGG.WorldInsert
open import LR-narrow.World
open import LR-narrow.TermRelation using (forgetWorld)
import proof.LR-narrow.FutureInsertion as Proof

------------------------------------------------------------------------
-- Insertion after a future
------------------------------------------------------------------------

insert-after-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀ᴾ Δ₀ᴵ Δ₀ᶜ}
    {Wᶜ : CTI.World Δ₀ᴾ Δ₀ᴵ Δ₀ᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ρᴾ : Δ₀ᴾ ↪ᵗ Δᴾ} {ρᴵ : Δ₀ᴵ ↪ᵗ Δᴵ} {π : Δ₀ᶜ ↪ᵗ Δᶜ}
  → WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W)
  → (W≼W′ : Future W W′)
  → WorldInsert (afterPrecise W≼W′ ρᴾ) (afterImprecise W≼W′ ρᴵ)
      (afterCenter W≼W′ π) Wᶜ (forgetWorld W′)
insert-after-future = Proof.insert-after-future

------------------------------------------------------------------------
-- Lifting renamed endpoints is renaming by the shifted embeddings
------------------------------------------------------------------------

liftPreciseTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (M : Term Δ₀)
  → liftPreciseTerm W≼W′ (renameᵗᵐ ρ M)
      ≡ renameᵗᵐ (afterPrecise W≼W′ ρ) M
liftPreciseTerm-after = Proof.liftPreciseTerm-after

liftImpreciseTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (M : Term Δ₀)
  → liftImpreciseTerm W≼W′ (renameᵗᵐ ρ M)
      ≡ renameᵗᵐ (afterImprecise W≼W′ ρ) M
liftImpreciseTerm-after = Proof.liftImpreciseTerm-after

liftPreciseBodyTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (M : Term (suc Δ₀))
  → liftPreciseBodyTerm W≼W′ (renameᵗᵐ (keep ρ) M)
      ≡ renameᵗᵐ (keep (afterPrecise W≼W′ ρ)) M
liftPreciseBodyTerm-after = Proof.liftPreciseBodyTerm-after

liftImpreciseBodyTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (M : Term (suc Δ₀))
  → liftImpreciseBodyTerm W≼W′ (renameᵗᵐ (keep ρ) M)
      ≡ renameᵗᵐ (keep (afterImprecise W≼W′ ρ)) M
liftImpreciseBodyTerm-after = Proof.liftImpreciseBodyTerm-after

liftPreciseTy-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (A : Ty Δ₀)
  → liftPreciseTy W≼W′ (renameᵗ (toRenameᵗ ρ) A)
      ≡ renameᵗ (toRenameᵗ (afterPrecise W≼W′ ρ)) A
liftPreciseTy-after = Proof.liftPreciseTy-after

liftImpreciseTy-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (A : Ty Δ₀)
  → liftImpreciseTy W≼W′ (renameᵗ (toRenameᵗ ρ) A)
      ≡ renameᵗ (toRenameᵗ (afterImprecise W≼W′ ρ)) A
liftImpreciseTy-after = Proof.liftImpreciseTy-after

liftCenterTy-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (π : Δ₀ ↪ᵗ Δᶜ) (A : Ty Δ₀)
  → liftCenterTy W≼W′ (renameᵗ (toRenameᵗ π) A)
      ≡ renameᵗ (toRenameᵗ (afterCenter W≼W′ π)) A
liftCenterTy-after = Proof.liftCenterTy-after

module proof.LR-narrow.FutureInsertion where

-- File Charter:
--   * Proves that a world insertion composes with every LR future by
--     shifting behind each allocation.
--   * Proves that the LR's future lifting of renamed endpoint terms and
--     types is renaming by the shifted embeddings, one weakening step at a
--     time.

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Data.Nat using (suc)
open import Types
open import CastTerms using (Term; renameᵗᵐ)
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ)
import Imprecision as I
import proof.DGG.CtxImp as CTI
open import proof.DGG.WorldInsert
open import proof.LR-narrow.TermRenamingComposition using
  (renameᵗᵐ-shift; shift-base; shift-under)
open import LR-narrow.World
open import LR-narrow.TermRelation using (forgetWorld)

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
insert-after-future ins future-refl = ins
insert-after-future ins (future-paired {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} W≼W′ r) =
  shiftBoth-insert I.X⊑X Aᴾ Aᴵ (insert-after-future ins W≼W′)
insert-after-future ins (future-precise {Aᴾ = Aᴾ} W≼W′ r) =
  shiftLeft-insert I.X⊑★ Aᴾ (insert-after-future ins W≼W′)
insert-after-future ins (future-imprecise {Aᴵ = Aᴵ} W≼W′) =
  shiftRight-insert Aᴵ (insert-after-future ins W≼W′)

------------------------------------------------------------------------
-- Lifting renamed endpoints is renaming by the shifted embeddings
------------------------------------------------------------------------

shift-type : ∀ {Δ Δ′} (σ : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → ⇑ᵗ (renameᵗ (toRenameᵗ σ) A) ≡ renameᵗ (toRenameᵗ (skip σ)) A
shift-type σ A = renameᵗ-comp (toRenameᵗ σ) _ A

liftPreciseTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (M : Term Δ₀)
  → liftPreciseTerm W≼W′ (renameᵗᵐ ρ M)
      ≡ renameᵗᵐ (afterPrecise W≼W′ ρ) M
liftPreciseTerm-after future-refl ρ M = refl
liftPreciseTerm-after (future-paired W≼W′ r) ρ M
    rewrite liftPreciseTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-base _) M
liftPreciseTerm-after (future-precise W≼W′ r) ρ M
    rewrite liftPreciseTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-base _) M
liftPreciseTerm-after (future-imprecise W≼W′) ρ M =
  liftPreciseTerm-after W≼W′ ρ M

liftImpreciseTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (M : Term Δ₀)
  → liftImpreciseTerm W≼W′ (renameᵗᵐ ρ M)
      ≡ renameᵗᵐ (afterImprecise W≼W′ ρ) M
liftImpreciseTerm-after future-refl ρ M = refl
liftImpreciseTerm-after (future-paired W≼W′ r) ρ M
    rewrite liftImpreciseTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-base _) M
liftImpreciseTerm-after (future-precise W≼W′ r) ρ M =
  liftImpreciseTerm-after W≼W′ ρ M
liftImpreciseTerm-after (future-imprecise W≼W′) ρ M
    rewrite liftImpreciseTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-base _) M

liftPreciseBodyTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (M : Term (suc Δ₀))
  → liftPreciseBodyTerm W≼W′ (renameᵗᵐ (keep ρ) M)
      ≡ renameᵗᵐ (keep (afterPrecise W≼W′ ρ)) M
liftPreciseBodyTerm-after future-refl ρ M = refl
liftPreciseBodyTerm-after (future-paired W≼W′ r) ρ M
    rewrite liftPreciseBodyTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-under (shift-base _)) M
liftPreciseBodyTerm-after (future-precise W≼W′ r) ρ M
    rewrite liftPreciseBodyTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-under (shift-base _)) M
liftPreciseBodyTerm-after (future-imprecise W≼W′) ρ M =
  liftPreciseBodyTerm-after W≼W′ ρ M

liftImpreciseBodyTerm-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (M : Term (suc Δ₀))
  → liftImpreciseBodyTerm W≼W′ (renameᵗᵐ (keep ρ) M)
      ≡ renameᵗᵐ (keep (afterImprecise W≼W′ ρ)) M
liftImpreciseBodyTerm-after future-refl ρ M = refl
liftImpreciseBodyTerm-after (future-paired W≼W′ r) ρ M
    rewrite liftImpreciseBodyTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-under (shift-base _)) M
liftImpreciseBodyTerm-after (future-precise W≼W′ r) ρ M =
  liftImpreciseBodyTerm-after W≼W′ ρ M
liftImpreciseBodyTerm-after (future-imprecise W≼W′) ρ M
    rewrite liftImpreciseBodyTerm-after W≼W′ ρ M =
  renameᵗᵐ-shift (shift-under (shift-base _)) M

liftPreciseTy-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (A : Ty Δ₀)
  → liftPreciseTy W≼W′ (renameᵗ (toRenameᵗ ρ) A)
      ≡ renameᵗ (toRenameᵗ (afterPrecise W≼W′ ρ)) A
liftPreciseTy-after future-refl ρ A = refl
liftPreciseTy-after (future-paired W≼W′ r) ρ A
    rewrite liftPreciseTy-after W≼W′ ρ A = shift-type _ A
liftPreciseTy-after (future-precise W≼W′ r) ρ A
    rewrite liftPreciseTy-after W≼W′ ρ A = shift-type _ A
liftPreciseTy-after (future-imprecise W≼W′) ρ A =
  liftPreciseTy-after W≼W′ ρ A

liftImpreciseTy-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (A : Ty Δ₀)
  → liftImpreciseTy W≼W′ (renameᵗ (toRenameᵗ ρ) A)
      ≡ renameᵗ (toRenameᵗ (afterImprecise W≼W′ ρ)) A
liftImpreciseTy-after future-refl ρ A = refl
liftImpreciseTy-after (future-paired W≼W′ r) ρ A
    rewrite liftImpreciseTy-after W≼W′ ρ A = shift-type _ A
liftImpreciseTy-after (future-precise W≼W′ r) ρ A =
  liftImpreciseTy-after W≼W′ ρ A
liftImpreciseTy-after (future-imprecise W≼W′) ρ A
    rewrite liftImpreciseTy-after W≼W′ ρ A = shift-type _ A

liftCenterTy-after : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (π : Δ₀ ↪ᵗ Δᶜ) (A : Ty Δ₀)
  → liftCenterTy W≼W′ (renameᵗ (toRenameᵗ π) A)
      ≡ renameᵗ (toRenameᵗ (afterCenter W≼W′ π)) A
liftCenterTy-after future-refl π A = refl
liftCenterTy-after (future-paired W≼W′ r) π A
    rewrite liftCenterTy-after W≼W′ π A = shift-type _ A
liftCenterTy-after (future-precise W≼W′ r) π A
    rewrite liftCenterTy-after W≼W′ π A = shift-type _ A
liftCenterTy-after (future-imprecise W≼W′) π A
    rewrite liftCenterTy-after W≼W′ π A = shift-type _ A

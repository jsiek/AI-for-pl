module proof.DGG.drafts.MergeImpDef where

-- File Charter:
--   * DRAFT STATEMENTS (2026-10-03), NOT APPROVED: conversion
--     composition `Δ ⊢ c₁ ⨟ c₂` preserves conversion imprecision
--     (PLAN.md §3 `Merge⊑`).  For review (drafts/STATEMENTS.md).
--   * ONE WORLD.  All four conversions are spelled on the two contexts
--     of one world W (in `Merge`, the merged conversion context, after
--     the `SameConv` respellings the rule carries).  Moving the
--     premises there from the two boundaries' conversion worlds is the
--     consumer's transport, not part of this lemma.
--   * `WfWorld W` is needed: `seal X ⨟ unseal X` is `mkId` of X's
--     representation, and the two sides' representations are related
--     only by `Agree` of the paired rep. vars.
--   * The end types are related (A ⊑ A′, C ⊑ C′; the consumer has them
--     from the term relations): `seal X ⨟ unseal X = mkId A` against
--     `id ★` needs `A ⊑ ★`, which no conversion premise gives.
--   * The typings are needed: `⨟` returns its first argument on the
--     pairs typing rules out, and the ★ clauses meet those pairs.
--   * The one-sided forms: only one side merges (the other side's
--     inner boundary is absent, `⟪⟫⊑` or `⊑⟪⟫` inside `⟪⟫⊑⟪⟫`); the
--     absent conversion's two ends are related to the partner's source.
--   * Orientation: the LEFT term is the more precise one.

open import Types using (Ty)
open import Ctx using (Ctxᵗ)
open import Conversion using (Conv; _⊢_∶_⇝_; _⊢_⨟_)
open import ImprecisionWorld
open import ConversionImprecision using (ConvImp)

-- both sides merge (Merge on both sides)
MergeImp2 : Set
MergeImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₁ c₂ c₁′ c₂′ : Conv} {A B C A′ B′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
  → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′)

-- the left alone merges (Sim: Merge against ⟪⟫⊑⟪⟫ over ⟪⟫⊑)
MergeImpL : Set
MergeImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₁ c₂ c₂′ : Conv} {A B C A′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₂ c₂′
  → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′

-- the right alone merges (SimBack: Merge against ⟪⟫⊑⟪⟫ over ⊑⟪⟫)
MergeImpR : Set
MergeImpR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
    {c₂ c₁′ c₂′ : Conv} {A C A′ B′ C′ : Ty}
  → WfWorld W
  → Δ ⊢ c₂ ∶ A ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
  → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ⟩ B′ → C ⊑ᵂ⟨ W ⟩ C′
  → ConvImp W c₂ c₂′
  → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′)

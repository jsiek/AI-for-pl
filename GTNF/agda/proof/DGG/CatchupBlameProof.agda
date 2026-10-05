module proof.DGG.CatchupBlameProof where

-- File Charter:
--   * PROOF of `CatchupBlame` (CatchupBlameDef), by induction on the
--     `⊑` derivation.  Only `blame⊑` and the one-sided LEFT wrappers
--     relate a term to `blame ℓ`: `cast⊑`, `ν⊑`, `⟪⟫⊑` (each runs its
--     subterm to blame inside the frame, RunFrames, then fires that
--     frame's Blame rule), and `Λ⊑`, which is impossible: its body is a
--     value, and a value that runs to blame is blame, not a value.
--   * The statement is at a world with no pending name (`πʷ W ≡ []`,
--     design.md D27), so only `cc-plain`, `claim-fresh` and `bc-plain`
--     occur, and every premise is again at a world with no pending name
--     (`refl`).
--   * No module parameters: the proof uses no other DGG lemma.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (refl)

open import Terms
open import Reduction
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.Evolve using (_++ʳ_)
open import proof.DGG.RunFrames
open import proof.DGG.CatchupBlameDef using (CatchupBlame)

catchup-blame : CatchupBlame
catchup-blame refl (κ⊑κ () p)
catchup-blame refl (blame⊑ {ℓ = ℓ} wA ⊢M′ p) = ℓ , done
catchup-blame refl (cast⊑ cc-plain M⊑ ct q) with catchup-blame refl M⊑
catchup-blame refl (cast⊑ cc-plain M⊑ ct q) | ℓ′ , r =
  ℓ′ , (ξ-cast* r ++ʳ (Blame-cast then done))
catchup-blame refl (Λ⊑ claim-fresh nv occ liftᴸ-[] v V⊑ q)
  with catchup-blame refl V⊑
catchup-blame refl (Λ⊑ claim-fresh nv occ liftᴸ-[] v V⊑ q) | ℓ′ , r
  with value-run≡ v r
catchup-blame refl (Λ⊑ claim-fresh nv occ liftᴸ-[] (V-simple ()) V⊑ q)
  | ℓ′ , r | refl
catchup-blame refl (ν⊑ L⊑ pA n q) with catchup-blame refl L⊑
catchup-blame refl (ν⊑ L⊑ pA n q) | ℓ′ , r =
  ℓ′ , (ξ-ν* r ++ʳ (Blame-ν then done))
catchup-blame refl (⟪⟫⊑ i bc-plain wi M⊑ b q)
  with catchup-blame refl M⊑
catchup-blame refl (⟪⟫⊑ i bc-plain wi M⊑ b q) | ℓ′ , r
  with ξ-⟪⟫* (int-left i) r
catchup-blame refl (⟪⟫⊑ i bc-plain wi M⊑ b q) | ℓ′ , r | Θ′ , r′ =
  ℓ′ , (r′ ++ʳ (Blame-⟪⟫ then done))

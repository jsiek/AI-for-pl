module strong.proof.ScopedAtUnsealDef where

-- THE SCOPING FACT AT AN ACTIVE FACE, as a STATEMENT MODULE (the `…Def`
-- convention).
--
-- Every rule whose contractum makes an INNER wrapper PRESENT A REP inside
-- Θ₂'s interior needs the same fact — the common wall of notes/DECISIONS
-- ("Peel FIXED and PROVEN; CancelR/TyPeelR/IdPush share ONE wall"):
--
--     the rep an outer `unseal Y` hands back is well formed
--     WHERE THE CONTRACTUM PUTS IT, i.e. on `intC Θ₂ Δ`.
--
--   ScopedAtUnseal = ∀ … → Δ ∣ [] ⊢ (V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ B
--                        → fceC Θ₂ Δ ∋ Y := A
--                        → intC Θ₂ Δ ⊢ᵗ A
--
-- It is stated once, at exactly the redex shape the rules match on (an
-- inert-faced inner wrapper under an `unseal`-faced outer one), so that
-- the CancelR preservation case (proof/CancelFaces.preserve-CancelR) is
-- discharged over it while the fact itself is being derived.  Note what
-- is NOT here: no premise about Θ₁, none about the inner face `c₁`
-- (universally quantified), and nothing Progress would have to supply —
-- the interface is a fact about the redex's TYPING.
--
-- STATUS (2026-09-06).  NOT INHABITED.  The routes tried, each closed by
-- a machine-checked counterexample:
--
--   * as a consequence of `Bwf` — refuted, proof/WallGrounding: the
--     `¬IdPushCase` witness and a REACHABLE wrapper of Examples §12 have
--     the same Δ and the same Θ and differ only in their FACE, so no
--     `Bwf Δ Θ` premise separates them; and the wall is not ⊑-stable, so
--     putting it in `Bwf` breaks `Bwf-⊑`/`⊢retag`/`preserve-TyBeta`.
--
--   * as a consequence of a face-conditioned `env` premise
--     (`scp Θ Δ ⊢ᵗ Bₑ` asked at REVEAL faces only) — refuted for IdPush:
--     the obstruction moves to Θ₁, the INNER (id-faced) layer, which the
--     premise does not constrain (the witness is `Ξ★`/`Θ★₁`,
--     proof/ChainScoped §3).  The candidate switched on the conversion
--     judgment's POLARITY index, retired 2026-09-06, so it can no longer
--     even be stated.
--
--   * pointwise `RepWf` at name-faced boundaries and the REP-CHAIN
--     premise — proof/ChainScoped: the first dies on a closed program,
--     the second on TyBeta's retag (a chain stops at a Λ-bound slot,
--     and TyBeta gives that slot a rep).
--
-- So it is exported HERE as a statement, for the consumers to take as a
-- parameter.  What DOES discharge it: the invariant of proof/WallReach at
-- this redex's active boundary — `WallReach.scoped-at-unseal` is this
-- statement with `RepWf (intC Θ₂ Δ)` as one extra premise (its mask-only
-- step is proven).  So the whole endgame is the gap between
-- `RepWf (intC Θ₂ Δ)` and the redex's own typing.  (That corollary lives
-- in WallReach, not here: WallReach imports Examples, and this module is
-- imported by Preservation, which Examples imports.)

open import Data.List using (List; []; _∷_)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ; _⊢ᵗ_; _∋_:=_)
open import strong.Conversion using (Conv; unseal)
open import strong.Terms using (Term; CtxMorph; _⟪_,_⟫; _∣_⊢_⦂_; intC; fceC)

ScopedAtUnseal : Set
ScopedAtUnseal = ∀ {Δ Θ₁ Θ₂ c₁ V Y A B}
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ B
  → fceC Θ₂ Δ ∋ Y := A
    ---------------------------------------------
  → intC Θ₂ Δ ⊢ᵗ A

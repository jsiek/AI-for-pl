module strong.proof.ScopedAtUnsealDef where

-- THE SCOPING INTERFACE, as a statement module (the `…Def` convention).
--
-- Every rule whose contractum makes an INNER wrapper PRESENT A REP inside
-- Θ₂'s interior needs the same fact — the common wall of notes/DECISIONS
-- ("Peel FIXED and PROVEN; CancelR/TyPeelR/IdPush share ONE wall"):
--
--     the rep an outer `unseal Y` hands back is well formed
--     WHERE THE CONTRACTUM PUTS IT, i.e. on `intC Θ₂ Δ`.
--
-- It is stated here, once, at exactly the redex shape the rules match on
-- (an inert-faced inner wrapper under an `unseal`-faced outer one), so
-- that the CancelR preservation case (proof/CancelFaces.preserve-CancelR)
-- can be discharged over it TODAY while the fact itself is being derived
-- from the strengthened `Bwf` — or, along the invariant route, from
-- `RepWf` + `MaskOnly` (proof/WallReach.unseal-scoped, which is literally
-- this statement with `RepWf (intC Θ₂ Δ)` as an extra premise).
--
-- Note what is NOT here: no premise about Θ₁, no premise about the inner
-- face `c₁` (it is universally quantified), and nothing Progress would
-- have to supply — the interface is a fact about the redex's TYPING.

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ; _⊢ᵗ_; _∋_:=_)
open import strong.Conversion using (Conv; unseal)
open import strong.Terms using (Term; CtxMorph; _⟪_,_⟫; _∣_⊢_⦂_; intC; fceC)

ScopedAtUnseal : Set
ScopedAtUnseal = ∀ {Δ Θ₁ Θ₂ c₁ V Y A B}
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , c₁ ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ B
  → fceC Θ₂ Δ ∋ Y := A
    ----------------------------------------------
  → intC Θ₂ Δ ⊢ᵗ A

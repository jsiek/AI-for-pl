module strong.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.

-- the core
open import strong.Types
open import strong.TypeSubst
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

-- the main theorems
open import strong.Preservation
open import strong.TypeSafety

-- the proof scripts
open import strong.proof.Adversary
open import strong.proof.MaskFacts
open import strong.proof.IdLayer
open import strong.proof.Preserve
open import strong.proof.PeelDual
open import strong.proof.MoveScope
open import strong.proof.TypeSafety
open import strong.proof.PreserveObstruct
open import strong.proof.IdPushReach

-- the regression corpus and the renderer
open import strong.Examples
open import strong.Show
open import strong.proof.Canonicity

-- progress (the canonical-forms suite and the theorem)
open import strong.proof.Canonical
open import strong.Progress

-- THE WALL, AS A HISTORICAL RECORD.  These three modules searched for an
-- INVARIANT that would ground the premise `intC Θ₂ Δ ⊢ᵗ A` — the one the
-- old CancelR/IdPush contracta needed.  The SCOPE MOVE (strong.Reduction
-- §2b) removes the need: the contractum presents the rep on Θ₂'s FACE
-- type context, where `wf-liftN-prep` supplies it.  They are kept because
-- each is a machine-checked refutation of a candidate design, and each
-- still says something true about `Δ`, `Θ` and `RepWf`; nothing in the
-- main development depends on them.
open import strong.proof.WallReach
open import strong.proof.WallGrounding
open import strong.proof.ChainScoped

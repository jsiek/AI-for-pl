module strong-rep-nu.notes.All where

-- Aggregate driver for the gated investigation and regression notes.
-- Deliberately ungated scratch probes are omitted.

-- (The thirteen-run reduction suite that used to head this list was
-- merged into strong-rep-nu.Examples on 2026-09-21; strong-rep-nu.All checks
-- it.)
open import strong-rep-nu.notes.CrossingAudit
open import strong-rep-nu.notes.WrapPremise
open import strong-rep-nu.notes.RepresentationVariablesProbe
open import strong-rep-nu.notes.RepWeakenBindsWall

-- DROPPED IN THE `ν` PORT (strong-rep-nu, 2026-09-24): three historical
-- wall records whose checked content is exact states of runs through the
-- retired `·[]`/TyBeta/TyPeelR rules — notes/CancelRReachabilityWitness,
-- notes/RawRunProbe (which runs that witness's program) and
-- notes/AddLock0Wall.  The files were DELETED here; strong-rep-store's
-- notes/ holds their checked versions.  The CancelR witness program itself
-- still runs green as strong-rep-nu.Examples §8 `S`.
--
-- DROPPED IN THE MERGE PORT (2026-09-24): notes/CancelRShiftWall, the
-- record of the `CancelR` weakening wall.  Its checked content is a
-- `CancelR` step and `preserve-CancelR`; both rules it was about
-- (`CancelR`, `IdPush`) are subsumed by `Merge`, whose preservation
-- case is strong-rep-nu.proof.MoveScope.preserve-Merge.  The file was
-- DELETED; the git history holds it.
--
-- DROPPED AFTER THE MERGE PORT (Jeremy, 2026-09-24): the wall probes
-- for rules no longer in the design — notes/ReUnlockWall (the
-- `CancelR`/`IdPush` contracta that motivated `conv-bind-live`) and
-- notes/ForallPayloadWall (the `TyPeelR-⟪⟫`/`IdPush` crossing
-- spellings).  DELETED here; strong-rep-store's notes/ holds both.

-- COLOR PRESERVATION on one run (2026-09-21): the statement layer of
-- strong-rep-nu.Residual exercised end to end on a Wrap under a Λ.
open import strong-rep-nu.notes.ColorPreservationProbe
open import strong-rep-nu.notes.StackCensus

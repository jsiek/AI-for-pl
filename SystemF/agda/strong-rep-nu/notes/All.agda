module strong-rep-nu.notes.All where

-- Aggregate driver for the gated investigation and regression notes.
-- Deliberately ungated scratch probes are omitted.

-- (The thirteen-run reduction suite that used to head this list was
-- merged into strong-rep-nu.Examples on 2026-09-21; strong-rep-nu.All checks
-- it.)
open import strong-rep-nu.notes.ReUnlockWall
open import strong-rep-nu.notes.ForallPayloadWall
open import strong-rep-nu.notes.CrossingAudit
open import strong-rep-nu.notes.PeelPremise
open import strong-rep-nu.notes.RepresentationVariablesProbe
open import strong-rep-nu.notes.RepWeakenBindsWall
open import strong-rep-nu.notes.CancelRShiftWall

-- DROPPED IN THE `ν` PORT (strong-rep-nu, 2026-09-24): three historical
-- wall records whose checked content is exact states of runs through the
-- retired `·[]`/TyBeta/TyPeelR rules — notes/CancelRReachabilityWitness,
-- notes/RawRunProbe (which runs that witness's program) and
-- notes/AddLock0Wall.  The files were DELETED here; strong-rep-store's
-- notes/ holds their checked versions.  The CancelR witness program itself
-- still runs green as strong-rep-nu.Examples §8 `S`.

-- COLOR PRESERVATION on one run (2026-09-21): the statement layer of
-- strong-rep-nu.Residual exercised end to end on a Peel under a Λ.
open import strong-rep-nu.notes.ColorPreservationProbe

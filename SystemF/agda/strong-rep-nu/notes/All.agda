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
open import strong-rep-nu.notes.CancelRReachabilityWitness
open import strong-rep-nu.notes.RawRunProbe
open import strong-rep-nu.notes.RepresentationVariablesProbe
open import strong-rep-nu.notes.RepWeakenBindsWall
open import strong-rep-nu.notes.AddLock0Wall
open import strong-rep-nu.notes.CancelRShiftWall

-- COLOR PRESERVATION on one run (2026-09-21): the statement layer of
-- strong-rep-nu.Residual exercised end to end on a Peel under a Λ.
open import strong-rep-nu.notes.ColorPreservationProbe

module strong-rep-store.notes.All where

-- Aggregate driver for the gated investigation and regression notes.
-- Deliberately ungated scratch probes are omitted.

-- (The thirteen-run reduction suite that used to head this list was
-- merged into strong-rep-store.Examples on 2026-09-21; strong-rep-store.All checks
-- it.)
open import strong-rep-store.notes.ReUnlockWall
open import strong-rep-store.notes.ForallPayloadWall
open import strong-rep-store.notes.CrossingAudit
open import strong-rep-store.notes.PeelPremise
open import strong-rep-store.notes.CancelRReachabilityWitness
open import strong-rep-store.notes.RawRunProbe
open import strong-rep-store.notes.RepresentationVariablesProbe
open import strong-rep-store.notes.RepWeakenBindsWall
open import strong-rep-store.notes.AddLock0Wall
open import strong-rep-store.notes.CancelRShiftWall

-- COLOR PRESERVATION on one run (2026-09-21): the statement layer of
-- strong-rep-store.Residual exercised end to end on a Peel under a Λ.
open import strong-rep-store.notes.ColorPreservationProbe

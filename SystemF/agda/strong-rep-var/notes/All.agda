module strong-rep-var.notes.All where

-- Aggregate driver for the gated investigation and regression notes.
-- Deliberately ungated scratch probes are omitted.

-- (The thirteen-run reduction suite that used to head this list was
-- merged into strong-rep-var.Examples on 2026-09-21; strong-rep-var.All checks
-- it.)
open import strong-rep-var.notes.ReUnlockWall
open import strong-rep-var.notes.ForallPayloadWall
open import strong-rep-var.notes.CrossingAudit
open import strong-rep-var.notes.PeelPremise
open import strong-rep-var.notes.CancelRReachabilityWitness
open import strong-rep-var.notes.RawRunProbe
open import strong-rep-var.notes.RepresentationVariablesProbe
open import strong-rep-var.notes.RepWeakenBindsWall
open import strong-rep-var.notes.AddLock0Wall
open import strong-rep-var.notes.CancelRShiftWall

-- COLOR PRESERVATION on one run (2026-09-21): the statement layer of
-- strong-rep-var.Residual exercised end to end on a Peel under a Λ.
open import strong-rep-var.notes.ColorPreservationProbe

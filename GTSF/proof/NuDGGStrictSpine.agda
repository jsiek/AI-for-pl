module proof.NuDGGStrictSpine where

-- File Charter:
--   * Aggregates the hole-free DGG spine and its terminal-trace support.
--   * Deliberately excludes the partial terminal proofs and active
--     catch-up/dispatcher scratch module.
--   * Provides a strict check target as proof components are promoted.

import proof.NuDGGPreservation
import proof.NuDGGSpine
import proof.NuDGGTerminal
import proof.NuDGGTerminalBackwardBlameAssembly
import proof.NuDGGTraceAlignment
import proof.NuDGGTraceMeasure
import proof.NuDGGWeakResultPreservation

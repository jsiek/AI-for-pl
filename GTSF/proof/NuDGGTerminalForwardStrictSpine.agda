module proof.NuDGGTerminalForwardStrictSpine where

-- File Charter:
--   * Aggregates the strict forward terminal architecture without importing
--     either unfinished semantic engine.
--   * Checks the source one-step and right-value catch-up contracts together
--     with the hole-free source-trace assembly.
--   * Provides a focused alternative to checking the broad DGG spine.

import proof.NuImprecisionWorldCoherentSourceOneStepDef
import proof.NuImprecisionWorldCoherentRightValueCatchupDef
import proof.NuDGGTerminalForwardDef
import proof.NuDGGTerminalForwardProof

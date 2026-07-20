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
import proof.NuDGGTerminalBackwardValueDef
import proof.NuDGGTerminalBackwardValueProof
import proof.NuImprecisionOneStepDef
import proof.NuImprecisionValueCatchupDef
import proof.NuDGGTraceAlignment
import proof.NuDGGTraceMeasure
import proof.NuDGGWeakResultPreservation
import proof.NuImprecisionCatchupSourceAllocationTerminal
import proof.NuImprecisionCatchupSourceCastTerminal
import proof.NuImprecisionOneStepSourceCastFrames
import proof.NuImprecisionOneStepSourceConversionFrames
import proof.NuImprecisionOneStepPrimitiveFrames
import proof.NuImprecisionOneStepPrimitiveLeaves
import proof.NuImprecisionOneStepApplicationRoots
import proof.NuImprecisionOneStepTargetBlameRoots
import proof.NuImprecisionOneStepTargetCastFrames
import proof.NuImprecisionOneStepTargetConversionFrames
import proof.NuImprecisionQuotientInstView
import proof.NuImprecisionTargetBlameCatchup

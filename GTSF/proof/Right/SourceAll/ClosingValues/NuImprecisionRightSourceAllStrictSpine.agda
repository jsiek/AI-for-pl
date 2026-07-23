module
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllStrictSpine
  where

-- File Charter:
--   * Provides the focused strict-check spine for source-universal
--     right-value closing.
--   * Imports the counterexample, flat case statements, constructor-form
--     dispatchers, and higher-order closing assembly.
--   * Intended for the routine edit/check loop; the broader terminal-forward
--     spine remains an integration-milestone check.
--   * Contains no theorem, implementation, postulate, hole, permissive
--     option, or broad obsolete simulation import.

import proof.Source.Core.NuImprecisionSourceOnlyContextFactorCounterexample
import proof.Right.Core.NuImprecisionRightContextAction
import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupContextDef
import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupContextDef
import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupContextProof
import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupFactorDef
import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupFactorProof
import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyTransportDropLemma
import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyAllBodyTransportDropLemma
import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyRightBodyTransportDropLemma
import
  proof.Left.LiftedStore.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorLemma
import
  proof.Store.Correspondence.NuImprecisionStoreCorrespondenceDropLeftLemma
import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDropLeftStoreLemma
import
  proof.Source.Core.NuImprecisionSourceOnlyContextDrop
import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyCaughtFactorLemma
import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixLeftLiftFactorLemma
import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixAlgebra
import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStoreLineageCompositionLemma
import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextLemma
import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextLemma
import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextLemma
import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextLemma
import
  proof.Right.Core.NuImprecisionRightAllocationContextSeed
import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceNarrowFrameContextLemma
import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceWidenFrameContextLemma
import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceRevealFrameContextLemma
import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceConcealFrameContextLemma
import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowFrameContextDef
import proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllSourceFramesDef
import proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
import proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllConstantBodyDef
import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllConstantBodyProof
import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllLambdaBodyDef
import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllLambdaBodyProof
import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyDef
import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyProof
import proof.Right.SourceAll.Core.NuImprecisionRightSourceAllUniversalBodyDef
import proof.Right.SourceAll.Core.NuImprecisionRightSourceAllUniversalBodyProof
import proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllValueFormsDef
import proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllValueFormsProof
import proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingDispatcherProof
import proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingProof
import proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesProof

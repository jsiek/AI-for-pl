module LR-narrow.Context.ContextAll where

-- File Charter:
--   * Checks the currently proved graduality context-lemma foundation.
--   * Imports each focused context-support module separately.
--   * Adds no compatibility wrapper or alias.

import LR-narrow.Context.Constant
import LR-narrow.Context.AssumptionDownward
import LR-narrow.Context.AssumptionFuture
import LR-narrow.Context.ClosedValueFuture
import LR-narrow.Context.ClosureApplication
import LR-narrow.Context.DynamicPayloadIntroduction
import LR-narrow.Context.FunctionsFuture
import LR-narrow.Context.GroundTagAgreementFuture
import LR-narrow.Context.KripkeRefl
import LR-narrow.Context.KripkeTrans
import LR-narrow.Context.Lambda
import LR-narrow.Context.RightBinderRebase
import LR-narrow.Context.RightUniversalsFuture
import LR-narrow.Context.PairedBinderRebase
import LR-narrow.Context.PairedBinderFresh
import LR-narrow.Context.PairedBindingFunctional
import LR-narrow.Context.PairedBindingInjective
import LR-narrow.Context.RelatedEnvironmentLookup
import LR-narrow.Context.RelatedEnvironments
import LR-narrow.Context.TermRelation
import LR-narrow.Context.TagEqualityFuture
import LR-narrow.Context.TagMatchBackward
import LR-narrow.Context.TagMatchForward
import LR-narrow.Context.TypedEndpointsFuture
import LR-narrow.Context.ValueDownward
import LR-narrow.Context.ValueFuture
import LR-narrow.Context.Variable
import LR-narrow.Context.UniversalsFuture

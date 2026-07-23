module All where

-- File Charter:
--   * Aggregate checker for the canonical public GTSF module surface.
--   * Imports every top-level GTSF `.agda` module except this file.
--   * Does not import `proof/` modules directly.  Proof modules must enter
--     this aggregate indirectly through the appropriate top-level module.
--   * New proof files should be connected to a public top-level module, not
--     added here.

import Coercions
import Compile
import CompileTermImprecision
import Consistency
import Conversion
import Ctx
import DynamicGradualGuarantee
import Eval
import ForallPermutation
import GradualExamples
import GradualTermImprecision
import GradualTermNarrowing
import GradualTerms
import GradualTypeCheck
import Imprecision
import ImprecisionWf
import NarrowWiden
import NarrowWidenComposition
import NarrowingExamples
import NuExamplesFresh
import NuMetaTheory
import NuReduction
import NuStore
import NuTermImprecision
import NuTerms
import PairedWideningCompatibility
import Primitives
import QuotientedTermImprecision
import ReductionTrace
import Run
import Store
import StoreCorrespondence
import TermNarrowing
import TermTyping
import TypeCheck
import Types

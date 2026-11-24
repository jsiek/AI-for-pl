{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.RightInjCoverageRegression where

-- File Charter:
--   * Replaces the former broad SourceStrip dispatcher reproducer with a
--     direct regression gate for the RightInj inversion proof.
--   * The old dispatcher required NON_COVERING and triggered an Agda 2.7.0.1
--     internal error.  The live proof now refutes its bare source-seal branch
--     from the exact constructor indices, so importing it checks ordinary
--     exhaustive coverage under --safe.

import proof.DGG.Inversion.RightInjInversion2Lemma

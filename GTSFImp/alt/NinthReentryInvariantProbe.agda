module alt.NinthReentryInvariantProbe where

-- History (U22 ninth re-entry probe): the live-bit telescope let an end
-- marker claim an anchor different from the type variable it removed.  That produced
-- a source/target lookup mismatch under re-entry.  U27 makes σ the intrinsic
-- type-variable-to-anchor map and gives `,end[_]` no anchor argument, so the lying
-- telescope is no longer representable.  Positive adjacent and non-adjacent
-- re-entry computations are checked in `alt.ThetaRegression`.

module proof.TermNarrowingProperties where

-- File Charter:
--   * Reserved for admissible rules and structural lemmas for typed term
--     narrowing.
--   * The two-sided typed cast rules now live directly in `TermNarrowing`.
--     They are constructors rather than derived rules because some examples
--     use seal-mode intermediate coercions that are not canonical `∶ᶜ`
--     indices.

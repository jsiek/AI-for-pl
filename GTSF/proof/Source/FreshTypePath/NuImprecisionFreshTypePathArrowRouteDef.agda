module proof.Source.FreshTypePath.NuImprecisionFreshTypePathArrowRouteDef where

-- File Charter:
--   * Defines equality of type-variable paths modulo insertion or removal of
--     universal-body edges.
--   * Preserves the complete arrow-domain/codomain route while deliberately
--     forgetting only universal nesting depth.
--   * Provides body-edge normalizers used by path transport and inversion.
--   * Contains no imprecision theorem, conversion theorem, postulate, hole,
--     permissive option, handler import, or simulation import.

open import proof.Source.FreshTypePath.NuImprecisionFreshTypePath using
  ( TypePath
  ; body
  ; codomain
  ; domain
  ; here
  )


data SameArrowRoute : TypePath → TypePath → Set where
  same-here : SameArrowRoute here here

  same-domain : ∀ {p q} →
    SameArrowRoute p q →
    SameArrowRoute (domain p) (domain q)

  same-codomain : ∀ {p q} →
    SameArrowRoute p q →
    SameArrowRoute (codomain p) (codomain q)

  skip-left-body : ∀ {p q} →
    SameArrowRoute p q →
    SameArrowRoute (body p) q

  skip-right-body : ∀ {p q} →
    SameArrowRoute p q →
    SameArrowRoute p (body q)


strip-left-body : ∀ {p q} →
  SameArrowRoute (body p) q →
  SameArrowRoute p q
strip-left-body (skip-left-body route) = route
strip-left-body (skip-right-body route) =
  skip-right-body (strip-left-body route)


strip-right-body : ∀ {p q} →
  SameArrowRoute p (body q) →
  SameArrowRoute p q
strip-right-body (skip-left-body route) =
  skip-left-body (strip-right-body route)
strip-right-body (skip-right-body route) = route

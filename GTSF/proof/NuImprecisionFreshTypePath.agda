module proof.NuImprecisionFreshTypePath where

-- File Charter:
--   * Defines proof-relevant paths to type-variable occurrences for the
--     source-only/paired-binder cycle argument.
--   * Proves path functionality and the finite-type obstruction saying that
--     one path cannot also occur below one additional universal constructor.
--   * Contains no conversion, store, term-imprecision, simulation, postulate,
--     hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.Nat using (_≟_; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Nullary using (no; yes)
open import Types using (Ty; TyVar; ＇_; ‵_; ★; _⇒_; `∀; occurs)


data TypePath : Set where
  here : TypePath
  domain : TypePath → TypePath
  codomain : TypePath → TypePath
  body : TypePath → TypePath


data VarAtPath (X : TyVar) : TypePath → Ty → Set where
  at-here : VarAtPath X here (＇ X)

  at-domain : ∀ {p A B} →
    VarAtPath X p A →
    VarAtPath X (domain p) (A ⇒ B)

  at-codomain : ∀ {p A B} →
    VarAtPath X p B →
    VarAtPath X (codomain p) (A ⇒ B)

  at-body : ∀ {p A} →
    VarAtPath (suc X) p A →
    VarAtPath X (body p) (`∀ A)


occurs-to-var-at-path :
  ∀ {X A} →
  occurs X A ≡ true →
  ∃[ p ] VarAtPath X p A
occurs-to-var-at-path {X} {A = ＇ Y} occ with X ≟ Y
occurs-to-var-at-path {X} {A = ＇ .X} occ | yes refl =
  here , at-here
occurs-to-var-at-path {X} {A = ＇ Y} () | no X≢Y
occurs-to-var-at-path {A = ‵ ι} ()
occurs-to-var-at-path {A = ★} ()
occurs-to-var-at-path {X} {A = A ⇒ B} occ
    with occurs X A in occ-A
occurs-to-var-at-path {X} {A = A ⇒ B} occ | true =
  let p , x-at = occurs-to-var-at-path {X = X} {A = A} occ-A in
  domain p , at-domain x-at
occurs-to-var-at-path {X} {A = A ⇒ B} occ | false =
  let p , x-at = occurs-to-var-at-path {X = X} {A = B} occ in
  codomain p , at-codomain x-at
occurs-to-var-at-path {X} {A = `∀ A} occ =
  let p , x-at = occurs-to-var-at-path {X = suc X} {A = A} occ in
  body p , at-body x-at


var-at-path-functional :
  ∀ {X Y p A} →
  VarAtPath X p A →
  VarAtPath Y p A →
  X ≡ Y
var-at-path-functional at-here at-here = refl
var-at-path-functional (at-domain x-at) (at-domain y-at) =
  var-at-path-functional x-at y-at
var-at-path-functional (at-codomain x-at) (at-codomain y-at) =
  var-at-path-functional x-at y-at
var-at-path-functional (at-body x-at) (at-body y-at) =
  suc-injective (var-at-path-functional x-at y-at)


var-at-path-not-below-itself :
  ∀ {X Y p A} →
  VarAtPath X p A →
  VarAtPath Y (body p) A →
  ⊥
var-at-path-not-below-itself at-here ()
var-at-path-not-below-itself (at-domain x-at) ()
var-at-path-not-below-itself (at-codomain x-at) ()
var-at-path-not-below-itself (at-body x-at) (at-body y-at) =
  var-at-path-not-below-itself x-at y-at


var-at-path-not-above-itself :
  ∀ {X Y p A} →
  VarAtPath X (body p) A →
  VarAtPath Y p A →
  ⊥
var-at-path-not-above-itself x-at y-at =
  var-at-path-not-below-itself y-at x-at

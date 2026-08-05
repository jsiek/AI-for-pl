module proof.InterpreterSealValueEliminationProof where

-- File Charter:
--   * Inverts paired sealed value narrowing.
--   * Excludes dynamic and quotient seal shapes structurally.
--   * Pushes inversion through source-name substitution provenance.
--   * Contains no interpreter computation or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame-source-not-sealed)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterValueSubstitutionShape using
  (substitute-name-sealed-source)
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    InterpreterTypeNarrowing


sealed-payload-injective :
  ∀ {α V U} →
  sealed α V ≡ sealed α U →
  V ≡ U
sealed-payload-injective refl =
  refl


paired-sealed-payloads :
  ∀ {W W′ α α′ V V′}
    {R : WorldRelation W W′} →
  ValueNarrowing R (sealed α V) (sealed α′ V′) →
  ValueNarrowing R V V′
paired-sealed-payloads (sealed⊑ α~α′ V~V′) =
  V~V′
paired-sealed-payloads
    (left-dynamic-sealed⊑ dynamic () V~V′)
paired-sealed-payloads
    (quotient-value-frame⊑ frame U-ok U′-ok V~V′) =
  ⊥-elim (quotient-value-frame-source-not-sealed frame)
paired-sealed-payloads
    {α = source}
    (left-name-instantiated⊑
      {X = X} {α = fresh} {V = V}
      R≤S fresh-ok result-eq V~V′)
    with substitute-name-sealed-source X fresh V result-eq
paired-sealed-payloads
    {α = source}
    (left-name-instantiated⊑
      {X = X} {α = fresh} {V = .(sealed source Q)}
      R≤S fresh-ok result-eq V~V′)
    | Q , refl =
  left-name-instantiated⊑
    R≤S fresh-ok
    (sealed-payload-injective result-eq)
    (paired-sealed-payloads V~V′)


paired-sealed-link :
  ∀ {W W′ α α′ V V′}
    {R : WorldRelation W W′} →
  ValueNarrowing R (sealed α V) (sealed α′ V′) →
  SealLink R α α′
paired-sealed-link (sealed⊑ α~α′ V~V′) =
  α~α′
paired-sealed-link
    (left-dynamic-sealed⊑ dynamic () V~V′)
paired-sealed-link
    (quotient-value-frame⊑ frame U-ok U′-ok V~V′) =
  ⊥-elim (quotient-value-frame-source-not-sealed frame)
paired-sealed-link
    {α = source}
    (left-name-instantiated⊑
      {X = X} {α = fresh} {V = V}
      R≤S fresh-ok result-eq V~V′)
    with substitute-name-sealed-source X fresh V result-eq
paired-sealed-link
    {α = source}
    (left-name-instantiated⊑
      {X = X} {α = fresh} {V = .(sealed source Q)}
      R≤S fresh-ok result-eq V~V′)
    | Q , refl =
  WorldProof.seal-link-weaken R≤S (paired-sealed-link V~V′)

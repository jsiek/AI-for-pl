module proof.InterpreterTagNarrowingProof where

-- File Charter:
--   * Proves that related runtime tags agree on successful checks.
--   * Reflects a target tag mismatch to the source, as required for blame.
--   * Uses only world correspondence and equality; no interpreter recursion.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (cong)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterTagNarrowingCore
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowingProperties
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; idˣ; idι; _↦_; id★)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Types

module WorldProperties =
  WorldNarrowingProperties InterpreterTypeNarrowing

tagOf-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ θ θ′ G H}
    {R : TagRelatedWorlds.WorldRelation W W′}
    (gG : Ground G) (gH : Ground H) →
  TypeEnvironmentRealization R Φ θ θ′ →
  Φ ∣ Δᴸ ⊢ G ⊑ H ⊣ Δᴿ →
  Σ[ tag ∈ Tag ]
  Σ[ tag′ ∈ Tag ]
    tagOf θ gG ≡ just tag ×
    tagOf θ′ gH ≡ just tag′ ×
    TagNarrowing R tag tag′
tagOf-narrowing (＇ X) (＇ X′) runtime
    (idˣ assumption X<Δᴸ X′<Δᴿ)
    with realizes-assumption runtime assumption
tagOf-narrowing (＇ X) (＇ X′) runtime
    (idˣ assumption X<Δᴸ X′<Δᴿ)
    | paired-assumption left-eq right-eq name~name′
    rewrite left-eq | right-eq =
  _ , _ , refl , refl , variable-tag⊑ name~name′
tagOf-narrowing (‵ ι) (‵ .ι) runtime idι =
  _ , _ , refl , refl , base-tag⊑ _
tagOf-narrowing ★⇒★ ★⇒★ runtime (id★ ↦ id★) =
  _ , _ , refl , refl , function-tag⊑

tag-narrowing-functional :
  ∀ {W W′ tag tag′ other′}
    {R : TagRelatedWorlds.WorldRelation W W′} →
  TagNarrowing R tag tag′ →
  TagNarrowing R tag other′ →
  tag′ ≡ other′
tag-narrowing-functional
    (variable-tag⊑ name~name′)
    (variable-tag⊑ name~other′) =
  cong variable-tag
    (WorldProperties.type-name-narrowing-functional
      name~name′ name~other′)
tag-narrowing-functional (base-tag⊑ ι) (base-tag⊑ .ι) =
  refl
tag-narrowing-functional function-tag⊑ function-tag⊑ =
  refl

tag-narrowing-injective :
  ∀ {W W′ tag other tag′}
    {R : TagRelatedWorlds.WorldRelation W W′} →
  TagNarrowing R tag tag′ →
  TagNarrowing R other tag′ →
  tag ≡ other
tag-narrowing-injective
    (variable-tag⊑ name~name′)
    (variable-tag⊑ other~name′) =
  cong variable-tag
    (WorldProperties.type-name-narrowing-injective
      name~name′ other~name′)
tag-narrowing-injective (base-tag⊑ ι) (base-tag⊑ .ι) =
  refl
tag-narrowing-injective function-tag⊑ function-tag⊑ =
  refl

tag-match-forward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : TagRelatedWorlds.WorldRelation W W′} →
  TagNarrowing R expected expected′ →
  TagNarrowing R actual actual′ →
  expected ≡ actual →
  expected′ ≡ actual′
tag-match-forward expected~expected′
    actual~actual′ refl =
  tag-narrowing-functional
    expected~expected′ actual~actual′

tag-match-backward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : TagRelatedWorlds.WorldRelation W W′} →
  TagNarrowing R expected expected′ →
  TagNarrowing R actual actual′ →
  expected′ ≡ actual′ →
  expected ≡ actual
tag-match-backward expected~expected′
    actual~actual′ refl =
  tag-narrowing-injective
    expected~expected′ actual~actual′

target-tag-mismatch-reflects :
  ∀ {W W′ expected expected′ actual actual′}
    {R : TagRelatedWorlds.WorldRelation W W′} →
  TagNarrowing R expected expected′ →
  TagNarrowing R actual actual′ →
  (expected′ ≡ actual′ → Data.Empty.⊥) →
  expected ≡ actual →
  Data.Empty.⊥
target-tag-mismatch-reflects
    expected~expected′ actual~actual′ expected′≢actual′
    expected≡actual =
  expected′≢actual′
    (tag-match-forward
      expected~expected′ actual~actual′ expected≡actual)

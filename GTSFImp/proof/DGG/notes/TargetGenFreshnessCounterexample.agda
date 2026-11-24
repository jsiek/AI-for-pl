{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetGenFreshnessCounterexample where

-- File Charter:
--   * Gives a checked counterexample to deriving target-allocation freshness
--     from the target-only generated-universal value, typing, and CTI inputs.
--   * Uses an aligned base variable X.  The source polymorphic identity is
--     related to a target dynamic identity cast to its polymorphic type, but
--     applying the target value at X cannot allocate a right-only cell whose
--     direct entry is X.
--   * Records why the private instantiation worker must retain the provenance
--     of the fresh target name allocated by the outer beta-inst step.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using
  ( Ty; TyVar; ★; ＇_; _⇒_; `∀; NonVar; _∈ᵗ_; nonvar-fun; var-∈
  ; ∈-fun-left
  )
open import TyStore using (store-empty; store-lift)
open import TermCtx using (Z)
open import Consistency using
  ( Env∼; _⊢_∼_; idᶜ; genᵐ; flipᵐ; id; _!; ？_; _↦_; gen_
  )
import Imprecision as I
import CastTerms as T
open T using
  ( Term; Value; GenSafe; ⟨_,_,_⟩; _⊢_⦂_; Λ_; ƛ_; `_; _⟨_⟩
  ; safe-⇒; genᵥ; _《_》; ⊢`; ⊢ƛ; ⊢⟨⟩
  )
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; allv-gen)
open import proof.DGG.World
import Reduction as R
open import proof.ImprecisionConsistency using (fin-suc-injective)
open import proof.DGG.WorldEvolution using
  ( CtxChange; WorldEvolution; keep-ctx; storeChange
  ; evolution-keep; evolution-bind-right
  )


one : Set
one = Fin.Fin (suc zero)


base-context : T.Ctx
base-context = ⟨ suc zero , store-lift store-empty , [] ⟩


-- X is aligned across the two endpoints.
aligned-X-world : base-context ⊑ᶜ base-context
aligned-X-world = liftBothᶜ I.X⊑X emptyᶜ


source-polymorphic-body : Ty (suc (suc zero))
source-polymorphic-body = ＇ Fin.zero ⇒ ＇ Fin.zero


target-polymorphic-body : Ty (suc (suc zero))
target-polymorphic-body = ＇ Fin.zero ⇒ ＇ Fin.zero


target-dynamic-function : Ty (suc zero)
target-dynamic-function = ★ ⇒ ★


target-gen-consistency :
  genᵐ (idᶜ {suc zero}) ⊢
    (★ ⇒ ★) ∼ (＇ Fin.zero ⇒ ＇ Fin.zero)
target-gen-consistency =
  ((id (＇ Fin.zero)) !) ↦ (？ (id (＇ Fin.zero)))


target-function-not-star : target-dynamic-function ≢ ★
target-function-not-star ()


instance
  target-zero-occurs : Fin.zero ∈ᵗ target-polymorphic-body
  target-zero-occurs = ∈-fun-left var-∈


target-body : Term (suc zero)
target-body = ƛ (T.` zero)


target-body-value : Value target-body
target-body-value = T.ƛ (T.` zero)


target-body-typing :
  base-context ⊢ target-body ⦂ target-dynamic-function
target-body-typing = ⊢ƛ (⊢` Z)


target-generated-value : Term (suc zero)
target-generated-value =
  target-body ⟨ (gen target-gen-consistency) target-function-not-star ⟩


target-generated-value-is-value : Value target-generated-value
target-generated-value-is-value =
  target-body-value 《 genᵥ target-function-not-star safe-⇒ 》


target-generated-value-typing :
  base-context ⊢ target-generated-value ⦂ `∀ target-polymorphic-body
target-generated-value-typing =
  ⊢⟨⟩ target-body-typing
    ((gen target-gen-consistency) target-function-not-star)


target-generated-all-view : AllValueView target-generated-value
target-generated-all-view =
  allv-gen target-body-value target-function-not-star safe-⇒ refl


source-body-target-body-imprecision :
  liftLeftᶜ aligned-X-world ⊢²
    T.ƛ (T.` zero) ⊑ target-body
    ∶ I.⇒⊑⇒ (I.X⊑★ {X = Fin.zero} refl)
              (I.X⊑★ {X = Fin.zero} refl)
source-body-target-body-imprecision =
  CTI.ƛ⊑ƛ²
    {pA = I.X⊑★ {X = Fin.zero} refl}
    {pB = I.X⊑★ {X = Fin.zero} refl}
    (CTI.x⊑x² {p = I.X⊑★ {X = Fin.zero} refl} Z Z)


before-gen-type-imprecision :
  `∀ source-polymorphic-body ⊑ᵀ⟨ aligned-X-world ⟩
    target-dynamic-function
before-gen-type-imprecision =
  I.∀⊑ nonvar-fun (∈-fun-left var-∈)
    (I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl))


after-gen-type-imprecision :
  `∀ source-polymorphic-body ⊑ᵀ⟨ aligned-X-world ⟩
    `∀ target-polymorphic-body
after-gen-type-imprecision =
  I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.X⊑X)


source-before-gen-imprecision :
  aligned-X-world ⊢²
    T.Λ (T.ƛ (T.` zero)) ⊑ target-body
    ∶ before-gen-type-imprecision
source-before-gen-imprecision =
  CTI.Λ⊑² nonvar-fun (∈-fun-left var-∈)
    (T.ƛ (T.` zero)) target-body-typing
    source-body-target-body-imprecision before-gen-type-imprecision


source-target-gen-imprecision :
  aligned-X-world ⊢²
    T.Λ (T.ƛ (T.` zero)) ⊑ target-generated-value
    ∶ after-gen-type-imprecision
source-target-gen-imprecision =
  CTI.⊑cast²
    ((gen target-gen-consistency) target-function-not-star)
    source-before-gen-imprecision after-gen-type-imprecision


-- The following is exactly the missing pre-IH proposition for the target
-- beta-gen step at X.  It is false because X is already aligned with the
-- source endpoint.
target-X-not-fresh : RightBindFreshᶜ aligned-X-world (＇ Fin.zero) → ⊥
target-X-not-fresh (inj₁ ())
target-X-not-fresh (inj₂ (Y , refl , disaligned)) =
  disaligned Fin.zero refl


-- By contrast, the actual public instantiation branch first allocates a
-- target-only dynamic cell.  Its new name is constructively fresh for the
-- following generated-cast allocation.  This is the provenance that the
-- current world-agnostic InstantiationSpine does not retain.
beta-inst-name-fresh : ∀ {Γᴸ Γᴿ : T.Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → RightBindFreshᶜ (bindRightᶜ γ ★ (inj₁ refl)) (＇ Fin.zero)
beta-inst-name-fresh =
  inj₂ (Fin.suc Fin.zero , refl , λ Xᴸ ())


-- This smaller predicate is the genuine provenance carried by a target name:
-- the name has no aligned source occupant in the current world.  It implies
-- exactly the RightBindFreshᶜ fact needed to allocate a cell containing that
-- name, but unlike the latter proposition it can be seeded at allocation and
-- transported along target-only evolution.
TargetOnlyNameᶜ : ∀ {Γᴸ Γᴿ : T.Ctx}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → TyVar (T.Δᵉ Γᴿ)
  → Set
TargetOnlyNameᶜ γ X = ∀ Xᴸ
  → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≢ toRenameⁱ (ηᴿᶜ γ) X


target-only-name-fresh : ∀ {Γᴸ Γᴿ : T.Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {X : TyVar (T.Δᵉ Γᴿ)}
  → TargetOnlyNameᶜ γ X
  → RightBindFreshᶜ γ (＇ X)
target-only-name-fresh {X = X} target-only =
  inj₂ (Fin.suc X , refl , λ Xᴸ aligned →
    target-only Xᴸ (fin-suc-injective aligned))


right-bind-new-target-only : ∀ {Γᴸ Γᴿ : T.Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {B : Ty (T.Δᵉ Γᴿ)}
    {fresh : RightBindFreshᶜ γ B}
  → TargetOnlyNameᶜ (bindRightᶜ γ B fresh) Fin.zero
right-bind-new-target-only Xᴸ ()


target-only-name-evolution : ∀ {Γᴸ Γᴿ Γᴿ′ : T.Ctx}
    {W : Γᴸ ⊑ᶜ Γᴿ} {W′ : Γᴸ ⊑ᶜ Γᴿ′}
    {stepᴿ : CtxChange Γᴿ Γᴿ′}
    {X : TyVar (T.Δᵉ Γᴿ)}
  → WorldEvolution {W = W} {W′ = W′} keep-ctx stepᴿ
  → TargetOnlyNameᶜ W X
  → TargetOnlyNameᶜ W′ (R.applyVar (storeChange stepᴿ) X)
target-only-name-evolution evolution-keep target-only = target-only
target-only-name-evolution (evolution-bind-right fresh refl) target-only
    Xᴸ aligned =
  target-only Xᴸ (fin-suc-injective aligned)


------------------------------------------------------------------------
-- Proposed private worker state
------------------------------------------------------------------------

-- Keep InstantiationSpine as the syntax/measure state.  Add a private,
-- world-indexed evidence judgment whose index is that exact spine:
--
--   SpineNamesTargetOnlyᶜ γ spine
--
-- Its type-transport, cast, reveal, and conceal clauses merely recurse on the
-- tail.  Its name-type-app clause stores TargetOnlyNameᶜ γ X for that
-- frame and recurses on the tail.  Thus freshness is not an arbitrary worker
-- argument: every pending name application carries allocation provenance.
--
-- The public beta-inst entry constructs the head evidence with
-- right-bind-new-target-only.  The target-gen branch obtains its exact
-- RightBindFreshᶜ premise with target-only-name-fresh.  When that branch
-- allocates its right cell, a private mapSpineNamesTargetOnly lemma transports
-- old name evidence with target-only-name-evolution; reveal/conceal child
-- spines get their new zero-name evidence from right-bind-new-target-only.
-- Target-all/keep simply preserves the evidence.
--
-- Pending cast/reveal/conceal normalization can return a target-only
-- MultiWorldEvolution.  Its recursive transport lemma is the list closure of
-- target-only-name-evolution.  Since the left StoreChanges index is [], only
-- reflexivity and right steps are possible, so no source allocation or
-- alignment case needs an assumed preservation theorem.
--
-- This changes only the private worker state and its constructors/helpers.
-- The three public catchup Def statements remain unchanged, as do CTI and the
-- public reduction/evolution relations.

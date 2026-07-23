module
  proof.Store.Correspondence.NuImprecisionStoreCorrespondenceDropLeftProof
  where

-- File Charter:
--   * Proves exact source-only correspondence removal by exhaustive recursion
--     on the store lift and correspondence membership.
--   * Retains explicit name and type equalities at the origin boundary so
--     constructor-form indices remain within Agda's unification fragment.
--   * Contains no term relation, postulate, hole, catch-all, permissive
--     option, termination bypass, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using
  (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; StoreCorresponds
  ; StoreImp
  ; correspondence-linked
  ; correspondence-stored
  ; lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; store-link
  ; store-matched
  )
open import Types using
  (Ty; TyCtx; TyVar; _[_]ᴿ; ⇑ᵗ)
open import
  proof.Store.Correspondence.NuImprecisionStoreCorrespondenceDropLeftDef
  using (StoreCorrespondenceDropLeftᵀ)
open import proof.Store.Correspondence.NuImprecisionStoreCorrespondenceLift using
  (store-corresponds-weaken)
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-single-suc-cancel)


left-correspondence-origin-exact :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp Ψ (suc Δᴸ) Δᴿ}
    {α′ β : TyVar} {A′ B : Ty} {p′} →
  LiftLeftStoreⁱ Ψ ρ ρᴸ →
  StoreCorresponds ρᴸ α′ A′ β B p′ →
  Σ[ α ∈ TyVar ]
  Σ[ A ∈ Ty ]
  ∃[ p ]
    (α′ ≡ suc α) ×
    (A′ ≡ ⇑ᵗ A) ×
    StoreCorresponds ρ α A β B p
left-correspondence-origin-exact
    lift-left-store-[] (correspondence-stored ())
left-correspondence-origin-exact
    lift-left-store-[] (correspondence-linked ())
left-correspondence-origin-exact
    {ρ = store-matched α A _ _ p ∷ ρ}
    (lift-left-store-∷ liftρ)
    (correspondence-stored (here refl)) =
  α , A , p , refl , refl , correspondence-stored (here refl)
left-correspondence-origin-exact
    (lift-left-store-∷ liftρ)
    (correspondence-stored (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-stored member)
left-correspondence-origin-exact
    (lift-left-store-∷ liftρ)
    (correspondence-stored (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    (lift-left-store-left liftρ)
    (correspondence-stored (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-stored member)
left-correspondence-origin-exact
    (lift-left-store-left liftρ)
    (correspondence-stored (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    (lift-left-store-right liftρ)
    (correspondence-stored (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-stored member)
left-correspondence-origin-exact
    (lift-left-store-right liftρ)
    (correspondence-stored (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    (lift-left-store-link liftρ)
    (correspondence-stored (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-stored member)
left-correspondence-origin-exact
    (lift-left-store-link liftρ)
    (correspondence-stored (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    (lift-left-store-∷ liftρ)
    (correspondence-linked (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-linked member)
left-correspondence-origin-exact
    (lift-left-store-∷ liftρ)
    (correspondence-linked (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    (lift-left-store-left liftρ)
    (correspondence-linked (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-linked member)
left-correspondence-origin-exact
    (lift-left-store-left liftρ)
    (correspondence-linked (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    (lift-left-store-right liftρ)
    (correspondence-linked (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-linked member)
left-correspondence-origin-exact
    (lift-left-store-right liftρ)
    (correspondence-linked (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr
left-correspondence-origin-exact
    {ρ = store-link α A _ _ p ∷ ρ}
    (lift-left-store-link liftρ)
    (correspondence-linked (here refl)) =
  α , A , p , refl , refl , correspondence-linked (here refl)
left-correspondence-origin-exact
    (lift-left-store-link liftρ)
    (correspondence-linked (there member))
    with left-correspondence-origin-exact
      liftρ (correspondence-linked member)
left-correspondence-origin-exact
    (lift-left-store-link liftρ)
    (correspondence-linked (there member))
    | α , A , p , eqα , eqA , corr =
  α , A , p , eqα , eqA , store-corresponds-weaken corr


raise-type-injective :
  ∀ {A B : Ty} → ⇑ᵗ A ≡ ⇑ᵗ B → A ≡ B
raise-type-injective {A = A} {B = B} eq =
  trans
    (sym (renameᵗ-single-suc-cancel zero A))
    (trans
      (cong (λ T → T [ zero ]ᴿ) eq)
      (renameᵗ-single-suc-cancel zero B))


store-correspondence-drop-left-proofᵀ :
  StoreCorrespondenceDropLeftᵀ
store-correspondence-drop-left-proofᵀ
    {α = α} {A = A} liftρ corr
    with left-correspondence-origin-exact liftρ corr
store-correspondence-drop-left-proofᵀ
    {α = α} {A = A} liftρ corr
    | α′ , A′ , p , eqα , eqA , corr′
    with suc-injective eqα | raise-type-injective eqA
store-correspondence-drop-left-proofᵀ
    {α = α} {A = A} liftρ corr
    | α′ , A′ , p , eqα , eqA , corr′
    | refl | refl =
  p , corr′

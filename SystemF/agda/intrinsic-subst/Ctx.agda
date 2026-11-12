module intrinsic-subst.Ctx where

-- File Charter:
--   * Term contexts of System F and their variables, from the library for
--     polymorphic languages (Subst/Poly.agda), instantiated with the types
--     of intrinsic-subst/Types.agda: a context `Ctx Δ` is a list of types
--     in `Δ` (`∅`, `Γ , A`), a variable `Γ ∋ A` is a typed de Bruijn index
--     (`Z`, `S x`), and `⇑ᶜ Γ` weakens the types of `Γ` past a new type
--     variable.
--   * Also re-exports the library's maps of term variables along a map of
--     types (`TyRen`, `extρ`, `⇑ρ`, `mapᶜ`, `mapᵛ`, `⇑ᵛ`, `instᵛ`), which
--     are used to rename and substitute the types of terms.

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import intrinsic-subst.Types
open import intrinsic-subst.proof.TypeSubst using (fuseᵗ; sub-idᵗ)

open import Subst.Scope public using (∅; _,_; _∋_; Z; S_)
open import Subst.Poly tyScope tt Typ `_ travᵗ (λ _ _ _ → refl) fuseᵗ sub-idᵗ
  public hiding (⇑ᵗ; _[_]ᵗ; module TL)

Ctx : TyCtx → Set
Ctx = Cx

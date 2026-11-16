module intrinsic-subst.TypeSubst where

-- File Charter:
--   * Public statements of the laws of type substitution that the
--     definitions of contexts and terms (Ctx.agda, Terms.agda) and of the
--     logical relation (Parametricity.agda) use in casts, so those
--     definitions can be audited from the top level alone.
--   * Each is a thin wrapper around its proof in proof/TypeSubst.agda.
--     Since a cast does not depend on which proof of an equation it uses,
--     the statements are all an auditor needs.
--   * The types of `Laws` and of the equations are from the library's
--     top-level Subst/Kit.agda.

open import Relation.Binary.PropositionalEquality using (_≡_)

open import intrinsic-subst.Types
import intrinsic-subst.proof.TypeSubst as P

-- what the kit of type variables satisfies
varLᵗ : TS.Laws TK.varK
varLᵗ = P.TL.varL

-- what the kit of types satisfies
tmLᵗ : TS.Laws TS.tmK
tmLᵗ = P.TL.tmL

-- instantiating a weakened type gives it back
⇑-[]ᵗ : ∀ {Δ s s'} (A : Typ Δ s) (B : Typ Δ s') → TS.⇑ A TS.[ B ] ≡ A
⇑-[]ᵗ = P.TL.⇑-[]

-- a type renaming or substitution commutes with instantiation
trav-[]ᵗ : ∀ {𝒦} → TS.Laws 𝒦
  → ∀ {Δ Δ'} (σ : TK.Sub 𝒦 Δ Δ') (A : Type (Δ ,α)) (B : Type Δ)
  → travᵗ 𝒦 σ (A [ B ]ᵗ) ≡ travᵗ 𝒦 (TK.exts 𝒦 σ) A [ travᵗ 𝒦 σ B ]ᵗ
trav-[]ᵗ L σ A B = P.TL.trav-[] L σ A B

-- a substitution under a binder, then instantiation, is one substitution
exts-[]ᵗ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (A : Type (Δ ,α)) (B : Type Δ')
  → substᵗ (extsᵗ σ) A [ B ]ᵗ ≡ substᵗ (B •ᵗ σ) A
exts-[]ᵗ σ A B = P.TL.exts-[] σ A B

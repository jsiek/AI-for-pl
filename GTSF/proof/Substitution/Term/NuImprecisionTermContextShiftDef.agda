module proof.Substitution.Term.NuImprecisionTermContextShiftDef where

-- File Charter:
--   * States weakening of no-bullet quotiented term imprecision by one fresh
--     term-context entry.
--   * Renames both terms with `suc` while leaving the relational type and
--     store worlds fixed.
--   * Isolates the exact support needed to extend parallel substitutions under
--     an ordinary lambda binder.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using (_∷_)
open import Data.Nat using (suc)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (CtxImp; StoreImp; ctx-imp)
open import NuTerms using (No•; Term; renameˣᵐ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)


QuotientedTermContextShiftᵀ : Set₁
QuotientedTermContextShiftᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B C C′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  No• M → No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp C C′ q ∷ γ
    ⊢ᴺ renameˣᵐ suc M ⊑ renameˣᵐ suc M′
    ⦂ A ⊑ B ∶ p

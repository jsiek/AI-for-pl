module LR-narrow.World where

-- File Charter:
--   * Adds mode-indexed semantic entries to a three-context GTSFImp world.
--   * Defines paired and either-sided future-world extensions.
--   * Lifts endpoint syntax and center imprecision through future worlds,
--     with structural and composition laws for the lifted syntax.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import TyStore using (store-empty)
open import CastTerms using (Term; renameᵗᵐ; ⇑ᵗᵐ; ƛ_; Λ_; _↓_)
open import Conversion using (seal)
open import Primitives using (Const; κℕ; κ𝔹; constTy)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; wk↪ᵗ; toRenameᵗ)
import Imprecision as I
open import proof.ImprecisionConsistency
  using (ext-injective; fin-suc-injective; rename-⊑; subst-⊑;
         subst₂-⊑; rename-occurs)
open import proof.TypeInTermSubst using
  (toRename-keep-eq; rename-openᵗ; renameᵗᵐ-preserves-Value;
   toRename-wk-eq; renameᵗ-wk-eq)
open import LR-narrow.WorldCore public
open import LR-narrow.Atoms public

record World (Δᴾ Δᴵ Δᶜ : TyCtx) : Set where
  constructor world
  field
    core : CoreWorld Δᴾ Δᴵ Δᶜ
    semanticEntry : (Z : TyVar Δᶜ)
      → SemanticEntry core Z (impEnv core Z)

open World public

emptyWorld : World 0 0 0
emptyWorld = world
  (core-world empty empty (λ ()) store-empty store-empty) (λ ())

pairedBindWorld : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → World (suc Δᴾ) (suc Δᴵ) (suc Δᶜ)
pairedBindWorld W Aᴾ Aᴵ r =
  world (pairedBindCore (core W) Aᴾ Aᴵ) atoms
  where
  atoms : (Z : TyVar _)
    → SemanticEntry (pairedBindCore (core W) Aᴾ Aᴵ) Z
        (impEnv (pairedBindCore (core W) Aᴾ Aᴵ) Z)
  atoms Fin.zero = paired-entry (fresh-semantic-atom (core W) Aᴾ Aᴵ r)
  atoms (Fin.suc Z) = weaken-entry Aᴾ Aᴵ (semanticEntry W Z)

preciseBindWorld : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (Aᴾ : Ty Δᴾ)
  → impEnv (core W) I.⊢ embedPrecise (core W) Aᴾ ⊑ ★
  → World (suc Δᴾ) Δᴵ (suc Δᶜ)
preciseBindWorld W Aᴾ r =
  world (preciseBindCore (core W) Aᴾ) atoms
  where
  atoms : (Z : TyVar _)
    → SemanticEntry (preciseBindCore (core W) Aᴾ) Z
        (impEnv (preciseBindCore (core W) Aᴾ) Z)
  atoms Fin.zero =
    dynamic-entry (fresh-dynamic-semantic-atom (core W) Aᴾ r)
  atoms (Fin.suc Z) = weaken-entry-precise Aᴾ (semanticEntry W Z)

impreciseBindWorld : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (Aᴵ : Ty Δᴵ)
  → World Δᴾ (suc Δᴵ) (suc Δᶜ)
impreciseBindWorld W Aᴵ =
  world (impreciseBindCore (core W) Aᴵ) atoms
  where
  atoms : (Z : TyVar _)
    → SemanticEntry (impreciseBindCore (core W) Aᴵ) Z
        (impEnv (impreciseBindCore (core W) Aᴵ) Z)
  atoms Fin.zero = target-entry (fresh-target-semantic-atom Aᴵ)
  atoms (Fin.suc Z) = weaken-entry-imprecise Aᴵ (semanticEntry W Z)

data Future {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
    → World Δᴾ′ Δᴵ′ Δᶜ′
    → Set where
  future-refl : Future W W

  future-paired : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Aᴾ : Ty Δᴾ′} {Aᴵ : Ty Δᴵ′}
    → Future W W′
    → (r : Aᴾ ⊑ᵂ⟨ core W′ ⟩ Aᴵ)
    → Future W (pairedBindWorld W′ Aᴾ Aᴵ r)

  future-precise : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {Aᴾ : Ty Δᴾ′}
    → Future W W′
    → (r : impEnv (core W′) I.⊢ embedPrecise (core W′) Aᴾ ⊑ ★)
    → Future W (preciseBindWorld W′ Aᴾ r)

  future-imprecise : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {Aᴵ : Ty Δᴵ′}
    → Future W W′
    → Future W (impreciseBindWorld W′ Aᴵ)

future-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
  → Future W₀ W₁
  → Future W₁ W₂
  → Future W₀ W₂
future-trans W₀≼W₁ future-refl = W₀≼W₁
future-trans W₀≼W₁ (future-paired W₁≼W₂ related) =
  future-paired (future-trans W₀≼W₁ W₁≼W₂) related
future-trans W₀≼W₁ (future-precise W₁≼W₂ related) =
  future-precise (future-trans W₀≼W₁ W₁≼W₂) related
future-trans W₀≼W₁ (future-imprecise W₁≼W₂) =
  future-imprecise (future-trans W₀≼W₁ W₁≼W₂)

liftPreciseTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴾ
  → Ty Δᴾ′
liftPreciseTy future-refl A = A
liftPreciseTy (future-paired W≼W′ related) A =
  ⇑ᵗ (liftPreciseTy W≼W′ A)
liftPreciseTy (future-precise W≼W′ related) A =
  ⇑ᵗ (liftPreciseTy W≼W′ A)
liftPreciseTy (future-imprecise W≼W′) A = liftPreciseTy W≼W′ A

liftImpreciseTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴵ
  → Ty Δᴵ′
liftImpreciseTy future-refl A = A
liftImpreciseTy (future-paired W≼W′ related) A =
  ⇑ᵗ (liftImpreciseTy W≼W′ A)
liftImpreciseTy (future-precise W≼W′ related) A =
  liftImpreciseTy W≼W′ A
liftImpreciseTy (future-imprecise W≼W′) A =
  ⇑ᵗ (liftImpreciseTy W≼W′ A)

liftCenterTy : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᶜ
  → Ty Δᶜ′
liftCenterTy future-refl A = A
liftCenterTy (future-paired W≼W′ related) A =
  ⇑ᵗ (liftCenterTy W≼W′ A)
liftCenterTy (future-precise W≼W′ related) A =
  ⇑ᵗ (liftCenterTy W≼W′ A)
liftCenterTy (future-imprecise W≼W′) A =
  ⇑ᵗ (liftCenterTy W≼W′ A)

liftCenterVariable : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TyVar Δᶜ
  → TyVar Δᶜ′
liftCenterVariable future-refl X = X
liftCenterVariable (future-paired W≼W′ related) X =
  Fin.suc (liftCenterVariable W≼W′ X)
liftCenterVariable (future-precise W≼W′ related) X =
  Fin.suc (liftCenterVariable W≼W′ X)
liftCenterVariable (future-imprecise W≼W′) X =
  Fin.suc (liftCenterVariable W≼W′ X)

liftCenterTy-variable : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᶜ)
  → liftCenterTy W≼W′ (＇ X) ≡ ＇ liftCenterVariable W≼W′ X
liftCenterTy-variable future-refl X = refl
liftCenterTy-variable (future-paired W≼W′ related) X =
  cong ⇑ᵗ (liftCenterTy-variable W≼W′ X)
liftCenterTy-variable (future-precise W≼W′ related) X =
  cong ⇑ᵗ (liftCenterTy-variable W≼W′ X)
liftCenterTy-variable (future-imprecise W≼W′) X =
  cong ⇑ᵗ (liftCenterTy-variable W≼W′ X)

liftCenterMode : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᶜ)
  → impEnv (core W′) (liftCenterVariable W≼W′ X)
      ≡ impEnv (core W) X
liftCenterMode future-refl X = refl
liftCenterMode (future-paired W≼W′ related) X =
  liftCenterMode W≼W′ X
liftCenterMode (future-precise W≼W′ related) X =
  liftCenterMode W≼W′ X
liftCenterMode (future-imprecise W≼W′) X = liftCenterMode W≼W′ X

liftPreciseTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term Δᴾ
  → Term Δᴾ′
liftPreciseTerm future-refl M = M
liftPreciseTerm (future-paired W≼W′ related) M =
  ⇑ᵗᵐ (liftPreciseTerm W≼W′ M)
liftPreciseTerm (future-precise W≼W′ related) M =
  ⇑ᵗᵐ (liftPreciseTerm W≼W′ M)
liftPreciseTerm (future-imprecise W≼W′) M = liftPreciseTerm W≼W′ M

liftImpreciseTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term Δᴵ
  → Term Δᴵ′
liftImpreciseTerm future-refl M = M
liftImpreciseTerm (future-paired W≼W′ related) M =
  ⇑ᵗᵐ (liftImpreciseTerm W≼W′ M)
liftImpreciseTerm (future-precise W≼W′ related) M =
  liftImpreciseTerm W≼W′ M
liftImpreciseTerm (future-imprecise W≼W′) M =
  ⇑ᵗᵐ (liftImpreciseTerm W≼W′ M)

liftPreciseBodyTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term (suc Δᴾ)
  → Term (suc Δᴾ′)
liftPreciseBodyTerm future-refl M = M
liftPreciseBodyTerm (future-paired W≼W′ related) M =
  renameᵗᵐ (keep wk↪ᵗ) (liftPreciseBodyTerm W≼W′ M)
liftPreciseBodyTerm (future-precise W≼W′ related) M =
  renameᵗᵐ (keep wk↪ᵗ) (liftPreciseBodyTerm W≼W′ M)
liftPreciseBodyTerm (future-imprecise W≼W′) M =
  liftPreciseBodyTerm W≼W′ M

liftImpreciseBodyTerm : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Term (suc Δᴵ)
  → Term (suc Δᴵ′)
liftImpreciseBodyTerm future-refl M = M
liftImpreciseBodyTerm (future-paired W≼W′ related) M =
  renameᵗᵐ (keep wk↪ᵗ) (liftImpreciseBodyTerm W≼W′ M)
liftImpreciseBodyTerm (future-precise W≼W′ related) M =
  liftImpreciseBodyTerm W≼W′ M
liftImpreciseBodyTerm (future-imprecise W≼W′) M =
  renameᵗᵐ (keep wk↪ᵗ) (liftImpreciseBodyTerm W≼W′ M)

liftPreciseTerm-universal : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) N
  → liftPreciseTerm W≼W′ (Λ N) ≡ Λ (liftPreciseBodyTerm W≼W′ N)
liftPreciseTerm-universal future-refl N = refl
liftPreciseTerm-universal (future-paired W≼W′ related) N
    rewrite liftPreciseTerm-universal W≼W′ N = refl
liftPreciseTerm-universal (future-precise W≼W′ related) N
    rewrite liftPreciseTerm-universal W≼W′ N = refl
liftPreciseTerm-universal (future-imprecise W≼W′) N =
  liftPreciseTerm-universal W≼W′ N

liftImpreciseTerm-universal : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) N
  → liftImpreciseTerm W≼W′ (Λ N) ≡
      Λ (liftImpreciseBodyTerm W≼W′ N)
liftImpreciseTerm-universal future-refl N = refl
liftImpreciseTerm-universal (future-paired W≼W′ related) N
    rewrite liftImpreciseTerm-universal W≼W′ N = refl
liftImpreciseTerm-universal (future-precise W≼W′ related) N =
  liftImpreciseTerm-universal W≼W′ N
liftImpreciseTerm-universal (future-imprecise W≼W′) N
    rewrite liftImpreciseTerm-universal W≼W′ N = refl

liftPreciseBodyTerm-value : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {V : Term (suc Δᴾ)}
  → CastTerms.Value V
  → CastTerms.Value (liftPreciseBodyTerm W≼W′ V)
liftPreciseBodyTerm-value future-refl vV = vV
liftPreciseBodyTerm-value (future-paired W≼W′ related) vV =
  renameᵗᵐ-preserves-Value (keep wk↪ᵗ)
    (liftPreciseBodyTerm-value W≼W′ vV)
liftPreciseBodyTerm-value (future-precise W≼W′ related) vV =
  renameᵗᵐ-preserves-Value (keep wk↪ᵗ)
    (liftPreciseBodyTerm-value W≼W′ vV)
liftPreciseBodyTerm-value (future-imprecise W≼W′) vV =
  liftPreciseBodyTerm-value W≼W′ vV

liftImpreciseBodyTerm-value : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {V : Term (suc Δᴵ)}
  → CastTerms.Value V
  → CastTerms.Value (liftImpreciseBodyTerm W≼W′ V)
liftImpreciseBodyTerm-value future-refl vV = vV
liftImpreciseBodyTerm-value (future-paired W≼W′ related) vV =
  renameᵗᵐ-preserves-Value (keep wk↪ᵗ)
    (liftImpreciseBodyTerm-value W≼W′ vV)
liftImpreciseBodyTerm-value (future-precise W≼W′ related) vV =
  liftImpreciseBodyTerm-value W≼W′ vV
liftImpreciseBodyTerm-value (future-imprecise W≼W′) vV =
  renameᵗᵐ-preserves-Value (keep wk↪ᵗ)
    (liftImpreciseBodyTerm-value W≼W′ vV)

liftPreciseTerm-lambda : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) N
  → liftPreciseTerm W≼W′ (ƛ N) ≡ ƛ liftPreciseTerm W≼W′ N
liftPreciseTerm-lambda future-refl N = refl
liftPreciseTerm-lambda (future-paired W≼W′ related) N
    rewrite liftPreciseTerm-lambda W≼W′ N = refl
liftPreciseTerm-lambda (future-precise W≼W′ related) N
    rewrite liftPreciseTerm-lambda W≼W′ N = refl
liftPreciseTerm-lambda (future-imprecise W≼W′) N =
  liftPreciseTerm-lambda W≼W′ N

liftImpreciseTerm-lambda : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) N
  → liftImpreciseTerm W≼W′ (ƛ N) ≡ ƛ liftImpreciseTerm W≼W′ N
liftImpreciseTerm-lambda future-refl N = refl
liftImpreciseTerm-lambda (future-paired W≼W′ related) N
    rewrite liftImpreciseTerm-lambda W≼W′ N = refl
liftImpreciseTerm-lambda (future-precise W≼W′ related) N =
  liftImpreciseTerm-lambda W≼W′ N
liftImpreciseTerm-lambda (future-imprecise W≼W′) N
    rewrite liftImpreciseTerm-lambda W≼W′ N = refl

liftPreciseTerm-variable : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) x
  → liftPreciseTerm W≼W′ (CastTerms.` x) ≡ CastTerms.` x
liftPreciseTerm-variable future-refl x = refl
liftPreciseTerm-variable (future-paired W≼W′ related) x
    rewrite liftPreciseTerm-variable W≼W′ x = refl
liftPreciseTerm-variable (future-precise W≼W′ related) x
    rewrite liftPreciseTerm-variable W≼W′ x = refl
liftPreciseTerm-variable (future-imprecise W≼W′) x =
  liftPreciseTerm-variable W≼W′ x

liftImpreciseTerm-variable : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) x
  → liftImpreciseTerm W≼W′ (CastTerms.` x) ≡ CastTerms.` x
liftImpreciseTerm-variable future-refl x = refl
liftImpreciseTerm-variable (future-paired W≼W′ related) x
    rewrite liftImpreciseTerm-variable W≼W′ x = refl
liftImpreciseTerm-variable (future-precise W≼W′ related) x =
  liftImpreciseTerm-variable W≼W′ x
liftImpreciseTerm-variable (future-imprecise W≼W′) x
    rewrite liftImpreciseTerm-variable W≼W′ x = refl

liftPreciseTerm-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftPreciseTerm W≼W′ (CastTerms.$ κ) ≡ CastTerms.$ κ
liftPreciseTerm-constant future-refl κ = refl
liftPreciseTerm-constant (future-paired W≼W′ related) κ
    rewrite liftPreciseTerm-constant W≼W′ κ = refl
liftPreciseTerm-constant (future-precise W≼W′ related) κ
    rewrite liftPreciseTerm-constant W≼W′ κ = refl
liftPreciseTerm-constant (future-imprecise W≼W′) κ =
  liftPreciseTerm-constant W≼W′ κ

liftImpreciseTerm-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftImpreciseTerm W≼W′ (CastTerms.$ κ) ≡ CastTerms.$ κ
liftImpreciseTerm-constant future-refl κ = refl
liftImpreciseTerm-constant (future-paired W≼W′ related) κ
    rewrite liftImpreciseTerm-constant W≼W′ κ = refl
liftImpreciseTerm-constant (future-precise W≼W′ related) κ =
  liftImpreciseTerm-constant W≼W′ κ
liftImpreciseTerm-constant (future-imprecise W≼W′) κ
    rewrite liftImpreciseTerm-constant W≼W′ κ = refl

liftPreciseTy-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (κ : Const)
  → liftPreciseTy W≼W′ (constTy κ) ≡ constTy κ
liftPreciseTy-constant future-refl κ = refl
liftPreciseTy-constant (future-paired W≼W′ related) (κℕ n)
    rewrite liftPreciseTy-constant W≼W′ (κℕ n) = refl
liftPreciseTy-constant (future-paired W≼W′ related) (κ𝔹 b)
    rewrite liftPreciseTy-constant W≼W′ (κ𝔹 b) = refl
liftPreciseTy-constant (future-precise W≼W′ related) (κℕ n)
    rewrite liftPreciseTy-constant W≼W′ (κℕ n) = refl
liftPreciseTy-constant (future-precise W≼W′ related) (κ𝔹 b)
    rewrite liftPreciseTy-constant W≼W′ (κ𝔹 b) = refl
liftPreciseTy-constant (future-imprecise W≼W′) κ =
  liftPreciseTy-constant W≼W′ κ

liftImpreciseTy-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (κ : Const)
  → liftImpreciseTy W≼W′ (constTy κ) ≡ constTy κ
liftImpreciseTy-constant future-refl κ = refl
liftImpreciseTy-constant (future-paired W≼W′ related) (κℕ n)
    rewrite liftImpreciseTy-constant W≼W′ (κℕ n) = refl
liftImpreciseTy-constant (future-paired W≼W′ related) (κ𝔹 b)
    rewrite liftImpreciseTy-constant W≼W′ (κ𝔹 b) = refl
liftImpreciseTy-constant (future-precise W≼W′ related) κ =
  liftImpreciseTy-constant W≼W′ κ
liftImpreciseTy-constant (future-imprecise W≼W′) (κℕ n)
    rewrite liftImpreciseTy-constant W≼W′ (κℕ n) = refl
liftImpreciseTy-constant (future-imprecise W≼W′) (κ𝔹 b)
    rewrite liftImpreciseTy-constant W≼W′ (κ𝔹 b) = refl

liftCenterTy-constant : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (κ : Const)
  → liftCenterTy W≼W′ (constTy κ) ≡ constTy κ
liftCenterTy-constant future-refl κ = refl
liftCenterTy-constant (future-paired W≼W′ related) (κℕ n)
    rewrite liftCenterTy-constant W≼W′ (κℕ n) = refl
liftCenterTy-constant (future-paired W≼W′ related) (κ𝔹 b)
    rewrite liftCenterTy-constant W≼W′ (κ𝔹 b) = refl
liftCenterTy-constant (future-precise W≼W′ related) (κℕ n)
    rewrite liftCenterTy-constant W≼W′ (κℕ n) = refl
liftCenterTy-constant (future-precise W≼W′ related) (κ𝔹 b)
    rewrite liftCenterTy-constant W≼W′ (κ𝔹 b) = refl
liftCenterTy-constant (future-imprecise W≼W′) (κℕ n)
    rewrite liftCenterTy-constant W≼W′ (κℕ n) = refl
liftCenterTy-constant (future-imprecise W≼W′) (κ𝔹 b)
    rewrite liftCenterTy-constant W≼W′ (κ𝔹 b) = refl

liftCenterTy-star : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → liftCenterTy W≼W′ ★ ≡ ★
liftCenterTy-star future-refl = refl
liftCenterTy-star (future-paired W≼W′ related)
    rewrite liftCenterTy-star W≼W′ = refl
liftCenterTy-star (future-precise W≼W′ related)
    rewrite liftCenterTy-star W≼W′ = refl
liftCenterTy-star (future-imprecise W≼W′)
    rewrite liftCenterTy-star W≼W′ = refl

liftCenterTy-arrow : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A B : Ty Δᶜ)
  → liftCenterTy W≼W′ (A ⇒ B) ≡
      (liftCenterTy W≼W′ A ⇒ liftCenterTy W≼W′ B)
liftCenterTy-arrow future-refl A B = refl
liftCenterTy-arrow (future-paired W≼W′ related) A B
    rewrite liftCenterTy-arrow W≼W′ A B = refl
liftCenterTy-arrow (future-precise W≼W′ related) A B
    rewrite liftCenterTy-arrow W≼W′ A B = refl
liftCenterTy-arrow (future-imprecise W≼W′) A B
    rewrite liftCenterTy-arrow W≼W′ A B = refl

liftPreciseBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᴾ)
  → Ty (suc Δᴾ′)
liftPreciseBody future-refl A = A
liftPreciseBody (future-paired W≼W′ related) A =
  renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ A)
liftPreciseBody (future-precise W≼W′ related) A =
  renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ A)
liftPreciseBody (future-imprecise W≼W′) A = liftPreciseBody W≼W′ A

liftImpreciseBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᴵ)
  → Ty (suc Δᴵ′)
liftImpreciseBody future-refl A = A
liftImpreciseBody (future-paired W≼W′ related) A =
  renameᵗ (extᵗ Fin.suc) (liftImpreciseBody W≼W′ A)
liftImpreciseBody (future-precise W≼W′ related) A =
  liftImpreciseBody W≼W′ A
liftImpreciseBody (future-imprecise W≼W′) A =
  renameᵗ (extᵗ Fin.suc) (liftImpreciseBody W≼W′ A)

liftCenterBody : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty (suc Δᶜ)
  → Ty (suc Δᶜ′)
liftCenterBody future-refl A = A
liftCenterBody (future-paired W≼W′ related) A =
  renameᵗ (extᵗ Fin.suc) (liftCenterBody W≼W′ A)
liftCenterBody (future-precise W≼W′ related) A =
  renameᵗ (extᵗ Fin.suc) (liftCenterBody W≼W′ A)
liftCenterBody (future-imprecise W≼W′) A =
  renameᵗ (extᵗ Fin.suc) (liftCenterBody W≼W′ A)

liftCenterBody-shift : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (A : Ty Δᶜ₀)
  → liftCenterBody W₀≼W₁ (⇑ᵗ A)
      ≡ ⇑ᵗ (liftCenterTy W₀≼W₁ A)
liftCenterBody-shift future-refl A = refl
liftCenterBody-shift (future-paired W₀≼W₁ related) A =
  trans (cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-shift W₀≼W₁ A))
    (renameᵗ-shift Fin.suc (liftCenterTy W₀≼W₁ A))
liftCenterBody-shift (future-precise W₀≼W₁ related) A =
  trans (cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-shift W₀≼W₁ A))
    (renameᵗ-shift Fin.suc (liftCenterTy W₀≼W₁ A))
liftCenterBody-shift (future-imprecise W₀≼W₁) A =
  trans (cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-shift W₀≼W₁ A))
    (renameᵗ-shift Fin.suc (liftCenterTy W₀≼W₁ A))

liftCenterBody-nonvar : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {A : Ty (suc Δᶜ₀)}
  → (W₀≼W₁ : Future W₀ W₁)
  → NonVar A
  → NonVar (liftCenterBody W₀≼W₁ A)
liftCenterBody-nonvar future-refl nonvar = nonvar
liftCenterBody-nonvar (future-paired W₀≼W₁ related) nonvar =
  renameNonVar (extᵗ Fin.suc) (liftCenterBody-nonvar W₀≼W₁ nonvar)
liftCenterBody-nonvar (future-precise W₀≼W₁ related) nonvar =
  renameNonVar (extᵗ Fin.suc) (liftCenterBody-nonvar W₀≼W₁ nonvar)
liftCenterBody-nonvar (future-imprecise W₀≼W₁) nonvar =
  renameNonVar (extᵗ Fin.suc) (liftCenterBody-nonvar W₀≼W₁ nonvar)

liftCenterBody-occurs : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {A : Ty (suc Δᶜ₀)}
  → (W₀≼W₁ : Future W₀ W₁)
  → Fin.zero ∈ᵗ A
  → Fin.zero ∈ᵗ liftCenterBody W₀≼W₁ A
liftCenterBody-occurs future-refl occurs = occurs
liftCenterBody-occurs (future-paired W₀≼W₁ related) occurs =
  rename-occurs (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (liftCenterBody-occurs W₀≼W₁ occurs)
liftCenterBody-occurs (future-precise W₀≼W₁ related) occurs =
  rename-occurs (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (liftCenterBody-occurs W₀≼W₁ occurs)
liftCenterBody-occurs (future-imprecise W₀≼W₁) occurs =
  rename-occurs (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (liftCenterBody-occurs W₀≼W₁ occurs)

liftPreciseTy-universal : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) A
  → liftPreciseTy W≼W′ (`∀ A) ≡ `∀ (liftPreciseBody W≼W′ A)
liftPreciseTy-universal future-refl A = refl
liftPreciseTy-universal (future-paired W≼W′ related) A
    rewrite liftPreciseTy-universal W≼W′ A = refl
liftPreciseTy-universal (future-precise W≼W′ related) A
    rewrite liftPreciseTy-universal W≼W′ A = refl
liftPreciseTy-universal (future-imprecise W≼W′) A =
  liftPreciseTy-universal W≼W′ A

liftImpreciseTy-universal : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) A
  → liftImpreciseTy W≼W′ (`∀ A) ≡ `∀ (liftImpreciseBody W≼W′ A)
liftImpreciseTy-universal future-refl A = refl
liftImpreciseTy-universal (future-paired W≼W′ related) A
    rewrite liftImpreciseTy-universal W≼W′ A = refl
liftImpreciseTy-universal (future-precise W≼W′ related) A =
  liftImpreciseTy-universal W≼W′ A
liftImpreciseTy-universal (future-imprecise W≼W′) A
    rewrite liftImpreciseTy-universal W≼W′ A = refl

liftCenterTy-universal : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) A
  → liftCenterTy W≼W′ (`∀ A) ≡ `∀ (liftCenterBody W≼W′ A)
liftCenterTy-universal future-refl A = refl
liftCenterTy-universal (future-paired W≼W′ related) A
    rewrite liftCenterTy-universal W≼W′ A = refl
liftCenterTy-universal (future-precise W≼W′ related) A
    rewrite liftCenterTy-universal W≼W′ A = refl
liftCenterTy-universal (future-imprecise W≼W′) A
    rewrite liftCenterTy-universal W≼W′ A = refl

liftCenterImprecision : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty Δᶜ}
  → (W≼W′ : Future W W′)
  → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W′) I.⊢ liftCenterTy W≼W′ Aᴾ
      ⊑ liftCenterTy W≼W′ Aᴵ
liftCenterImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftCenterImprecision (future-paired W≼W′ related) Aᴾ⊑Aᴵ =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)
    (liftCenterImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterImprecision (future-precise W≼W′ related) Aᴾ⊑Aᴵ =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)
    (liftCenterImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterImprecision (future-imprecise W≼W′) Aᴾ⊑Aᴵ =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)
    (liftCenterImprecision W≼W′ Aᴾ⊑Aᴵ)

liftCenterBodyImprecision :
    ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Aᴾ Aᴵ : Ty (suc Δᶜ)}
  → (W≼W′ : Future W W′)
  → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → I.extᵐ (impEnv (core W′)) I.⊢ liftCenterBody W≼W′ Aᴾ
      ⊑ liftCenterBody W≼W′ Aᴵ
liftCenterBodyImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftCenterBodyImprecision
    (future-paired W≼W′ related) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero () ; (Fin.suc X) eq → eq })
    (liftCenterBodyImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterBodyImprecision (future-precise W≼W′ related) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero () ; (Fin.suc X) eq → eq })
    (liftCenterBodyImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterBodyImprecision (future-imprecise W≼W′) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero () ; (Fin.suc X) eq → eq })
    (liftCenterBodyImprecision W≼W′ Aᴾ⊑Aᴵ)

liftCenterDynamicBodyImprecision :
    ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Aᴾ Aᴵ : Ty (suc Δᶜ)}
  → (W≼W′ : Future W W′)
  → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → I.instᵐ (impEnv (core W′)) I.⊢ liftCenterBody W≼W′ Aᴾ
      ⊑ liftCenterBody W≼W′ Aᴵ
liftCenterDynamicBodyImprecision future-refl Aᴾ⊑Aᴵ = Aᴾ⊑Aᴵ
liftCenterDynamicBodyImprecision
    (future-paired W≼W′ related) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero eq → eq ; (Fin.suc X) eq → eq })
    (liftCenterDynamicBodyImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterDynamicBodyImprecision
    (future-precise W≼W′ related) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero eq → eq ; (Fin.suc X) eq → eq })
    (liftCenterDynamicBodyImprecision W≼W′ Aᴾ⊑Aᴵ)
liftCenterDynamicBodyImprecision
    (future-imprecise W≼W′) Aᴾ⊑Aᴵ =
  rename-⊑ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (λ { Fin.zero eq → eq ; (Fin.suc X) eq → eq })
    (liftCenterDynamicBodyImprecision W≼W′ Aᴾ⊑Aᴵ)

openFreshImprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ (suc Δᶜ)} {Aᴾ Aᴵ : Ty (suc (suc Δᶜ))}
  → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W) I.⊢ Aᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ Aᴵ [ ＇ Fin.zero ]ᵗ
openFreshImprecision Aᴾ⊑Aᴵ =
  subst-⊑ (λ { Fin.zero () ; (Fin.suc X) eq → I.X⊑★ eq }) Aᴾ⊑Aᴵ

openRelatedBodyImprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
  → I.extᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) Aᴾ
      ⊑ renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W)))) Aᴵ
  → Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ
  → Aᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Aᴵ [ Rᴵ ]ᵗ
openRelatedBodyImprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} body-related argument-related =
  subst (λ L → impEnv (core W) I.⊢ L ⊑ right)
    (sym (rename-openᵗ (toRenameᵗ (preciseEmbedding (core W))) Aᴾ Rᴾ))
    (subst (λ R → impEnv (core W) I.⊢ opened-left ⊑ R)
      (sym (rename-openᵗ
        (toRenameᵗ (impreciseEmbedding (core W))) Aᴵ Rᴵ))
      (subst₂-⊑ same star body-related))
  where
  opened-left = renameᵗ (extᵗ
    (toRenameᵗ (preciseEmbedding (core W)))) Aᴾ
    [ embedPrecise (core W) Rᴾ ]ᵗ

  right = embedImprecise (core W) (Aᴵ [ Rᴵ ]ᵗ)

  same : ∀ X → impEnv (core W) I.⊢
      singleSubᵗ (embedPrecise (core W) Rᴾ) X
      ⊑ singleSubᵗ (embedImprecise (core W) Rᴵ) X
  same Fin.zero = argument-related
  same (Fin.suc X) = I.X⊑X

  star : ∀ X → I.extᵐ (impEnv (core W)) X ≡ I.X⊑★
    → impEnv (core W) I.⊢
        singleSubᵗ (embedPrecise (core W) Rᴾ) X ⊑ ★
  star Fin.zero ()
  star (Fin.suc X) eq = I.X⊑★ eq

openFreshDynamicImprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ (suc Δᶜ)} {Aᴾ Aᴵ : Ty (suc (suc Δᶜ))}
  → impEnv (core W) Fin.zero ≡ I.X⊑★
  → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
  → impEnv (core W) I.⊢ Aᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ Aᴵ [ ＇ Fin.zero ]ᵗ
openFreshDynamicImprecision fresh-mode Aᴾ⊑Aᴵ =
  subst-⊑
    (λ { Fin.zero eq → I.X⊑★ fresh-mode
       ; (Fin.suc X) eq → I.X⊑★ eq })
    Aᴾ⊑Aᴵ

embed-keep-shift : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
embed-keep-shift η A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
    (renameᵗ-shift (toRenameᵗ η) A)

renameᵗ-skip-eq : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (skip η)) A
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
renameᵗ-skip-eq η A =
  trans (renameᵗ-cong A (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc A))

embedPrecise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A : Ty Δᴾ)
  → embedPrecise (core W′) (liftPreciseTy W≼W′ A)
      ≡ liftCenterTy W≼W′ (embedPrecise (core W) A)
embedPrecise-lift future-refl A = refl
embedPrecise-lift
    (future-paired {W′ = W′} W≼W′ related) A =
  trans (embed-keep-shift (preciseEmbedding (core W′))
      (liftPreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedPrecise-lift W≼W′ A))
embedPrecise-lift
    (future-precise {W′ = W′} W≼W′ related) A =
  trans (embed-keep-shift (preciseEmbedding (core W′))
      (liftPreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedPrecise-lift W≼W′ A))
embedPrecise-lift
    (future-imprecise {W′ = W′} W≼W′) A =
  trans (renameᵗ-skip-eq (preciseEmbedding (core W′))
      (liftPreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedPrecise-lift W≼W′ A))

embedImprecise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (A : Ty Δᴵ)
  → embedImprecise (core W′) (liftImpreciseTy W≼W′ A)
      ≡ liftCenterTy W≼W′ (embedImprecise (core W) A)
embedImprecise-lift future-refl A = refl
embedImprecise-lift
    (future-paired {W′ = W′} W≼W′ related) A =
  trans (embed-keep-shift (impreciseEmbedding (core W′))
      (liftImpreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedImprecise-lift W≼W′ A))

embedImprecise-lift
    (future-precise {W′ = W′} W≼W′ related) A =
  trans (renameᵗ-skip-eq (impreciseEmbedding (core W′))
      (liftImpreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedImprecise-lift W≼W′ A))
embedImprecise-lift
    (future-imprecise {W′ = W′} W≼W′) A =
  trans (embed-keep-shift (impreciseEmbedding (core W′))
      (liftImpreciseTy W≼W′ A))
    (cong ⇑ᵗ (embedImprecise-lift W≼W′ A))

paired-local-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {Bᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
    (r : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → ⇑ᵗ Aᴾ
      ⊑ᵂ⟨ core (pairedBindWorld W Bᴾ Bᴵ r) ⟩ ⇑ᵗ Aᴵ
paired-local-imprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} r p =
  subst
    (λ L → impEnv (pairedBindCore (core W) Bᴾ Bᴵ) I.⊢ L ⊑
      embedImprecise (pairedBindCore (core W) Bᴾ Bᴵ) (⇑ᵗ Aᴵ))
    (sym (embed-keep-shift (preciseEmbedding (core W)) Aᴾ))
    (subst
      (λ R → impEnv (pairedBindCore (core W) Bᴾ Bᴵ) I.⊢
        ⇑ᵗ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (embed-keep-shift (impreciseEmbedding (core W)) Aᴵ))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))

precise-local-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {Bᴾ : Ty Δᴾ}
    (r : impEnv (core W) I.⊢ embedPrecise (core W) Bᴾ ⊑ ★)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → ⇑ᵗ Aᴾ ⊑ᵂ⟨ core (preciseBindWorld W Bᴾ r) ⟩ Aᴵ
precise-local-imprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} r p =
  subst
    (λ L → impEnv (preciseBindCore (core W) Bᴾ) I.⊢ L ⊑
      embedImprecise (preciseBindCore (core W) Bᴾ) Aᴵ)
    (sym (embed-keep-shift (preciseEmbedding (core W)) Aᴾ))
    (subst
      (λ R → impEnv (preciseBindCore (core W) Bᴾ) I.⊢
        ⇑ᵗ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (renameᵗ-skip-eq (impreciseEmbedding (core W)) Aᴵ))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))

imprecise-local-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Aᴾ : Ty Δᴾ} {Aᴵ Bᴵ : Ty Δᴵ}
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → Aᴾ ⊑ᵂ⟨ core (impreciseBindWorld W Bᴵ) ⟩ ⇑ᵗ Aᴵ
imprecise-local-imprecision {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴵ = Bᴵ} p =
  subst
    (λ L → impEnv (impreciseBindCore (core W) Bᴵ) I.⊢ L ⊑
      embedImprecise (impreciseBindCore (core W) Bᴵ) (⇑ᵗ Aᴵ))
    (sym (renameᵗ-skip-eq (preciseEmbedding (core W)) Aᴾ))
    (subst
      (λ R → impEnv (impreciseBindCore (core W) Bᴵ) I.⊢
        ⇑ᵗ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (embed-keep-shift (impreciseEmbedding (core W)) Aᴵ))
      (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p))

liftLocalImprecision : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → (W≼W′ : Future W W′)
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → liftPreciseTy W≼W′ Aᴾ ⊑ᵂ⟨ core W′ ⟩
      liftImpreciseTy W≼W′ Aᴵ
liftLocalImprecision future-refl p = p
liftLocalImprecision
    (future-paired {W′ = W′} {Aᴾ = Bᴾ} {Aᴵ = Bᴵ}
      W≼W′ related) p =
  paired-local-imprecision {W = W′}
    {Aᴾ = liftPreciseTy W≼W′ _} {Aᴵ = liftImpreciseTy W≼W′ _}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} related (liftLocalImprecision W≼W′ p)
liftLocalImprecision
    (future-precise {W′ = W′} {Aᴾ = Bᴾ} W≼W′ related) p =
  precise-local-imprecision {W = W′}
    {Aᴾ = liftPreciseTy W≼W′ _} {Aᴵ = liftImpreciseTy W≼W′ _}
    {Bᴾ = Bᴾ} related (liftLocalImprecision W≼W′ p)
liftLocalImprecision
    (future-imprecise {W′ = W′} {Aᴵ = Bᴵ} W≼W′) p =
  imprecise-local-imprecision {W = W′}
    {Aᴾ = liftPreciseTy W≼W′ _} {Aᴵ = liftImpreciseTy W≼W′ _}
    {Bᴵ = Bᴵ} (liftLocalImprecision W≼W′ p)

liftImpreciseTy-star : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → liftImpreciseTy W≼W′ ★ ≡ ★
liftImpreciseTy-star future-refl = refl
liftImpreciseTy-star (future-paired W≼W′ related)
    rewrite liftImpreciseTy-star W≼W′ = refl
liftImpreciseTy-star (future-precise W≼W′ related) =
  liftImpreciseTy-star W≼W′
liftImpreciseTy-star (future-imprecise W≼W′)
    rewrite liftImpreciseTy-star W≼W′ = refl

-- Imprecision below ★ lifts through futures on the precise side.

liftStarImprecision : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ : Ty Δᴾ}
  → (W≼W′ : Future W W′)
  → impEnv (core W) I.⊢ embedPrecise (core W) Aᴾ ⊑ ★
  → impEnv (core W′) I.⊢
      embedPrecise (core W′) (liftPreciseTy W≼W′ Aᴾ) ⊑ ★
liftStarImprecision {W′ = W′} {Aᴾ = Aᴾ} W≼W′ p =
  subst (λ T → impEnv (core W′) I.⊢
      embedPrecise (core W′) (liftPreciseTy W≼W′ Aᴾ)
        ⊑ embedImprecise (core W′) T)
    (liftImpreciseTy-star W≼W′)
    (liftLocalImprecision W≼W′ p)


liftCenterVariable-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (X : TyVar Δᶜ₀)
  → liftCenterVariable (future-trans W₀≼W₁ W₁≼W₂) X
      ≡ liftCenterVariable W₁≼W₂ (liftCenterVariable W₀≼W₁ X)
liftCenterVariable-trans W₀≼W₁ future-refl X = refl
liftCenterVariable-trans W₀≼W₁
    (future-paired W₁≼W₂ related) X =
  cong Fin.suc (liftCenterVariable-trans W₀≼W₁ W₁≼W₂ X)
liftCenterVariable-trans W₀≼W₁ (future-precise W₁≼W₂ related) X =
  cong Fin.suc (liftCenterVariable-trans W₀≼W₁ W₁≼W₂ X)
liftCenterVariable-trans W₀≼W₁ (future-imprecise W₁≼W₂) X =
  cong Fin.suc (liftCenterVariable-trans W₀≼W₁ W₁≼W₂ X)

liftPreciseTy-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty Δᴾ₀)
  → liftPreciseTy (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftPreciseTy W₁≼W₂ (liftPreciseTy W₀≼W₁ A)
liftPreciseTy-trans W₀≼W₁ future-refl A = refl
liftPreciseTy-trans W₀≼W₁ (future-paired W₁≼W₂ related) A =
  cong ⇑ᵗ (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ A)
liftPreciseTy-trans W₀≼W₁ (future-precise W₁≼W₂ related) A =
  cong ⇑ᵗ (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ A)
liftPreciseTy-trans W₀≼W₁ (future-imprecise W₁≼W₂) A =
  liftPreciseTy-trans W₀≼W₁ W₁≼W₂ A

liftImpreciseTy-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty Δᴵ₀)
  → liftImpreciseTy (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftImpreciseTy W₁≼W₂ (liftImpreciseTy W₀≼W₁ A)
liftImpreciseTy-trans W₀≼W₁ future-refl A = refl
liftImpreciseTy-trans W₀≼W₁ (future-paired W₁≼W₂ related) A =
  cong ⇑ᵗ (liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ A)
liftImpreciseTy-trans W₀≼W₁ (future-precise W₁≼W₂ related) A =
  liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ A
liftImpreciseTy-trans W₀≼W₁ (future-imprecise W₁≼W₂) A =
  cong ⇑ᵗ (liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ A)

liftCenterTy-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty Δᶜ₀)
  → liftCenterTy (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftCenterTy W₁≼W₂ (liftCenterTy W₀≼W₁ A)
liftCenterTy-trans W₀≼W₁ future-refl A = refl
liftCenterTy-trans W₀≼W₁ (future-paired W₁≼W₂ related) A =
  cong ⇑ᵗ (liftCenterTy-trans W₀≼W₁ W₁≼W₂ A)
liftCenterTy-trans W₀≼W₁ (future-precise W₁≼W₂ related) A =
  cong ⇑ᵗ (liftCenterTy-trans W₀≼W₁ W₁≼W₂ A)
liftCenterTy-trans W₀≼W₁ (future-imprecise W₁≼W₂) A =
  cong ⇑ᵗ (liftCenterTy-trans W₀≼W₁ W₁≼W₂ A)

liftPreciseTerm-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (M : Term Δᴾ₀)
  → liftPreciseTerm (future-trans W₀≼W₁ W₁≼W₂) M
      ≡ liftPreciseTerm W₁≼W₂ (liftPreciseTerm W₀≼W₁ M)
liftPreciseTerm-trans W₀≼W₁ future-refl M = refl
liftPreciseTerm-trans W₀≼W₁ (future-paired W₁≼W₂ related) M =
  cong ⇑ᵗᵐ (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)
liftPreciseTerm-trans W₀≼W₁ (future-precise W₁≼W₂ related) M =
  cong ⇑ᵗᵐ (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)
liftPreciseTerm-trans W₀≼W₁ (future-imprecise W₁≼W₂) M =
  liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M

liftImpreciseTerm-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (M : Term Δᴵ₀)
  → liftImpreciseTerm (future-trans W₀≼W₁ W₁≼W₂) M
      ≡ liftImpreciseTerm W₁≼W₂ (liftImpreciseTerm W₀≼W₁ M)
liftImpreciseTerm-trans W₀≼W₁ future-refl M = refl
liftImpreciseTerm-trans W₀≼W₁
    (future-paired W₁≼W₂ related) M =
  cong ⇑ᵗᵐ (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)
liftImpreciseTerm-trans W₀≼W₁ (future-precise W₁≼W₂ related) M =
  liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M
liftImpreciseTerm-trans W₀≼W₁ (future-imprecise W₁≼W₂) M =
  cong ⇑ᵗᵐ (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)

liftPreciseBodyTerm-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (M : Term (suc Δᴾ₀))
  → liftPreciseBodyTerm (future-trans W₀≼W₁ W₁≼W₂) M
      ≡ liftPreciseBodyTerm W₁≼W₂
          (liftPreciseBodyTerm W₀≼W₁ M)
liftPreciseBodyTerm-trans W₀≼W₁ future-refl M = refl
liftPreciseBodyTerm-trans W₀≼W₁
    (future-paired W₁≼W₂ related) M =
  cong (renameᵗᵐ (keep wk↪ᵗ))
    (liftPreciseBodyTerm-trans W₀≼W₁ W₁≼W₂ M)
liftPreciseBodyTerm-trans W₀≼W₁
    (future-precise W₁≼W₂ related) M =
  cong (renameᵗᵐ (keep wk↪ᵗ))
    (liftPreciseBodyTerm-trans W₀≼W₁ W₁≼W₂ M)
liftPreciseBodyTerm-trans W₀≼W₁
    (future-imprecise W₁≼W₂) M =
  liftPreciseBodyTerm-trans W₀≼W₁ W₁≼W₂ M

liftImpreciseBodyTerm-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (M : Term (suc Δᴵ₀))
  → liftImpreciseBodyTerm (future-trans W₀≼W₁ W₁≼W₂) M
      ≡ liftImpreciseBodyTerm W₁≼W₂
          (liftImpreciseBodyTerm W₀≼W₁ M)
liftImpreciseBodyTerm-trans W₀≼W₁ future-refl M = refl
liftImpreciseBodyTerm-trans W₀≼W₁
    (future-paired W₁≼W₂ related) M =
  cong (renameᵗᵐ (keep wk↪ᵗ))
    (liftImpreciseBodyTerm-trans W₀≼W₁ W₁≼W₂ M)
liftImpreciseBodyTerm-trans W₀≼W₁
    (future-precise W₁≼W₂ related) M =
  liftImpreciseBodyTerm-trans W₀≼W₁ W₁≼W₂ M
liftImpreciseBodyTerm-trans W₀≼W₁
    (future-imprecise W₁≼W₂) M =
  cong (renameᵗᵐ (keep wk↪ᵗ))
    (liftImpreciseBodyTerm-trans W₀≼W₁ W₁≼W₂ M)

liftPreciseBody-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty (suc Δᴾ₀))
  → liftPreciseBody (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftPreciseBody W₁≼W₂ (liftPreciseBody W₀≼W₁ A)
liftPreciseBody-trans W₀≼W₁ future-refl A = refl
liftPreciseBody-trans W₀≼W₁ (future-paired W₁≼W₂ related) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftPreciseBody-trans W₀≼W₁ W₁≼W₂ A)
liftPreciseBody-trans W₀≼W₁ (future-precise W₁≼W₂ related) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftPreciseBody-trans W₀≼W₁ W₁≼W₂ A)
liftPreciseBody-trans W₀≼W₁ (future-imprecise W₁≼W₂) A =
  liftPreciseBody-trans W₀≼W₁ W₁≼W₂ A

liftImpreciseBody-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty (suc Δᴵ₀))
  → liftImpreciseBody (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftImpreciseBody W₁≼W₂ (liftImpreciseBody W₀≼W₁ A)
liftImpreciseBody-trans W₀≼W₁ future-refl A = refl
liftImpreciseBody-trans W₀≼W₁
    (future-paired W₁≼W₂ related) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftImpreciseBody-trans W₀≼W₁ W₁≼W₂ A)
liftImpreciseBody-trans W₀≼W₁ (future-precise W₁≼W₂ related) A =
  liftImpreciseBody-trans W₀≼W₁ W₁≼W₂ A
liftImpreciseBody-trans W₀≼W₁ (future-imprecise W₁≼W₂) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftImpreciseBody-trans W₀≼W₁ W₁≼W₂ A)

liftCenterBody-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (A : Ty (suc Δᶜ₀))
  → liftCenterBody (future-trans W₀≼W₁ W₁≼W₂) A
      ≡ liftCenterBody W₁≼W₂ (liftCenterBody W₀≼W₁ A)
liftCenterBody-trans W₀≼W₁ future-refl A = refl
liftCenterBody-trans W₀≼W₁ (future-paired W₁≼W₂ related) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-trans W₀≼W₁ W₁≼W₂ A)
liftCenterBody-trans W₀≼W₁ (future-precise W₁≼W₂ related) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-trans W₀≼W₁ W₁≼W₂ A)
liftCenterBody-trans W₀≼W₁ (future-imprecise W₁≼W₂) A =
  cong (renameᵗ (extᵗ Fin.suc))
    (liftCenterBody-trans W₀≼W₁ W₁≼W₂ A)

------------------------------------------------------------------------
-- Endpoint variables and sealed values through futures
------------------------------------------------------------------------

liftPreciseVariable : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TyVar Δᴾ
  → TyVar Δᴾ′
liftPreciseVariable future-refl X = X
liftPreciseVariable (future-paired W≼W′ related) X =
  Fin.suc (liftPreciseVariable W≼W′ X)
liftPreciseVariable (future-precise W≼W′ related) X =
  Fin.suc (liftPreciseVariable W≼W′ X)
liftPreciseVariable (future-imprecise W≼W′) X =
  liftPreciseVariable W≼W′ X

liftImpreciseVariable : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → TyVar Δᴵ
  → TyVar Δᴵ′
liftImpreciseVariable future-refl X = X
liftImpreciseVariable (future-paired W≼W′ related) X =
  Fin.suc (liftImpreciseVariable W≼W′ X)
liftImpreciseVariable (future-precise W≼W′ related) X =
  liftImpreciseVariable W≼W′ X
liftImpreciseVariable (future-imprecise W≼W′) X =
  Fin.suc (liftImpreciseVariable W≼W′ X)

-- Shifting a sealed value is sealing the shifted payload at the shifted
-- variable and representation.

shift-sealed : ∀ {Δ} (U : Term Δ) (X : TyVar Δ) (R : Ty Δ)
  → ⇑ᵗᵐ (U ↓ seal X R) ≡ ⇑ᵗᵐ U ↓ seal (Fin.suc X) (⇑ᵗ R)
shift-sealed U X R =
  cong₂ (λ Y T → ⇑ᵗᵐ U ↓ seal Y T) (toRename-wk-eq X)
    (renameᵗ-wk-eq R)

liftPreciseTerm-sealed : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) U X R
  → liftPreciseTerm W≼W′ (U ↓ seal X R)
      ≡ liftPreciseTerm W≼W′ U
          ↓ seal (liftPreciseVariable W≼W′ X) (liftPreciseTy W≼W′ R)
liftPreciseTerm-sealed future-refl U X R = refl
liftPreciseTerm-sealed (future-paired W≼W′ related) U X R
    rewrite liftPreciseTerm-sealed W≼W′ U X R =
  shift-sealed _ _ _
liftPreciseTerm-sealed (future-precise W≼W′ related) U X R
    rewrite liftPreciseTerm-sealed W≼W′ U X R =
  shift-sealed _ _ _
liftPreciseTerm-sealed (future-imprecise W≼W′) U X R =
  liftPreciseTerm-sealed W≼W′ U X R

liftImpreciseTerm-sealed : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) U X R
  → liftImpreciseTerm W≼W′ (U ↓ seal X R)
      ≡ liftImpreciseTerm W≼W′ U
          ↓ seal (liftImpreciseVariable W≼W′ X)
              (liftImpreciseTy W≼W′ R)
liftImpreciseTerm-sealed future-refl U X R = refl
liftImpreciseTerm-sealed (future-paired W≼W′ related) U X R
    rewrite liftImpreciseTerm-sealed W≼W′ U X R =
  shift-sealed _ _ _
liftImpreciseTerm-sealed (future-precise W≼W′ related) U X R =
  liftImpreciseTerm-sealed W≼W′ U X R
liftImpreciseTerm-sealed (future-imprecise W≼W′) U X R
    rewrite liftImpreciseTerm-sealed W≼W′ U X R =
  shift-sealed _ _ _

------------------------------------------------------------------------
-- Semantic entries through futures
------------------------------------------------------------------------

-- The entry at the lifted center of a future world is the lifted entry:
-- the same kind of slot, with lifted endpoint variables and lifted
-- representation types.

data EntryLift {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ} :
    ∀ {mode mode′} → SemanticEntry (core W) Z mode
    → SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′
    → Set where
  lift-paired : ∀ {mode mode′}
      {a : SemanticAtom (core W) Z}
      {a′ : SemanticAtom (core W′) (liftCenterVariable W≼W′ Z)}
    → preciseVariable a′ ≡ liftPreciseVariable W≼W′ (preciseVariable a)
    → impreciseVariable a′
        ≡ liftImpreciseVariable W≼W′ (impreciseVariable a)
    → preciseRep a′ ≡ liftPreciseTy W≼W′ (preciseRep a)
    → impreciseRep a′ ≡ liftImpreciseTy W≼W′ (impreciseRep a)
    → EntryLift W≼W′ (paired-entry {mode = mode} a)
        (paired-entry {mode = mode′} a′)
  lift-dynamic :
      {a : DynamicSemanticAtom (core W) Z}
      {a′ : DynamicSemanticAtom (core W′) (liftCenterVariable W≼W′ Z)}
    → dynamicPreciseVariable a′
        ≡ liftPreciseVariable W≼W′ (dynamicPreciseVariable a)
    → dynamicRep a′ ≡ liftPreciseTy W≼W′ (dynamicRep a)
    → EntryLift W≼W′ (dynamic-entry a) (dynamic-entry a′)
  lift-target :
      {a : TargetSemanticAtom (core W) Z}
      {a′ : TargetSemanticAtom (core W′) (liftCenterVariable W≼W′ Z)}
    → EntryLift W≼W′ (target-entry a) (target-entry a′)

-- Extending an entry lift by one further binding.

entry-lift-paired : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
    {Rᴾ : Ty Δᴾ′} {Rᴵ : Ty Δᴵ′} (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
    {Z : TyVar Δᶜ} {mode mode′}
    {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ e e′
  → EntryLift (future-paired W≼W′ r) e (weaken-entry Rᴾ Rᴵ e′)
entry-lift-paired W≼W′ r (lift-paired eqᴾ eqᴵ repᴾ repᴵ) =
  lift-paired (cong Fin.suc eqᴾ) (cong Fin.suc eqᴵ)
    (cong ⇑ᵗ repᴾ) (cong ⇑ᵗ repᴵ)
entry-lift-paired W≼W′ r (lift-dynamic eqᴾ repᴾ) =
  lift-dynamic (cong Fin.suc eqᴾ) (cong ⇑ᵗ repᴾ)
entry-lift-paired W≼W′ r lift-target = lift-target

entry-lift-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
    {Rᴾ : Ty Δᴾ′}
    (r : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
    {Z : TyVar Δᶜ} {mode mode′}
    {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ e e′
  → EntryLift (future-precise W≼W′ r) e (weaken-entry-precise Rᴾ e′)
entry-lift-precise W≼W′ r (lift-paired eqᴾ eqᴵ repᴾ repᴵ) =
  lift-paired (cong Fin.suc eqᴾ) eqᴵ (cong ⇑ᵗ repᴾ) repᴵ
entry-lift-precise W≼W′ r (lift-dynamic eqᴾ repᴾ) =
  lift-dynamic (cong Fin.suc eqᴾ) (cong ⇑ᵗ repᴾ)
entry-lift-precise W≼W′ r lift-target = lift-target

entry-lift-imprecise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
    {Rᴵ : Ty Δᴵ′}
    {Z : TyVar Δᶜ} {mode mode′}
    {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ e e′
  → EntryLift (future-imprecise {Aᴵ = Rᴵ} W≼W′) e
      (weaken-entry-imprecise Rᴵ e′)
entry-lift-imprecise W≼W′ (lift-paired eqᴾ eqᴵ repᴾ repᴵ) =
  lift-paired eqᴾ (cong Fin.suc eqᴵ) repᴾ (cong ⇑ᵗ repᴵ)
entry-lift-imprecise W≼W′ (lift-dynamic eqᴾ repᴾ) =
  lift-dynamic eqᴾ repᴾ
entry-lift-imprecise W≼W′ lift-target = lift-target

entry-lift-refl : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {mode} (e : SemanticEntry (core W) Z mode)
  → EntryLift (future-refl {W = W}) e e
entry-lift-refl (paired-entry a) = lift-paired refl refl refl refl
entry-lift-refl (dynamic-entry a) = lift-dynamic refl refl
entry-lift-refl (target-entry a) = lift-target

-- The entry at the lifted center of any future world lifts the entry at
-- the original center.

entry-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (Z : TyVar Δᶜ)
  → EntryLift W≼W′ (semanticEntry W Z)
      (semanticEntry W′ (liftCenterVariable W≼W′ Z))
entry-future future-refl Z = entry-lift-refl _
entry-future (future-paired W≼W′ r) Z =
  entry-lift-paired W≼W′ r (entry-future W≼W′ Z)
entry-future (future-precise W≼W′ r) Z =
  entry-lift-precise W≼W′ r (entry-future W≼W′ Z)
entry-future (future-imprecise W≼W′) Z =
  entry-lift-imprecise W≼W′ (entry-future W≼W′ Z)

------------------------------------------------------------------------
-- Embeddings after a future
------------------------------------------------------------------------

-- The precise, imprecise, and center embeddings of an order-preserving
-- embedding followed by the allocations of a future, built by skipping
-- each allocation.  Lifting a renamed endpoint through the future is
-- renaming by the shifted embedding.

afterPrecise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′ → Δ₀ ↪ᵗ Δᴾ → Δ₀ ↪ᵗ Δᴾ′
afterPrecise future-refl ρ = ρ
afterPrecise (future-paired W≼W′ r) ρ = skip (afterPrecise W≼W′ ρ)
afterPrecise (future-precise W≼W′ r) ρ = skip (afterPrecise W≼W′ ρ)
afterPrecise (future-imprecise W≼W′) ρ = afterPrecise W≼W′ ρ

afterImprecise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′ → Δ₀ ↪ᵗ Δᴵ → Δ₀ ↪ᵗ Δᴵ′
afterImprecise future-refl ρ = ρ
afterImprecise (future-paired W≼W′ r) ρ = skip (afterImprecise W≼W′ ρ)
afterImprecise (future-precise W≼W′ r) ρ = afterImprecise W≼W′ ρ
afterImprecise (future-imprecise W≼W′) ρ = skip (afterImprecise W≼W′ ρ)

afterCenter : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′ → Δ₀ ↪ᵗ Δᶜ → Δ₀ ↪ᵗ Δᶜ′
afterCenter future-refl π = π
afterCenter (future-paired W≼W′ r) π = skip (afterCenter W≼W′ π)
afterCenter (future-precise W≼W′ r) π = skip (afterCenter W≼W′ π)
afterCenter (future-imprecise W≼W′) π = skip (afterCenter W≼W′ π)

module proof.Target.GroundValue.NuImprecisionTargetGroundValueQuotientEliminationProperties where

-- File Charter:
--   * Provides permutation and composition algebra for eliminating a
--     quotient index whose target endpoint is ground.
--   * Handles source-side adjacent-forall permutations with local transport.
--   * Contains no term-imprecision constructor cases or simulation result
--     dependency, so the migrating theorem can be checked independently.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; narrowing
  ; widening
  ; shape-id-var
  ; shape-id-base
  ; shape-id-star
  ; shape-fun
  ; shape-all
  ; shape-tag-var
  ; shape-tag-base
  ; shape-tag-fun
  ; shape-untag-var
  ; shape-untag-base
  ; shape-untag-fun
  ; shape-seal
  ; shape-unseal
  ; shape-gen
  ; shape-inst
  ; shape-sequence-widening
  ; shape-sequence-narrowing
  )
open import Data.Bool using (false; true; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  ; quotientᵖ
  ; swap01ᵗ
  ; _∣_⊢_⊑ᵖ_⊣_
  )
open import Imprecision using
  ( ImpAssm
  ; NonVar
  ; nonvar-all
  ; nonvar-fun
  ; renameNonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ImpCtx
  ; ⇑ᴸᵢ
  )
open import ImprecisionComposition using
  ( _⊢_≈∀ˢ_
  ; source-perm-refl
  ; source-perm-sym
  ; source-perm-trans
  ; source-perm-↦
  ; source-perm-tag-⇛
  ; source-perm-∀
  ; source-perm-ν
  ; source-swap-∀∀
  ; source-swap-∀ν
  ; source-swap-ν∀
  ; source-swap-νν
  ; ⌊_⌋
  ; id★ˢ
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; _；_≋_
  ; comp-id★
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-tag-id★
  ; comp-tag-⇛-id★
  ; comp-tagˣ-id★
  ; comp-ν
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  )
open import ImprecisionWf using
  ( id★
  ; idˣ
  ; idι
  ; _↦_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTerms using (Value; _⟨_⟩)
import Types as T
open import proof.Core.Permutation.ForallPermutationProperties using
  ( ≈∀-atom-left-eq
  ; ≈∀-ground-left-eq
  ; ≈∀-ground-right-eq
  ; renameᵗ-swap01-involutive
  ; swap01-involutive
  ; swap01-pres-<
  )
import proof.Core.Properties.NarrowWidenProperties as NWP
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( imprecision-composition-shape-transport
  ; shape-subst-source
  )
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-result-unique)
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; occurs-zero-rename-ext
  )


rename-left-assm : T.Renameᵗ → ImpAssm → ImpAssm
rename-left-assm ρ (X ˣ⊑★) = ρ X ˣ⊑★
rename-left-assm ρ (X ˣ⊑ˣ Y) = ρ X ˣ⊑ˣ Y


lift-left-star :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
lift-left-star {Φ = []} ()
lift-left-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
lift-left-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (lift-left-star x∈)
lift-left-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (lift-left-star x∈)


unlift-left-star :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
unlift-left-star {Φ = []} ()
unlift-left-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
unlift-left-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (unlift-left-star x∈)
unlift-left-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (unlift-left-star x∈)


no-lift-left-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-lift-left-zero-star {Φ = []} ()
no-lift-left-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-lift-left-zero-star x∈
no-lift-left-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-lift-left-zero-star x∈


lift-left-var :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
lift-left-var {Φ = []} ()
lift-left-var {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (lift-left-var x∈)
lift-left-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
lift-left-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (lift-left-var x∈)


unlift-left-var :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
unlift-left-var {Φ = []} ()
unlift-left-var {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (unlift-left-var x∈)
unlift-left-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
unlift-left-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (unlift-left-var x∈)


no-lift-left-zero-var :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-lift-left-zero-var {Φ = []} ()
no-lift-left-zero-var {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-lift-left-zero-var x∈
no-lift-left-zero-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-lift-left-zero-var x∈


lift-left-assm-map :
  ∀ {Ρ Σ : ImpCtx} {ρ : T.Renameᵗ} →
  (∀ {a} → a ∈ Ρ → rename-left-assm ρ a ∈ Σ) →
  ∀ {a} →
  a ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ρ) →
  rename-left-assm (T.extᵗ ρ) a ∈
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Σ)
lift-left-assm-map h {a = zero ˣ⊑★} (here refl) = here refl
lift-left-assm-map h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-lift-left-zero-star a∈)
lift-left-assm-map h {a = suc X ˣ⊑★} (here ())
lift-left-assm-map h {a = suc X ˣ⊑★} (there a∈) =
  there (lift-left-star (h (unlift-left-star a∈)))
lift-left-assm-map h {a = zero ˣ⊑ˣ Y} (here ())
lift-left-assm-map h {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-lift-left-zero-var a∈)
lift-left-assm-map h {a = suc X ˣ⊑ˣ Y} (here ())
lift-left-assm-map h {a = suc X ˣ⊑ˣ Y} (there a∈) =
  there (lift-left-var (h (unlift-left-var a∈)))


swap-double-left-assm-map :
  ∀ {Φ : ImpCtx} {a} →
  a ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) →
  rename-left-assm swap01ᵗ a ∈
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
swap-double-left-assm-map {a = zero ˣ⊑★} (here refl) =
  there (here refl)
swap-double-left-assm-map {a = zero ˣ⊑★} (there (here ()))
swap-double-left-assm-map {a = zero ˣ⊑★} (there (there a∈)) =
  ⊥-elim (no-lift-left-zero-star a∈)
swap-double-left-assm-map {a = suc zero ˣ⊑★} (here ())
swap-double-left-assm-map {a = suc zero ˣ⊑★}
    (there (here refl)) =
  here refl
swap-double-left-assm-map {a = suc zero ˣ⊑★}
    (there (there a∈)) =
  ⊥-elim
    (no-lift-left-zero-star (unlift-left-star a∈))
swap-double-left-assm-map {a = suc (suc X) ˣ⊑★} (here ())
swap-double-left-assm-map {a = suc (suc X) ˣ⊑★}
    (there (here ()))
swap-double-left-assm-map {a = suc (suc X) ˣ⊑★}
    (there (there a∈)) =
  there (there a∈)
swap-double-left-assm-map {a = zero ˣ⊑ˣ Y} (here ())
swap-double-left-assm-map {a = zero ˣ⊑ˣ Y} (there (here ()))
swap-double-left-assm-map {a = zero ˣ⊑ˣ Y} (there (there a∈)) =
  ⊥-elim (no-lift-left-zero-var a∈)
swap-double-left-assm-map {a = suc zero ˣ⊑ˣ Y} (here ())
swap-double-left-assm-map {a = suc zero ˣ⊑ˣ Y}
    (there (here ()))
swap-double-left-assm-map {a = suc zero ˣ⊑ˣ Y}
    (there (there a∈)) =
  ⊥-elim (no-lift-left-zero-var (unlift-left-var a∈))
swap-double-left-assm-map {a = suc (suc X) ˣ⊑ˣ Y} (here ())
swap-double-left-assm-map {a = suc (suc X) ˣ⊑ˣ Y}
    (there (here ()))
swap-double-left-assm-map {a = suc (suc X) ˣ⊑ˣ Y}
    (there (there a∈)) =
  there (there a∈)


ext-injective :
  ∀ {ρ : T.Renameᵗ} →
  (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y) →
  ∀ {X Y} → T.extᵗ ρ X ≡ T.extᵗ ρ Y → X ≡ Y
ext-injective injective {zero} {zero} eq = refl
ext-injective injective {zero} {suc Y} ()
ext-injective injective {suc X} {zero} ()
ext-injective injective {suc X} {suc Y} eq =
  cong suc (injective (suc-injective eq))


occurs-rename-injective :
  ∀ {ρ : T.Renameᵗ} →
  (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y) →
  ∀ X A →
  T.occurs (ρ X) (T.renameᵗ ρ A) ≡ T.occurs X A
occurs-rename-injective {ρ = ρ} injective X (T.＇ Y)
    with X ≟ Y | ρ X ≟ ρ Y
occurs-rename-injective injective X (T.＇ .X)
    | yes refl | yes refl = refl
occurs-rename-injective injective X (T.＇ .X)
    | yes refl | no X≢X = ⊥-elim (X≢X refl)
occurs-rename-injective injective X (T.＇ Y)
    | no X≢Y | yes eq = ⊥-elim (X≢Y (injective eq))
occurs-rename-injective injective X (T.＇ Y)
    | no X≢Y | no ρX≢ρY = refl
occurs-rename-injective injective X (T.‵ ι) = refl
occurs-rename-injective injective X T.★ = refl
occurs-rename-injective injective X (A T.⇒ B)
    rewrite occurs-rename-injective injective X A
          | occurs-rename-injective injective X B =
  refl
occurs-rename-injective {ρ = ρ} injective X (T.`∀ A) =
  occurs-rename-injective (ext-injective injective) (suc X) A


swap01-injective :
  ∀ {X Y} →
  swap01ᵗ X ≡ swap01ᵗ Y →
  X ≡ Y
swap01-injective {X} {Y} eq =
  trans (sym (swap01-involutive X))
    (trans (cong swap01ᵗ eq) (swap01-involutive Y))


≈∀-occurs :
  ∀ {A B} →
  A ≈∀ B →
  ∀ X → T.occurs X A ≡ T.occurs X B
≈∀-occurs ≈∀-refl X = refl
≈∀-occurs (≈∀-sym B≈A) X = sym (≈∀-occurs B≈A X)
≈∀-occurs (≈∀-trans A≈B B≈C) X =
  trans (≈∀-occurs A≈B X) (≈∀-occurs B≈C X)
≈∀-occurs (≈∀-⇒ A≈A′ B≈B′) X =
  cong₂ _∨_ (≈∀-occurs A≈A′ X) (≈∀-occurs B≈B′ X)
≈∀-occurs (≈∀-∀ A≈B) X = ≈∀-occurs A≈B (suc X)
≈∀-occurs {A = T.`∀ (T.`∀ A)} ≈∀-swap X =
  sym (occurs-rename-injective swap01-injective (suc (suc X)) A)


mutual
  ≈∀-nonVar-left :
    ∀ {A B} →
    A ≈∀ B →
    NonVar B →
    NonVar A
  ≈∀-nonVar-left ≈∀-refl safe = safe
  ≈∀-nonVar-left (≈∀-sym B≈A) safe =
    ≈∀-nonVar-right B≈A safe
  ≈∀-nonVar-left (≈∀-trans A≈B B≈C) safe =
    ≈∀-nonVar-left A≈B (≈∀-nonVar-left B≈C safe)
  ≈∀-nonVar-left (≈∀-⇒ A≈A′ B≈B′) nonvar-fun = nonvar-fun
  ≈∀-nonVar-left (≈∀-∀ A≈B) nonvar-all = nonvar-all
  ≈∀-nonVar-left ≈∀-swap nonvar-all = nonvar-all

  ≈∀-nonVar-right :
    ∀ {A B} →
    A ≈∀ B →
    NonVar A →
    NonVar B
  ≈∀-nonVar-right ≈∀-refl safe = safe
  ≈∀-nonVar-right (≈∀-sym B≈A) safe =
    ≈∀-nonVar-left B≈A safe
  ≈∀-nonVar-right (≈∀-trans A≈B B≈C) safe =
    ≈∀-nonVar-right B≈C (≈∀-nonVar-right A≈B safe)
  ≈∀-nonVar-right (≈∀-⇒ A≈A′ B≈B′) nonvar-fun = nonvar-fun
  ≈∀-nonVar-right (≈∀-∀ A≈B) nonvar-all = nonvar-all
  ≈∀-nonVar-right ≈∀-swap nonvar-all = nonvar-all


mutual
  source-star-rename :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ} {ρ : T.Renameᵗ} {A} →
    (∀ {a} → a ∈ Φ → rename-left-assm ρ a ∈ Ψ) →
    TyRenameWf Δᴸ Δᴸ′ ρ →
    Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
    Ψ ∣ Δᴸ′ ⊢ T.renameᵗ ρ A ⊑ T.★ ⊣ Δᴿ
  source-star-rename h hρ id★ = id★
  source-star-rename h hρ (tag ι) = tag ι
  source-star-rename h hρ (tag p ⇛ q) =
    tag (source-star-rename h hρ p) ⇛
      source-star-rename h hρ q
  source-star-rename h hρ (tagˣ x∈ X<Δᴸ) = tagˣ (h x∈) (hρ X<Δᴸ)
  source-star-rename {ρ = ρ} h hρ (ν {A = A} safe occ p) =
    ν (renameNonVar (T.extᵗ ρ) safe)
      (trans (occurs-zero-rename-ext ρ A) occ)
      (source-star-rename
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)

  source-ground-rename :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ} {ρ : T.Renameᵗ} {A H} →
    T.Ground H →
    (∀ {a} → a ∈ Φ → rename-left-assm ρ a ∈ Ψ) →
    TyRenameWf Δᴸ Δᴸ′ ρ →
    Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ →
    Ψ ∣ Δᴸ′ ⊢ T.renameᵗ ρ A ⊑ H ⊣ Δᴿ
  source-ground-rename (T.＇ Y) h hρ
      (idˣ x∈ X<Δᴸ Y<Δᴿ) =
    idˣ (h x∈) (hρ X<Δᴸ) Y<Δᴿ
  source-ground-rename {ρ = ρ} (T.＇ Y) h hρ
      (ν {A = A} safe occ p) =
    ν (renameNonVar (T.extᵗ ρ) safe)
      (trans (occurs-zero-rename-ext ρ A) occ)
      (source-ground-rename (T.＇ Y)
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)
  source-ground-rename (T.‵ ι) h hρ idι = idι
  source-ground-rename {ρ = ρ} (T.‵ ι) h hρ
      (ν {A = A} safe occ p) =
    ν (renameNonVar (T.extᵗ ρ) safe)
      (trans (occurs-zero-rename-ext ρ A) occ)
      (source-ground-rename (T.‵ ι)
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)
  source-ground-rename T.★⇒★ h hρ (p ↦ q) =
    source-star-rename h hρ p ↦ source-star-rename h hρ q
  source-ground-rename {ρ = ρ} T.★⇒★ h hρ
      (ν {A = A} safe occ p) =
    ν (renameNonVar (T.extᵗ ρ) safe)
      (trans (occurs-zero-rename-ext ρ A) occ)
      (source-ground-rename T.★⇒★
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)


mutual
  source-star-rename-shape :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ} {ρ : T.Renameᵗ} {A}
      (h : ∀ {a} → a ∈ Φ → rename-left-assm ρ a ∈ Ψ)
      (hρ : TyRenameWf Δᴸ Δᴸ′ ρ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
    ⌊ source-star-rename h hρ p ⌋ ≡ ⌊ p ⌋
  source-star-rename-shape h hρ id★ = refl
  source-star-rename-shape h hρ (tag ι) = refl
  source-star-rename-shape h hρ (tag p ⇛ q) =
    cong₂ tag_⇛ˢ_
      (source-star-rename-shape h hρ p)
      (source-star-rename-shape h hρ q)
  source-star-rename-shape h hρ (tagˣ x∈ X<Δᴸ) = refl
  source-star-rename-shape {ρ = ρ} h hρ
      (ν {A = A} safe occ p) =
    cong νˢ_
      (source-star-rename-shape
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)

  source-ground-rename-shape :
    ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ} {ρ : T.Renameᵗ} {A H}
      (gH : T.Ground H)
      (h : ∀ {a} → a ∈ Φ → rename-left-assm ρ a ∈ Ψ)
      (hρ : TyRenameWf Δᴸ Δᴸ′ ρ)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ) →
    ⌊ source-ground-rename gH h hρ p ⌋ ≡ ⌊ p ⌋
  source-ground-rename-shape (T.＇ Y) h hρ
      (idˣ x∈ X<Δᴸ Y<Δᴿ) =
    refl
  source-ground-rename-shape {ρ = ρ} (T.＇ Y) h hρ
      (ν {A = A} safe occ p) =
    cong νˢ_
      (source-ground-rename-shape (T.＇ Y)
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)
  source-ground-rename-shape (T.‵ ι) h hρ idι = refl
  source-ground-rename-shape {ρ = ρ} (T.‵ ι) h hρ
      (ν {A = A} safe occ p) =
    cong νˢ_
      (source-ground-rename-shape (T.‵ ι)
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)
  source-ground-rename-shape T.★⇒★ h hρ (p ↦ q) =
    cong₂ _↦ˢ_
      (source-star-rename-shape h hρ p)
      (source-star-rename-shape h hρ q)
  source-ground-rename-shape {ρ = ρ} T.★⇒★ h hρ
      (ν {A = A} safe occ p) =
    cong νˢ_
      (source-ground-rename-shape T.★⇒★
        (lift-left-assm-map h) (TyRenameWf-ext hρ) p)


mutual
  source-star-≈∀-left :
    ∀ {Φ Δᴸ Δᴿ A B} →
    A ≈∀ B →
    Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ
  source-star-≈∀-left ≈∀-refl p = p
  source-star-≈∀-left (≈∀-sym B≈A) p =
    source-star-≈∀-right B≈A p
  source-star-≈∀-left (≈∀-trans A≈B B≈C) p =
    source-star-≈∀-left A≈B (source-star-≈∀-left B≈C p)
  source-star-≈∀-left (≈∀-⇒ A≈A′ B≈B′) (tag p ⇛ q) =
    tag source-star-≈∀-left A≈A′ p ⇛
      source-star-≈∀-left B≈B′ q
  source-star-≈∀-left (≈∀-∀ A≈B) (ν safe occ p) =
    ν (≈∀-nonVar-left A≈B safe)
      (trans (≈∀-occurs A≈B zero) occ)
      (source-star-≈∀-left A≈B p)
  source-star-≈∀-left {A = T.`∀ (T.`∀ A)} ≈∀-swap
      (ν outer-safe outer (ν inner-safe inner p)) =
    ν nonvar-all (trans (sym one-eq) inner)
      (ν safe-A (trans (sym zero-eq) outer)
        (subst (λ X → _ ∣ _ ⊢ X ⊑ T.★ ⊣ _)
          (renameᵗ-swap01-involutive A)
          (source-star-rename swap-double-left-assm-map
            swap01-pres-< p)))
    where
    safe-A =
      subst NonVar (renameᵗ-swap01-involutive A)
        (renameNonVar swap01ᵗ inner-safe)
    zero-eq = occurs-rename-injective swap01-injective zero A
    one-eq = occurs-rename-injective swap01-injective (suc zero) A

  source-star-≈∀-right :
    ∀ {Φ Δᴸ Δᴿ A B} →
    A ≈∀ B →
    Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ
  source-star-≈∀-right ≈∀-refl p = p
  source-star-≈∀-right (≈∀-sym B≈A) p =
    source-star-≈∀-left B≈A p
  source-star-≈∀-right (≈∀-trans A≈B B≈C) p =
    source-star-≈∀-right B≈C (source-star-≈∀-right A≈B p)
  source-star-≈∀-right (≈∀-⇒ A≈A′ B≈B′) (tag p ⇛ q) =
    tag source-star-≈∀-right A≈A′ p ⇛
      source-star-≈∀-right B≈B′ q
  source-star-≈∀-right (≈∀-∀ A≈B) (ν safe occ p) =
    ν (≈∀-nonVar-right A≈B safe)
      (trans (sym (≈∀-occurs A≈B zero)) occ)
      (source-star-≈∀-right A≈B p)
  source-star-≈∀-right {A = T.`∀ (T.`∀ A)} ≈∀-swap
      (ν outer-safe outer (ν inner-safe inner p)) =
    ν nonvar-all (trans zero-eq inner)
      (ν (renameNonVar swap01ᵗ inner-safe) (trans one-eq outer)
        (source-star-rename swap-double-left-assm-map
          swap01-pres-< p))
    where
    zero-eq = occurs-rename-injective swap01-injective zero A
    one-eq = occurs-rename-injective swap01-injective (suc zero) A


mutual
  source-ground-≈∀-left :
    ∀ {Φ Δᴸ Δᴿ A B H} →
    T.Ground H →
    A ≈∀ B →
    Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ
  source-ground-≈∀-left gH ≈∀-refl p = p
  source-ground-≈∀-left gH (≈∀-sym B≈A) p =
    source-ground-≈∀-right gH B≈A p
  source-ground-≈∀-left gH (≈∀-trans A≈B B≈C) p =
    source-ground-≈∀-left gH A≈B
      (source-ground-≈∀-left gH B≈C p)
  source-ground-≈∀-left (T.＇ X) (≈∀-⇒ A≈A′ B≈B′) ()
  source-ground-≈∀-left (T.‵ ι) (≈∀-⇒ A≈A′ B≈B′) ()
  source-ground-≈∀-left T.★⇒★ (≈∀-⇒ A≈A′ B≈B′)
      (p ↦ q) =
    source-star-≈∀-left A≈A′ p ↦
      source-star-≈∀-left B≈B′ q
  source-ground-≈∀-left gH (≈∀-∀ A≈B) (ν safe occ p) =
    ν (≈∀-nonVar-left A≈B safe)
      (trans (≈∀-occurs A≈B zero) occ)
      (source-ground-≈∀-left gH A≈B p)
  source-ground-≈∀-left {A = T.`∀ (T.`∀ A)} gH ≈∀-swap
      (ν outer-safe outer (ν inner-safe inner p)) =
    ν nonvar-all (trans (sym one-eq) inner)
      (ν safe-A (trans (sym zero-eq) outer)
        (subst (λ X → _ ∣ _ ⊢ X ⊑ _ ⊣ _)
          (renameᵗ-swap01-involutive A)
          (source-ground-rename gH swap-double-left-assm-map
            swap01-pres-< p)))
    where
    safe-A =
      subst NonVar (renameᵗ-swap01-involutive A)
        (renameNonVar swap01ᵗ inner-safe)
    zero-eq = occurs-rename-injective swap01-injective zero A
    one-eq = occurs-rename-injective swap01-injective (suc zero) A

  source-ground-≈∀-right :
    ∀ {Φ Δᴸ Δᴿ A B H} →
    T.Ground H →
    A ≈∀ B →
    Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ
  source-ground-≈∀-right gH ≈∀-refl p = p
  source-ground-≈∀-right gH (≈∀-sym B≈A) p =
    source-ground-≈∀-left gH B≈A p
  source-ground-≈∀-right gH (≈∀-trans A≈B B≈C) p =
    source-ground-≈∀-right gH B≈C
      (source-ground-≈∀-right gH A≈B p)
  source-ground-≈∀-right (T.＇ X) (≈∀-⇒ A≈A′ B≈B′) ()
  source-ground-≈∀-right (T.‵ ι) (≈∀-⇒ A≈A′ B≈B′) ()
  source-ground-≈∀-right T.★⇒★ (≈∀-⇒ A≈A′ B≈B′)
      (p ↦ q) =
    source-star-≈∀-right A≈A′ p ↦
      source-star-≈∀-right B≈B′ q
  source-ground-≈∀-right gH (≈∀-∀ A≈B) (ν safe occ p) =
    ν (≈∀-nonVar-right A≈B safe)
      (trans (sym (≈∀-occurs A≈B zero)) occ)
      (source-ground-≈∀-right gH A≈B p)
  source-ground-≈∀-right {A = T.`∀ (T.`∀ A)} gH ≈∀-swap
      (ν outer-safe outer (ν inner-safe inner p)) =
    ν nonvar-all (trans zero-eq inner)
      (ν (renameNonVar swap01ᵗ inner-safe) (trans one-eq outer)
        (source-ground-rename gH swap-double-left-assm-map
          swap01-pres-< p))
    where
    zero-eq = occurs-rename-injective swap01-injective zero A
    one-eq = occurs-rename-injective swap01-injective (suc zero) A


mutual
  source-star-≈∀-left-composition :
    ∀ {Φ Δᴸ Δᴿ A B s t u}
      (equivalence : A ≈∀ B) →
    equivalence ⊢ s ≈∀ˢ t →
    (p : Φ ∣ Δᴸ ⊢ B ⊑ T.★ ⊣ Δᴿ) →
    t ； u ≋ ⌊ p ⌋ →
    s ； u ≋ ⌊ source-star-≈∀-left equivalence p ⌋
  source-star-≈∀-left-composition
      ≈∀-refl source-perm-refl p composition =
    composition
  source-star-≈∀-left-composition
      (≈∀-sym B≈A) (source-perm-sym shape) p composition =
    source-star-≈∀-right-composition B≈A shape p composition
  source-star-≈∀-left-composition
      (≈∀-trans A≈B B≈C)
      (source-perm-trans first-shape second-shape)
      p composition =
    source-star-≈∀-left-composition A≈B first-shape
      (source-star-≈∀-left B≈C p)
      (source-star-≈∀-left-composition
        B≈C second-shape p composition)
  source-star-≈∀-left-composition
      (≈∀-⇒ A≈A′ B≈B′)
      (source-perm-↦ domain-shape codomain-shape)
      (tag p ⇛ q)
      (comp-↦-tag domain-composition codomain-composition) =
    comp-↦-tag
      (source-star-≈∀-left-composition
        A≈A′ domain-shape p domain-composition)
      (source-star-≈∀-left-composition
        B≈B′ codomain-shape q codomain-composition)
  source-star-≈∀-left-composition
      (≈∀-⇒ A≈A′ B≈B′)
      (source-perm-tag-⇛ domain-shape codomain-shape)
      (tag p ⇛ q)
      (comp-tag-⇛-id★
        domain-composition codomain-composition) =
    comp-tag-⇛-id★
      (source-star-≈∀-left-composition
        A≈A′ domain-shape p domain-composition)
      (source-star-≈∀-left-composition
        B≈B′ codomain-shape q codomain-composition)
  source-star-≈∀-left-composition
      (≈∀-∀ A≈B)
      (source-perm-∀ shape)
      (ν safe occ p)
      (comp-∀-ν composition) =
    comp-∀-ν
      (source-star-≈∀-left-composition
        A≈B shape p composition)
  source-star-≈∀-left-composition
      (≈∀-∀ A≈B)
      (source-perm-ν shape)
      (ν safe occ p)
      (comp-ν composition) =
    comp-ν
      (source-star-≈∀-left-composition
        A≈B shape p composition)
  source-star-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-∀∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-∀-ν (comp-∀-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-star-rename swap-double-left-assm-map
            swap01-pres-< p))
        (source-star-rename-shape
          swap-double-left-assm-map swap01-pres-< p)
  source-star-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-∀ν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-∀-ν (comp-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-star-rename swap-double-left-assm-map
            swap01-pres-< p))
        (source-star-rename-shape
          swap-double-left-assm-map swap01-pres-< p)
  source-star-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-ν∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-ν (comp-∀-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-star-rename swap-double-left-assm-map
            swap01-pres-< p))
        (source-star-rename-shape
          swap-double-left-assm-map swap01-pres-< p)
  source-star-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-νν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-ν (comp-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-star-rename swap-double-left-assm-map
            swap01-pres-< p))
        (source-star-rename-shape
          swap-double-left-assm-map swap01-pres-< p)

  source-star-≈∀-right-composition :
    ∀ {Φ Δᴸ Δᴿ A B s t u}
      (equivalence : A ≈∀ B) →
    equivalence ⊢ s ≈∀ˢ t →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
    s ； u ≋ ⌊ p ⌋ →
    t ； u ≋ ⌊ source-star-≈∀-right equivalence p ⌋
  source-star-≈∀-right-composition
      ≈∀-refl source-perm-refl p composition =
    composition
  source-star-≈∀-right-composition
      (≈∀-sym B≈A) (source-perm-sym shape) p composition =
    source-star-≈∀-left-composition B≈A shape p composition
  source-star-≈∀-right-composition
      (≈∀-trans A≈B B≈C)
      (source-perm-trans first-shape second-shape)
      p composition =
    source-star-≈∀-right-composition B≈C second-shape
      (source-star-≈∀-right A≈B p)
      (source-star-≈∀-right-composition
        A≈B first-shape p composition)
  source-star-≈∀-right-composition
      (≈∀-⇒ A≈A′ B≈B′)
      (source-perm-↦ domain-shape codomain-shape)
      (tag p ⇛ q)
      (comp-↦-tag domain-composition codomain-composition) =
    comp-↦-tag
      (source-star-≈∀-right-composition
        A≈A′ domain-shape p domain-composition)
      (source-star-≈∀-right-composition
        B≈B′ codomain-shape q codomain-composition)
  source-star-≈∀-right-composition
      (≈∀-⇒ A≈A′ B≈B′)
      (source-perm-tag-⇛ domain-shape codomain-shape)
      (tag p ⇛ q)
      (comp-tag-⇛-id★
        domain-composition codomain-composition) =
    comp-tag-⇛-id★
      (source-star-≈∀-right-composition
        A≈A′ domain-shape p domain-composition)
      (source-star-≈∀-right-composition
        B≈B′ codomain-shape q codomain-composition)
  source-star-≈∀-right-composition
      (≈∀-∀ A≈B)
      (source-perm-∀ shape)
      (ν safe occ p)
      (comp-∀-ν composition) =
    comp-∀-ν
      (source-star-≈∀-right-composition
        A≈B shape p composition)
  source-star-≈∀-right-composition
      (≈∀-∀ A≈B)
      (source-perm-ν shape)
      (ν safe occ p)
      (comp-ν composition) =
    comp-ν
      (source-star-≈∀-right-composition
        A≈B shape p composition)
  source-star-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-∀∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-star-rename-shape
          {ρ = swap01ᵗ}
          swap-double-left-assm-map swap01-pres-< p))
      (comp-∀-ν (comp-∀-ν composition))
  source-star-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-∀ν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-star-rename-shape
          {ρ = swap01ᵗ}
          swap-double-left-assm-map swap01-pres-< p))
      (comp-ν (comp-∀-ν composition))
  source-star-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-ν∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-star-rename-shape
          {ρ = swap01ᵗ}
          swap-double-left-assm-map swap01-pres-< p))
      (comp-∀-ν (comp-ν composition))
  source-star-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      ≈∀-swap source-swap-νν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-star-rename-shape
          {ρ = swap01ᵗ}
          swap-double-left-assm-map swap01-pres-< p))
      (comp-ν (comp-ν composition))


mutual
  source-ground-≈∀-left-composition :
    ∀ {Φ Δᴸ Δᴿ A B H s t u}
      (gH : T.Ground H)
      (equivalence : A ≈∀ B) →
    equivalence ⊢ s ≈∀ˢ t →
    (p : Φ ∣ Δᴸ ⊢ B ⊑ H ⊣ Δᴿ) →
    t ； u ≋ ⌊ p ⌋ →
    s ； u ≋ ⌊ source-ground-≈∀-left gH equivalence p ⌋
  source-ground-≈∀-left-composition
      gH ≈∀-refl source-perm-refl p composition =
    composition
  source-ground-≈∀-left-composition
      gH (≈∀-sym B≈A) (source-perm-sym shape) p composition =
    source-ground-≈∀-right-composition
      gH B≈A shape p composition
  source-ground-≈∀-left-composition
      gH (≈∀-trans A≈B B≈C)
      (source-perm-trans first-shape second-shape)
      p composition =
    source-ground-≈∀-left-composition gH A≈B first-shape
      (source-ground-≈∀-left gH B≈C p)
      (source-ground-≈∀-left-composition
        gH B≈C second-shape p composition)
  source-ground-≈∀-left-composition
      (T.＇ X) (≈∀-⇒ A≈A′ B≈B′) shape () composition
  source-ground-≈∀-left-composition
      (T.‵ ι) (≈∀-⇒ A≈A′ B≈B′) shape () composition
  source-ground-≈∀-left-composition
      T.★⇒★ (≈∀-⇒ A≈A′ B≈B′)
      (source-perm-↦ domain-shape codomain-shape)
      (p ↦ q)
      (comp-↦-↦ domain-composition codomain-composition) =
    comp-↦-↦
      (source-star-≈∀-left-composition
        A≈A′ domain-shape p domain-composition)
      (source-star-≈∀-left-composition
        B≈B′ codomain-shape q codomain-composition)
  source-ground-≈∀-left-composition
      gH (≈∀-∀ A≈B)
      (source-perm-∀ shape)
      (ν safe occ p)
      (comp-∀-ν composition) =
    comp-∀-ν
      (source-ground-≈∀-left-composition
        gH A≈B shape p composition)
  source-ground-≈∀-left-composition
      gH (≈∀-∀ A≈B)
      (source-perm-ν shape)
      (ν safe occ p)
      (comp-ν composition) =
    comp-ν
      (source-ground-≈∀-left-composition
        gH A≈B shape p composition)
  source-ground-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-∀∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-∀-ν (comp-∀-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-ground-rename gH swap-double-left-assm-map
            swap01-pres-< p))
        (source-ground-rename-shape gH
          swap-double-left-assm-map swap01-pres-< p)
  source-ground-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-∀ν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-∀-ν (comp-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-ground-rename gH swap-double-left-assm-map
            swap01-pres-< p))
        (source-ground-rename-shape gH
          swap-double-left-assm-map swap01-pres-< p)
  source-ground-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-ν∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-ν (comp-∀-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-ground-rename gH swap-double-left-assm-map
            swap01-pres-< p))
        (source-ground-rename-shape gH
          swap-double-left-assm-map swap01-pres-< p)
  source-ground-≈∀-left-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-νν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl (cong (λ s → νˢ (νˢ s)) body-shape)
      (comp-ν (comp-ν composition))
    where
    body-shape =
      trans
        (shape-subst-source
          (renameᵗ-swap01-involutive A)
          (source-ground-rename gH swap-double-left-assm-map
            swap01-pres-< p))
        (source-ground-rename-shape gH
          swap-double-left-assm-map swap01-pres-< p)

  source-ground-≈∀-right-composition :
    ∀ {Φ Δᴸ Δᴿ A B H s t u}
      (gH : T.Ground H)
      (equivalence : A ≈∀ B) →
    equivalence ⊢ s ≈∀ˢ t →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ) →
    s ； u ≋ ⌊ p ⌋ →
    t ； u ≋ ⌊ source-ground-≈∀-right gH equivalence p ⌋
  source-ground-≈∀-right-composition
      gH ≈∀-refl source-perm-refl p composition =
    composition
  source-ground-≈∀-right-composition
      gH (≈∀-sym B≈A) (source-perm-sym shape) p composition =
    source-ground-≈∀-left-composition
      gH B≈A shape p composition
  source-ground-≈∀-right-composition
      gH (≈∀-trans A≈B B≈C)
      (source-perm-trans first-shape second-shape)
      p composition =
    source-ground-≈∀-right-composition gH B≈C second-shape
      (source-ground-≈∀-right gH A≈B p)
      (source-ground-≈∀-right-composition
        gH A≈B first-shape p composition)
  source-ground-≈∀-right-composition
      (T.＇ X) (≈∀-⇒ A≈A′ B≈B′) shape () composition
  source-ground-≈∀-right-composition
      (T.‵ ι) (≈∀-⇒ A≈A′ B≈B′) shape () composition
  source-ground-≈∀-right-composition
      T.★⇒★ (≈∀-⇒ A≈A′ B≈B′)
      (source-perm-↦ domain-shape codomain-shape)
      (p ↦ q)
      (comp-↦-↦ domain-composition codomain-composition) =
    comp-↦-↦
      (source-star-≈∀-right-composition
        A≈A′ domain-shape p domain-composition)
      (source-star-≈∀-right-composition
        B≈B′ codomain-shape q codomain-composition)
  source-ground-≈∀-right-composition
      gH (≈∀-∀ A≈B)
      (source-perm-∀ shape)
      (ν safe occ p)
      (comp-∀-ν composition) =
    comp-∀-ν
      (source-ground-≈∀-right-composition
        gH A≈B shape p composition)
  source-ground-≈∀-right-composition
      gH (≈∀-∀ A≈B)
      (source-perm-ν shape)
      (ν safe occ p)
      (comp-ν composition) =
    comp-ν
      (source-ground-≈∀-right-composition
        gH A≈B shape p composition)
  source-ground-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-∀∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-ground-rename-shape
          {ρ = swap01ᵗ} gH
          swap-double-left-assm-map swap01-pres-< p))
      (comp-∀-ν (comp-∀-ν composition))
  source-ground-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-∀ν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-∀-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-ground-rename-shape
          {ρ = swap01ᵗ} gH
          swap-double-left-assm-map swap01-pres-< p))
      (comp-ν (comp-∀-ν composition))
  source-ground-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-ν∀
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-∀-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-ground-rename-shape
          {ρ = swap01ᵗ} gH
          swap-double-left-assm-map swap01-pres-< p))
      (comp-∀-ν (comp-ν composition))
  source-ground-≈∀-right-composition
      {A = T.`∀ (T.`∀ A)}
      gH ≈∀-swap source-swap-νν
      (ν outer-safe outer (ν inner-safe inner p))
      (comp-ν (comp-ν composition)) =
    imprecision-composition-shape-transport
      refl refl
      (cong (λ s → νˢ (νˢ s))
        (source-ground-rename-shape
          {ρ = swap01ᵗ} gH
          swap-double-left-assm-map swap01-pres-< p))
      (comp-ν (comp-ν composition))


star-self-permutation-shape-equal :
  ∀ {equivalence : T.★ ≈∀ T.★} {s t} →
  equivalence ⊢ s ≈∀ˢ t →
  s ≡ t
star-self-permutation-shape-equal source-perm-refl = refl
star-self-permutation-shape-equal
    (source-perm-sym shape) =
  sym (star-self-permutation-shape-equal shape)
star-self-permutation-shape-equal
    (source-perm-trans
      {A≈B = first-equivalence}
      {B≈C = second-equivalence}
      first second)
    with ≈∀-atom-left-eq T.★ first-equivalence
star-self-permutation-shape-equal
    (source-perm-trans
      {A≈B = first-equivalence}
      {B≈C = second-equivalence}
      first second)
    | refl =
  trans
    (star-self-permutation-shape-equal first)
    (star-self-permutation-shape-equal second)


function-ground-self-permutation-shape-equal :
  ∀ {equivalence :
      T.★ T.⇒ T.★ ≈∀ T.★ T.⇒ T.★} {s t} →
  equivalence ⊢ s ≈∀ˢ t →
  s ≡ t
function-ground-self-permutation-shape-equal
    source-perm-refl =
  refl
function-ground-self-permutation-shape-equal
    (source-perm-sym shape) =
  sym (function-ground-self-permutation-shape-equal shape)
function-ground-self-permutation-shape-equal
    (source-perm-trans
      {A≈B = first-equivalence}
      {B≈C = second-equivalence}
      first second)
    with ≈∀-ground-left-eq T.★⇒★ first-equivalence
function-ground-self-permutation-shape-equal
    (source-perm-trans
      {A≈B = first-equivalence}
      {B≈C = second-equivalence}
      first second)
    | refl =
  trans
    (function-ground-self-permutation-shape-equal first)
    (function-ground-self-permutation-shape-equal second)
function-ground-self-permutation-shape-equal
    (source-perm-↦ domain codomain) =
  cong₂ _↦ˢ_
    (star-self-permutation-shape-equal domain)
    (star-self-permutation-shape-equal codomain)
function-ground-self-permutation-shape-equal
    (source-perm-tag-⇛ domain codomain) =
  cong₂ tag_⇛ˢ_
    (star-self-permutation-shape-equal domain)
    (star-self-permutation-shape-equal codomain)


star-right-identity-composition :
  ∀ {Φ Δᴸ Δᴿ A}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ T.★ ⊣ Δᴿ) →
  ⌊ p ⌋ ； id★ˢ ≋ ⌊ p ⌋
star-right-identity-composition id★ = comp-id★
star-right-identity-composition (tag ι) = comp-tag-id★
star-right-identity-composition (tag p ⇛ q) =
  comp-tag-⇛-id★
    (star-right-identity-composition p)
    (star-right-identity-composition q)
star-right-identity-composition (tagˣ x∈ X<Δᴸ) =
  comp-tagˣ-id★
star-right-identity-composition (ν safe occ p) =
  comp-ν (star-right-identity-composition p)


function-ground-right-identity-composition :
  ∀ {Φ Δᴸ Δᴿ A}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  ⌊ p ⌋ ； (id★ˢ ↦ˢ id★ˢ) ≋ ⌊ p ⌋
function-ground-right-identity-composition (p ↦ q) =
  comp-↦-↦
    (star-right-identity-composition p)
    (star-right-identity-composition q)
function-ground-right-identity-composition (ν safe occ p) =
  comp-ν (function-ground-right-identity-composition p)


cast-shape-result-unique :
  ∀ {direction c s t} →
  direction ⊢ᶜ c ⦂ s →
  direction ⊢ᶜ c ⦂ t →
  s ≡ t
cast-shape-result-unique shape-id-var shape-id-var = refl
cast-shape-result-unique shape-id-base shape-id-base = refl
cast-shape-result-unique shape-id-star shape-id-star = refl
cast-shape-result-unique
    (shape-fun source target)
    (shape-fun source′ target′) =
  cong₂ _↦ˢ_
    (cast-shape-result-unique source source′)
    (cast-shape-result-unique target target′)
cast-shape-result-unique
    (shape-all shape) (shape-all shape′) =
  cong ∀ˢ_ (cast-shape-result-unique shape shape′)
cast-shape-result-unique shape-tag-var shape-tag-var = refl
cast-shape-result-unique shape-tag-base shape-tag-base = refl
cast-shape-result-unique shape-tag-fun shape-tag-fun = refl
cast-shape-result-unique shape-untag-var shape-untag-var = refl
cast-shape-result-unique shape-untag-base shape-untag-base = refl
cast-shape-result-unique shape-untag-fun shape-untag-fun = refl
cast-shape-result-unique shape-seal shape-seal = refl
cast-shape-result-unique shape-unseal shape-unseal = refl
cast-shape-result-unique
    (shape-gen shape) (shape-gen shape′) =
  cong νˢ_ (cast-shape-result-unique shape shape′)
cast-shape-result-unique
    (shape-inst shape) (shape-inst shape′) =
  cong νˢ_ (cast-shape-result-unique shape shape′)
cast-shape-result-unique
    (shape-sequence-widening
      first second composition)
    (shape-sequence-widening
      first′ second′ composition′) =
  compose-result-unique composition
    (imprecision-composition-shape-transport
      (cast-shape-result-unique first first′)
      (cast-shape-result-unique second second′)
      refl composition′)
cast-shape-result-unique
    (shape-sequence-narrowing
      first second composition)
    (shape-sequence-narrowing
      first′ second′ composition′) =
  compose-result-unique composition
    (imprecision-composition-shape-transport
      (cast-shape-result-unique second second′)
      (cast-shape-result-unique first first′)
      refl composition′)


⊑ᵖ-ground-right :
  ∀ {Φ Δᴸ Δᴿ A H} →
  T.Ground H →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ H ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ
⊑ᵖ-ground-right gH (quotientᵖ A≈A′ A′⊑H′ H′≈H)
    with ≈∀-ground-right-eq gH H′≈H
⊑ᵖ-ground-right gH (quotientᵖ A≈A′ A′⊑H′ H′≈H) | refl =
  source-ground-≈∀-left gH A≈A′ A′⊑H′


⊑ᵖ-function-ground-right-composition :
  ∀ {Φ Δᴸ Δᴿ A A′ D s s′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ T.★ T.⇒ T.★ ⊣ Δᴿ) →
  s ；⌊ p ⌋≋ᵖ q ； s′ →
  s′ ≡ id★ˢ ↦ˢ id★ˢ →
  s ； ⌊ p ⌋ ≋ ⌊ ⊑ᵖ-ground-right T.★⇒★ q ⌋
⊑ᵖ-function-ground-right-composition
    (quotientᵖ source middle target)
    (quotient-boundary-square
      source-shape left-composition
      target-shape right-composition)
    final-shape
    with ≈∀-ground-right-eq T.★⇒★ target
⊑ᵖ-function-ground-right-composition
    (quotientᵖ source middle target)
    (quotient-boundary-square
      source-shape left-composition
      target-shape right-composition)
    final-shape
    | refl =
  source-ground-≈∀-left-composition
    T.★⇒★ source source-shape middle left-composition′
  where
  target-shape-equality =
    trans
      (function-ground-self-permutation-shape-equal target-shape)
      final-shape

  right-composition′ =
    imprecision-composition-shape-transport
      refl (sym target-shape-equality) refl right-composition

  result-equality =
    compose-result-unique right-composition′
      (function-ground-right-identity-composition middle)

  left-composition′ =
    imprecision-composition-shape-transport
      refl refl (sym result-equality) left-composition


id-only-no-seal :
  ∀ α → C.sealModeAllowed (C.id-onlyᵈ α) ≡ false
id-only-no-seal α = refl


gen-tag-or-id-no-seal :
  ∀ α →
  C.sealModeAllowed (C.genᵈ C.tag-or-idᵈ α) ≡ false
gen-tag-or-id-no-seal zero = refl
gen-tag-or-id-no-seal (suc α) = refl


false≢true : false ≡ true → ⊥
false≢true ()


cast-value-inert :
  ∀ {V c} →
  Value (V ⟨ c ⟩) →
  C.Inert c
cast-value-inert (vV ⟨ inert ⟩) = inert


inert-narrowing-target-var-no-seal :
  ∀ {μ Δ Σ d C α} →
  (∀ β → C.sealModeAllowed (μ β) ≡ false) →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C ⊒ T.＇ α →
  C.Inert d →
  ⊥
inert-narrowing-target-var-no-seal no-seal
    (_ , NW.cross ()) (G C.!)
inert-narrowing-target-var-no-seal no-seal
    (C.cast-seal hA α∈Σ ok , NW.sealⁿ A α) (C.seal A α) =
  false≢true (trans (sym (no-seal α)) ok)
inert-narrowing-target-var-no-seal no-seal
    (() , NW.cross (cʷ NW.↦ dⁿ)) (c C.↦ d)
inert-narrowing-target-var-no-seal no-seal
    (() , NW.cross (NW.`∀ cⁿ)) (C.`∀ c)
inert-narrowing-target-var-no-seal no-seal
    (() , NW.gen cⁿ) (C.gen A c)


inert-narrowing-target-base :
  ∀ {μ Δ Σ d C ι} →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C ⊒ T.‵ ι →
  C.Inert d →
  ⊥
inert-narrowing-target-base (_ , NW.cross ()) (G C.!)
inert-narrowing-target-base
    (() , NW.sealⁿ A α) (C.seal A α)
inert-narrowing-target-base
    (() , NW.cross (cʷ NW.↦ dⁿ)) (c C.↦ d)
inert-narrowing-target-base
    (() , NW.cross (NW.`∀ cⁿ)) (C.`∀ c)
inert-narrowing-target-base
    (() , NW.gen cⁿ) (C.gen A c)


inert-function-ground-narrowing-source :
  ∀ {μ Δ Σ C c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊒ (T.★ T.⇒ T.★) →
  C.Inert c →
  C ≡ T.★ T.⇒ T.★
inert-function-ground-narrowing-source
    (() , NW.cross (NW.id-＇ α)) inert
inert-function-ground-narrowing-source
    (() , NW.cross (NW.id-‵ ι)) inert
inert-function-ground-narrowing-source
    (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) (s C.↦ t)
    with NWP.widening-source-star-target-star (s⊢ , sʷ)
       | NWP.narrowing-target-star-source-star (t⊢ , tⁿ)
inert-function-ground-narrowing-source
    (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) (s C.↦ t)
    | refl | refl =
  refl
inert-function-ground-narrowing-source
    (() , NW.cross (NW.`∀ tⁿ)) inert
inert-function-ground-narrowing-source (c⊢ , NW.id★) ()
inert-function-ground-narrowing-source (() , NW.gen tⁿ) inert
inert-function-ground-narrowing-source (c⊢ , NW.untag gG) ()
inert-function-ground-narrowing-source (c⊢ , gG NW.？︔ tⁿ) ()
inert-function-ground-narrowing-source (() , NW.sealⁿ A α) inert
inert-function-ground-narrowing-source (c⊢ , sⁿ NW.︔seal α) ()


star-narrowing-shape :
  ∀ {μ Δ Σ c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ T.★ ⊒ T.★ →
  narrowing ⊢ᶜ c ⦂ id★ˢ
star-narrowing-shape (() , NW.cross (NW.id-＇ α))
star-narrowing-shape (() , NW.cross (NW.id-‵ ι))
star-narrowing-shape (() , NW.cross (sʷ NW.↦ tⁿ))
star-narrowing-shape (() , NW.cross (NW.`∀ tⁿ))
star-narrowing-shape (c⊢ , NW.id★) = shape-id-star
star-narrowing-shape (() , NW.gen tⁿ)
star-narrowing-shape
    (C.cast-untag hG () tag-ok , NW.untag gG)
star-narrowing-shape
    (C.cast-seq (C.cast-untag hG gG⊢ tag-ok) t⊢ ,
     gG NW.？︔ tⁿ) =
  ⊥-elim
    (NWP.narrowing-cross-ground-target-star⊥
      gG⊢ (t⊢ , NW.strictCrossⁿ→cross tⁿ))
star-narrowing-shape (() , NW.sealⁿ A α)
star-narrowing-shape
    (C.cast-seq s⊢ () , sⁿ NW.︔seal α)
star-narrowing-shape
    (C.cast-seq c⊢ () , NW.fun-untag-gen safe)


star-widening-shape :
  ∀ {μ Δ Σ c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ T.★ ⊑ T.★ →
  widening ⊢ᶜ c ⦂ id★ˢ
star-widening-shape (() , NW.cross (NW.id-＇ α))
star-widening-shape (() , NW.cross (NW.id-‵ ι))
star-widening-shape (() , NW.cross (sⁿ NW.↦ tʷ))
star-widening-shape (() , NW.cross (NW.`∀ tʷ))
star-widening-shape (c⊢ , NW.id★) = shape-id-star
star-widening-shape (() , NW.inst tʷ)
star-widening-shape
    (C.cast-tag hG () tag-ok , NW.tag gG)
star-widening-shape
    (C.cast-seq s⊢ (C.cast-tag hG gG⊢ tag-ok) ,
     sʷ NW.︔ gG !) =
  ⊥-elim
    (NWP.widening-cross-ground-source-star⊥
      gG⊢ (s⊢ , NW.strictCrossʷ→cross sʷ))
star-widening-shape (() , NW.unsealʷ α A)
star-widening-shape
    (C.cast-seq () t⊢ , NW.unseal︔_ α tʷ)
star-widening-shape
    (C.cast-seq () d⊢ , NW.inst-fun-tag safe)


inert-function-ground-narrowing-shape :
  ∀ {μ Δ Σ C c} →
  (c⊒ : μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊒ (T.★ T.⇒ T.★)) →
  C.Inert c →
  narrowing ⊢ᶜ c ⦂ (id★ˢ ↦ˢ id★ˢ)
inert-function-ground-narrowing-shape
    (() , NW.cross (NW.id-＇ α)) inert
inert-function-ground-narrowing-shape
    (() , NW.cross (NW.id-‵ ι)) inert
inert-function-ground-narrowing-shape
    (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) (s C.↦ t)
    with NWP.widening-source-star-target-star (s⊢ , sʷ)
       | NWP.narrowing-target-star-source-star (t⊢ , tⁿ)
inert-function-ground-narrowing-shape
    (C.cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) (s C.↦ t)
    | refl | refl =
  shape-fun
    (star-widening-shape (s⊢ , sʷ))
    (star-narrowing-shape (t⊢ , tⁿ))
inert-function-ground-narrowing-shape
    (() , NW.cross (NW.`∀ tⁿ)) inert
inert-function-ground-narrowing-shape (c⊢ , NW.id★) ()
inert-function-ground-narrowing-shape (() , NW.gen tⁿ) inert
inert-function-ground-narrowing-shape
    (c⊢ , NW.untag gG) ()
inert-function-ground-narrowing-shape
    (c⊢ , gG NW.？︔ tⁿ) ()
inert-function-ground-narrowing-shape
    (() , NW.sealⁿ A α) inert
inert-function-ground-narrowing-shape
    (c⊢ , sⁿ NW.︔seal α) ()

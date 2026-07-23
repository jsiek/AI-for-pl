module proof.NuImprecisionTargetGroundValueQuotientEliminationProof where

-- File Charter:
--   * Proves quotient elimination for values with a ground target endpoint.
--   * Handles source-side adjacent-forall permutations with local transport.
--   * Exposes no intermediate carrier, view, or unrestricted dequotienting API.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_; refl)
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
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( leftStoreⁱ
  ; rightStoreⁱ
  ; seal★-tag-or-id
  )
open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; down⊑downᵀ
  ; gen-down⊑gen-downᵀ
  ; seal★-gen-tag-or-id
  ; ⊑cast⊒ᵀ
  )
open import TermTyping using (cast-gen; cast-tag-or-id)
import Types as T
open import proof.ForallPermutationProperties using
  ( ≈∀-ground-right-eq
  ; renameᵗ-swap01-involutive
  ; swap01-involutive
  ; swap01-pres-<
  )
import proof.NarrowWidenProperties as NWP
open import
  proof.NuImprecisionTargetGroundValueQuotientEliminationDef using
  (TargetGroundValueQuotientEliminationᵀ)
open import proof.TypeProperties using
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


private
  ⊑ᵖ-ground-right :
    ∀ {Φ Δᴸ Δᴿ A H} →
    T.Ground H →
    Φ ∣ Δᴸ ⊢ A ⊑ᵖ H ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ
  ⊑ᵖ-ground-right gH (quotientᵖ A≈A′ A′⊑H′ H′≈H)
      with ≈∀-ground-right-eq gH H′≈H
  ⊑ᵖ-ground-right gH (quotientᵖ A≈A′ A′⊑H′ H′≈H) | refl =
    source-ground-≈∀-left gH A≈A′ A′⊑H′


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
    (C.cast-seal hA α∈Σ ok , narrowing) (C.seal A α) =
  false≢true (trans (sym (no-seal α)) ok)
inert-narrowing-target-var-no-seal no-seal
    (() , narrowing) (c C.↦ d)
inert-narrowing-target-var-no-seal no-seal
    (() , narrowing) (C.`∀ c)
inert-narrowing-target-var-no-seal no-seal
    (() , narrowing) (C.gen A c)


inert-narrowing-target-base :
  ∀ {μ Δ Σ d C ι} →
  μ ∣ Δ ∣ Σ ⊢ d ∶ C ⊒ T.‵ ι →
  C.Inert d →
  ⊥
inert-narrowing-target-base (_ , NW.cross ()) (G C.!)
inert-narrowing-target-base (() , narrowing) (C.seal A α)
inert-narrowing-target-base (() , narrowing) (c C.↦ d)
inert-narrowing-target-base (() , narrowing) (C.`∀ c)
inert-narrowing-target-base (() , narrowing) (C.gen A c)


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


target-ground-value-quotient-elimination-proofᵀ :
  TargetGroundValueQuotientEliminationᵀ
target-ground-value-quotient-elimination-proofᵀ
    (T.＇ α) vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim
    (inert-narrowing-target-var-no-seal
      id-only-no-seal
      d′⊒ (cast-value-inert vV′))
target-ground-value-quotient-elimination-proofᵀ
    (T.＇ α) vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim
    (inert-narrowing-target-var-no-seal
      gen-tag-or-id-no-seal
      d′⊒ (cast-value-inert vV′))
target-ground-value-quotient-elimination-proofᵀ
    (T.‵ ι) vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim (inert-narrowing-target-base d′⊒ (cast-value-inert vV′))
target-ground-value-quotient-elimination-proofᵀ
    (T.‵ ι) vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD) =
  ⊥-elim (inert-narrowing-target-base d′⊒ (cast-value-inert vV′))
target-ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD)
    with ⊑ᵖ-ground-right T.★⇒★ qD
       | inert-function-ground-narrowing-source
           d′⊒ (cast-value-inert vV′)
target-ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (down⊑downᵀ d⊒ d′⊒ M⊑M′ qD)
    | q | refl =
  q ,
  ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
    (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d′⊒)
    (cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d⊒) M⊑M′ q) q
target-ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
    with ⊑ᵖ-ground-right T.★⇒★ qD
       | inert-function-ground-narrowing-source
           d′⊒ (cast-value-inert vV′)
target-ground-value-quotient-elimination-proofᵀ
    T.★⇒★ vV vV′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD)
    | q | refl =
  q ,
  ⊑cast⊒ᵀ (cast-gen cast-tag-or-id) seal★-gen-tag-or-id d′⊒
    (cast⊒⊑ᵀ (cast-gen cast-tag-or-id) seal★-gen-tag-or-id
      d⊒ M⊑M′ q) q

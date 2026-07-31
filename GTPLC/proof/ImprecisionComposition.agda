module proof.ImprecisionComposition where

-- File Charter:
--   * Composes one-context GTPLC narrowing and widening bundles.
--   * Normalizes composition structurally through every constructor.
--   * Retains only canonical tag, untag, seal, and unseal sequences.
--   * Uses well-founded recursion over the total coercion size.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; s≤s; zero; suc)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  ( +-assoc
  ; +-comm
  ; +-monoˡ-<
  ; +-monoʳ-<
  ; +-monoˡ-≤
  ; +-monoʳ-≤
  ; m≤m+n
  ; m≤n+m
  ; n<1+n
  ; n≤1+n
  ; ≤-<-trans
  ; ≤-refl
  ; ≤-trans
  )
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst; sym)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden
open import proof.ImprecisionModeWeakening using
  ( ext-gen-incl
  ; ext-inst-incl
  ; weakenⁿ
  ; weakenʷ
  )
open import proof.ImprecisionRenaming using (⇑ⁿ-gen; ⇑ʷ-inst)
open import proof.TyStore using (∈-⟰ᵗ-inv; ∈-⟰ᵗ-zero)
open import proof.TypeInTypeSubst using (rename-preserves-∈ᵗ)

------------------------------------------------------------------------
-- Store weakening
------------------------------------------------------------------------

StoreIncl : TyStore → TyStore → Set
StoreIncl Σ Π = ∀ {X A} → (X , A) ∈ Σ → (X , A) ∈ Π

∈-⟰ᵗ : ∀ {Σ X A}
  → (X , A) ∈ Σ
  → (suc X , ⇑ᵗ A) ∈ ⟰ᵗ Σ
∈-⟰ᵗ (here refl) = here refl
∈-⟰ᵗ (there X,A∈Σ) = there (∈-⟰ᵗ X,A∈Σ)

shift-incl : ∀ {Σ Π}
  → StoreIncl Σ Π
  → StoreIncl (⟰ᵗ Σ) (⟰ᵗ Π)
shift-incl incl {X = suc X} X,A∈Σ with ∈-⟰ᵗ-inv X,A∈Σ
shift-incl incl {X = suc X} X,A∈Σ | A , refl , X,A∈Σ′ =
  ∈-⟰ᵗ (incl X,A∈Σ′)
shift-incl incl {X = zero} X,A∈Σ = ⊥-elim (∈-⟰ᵗ-zero X,A∈Σ)

bind-incl : ∀ {Σ Π}
  → StoreIncl Σ Π
  → StoreIncl ((zero , ★) ∷ ⟰ᵗ Σ) ((zero , ★) ∷ ⟰ᵗ Π)
bind-incl incl (here refl) = here refl
bind-incl incl (there X,A∈Σ) = there (shift-incl incl X,A∈Σ)

mutual

  weaken-storeʷ : ∀ {μ Δ Σ Π c A B}
    → StoreIncl Σ Π
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → μ ∣ Δ ∣ Π ⊢ c ⦂ A ⊑ B
  weaken-storeʷ incl (idᵃ a hA) = idᵃ a hA
  weaken-storeʷ incl (p ↦ q) =
    weaken-storeⁿ incl p ↦ weaken-storeʷ incl q
  weaken-storeʷ incl (∀ʷ p) = ∀ʷ (weaken-storeʷ (shift-incl incl) p)
  weaken-storeʷ incl (tag G hG allowed G꞉A) =
    tag G hG allowed G꞉A
  weaken-storeʷ incl (tag-seq G p hG allowed G꞉B A≢B) =
    tag-seq G (weaken-storeʷ incl p) hG allowed G꞉B A≢B
  weaken-storeʷ incl (unseal X<Δ hA X,A∈Σ allowed) =
    unseal X<Δ hA (incl X,A∈Σ) allowed
  weaken-storeʷ incl (unseal-seq X<Δ X,A∈Σ allowed p A≢B) =
    unseal-seq X<Δ (incl X,A∈Σ) allowed
      (weaken-storeʷ incl p) A≢B
  weaken-storeʷ incl (inst nonvarA zero∈A hB p B≢★) =
    inst nonvarA zero∈A hB
      (weaken-storeʷ (bind-incl incl) p) B≢★

  weaken-storeⁿ : ∀ {μ Δ Σ Π c A B}
    → StoreIncl Σ Π
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → μ ∣ Δ ∣ Π ⊢ c ⦂ A ⊒ B
  weaken-storeⁿ incl (idᵃ a hA) = idᵃ a hA
  weaken-storeⁿ incl (p ↦ q) =
    weaken-storeʷ incl p ↦ weaken-storeⁿ incl q
  weaken-storeⁿ incl (∀ⁿ p) = ∀ⁿ (weaken-storeⁿ (shift-incl incl) p)
  weaken-storeⁿ incl (untag G hG allowed G꞉B) =
    untag G hG allowed G꞉B
  weaken-storeⁿ incl (untag-seq G hG allowed G꞉A p A≢B) =
    untag-seq G hG allowed G꞉A (weaken-storeⁿ incl p) A≢B
  weaken-storeⁿ incl (seal X<Δ hA X,A∈Σ allowed) =
    seal X<Δ hA (incl X,A∈Σ) allowed
  weaken-storeⁿ incl (seal-seq p X<Δ X,B∈Σ allowed A≢B) =
    seal-seq (weaken-storeⁿ incl p) X<Δ (incl X,B∈Σ) allowed A≢B
  weaken-storeⁿ incl (gen nonvarA zero∈A hB p B≢★) =
    gen nonvarA zero∈A hB
      (weaken-storeⁿ (shift-incl incl) p) B≢★

add-head : ∀ {Σ} → StoreIncl Σ ((zero , ★) ∷ Σ)
add-head X,A∈Σ = there X,A∈Σ

⇑ʷ-inst-head : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
      ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
⇑ʷ-inst-head p with ⇑ʷ-inst p
⇑ʷ-inst-head p | c , c⊑ = c , weaken-storeʷ add-head c⊑

ext-to-inst : ∀ {μ Δ Σ A B}
  → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ A ⊑ B
  → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ ⊢ A ⊑ B
ext-to-inst (c , c⊑) =
  c , weakenʷ ext-inst-incl (weaken-storeʷ add-head c⊑)

------------------------------------------------------------------------
-- Occurrence preservation away from store representations
------------------------------------------------------------------------

rename-member-inv : ∀ ρ {X A}
  → X ∈ᵗ renameᵗ ρ A
  → Σ[ Y ∈ TyVar ] (X ≡ ρ Y) × (Y ∈ᵗ A)
rename-member-inv ρ {A = ＇ Y} var-∈ = Y , refl , var-∈
rename-member-inv ρ {A = A ⇒ B} (∈-fun-left X∈A)
    with rename-member-inv ρ X∈A
rename-member-inv ρ {A = A ⇒ B} (∈-fun-left X∈A)
    | Y , eq , Y∈A = Y , eq , ∈-fun-left Y∈A
rename-member-inv ρ {A = A ⇒ B} (∈-fun-right X∈B)
    with rename-member-inv ρ X∈B
rename-member-inv ρ {A = A ⇒ B} (∈-fun-right X∈B)
    | Y , eq , Y∈B = Y , eq , ∈-fun-right Y∈B
rename-member-inv ρ {A = `∀ A} (∈-all X∈A)
    with rename-member-inv (extᵗ ρ) X∈A
rename-member-inv ρ {A = `∀ A} (∈-all X∈A)
    | zero , () , Y∈A
rename-member-inv ρ {A = `∀ A} (∈-all X∈A)
    | suc Y , refl , Y∈A = Y , refl , ∈-all Y∈A

StoreFresh : TyVar → TyStore → Set
StoreFresh X Σ = ∀ {Y A} → (Y , A) ∈ Σ → X ∈ᵗ A → ⊥

shift-fresh : ∀ {X Σ}
  → StoreFresh X Σ
  → StoreFresh (suc X) (⟰ᵗ Σ)
shift-fresh fresh {Y = zero} Y,A∈Σ Y∈A =
  ⊥-elim (∈-⟰ᵗ-zero Y,A∈Σ)
shift-fresh {X = X} fresh {Y = suc Y} Y,A∈Σ X∈A
    with ∈-⟰ᵗ-inv Y,A∈Σ
shift-fresh {X = X} fresh {Y = suc Y} Y,A∈Σ X∈A
    | A , refl , Y,A∈Σ′ with rename-member-inv suc X∈A
shift-fresh {X = X} fresh {Y = suc Y} Y,A∈Σ X∈A
    | A , refl , Y,A∈Σ′ | .X , refl , X∈A′ =
  fresh Y,A∈Σ′ X∈A′

zero-fresh-shift : ∀ {Σ} → StoreFresh zero (⟰ᵗ Σ)
zero-fresh-shift {Σ} {Y = zero} Y,A∈Σ zero∈A =
  ⊥-elim (∈-⟰ᵗ-zero Y,A∈Σ)
zero-fresh-shift {Σ} {Y = suc Y} Y,A∈Σ zero∈A
    with ∈-⟰ᵗ-inv Y,A∈Σ
zero-fresh-shift {Σ} {Y = suc Y} Y,A∈Σ zero∈A
    | A , refl , Y,A∈Σ′ with rename-member-inv suc zero∈A
zero-fresh-shift {Σ} {Y = suc Y} Y,A∈Σ zero∈A
    | A , refl , Y,A∈Σ′ | _ , () , _

bind-fresh : ∀ {X Σ}
  → StoreFresh X Σ
  → StoreFresh (suc X) ((zero , ★) ∷ ⟰ᵗ Σ)
bind-fresh fresh (here refl) ()
bind-fresh fresh (there Y,A∈Σ) X∈A = shift-fresh fresh Y,A∈Σ X∈A

mutual

  narrowing-member : ∀ {μ Δ Σ X c A B}
    → StoreFresh X Σ
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → X ∈ᵗ A
    → X ∈ᵗ B
  narrowing-member fresh (idᵃ a hA) X∈A = X∈A
  narrowing-member fresh (p ↦ q) (∈-fun-left X∈A) =
    ∈-fun-left (widening-member fresh p X∈A)
  narrowing-member fresh (p ↦ q) (∈-fun-right X∈B) =
    ∈-fun-right (narrowing-member fresh q X∈B)
  narrowing-member fresh (∀ⁿ p) (∈-all X∈A) =
    ∈-all (narrowing-member (shift-fresh fresh) p X∈A)
  narrowing-member fresh (untag G hG allowed G꞉B) ()
  narrowing-member fresh (untag-seq G hG allowed G꞉A p A≢B) ()
  narrowing-member fresh (seal X<Δ hA X,A∈Σ allowed) X∈A =
    ⊥-elim (fresh X,A∈Σ X∈A)
  narrowing-member fresh
      (seal-seq p X<Δ X,B∈Σ allowed A≢B) X∈A =
    ⊥-elim (fresh X,B∈Σ (narrowing-member fresh p X∈A))
  narrowing-member fresh
      (gen nonvarA zero∈A hB p B≢★) X∈B =
    ∈-all
      (narrowing-member (shift-fresh fresh) p
        (rename-preserves-∈ᵗ suc X∈B))

  widening-member : ∀ {μ Δ Σ X c A B}
    → StoreFresh X Σ
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → X ∈ᵗ B
    → X ∈ᵗ A
  widening-member fresh (idᵃ a hA) X∈A = X∈A
  widening-member fresh (p ↦ q) (∈-fun-left X∈A) =
    ∈-fun-left (narrowing-member fresh p X∈A)
  widening-member fresh (p ↦ q) (∈-fun-right X∈B) =
    ∈-fun-right (widening-member fresh q X∈B)
  widening-member fresh (∀ʷ p) (∈-all X∈A) =
    ∈-all (widening-member (shift-fresh fresh) p X∈A)
  widening-member fresh (tag G hG allowed G꞉A) ()
  widening-member fresh (tag-seq G p hG allowed G꞉B A≢B) ()
  widening-member fresh (unseal X<Δ hA X,A∈Σ allowed) X∈A =
    ⊥-elim (fresh X,A∈Σ X∈A)
  widening-member fresh
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B) X∈B =
    ⊥-elim (fresh X,A∈Σ (widening-member fresh p X∈B))
  widening-member fresh
      (inst nonvarA zero∈A hB p B≢★) X∈B =
    ∈-all
      (widening-member (bind-fresh fresh) p
        (rename-preserves-∈ᵗ suc X∈B))

narrowing-nonvar-member : ∀ {μ Δ Σ X c A B}
  → StoreFresh X Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → NonVar A
  → X ∈ᵗ A
  → NonVar B
narrowing-nonvar-member fresh (idᵃ (＇ Y) hA) () X∈A
narrowing-nonvar-member fresh (idᵃ (‵ iota) hA) nonvar-base ()
narrowing-nonvar-member fresh (idᵃ ★ hA) nonvar-star ()
narrowing-nonvar-member fresh (p ↦ q) nonvar-fun X∈A = nonvar-fun
narrowing-nonvar-member fresh (∀ⁿ p) nonvar-all X∈A = nonvar-all
narrowing-nonvar-member fresh (untag G hG allowed G꞉B) nonvar-star ()
narrowing-nonvar-member fresh
    (untag-seq G hG allowed G꞉A p A≢B) nonvar-star ()
narrowing-nonvar-member fresh
    (seal X<Δ hA X,A∈Σ allowed) nonvarA X∈A =
  ⊥-elim (fresh X,A∈Σ X∈A)
narrowing-nonvar-member fresh
    (seal-seq p X<Δ X,B∈Σ allowed A≢B) nonvarA X∈A =
  ⊥-elim (fresh X,B∈Σ (narrowing-member fresh p X∈A))
narrowing-nonvar-member fresh
    (gen nonvarB zero∈B hA p A≢★) nonvarA X∈A = nonvar-all

widening-nonvar-member : ∀ {μ Δ Σ X c A B}
  → StoreFresh X Σ
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → NonVar B
  → X ∈ᵗ B
  → NonVar A
widening-nonvar-member fresh (idᵃ (＇ Y) hA) () X∈A
widening-nonvar-member fresh (idᵃ (‵ iota) hA) nonvar-base ()
widening-nonvar-member fresh (idᵃ ★ hA) nonvar-star ()
widening-nonvar-member fresh (p ↦ q) nonvar-fun X∈A = nonvar-fun
widening-nonvar-member fresh (∀ʷ p) nonvar-all X∈A = nonvar-all
widening-nonvar-member fresh (tag G hG allowed G꞉A) nonvar-star ()
widening-nonvar-member fresh
    (tag-seq G p hG allowed G꞉B A≢B) nonvar-star ()
widening-nonvar-member fresh
    (unseal X<Δ hA X,A∈Σ allowed) nonvarA X∈A =
  ⊥-elim (fresh X,A∈Σ X∈A)
widening-nonvar-member fresh
    (unseal-seq X<Δ X,A∈Σ allowed p A≢B) nonvarB X∈B =
  ⊥-elim (fresh X,A∈Σ (widening-member fresh p X∈B))
widening-nonvar-member fresh
    (inst nonvarA zero∈A hB p B≢★) nonvarB X∈B = nonvar-all

------------------------------------------------------------------------
-- Fresh-variable exclusions at polymorphic boundaries
------------------------------------------------------------------------

head-star-unique : ∀ {Σ A}
  → (zero , A) ∈ ((zero , ★) ∷ ⟰ᵗ Σ)
  → A ≡ ★
head-star-unique (here refl) = refl
head-star-unique (there zero,A∈Σ) =
  ⊥-elim (∈-⟰ᵗ-zero zero,A∈Σ)

star-widening-variable⊥ : ∀ {μ Δ Σ c X}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ ★ ⊑ ＇ X
  → ⊥
star-widening-variable⊥ ()

shifted-variable-target-no-zero : ∀ {μ Δ Σ X c A}
  → μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ ＇ (suc X) ⊒ A
  → zero ∈ᵗ A
  → ⊥
shifted-variable-target-no-zero (idᵃ (＇ ._) hA) ()
shifted-variable-target-no-zero
    (seal {X = zero} X<Δ hA zero,A∈Σ allowed) var-∈ =
  ⊥-elim (∈-⟰ᵗ-zero zero,A∈Σ)
shifted-variable-target-no-zero
    (seal-seq {X = zero} p X<Δ zero,A∈Σ allowed A≢B) var-∈ =
  ⊥-elim (∈-⟰ᵗ-zero zero,A∈Σ)
shifted-variable-target-no-zero
    (gen nonvarA zero∈A hB p B≢★) zero∈∀A =
  shifted-variable-target-no-zero p zero∈A

inst-variable-source-no-zero : ∀ {μ Δ Σ X c A}
  → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
      ⊢ c ⦂ A ⊑ ＇ (suc X)
  → zero ∈ᵗ A
  → ⊥
inst-variable-source-no-zero (idᵃ (＇ ._) hA) ()
inst-variable-source-no-zero
    (unseal {X = zero} X<Δ hA zero,A∈Σ allowed) var-∈
    with head-star-unique zero,A∈Σ
inst-variable-source-no-zero
    (unseal {X = zero} X<Δ hA zero,A∈Σ allowed) var-∈ | ()
inst-variable-source-no-zero
    (unseal-seq {X = zero} X<Δ zero,A∈Σ allowed p A≢B) var-∈
    with head-star-unique zero,A∈Σ
inst-variable-source-no-zero
    (unseal-seq {X = zero} X<Δ zero,A∈Σ allowed p A≢B) var-∈
    | refl =
  star-widening-variable⊥ p
inst-variable-source-no-zero
    (inst nonvarA zero∈A hB p B≢★) zero∈∀A =
  inst-variable-source-no-zero p zero∈A

------------------------------------------------------------------------
-- Termination measure for structural composition
------------------------------------------------------------------------

sizeᶜ : Coercion → ℕ
sizeᶜ id = suc zero
sizeᶜ (c ︔ d) = suc (sizeᶜ c + sizeᶜ d)
sizeᶜ (c ↦ d) = suc (sizeᶜ c + sizeᶜ d)
sizeᶜ (`∀ c) = suc (sizeᶜ c)
sizeᶜ (G !) = suc zero
sizeᶜ (G ？) = suc zero
sizeᶜ (seal X) = suc zero
sizeᶜ (unseal X) = suc zero
sizeᶜ (gen c) = suc (sizeᶜ c)
sizeᶜ (inst c) = suc (sizeᶜ c)
sizeᶜ error = suc zero

sizeᶜ-renameᶜ : ∀ ρ c → sizeᶜ (renameᶜ ρ c) ≡ sizeᶜ c
sizeᶜ-renameᶜ ρ id = refl
sizeᶜ-renameᶜ ρ (c ︔ d) =
  cong suc (cong₂ _+_ (sizeᶜ-renameᶜ ρ c) (sizeᶜ-renameᶜ ρ d))
sizeᶜ-renameᶜ ρ (c ↦ d) =
  cong suc (cong₂ _+_ (sizeᶜ-renameᶜ ρ c) (sizeᶜ-renameᶜ ρ d))
sizeᶜ-renameᶜ ρ (`∀ c) = cong suc (sizeᶜ-renameᶜ (extᵗ ρ) c)
sizeᶜ-renameᶜ ρ (G !) = refl
sizeᶜ-renameᶜ ρ (G ？) = refl
sizeᶜ-renameᶜ ρ (seal X) = refl
sizeᶜ-renameᶜ ρ (unseal X) = refl
sizeᶜ-renameᶜ ρ (gen c) =
  cong suc (sizeᶜ-renameᶜ (extᵗ ρ) c)
sizeᶜ-renameᶜ ρ (inst c) =
  cong suc (sizeᶜ-renameᶜ (extᵗ ρ) c)
sizeᶜ-renameᶜ ρ error = refl

sizeᶜ-⇑ᶜ : ∀ c → sizeᶜ (⇑ᶜ c) ≡ sizeᶜ c
sizeᶜ-⇑ᶜ = sizeᶜ-renameᶜ suc

arrow-left-≤ : ∀ a b c d → c + a ≤ (a + b) + suc (c + d)
arrow-left-≤ a b c d = ≤-trans c+a≤a+c a+c≤target
  where
  c≤target : c ≤ b + suc (c + d)
  c≤target =
    ≤-trans (m≤m+n c d)
      (≤-trans (n≤1+n (c + d)) (m≤n+m (suc (c + d)) b))

  a+c≤target : a + c ≤ (a + b) + suc (c + d)
  a+c≤target =
    subst (a + c ≤_) (sym (+-assoc a b (suc (c + d))))
      (+-monoʳ-≤ a c≤target)

  c+a≤a+c : c + a ≤ a + c
  c+a≤a+c = subst (c + a ≤_) (+-comm c a) ≤-refl

arrow-right-≤ : ∀ a b c d → b + d ≤ (a + b) + suc (c + d)
arrow-right-≤ a b c d = ≤-trans b+d≤inner b+d≤target
  where
  d≤inner : d ≤ suc (c + d)
  d≤inner = ≤-trans (m≤n+m d c) (n≤1+n (c + d))

  b+d≤inner : b + d ≤ b + suc (c + d)
  b+d≤inner = +-monoʳ-≤ b d≤inner

  b+d≤target : b + suc (c + d) ≤ (a + b) + suc (c + d)
  b+d≤target =
    subst (b + suc (c + d) ≤_) (sym (+-assoc a b (suc (c + d))))
      (m≤n+m (b + suc (c + d)) a)

left-seq-≤ : ∀ a b e → a + e ≤ (b + a) + e
left-seq-≤ a b e = +-monoˡ-≤ e (m≤n+m a b)

right-seq-< : ∀ a b e → a + b < a + suc (b + e)
right-seq-< a b e =
  ≤-<-trans (+-monoʳ-≤ a (m≤m+n b e))
    (+-monoʳ-< a (n<1+n (b + e)))

fun-left-< : ∀ a b c d → c + a < suc (a + b) + suc (c + d)
fun-left-< a b c d = s≤s (arrow-left-≤ a b c d)

fun-right-< : ∀ a b c d → b + d < suc (a + b) + suc (c + d)
fun-right-< a b c d = s≤s (arrow-right-≤ a b c d)

drop-both-< : ∀ a b → a + b < suc a + suc b
drop-both-< a b = s≤s (+-monoʳ-≤ a (n≤1+n b))

drop-left-< : ∀ a b → a + b < suc a + b
drop-left-< a b = n<1+n (a + b)

drop-right-< : ∀ a b → a + b < a + suc b
drop-right-< a b = +-monoʳ-< a (n<1+n b)

keep-left-drop-right-< : ∀ a b → suc a + b < suc a + suc b
keep-left-drop-right-< a b = +-monoʳ-< (suc a) (n<1+n b)

drop-left-keep-right-< : ∀ a b → a + suc b < suc a + suc b
drop-left-keep-right-< a b = n<1+n (a + suc b)

left-seq-drop-< : ∀ a b e → a + e < suc (b + a) + e
left-seq-drop-< a b e = s≤s (left-seq-≤ a b e)

shift-left-drop-right-< : ∀ c d
  → sizeᶜ (⇑ᶜ c) + sizeᶜ d < sizeᶜ c + suc (sizeᶜ d)
shift-left-drop-right-< c d =
  subst (λ n → n + sizeᶜ d < sizeᶜ c + suc (sizeᶜ d))
    (sym (sizeᶜ-⇑ᶜ c)) (drop-right-< (sizeᶜ c) (sizeᶜ d))

drop-left-shift-right-< : ∀ c d
  → sizeᶜ c + sizeᶜ (⇑ᶜ d) < suc (sizeᶜ c) + sizeᶜ d
drop-left-shift-right-< c d =
  subst (λ n → sizeᶜ c + n < suc (sizeᶜ c) + sizeᶜ d)
    (sym (sizeᶜ-⇑ᶜ d)) (drop-left-< (sizeᶜ c) (sizeᶜ d))

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

infixl 6 _⨟ⁿ_
infixl 6 _⨟ʷ_

mutual

  composeⁿ : ∀ {μ Δ Σ c d A B C}
    → (p : μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B)
    → (q : μ ∣ Δ ∣ Σ ⊢ d ⦂ B ⊒ C)
    → Acc _<_ (sizeᶜ c + sizeᶜ d)
    → μ ∣ Δ ∣ Σ ⊢ A ⊒ C
  composeⁿ (idᵃ a hA) q access = _ , q
  composeⁿ p (idᵃ a hB) access = _ , p
  composeⁿ {c = c ↦ d} {d = e ↦ f}
      (p₁ ↦ p₂) (q₁ ↦ q₂) (acc rec)
      with composeʷ q₁ p₁
             (rec (fun-left-< (sizeᶜ c) (sizeᶜ d)
                     (sizeᶜ e) (sizeᶜ f)))
         | composeⁿ p₂ q₂
             (rec (fun-right-< (sizeᶜ c) (sizeᶜ d)
                     (sizeᶜ e) (sizeᶜ f)))
  composeⁿ (p₁ ↦ p₂) (q₁ ↦ q₂) (acc rec)
      | g , r₁ | h , r₂ =
    (g ↦ h) , (r₁ ↦ r₂)
  composeⁿ {c = `∀ c} {d = `∀ d} (∀ⁿ p) (∀ⁿ q) (acc rec)
      with composeⁿ p q (rec (drop-both-< (sizeᶜ c) (sizeᶜ d)))
  composeⁿ (∀ⁿ p) (∀ⁿ q) (acc rec)
      | e , r =
    `∀ e , ∀ⁿ r
  composeⁿ (untag G hG allowed G꞉B) q access =
    wrap-untag hG allowed G꞉B q
  composeⁿ {c = (G ？) ︔ c} {d = d}
      (untag-seq G hG allowed G꞉B p B≢C) q (acc rec)
      with composeⁿ p q
        (rec (left-seq-drop-< (sizeᶜ c) (sizeᶜ (G ？)) (sizeᶜ d)))
  composeⁿ (untag-seq G hG allowed G꞉B p B≢C) q (acc rec)
      | d , r =
    wrap-untag hG allowed G꞉B r
  composeⁿ p (seal X<Δ hB X,B∈Σ allowed) access =
    wrap-seal p X<Δ X,B∈Σ allowed
  composeⁿ {c = c} {d = d ︔ seal X}
      p (seal-seq q X<Δ X,C∈Σ allowed B≢C) (acc rec)
      with composeⁿ p q
        (rec (right-seq-< (sizeᶜ c) (sizeᶜ d) (sizeᶜ (seal X))))
  composeⁿ p (seal-seq q X<Δ X,C∈Σ allowed B≢C) (acc rec)
      | d , r =
    wrap-seal r X<Δ X,C∈Σ allowed
  composeⁿ (seal X<Δ hA X,A∈Σ allowed)
      (gen nonvarC zero∈C hB q B≢★) access =
    ⊥-elim (shifted-variable-target-no-zero q zero∈C)
  composeⁿ (seal-seq p X<Δ X,A∈Σ allowed B≢A)
      (gen nonvarC zero∈C hB q A≢★) access =
    ⊥-elim (shifted-variable-target-no-zero q zero∈C)
  composeⁿ {c = c ↦ d} {d = gen e}
      (p₁ ↦ p₂) (gen nonvarC zero∈C hB q B≢★) (acc rec)
      with composeⁿ (proj₂ (⇑ⁿ-gen ((c ↦ d) , (p₁ ↦ p₂)))) q
        (rec (shift-left-drop-right-< (c ↦ d) e))
  composeⁿ {c = c ↦ d} {d = gen e}
      (p₁ ↦ p₂) (gen nonvarC zero∈C hB q B≢★) (acc rec)
      | f , r =
    gen f , gen nonvarC zero∈C
      (⊒-src-wf (p₁ ↦ p₂)) r (λ ())
  composeⁿ {c = `∀ c} {d = gen e}
      (∀ⁿ p) (gen nonvarC zero∈C hB q B≢★) (acc rec)
      with composeⁿ (proj₂ (⇑ⁿ-gen (`∀ c , ∀ⁿ p))) q
        (rec (shift-left-drop-right-< (`∀ c) e))
  composeⁿ {c = `∀ c} {d = gen e}
      (∀ⁿ p) (gen nonvarC zero∈C hB q B≢★) (acc rec)
      | f , r =
    gen f , gen nonvarC zero∈C (wf∀ (⊒-src-wf p)) r (λ ())
  composeⁿ {c = gen c} {d = gen d}
      (gen nonvarB zero∈B hA p A≢★)
      (gen nonvarC zero∈C hB q B≢★) (acc rec)
      with composeⁿ
        (proj₂ (⇑ⁿ-gen (gen c , gen nonvarB zero∈B hA p A≢★))) q
        (rec (shift-left-drop-right-< (gen c) d))
  composeⁿ {c = gen c} {d = gen d}
      (gen nonvarB zero∈B hA p A≢★)
      (gen nonvarC zero∈C hB q B≢★) (acc rec)
      | e , r =
    gen e , gen nonvarC zero∈C hA r A≢★
  composeⁿ {c = gen c} {d = `∀ d}
      (gen nonvarB zero∈B hA p A≢★) (∀ⁿ q) (acc rec)
      with composeⁿ p (weakenⁿ ext-gen-incl q)
        (rec (drop-both-< (sizeᶜ c) (sizeᶜ d)))
  composeⁿ (gen nonvarB zero∈B hA p A≢★) (∀ⁿ q) (acc rec)
      | f , r =
    gen f , gen nonvarC zero∈C hA r A≢★
    where
    zero∈C = narrowing-member zero-fresh-shift q zero∈B
    nonvarC =
      narrowing-nonvar-member zero-fresh-shift q nonvarB zero∈B

  composeʷ : ∀ {μ Δ Σ c d A B C}
    → (p : μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B)
    → (q : μ ∣ Δ ∣ Σ ⊢ d ⦂ B ⊑ C)
    → Acc _<_ (sizeᶜ c + sizeᶜ d)
    → μ ∣ Δ ∣ Σ ⊢ A ⊑ C
  composeʷ (idᵃ a hA) q access = _ , q
  composeʷ p (idᵃ a hB) access = _ , p
  composeʷ {c = c ↦ d} {d = e ↦ f}
      (p₁ ↦ p₂) (q₁ ↦ q₂) (acc rec)
      with composeⁿ q₁ p₁
             (rec (fun-left-< (sizeᶜ c) (sizeᶜ d)
                     (sizeᶜ e) (sizeᶜ f)))
         | composeʷ p₂ q₂
             (rec (fun-right-< (sizeᶜ c) (sizeᶜ d)
                     (sizeᶜ e) (sizeᶜ f)))
  composeʷ (p₁ ↦ p₂) (q₁ ↦ q₂) (acc rec)
      | g , r₁ | h , r₂ =
    (g ↦ h) , (r₁ ↦ r₂)
  composeʷ {c = `∀ c} {d = `∀ d} (∀ʷ p) (∀ʷ q) (acc rec)
      with composeʷ p q (rec (drop-both-< (sizeᶜ c) (sizeᶜ d)))
  composeʷ (∀ʷ p) (∀ʷ q) (acc rec)
      | e , r =
    `∀ e , ∀ʷ r
  composeʷ (unseal X<Δ hA X,A∈Σ allowed) q access =
    wrap-unseal X<Δ X,A∈Σ allowed q
  composeʷ {c = unseal X ︔ c} {d = d}
      (unseal-seq X<Δ X,A∈Σ allowed p A≢B) q (acc rec)
      with composeʷ p q
        (rec (left-seq-drop-< (sizeᶜ c) (sizeᶜ (unseal X)) (sizeᶜ d)))
  composeʷ (unseal-seq X<Δ X,A∈Σ allowed p A≢B) q (acc rec)
      | d , r =
    wrap-unseal X<Δ X,A∈Σ allowed r
  composeʷ p (tag G hG allowed G꞉B) access =
    wrap-tag p hG allowed G꞉B
  composeʷ {c = c} {d = d ︔ (G !)}
      p (tag-seq G q hG allowed G꞉C B≢C) (acc rec)
      with composeʷ p q
        (rec (right-seq-< (sizeᶜ c) (sizeᶜ d) (sizeᶜ (G !))))
  composeʷ p (tag-seq G q hG allowed G꞉C B≢C) (acc rec)
      | d , r =
    wrap-tag r hG allowed G꞉C
  composeʷ {c = `∀ c} {d = inst d}
      (∀ʷ p) (inst nonvarB zero∈B hC q C≢★) (acc rec)
      with composeʷ (proj₂ (ext-to-inst (c , p))) q
        (rec (drop-both-< (sizeᶜ c) (sizeᶜ d)))
  composeʷ {c = `∀ c} {d = inst d}
      (∀ʷ p) (inst nonvarB zero∈B hC q C≢★) (acc rec)
      | e , r =
    inst e , inst nonvarA zero∈A hC r C≢★
    where
    zero∈A = widening-member zero-fresh-shift p zero∈B
    nonvarA =
      widening-nonvar-member zero-fresh-shift p nonvarB zero∈B
  composeʷ {c = inst c} {d = d ↦ e}
      (inst nonvarA zero∈A hB p B≢★) (q₁ ↦ q₂) (acc rec)
      with composeʷ p (proj₂ (⇑ʷ-inst-head ((d ↦ e) , (q₁ ↦ q₂))))
        (rec (drop-left-shift-right-< c (d ↦ e)))
  composeʷ {c = inst c} {d = d ↦ e}
      (inst nonvarA zero∈A hB p B≢★) (q₁ ↦ q₂) (acc rec)
      | f , r =
    inst f , inst nonvarA zero∈A
      (⊑-tgt-wf (q₁ ↦ q₂)) r (λ ())
  composeʷ {c = inst c} {d = `∀ d}
      (inst nonvarA zero∈A hB p B≢★) (∀ʷ q) (acc rec)
      with composeʷ p (proj₂ (⇑ʷ-inst-head (`∀ d , ∀ʷ q)))
        (rec (drop-left-shift-right-< c (`∀ d)))
  composeʷ {c = inst c} {d = `∀ d}
      (inst nonvarA zero∈A hB p B≢★) (∀ʷ q) (acc rec)
      | e , r =
    inst e , inst nonvarA zero∈A
      (wf∀ (⊑-tgt-wf q)) r (λ ())
  composeʷ {c = inst c} {d = inst d}
      (inst nonvarA zero∈A hB p B≢★)
      (inst nonvarC zero∈C hD q C≢★) (acc rec)
      with composeʷ p
        (proj₂ (⇑ʷ-inst-head
          (inst d , inst nonvarC zero∈C hD q C≢★)))
        (rec (drop-left-shift-right-< c (inst d)))
  composeʷ {c = inst c} {d = inst d}
      (inst nonvarA zero∈A hB p B≢★)
      (inst nonvarC zero∈C hD q C≢★) (acc rec)
      | e , r =
    inst e , inst nonvarA zero∈A hD r C≢★
  composeʷ (inst nonvarA zero∈A hB p B≢★)
      (unseal X<Δ hC X,C∈Σ allowed) access =
    ⊥-elim (inst-variable-source-no-zero p zero∈A)
  composeʷ (inst nonvarA zero∈A hB p B≢★)
      (unseal-seq X<Δ X,C∈Σ allowed q C≢D) access =
    ⊥-elim (inst-variable-source-no-zero p zero∈A)

_⨟ⁿ_ : ∀ {μ Δ Σ A B C}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊒ C
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ C
(c , p) ⨟ⁿ (d , q) = composeⁿ p q (<-wellFounded (sizeᶜ c + sizeᶜ d))

_⨟ʷ_ : ∀ {μ Δ Σ A B C}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊑ C
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ C
(c , p) ⨟ʷ (d , q) = composeʷ p q (<-wellFounded (sizeᶜ c + sizeᶜ d))

------------------------------------------------------------------------
-- Equality of bundled coercions
------------------------------------------------------------------------

infix 4 _≐ⁿ_
infix 4 _≐ʷ_

_≐ⁿ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → Set
p ≐ⁿ q = proj₁ p ≡ proj₁ q

_≐ʷ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → Set
p ≐ʷ q = proj₁ p ≡ proj₁ q

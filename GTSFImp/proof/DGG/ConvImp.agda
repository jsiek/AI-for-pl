module proof.DGG.ConvImp where

-- File Charter:
--   * Occurrence transport along the pivot-indexed conversion typing
--     _⊢↑[_]_ / _⊢↓[_]_ of proof.DGG.CastTermImprecision2.
--   * A conversion pivoted at just X only rewrites occurrences of X,
--     so any other variable Y occurs in one endpoint iff it occurs in
--     the other, provided Y avoids the store representation of the
--     pivot.  A conversion with pivot nothing is identity-shaped and
--     its endpoints are equal outright.
--   * Transports both the occurrence relation _∈ᵗ_ and its complement
--     _∉ᵗ_, in both directions, because _∈ᵗ_'s function-range
--     constructor carries a _∉ᵗ_ witness for the domain and because
--     the domain component of an arrow conversion flips direction.
--   * Arrow conversions join their components' pivots with PivotJoin;
--     a component at pivot nothing transports by its endpoint equality
--     instead of by recursion.
--   * Specializes the transport to the ∀-binder, where the pivot is a
--     shifted variable and the transported variable is zero.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Types
open import TyStore using (TyStore; store-lift; _∋_⦂_; S-lift∋)
open import Conversion using
  (Conv↑; Conv↓; unseal; _↦↑_; `∀↑_; id↑; seal; _↦↓_; `∀↓_; id↓)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (_⊢↑[_]_; _⊢↓[_]_;
   ⊢↑-unsealˣ; ⊢↑-⇒ˣ; ⊢↑-∀ˣ; ⊢↑-∀-idˣ; ⊢↑-idˣ;
   ⊢↓-sealˣ; ⊢↓-⇒ˣ; ⊢↓-∀ˣ; ⊢↓-∀-idˣ; ⊢↓-idˣ;
   PivotJoin; join-none; join-left; join-right; join-both)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; shift-not-occurs; zero-absent-shift)

------------------------------------------------------------------------
-- Occurrence and non-occurrence are contradictory
------------------------------------------------------------------------

occurs-absent-⊥ : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∈ᵗ A
  → X ∉ᵗ A
    ---------
  → ⊥
occurs-absent-⊥ var-∈ (∉-var X≢X) = ≢ᶠ→≢ X≢X refl
occurs-absent-⊥ (∈-fun-left X∈A) (∉-fun X∉A X∉B) =
  occurs-absent-⊥ X∈A X∉A
occurs-absent-⊥ (∈-fun-right X∉A′ X∈B) (∉-fun X∉A X∉B) =
  occurs-absent-⊥ X∈B X∉B
occurs-absent-⊥ (∈-all X∈A) (∉-all X∉A) =
  occurs-absent-⊥ X∈A X∉A

occurs-cast : ∀ {Δ} {Y : TyVar Δ} {A B : Ty Δ}
  → A ≡ B
  → Y ∈ᵗ A
    -------
  → Y ∈ᵗ B
occurs-cast refl Y∈A = Y∈A

absent-cast : ∀ {Δ} {Y : TyVar Δ} {A B : Ty Δ}
  → A ≡ B
  → Y ∉ᵗ A
    -------
  → Y ∉ᵗ B
absent-cast refl Y∉A = Y∉A

------------------------------------------------------------------------
-- Identity-pivot conversions do not change the type
------------------------------------------------------------------------

pivot-id-endpoints↑ : ∀ {Δ} {Σ : TyStore Δ} {A B : Ty Δ}
    {c : Conv↑ Δ A B}
  → Σ ⊢↑[ nothing ] c
    ------------------
  → A ≡ B

pivot-id-endpoints↓ : ∀ {Δ} {Σ : TyStore Δ} {A B : Ty Δ}
    {c : Conv↓ Δ A B}
  → Σ ⊢↓[ nothing ] c
    ------------------
  → A ≡ B

pivot-id-endpoints↑ (⊢↑-⇒ˣ join-none ⊢c ⊢d) =
  cong₂ _⇒_ (sym (pivot-id-endpoints↓ ⊢c)) (pivot-id-endpoints↑ ⊢d)
pivot-id-endpoints↑ (⊢↑-∀-idˣ ⊢c) =
  cong `∀ (pivot-id-endpoints↑ ⊢c)
pivot-id-endpoints↑ ⊢↑-idˣ = refl

pivot-id-endpoints↓ (⊢↓-⇒ˣ join-none ⊢c ⊢d) =
  cong₂ _⇒_ (sym (pivot-id-endpoints↑ ⊢c)) (pivot-id-endpoints↓ ⊢d)
pivot-id-endpoints↓ (⊢↓-∀-idˣ ⊢c) =
  cong `∀ (pivot-id-endpoints↓ ⊢c)
pivot-id-endpoints↓ ⊢↓-idˣ = refl

------------------------------------------------------------------------
-- Freshness for the pivot's representation, under a type binder
------------------------------------------------------------------------

-- The freshness side condition of the transport lemmas is
--   ∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R,
-- read as: the transported variable Y avoids every representation the
-- store assigns to the pivot X.  Under a ∀ binder the pivot becomes
-- suc X and the store becomes store-lift Σ, so the side condition has
-- to be shifted along with them.

lift-pivot-fresh : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
  → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
  → ∀ {R′} → store-lift Σ ∋ Fin.suc X ⦂ R′
    -----------------------------------------
  → Fin.suc Y ∉ᵗ R′
lift-pivot-fresh fresh (S-lift∋ ∋X refl) = shift-not-occurs (fresh ∋X)

------------------------------------------------------------------------
-- Occurrence transport along a pivoted conversion
------------------------------------------------------------------------

mutual
  conv↑-occurs-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ ⊢↑[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∈ᵗ A
      -------
    → Y ∈ᵗ B
  conv↑-occurs-pre (⊢↑-unsealˣ ∋X) Y≢X fresh var-∈ =
    ⊥-elim (Y≢X refl)
  conv↑-occurs-pre (⊢↑-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A) =
    ∈-fun-left (conv↓-occurs-post ⊢c Y≢X fresh Y∈A)
  conv↑-occurs-pre (⊢↑-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (conv↓-absent-post ⊢c Y≢X fresh Y∉A)
      (conv↑-occurs-pre ⊢d Y≢X fresh Y∈B)
  conv↑-occurs-pre (⊢↑-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A) =
    ∈-fun-left (conv↓-occurs-post ⊢c Y≢X fresh Y∈A)
  conv↑-occurs-pre (⊢↑-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (conv↓-absent-post ⊢c Y≢X fresh Y∉A)
      (occurs-cast (pivot-id-endpoints↑ ⊢d) Y∈B)
  conv↑-occurs-pre (⊢↑-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A) =
    ∈-fun-left (occurs-cast (sym (pivot-id-endpoints↓ ⊢c)) Y∈A)
  conv↑-occurs-pre (⊢↑-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (absent-cast (sym (pivot-id-endpoints↓ ⊢c)) Y∉A)
      (conv↑-occurs-pre ⊢d Y≢X fresh Y∈B)
  conv↑-occurs-pre (⊢↑-∀ˣ ⊢c) Y≢X fresh (∈-all Y∈A) =
    ∈-all (conv↑-occurs-pre ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∈A)

  conv↑-occurs-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ ⊢↑[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∈ᵗ B
      -------
    → Y ∈ᵗ A
  conv↑-occurs-post (⊢↑-unsealˣ ∋X) Y≢X fresh Y∈R =
    ⊥-elim (occurs-absent-⊥ Y∈R (fresh ∋X))
  conv↑-occurs-post (⊢↑-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A′) =
    ∈-fun-left (conv↓-occurs-pre ⊢c Y≢X fresh Y∈A′)
  conv↑-occurs-post (⊢↑-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (conv↓-absent-pre ⊢c Y≢X fresh Y∉A′)
      (conv↑-occurs-post ⊢d Y≢X fresh Y∈B′)
  conv↑-occurs-post (⊢↑-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A′) =
    ∈-fun-left (conv↓-occurs-pre ⊢c Y≢X fresh Y∈A′)
  conv↑-occurs-post (⊢↑-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (conv↓-absent-pre ⊢c Y≢X fresh Y∉A′)
      (occurs-cast (sym (pivot-id-endpoints↑ ⊢d)) Y∈B′)
  conv↑-occurs-post (⊢↑-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A′) =
    ∈-fun-left (occurs-cast (pivot-id-endpoints↓ ⊢c) Y∈A′)
  conv↑-occurs-post (⊢↑-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (absent-cast (pivot-id-endpoints↓ ⊢c) Y∉A′)
      (conv↑-occurs-post ⊢d Y≢X fresh Y∈B′)
  conv↑-occurs-post (⊢↑-∀ˣ ⊢c) Y≢X fresh (∈-all Y∈B) =
    ∈-all (conv↑-occurs-post ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∈B)

  conv↓-occurs-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ ⊢↓[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∈ᵗ A
      -------
    → Y ∈ᵗ B
  conv↓-occurs-pre (⊢↓-sealˣ ∋X) Y≢X fresh Y∈R =
    ⊥-elim (occurs-absent-⊥ Y∈R (fresh ∋X))
  conv↓-occurs-pre (⊢↓-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A) =
    ∈-fun-left (conv↑-occurs-post ⊢c Y≢X fresh Y∈A)
  conv↓-occurs-pre (⊢↓-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (conv↑-absent-post ⊢c Y≢X fresh Y∉A)
      (conv↓-occurs-pre ⊢d Y≢X fresh Y∈B)
  conv↓-occurs-pre (⊢↓-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A) =
    ∈-fun-left (conv↑-occurs-post ⊢c Y≢X fresh Y∈A)
  conv↓-occurs-pre (⊢↓-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (conv↑-absent-post ⊢c Y≢X fresh Y∉A)
      (occurs-cast (pivot-id-endpoints↓ ⊢d) Y∈B)
  conv↓-occurs-pre (⊢↓-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A) =
    ∈-fun-left (occurs-cast (sym (pivot-id-endpoints↑ ⊢c)) Y∈A)
  conv↓-occurs-pre (⊢↓-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A Y∈B) =
    ∈-fun-right (absent-cast (sym (pivot-id-endpoints↑ ⊢c)) Y∉A)
      (conv↓-occurs-pre ⊢d Y≢X fresh Y∈B)
  conv↓-occurs-pre (⊢↓-∀ˣ ⊢c) Y≢X fresh (∈-all Y∈A) =
    ∈-all (conv↓-occurs-pre ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∈A)

  conv↓-occurs-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ ⊢↓[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∈ᵗ B
      -------
    → Y ∈ᵗ A
  conv↓-occurs-post (⊢↓-sealˣ ∋X) Y≢X fresh var-∈ =
    ⊥-elim (Y≢X refl)
  conv↓-occurs-post (⊢↓-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A′) =
    ∈-fun-left (conv↑-occurs-pre ⊢c Y≢X fresh Y∈A′)
  conv↓-occurs-post (⊢↓-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (conv↑-absent-pre ⊢c Y≢X fresh Y∉A′)
      (conv↓-occurs-post ⊢d Y≢X fresh Y∈B′)
  conv↓-occurs-post (⊢↓-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A′) =
    ∈-fun-left (conv↑-occurs-pre ⊢c Y≢X fresh Y∈A′)
  conv↓-occurs-post (⊢↓-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (conv↑-absent-pre ⊢c Y≢X fresh Y∉A′)
      (occurs-cast (sym (pivot-id-endpoints↓ ⊢d)) Y∈B′)
  conv↓-occurs-post (⊢↓-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-left Y∈A′) =
    ∈-fun-left (occurs-cast (pivot-id-endpoints↑ ⊢c) Y∈A′)
  conv↓-occurs-post (⊢↓-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∈-fun-right Y∉A′ Y∈B′) =
    ∈-fun-right (absent-cast (pivot-id-endpoints↑ ⊢c) Y∉A′)
      (conv↓-occurs-post ⊢d Y≢X fresh Y∈B′)
  conv↓-occurs-post (⊢↓-∀ˣ ⊢c) Y≢X fresh (∈-all Y∈B) =
    ∈-all (conv↓-occurs-post ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∈B)

  conv↑-absent-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ ⊢↑[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∉ᵗ A
      -------
    → Y ∉ᵗ B
  conv↑-absent-pre (⊢↑-unsealˣ ∋X) Y≢X fresh Y∉X = fresh ∋X
  conv↑-absent-pre (⊢↑-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A Y∉B) =
    ∉-fun (conv↓-absent-post ⊢c Y≢X fresh Y∉A)
      (conv↑-absent-pre ⊢d Y≢X fresh Y∉B)
  conv↑-absent-pre (⊢↑-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A Y∉B) =
    ∉-fun (conv↓-absent-post ⊢c Y≢X fresh Y∉A)
      (absent-cast (pivot-id-endpoints↑ ⊢d) Y∉B)
  conv↑-absent-pre (⊢↑-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A Y∉B) =
    ∉-fun (absent-cast (sym (pivot-id-endpoints↓ ⊢c)) Y∉A)
      (conv↑-absent-pre ⊢d Y≢X fresh Y∉B)
  conv↑-absent-pre (⊢↑-∀ˣ ⊢c) Y≢X fresh (∉-all Y∉A) =
    ∉-all (conv↑-absent-pre ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∉A)

  conv↑-absent-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↑ Δ A B}
    → Σ ⊢↑[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∉ᵗ B
      -------
    → Y ∉ᵗ A
  conv↑-absent-post (⊢↑-unsealˣ ∋X) Y≢X fresh Y∉R =
    ∉-var (≢→≢ᶠ Y≢X)
  conv↑-absent-post (⊢↑-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (conv↓-absent-pre ⊢c Y≢X fresh Y∉A′)
      (conv↑-absent-post ⊢d Y≢X fresh Y∉B′)
  conv↑-absent-post (⊢↑-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (conv↓-absent-pre ⊢c Y≢X fresh Y∉A′)
      (absent-cast (sym (pivot-id-endpoints↑ ⊢d)) Y∉B′)
  conv↑-absent-post (⊢↑-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (absent-cast (pivot-id-endpoints↓ ⊢c) Y∉A′)
      (conv↑-absent-post ⊢d Y≢X fresh Y∉B′)
  conv↑-absent-post (⊢↑-∀ˣ ⊢c) Y≢X fresh (∉-all Y∉B) =
    ∉-all (conv↑-absent-post ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∉B)

  conv↓-absent-pre : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ ⊢↓[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∉ᵗ A
      -------
    → Y ∉ᵗ B
  conv↓-absent-pre (⊢↓-sealˣ ∋X) Y≢X fresh Y∉R =
    ∉-var (≢→≢ᶠ Y≢X)
  conv↓-absent-pre (⊢↓-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A Y∉B) =
    ∉-fun (conv↑-absent-post ⊢c Y≢X fresh Y∉A)
      (conv↓-absent-pre ⊢d Y≢X fresh Y∉B)
  conv↓-absent-pre (⊢↓-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A Y∉B) =
    ∉-fun (conv↑-absent-post ⊢c Y≢X fresh Y∉A)
      (absent-cast (pivot-id-endpoints↓ ⊢d) Y∉B)
  conv↓-absent-pre (⊢↓-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A Y∉B) =
    ∉-fun (absent-cast (sym (pivot-id-endpoints↑ ⊢c)) Y∉A)
      (conv↓-absent-pre ⊢d Y≢X fresh Y∉B)
  conv↓-absent-pre (⊢↓-∀ˣ ⊢c) Y≢X fresh (∉-all Y∉A) =
    ∉-all (conv↓-absent-pre ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∉A)

  conv↓-absent-post : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
      {A B : Ty Δ} {c : Conv↓ Δ A B}
    → Σ ⊢↓[ just X ] c
    → Y ≢ X
    → (∀ {R} → Σ ∋ X ⦂ R → Y ∉ᵗ R)
    → Y ∉ᵗ B
      -------
    → Y ∉ᵗ A
  conv↓-absent-post (⊢↓-sealˣ ∋X) Y≢X fresh Y∉X = fresh ∋X
  conv↓-absent-post (⊢↓-⇒ˣ join-both ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (conv↑-absent-pre ⊢c Y≢X fresh Y∉A′)
      (conv↓-absent-post ⊢d Y≢X fresh Y∉B′)
  conv↓-absent-post (⊢↓-⇒ˣ join-left ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (conv↑-absent-pre ⊢c Y≢X fresh Y∉A′)
      (absent-cast (sym (pivot-id-endpoints↓ ⊢d)) Y∉B′)
  conv↓-absent-post (⊢↓-⇒ˣ join-right ⊢c ⊢d) Y≢X fresh
      (∉-fun Y∉A′ Y∉B′) =
    ∉-fun (absent-cast (pivot-id-endpoints↑ ⊢c) Y∉A′)
      (conv↓-absent-post ⊢d Y≢X fresh Y∉B′)
  conv↓-absent-post (⊢↓-∀ˣ ⊢c) Y≢X fresh (∉-all Y∉B) =
    ∉-all (conv↓-absent-post ⊢c (λ eq → Y≢X (fin-suc-injective eq))
             (lift-pivot-fresh fresh) Y∉B)

------------------------------------------------------------------------
-- Corollaries for the ∀-binder
------------------------------------------------------------------------

-- Under a ∀ binder the pivot is a shifted variable suc X, so the bound
-- variable zero is neither the pivot nor present in any lifted store
-- representation.  Hence zero's occurrences survive the conversion.

zero-pivot-fresh : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R : Ty (Nat.suc Δ)}
  → store-lift Σ ∋ Fin.suc X ⦂ R
    -----------------------------
  → Fin.zero ∉ᵗ R
zero-pivot-fresh (S-lift∋ ∋X refl) = zero-absent-shift _

conv↑-zero-pre : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↑[ just (Fin.suc X) ] c
  → Fin.zero ∈ᵗ A
    --------------
  → Fin.zero ∈ᵗ B
conv↑-zero-pre ⊢c = conv↑-occurs-pre ⊢c (λ ()) zero-pivot-fresh

conv↑-zero-post : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↑[ just (Fin.suc X) ] c
  → Fin.zero ∈ᵗ B
    --------------
  → Fin.zero ∈ᵗ A
conv↑-zero-post ⊢c = conv↑-occurs-post ⊢c (λ ()) zero-pivot-fresh

conv↓-zero-pre : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↓[ just (Fin.suc X) ] c
  → Fin.zero ∈ᵗ A
    --------------
  → Fin.zero ∈ᵗ B
conv↓-zero-pre ⊢c = conv↓-occurs-pre ⊢c (λ ()) zero-pivot-fresh

conv↓-zero-post : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↓[ just (Fin.suc X) ] c
  → Fin.zero ∈ᵗ B
    --------------
  → Fin.zero ∈ᵗ A
conv↓-zero-post ⊢c = conv↓-occurs-post ⊢c (λ ()) zero-pivot-fresh

------------------------------------------------------------------------
-- Non-variable transport away from the bound variable
------------------------------------------------------------------------

-- A conversion pivoted at suc X cannot turn a zero-containing non-variable
-- type into a variable, or conversely.  These small inversion lemmas are the
-- shape component used alongside the occurrence transport above.

conv↑-nonvar-pre-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↑[ just (Fin.suc X) ] c
  → NonVar B
  → Fin.zero ∈ᵗ A
    ----------------
  → NonVar A
conv↑-nonvar-pre-zero (⊢↑-unsealˣ ∋X) Bnv ()
conv↑-nonvar-pre-zero (⊢↑-⇒ˣ join-both ⊢c ⊢d) Bnv zero∈A =
  nonvar-fun
conv↑-nonvar-pre-zero (⊢↑-⇒ˣ join-left ⊢c ⊢d) Bnv zero∈A =
  nonvar-fun
conv↑-nonvar-pre-zero (⊢↑-⇒ˣ join-right ⊢c ⊢d) Bnv zero∈A =
  nonvar-fun
conv↑-nonvar-pre-zero (⊢↑-∀ˣ ⊢c) Bnv zero∈A = nonvar-all

conv↑-nonvar-post-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↑ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↑[ just (Fin.suc X) ] c
  → NonVar A
  → Fin.zero ∈ᵗ B
    ----------------
  → NonVar B
conv↑-nonvar-post-zero (⊢↑-unsealˣ ∋X) () zero∈B
conv↑-nonvar-post-zero (⊢↑-⇒ˣ join-both ⊢c ⊢d) Anv zero∈B =
  nonvar-fun
conv↑-nonvar-post-zero (⊢↑-⇒ˣ join-left ⊢c ⊢d) Anv zero∈B =
  nonvar-fun
conv↑-nonvar-post-zero (⊢↑-⇒ˣ join-right ⊢c ⊢d) Anv zero∈B =
  nonvar-fun
conv↑-nonvar-post-zero (⊢↑-∀ˣ ⊢c) Anv zero∈B = nonvar-all

conv↓-nonvar-pre-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↓[ just (Fin.suc X) ] c
  → NonVar B
  → Fin.zero ∈ᵗ A
    ----------------
  → NonVar A
conv↓-nonvar-pre-zero (⊢↓-sealˣ ∋X) () zero∈A
conv↓-nonvar-pre-zero (⊢↓-⇒ˣ join-both ⊢c ⊢d) Bnv zero∈A =
  nonvar-fun
conv↓-nonvar-pre-zero (⊢↓-⇒ˣ join-left ⊢c ⊢d) Bnv zero∈A =
  nonvar-fun
conv↓-nonvar-pre-zero (⊢↓-⇒ˣ join-right ⊢c ⊢d) Bnv zero∈A =
  nonvar-fun
conv↓-nonvar-pre-zero (⊢↓-∀ˣ ⊢c) Bnv zero∈A = nonvar-all

conv↓-nonvar-post-zero : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {A B : Ty (Nat.suc Δ)} {c : Conv↓ (Nat.suc Δ) A B}
  → store-lift Σ ⊢↓[ just (Fin.suc X) ] c
  → NonVar A
  → Fin.zero ∈ᵗ B
    ----------------
  → NonVar B
conv↓-nonvar-post-zero (⊢↓-sealˣ ∋X) Anv ()
conv↓-nonvar-post-zero (⊢↓-⇒ˣ join-both ⊢c ⊢d) Anv zero∈B =
  nonvar-fun
conv↓-nonvar-post-zero (⊢↓-⇒ˣ join-left ⊢c ⊢d) Anv zero∈B =
  nonvar-fun
conv↓-nonvar-post-zero (⊢↓-⇒ˣ join-right ⊢c ⊢d) Anv zero∈B =
  nonvar-fun
conv↓-nonvar-post-zero (⊢↓-∀ˣ ⊢c) Anv zero∈B = nonvar-all

module proof.ImprecisionComposition where

-- File Charter:
--   * Proves that narrowing and widening composition is total for operands
--     with the two-context imprecision typings used by term imprecision.
--   * Proves that the raw result returned by composition is well typed.
--   * Depends on the proof-facing fuel interface in `NarrowWiden`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat
  using (ℕ; zero; suc; z≤n; s≤s; s≤s⁻¹; _+_; _<_; _≤_)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-trans
  ; <-trans
  ; <-≤-trans
  ; +-comm
  ; +-mono-<
  ; +-mono-≤
  ; +-monoˡ-<
  ; +-monoʳ-<
  ; +-suc
  ; m≤m+n
  ; m≤n+m
  ; n<1+n
  )
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (subst; sym; cong; cong₂; inspect; trans; [_])

open import Types
open import proof.TypeInTypeSubst using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; rename-ext-preserves-zero∈
  )
open import Coercions using
  ( Coercion
  ; id
  ; _︔_
  ; _↦_
  ; `∀
  ; _!
  ; _？
  ; seal
  ; unseal
  ; gen
  ; inst
  ; error
  ; renameᶜ
  )
open import NarrowWiden
open import Imprecision

open NarrowWiden.CompositionInternals

------------------------------------------------------------------------
-- Identity imprecision contexts
------------------------------------------------------------------------

un⇑ᵢ-var : ∀ {Φ X Y}
  → (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
  → (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᵢ-var {Φ = []} ()
un⇑ᵢ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-var X∈)
un⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-var X∈)

un⇑ᵢ-star : ∀ {Φ X}
  → (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
  → (X ˣ⊑★) ∈ Φ
un⇑ᵢ-star {Φ = []} ()
un⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-star X∈)
un⇑ᵢ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᵢ-star X∈)

⇑ᵢ-var : ∀ {Φ X Y}
  → (X ˣ⊑ˣ Y) ∈ Φ
  → (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
⇑ᵢ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᵢ-var X∈)
⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᵢ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᵢ-var X∈)

⇑ᵢ-star : ∀ {Φ X}
  → (X ˣ⊑★) ∈ Φ
  → (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᵢ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᵢ-star X∈)
⇑ᵢ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᵢ-star X∈)

no-⇑ᵢ-zero-left : ∀ {Φ Y}
  → (zero ˣ⊑ˣ Y) ∈ ⇑ᵢ Φ
  → ⊥
no-⇑ᵢ-zero-left {Φ = []} ()
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-left X∈
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-left X∈

no-⇑ᵢ-zero-right : ∀ {Φ X}
  → (X ˣ⊑ˣ zero) ∈ ⇑ᵢ Φ
  → ⊥
no-⇑ᵢ-zero-right {Φ = []} ()
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-right X∈
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-right X∈

no-⇑ᵢ-zero-star : ∀ {Φ}
  → (zero ˣ⊑★) ∈ ⇑ᵢ Φ
  → ⊥
no-⇑ᵢ-zero-star {Φ = []} ()
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-star X∈
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᵢ-zero-star X∈

idᵢ-var-identity : ∀ {Δ X Y}
  → (X ˣ⊑ˣ Y) ∈ idᵢ Δ
  → X ≡ Y
idᵢ-var-identity {Δ = zero} ()
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero}
    (here refl) =
  refl
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = suc Y}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (idᵢ-var-identity (un⇑ᵢ-var X∈))

idᵢ-no-star : ∀ {Δ X}
  → (X ˣ⊑★) ∈ idᵢ Δ
  → ⊥
idᵢ-no-star {Δ = zero} ()
idᵢ-no-star {Δ = suc Δ} {X = zero} (there X∈) =
  no-⇑ᵢ-zero-star X∈
idᵢ-no-star {Δ = suc Δ} {X = suc X} (there X∈) =
  idᵢ-no-star (un⇑ᵢ-star X∈)

------------------------------------------------------------------------
-- Asymmetric renaming of indexed narrowing and widening
------------------------------------------------------------------------

renameFirst : Renameᵗ → ImpAssm → ImpAssm
renameFirst ρ (X ˣ⊑★) = ρ X ˣ⊑★
renameFirst ρ (X ˣ⊑ˣ Y) = ρ X ˣ⊑ˣ Y

renameFirst-⇑ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ ⇑ᵢ Φ
  → renameFirst (extᵗ ρ) a ∈ ⇑ᵢ Ψ
renameFirst-⇑ {Φ = []} h ()
renameFirst-⇑ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (ρ X ˣ⊑★) ∈ Ψ
    → (suc (ρ X) ˣ⊑★) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (ρ X ˣ⊑ˣ Y) ∈ Ψ
    → (suc (ρ X) ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ {Φ = (_ ˣ⊑★) ∷ Φ} h (there a∈) =
  renameFirst-⇑ (λ b∈ → h (there b∈)) a∈
renameFirst-⇑ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (there a∈) =
  renameFirst-⇑ (λ b∈ → h (there b∈)) a∈

renameFirst-all : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ
  → renameFirst (extᵗ ρ) a
      ∈ (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ
renameFirst-all h (here refl) = here refl
renameFirst-all h (there a∈) = there (renameFirst-⇑ h a∈)

renameFirst-⇑ᴸ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ ⇑ᴸᵢ Φ
  → renameFirst (extᵗ ρ) a ∈ ⇑ᴸᵢ Ψ
renameFirst-⇑ᴸ {Φ = []} h ()
renameFirst-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (ρ X ˣ⊑★) ∈ Ψ
    → (suc (ρ X) ˣ⊑★) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (ρ X ˣ⊑ˣ Y) ∈ Ψ
    → (suc (ρ X) ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameFirst-⇑ᴸ {Φ = (_ ˣ⊑★) ∷ Φ} h (there a∈) =
  renameFirst-⇑ᴸ (λ b∈ → h (there b∈)) a∈
renameFirst-⇑ᴸ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (there a∈) =
  renameFirst-⇑ᴸ (λ b∈ → h (there b∈)) a∈

renameFirst-gen : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameFirst ρ b ∈ Ψ)
  → a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
  → renameFirst (extᵗ ρ) a
      ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ
renameFirst-gen h (here refl) = here refl
renameFirst-gen h (there a∈) = there (renameFirst-⇑ᴸ h a∈)

mutual

  rename-nonIdⁿ : ∀ ρ {c} (n : NonIdⁿ c)
    → renameⁿ ρ (nonIdⁿ→narrowing n)
        ≡ nonIdⁿ→narrowing (renameNonIdⁿ ρ n)
  rename-nonIdⁿ ρ (cross n) rewrite rename-nonIdCrossⁿ ρ n = refl
  rename-nonIdⁿ ρ (gen n) = refl
  rename-nonIdⁿ ρ (G ？) = refl
  rename-nonIdⁿ ρ (G ？︔ n) = refl
  rename-nonIdⁿ ρ (fun-？︔gen n) = refl
  rename-nonIdⁿ ρ (seal X) = refl
  rename-nonIdⁿ ρ (n ︔seal X) = refl

  rename-nonIdCrossⁿ : ∀ ρ {c} (n : NonIdCrossⁿ c)
    → renameCrossⁿ ρ (nonIdCrossⁿ→cross n)
        ≡ nonIdCrossⁿ→cross (renameNonIdCrossⁿ ρ n)
  rename-nonIdCrossⁿ ρ (w ↦ˡ n)
      rewrite rename-nonIdʷ ρ w =
    refl
  rename-nonIdCrossⁿ ρ (w ↦ʳ n)
      rewrite rename-nonIdⁿ ρ n =
    refl
  rename-nonIdCrossⁿ ρ (`∀ n)
      rewrite rename-nonIdⁿ (extᵗ ρ) n =
    refl

  rename-nonIdʷ : ∀ ρ {c} (w : NonIdʷ c)
    → renameʷ ρ (nonIdʷ→widening w)
        ≡ nonIdʷ→widening (renameNonIdʷ ρ w)
  rename-nonIdʷ ρ (cross w) rewrite rename-nonIdCrossʷ ρ w = refl
  rename-nonIdʷ ρ (inst w) = refl
  rename-nonIdʷ ρ (G !) = refl
  rename-nonIdʷ ρ (w ︔ G !) = refl
  rename-nonIdʷ ρ (inst w ︔★⇒★!) = refl
  rename-nonIdʷ ρ (unseal X) = refl
  rename-nonIdʷ ρ (NonIdʷ.unseal_︔_ X w) = refl

  rename-nonIdCrossʷ : ∀ ρ {c} (w : NonIdCrossʷ c)
    → renameCrossʷ ρ (nonIdCrossʷ→cross w)
        ≡ nonIdCrossʷ→cross (renameNonIdCrossʷ ρ w)
  rename-nonIdCrossʷ ρ (n ↦ˡ w)
      rewrite rename-nonIdⁿ ρ n =
    refl
  rename-nonIdCrossʷ ρ (n ↦ʳ w)
      rewrite rename-nonIdʷ ρ w =
    refl
  rename-nonIdCrossʷ ρ (`∀ w)
      rewrite rename-nonIdʷ (extᵗ ρ) w =
    refl

rename-genSafe : ∀ ρ {c} (n : GenSafe c)
  → renameⁿ ρ (genSafe→narrowing n)
      ≡ genSafe→narrowing (renameGenSafe ρ n)
rename-genSafe ρ (w ↦ n) = refl
rename-genSafe ρ (`∀ n) = refl
rename-genSafe ρ (gen n) = refl

rename-instSafe : ∀ ρ {c} (w : InstSafe c)
  → renameʷ ρ (instSafe→widening w)
      ≡ instSafe→widening (renameInstSafe ρ w)
rename-instSafe ρ (n ↦ w) = refl
rename-instSafe ρ (`∀ w) = refl
rename-instSafe ρ (inst w) = refl

mutual

  rename-sourceʷ : ∀ {ρ Φ Ψ Δᴸ Δᴸ′ Δᴿ c A B}
    {w : Widening c}
    → (∀ {a} → a ∈ Φ → renameFirst ρ a ∈ Ψ)
    → TyRenameWf Δᴸ Δᴸ′ ρ
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ′ ⊢ renameʷ ρ w ⦂ renameᵗ ρ A ⊑ B ⊣ Δᴿ
  rename-sourceʷ h hρ id★ = id★
  rename-sourceʷ h hρ (idˣ X∈ X<Δᴸ Y<Δᴿ) =
    idˣ (h X∈) (hρ X<Δᴸ) Y<Δᴿ
  rename-sourceʷ h hρ idι = idι
  rename-sourceʷ h hρ (p ↦ q) =
    rename-targetⁿ h hρ p ↦ rename-sourceʷ h hρ q
  rename-sourceʷ h hρ (∀ⁱ p) =
    ∀ⁱ (rename-sourceʷ (renameFirst-all h)
          (TyRenameWf-ext hρ) p)
  rename-sourceʷ h hρ (tag ι) = tag ι
  rename-sourceʷ h hρ tag⇒ = tag⇒
  rename-sourceʷ {ρ = ρ} h hρ (tag p ↦ˡ q) =
    tag
      (subst
        (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
        (rename-nonIdⁿ ρ _)
        (rename-targetⁿ h hρ p))
      ↦ˡ rename-sourceʷ h hρ q
  rename-sourceʷ {ρ = ρ} h hρ (tag p ↦ʳ q) =
    tag rename-targetⁿ h hρ p ↦ʳ
      (subst
        (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
        (rename-nonIdʷ ρ _)
        (rename-sourceʷ h hρ q))
  rename-sourceʷ h hρ (tagˣ X∈ X<Δᴸ) =
    tagˣ (h X∈) (hρ X<Δᴸ)
  rename-sourceʷ {ρ = ρ} h hρ (inst nonvar occ p) =
    inst (renameNonVar (extᵗ ρ) nonvar)
      (rename-ext-preserves-zero∈ ρ occ)
      (subst
        (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
        (rename-instSafe (extᵗ ρ) _)
        (rename-sourceʷ (renameFirst-gen h)
          (TyRenameWf-ext hρ) p))
  rename-sourceʷ {ρ = ρ} h hρ (inst-tag nonvar occ p) =
    inst-tag (renameNonVar (extᵗ ρ) nonvar)
      (rename-ext-preserves-zero∈ ρ occ)
      (subst
        (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
        (rename-instSafe (extᵗ ρ) _)
        (rename-sourceʷ (renameFirst-gen h)
          (TyRenameWf-ext hρ) p))

  rename-targetⁿ : ∀ {ρ Φ Ψ Δᴸ Δᴿ Δᴿ′ c A B}
    {n : Narrowing c}
    → (∀ {a} → a ∈ Φ → renameFirst ρ a ∈ Ψ)
    → TyRenameWf Δᴿ Δᴿ′ ρ
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ renameⁿ ρ n ⦂ A ⊒ renameᵗ ρ B ⊣ Δᴿ′
  rename-targetⁿ h hρ id★ = id★
  rename-targetⁿ h hρ (idˣ X∈ X<Δᴸ Y<Δᴿ) =
    idˣ (h X∈) X<Δᴸ (hρ Y<Δᴿ)
  rename-targetⁿ h hρ idι = idι
  rename-targetⁿ h hρ (p ↦ q) =
    rename-sourceʷ h hρ p ↦ rename-targetⁿ h hρ q
  rename-targetⁿ h hρ (∀ⁱ p) =
    ∀ⁱ (rename-targetⁿ (renameFirst-all h)
          (TyRenameWf-ext hρ) p)
  rename-targetⁿ h hρ (untag ι) = untag ι
  rename-targetⁿ h hρ untag⇒ = untag⇒
  rename-targetⁿ {ρ = ρ} h hρ (untag p ↦ˡ q) =
    untag
      (subst
        (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
        (rename-nonIdʷ ρ _)
        (rename-sourceʷ h hρ p))
      ↦ˡ rename-targetⁿ h hρ q
  rename-targetⁿ {ρ = ρ} h hρ (untag p ↦ʳ q) =
    untag rename-sourceʷ h hρ p ↦ʳ
      (subst
        (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
        (rename-nonIdⁿ ρ _)
        (rename-targetⁿ h hρ q))
  rename-targetⁿ h hρ (untagˣ X∈ X<Δᴿ) =
    untagˣ (h X∈) (hρ X<Δᴿ)
  rename-targetⁿ {ρ = ρ} h hρ (gen nonvar occ p) =
    gen (renameNonVar (extᵗ ρ) nonvar)
      (rename-ext-preserves-zero∈ ρ occ)
      (subst
        (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
        (rename-genSafe (extᵗ ρ) _)
        (rename-targetⁿ (renameFirst-gen h)
          (TyRenameWf-ext hρ) p))
  rename-targetⁿ {ρ = ρ} h hρ (gen-untag nonvar occ p) =
    gen-untag (renameNonVar (extᵗ ρ) nonvar)
      (rename-ext-preserves-zero∈ ρ occ)
      (subst
        (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
        (rename-genSafe (extᵗ ρ) _)
        (rename-targetⁿ (renameFirst-gen h)
          (TyRenameWf-ext hρ) p))

renameFirst-suc-gen : ∀ {Φ a}
  → a ∈ Φ
  → renameFirst suc a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ
renameFirst-suc-gen {a = X ˣ⊑★} X∈ =
  there (go X∈)
  where
  go : ∀ {Φ X}
    → (X ˣ⊑★) ∈ Φ
    → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  go {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
  go {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) = there (go X∈)
  go {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) = there (go X∈)
renameFirst-suc-gen {a = X ˣ⊑ˣ Y} X∈ =
  there (go X∈)
  where
  go : ∀ {Φ X Y}
    → (X ˣ⊑ˣ Y) ∈ Φ
    → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  go {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) = there (go X∈)
  go {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
  go {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) = there (go X∈)

source-liftʷ : ∀ {Φ Δᴸ Δᴿ c A B} {w : Widening c}
  → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ renameʷ suc w ⦂ ⇑ᵗ A ⊑ B ⊣ Δᴿ
source-liftʷ =
  rename-sourceʷ renameFirst-suc-gen (λ X<Δ → s≤s X<Δ)

target-liftⁿ : ∀ {Φ Δᴸ Δᴿ c A B} {n : Narrowing c}
  → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ Δᴸ ⊢ renameⁿ suc n ⦂ A ⊒ ⇑ᵗ B ⊣ suc Δᴿ
target-liftⁿ =
  rename-targetⁿ renameFirst-suc-gen (λ X<Δ → s≤s X<Δ)

------------------------------------------------------------------------
-- Weakening the imprecision-assumption context
------------------------------------------------------------------------

CtxIncl : ImpCtx → ImpCtx → Set
CtxIncl Φ Ψ = ∀ {a} → a ∈ Φ → a ∈ Ψ

map-⇑-incl : ∀ {Φ Ψ}
  → CtxIncl Φ Ψ
  → CtxIncl (⇑ᵢ Φ) (⇑ᵢ Ψ)
map-⇑-incl {Φ = []} incl ()
map-⇑-incl {Φ = (X ˣ⊑★) ∷ Φ} incl (here refl) =
  go (incl (here refl))
  where
  go : ∀ {Ψ}
    → (X ˣ⊑★) ∈ Ψ
    → (suc X ˣ⊑★) ∈ ⇑ᵢ Ψ
  go {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  go {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) = there (go X∈)
  go {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) = there (go X∈)
map-⇑-incl {Φ = (X ˣ⊑ˣ Y) ∷ Φ} incl (here refl) =
  go (incl (here refl))
  where
  go : ∀ {Ψ}
    → (X ˣ⊑ˣ Y) ∈ Ψ
    → (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Ψ
  go {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) = there (go X∈)
  go {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  go {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) = there (go X∈)
map-⇑-incl {Φ = _ ∷ Φ} incl (there a∈) =
  map-⇑-incl (λ b∈ → incl (there b∈)) a∈

all-incl : ∀ {Φ Ψ}
  → CtxIncl Φ Ψ
  → CtxIncl ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
all-incl incl (here refl) = here refl
all-incl incl (there a∈) = there (map-⇑-incl incl a∈)

map-⇑ᴸ-incl : ∀ {Φ Ψ}
  → CtxIncl Φ Ψ
  → CtxIncl (⇑ᴸᵢ Φ) (⇑ᴸᵢ Ψ)
map-⇑ᴸ-incl {Φ = []} incl ()
map-⇑ᴸ-incl {Φ = (X ˣ⊑★) ∷ Φ} incl (here refl) =
  go (incl (here refl))
  where
  go : ∀ {Ψ}
    → (X ˣ⊑★) ∈ Ψ
    → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Ψ
  go {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  go {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) = there (go X∈)
  go {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) = there (go X∈)
map-⇑ᴸ-incl {Φ = (X ˣ⊑ˣ Y) ∷ Φ} incl (here refl) =
  go (incl (here refl))
  where
  go : ∀ {Ψ}
    → (X ˣ⊑ˣ Y) ∈ Ψ
    → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Ψ
  go {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) = there (go X∈)
  go {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  go {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) = there (go X∈)
map-⇑ᴸ-incl {Φ = _ ∷ Φ} incl (there a∈) =
  map-⇑ᴸ-incl (λ b∈ → incl (there b∈)) a∈

gen-incl : ∀ {Φ Ψ}
  → CtxIncl Φ Ψ
  → CtxIncl ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
gen-incl incl (here refl) = here refl
gen-incl incl (there a∈) = there (map-⇑ᴸ-incl incl a∈)

mutual

  weaken-ctxʷ : ∀ {Φ Ψ Δᴸ Δᴿ c A B} {w : Widening c}
    → CtxIncl Φ Ψ
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  weaken-ctxʷ incl id★ = id★
  weaken-ctxʷ incl (idˣ X∈ X<Δᴸ Y<Δᴿ) =
    idˣ (incl X∈) X<Δᴸ Y<Δᴿ
  weaken-ctxʷ incl idι = idι
  weaken-ctxʷ incl (p ↦ q) =
    weaken-ctxⁿ incl p ↦ weaken-ctxʷ incl q
  weaken-ctxʷ incl (∀ⁱ p) = ∀ⁱ (weaken-ctxʷ (all-incl incl) p)
  weaken-ctxʷ incl (tag ι) = tag ι
  weaken-ctxʷ incl tag⇒ = tag⇒
  weaken-ctxʷ incl (tag p ↦ˡ q) =
    tag weaken-ctxⁿ incl p ↦ˡ weaken-ctxʷ incl q
  weaken-ctxʷ incl (tag p ↦ʳ q) =
    tag weaken-ctxⁿ incl p ↦ʳ weaken-ctxʷ incl q
  weaken-ctxʷ incl (tagˣ X∈ X<Δᴸ) = tagˣ (incl X∈) X<Δᴸ
  weaken-ctxʷ incl (inst nonvar occ p) =
    inst nonvar occ (weaken-ctxʷ (gen-incl incl) p)
  weaken-ctxʷ incl (inst-tag nonvar occ p) =
    inst-tag nonvar occ (weaken-ctxʷ (gen-incl incl) p)

  weaken-ctxⁿ : ∀ {Φ Ψ Δᴸ Δᴿ c A B} {n : Narrowing c}
    → CtxIncl Φ Ψ
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  weaken-ctxⁿ incl id★ = id★
  weaken-ctxⁿ incl (idˣ X∈ X<Δᴸ Y<Δᴿ) =
    idˣ (incl X∈) X<Δᴸ Y<Δᴿ
  weaken-ctxⁿ incl idι = idι
  weaken-ctxⁿ incl (p ↦ q) =
    weaken-ctxʷ incl p ↦ weaken-ctxⁿ incl q
  weaken-ctxⁿ incl (∀ⁱ p) = ∀ⁱ (weaken-ctxⁿ (all-incl incl) p)
  weaken-ctxⁿ incl (untag ι) = untag ι
  weaken-ctxⁿ incl untag⇒ = untag⇒
  weaken-ctxⁿ incl (untag p ↦ˡ q) =
    untag weaken-ctxʷ incl p ↦ˡ weaken-ctxⁿ incl q
  weaken-ctxⁿ incl (untag p ↦ʳ q) =
    untag weaken-ctxʷ incl p ↦ʳ weaken-ctxⁿ incl q
  weaken-ctxⁿ incl (untagˣ X∈ X<Δᴿ) = untagˣ (incl X∈) X<Δᴿ
  weaken-ctxⁿ incl (gen nonvar occ p) =
    gen nonvar occ (weaken-ctxⁿ (gen-incl incl) p)
  weaken-ctxⁿ incl (gen-untag nonvar occ p) =
    gen-untag nonvar occ (weaken-ctxⁿ (gen-incl incl) p)

------------------------------------------------------------------------
-- Type shapes
------------------------------------------------------------------------

data TyShape : Set where
  var base star : TyShape
  _⇒ˢ_ : TyShape → TyShape → TyShape
  all : TyShape → TyShape

shape : Ty → TyShape
shape (＇ X) = var
shape (‵ ι) = base
shape ★ = star
shape (A ⇒ B) = shape A ⇒ˢ shape B
shape (`∀ A) = all (shape A)

data GenShape : TyShape → Set where
  fun : ∀ {A B} → GenShape (A ⇒ˢ B)
  all : ∀ {A} → GenShape (all A)

nonvar-member-shape : ∀ {A X}
  → NonVar A
  → X ∈ᵗ A
  → GenShape (shape A)
nonvar-member-shape nonvar-base ()
nonvar-member-shape nonvar-star ()
nonvar-member-shape nonvar-fun member = fun
nonvar-member-shape nonvar-all member = all

------------------------------------------------------------------------
-- Shape typing for raw narrowing and widening coercions
------------------------------------------------------------------------

mutual

  data Wtʷ : Coercion → TyShape → TyShape → Set where
    w-id★ : Wtʷ id star star
    w-idˣ : Wtʷ id var var
    w-idι : Wtʷ id base base

    w-↦ : ∀ {c d A A′ B B′}
      → Wtⁿ c A′ A
      → Wtʷ d B B′
      → Wtʷ (c ↦ d) (A ⇒ˢ B) (A′ ⇒ˢ B′)

    w-∀ : ∀ {c A B}
      → Wtʷ c A B
      → Wtʷ (`∀ c) (all A) (all B)

    w-tag-base : Wtʷ ((‵ `ℕ) !) base star
    w-tag-base′ : Wtʷ ((‵ `𝔹) !) base star
    w-tag-fun : Wtʷ (★⇒★ !) (star ⇒ˢ star) star

    w-tag-seq : ∀ {c A}
      → Wtʷ c A (star ⇒ˢ star)
      → Wtʷ (c ︔ (★⇒★ !)) A star

    w-unseal : ∀ {X} → Wtʷ (unseal X) var star

    w-inst : ∀ {c A B}
      → GenShape A
      → Wtʷ c A B
      → Wtʷ (inst c) (all A) B

    w-inst-tag : ∀ {c A}
      → GenShape A
      → Wtʷ c A (star ⇒ˢ star)
      → Wtʷ (inst c ︔ (★⇒★ !)) (all A) star

  data Wtⁿ : Coercion → TyShape → TyShape → Set where
    n-id★ : Wtⁿ id star star
    n-idˣ : Wtⁿ id var var
    n-idι : Wtⁿ id base base

    n-↦ : ∀ {c d A A′ B B′}
      → Wtʷ c A′ A
      → Wtⁿ d B B′
      → Wtⁿ (c ↦ d) (A ⇒ˢ B) (A′ ⇒ˢ B′)

    n-∀ : ∀ {c A B}
      → Wtⁿ c A B
      → Wtⁿ (`∀ c) (all A) (all B)

    n-untag-base : Wtⁿ ((‵ `ℕ) ？) star base
    n-untag-base′ : Wtⁿ ((‵ `𝔹) ？) star base
    n-untag-fun : Wtⁿ (★⇒★ ？) star (star ⇒ˢ star)

    n-untag-seq : ∀ {c B}
      → Wtⁿ c (star ⇒ˢ star) B
      → Wtⁿ ((★⇒★ ？) ︔ c) star B

    n-seal : ∀ {X} → Wtⁿ (seal X) star var

    n-seal-seq : ∀ {c A X}
      → Wtⁿ c A star
      → Wtⁿ (c ︔ seal X) A var

    n-gen : ∀ {c A B}
      → GenShape A
      → Wtⁿ c B A
      → Wtⁿ (gen c) B (all A)

    n-gen-untag : ∀ {c A}
      → GenShape A
      → Wtⁿ c (star ⇒ˢ star) A
      → Wtⁿ ((★⇒★ ？) ︔ gen c) star (all A)

------------------------------------------------------------------------
-- Erasure from public imprecision typings
------------------------------------------------------------------------

mutual

  eraseʷ : ∀ {c Φ Δᴸ Δᴿ A B} {w : Widening c}
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → Wtʷ c (shape A) (shape B)
  eraseʷ id★ = w-id★
  eraseʷ (idˣ _ _ _) = w-idˣ
  eraseʷ idι = w-idι
  eraseʷ (p ↦ q) = w-↦ (eraseⁿ p) (eraseʷ q)
  eraseʷ (∀ⁱ p) = w-∀ (eraseʷ p)
  eraseʷ (tag `ℕ) = w-tag-base
  eraseʷ (tag `𝔹) = w-tag-base′
  eraseʷ tag⇒ = w-tag-fun
  eraseʷ (tag p ↦ˡ q) = w-tag-seq (w-↦ (eraseⁿ p) (eraseʷ q))
  eraseʷ (tag p ↦ʳ q) = w-tag-seq (w-↦ (eraseⁿ p) (eraseʷ q))
  eraseʷ (tagˣ _ _) = w-unseal
  eraseʷ (inst nonvar member p) =
    w-inst (nonvar-member-shape nonvar member) (eraseʷ p)
  eraseʷ (inst-tag nonvar member p) =
    w-inst-tag (nonvar-member-shape nonvar member)
      (eraseʷ p)

  eraseⁿ : ∀ {c Φ Δᴸ Δᴿ A B} {n : Narrowing c}
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → Wtⁿ c (shape A) (shape B)
  eraseⁿ id★ = n-id★
  eraseⁿ (idˣ _ _ _) = n-idˣ
  eraseⁿ idι = n-idι
  eraseⁿ (p ↦ q) = n-↦ (eraseʷ p) (eraseⁿ q)
  eraseⁿ (∀ⁱ p) = n-∀ (eraseⁿ p)
  eraseⁿ (untag `ℕ) = n-untag-base
  eraseⁿ (untag `𝔹) = n-untag-base′
  eraseⁿ untag⇒ = n-untag-fun
  eraseⁿ (untag p ↦ˡ q) =
    n-untag-seq (n-↦ (eraseʷ p) (eraseⁿ q))
  eraseⁿ (untag p ↦ʳ q) =
    n-untag-seq (n-↦ (eraseʷ p) (eraseⁿ q))
  eraseⁿ (untagˣ _ _) = n-seal
  eraseⁿ (gen nonvar member p) =
    n-gen (nonvar-member-shape nonvar member) (eraseⁿ p)
  eraseⁿ (gen-untag nonvar member p) =
    n-gen-untag (nonvar-member-shape nonvar member)
      (eraseⁿ p)

------------------------------------------------------------------------
-- Shape typing is invariant under type-variable renaming
------------------------------------------------------------------------

mutual

  rename-wtʷ : ∀ ρ {c A B}
    → Wtʷ c A B
    → Wtʷ (renameᶜ ρ c) A B
  rename-wtʷ ρ w-id★ = w-id★
  rename-wtʷ ρ w-idˣ = w-idˣ
  rename-wtʷ ρ w-idι = w-idι
  rename-wtʷ ρ (w-↦ p q) =
    w-↦ (rename-wtⁿ ρ p) (rename-wtʷ ρ q)
  rename-wtʷ ρ (w-∀ p) = w-∀ (rename-wtʷ (extᵗ ρ) p)
  rename-wtʷ ρ w-tag-base = w-tag-base
  rename-wtʷ ρ w-tag-base′ = w-tag-base′
  rename-wtʷ ρ w-tag-fun = w-tag-fun
  rename-wtʷ ρ (w-tag-seq p) = w-tag-seq (rename-wtʷ ρ p)
  rename-wtʷ ρ w-unseal = w-unseal
  rename-wtʷ ρ (w-inst shapeA p) =
    w-inst shapeA (rename-wtʷ (extᵗ ρ) p)
  rename-wtʷ ρ (w-inst-tag shapeA p) =
    w-inst-tag shapeA (rename-wtʷ (extᵗ ρ) p)

  rename-wtⁿ : ∀ ρ {c A B}
    → Wtⁿ c A B
    → Wtⁿ (renameᶜ ρ c) A B
  rename-wtⁿ ρ n-id★ = n-id★
  rename-wtⁿ ρ n-idˣ = n-idˣ
  rename-wtⁿ ρ n-idι = n-idι
  rename-wtⁿ ρ (n-↦ p q) =
    n-↦ (rename-wtʷ ρ p) (rename-wtⁿ ρ q)
  rename-wtⁿ ρ (n-∀ p) = n-∀ (rename-wtⁿ (extᵗ ρ) p)
  rename-wtⁿ ρ n-untag-base = n-untag-base
  rename-wtⁿ ρ n-untag-base′ = n-untag-base′
  rename-wtⁿ ρ n-untag-fun = n-untag-fun
  rename-wtⁿ ρ (n-untag-seq p) =
    n-untag-seq (rename-wtⁿ ρ p)
  rename-wtⁿ ρ n-seal = n-seal
  rename-wtⁿ ρ (n-seal-seq p) =
    n-seal-seq (rename-wtⁿ ρ p)
  rename-wtⁿ ρ (n-gen shapeA p) =
    n-gen shapeA (rename-wtⁿ (extᵗ ρ) p)
  rename-wtⁿ ρ (n-gen-untag shapeA p) =
    n-gen-untag shapeA (rename-wtⁿ (extᵗ ρ) p)

------------------------------------------------------------------------
-- Safe grammar views at polymorphic shapes
------------------------------------------------------------------------

gen-safe : ∀ {c A B}
  → GenShape A
  → GenShape B
  → Wtⁿ c A B
  → (n : Narrowing c)
  → ∃[ safe ] genSafe? n ≡ just safe
gen-safe () shapeB n-id★ n
gen-safe () shapeB n-idˣ n
gen-safe () shapeB n-idι n
gen-safe fun fun (n-↦ p q) (cross (w ↦ n)) =
  (w ↦ n) , refl
gen-safe all all (n-∀ p) (cross (`∀ n)) = (`∀ n) , refl
gen-safe () shapeB n-untag-base n
gen-safe () shapeB n-untag-base′ n
gen-safe () shapeB n-untag-fun n
gen-safe () shapeB (n-untag-seq p) n
gen-safe () shapeB n-seal n
gen-safe shapeA () (n-seal-seq p) n
gen-safe shapeB all (n-gen shapeA p) (Narrowing.gen safe) =
  GenSafe.gen safe , refl
gen-safe () shapeB (n-gen-untag shapeA p) n

inst-safe : ∀ {c A B}
  → GenShape A
  → GenShape B
  → Wtʷ c A B
  → (w : Widening c)
  → ∃[ safe ] instSafe? w ≡ just safe
inst-safe () shapeB w-id★ w
inst-safe () shapeB w-idˣ w
inst-safe () shapeB w-idι w
inst-safe fun fun (w-↦ p q) (cross (n ↦ w)) =
  (n ↦ w) , refl
inst-safe all all (w-∀ p) (cross (`∀ w)) = (`∀ w) , refl
inst-safe () shapeB w-tag-base w
inst-safe () shapeB w-tag-base′ w
inst-safe shapeA () w-tag-fun w
inst-safe shapeA () (w-tag-seq p) w
inst-safe shapeA () w-unseal w
inst-safe all shapeB (w-inst shapeA p) (Widening.inst safe) =
  InstSafe.inst safe , refl
inst-safe shapeA () (w-inst-tag shapeB p) w

gen-safe-source-shape : ∀ {c A B}
  → (safe : GenSafe c)
  → Wtⁿ c A B
  → GenShape A
gen-safe-source-shape (w ↦ n) (n-↦ p q) = fun
gen-safe-source-shape (`∀ n) (n-∀ p) = all
gen-safe-source-shape (GenSafe.gen safe) (n-gen shapeB p) =
  gen-safe-source-shape safe p

gen-safe-target-shape : ∀ {c A B}
  → (safe : GenSafe c)
  → Wtⁿ c A B
  → GenShape B
gen-safe-target-shape (w ↦ n) (n-↦ p q) = fun
gen-safe-target-shape (`∀ n) (n-∀ p) = all
gen-safe-target-shape (GenSafe.gen safe) (n-gen shapeB p) = all

inst-safe-source-shape : ∀ {c A B}
  → (safe : InstSafe c)
  → Wtʷ c A B
  → GenShape A
inst-safe-source-shape (n ↦ w) (w-↦ p q) = fun
inst-safe-source-shape (`∀ w) (w-∀ p) = all
inst-safe-source-shape (InstSafe.inst safe) (w-inst shapeA p) = all

inst-safe-target-shape : ∀ {c A B}
  → (safe : InstSafe c)
  → Wtʷ c A B
  → GenShape B
inst-safe-target-shape (n ↦ w) (w-↦ p q) = fun
inst-safe-target-shape (`∀ w) (w-∀ p) = all
inst-safe-target-shape (InstSafe.inst safe) (w-inst shapeA p) =
  inst-safe-target-shape safe p

gen-narrow-star⊥ : ∀ {c A}
  → GenShape A
  → Wtⁿ c A star
  → ⊥
gen-narrow-star⊥ () n-id★
gen-narrow-star⊥ () (n-untag-seq p)

narrowing-gen-forward : ∀ {c A B}
  → GenShape A
  → Wtⁿ c A B
  → (n : Narrowing c)
  → GenShape B
narrowing-gen-forward () n-id★ n
narrowing-gen-forward () n-idˣ n
narrowing-gen-forward () n-idι n
narrowing-gen-forward fun (n-↦ p q) (cross (w ↦ n)) = fun
narrowing-gen-forward all (n-∀ p) (cross (`∀ n)) = all
narrowing-gen-forward () n-untag-base n
narrowing-gen-forward () n-untag-base′ n
narrowing-gen-forward () n-untag-fun n
narrowing-gen-forward () (n-untag-seq p) n
narrowing-gen-forward () n-seal n
narrowing-gen-forward shapeA (n-seal-seq p) (n ︔seal X) =
  ⊥-elim (gen-narrow-star⊥ shapeA p)
narrowing-gen-forward shapeB (n-gen shapeA p)
    (Narrowing.gen safe) = all
narrowing-gen-forward () (n-gen-untag shapeA p) n

cross-narrowing-gen-backward : ∀ {c A B}
  → GenShape B
  → Wtⁿ c A B
  → (n : Crossⁿ c)
  → GenShape A
cross-narrowing-gen-backward () n-id★ n
cross-narrowing-gen-backward () n-idˣ n
cross-narrowing-gen-backward () n-idι n
cross-narrowing-gen-backward fun (n-↦ p q) (w ↦ n) = fun
cross-narrowing-gen-backward all (n-∀ p) (`∀ n) = all

widening-gen-backward : ∀ {c A B}
  → GenShape B
  → Wtʷ c A B
  → (w : Widening c)
  → GenShape A
widening-gen-backward () w-id★ w
widening-gen-backward () w-idˣ w
widening-gen-backward () w-idι w
widening-gen-backward fun (w-↦ p q) (cross (n ↦ w)) = fun
widening-gen-backward all (w-∀ p) (cross (`∀ w)) = all
widening-gen-backward () w-tag-base w
widening-gen-backward () w-tag-base′ w
widening-gen-backward () w-tag-fun w
widening-gen-backward () (w-tag-seq p) w
widening-gen-backward () w-unseal w
widening-gen-backward shapeB (w-inst shapeA p)
    (Widening.inst safe) = all
widening-gen-backward () (w-inst-tag shapeA p) w

cross-widening-gen-forward : ∀ {c A B}
  → GenShape A
  → Wtʷ c A B
  → (w : Crossʷ c)
  → GenShape B
cross-widening-gen-forward () w-id★ w
cross-widening-gen-forward () w-idˣ w
cross-widening-gen-forward () w-idι w
cross-widening-gen-forward fun (w-↦ p q) (n ↦ w) = fun
cross-widening-gen-forward all (w-∀ p) (`∀ w) = all

fun-narrow-star⊥ : ∀ {c}
  → Wtⁿ c (star ⇒ˢ star) star
  → ⊥
fun-narrow-star⊥ ()

cross-fun-all⊥ : ∀ {c A}
  → (n : Crossⁿ c)
  → Wtⁿ c (star ⇒ˢ star) (all A)
  → ⊥
cross-fun-all⊥ id ()
cross-fun-all⊥ (w ↦ n) ()
cross-fun-all⊥ (`∀ n) ()

cross-widen-all-fun⊥ : ∀ {c A}
  → (w : Crossʷ c)
  → Wtʷ c (all A) (star ⇒ˢ star)
  → ⊥
cross-widen-all-fun⊥ id ()
cross-widen-all-fun⊥ (n ↦ w) ()
cross-widen-all-fun⊥ (`∀ w) ()

cross-widen-star-fun⊥ : ∀ {c}
  → (w : Crossʷ c)
  → Wtʷ c star (star ⇒ˢ star)
  → ⊥
cross-widen-star-fun⊥ id ()
cross-widen-star-fun⊥ (n ↦ w) ()
cross-widen-star-fun⊥ (`∀ w) ()

unseal-seq-wt⊥ : ∀ {c X A B}
  → NonIdʷ c
  → Wtʷ (Coercions.unseal X ︔ c) A B
  → ⊥
unseal-seq-wt⊥ w (w-tag-seq ())

inst-tag-source-all : ∀ {c A B}
  → Wtʷ (inst c ︔ (★⇒★ !)) A B
  → ∃[ C ] A ≡ all C
inst-tag-source-all (w-tag-seq (w-inst shapeC p)) =
  _ , refl
inst-tag-source-all (w-inst-tag shapeC p) =
  _ , refl

------------------------------------------------------------------------
-- Identity shapes and normalized wrappers
------------------------------------------------------------------------

mutual

  id-shapeⁿ : ∀ {c A B} (n : Narrowing c)
    → Wtⁿ c A B
    → nonIdⁿ? n ≡ nothing
    → A ≡ B
  id-shapeⁿ (cross n) p eq
      with nonIdCrossⁿ? n | inspect nonIdCrossⁿ? n
  id-shapeⁿ (cross n) p () | just n′ | [ decision ]
  id-shapeⁿ (cross n) p eq | nothing | [ decision ] =
    id-cross-shapeⁿ n p decision
  id-shapeⁿ id n-id★ eq = refl
  id-shapeⁿ id n-idˣ eq = refl
  id-shapeⁿ id n-idι eq = refl
  id-shapeⁿ (gen n) p ()
  id-shapeⁿ (G ？) p ()
  id-shapeⁿ (G ？︔ n) p ()
  id-shapeⁿ (fun-？︔gen n) p ()
  id-shapeⁿ (seal X) p ()
  id-shapeⁿ (n ︔seal X) p ()

  id-cross-shapeⁿ : ∀ {c A B} (n : Crossⁿ c)
    → Wtⁿ c A B
    → nonIdCrossⁿ? n ≡ nothing
    → A ≡ B
  id-cross-shapeⁿ id n-id★ eq = refl
  id-cross-shapeⁿ id n-idˣ eq = refl
  id-cross-shapeⁿ id n-idι eq = refl
  id-cross-shapeⁿ (w ↦ n) (n-↦ p q) eq
      with nonIdʷ? w | inspect nonIdʷ? w
  id-cross-shapeⁿ (w ↦ n) (n-↦ p q) ()
      | just w′ | [ decision ]
  id-cross-shapeⁿ (w ↦ n) (n-↦ p q) eq
      | nothing | [ decision-w ]
      with nonIdⁿ? n | inspect nonIdⁿ? n
  id-cross-shapeⁿ (w ↦ n) (n-↦ p q) ()
      | nothing | [ decision-w ] | just n′ | [ decision-n ]
  id-cross-shapeⁿ (w ↦ n) (n-↦ p q) eq
      | nothing | [ decision-w ] | nothing | [ decision-n ] =
    cong₂ _⇒ˢ_ (sym (id-shapeʷ w p decision-w))
      (id-shapeⁿ n q decision-n)
  id-cross-shapeⁿ (`∀ n) (n-∀ p) eq
      with nonIdⁿ? n | inspect nonIdⁿ? n
  id-cross-shapeⁿ (`∀ n) (n-∀ p) ()
      | just n′ | [ decision ]
  id-cross-shapeⁿ (`∀ n) (n-∀ p) eq
      | nothing | [ decision ] =
    cong all (id-shapeⁿ n p decision)

  id-shapeʷ : ∀ {c A B} (w : Widening c)
    → Wtʷ c A B
    → nonIdʷ? w ≡ nothing
    → A ≡ B
  id-shapeʷ (cross w) p eq
      with nonIdCrossʷ? w | inspect nonIdCrossʷ? w
  id-shapeʷ (cross w) p () | just w′ | [ decision ]
  id-shapeʷ (cross w) p eq | nothing | [ decision ] =
    id-cross-shapeʷ w p decision
  id-shapeʷ id w-id★ eq = refl
  id-shapeʷ id w-idˣ eq = refl
  id-shapeʷ id w-idι eq = refl
  id-shapeʷ (inst w) p ()
  id-shapeʷ (G !) p ()
  id-shapeʷ (w ︔ G !) p ()
  id-shapeʷ (inst w ︔★⇒★!) p ()
  id-shapeʷ (unseal X) p ()
  id-shapeʷ (Widening.unseal_︔_ X w) p ()

  id-cross-shapeʷ : ∀ {c A B} (w : Crossʷ c)
    → Wtʷ c A B
    → nonIdCrossʷ? w ≡ nothing
    → A ≡ B
  id-cross-shapeʷ id w-id★ eq = refl
  id-cross-shapeʷ id w-idˣ eq = refl
  id-cross-shapeʷ id w-idι eq = refl
  id-cross-shapeʷ (n ↦ w) (w-↦ p q) eq
      with nonIdⁿ? n | inspect nonIdⁿ? n
  id-cross-shapeʷ (n ↦ w) (w-↦ p q) ()
      | just n′ | [ decision ]
  id-cross-shapeʷ (n ↦ w) (w-↦ p q) eq
      | nothing | [ decision-n ]
      with nonIdʷ? w | inspect nonIdʷ? w
  id-cross-shapeʷ (n ↦ w) (w-↦ p q) ()
      | nothing | [ decision-n ] | just w′ | [ decision-w ]
  id-cross-shapeʷ (n ↦ w) (w-↦ p q) eq
      | nothing | [ decision-n ] | nothing | [ decision-w ] =
    cong₂ _⇒ˢ_ (sym (id-shapeⁿ n p decision-n))
      (id-shapeʷ w q decision-w)
  id-cross-shapeʷ (`∀ w) (w-∀ p) eq
      with nonIdʷ? w | inspect nonIdʷ? w
  id-cross-shapeʷ (`∀ w) (w-∀ p) ()
      | just w′ | [ decision ]
  id-cross-shapeʷ (`∀ w) (w-∀ p) eq
      | nothing | [ decision ] =
    cong all (id-shapeʷ w p decision)

wrap-untag-fun-wt : ∀ {c B} (n : Crossⁿ c)
  → Wtⁿ c (star ⇒ˢ star) B
  → ∃[ u ] ∃[ r ]
      (wrap-？ⁿ ★⇒★ n ≡ (u , r)) × Wtⁿ u star B
wrap-untag-fun-wt n p
    with nonIdCrossⁿ? n | inspect nonIdCrossⁿ? n
wrap-untag-fun-wt n p | just n′ | [ decision ] =
  _ , _ , refl , n-untag-seq p
wrap-untag-fun-wt n p | nothing | [ decision ]
    with id-cross-shapeⁿ n p decision
wrap-untag-fun-wt n p | nothing | [ decision ] | refl =
  _ , _ , refl , n-untag-fun

wrap-seal-wt : ∀ {c A} (n : Narrowing c)
  → Wtⁿ c A star
  → (X : TyVar)
  → ∃[ u ] ∃[ r ]
      (wrap-sealⁿ n X ≡ (u , r)) × Wtⁿ u A var
wrap-seal-wt n p X with nonIdⁿ? n | inspect nonIdⁿ? n
wrap-seal-wt n p X | just n′ | [ decision ] =
  _ , _ , refl , n-seal-seq p
wrap-seal-wt n p X | nothing | [ decision ]
    with id-shapeⁿ n p decision
wrap-seal-wt n p X | nothing | [ decision ] | refl =
  _ , _ , refl , n-seal

wrap-tag-fun-wt : ∀ {c A} (w : Crossʷ c)
  → Wtʷ c A (star ⇒ˢ star)
  → ∃[ u ] ∃[ r ]
      (wrap-!ʷ w ★⇒★ ≡ (u , r)) × Wtʷ u A star
wrap-tag-fun-wt w p
    with nonIdCrossʷ? w | inspect nonIdCrossʷ? w
wrap-tag-fun-wt w p | just w′ | [ decision ] =
  _ , _ , refl , w-tag-seq p
wrap-tag-fun-wt w p | nothing | [ decision ]
    with id-cross-shapeʷ w p decision
wrap-tag-fun-wt w p | nothing | [ decision ] | refl =
  _ , _ , refl , w-tag-fun

nonid-widen-star⊥ : ∀ {c B}
  → NonIdʷ c
  → Wtʷ c star B
  → ⊥
nonid-widen-star⊥ (cross ()) w-id★

wrap-unseal-wt : ∀ {c B} (w : Widening c)
  → Wtʷ c star B
  → (X : TyVar)
  → ∃[ u ] ∃[ r ]
      (wrap-unsealʷ X w ≡ (u , r)) × Wtʷ u var B
wrap-unseal-wt w p X with nonIdʷ? w | inspect nonIdʷ? w
wrap-unseal-wt w p X | just w′ | [ decision ] =
  ⊥-elim (nonid-widen-star⊥ w′ p)
wrap-unseal-wt w p X | nothing | [ decision ]
    with id-shapeʷ w p decision
wrap-unseal-wt w p X | nothing | [ decision ] | refl =
  _ , _ , refl , w-unseal

------------------------------------------------------------------------
-- Fuel bounds
------------------------------------------------------------------------

size-rename : ∀ ρ c
  → coercion-size (renameᶜ ρ c) ≡ coercion-size c
size-rename ρ id = refl
size-rename ρ (s ︔ t)
  rewrite size-rename ρ s | size-rename ρ t = refl
size-rename ρ (s ↦ t)
  rewrite size-rename ρ s | size-rename ρ t = refl
size-rename ρ (`∀ s) rewrite size-rename (extᵗ ρ) s = refl
size-rename ρ (G !) = refl
size-rename ρ (G ？) = refl
size-rename ρ (seal α) = refl
size-rename ρ (unseal α) = refl
size-rename ρ (gen s) rewrite size-rename (extᵗ ρ) s = refl
size-rename ρ (inst s) rewrite size-rename (extᵗ ρ) s = refl
size-rename ρ error = refl

size-↦ˡ : ∀ s t
  → coercion-size s < coercion-size (s ↦ t)
size-↦ˡ s t = s≤s (m≤m+n (coercion-size s) (coercion-size t))

size-↦ʳ : ∀ s t
  → coercion-size t < coercion-size (s ↦ t)
size-↦ʳ s t = s≤s (m≤n+m (coercion-size t) (coercion-size s))

size-︔ˡ : ∀ s t
  → coercion-size s < coercion-size (s ︔ t)
size-︔ˡ s t = s≤s (m≤m+n (coercion-size s) (coercion-size t))

size-︔ʳ : ∀ s t
  → coercion-size t < coercion-size (s ︔ t)
size-︔ʳ s t = s≤s (m≤n+m (coercion-size t) (coercion-size s))

size-under : ∀ c
  → coercion-size c < suc (coercion-size c)
size-under c = n<1+n (coercion-size c)

sum-swap-smaller : ∀ {a b c d}
  → a < b
  → c < d
  → c + a < b + d
sum-swap-smaller {a} {b} {c} {d} a<b c<d =
  subst (λ n → n < b + d) (+-comm a c)
    (+-mono-< a<b c<d)

sum-right-smaller : ∀ {a b c}
  → b < c
  → a + b < a + c
sum-right-smaller {a} {b} {c} b<c =
  subst (λ n → n < a + c) (+-comm b a)
    (subst (λ n → b + a < n) (+-comm c a)
      (+-monoˡ-< a b<c))

sum-left-smaller : ∀ {a b c}
  → a < b
  → a + c < b + c
sum-left-smaller {c = c} a<b = +-monoˡ-< c a<b

lower-fuel : ∀ {small whole fuel}
  → small < whole
  → whole < suc fuel
  → small < fuel
lower-fuel small<whole whole<fuel =
  <-≤-trans small<whole (s≤s⁻¹ whole<fuel)

two-lower-fuel : ∀ {small whole fuel}
  → suc small < whole
  → whole < suc (suc fuel)
  → small < fuel
two-lower-fuel small<whole whole<fuel =
  s≤s⁻¹ (lower-fuel small<whole whole<fuel)

sum-two-smaller : ∀ {a b c d}
  → a < b
  → c < d
  → suc (a + c) < b + d
sum-two-smaller {a} {b} {c} {d} a<b c<d =
  subst (λ n → n ≤ b + d) (cong suc (+-suc a c))
    (+-mono-≤ a<b c<d)

sum-swap-two-smaller : ∀ {a b c d}
  → a < b
  → c < d
  → suc (c + a) < b + d
sum-swap-two-smaller {a} {b} {c} {d} a<b c<d =
  subst (λ n → suc n < b + d) (+-comm a c)
    (sum-two-smaller a<b c<d)

size-positive : ∀ c
  → suc zero ≤ coercion-size c
size-positive id = s≤s z≤n
size-positive (c ︔ d) = s≤s z≤n
size-positive (c ↦ d) = s≤s z≤n
size-positive (`∀ c) = s≤s z≤n
size-positive (G !) = s≤s z≤n
size-positive (G ？) = s≤s z≤n
size-positive (seal X) = s≤s z≤n
size-positive (unseal X) = s≤s z≤n
size-positive (gen c) = s≤s z≤n
size-positive (inst c) = s≤s z≤n
size-positive error = s≤s z≤n

size-sum-not-<1 : ∀ c d
  → coercion-size c + coercion-size d < suc zero
  → ⊥
size-sum-not-<1 c d bound
    with ≤-trans
      (s≤s (≤-trans (size-positive c)
        (m≤m+n (coercion-size c) (coercion-size d))))
      bound
size-sum-not-<1 c d bound | s≤s ()

compose-left-idⁿ : ∀ fuel {d B C}
  → (m : Narrowing d)
  → Wtⁿ d B C
  → ∃[ u ] ∃[ r ]
      (composeⁿ-fuel (suc fuel) id m ≡ just (u , r)) × Wtⁿ u B C
compose-left-idⁿ fuel (cross id) q = _ , _ , refl , q
compose-left-idⁿ fuel (cross (w ↦ n)) q = _ , _ , refl , q
compose-left-idⁿ fuel (cross (`∀ n)) q = _ , _ , refl , q
compose-left-idⁿ fuel id q = _ , _ , refl , q
compose-left-idⁿ fuel (gen n) q = _ , _ , refl , q
compose-left-idⁿ fuel (G ？) q = _ , _ , refl , q
compose-left-idⁿ fuel (G ？︔ n) q = _ , _ , refl , q
compose-left-idⁿ fuel (fun-？︔gen n) q = _ , _ , refl , q
compose-left-idⁿ fuel (seal X) q = _ , _ , refl , q
compose-left-idⁿ fuel (n ︔seal X) q = _ , _ , refl , q

compose-left-cross-idⁿ : ∀ fuel {d B C}
  → (m : Narrowing d)
  → Wtⁿ d B C
  → ∃[ u ] ∃[ r ]
      (composeⁿ-fuel (suc fuel) (cross id) m
        ≡ just (u , r)) × Wtⁿ u B C
compose-left-cross-idⁿ fuel (cross id) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (cross (w ↦ n)) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (cross (`∀ n)) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel id q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (gen n) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (G ？) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (G ？︔ n) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (fun-？︔gen n) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (seal X) q = _ , _ , refl , q
compose-left-cross-idⁿ fuel (n ︔seal X) q = _ , _ , refl , q

compose-left-idʷ : ∀ fuel {d B C}
  → (v : Widening d)
  → Wtʷ d B C
  → ∃[ u ] ∃[ r ]
      (composeʷ-fuel (suc fuel) id v ≡ just (u , r)) × Wtʷ u B C
compose-left-idʷ fuel (cross id) q = _ , _ , refl , q
compose-left-idʷ fuel (cross (n ↦ w)) q = _ , _ , refl , q
compose-left-idʷ fuel (cross (`∀ w)) q = _ , _ , refl , q
compose-left-idʷ fuel id q = _ , _ , refl , q
compose-left-idʷ fuel (inst w) q = _ , _ , refl , q
compose-left-idʷ fuel (G !) q = _ , _ , refl , q
compose-left-idʷ fuel (w ︔ G !) q = _ , _ , refl , q
compose-left-idʷ fuel (inst w ︔★⇒★!) q = _ , _ , refl , q
compose-left-idʷ fuel (unseal X) q = _ , _ , refl , q
compose-left-idʷ fuel (Widening.unseal_︔_ X w) q =
  _ , _ , refl , q

compose-left-cross-idʷ : ∀ fuel {d B C}
  → (v : Widening d)
  → Wtʷ d B C
  → ∃[ u ] ∃[ r ]
      (composeʷ-fuel (suc fuel) (cross id) v
        ≡ just (u , r)) × Wtʷ u B C
compose-left-cross-idʷ fuel (cross id) q = _ , _ , refl , q
compose-left-cross-idʷ fuel (cross (n ↦ w)) q = _ , _ , refl , q
compose-left-cross-idʷ fuel (cross (`∀ w)) q = _ , _ , refl , q
compose-left-cross-idʷ fuel id q = _ , _ , refl , q
compose-left-cross-idʷ fuel (inst w) q = _ , _ , refl , q
compose-left-cross-idʷ fuel (G !) q = _ , _ , refl , q
compose-left-cross-idʷ fuel (w ︔ G !) q = _ , _ , refl , q
compose-left-cross-idʷ fuel (inst w ︔★⇒★!) q =
  _ , _ , refl , q
compose-left-cross-idʷ fuel (unseal X) q = _ , _ , refl , q
compose-left-cross-idʷ fuel (Widening.unseal_︔_ X w) q =
  _ , _ , refl , q

data Activeⁿ : ∀ {c} → Narrowing c → Set where
  active-cross-↦ : ∀ {c d} {w : Widening c} {n : Narrowing d}
    → Activeⁿ (cross (w ↦ n))
  active-cross-∀ : ∀ {c} {n : Narrowing c}
    → Activeⁿ (cross (`∀ n))
  active-gen : ∀ {c} {safe : GenSafe c}
    → Activeⁿ (Narrowing.gen safe)
  active-untag : ∀ G → Activeⁿ (G ？)
  active-untag-seq : ∀ {c} G {n : NonIdCrossⁿ c}
    → Activeⁿ (G ？︔ n)
  active-untag-gen : ∀ {c} {safe : GenSafe c}
    → Activeⁿ (fun-？︔gen safe)
  active-seal : ∀ X → Activeⁿ (Narrowing.seal X)
  active-seal-seq : ∀ {c} {n : NonIdⁿ c} X
    → Activeⁿ (n ︔seal X)

data HeadViewⁿ : ∀ {c} → Narrowing c → Set where
  head-id : HeadViewⁿ id
  head-cross-id : HeadViewⁿ (cross id)
  head-active : ∀ {c} {n : Narrowing c}
    → Activeⁿ n
    → HeadViewⁿ n

head-viewⁿ : ∀ {c} (n : Narrowing c)
  → HeadViewⁿ n
head-viewⁿ (cross id) = head-cross-id
head-viewⁿ (cross (w ↦ n)) = head-active active-cross-↦
head-viewⁿ (cross (`∀ n)) = head-active active-cross-∀
head-viewⁿ id = head-id
head-viewⁿ (gen n) = head-active active-gen
head-viewⁿ (G ？) = head-active (active-untag G)
head-viewⁿ (G ？︔ n) = head-active (active-untag-seq G)
head-viewⁿ (fun-？︔gen n) = head-active active-untag-gen
head-viewⁿ (seal X) = head-active (active-seal X)
head-viewⁿ (n ︔seal X) = head-active (active-seal-seq X)

finish-seal-seqⁿ : ∀ fuel {c t u v X}
  {n : Narrowing c} {tⁿ : NonIdⁿ t}
  {uⁿ : Narrowing u} {vⁿ : Narrowing v}
  → Activeⁿ n
  → composeⁿ-fuel (suc fuel) n (nonIdⁿ→narrowing tⁿ)
      ≡ just (u , uⁿ)
  → wrap-sealⁿ uⁿ X ≡ (v , vⁿ)
  → composeⁿ-fuel (suc (suc fuel)) n (tⁿ ︔seal X)
      ≡ just (v , vⁿ)
finish-seal-seqⁿ fuel active-cross-↦ eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel active-cross-∀ eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel active-gen eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel (active-untag G) eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel (active-untag-seq G) eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel active-untag-gen eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel (active-seal X) eq eq-wrap
  rewrite eq | eq-wrap = refl
finish-seal-seqⁿ fuel (active-seal-seq X) eq eq-wrap
  rewrite eq | eq-wrap = refl

active-narrow-target-star⊥ : ∀ {c A} {n : Narrowing c}
  → Activeⁿ n
  → Wtⁿ c A star
  → ⊥
active-narrow-target-star⊥ active-cross-↦ ()
active-narrow-target-star⊥ active-cross-∀ ()
active-narrow-target-star⊥ active-gen ()
active-narrow-target-star⊥ (active-untag G) ()
active-narrow-target-star⊥ (active-untag-seq G)
    (n-untag-seq p) =
  fun-narrow-star⊥ p
active-narrow-target-star⊥ active-untag-gen (n-untag-seq p) =
  fun-narrow-star⊥ p
active-narrow-target-star⊥ (active-seal X) ()
active-narrow-target-star⊥ (active-seal-seq X)
    (n-untag-seq p) =
  fun-narrow-star⊥ p

compose-from-starⁿ : ∀ fuel {c d A C}
  → (n : Narrowing c)
  → (m : Narrowing d)
  → Wtⁿ c A star
  → Wtⁿ d star C
  → ∃[ u ] ∃[ r ]
      (composeⁿ-fuel (suc fuel) n m ≡ just (u , r)) × Wtⁿ u A C
compose-from-starⁿ fuel n m p q with head-viewⁿ n
compose-from-starⁿ fuel n m n-id★ q | head-id =
  compose-left-idⁿ fuel m q
compose-from-starⁿ fuel n m n-id★ q | head-cross-id =
  compose-left-cross-idⁿ fuel m q
compose-from-starⁿ fuel n m p q | head-active active =
  ⊥-elim (active-narrow-target-star⊥ active p)

------------------------------------------------------------------------
-- Fuel-indexed composition is total at composable shapes
------------------------------------------------------------------------

mutual

  composeⁿ-total-fuel : ∀ {fuel c d A B C}
    → (n : Narrowing c)
    → (m : Narrowing d)
    → Wtⁿ c A B
    → Wtⁿ d B C
    → coercion-size c + coercion-size d < fuel
    → ∃[ u ] ∃[ r ]
        (composeⁿ-fuel fuel n m ≡ just (u , r)) × Wtⁿ u A C
  composeⁿ-total-fuel {fuel = zero} n m p q ()
  composeⁿ-total-fuel {fuel = suc zero} {c = c} {d = d}
      n m p q bound =
    ⊥-elim (size-sum-not-<1 c d bound)

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n id p n-id★ bound =
    _ , _ , refl , p
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n id p n-idˣ bound =
    _ , _ , refl , p
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n id p n-idι bound =
    _ , _ , refl , p
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (cross id) p n-id★ bound =
    _ , _ , refl , p
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (cross id) p n-idˣ bound =
    _ , _ , refl , p
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (cross id) p n-idι bound =
    _ , _ , refl , p
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      id m n-id★ q bound
      with compose-left-idⁿ (suc fuel) m q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      id m n-id★ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      id m n-idˣ q bound
      with compose-left-idⁿ (suc fuel) m q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      id m n-idˣ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      id m n-idι q bound
      with compose-left-idⁿ (suc fuel) m q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      id m n-idι q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (cross id) m n-id★ q bound
      with compose-left-cross-idⁿ (suc fuel) m q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (cross id) m n-id★ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (cross id) m n-idˣ q bound
      with compose-left-cross-idⁿ (suc fuel) m q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (cross id) m n-idˣ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (cross id) m n-idι q bound
      with compose-left-cross-idⁿ (suc fuel) m q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (cross id) m n-idι q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      (cross (s₁ʷ ↦ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-↦ p₁ p₂) (n-↦ q₁ q₂) bound
      with composeʷ-total-fuel t₁ʷ s₁ʷ q₁ p₁
        (two-lower-fuel
          (sum-swap-two-smaller
            (size-↦ˡ s₁ s₂) (size-↦ˡ t₁ t₂))
          bound)
         | composeⁿ-total-fuel s₂ⁿ t₂ⁿ p₂ q₂
        (two-lower-fuel
          (sum-two-smaller
            (size-↦ʳ s₁ s₂) (size-↦ʳ t₁ t₂))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      (cross (s₁ʷ ↦ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-↦ p₁ p₂) (n-↦ q₁ q₂) bound
      | u₁ , u₁ʷ , eq₁ , r₁ | u₂ , u₂ⁿ , eq₂ , r₂
      rewrite eq₁ | eq₂ =
    _ , _ , refl , n-↦ r₁ r₂

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = `∀ t}
      (cross (`∀ sⁿ)) (cross (`∀ tⁿ))
      (n-∀ p) (n-∀ q) bound
      with composeⁿ-total-fuel sⁿ tⁿ p q
        (two-lower-fuel
          (sum-two-smaller (size-under s) (size-under t))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = `∀ t}
      (cross (`∀ sⁿ)) (cross (`∀ tⁿ))
      (n-∀ p) (n-∀ q) bound
      | u , uⁿ , eq , r rewrite eq =
    _ , _ , refl , n-∀ r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (★⇒★ ？) (cross (t₁ʷ ↦ t₂ⁿ))
      n-untag-fun (n-↦ q₁ q₂) bound
      with wrap-untag-fun-wt (t₁ʷ ↦ t₂ⁿ) (n-↦ q₁ q₂)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (★⇒★ ？) (cross (t₁ʷ ↦ t₂ⁿ))
      n-untag-fun (n-↦ q₁ q₂) bound
      | u , uⁿ , eq , r rewrite eq =
    u , uⁿ , refl , r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      (★⇒★ ？︔ (s₁ʷ ↦ˡ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-untag-seq (n-↦ p₁ p₂)) (n-↦ q₁ q₂) bound
      with composeʷ-total-fuel t₁ʷ
        (nonIdʷ→widening s₁ʷ) q₁ p₁
        (two-lower-fuel
          (sum-swap-two-smaller
            (<-trans (size-↦ˡ s₁ s₂)
              (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
            (size-↦ˡ t₁ t₂))
          bound)
         | composeⁿ-total-fuel s₂ⁿ t₂ⁿ p₂ q₂
        (two-lower-fuel
          (sum-two-smaller
            (<-trans (size-↦ʳ s₁ s₂)
              (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
            (size-↦ʳ t₁ t₂))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      (★⇒★ ？︔ (s₁ʷ ↦ˡ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-untag-seq (n-↦ p₁ p₂)) (n-↦ q₁ q₂) bound
      | u₁ , u₁ʷ , eq₁ , r₁ | u₂ , u₂ⁿ , eq₂ , r₂
      with wrap-untag-fun-wt (u₁ʷ ↦ u₂ⁿ) (n-↦ r₁ r₂)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      (★⇒★ ？︔ (s₁ʷ ↦ˡ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-untag-seq (n-↦ p₁ p₂)) (n-↦ q₁ q₂) bound
      | u₁ , u₁ʷ , eq₁ , r₁ | u₂ , u₂ⁿ , eq₂ , r₂
      | u , uⁿ , eq-wrap , r
      rewrite eq₁ | eq₂ | eq-wrap =
    u , uⁿ , refl , r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      (★⇒★ ？︔ (s₁ʷ ↦ʳ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-untag-seq (n-↦ p₁ p₂)) (n-↦ q₁ q₂) bound
      with composeʷ-total-fuel t₁ʷ s₁ʷ q₁ p₁
        (two-lower-fuel
          (sum-swap-two-smaller
            (<-trans (size-↦ˡ s₁ s₂)
              (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
            (size-↦ˡ t₁ t₂))
          bound)
         | composeⁿ-total-fuel
        (nonIdⁿ→narrowing s₂ⁿ) t₂ⁿ p₂ q₂
        (two-lower-fuel
          (sum-two-smaller
            (<-trans (size-↦ʳ s₁ s₂)
              (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
            (size-↦ʳ t₁ t₂))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      (★⇒★ ？︔ (s₁ʷ ↦ʳ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-untag-seq (n-↦ p₁ p₂)) (n-↦ q₁ q₂) bound
      | u₁ , u₁ʷ , eq₁ , r₁ | u₂ , u₂ⁿ , eq₂ , r₂
      with wrap-untag-fun-wt (u₁ʷ ↦ u₂ⁿ) (n-↦ r₁ r₂)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      (★⇒★ ？︔ (s₁ʷ ↦ʳ s₂ⁿ)) (cross (t₁ʷ ↦ t₂ⁿ))
      (n-untag-seq (n-↦ p₁ p₂)) (n-↦ q₁ q₂) bound
      | u₁ , u₁ʷ , eq₁ , r₁ | u₂ , u₂ⁿ , eq₂ , r₂
      | u , uⁿ , eq-wrap , r
      rewrite eq₁ | eq₂ | eq-wrap =
    u , uⁿ , refl , r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = `∀ t}
      (Narrowing.gen sⁿ) (cross (`∀ tⁿ))
      (n-gen shapeB p) (n-∀ q) bound
      with composeⁿ-total-fuel
        (genSafe→narrowing sⁿ) tⁿ p q
        (lower-fuel
          (+-mono-< (size-under s) (size-under t))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = `∀ t}
      (Narrowing.gen sⁿ) (cross (`∀ tⁿ))
      (n-gen shapeB p) (n-∀ q) bound
      | u , uⁿ , eq , r
      with gen-safe (gen-safe-source-shape sⁿ p)
        (narrowing-gen-forward shapeB q tⁿ) r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = `∀ t}
      (Narrowing.gen sⁿ) (cross (`∀ tⁿ))
      (n-gen shapeB p) (n-∀ q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen (narrowing-gen-forward shapeB q tⁿ) r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
      (n-gen-untag shapeB p) (n-∀ q) bound
      with composeⁿ-total-fuel
        (genSafe→narrowing sⁿ) tⁿ p q
        (lower-fuel
          (+-mono-<
            (<-trans (size-under s)
              (size-︔ʳ (★⇒★ ？) (gen s)))
            (size-under t))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
      (n-gen-untag shapeB p) (n-∀ q) bound
      | u , uⁿ , eq , r
      with gen-safe fun (narrowing-gen-forward shapeB q tⁿ) r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
      (n-gen-untag shapeB p) (n-∀ q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
    n-gen-untag (narrowing-gen-forward shapeB q tⁿ) r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
      (n-untag-seq (n-gen shapeB p)) (n-∀ q) bound
      with composeⁿ-total-fuel
        (genSafe→narrowing sⁿ) tⁿ p q
        (lower-fuel
          (+-mono-<
            (<-trans (size-under s)
              (size-︔ʳ (★⇒★ ？) (gen s)))
            (size-under t))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
      (n-untag-seq (n-gen shapeB p)) (n-∀ q) bound
      | u , uⁿ , eq , r
      with gen-safe fun (narrowing-gen-forward shapeB q tⁿ) r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      (fun-？︔gen sⁿ) (cross (`∀ tⁿ))
      (n-untag-seq (n-gen shapeB p)) (n-∀ q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
    n-gen-untag (narrowing-gen-forward shapeB q tⁿ) r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = gen t}
      (cross (s₁ʷ ↦ s₂ⁿ)) (Narrowing.gen tⁿ)
      (n-↦ p₁ p₂) (n-gen shapeC q) bound
      with composeⁿ-total-fuel
        (renameⁿ suc (cross (s₁ʷ ↦ s₂ⁿ)))
        (genSafe→narrowing tⁿ)
        (rename-wtⁿ suc (n-↦ p₁ p₂)) q
        (subst (λ k → k + coercion-size t < suc fuel)
          (sym (size-rename suc (s₁ ↦ s₂)))
          (lower-fuel
            (sum-right-smaller (size-under t))
            bound))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = gen t}
      (cross (s₁ʷ ↦ s₂ⁿ)) (Narrowing.gen tⁿ)
      (n-↦ p₁ p₂) (n-gen shapeC q) bound
      | u , uⁿ , eq , r
      with gen-safe fun shapeC r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = gen t}
      (cross (s₁ʷ ↦ s₂ⁿ)) (Narrowing.gen tⁿ)
      (n-↦ p₁ p₂) (n-gen shapeC q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen shapeC r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = gen t}
      (cross (`∀ sⁿ)) (Narrowing.gen tⁿ)
      (n-∀ p) (n-gen shapeC q) bound
      with composeⁿ-total-fuel
        (renameⁿ suc (cross (`∀ sⁿ)))
        (genSafe→narrowing tⁿ)
        (rename-wtⁿ suc (n-∀ p)) q
        (subst (λ k → k + coercion-size t < suc fuel)
          (sym (size-rename suc (`∀ s)))
          (lower-fuel
            (sum-right-smaller (size-under t))
            bound))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = gen t}
      (cross (`∀ sⁿ)) (Narrowing.gen tⁿ)
      (n-∀ p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r
      with gen-safe all shapeC r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = gen t}
      (cross (`∀ sⁿ)) (Narrowing.gen tⁿ)
      (n-∀ p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen shapeC r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = gen t}
      (Narrowing.gen sⁿ) (Narrowing.gen tⁿ)
      (n-gen shapeB p) (n-gen shapeC q) bound
      with composeⁿ-total-fuel
        (renameⁿ suc (Narrowing.gen sⁿ))
        (genSafe→narrowing tⁿ)
        (rename-wtⁿ suc (n-gen shapeB p)) q
        (subst (λ k → k + coercion-size t < suc fuel)
          (sym (size-rename suc (gen s)))
          (lower-fuel
            (sum-right-smaller (size-under t))
            bound))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = gen t}
      (Narrowing.gen sⁿ) (Narrowing.gen tⁿ)
      (n-gen shapeB p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r
      with gen-safe (gen-safe-source-shape sⁿ p) shapeC r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = gen t}
      (Narrowing.gen sⁿ) (Narrowing.gen tⁿ)
      (n-gen shapeB p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen shapeC r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (★⇒★ ？) (Narrowing.gen tⁿ)
      n-untag-fun (n-gen shapeC q) bound =
    _ , _ , refl , n-gen-untag shapeC q

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ s} {d = gen t}
      (★⇒★ ？︔ sⁿ) (Narrowing.gen tⁿ)
      (n-untag-seq p) (n-gen shapeC q) bound
      with composeⁿ-total-fuel
        (renameⁿ suc (cross (nonIdCrossⁿ→cross sⁿ)))
        (genSafe→narrowing tⁿ)
        (rename-wtⁿ suc p) q
        (subst (λ k → k + coercion-size t < suc fuel)
          (sym (size-rename suc s))
          (lower-fuel
            (+-mono-<
              (size-︔ʳ (★⇒★ ？) s) (size-under t))
            bound))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ s} {d = gen t}
      (★⇒★ ？︔ sⁿ) (Narrowing.gen tⁿ)
      (n-untag-seq p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r
      with gen-safe fun shapeC r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ s} {d = gen t}
      (★⇒★ ？︔ sⁿ) (Narrowing.gen tⁿ)
      (n-untag-seq p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen-untag shapeC r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      (fun-？︔gen sⁿ) (Narrowing.gen tⁿ)
      (n-gen-untag shapeB p) (n-gen shapeC q) bound
      with composeⁿ-total-fuel
        (renameⁿ suc (Narrowing.gen sⁿ))
        (genSafe→narrowing tⁿ)
        (rename-wtⁿ suc (n-gen shapeB p)) q
        (subst (λ k → k + coercion-size t < suc fuel)
          (sym (size-rename suc (gen s)))
          (lower-fuel
            (+-mono-<
              (size-︔ʳ (★⇒★ ？) (gen s)) (size-under t))
            bound))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      (fun-？︔gen sⁿ) (Narrowing.gen tⁿ)
      (n-gen-untag shapeB p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r
      with gen-safe fun shapeC r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      (fun-？︔gen sⁿ) (Narrowing.gen tⁿ)
      (n-gen-untag shapeB p) (n-gen shapeC q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen-untag shapeC r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      (fun-？︔gen sⁿ) (Narrowing.gen tⁿ)
      (n-untag-seq (n-gen shapeB p)) (n-gen shapeC q) bound
      with composeⁿ-total-fuel
        (renameⁿ suc (Narrowing.gen sⁿ))
        (genSafe→narrowing tⁿ)
        (rename-wtⁿ suc (n-gen shapeB p)) q
        (subst (λ k → k + coercion-size t < suc fuel)
          (sym (size-rename suc (gen s)))
          (lower-fuel
            (+-mono-<
              (size-︔ʳ (★⇒★ ？) (gen s)) (size-under t))
            bound))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      (fun-？︔gen sⁿ) (Narrowing.gen tⁿ)
      (n-untag-seq (n-gen shapeB p)) (n-gen shapeC q) bound
      | u , uⁿ , eq , r
      with gen-safe fun shapeC r uⁿ
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      (fun-？︔gen sⁿ) (Narrowing.gen tⁿ)
      (n-untag-seq (n-gen shapeB p)) (n-gen shapeC q) bound
      | u , uⁿ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , n-gen-untag shapeC r

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      n-untag-base (n-gen shapeC q) bound
      with gen-safe-source-shape tⁿ q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      n-untag-base (n-gen shapeC q) bound | ()
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      n-untag-base′ (n-gen shapeC q) bound
      with gen-safe-source-shape tⁿ q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      n-untag-base′ (n-gen shapeC q) bound | ()
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      n-seal (n-gen shapeC q) bound
      with gen-safe-source-shape tⁿ q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      n-seal (n-gen shapeC q) bound | ()
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      (n-seal-seq p) (n-gen shapeC q) bound
      with gen-safe-source-shape tⁿ q
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.gen tⁿ)
      (n-seal-seq p) (n-gen shapeC q) bound | ()

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      (★⇒★ ？︔ sⁿ) (cross (`∀ tⁿ))
      (n-untag-seq p) (n-∀ q) bound =
    ⊥-elim (cross-fun-all⊥ (nonIdCrossⁿ→cross sⁿ) p)

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n ((‵ `ℕ) ？) p n-untag-base bound =
    compose-from-starⁿ (suc fuel) n ((‵ `ℕ) ？) p n-untag-base
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n ((‵ `𝔹) ？) p n-untag-base′ bound =
    compose-from-starⁿ (suc fuel) n ((‵ `𝔹) ？) p n-untag-base′
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (★⇒★ ？) p n-untag-fun bound =
    compose-from-starⁿ (suc fuel) n (★⇒★ ？) p n-untag-fun
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (★⇒★ ？︔ tⁿ) p (n-untag-seq q) bound =
    compose-from-starⁿ (suc fuel) n (★⇒★ ？︔ tⁿ) p
      (n-untag-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (fun-？︔gen tⁿ) p
      (n-gen-untag shapeC q) bound =
    compose-from-starⁿ (suc fuel) n (fun-？︔gen tⁿ) p
      (n-gen-untag shapeC q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (fun-？︔gen tⁿ) p
      (n-untag-seq (n-gen shapeC q)) bound =
    compose-from-starⁿ (suc fuel) n (fun-？︔gen tⁿ) p
      (n-untag-seq (n-gen shapeC q))
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      n (Narrowing.seal X) p n-seal bound =
    compose-from-starⁿ (suc fuel) n (Narrowing.seal X) p n-seal

  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) p (n-seal-seq q) bound
      with head-viewⁿ n
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-id★ (n-seal-seq q) bound
      | head-id
      with compose-left-idⁿ (suc fuel) (tⁿ ︔seal X)
        (n-seal-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-id★ (n-seal-seq q) bound
      | head-id | u , uⁿ , eq , r =
    u , uⁿ , eq , r
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idˣ (n-seal-seq q) bound
      | head-id
      with compose-left-idⁿ (suc fuel) (tⁿ ︔seal X)
        (n-seal-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idˣ (n-seal-seq q) bound
      | head-id | u , uⁿ , eq , r =
    u , uⁿ , eq , r
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idι (n-seal-seq q) bound
      | head-id
      with compose-left-idⁿ (suc fuel) (tⁿ ︔seal X)
        (n-seal-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idι (n-seal-seq q) bound
      | head-id | u , uⁿ , eq , r =
    u , uⁿ , eq , r
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-id★ (n-seal-seq q) bound
      | head-cross-id
      with compose-left-cross-idⁿ (suc fuel) (tⁿ ︔seal X)
        (n-seal-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-id★ (n-seal-seq q) bound
      | head-cross-id | u , uⁿ , eq , r =
    u , uⁿ , eq , r
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idˣ (n-seal-seq q) bound
      | head-cross-id
      with compose-left-cross-idⁿ (suc fuel) (tⁿ ︔seal X)
        (n-seal-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idˣ (n-seal-seq q) bound
      | head-cross-id | u , uⁿ , eq , r =
    u , uⁿ , eq , r
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idι (n-seal-seq q) bound
      | head-cross-id
      with compose-left-cross-idⁿ (suc fuel) (tⁿ ︔seal X)
        (n-seal-seq q)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) n-idι (n-seal-seq q) bound
      | head-cross-id | u , uⁿ , eq , r =
    u , uⁿ , eq , r
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) p (n-seal-seq q) bound
      | head-active active
      with composeⁿ-total-fuel n (nonIdⁿ→narrowing tⁿ) p q
        (lower-fuel
          (sum-right-smaller (size-︔ˡ t (seal X)))
          bound)
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) p (n-seal-seq q) bound
      | head-active active | u , uⁿ , eq , r
      with wrap-seal-wt uⁿ r X
  composeⁿ-total-fuel {fuel = suc (suc fuel)}
      {d = t ︔ seal X}
      n (tⁿ ︔seal X) p (n-seal-seq q) bound
      | head-active active | u , uⁿ , eq , r
      | v , vⁿ , eq-wrap , v-wt =
    v , vⁿ , finish-seal-seqⁿ fuel active eq eq-wrap , v-wt

  composeʷ-total-fuel : ∀ {fuel c d A B C}
    → (w : Widening c)
    → (v : Widening d)
    → Wtʷ c A B
    → Wtʷ d B C
    → coercion-size c + coercion-size d < fuel
    → ∃[ u ] ∃[ r ]
        (composeʷ-fuel fuel w v ≡ just (u , r)) × Wtʷ u A C
  composeʷ-total-fuel {fuel = zero} w v p q ()
  composeʷ-total-fuel {fuel = suc zero} {c = c} {d = d}
      w v p q bound =
    ⊥-elim (size-sum-not-<1 c d bound)

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w id p w-id★ bound =
    _ , _ , refl , p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w id p w-idˣ bound =
    _ , _ , refl , p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w id p w-idι bound =
    _ , _ , refl , p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (cross id) p w-id★ bound =
    _ , _ , refl , p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (cross id) p w-idˣ bound =
    _ , _ , refl , p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (cross id) p w-idι bound =
    _ , _ , refl , p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      id v w-id★ q bound
      with compose-left-idʷ (suc fuel) v q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      id v w-id★ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      id v w-idˣ q bound
      with compose-left-idʷ (suc fuel) v q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      id v w-idˣ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      id v w-idι q bound
      with compose-left-idʷ (suc fuel) v q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      id v w-idι q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross id) v w-id★ q bound
      with compose-left-cross-idʷ (suc fuel) v q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross id) v w-id★ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross id) v w-idˣ q bound
      with compose-left-cross-idʷ (suc fuel) v q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross id) v w-idˣ q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross id) v w-idι q bound
      with compose-left-cross-idʷ (suc fuel) v q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross id) v w-idι q bound
      | u , r , eq , r-wt =
    u , r , eq , r-wt

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      (cross (s₁ⁿ ↦ s₂ʷ)) (cross (t₁ⁿ ↦ t₂ʷ))
      (w-↦ p₁ p₂) (w-↦ q₁ q₂) bound
      with composeⁿ-total-fuel t₁ⁿ s₁ⁿ q₁ p₁
        (two-lower-fuel
          (sum-swap-two-smaller
            (size-↦ˡ s₁ s₂) (size-↦ˡ t₁ t₂))
          bound)
         | composeʷ-total-fuel s₂ʷ t₂ʷ p₂ q₂
        (two-lower-fuel
          (sum-two-smaller
            (size-↦ʳ s₁ s₂) (size-↦ʳ t₁ t₂))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      (cross (s₁ⁿ ↦ s₂ʷ)) (cross (t₁ⁿ ↦ t₂ʷ))
      (w-↦ p₁ p₂) (w-↦ q₁ q₂) bound
      | u₁ , u₁ⁿ , eq₁ , r₁ | u₂ , u₂ʷ , eq₂ , r₂
      rewrite eq₁ | eq₂ =
    _ , _ , refl , w-↦ r₁ r₂

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = `∀ t}
      (cross (`∀ sʷ)) (cross (`∀ tʷ))
      (w-∀ p) (w-∀ q) bound
      with composeʷ-total-fuel sʷ tʷ p q
        (two-lower-fuel
          (sum-two-smaller (size-under s) (size-under t))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = `∀ t}
      (cross (`∀ sʷ)) (cross (`∀ tʷ))
      (w-∀ p) (w-∀ q) bound
      | u , uʷ , eq , r rewrite eq =
    _ , _ , refl , w-∀ r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross (s₁ⁿ ↦ s₂ʷ)) (★⇒★ !)
      (w-↦ p₁ p₂) w-tag-fun bound
      with wrap-tag-fun-wt (s₁ⁿ ↦ s₂ʷ) (w-↦ p₁ p₂)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (cross (s₁ⁿ ↦ s₂ʷ)) (★⇒★ !)
      (w-↦ p₁ p₂) w-tag-fun bound
      | u , uʷ , eq , r rewrite eq =
    u , uʷ , refl , r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      (cross (s₁ⁿ ↦ s₂ʷ)) ((t₁ⁿ ↦ˡ t₂ʷ) ︔ ★⇒★ !)
      (w-↦ p₁ p₂) (w-tag-seq (w-↦ q₁ q₂)) bound
      with composeⁿ-total-fuel
        (nonIdⁿ→narrowing t₁ⁿ) s₁ⁿ q₁ p₁
        (two-lower-fuel
          (sum-swap-two-smaller
            (size-↦ˡ s₁ s₂)
            (<-trans (size-↦ˡ t₁ t₂)
              (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
          bound)
         | composeʷ-total-fuel s₂ʷ t₂ʷ p₂ q₂
        (two-lower-fuel
          (sum-two-smaller
            (size-↦ʳ s₁ s₂)
            (<-trans (size-↦ʳ t₁ t₂)
              (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      (cross (s₁ⁿ ↦ s₂ʷ)) ((t₁ⁿ ↦ˡ t₂ʷ) ︔ ★⇒★ !)
      (w-↦ p₁ p₂) (w-tag-seq (w-↦ q₁ q₂)) bound
      | u₁ , u₁ⁿ , eq₁ , r₁ | u₂ , u₂ʷ , eq₂ , r₂
      with wrap-tag-fun-wt (u₁ⁿ ↦ u₂ʷ) (w-↦ r₁ r₂)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      (cross (s₁ⁿ ↦ s₂ʷ)) ((t₁ⁿ ↦ˡ t₂ʷ) ︔ ★⇒★ !)
      (w-↦ p₁ p₂) (w-tag-seq (w-↦ q₁ q₂)) bound
      | u₁ , u₁ⁿ , eq₁ , r₁ | u₂ , u₂ʷ , eq₂ , r₂
      | u , uʷ , eq-wrap , r
      rewrite eq₁ | eq₂ | eq-wrap =
    u , uʷ , refl , r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      (cross (s₁ⁿ ↦ s₂ʷ)) ((t₁ⁿ ↦ʳ t₂ʷ) ︔ ★⇒★ !)
      (w-↦ p₁ p₂) (w-tag-seq (w-↦ q₁ q₂)) bound
      with composeⁿ-total-fuel t₁ⁿ s₁ⁿ q₁ p₁
        (two-lower-fuel
          (sum-swap-two-smaller
            (size-↦ˡ s₁ s₂)
            (<-trans (size-↦ˡ t₁ t₂)
              (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
          bound)
         | composeʷ-total-fuel s₂ʷ
        (nonIdʷ→widening t₂ʷ) p₂ q₂
        (two-lower-fuel
          (sum-two-smaller
            (size-↦ʳ s₁ s₂)
            (<-trans (size-↦ʳ t₁ t₂)
              (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      (cross (s₁ⁿ ↦ s₂ʷ)) ((t₁ⁿ ↦ʳ t₂ʷ) ︔ ★⇒★ !)
      (w-↦ p₁ p₂) (w-tag-seq (w-↦ q₁ q₂)) bound
      | u₁ , u₁ⁿ , eq₁ , r₁ | u₂ , u₂ʷ , eq₂ , r₂
      with wrap-tag-fun-wt (u₁ⁿ ↦ u₂ʷ) (w-↦ r₁ r₂)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      (cross (s₁ⁿ ↦ s₂ʷ)) ((t₁ⁿ ↦ʳ t₂ʷ) ︔ ★⇒★ !)
      (w-↦ p₁ p₂) (w-tag-seq (w-↦ q₁ q₂)) bound
      | u₁ , u₁ⁿ , eq₁ , r₁ | u₂ , u₂ʷ , eq₂ , r₂
      | u , uʷ , eq-wrap , r
      rewrite eq₁ | eq₂ | eq-wrap =
    u , uʷ , refl , r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      (w-∀ p) (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-all-fun⊥ (nonIdCrossʷ→cross tʷ) q)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      w-tag-base (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-star-fun⊥ (nonIdCrossʷ→cross tʷ) q)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      w-tag-base′ (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-star-fun⊥ (nonIdCrossʷ→cross tʷ) q)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      w-tag-fun (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-star-fun⊥ (nonIdCrossʷ→cross tʷ) q)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      (w-tag-seq p) (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-star-fun⊥ (nonIdCrossʷ→cross tʷ) q)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      w-unseal (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-star-fun⊥ (nonIdCrossʷ→cross tʷ) q)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (tʷ ︔ ★⇒★ !)
      (w-inst-tag shapeA p) (w-tag-seq q) bound =
    ⊥-elim
      (cross-widen-star-fun⊥ (nonIdCrossʷ→cross tʷ) q)

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t}
      (cross (`∀ sʷ)) (Widening.inst tʷ)
      (w-∀ p) (w-inst shapeB q) bound
      with composeʷ-total-fuel
        sʷ (instSafe→widening tʷ) p q
        (lower-fuel
          (+-mono-< (size-under s) (size-under t))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t}
      (cross (`∀ sʷ)) (Widening.inst tʷ)
      (w-∀ p) (w-inst shapeB q) bound
      | u , uʷ , eq , r
      with inst-safe
        (widening-gen-backward shapeB p sʷ)
        (inst-safe-target-shape tʷ q) r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t}
      (cross (`∀ sʷ)) (Widening.inst tʷ)
      (w-∀ p) (w-inst shapeB q) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst (widening-gen-backward shapeB p sʷ) r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t₁ ↦ t₂}
      (Widening.inst sʷ) (cross (t₁ⁿ ↦ t₂ʷ))
      (w-inst shapeA p) (w-↦ q₁ q₂) bound
      with composeʷ-total-fuel
        (instSafe→widening sʷ)
        (renameʷ suc (cross (t₁ⁿ ↦ t₂ʷ)))
        p (rename-wtʷ suc (w-↦ q₁ q₂))
        (subst (λ k → coercion-size s + k < suc fuel)
          (sym (size-rename suc (t₁ ↦ t₂)))
          (lower-fuel
            (sum-left-smaller (size-under s))
            bound))
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t₁ ↦ t₂}
      (Widening.inst sʷ) (cross (t₁ⁿ ↦ t₂ʷ))
      (w-inst shapeA p) (w-↦ q₁ q₂) bound
      | u , uʷ , eq , r
      with inst-safe shapeA
        (cross-widening-gen-forward
          (inst-safe-target-shape sʷ p)
          (w-↦ q₁ q₂) (t₁ⁿ ↦ t₂ʷ))
        r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t₁ ↦ t₂}
      (Widening.inst sʷ) (cross (t₁ⁿ ↦ t₂ʷ))
      (w-inst shapeA p) (w-↦ q₁ q₂) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst shapeA r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = `∀ t}
      (Widening.inst sʷ) (cross (`∀ tʷ))
      (w-inst shapeA p) (w-∀ q) bound
      with composeʷ-total-fuel
        (instSafe→widening sʷ)
        (renameʷ suc (cross (`∀ tʷ)))
        p (rename-wtʷ suc (w-∀ q))
        (subst (λ k → coercion-size s + k < suc fuel)
          (sym (size-rename suc (`∀ t)))
          (lower-fuel
            (sum-left-smaller (size-under s))
            bound))
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = `∀ t}
      (Widening.inst sʷ) (cross (`∀ tʷ))
      (w-inst shapeA p) (w-∀ q) bound
      | u , uʷ , eq , r
      with inst-safe shapeA all r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = `∀ t}
      (Widening.inst sʷ) (cross (`∀ tʷ))
      (w-inst shapeA p) (w-∀ q) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst shapeA r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t}
      (Widening.inst sʷ) (Widening.inst tʷ)
      (w-inst shapeA p) (w-inst shapeB q) bound
      with composeʷ-total-fuel
        (instSafe→widening sʷ)
        (renameʷ suc (Widening.inst tʷ))
        p (rename-wtʷ suc (w-inst shapeB q))
        (subst (λ k → coercion-size s + k < suc fuel)
          (sym (size-rename suc (inst t)))
          (lower-fuel
            (sum-left-smaller (size-under s))
            bound))
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t}
      (Widening.inst sʷ) (Widening.inst tʷ)
      (w-inst shapeA p) (w-inst shapeB q) bound
      | u , uʷ , eq , r
      with inst-safe shapeA (inst-safe-target-shape tʷ q) r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t}
      (Widening.inst sʷ) (Widening.inst tʷ)
      (w-inst shapeA p) (w-inst shapeB q) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst shapeA r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) (★⇒★ !)
      (w-inst shapeA p) w-tag-fun bound =
    _ , _ , refl , w-inst-tag shapeA p

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (tʷ ︔ ★⇒★ !)
      (w-inst shapeA p) (w-tag-seq q) bound
      with composeʷ-total-fuel
        (instSafe→widening sʷ)
        (renameʷ suc (cross (nonIdCrossʷ→cross tʷ)))
        p (rename-wtʷ suc q)
        (subst (λ k → coercion-size s + k < suc fuel)
          (sym (size-rename suc t))
          (lower-fuel
            (+-mono-<
              (size-under s) (size-︔ˡ t (★⇒★ !)))
            bound))
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (tʷ ︔ ★⇒★ !)
      (w-inst shapeA p) (w-tag-seq q) bound
      | u , uʷ , eq , r
      with inst-safe shapeA fun r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (tʷ ︔ ★⇒★ !)
      (w-inst shapeA p) (w-tag-seq q) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst-tag shapeA r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (inst tʷ ︔★⇒★!)
      (w-inst shapeA p) (w-inst-tag shapeB q) bound
      with composeʷ-total-fuel
        (instSafe→widening sʷ)
        (renameʷ suc (Widening.inst tʷ))
        p (rename-wtʷ suc (w-inst shapeB q))
        (subst (λ k → coercion-size s + k < suc fuel)
          (sym (size-rename suc (inst t)))
          (lower-fuel
            (+-mono-<
              (size-under s)
              (size-︔ˡ (inst t) (★⇒★ !)))
            bound))
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (inst tʷ ︔★⇒★!)
      (w-inst shapeA p) (w-inst-tag shapeB q) bound
      | u , uʷ , eq , r
      with inst-safe shapeA fun r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (inst tʷ ︔★⇒★!)
      (w-inst shapeA p) (w-inst-tag shapeB q) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst-tag shapeA r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      (cross (`∀ sʷ)) (inst tʷ ︔★⇒★!)
      (w-∀ p) (w-inst-tag shapeB q) bound
      with composeʷ-total-fuel
        sʷ (instSafe→widening tʷ) p q
        (two-lower-fuel
          (sum-two-smaller
            (size-under s)
            (<-trans (size-under t)
              (size-︔ˡ (inst t) (★⇒★ !))))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      (cross (`∀ sʷ)) (inst tʷ ︔★⇒★!)
      (w-∀ p) (w-inst-tag shapeB q) bound
      | u , uʷ , eq , r
      with inst-safe (widening-gen-backward shapeB p sʷ) fun r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      (cross (`∀ sʷ)) (inst tʷ ︔★⇒★!)
      (w-∀ p) (w-inst-tag shapeB q) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
    w-inst-tag (widening-gen-backward shapeB p sʷ) r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      (cross (`∀ sʷ)) (inst tʷ ︔★⇒★!)
      (w-∀ p) (w-tag-seq (w-inst shapeB q)) bound
      with composeʷ-total-fuel
        sʷ (instSafe→widening tʷ) p q
        (two-lower-fuel
          (sum-two-smaller
            (size-under s)
            (<-trans (size-under t)
              (size-︔ˡ (inst t) (★⇒★ !))))
          bound)
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      (cross (`∀ sʷ)) (inst tʷ ︔★⇒★!)
      (w-∀ p) (w-tag-seq (w-inst shapeB q)) bound
      | u , uʷ , eq , r
      with inst-safe (widening-gen-backward shapeB p sʷ) fun r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      (cross (`∀ sʷ)) (inst tʷ ︔★⇒★!)
      (w-∀ p) (w-tag-seq (w-inst shapeB q)) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
    w-inst-tag (widening-gen-backward shapeB p sʷ) r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (inst tʷ ︔★⇒★!)
      (w-inst shapeA p) (w-tag-seq (w-inst shapeB q)) bound
      with composeʷ-total-fuel
        (instSafe→widening sʷ)
        (renameʷ suc (Widening.inst tʷ))
        p (rename-wtʷ suc (w-inst shapeB q))
        (subst (λ k → coercion-size s + k < suc fuel)
          (sym (size-rename suc (inst t)))
          (lower-fuel
            (+-mono-<
              (size-under s)
              (size-︔ˡ (inst t) (★⇒★ !)))
            bound))
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (inst tʷ ︔★⇒★!)
      (w-inst shapeA p) (w-tag-seq (w-inst shapeB q)) bound
      | u , uʷ , eq , r
      with inst-safe shapeA fun r uʷ
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      (Widening.inst sʷ) (inst tʷ ︔★⇒★!)
      (w-inst shapeA p) (w-tag-seq (w-inst shapeB q)) bound
      | u , uʷ , eq , r | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl , w-inst-tag shapeA r

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) ((‵ `ℕ) !)
      (w-inst shapeA p) w-tag-base bound
      with inst-safe-target-shape sʷ p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) ((‵ `ℕ) !)
      (w-inst shapeA p) w-tag-base bound | ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) ((‵ `𝔹) !)
      (w-inst shapeA p) w-tag-base′ bound
      with inst-safe-target-shape sʷ p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) ((‵ `𝔹) !)
      (w-inst shapeA p) w-tag-base′ bound | ()

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) (Widening.unseal X)
      (w-inst shapeA p) w-unseal bound
      with inst-safe-target-shape sʷ p
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      (Widening.inst sʷ) (Widening.unseal X)
      (w-inst shapeA p) w-unseal bound | ()

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) (w-↦ p₁ p₂) q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) (w-↦ p₁ p₂) q bound | C , ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-tag-base q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-tag-base q bound | C , ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-tag-base′ q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-tag-base′ q bound | C , ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-tag-fun q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-tag-fun q bound | C , ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) (w-tag-seq p) q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) (w-tag-seq p) q bound | C , ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-unseal q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) w-unseal q bound | C , ()
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) (w-inst-tag shapeA p) q bound
      with inst-tag-source-all q
  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (inst tʷ ︔★⇒★!) (w-inst-tag shapeA p) q bound | C , ()

  composeʷ-total-fuel {fuel = suc (suc fuel)}
      w (Widening.unseal_︔_ X v) p q bound =
    ⊥-elim (unseal-seq-wt⊥ v q)

------------------------------------------------------------------------
-- Composition typing with one shared world
------------------------------------------------------------------------

renameSecond : Renameᵗ → ImpAssm → ImpAssm
renameSecond ρ (X ˣ⊑★) = X ˣ⊑★
renameSecond ρ (X ˣ⊑ˣ Y) = X ˣ⊑ˣ ρ Y

renameSecond-⇑ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ⇑ᵢ Φ
  → renameSecond (extᵗ ρ) a ∈ ⇑ᵢ Ψ
renameSecond-⇑ {Φ = []} h ()
renameSecond-⇑ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (X ˣ⊑★) ∈ Ψ
    → (suc X ˣ⊑★) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (X ˣ⊑ˣ ρ Y) ∈ Ψ
    → (suc X ˣ⊑ˣ suc (ρ Y)) ∈ ⇑ᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ {Φ = _ ∷ Φ} h (there X∈) =
  renameSecond-⇑ (λ Y∈ → h (there Y∈)) X∈

renameSecond-all : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
  → renameSecond (extᵗ ρ) a
      ∈ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ)
renameSecond-all h (here refl) = here refl
renameSecond-all h (there X∈) =
  there (renameSecond-⇑ h X∈)

renameSecond-⇑ᴸ : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ⇑ᴸᵢ Φ
  → renameSecond ρ a ∈ ⇑ᴸᵢ Ψ
renameSecond-⇑ᴸ {Φ = []} h ()
renameSecond-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑★) ∷ Φ} h
    (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X}
    → (X ˣ⊑★) ∈ Ψ
    → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ᴸ {ρ = ρ} {Φ = (_ ˣ⊑ˣ _) ∷ Φ} h
    (here refl) =
  map-head (h (here refl))
  where
  map-head : ∀ {Ψ X Y}
    → (X ˣ⊑ˣ ρ Y) ∈ Ψ
    → (suc X ˣ⊑ˣ ρ Y) ∈ ⇑ᴸᵢ Ψ
  map-head {Ψ = (_ ˣ⊑★) ∷ Ψ} (there X∈) =
    there (map-head X∈)
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (here refl) = here refl
  map-head {Ψ = (_ ˣ⊑ˣ _) ∷ Ψ} (there X∈) =
    there (map-head X∈)
renameSecond-⇑ᴸ {Φ = _ ∷ Φ} h (there X∈) =
  renameSecond-⇑ᴸ (λ Y∈ → h (there Y∈)) X∈

renameSecond-gen : ∀ {ρ Φ Ψ a}
  → (∀ {b} → b ∈ Φ → renameSecond ρ b ∈ Ψ)
  → a ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
  → renameSecond ρ a ∈ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
renameSecond-gen h (here refl) = here refl
renameSecond-gen h (there X∈) =
  there (renameSecond-⇑ᴸ h X∈)

mutual

  rename-targetʷ : ∀ {ρ Φ Ψ Δᴸ Δᴿ Δᴿ′ c A B}
      {w : Widening c}
    → (∀ {a} → a ∈ Φ → renameSecond ρ a ∈ Ψ)
    → TyRenameWf Δᴿ Δᴿ′ ρ
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ ⊢ w ⦂ A ⊑ renameᵗ ρ B ⊣ Δᴿ′
  rename-targetʷ h hρ id★ = id★
  rename-targetʷ h hρ (idˣ X∈ X<Δᴸ Y<Δᴿ) =
    idˣ (h X∈) X<Δᴸ (hρ Y<Δᴿ)
  rename-targetʷ h hρ idι = idι
  rename-targetʷ h hρ (p ↦ q) =
    rename-sourceⁿ h hρ p ↦ rename-targetʷ h hρ q
  rename-targetʷ h hρ (∀ⁱ p) =
    ∀ⁱ (rename-targetʷ (renameSecond-all h)
          (TyRenameWf-ext hρ) p)
  rename-targetʷ h hρ (tag ι) = tag ι
  rename-targetʷ h hρ tag⇒ = tag⇒
  rename-targetʷ h hρ (tag p ↦ˡ q) =
    tag rename-sourceⁿ h hρ p ↦ˡ rename-targetʷ h hρ q
  rename-targetʷ h hρ (tag p ↦ʳ q) =
    tag rename-sourceⁿ h hρ p ↦ʳ rename-targetʷ h hρ q
  rename-targetʷ h hρ (tagˣ X∈ X<Δᴸ) =
    tagˣ (h X∈) X<Δᴸ
  rename-targetʷ h hρ (inst nonvar occ p) =
    inst nonvar occ
      (rename-targetʷ (renameSecond-gen h) hρ p)
  rename-targetʷ h hρ (inst-tag nonvar occ p) =
    inst-tag nonvar occ
      (rename-targetʷ (renameSecond-gen h) hρ p)

  rename-sourceⁿ : ∀ {ρ Φ Ψ Δᴸ Δᴸ′ Δᴿ c A B}
      {n : Narrowing c}
    → (∀ {a} → a ∈ Φ → renameSecond ρ a ∈ Ψ)
    → TyRenameWf Δᴸ Δᴸ′ ρ
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → Ψ ∣ Δᴸ′ ⊢ n ⦂ renameᵗ ρ A ⊒ B ⊣ Δᴿ
  rename-sourceⁿ h hρ id★ = id★
  rename-sourceⁿ h hρ (idˣ X∈ X<Δᴸ Y<Δᴿ) =
    idˣ (h X∈) (hρ X<Δᴸ) Y<Δᴿ
  rename-sourceⁿ h hρ idι = idι
  rename-sourceⁿ h hρ (p ↦ q) =
    rename-targetʷ h hρ p ↦ rename-sourceⁿ h hρ q
  rename-sourceⁿ h hρ (∀ⁱ p) =
    ∀ⁱ (rename-sourceⁿ (renameSecond-all h)
          (TyRenameWf-ext hρ) p)
  rename-sourceⁿ h hρ (untag ι) = untag ι
  rename-sourceⁿ h hρ untag⇒ = untag⇒
  rename-sourceⁿ h hρ (untag p ↦ˡ q) =
    untag rename-targetʷ h hρ p ↦ˡ rename-sourceⁿ h hρ q
  rename-sourceⁿ h hρ (untag p ↦ʳ q) =
    untag rename-targetʷ h hρ p ↦ʳ rename-sourceⁿ h hρ q
  rename-sourceⁿ h hρ (untagˣ X∈ X<Δᴿ) =
    untagˣ (h X∈) X<Δᴿ
  rename-sourceⁿ h hρ (gen nonvar occ p) =
    gen nonvar occ
      (rename-sourceⁿ (renameSecond-gen h) hρ p)
  rename-sourceⁿ h hρ (gen-untag nonvar occ p) =
    gen-untag nonvar occ
      (rename-sourceⁿ (renameSecond-gen h) hρ p)

renameSecond-suc : ∀ {Φ a}
  → a ∈ Φ
  → renameSecond suc a ∈ ⇑ᴿᵢ Φ
renameSecond-suc {Φ = (_ ˣ⊑★) ∷ Φ} {a = X ˣ⊑★}
    (here refl) =
  here refl
renameSecond-suc {Φ = (_ ˣ⊑★) ∷ Φ} {a = X ˣ⊑★}
    (there X∈) =
  there (renameSecond-suc X∈)
renameSecond-suc {Φ = (_ ˣ⊑ˣ _) ∷ Φ} {a = X ˣ⊑★}
    (there X∈) =
  there (renameSecond-suc X∈)
renameSecond-suc {Φ = (_ ˣ⊑★) ∷ Φ} {a = X ˣ⊑ˣ Y}
    (there X∈) =
  there (renameSecond-suc X∈)
renameSecond-suc {Φ = (_ ˣ⊑ˣ _) ∷ Φ} {a = X ˣ⊑ˣ Y}
    (here refl) =
  here refl
renameSecond-suc {Φ = (_ ˣ⊑ˣ _) ∷ Φ} {a = X ˣ⊑ˣ Y}
    (there X∈) =
  there (renameSecond-suc X∈)

target-liftʷ : ∀ {Φ Δᴸ Δᴿ c A B} {w : Widening c}
  → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  → ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
target-liftʷ =
  rename-targetʷ renameSecond-suc (λ X<Δ → s≤s X<Δ)

source-liftⁿ : ∀ {Φ Δᴸ Δᴿ c A B} {n : Narrowing c}
  → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  → ⇑ᴿᵢ Φ ∣ suc Δᴸ ⊢ n ⦂ ⇑ᵗ A ⊒ B ⊣ Δᴿ
source-liftⁿ =
  rename-sourceⁿ renameSecond-suc (λ X<Δ → s≤s X<Δ)

⇑ᴿ-⇑ᴸ : ∀ Φ
  → ⇑ᴿᵢ (⇑ᴸᵢ Φ) ≡ ⇑ᵢ Φ
⇑ᴿ-⇑ᴸ [] = refl
⇑ᴿ-⇑ᴸ ((X ˣ⊑★) ∷ Φ) =
  cong ((suc X ˣ⊑★) ∷_) (⇑ᴿ-⇑ᴸ Φ)
⇑ᴿ-⇑ᴸ ((X ˣ⊑ˣ Y) ∷ Φ) =
  cong ((suc X ˣ⊑ˣ suc Y) ∷_) (⇑ᴿ-⇑ᴸ Φ)

source-lift-genⁿ : ∀ {Φ Δᴸ Δᴿ c A B}
    {n : Narrowing c}
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ suc Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ n ⦂ ⇑ᵗ A ⊒ B ⊣ suc Δᴿ
source-lift-genⁿ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} {n = n} p =
  subst
    (λ Ψ → Ψ ∣ suc Δᴸ ⊢ n ⦂ ⇑ᵗ A ⊒ B ⊣ suc Δᴿ)
    (cong ((zero ˣ⊑★) ∷_) (⇑ᴿ-⇑ᴸ Φ))
    (source-liftⁿ p)

target-lift-genʷ : ∀ {Φ Δᴸ Δᴿ c A B}
    {w : Widening c}
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ w ⦂ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
target-lift-genʷ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {B = B} {w = w} p =
  subst
    (λ Ψ → Ψ ∣ suc Δᴸ ⊢ w ⦂ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ)
    (cong ((zero ˣ⊑★) ∷_) (⇑ᴿ-⇑ᴸ Φ))
    (target-liftʷ p)

genSafe?-sound : ∀ {c} (n : Narrowing c) {safe}
  → genSafe? n ≡ just safe
  → genSafe→narrowing safe ≡ n
genSafe?-sound (cross id) ()
genSafe?-sound (cross (w ↦ n)) refl = refl
genSafe?-sound (cross (`∀ n)) refl = refl
genSafe?-sound id ()
genSafe?-sound (gen safe) refl = refl
genSafe?-sound (G ？) ()
genSafe?-sound (G ？︔ n) ()
genSafe?-sound (fun-？︔gen safe) ()
genSafe?-sound (seal X) ()
genSafe?-sound (n ︔seal X) ()

instSafe?-sound : ∀ {c} (w : Widening c) {safe}
  → instSafe? w ≡ just safe
  → instSafe→widening safe ≡ w
instSafe?-sound (cross id) ()
instSafe?-sound (cross (n ↦ w)) refl = refl
instSafe?-sound (cross (`∀ w)) refl = refl
instSafe?-sound id ()
instSafe?-sound (inst safe) refl = refl
instSafe?-sound (G !) ()
instSafe?-sound (w ︔ G !) ()
instSafe?-sound (inst w ︔★⇒★!) ()
instSafe?-sound (unseal X) ()
instSafe?-sound (Widening.unseal_︔_ X w) ()

mutual

  nonIdⁿ?-sound : ∀ {c} (n : Narrowing c) {strict}
    → nonIdⁿ? n ≡ just strict
    → nonIdⁿ→narrowing strict ≡ n
  nonIdⁿ?-sound (cross n) eq
      with nonIdCrossⁿ? n | inspect nonIdCrossⁿ? n
  nonIdⁿ?-sound (cross n) refl
      | just strict | [ decision ] =
    cong cross (nonIdCrossⁿ?-sound n decision)
  nonIdⁿ?-sound (cross n) ()
      | nothing | [ decision ]
  nonIdⁿ?-sound id ()
  nonIdⁿ?-sound (gen safe) refl = refl
  nonIdⁿ?-sound (G ？) refl = refl
  nonIdⁿ?-sound (G ？︔ n) refl = refl
  nonIdⁿ?-sound (fun-？︔gen safe) refl = refl
  nonIdⁿ?-sound (seal X) refl = refl
  nonIdⁿ?-sound (n ︔seal X) refl = refl

  nonIdCrossⁿ?-sound : ∀ {c} (n : Crossⁿ c) {strict}
    → nonIdCrossⁿ? n ≡ just strict
    → nonIdCrossⁿ→cross strict ≡ n
  nonIdCrossⁿ?-sound id ()
  nonIdCrossⁿ?-sound (w ↦ n) eq
      with nonIdʷ? w | inspect nonIdʷ? w
  nonIdCrossⁿ?-sound (w ↦ n) refl
      | just strict | [ decision ] =
    cong (_↦ n) (nonIdʷ?-sound w decision)
  nonIdCrossⁿ?-sound (w ↦ n) eq
      | nothing | [ decision-w ]
      with nonIdⁿ? n | inspect nonIdⁿ? n
  nonIdCrossⁿ?-sound (w ↦ n) refl
      | nothing | [ decision-w ] | just strict | [ decision-n ] =
    cong (w ↦_) (nonIdⁿ?-sound n decision-n)
  nonIdCrossⁿ?-sound (w ↦ n) ()
      | nothing | [ decision-w ] | nothing | [ decision-n ]
  nonIdCrossⁿ?-sound (`∀ n) eq
      with nonIdⁿ? n | inspect nonIdⁿ? n
  nonIdCrossⁿ?-sound (`∀ n) refl
      | just strict | [ decision ] =
    cong `∀ (nonIdⁿ?-sound n decision)
  nonIdCrossⁿ?-sound (`∀ n) ()
      | nothing | [ decision ]

  nonIdʷ?-sound : ∀ {c} (w : Widening c) {strict}
    → nonIdʷ? w ≡ just strict
    → nonIdʷ→widening strict ≡ w
  nonIdʷ?-sound (cross w) eq
      with nonIdCrossʷ? w | inspect nonIdCrossʷ? w
  nonIdʷ?-sound (cross w) refl
      | just strict | [ decision ] =
    cong cross (nonIdCrossʷ?-sound w decision)
  nonIdʷ?-sound (cross w) ()
      | nothing | [ decision ]
  nonIdʷ?-sound id ()
  nonIdʷ?-sound (inst safe) refl = refl
  nonIdʷ?-sound (G !) refl = refl
  nonIdʷ?-sound (w ︔ G !) refl = refl
  nonIdʷ?-sound (inst w ︔★⇒★!) refl = refl
  nonIdʷ?-sound (unseal X) refl = refl
  nonIdʷ?-sound (Widening.unseal_︔_ X w) refl = refl

  nonIdCrossʷ?-sound : ∀ {c} (w : Crossʷ c) {strict}
    → nonIdCrossʷ? w ≡ just strict
    → nonIdCrossʷ→cross strict ≡ w
  nonIdCrossʷ?-sound id ()
  nonIdCrossʷ?-sound (n ↦ w) eq
      with nonIdⁿ? n | inspect nonIdⁿ? n
  nonIdCrossʷ?-sound (n ↦ w) refl
      | just strict | [ decision ] =
    cong (_↦ w) (nonIdⁿ?-sound n decision)
  nonIdCrossʷ?-sound (n ↦ w) eq
      | nothing | [ decision-n ]
      with nonIdʷ? w | inspect nonIdʷ? w
  nonIdCrossʷ?-sound (n ↦ w) refl
      | nothing | [ decision-n ] | just strict | [ decision-w ] =
    cong (n ↦_) (nonIdʷ?-sound w decision-w)
  nonIdCrossʷ?-sound (n ↦ w) ()
      | nothing | [ decision-n ] | nothing | [ decision-w ]
  nonIdCrossʷ?-sound (`∀ w) eq
      with nonIdʷ? w | inspect nonIdʷ? w
  nonIdCrossʷ?-sound (`∀ w) refl
      | just strict | [ decision ] =
    cong `∀ (nonIdʷ?-sound w decision)
  nonIdCrossʷ?-sound (`∀ w) ()
      | nothing | [ decision ]

as-nonIdⁿ : ∀ {c Φ Δᴸ Δᴿ A B}
    {n : Narrowing c} {strict : NonIdⁿ c}
  → nonIdⁿ? n ≡ just strict
  → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ nonIdⁿ→narrowing strict ⦂ A ⊒ B ⊣ Δᴿ
as-nonIdⁿ {n = n} eq p =
  subst (λ r → _ ∣ _ ⊢ r ⦂ _ ⊒ _ ⊣ _)
    (sym (nonIdⁿ?-sound n eq)) p

as-nonIdʷ : ∀ {c Φ Δᴸ Δᴿ A B}
    {w : Widening c} {strict : NonIdʷ c}
  → nonIdʷ? w ≡ just strict
  → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ nonIdʷ→widening strict ⦂ A ⊑ B ⊣ Δᴿ
as-nonIdʷ {w = w} eq p =
  subst (λ r → _ ∣ _ ⊢ r ⦂ _ ⊑ _ ⊣ _)
    (sym (nonIdʷ?-sound w eq)) p

no-nonId-widen-to-star : ∀ {c Φ Δᴸ Δᴿ A}
    {w : Widening c}
  → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ ★ ⊣ Δᴿ
  → nonIdʷ? w ≡ nothing
  → A ≡ ★
no-nonId-widen-to-star id★ eq = refl
no-nonId-widen-to-star (tag ι) ()
no-nonId-widen-to-star tag⇒ ()
no-nonId-widen-to-star (tag p ↦ˡ q) ()
no-nonId-widen-to-star (tag p ↦ʳ q) ()
no-nonId-widen-to-star (tagˣ X∈ X<Δ) ()
no-nonId-widen-to-star (inst nonvar occ p) ()
no-nonId-widen-to-star (inst-tag nonvar occ p) ()

no-nonId-narrow-from-star : ∀ {c Φ Δᴸ Δᴿ B}
    {n : Narrowing c}
  → Φ ∣ Δᴸ ⊢ n ⦂ ★ ⊒ B ⊣ Δᴿ
  → nonIdⁿ? n ≡ nothing
  → ★ ≡ B
no-nonId-narrow-from-star id★ eq = refl
no-nonId-narrow-from-star (untag ι) ()
no-nonId-narrow-from-star untag⇒ ()
no-nonId-narrow-from-star (untag p ↦ˡ q) ()
no-nonId-narrow-from-star (untag p ↦ʳ q) ()
no-nonId-narrow-from-star (untagˣ X∈ X<Δ) ()
no-nonId-narrow-from-star (gen nonvar occ p) ()
no-nonId-narrow-from-star (gen-untag nonvar occ p) ()

un⇑ᴸ-varᵐ : ∀ {Φ X Y}
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸ-varᵐ {Φ = []} ()
un⇑ᴸ-varᵐ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-varᵐ X∈)
un⇑ᴸ-varᵐ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸ-varᵐ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-varᵐ X∈)

no-⇑ᴸ-zero-leftᵐ : ∀ {Φ Y}
  → (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-leftᵐ {Φ = []} ()
no-⇑ᴸ-zero-leftᵐ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-leftᵐ X∈
no-⇑ᴸ-zero-leftᵐ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-leftᵐ X∈

VarMap : Renameᵗ → ImpCtx → Set
VarMap ρ Φ =
  ∀ {X Y} → (X ˣ⊑ˣ Y) ∈ Φ → X ≡ ρ Y

idᵢ-var-map : ∀ {Δ}
  → VarMap (λ X → X) (idᵢ Δ)
idᵢ-var-map = idᵢ-var-identity

all-var-map : ∀ {ρ Φ}
  → VarMap ρ Φ
  → VarMap (extᵗ ρ) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
all-var-map h (here refl) = refl
all-var-map h {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
all-var-map h {X = suc X} {Y = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
all-var-map h {X = suc X} {Y = suc Y} (there X∈) =
  cong suc (h (un⇑ᵢ-var X∈))

νRename : Renameᵗ → Renameᵗ
νRename ρ X = suc (ρ X)

gen-var-map : ∀ {ρ Φ}
  → VarMap ρ Φ
  → VarMap (νRename ρ) ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
gen-var-map h {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᴸ-zero-leftᵐ X∈)
gen-var-map h {X = suc X} (there X∈) =
  cong suc (h (un⇑ᴸ-varᵐ X∈))

mutual

  member-backʷ : ∀ {ρ Φ Δᴸ Δᴿ c A B X}
      {w : Widening c}
    → VarMap ρ Φ
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
    → X ∈ᵗ B
    → ρ X ∈ᵗ A
  member-backʷ h id★ ()
  member-backʷ h (idˣ X∈ X<Δ Y<Δ) var-∈
      rewrite h X∈ =
    var-∈
  member-backʷ h idι ()
  member-backʷ h (p ↦ q) (∈-fun-left X∈) =
    ∈-fun-left (member-backⁿ h p X∈)
  member-backʷ h (p ↦ q) (∈-fun-right X∈) =
    ∈-fun-right (member-backʷ h q X∈)
  member-backʷ h (∀ⁱ p) (∈-all X∈) =
    ∈-all (member-backʷ (all-var-map h) p X∈)
  member-backʷ h (tag ι) ()
  member-backʷ h tag⇒ ()
  member-backʷ h (tag p ↦ˡ q) ()
  member-backʷ h (tag p ↦ʳ q) ()
  member-backʷ h (tagˣ X∈ X<Δ) ()
  member-backʷ h (inst nonvar occ p) X∈ =
    ∈-all (member-backʷ (gen-var-map h) p X∈)
  member-backʷ h (inst-tag nonvar occ p) ()

  member-backⁿ : ∀ {ρ Φ Δᴸ Δᴿ c A B X}
      {n : Narrowing c}
    → VarMap ρ Φ
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → X ∈ᵗ A
    → ρ X ∈ᵗ B
  member-backⁿ h id★ ()
  member-backⁿ h (idˣ X∈ X<Δ Y<Δ) var-∈
      rewrite h X∈ =
    var-∈
  member-backⁿ h idι ()
  member-backⁿ h (p ↦ q) (∈-fun-left X∈) =
    ∈-fun-left (member-backʷ h p X∈)
  member-backⁿ h (p ↦ q) (∈-fun-right X∈) =
    ∈-fun-right (member-backⁿ h q X∈)
  member-backⁿ h (∀ⁱ p) (∈-all X∈) =
    ∈-all (member-backⁿ (all-var-map h) p X∈)
  member-backⁿ h (untag ι) ()
  member-backⁿ h untag⇒ ()
  member-backⁿ h (untag p ↦ˡ q) ()
  member-backⁿ h (untag p ↦ʳ q) ()
  member-backⁿ h (untagˣ X∈ X<Δ) ()
  member-backⁿ h (gen nonvar occ p) X∈ =
    ∈-all (member-backⁿ (gen-var-map h) p X∈)
  member-backⁿ h (gen-untag nonvar occ p) ()

nonvar-backʷ : ∀ {Φ Δᴸ Δᴿ c A B X}
    {w : Widening c}
  → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴿ
  → NonVar B
  → X ∈ᵗ B
  → NonVar A
nonvar-backʷ id★ nonvar-star ()
nonvar-backʷ (idˣ X∈ X<Δ Y<Δ) () occ
nonvar-backʷ idι nonvar-base ()
nonvar-backʷ (p ↦ q) nonvar-fun X∈ = nonvar-fun
nonvar-backʷ (∀ⁱ p) nonvar-all X∈ = nonvar-all
nonvar-backʷ (tag ι) nonvar-star ()
nonvar-backʷ tag⇒ nonvar-star ()
nonvar-backʷ (tag p ↦ˡ q) nonvar-star ()
nonvar-backʷ (tag p ↦ʳ q) nonvar-star ()
nonvar-backʷ (tagˣ X∈ X<Δ) nonvar-star ()
nonvar-backʷ (inst nonvar occ p) nonvarB X∈ = nonvar-all
nonvar-backʷ (inst-tag nonvar occ p) nonvar-star ()

nonvar-backⁿ : ∀ {Φ Δᴸ Δᴿ c A B X}
    {n : Narrowing c}
  → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  → NonVar A
  → X ∈ᵗ A
  → NonVar B
nonvar-backⁿ id★ nonvar-star ()
nonvar-backⁿ (idˣ X∈ X<Δ Y<Δ) () occ
nonvar-backⁿ idι nonvar-base ()
nonvar-backⁿ (p ↦ q) nonvar-fun X∈ = nonvar-fun
nonvar-backⁿ (∀ⁱ p) nonvar-all X∈ = nonvar-all
nonvar-backⁿ (untag ι) nonvar-star ()
nonvar-backⁿ untag⇒ nonvar-star ()
nonvar-backⁿ (untag p ↦ˡ q) nonvar-star ()
nonvar-backⁿ (untag p ↦ʳ q) nonvar-star ()
nonvar-backⁿ (untagˣ X∈ X<Δ) nonvar-star ()
nonvar-backⁿ (gen nonvar occ p) nonvarA X∈ = nonvar-all
nonvar-backⁿ (gen-untag nonvar occ p) nonvar-star ()

⇑ᴸ-varᶜ : ∀ {Φ X Y}
  → (X ˣ⊑ˣ Y) ∈ Φ
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸ-varᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᴸ-varᶜ X∈)
⇑ᴸ-varᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᴸ-varᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᴸ-varᶜ X∈)

un⇑ᴸ-varᶜ : ∀ {Φ X Y}
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸ-varᶜ {Φ = []} ()
un⇑ᴸ-varᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-varᶜ X∈)
un⇑ᴸ-varᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸ-varᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-varᶜ X∈)

⇑ᴸ-starᶜ : ∀ {Φ X}
  → (X ˣ⊑★) ∈ Φ
  → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸ-starᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᴸ-starᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᴸ-starᶜ X∈)
⇑ᴸ-starᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᴸ-starᶜ X∈)

un⇑ᴸ-starᶜ : ∀ {Φ X}
  → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑★) ∈ Φ
un⇑ᴸ-starᶜ {Φ = []} ()
un⇑ᴸ-starᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸ-starᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-starᶜ X∈)
un⇑ᴸ-starᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-starᶜ X∈)

no-⇑ᴸ-zero-starᶜ : ∀ {Φ}
  → (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-starᶜ {Φ = []} ()
no-⇑ᴸ-zero-starᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-starᶜ X∈
no-⇑ᴸ-zero-starᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-starᶜ X∈

no-⇑ᴸ-zero-leftᶜ : ∀ {Φ Y}
  → (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-leftᶜ {Φ = []} ()
no-⇑ᴸ-zero-leftᶜ {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-leftᶜ X∈
no-⇑ᴸ-zero-leftᶜ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-leftᶜ X∈

record ComposeCtx
    (Δ : TyCtx) (Φᴵ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    compose-map-var : ∀ {X Y}
      → (X ˣ⊑ˣ Y) ∈ Φᴵ
      → X ≡ Y

    compose-var-var : ∀ {X Y Z}
      → (X ˣ⊑ˣ Y) ∈ Φᴵ
      → (Y ˣ⊑ˣ Z) ∈ Φᴿ
      → (X ˣ⊑ˣ Z) ∈ Φᴼ

    compose-var-star : ∀ {X Y}
      → (X ˣ⊑ˣ Y) ∈ Φᴵ
      → (Y ˣ⊑★) ∈ Φᴿ
      → (X ˣ⊑★) ∈ Φᴼ

    compose-star-left : ∀ {X}
      → X < Δ
      → (X ˣ⊑★) ∈ Φᴵ
      → (X ˣ⊑★) ∈ Φᴼ

open ComposeCtx

compose-id-left : ∀ Δ Φ
  → ComposeCtx Δ (idᵢ Δ) Φ Φ
compose-id-left Δ Φ .compose-map-var X∈ =
  idᵢ-var-identity X∈
compose-id-left Δ Φ .compose-var-var X∈ Y∈ =
  subst (λ X → (X ˣ⊑ˣ _) ∈ Φ)
    (sym (idᵢ-var-identity X∈)) Y∈
compose-id-left Δ Φ .compose-var-star X∈ Y∈ =
  subst (λ X → (X ˣ⊑★) ∈ Φ)
    (sym (idᵢ-var-identity X∈)) Y∈
compose-id-left Δ Φ .compose-star-left X<Δ X∈ =
  ⊥-elim (idᵢ-no-star X∈)

compose-all : ∀ {Δ Φᴵ Φᴿ Φᴼ}
  → ComposeCtx Δ Φᴵ Φᴿ Φᴼ
  → ComposeCtx (suc Δ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴵ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴿ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴼ)
compose-all comp .compose-map-var (here refl) = refl
compose-all comp .compose-map-var {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all comp .compose-map-var {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all comp .compose-map-var {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (compose-map-var comp (un⇑ᵢ-var X∈))
compose-all comp .compose-var-var (here refl) (here refl) =
  here refl
compose-all comp .compose-var-var (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᵢ-zero-left Y∈)
compose-all comp .compose-var-var {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all comp .compose-var-var {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all comp .compose-var-var
    {X = suc X} {Y = suc Y} {Z = zero}
    (there X∈) (there Y∈) =
  ⊥-elim (no-⇑ᵢ-zero-right Y∈)
compose-all comp .compose-var-var
    {X = suc X} {Y = suc Y} {Z = suc z}
    (there X∈) (there Y∈) =
  there (⇑ᵢ-var
    (compose-var-var comp
      (un⇑ᵢ-var X∈) (un⇑ᵢ-var Y∈)))
compose-all comp .compose-var-star (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᵢ-zero-star Y∈)
compose-all comp .compose-var-star {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all comp .compose-var-star {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all comp .compose-var-star {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᵢ-star
    (compose-var-star comp
      (un⇑ᵢ-var X∈) (un⇑ᵢ-star Y∈)))
compose-all comp .compose-star-left {X = zero} X<Δ (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-star X∈)
compose-all comp .compose-star-left {X = suc X}
    (s≤s X<Δ) (there X∈) =
  there (⇑ᵢ-star
    (compose-star-left comp X<Δ (un⇑ᵢ-star X∈)))

compose-all-gen : ∀ {Δ Φᴵ Φ}
  → ComposeCtx Δ Φᴵ Φ Φ
  → ComposeCtx (suc Δ)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φᴵ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
compose-all-gen comp .compose-map-var (here refl) = refl
compose-all-gen comp .compose-map-var {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all-gen comp .compose-map-var {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all-gen comp .compose-map-var {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (compose-map-var comp (un⇑ᵢ-var X∈))
compose-all-gen comp .compose-var-var (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᴸ-zero-leftᶜ Y∈)
compose-all-gen comp .compose-var-var {X = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all-gen comp .compose-var-var {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all-gen comp .compose-var-var {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-varᶜ
    (compose-var-var comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-varᶜ Y∈)))
compose-all-gen comp .compose-var-star (here refl) (here refl) =
  here refl
compose-all-gen comp .compose-var-star (here refl) (there Y∈) =
  ⊥-elim (no-⇑ᴸ-zero-starᶜ Y∈)
compose-all-gen comp .compose-var-star {X = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-all-gen comp .compose-var-star {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-all-gen comp .compose-var-star {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-starᶜ
    (compose-var-star comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-starᶜ Y∈)))
compose-all-gen comp .compose-star-left {X = zero}
    X<Δ (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-star X∈)
compose-all-gen comp .compose-star-left {X = suc X}
    (s≤s X<Δ) (there X∈) =
  there (⇑ᴸ-starᶜ
    (compose-star-left comp X<Δ (un⇑ᵢ-star X∈)))

compose-gen : ∀ {Δ Φᴵ Φᴿ Φᴼ}
  → ComposeCtx Δ Φᴵ Φᴿ Φᴼ
  → ComposeCtx (suc Δ)
      ((zero ˣ⊑★) ∷ ⇑ᵢ Φᴵ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φᴼ)
compose-gen comp .compose-map-var {X = zero} (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-gen comp .compose-map-var {X = suc X} {Y = zero}
    (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-gen comp .compose-map-var {X = suc X} {Y = suc Y}
    (there X∈) =
  cong suc (compose-map-var comp (un⇑ᵢ-var X∈))
compose-gen comp .compose-var-var {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-gen comp .compose-var-var {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-gen comp .compose-var-var {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-varᶜ
    (compose-var-var comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-varᶜ Y∈)))
compose-gen comp .compose-var-star {X = zero} (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-left X∈)
compose-gen comp .compose-var-star {X = suc X} {Y = zero}
    (there X∈) Y∈ =
  ⊥-elim (no-⇑ᵢ-zero-right X∈)
compose-gen comp .compose-var-star {X = suc X} {Y = suc Y}
    (there X∈) (there Y∈) =
  there (⇑ᴸ-starᶜ
    (compose-var-star comp
      (un⇑ᵢ-var X∈) (un⇑ᴸ-starᶜ Y∈)))
compose-gen comp .compose-star-left {X = zero}
    (s≤s z≤n) (here refl) =
  here refl
compose-gen comp .compose-star-left {X = zero} X<Δ (there X∈) =
  ⊥-elim (no-⇑ᵢ-zero-star X∈)
compose-gen comp .compose-star-left {X = suc X}
    (s≤s X<Δ) (there X∈) =
  there (⇑ᴸ-starᶜ
    (compose-star-left comp X<Δ (un⇑ᵢ-star X∈)))

StarIncl : TyCtx → ImpCtx → ImpCtx → Set
StarIncl Δ Φ Ψ =
  ∀ {X} → X < Δ → (X ˣ⊑★) ∈ Φ → (X ˣ⊑★) ∈ Ψ

idᵢ-star-incl : ∀ {Δ Φ}
  → StarIncl Δ (idᵢ Δ) Φ
idᵢ-star-incl X<Δ X∈ = ⊥-elim (idᵢ-no-star X∈)

⇑ᴸ-star : ∀ {Φ X}
  → (X ˣ⊑★) ∈ Φ
  → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᴸ-star X∈)
⇑ᴸ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᴸ-star X∈)

⇑ᴸ-var : ∀ {Φ X Y}
  → (X ˣ⊑ˣ Y) ∈ Φ
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (⇑ᴸ-var X∈)
⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (⇑ᴸ-var X∈)

un⇑ᴸ-var : ∀ {Φ X Y}
  → (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸ-var {Φ = []} ()
un⇑ᴸ-var {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-var X∈)
un⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸ-var {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-var X∈)

un⇑ᴸ-star : ∀ {Φ X}
  → (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  → (X ˣ⊑★) ∈ Φ
un⇑ᴸ-star {Φ = []} ()
un⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸ-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-star X∈)
un⇑ᴸ-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  there (un⇑ᴸ-star X∈)

no-⇑ᴸ-zero-star : ∀ {Φ}
  → (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-star {Φ = []} ()
no-⇑ᴸ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-star X∈
no-⇑ᴸ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-star X∈

no-⇑ᴸ-zero-left : ∀ {Φ Y}
  → (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
  → ⊥
no-⇑ᴸ-zero-left {Φ = []} ()
no-⇑ᴸ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-left X∈
no-⇑ᴸ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X∈) =
  no-⇑ᴸ-zero-left X∈

gen-star-incl : ∀ {Δ Φ Ψ}
  → StarIncl Δ Φ Ψ
  → StarIncl (suc Δ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
gen-star-incl incl (s≤s z≤n) (here refl) = here refl
gen-star-incl incl {X = zero} X<Δ (there X∈) =
  ⊥-elim (no-⇑ᴸ-zero-star X∈)
gen-star-incl incl {X = suc X} (s≤s X<Δ) (there X∈) =
  there (⇑ᴸ-star (incl X<Δ (un⇑ᴸ-star X∈)))

mutual

  recontext-to-starʷ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c A}
      {w : Widening c}
    → StarIncl Δᴸ Ψ Φ
    → Ψ ∣ Δᴸ ⊢ w ⦂ A ⊑ ★ ⊣ Δᴹ
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ ★ ⊣ Δᴿ
  recontext-to-starʷ incl id★ = id★
  recontext-to-starʷ incl (tag ι) = tag ι
  recontext-to-starʷ incl tag⇒ = tag⇒
  recontext-to-starʷ incl (tag p ↦ˡ q) =
    tag recontext-from-starⁿ incl p ↦ˡ
      recontext-to-starʷ incl q
  recontext-to-starʷ incl (tag p ↦ʳ q) =
    tag recontext-from-starⁿ incl p ↦ʳ
      recontext-to-starʷ incl q
  recontext-to-starʷ incl (tagˣ X∈ X<Δ) =
    tagˣ (incl X<Δ X∈) X<Δ
  recontext-to-starʷ incl (inst nonvar occ p) =
    inst nonvar occ (recontext-to-starʷ (gen-star-incl incl) p)
  recontext-to-starʷ incl (inst-tag nonvar occ p) =
    inst-tag nonvar occ
      (recontext-to-funʷ (gen-star-incl incl) p)

  recontext-to-funʷ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c A}
      {w : Widening c}
    → StarIncl Δᴸ Ψ Φ
    → Ψ ∣ Δᴸ ⊢ w ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴹ
    → Φ ∣ Δᴸ ⊢ w ⦂ A ⊑ (★ ⇒ ★) ⊣ Δᴿ
  recontext-to-funʷ incl (p ↦ q) =
    recontext-from-starⁿ incl p ↦ recontext-to-starʷ incl q
  recontext-to-funʷ incl (inst nonvar occ p) =
    inst nonvar occ (recontext-to-funʷ (gen-star-incl incl) p)

  recontext-from-starⁿ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c B}
      {n : Narrowing c}
    → StarIncl Δᴿ Ψ Φ
    → Ψ ∣ Δᴹ ⊢ n ⦂ ★ ⊒ B ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ n ⦂ ★ ⊒ B ⊣ Δᴿ
  recontext-from-starⁿ incl id★ = id★
  recontext-from-starⁿ incl (untag ι) = untag ι
  recontext-from-starⁿ incl untag⇒ = untag⇒
  recontext-from-starⁿ incl (untag p ↦ˡ q) =
    untag recontext-to-starʷ incl p ↦ˡ
      recontext-from-starⁿ incl q
  recontext-from-starⁿ incl (untag p ↦ʳ q) =
    untag recontext-to-starʷ incl p ↦ʳ
      recontext-from-starⁿ incl q
  recontext-from-starⁿ incl (untagˣ X∈ X<Δ) =
    untagˣ (incl X<Δ X∈) X<Δ
  recontext-from-starⁿ incl (gen nonvar occ p) =
    gen nonvar occ (recontext-from-starⁿ (gen-star-incl incl) p)
  recontext-from-starⁿ incl (gen-untag nonvar occ p) =
    gen-untag nonvar occ
      (recontext-from-funⁿ (gen-star-incl incl) p)

  recontext-from-funⁿ : ∀ {Φ Ψ Δᴸ Δᴹ Δᴿ c B}
      {n : Narrowing c}
    → StarIncl Δᴿ Ψ Φ
    → Ψ ∣ Δᴹ ⊢ n ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
    → Φ ∣ Δᴸ ⊢ n ⦂ (★ ⇒ ★) ⊒ B ⊣ Δᴿ
  recontext-from-funⁿ incl (p ↦ q) =
    recontext-to-starʷ incl p ↦ recontext-from-starⁿ incl q
  recontext-from-funⁿ incl (gen nonvar occ p) =
    gen nonvar occ (recontext-from-funⁿ (gen-star-incl incl) p)

wrap-untag-indexed : ∀ {c Φ Δᴸ Δᴿ A B}
    {n : Crossⁿ c}
  → Φ ∣ Δᴸ ⊢ cross n ⦂ (★ ⇒ ★) ⊒ (A ⇒ B) ⊣ Δᴿ
  → ∃[ u ] Σ[ r ∈ Narrowing u ]
      (wrap-？ⁿ ★⇒★ n ≡ (u , r)) ×
      (Φ ∣ Δᴸ ⊢ r ⦂ ★ ⊒ (A ⇒ B) ⊣ Δᴿ)
wrap-untag-indexed {n = w ↦ n} (p ↦ q)
    with nonIdʷ? w | inspect nonIdʷ? w
wrap-untag-indexed {n = w ↦ n} (p ↦ q)
    | just strict | [ decision ] =
  _ , _ , refl , untag as-nonIdʷ decision p ↦ˡ q
wrap-untag-indexed {n = w ↦ n} (p ↦ q)
    | nothing | [ decision-w ]
    with nonIdⁿ? n | inspect nonIdⁿ? n
wrap-untag-indexed {n = w ↦ n} (p ↦ q)
    | nothing | [ decision-w ] | just strict | [ decision-n ] =
  _ , _ , refl , untag p ↦ʳ as-nonIdⁿ decision-n q
wrap-untag-indexed {n = w ↦ n} (p ↦ q)
    | nothing | [ decision-w ] | nothing | [ decision-n ]
    with no-nonId-widen-to-star p decision-w
       | no-nonId-narrow-from-star q decision-n
wrap-untag-indexed {n = w ↦ n} (p ↦ q)
    | nothing | [ decision-w ] | nothing | [ decision-n ]
    | refl | refl =
  _ , _ , refl , untag⇒

wrap-tag-indexed : ∀ {c Φ Δᴸ Δᴿ A B}
    {w : Crossʷ c}
  → Φ ∣ Δᴸ ⊢ cross w ⦂ (A ⇒ B) ⊑ (★ ⇒ ★) ⊣ Δᴿ
  → ∃[ u ] Σ[ r ∈ Widening u ]
      (wrap-!ʷ w ★⇒★ ≡ (u , r)) ×
      (Φ ∣ Δᴸ ⊢ r ⦂ (A ⇒ B) ⊑ ★ ⊣ Δᴿ)
wrap-tag-indexed {w = n ↦ w} (p ↦ q)
    with nonIdⁿ? n | inspect nonIdⁿ? n
wrap-tag-indexed {w = n ↦ w} (p ↦ q)
    | just strict | [ decision ] =
  _ , _ , refl , tag as-nonIdⁿ decision p ↦ˡ q
wrap-tag-indexed {w = n ↦ w} (p ↦ q)
    | nothing | [ decision-n ]
    with nonIdʷ? w | inspect nonIdʷ? w
wrap-tag-indexed {w = n ↦ w} (p ↦ q)
    | nothing | [ decision-n ] | just strict | [ decision-w ] =
  _ , _ , refl , tag p ↦ʳ as-nonIdʷ decision-w q
wrap-tag-indexed {w = n ↦ w} (p ↦ q)
    | nothing | [ decision-n ] | nothing | [ decision-w ]
    with no-nonId-narrow-from-star p decision-n
       | no-nonId-widen-to-star q decision-w
wrap-tag-indexed {w = n ↦ w} (p ↦ q)
    | nothing | [ decision-n ] | nothing | [ decision-w ]
    | refl | refl =
  _ , _ , refl , tag⇒

mutual

  composeⁿ-typed-fuel : ∀ {fuel c d Φᴵ Φ Δᴸ Δᴿ A B C}
      {n : Narrowing c} {m : Narrowing d}
    → ComposeCtx Δᴿ Φᴵ Φ Φ
    → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
    → Φᴵ ∣ Δᴿ ⊢ m ⦂ B ⊒ C ⊣ Δᴿ
    → coercion-size c + coercion-size d < fuel
    → ∃[ u ] Σ[ r ∈ Narrowing u ]
        (composeⁿ-fuel fuel n m ≡ just (u , r)) ×
        (Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ)
  composeⁿ-typed-fuel {fuel = zero} comp p q ()
  composeⁿ-typed-fuel {fuel = suc zero} {c = c} {d = d}
      comp p q bound =
    ⊥-elim (size-sum-not-<1 c d bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)} comp p id★ bound =
    _ , _ , refl , p
  composeⁿ-typed-fuel {fuel = suc (suc fuel)} comp p idι bound =
    _ , _ , refl , p
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp p (idˣ X∈ X<Δ Y<Δ) bound
      rewrite compose-map-var comp X∈ =
    _ , _ , refl , p
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {Φᴵ = Φᴵ} {Φ = Φ} comp id★ (untag ι) bound =
    _ , _ , refl , untag ι
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {Φᴵ = Φᴵ} {Φ = Φ} comp id★ untag⇒ bound =
    _ , _ , refl , untag⇒
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp id★ (untag p ↦ˡ q) bound =
    _ , _ , refl ,
      recontext-from-starⁿ
        (compose-star-left comp) (untag p ↦ˡ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp id★ (untag p ↦ʳ q) bound =
    _ , _ , refl ,
      recontext-from-starⁿ
        (compose-star-left comp) (untag p ↦ʳ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {Φᴵ = Φᴵ} {Φ = Φ}
      comp id★ (untagˣ X∈ X<Δ) bound =
    _ , _ , refl ,
      untagˣ (compose-star-left comp X<Δ X∈) X<Δ
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp id★ (gen-untag nonvar occ q) bound =
    _ , _ , refl ,
      recontext-from-starⁿ (compose-star-left comp)
        (gen-untag nonvar occ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp id★ (gen nonvar occ q) bound =
    _ , _ , refl ,
      recontext-from-starⁿ (compose-star-left comp)
        (gen nonvar occ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (idˣ X∈ X<Δ Y<Δ)
        (gen {safe = safe} nonvar occ q) bound
      with gen-safe-source-shape safe (eraseⁿ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (idˣ X∈ X<Δ Y<Δ)
        (gen {safe = safe} nonvar occ q) bound
      | ()
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp idι (gen {safe = safe} nonvar occ q) bound
      with gen-safe-source-shape safe (eraseⁿ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp idι (gen {safe = safe} nonvar occ q) bound
      | ()
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (untag ι) (gen {safe = safe} nonvar occ q) bound
      with gen-safe-source-shape safe (eraseⁿ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (untag ι) (gen {safe = safe} nonvar occ q) bound
      | ()
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (untagˣ X∈ X<Δ)
        (gen {safe = safe} nonvar occ q) bound
      with gen-safe-source-shape safe (eraseⁿ q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (untagˣ X∈ X<Δ)
        (gen {safe = safe} nonvar occ q) bound
      | ()
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp untag⇒ (q₁ ↦ q₂) bound
      with wrap-untag-indexed
             (recontext-to-starʷ (compose-star-left comp) q₁
                ↦ recontext-from-starⁿ
                    (compose-star-left comp) q₂)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp untag⇒ (q₁ ↦ q₂) bound
      | u , r , eq , r⊢ rewrite eq =
    u , r , refl , r⊢
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      comp (untag p₁ ↦ˡ p₂) (q₁ ↦ q₂) bound
      with composeʷ-typed-fuel comp q₁ p₁
             (two-lower-fuel
               (sum-swap-two-smaller
                 (<-trans (size-↦ˡ s₁ s₂)
                   (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
                 (size-↦ˡ t₁ t₂))
               bound)
         | composeⁿ-typed-fuel comp p₂ q₂
             (two-lower-fuel
               (sum-two-smaller
                 (<-trans (size-↦ʳ s₁ s₂)
                   (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
                 (size-↦ʳ t₁ t₂))
               bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      comp (untag p₁ ↦ˡ p₂) (q₁ ↦ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      with wrap-untag-indexed (r₁⊢ ↦ r₂⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      comp (untag p₁ ↦ˡ p₂) (q₁ ↦ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      | u , r , eq-wrap , r⊢
      rewrite eq₁ | eq₂ | eq-wrap =
    u , r , refl , r⊢
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      comp (untag p₁ ↦ʳ p₂) (q₁ ↦ q₂) bound
      with composeʷ-typed-fuel comp q₁ p₁
             (two-lower-fuel
               (sum-swap-two-smaller
                 (<-trans (size-↦ˡ s₁ s₂)
                   (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
                 (size-↦ˡ t₁ t₂))
               bound)
         | composeⁿ-typed-fuel comp p₂ q₂
             (two-lower-fuel
               (sum-two-smaller
                 (<-trans (size-↦ʳ s₁ s₂)
                   (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂)))
                 (size-↦ʳ t₁ t₂))
               bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      comp (untag p₁ ↦ʳ p₂) (q₁ ↦ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      with wrap-untag-indexed (r₁⊢ ↦ r₂⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = t₁ ↦ t₂}
      comp (untag p₁ ↦ʳ p₂) (q₁ ↦ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      | u , r , eq-wrap , r⊢
      rewrite eq₁ | eq₂ | eq-wrap =
    u , r , refl , r⊢
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      comp (p₁ ↦ p₂) (q₁ ↦ q₂) bound
      with composeʷ-typed-fuel comp q₁ p₁
             (two-lower-fuel
               (sum-swap-two-smaller
                 (size-↦ˡ s₁ s₂) (size-↦ˡ t₁ t₂))
               bound)
         | composeⁿ-typed-fuel comp p₂ q₂
             (two-lower-fuel
               (sum-two-smaller
                 (size-↦ʳ s₁ s₂) (size-↦ʳ t₁ t₂))
               bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      comp (p₁ ↦ p₂) (q₁ ↦ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      rewrite eq₁ | eq₂ =
    _ , _ , refl , (r₁⊢ ↦ r₂⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (∀ⁱ p) (∀ⁱ q) bound
      with composeⁿ-typed-fuel (compose-all comp) p q
             (two-lower-fuel
               (sum-two-smaller (size-under _) (size-under _))
               bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp (∀ⁱ p) (∀ⁱ q) bound
      | u , r , eq , r⊢ rewrite eq =
    _ , _ , refl , ∀ⁱ r⊢
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = `∀ t}
      comp (gen {safe = safeB} nonvarB occB p) (∀ⁱ q) bound
      with composeⁿ-typed-fuel (compose-all-gen comp) p q
             (lower-fuel
               (+-mono-< (size-under s) (size-under t))
               bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = `∀ t}
      comp (gen {safe = safeB} nonvarB occB p) (∀ⁱ q) bound
      | u , r , eq , r⊢
      with gen-safe
             (gen-safe-source-shape safeB (eraseⁿ p))
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
      where
      occC = member-backⁿ
        (all-var-map (compose-map-var comp)) q occB
      nonvarC = nonvar-backⁿ q nonvarB occB
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = `∀ t}
      comp (gen {safe = safeB} nonvarB occB p) (∀ⁱ q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
    where
    occC = member-backⁿ
      (all-var-map (compose-map-var comp)) q occB
    nonvarC = nonvar-backⁿ q nonvarB occB
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      comp (gen-untag {safe = safeB} nonvarB occB p)
        (∀ⁱ q) bound
      with composeⁿ-typed-fuel (compose-all-gen comp) p q
             (lower-fuel
               (+-mono-<
                 (<-trans (size-under s)
                   (size-︔ʳ (★⇒★ ？) (gen s)))
                 (size-under t))
               bound)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      comp (gen-untag {safe = safeB} nonvarB occB p)
        (∀ⁱ q) bound
      | u , r , eq , r⊢
      with gen-safe fun
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
      where
      occC = member-backⁿ
        (all-var-map (compose-map-var comp)) q occB
      nonvarC = nonvar-backⁿ q nonvarB occB
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = `∀ t}
      comp (gen-untag {safe = safeB} nonvarB occB p)
        (∀ⁱ q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen-untag nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
    where
    occC = member-backⁿ
      (all-var-map (compose-map-var comp)) q occB
    nonvarC = nonvar-backⁿ q nonvarB occB
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = gen t}
      comp (p₁ ↦ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      with composeⁿ-typed-fuel (compose-gen comp)
             (target-liftⁿ (p₁ ↦ p₂))
             (source-lift-genⁿ q)
             (subst (λ k → k + coercion-size t < suc fuel)
               (sym (size-rename suc (s₁ ↦ s₂)))
               (lower-fuel
                 (sum-right-smaller (size-under t))
                 bound))
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = gen t}
      comp (p₁ ↦ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢
      with gen-safe fun
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = gen t}
      comp (p₁ ↦ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = gen t}
      comp (∀ⁱ p)
        (gen {safe = safeC} nonvarC occC q) bound
      with composeⁿ-typed-fuel (compose-gen comp)
             (target-liftⁿ (∀ⁱ p))
             (source-lift-genⁿ q)
             (subst (λ k → k + coercion-size t < suc fuel)
               (sym (size-rename suc (`∀ s)))
               (lower-fuel
                 (sum-right-smaller (size-under t))
                 bound))
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = gen t}
      comp (∀ⁱ p)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢
      with gen-safe all
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = gen t}
      comp (∀ⁱ p)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = gen t}
      comp (gen {safe = safeB} nonvarB occB p)
        (gen {safe = safeC} nonvarC occC q) bound
      with composeⁿ-typed-fuel (compose-gen comp)
             (target-liftⁿ
               (gen {safe = safeB} nonvarB occB p))
             (source-lift-genⁿ q)
             (subst (λ k → k + coercion-size t < suc fuel)
               (sym (size-rename suc (gen s)))
               (lower-fuel
                 (sum-right-smaller (size-under t))
                 bound))
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = gen t}
      comp (gen {safe = safeB} nonvarB occB p)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢
      with gen-safe
             (gen-safe-source-shape safeB (eraseⁿ p))
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = gen s} {d = gen t}
      comp (gen {safe = safeB} nonvarB occB p)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      comp untag⇒
        (gen nonvarC occC q) bound =
    _ , _ , refl ,
      gen-untag nonvarC occC
        (recontext-from-funⁿ
          (gen-star-incl (compose-star-left comp)) q)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = gen t}
      comp (untag p₁ ↦ˡ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      with composeⁿ-typed-fuel (compose-gen comp)
             (target-liftⁿ (p₁ ↦ p₂))
             (source-lift-genⁿ q)
             (subst (λ k → k + coercion-size t < suc fuel)
               (sym (size-rename suc (s₁ ↦ s₂)))
               (lower-fuel
                 (+-mono-<
                   (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂))
                   (size-under t))
                 bound))
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = gen t}
      comp (untag p₁ ↦ˡ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢
      with gen-safe fun
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = gen t}
      comp (untag p₁ ↦ˡ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen-untag nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = gen t}
      comp (untag p₁ ↦ʳ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      with composeⁿ-typed-fuel (compose-gen comp)
             (target-liftⁿ (p₁ ↦ p₂))
             (source-lift-genⁿ q)
             (subst (λ k → k + coercion-size t < suc fuel)
               (sym (size-rename suc (s₁ ↦ s₂)))
               (lower-fuel
                 (+-mono-<
                   (size-︔ʳ (★⇒★ ？) (s₁ ↦ s₂))
                   (size-under t))
                 bound))
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = gen t}
      comp (untag p₁ ↦ʳ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢
      with gen-safe fun
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ (s₁ ↦ s₂)} {d = gen t}
      comp (untag p₁ ↦ʳ p₂)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen-untag nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      comp (gen-untag {safe = safeB} nonvarB occB p)
        (gen {safe = safeC} nonvarC occC q) bound
      with composeⁿ-typed-fuel (compose-gen comp)
             (target-liftⁿ
               (gen nonvarB occB p))
             (source-lift-genⁿ q)
             (subst (λ k → k + coercion-size t < suc fuel)
               (sym (size-rename suc (gen s)))
               (lower-fuel
                 (+-mono-<
                   (size-︔ʳ (★⇒★ ？) (gen s))
                   (size-under t))
                 bound))
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      comp (gen-untag {safe = safeB} nonvarB occB p)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢
      with gen-safe fun
             (nonvar-member-shape nonvarC occC)
             (eraseⁿ r⊢) r
  composeⁿ-typed-fuel {fuel = suc (suc fuel)}
      {c = (★⇒★ ？) ︔ gen s} {d = gen t}
      comp (gen-untag {safe = safeB} nonvarB occB p)
        (gen {safe = safeC} nonvarC occC q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      gen-untag nonvarC occC
        (subst
          (λ n → _ ∣ _ ⊢ n ⦂ _ ⊒ _ ⊣ _)
          (sym (genSafe?-sound r eq-safe))
          r⊢)

  composeʷ-typed-fuel : ∀ {fuel c d Φᴵ Φ Δᴸ Δᴿ A B C}
      {w : Widening c} {v : Widening d}
    → ComposeCtx Δᴸ Φᴵ Φ Φ
    → Φᴵ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴸ
    → Φ ∣ Δᴸ ⊢ v ⦂ B ⊑ C ⊣ Δᴿ
    → coercion-size c + coercion-size d < fuel
    → ∃[ u ] Σ[ r ∈ Widening u ]
        (composeʷ-fuel fuel w v ≡ just (u , r)) ×
        (Φ ∣ Δᴸ ⊢ r ⦂ A ⊑ C ⊣ Δᴿ)
  composeʷ-typed-fuel {fuel = zero} comp p q ()
  composeʷ-typed-fuel {fuel = suc zero} {c = c} {d = d}
      comp p q bound =
    ⊥-elim (size-sum-not-<1 c d bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)} comp p id★ bound =
    _ , _ , refl ,
      recontext-to-starʷ (compose-star-left comp) p
  composeʷ-typed-fuel {fuel = suc (suc fuel)} comp idι idι bound =
    _ , _ , refl , idι
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp idι (tag ι) bound =
    _ , _ , refl , tag ι
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (idˣ X∈ X<Δ Y<Δ) (idˣ Y∈ Y<Δ′ Z<Δ) bound =
    _ , _ , refl ,
      idˣ (compose-var-var comp X∈ Y∈) X<Δ Z<Δ
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (idˣ X∈ X<Δ Y<Δ) (tagˣ Y∈ Y<Δ′) bound
      rewrite compose-map-var comp X∈ =
    _ , _ , refl , tagˣ Y∈ Y<Δ′
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p)
        (idˣ X∈ X<Δ Y<Δ) bound
      with inst-safe-target-shape safe (eraseʷ p)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p)
        (idˣ X∈ X<Δ Y<Δ) bound
      | ()
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p) idι bound
      with inst-safe-target-shape safe (eraseʷ p)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p) idι bound
      | ()
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p) (tag ι) bound
      with inst-safe-target-shape safe (eraseʷ p)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p) (tag ι) bound
      | ()
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p)
        (tagˣ X∈ X<Δ) bound
      with inst-safe-target-shape safe (eraseʷ p)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst {safe = safe} nonvar occ p)
        (tagˣ X∈ X<Δ) bound
      | ()
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (inst nonvar occ p) tag⇒ bound =
    _ , _ , refl ,
      inst-tag nonvar occ
        (recontext-to-funʷ
          (gen-star-incl (compose-star-left comp)) p)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (p₁ ↦ p₂) tag⇒ bound
      with wrap-tag-indexed
             (recontext-from-starⁿ
                (compose-star-left comp) p₁
                ↦ recontext-to-starʷ
                    (compose-star-left comp) p₂)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (p₁ ↦ p₂) tag⇒ bound
      | u , r , eq-wrap , r⊢ rewrite eq-wrap =
    u , r , refl , r⊢
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (p₁ ↦ p₂) (tag q₁ ↦ˡ q₂) bound
      with composeⁿ-typed-fuel comp q₁ p₁
             (two-lower-fuel
               (sum-swap-two-smaller
                 (size-↦ˡ s₁ s₂)
                 (<-trans (size-↦ˡ t₁ t₂)
                   (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
               bound)
         | composeʷ-typed-fuel comp p₂ q₂
             (two-lower-fuel
               (sum-two-smaller
                 (size-↦ʳ s₁ s₂)
                 (<-trans (size-↦ʳ t₁ t₂)
                   (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
               bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (p₁ ↦ p₂) (tag q₁ ↦ˡ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      with wrap-tag-indexed (r₁⊢ ↦ r₂⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (p₁ ↦ p₂) (tag q₁ ↦ˡ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      | u , r , eq-wrap , r⊢
      rewrite eq₁ | eq₂ | eq-wrap =
    u , r , refl , r⊢
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (p₁ ↦ p₂) (tag q₁ ↦ʳ q₂) bound
      with composeⁿ-typed-fuel comp q₁ p₁
             (two-lower-fuel
               (sum-swap-two-smaller
                 (size-↦ˡ s₁ s₂)
                 (<-trans (size-↦ˡ t₁ t₂)
                   (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
               bound)
         | composeʷ-typed-fuel comp p₂ q₂
             (two-lower-fuel
               (sum-two-smaller
                 (size-↦ʳ s₁ s₂)
                 (<-trans (size-↦ʳ t₁ t₂)
                   (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !))))
               bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (p₁ ↦ p₂) (tag q₁ ↦ʳ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      with wrap-tag-indexed (r₁⊢ ↦ r₂⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (p₁ ↦ p₂) (tag q₁ ↦ʳ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      | u , r , eq-wrap , r⊢
      rewrite eq₁ | eq₂ | eq-wrap =
    u , r , refl , r⊢
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      comp (p₁ ↦ p₂) (q₁ ↦ q₂) bound
      with composeⁿ-typed-fuel comp q₁ p₁
             (two-lower-fuel
               (sum-swap-two-smaller
                 (size-↦ˡ s₁ s₂) (size-↦ˡ t₁ t₂))
               bound)
         | composeʷ-typed-fuel comp p₂ q₂
             (two-lower-fuel
               (sum-two-smaller
                 (size-↦ʳ s₁ s₂) (size-↦ʳ t₁ t₂))
               bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = s₁ ↦ s₂} {d = t₁ ↦ t₂}
      comp (p₁ ↦ p₂) (q₁ ↦ q₂) bound
      | u₁ , r₁ , eq₁ , r₁⊢
      | u₂ , r₂ , eq₂ , r₂⊢
      rewrite eq₁ | eq₂ =
    _ , _ , refl , (r₁⊢ ↦ r₂⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (∀ⁱ p) (∀ⁱ q) bound
      with composeʷ-typed-fuel (compose-all comp) p q
             (two-lower-fuel
               (sum-two-smaller (size-under _) (size-under _))
               bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      comp (∀ⁱ p) (∀ⁱ q) bound
      | u , r , eq , r⊢ rewrite eq =
    _ , _ , refl , ∀ⁱ r⊢
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t₁ ↦ t₂}
      comp (inst {safe = safeA} nonvarA occA p)
        (q₁ ↦ q₂) bound
      with composeʷ-typed-fuel (compose-gen comp)
             (target-lift-genʷ p)
             (source-liftʷ (q₁ ↦ q₂))
             (subst (λ k → coercion-size s + k < suc fuel)
               (sym (size-rename suc (t₁ ↦ t₂)))
               (lower-fuel
                 (sum-left-smaller (size-under s))
                 bound))
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t₁ ↦ t₂}
      comp (inst {safe = safeA} nonvarA occA p)
        (q₁ ↦ q₂) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             fun (eraseʷ r⊢) r
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = t₁ ↦ t₂}
      comp (inst {safe = safeA} nonvarA occA p)
        (q₁ ↦ q₂) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = `∀ t}
      comp (inst {safe = safeA} nonvarA occA p)
        (∀ⁱ q) bound
      with composeʷ-typed-fuel (compose-gen comp)
             (target-lift-genʷ p)
             (source-liftʷ (∀ⁱ q))
             (subst (λ k → coercion-size s + k < suc fuel)
               (sym (size-rename suc (`∀ t)))
               (lower-fuel
                 (sum-left-smaller (size-under s))
                 bound))
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = `∀ t}
      comp (inst {safe = safeA} nonvarA occA p)
        (∀ⁱ q) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             all (eraseʷ r⊢) r
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = `∀ t}
      comp (inst {safe = safeA} nonvarA occA p)
        (∀ⁱ q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (tag q₁ ↦ˡ q₂) bound
      with composeʷ-typed-fuel (compose-gen comp)
             (target-lift-genʷ p)
             (source-liftʷ (q₁ ↦ q₂))
             (subst (λ k → coercion-size s + k < suc fuel)
               (sym (size-rename suc (t₁ ↦ t₂)))
               (lower-fuel
                 (+-mono-<
                   (size-under s)
                   (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !)))
                 bound))
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (tag q₁ ↦ˡ q₂) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             fun (eraseʷ r⊢) r
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (tag q₁ ↦ˡ q₂) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst-tag nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (tag q₁ ↦ʳ q₂) bound
      with composeʷ-typed-fuel (compose-gen comp)
             (target-lift-genʷ p)
             (source-liftʷ (q₁ ↦ q₂))
             (subst (λ k → coercion-size s + k < suc fuel)
               (sym (size-rename suc (t₁ ↦ t₂)))
               (lower-fuel
                 (+-mono-<
                   (size-under s)
                   (size-︔ˡ (t₁ ↦ t₂) (★⇒★ !)))
                 bound))
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (tag q₁ ↦ʳ q₂) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             fun (eraseʷ r⊢) r
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = (t₁ ↦ t₂) ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (tag q₁ ↦ʳ q₂) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst-tag nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t}
      comp (∀ⁱ p)
        (inst {safe = safeC} nonvarB occB q) bound
      with composeʷ-typed-fuel (compose-all-gen comp) p q
             (lower-fuel
               (+-mono-< (size-under s) (size-under t))
               bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t}
      comp (∀ⁱ p)
        (inst {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             (inst-safe-target-shape safeC (eraseʷ q))
             (eraseʷ r⊢) r
      where
      occA = member-backʷ
        (all-var-map (compose-map-var comp)) p occB
      nonvarA = nonvar-backʷ p nonvarB occB
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t}
      comp (∀ⁱ p)
        (inst {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
    where
    occA = member-backʷ
      (all-var-map (compose-map-var comp)) p occB
    nonvarA = nonvar-backʷ p nonvarB occB
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t}
      comp (inst {safe = safeA} nonvarA occA p)
        (inst {safe = safeC} nonvarB occB q) bound
      with composeʷ-typed-fuel (compose-gen comp)
             (target-lift-genʷ p)
             (source-liftʷ
               (inst {safe = safeC} nonvarB occB q))
             (subst (λ k → coercion-size s + k < suc fuel)
               (sym (size-rename suc (inst t)))
               (lower-fuel
                 (sum-left-smaller (size-under s))
                 bound))
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t}
      comp (inst {safe = safeA} nonvarA occA p)
        (inst {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             (inst-safe-target-shape safeC (eraseʷ q))
             (eraseʷ r⊢) r
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t}
      comp (inst {safe = safeA} nonvarA occA p)
        (inst {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      comp (∀ⁱ p)
        (inst-tag {safe = safeC} nonvarB occB q) bound
      with composeʷ-typed-fuel (compose-all-gen comp) p q
             (two-lower-fuel
               (sum-two-smaller
                 (size-under s)
                 (<-trans (size-under t)
                   (size-︔ˡ (inst t) (★⇒★ !))))
               bound)
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      comp (∀ⁱ p)
        (inst-tag {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             fun (eraseʷ r⊢) r
      where
      occA = member-backʷ
        (all-var-map (compose-map-var comp)) p occB
      nonvarA = nonvar-backʷ p nonvarB occB
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = `∀ s} {d = inst t ︔ (★⇒★ !)}
      comp (∀ⁱ p)
        (inst-tag {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst-tag nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)
    where
    occA = member-backʷ
      (all-var-map (compose-map-var comp)) p occB
    nonvarA = nonvar-backʷ p nonvarB occB
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (inst-tag {safe = safeC} nonvarB occB q) bound
      with composeʷ-typed-fuel (compose-gen comp)
             (target-lift-genʷ p)
             (source-liftʷ
               (inst {safe = safeC} nonvarB occB q))
             (subst (λ k → coercion-size s + k < suc fuel)
               (sym (size-rename suc (inst t)))
               (lower-fuel
                 (+-mono-<
                   (size-under s)
                   (size-︔ˡ (inst t) (★⇒★ !)))
                 bound))
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (inst-tag {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢
      with inst-safe
             (nonvar-member-shape nonvarA occA)
             fun (eraseʷ r⊢) r
  composeʷ-typed-fuel {fuel = suc (suc fuel)}
      {c = inst s} {d = inst t ︔ (★⇒★ !)}
      comp (inst {safe = safeA} nonvarA occA p)
        (inst-tag {safe = safeC} nonvarB occB q) bound
      | u , r , eq , r⊢ | safe , eq-safe
      rewrite eq | eq-safe =
    _ , _ , refl ,
      inst-tag nonvarA occA
        (subst
          (λ w → _ ∣ _ ⊢ w ⦂ _ ⊑ _ ⊣ _)
          (sym (instSafe?-sound r eq-safe))
          r⊢)

------------------------------------------------------------------------
-- Totality of the public composition operators
------------------------------------------------------------------------

narrowing-composition-total : ∀ {c d Φ Δᴸ Δᴿ A B C}
  {n : Narrowing c} {m : Narrowing d}
  → Φ ∣ Δᴸ ⊢ n ⦂ A ⊒ B ⊣ Δᴿ
  → idᵢ Δᴿ ∣ Δᴿ ⊢ m ⦂ B ⊒ C ⊣ Δᴿ
  → Σ[ u ∈ Coercion ] Σ[ r ∈ Narrowing u ]
      (n ⨟ⁿ m ≡ just (u , r)) ×
      (Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ)
narrowing-composition-total {c = c} {d = d} {Φ = Φ}
    {Δᴿ = Δᴿ} p q =
  composeⁿ-typed-fuel (compose-id-left Δᴿ Φ) p q
    (n<1+n (coercion-size c + coercion-size d))

widening-composition-total : ∀ {c d Φ Δᴸ Δᴿ A B C}
  {w : Widening c} {v : Widening d}
  → idᵢ Δᴸ ∣ Δᴸ ⊢ w ⦂ A ⊑ B ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ v ⦂ B ⊑ C ⊣ Δᴿ
  → Σ[ u ∈ Coercion ] Σ[ r ∈ Widening u ]
      (w ⨟ʷ v ≡ just (u , r)) ×
      (Φ ∣ Δᴸ ⊢ r ⦂ A ⊑ C ⊣ Δᴿ)
widening-composition-total {c = c} {d = d} {Φ = Φ}
    {Δᴸ = Δᴸ} p q =
  composeʷ-typed-fuel (compose-id-left Δᴸ Φ) p q
    (n<1+n (coercion-size c + coercion-size d))

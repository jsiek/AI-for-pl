module proof.LR.PrecisionSubst where

-- File Charter:
--   * Renaming and substitution of two-context precision derivations
--     (notes/logrel-dgg.md, Section 6.9, item 4).  Both are structural,
--     so the value relation at the result unfolds rule by rule along
--     the original derivation.
--   * A renaming maps paired variables to paired ones and left-only
--     variables to left-only ones.  The weakenings under `pair`, `only`
--     and `dead` are instances.
--   * A substitution maps each paired variable `X ↔ Y` to a derivation
--     of `σl X ⊑ σr Y`, and each left-only variable `X` to a derivation
--     of `σl X ⊑ ★`.  So the rule at every node is kept, except at the
--     variables, and at `∀⊑★` over a left-only variable sent to `★`,
--     which becomes `∀★⊑★`.  The type applications are instances:
--     `•⊑•` substitutes for a paired variable, `•⊑` for a left-only
--     one.
--   * Precision into a variable relates a paired variable only.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

open import Types
open import Consistency using (subst-∈ᵗ)
open import LR.Precision
open import proof.Consistency using (rename-occursᶜ)
open import proof.TypeInTermSubst using (renameᵗ-id)

private
  variable
    Δ₁ Δ₁′ Δ₂ Δ₂′ : TyCtx

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

record CRen (Ψ : Corr Δ₁ Δ₁′) (Ψ′ : Corr Δ₂ Δ₂′) : Set where
  field
    ρl : Δ₁ ⇒ʳ Δ₂
    ρr : Δ₁′ ⇒ʳ Δ₂′
    ren↔ : ∀ {X Y} → Ψ ∋ X ↔ Y → Ψ′ ∋ ρl X ↔ ρr Y
    renOnly : ∀ {X} → Ψ ∋ X only → Ψ′ ∋ ρl X only

open CRen public

module _ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′) where

  ext-pairᴿ : CRen (pair Ψ) (pair Ψ′)
  ρl ext-pairᴿ = extᵗ (ρl R)
  ρr ext-pairᴿ = extᵗ (ρr R)
  ren↔ ext-pairᴿ ↔-here = ↔-here
  ren↔ ext-pairᴿ (↔-pair x) = ↔-pair (ren↔ R x)
  renOnly ext-pairᴿ (only-pair x) = only-pair (renOnly R x)

  ext-onlyᴿ : CRen (only Ψ) (only Ψ′)
  ρl ext-onlyᴿ = extᵗ (ρl R)
  ρr ext-onlyᴿ = ρr R
  ren↔ ext-onlyᴿ (↔-only x) = ↔-only (ren↔ R x)
  renOnly ext-onlyᴿ only-here = only-here
  renOnly ext-onlyᴿ (only-only x) = only-only (renOnly R x)

  ext-deadᴿ : CRen (dead Ψ) (dead Ψ′)
  ρl ext-deadᴿ = extᵗ (ρl R)
  ρr ext-deadᴿ = ρr R
  ren↔ ext-deadᴿ (↔-dead x) = ↔-dead (ren↔ R x)
  renOnly ext-deadᴿ (only-dead x) = only-dead (renOnly R x)

module _ {Ψ : Corr Δ₁ Δ₁′} where

  wk-pairᴿ : CRen Ψ (pair Ψ)
  ρl wk-pairᴿ = suc
  ρr wk-pairᴿ = suc
  ren↔ wk-pairᴿ = ↔-pair
  renOnly wk-pairᴿ = only-pair

  wk-onlyᴿ : CRen Ψ (only Ψ)
  ρl wk-onlyᴿ = suc
  ρr wk-onlyᴿ Y = Y
  ren↔ wk-onlyᴿ = ↔-only
  renOnly wk-onlyᴿ = only-only

  wk-deadᴿ : CRen Ψ (dead Ψ)
  ρl wk-deadᴿ = suc
  ρr wk-deadᴿ Y = Y
  ren↔ wk-deadᴿ = ↔-dead
  renOnly wk-deadᴿ = only-dead

renameNonStar : ∀ {A : Ty Δ₁} (ρ : Δ₁ ⇒ʳ Δ₂)
  → NonStar A → NonStar (renameᵗ ρ A)
renameNonStar ρ nonstar-X = nonstar-X
renameNonStar ρ nonstar-ι = nonstar-ι
renameNonStar ρ nonstar-⇒ = nonstar-⇒
renameNonStar ρ nonstar-∀ = nonstar-∀

renᵖ : ∀ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (R : CRen Ψ Ψ′) {A B}
  → Ψ ⊢ A ⊑ B → Ψ′ ⊢ renameᵗ (ρl R) A ⊑ renameᵗ (ρr R) B
renᵖ R ★⊑★ = ★⊑★
renᵖ R ι⊑ι = ι⊑ι
renᵖ R (X⊑Y x) = X⊑Y (ren↔ R x)
renᵖ R (⇒⊑⇒ p q) = ⇒⊑⇒ (renᵖ R p) (renᵖ R q)
renᵖ R (∀⊑∀ p) = ∀⊑∀ (renᵖ (ext-pairᴿ R) p)
renᵖ R (⇒⊑★ p q) = ⇒⊑★ (renᵖ R p) (renᵖ R q)
renᵖ R ι⊑★ = ι⊑★
renᵖ R (X⊑★ x) = X⊑★ (renOnly R x)
renᵖ R (∀⊑ a z p) =
  ∀⊑ (renameNonVar _ a) (rename-occursᶜ (extᵗ (ρl R)) z)
    (renᵖ (ext-onlyᴿ R) p)
renᵖ R ∀★⊑★ = ∀★⊑★
renᵖ R (∀⊑★ ns p) = ∀⊑★ (renameNonStar _ ns) (renᵖ (ext-deadᴿ R) p)
renᵖ R bot-elim = bot-elim
renᵖ R bot⊑★ = bot⊑★

-- weakenings that leave the right type alone
wk-onlyᵖ : ∀ {Ψ : Corr Δ₁ Δ₁′} {A B}
  → Ψ ⊢ A ⊑ B → only Ψ ⊢ ⇑ᵗ A ⊑ B
wk-onlyᵖ {B = B} p =
  subst (λ C → _ ⊢ _ ⊑ C) (renameᵗ-id B) (renᵖ wk-onlyᴿ p)

wk-deadᵖ : ∀ {Ψ : Corr Δ₁ Δ₁′} {A B}
  → Ψ ⊢ A ⊑ B → dead Ψ ⊢ ⇑ᵗ A ⊑ B
wk-deadᵖ {B = B} p =
  subst (λ C → _ ⊢ _ ⊑ C) (renameᵗ-id B) (renᵖ wk-deadᴿ p)

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

record PSub (Ψ : Corr Δ₁ Δ₁′) (Ψ′ : Corr Δ₂ Δ₂′) : Set where
  field
    σl : Δ₁ ⇒ˢ Δ₂
    σr : Δ₁′ ⇒ˢ Δ₂′
    σ↔ : ∀ {X Y} → Ψ ∋ X ↔ Y → Ψ′ ⊢ σl X ⊑ σr Y
    σo : ∀ {X} → Ψ ∋ X only → Ψ′ ⊢ σl X ⊑ ★

open PSub public

module _ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′) where

  exts-pairˢ : PSub (pair Ψ) (pair Ψ′)
  σl exts-pairˢ = extsᵗ (σl S)
  σr exts-pairˢ = extsᵗ (σr S)
  σ↔ exts-pairˢ ↔-here = X⊑Y ↔-here
  σ↔ exts-pairˢ (↔-pair x) = renᵖ wk-pairᴿ (σ↔ S x)
  σo exts-pairˢ (only-pair x) = renᵖ wk-pairᴿ (σo S x)

  exts-onlyˢ : PSub (only Ψ) (only Ψ′)
  σl exts-onlyˢ = extsᵗ (σl S)
  σr exts-onlyˢ = σr S
  σ↔ exts-onlyˢ (↔-only x) = wk-onlyᵖ (σ↔ S x)
  σo exts-onlyˢ only-here = X⊑★ only-here
  σo exts-onlyˢ (only-only x) = wk-onlyᵖ (σo S x)

  exts-deadˢ : PSub (dead Ψ) (dead Ψ′)
  σl exts-deadˢ = extsᵗ (σl S)
  σr exts-deadˢ = σr S
  σ↔ exts-deadˢ (↔-dead x) = wk-deadᵖ (σ↔ S x)
  σo exts-deadˢ (only-dead x) = wk-deadᵖ (σo S x)

-- `∀⊑★` over a left-only variable sent to C: the body stays a
-- non-`★`, except that `∀X.★` is `∀★⊑★`
∀★ᵖ : ∀ {Ψ : Corr Δ₁ Δ₁′} {C} → Ψ ⊢ C ⊑ ★ → Ψ ⊢ `∀ (⇑ᵗ C) ⊑ ★
∀★ᵖ ★⊑★ = ∀★⊑★
∀★ᵖ q@(⇒⊑★ p₁ p₂) = ∀⊑★ nonstar-⇒ (wk-deadᵖ q)
∀★ᵖ q@ι⊑★ = ∀⊑★ nonstar-ι (wk-deadᵖ q)
∀★ᵖ q@(X⊑★ x) = ∀⊑★ nonstar-X (wk-deadᵖ q)
∀★ᵖ q@(∀⊑ a z p) = ∀⊑★ nonstar-∀ (wk-deadᵖ q)
∀★ᵖ q@∀★⊑★ = ∀⊑★ nonstar-∀ (wk-deadᵖ q)
∀★ᵖ q@(∀⊑★ ns p) = ∀⊑★ nonstar-∀ (wk-deadᵖ q)
∀★ᵖ q@bot⊑★ = ∀⊑★ nonstar-∀ (wk-deadᵖ q)

substᵖ : ∀ {Ψ : Corr Δ₁ Δ₁′} {Ψ′ : Corr Δ₂ Δ₂′} (S : PSub Ψ Ψ′) {A B}
  → Ψ ⊢ A ⊑ B → Ψ′ ⊢ substᵗ (σl S) A ⊑ substᵗ (σr S) B
substᵖ S ★⊑★ = ★⊑★
substᵖ S ι⊑ι = ι⊑ι
substᵖ S (X⊑Y x) = σ↔ S x
substᵖ S (⇒⊑⇒ p q) = ⇒⊑⇒ (substᵖ S p) (substᵖ S q)
substᵖ S (∀⊑∀ p) = ∀⊑∀ (substᵖ (exts-pairˢ S) p)
substᵖ S (⇒⊑★ p q) = ⇒⊑★ (substᵖ S p) (substᵖ S q)
substᵖ S ι⊑★ = ι⊑★
substᵖ S (X⊑★ x) = σo S x
substᵖ S (∀⊑ a z p) =
  ∀⊑ (substNonVar _ a) (subst-∈ᵗ z var-∈) (substᵖ (exts-onlyˢ S) p)
substᵖ S ∀★⊑★ = ∀★⊑★
substᵖ S (∀⊑★ nonstar-X (X⊑★ (only-dead x))) = ∀★ᵖ (σo S x)
substᵖ S (∀⊑★ nonstar-ι p) = ∀⊑★ nonstar-ι (substᵖ (exts-deadˢ S) p)
substᵖ S (∀⊑★ nonstar-⇒ p) = ∀⊑★ nonstar-⇒ (substᵖ (exts-deadˢ S) p)
substᵖ S (∀⊑★ nonstar-∀ p) = ∀⊑★ nonstar-∀ (substᵖ (exts-deadˢ S) p)
substᵖ S bot-elim = bot-elim
substᵖ S bot⊑★ = bot⊑★

-- substituting for the outermost paired variable (`•⊑•`)
singleˢ : ∀ {Ψ : Corr Δ₁ Δ₁′} {T T′} → Ψ ⊢ T ⊑ T′ → PSub (pair Ψ) Ψ
σl (singleˢ {T = T} q) = singleSubᵗ T
σr (singleˢ {T′ = T′} q) = singleSubᵗ T′
σ↔ (singleˢ q) ↔-here = q
σ↔ (singleˢ q) (↔-pair x) = X⊑Y x
σo (singleˢ q) (only-pair x) = X⊑★ x

-- substituting for the outermost left-only variable (`•⊑`)
singleOˢ : ∀ {Ψ : Corr Δ₁ Δ₁′} {T} → Ψ ⊢ T ⊑ ★ → PSub (only Ψ) Ψ
σl (singleOˢ {T = T} q) = singleSubᵗ T
σr (singleOˢ q) Y = ＇ Y
σ↔ (singleOˢ q) (↔-only x) = X⊑Y x
σo (singleOˢ q) only-here = q
σo (singleOˢ q) (only-only x) = X⊑★ x

------------------------------------------------------------------------
-- Precision into a variable
------------------------------------------------------------------------

⊑-var : ∀ {Ψ : Corr Δ₁ Δ₁′} {A Y}
  → Ψ ⊢ A ⊑ ＇ Y → Σ[ X ∈ TyVar Δ₁ ] (A ≡ ＇ X × Ψ ∋ X ↔ Y)
⊑-var (X⊑Y x) = _ , refl , x
⊑-var (∀⊑ a z p) with ⊑-var p
⊑-var (∀⊑ a z p) | X , refl , x = ⊥-elim (zero-unpaired z x)
  where
  zero-unpaired : ∀ {Ψ : Corr Δ₁ Δ₁′} {X Y}
    → zero ∈ᵗ ＇ X → only Ψ ∋ X ↔ Y → ⊥
  zero-unpaired var-∈ ()

-- so `∀⊑` never has a variable on the right
∀⊑-var⊥ : ∀ {Ψ : Corr Δ₁ Δ₁′} {A Y}
  → NonVar A → zero ∈ᵗ A → only Ψ ⊢ A ⊑ ＇ Y → ⊥
∀⊑-var⊥ a z p with ⊑-var p
∀⊑-var⊥ () z p | X , refl , x

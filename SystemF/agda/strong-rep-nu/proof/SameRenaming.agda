module strong-rep-nu.proof.SameRenaming where

-- File Charter:
--   * `_⊢_~_` IS RENAMING.  On a well-formed type, `names Δ ⊢ A ~ R`
--     holds exactly when `R` is `A` renamed through the name map
--     (`same→ren`, `ren→same`); `_⊢_≈_⊣_` is then an equation between
--     two renamings (`≈→ren`, `ren→≈`).
--   * The relation is kept (it bundles scoping with the result and
--     inverts by pattern matching); this file only records what it means.
-- Commentary: Commentary.md § proof/SameRenaming.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx using (∋ˡ-ren⁻)
open import strong-rep-nu.proof.Preserve using (wf-same; same-wf)

------------------------------------------------------------------------
-- 1.  The name map read as a renaming
------------------------------------------------------------------------

-- Off the map `read` returns X itself; that value is never consulted on
-- a well-formed type.
read : TyCtx → Renameᵗ
read []      X       = X
read (α ∷ η) zero    = α
read (α ∷ η) (suc X) = read η X

infix 5 ⟦_⟧_
⟦_⟧_ : Ty → TyCtx → Ty
⟦ A ⟧ η = renameᵗ (read η) A

-- ρ agrees with the name map η on every name η maps.
Agrees : Renameᵗ → TyCtx → Set
Agrees ρ η = ∀ {X α} → η ∋ˡ X := α → ρ X ≡ α

read-agrees : ∀ {η} → Agrees (read η) η
read-agrees here      = refl
read-agrees (there d) = read-agrees d

-- Going under a `∀` extends the renaming exactly as `same-∀` extends
-- the name map.
agrees-ext : ∀ {ρ η} → Agrees ρ η → Agrees (extᵗ ρ) (zero ∷ shiftReps η)
agrees-ext ag here = refl
agrees-ext {η = η} ag (there d) with ∋ˡ-ren⁻ suc η d
... | α , d′ , refl = cong suc (ag d′)

------------------------------------------------------------------------
-- 2.  `_⊢_~_` is renaming
------------------------------------------------------------------------

~→ren : ∀ {ρ η A R} → Agrees ρ η → η ⊢ A ~ R → renameᵗ ρ A ≡ R
~→ren ag (same-var d) = cong `_ (ag d)
~→ren ag same-ℕ       = refl
~→ren ag same-𝔹       = refl
~→ren ag (same-⇒ p q) = cong₂ _⇒_ (~→ren ag p) (~→ren ag q)
~→ren ag (same-∀ p)   = cong `∀ (~→ren (agrees-ext ag) p)

same→ren : ∀ {Δ A R} → names Δ ⊢ A ~ R
  → (Δ ⊢ᵗ A) × (⟦ A ⟧ names Δ ≡ R)
same→ren {Δ = Δ} p = same-wf {Δ = Δ} p , ~→ren read-agrees p

ren→same : ∀ {Δ A R} → Δ ⊢ᵗ A → ⟦ A ⟧ names Δ ≡ R → names Δ ⊢ A ~ R
ren→same w eq with wf-same w
... | R′ , p = subst (_ ⊢ _ ~_) (trans (sym (~→ren read-agrees p)) eq) p

------------------------------------------------------------------------
-- 3.  `_⊢_≈_⊣_` is an equation between renamings
------------------------------------------------------------------------

≈→ren : ∀ {Δ Δ′ A B} → Δ ⊢ A ≈ B ⊣ Δ′
  → (Δ ⊢ᵗ A) × (Δ′ ⊢ᵗ B) × (⟦ A ⟧ names Δ ≡ ⟦ B ⟧ names Δ′)
≈→ren {Δ = Δ} {Δ′} (R , p , q) with same→ren {Δ = Δ} p
                                    | same→ren {Δ = Δ′} q
... | wA , eqA | wB , eqB = wA , wB , trans eqA (sym eqB)

ren→≈ : ∀ {Δ Δ′ A B} → Δ ⊢ᵗ A → Δ′ ⊢ᵗ B
  → ⟦ A ⟧ names Δ ≡ ⟦ B ⟧ names Δ′ → Δ ⊢ A ≈ B ⊣ Δ′
ren→≈ wA wB eq = _ , ren→same wA refl , ren→same wB (sym eq)

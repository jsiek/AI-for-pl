module proof.Relabel where

-- File Charter:
--   * Relabeling the two sides of a term precision derivation
--     d : Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p (TermPrecision.agda): `relabelL d` is M
--     and `relabelR d` is M′, except that every instantiation carries
--     the derivation q of its ⊑inst rule as its label.  Corresponding
--     instantiations of the two relabeled programs thus carry the same
--     label.
--   * Label-insensitive equality of terms `_≈ˡ_` (congruence on every
--     constructor, any two labels on `inst`) and of stores `_≈ˢ_` (same
--     types, any labels), with reflexivity and symmetry.
--   * Main results: `relabelL-≈ˡ : relabelL d ≈ˡ M`,
--     `relabelR-≈ˡ : relabelR d ≈ˡ M′`, and `relabel-⊑`: the relabeled
--     programs are related by precision at the same type.
--   * Consumed by proof/LabelIrrelevance.agda, which shows that ≈ˡ
--     preserves the observable behavior of programs.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)

open import Types
open import Terms
open import TermPrecision

------------------------------------------------------------------------
-- Label-insensitive equality of terms and stores
------------------------------------------------------------------------

infix 4 _≈ˡ_ _≈ˢ_

data _≈ˡ_ : Term → Term → Set where
  ≈` : ∀ {x} → ` x ≈ˡ ` x
  ≈℧ : ℧ ≈ˡ ℧
  ≈true : true ≈ˡ true
  ≈false : false ≈ˡ false
  ≈if : ∀ {L L′ M M′ N N′} →
    L ≈ˡ L′ → M ≈ˡ M′ → N ≈ˡ N′ → if L M N ≈ˡ if L′ M′ N′
  ≈ƛ : ∀ {A M M′} → M ≈ˡ M′ → ƛ A M ≈ˡ ƛ A M′
  ≈· : ∀ {L L′ M M′} → L ≈ˡ L′ → M ≈ˡ M′ → L · M ≈ˡ L′ · M′
  ≈letv : ∀ {M M′ N N′} → M ≈ˡ M′ → N ≈ˡ N′ → letv M N ≈ˡ letv M′ N′
  ≈seal : ∀ {α M M′} → M ≈ˡ M′ → seal α M ≈ˡ seal α M′
  ≈unseal : ∀ {α M M′} → M ≈ˡ M′ → unseal α M ≈ˡ unseal α M′
  ≈is : ∀ {G M M′} → M ≈ˡ M′ → is G M ≈ˡ is G M′
  ≈inj : ∀ {G M M′} → M ≈ˡ M′ → inj G M ≈ˡ inj G M′
  ≈cast : ∀ {d p M M′} → M ≈ˡ M′ → cast d p M ≈ˡ cast d p M′
  ≈Λν : ∀ {cs M M′} → M ≈ˡ M′ → Λν cs M ≈ˡ Λν cs M′
  -- the labels ℓ and ℓ′ are arbitrary
  ≈inst : ∀ {M M′ B ℓ ℓ′ N N′} →
    M ≈ˡ M′ → N ≈ˡ N′ → inst M B ℓ N ≈ˡ inst M′ B ℓ′ N′

data _≈ˢ_ : Store → Store → Set where
  ≈[] : [] ≈ˢ []
  ≈∷ : ∀ {Σ Σ′ A ℓ ℓ′} → Σ ≈ˢ Σ′ → ((A , ℓ) ∷ Σ) ≈ˢ ((A , ℓ′) ∷ Σ′)

≈ˡ-refl : ∀ M → M ≈ˡ M
≈ˡ-refl (` x) = ≈`
≈ˡ-refl ℧ = ≈℧
≈ˡ-refl true = ≈true
≈ˡ-refl false = ≈false
≈ˡ-refl (if L M N) = ≈if (≈ˡ-refl L) (≈ˡ-refl M) (≈ˡ-refl N)
≈ˡ-refl (ƛ A M) = ≈ƛ (≈ˡ-refl M)
≈ˡ-refl (L · M) = ≈· (≈ˡ-refl L) (≈ˡ-refl M)
≈ˡ-refl (letv M N) = ≈letv (≈ˡ-refl M) (≈ˡ-refl N)
≈ˡ-refl (seal α M) = ≈seal (≈ˡ-refl M)
≈ˡ-refl (unseal α M) = ≈unseal (≈ˡ-refl M)
≈ˡ-refl (is G M) = ≈is (≈ˡ-refl M)
≈ˡ-refl (inj G M) = ≈inj (≈ˡ-refl M)
≈ˡ-refl (cast d p M) = ≈cast (≈ˡ-refl M)
≈ˡ-refl (Λν cs M) = ≈Λν (≈ˡ-refl M)
≈ˡ-refl (inst M B ℓ N) = ≈inst (≈ˡ-refl M) (≈ˡ-refl N)

≈ˡ-sym : ∀ {M M′} → M ≈ˡ M′ → M′ ≈ˡ M
≈ˡ-sym ≈` = ≈`
≈ˡ-sym ≈℧ = ≈℧
≈ˡ-sym ≈true = ≈true
≈ˡ-sym ≈false = ≈false
≈ˡ-sym (≈if L≈ M≈ N≈) = ≈if (≈ˡ-sym L≈) (≈ˡ-sym M≈) (≈ˡ-sym N≈)
≈ˡ-sym (≈ƛ M≈) = ≈ƛ (≈ˡ-sym M≈)
≈ˡ-sym (≈· L≈ M≈) = ≈· (≈ˡ-sym L≈) (≈ˡ-sym M≈)
≈ˡ-sym (≈letv M≈ N≈) = ≈letv (≈ˡ-sym M≈) (≈ˡ-sym N≈)
≈ˡ-sym (≈seal M≈) = ≈seal (≈ˡ-sym M≈)
≈ˡ-sym (≈unseal M≈) = ≈unseal (≈ˡ-sym M≈)
≈ˡ-sym (≈is M≈) = ≈is (≈ˡ-sym M≈)
≈ˡ-sym (≈inj M≈) = ≈inj (≈ˡ-sym M≈)
≈ˡ-sym (≈cast M≈) = ≈cast (≈ˡ-sym M≈)
≈ˡ-sym (≈Λν M≈) = ≈Λν (≈ˡ-sym M≈)
≈ˡ-sym (≈inst M≈ N≈) = ≈inst (≈ˡ-sym M≈) (≈ˡ-sym N≈)

≈ˢ-refl : ∀ Σ → Σ ≈ˢ Σ
≈ˢ-refl [] = ≈[]
≈ˢ-refl ((A , ℓ) ∷ Σ) = ≈∷ (≈ˢ-refl Σ)

≈ˢ-sym : ∀ {Σ Σ′} → Σ ≈ˢ Σ′ → Σ′ ≈ˢ Σ
≈ˢ-sym ≈[] = ≈[]
≈ˢ-sym (≈∷ Σ≈) = ≈∷ (≈ˢ-sym Σ≈)

------------------------------------------------------------------------
-- Relabeling
------------------------------------------------------------------------

relabelL : ∀ {Δ⊑ Γ⊑ M M′ p} → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p → Term
relabelL (⊑` {x = x} x∋) = ` x
relabelL (⊑letv dM dN) = letv (relabelL dM) (relabelL dN)
relabelL (⊑seal {X = X} X∋ dM) = seal (tvar X) (relabelL dM)
relabelL (⊑unseal {X = X} X∋ dM) = unseal (tvar X) (relabelL dM)
relabelL (⊑is {G = G} wfG dM) = is G (relabelL dM)
relabelL ⊑true = true
relabelL ⊑false = false
relabelL (⊑if dL dM dN) = if (relabelL dL) (relabelL dM) (relabelL dN)
relabelL (⊑ƛ {A = A} p⊢ dM) = ƛ A (relabelL dM)
relabelL (⊑· dL dM) = relabelL dL · relabelL dM
relabelL (⊑Λν dM) = Λν [] (relabelL dM)
relabelL (⊑inst {B = B} {q = q} dM q⊢ dN) =
  inst (relabelL dM) B q (relabelL dN)
relabelL (⊑upL {AB = AB} dM AB⊢ BC⊢ AC⊢) = cast up AB (relabelL dM)
relabelL (⊑downL {AB = AB} dM AB⊢ BC⊢ AC⊢) = cast down AB (relabelL dM)
relabelL (⊑upR dM AB⊢ BC⊢ AC⊢) = relabelL dM
relabelL (⊑downR dM AB⊢ BC⊢ AC⊢) = relabelL dM

relabelR : ∀ {Δ⊑ Γ⊑ M M′ p} → Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p → Term
relabelR (⊑` {x = x} x∋) = ` x
relabelR (⊑letv dM dN) = letv (relabelR dM) (relabelR dN)
relabelR (⊑seal {X = X} X∋ dM) = seal (tvar X) (relabelR dM)
relabelR (⊑unseal {X = X} X∋ dM) = unseal (tvar X) (relabelR dM)
relabelR (⊑is {G = G} wfG dM) = is G (relabelR dM)
relabelR ⊑true = true
relabelR ⊑false = false
relabelR (⊑if dL dM dN) = if (relabelR dL) (relabelR dM) (relabelR dN)
relabelR (⊑ƛ {A′ = A′} p⊢ dM) = ƛ A′ (relabelR dM)
relabelR (⊑· dL dM) = relabelR dL · relabelR dM
relabelR (⊑Λν dM) = Λν [] (relabelR dM)
relabelR (⊑inst {B′ = B′} {q = q} dM q⊢ dN) =
  inst (relabelR dM) B′ q (relabelR dN)
relabelR (⊑upL dM AB⊢ BC⊢ AC⊢) = relabelR dM
relabelR (⊑downL dM AB⊢ BC⊢ AC⊢) = relabelR dM
relabelR (⊑upR {BC = BC} dM AB⊢ BC⊢ AC⊢) = cast up BC (relabelR dM)
relabelR (⊑downR {BC = BC} dM AB⊢ BC⊢ AC⊢) =
  cast down BC (relabelR dM)

------------------------------------------------------------------------
-- Relabeling only changes labels
------------------------------------------------------------------------

relabelL-≈ˡ : ∀ {Δ⊑ Γ⊑ M M′ p}
  → (d : Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p)
  → relabelL d ≈ˡ M
relabelL-≈ˡ (⊑` x∋) = ≈`
relabelL-≈ˡ (⊑letv dM dN) = ≈letv (relabelL-≈ˡ dM) (relabelL-≈ˡ dN)
relabelL-≈ˡ (⊑seal X∋ dM) = ≈seal (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑unseal X∋ dM) = ≈unseal (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑is wfG dM) = ≈is (relabelL-≈ˡ dM)
relabelL-≈ˡ ⊑true = ≈true
relabelL-≈ˡ ⊑false = ≈false
relabelL-≈ˡ (⊑if dL dM dN) =
  ≈if (relabelL-≈ˡ dL) (relabelL-≈ˡ dM) (relabelL-≈ˡ dN)
relabelL-≈ˡ (⊑ƛ p⊢ dM) = ≈ƛ (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑· dL dM) = ≈· (relabelL-≈ˡ dL) (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑Λν dM) = ≈Λν (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑inst dM q⊢ dN) = ≈inst (relabelL-≈ˡ dM) (relabelL-≈ˡ dN)
relabelL-≈ˡ (⊑upL dM AB⊢ BC⊢ AC⊢) = ≈cast (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑downL dM AB⊢ BC⊢ AC⊢) = ≈cast (relabelL-≈ˡ dM)
relabelL-≈ˡ (⊑upR dM AB⊢ BC⊢ AC⊢) = relabelL-≈ˡ dM
relabelL-≈ˡ (⊑downR dM AB⊢ BC⊢ AC⊢) = relabelL-≈ˡ dM

relabelR-≈ˡ : ∀ {Δ⊑ Γ⊑ M M′ p}
  → (d : Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p)
  → relabelR d ≈ˡ M′
relabelR-≈ˡ (⊑` x∋) = ≈`
relabelR-≈ˡ (⊑letv dM dN) = ≈letv (relabelR-≈ˡ dM) (relabelR-≈ˡ dN)
relabelR-≈ˡ (⊑seal X∋ dM) = ≈seal (relabelR-≈ˡ dM)
relabelR-≈ˡ (⊑unseal X∋ dM) = ≈unseal (relabelR-≈ˡ dM)
relabelR-≈ˡ (⊑is wfG dM) = ≈is (relabelR-≈ˡ dM)
relabelR-≈ˡ ⊑true = ≈true
relabelR-≈ˡ ⊑false = ≈false
relabelR-≈ˡ (⊑if dL dM dN) =
  ≈if (relabelR-≈ˡ dL) (relabelR-≈ˡ dM) (relabelR-≈ˡ dN)
relabelR-≈ˡ (⊑ƛ p⊢ dM) = ≈ƛ (relabelR-≈ˡ dM)
relabelR-≈ˡ (⊑· dL dM) = ≈· (relabelR-≈ˡ dL) (relabelR-≈ˡ dM)
relabelR-≈ˡ (⊑Λν dM) = ≈Λν (relabelR-≈ˡ dM)
relabelR-≈ˡ (⊑inst dM q⊢ dN) = ≈inst (relabelR-≈ˡ dM) (relabelR-≈ˡ dN)
relabelR-≈ˡ (⊑upL dM AB⊢ BC⊢ AC⊢) = relabelR-≈ˡ dM
relabelR-≈ˡ (⊑downL dM AB⊢ BC⊢ AC⊢) = relabelR-≈ˡ dM
relabelR-≈ˡ (⊑upR dM AB⊢ BC⊢ AC⊢) = ≈cast (relabelR-≈ˡ dM)
relabelR-≈ˡ (⊑downR dM AB⊢ BC⊢ AC⊢) = ≈cast (relabelR-≈ˡ dM)

------------------------------------------------------------------------
-- The relabeled programs are still related by precision
------------------------------------------------------------------------

relabel-⊑ : ∀ {Δ⊑ Γ⊑ M M′ p}
  → (d : Δ⊑ ∣ Γ⊑ ⊢ M ⊑ M′ ⦂ p)
  → Δ⊑ ∣ Γ⊑ ⊢ relabelL d ⊑ relabelR d ⦂ p
relabel-⊑ (⊑` x∋) = ⊑` x∋
relabel-⊑ (⊑letv dM dN) = ⊑letv (relabel-⊑ dM) (relabel-⊑ dN)
relabel-⊑ (⊑seal X∋ dM) = ⊑seal X∋ (relabel-⊑ dM)
relabel-⊑ (⊑unseal X∋ dM) = ⊑unseal X∋ (relabel-⊑ dM)
relabel-⊑ (⊑is wfG dM) = ⊑is wfG (relabel-⊑ dM)
relabel-⊑ ⊑true = ⊑true
relabel-⊑ ⊑false = ⊑false
relabel-⊑ (⊑if dL dM dN) =
  ⊑if (relabel-⊑ dL) (relabel-⊑ dM) (relabel-⊑ dN)
relabel-⊑ (⊑ƛ p⊢ dM) = ⊑ƛ p⊢ (relabel-⊑ dM)
relabel-⊑ (⊑· dL dM) = ⊑· (relabel-⊑ dL) (relabel-⊑ dM)
relabel-⊑ (⊑Λν dM) = ⊑Λν (relabel-⊑ dM)
relabel-⊑ (⊑inst dM q⊢ dN) = ⊑inst (relabel-⊑ dM) q⊢ (relabel-⊑ dN)
relabel-⊑ (⊑upL dM AB⊢ BC⊢ AC⊢) = ⊑upL (relabel-⊑ dM) AB⊢ BC⊢ AC⊢
relabel-⊑ (⊑downL dM AB⊢ BC⊢ AC⊢) = ⊑downL (relabel-⊑ dM) AB⊢ BC⊢ AC⊢
relabel-⊑ (⊑upR dM AB⊢ BC⊢ AC⊢) = ⊑upR (relabel-⊑ dM) AB⊢ BC⊢ AC⊢
relabel-⊑ (⊑downR dM AB⊢ BC⊢ AC⊢) = ⊑downR (relabel-⊑ dM) AB⊢ BC⊢ AC⊢

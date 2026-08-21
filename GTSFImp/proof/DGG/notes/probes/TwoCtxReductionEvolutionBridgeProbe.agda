{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxReductionEvolutionBridgeProbe where

-- File Charter:
--   * Checks the smallest bridge from trusted one-step reduction outcomes to
--     the canonical two-Ctx WorldEvolutionRequest.
--   * Shows that reduction determines only keep/bind indices: right-only
--     allocation additionally needs direct freshness, and paired allocation
--     additionally needs direct type imprecision and an explicit mark choice.
--   * Gives concrete trusted reductions for which those extra facts fail;
--     it adds no old-World bridge and changes no live relation.

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (Ty; ‵_; ★; `ℕ; `𝔹; ⇑ᵗ)
open import Primitives using (κℕ; κ𝔹)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Ctx; Δᵉ; Term; Λ_; _⦂∀_[_]; $; _↑_)
open import Reduction using
  (keep; bind; _—→[_]_; β-Λ)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TwoCtxWorldEvolutionProducer


request-keep-from-reductions : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ}
    {M N : Term (Δᵉ Cᴸ)} {M′ N′ : Term (Δᵉ Cᴿ)}
  → M —→[ keep ] N
  → M′ —→[ keep ] N′
  → WorldEvolutionRequest W keep keep
request-keep-from-reductions left-step right-step =
  evolution-request-keep


request-left-from-reduction : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {A : Ty (Δᵉ Cᴸ)}
    {M : Term (Δᵉ Cᴸ)} {N : Term (Nat.suc (Δᵉ Cᴸ))}
  → M —→[ bind A ] N
  → WorldEvolutionRequest W (bind A) keep
request-left-from-reduction left-step =
  evolution-request-left refl


request-right-from-reduction : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {B : Ty (Δᵉ Cᴿ)}
    {M′ : Term (Δᵉ Cᴿ)} {N′ : Term (Nat.suc (Δᵉ Cᴿ))}
  → M′ —→[ bind B ] N′
  → RightBindFreshᶜ W B
  → WorldEvolutionRequest W keep (bind B)
request-right-from-reduction right-step fresh =
  evolution-request-right fresh refl


request-paired-precise-from-reductions : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    {M : Term (Δᵉ Cᴸ)} {N : Term (Nat.suc (Δᵉ Cᴸ))}
    {M′ : Term (Δᵉ Cᴿ)} {N′ : Term (Nat.suc (Δᵉ Cᴿ))}
  → M —→[ bind A ] N
  → M′ —→[ bind B ] N′
  → A ⊑ᵀ⟨ W ⟩ B
  → WorldEvolutionRequest W (bind A) (bind B)
request-paired-precise-from-reductions left-step right-step represented =
  evolution-request-both-precise represented refl refl


request-paired-dynamic-from-reductions : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    {M : Term (Δᵉ Cᴸ)} {N : Term (Nat.suc (Δᵉ Cᴸ))}
    {M′ : Term (Δᵉ Cᴿ)} {N′ : Term (Nat.suc (Δᵉ Cᴿ))}
  → M —→[ bind A ] N
  → M′ —→[ bind B ] N′
  → A ⊑ᵀ⟨ W ⟩ B
  → ⇑ᵗ A ≢ ★
  → WorldEvolutionRequest W (bind A) (bind B)
request-paired-dynamic-from-reductions
    left-step right-step represented A≢★ =
  evolution-request-both-dynamic represented A≢★ refl refl


right-request-fresh : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ} {B : Ty (Δᵉ Cᴿ)}
  → WorldEvolutionRequest W keep (bind B)
  → RightBindFreshᶜ W B
right-request-fresh (evolution-request-right fresh eqᴿ) = fresh


paired-request-direct : ∀ {Cᴸ Cᴿ : Ctx}
    {W : Cᴸ ⊑ᶜ Cᴿ}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
  → WorldEvolutionRequest W (bind A) (bind B)
  → A ⊑ᵀ⟨ W ⟩ B
paired-request-direct
    (evolution-request-both-precise represented eqᴸ eqᴿ) = represented
paired-request-direct
    (evolution-request-both-dynamic represented A≢★ eqᴸ eqᴿ) = represented


nat-allocation-step :
    ((Λ ($ (κℕ Nat.zero))) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ])
      —→[ bind (‵ `ℕ) ]
    ($ (κℕ Nat.zero))
      ↑ 〖 Fin.zero , ⇑ᵗ (‵ `ℕ) ↑ (‵ `ℕ) 〗
nat-allocation-step =
  β-Λ {Nat.zero} {A = ‵ `ℕ} {B = ‵ `ℕ} ($ (κℕ Nat.zero))


bool-allocation-step :
    ((Λ ($ (κ𝔹 false))) ⦂∀ (‵ `𝔹) [ ‵ `𝔹 ])
      —→[ bind (‵ `𝔹) ]
    ($ (κ𝔹 false))
      ↑ 〖 Fin.zero , ⇑ᵗ (‵ `𝔹) ↑ (‵ `𝔹) 〗
bool-allocation-step =
  β-Λ {Nat.zero} {A = ‵ `𝔹} {B = ‵ `𝔹} ($ (κ𝔹 false))


empty-right-nat-fresh-impossible :
  RightBindFreshᶜ emptyᶜ (‵ `ℕ) → ⊥
empty-right-nat-fresh-impossible (inj₁ ())
empty-right-nat-fresh-impossible (inj₂ (Yᴿ , () , separated))


empty-right-nat-request-impossible :
  WorldEvolutionRequest emptyᶜ keep (bind (‵ `ℕ)) → ⊥
empty-right-nat-request-impossible request =
  empty-right-nat-fresh-impossible (right-request-fresh request)


empty-nat-bool-imprecision-impossible :
  (‵ `ℕ) ⊑ᵀ⟨ emptyᶜ ⟩ (‵ `𝔹) → ⊥
empty-nat-bool-imprecision-impossible ()


empty-nat-bool-request-impossible :
  WorldEvolutionRequest emptyᶜ (bind (‵ `ℕ)) (bind (‵ `𝔹)) → ⊥
empty-nat-bool-request-impossible request =
  empty-nat-bool-imprecision-impossible (paired-request-direct request)


-- `nat-allocation-step` and `bool-allocation-step` are trusted operational
-- allocations, yet the right-only natural allocation has no direct freshness
-- certificate at `emptyᶜ`, and the paired natural/Boolean allocations have no
-- direct type-imprecision certificate.  Thus raw reduction outcomes cannot
-- produce WorldEvolutionRequest.  The smallest sound producer boundary is the
-- four checked functions above: reduction indices plus exactly the direct
-- evidence already required by the canonical request constructors.

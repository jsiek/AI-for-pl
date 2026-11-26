module proof.LR.VarStarProbe where

-- File Charter:
--   * A counterexample to the proposed `VarI` field "if `δl δ Z ≡ ★`
--     then Z's leaf and `★⊑★` relate the same values, at every stage"
--     (notes/logrel-dgg.md, Section 7, "The ★ field of VarI").
--   * The interpretation is case 6's induction hypothesis δ₃ (module
--     `Case6`): one left-only variable X, of mode `X∼X` (the left's
--     `∀ᶜ`), mapped to the goal clause's descriptor
--     `sdesc [] [] (desc ★⊑★ [] [])`, which is `OnlyS`, with bound
--     `suc s` for s = 0.  So `δl X ≡ ★`.
--   * At stage 1, `★⊑★` relates `$1 ⟨ℕ!⟩` to itself (`star1`), while
--     X's leaf, defined only below its bound, relates nothing
--     (`leaf1`).  `VarI` quantifies over every stage, so the field
--     cannot be discharged there.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Nat using (_≤′_; ≤′-refl)
open import Data.Product using (_,_)
open import Data.Vec using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty)
open import Consistency
open import CastTerms using (Term; $; _⟨_⟩)
open import Primitives using (κℕ)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation

-- the empty world
w₀ : World
w₀ = mkWorld 0 0 (λ ()) 0 pid store-empty

-- the goal clause's descriptor: a core at `★⊑★`, no seals
starD : SDesc 0 0
starD = sdesc [] [] (desc (★⊑★ {Φ = []}) []ᵛ []ᵛ)

starD-ok : OnlyS starD
starD-ok = (λ ()) , refl

-- case 6's δ₃ at s = 0: X left-only, leaf bounded by 1
δX : Interp 1 0 0 0
δX = extOnlyI (leftTyS starD) (sem (onlyLeafS ≺ (≤′-refl {1}) starD))
  closedI

δX-★ : δl δX zero ≡ ★
δX-★ = refl

-- `$1 ⟨ ℕ! ⟩`, on either side
one! : ∀ {Δ} {μ : Env∼ Δ} → Term Δ
one! {μ = μ} = $ (κℕ 1) ⟨ _! {μ = μ} ⦃ ‵ `ℕ ⦄ (id (‵ `ℕ)) ⟩

star1 : 𝒱 ≺ 1 (★⊑★ {Φ = only []}) w₀ δX (one! {μ = []ᵛ}) (one! {μ = []ᵛ})
star1 = refl , refl

leaf1 : leafRel ≺ 1 w₀ (leaf δX zero) (one! {μ = []ᵛ}) (one! {μ = []ᵛ})
  → ⊥
leaf1 ()

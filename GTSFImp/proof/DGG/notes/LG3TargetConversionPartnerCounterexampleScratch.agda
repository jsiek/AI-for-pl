module LG3TargetConversionPartnerCounterexampleScratch where

-- File Charter:
--   * Notes-only LG-3ag counterexample scratch for target conversion
--     keep-discharge partner transport.
--   * Exhibits a wrapper partner witness for `M′ ↑ id↑ A` whose reduct `M′`
--     has no `SourceConcealPartnerOK` seal branch.
--   * Does not edit the live CTI relation, proof surfaces, or reduction rules.

open import Data.Empty using (⊥)
import Data.Fin as Fin

open import Types using (Ty; TyVar; ★; ‵_; `ℕ)
open import Consistency using (idᶜ; _⊢_∼_; id; _!)
open import Conversion using (seal; id↑)
open import CastTerms using (Term; Value; $; _⟨_⟩; _↑_; _《_》; inj)
open import Primitives using (κℕ)
open import Reduction using (keep; pure-step; id-reveal; _—→[_]_)

import proof.DGG.CtxImp as CTI2
open CTI2 using (World)


X : TyVar 1
X = Fin.zero

ℕᴸ : Ty 1
ℕᴸ = ‵ `ℕ

ℕᴿ : Ty 0
ℕᴿ = ‵ `ℕ

target-tag : idᶜ ⊢ ℕᴿ ∼ ★
target-tag = id (‵ `ℕ) !

target-inert : Term 0
target-inert = $ (κℕ 0) ⟨ target-tag ⟩

target-inert-value : Value target-inert
target-inert-value = $ (κℕ 0) 《 inj 》

target-wrapper : Term 0
target-wrapper = target-inert ↑ id↑ ★

target-wrapper-keep : target-wrapper —→[ keep ] target-inert
target-wrapper-keep = pure-step (id-reveal target-inert-value)

wrapper-source-partner : ∀ {Δ} {W : World 1 0 Δ}
    {P : Term 1} {Xᴿ?}
  → CTI2.SourceConcealPartnerOK W P (seal X ℕᴸ) Xᴿ? target-wrapper
wrapper-source-partner =
  CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↑)

reduct-seal-partner-impossible : ∀ {Δ} {W : World 1 0 Δ}
    {P : Term 1} {Xᴿ?}
  → CTI2.SealPartnerOK W X P ℕᴸ Xᴿ? target-inert
  → ⊥
reduct-seal-partner-impossible (CTI2.plain-target ())

reduct-source-partner-impossible : ∀ {Δ} {W : World 1 0 Δ}
    {P : Term 1} {Xᴿ?}
  → CTI2.SourceConcealPartnerOK W P (seal X ℕᴸ) Xᴿ? target-inert
  → ⊥
reduct-source-partner-impossible (CTI2.seal-partner-ok ok) =
  reduct-seal-partner-impossible ok

conversion-keep-source-partner-false : ∀ {Δ} {W : World 1 0 Δ}
    {P : Term 1} {Xᴿ?}
  → (CTI2.SourceConcealPartnerOK W P (seal X ℕᴸ) Xᴿ? target-wrapper
      → CTI2.SourceConcealPartnerOK W P (seal X ℕᴸ) Xᴿ? target-inert)
  → ⊥
conversion-keep-source-partner-false transport =
  reduct-source-partner-impossible (transport wrapper-source-partner)

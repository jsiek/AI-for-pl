module M6ProvenancePreflightScratch where

-- File Charter:
--   * Pre-flight for the provenance-carrying M6 driver statement
--     (notes/M6-PROVENANCE-DESIGN.md, candidate A).
--   * Defines the term-independent provenance fragment CatchupCast⁻,
--     column provenance CatchupColumn (head-full, tail-term-independent),
--     and the driver surface ValueCatchupRightProv².
--   * States (does not prove) the three support surfaces the driver
--     recursion needs: fragment embedding, fragment transport along
--     WorldExtendᴿ, and fragment stability under store-change mapping.
--   * Calibrates: the catalog inst-then-function column carries a
--     CatchupColumn; the projection-mismatch package is excluded at the
--     head by the existing (checked) provenance emptiness, and in tails
--     by construction (the fragment has no projection constructor).

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; _!; ？_; inst_; instᵐ;
   bot-elim; bot-intro)
import Consistency as C
open import CastTerms using (Term; Value; Inert; fun; _⟨_⟩)
open import Reduction using (StoreChanges; _—↠[_]_)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (CastColumn; []ᶜ; _▻ᶜ_; applyColumn; mapColumn; columnSize)
import proof.DGG.ReachabilityCatalog as RC
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open ECR using (CatchupCast; catchup-inert; catchup-id;
  catchup-ground-other; catchup-inst; catchup-bot-elim;
  catchup-bot-intro; WorldExtendᴿ; transport⊑ᵂ; mapCtxᴿ)

open import ProjectionMismatchStarRepScratch using
  (Y?; probe-p; probe-q; target-tagged;
   projection-mismatch-violates-provenance)

------------------------------------------------------------------------
-- The term-independent provenance fragment
------------------------------------------------------------------------

-- CatchupCast minus the projection family and minus the Term index.
-- Every constructor mirrors its CatchupCast counterpart; ground-other's
-- recursion stays inside the fragment.

data CatchupCast⁻ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} :
    ∀ {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → ν ⊢ B ∼ B′
    → A ⊑ᵂ⟨ W ⟩ B′
    → Set where

  catchup⁻-inert : ∀ {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {c′ : ν ⊢ B ∼ B′}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
    → Inert c′
    → CatchupCast⁻ p c′ q

  catchup⁻-id : ∀ {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B}
    → (a : Atom B)
    → CatchupCast⁻ p (id {μ = ν} a) q

  catchup⁻-ground-other : ∀ {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
      {Gᵍ : Ground G} {G∼★ : ν ⊢ G ∼★}
      {Bns : NonStar B}
      {c : ν ⊢ B ∼ G} {q : A ⊑ᵂ⟨ W ⟩ ★}
    → B ≢ G
    → (r : A ⊑ᵂ⟨ W ⟩ G)
    → CatchupCast⁻ {W = W} {A = A} p c r
    → CatchupCast⁻ p
        (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄)
        q

  catchup⁻-inst : ∀ {B₀ : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
      {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B₀}
      {c′ : C.instᵐ ν ⊢ B₀ ∼ ⇑ᵗ B′}
      ⦃ Bnv : NonVar B₀ ⦄ ⦃ zero∈B : Fin.zero ∈ᵗ B₀ ⦄
      {B′≢★ : B′ ≢ ★} {q : A ⊑ᵂ⟨ W ⟩ B′}
    → CatchupCast⁻ p ((inst c′) B′≢★) q

  catchup⁻-bot-elim : ∀ {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ (＇ Fin.zero)}
      {q : A ⊑ᵂ⟨ W ⟩ `∀ ★}
    → CatchupCast⁻ p (bot-elim {μ = ν}) q

  catchup⁻-bot-intro : ∀ {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ ★}
      {q : A ⊑ᵂ⟨ W ⟩ `∀ (＇ Fin.zero)}
    → CatchupCast⁻ p (bot-intro {μ = ν}) q

-- Embedding: the fragment never inspects the term, so it is provenance
-- for ANY target term.

catchup⁻-embed : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {c′ : ν ⊢ B ∼ B′}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (N : Term Δᴿ)
  → CatchupCast⁻ {W = W} {A = A} p c′ q
  → CatchupCast {W = W} {A = A} p N c′ q
catchup⁻-embed N (catchup⁻-inert i) = catchup-inert i
catchup⁻-embed N (catchup⁻-id a) = catchup-id a
catchup⁻-embed N (catchup⁻-ground-other B≢G r k) =
  catchup-ground-other B≢G r (catchup⁻-embed N k)
catchup⁻-embed N catchup⁻-inst = catchup-inst
catchup⁻-embed N catchup⁻-bot-elim = catchup-bot-elim
catchup⁻-embed N catchup⁻-bot-intro = catchup-bot-intro

------------------------------------------------------------------------
-- Column provenance: head-full, tail-term-independent
------------------------------------------------------------------------

data CatchupColumn⁻ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} :
    ∀ {B B′ : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → CastColumn B B′
    → A ⊑ᵂ⟨ W ⟩ B′
    → Set where
  ccol⁻-[] : ∀ {B : Ty Δᴿ} {q : A ⊑ᵂ⟨ W ⟩ B}
    → CatchupColumn⁻ q []ᶜ q
  ccol⁻-▻ : ∀ {B B₁ B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {q₀ : A ⊑ᵂ⟨ W ⟩ B} {q₁ : A ⊑ᵂ⟨ W ⟩ B₁}
      {q′ : A ⊑ᵂ⟨ W ⟩ B′}
      {c : ν ⊢ B ∼ B₁} {κ : CastColumn B₁ B′}
    → CatchupCast⁻ {W = W} {A = A} q₀ c q₁
    → CatchupColumn⁻ {W = W} {A = A} q₁ κ q′
    → CatchupColumn⁻ q₀ (c ▻ᶜ κ) q′

data CatchupColumn {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ}
    (M′ : Term Δᴿ) :
    ∀ {B B′ : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → CastColumn B B′
    → A ⊑ᵂ⟨ W ⟩ B′
    → Set where
  ccol-[] : ∀ {B : Ty Δᴿ} {q : A ⊑ᵂ⟨ W ⟩ B}
    → CatchupColumn M′ q []ᶜ q
  ccol-▻ : ∀ {B B₁ B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q₁ : A ⊑ᵂ⟨ W ⟩ B₁}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
      {c : ν ⊢ B ∼ B₁} {κ : CastColumn B₁ B′}
    → CatchupCast {W = W} {A = A} p M′ c q₁
    → CatchupColumn⁻ {W = W} {A = A} q₁ κ q
    → CatchupColumn M′ p (c ▻ᶜ κ) q

------------------------------------------------------------------------
-- Driver surface with provenance
------------------------------------------------------------------------

ValueCatchupRightProv² : Set
ValueCatchupRightProv² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (κ : CastColumn B B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → CatchupColumn {W = W} {A = A} M′ p κ q
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (applyColumn M′ κ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))

-- Support surfaces the driver recursion needs (statements only here;
-- proofs are Run-2 deliverables):
--   * fragment transport along a right world extension, cast side
--     mapped by the store changes.

CatchupColumn⁻TransportᵀStatement : Set
CatchupColumn⁻TransportᵀStatement =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′W}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′W}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q₀ : A ⊑ᵂ⟨ W ⟩ B} {q′ : A ⊑ᵂ⟨ W ⟩ B′}
    {κ : CastColumn B B′}
  → (ext : WorldExtendᴿ χs W W′)
  → CatchupColumn⁻ {W = W} {A = A} q₀ κ q′
  → CatchupColumn⁻ {W = W′} {A = A} (transport⊑ᵂ ext q₀)
      (mapColumn χs κ) (transport⊑ᵂ ext q′)

------------------------------------------------------------------------
-- Calibration
------------------------------------------------------------------------

-- 1. The catalog inst-then-function column carries provenance:
--    head catchup-inst, tail inert function cast.

catalog-column :
  CastColumn (RC.∀X⇒X {Δ = 0}) (RC.★⇒★ᵗ {Δ = 0})
catalog-column = RC.∀X⇒X∼★⇒★ ▻ᶜ RC.★⇒★∼★⇒★ ▻ᶜ []ᶜ

-- (the concrete p/q obligations and the target term are supplied at a
--  driver call site; here we only check the provenance layers exist at
--  SOME obligations, which is what the driver interface consumes)

catalog-column-provenance : ∀ {Δᴸ Δ} {W : World Δᴸ 0 Δ}
    {A : Ty Δᴸ} {M′ : Term 0}
    {p : A ⊑ᵂ⟨ W ⟩ RC.∀X⇒X}
    {q₁ : A ⊑ᵂ⟨ W ⟩ RC.★⇒★ᵗ}
    {q : A ⊑ᵂ⟨ W ⟩ RC.★⇒★ᵗ}
  → CatchupCast {W = W} {A = A} p M′ RC.∀X⇒X∼★⇒★ q₁
  → CatchupColumn M′ p catalog-column q
catalog-column-provenance head =
  ccol-▻ head
    (ccol⁻-▻ (catchup⁻-inert fun) ccol⁻-[])

-- 2. The projection-mismatch package is excluded:
--    at the head, CatchupCast is empty (checked in the probe scratch);
--    in tails, by construction — no projection constructor exists.

mismatch-head-excluded :
  CatchupColumn target-tagged probe-p (Y? ▻ᶜ []ᶜ) probe-q
  → ⊥
mismatch-head-excluded (ccol-▻ head ccol⁻-[]) =
  projection-mismatch-violates-provenance head

no-projection-tail : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q₀ : A ⊑ᵂ⟨ W ⟩ ★} {q′ : A ⊑ᵂ⟨ W ⟩ B′}
    {G : Ty Δᴿ} {Gᵍ : Ground G} {★∼G : ν ⊢★∼ G}
    {c : ν ⊢ G ∼ B′} {Bns : NonStar B′}
  → CatchupCast⁻ {W = W} {A = A} q₀ (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q′
  → ⊥
no-projection-tail (catchup⁻-inert ())

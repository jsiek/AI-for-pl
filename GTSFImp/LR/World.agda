module LR.World where

-- File Charter:
--   * Kripke worlds for the logical relation (notes/logrel-dgg.md,
--     Section 6.11): the sizes of the two stores, and for each left
--     store variable a tag descriptor (`LR.Desc`).  Tags are syntax, so
--     worlds need no staging and live in `Set`.
--   * The right side has a scope and a store (notes/logrel-dgg.md,
--     Section 7, "Design (W)").  Tags, descriptors and leaves live in
--     the scope; right terms and the interpretations' right types live
--     in the store, which is the scope's oldest variables (`Prefix`).
--     The scope's other variables are reserved: the right program
--     allocates them next (`Steps`), so a right run can be replayed
--     from an earlier store.  An ordinary world reserves nothing
--     (`world`).
--   * Extension `w′ ⊒ w` embeds the left store, the right scope and the
--     right store in order, compatibly with the store's place in the
--     scope, and keeps every old tag, renamed.  The right scope only
--     grows at its new end (`Grows`), as every run's does
--     (`Steps-grows`); a replay world needs this (notes/logrel-dgg.md,
--     Gap G1).
--   * Relations relative to a store: a relation at each stage, applied
--     at any world together with embeddings of the store into the
--     world's left store and right scope (`RelΩ`).  This is how a leaf
--     relation built in one world is read in a later one.

import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym;
  trans; cong)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term)
open import Reduction using (StoreChange; StoreChanges; keep; bind;
  []; _∷_)
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
open import proof.TypeInTermSubst using (toRename-id-eq)
open import LR.Desc
open import LR.Steps using (embedᶜ; embedᶜˢ)

------------------------------------------------------------------------
-- The right store inside the right scope
------------------------------------------------------------------------

-- the right store Θ as the oldest variables of the right scope Δ; each
-- `pres` reserves one more variable, newer than the others
data Prefix : TyCtx → TyCtx → Set where
  pid : ∀ {Θ} → Prefix Θ Θ
  pres : ∀ {Θ Δ} → Prefix Θ Δ → Prefix Θ (suc Δ)

-- the store's embedding in the scope
ιᴾ : ∀ {Θ Δ} → Prefix Θ Δ → Θ ↪ᵗ Δ
ιᴾ pid = id↪ᵗ
ιᴾ (pres p) = skip (ιᴾ p)

-- the store after allocating the oldest reserved variable
consumeᴾ : ∀ {Θ Δ} → Prefix Θ Δ → Prefix (suc Θ) (suc Δ)
consumeᴾ pid = pid
consumeᴾ (pres p) = pres (consumeᴾ p)

-- one change: an allocation takes the oldest reserved variable, or
-- extends the scope when none is reserved; the new prefix and the old
-- scope's embedding in the new one
data Step1 : ∀ {Θ Θ′ Δ Δ′} → Prefix Θ Δ → StoreChange Θ Θ′
    → Prefix Θ′ Δ′ → Δ ↪ᵗ Δ′ → Set where
  fresh : ∀ {Θ Θ′} {χ : StoreChange Θ Θ′} → Step1 pid χ pid (embedᶜ χ)
  stay : ∀ {Θ Δ} {p : Prefix Θ Δ} → Step1 (pres p) keep (pres p) id↪ᵗ
  take : ∀ {Θ Δ} {p : Prefix Θ Δ} {A}
    → Step1 (pres p) (bind A) (consumeᴾ p) id↪ᵗ

-- a run's changes, in order; the embedding is given up to equality, so
-- that runs compose without rewriting
data Steps : ∀ {Θ Θ′ Δ Δ′} → Prefix Θ Δ → StoreChanges Θ Θ′
    → Prefix Θ′ Δ′ → Δ ↪ᵗ Δ′ → Set where
  done : ∀ {Θ Δ} {p : Prefix Θ Δ} {ρ} → ρ ≡ id↪ᵗ → Steps p [] p ρ
  more : ∀ {Θ Θ₁ Θ′ Δ Δ₁ Δ′} {p : Prefix Θ Δ} {χ : StoreChange Θ Θ₁}
      {χs : StoreChanges Θ₁ Θ′} {p₁ : Prefix Θ₁ Δ₁} {p′ : Prefix Θ′ Δ′}
      {ρ₁ ρ₂ ρ}
    → Step1 p χ p₁ ρ₁ → Steps p₁ χs p′ ρ₂ → ρ ≡ ρ₂ ∘↪ ρ₁
    → Steps p (χ ∷ χs) p′ ρ

-- every run has its steps
step1 : ∀ {Θ Θ′ Δ} (p : Prefix Θ Δ) (χ : StoreChange Θ Θ′)
  → Σ[ Δ′ ∈ TyCtx ] Σ[ p′ ∈ Prefix Θ′ Δ′ ] Σ[ ρ ∈ Δ ↪ᵗ Δ′ ] Step1 p χ p′ ρ
step1 pid χ = _ , pid , embedᶜ χ , fresh
step1 (pres p) keep = _ , pres p , id↪ᵗ , stay
step1 (pres p) (bind A) = _ , consumeᴾ p , id↪ᵗ , take

steps : ∀ {Θ Θ′ Δ} (p : Prefix Θ Δ) (χs : StoreChanges Θ Θ′)
  → Σ[ Δ′ ∈ TyCtx ] Σ[ p′ ∈ Prefix Θ′ Δ′ ] Σ[ ρ ∈ Δ ↪ᵗ Δ′ ] Steps p χs p′ ρ
steps p [] = _ , p , id↪ᵗ , done refl
steps p (χ ∷ χs) with step1 p χ
steps p (χ ∷ χs) | Δ₁ , p₁ , ρ₁ , s₁ with steps p₁ χs
steps p (χ ∷ χs) | Δ₁ , p₁ , ρ₁ , s₁ | Δ′ , p′ , ρ₂ , ss =
  Δ′ , p′ , ρ₂ ∘↪ ρ₁ , more s₁ ss refl

-- the store embedding commutes with the scope embedding
Coh : ∀ {Θ Θ′ Δ Δ′} → Prefix Θ Δ → Prefix Θ′ Δ′
  → Θ ↪ᵗ Θ′ → Δ ↪ᵗ Δ′ → Set
Coh p p′ ρS ρR =
  ∀ X → toRenameᵗ ρR (toRenameᵗ (ιᴾ p) X)
        ≡ toRenameᵗ (ιᴾ p′) (toRenameᵗ ρS X)

ιᴾ-consume : ∀ {Θ Δ} (p : Prefix Θ Δ) (X : TyVar Θ)
  → toRenameᵗ (ιᴾ (consumeᴾ p)) (Fin.suc X) ≡ Fin.suc (toRenameᵗ (ιᴾ p) X)
ιᴾ-consume pid X = refl
ιᴾ-consume (pres p) X = cong Fin.suc (ιᴾ-consume p X)

coh-id : ∀ {Θ Δ} (p : Prefix Θ Δ) → Coh p p id↪ᵗ id↪ᵗ
coh-id p X =
  trans (toRename-id-eq _) (cong (toRenameᵗ (ιᴾ p)) (sym (toRename-id-eq X)))

coh-step : ∀ {Θ Θ′ Δ Δ′} {p : Prefix Θ Δ} {χ : StoreChange Θ Θ′}
    {p′ : Prefix Θ′ Δ′} {ρ} → Step1 p χ p′ ρ → Coh p p′ (embedᶜ χ) ρ
coh-step {χ = χ} fresh X =
  trans (cong (toRenameᵗ (embedᶜ χ)) (toRename-id-eq X))
    (sym (toRename-id-eq _))
coh-step {p = pres p} stay = coh-id (pres p)
coh-step {p = pres p} take X =
  trans (toRename-id-eq _)
    (trans (sym (ιᴾ-consume p X))
      (cong (λ Y → toRenameᵗ (ιᴾ (consumeᴾ p)) (Fin.suc Y))
        (sym (toRename-id-eq X))))

coh-∘ : ∀ {Θ₁ Θ₂ Θ₃ Δ₁ Δ₂ Δ₃}
  {p₁ : Prefix Θ₁ Δ₁} {p₂ : Prefix Θ₂ Δ₂} {p₃ : Prefix Θ₃ Δ₃}
  {σ₁ : Θ₁ ↪ᵗ Θ₂} {σ₂ : Θ₂ ↪ᵗ Θ₃} {ρ₁ : Δ₁ ↪ᵗ Δ₂} {ρ₂ : Δ₂ ↪ᵗ Δ₃}
  → Coh p₁ p₂ σ₁ ρ₁ → Coh p₂ p₃ σ₂ ρ₂ → Coh p₁ p₃ (σ₂ ∘↪ σ₁) (ρ₂ ∘↪ ρ₁)
coh-∘ {p₁ = p₁} {p₃ = p₃} {σ₁} {σ₂} {ρ₁} {ρ₂} c₁ c₂ X =
  trans (toRenameᵗ-∘ ρ₂ ρ₁ _)
    (trans (cong (toRenameᵗ ρ₂) (c₁ X))
      (trans (c₂ _) (cong (toRenameᵗ (ιᴾ p₃)) (sym (toRenameᵗ-∘ σ₂ σ₁ X)))))

coh-steps : ∀ {Θ Θ′ Δ Δ′} {p : Prefix Θ Δ} {χs : StoreChanges Θ Θ′}
    {p′ : Prefix Θ′ Δ′} {ρ} → Steps p χs p′ ρ → Coh p p′ (embedᶜˢ χs) ρ
coh-steps {p = p} (done refl) = coh-id p
coh-steps {p = p} {χs = χ ∷ χs} {p′ = p′} (more {p₁ = p₁} s₁ ss refl) =
  coh-∘ {p₁ = p} {p₂ = p₁} {p₃ = p′} (coh-step s₁) (coh-steps ss)

------------------------------------------------------------------------
-- Embeddings that grow at the new end
------------------------------------------------------------------------

infixr 5 _++ᴾ_

_++ᴾ_ : ∀ {Θ Δ Δ′} → Prefix Θ Δ → Prefix Δ Δ′ → Prefix Θ Δ′
p ++ᴾ pid = p
p ++ᴾ pres q = pres (p ++ᴾ q)

-- the scope only grows at its new end: the embedding is a prefix's
Grows : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Set
Grows {Δ} {Δ′} ρ = Σ[ q ∈ Prefix Δ Δ′ ] ρ ≡ ιᴾ q

∘↪-idˡ : ∀ {Δ Δ′} (η : Δ ↪ᵗ Δ′) → id↪ᵗ ∘↪ η ≡ η
∘↪-idˡ empty = refl
∘↪-idˡ (keep η) = cong keep (∘↪-idˡ η)
∘↪-idˡ (skip η) = cong skip (∘↪-idˡ η)

skip-∘ : ∀ {Δ₁ Δ₂ Δ₃} (π : Δ₂ ↪ᵗ Δ₃) (η : Δ₁ ↪ᵗ Δ₂)
  → skip π ∘↪ η ≡ skip (π ∘↪ η)
skip-∘ π empty = refl
skip-∘ π (keep η) = refl
skip-∘ π (skip η) = refl

ιᴾ-++ : ∀ {Θ Δ Δ′} (p : Prefix Θ Δ) (q : Prefix Δ Δ′)
  → ιᴾ (p ++ᴾ q) ≡ ιᴾ q ∘↪ ιᴾ p
ιᴾ-++ p pid = sym (∘↪-idˡ (ιᴾ p))
ιᴾ-++ p (pres q) =
  trans (cong skip (ιᴾ-++ p q)) (sym (skip-∘ (ιᴾ q) (ιᴾ p)))

Grows-id : ∀ {Δ} → Grows (id↪ᵗ {Δ})
Grows-id = pid , refl

Grows-∘ : ∀ {Δ₁ Δ₂ Δ₃} {π : Δ₂ ↪ᵗ Δ₃} {η : Δ₁ ↪ᵗ Δ₂}
  → Grows π → Grows η → Grows (π ∘↪ η)
Grows-∘ (q , refl) (q′ , refl) = q′ ++ᴾ q , sym (ιᴾ-++ q′ q)

-- a run's scope embedding grows
Step1-grows : ∀ {Θ Θ′ Δ Δ′} {p : Prefix Θ Δ} {χ : StoreChange Θ Θ′}
    {p′ : Prefix Θ′ Δ′} {ρ} → Step1 p χ p′ ρ → Grows ρ
Step1-grows (fresh {χ = keep}) = pid , refl
Step1-grows (fresh {χ = bind A}) = pres pid , refl
Step1-grows stay = pid , refl
Step1-grows take = pid , refl

Steps-grows : ∀ {Θ Θ′ Δ Δ′} {p : Prefix Θ Δ} {χs : StoreChanges Θ Θ′}
    {p′ : Prefix Θ′ Δ′} {ρ} → Steps p χs p′ ρ → Grows ρ
Steps-grows (done refl) = Grows-id
Steps-grows (more s ss refl) = Grows-∘ (Steps-grows ss) (Step1-grows s)

------------------------------------------------------------------------
-- Worlds
------------------------------------------------------------------------

record World : Set where
  constructor mkWorld
  field
    ΔL : TyCtx
    ΔR : TyCtx
    tag : TyVar ΔL → Tag ΔL ΔR
    storeR : TyCtx
    pre : Prefix storeR ΔR

open World public

-- an ordinary world: the right store is the whole scope
pattern world ΔL ΔR tag = mkWorld ΔL ΔR tag _ pid

-- the right store's embedding in the scope
ιʷ : (w : World) → storeR w ↪ᵗ ΔR w
ιʷ w = ιᴾ (pre w)

infix 4 _⊒_

-- w′ is a possible future of w
record _⊒_ (w′ w : World) : Set where
  constructor ext
  field
    ρL : ΔL w ↪ᵗ ΔL w′
    ρR : ΔR w ↪ᵗ ΔR w′
    ρS : storeR w ↪ᵗ storeR w′
    coh : Coh (pre w) (pre w′) ρS ρR
    grows : Grows ρR
    tags≡ : ∀ X → tag w′ (toRenameᵗ ρL X) ≡ renameTag ρL ρR (tag w X)

open _⊒_ public

------------------------------------------------------------------------
-- Relations relative to a store
------------------------------------------------------------------------

-- a relation at each stage, read at any world through embeddings of the
-- left store ΔL and the right scope ΔR into the world's; the right
-- terms are in the world's right store
RelΩ : TyCtx → TyCtx → Set₁
RelΩ ΔL₀ ΔR₀ = (k : ℕ) (w : World)
  → ΔL₀ ↪ᵗ ΔL w → ΔR₀ ↪ᵗ ΔR w
  → Term (ΔL w) → Term (storeR w) → Set

-- moving a relation to a larger store
transportΩ : ∀ {ΔL₀ ΔR₀ ΔL₁ ΔR₁}
  → ΔL₀ ↪ᵗ ΔL₁ → ΔR₀ ↪ᵗ ΔR₁ → RelΩ ΔL₀ ΔR₀ → RelΩ ΔL₁ ΔR₁
transportΩ σL σR R k w τL τR = R k w (τL ∘↪ σL) (τR ∘↪ σR)

-- the trivial relation
⊤Ω : ∀ {ΔL₀ ΔR₀} → RelΩ ΔL₀ ΔR₀
⊤Ω k w τL τR V V′ = ⊤

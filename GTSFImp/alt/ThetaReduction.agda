module alt.ThetaReduction where

-- File Charter:
--   * Defines values, results, term-variable substitution, and telescope-
--     indexed one-step reduction for the Θ-indexed alternative syntax.
--   * Regular-type renaming uses the repository's context injections.  At a
--     crossing it inserts or deletes the distinguished slot canonically;
--     weakening is the derived skip-at-position instance.  Term substitution
--     stops at closed crossing and ν interiors.
--   * Evaluation descends beneath ν.  A ν-headed result floats through every
--     demanded frame; siblings shift eagerly in the anchor context.
--   * The binder telescope is otherwise an inert step index: `float-reveal`
--     is the only rule that consults it, resolving an exiting representation
--     from an anchor lookup.
--   * Review suggestion (not undertaken here): `CanonicalInterior` already
--     projects to `Value`; a later cleanup should assess whether its overlap
--     with the delimiter cases of `RevealValue` and `ConcealValue` can shrink
--     the existing value-predicate family without changing canonical forms.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term Θ Δ → Term Θ Δ
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ A ˙ M) = ƛ A ˙ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ rename ρ M
rename ρ (L ⦂∀ C [ A ]) = rename ρ L ⦂∀ C [ A ]
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
-- These interiors are literally typed under `[]`, so they contain no outer
-- term variables and renaming leaves them unchanged.
rename ρ (M ↑[ Y ≔ α ] c) = M ↑[ Y ≔ α ] c
rename ρ (M ↓[ Y ≔ α ] c) = M ↓[ Y ≔ α ] c
rename ρ (ν[ A ] M) = ν[ A ] M
rename ρ blame = blame

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

-- Insert one matched source/target slot into an injection.  The new slot is
-- placed at Y in the source and at the corresponding canonical position in
-- the target.  Skipped target slots remain in their original order.

insert↪ᵗ : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′
  → TyVar (suc Δ)
  → suc Δ ↪ᵗ suc Δ′
insert↪ᵗ ρ zero = keep ρ
insert↪ᵗ (keep ρ) (suc Y) = keep (insert↪ᵗ ρ Y)
insert↪ᵗ (skip ρ) (suc Y) = skip (insert↪ᵗ ρ (suc Y))

-- Delete one source slot and its image.  This is the factor of an injection
-- used for the interior of a conceal node, whose conclusion binds that slot.

delete↪ᵗ : ∀ {Δ Δ′}
  → suc Δ ↪ᵗ suc Δ′
  → TyVar (suc Δ)
  → Δ ↪ᵗ Δ′
delete↪ᵗ (keep ρ) zero = ρ
delete↪ᵗ {Δ = suc Δ} {Δ′ = zero} (keep ()) (suc Y)
delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′} (keep ρ) (suc Y) =
  keep (delete↪ᵗ ρ Y)
delete↪ᵗ {Δ′ = zero} (skip ()) Y
delete↪ᵗ {Δ′ = suc Δ′} (skip ρ) Y = skip (delete↪ᵗ ρ Y)

renameᵗᵐ : Δ ↪ᵗ Δ′ → Term Θ Δ → Term Θ Δ′
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ A ˙ M) =
  ƛ renameᵗ (toRenameᵗ ρ) A ˙ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (keep ρ) M)
renameᵗᵐ ρ (L ⦂∀ C [ A ]) =
  renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
    [ renameᵗ (toRenameᵗ ρ) A ]
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) =
  renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ c ⟩) = renameᵗᵐ ρ M ⟨ renameᵐᶜ ρ c ⟩
renameᵗᵐ ρ (M ↑[ Y ≔ α ] c) =
  renameᵗᵐ (insert↪ᵗ ρ Y) M
    ↑[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ] c
renameᵗᵐ (keep ρ) (M ↓[ Y ≔ α ] c) =
  renameᵗᵐ (delete↪ᵗ (keep ρ) Y) M
    ↓[ toRenameᵗ (keep ρ) Y ≔ α ] c
renameᵗᵐ (skip ρ) (M ↓[ Y ≔ α ] c) =
  renameᵗᵐ (delete↪ᵗ (skip ρ) Y) M
    ↓[ toRenameᵗ (skip ρ) Y ≔ α ] c
renameᵗᵐ ρ (ν[ A ] M) =
  ν[ renameᵗ (toRenameᵗ ρ) A ] renameᵗᵐ ρ M
renameᵗᵐ ρ blame = blame

skipAt↪ᵗ : ∀ {Δ} → TyVar (suc Δ) → Δ ↪ᵗ suc Δ
skipAt↪ᵗ zero = skip id↪ᵗ
skipAt↪ᵗ {Δ = suc Δ} (suc X) = keep (skipAt↪ᵗ X)

weakenᵗᵐ : ∀ {Θ Δ} (X : TyVar (suc Δ))
  → Term Θ Δ
  → Term Θ (suc Δ)
weakenᵗᵐ X = renameᵗᵐ (skipAt↪ᵗ X)

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Subst : AnchorCtx → TyCtx → Set
Subst Θ Δ = Var → Term Θ Δ

exts : Subst Θ Δ → Subst Θ Δ
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

liftˢ : Subst Θ Δ → Subst Θ (suc Δ)
liftˢ σ x = weakenᵗᵐ zero (σ x)

subst : Subst Θ Δ → Term Θ Δ → Term Θ Δ
subst σ (` x) = σ x
subst σ (ƛ A ˙ M) = ƛ A ˙ subst (exts σ) M
subst σ (L · M) = subst σ L · subst σ M
subst σ (Λ M) = Λ (subst (liftˢ σ) M)
subst σ (L ⦂∀ C [ A ]) = subst σ L ⦂∀ C [ A ]
subst σ ($ κ) = $ κ
subst σ (L ⊕[ op ] M) = subst σ L ⊕[ op ] subst σ M
subst σ (M ⟨ c ⟩) = subst σ M ⟨ c ⟩
-- These interiors are literally typed under `[]`, so they contain no outer
-- term variables and substitution leaves them unchanged.
subst σ (M ↑[ Y ≔ α ] c) = M ↑[ Y ≔ α ] c
subst σ (M ↓[ Y ≔ α ] c) = M ↓[ Y ≔ α ] c
subst σ (ν[ A ] M) = ν[ A ] M
subst σ blame = blame

singleSub : Term Θ Δ → Subst Θ Δ
singleSub N zero = N
singleSub N (suc x) = ` x

infixl 8 _[_]
_[_] : Term Θ Δ → Term Θ Δ → Term Θ Δ
M [ N ] = subst (singleSub N) M

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GenSafe : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  safe-⇒ : ∀ {Δ μ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
      ---------------------------------------------
    → GenSafe (c ↦ d)

  safe-∀ : ∀ {Δ μ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
      ----------------------
    → GenSafe (∀ᶜ c)

  safe-inst : ∀ {Δ μ} {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → (B≢★ : B ≢ ★)
      ---------------------------
    → GenSafe ((inst c) B≢★)

  safe-gen : ∀ {Δ μ} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
      --------------------------
    → GenSafe ((gen c) A≢★)

data Inert : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  inj : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
      --------------------------------------
    → Inert {μ = μ} ((idᵍ {μ = μ} Gᵍ) !)

  fun : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
      ---------------------------------------------
    → Inert (c ↦ d)

  all : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
      ----------------------
    → Inert (∀ᶜ c)

  genᵥ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------
    → Inert ((gen c) A≢★)

mutual
  data RevealValue {Θ : AnchorCtx} {Δ : TyCtx}
      (V : Term Θ Δ) : Reveal → Set where
    fun : ∀ {c d}
      ------------------------
      → RevealValue V (c ↦↑ d)

    all : ∀ {c}
      -----------------------
      → RevealValue V (`∀↑ c)

    delimiter :
      CanonicalInterior V
      ------------------------
      → RevealValue V id↑

  data ConcealValue {Θ : AnchorCtx} {Δ : TyCtx}
      (V : Term Θ Δ) : Conceal → Set where
    sealᵥ :
      -------------------------------
      ConcealValue V seal

    fun : ∀ {c d}
      -------------------------
      → ConcealValue V (c ↦↓ d)

    all : ∀ {c}
      ------------------------
      → ConcealValue V (`∀↓ c)

    delimiter :
      CanonicalInterior V
      -------------------------
      → ConcealValue V id↓

  data Value : ∀ {Θ : AnchorCtx} {Δ : TyCtx} → Term Θ Δ → Set where
    ƛ_˙_ : ∀ {Θ Δ} (A : Ty Δ) (N : Term Θ Δ)
      ------------------------------------------
      → Value (ƛ A ˙ N)

    Λ_ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      → Value V
      ----------------
      → Value (Λ V)

    $ : ∀ {Θ Δ} (κ : Const)
      ---------------------------
      → Value {Θ = Θ} {Δ = Δ} ($ κ)

    _《_》 : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
        {c : μ ⊢ A ∼ B}
      → Value V
      → Inert c
        ----------------
      → Value (V ⟨ c ⟩)

    _↑[_≔_]_ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
      → {c : Reveal}
      → RevealValue V c
        --------------------------
      → Value (V ↑[ X ≔ α ] c)

    _↓[_≔_]_ : ∀ {Θ Δ} {V : Term Θ Δ}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
      → {c : Conceal}
      → ConcealValue V c
        --------------------------
      → Value (V ↓[ X ≔ α ] c)

  data CanonicalInterior : ∀ {Θ : AnchorCtx} {Δ : TyCtx}
      → Term Θ Δ → Set where
    tagged : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
        ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
        ⦃ Gns : NonStar G ⦄
      → Value V
        ------------------------------------------
      → CanonicalInterior (V ⟨ (idᵍ Gᵍ) ! ⟩)

    sealed : ∀ {Θ Δ} {V : Term Θ Δ}
      → Value V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
        --------------------------------------------------------
      → CanonicalInterior (V ↓[ X ≔ α ] seal)

    delimited : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      → CanonicalInterior V
      → (X : TyVar (suc Δ))
      → (α : TyVar Θ)
        ---------------------------------------------
      → CanonicalInterior (V ↑[ X ≔ α ] id↑)

canonical-value : ∀ {Θ Δ} {V : Term Θ Δ}
  → CanonicalInterior V
  → Value V
canonical-value (tagged Vᵥ) = Vᵥ 《 inj 》
canonical-value (sealed Vᵥ X α) = Vᵥ ↓[ X ≔ α ] sealᵥ
canonical-value (delimited Vᶜ X α) =
  canonical-value Vᶜ ↑[ X ≔ α ] delimiter Vᶜ

------------------------------------------------------------------------
-- Results
------------------------------------------------------------------------

data Result : ∀ {Θ Δ} → Term Θ Δ → Set where
  result-val : ∀ {Θ Δ} {V : Term Θ Δ}
    → Value V
      -------------
    → Result V

  result-ν : ∀ {Θ Δ} {A : Ty Δ} {M : Term (suc Θ) Δ}
    → Result M
      -----------------
    → Result (ν[ A ] M)

------------------------------------------------------------------------
-- Resolving a regular-type slot
------------------------------------------------------------------------

-- Live `_[_]ᵗ` removes only slot zero, so resolving an arbitrary Y needs this
-- substitution environment.  It removes Y and sends it to C; viewed before
-- exit, C is `wkᵗ Y C` in the region context.

private
  removeResolved : ∀ {n} (Y X : Fin (suc n)) → Y ≢ X → Fin n
  removeResolved zero zero Y≢X = ⊥-elim (Y≢X refl)
  removeResolved zero (suc X) Y≢X = X
  removeResolved {n = suc n} (suc Y) zero Y≢X = zero
  removeResolved {n = suc n} (suc Y) (suc X) Y≢X =
    suc (removeResolved Y X (λ Y≡X → Y≢X (cong suc Y≡X)))

  resolveSubᵗ : ∀ {Δ} → TyVar (suc Δ) → Ty Δ → suc Δ ⇒ˢ Δ
  resolveSubᵗ Y C X with Y ≟ X
  resolveSubᵗ Y C .Y | yes refl = C
  resolveSubᵗ Y C X | no Y≢X = ＇ removeResolved Y X Y≢X

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _⊢_—→_

data _⊢_—→_ : ∀ {Θ Δ}
  → TyEnv Θ Δ → Term Θ Δ → Term Θ Δ → Set where
  δ-⊕ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {op κ₁ κ₂ κ₃}
    → δ op κ₁ κ₂ κ₃
      -----------------------------------------
    → Ψ ⊢ ($ κ₁ ⊕[ op ] $ κ₂) —→ ($ κ₃)

  β : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V N : Term Θ Δ} {A : Ty Δ}
    → Value V
      -----------------------------
    → Ψ ⊢ (ƛ A ˙ N) · V —→ N [ V ]

  β-id : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A : Ty Δ} {a : Atom A}
    → Value V
      ---------------------------------
    → Ψ ⊢ V ⟨ id {μ = μ} a ⟩ —→ V

  β-⇒ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V W : Term Θ Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
    → Value W
      ------------------------------------------------
    → Ψ ⊢ (V ⟨ c ↦ d ⟩) · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩

  β-∀ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {C : Ty Δ}
      {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
      -------------------------------------------------------
    → Ψ ⊢ (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] —→
        (V ⦂∀ A [ C ]) ⟨ d ⟩

  ground : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → A ≢ G
      -------------------------------------------------
    → Ψ ⊢ V ⟨ c ! ⟩ —→ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩

  expand : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → G ≢ B
      -------------------------------------------------
    → Ψ ⊢ V ⟨ ？ c ⟩ —→ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩

  tag-untag : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ ν : Env∼ Δ}
      {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      -------------------------------------------------------
    → Ψ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V

  tag-untag-bad : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ ν : Env∼ Δ}
      {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : ν ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → G ≢ H
      ------------------------------------------------------------
    → Ψ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩ —→ blame

  blame-bot-intro : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
    → Value V
      ------------------------------------------
    → Ψ ⊢ V ⟨ bot-intro {μ = μ} ⟩ —→ blame

  β-reveal-⇒ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ (suc Δ)} {W : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal} {d : Reveal}
    → Value V
    → Value W
      ------------------------------------------------------------
    → Ψ ⊢ (V ↑[ X ≔ α ] (c ↦↑ d)) · W —→
        (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d

  β-conceal-⇒ : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {V : Term Θ Δ} {W : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal} {d : Conceal}
    → Value V
    → Value W
      ------------------------------------------------------------
    → Ψ ⊢ (V ↓[ X ≔ α ] (c ↦↓ d)) · W —→
        (V · (W ↑[ X ≔ α ] c)) ↓[ X ≔ α ] d

  id-cancel : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → CanonicalInterior V
      -----------------------------------------------------
    → Ψ ⊢ (V ↓[ X ≔ α ] id↓) ↑[ Y ≔ β ] id↑ —→ V

  id-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → Ψ ⊢ ($ κ) ↑[ X ≔ α ] id↑ —→ $ κ

  id-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → Ψ ⊢ ($ κ) ↓[ X ≔ α ] id↓ —→ $ κ

  conceal-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ (V ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal —→ V

  blame-·₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {M : Term Θ Δ}
      ------------------------
    → Ψ ⊢ blame · M —→ blame

  blame-·₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V : Term Θ Δ}
    → Value V
      ------------------------
    → Ψ ⊢ V · blame —→ blame

  blame-• : ∀ {Θ : AnchorCtx} {Δ : TyCtx} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
      ----------------------------------
    → Ψ ⊢ blame ⦂∀ B [ A ] —→ blame

  blame-⟨⟩ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {μ : Env∼ Δ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
      ------------------------
    → Ψ ⊢ blame ⟨ c ⟩ —→ blame

  blame-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
      --------------------------------------
    → Ψ ⊢ blame ↑[ X ≔ α ] c —→ blame

  blame-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
      --------------------------------------
    → Ψ ⊢ blame ↓[ X ≔ α ] c —→ blame

  blame-⊕₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {M : Term Θ Δ} {op : Prim}
      --------------------------------
    → Ψ ⊢ blame ⊕[ op ] M —→ blame

  blame-⊕₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {op : Prim}
    → Value V
      --------------------------------
    → Ψ ⊢ V ⊕[ op ] blame —→ blame

  blame-ν : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ}
      -------------------------
    → Ψ ⊢ ν[ A ] blame —→ blame

  const-ν : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {κ : Const}
      ----------------------------
    → Ψ ⊢ ν[ A ] ($ κ) —→ ($ κ)

  β-Λ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ (suc Δ)} {B : Ty (suc Δ)} {C : Ty Δ}
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ (Λ V) ⦂∀ B [ C ] —→
        ν[ C ] (shiftᶿ V ↑[ zero ≔ zero ] 〖 zero , ⇑ᵗ C ↑ B 〗)

  -- The consistency evidence mentions only the regular context.  `shiftᶿ`
  -- changes only the anchor count, so the inner cast reuses `c` unchanged.
  β-gen : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V : Term Θ Δ} {μ : Env∼ Δ} {A C : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------------------------------------------
    → Ψ ⊢ (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→
        ν[ C ] (((shiftᶿ V ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
          ↑[ zero ≔ zero ] 〖 zero , ⇑ᵗ C ↑ B 〗)

  -- DEFERRED: β-inst, β-reveal-∀, and β-conceal-∀ remain absent pending
  -- user sign-off on their Exchange-validated statements.

  ξ-·₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {L L′ M : Term Θ Δ}
    → Ψ ⊢ L —→ L′
      --------------------
    → Ψ ⊢ L · M —→ L′ · M

  ξ-·₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {V M M′ : Term Θ Δ}
    → Value V
    → Ψ ⊢ M —→ M′
      --------------------
    → Ψ ⊢ V · M —→ V · M′

  ξ-• : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {M M′ : Term Θ Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → Ψ ⊢ M —→ M′
      ------------------------------------
    → Ψ ⊢ M ⦂∀ B [ A ] —→ M′ ⦂∀ B [ A ]

  ξ-⟨⟩ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {M M′ : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → Ψ ⊢ M —→ M′
      ---------------------------
    → Ψ ⊢ M ⟨ c ⟩ —→ M′ ⟨ c ⟩

  ξ-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {M M′ : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Ψ ,typ[ X ] ⊢ M —→ M′
      ------------------------------------------
    → Ψ ⊢ M ↑[ X ≔ α ] c —→ M′ ↑[ X ≔ α ] c

  ξ-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {M M′ : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Ψ ⊢ M —→ M′
      ------------------------------------------
    → Ψ ,typ[ X ] ⊢ M ↓[ X ≔ α ] c —→ M′ ↓[ X ≔ α ] c

  ξ-⊕₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {L L′ M : Term Θ Δ} {op : Prim}
    → Ψ ⊢ L —→ L′
      --------------------------------
    → Ψ ⊢ L ⊕[ op ] M —→ L′ ⊕[ op ] M

  ξ-⊕₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {V M M′ : Term Θ Δ} {op : Prim}
    → Value V
    → Ψ ⊢ M —→ M′
      --------------------------------
    → Ψ ⊢ V ⊕[ op ] M —→ V ⊕[ op ] M′

  ξ-ν : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {M M′ : Term (suc Θ) Δ}
    → Ψ ,:= A ⊢ M —→ M′
      -------------------------------
    → Ψ ⊢ ν[ A ] M —→ ν[ A ] M′

  -- ν is the region binder, not an eliminator frame.  Nested ν-headed
  -- results are represented directly by `result-ν`, so there is no float-ν.
  float-·₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ}
    → Result (ν[ A ] M)
      --------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) · N —→ ν[ A ] (M · shiftᶿ N)

  float-·₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ}
    → Value V
    → Result (ν[ A ] M)
      --------------------------------------------------
    → Ψ ⊢ V · (ν[ A ] M) —→ ν[ A ] (shiftᶿ V · M)

  float-• : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {M : Term (suc Θ) Δ}
    → Result (ν[ A ] M)
      ------------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ⦂∀ B [ C ] —→ ν[ A ] (M ⦂∀ B [ C ])

  float-⟨⟩ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A B C : Ty Δ} {M : Term (suc Θ) Δ} {μ : Env∼ Δ}
      {c : μ ⊢ B ∼ C}
    → Result (ν[ A ] M)
      --------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ⟨ c ⟩ —→ ν[ A ] (M ⟨ c ⟩)

  float-reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty (suc Δ)} {M : Term (suc Θ) (suc Δ)}
      {Y : TyVar (suc Δ)} {α : TyVar Θ} {C : Ty Δ} {c : Reveal}
    → Ψ ∋ α := C
    → Result (ν[ A ] M)
      ------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ↑[ Y ≔ α ] c —→
        ν[ substᵗ (resolveSubᵗ Y C) A ] (M ↑[ Y ≔ suc α ] c)

  -- Conceal binds Y on its conclusion side.  Floating ν outward therefore
  -- weakens its representation at Y; unlike reveal, no slot is resolved and
  -- no telescope lookup is needed.  The node's anchor shifts beneath ν.
  float-conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {M : Term (suc Θ) Δ}
      {Y : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Result (ν[ A ] M)
      ------------------------------------------------------------
    → Ψ ,typ[ Y ] ⊢ (ν[ A ] M) ↓[ Y ≔ α ] c —→
        ν[ wkᵗ Y A ] (M ↓[ Y ≔ suc α ] c)

  float-⊕₁ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ} {op : Prim}
    → Result (ν[ A ] M)
      ------------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ⊕[ op ] N —→ ν[ A ] (M ⊕[ op ] shiftᶿ N)

  float-⊕₂ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ} {op : Prim}
    → Value V
    → Result (ν[ A ] M)
      ------------------------------------------------------------------
    → Ψ ⊢ V ⊕[ op ] (ν[ A ] M) —→ ν[ A ] (shiftᶿ V ⊕[ op ] M)

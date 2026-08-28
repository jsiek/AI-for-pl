module alt.ThetaReduction where

-- File Charter:
--   * Defines term-variable substitution and telescope-indexed one-step
--     reduction for the Θ-indexed alternative syntax.
--   * Regular-type renaming uses the repository's context injections.  At a
--     crossing it inserts or deletes the distinguished type variable canonically;
--     weakening is the derived skip-at-position instance.  Term substitution
--     stops at closed crossing and ν interiors.
--   * Evaluation descends beneath ν.  A ν-headed result floats through term
--     frames and through reveal when its entry strengthens across the crossing.
--   * Identity cancellation is strict in both node fields.  A mismatched
--     identity conceal/reveal pair is an inert adapter value, with pair
--     disequality evidence kept in `RevealValue`.
--   * Boundary rules accept ν-prefixed results as interiors and carry the
--     entire prefix verbatim.  Stacked regions move only by iterating the
--     ordinary two-constructor term-frame rules.
--   * Universal crossings use ScTyWrap: they move beneath Λ without
--     instantiating, allocating, or inspecting the telescope.
--   * Review suggestion (not undertaken here): `CanonicalInterior` already
--     projects to `Value`; a later cleanup should assess whether its overlap
--     with the delimiter cases of `RevealValue` and `ConcealValue` can shrink
--     the existing value-predicate family without changing canonical forms.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; yes; no)

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

-- `insert↪ᵗ` and `delete↪ᵗ` are exported by ThetaTyping because balanced
-- telescope extension and term renaming share exactly this type variable bookkeeping.

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
-- One-step reduction
------------------------------------------------------------------------

infix 2 _⊢_—→_

data _⊢_—→_ : ∀ {Θ Δ σ}
  → TyEnv Θ Δ σ → Term Θ Δ → Term Θ Δ → Set where
  δ-⊕ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {op κ₁ κ₂ κ₃}
    → δ op κ₁ κ₂ κ₃
      -----------------------------------------
    → Ψ ⊢ ($ κ₁ ⊕[ op ] $ κ₂) —→ ($ κ₃)

  β : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V N : Term Θ Δ} {A : Ty Δ}
    → Value V
      -----------------------------
    → Ψ ⊢ (ƛ A ˙ N) · V —→ N [ V ]

  β-id : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A : Ty Δ} {a : Atom A}
    → Value V
      ---------------------------------
    → Ψ ⊢ V ⟨ id {μ = μ} a ⟩ —→ V

  β-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V W : Term Θ Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
    → Value W
      ------------------------------------------------
    → Ψ ⊢ (V ⟨ c ↦ d ⟩) · W —→ (V · (W ⟨ c ⟩)) ⟨ d ⟩

  β-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {C : Ty Δ}
      {c : extᵐ μ ⊢ A ∼ B} {d : μ ⊢ A [ C ]ᵗ ∼ B [ C ]ᵗ}
    → Value V
    → d ≡ c [ C ]ᶜ
      -------------------------------------------------------
    → Ψ ⊢ (V ⟨ ∀ᶜ c ⟩) ⦂∀ B [ C ] —→
        (V ⦂∀ A [ C ]) ⟨ d ⟩

  ground : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      {c : μ ⊢ A ∼ G} ⦃ Ans : NonStar A ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → A ≢ G
      -------------------------------------------------
    → Ψ ⊢ V ⟨ c ! ⟩ —→ V ⟨ c ⟩ ⟨ (idᵍ Gᵍ) ! ⟩

  expand : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {G B : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      {c : μ ⊢ G ∼ B} ⦃ Bns : NonStar B ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → G ≢ B
      -------------------------------------------------
    → Ψ ⊢ V ⟨ ？ c ⟩ —→ V ⟨ ？ (idᵍ Gᵍ) ⟩ ⟨ c ⟩

  tag-untag : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ ν : Env∼ Δ}
      {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      -------------------------------------------------------
    → Ψ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Gᵍ) ⟩ —→ V

  tag-untag-bad : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ ν : Env∼ Δ}
      {G H : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ Hᵍ : Ground H ⦄
      ⦃ G∼★ : μ ⊢ G ∼★ ⦄ ⦃ ★∼H : ν ⊢★∼ H ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ Hns : NonStar H ⦄
    → Value V
    → G ≢ H
      ------------------------------------------------------------
    → Ψ ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⟨ ？ (idᵍ Hᵍ) ⟩ —→ blame

  blame-bot-intro : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
    → Value V
      ------------------------------------------
    → Ψ ⊢ V ⟨ bot-intro {μ = μ} ⟩ —→ blame

  β-reveal-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {W : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal} {d : Reveal}
    → Result V
    → Value W
      ------------------------------------------------------------
    → Ψ ⊢ (V ↑[ X ≔ α ] (c ↦↑ d)) · W —→
        (V · (W ↓[ X ≔ α ] c)) ↑[ X ≔ α ] d

  β-conceal-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ Δ} {W : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal} {d : Conceal}
    → Result V
    → Value W
      ------------------------------------------------------------
    → Ψ ⊢ (V ↓[ X ≔ α ] (c ↦↓ d)) · W —→
        (V · (W ↑[ X ≔ α ] c)) ↓[ X ≔ α ] d

  id-cancel : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {R : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Result R
      ----------------------------------------------------
    → Ψ ⊢ (R ↓[ X ≔ α ] id↓) ↑[ X ≔ α ] id↑ —→ R

  id-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → Ψ ⊢ ($ κ) ↑[ X ≔ α ] id↑ —→ $ κ

  id-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {κ}
      ---------------------------------------------
    → Ψ ⊢ ($ κ) ↓[ X ≔ α ] id↓ —→ $ κ

  conceal-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {R : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Result R
      ------------------------------------------------------------
    → Ψ ⊢ (R ↓[ X ≔ α ] seal) ↑[ Y ≔ β ] unseal —→ R

  blame-·₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M : Term Θ Δ}
      ------------------------
    → Ψ ⊢ blame · M —→ blame

  blame-·₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
    → Value V
      ------------------------
    → Ψ ⊢ V · blame —→ blame

  blame-• : ∀ {Θ : AnchorCtx} {Δ : TyCtx}
      {σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {B : Ty (suc Δ)}
      ----------------------------------
    → Ψ ⊢ blame ⦂∀ B [ A ] —→ blame

  blame-⟨⟩ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {μ : Env∼ Δ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
      ------------------------
    → Ψ ⊢ blame ⟨ c ⟩ —→ blame

  blame-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
      --------------------------------------
    → Ψ ⊢ blame ↑[ X ≔ α ] c —→ blame

  blame-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
      --------------------------------------
    → Ψ ⊢ blame ↓[ X ≔ α ] c —→ blame

  blame-⊕₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ Δ} {op : Prim}
      --------------------------------
    → Ψ ⊢ blame ⊕[ op ] M —→ blame

  blame-⊕₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {op : Prim}
    → Value V
      --------------------------------
    → Ψ ⊢ V ⊕[ op ] blame —→ blame

  blame-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ}
      -------------------------
    → Ψ ⊢ ν[ A ] blame —→ blame

  β-Λ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {B : Ty (suc Δ)} {C : Ty Δ}
    → Value V
      ------------------------------------------------------------
    → Ψ ⊢ (Λ V) ⦂∀ B [ C ] —→
        ν[ C ] (shiftᶿ V ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)

  -- The consistency evidence mentions only the regular context.  `shiftᶿ`
  -- changes only the anchor count, so the inner cast reuses `c` unchanged.
  β-gen : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ} {A C : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------------------------------------------
    → Ψ ⊢ (V ⟨ (gen c) A≢★ ⟩) ⦂∀ B [ C ] —→
        ν[ C ] (((shiftᶿ V ↓[ zero ≔ zero ] δ↓ (⇑ᵗ A)) ⟨ c ⟩)
          ↑[ zero ≔ zero ] 〖 zero ↑ B 〗)

  -- β-inst instantiates the polymorphic value V at ★ and applies the
  -- closed consistency evidence.  Allocation and the seal/unseal
  -- mediation are deliberately not this rule's job: the contractum is an
  -- ordinary type application, and the downstream ⦂∀ rules (β-Λ, β-∀,
  -- β-gen, β-reveal-∀, β-conceal-∀) perform them for whichever canonical
  -- ∀-value V is.
  -- U35 producer audit: this is the only rule whose contractum introduces a
  -- type-application node absent from its redex, and its argument is ★.
  -- β-∀ copies its existing argument; ξ-• and float-• only propagate an
  -- existing node.  No reduction rule mints `⦂∀ _ [ ＇ X ]` at a live
  -- crossing.
  β-inst : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {μ : Env∼ Δ}
      {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → Value V
    → (B≢★ : B ≢ ★)
      ------------------------------------------------------------
    → Ψ ⊢ V ⟨ (inst c) B≢★ ⟩ —→ (V ⦂∀ A [ ★ ]) ⟨ c [ ★/0 ]ᶜ ⟩

  -- ScTyWrap pushes a crossing through Λ without opening the binder.
  -- The raw shape is already typed one binder deeper by the crossing rule,
  -- so it is carried verbatim and the pivot merely shifts by `suc`.
  β-reveal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc (suc Δ))}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Result V
      ------------------------------------------------------------
    → Ψ ⊢ ((Λ V) ↑[ X ≔ α ] `∀↑ c) —→
        Λ (V ↑[ suc X ≔ α ] c)

  β-conceal-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Result V
      ------------------------------------------------------------
    → Ψ ⊢ ((Λ V) ↓[ X ≔ α ] `∀↓ c) —→
        Λ (V ↓[ suc X ≔ α ] c)

  ξ-Λ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M M′ : Term Θ (suc Δ)}
    → Ψ ,typ ⊢ M —→ M′
      ----------------------
    → Ψ ⊢ Λ M —→ Λ M′

  ξ-·₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {L L′ M : Term Θ Δ}
    → Ψ ⊢ L —→ L′
      --------------------
    → Ψ ⊢ L · M —→ L′ · M

  ξ-·₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V M M′ : Term Θ Δ}
    → Value V
    → Ψ ⊢ M —→ M′
      --------------------
    → Ψ ⊢ V · M —→ V · M′

  ξ-• : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M M′ : Term Θ Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → Ψ ⊢ M —→ M′
      ------------------------------------
    → Ψ ⊢ M ⦂∀ B [ A ] —→ M′ ⦂∀ B [ A ]

  ξ-⟨⟩ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M M′ : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → Ψ ⊢ M —→ M′
      ---------------------------
    → Ψ ⊢ M ⟨ c ⟩ —→ M′ ⟨ c ⟩

  ξ-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M M′ : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
      {fresh : α ∉ᵛ σ}
    → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ⊢ M —→ M′
      ------------------------------------------
    → Ψ ⊢ M ↑[ X ≔ α ] c —→ M′ ↑[ X ≔ α ] c

  ξ-conceal : ∀ {Θ Δ σ} {Ψ′ : TyEnv Θ (suc Δ) σ}
      {M M′ : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Ψ′ ,end[ X ] ⊢ M —→ M′
      ------------------------------------------
    → Ψ′ ⊢ M ↓[ X ≔ α ] c —→ M′ ↓[ X ≔ α ] c

  float-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {A : Ty Δ} {M : Term (suc Θ) Δ}
      {Y : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Result (ν[ A ] M)
      ------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ↓[ Y ≔ α ] c —→
        ν[ wkᵗ Y A ] (M ↓[ Y ≔ suc α ] c)

  ξ-⊕₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {L L′ M : Term Θ Δ} {op : Prim}
    → Ψ ⊢ L —→ L′
      --------------------------------
    → Ψ ⊢ L ⊕[ op ] M —→ L′ ⊕[ op ] M

  ξ-⊕₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V M M′ : Term Θ Δ} {op : Prim}
    → Value V
    → Ψ ⊢ M —→ M′
      --------------------------------
    → Ψ ⊢ V ⊕[ op ] M —→ V ⊕[ op ] M′

  ξ-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {M M′ : Term (suc Θ) Δ}
    → Ψ ,:= A ⊢ M —→ M′
      -------------------------------
    → Ψ ⊢ ν[ A ] M —→ ν[ A ] M′

  float-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty (suc Δ)} {A₀ : Ty Δ} {M : Term (suc Θ) (suc Δ)}
      {Y : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → strengthenᵗ? Y A ≡ just A₀
    → Result (ν[ A ] M)
      ------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ↑[ Y ≔ α ] c —→
        ν[ A₀ ] (M ↑[ Y ≔ suc α ] c)

  -- ν is the region binder, not an eliminator frame.  Nested ν-headed
  -- results are represented directly by `result-ν`, so there is no float-ν.
  float-·₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ}
    → Result (ν[ A ] M)
      --------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) · N —→ ν[ A ] (M · shiftᶿ N)

  float-·₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ}
    → Value V
    → Result (ν[ A ] M)
      --------------------------------------------------
    → Ψ ⊢ V · (ν[ A ] M) —→ ν[ A ] (shiftᶿ V · M)

  float-• : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {M : Term (suc Θ) Δ}
    → Result (ν[ A ] M)
      ------------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ⦂∀ B [ C ] —→ ν[ A ] (M ⦂∀ B [ C ])

  float-⟨⟩ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A B C : Ty Δ} {M : Term (suc Θ) Δ} {μ : Env∼ Δ}
      {c : μ ⊢ B ∼ C}
    → Result (ν[ A ] M)
      --------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ⟨ c ⟩ —→ ν[ A ] (M ⟨ c ⟩)

  float-⊕₁ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {M : Term (suc Θ) Δ} {N : Term Θ Δ} {op : Prim}
    → Result (ν[ A ] M)
      ------------------------------------------------------------------
    → Ψ ⊢ (ν[ A ] M) ⊕[ op ] N —→ ν[ A ] (M ⊕[ op ] shiftᶿ N)

  float-⊕₂ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {A : Ty Δ} {V : Term Θ Δ} {M : Term (suc Θ) Δ} {op : Prim}
    → Value V
    → Result (ν[ A ] M)
      ------------------------------------------------------------------
    → Ψ ⊢ V ⊕[ op ] (ν[ A ] M) —→ ν[ A ] (shiftᶿ V ⊕[ op ] M)

------------------------------------------------------------------------
-- Values and results do not reduce
------------------------------------------------------------------------

mutual
  value-no-step : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V M′ : Term Θ Δ}
    → Value V
    → ¬ (Ψ ⊢ V —→ M′)
  value-no-step (Λ Vʳ) (ξ-Λ step) = result-no-step Vʳ step
  value-no-step (Vᵥ 《 inj 》) (ground Vᵥ′ G≢G) = G≢G refl
  value-no-step (Vᵥ 《 inert 》) (ξ-⟨⟩ step) =
    value-no-step Vᵥ step
  value-no-step
      (Vʳ ↑[ X ≔ α ] adapter Rʳ pair≢)
      (id-cancel Rʳ′) =
    pair≢ (refl , refl)
  value-no-step
      (Vʳ ↑[ X ≔ α ] delimiter ())
      id-reveal
  value-no-step
      (result-val () ↑[ X ≔ α ] gate)
      blame-reveal
  value-no-step (Vʳ ↑[ X ≔ α ] gate) (ξ-reveal step) =
    result-no-step Vʳ step
  value-no-step
      (result-ν Vʳ ↑[ X ≔ α ] adapter-region Rʳ X∈A)
      (float-reveal strengthens result) =
    ⊥-elim (impossible (trans (sym (strengthenᵗ?-present X∈A)) strengthens))
    where
    impossible : ∀ {Δ} {A₀ : Ty Δ} → nothing ≡ just A₀ → ⊥
    impossible ()
  value-no-step
      (Vʳ ↓[ X ≔ α ] delimiter ())
      id-conceal
  value-no-step
      (() ↓[ X ≔ α ] gate)
      blame-conceal
  value-no-step (Vᵥ ↓[ X ≔ α ] gate) (ξ-conceal step) =
    value-no-step Vᵥ step

  result-no-step : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V M′ : Term Θ Δ}
    → Result V
    → ¬ (Ψ ⊢ V —→ M′)
  result-no-step (result-val Vᵥ) step = value-no-step Vᵥ step
  result-no-step (result-ν (result-val ())) blame-ν
  result-no-step (result-ν Vʳ) (ξ-ν step) = result-no-step Vʳ step

ΛBody-stable : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {M M′ : Term Θ Δ}
  → ΛBody M
  → Ψ ⊢ M —→ M′
  → ΛBody M′
ΛBody-stable (body-result Vʳ) step =
  ⊥-elim (result-no-step Vʳ step)
ΛBody-stable (body-reveal Vʳ) (id-cancel Rʳ) = body-result Rʳ
ΛBody-stable (body-reveal (result-val ($ κ))) id-reveal =
  body-result (result-val ($ κ))
ΛBody-stable (body-reveal Vʳ) (conceal-reveal Rʳ) = body-result Rʳ
ΛBody-stable (body-reveal (result-val ())) blame-reveal
ΛBody-stable (body-reveal Vʳ) (β-reveal-∀ Rʳ) =
  body-Λ (body-reveal Rʳ)
ΛBody-stable (body-reveal Vʳ)
    (float-reveal strengthens (result-ν Rʳ)) =
  body-ν (body-reveal Rʳ)
ΛBody-stable (body-reveal Vʳ) (ξ-reveal step) =
  ⊥-elim (result-no-step Vʳ step)
ΛBody-stable (body-conceal (result-val ($ κ))) id-conceal =
  body-result (result-val ($ κ))
ΛBody-stable (body-conceal Vʳ) (β-conceal-∀ Rʳ) =
  body-Λ (body-conceal Rʳ)
ΛBody-stable (body-conceal (result-ν Vʳ))
    (float-conceal (result-ν Rʳ)) =
  body-ν (body-conceal Vʳ)
ΛBody-stable (body-conceal Vʳ) (ξ-conceal step) =
  ⊥-elim (result-no-step Vʳ step)
ΛBody-stable (body-ν (body-result (result-val ()))) blame-ν
ΛBody-stable (body-ν body) (ξ-ν step) =
  body-ν (ΛBody-stable body step)
ΛBody-stable (body-Λ body) (ξ-Λ step) =
  body-Λ (ΛBody-stable body step)

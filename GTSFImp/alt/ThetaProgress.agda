{-# OPTIONS --allow-unsolved-metas #-}

module alt.ThetaProgress where

-- File Charter:
--   * Proves closed-term progress from three explicit gap-family interfaces.
--   * Supplies total canonical forms and an indexed account of every residual
--     blocked eliminator; no unresolved obligation is hidden in the assembler.
--   * The adapter-family interface also exposes immobile ν values; the other
--     interfaces are ∀ boundary casts.
--   * The checked witnesses in `alt.probes.ProgressGaps` exhibit one inhabitant
--     of each interface, so future reduction rules can implement them directly.

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; refl; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import proof.Consistency using (shift-star-injective; zero-not-shift)

------------------------------------------------------------------------
-- Progress and canonical views
------------------------------------------------------------------------

data Progress {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Term Θ Δ → Set where
  step : ∀ {M M′}
    → Ψ ⊢ M —→ M′
      -------------
    → Progress Ψ M

  done : ∀ {M}
    → Value M
      ------------
    → Progress Ψ M

  failed : Progress Ψ blame

data CanonicalFun : ∀ {Θ Δ} → Term Θ Δ → Set where
  cf-ƛ : ∀ {Θ Δ} {A : Ty Δ} {N : Term Θ Δ}
      ----------------------
    → CanonicalFun (ƛ A ˙ N)

  cf-cast : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
    → Value V
      ------------------------------
    → CanonicalFun (V ⟨ c ↦ d ⟩)

  cf-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal} {d : Reveal}
    → Value V
      ---------------------------------------
    → CanonicalFun (V ↑[ X ≔ α ] (c ↦↑ d))

  cf-conceal : ∀ {Θ Δ} {V : Term Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal} {d : Conceal}
    → Value V
      -------------------------------------------------
    → CanonicalFun {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] (c ↦↓ d))

  cf-adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
      -------------------------------------------------
    → CanonicalFun ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  cf-adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ} {c}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → CanonicalFun ((ν[ A ] M) ↑[ X ≔ α ] c)

data CanonicalAll : ∀ {Θ Δ} → Term Θ Δ → Set where
  ca-Λ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
    → Value V
      ------------------
    → CanonicalAll (Λ V)

  ca-cast : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {c : extᵐ μ ⊢ A ∼ B}
    → Value V
      -------------------------
    → CanonicalAll (V ⟨ ∀ᶜ c ⟩)

  ca-gen : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------------------
    → CanonicalAll (V ⟨ (gen c) A≢★ ⟩)

  ca-adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
      -------------------------------------------------
    → CanonicalAll ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  ca-adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ} {c}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → CanonicalAll ((ν[ A ] M) ↑[ X ≔ α ] c)

data CanonicalStar : ∀ {Θ Δ} → Term Θ Δ → Set where
  cs-tag : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
      {Gᵍ : Ground G} ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      ----------------------------------------------------
    → CanonicalStar (V ⟨ _! ⦃ Gᵍ ⦄ (idᵍ {μ = μ} Gᵍ) ⟩)

  cs-adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
      ------------------------------------------------------------
    → CanonicalStar ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  cs-adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ} {c}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → CanonicalStar ((ν[ A ] M) ↑[ X ≔ α ] c)

data CanonicalBase : ∀ {Θ Δ} → Term Θ Δ → Set where
  cb-ℕ : ∀ {Θ Δ n}
      ---------------------------
    → CanonicalBase {Θ = Θ} {Δ = Δ} ($ (κℕ n))

  cb-𝔹 : ∀ {Θ Δ b}
      ---------------------------
    → CanonicalBase {Θ = Θ} {Δ = Δ} ($ (κ𝔹 b))

  cb-adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
      ------------------------------------------------------------
    → CanonicalBase ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  cb-adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ} {c}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → CanonicalBase ((ν[ A ] M) ↑[ X ≔ α ] c)

data BoundaryBase : ∀ {Θ Δ} → Term Θ Δ → Set where
  bb-adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
      ------------------------------------------------------------
    → BoundaryBase ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  bb-adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ} {c}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → BoundaryBase ((ν[ A ] M) ↑[ X ≔ α ] c)

data BoundaryValue : ∀ {Θ Δ} → Term Θ Δ → Set where
  bv-reveal-adapter : ∀ {Θ Δ} {R : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Value R
    → ImmobileHead R
    → ¬ (X ≡ Y × α ≡ β)
      ------------------------------------------------------------
    → BoundaryValue ((R ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  bv-reveal-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → BoundaryValue ((ν[ A ] M) ↑[ X ≔ α ] c)

data CanonicalAtom : ∀ {Θ Δ} → Term Θ Δ → Set where
  atom-constant : ∀ {Θ Δ κ}
      ---------------------------------
    → CanonicalAtom {Θ = Θ} {Δ = Δ} ($ κ)

  atom-seal : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Value V
      -------------------------------------
    → CanonicalAtom (V ↓[ X ≔ α ] seal)

  atom-tagged : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {H : Ty Δ} ⦃ Hᵍ : Ground H ⦄ ⦃ H∼★ : μ ⊢ H ∼★ ⦄
      ⦃ Hns : NonStar H ⦄
    → Value V
      ----------------------------------------------------
    → CanonicalAtom (V ⟨ (idᵍ Hᵍ) ! ⟩)

  atom-boundary : ∀ {Θ Δ} {V : Term Θ Δ}
    → BoundaryValue V
      -------------------
    → CanonicalAtom V

data ConcealBoundary : ∀ {Θ Δ} → Term Θ Δ → Set where
  conceal-boundary : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Value V
    → ImmobileHead V
      -------------------------------------------------
    → ConcealBoundary {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] c)

data NonLambdaAll : ∀ {Θ Δ} → Term Θ Δ → Set where
  nla-cast : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {A B : Ty (suc Δ)} {c : extᵐ μ ⊢ A ∼ B}
    → Value V
      --------------------------
    → NonLambdaAll (V ⟨ ∀ᶜ c ⟩)

  nla-gen : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value V
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------------------
    → NonLambdaAll (V ⟨ (gen c) A≢★ ⟩)

  nla-adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
      -------------------------------------------------
    → NonLambdaAll ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  nla-adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ} {c}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
      -------------------------------------------------
    → NonLambdaAll ((ν[ A ] M) ↑[ X ≔ α ] c)

data BlockedElimination {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) :
    Term Θ Δ → Set where
  adapter-· : ∀ {B : Ty Δ} {F V : Term Θ Δ}
    → Value F
    → ImmobileHead F
    → Value V
    → Ψ ∣ [] ⊢ F · V ⦂ B
      ------------------------------
    → BlockedElimination Ψ (F · V)

  adapter-• : ∀ {C : Ty Δ} {B : Ty (suc Δ)} {F : Term Θ Δ}
    → Value F
    → ImmobileHead F
    → Ψ ∣ [] ⊢ F ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
      ---------------------------------------------
    → BlockedElimination Ψ (F ⦂∀ B [ C ])

  adapter-project : ∀ {F : Term Θ Δ}
      {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Value F
    → ImmobileHead F
    → Ψ ∣ [] ⊢ F ⟨ ？ (idᵍ Gᵍ) ⟩ ⦂ G
      ---------------------------------------------
    → BlockedElimination Ψ (F ⟨ ？ (idᵍ Gᵍ) ⟩)

  boundary-⊕ : ∀ {op V W}
    → Value V
    → Value W
    → ((BoundaryBase V × (∀ {V′} → ¬ (Ψ ⊢ V —→ V′)))
      ⊎ (BoundaryBase W × (∀ {W′} → ¬ (Ψ ⊢ W —→ W′))))
    → Ψ ∣ [] ⊢ V ⊕[ op ] W ⦂ primResultTy op
      ------------------------------------------------------------
    → BlockedElimination Ψ (V ⊕[ op ] W)

  atomic-reveal : ∀ {A : Ty (suc Δ)} {B : Ty Δ}
      {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Atom A
    → Value V
    → ImmobileHead V
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] c ⦂ B
      ------------------------------------------------------------
    → BlockedElimination Ψ (V ↑[ X ≔ α ] c)

  unseal-interior : ∀ {B : Ty Δ} {V : Term Θ (suc (suc Δ))}
      {Y : TyVar (suc (suc Δ))} {β : TyVar Θ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Value (V ↑[ Y ≔ β ] id↑)
    → ImmobileHead (V ↑[ Y ≔ β ] id↑)
    → Ψ ∣ [] ⊢ (V ↑[ Y ≔ β ] id↑)
        ↑[ X ≔ α ] unseal ⦂ B
      ------------------------------------------------------------
    → BlockedElimination Ψ
        ((V ↑[ Y ≔ β ] id↑) ↑[ X ≔ α ] unseal)

  atomic-conceal : ∀ {A : Ty Δ} {M : Term Θ Δ}
    → ConcealBoundary M
    → Ψ ∣ [] ⊢ M ⦂ A
      ------------------------------------------------------------
    → BlockedElimination Ψ M

  bottom-cast : ∀ {A : Ty Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
    → Value V
    → Ψ ∣ [] ⊢ V ⟨ bot-elim { μ = μ } ⟩ ⦂ A
      ------------------------------------------------------------
    → BlockedElimination Ψ (V ⟨ bot-elim { μ = μ } ⟩)

  ν-immobile : ∀ {A B : Ty Δ} {V : Term (suc Θ) Δ}
    → Value V
    → ImmobileHead V
    → Ψ ∣ [] ⊢ ν[ A ] V ⦂ B
      ---------------------------------
    → BlockedElimination Ψ (ν[ A ] V)

------------------------------------------------------------------------
-- Canonical forms
------------------------------------------------------------------------

wkᵗ-injective : ∀ {Δ} (X : TyVar (suc Δ)) {A B : Ty Δ}
  → wkᵗ X A ≡ wkᵗ X B
  → A ≡ B
wkᵗ-injective X {A} {B} eq = just-injective
  (trans (sym (strengthenᵗ?-wkᵗ X A))
    (trans (cong (strengthenᵗ? X) eq) (strengthenᵗ?-wkᵗ X B)))

atom-not-⇒ : ∀ {Δ} {A B C : Ty Δ}
  → Atom A
  → A ≢ B ⇒ C
atom-not-⇒ (＇ X) ()
atom-not-⇒ (‵ ι) ()
atom-not-⇒ ★ ()

atom-not-∀ : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → Atom A
  → A ≢ `∀ B
atom-not-∀ (＇ X) ()
atom-not-∀ (‵ ι) ()
atom-not-∀ ★ ()

wk-atom : ∀ {Δ} (X : TyVar (suc Δ)) {A : Ty Δ}
  → Atom A
  → Atom (wkᵗ X A)
wk-atom X (＇ Y) = ＇ punchIn X Y
wk-atom X (‵ ι) = ‵ ι
wk-atom X ★ = ★

no-id-conceal-⇒ : ∀ {Δ} {X : TyVar (suc Δ)} {R S T : Ty (suc Δ)}
    {A B : Ty (suc Δ)}
  → ⊢↓[ X ⦂ R ] id↓ ⦂ S ↝ T
  → T ≡ A ⇒ B
  → ⊥
no-id-conceal-⇒ (⊢id↓ atom) eq = atom-not-⇒ atom eq

no-id-conceal-∀ : ∀ {Δ} {X : TyVar (suc Δ)} {R S T : Ty (suc Δ)}
    {A : Ty (suc (suc Δ))}
  → ⊢↓[ X ⦂ R ] id↓ ⦂ S ↝ T
  → T ≡ `∀ A
  → ⊥
no-id-conceal-∀ (⊢id↓ atom) eq = atom-not-∀ atom eq

no-fun-reveal-∀ : ∀ {Δ} {X : TyVar (suc Δ)} {R S T : Ty (suc Δ)}
    {A : Ty (suc Δ)} {c : Conceal} {d : Reveal}
  → ⊢↑[ X ⦂ R ] c ↦↑ d ⦂ S ↝ T
  → T ≡ wkᵗ X (`∀ A)
  → ⊥
no-fun-reveal-∀ (⊢↑-⇒ c⊢ d⊢) ()

no-id-reveal-∀ : ∀ {Δ} {X : TyVar (suc Δ)} {R S T : Ty (suc Δ)}
    {A : Ty (suc Δ)}
  → ⊢↑[ X ⦂ R ] id↑ ⦂ S ↝ T
  → T ≡ wkᵗ X (`∀ A)
  → ⊥
no-id-reveal-∀ (⊢id↑ atom) eq = atom-not-∀ atom eq

canonical-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A B : Ty Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → CanonicalFun V
canonical-⇒ (ƛ A ˙ N) (⊢ƛ V⊢) = cf-ƛ
canonical-⇒ (Λ Vᵛ) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ ($ (κ𝔹 b)) ()
canonical-⇒ (inject Vᵛ) ()
canonical-⇒ (Vᵛ 《 fun 》) (⊢⟨⟩ V⊢ (c ↦ d)) = cf-cast Vᵛ
canonical-⇒ (Vᵛ 《 all 》) ()
canonical-⇒ (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-⇒ (seal-value Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-⇒ (reveal-fun Vᵛ nonλ) typing = cf-reveal Vᵛ
canonical-⇒ (conceal-fun Vᵛ) typing = cf-conceal Vᵛ
canonical-⇒ (adapter Vᵛ head pair≢) typing =
  cf-adapter Vᵛ head pair≢
canonical-⇒ (adapter-region Vᵛ head X∈E) typing =
  cf-adapter-region Vᵛ head X∈E

canonical-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty (suc Δ)}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ `∀ A
  → CanonicalAll V
canonical-∀ (ƛ A ˙ N) ()
canonical-∀ (Λ Vᵛ) (⊢Λ V⊢) = ca-Λ Vᵛ
canonical-∀ ($ (κℕ n)) ()
canonical-∀ ($ (κ𝔹 b)) ()
canonical-∀ (inject Vᵛ) ()
canonical-∀ (Vᵛ 《 fun 》) ()
canonical-∀ (Vᵛ 《 all 》) (⊢⟨⟩ V⊢ (∀ᶜ c)) = ca-cast Vᵛ
canonical-∀ (Vᵛ 《 genᵥ A≠★ safe 》)
    (⊢⟨⟩ V⊢ ((gen c) A≠★)) =
  ca-gen Vᵛ A≠★ safe
canonical-∀ (seal-value Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-∀ (reveal-fun Vᵛ nonλ)
    (⊢reveal α-eq c⊢ V⊢) =
  ⊥-elim (no-fun-reveal-∀ c⊢ refl)
canonical-∀ (conceal-fun Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-∀ (adapter Vᵛ head pair≢) typing =
  ca-adapter Vᵛ head pair≢
canonical-∀ (adapter-region Vᵛ head X∈E) typing =
  ca-adapter-region Vᵛ head X∈E

canonical-★ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ★
  → CanonicalStar V
canonical-★ (ƛ A ˙ N) ()
canonical-★ (Λ Vᵛ) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ ($ (κ𝔹 b)) ()
canonical-★ (inject Vᵛ) (⊢⟨⟩ V⊢ c) = cs-tag Vᵛ
canonical-★ (Vᵛ 《 fun 》) ()
canonical-★ (Vᵛ 《 all 》) ()
canonical-★ (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-★ (seal-value Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-★ (reveal-fun Vᵛ nonλ)
    (⊢reveal α-eq () V⊢)
canonical-★ (conceal-fun Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-★ (adapter Vᵛ head pair≢) typing =
  cs-adapter Vᵛ head pair≢
canonical-★ (adapter-region Vᵛ head X∈E) typing =
  cs-adapter-region Vᵛ head X∈E

canonical-base : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {ι : Base}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ‵ ι
  → CanonicalBase V
canonical-base (ƛ A ˙ N) ()
canonical-base (Λ Vᵛ) ()
canonical-base ($ (κℕ n)) (⊢$ (κℕ .n)) = cb-ℕ
canonical-base ($ (κ𝔹 b)) (⊢$ (κ𝔹 .b)) = cb-𝔹
canonical-base (inject Vᵛ) ()
canonical-base (Vᵛ 《 fun 》) ()
canonical-base (Vᵛ 《 all 》) ()
canonical-base (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-base (seal-value Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-base (reveal-fun Vᵛ nonλ)
    (⊢reveal α-eq () V⊢)
canonical-base (conceal-fun Vᵛ)
    (⊢conceal X-live α-eq () V⊢)
canonical-base (adapter Vᵛ head pair≢) typing =
  cb-adapter Vᵛ head pair≢
canonical-base (adapter-region Vᵛ head X∈E) typing =
  cb-adapter-region Vᵛ head X∈E

canonical-variable : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {Y : TyVar Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ＇ Y
  → CanonicalAtom V
canonical-variable (ƛ A ˙ N) ()
canonical-variable (Λ Vᵛ) ()
canonical-variable ($ (κℕ n)) ()
canonical-variable ($ (κ𝔹 b)) ()
canonical-variable (inject Vᵛ) ()
canonical-variable (Vᵛ 《 fun 》) ()
canonical-variable (Vᵛ 《 all 》) ()
canonical-variable (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-variable (seal-value Vᵛ) typing = atom-seal Vᵛ
canonical-variable (reveal-fun Vᵛ nonλ) (⊢reveal α-eq () V⊢)
canonical-variable (conceal-fun Vᵛ) (⊢conceal X-live α-eq () V⊢)
canonical-variable (adapter Vᵛ head pair≢) typing =
  atom-boundary (bv-reveal-adapter Vᵛ head pair≢)
canonical-variable (adapter-region Vᵛ head X∈E) typing =
  atom-boundary (bv-reveal-region Vᵛ head X∈E)

canonical-atom : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty Δ}
  → Atom A
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ A
  → CanonicalAtom V
canonical-atom (＇ X) Vᵛ V⊢ = canonical-variable Vᵛ V⊢
canonical-atom (‵ `ℕ) Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-atom (‵ `ℕ) Vᵛ V⊢ | cb-ℕ = atom-constant
canonical-atom (‵ `ℕ) Vᵛ V⊢ | cb-adapter Wᵛ head neq =
  atom-boundary (bv-reveal-adapter Wᵛ head neq)
canonical-atom (‵ `ℕ) Vᵛ V⊢ | cb-adapter-region Wᵛ head X∈E =
  atom-boundary (bv-reveal-region Wᵛ head X∈E)
canonical-atom (‵ `𝔹) Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-atom (‵ `𝔹) Vᵛ V⊢ | cb-𝔹 = atom-constant
canonical-atom (‵ `𝔹) Vᵛ V⊢ | cb-adapter Wᵛ head neq =
  atom-boundary (bv-reveal-adapter Wᵛ head neq)
canonical-atom (‵ `𝔹) Vᵛ V⊢ | cb-adapter-region Wᵛ head X∈E =
  atom-boundary (bv-reveal-region Wᵛ head X∈E)
canonical-atom ★ Vᵛ V⊢ with canonical-★ Vᵛ V⊢
canonical-atom ★ Vᵛ V⊢
    | cs-tag {G = G} {Gᵍ = Gᵍ} ⦃ G∼★ ⦄ ⦃ Gns ⦄ Wᵛ =
  atom-tagged ⦃ Hᵍ = Gᵍ ⦄ ⦃ H∼★ = G∼★ ⦄
    ⦃ Hns = Gns ⦄ Wᵛ
canonical-atom ★ Vᵛ V⊢ | cs-adapter Wᵛ head neq =
  atom-boundary (bv-reveal-adapter Wᵛ head neq)
canonical-atom ★ Vᵛ V⊢ | cs-adapter-region Wᵛ head X∈E =
  atom-boundary (bv-reveal-region Wᵛ head X∈E)

constant-not-variable : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {κ : Const} {X : TyVar Δ}
  → Ψ ∣ [] ⊢ $ κ ⦂ ＇ X
  → ⊥
constant-not-variable {κ = κℕ n} ()
constant-not-variable {κ = κ𝔹 b} ()

tagged-not-variable : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ Gns : NonStar G ⦄ {X : TyVar Δ}
  → Ψ ∣ [] ⊢ V ⟨ (idᵍ Gᵍ) ! ⟩ ⦂ ＇ X
  → ⊥
tagged-not-variable ()

data CanonicalNat : ∀ {Θ Δ} → Term Θ Δ → Set where
  nat-constant : ∀ {Θ Δ n}
      -------------------------------
    → CanonicalNat {Θ = Θ} {Δ = Δ} ($ (κℕ n))

  nat-boundary : ∀ {Θ Δ} {V : Term Θ Δ}
    → BoundaryBase V
      ------------------
    → CanonicalNat V

data CanonicalBool : ∀ {Θ Δ} → Term Θ Δ → Set where
  bool-constant : ∀ {Θ Δ b}
      --------------------------------
    → CanonicalBool {Θ = Θ} {Δ = Δ} ($ (κ𝔹 b))

  bool-boundary : ∀ {Θ Δ} {V : Term Θ Δ}
    → BoundaryBase V
      ------------------
    → CanonicalBool V

canonical-ℕ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ‵ `ℕ
  → CanonicalNat V
canonical-ℕ Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-ℕ Vᵛ V⊢ | cb-ℕ = nat-constant
canonical-ℕ ($ (κ𝔹 b)) () | cb-𝔹
canonical-ℕ Vᵛ V⊢ | cb-adapter Wᵛ head neq =
  nat-boundary (bb-adapter Wᵛ head neq)
canonical-ℕ Vᵛ V⊢ | cb-adapter-region Wᵛ head X∈E =
  nat-boundary (bb-adapter-region Wᵛ head X∈E)

canonical-𝔹 : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ‵ `𝔹
  → CanonicalBool V
canonical-𝔹 Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-𝔹 ($ (κℕ n)) () | cb-ℕ
canonical-𝔹 Vᵛ V⊢ | cb-𝔹 = bool-constant
canonical-𝔹 Vᵛ V⊢ | cb-adapter Wᵛ head neq =
  bool-boundary (bb-adapter Wᵛ head neq)
canonical-𝔹 Vᵛ V⊢ | cb-adapter-region Wᵛ head X∈E =
  bool-boundary (bb-adapter-region Wᵛ head X∈E)

------------------------------------------------------------------------
-- Ground-cast classification
------------------------------------------------------------------------

data ToStar {Δ : TyCtx} {μ : Env∼ Δ} : ∀ {A : Ty Δ}
    → (c : μ ⊢ A ∼ ★) → Set where
  same : ToStar (id ★)
  other : ∀ {A : Ty Δ} {c : μ ⊢ A ∼ ★}
    → A ≢ ★
    → ToStar c

to-star : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c : μ ⊢ A ∼ ★)
  → ToStar c
to-star (id ★) = same
to-star (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (nonStar≢★ Ans)
to-star (？_ ⦃ g ⦄ c ⦃ () ⦄)
to-star (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) = other (λ ())

data FromStar {Δ : TyCtx} {μ : Env∼ Δ} : ∀ {B : Ty Δ}
    → (c : μ ⊢ ★ ∼ B) → Set where
  same : FromStar (id ★)
  other : ∀ {B : Ty Δ} {c : μ ⊢ ★ ∼ B}
    → B ≢ ★
    → FromStar c

from-star : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ}
  → (c : μ ⊢ ★ ∼ B)
  → FromStar c
from-star (id ★) = same
from-star (_! ⦃ g ⦄ c ⦃ () ⦄)
from-star (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (nonStar≢★ Bns)
from-star (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) = other (λ ())

data ToGround {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    (Gᵍ : Ground G) : ∀ {A : Ty Δ} → μ ⊢ A ∼ G → Set where
  same : ToGround Gᵍ (idᵍ Gᵍ)
  other : ∀ {A : Ty Δ} {c : μ ⊢ A ∼ G}
    → A ≢ G
    → ToGround Gᵍ c

occurs-star-impossible : ∀ {Δ} {X : TyVar Δ}
  → X ∈ᵗ ★
  → ⊥
occurs-star-impossible ()

to-ground : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
  → (Gᵍ : Ground G)
  → (c : μ ⊢ A ∼ G)
  → ToGround Gᵍ c
to-ground (‵ ι) (id (‵ ι)) = same
to-ground (‵ ι) (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground (‵ ι) (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) = other (λ ())
to-ground ★⇒★ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground ★⇒★ (c ↦ d) with from-star c | to-star d
to-ground ★⇒★ (.(id ★) ↦ .(id ★)) | same | same = same
to-ground ★⇒★ (c ↦ d) | same | other B≠★ =
  other (λ { refl → B≠★ refl })
to-ground ★⇒★ (c ↦ d) | other A≠★ | same =
  other (λ { refl → A≠★ refl })
to-ground ★⇒★ (c ↦ d) | other A≠★ | other B≠★ =
  other (λ { refl → A≠★ refl })
to-ground ★⇒★ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) = other (λ ())
to-ground (＇ X) (id (＇ .X)) = same
to-ground (＇ X) (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground (＇ X) (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) = other (λ ())
to-ground ∀★ (∀ᶜ c) with to-star c
to-ground ∀★ (∀ᶜ (id ★)) | same = same
to-ground ∀★ (∀ᶜ c) | other A≠★ =
  other (λ { refl → A≠★ refl })
to-ground ∀★ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) = other (λ ())
to-ground ∀★ (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≠★)
to-ground ∀★ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) =
  other (λ { refl → occurs-star-impossible z∈A })
to-ground ∀★ bot-elim = other (λ ())

data FromGround {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    (Gᵍ : Ground G) : ∀ {B : Ty Δ} → μ ⊢ G ∼ B → Set where
  same : FromGround Gᵍ (idᵍ Gᵍ)
  other : ∀ {B : Ty Δ} {c : μ ⊢ G ∼ B}
    → B ≢ G
    → FromGround Gᵍ c

from-ground : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
  → (Gᵍ : Ground G)
  → (c : μ ⊢ G ∼ B)
  → FromGround Gᵍ c
from-ground (‵ ι) (id (‵ ι)) = same
from-ground (‵ ι) (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground (‵ ι) (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) = other (λ ())
from-ground ★⇒★ (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground ★⇒★ (c ↦ d) with to-star c | from-star d
from-ground ★⇒★ (.(id ★) ↦ .(id ★)) | same | same = same
from-ground ★⇒★ (c ↦ d) | same | other B≠★ =
  other (λ { refl → B≠★ refl })
from-ground ★⇒★ (c ↦ d) | other A≠★ | same =
  other (λ { refl → A≠★ refl })
from-ground ★⇒★ (c ↦ d) | other A≠★ | other B≠★ =
  other (λ { refl → A≠★ refl })
from-ground ★⇒★ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) = other (λ ())
from-ground (＇ X) (id (＇ .X)) = same
from-ground (＇ X) (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground (＇ X) (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) = other (λ ())
from-ground ∀★ (∀ᶜ c) with from-star c
from-ground ∀★ (∀ᶜ (id ★)) | same = same
from-ground ∀★ (∀ᶜ c) | other B≠★ =
  other (λ { refl → B≠★ refl })
from-ground ∀★ (_! ⦃ g ⦄ c ⦃ Ans ⦄) = other (λ ())
from-ground ∀★ (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c B≠★)
from-ground ∀★ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) =
  other (λ { refl → occurs-star-impossible z∈B })
from-ground ∀★ bot-intro = other (λ ())

theta-gen-safe′ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    {C B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ C ∼ B)
  → C ≡ ⇑ᵗ A
  → A ≢ ★
  → NonVar B
  → zero ∈ᵗ B
  → GenSafe c
theta-gen-safe′ (id a) refl A≠★ Bnv z∈B =
  ⊥-elim (zero-not-shift z∈B)
theta-gen-safe′ (c ↦ d) eq A≠★ Bnv z∈B = safe-⇒
theta-gen-safe′ (∀ᶜ c) eq A≠★ Bnv z∈B = safe-∀
theta-gen-safe′ (_! ⦃ g ⦄ c ⦃ Ans ⦄) eq A≠★ Bnv ()
theta-gen-safe′ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) eq A≠★ Bnv z∈B =
  ⊥-elim (A≠★ (shift-star-injective (sym eq)))
theta-gen-safe′ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★)
    eq A≠★ Bnv z∈B =
  safe-inst B≠★
theta-gen-safe′ (gen_ {A = D} ⦃ Dnv ⦄ ⦃ z∈D ⦄ c D≠★)
    eq A≠★ Bnv z∈B =
  safe-gen D≠★ (theta-gen-safe′ c refl D≠★ Dnv z∈D)
theta-gen-safe′ bot-elim eq A≠★ Bnv (∈-all ())
theta-gen-safe′ bot-intro eq A≠★ Bnv (∈-all ())

theta-gen-safe : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    {B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ ⇑ᵗ A ∼ B)
  → A ≢ ★
  → NonVar B
  → zero ∈ᵗ B
  → GenSafe c
theta-gen-safe c A≠★ Bnv z∈B =
  theta-gen-safe′ c refl A≠★ Bnv z∈B

------------------------------------------------------------------------
-- Progress modulo the three checked merge families
------------------------------------------------------------------------

module WithGaps
  -- Representative: `alt.probes.ProgressGaps.baseAdapter-gap-witness`.
  (gap-adapter-⊕ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ Δ}
    → BlockedElimination Ψ M
    → Progress Ψ M)
  -- Witness: `alt.probes.ProgressGaps.allReveal-gap-witness`.
  (gap-∀-reveal-cast : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {B : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Value V
    → NonLambdaAll V
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] `∀↑ c ⦂ `∀ B
    → Progress Ψ (V ↑[ X ≔ α ] `∀↑ c))
  -- Witness: `alt.probes.ProgressGaps.allConceal-gap-witness`.
  (gap-∀-conceal-cast : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {V : Term Θ Δ}
      {B : Ty (suc (suc Δ))} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal}
    → Value V
    → NonLambdaAll V
    → Ψ ∣ [] ⊢ V ↓[ X ≔ α ] `∀↓ c ⦂ `∀ B
    → Progress Ψ (V ↓[ X ≔ α ] `∀↓ c))
  where


  boundary-head : ∀ {Θ Δ} {V : Term Θ Δ}
    → BoundaryValue V
    → ImmobileHead V
  boundary-head (bv-reveal-adapter Vᵛ head neq) = adapter-head
  boundary-head (bv-reveal-region Vᵛ head X∈A) = adapter-region-head

  cast-value-progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {A B : Ty Δ} {μ : Env∼ Δ}
    → Ψ ∣ [] ⊢ V ⦂ A
    → Value V
    → (c : μ ⊢ A ∼ B)
    → Progress Ψ (V ⟨ c ⟩)
  cast-value-progress V⊢ Vᵛ (id a) = step (β-id Vᵛ)
  cast-value-progress V⊢ Vᵛ (c ↦ d) = done (Vᵛ 《 fun 》)
  cast-value-progress V⊢ Vᵛ (∀ᶜ c) = done (Vᵛ 《 all 》)
  cast-value-progress V⊢ Vᵛ
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
      with to-ground Gᵍ c
  cast-value-progress V⊢ Vᵛ
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ .(idᵍ Gᵍ) ⦃ Ans ⦄)
      | same =
    done
      (inject ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
        ⦃ Gns = Ans ⦄ Vᵛ)
  cast-value-progress V⊢ Vᵛ
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
      | other A≠G =
    step (ground ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Ans = Ans ⦄ ⦃ Gns = ground-nonstar Gᵍ ⦄ Vᵛ A≠G)
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)
      with from-ground Gᵍ c
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄)
      | other B≠G =
    step (expand ⦃ Gᵍ = Gᵍ ⦄ ⦃ ★∼G = ★∼G ⦄
      ⦃ Bns = Bns ⦄ ⦃ Gns = ground-nonstar Gᵍ ⦄ Vᵛ
      (λ G≡B → B≠G (sym G≡B)))
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same with canonical-★ Vᵛ V⊢
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-tag {G = H} {Gᵍ = Hᵍ} ⦃ H∼★ ⦄ ⦃ Hns ⦄ Wᵛ
      with H ≟Ty G
  cast-value-progress V⊢ Vᵛ
      (？_ {G = .H} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-tag {G = H} {Gᵍ = Hᵍ} ⦃ H∼★ ⦄ ⦃ Hns ⦄ Wᵛ
      | yes refl rewrite nonStar-unique Bns Hns | ground-unique Gᵍ Hᵍ =
    step (tag-untag ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄
      ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = Hns ⦄ Wᵛ)
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-tag {G = H} {Gᵍ = Hᵍ} ⦃ H∼★ ⦄ ⦃ Hns ⦄ Wᵛ
      | no H≠G =
    step (tag-untag-bad ⦃ Gᵍ = Hᵍ ⦄ ⦃ Hᵍ = Gᵍ ⦄
      ⦃ G∼★ = H∼★ ⦄ ⦃ ★∼H = ★∼G ⦄
      ⦃ Gns = Hns ⦄ ⦃ Hns = Bns ⦄ Wᵛ H≠G)
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-adapter Wᵛ head neq =
    step (★-project-reveal Vᵛ)
  cast-value-progress V⊢ Vᵛ
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-adapter-region Wᵛ head X∈E =
    gap-adapter-⊕
      (adapter-project Vᵛ adapter-region-head
        (⊢⟨⟩ V⊢ (？ (idᵍ Gᵍ))))
  cast-value-progress V⊢ Vᵛ
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) =
    step (β-inst Vᵛ B≠★)
  cast-value-progress V⊢ Vᵛ
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) =
    done (Vᵛ 《 genᵥ A≠★ (theta-gen-safe c A≠★ Bnv z∈B) 》)
  cast-value-progress V⊢ Vᵛ bot-elim =
    gap-adapter-⊕ (bottom-cast Vᵛ (⊢⟨⟩ V⊢ bot-elim))
  cast-value-progress V⊢ Vᵛ bot-intro = step (blame-bot-intro Vᵛ)

  ground-occurs-pivot : ∀ {Δ} {X : TyVar Δ} {G : Ty Δ}
    → Ground G
    → X ∈ᵗ G
    → G ≡ ＇ X
  ground-occurs-pivot {X = X} (＇ .X) var-∈ = refl
  ground-occurs-pivot (‵ ι) ()
  ground-occurs-pivot ★⇒★ (∈-fun-left ())
  ground-occurs-pivot ★⇒★ (∈-fun-right X∉★ ())
  ground-occurs-pivot ∀★ (∈-all ())

  finish-id-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {B : Ty Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Atom B
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] id↑ ⦂ B
    → Value V
    → CanonicalAtom V
    → Progress Ψ (V ↑[ X ≔ α ] id↑)
  finish-id-reveal atom typing ($ κ) atom-constant = step id-reveal
  finish-id-reveal {X = X} atom
      typing@(⊢reveal rep-eq c⊢ V⊢) (inject Vᵛ)
      (atom-tagged {H = ＇ Y} ⦃ Hᵍ = ＇ .Y ⦄ Vᵛ′)
      with X ≟ Y
  finish-id-reveal atom typing@(⊢reveal rep-eq c⊢ V⊢)
      (inject Vᵛ)
      (atom-tagged ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄ Vᵛ′)
      | yes refl =
    step (inject-reveal-resolve ⦃ X∼★ = H∼★ ⦄ ⦃ Xns = Hns ⦄
      rep-eq Vᵛ′)
  finish-id-reveal atom typing (inject Vᵛ)
      (atom-tagged ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄ Vᵛ′)
      | no X≢Y with strengthenᵗ?-absent (∉-var (≢→≢ᶠ X≢Y))
  finish-id-reveal atom typing (inject Vᵛ)
      (atom-tagged ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄ Vᵛ′)
      | no X≢Y | H₀ , strengthens =
    step (inject-reveal ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄
      strengthens Vᵛ′)
  finish-id-reveal atom typing (inject Vᵛ)
      (atom-tagged ⦃ Hᵍ = ‵ ι ⦄ ⦃ H∼★ = H∼★ ⦄
        ⦃ Hns = Hns ⦄ Vᵛ′) =
    step
      (inject-reveal ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄ refl Vᵛ′)
  finish-id-reveal atom typing (inject Vᵛ)
      (atom-tagged ⦃ Hᵍ = ★⇒★ ⦄ ⦃ H∼★ = H∼★ ⦄
        ⦃ Hns = Hns ⦄ Vᵛ′) =
    step
      (inject-reveal ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄ refl Vᵛ′)
  finish-id-reveal atom typing (inject Vᵛ)
      (atom-tagged ⦃ Hᵍ = ∀★ ⦄ ⦃ H∼★ = H∼★ ⦄
        ⦃ Hns = Hns ⦄ Vᵛ′) =
    step
      (inject-reveal ⦃ H∼★ = H∼★ ⦄ ⦃ Hns = Hns ⦄ refl Vᵛ′)
  finish-id-reveal {X = X} atom typing Vᵛ (atom-seal Wᵛ) =
    gap-adapter-⊕ (atomic-reveal (wk-atom X atom) Vᵛ seal-head typing)
  finish-id-reveal {X = X} atom typing Vᵛ
      (atom-boundary boundary) =
    gap-adapter-⊕
      (atomic-reveal (wk-atom X atom) Vᵛ (boundary-head boundary) typing)

  reveal-value-progress-core : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {C B : Ty Δ} {A T : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
      {fresh : α ∉ᵛ σ}
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] c ⦂ B
    → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ∣ [] ⊢ V ⦂ A
    → Value V
    → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ A ↝ T
    → T ≡ wkᵗ X B
    → Progress Ψ (V ↑[ X ≔ α ] c)
  reveal-value-progress-core {X = X} typing V⊢ Vᵛ ⊢unseal target-eq
      with wkᵗ-injective X target-eq
  reveal-value-progress-core typing V⊢ Vᵛ ⊢unseal target-eq | refl
      with canonical-atom (＇ _) Vᵛ V⊢
  reveal-value-progress-core typing V⊢ ($ κ) ⊢unseal target-eq
      | refl | atom-constant =
    ⊥-elim (constant-not-variable V⊢)
  reveal-value-progress-core typing V⊢ Vᵛ ⊢unseal target-eq
      | refl | atom-tagged Wᵛ =
    ⊥-elim (tagged-not-variable V⊢)
  reveal-value-progress-core typing V⊢ (seal-value Wᵛ) ⊢unseal target-eq
      | refl | atom-seal Wᵛ′ =
    step (conceal-reveal Wᵛ)
  reveal-value-progress-core {X = X} typing V⊢ Vᵛ ⊢unseal target-eq
      | refl | atom-boundary boundary =
    gap-adapter-⊕
      (atomic-reveal (＇ X) Vᵛ (boundary-head boundary) typing)
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-⇒ c⊢ d⊢) target-eq = ?
  reveal-value-progress-core {B = ＇ Y} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = ‵ ι} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = ★} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = B ⇒ D} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = `∀ B} typing V⊢ Vᵛ
      (⊢↑-∀ c⊢) refl with canonical-∀ Vᵛ V⊢
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-Λ Wᵛ = step (β-reveal-∀ Wᵛ)
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-cast Wᵛ =
    gap-∀-reveal-cast Vᵛ (nla-cast Wᵛ) typing
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-gen Wᵛ A≠★ safe =
    gap-∀-reveal-cast Vᵛ (nla-gen Wᵛ A≠★ safe) typing
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-adapter Wᵛ head neq =
    gap-∀-reveal-cast Vᵛ (nla-adapter Wᵛ head neq) typing
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-adapter-region Wᵛ head X∈E =
    gap-∀-reveal-cast Vᵛ (nla-adapter-region Wᵛ head X∈E) typing
  reveal-value-progress-core {B = ＇ Y} typing V⊢ Vᵛ (⊢id↑ atom) refl =
    finish-id-reveal (＇ Y) typing Vᵛ (canonical-atom atom Vᵛ V⊢)
  reveal-value-progress-core {B = ‵ ι} typing V⊢ Vᵛ
      (⊢id↑ atom) refl =
    finish-id-reveal (‵ ι) typing Vᵛ (canonical-atom atom Vᵛ V⊢)
  reveal-value-progress-core {B = ★} typing V⊢ Vᵛ (⊢id↑ atom) refl =
    finish-id-reveal ★ typing Vᵛ (canonical-atom atom Vᵛ V⊢)
  reveal-value-progress-core {B = B ⇒ D} typing V⊢ Vᵛ (⊢id↑ atom) eq =
    ⊥-elim (atom-not-⇒ atom eq)
  reveal-value-progress-core {B = `∀ B} typing V⊢ Vᵛ (⊢id↑ atom) eq =
    ⊥-elim (atom-not-∀ atom eq)

  reveal-value-progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {B : Ty Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] c ⦂ B
    → Value V
    → Progress Ψ (V ↑[ X ≔ α ] c)
  reveal-value-progress typing@(⊢reveal α-eq c⊢ V⊢) Vᵛ =
    reveal-value-progress-core typing V⊢ Vᵛ c⊢ refl

  finish-id-conceal : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {V : Term Θ Δ}
      {A : Ty Δ} {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Atom A
    → Ψ ∣ [] ⊢ V ↓[ X ≔ α ] id↓ ⦂ wkᵗ X A
    → Value V
    → CanonicalAtom V
    → Progress Ψ (V ↓[ X ≔ α ] id↓)
  finish-id-conceal atom typing ($ κ) atom-constant = step id-conceal
  finish-id-conceal atom typing (inject Vᵛ) (atom-tagged Vᵛ′) =
    step (inject-conceal Vᵛ′)
  finish-id-conceal atom typing Vᵛ (atom-seal Wᵛ) =
    gap-adapter-⊕
      (atomic-conceal (conceal-boundary Vᵛ seal-head) typing)
  finish-id-conceal atom typing Vᵛ (atom-boundary boundary) =
    gap-adapter-⊕
      (atomic-conceal
        (conceal-boundary Vᵛ (boundary-head boundary)) typing)

  conceal-value-progress-core : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {V : Term Θ Δ}
      {C A : Ty Δ} {S T B : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Ψ ∣ [] ⊢ V ↓[ X ≔ α ] c ⦂ B
    → Ψ ,end[ X ] ∣ [] ⊢ V ⦂ A
    → Value V
    → ⊢↓[ X ⦂ wkᵗ X C ] c ⦂ S ↝ T
    → S ≡ wkᵗ X A
    → T ≡ B
    → Progress Ψ (V ↓[ X ≔ α ] c)
  conceal-value-progress-core {X = X} typing V⊢ Vᵛ ⊢seal source-eq refl
      with wkᵗ-injective X source-eq
  conceal-value-progress-core typing V⊢ Vᵛ ⊢seal source-eq refl | refl =
    done (seal-value Vᵛ)
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-⇒ c⊢ d⊢)
      source-eq target-eq =
    done (conceal-fun Vᵛ)
  conceal-value-progress-core {A = ＇ Y} typing V⊢ Vᵛ
      (⊢↓-∀ c⊢) () target-eq
  conceal-value-progress-core {A = ‵ ι} typing V⊢ Vᵛ
      (⊢↓-∀ c⊢) () target-eq
  conceal-value-progress-core {A = ★} typing V⊢ Vᵛ
      (⊢↓-∀ c⊢) () target-eq
  conceal-value-progress-core {A = A ⇒ D} typing V⊢ Vᵛ
      (⊢↓-∀ c⊢) () target-eq
  conceal-value-progress-core {A = `∀ A} typing V⊢ Vᵛ (⊢↓-∀ c⊢)
      refl refl with canonical-∀ Vᵛ V⊢
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-Λ Wᵛ = step (β-conceal-∀ Wᵛ)
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-cast Wᵛ =
    gap-∀-conceal-cast Vᵛ (nla-cast Wᵛ) typing
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-gen Wᵛ A≠★ safe =
    gap-∀-conceal-cast Vᵛ (nla-gen Wᵛ A≠★ safe) typing
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-adapter Wᵛ head neq =
    gap-∀-conceal-cast Vᵛ (nla-adapter Wᵛ head neq) typing
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-adapter-region Wᵛ head X∈E =
    gap-∀-conceal-cast Vᵛ (nla-adapter-region Wᵛ head X∈E) typing
  conceal-value-progress-core {A = ＇ Y} typing V⊢ Vᵛ
      (⊢id↓ atom) refl refl =
    finish-id-conceal (＇ Y) typing Vᵛ (canonical-atom (＇ _) Vᵛ V⊢)
  conceal-value-progress-core {A = ‵ ι} typing V⊢ Vᵛ
      (⊢id↓ atom) refl refl =
    finish-id-conceal (‵ ι) typing Vᵛ (canonical-atom (‵ ι) Vᵛ V⊢)
  conceal-value-progress-core {A = ★} typing V⊢ Vᵛ
      (⊢id↓ atom) refl refl =
    finish-id-conceal ★ typing Vᵛ (canonical-atom ★ Vᵛ V⊢)
  conceal-value-progress-core {A = A ⇒ D} typing V⊢ Vᵛ (⊢id↓ atom)
      source-eq target-eq =
    ⊥-elim (atom-not-⇒ atom source-eq)
  conceal-value-progress-core {A = `∀ A} typing V⊢ Vᵛ (⊢id↓ atom)
      source-eq target-eq =
    ⊥-elim (atom-not-∀ atom source-eq)

  conceal-value-progress : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {V : Term Θ Δ}
      {B : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal}
    → Ψ ∣ [] ⊢ V ↓[ X ≔ α ] c ⦂ B
    → Value V
    → Progress Ψ (V ↓[ X ≔ α ] c)
  conceal-value-progress {Ψ = Ψ} {V = V} {X = X}
      typing@(⊢conceal {A = A} X-live α-eq c⊢ V⊢) Vᵛ =
    conceal-value-progress-core typing pocket⊢ Vᵛ c⊢ refl refl
    where
    pocket⊢ : Ψ ,end[ X ] ∣ [] ⊢ V ⦂ A
    pocket⊢ = subst≡ (λ Γ → Ψ ,end[ X ] ∣ Γ ⊢ V ⦂ A)
      (truncateForEnd-empty X) V⊢

  progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ Δ} {A : Ty Δ}
    → Ψ ∣ [] ⊢ M ⦂ A
    → Progress Ψ M
  progress (⊢` ())
  progress (⊢ƛ M⊢) = done (ƛ _ ˙ _)
  progress typing@(⊢· L⊢ M⊢) with progress L⊢
  progress typing@(⊢· L⊢ M⊢) | step L—→L′ =
    step (ξ-·₁ L—→L′)
  progress typing@(⊢· L⊢ M⊢) | failed = step blame-·₁
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ with progress M⊢
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | step M—→M′ =
    step (ξ-·₂ Lᵛ M—→M′)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | failed =
    step (blame-·₂ Lᵛ)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ
      with canonical-⇒ Lᵛ L⊢
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ | cf-ƛ =
    step (β Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ
      | cf-cast Wᵛ = step (β-⇒ Wᵛ Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ
      | cf-reveal Wᵛ = step (β-reveal-⇒ Wᵛ Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ
      | cf-conceal Wᵛ = step (β-conceal-⇒ Wᵛ Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ
      | cf-adapter Wᵛ head neq =
    gap-adapter-⊕ (adapter-· Lᵛ adapter-head Mᵛ typing)
  progress typing@(⊢· L⊢ M⊢) | done Lᵛ | done Mᵛ
      | cf-adapter-region Wᵛ head X∈E =
    gap-adapter-⊕ (adapter-· Lᵛ adapter-region-head Mᵛ typing)
  progress typing@(⊢Λ M⊢) with progress M⊢
  progress typing@(⊢Λ M⊢) | step M—→M′ = step (ξ-Λ M—→M′)
  progress typing@(⊢Λ M⊢) | done Mᵛ = done (Λ Mᵛ)
  progress typing@(⊢Λ M⊢) | failed = step blame-Λ
  progress typing@(⊢⦂∀ F⊢) with progress F⊢
  progress typing@(⊢⦂∀ F⊢) | step F—→F′ =
    step (ξ-• F—→F′)
  progress typing@(⊢⦂∀ F⊢) | failed = step blame-•
  progress typing@(⊢⦂∀ F⊢) | done Fᵛ with canonical-∀ Fᵛ F⊢
  progress typing@(⊢⦂∀ F⊢) | done Fᵛ | ca-Λ Vᵛ = step (β-Λ Vᵛ)
  progress typing@(⊢⦂∀ F⊢@(⊢⟨⟩ V⊢ (∀ᶜ c))) | done Fᵛ
      | ca-cast Vᵛ = step (β-∀ Vᵛ refl)
  progress typing@(⊢⦂∀ F⊢@(⊢⟨⟩ V⊢ ((gen c) A≠★)))
      | done Fᵛ
      | ca-gen Vᵛ A≠★ safe = step (β-gen Vᵛ A≠★ safe)
  progress typing@(⊢⦂∀ F⊢) | done Fᵛ | ca-adapter Vᵛ head neq =
    gap-adapter-⊕ (adapter-• Fᵛ adapter-head typing)
  progress typing@(⊢⦂∀ F⊢) | done Fᵛ
      | ca-adapter-region Vᵛ head X∈E =
    gap-adapter-⊕ (adapter-• Fᵛ adapter-region-head typing)
  progress (⊢$ κ) = done ($ κ)
  progress typing@(⊢⊕ op L⊢ M⊢) with progress L⊢
  progress typing@(⊢⊕ op L⊢ M⊢) | step L—→L′ =
    step (ξ-⊕₁ L—→L′)
  progress typing@(⊢⊕ op L⊢ M⊢) | failed = step blame-⊕₁
  progress typing@(⊢⊕ op L⊢ M⊢) | done Lᵛ with progress M⊢
  progress typing@(⊢⊕ op L⊢ M⊢) | done Lᵛ | step M—→M′ =
    step (ξ-⊕₂ Lᵛ M—→M′)
  progress typing@(⊢⊕ op L⊢ M⊢) | done Lᵛ | failed =
    step (blame-⊕₂ Lᵛ)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done Lᵛ | done Mᵛ
      with canonical-ℕ Lᵛ L⊢ | canonical-ℕ Mᵛ M⊢
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done Lᵛ | done Mᵛ
      | nat-constant | nat-constant = step (δ-⊕ δ-add)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done Lᵛ | done Mᵛ
      | nat-boundary Lᵇ | nat-constant =
    gap-adapter-⊕
      (boundary-⊕ Lᵛ Mᵛ (inj₁ (Lᵇ , value-no-step Lᵛ)) typing)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done Lᵛ | done Mᵛ
      | nat-constant | nat-boundary Mᵇ =
    gap-adapter-⊕
      (boundary-⊕ Lᵛ Mᵛ (inj₂ (Mᵇ , value-no-step Mᵛ)) typing)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done Lᵛ | done Mᵛ
      | nat-boundary Lᵇ | nat-boundary Mᵇ =
    gap-adapter-⊕
      (boundary-⊕ Lᵛ Mᵛ (inj₁ (Lᵇ , value-no-step Lᵛ)) typing)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done Lᵛ | done Mᵛ
      with canonical-𝔹 Lᵛ L⊢ | canonical-𝔹 Mᵛ M⊢
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done Lᵛ | done Mᵛ
      | bool-constant | bool-constant = step (δ-⊕ δ-and)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done Lᵛ | done Mᵛ
      | bool-boundary Lᵇ | bool-constant =
    gap-adapter-⊕
      (boundary-⊕ Lᵛ Mᵛ (inj₁ (Lᵇ , value-no-step Lᵛ)) typing)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done Lᵛ | done Mᵛ
      | bool-constant | bool-boundary Mᵇ =
    gap-adapter-⊕
      (boundary-⊕ Lᵛ Mᵛ (inj₂ (Mᵇ , value-no-step Mᵛ)) typing)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done Lᵛ | done Mᵛ
      | bool-boundary Lᵇ | bool-boundary Mᵇ =
    gap-adapter-⊕
      (boundary-⊕ Lᵛ Mᵛ (inj₁ (Lᵇ , value-no-step Lᵛ)) typing)
  progress typing@(⊢⟨⟩ M⊢ c) with progress M⊢
  progress typing@(⊢⟨⟩ M⊢ c) | step M—→M′ =
    step (ξ-⟨⟩ M—→M′)
  progress typing@(⊢⟨⟩ M⊢ c) | failed = step blame-⟨⟩
  progress typing@(⊢⟨⟩ M⊢ c) | done Mᵛ =
    cast-value-progress M⊢ Mᵛ c
  progress typing@(⊢ν M⊢) with progress M⊢
  progress typing@(⊢ν M⊢) | step M—→M′ = step (ξ-ν M—→M′)
  progress typing@(⊢ν M⊢) | failed = step blame-ν
  progress typing@(⊢ν (⊢$ κ)) | done ($ .κ) = step const-ν
  progress typing@(⊢ν (⊢⟨⟩ V⊢ c)) | done (inject Vᵛ) =
    step (tag-out Vᵛ)
  progress typing@(⊢ν (⊢⟨⟩ V⊢ c)) | done (Vᵛ 《 inert 》) =
    step (inert-cast-out Vᵛ inert)
  progress typing@(⊢ν (⊢ƛ N⊢)) | done (ƛ A ˙ N) = step NUWRAP
  progress typing@(⊢ν (⊢Λ V⊢)) | done (Λ Vᵛ) = step NUTYWRAP
  progress typing@(⊢ν M⊢) | done Vᵛ@(seal-value Wᵛ) =
    gap-adapter-⊕ (ν-immobile Vᵛ seal-head typing)
  progress typing@(⊢ν M⊢) | done Vᵛ@(reveal-fun Wᵛ nonλ) =
    gap-adapter-⊕ (ν-immobile Vᵛ reveal-fun-head typing)
  progress typing@(⊢ν M⊢) | done Vᵛ@(conceal-fun Wᵛ) =
    gap-adapter-⊕ (ν-immobile Vᵛ conceal-fun-head typing)
  progress typing@(⊢ν M⊢) | done Vᵛ@(adapter Wᵛ head neq) =
    gap-adapter-⊕ (ν-immobile Vᵛ adapter-head typing)
  progress typing@(⊢ν M⊢) | done Vᵛ@(adapter-region Wᵛ head X∈A) =
    gap-adapter-⊕ (ν-immobile Vᵛ adapter-region-head typing)
  progress typing@(⊢reveal α-eq c⊢ M⊢) with progress M⊢
  progress typing@(⊢reveal α-eq c⊢ M⊢) | step M—→M′ =
    step (ξ-reveal M—→M′)
  progress typing@(⊢reveal α-eq c⊢ M⊢) | failed = step blame-reveal
  progress typing@(⊢reveal α-eq c⊢ M⊢) | done Mᵛ =
    reveal-value-progress typing Mᵛ
  progress typing@(⊢conceal {Ψ = Ψ} {M = M} {A = A} {Y = Y}
      X-live α-eq c⊢ M⊢)
      with progress (subst≡ (λ Γ → Ψ ,end[ Y ] ∣ Γ ⊢ M ⦂ A)
        (truncateForEnd-empty Y) M⊢)
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) | step M—→M′ =
    step (ξ-conceal M—→M′)
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) | failed =
    step blame-conceal
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) | done Mᵛ =
    conceal-value-progress typing Mᵛ
  progress ⊢blame = failed

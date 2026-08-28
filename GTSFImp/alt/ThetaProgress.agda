module alt.ThetaProgress where

-- File Charter:
--   * Proves closed-term progress from four explicit gap-family interfaces.
--   * Supplies total canonical forms and an indexed account of every residual
--     blocked eliminator; no unresolved obligation is hidden in the assembler.
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
    → Result M
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
    → Result V
      ---------------------------------------
    → CanonicalFun (V ↑[ X ≔ α ] (c ↦↑ d))

  cf-conceal : ∀ {Θ Δ} {V : Term Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal} {d : Conceal}
    → Value V
      -------------------------------------------------
    → CanonicalFun {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] (c ↦↓ d))

  cf-adapter : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Result M
    → X ∈ᵗ A
      -------------------------------------------------
    → CanonicalFun ((ν[ A ] M) ↑[ X ≔ α ] unseal)

data CanonicalAll : ∀ {Θ Δ} → Term Θ Δ → Set where
  ca-Λ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
    → Result V
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

  ca-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
    → Result V
    → RevealValue V X α (`∀↑ c)
      --------------------------------------
    → CanonicalAll (V ↑[ X ≔ α ] `∀↑ c)

  ca-adapter : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Result M
    → X ∈ᵗ A
      -------------------------------------------------
    → CanonicalAll ((ν[ A ] M) ↑[ X ≔ α ] unseal)

data CanonicalStar : ∀ {Θ Δ} → Term Θ Δ → Set where
  cs-tag : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
      {Gᵍ : Ground G} ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      ----------------------------------------------------
    → CanonicalStar (V ⟨ _! ⦃ Gᵍ ⦄ (idᵍ {μ = μ} Gᵍ) ⟩)

  cs-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
    → Result V
    → RevealValue V X α c
      --------------------------------
    → CanonicalStar (V ↑[ X ≔ α ] c)

  cs-conceal : ∀ {Θ Δ} {V : Term Θ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ}
    → Value V
    → ConcealValue V id↓
      --------------------------------------------
    → CanonicalStar {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] id↓)

data CanonicalBase : ∀ {Θ Δ} → Term Θ Δ → Set where
  cb-ℕ : ∀ {Θ Δ n}
      ---------------------------
    → CanonicalBase {Θ = Θ} {Δ = Δ} ($ (κℕ n))

  cb-𝔹 : ∀ {Θ Δ b}
      ---------------------------
    → CanonicalBase {Θ = Θ} {Δ = Δ} ($ (κ𝔹 b))

  cb-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Result V
    → RevealValue V X α c
      --------------------------------
    → CanonicalBase (V ↑[ X ≔ α ] c)

  cb-conceal : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Value V
    → ConcealValue V c
      ------------------------------------------------
    → CanonicalBase {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] c)

data BoundaryBase : ∀ {Θ Δ} → Term Θ Δ → Set where
  bb-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Result V
    → RevealValue V X α c
      --------------------------------
    → BoundaryBase (V ↑[ X ≔ α ] c)

  bb-conceal : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → Value V
    → ConcealValue V c
      ------------------------------------------------
    → BoundaryBase {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] c)

data BoundaryValue : ∀ {Θ Δ} → Term Θ Δ → Set where
  bv-reveal-fun : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal} {d : Reveal}
    → Result V
    → Value V
      -------------------------------------------------
    → BoundaryValue (V ↑[ X ≔ α ] (c ↦↑ d))

  bv-reveal-adapter : ∀ {Θ Δ} {R : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Result R
    → ¬ (X ≡ Y × α ≡ β)
      ------------------------------------------------------------
    → BoundaryValue ((R ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  bv-reveal-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal}
    → Result M
    → X ∈ᵗ A
      -------------------------------------------------
    → BoundaryValue ((ν[ A ] M) ↑[ X ≔ α ] c)

  bv-conceal-fun : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal} {d : Conceal}
    → Value V
      -------------------------------------------------
    → BoundaryValue { Θ = Θ } { Δ = suc Δ }
        (V ↓[ X ≔ α ] (c ↦↓ d))

  bv-conceal-id : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Value V
    → CanonicalInterior V
      -------------------------------------------------
    → BoundaryValue {Θ = Θ} {Δ = suc Δ}
        (V ↓[ X ≔ α ] id↓)

data CanonicalAtom : ∀ {Θ Δ} → Term Θ Δ → Set where
  atom-constant : ∀ {Θ Δ κ}
      ---------------------------------
    → CanonicalAtom {Θ = Θ} {Δ = Δ} ($ κ)

  atom-interior : ∀ {Θ Δ} {V : Term Θ Δ}
    → CanonicalInterior V
      -----------------------
    → CanonicalAtom V

  atom-boundary : ∀ {Θ Δ} {V : Term Θ Δ}
    → BoundaryValue V
      -------------------
    → CanonicalAtom V

data NonSealInterior : ∀ {Θ Δ} → Term Θ Δ → Set where
  nsi-tagged : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ}
      {G : Ty Δ} ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
      ----------------------------------------------------
    → NonSealInterior (V ⟨ _! ⦃ Gᵍ ⦄ (idᵍ Gᵍ) ⟩)

  nsi-delimited : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → CanonicalInterior V
      -------------------------------------------------
    → NonSealInterior (V ↑[ X ≔ α ] id↑)

data ConcealBoundary : ∀ {Θ Δ} → Term Θ Δ → Set where
  conceal-boundary : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
    → BoundaryValue V
      -------------------------------------------------
    → ConcealBoundary { Θ = Θ } { Δ = suc Δ }
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

  nla-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Result V
    → RevealValue V X α (`∀↑ c)
      --------------------------------------
    → NonLambdaAll (V ↑[ X ≔ α ] `∀↑ c)

  nla-adapter : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Result M
    → X ∈ᵗ A
      -------------------------------------------------
    → NonLambdaAll ((ν[ A ] M) ↑[ X ≔ α ] unseal)

data BlockedElimination {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) :
    Term Θ Δ → Set where
  adapter-· : ∀ {B : Ty Δ} {E : Ty (suc Δ)}
      {M : Term (suc Θ) (suc Δ)}
      {V : Term Θ Δ} {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Result M
    → X ∈ᵗ E
    → Value V
    → Ψ ∣ [] ⊢ ((ν[ E ] M) ↑[ X ≔ α ] unseal) · V ⦂ B
      ------------------------------------------------------------
    → BlockedElimination Ψ
        (((ν[ E ] M) ↑[ X ≔ α ] unseal) · V)

  adapter-• : ∀ {E : Ty (suc Δ)} {C : Ty Δ} {B : Ty (suc Δ)}
      {M : Term (suc Θ) (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Result M
    → X ∈ᵗ E
    → Ψ ∣ [] ⊢ ((ν[ E ] M) ↑[ X ≔ α ] c)
        ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
      ------------------------------------------------------------
    → BlockedElimination Ψ
        (((ν[ E ] M) ↑[ X ≔ α ] c) ⦂∀ B [ C ])

  adapter-project : ∀ {E : Ty (suc Δ)}
      {M : Term (suc Θ) (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
      {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Result M
    → X ∈ᵗ E
    → Ψ ∣ [] ⊢ ((ν[ E ] M) ↑[ X ≔ α ] unseal)
        ⟨ ？ (idᵍ Gᵍ) ⟩ ⦂ G
      ------------------------------------------------------------
    → BlockedElimination Ψ
        (((ν[ E ] M) ↑[ X ≔ α ] unseal) ⟨ ？ (idᵍ Gᵍ) ⟩)

  region-Λ-• : ∀ {E : Ty (suc Δ)} {C : Ty Δ} {B : Ty (suc Δ)}
      {M : Term (suc Θ) (suc Δ)}
    → Result M
    → Ψ ∣ [] ⊢ (Λ (ν[ E ] M)) ⦂∀ B [ C ] ⦂ B [ C ]ᵗ
      ------------------------------------------------------------
    → BlockedElimination Ψ ((Λ (ν[ E ] M)) ⦂∀ B [ C ])

  boundary-⊕ : ∀ {op V W}
    → Value V
    → Value W
    → (BoundaryBase V ⊎ BoundaryBase W)
    → Ψ ∣ [] ⊢ V ⊕[ op ] W ⦂ primResultTy op
      ------------------------------------------------------------
    → BlockedElimination Ψ (V ⊕[ op ] W)

  atomic-reveal : ∀ {A : Ty (suc Δ)} {B : Ty Δ}
      {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Atom A
    → BoundaryValue V
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] c ⦂ B
      ------------------------------------------------------------
    → BlockedElimination Ψ (V ↑[ X ≔ α ] c)

  unseal-interior : ∀ {B : Ty Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → NonSealInterior V
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] unseal ⦂ B
      ------------------------------------------------------------
    → BlockedElimination Ψ (V ↑[ X ≔ α ] unseal)

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

canonical-adapter-⇒ : ∀ {Θ Δ} {C A B : Ty Δ}
    {E S T : Ty (suc Δ)} {M : Term (suc Θ) (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → Result M
  → X ∈ᵗ E
  → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ S ↝ T
  → T ≡ wkᵗ X (A ⇒ B)
  → CanonicalFun ((ν[ E ] M) ↑[ X ≔ α ] c)
canonical-adapter-⇒ {X = X} Rʳ X∈E ⊢unseal eq
    with wkᵗ-injective X eq
canonical-adapter-⇒ Rʳ X∈E ⊢unseal eq | refl =
  cf-adapter Rʳ X∈E
canonical-adapter-⇒ Rʳ X∈E (⊢↑-⇒ c⊢ d⊢) refl =
  cf-reveal (result-ν Rʳ)
canonical-adapter-⇒ Rʳ X∈E (⊢↑-∀ c⊢) ()
canonical-adapter-⇒ Rʳ X∈E (⊢id↑ atom) eq =
  ⊥-elim (atom-not-⇒ atom eq)

canonical-adapter-∀ : ∀ {Θ Δ} {C : Ty Δ} {B : Ty (suc Δ)}
    {E S T : Ty (suc Δ)} {M : Term (suc Θ) (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → Result M
  → X ∈ᵗ E
  → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ S ↝ T
  → T ≡ wkᵗ X (`∀ B)
  → CanonicalAll ((ν[ E ] M) ↑[ X ≔ α ] c)
canonical-adapter-∀ {X = X} Rʳ X∈E ⊢unseal eq
    with wkᵗ-injective X eq
canonical-adapter-∀ Rʳ X∈E ⊢unseal eq | refl =
  ca-adapter Rʳ X∈E
canonical-adapter-∀ Rʳ X∈E (⊢↑-⇒ c⊢ d⊢) ()
canonical-adapter-∀ Rʳ X∈E (⊢↑-∀ c⊢) refl =
  ca-reveal (result-ν Rʳ) (adapter-region Rʳ X∈E)
canonical-adapter-∀ Rʳ X∈E (⊢id↑ atom) eq =
  ⊥-elim (atom-not-∀ atom eq)

canonical-⇒ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A B : Ty Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → CanonicalFun V
canonical-⇒ (ƛ A ˙ N) (⊢ƛ V⊢) = cf-ƛ
canonical-⇒ (Λ Vʳ) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ ($ (κ𝔹 b)) ()
canonical-⇒ (Vᵛ 《 inj 》) ()
canonical-⇒ (Vᵛ 《 fun 》) (⊢⟨⟩ V⊢ (c ↦ d)) = cf-cast Vᵛ
canonical-⇒ (Vᵛ 《 all 》) ()
canonical-⇒ (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-⇒ (Vʳ ↑[ X ≔ α ] fun Vᵛ) typing =
  cf-reveal Vʳ
canonical-⇒ (Vʳ ↑[ X ≔ α ] delimiter Vᶜ)
    (⊢reveal α-eq (⊢id↑ ()) V⊢)
canonical-⇒ (Vʳ ↑[ X ≔ α ] adapter Rʳ pair≢)
    (⊢reveal α-eq (⊢id↑ ()) V⊢)
canonical-⇒
    (result-ν Rʳ ↑[ X ≔ α ] adapter-region Rʳ′ X∈E)
    (⊢reveal α-eq c⊢ V⊢) =
  canonical-adapter-⇒ Rʳ′ X∈E c⊢ refl
canonical-⇒ (Vᵛ ↓[ X ≔ α ] sealᵥ)
    (⊢conceal X-live α-eq () V⊢)
canonical-⇒ (Vᵛ ↓[ X ≔ α ] fun) typing =
  cf-conceal Vᵛ
canonical-⇒ (Vᵛ ↓[ X ≔ α ] delimiter Vᶜ)
    (⊢conceal X-live α-eq c⊢ V⊢) =
  ⊥-elim (no-id-conceal-⇒ c⊢ refl)

canonical-∀ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty (suc Δ)}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ `∀ A
  → CanonicalAll V
canonical-∀ (ƛ A ˙ N) ()
canonical-∀ (Λ Vʳ) (⊢Λ body V⊢) = ca-Λ Vʳ
canonical-∀ ($ (κℕ n)) ()
canonical-∀ ($ (κ𝔹 b)) ()
canonical-∀ (Vᵛ 《 inj 》) ()
canonical-∀ (Vᵛ 《 fun 》) ()
canonical-∀ (Vᵛ 《 all 》) (⊢⟨⟩ V⊢ (∀ᶜ c)) = ca-cast Vᵛ
canonical-∀ (Vᵛ 《 genᵥ A≠★ safe 》)
    (⊢⟨⟩ V⊢ ((gen c) A≠★)) =
  ca-gen Vᵛ A≠★ safe
canonical-∀ (Vʳ ↑[ X ≔ α ] fun Vᵛ)
    (⊢reveal α-eq c⊢ V⊢) =
  ⊥-elim (no-fun-reveal-∀ c⊢ refl)
canonical-∀ (Vʳ ↑[ X ≔ α ] delimiter Vᶜ)
    (⊢reveal α-eq c⊢ V⊢) =
  ⊥-elim (no-id-reveal-∀ c⊢ refl)
canonical-∀ (Vʳ ↑[ X ≔ α ] adapter Rʳ pair≢)
    (⊢reveal α-eq c⊢ V⊢) =
  ⊥-elim (no-id-reveal-∀ c⊢ refl)
canonical-∀
    (result-ν Rʳ ↑[ X ≔ α ] adapter-region Rʳ′ X∈E)
    (⊢reveal α-eq c⊢ V⊢) =
  canonical-adapter-∀ Rʳ′ X∈E c⊢ refl
canonical-∀ (Vᵛ ↓[ X ≔ α ] sealᵥ)
    (⊢conceal X-live α-eq () V⊢)
canonical-∀ (Vᵛ ↓[ X ≔ α ] fun)
    (⊢conceal X-live α-eq () V⊢)
canonical-∀ (Vᵛ ↓[ X ≔ α ] delimiter Vᶜ)
    (⊢conceal X-live α-eq c⊢ V⊢) =
  ⊥-elim (no-id-conceal-∀ c⊢ refl)

canonical-★ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ★
  → CanonicalStar V
canonical-★ (ƛ A ˙ N) ()
canonical-★ (Λ Vʳ) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ ($ (κ𝔹 b)) ()
canonical-★ (Vᵛ 《 inj 》) (⊢⟨⟩ V⊢ c) = cs-tag Vᵛ
canonical-★ (Vᵛ 《 fun 》) ()
canonical-★ (Vᵛ 《 all 》) ()
canonical-★ (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-★ (Vʳ ↑[ X ≔ α ] gate)
    (⊢reveal α-eq c⊢ V⊢) =
  cs-reveal Vʳ gate
canonical-★ (Vᵛ ↓[ X ≔ α ] sealᵥ)
    (⊢conceal X-live α-eq () V⊢)
canonical-★ (Vᵛ ↓[ X ≔ α ] fun)
    (⊢conceal X-live α-eq () V⊢)
canonical-★ (Vᵛ ↓[ X ≔ α ] delimiter Vᶜ) typing =
  cs-conceal Vᵛ (delimiter Vᶜ)

canonical-base : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {ι : Base}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ‵ ι
  → CanonicalBase V
canonical-base (ƛ A ˙ N) ()
canonical-base (Λ Vʳ) ()
canonical-base ($ (κℕ n)) (⊢$ (κℕ .n)) = cb-ℕ
canonical-base ($ (κ𝔹 b)) (⊢$ (κ𝔹 .b)) = cb-𝔹
canonical-base (Vᵛ 《 inj 》) ()
canonical-base (Vᵛ 《 fun 》) ()
canonical-base (Vᵛ 《 all 》) ()
canonical-base (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-base (Vʳ ↑[ X ≔ α ] gate)
    (⊢reveal α-eq c⊢ V⊢) =
  cb-reveal Vʳ gate
canonical-base (Vᵛ ↓[ X ≔ α ] sealᵥ)
    (⊢conceal X-live α-eq () V⊢)
canonical-base (Vᵛ ↓[ X ≔ α ] fun)
    (⊢conceal X-live α-eq () V⊢)
canonical-base (Vᵛ ↓[ X ≔ α ] delimiter Vᶜ) typing =
  cb-conceal Vᵛ (delimiter Vᶜ)

atom-reveal : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
  → Result V
  → RevealValue V X α c
  → CanonicalAtom (V ↑[ X ≔ α ] c)
atom-reveal Vʳ (fun Vᵛ) = atom-boundary (bv-reveal-fun Vʳ Vᵛ)
atom-reveal Vʳ (delimiter Vᶜ) = atom-interior (delimited Vᶜ _ _)
atom-reveal Vʳ (adapter Rʳ pair≢) =
  atom-boundary (bv-reveal-adapter Rʳ pair≢)
atom-reveal (result-ν Vʳ) (adapter-region Rʳ X∈A) =
  atom-boundary (bv-reveal-region Rʳ X∈A)

atom-conceal : ∀ {Θ Δ} {V : Term Θ Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Conceal}
  → Value V
  → ConcealValue V c
  → CanonicalAtom { Θ = Θ } { Δ = suc Δ }
      (V ↓[ X ≔ α ] c)
atom-conceal Vᵛ sealᵥ = atom-interior (sealed Vᵛ _ _)
atom-conceal Vᵛ fun = atom-boundary (bv-conceal-fun Vᵛ)
atom-conceal Vᵛ (delimiter Vᶜ) =
  atom-boundary (bv-conceal-id Vᵛ Vᶜ)

canonical-variable : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {Y : TyVar Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ＇ Y
  → CanonicalAtom V
canonical-variable (ƛ A ˙ N) ()
canonical-variable (Λ Vʳ) ()
canonical-variable ($ (κℕ n)) ()
canonical-variable ($ (κ𝔹 b)) ()
canonical-variable (Vᵛ 《 inj 》) ()
canonical-variable (Vᵛ 《 fun 》) ()
canonical-variable (Vᵛ 《 all 》) ()
canonical-variable (Vᵛ 《 genᵥ A≠★ safe 》) ()
canonical-variable (Vʳ ↑[ X ≔ α ] gate) typing =
  atom-reveal Vʳ gate
canonical-variable (Vᵛ ↓[ X ≔ α ] gate) typing =
  atom-conceal Vᵛ gate

canonical-atom : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {V : Term Θ Δ} {A : Ty Δ}
  → Atom A
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ A
  → CanonicalAtom V
canonical-atom (＇ X) Vᵛ V⊢ = canonical-variable Vᵛ V⊢
canonical-atom (‵ `ℕ) Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-atom (‵ `ℕ) Vᵛ V⊢ | cb-ℕ = atom-constant
canonical-atom (‵ `ℕ) Vᵛ V⊢ | cb-reveal Rʳ gate =
  atom-reveal Rʳ gate
canonical-atom (‵ `ℕ) Vᵛ V⊢ | cb-conceal Wᵛ gate =
  atom-conceal Wᵛ gate
canonical-atom (‵ `𝔹) Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-atom (‵ `𝔹) Vᵛ V⊢ | cb-𝔹 = atom-constant
canonical-atom (‵ `𝔹) Vᵛ V⊢ | cb-reveal Rʳ gate =
  atom-reveal Rʳ gate
canonical-atom (‵ `𝔹) Vᵛ V⊢ | cb-conceal Wᵛ gate =
  atom-conceal Wᵛ gate
canonical-atom ★ Vᵛ V⊢ with canonical-★ Vᵛ V⊢
canonical-atom ★ Vᵛ V⊢
    | cs-tag {G = G} {Gᵍ = Gᵍ} ⦃ G∼★ ⦄ ⦃ Gns ⦄ Wᵛ =
  atom-interior
    (tagged ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Gns = Gns ⦄ Wᵛ)
canonical-atom ★ Vᵛ V⊢ | cs-reveal Rʳ gate =
  atom-reveal Rʳ gate
canonical-atom ★ Vᵛ V⊢ | cs-conceal Wᵛ gate =
  atom-conceal Wᵛ gate

constant-not-variable : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {κ : Const} {X : TyVar Δ}
  → Ψ ∣ [] ⊢ $ κ ⦂ ＇ X
  → ⊥
constant-not-variable {κ = κℕ n} ()
constant-not-variable {κ = κ𝔹 b} ()

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
canonical-ℕ Vᵛ V⊢ | cb-reveal Rʳ gate =
  nat-boundary (bb-reveal Rʳ gate)
canonical-ℕ Vᵛ V⊢ | cb-conceal Wᵛ gate =
  nat-boundary (bb-conceal Wᵛ gate)

canonical-𝔹 : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {V : Term Θ Δ}
  → Value V
  → Ψ ∣ [] ⊢ V ⦂ ‵ `𝔹
  → CanonicalBool V
canonical-𝔹 Vᵛ V⊢ with canonical-base Vᵛ V⊢
canonical-𝔹 ($ (κℕ n)) () | cb-ℕ
canonical-𝔹 Vᵛ V⊢ | cb-𝔹 = bool-constant
canonical-𝔹 Vᵛ V⊢ | cb-reveal Rʳ gate =
  bool-boundary (bb-reveal Rʳ gate)
canonical-𝔹 Vᵛ V⊢ | cb-conceal Wᵛ gate =
  bool-boundary (bb-conceal Wᵛ gate)

ΛBody-not-blame : ∀ {Θ Δ}
  → ΛBody (blame { Θ = Θ } { Δ = Δ })
  → ⊥
ΛBody-not-blame (body-result (result-val ()))

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
-- Progress modulo the four checked merge families
------------------------------------------------------------------------

module WithGaps
  -- Representative: `alt.probes.ProgressGaps.baseAdapter-gap-witness`.
  (gap-adapter-⊕ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ Δ}
    → BlockedElimination Ψ M
    → Progress Ψ M)
  -- Witness: `alt.probes.ProgressGaps.starConcealMerge-gap-witness`.
  (gap-★-project-conceal : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {μ : Env∼ (suc Δ)}
      {G : Ty (suc Δ)} {Gᵍ : Ground G}
      ⦃ ★∼G : μ ⊢★∼ G ⦄ ⦃ Gns : NonStar G ⦄
    → Value V
    → ConcealValue V id↓
    → Ψ ∣ [] ⊢ V ↓[ X ≔ α ] id↓ ⦂ ★
    → Progress Ψ ((V ↓[ X ≔ α ] id↓)
        ⟨ ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄
          (idᵍ { μ = μ } Gᵍ) ⦃ Gns ⦄ ⟩))
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

  star-project-reveal-progress-core : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ Δ σ} {V : Term Θ (suc Δ)}
      {C : Ty Δ} {A T : Ty (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
      {fresh : α ∉ᵛ σ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] c ⦂ ★
    → Result V
    → RevealValue V X α c
    → Ψ ,begin[ X ≔ α ]⟨ fresh ⟩ ∣ [] ⊢ V ⦂ A
    → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ A ↝ T
    → T ≡ wkᵗ X ★
    → Progress Ψ ((V ↑[ X ≔ α ] c)
        ⟨ ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄
          (idᵍ {μ = μ} Gᵍ) ⦃ Gns ⦄ ⟩)
  star-project-reveal-progress-core typing (result-ν Rʳ)
      (adapter-region Rʳ′ X∈E) V⊢ ⊢unseal target-eq =
    gap-adapter-⊕
      (adapter-project Rʳ′ X∈E (⊢⟨⟩ typing (？ (idᵍ _))))
  star-project-reveal-progress-core typing (result-val ())
      (adapter-region Rʳ′ X∈E) V⊢ ⊢unseal target-eq
  star-project-reveal-progress-core typing Rʳ gate V⊢
      (⊢↑-⇒ c⊢ d⊢) ()
  star-project-reveal-progress-core typing Rʳ gate V⊢
      (⊢↑-∀ c⊢) ()
  star-project-reveal-progress-core typing Rʳ gate V⊢
      (⊢id↑ (＇ Y)) ()
  star-project-reveal-progress-core typing Rʳ gate V⊢
      (⊢id↑ (‵ ι)) ()
  star-project-reveal-progress-core typing Rʳ gate V⊢
      (⊢id↑ ★) refl =
    step (★-project-reveal Rʳ)

  star-project-reveal-progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
      ⦃ Gns : NonStar G ⦄
    → Result V
    → RevealValue V X α c
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] c ⦂ ★
    → Progress Ψ ((V ↑[ X ≔ α ] c)
        ⟨ ？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄
          (idᵍ {μ = μ} Gᵍ) ⦃ Gns ⦄ ⟩)
  star-project-reveal-progress Rʳ gate
      typing@(⊢reveal α-eq c⊢ V⊢) =
    star-project-reveal-progress-core typing Rʳ gate V⊢ c⊢ refl

  cast-value-progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ Δ} {A B : Ty Δ} {μ : Env∼ Δ}
    → Ψ ∣ [] ⊢ V ⦂ A
    → Value V
    → (c : μ ⊢ A ∼ B)
    → Progress Ψ (V ⟨ c ⟩)
  cast-value-progress V⊢ Vᵛ (id a) = step (β-id Vᵛ)
  cast-value-progress V⊢ Vᵛ (c ↦ d) = done (result-val (Vᵛ 《 fun 》))
  cast-value-progress V⊢ Vᵛ (∀ᶜ c) =
    done (result-val (Vᵛ 《 all 》))
  cast-value-progress V⊢ Vᵛ
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄)
      with to-ground Gᵍ c
  cast-value-progress V⊢ Vᵛ
      (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ .(idᵍ Gᵍ) ⦃ Ans ⦄)
      | same =
    done (result-val
      (Vᵛ 《 inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
        ⦃ Gns = Ans ⦄ 》))
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
  cast-value-progress V⊢
      (Rʳ ↑[ X ≔ α ] gate)
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-reveal Rʳ′ gate′ =
    star-project-reveal-progress Rʳ gate V⊢
  cast-value-progress V⊢
      (Wᵛ ↓[ X ≔ α ] gate)
      (？_ {G = G} ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ .(idᵍ Gᵍ) ⦃ Bns ⦄)
      | same | cs-conceal Wᵛ′ gate′ =
    gap-★-project-conceal Wᵛ gate V⊢
  cast-value-progress V⊢ Vᵛ
      (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≠★) =
    step (β-inst Vᵛ B≠★)
  cast-value-progress V⊢ Vᵛ
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≠★) =
    done (result-val
      (Vᵛ 《 genᵥ A≠★ (theta-gen-safe c A≠★ Bnv z∈B) 》))
  cast-value-progress V⊢ Vᵛ bot-elim =
    gap-adapter-⊕ (bottom-cast Vᵛ (⊢⟨⟩ V⊢ bot-elim))
  cast-value-progress V⊢ Vᵛ bot-intro = step (blame-bot-intro Vᵛ)

  finish-id-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {V : Term Θ (suc Δ)} {B : Ty Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Atom B
    → Ψ ∣ [] ⊢ V ↑[ X ≔ α ] id↑ ⦂ B
    → Value V
    → CanonicalAtom V
    → Progress Ψ (V ↑[ X ≔ α ] id↑)
  finish-id-reveal atom typing ($ κ) atom-constant = step id-reveal
  finish-id-reveal atom typing Vᵛ (atom-interior Vᶜ) =
    done (result-val (result-val Vᵛ ↑[ _ ≔ _ ] delimiter Vᶜ))
  finish-id-reveal {X = X} atom typing Vᵛ (atom-boundary boundary) =
    gap-adapter-⊕ (atomic-reveal (wk-atom X atom) boundary typing)

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
      | refl | atom-interior (tagged Wᵛ) =
    gap-adapter-⊕ (unseal-interior (nsi-tagged Wᵛ) typing)
  reveal-value-progress-core typing V⊢ Vᵛ ⊢unseal target-eq
      | refl | atom-interior (sealed Wᵛ Y γ) =
    step (conceal-reveal (result-val Wᵛ))
  reveal-value-progress-core typing V⊢ Vᵛ ⊢unseal target-eq
      | refl | atom-interior (delimited Wᶜ Y γ) =
    gap-adapter-⊕ (unseal-interior (nsi-delimited Wᶜ) typing)
  reveal-value-progress-core {X = X} typing V⊢ Vᵛ ⊢unseal target-eq
      | refl | atom-boundary boundary =
    gap-adapter-⊕ (atomic-reveal (＇ X) boundary typing)
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-⇒ c⊢ d⊢) target-eq =
    done (result-val (result-val Vᵛ ↑[ _ ≔ _ ] fun Vᵛ))
  reveal-value-progress-core {B = ＇ Y} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = ‵ ι} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = ★} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = B ⇒ D} typing V⊢ Vᵛ (⊢↑-∀ c⊢) ()
  reveal-value-progress-core {B = `∀ B} typing V⊢ Vᵛ
      (⊢↑-∀ c⊢) refl with canonical-∀ Vᵛ V⊢
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-Λ Rʳ =
    step (β-reveal-∀ Rʳ)
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-cast Wᵛ =
    gap-∀-reveal-cast Vᵛ (nla-cast Wᵛ) typing
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-gen Wᵛ A≠★ safe =
    gap-∀-reveal-cast Vᵛ (nla-gen Wᵛ A≠★ safe) typing
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-reveal Rʳ gate =
    gap-∀-reveal-cast Vᵛ (nla-reveal Rʳ gate) typing
  reveal-value-progress-core typing V⊢ Vᵛ (⊢↑-∀ c⊢) refl
      | ca-adapter Rʳ X∈E =
    gap-∀-reveal-cast Vᵛ (nla-adapter Rʳ X∈E) typing
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

  reveal-result-progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ (suc Δ)} {B : Ty Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c : Reveal}
    → Ψ ∣ [] ⊢ M ↑[ X ≔ α ] c ⦂ B
    → Result M
    → Progress Ψ (M ↑[ X ≔ α ] c)
  reveal-result-progress typing (result-val Vᵛ) =
    reveal-value-progress typing Vᵛ
  reveal-result-progress {X = X} typing (result-ν {A = E} Rʳ)
      with occurs? X E
  reveal-result-progress typing (result-ν Rʳ) | present X∈E =
    done (result-val
      (result-ν Rʳ ↑[ _ ≔ _ ] adapter-region Rʳ X∈E))
  reveal-result-progress typing (result-ν Rʳ) | absent X∉E
      with strengthenᵗ?-absent X∉E
  reveal-result-progress typing (result-ν Rʳ) | absent X∉E
      | E₀ , strengthens =
    step (float-reveal strengthens (result-ν Rʳ))

  finish-id-conceal : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {V : Term Θ Δ}
      {A : Ty Δ} {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Atom A
    → Ψ ∣ [] ⊢ V ↓[ X ≔ α ] id↓ ⦂ wkᵗ X A
    → Value V
    → CanonicalAtom V
    → Progress Ψ (V ↓[ X ≔ α ] id↓)
  finish-id-conceal atom typing ($ κ) atom-constant = step id-conceal
  finish-id-conceal atom typing Vᵛ (atom-interior Vᶜ) =
    done (result-val (Vᵛ ↓[ _ ≔ _ ] delimiter Vᶜ))
  finish-id-conceal atom typing Vᵛ (atom-boundary boundary) =
    gap-adapter-⊕ (atomic-conceal (conceal-boundary boundary) typing)

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
    done (result-val (Vᵛ ↓[ _ ≔ _ ] sealᵥ))
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-⇒ c⊢ d⊢)
      source-eq target-eq =
    done (result-val (Vᵛ ↓[ _ ≔ _ ] fun))
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
      | ca-Λ Rʳ =
    step (β-conceal-∀ Rʳ)
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-cast Wᵛ =
    gap-∀-conceal-cast Vᵛ (nla-cast Wᵛ) typing
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-gen Wᵛ A≠★ safe =
    gap-∀-conceal-cast Vᵛ (nla-gen Wᵛ A≠★ safe) typing
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-reveal Rʳ gate =
    gap-∀-conceal-cast Vᵛ (nla-reveal Rʳ gate) typing
  conceal-value-progress-core typing V⊢ Vᵛ (⊢↓-∀ c⊢) refl refl
      | ca-adapter Rʳ X∈E =
    gap-∀-conceal-cast Vᵛ (nla-adapter Rʳ X∈E) typing
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
  conceal-value-progress typing@(⊢conceal X-live α-eq c⊢ V⊢) Vᵛ =
    conceal-value-progress-core typing V⊢ Vᵛ c⊢ refl refl

  conceal-result-progress : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ (suc Δ) σ} {M : Term Θ Δ}
      {B : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Conceal}
    → Ψ ∣ [] ⊢ M ↓[ X ≔ α ] c ⦂ B
    → Result M
    → Progress Ψ (M ↓[ X ≔ α ] c)
  conceal-result-progress typing (result-val Vᵛ) =
    conceal-value-progress typing Vᵛ
  conceal-result-progress typing (result-ν Rʳ) =
    step (float-conceal (result-ν Rʳ))

  progress : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ Δ} {A : Ty Δ}
    → Ψ ∣ [] ⊢ M ⦂ A
    → Progress Ψ M
  progress (⊢` ())
  progress (⊢ƛ M⊢) = done (result-val (ƛ _ ˙ _))
  progress typing@(⊢· L⊢ M⊢) with progress L⊢
  progress typing@(⊢· L⊢ M⊢) | step L—→L′ =
    step (ξ-·₁ L—→L′)
  progress typing@(⊢· L⊢ M⊢) | failed = step blame-·₁
  progress typing@(⊢· L⊢ M⊢) | done (result-ν Rʳ) =
    step (float-·₁ (result-ν Rʳ))
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      with progress M⊢
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | step M—→M′ =
    step (ξ-·₂ Lᵛ M—→M′)
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ) | failed =
    step (blame-·₂ Lᵛ)
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-ν Rʳ) =
    step (float-·₂ Lᵛ (result-ν Rʳ))
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) with canonical-⇒ Lᵛ L⊢
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | cf-ƛ =
    step (β Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | cf-cast Wᵛ =
    step (β-⇒ Wᵛ Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | cf-reveal Rʳ =
    step (β-reveal-⇒ Rʳ Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | cf-conceal Wᵛ =
    step (β-conceal-⇒ (result-val Wᵛ) Mᵛ)
  progress typing@(⊢· L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | cf-adapter Rʳ X∈E =
    gap-adapter-⊕ (adapter-· Rʳ X∈E Mᵛ typing)
  progress typing@(⊢Λ body M⊢) with progress M⊢
  progress typing@(⊢Λ body M⊢) | step M—→M′ =
    step (ξ-Λ M—→M′)
  progress typing@(⊢Λ body M⊢) | done Rʳ =
    done (result-val (Λ Rʳ))
  progress typing@(⊢Λ body M⊢) | failed =
    ⊥-elim (ΛBody-not-blame body)
  progress typing@(⊢⦂∀ F⊢) with progress F⊢
  progress typing@(⊢⦂∀ F⊢) | step F—→F′ =
    step (ξ-• F—→F′)
  progress typing@(⊢⦂∀ F⊢) | failed = step blame-•
  progress typing@(⊢⦂∀ F⊢) | done (result-ν Rʳ) =
    step (float-• (result-ν Rʳ))
  progress typing@(⊢⦂∀ F⊢) | done (result-val Fᵛ)
      with canonical-∀ Fᵛ F⊢
  progress typing@(⊢⦂∀ F⊢) | done (result-val Fᵛ)
      | ca-Λ (result-val Vᵛ) =
    step (β-Λ Vᵛ)
  progress typing@(⊢⦂∀ F⊢) | done (result-val Fᵛ)
      | ca-Λ (result-ν Rʳ) =
    gap-adapter-⊕ (region-Λ-• Rʳ typing)
  progress typing@(⊢⦂∀ F⊢@(⊢⟨⟩ V⊢ (∀ᶜ c)))
      | done (result-val Fᵛ)
      | ca-cast Vᵛ =
    step (β-∀ Vᵛ refl)
  progress typing@(⊢⦂∀ F⊢@(⊢⟨⟩ V⊢ ((gen c) A≠★)))
      | done (result-val Fᵛ)
      | ca-gen Vᵛ A≠★ safe =
    step (β-gen Vᵛ A≠★ safe)
  progress typing@(⊢⦂∀ F⊢) | done (result-val Fᵛ)
      | ca-reveal (result-ν Rʳ) (adapter-region Rʳ′ X∈E) =
    gap-adapter-⊕ (adapter-• Rʳ′ X∈E typing)
  progress typing@(⊢⦂∀ F⊢) | done (result-val Fᵛ)
      | ca-adapter Rʳ X∈E =
    gap-adapter-⊕ (adapter-• Rʳ X∈E typing)
  progress (⊢$ κ) = done (result-val ($ κ))
  progress typing@(⊢⊕ addℕ L⊢ M⊢) with progress L⊢
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | step L—→L′ =
    step (ξ-⊕₁ L—→L′)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | failed = step blame-⊕₁
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-ν Rʳ) =
    step (float-⊕₁ (result-ν Rʳ))
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      with progress M⊢
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | step M—→M′ =
    step (ξ-⊕₂ Lᵛ M—→M′)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ) | failed =
    step (blame-⊕₂ Lᵛ)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-ν Rʳ) =
    step (float-⊕₂ Lᵛ (result-ν Rʳ))
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ)
      with canonical-ℕ Lᵛ L⊢ | canonical-ℕ Mᵛ M⊢
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | nat-constant | nat-constant =
    step (δ-⊕ δ-add)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | nat-boundary Lᵇ | nat-constant =
    gap-adapter-⊕ (boundary-⊕ Lᵛ Mᵛ (inj₁ Lᵇ) typing)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | nat-constant | nat-boundary Mᵇ =
    gap-adapter-⊕ (boundary-⊕ Lᵛ Mᵛ (inj₂ Mᵇ) typing)
  progress typing@(⊢⊕ addℕ L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | nat-boundary Lᵇ | nat-boundary Mᵇ =
    gap-adapter-⊕ (boundary-⊕ Lᵛ Mᵛ (inj₁ Lᵇ) typing)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) with progress L⊢
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | step L—→L′ =
    step (ξ-⊕₁ L—→L′)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | failed = step blame-⊕₁
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-ν Rʳ) =
    step (float-⊕₁ (result-ν Rʳ))
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      with progress M⊢
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | step M—→M′ =
    step (ξ-⊕₂ Lᵛ M—→M′)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ) | failed =
    step (blame-⊕₂ Lᵛ)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-ν Rʳ) =
    step (float-⊕₂ Lᵛ (result-ν Rʳ))
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ)
      with canonical-𝔹 Lᵛ L⊢ | canonical-𝔹 Mᵛ M⊢
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | bool-constant | bool-constant =
    step (δ-⊕ δ-and)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | bool-boundary Lᵇ | bool-constant =
    gap-adapter-⊕ (boundary-⊕ Lᵛ Mᵛ (inj₁ Lᵇ) typing)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | bool-constant | bool-boundary Mᵇ =
    gap-adapter-⊕ (boundary-⊕ Lᵛ Mᵛ (inj₂ Mᵇ) typing)
  progress typing@(⊢⊕ and𝔹 L⊢ M⊢) | done (result-val Lᵛ)
      | done (result-val Mᵛ) | bool-boundary Lᵇ | bool-boundary Mᵇ =
    gap-adapter-⊕ (boundary-⊕ Lᵛ Mᵛ (inj₁ Lᵇ) typing)
  progress typing@(⊢⟨⟩ M⊢ c) with progress M⊢
  progress typing@(⊢⟨⟩ M⊢ c) | step M—→M′ =
    step (ξ-⟨⟩ M—→M′)
  progress typing@(⊢⟨⟩ M⊢ c) | failed = step blame-⟨⟩
  progress typing@(⊢⟨⟩ M⊢ c) | done (result-ν Rʳ) =
    step (float-⟨⟩ (result-ν Rʳ))
  progress typing@(⊢⟨⟩ M⊢ c) | done (result-val Mᵛ) =
    cast-value-progress M⊢ Mᵛ c
  progress typing@(⊢ν M⊢) with progress M⊢
  progress typing@(⊢ν M⊢) | step M—→M′ = step (ξ-ν M—→M′)
  progress typing@(⊢ν M⊢) | failed = step blame-ν
  progress typing@(⊢ν M⊢) | done Rʳ = done (result-ν Rʳ)
  progress typing@(⊢reveal α-eq c⊢ M⊢) with progress M⊢
  progress typing@(⊢reveal α-eq c⊢ M⊢) | step M—→M′ =
    step (ξ-reveal M—→M′)
  progress typing@(⊢reveal α-eq c⊢ M⊢) | failed = step blame-reveal
  progress typing@(⊢reveal α-eq c⊢ M⊢) | done Rʳ =
    reveal-result-progress typing Rʳ
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) with progress M⊢
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) | step M—→M′ =
    step (ξ-conceal M—→M′)
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) | failed =
    step blame-conceal
  progress typing@(⊢conceal X-live α-eq c⊢ M⊢) | done Rʳ =
    conceal-result-progress typing Rʳ
  progress ⊢blame = failed

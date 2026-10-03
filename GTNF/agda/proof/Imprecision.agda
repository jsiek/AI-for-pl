module proof.Imprecision where

-- File Charter:
--   * UNIQUENESS OF TYPE-IMPRECISION DERIVATIONS, ported from
--     GTSFImp/proof/Imprecision.agda (`⊑-unique`).
--   * THE PORT DOES NOT GO THROUGH AS STATED.  GTNF's occurrence
--     relation `_∈ᵗ_` (Coercion) has overlapping `∈-⇒ˡ`/`∈-⇒ʳ` (GTSFImp's
--     `∈-fun-right` carries `X ∉ᵗ A`), so `0 ∈ᵗ A` is not a proposition
--     and neither is `∀⊑`'s premise.  `∈ᵗ-not-unique` and
--     `⊑-not-unique` are the checked counterexample
--         `∀X. X → X  ⊑  ★ → ★`
--     derived by `∀⊑` with the witness `∈-⇒ˡ ∈-var` or `∈-⇒ʳ ∈-var`.
--   * WHAT IS PROVED: uniqueness of every other side condition
--     (`∋ˡ-unique`, `Base-unique`, `NonVar-unique`, `NonStar-unique`),
--     the disjointness of the overlapping rules (`∀⊑∀-∀⊑-disjoint`,
--     `occurs-not-star`), and, in the module `Unique` parameterised by
--     irrelevance of `0 ∈ᵗ A`, `⊑-unique` and `⊑ᵂ-unique`.  Once
--     `_∈ᵗ_` (or `∀⊑`'s premise) is made propositional, instantiate
--     `Unique` with its uniqueness lemma.
--   * DISJOINTNESS BY ∀-FREE PATHS (not GTSFImp's WidenPath /
--     EndpointSpine): an occurrence of an `X⊑X` variable at path π of
--     the source reaches a variable at π in the target (`occ-same`); an
--     occurrence of an `X⊑★` variable absent from the target reaches a
--     `★` at π (`occ-star`).  `nodeAt` skips `∀`s, so `B` and
--     `⇑ᵗ (∀ B)` agree at every path.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

open import Types
open import Ctx using (_∋ˡ_:=_; here; there)
open import Coercion
  using (NonVar; nv-ℕ; nv-𝔹; nv-★; nv-⇒; nv-∀;
         NonStar; ns-var; ns-ℕ; ns-𝔹; ns-⇒; ns-∀;
         _∈ᵗ_; ∈-var; ∈-⇒ˡ; ∈-⇒ʳ; ∈-∀)
open import Imprecision
open import ImprecisionWorld using (World; _⊑ᵂ⟨_⟩_)

private
  variable
    μ : ImpEnv
    A B C : Ty
    X : ℕ

------------------------------------------------------------------------
-- Uniqueness of the side conditions
------------------------------------------------------------------------

∋ˡ-unique : ∀ {T : Set} {xs : List T} {i : ℕ} {x : T}
  → (p q : xs ∋ˡ i := x)
  → p ≡ q
∋ˡ-unique here here = refl
∋ˡ-unique (there p) (there q) = cong there (∋ˡ-unique p q)

∋ˡ-functional : ∀ {T : Set} {xs : List T} {i : ℕ} {x y : T}
  → xs ∋ˡ i := x
  → xs ∋ˡ i := y
  → x ≡ y
∋ˡ-functional here here = refl
∋ˡ-functional (there p) (there q) = ∋ˡ-functional p q

Base-unique : (p q : Base A) → p ≡ q
Base-unique base-ℕ base-ℕ = refl
Base-unique base-𝔹 base-𝔹 = refl

NonVar-unique : (p q : NonVar A) → p ≡ q
NonVar-unique nv-ℕ nv-ℕ = refl
NonVar-unique nv-𝔹 nv-𝔹 = refl
NonVar-unique nv-★ nv-★ = refl
NonVar-unique nv-⇒ nv-⇒ = refl
NonVar-unique nv-∀ nv-∀ = refl

NonStar-unique : (p q : NonStar A) → p ≡ q
NonStar-unique ns-var ns-var = refl
NonStar-unique ns-ℕ ns-ℕ = refl
NonStar-unique ns-𝔹 ns-𝔹 = refl
NonStar-unique ns-⇒ ns-⇒ = refl
NonStar-unique ns-∀ ns-∀ = refl

------------------------------------------------------------------------
-- The counterexample: occurrence evidence is not unique, hence
-- neither is imprecision evidence
------------------------------------------------------------------------

∈ᵗ-not-unique : ¬ (∀ {A} (i j : 0 ∈ᵗ A) → i ≡ j)
∈ᵗ-not-unique irr
    with irr {A = ` 0 ⇒ ` 0} (∈-⇒ˡ ∈-var) (∈-⇒ʳ ∈-var)
... | ()

-- ∀X. X → X  ⊑  ★ → ★, twice
private
  id⊑ : 0 ∈ᵗ (` 0 ⇒ ` 0) → [] ⊢ `∀ (` 0 ⇒ ` 0) ⊑ ★ ⇒ ★
  id⊑ i = ∀⊑ nv-⇒ i (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

⊑-not-unique : ¬ (∀ {μ A B} (p q : μ ⊢ A ⊑ B) → p ≡ q)
⊑-not-unique uniq
    with uniq (id⊑ (∈-⇒ˡ ∈-var)) (id⊑ (∈-⇒ʳ ∈-var))
... | ()

------------------------------------------------------------------------
-- Occurrences under renaming
------------------------------------------------------------------------

private
  suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

∈-renameᵗ : ∀ (ρ : Renameᵗ) (A : Ty) {X}
  → X ∈ᵗ renameᵗ ρ A
  → Σ[ Y ∈ ℕ ] (ρ Y ≡ X × Y ∈ᵗ A)
∈-renameᵗ ρ (` Y) ∈-var = Y , refl , ∈-var
∈-renameᵗ ρ (A ⇒ B) (∈-⇒ˡ i)
    with ∈-renameᵗ ρ A i
... | Y , eq , j = Y , eq , ∈-⇒ˡ j
∈-renameᵗ ρ (A ⇒ B) (∈-⇒ʳ i)
    with ∈-renameᵗ ρ B i
... | Y , eq , j = Y , eq , ∈-⇒ʳ j
∈-renameᵗ ρ (`∀ A) (∈-∀ i)
    with ∈-renameᵗ (extᵗ ρ) A i
... | zero , () , j
... | suc Y , eq , j = Y , suc-inj eq , ∈-∀ j

zero-∉-⇑ᵗ : ∀ A → ¬ (0 ∈ᵗ ⇑ᵗ A)
zero-∉-⇑ᵗ A i
    with ∈-renameᵗ suc A i
... | Y , () , j

suc-∈-⇑ᵗ : ∀ A → suc X ∈ᵗ ⇑ᵗ A → X ∈ᵗ A
suc-∈-⇑ᵗ A i
    with ∈-renameᵗ suc A i
... | Y , refl , j = j

------------------------------------------------------------------------
-- ∀-free paths
------------------------------------------------------------------------

data Dir : Set where
  ←d →d : Dir

Path : Set
Path = List Dir

-- `OccAt X A π`: X occurs free in A at the ∀-free path π
data OccAt : ℕ → Ty → Path → Set where
  occ-var : OccAt X (` X) []
  occ-⇒ˡ : ∀ {π} → OccAt X A π → OccAt X (A ⇒ B) (←d ∷ π)
  occ-⇒ʳ : ∀ {π} → OccAt X B π → OccAt X (A ⇒ B) (→d ∷ π)
  occ-∀ : ∀ {π} → OccAt (suc X) A π → OccAt X (`∀ A) π

∈→OccAt : X ∈ᵗ A → Σ[ π ∈ Path ] OccAt X A π
∈→OccAt ∈-var = [] , occ-var
∈→OccAt (∈-⇒ˡ i) with ∈→OccAt i
... | π , o = ←d ∷ π , occ-⇒ˡ o
∈→OccAt (∈-⇒ʳ i) with ∈→OccAt i
... | π , o = →d ∷ π , occ-⇒ʳ o
∈→OccAt (∈-∀ i) with ∈→OccAt i
... | π , o = π , occ-∀ o

-- the kind of node reached along a path; `∀` is skipped, `★` absorbs
data Kind : Set where
  kvar kbase k★ k⇒ knone : Kind

nodeAt : Ty → Path → Kind
nodeAt (` X) [] = kvar
nodeAt (` X) (d ∷ π) = knone
nodeAt `ℕ [] = kbase
nodeAt `ℕ (d ∷ π) = knone
nodeAt `𝔹 [] = kbase
nodeAt `𝔹 (d ∷ π) = knone
nodeAt ★ π = k★
nodeAt (A ⇒ B) [] = k⇒
nodeAt (A ⇒ B) (←d ∷ π) = nodeAt A π
nodeAt (A ⇒ B) (→d ∷ π) = nodeAt B π
nodeAt (`∀ A) π = nodeAt A π

nodeAt-renameᵗ : ∀ (ρ : Renameᵗ) A π
  → nodeAt (renameᵗ ρ A) π ≡ nodeAt A π
nodeAt-renameᵗ ρ (` X) [] = refl
nodeAt-renameᵗ ρ (` X) (d ∷ π) = refl
nodeAt-renameᵗ ρ `ℕ [] = refl
nodeAt-renameᵗ ρ `ℕ (d ∷ π) = refl
nodeAt-renameᵗ ρ `𝔹 [] = refl
nodeAt-renameᵗ ρ `𝔹 (d ∷ π) = refl
nodeAt-renameᵗ ρ ★ π = refl
nodeAt-renameᵗ ρ (A ⇒ B) [] = refl
nodeAt-renameᵗ ρ (A ⇒ B) (←d ∷ π) = nodeAt-renameᵗ ρ A π
nodeAt-renameᵗ ρ (A ⇒ B) (→d ∷ π) = nodeAt-renameᵗ ρ B π
nodeAt-renameᵗ ρ (`∀ A) π = nodeAt-renameᵗ (extᵗ ρ) A π

------------------------------------------------------------------------
-- Where occurrences go
------------------------------------------------------------------------

-- an `X⊑X` variable reaches a variable at the same path
occ-same : ∀ {π}
  → μ ∋ˡ X := X⊑X
  → OccAt X A π
  → μ ⊢ A ⊑ B
  → nodeAt B π ≡ kvar
occ-same h () ★⊑★
occ-same h () (ι⊑ι base-ℕ)
occ-same h () (ι⊑ι base-𝔹)
occ-same h occ-var X⊑X = refl
occ-same h (occ-⇒ˡ o) (⇒⊑⇒ p q) = occ-same h o p
occ-same h (occ-⇒ʳ o) (⇒⊑⇒ p q) = occ-same h o q
occ-same h (occ-∀ o) (∀⊑∀ p) = occ-same (there h) o p
occ-same h (occ-⇒ˡ o) (⇒⊑★ p q) = occ-same h o p
occ-same h (occ-⇒ʳ o) (⇒⊑★ p q) = occ-same h o q
occ-same h () (ι⊑★ base-ℕ)
occ-same h () (ι⊑★ base-𝔹)
occ-same h occ-var (X⊑★ h′)
    with ∋ˡ-functional h h′
... | ()
occ-same {π = π} h (occ-∀ o) (∀⊑ {B = B} nv i p) =
  trans (sym (nodeAt-renameᵗ suc B π)) (occ-same (there h) o p)
occ-same h (occ-∀ ()) ∀★⊑★
occ-same h (occ-∀ o) (∀⊑★ ns p) = occ-same (there h) o p
occ-same h (occ-∀ ()) bot-elim
occ-same h (occ-∀ ()) bot⊑★

-- an `X⊑★` variable absent from the target reaches a `★`
occ-star : ∀ {π}
  → μ ∋ˡ X := X⊑★
  → OccAt X A π
  → ¬ (X ∈ᵗ C)
  → μ ⊢ A ⊑ C
  → nodeAt C π ≡ k★
occ-star h () fr ★⊑★
occ-star h () fr (ι⊑ι base-ℕ)
occ-star h () fr (ι⊑ι base-𝔹)
occ-star h occ-var fr X⊑X = ⊥-elim (fr ∈-var)
occ-star h (occ-⇒ˡ o) fr (⇒⊑⇒ p q) =
  occ-star h o (λ i → fr (∈-⇒ˡ i)) p
occ-star h (occ-⇒ʳ o) fr (⇒⊑⇒ p q) =
  occ-star h o (λ i → fr (∈-⇒ʳ i)) q
occ-star h (occ-∀ o) fr (∀⊑∀ p) =
  occ-star (there h) o (λ i → fr (∈-∀ i)) p
occ-star h o fr (⇒⊑★ p q) = refl
occ-star h o fr (ι⊑★ b) = refl
occ-star h o fr (X⊑★ h′) = refl
occ-star {π = π} h (occ-∀ o) fr (∀⊑ {B = C} nv i p) =
  trans (sym (nodeAt-renameᵗ suc C π))
    (occ-star (there h) o (λ j → fr (suc-∈-⇑ᵗ C j)) p)
occ-star h o fr ∀★⊑★ = refl
occ-star h o fr (∀⊑★ ns p) = refl
occ-star h (occ-∀ ()) fr bot-elim
occ-star h o fr bot⊑★ = refl

------------------------------------------------------------------------
-- Disjointness of the overlapping rules
------------------------------------------------------------------------

private
  kvar≢k★ : kvar ≡ k★ → ⊥
  kvar≢k★ ()

-- an `X⊑X` variable never goes to `★`
occurs-not-star :
    μ ∋ˡ X := X⊑X
  → X ∈ᵗ A
  → μ ⊢ A ⊑ ★
  → ⊥
occurs-not-star h i p
    with ∈→OccAt i
... | π , o = kvar≢k★ (sym (occ-same h o p))

-- `∀⊑∀` and `∀⊑` never derive the same judgment
∀⊑∀-∀⊑-disjoint :
    0 ∈ᵗ A
  → extᵐ μ ⊢ A ⊑ B
  → instᵐ μ ⊢ A ⊑ ⇑ᵗ (`∀ B)
  → ⊥
∀⊑∀-∀⊑-disjoint {B = B} i p q
    with ∈→OccAt i
... | π , o =
  kvar≢k★
    (trans (sym (occ-same here o p))
      (trans (sym (nodeAt-renameᵗ suc (`∀ B) π))
        (occ-star here o (zero-∉-⇑ᵗ (`∀ B)) q)))

------------------------------------------------------------------------
-- Uniqueness, given irrelevance of `∀⊑`'s occurrence premise
------------------------------------------------------------------------

module Unique (∈ᵗ-irr₀ : ∀ {A} (i j : 0 ∈ᵗ A) → i ≡ j) where

  ⊑-unique : (p q : μ ⊢ A ⊑ B) → p ≡ q
  ⊑-unique ★⊑★ ★⊑★ = refl
  ⊑-unique (ι⊑ι b) (ι⊑ι b′)
      rewrite Base-unique b b′ =
    refl
  ⊑-unique X⊑X X⊑X = refl
  ⊑-unique (⇒⊑⇒ p₁ p₂) (⇒⊑⇒ q₁ q₂)
      rewrite ⊑-unique p₁ q₁
            | ⊑-unique p₂ q₂ =
    refl
  ⊑-unique (∀⊑∀ p) (∀⊑∀ q)
      rewrite ⊑-unique p q =
    refl
  ⊑-unique (∀⊑∀ p) (∀⊑ nv i q) =
    ⊥-elim (∀⊑∀-∀⊑-disjoint i p q)
  ⊑-unique (∀⊑∀ p) bot-elim =
    ⊥-elim (occurs-not-star here ∈-var p)
  ⊑-unique (⇒⊑★ p₁ p₂) (⇒⊑★ q₁ q₂)
      rewrite ⊑-unique p₁ q₁
            | ⊑-unique p₂ q₂ =
    refl
  ⊑-unique (ι⊑★ b) (ι⊑★ b′)
      rewrite Base-unique b b′ =
    refl
  ⊑-unique (X⊑★ h) (X⊑★ h′)
      rewrite ∋ˡ-unique h h′ =
    refl
  ⊑-unique (∀⊑ nv i p) (∀⊑∀ q) =
    ⊥-elim (∀⊑∀-∀⊑-disjoint i q p)
  ⊑-unique (∀⊑ nv i p) (∀⊑ nv′ i′ q)
      rewrite NonVar-unique nv nv′
            | ∈ᵗ-irr₀ i i′
            | ⊑-unique p q =
    refl
  ⊑-unique (∀⊑ nv () p) ∀★⊑★
  ⊑-unique (∀⊑ nv i p) (∀⊑★ ns q) =
    ⊥-elim (occurs-not-star here i q)
  ⊑-unique (∀⊑ () i p) bot-elim
  ⊑-unique (∀⊑ () i p) bot⊑★
  ⊑-unique ∀★⊑★ (∀⊑ nv () q)
  ⊑-unique ∀★⊑★ ∀★⊑★ = refl
  ⊑-unique ∀★⊑★ (∀⊑★ () q)
  ⊑-unique (∀⊑★ ns p) (∀⊑ nv i q) =
    ⊥-elim (occurs-not-star here i p)
  ⊑-unique (∀⊑★ () p) ∀★⊑★
  ⊑-unique (∀⊑★ ns p) (∀⊑★ ns′ q)
      rewrite NonStar-unique ns ns′
            | ⊑-unique p q =
    refl
  ⊑-unique (∀⊑★ ns p) bot⊑★ =
    ⊥-elim (occurs-not-star here ∈-var p)
  ⊑-unique bot-elim (∀⊑∀ q) =
    ⊥-elim (occurs-not-star here ∈-var q)
  ⊑-unique bot-elim (∀⊑ () i q)
  ⊑-unique bot-elim bot-elim = refl
  ⊑-unique bot⊑★ (∀⊑ () i q)
  ⊑-unique bot⊑★ (∀⊑★ ns q) =
    ⊥-elim (occurs-not-star here ∈-var q)
  ⊑-unique bot⊑★ bot⊑★ = refl

  ⊑ᵂ-unique : ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ : Ty}
    → (p q : A ⊑ᵂ⟨ W ⟩ A′)
    → p ≡ q
  ⊑ᵂ-unique p q = ⊑-unique p q

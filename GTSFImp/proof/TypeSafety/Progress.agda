module proof.TypeSafety.Progress where

-- File Charter:
--   * Proves progress for closed, well-typed GTSFImp terms.
--   * Supplies the canonical forms and cast classifications used by the proof.
--   * Depends on CastTerms typing and the store-changing Reduction relation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import Reduction

------------------------------------------------------------------------
-- Progress and canonical views
------------------------------------------------------------------------

data Progress {Δ : TyCtx} {Σ : TyStore Δ} (M : Term Δ) : Set where
  done : Value M → Progress {Σ = Σ} M
  step : ∀ {Δ′} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    → M —→[ χ ] N
    → Progress {Σ = Σ} M
  crash : M ≡ blame → Progress {Σ = Σ} M

data FunView {Δ : TyCtx} (V : Term Δ) : Set where
  fv-ƛ : ∀ {N} → V ≡ ƛ N → FunView V
  fv-⇒ : ∀ {μ : Env∼ Δ} {W} {A A′ B B′ : Ty Δ}
      {c : μ ⊢ A ∼ A′} {d : μ ⊢ B ∼ B′}
    → Value W
    → V ≡ W ⟨ c ↦ d ⟩
    → FunView V
  fv-reveal : ∀ {W} {c : Conv↓ Δ} {d : Conv↑ Δ}
    → Value W → V ≡ W ↑ (c ↦↑ d) → FunView V
  fv-conceal : ∀ {W} {c : Conv↑ Δ} {d : Conv↓ Δ}
    → Value W → V ≡ W ↓ (c ↦↓ d) → FunView V

data AllView {Δ : TyCtx} (C : Ty (suc Δ)) (V : Term Δ) : Set where
  av-Λ : ∀ {W} → Value W → V ≡ Λ W → AllView C V
  av-∀ : ∀ {μ : Env∼ Δ} {W} {A : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ C}
    → Value W → V ≡ W ⟨ ∀ᶜ c ⟩ → AllView C V
  av-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ C}
      ⦃ Cnv : NonVar C ⦄ ⦃ z∈C : 0 ∈ᵗ C ⦄
    → Value W
    → A ≢ ★
    → GenSafe c
    → V ≡ W ⟨ gen c ⟩
    → AllView C V
  av-reveal : ∀ {W} {c : Conv↑ (suc Δ)}
    → Ty (suc Δ)
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllView C V
  av-conceal : ∀ {W} {c : Conv↓ (suc Δ)}
    → Ty (suc Δ)
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllView C V

data NatView {Δ : TyCtx} (V : Term Δ) : Set where
  nv-const : ∀ {n} → V ≡ $ (κℕ n) → NatView V

data BoolView {Δ : TyCtx} (V : Term Δ) : Set where
  bv-const : ∀ {b : Bool} → V ≡ $ (κ𝔹 b) → BoolView V

data StarView {Δ : TyCtx} (V : Term Δ) : Set where
  sv-tag : ∀ {μ : Env∼ Δ} {W G} {g : Groundʳ μ X∼★ G}
      ⦃ Gns : NonStar G ⦄ ⦃ match : GroundMatch g G ⦄
    → Value W
    → V ≡ W ⟨ _! ⦃ g ⦄ (idᵍ {μ = μ} g) ⟩
    → StarView V

data SealView {Δ : TyCtx} (X : TyVar Δ) (V : Term Δ) : Set where
  sv-conceal : ∀ {W}
    → Value W
    → V ≡ W ↓ seal X
    → SealView X V

------------------------------------------------------------------------
-- Canonical forms
------------------------------------------------------------------------

canonical-⇒ : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ} {A B : Ty Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ (A ⇒ B)
  → FunView V
canonical-⇒ (ƛ N) (⊢ƛ V⊢) = fv-ƛ refl
canonical-⇒ (Λ vV) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ ($ (κ𝔹 b)) ()
canonical-⇒ (vW 《 inj 》) ()
canonical-⇒ (vW 《 fun 》) (⊢⟨⟩ W⊢ c) = fv-⇒ vW refl
canonical-⇒ (vW 《 all 》) ()
canonical-⇒ (vW 《 genᵥ A≠★ safe 》) ()
canonical-⇒ (vW ↑ fun) (⊢reveal (⊢↑-⇒ c⊢ d⊢) W⊢) =
  fv-reveal vW refl
canonical-⇒ (vW ↑ all) (⊢reveal () W⊢)
canonical-⇒ (vW ↓ seal) (⊢conceal () W⊢)
canonical-⇒ (vW ↓ fun) (⊢conceal (⊢↓-⇒ c⊢ d⊢) W⊢) =
  fv-conceal vW refl
canonical-⇒ (vW ↓ all) (⊢conceal () W⊢)

canonical-∀ : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ} {A : Ty (suc Δ)}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ `∀ A
  → AllView A V
canonical-∀ (ƛ N) ()
canonical-∀ (Λ vV) (⊢Λ _ V⊢) = av-Λ vV refl
canonical-∀ ($ (κℕ n)) ()
canonical-∀ ($ (κ𝔹 b)) ()
canonical-∀ (vW 《 inj 》) ()
canonical-∀ (vW 《 fun 》) ()
canonical-∀ (vW 《 all 》) (⊢⟨⟩ W⊢ c) = av-∀ vW refl
canonical-∀ (vW 《 genᵥ A≠★ safe 》) (⊢⟨⟩ W⊢ c) =
  av-gen vW A≠★ safe refl
canonical-∀ (vW ↑ fun) (⊢reveal () W⊢)
canonical-∀ (vW ↑ all)
    (⊢reveal (⊢↑-∀ {A = A} c⊢) W⊢) =
  av-reveal A vW refl
canonical-∀ (vW ↓ seal) (⊢conceal () W⊢)
canonical-∀ (vW ↓ fun) (⊢conceal () W⊢)
canonical-∀ (vW ↓ all)
    (⊢conceal (⊢↓-∀ {A = A} c⊢) W⊢) =
  av-conceal A vW refl

canonical-ℕ : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ‵ `ℕ
  → NatView V
canonical-ℕ (ƛ N) ()
canonical-ℕ (Λ vV) ()
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ ($ (κ𝔹 b)) ()
canonical-ℕ (vW 《 inj 》) ()
canonical-ℕ (vW 《 fun 》) ()
canonical-ℕ (vW 《 all 》) ()
canonical-ℕ (vW 《 genᵥ A≠★ safe 》) ()
canonical-ℕ (vW ↑ fun) (⊢reveal () W⊢)
canonical-ℕ (vW ↑ all) (⊢reveal () W⊢)
canonical-ℕ (vW ↓ seal) (⊢conceal () W⊢)
canonical-ℕ (vW ↓ fun) (⊢conceal () W⊢)
canonical-ℕ (vW ↓ all) (⊢conceal () W⊢)

canonical-𝔹 : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ‵ `𝔹
  → BoolView V
canonical-𝔹 (ƛ N) ()
canonical-𝔹 (Λ vV) ()
canonical-𝔹 ($ (κℕ n)) ()
canonical-𝔹 ($ (κ𝔹 b)) (⊢$ (κ𝔹 .b)) = bv-const refl
canonical-𝔹 (vW 《 inj 》) ()
canonical-𝔹 (vW 《 fun 》) ()
canonical-𝔹 (vW 《 all 》) ()
canonical-𝔹 (vW 《 genᵥ A≠★ safe 》) ()
canonical-𝔹 (vW ↑ fun) (⊢reveal () W⊢)
canonical-𝔹 (vW ↑ all) (⊢reveal () W⊢)
canonical-𝔹 (vW ↓ seal) (⊢conceal () W⊢)
canonical-𝔹 (vW ↓ fun) (⊢conceal () W⊢)
canonical-𝔹 (vW ↓ all) (⊢conceal () W⊢)

canonical-★ : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ★
  → StarView V
canonical-★ (ƛ N) ()
canonical-★ (Λ vV) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ ($ (κ𝔹 b)) ()
canonical-★ (vW 《 inj 》) (⊢⟨⟩ W⊢ c) =
  sv-tag vW refl
canonical-★ (vW 《 fun 》) ()
canonical-★ (vW 《 all 》) ()
canonical-★ (vW 《 genᵥ A≠★ safe 》) ()
canonical-★ (vW ↑ fun) (⊢reveal () W⊢)
canonical-★ (vW ↑ all) (⊢reveal () W⊢)
canonical-★ (vW ↓ seal) (⊢conceal () W⊢)
canonical-★ (vW ↓ fun) (⊢conceal () W⊢)
canonical-★ (vW ↓ all) (⊢conceal () W⊢)

canonical-X : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ} {X : TyVar Δ}
  → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ ＇ X
  → SealView X V
canonical-X (ƛ N) ()
canonical-X (Λ vV) ()
canonical-X ($ (κℕ n)) ()
canonical-X ($ (κ𝔹 b)) ()
canonical-X (vW 《 inj 》) ()
canonical-X (vW 《 fun 》) ()
canonical-X (vW 《 all 》) ()
canonical-X (vW 《 genᵥ A≠★ safe 》) ()
canonical-X (vW ↑ fun) (⊢reveal () W⊢)
canonical-X (vW ↑ all) (⊢reveal () W⊢)
canonical-X (vW ↓ seal) (⊢conceal (⊢↓-seal X∈) W⊢) =
  sv-conceal vW refl
canonical-X (vW ↓ fun) (⊢conceal () W⊢)
canonical-X (vW ↓ all) (⊢conceal () W⊢)

------------------------------------------------------------------------
-- Ground-cast classification
------------------------------------------------------------------------

data ToStar {Δ : TyCtx} {μ : Env∼ Δ} : ∀ {A : Ty Δ}
    → (c : μ ⊢ A ∼ ★) → Set where
  same : ToStar (id ★)
  other : ∀ {A : Ty Δ} {c : μ ⊢ A ∼ ★}
    → A ≢ ★ → ToStar c

to-star : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
  → (c : μ ⊢ A ∼ ★) → ToStar c
to-star (id ★) = same
to-star (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) = other (nonStar≢★ Ans)
to-star (？_ ⦃ g ⦄ c ⦃ () ⦄ ⦃ match ⦄)
to-star (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) = other (λ ())

data FromStar {Δ : TyCtx} {μ : Env∼ Δ} : ∀ {B : Ty Δ}
    → (c : μ ⊢ ★ ∼ B) → Set where
  same : FromStar (id ★)
  other : ∀ {B : Ty Δ} {c : μ ⊢ ★ ∼ B}
    → B ≢ ★ → FromStar c

from-star : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ}
  → (c : μ ⊢ ★ ∼ B) → FromStar c
from-star (id ★) = same
from-star (_! ⦃ g ⦄ c ⦃ () ⦄ ⦃ match ⦄)
from-star (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) =
  other (nonStar≢★ Bns)
from-star (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) = other (λ ())

data ToGround {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    (g : Groundʳ μ X∼★ G) :
    ∀ {A : Ty Δ} → μ ⊢ A ∼ G → Set where
  same : ToGround g (idᵍ g)
  other : ∀ {A : Ty Δ} {c : μ ⊢ A ∼ G}
    → A ≢ G → ToGround g c

to-ground : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
  → (g : Groundʳ μ X∼★ G)
  → GroundMatch g A
  → (c : μ ⊢ A ∼ G)
  → ToGround g c
to-ground g-ι match-ι (id (‵ ι)) = same
to-ground g-ι match-ι (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) =
  other (λ ())
to-ground g-ι match-ι (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) = other (λ ())
to-ground g-⇒ match-⇒ (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) =
  other (λ ())
to-ground g-⇒ match-⇒ (c ↦ d) with to-star c | to-star d
to-ground g-⇒ match-⇒ (.(id ★) ↦ .(id ★))
    | same | same = same
to-ground g-⇒ match-⇒ (c ↦ d) | same | other B≠★ =
  other (λ { refl → B≠★ refl })
to-ground g-⇒ match-⇒ (c ↦ d) | other A≠★ | same =
  other (λ { refl → A≠★ refl })
to-ground g-⇒ match-⇒ (c ↦ d)
    | other A≠★ | other B≠★ =
  other (λ { refl → A≠★ refl })
to-ground g-⇒ match-⇒ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) = other (λ ())
to-ground (g-X eq) match-X (id (＇ X)) = same

data FromGround {Δ : TyCtx} {μ : Env∼ Δ} {G : Ty Δ}
    (g : Groundʳ μ ★∼X G) :
    ∀ {B : Ty Δ} → μ ⊢ G ∼ B → Set where
  same : FromGround g (idᵍ g)
  other : ∀ {B : Ty Δ} {c : μ ⊢ G ∼ B}
    → B ≢ G → FromGround g c

from-ground : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
  → (g : Groundʳ μ ★∼X G)
  → GroundMatch g B
  → (c : μ ⊢ G ∼ B)
  → FromGround g c
from-ground g-ι match-ι (id (‵ ι)) = same
from-ground g-ι match-ι (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) =
  other (λ ())
from-ground g-ι match-ι (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) = other (λ ())
from-ground g-⇒ match-⇒ (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) =
  other (λ ())
from-ground g-⇒ match-⇒ (c ↦ d) with from-star c | from-star d
from-ground g-⇒ match-⇒ (.(id ★) ↦ .(id ★))
    | same | same = same
from-ground g-⇒ match-⇒ (c ↦ d) | same | other B≠★ =
  other (λ { refl → B≠★ refl })
from-ground g-⇒ match-⇒ (c ↦ d) | other A≠★ | same =
  other (λ { refl → A≠★ refl })
from-ground g-⇒ match-⇒ (c ↦ d)
    | other A≠★ | other B≠★ =
  other (λ { refl → A≠★ refl })
from-ground g-⇒ match-⇒ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) = other (λ ())
from-ground (g-X eq) match-X (id (＇ X)) = same

------------------------------------------------------------------------
-- Polymorphic cast classification
------------------------------------------------------------------------

data Preimage {Δ Δ′ : TyCtx} (ρ : Δ ⇒ʳ Δ′) (Y : TyVar Δ′)
    (A : Ty Δ) : Set where
  found : (X : TyVar Δ) → ρ X ≡ Y → X ∈ᵗ A → Preimage ρ Y A

rename-preimage : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {Y : TyVar Δ′}
    {A : Ty Δ}
  → Y ∈ᵗ renameᵗ ρ A
  → Preimage ρ Y A
rename-preimage {A = ＇ X} var-∈ = found X refl var-∈
rename-preimage {A = ‵ ι} ()
rename-preimage {A = ★} ()
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    | found X eq X∈A =
  found X eq (∈-fun-left X∈A)
rename-preimage {A = A ⇒ B} (∈-fun-right Y∈B)
    with rename-preimage Y∈B
rename-preimage {A = A ⇒ B} (∈-fun-right Y∈B)
    | found X eq X∈B =
  found X eq (∈-fun-right X∈B)
rename-preimage {A = `∀ A} (∈-all Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found Fin.zero () X∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found (Fin.suc X) refl X∈A =
  found X refl (∈-all X∈A)

zero-not-shift : ∀ {Δ} {A : Ty Δ} → 0 ∈ᵗ ⇑ᵗ A → ⊥
zero-not-shift z∈ with rename-preimage z∈
zero-not-shift z∈ | found X () X∈A

no-to-base : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {X : TyVar Δ} {ι}
  → μ ⊢ A ∼ ‵ ι
  → X ∈ᵗ A
  → ⊥
no-to-base (id (‵ ι)) ()
no-to-base (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) ()
no-to-base (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) (∈-all X∈A) =
  no-to-base c X∈A

no-from-base : ∀ {Δ} {μ : Env∼ Δ} {B : Ty Δ} {X : TyVar Δ} {ι}
  → μ ⊢ ‵ ι ∼ B
  → X ∈ᵗ B
  → ⊥
no-from-base (id (‵ ι)) ()
no-from-base (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) ()
no-from-base (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) (∈-all X∈B) =
  no-from-base c X∈B

occurrence-nonstar : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∈ᵗ A
  → NonStar A
occurrence-nonstar var-∈ = nonstar-X
occurrence-nonstar (∈-fun-left X∈A) = nonstar-⇒
occurrence-nonstar (∈-fun-right X∈B) = nonstar-⇒
occurrence-nonstar (∈-all X∈A) = nonstar-∀

shift-star-injective : ∀ {Δ} {A : Ty Δ}
  → ⇑ᵗ A ≡ ★
  → A ≡ ★
shift-star-injective {A = ＇ X} ()
shift-star-injective {A = ‵ ι} ()
shift-star-injective {A = ★} refl = refl
shift-star-injective {A = A ⇒ B} ()
shift-star-injective {A = `∀ A} ()

gen-safe′ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    {C B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ C ∼ B)
  → C ≡ ⇑ᵗ A
  → A ≢ ★
  → NonVar B
  → 0 ∈ᵗ B
  → GenSafe c
gen-safe′ (id a) refl A≠★ Bnv z∈B =
  ⊥-elim (zero-not-shift z∈B)
gen-safe′ (c ↦ d) eq A≠★ Bnv z∈B = safe-⇒
gen-safe′ (∀ᶜ c) eq A≠★ Bnv z∈B = safe-∀
gen-safe′ (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) eq A≠★ Bnv ()
gen-safe′ (？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    eq A≠★ Bnv z∈B =
  ⊥-elim (A≠★ (shift-star-injective (sym eq)))
gen-safe′ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) eq A≠★ Bnv z∈B = safe-inst
gen-safe′ (gen_ {A = C} ⦃ Cnv ⦄ ⦃ z∈C ⦄ c)
    eq A≠★ Bnv z∈B =
  safe-gen (gen-safe′ c refl C≠★ Cnv z∈C)
  where
  C≠★ : C ≢ ★
  C≠★ C≡★ = A≠★ (shift-star-injective (trans (sym eq) C≡★))

gen-safe : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ ⇑ᵗ A ∼ B)
  → A ≢ ★
  → NonVar B
  → 0 ∈ᵗ B
  → GenSafe c
gen-safe c A≠★ Bnv z∈B = gen-safe′ c refl A≠★ Bnv z∈B

data GroundGenView {Δ : TyCtx} {μ : Env∼ Δ} {B : Ty Δ}
    (c : μ ⊢ ★ ∼ B) : Set where
  factor : ∀ {c′ : μ ⊢ (★ ⇒ ★) ∼ B}
    → GroundGen c c′
    → GroundGenView c

ground-gen-view : ∀ {Δ} {μ : Env∼ Δ} {B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ ★ ∼ B)
  → NonVar B
  → 0 ∈ᵗ B
  → GroundGenView c
ground-gen-view (id ★) Bnv ()
ground-gen-view (_! ⦃ g ⦄ c ⦃ () ⦄ ⦃ match ⦄) Bnv z∈B
ground-gen-view (？_ ⦃ g-⇒ ⦄ c ⦃ Bns ⦄ ⦃ match-⇒ ⦄)
    Bnv z∈B =
  factor (ground-gen-⇒ (gen-safe c (λ ()) Bnv z∈B))
ground-gen-view (？_ ⦃ g-ι ⦄ c ⦃ Bns ⦄ ⦃ match-ι ⦄)
    Bnv z∈B =
  ⊥-elim (no-from-base c z∈B)
ground-gen-view (？_ ⦃ g-X eq ⦄ c ⦃ Bns ⦄ ⦃ match-X ⦄) () z∈B
ground-gen-view (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) Bnv′ z∈∀B
    with ground-gen-view c Bnv z∈B
ground-gen-view (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c) Bnv′ z∈∀B
    | factor {c′ = c′} f =
  factor (ground-gen-∀ {c = c} {c′ = c′}
    ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ f)

data GroundInstView {Δ : TyCtx} {μ : Env∼ Δ} {A : Ty Δ}
    (c : μ ⊢ A ∼ ★) : Set where
  factor : ∀ {c′ : μ ⊢ A ∼ (★ ⇒ ★)}
    → GroundInst c c′
    → GroundInstView c

ground-inst-view : ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
  → (c : instᵐ μ ⊢ A ∼ ★)
  → NonVar A
  → 0 ∈ᵗ A
  → GroundInstView c
ground-inst-view (id ★) Anv ()
ground-inst-view (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match-⇒ ⦄) Anv z∈A =
  factor ground-inst-⇒
ground-inst-view (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match-ι ⦄) Anv z∈A =
  ⊥-elim (no-to-base c z∈A)
ground-inst-view (_! ⦃ g-X eq ⦄ c ⦃ Ans ⦄ ⦃ match-X ⦄) () z∈A
ground-inst-view (？_ ⦃ g ⦄ c ⦃ () ⦄ ⦃ match ⦄) Anv z∈A
ground-inst-view (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) Anv′ z∈∀A
    with ground-inst-view c Anv z∈A
ground-inst-view (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c) Anv′ z∈∀A
    | factor {c′ = c′} f =
  factor (ground-inst-∀ {c = c} {c′ = c′}
    ⦃ Anv = Anv ⦄ ⦃ z∈A = z∈A ⦄ f)

------------------------------------------------------------------------
-- Progress for values under casts and conversions
------------------------------------------------------------------------

cast-value-progress : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {A B : Ty Δ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → Value V
  → (c : A ∼ B)
  → Progress {Σ = Σ} (V ⟨ c ⟩)
cast-value-progress V⊢ vV (id a) = step (pure-step (β-id vV))
cast-value-progress V⊢ vV (c ↦ d) = done (vV 《 fun 》)
cast-value-progress V⊢ vV (∀ᶜ c) = done (vV 《 all 》)
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    with to-ground g-⇒ match c
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-⇒ ⦄ c
      ⦃ nonstar-⇒ ⦄ ⦃ match-⇒ ⦄)
    | same =
  done
    (vV 《 inj ⦃ Gns = nonstar-⇒ ⦄ ⦃ match = match-⇒ ⦄
      》)
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-⇒ ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    | other A≠G =
  step
    (pure-step
      (ground ⦃ g-⇒ ⦄ ⦃ Ans ⦄ ⦃ match ⦄ vV A≠G))
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    with to-ground g-ι match c
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-ι ⦄ c
      ⦃ nonstar-ι ⦄ ⦃ match-ι ⦄)
    | same =
  done
    (vV 《 inj ⦃ Gns = nonstar-ι ⦄ ⦃ match = match-ι ⦄
      》)
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-ι ⦄ c ⦃ Ans ⦄ ⦃ match ⦄)
    | other A≠G =
  step
    (pure-step
      (ground ⦃ g-ι ⦄ ⦃ Ans ⦄ ⦃ match ⦄ vV A≠G))
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-X eq ⦄ c ⦃ Xns ⦄ ⦃ match ⦄)
    with to-ground (g-X eq) match c
cast-value-progress {Δ = Δ} V⊢ vV
    (_! ⦃ g-X eq ⦄ .(idᵍ {μ = idᶜ} (g-X eq))
      ⦃ Xns ⦄ ⦃ match ⦄)
    | same rewrite nonStar-unique Xns nonstar-X
                 | groundMatch-unique match match-X =
  done
    (vV 《 inj ⦃ g = g-X eq ⦄ ⦃ Gns = nonstar-X ⦄
      ⦃ match = match-X ⦄ 》)
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    with from-ground g match c
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄)
    | other B≠G =
  step (pure-step (expand ⦃ Gns = ground-nonstar g ⦄
    ⦃ gmatch = ground-match g ⦄ vV (λ G≡B → B≠G (sym G≡B))))
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | same with canonical-★ vV V⊢
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | same | sv-tag {G = H} {g = h} ⦃ Gns ⦄ ⦃ hmatch ⦄ vW refl
    with H ≟Ty G
cast-value-progress V⊢ vV
    (？_ {G = .H} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | same | sv-tag {G = H} {g = h} ⦃ Gns ⦄ ⦃ hmatch ⦄ vW refl
    | yes refl rewrite nonStar-unique Bns Gns =
  step (pure-step (tag-untag
    ⦃ g = h ⦄ ⦃ h = g ⦄
    ⦃ Gns = Gns ⦄ ⦃ gmatch = hmatch ⦄
    ⦃ hmatch = match ⦄ vW))
cast-value-progress V⊢ vV
    (？_ {G = G} ⦃ g ⦄ .(idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄)
    | same | sv-tag {G = H} {g = h} ⦃ Gns ⦄ ⦃ hmatch ⦄ vW refl
    | no H≠G =
  step (pure-step (tag-untag-bad
    ⦃ g = h ⦄ ⦃ h = g ⦄
    ⦃ Gns = Gns ⦄ ⦃ gmatch = hmatch ⦄
    ⦃ Hns = Bns ⦄ ⦃ hmatch = match ⦄ vW H≠G))
cast-value-progress V⊢ vV
    (inst_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    with B ≟Ty ★
cast-value-progress V⊢ vV
    (inst_ {B = B} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | no B≠★ =
  step (β-inst vV B≠★)
cast-value-progress V⊢ vV
    (inst_ {B = .★} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | yes refl with ground-inst-view c Anv z∈A
cast-value-progress V⊢ vV
    (inst_ {B = .★} ⦃ Anv ⦄ ⦃ z∈A ⦄ c)
    | yes refl | factor f =
  step (pure-step (ground-∀ vV f))
cast-value-progress V⊢ vV
    (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    with A ≟Ty ★
cast-value-progress V⊢ vV
    (gen_ {A = A} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | no A≠★ =
  done (vV 《 genᵥ A≠★ (gen-safe c A≠★ Bnv z∈B) 》)
cast-value-progress V⊢ vV
    (gen_ {A = .★} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | yes refl with ground-gen-view c Bnv z∈B
cast-value-progress V⊢ vV
    (gen_ {A = .★} ⦃ Bnv ⦄ ⦃ z∈B ⦄ c)
    | yes refl | factor f =
  step (pure-step (expand-∀ vV f))

reveal-value-progress : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {A B : Ty Δ} {c : Conv↑ Δ}
  → Σ ⊢ c ⦂ A ↑ˢ B
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → Value V
  → Progress {Σ = Σ} (V ↑ c)
reveal-value-progress (⊢↑-unseal X∈) V⊢ vV
    with canonical-X vV V⊢
reveal-value-progress (⊢↑-unseal X∈) V⊢ vV
    | sv-conceal vW refl =
  step (pure-step (conceal-reveal vW))
reveal-value-progress (⊢↑-⇒ c⊢ d⊢) V⊢ vV = done (vV ↑ fun)
reveal-value-progress (⊢↑-∀ c⊢) V⊢ vV = done (vV ↑ all)
reveal-value-progress ⊢↑-id V⊢ vV = step (pure-step (id-reveal vV))

conceal-value-progress : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    {A B : Ty Δ} {c : Conv↓ Δ}
  → Σ ⊢ c ⦂ A ↓ˢ B
  → Value V
  → Progress {Σ = Σ} (V ↓ c)
conceal-value-progress (⊢↓-seal X∈) vV = done (vV ↓ seal)
conceal-value-progress (⊢↓-⇒ c⊢ d⊢) vV = done (vV ↓ fun)
conceal-value-progress (⊢↓-∀ c⊢) vV = done (vV ↓ all)
conceal-value-progress ⊢↓-id vV = step (pure-step (id-conceal vV))

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ} {A : Ty Δ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → Progress {Σ = Σ} M
progress (⊢` ())
progress (⊢ƛ M⊢) = done (ƛ _)
progress (⊢· L⊢ M⊢) with progress L⊢
progress (⊢· L⊢ M⊢) | step L→L′ =
  step (ξ-·₁ L→L′ refl)
progress (⊢· L⊢ M⊢) | crash refl =
  step (pure-step blame-·₁)
progress (⊢· L⊢ M⊢) | done vL with progress M⊢
progress (⊢· L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-·₂ vL M→M′ refl)
progress (⊢· L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-·₂ vL))
progress (⊢· L⊢ M⊢) | done vL | done vM
    with canonical-⇒ vL L⊢
progress (⊢· L⊢ M⊢) | done vL | done vM | fv-ƛ refl =
  step (pure-step (β vM))
progress (⊢· L⊢ M⊢) | done vL | done vM
    | fv-⇒ vW refl =
  step (pure-step (β-⇒ vW vM refl))
progress (⊢· L⊢ M⊢) | done vL | done vM
    | fv-reveal vW refl =
  step (pure-step (β-reveal-⇒ vW vM))
progress (⊢· L⊢ M⊢) | done vL | done vM
    | fv-conceal vW refl =
  step (pure-step (β-conceal-⇒ vW vM))
progress (⊢Λ vM M⊢) = done (Λ vM)
progress (⊢• {C = C} L⊢) with progress L⊢
progress (⊢• {C = C} L⊢) | step L→L′ =
  step (ξ-• L→L′ refl refl)
progress (⊢• {C = C} L⊢) | crash refl =
  step (pure-step blame-•)
progress (⊢• {C = C} L⊢) | done vL
    with canonical-∀ vL L⊢
progress (⊢• {C = C} L⊢) | done vL | av-Λ vW refl =
  step (β-Λ {B = C} vW)
progress (⊢• {C = C} L⊢) | done vL | av-∀ vW refl =
  step (pure-step (β-∀ vW refl))
progress (⊢• {C = C} L⊢) | done vL
    | av-gen vW A≠★ safe refl =
  step (β-gen vW A≠★ safe)
progress (⊢• {C = C} L⊢) | done vL
    | av-reveal A vW refl =
  step (β-reveal-∀ {C = A} vW)
progress (⊢• {C = C} L⊢) | done vL
    | av-conceal A vW refl =
  step (β-conceal-∀ {C = A} vW)
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ addℕ L⊢ M⊢) with progress L⊢
progress (⊢⊕ addℕ L⊢ M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′ refl)
progress (⊢⊕ addℕ L⊢ M⊢) | crash refl =
  step (pure-step blame-⊕₁)
progress (⊢⊕ addℕ L⊢ M⊢) | done vL with progress M⊢
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′ refl)
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | done vM
    with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
progress (⊢⊕ addℕ L⊢ M⊢) | done vL | done vM
    | nv-const refl | nv-const refl =
  step (pure-step (δ-⊕ δ-add))
progress (⊢⊕ and𝔹 L⊢ M⊢) with progress L⊢
progress (⊢⊕ and𝔹 L⊢ M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′ refl)
progress (⊢⊕ and𝔹 L⊢ M⊢) | crash refl =
  step (pure-step blame-⊕₁)
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL with progress M⊢
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′ refl)
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | done vM
    with canonical-𝔹 vL L⊢ | canonical-𝔹 vM M⊢
progress (⊢⊕ and𝔹 L⊢ M⊢) | done vL | done vM
    | bv-const refl | bv-const refl =
  step (pure-step (δ-⊕ δ-and))
progress (⊢⟨⟩ M⊢ c) with progress M⊢
progress (⊢⟨⟩ M⊢ c) | step M→M′ =
  step (ξ-⟨⟩ M→M′ refl)
progress (⊢⟨⟩ M⊢ c) | crash refl =
  step (pure-step blame-⟨⟩)
progress (⊢⟨⟩ M⊢ c) | done vM = cast-value-progress M⊢ vM c
progress (⊢reveal c⊢ M⊢) with progress M⊢
progress (⊢reveal c⊢ M⊢) | step M→M′ =
  step (ξ-reveal M→M′ refl)
progress (⊢reveal c⊢ M⊢) | crash refl =
  step (pure-step blame-reveal)
progress (⊢reveal c⊢ M⊢) | done vM =
  reveal-value-progress c⊢ M⊢ vM
progress (⊢conceal c⊢ M⊢) with progress M⊢
progress (⊢conceal c⊢ M⊢) | step M→M′ =
  step (ξ-conceal M→M′ refl)
progress (⊢conceal c⊢ M⊢) | crash refl =
  step (pure-step blame-conceal)
progress (⊢conceal c⊢ M⊢) | done vM =
  conceal-value-progress c⊢ vM
progress ⊢blame = crash refl

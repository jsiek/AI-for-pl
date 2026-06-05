module proof.CoercionReduction where

-- Coercion lists for GTLC, including blame coercions, adjacent-cell
-- reduction, preservation, and normal-form syntax for the reduction proof
-- development.  This file is intentionally self-contained rather than
-- re-exporting the older binary sequencing presentation from Coercions.

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_+_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  ( 0<1+n; n<1+n; m<m+n; +-assoc; +-comm; +-identityʳ
  ; +-monoˡ-<; +-monoʳ-<)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import GTLC

infixr 7 _⨟_
infixr 6 _↦_

-- This adds ⊥ compared to Coercion in Coercions.agda.
data Crcn : Set where
  _!     : Ty → Crcn -- injection (tagging)
  _？_    : Ty → Nat → Crcn -- projection (tag checking)
  _↦_    : List Crcn → List Crcn → Crcn
  ⊥ᶜ_⇨_at_ : Ty → Ty → Nat → Crcn

Coercion : Set
Coercion = List Crcn

_⨟_ : Coercion → Coercion → Coercion
[] ⨟ d = d
(c ∷ cs) ⨟ d = c ∷ (cs ⨟ d)

singleᶜ : Crcn → Coercion
singleᶜ c = c ∷ []

data Atomic : Crcn → Set where
  atom-! : ∀ {G} → Atomic (G !)
  atom-? : ∀ {G ℓ} → Atomic (G ？ ℓ)

infix 4 ⊢_⦂_⇨ᶜ_
infix 4 ⊢_⦂_⇨_

data ⊢_⦂_⇨_ : Coercion → Ty → Ty → Set

data ⊢_⦂_⇨ᶜ_ : Crcn → Ty → Ty → Set where
  ⊢! : ∀ {G}
    → Ground G
    → ⊢ G ! ⦂ G ⇨ᶜ ★

  ⊢? : ∀ {G ℓ}
    → Ground G
    → ⊢ (G ？ ℓ) ⦂ ★ ⇨ᶜ G

  ⊢↦ : ∀ {A B C D c d}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ᶜ (C ⇒ D)

  ⊢⊥ : ∀ {A B ℓ}
    → ⊢ (⊥ᶜ A ⇨ B at ℓ) ⦂ A ⇨ᶜ B

data ⊢_⦂_⇨_ where
  ⊢[] : ∀ {A}
    → ⊢ [] ⦂ A ⇨ A

  ⊢∷ : ∀ {A B C c d}
    → ⊢ c ⦂ A ⇨ᶜ B
    → ⊢ d ⦂ B ⇨ C
    → ⊢ (c ∷ d) ⦂ A ⇨ C

⊢singleᶜ : ∀ {A B c}
  → ⊢ c ⦂ A ⇨ᶜ B
  → ⊢ singleᶜ c ⦂ A ⇨ B
⊢singleᶜ cwt = ⊢∷ cwt ⊢[]

⊢⨟ : ∀ {A B C c d}
  → ⊢ c ⦂ A ⇨ B
  → ⊢ d ⦂ B ⇨ C
  → ⊢ c ⨟ d ⦂ A ⇨ C
⊢⨟ ⊢[] dwt = dwt
⊢⨟ (⊢∷ cwt restwt) dwt = ⊢∷ cwt (⊢⨟ restwt dwt)

⊢++ : ∀ {A B C c d}
  → ⊢ c ⦂ A ⇨ B
  → ⊢ d ⦂ B ⇨ C
  → ⊢ c ++ d ⦂ A ⇨ C
⊢++ ⊢[] dwt = dwt
⊢++ (⊢∷ cwt restwt) dwt = ⊢∷ cwt (⊢++ restwt dwt)

coerce : ∀ {A B} → Nat → A ~ B → Coercion
coerce ℓ ~-ℕ = []
coerce ℓ ~-★ = []
coerce ℓ ★~ℕ = singleᶜ (ℕ ？ ℓ)
coerce ℓ ℕ~★ = singleᶜ (ℕ !)
coerce ℓ (★~⇒ c d) =
  singleᶜ ((★ ⇒ ★) ？ ℓ) ⨟ singleᶜ (coerce ℓ c ↦ coerce ℓ d)
coerce ℓ (⇒~★ c d) =
  singleᶜ (coerce ℓ c ↦ coerce ℓ d) ⨟
  singleᶜ ((★ ⇒ ★) !)
coerce ℓ (~-⇒ c d) = singleᶜ (coerce ℓ c ↦ coerce ℓ d)

coerce-wt : ∀ {A B} (ℓ : Nat) (p : A ~ B) → ⊢ coerce ℓ p ⦂ A ⇨ B
coerce-wt ℓ ~-ℕ = ⊢[]
coerce-wt ℓ ~-★ = ⊢[]
coerce-wt ℓ ★~ℕ = ⊢singleᶜ (⊢? G-ℕ)
coerce-wt ℓ ℕ~★ = ⊢singleᶜ (⊢! G-ℕ)
coerce-wt ℓ (★~⇒ c d) =
  ⊢⨟ (⊢singleᶜ (⊢? G-⇒))
      (⊢singleᶜ (⊢↦ (coerce-wt ℓ c) (coerce-wt ℓ d)))
coerce-wt ℓ (⇒~★ c d) =
  ⊢⨟ (⊢singleᶜ (⊢↦ (coerce-wt ℓ c) (coerce-wt ℓ d)))
      (⊢singleᶜ (⊢! G-⇒))
coerce-wt ℓ (~-⇒ c d) =
  ⊢singleᶜ (⊢↦ (coerce-wt ℓ c) (coerce-wt ℓ d))

mutual
  coercion-crcn-target-unique : ∀ {c A B C}
    → ⊢ c ⦂ A ⇨ᶜ B
    → ⊢ c ⦂ A ⇨ᶜ C
    → B ≡ C
  coercion-crcn-target-unique (⊢! g₁) (⊢! g₂) = refl
  coercion-crcn-target-unique (⊢? g₁) (⊢? g₂) = refl
  coercion-crcn-target-unique (⊢↦ c₁ d₁) (⊢↦ c₂ d₂)
    with coercion-source-unique c₁ c₂
       | coercion-target-unique d₁ d₂
  ... | refl | refl = refl
  coercion-crcn-target-unique ⊢⊥ ⊢⊥ = refl

  coercion-target-unique : ∀ {c A B C}
    → ⊢ c ⦂ A ⇨ B
    → ⊢ c ⦂ A ⇨ C
    → B ≡ C
  coercion-target-unique ⊢[] ⊢[] = refl
  coercion-target-unique (⊢∷ c₁ d₁) (⊢∷ c₂ d₂)
    with coercion-crcn-target-unique c₁ c₂
  ... | refl = coercion-target-unique d₁ d₂

  coercion-crcn-source-unique : ∀ {c A B C}
    → ⊢ c ⦂ A ⇨ᶜ C
    → ⊢ c ⦂ B ⇨ᶜ C
    → A ≡ B
  coercion-crcn-source-unique (⊢! g₁) (⊢! g₂) = refl
  coercion-crcn-source-unique (⊢? g₁) (⊢? g₂) = refl
  coercion-crcn-source-unique (⊢↦ c₁ d₁) (⊢↦ c₂ d₂)
    with coercion-target-unique c₁ c₂
       | coercion-source-unique d₁ d₂
  ... | refl | refl = refl
  coercion-crcn-source-unique ⊢⊥ ⊢⊥ = refl

  coercion-source-unique : ∀ {c A B C}
    → ⊢ c ⦂ A ⇨ C
    → ⊢ c ⦂ B ⇨ C
    → A ≡ B
  coercion-source-unique ⊢[] ⊢[] = refl
  coercion-source-unique (⊢∷ c₁ d₁) (⊢∷ c₂ d₂)
    with coercion-source-unique d₁ d₂
  ... | refl = coercion-crcn-source-unique c₁ c₂

----------------------------------------------------------------
-- Coercion Reduction
----------------------------------------------------------------

infix 4 _;_—→ᶜ_
infix 4 _—→ᶜᶜ_
infix 3 _∎ᶜᶜ
infixr 2 _—→ᶜᶜ⟨_⟩_
infix 2 _—↠ᶜᶜ_

data _;_—→ᶜ_ : Crcn → Crcn → Coercion → Set where
  β-proj-inj-okᶜ : ∀ {G ℓ}
    → G ! ; (G ？ ℓ) —→ᶜ []

  β-proj-inj-badᶜ : ∀ {G H ℓ}
    → G ≢ H
    → G ! ;  H ？ ℓ  —→ᶜ (⊥ᶜ G ⇨ H at ℓ) ∷ []

  β-↦ᶜ : ∀ {c d c′ d′}
    → (c ↦ d) ; (c′ ↦ d′) —→ᶜ (c′ ⨟ c) ↦ (d ⨟ d′) ∷ []

  β-⊥Lᶜ : ∀ {A B C d ℓ}
    → ⊢ d ⦂ B ⇨ᶜ C
    → (⊥ᶜ A ⇨ B at ℓ) ; d —→ᶜ (⊥ᶜ A ⇨ C at ℓ) ∷ []

  β-!⊥ᶜ : ∀ {G B ℓ}
    → G ! ; (⊥ᶜ ★ ⇨ B at ℓ) —→ᶜ (⊥ᶜ G ⇨ B at ℓ) ∷ []

  β-↦⊥ᶜ : ∀ {c d A B C D E ℓ}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → (c ↦ d) ; (⊥ᶜ (C ⇒ D) ⇨ E at ℓ)
      —→ᶜ (⊥ᶜ (A ⇒ B) ⇨ E at ℓ) ∷ []

data _—→ᶜᶜ_ : Coercion → Coercion → Set where

  ξ-pair : ∀ {c₁ c₂ d̅ c̅ c′}
    → c₁ ; c₂ —→ᶜ d̅
    → c′ ≡ d̅ ++ c̅
      ---------------------------------------
    →  (c₁ ∷ c₂ ∷ c̅) —→ᶜᶜ c′ 

  ξ-∷ᶜ : ∀ {c cs cs′}
    → cs —→ᶜᶜ cs′
    → (c ∷ cs) —→ᶜᶜ (c ∷ cs′)

  ξ-↦₁ᶜ : ∀ {c c′ d cs}
    → c —→ᶜᶜ c′
    → ((c ↦ d) ∷ cs) —→ᶜᶜ ((c′ ↦ d) ∷ cs)

  ξ-↦₂ᶜ : ∀ {c d d′ cs}
    → d —→ᶜᶜ d′
    → ((c ↦ d) ∷ cs) —→ᶜᶜ ((c ↦ d′) ∷ cs)

data _—↠ᶜᶜ_ : Coercion → Coercion → Set where
  _∎ᶜᶜ : (c : Coercion) → c —↠ᶜᶜ c
  _—→ᶜᶜ⟨_⟩_ : (l : Coercion) {m n : Coercion}
    → l —→ᶜᶜ m
    → m —↠ᶜᶜ n
    → l —↠ᶜᶜ n

multi-transᶜᶜ : {c d e : Coercion}
  → c —↠ᶜᶜ d
  → d —↠ᶜᶜ e
  → c —↠ᶜᶜ e
multi-transᶜᶜ (_ ∎ᶜᶜ) ms2 = ms2
multi-transᶜᶜ (_ —→ᶜᶜ⟨ s ⟩ ms1′) ms2 =
  _ —→ᶜᶜ⟨ s ⟩ (multi-transᶜᶜ ms1′ ms2)

infixr 2 _—↠ᶜᶜ⟨_⟩_
_—↠ᶜᶜ⟨_⟩_ : ∀ (l : Coercion) {m n : Coercion}
  → l —↠ᶜᶜ m
  → m —↠ᶜᶜ n
  → l —↠ᶜᶜ n
l —↠ᶜᶜ⟨ l—↠m ⟩ m—↠n = multi-transᶜᶜ l—↠m m—↠n

preserve-pairᶜ : ∀ {c d c′ A B C}
  → ⊢ c ⦂ A ⇨ᶜ B
  → ⊢ d ⦂ B ⇨ᶜ C
  → c ; d —→ᶜ c′
  → ⊢ c′ ⦂ A ⇨ C
preserve-pairᶜ (⊢! g) (⊢? h) β-proj-inj-okᶜ = ⊢[]
preserve-pairᶜ (⊢! g) (⊢? h) (β-proj-inj-badᶜ G≢H) = ⊢singleᶜ ⊢⊥
preserve-pairᶜ (⊢↦ cwt dwt) (⊢↦ c′wt d′wt) β-↦ᶜ =
  ⊢singleᶜ (⊢↦ (⊢⨟ c′wt cwt) (⊢⨟ dwt d′wt))
preserve-pairᶜ ⊢⊥ dwt (β-⊥Lᶜ dwt′)
  with coercion-crcn-target-unique dwt dwt′
preserve-pairᶜ ⊢⊥ dwt (β-⊥Lᶜ dwt′) | refl = ⊢singleᶜ ⊢⊥
preserve-pairᶜ (⊢! g) ⊢⊥ β-!⊥ᶜ = ⊢singleᶜ ⊢⊥
preserve-pairᶜ (⊢↦ cwt dwt) ⊢⊥ (β-↦⊥ᶜ cwt′ dwt′)
  with coercion-target-unique cwt cwt′ | coercion-source-unique dwt dwt′
preserve-pairᶜ (⊢↦ cwt dwt) ⊢⊥ (β-↦⊥ᶜ cwt′ dwt′)
  | refl | refl = ⊢singleᶜ ⊢⊥

preserve-—→ᶜᶜ : ∀ {c c′ A B}
  → ⊢ c ⦂ A ⇨ B
  → c —→ᶜᶜ c′
  → ⊢ c′ ⦂ A ⇨ B
preserve-—→ᶜᶜ (⊢∷ cwt (⊢∷ dwt restwt)) (ξ-pair c;d→c′ refl) =
  ⊢++ (preserve-pairᶜ cwt dwt c;d→c′) restwt
preserve-—→ᶜᶜ (⊢∷ cwt restwt) (ξ-∷ᶜ cs→cs′) =
  ⊢∷ cwt (preserve-—→ᶜᶜ restwt cs→cs′)
preserve-—→ᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) (ξ-↦₁ᶜ c→c′) =
  ⊢∷ (⊢↦ (preserve-—→ᶜᶜ cwt c→c′) dwt) restwt
preserve-—→ᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) (ξ-↦₂ᶜ d→d′) =
  ⊢∷ (⊢↦ cwt (preserve-—→ᶜᶜ dwt d→d′)) restwt

----------------------------------------------------------------
-- Coercion Normal Forms
----------------------------------------------------------------

data IrredPairᶜ : Crcn → Crcn → Set where
  irred-?! : ∀ {G ℓ}
    → IrredPairᶜ (G ？ ℓ) (G !)

  irred-?⊥ : ∀ {G ℓ ℓ′ A B}
    → IrredPairᶜ (G ？ ℓ) (⊥ᶜ A ⇨ B at ℓ′)

  irred-?↦ : ∀ {ℓ c d}
    → IrredPairᶜ ((★ ⇒ ★) ？ ℓ) (c ↦ d)

  irred-↦! : ∀ {c d}
    → IrredPairᶜ (c ↦ d) ((★ ⇒ ★) !)

mutual
  data SingleNormalᶜ : Crcn → Set where
    nf-! : ∀ {G}
      → SingleNormalᶜ (G !)

    nf-? : ∀ {G ℓ}
      → SingleNormalᶜ (G ？ ℓ)

    nf-↦ : ∀ {c d}
      → Normalᶜ c
      → Normalᶜ d
      → SingleNormalᶜ (c ↦ d)

    nf-⊥ : ∀ {A B ℓ}
      → SingleNormalᶜ (⊥ᶜ A ⇨ B at ℓ)

  data Normalᶜ : Coercion → Set where
    nf-[] : Normalᶜ []

    nf-singleton : ∀ {c}
      → SingleNormalᶜ c
      → Normalᶜ (c ∷ [])

    nf-step : ∀ {c d cs}
      → SingleNormalᶜ c
      → IrredPairᶜ c d
      → Normalᶜ (d ∷ cs)
      → Normalᶜ (c ∷ d ∷ cs)

Step : Coercion → Set
Step c = Σ[ c′ ∈ Coercion ] c —→ᶜᶜ c′

step : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Maybe (Step c)
step ⊢[] = nothing
step (⊢∷ (⊢! g) ⊢[]) = nothing
step (⊢∷ (⊢? g) ⊢[]) = nothing
step (⊢∷ ⊢⊥ ⊢[]) = nothing
step (⊢∷ (⊢↦ cwt dwt) restwt) with step cwt
step (⊢∷ (⊢↦ cwt dwt) restwt) | just (_ , c→c′) =
  just (_ , ξ-↦₁ᶜ c→c′)
step (⊢∷ (⊢↦ cwt dwt) restwt) | nothing with step dwt
step (⊢∷ (⊢↦ cwt dwt) restwt) | nothing | just (_ , d→d′) =
  just (_ , ξ-↦₂ᶜ d→d′)
step (⊢∷ (⊢↦ cwt dwt) ⊢[]) | nothing | nothing = nothing
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢↦ c′wt d′wt) restwt))
  | nothing | nothing = just (_ , ξ-pair β-↦ᶜ refl)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ ⊢⊥ restwt))
  | nothing | nothing = just (_ , ξ-pair (β-↦⊥ᶜ cwt dwt) refl)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ dwt′ restwt))
  | nothing | nothing
  with step (⊢∷ dwt′ restwt)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ dwt′ restwt))
  | nothing | nothing | just (_ , d→d′) = just (_ , ξ-∷ᶜ d→d′)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ dwt′ restwt))
  | nothing | nothing | nothing = nothing
step (⊢∷ (⊢! {G = G} g) (⊢∷ (⊢? {G = H} h) restwt))
  with G ≟Ty H
step (⊢∷ (⊢! g) (⊢∷ (⊢? h) restwt)) | yes refl =
  just (_ , ξ-pair β-proj-inj-okᶜ refl)
step (⊢∷ (⊢! g) (⊢∷ (⊢? h) restwt)) | no G≢H =
  just (_ , ξ-pair (β-proj-inj-badᶜ G≢H) refl)
step (⊢∷ (⊢! g) (⊢∷ ⊢⊥ restwt)) =
  just (_ , ξ-pair β-!⊥ᶜ refl)
step (⊢∷ ⊢⊥ (⊢∷ dwt restwt)) =
  just (_ , ξ-pair (β-⊥Lᶜ dwt) refl)
step (⊢∷ cwt (⊢∷ dwt restwt)) with step (⊢∷ dwt restwt)
step (⊢∷ cwt (⊢∷ dwt restwt)) | just (_ , d→d′) =
  just (_ , ξ-∷ᶜ d→d′)
step (⊢∷ cwt (⊢∷ dwt restwt)) | nothing = nothing

data Progressᶜᶜ (c : Coercion) : Set where
  done : Normalᶜ c → Progressᶜᶜ c
  stepᶜᶜ : Step c → Progressᶜᶜ c

progressᶜᶜ : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Progressᶜᶜ c
progressᶜᶜ ⊢[] = done nf-[]
progressᶜᶜ (⊢∷ (⊢! g) ⊢[]) = done (nf-singleton nf-!)
progressᶜᶜ (⊢∷ (⊢? g) ⊢[]) = done (nf-singleton nf-?)
progressᶜᶜ (⊢∷ ⊢⊥ ⊢[]) = done (nf-singleton nf-⊥)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) with progressᶜᶜ cwt
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) | stepᶜᶜ (_ , c→c′) =
  stepᶜᶜ (_ , ξ-↦₁ᶜ c→c′)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) | done cnf with progressᶜᶜ dwt
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) | done cnf
  | stepᶜᶜ (_ , d→d′) = stepᶜᶜ (_ , ξ-↦₂ᶜ d→d′)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) ⊢[]) | done cnf | done dnf =
  done (nf-singleton (nf-↦ cnf dnf))
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢! G-⇒) restwt))
  | done cnf | done dnf with progressᶜᶜ (⊢∷ (⊢! G-⇒) restwt)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢! G-⇒) restwt))
  | done cnf | done dnf | done restnf =
  done (nf-step (nf-↦ cnf dnf) irred-↦! restnf)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢! G-⇒) restwt))
  | done cnf | done dnf | stepᶜᶜ (_ , rest→rest′) =
  stepᶜᶜ (_ , ξ-∷ᶜ rest→rest′)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢↦ c′wt d′wt) restwt))
  | done cnf | done dnf = stepᶜᶜ (_ , ξ-pair β-↦ᶜ refl)
progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) (⊢∷ ⊢⊥ restwt))
  | done cnf | done dnf = stepᶜᶜ (_ , ξ-pair (β-↦⊥ᶜ cwt dwt) refl)
progressᶜᶜ (⊢∷ (⊢! {G = G} g) (⊢∷ (⊢? {G = H} h) restwt))
  with G ≟Ty H
progressᶜᶜ (⊢∷ (⊢! g) (⊢∷ (⊢? h) restwt)) | yes refl =
  stepᶜᶜ (_ , ξ-pair β-proj-inj-okᶜ refl)
progressᶜᶜ (⊢∷ (⊢! g) (⊢∷ (⊢? h) restwt)) | no G≢H =
  stepᶜᶜ (_ , ξ-pair (β-proj-inj-badᶜ G≢H) refl)
progressᶜᶜ (⊢∷ (⊢! g) (⊢∷ ⊢⊥ restwt)) =
  stepᶜᶜ (_ , ξ-pair β-!⊥ᶜ refl)
progressᶜᶜ (⊢∷ ⊢⊥ (⊢∷ dwt restwt)) =
  stepᶜᶜ (_ , ξ-pair (β-⊥Lᶜ dwt) refl)
progressᶜᶜ (⊢∷ (⊢? g) (⊢∷ (⊢! g′) restwt))
  with progressᶜᶜ (⊢∷ (⊢! g′) restwt)
progressᶜᶜ (⊢∷ (⊢? g) (⊢∷ (⊢! g′) restwt))
  | done restnf = done (nf-step nf-? irred-?! restnf)
progressᶜᶜ (⊢∷ (⊢? g) (⊢∷ (⊢! g′) restwt))
  | stepᶜᶜ (_ , rest→rest′) = stepᶜᶜ (_ , ξ-∷ᶜ rest→rest′)
progressᶜᶜ (⊢∷ (⊢? G-⇒) (⊢∷ (⊢↦ cwt dwt) restwt))
  with progressᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt)
progressᶜᶜ (⊢∷ (⊢? G-⇒) (⊢∷ (⊢↦ cwt dwt) restwt))
  | done restnf = done (nf-step nf-? irred-?↦ restnf)
progressᶜᶜ (⊢∷ (⊢? G-⇒) (⊢∷ (⊢↦ cwt dwt) restwt))
  | stepᶜᶜ (_ , rest→rest′) = stepᶜᶜ (_ , ξ-∷ᶜ rest→rest′)
progressᶜᶜ (⊢∷ (⊢? g) (⊢∷ ⊢⊥ restwt))
  with progressᶜᶜ (⊢∷ ⊢⊥ restwt)
progressᶜᶜ (⊢∷ (⊢? g) (⊢∷ ⊢⊥ restwt))
  | done restnf = done (nf-step nf-? irred-?⊥ restnf)
progressᶜᶜ (⊢∷ (⊢? g) (⊢∷ ⊢⊥ restwt))
  | stepᶜᶜ (_ , rest→rest′) = stepᶜᶜ (_ , ξ-∷ᶜ rest→rest′)

preserve-—↠ᶜᶜ : ∀ {c c′ A B}
  → ⊢ c ⦂ A ⇨ B
  → c —↠ᶜᶜ c′
  → ⊢ c′ ⦂ A ⇨ B
preserve-—↠ᶜᶜ cwt (_ ∎ᶜᶜ) = cwt
preserve-—↠ᶜᶜ cwt (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠c′) =
  preserve-—↠ᶜᶜ (preserve-—→ᶜᶜ cwt c→c₁) c₁↠c′

multi-ξ-∷ᶜᶜ : ∀ {c cs cs′}
  → cs —↠ᶜᶜ cs′
  → (c ∷ cs) —↠ᶜᶜ (c ∷ cs′)
multi-ξ-∷ᶜᶜ (_ ∎ᶜᶜ) = (_ ∷ _) ∎ᶜᶜ
multi-ξ-∷ᶜᶜ (_ —→ᶜᶜ⟨ cs→cs₁ ⟩ cs₁↠cs′) =
  (_ ∷ _) —→ᶜᶜ⟨ ξ-∷ᶜ cs→cs₁ ⟩ multi-ξ-∷ᶜᶜ cs₁↠cs′

multi-ξ-↦₁ᶜᶜ : ∀ {c c′ d}
  → c —↠ᶜᶜ c′
  → singleᶜ (c ↦ d) —↠ᶜᶜ singleᶜ (c′ ↦ d)
multi-ξ-↦₁ᶜᶜ (_ ∎ᶜᶜ) = singleᶜ (_ ↦ _) ∎ᶜᶜ
multi-ξ-↦₁ᶜᶜ (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠c′) =
  singleᶜ (_ ↦ _) —→ᶜᶜ⟨ ξ-↦₁ᶜ c→c₁ ⟩
  multi-ξ-↦₁ᶜᶜ c₁↠c′

multi-ξ-↦₂ᶜᶜ : ∀ {c d d′}
  → d —↠ᶜᶜ d′
  → singleᶜ (c ↦ d) —↠ᶜᶜ singleᶜ (c ↦ d′)
multi-ξ-↦₂ᶜᶜ (_ ∎ᶜᶜ) = singleᶜ (_ ↦ _) ∎ᶜᶜ
multi-ξ-↦₂ᶜᶜ (_ —→ᶜᶜ⟨ d→d₁ ⟩ d₁↠d′) =
  singleᶜ (_ ↦ _) —→ᶜᶜ⟨ ξ-↦₂ᶜ d→d₁ ⟩
  multi-ξ-↦₂ᶜᶜ d₁↠d′

mutual
  singleSize : Crcn → Nat
  singleSize (G !) = 1
  singleSize (G ？ ℓ) = 1
  singleSize (c ↦ d) = 1 + (seqSize c + seqSize d)
  singleSize (⊥ᶜ A ⇨ B at ℓ) = 1

  seqSize : Coercion → Nat
  seqSize [] = 0
  seqSize (c ∷ cs) = singleSize c + seqSize cs

singleSize-positive : ∀ c → 0 < singleSize c
singleSize-positive (G !) = 0<1+n
singleSize-positive (G ？ ℓ) = 0<1+n
singleSize-positive (c ↦ d) = 0<1+n
singleSize-positive (⊥ᶜ A ⇨ B at ℓ) = 0<1+n

seqSize-++ : ∀ c d → seqSize (c ++ d) ≡ seqSize c + seqSize d
seqSize-++ [] d = refl
seqSize-++ (c ∷ cs) d
  rewrite seqSize-++ cs d
        | sym (+-assoc (singleSize c) (seqSize cs) (seqSize d)) =
  refl

seqSize-⨟ : ∀ c d → seqSize (c ⨟ d) ≡ seqSize c + seqSize d
seqSize-⨟ [] d = refl
seqSize-⨟ (c ∷ cs) d
  rewrite seqSize-⨟ cs d
        | sym (+-assoc (singleSize c) (seqSize cs) (seqSize d)) =
  refl

↦-pair-size : ∀ c d c′ d′
  → 1 + singleSize ((c′ ⨟ c) ↦ (d ⨟ d′))
      ≡ singleSize (c ↦ d) + singleSize (c′ ↦ d′)
↦-pair-size c d c′ d′
  rewrite seqSize-⨟ c′ c
        | seqSize-⨟ d d′ =
  solve 4
    (λ a b c d →
      con 1 :+ (con 1 :+ ((c :+ a) :+ (b :+ d)))
        :=ᵉ (con 1 :+ (a :+ b)) :+ (con 1 :+ (c :+ d)))
    refl
    (seqSize c)
    (seqSize d)
    (seqSize c′)
    (seqSize d′)
  where
  open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ᵉ_)

pair-step-decreases : ∀ {c d d′}
  → c ; d —→ᶜ d′
  → seqSize d′ < singleSize c + singleSize d
pair-step-decreases β-proj-inj-okᶜ = s≤s z≤n
pair-step-decreases (β-proj-inj-badᶜ G≢H) = n<1+n 1
pair-step-decreases {c = c ↦ d} {d = c′ ↦ d′} β-↦ᶜ
  rewrite +-identityʳ (singleSize ((c′ ⨟ c) ↦ (d ⨟ d′))) =
  subst (singleSize ((c′ ⨟ c) ↦ (d ⨟ d′)) <_)
        (↦-pair-size c d c′ d′)
        (n<1+n _)
pair-step-decreases {d = d} (β-⊥Lᶜ dwt) =
  s≤s (singleSize-positive d)
pair-step-decreases β-!⊥ᶜ = n<1+n 1
pair-step-decreases {c = c ↦ d} (β-↦⊥ᶜ cwt dwt)
  rewrite +-comm (seqSize c + seqSize d) 1 =
  s≤s (s≤s z≤n)

step-decreases : ∀ {c d}
  → c —→ᶜᶜ d
  → seqSize d < seqSize c
step-decreases (ξ-pair {c₁} {c₂} {d̅} {c̅} c₁;c₂→d̅ refl)
  rewrite seqSize-++ d̅ c̅ =
  subst (seqSize d̅ + seqSize c̅ <_)
        (+-assoc (singleSize c₁) (singleSize c₂) (seqSize c̅))
        (+-monoˡ-< (seqSize c̅) (pair-step-decreases c₁;c₂→d̅))
step-decreases (ξ-∷ᶜ {c = c} cs→cs′) =
  +-monoʳ-< (singleSize c) (step-decreases cs→cs′)
step-decreases (ξ-↦₁ᶜ {d = d} {cs = cs} c→c′) =
  +-monoˡ-< (seqSize cs)
    (s≤s (+-monoˡ-< (seqSize d) (step-decreases c→c′)))
step-decreases (ξ-↦₂ᶜ {c = c} {cs = cs} d→d′) =
  +-monoˡ-< (seqSize cs)
    (s≤s (+-monoʳ-< (seqSize c) (step-decreases d→d′)))

normalize-acc : ∀ {c A B}
  → Acc _<_ (seqSize c)
  → ⊢ c ⦂ A ⇨ B
  → Σ[ d ∈ Coercion ] ((c —↠ᶜᶜ d) × Normalᶜ d)
normalize-acc (acc rec) cwt with progressᶜᶜ cwt
... | done nf = _ , ((_ ∎ᶜᶜ) , nf)
... | stepᶜᶜ (d , c→d)
    with normalize-acc (rec (step-decreases c→d))
                       (preserve-—→ᶜᶜ cwt c→d)
...   | e , (d↠e , nf) = e , ((_ —→ᶜᶜ⟨ c→d ⟩ d↠e) , nf)

normalization : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Σ[ d ∈ Coercion ] ((c —↠ᶜᶜ d) × Normalᶜ d)
normalization {c = c} cwt = normalize-acc (<-wellFounded (seqSize c)) cwt

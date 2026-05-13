module CoercionReduction where

-- Coercion lists for GTLC, including blame coercions, adjacent-cell
-- reduction, preservation, and normal-form syntax for the reduction proof
-- development.  This file is intentionally self-contained rather than
-- re-exporting the older binary sequencing presentation from Coercions.

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import GTLC

infixr 7 _⨟_
infixr 6 _↦_

-- This adds ⊥ compared to Coercion in Coercions.agda.
data Crcn : Set where
  idᶜ    : Ty → Crcn
  _!     : Ty → Crcn -- injection (tagging)
  _`?    : {ℓ : Nat} → Ty → Crcn -- projection (tag checking)
  _↦_    : List Crcn → List Crcn → Crcn
  ⊥ᶜ_⇨_ : Ty → Ty → Crcn

Coercion : Set
Coercion = List Crcn

_⨟_ : Coercion → Coercion → Coercion
[] ⨟ d = d
(c ∷ cs) ⨟ d = c ∷ (cs ⨟ d)

singleᶜ : Crcn → Coercion
singleᶜ c = c ∷ []

data Atomic : Crcn → Set where
  atom-idᶜ : ∀ {A} → Atomic (idᶜ A)
  atom-! : ∀ {G} → Atomic (G !)
  atom-? : ∀ {G ℓ} → Atomic ((_`? {ℓ = ℓ}) G)

infix 4 ⊢_⦂_⇨ᶜ_
infix 4 ⊢_⦂_⇨_

data ⊢_⦂_⇨_ : Coercion → Ty → Ty → Set

data ⊢_⦂_⇨ᶜ_ : Crcn → Ty → Ty → Set where
  ⊢idᶜ : ∀ {A}
    → ⊢ idᶜ A ⦂ A ⇨ᶜ A

  ⊢! : ∀ {G}
    → Ground G
    → ⊢ G ! ⦂ G ⇨ᶜ ★

  ⊢? : ∀ {G ℓ}
    → Ground G
    → ⊢ ((_`? {ℓ = ℓ}) G) ⦂ ★ ⇨ᶜ G

  ⊢↦ : ∀ {A B C D c d}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ᶜ (C ⇒ D)

  ⊢⊥ : ∀ {A B}
    → ⊢ (⊥ᶜ A ⇨ B) ⦂ A ⇨ᶜ B

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

coerce : ∀ {A B} → Nat → A ~ B → Coercion
coerce ℓ ~-ℕ = singleᶜ (idᶜ ℕ)
coerce ℓ ~-★ = singleᶜ (idᶜ ★)
coerce ℓ ★~ℕ = singleᶜ ((_`? {ℓ = ℓ}) ℕ)
coerce ℓ ℕ~★ = singleᶜ (ℕ !)
coerce ℓ (★~⇒ c d) =
  singleᶜ ((_`? {ℓ = ℓ}) (★ ⇒ ★)) ⨟
  singleᶜ (coerce ℓ c ↦ coerce ℓ d)
coerce ℓ (⇒~★ c d) =
  singleᶜ (coerce ℓ c ↦ coerce ℓ d) ⨟
  singleᶜ ((★ ⇒ ★) !)
coerce ℓ (~-⇒ c d) = singleᶜ (coerce ℓ c ↦ coerce ℓ d)

coerce-wt : ∀ {A B} (ℓ : Nat) (p : A ~ B) → ⊢ coerce ℓ p ⦂ A ⇨ B
coerce-wt ℓ ~-ℕ = ⊢singleᶜ ⊢idᶜ
coerce-wt ℓ ~-★ = ⊢singleᶜ ⊢idᶜ
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
  coercion-crcn-target-unique ⊢idᶜ ⊢idᶜ = refl
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
  coercion-crcn-source-unique ⊢idᶜ ⊢idᶜ = refl
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

infix 4 _—→ᶜᶜ_
infix 3 _∎ᶜᶜ
infixr 2 _—→ᶜᶜ⟨_⟩_
infix 2 _—↠ᶜᶜ_

data _—→ᶜᶜ_ : Coercion → Coercion → Set where
  β-proj-inj-okᶜ : ∀ {G ℓ cs}
    → (G ! ∷ ((_`? {ℓ = ℓ}) G) ∷ cs) —→ᶜᶜ (idᶜ G ∷ cs)

  β-proj-inj-badᶜ : ∀ {G H ℓ cs}
    → G ≢ H
    → (G ! ∷ ((_`? {ℓ = ℓ}) H) ∷ cs) —→ᶜᶜ ((⊥ᶜ G ⇨ H) ∷ cs)

  β-idLᶜ : ∀ {A d cs}
    → (idᶜ A ∷ d ∷ cs) —→ᶜᶜ (d ∷ cs)

  β-idRᶜ : ∀ {B c cs}
    → (c ∷ idᶜ B ∷ cs) —→ᶜᶜ (c ∷ cs)

  β-↦ᶜ : ∀ {c d c′ d′ cs}
    → ((c ↦ d) ∷ (c′ ↦ d′) ∷ cs) —→ᶜᶜ
      (((c′ ⨟ c) ↦ (d ⨟ d′)) ∷ cs)

  β-⊥Lᶜ : ∀ {A B C d cs}
    → ⊢ d ⦂ B ⇨ᶜ C
    → ((⊥ᶜ A ⇨ B) ∷ d ∷ cs) —→ᶜᶜ ((⊥ᶜ A ⇨ C) ∷ cs)

  β-!⊥ᶜ : ∀ {G B cs}
    → (G ! ∷ (⊥ᶜ ★ ⇨ B) ∷ cs) —→ᶜᶜ ((⊥ᶜ G ⇨ B) ∷ cs)

  β-↦⊥ᶜ : ∀ {c d A B C D E cs}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ((c ↦ d) ∷ (⊥ᶜ (C ⇒ D) ⇨ E) ∷ cs) —→ᶜᶜ
      ((⊥ᶜ (A ⇒ B) ⇨ E) ∷ cs)

  ξ-∷ᶜ : ∀ {c cs cs′}
    → cs —→ᶜᶜ cs′
    → (c ∷ cs) —→ᶜᶜ (c ∷ cs′)

  ξ-↦₁ᶜ : ∀ {c c′ d cs}
    → c —→ᶜᶜ c′
    → ((c ↦ d) ∷ cs) —→ᶜᶜ ((c′ ↦ d) ∷ cs)

  ξ-↦₂ᶜ : ∀ {c d d′ cs}
    → d —→ᶜᶜ d′
    → ((c ↦ d) ∷ cs) —→ᶜᶜ ((c ↦ d′) ∷ cs)

  -- consider adding:
  --  idᶜ A ↦ idᶜ B —→ᶜᶜ idᶜ (A ⇒ B)

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

preserve-—→ᶜᶜ : ∀ {c c′ A B}
  → ⊢ c ⦂ A ⇨ B
  → c —→ᶜᶜ c′
  → ⊢ c′ ⦂ A ⇨ B
preserve-—→ᶜᶜ (⊢∷ (⊢! g) (⊢∷ (⊢? g′) restwt))
  β-proj-inj-okᶜ = ⊢∷ ⊢idᶜ restwt
preserve-—→ᶜᶜ (⊢∷ (⊢! g) (⊢∷ (⊢? g′) restwt))
  (β-proj-inj-badᶜ G≢H) = ⊢∷ ⊢⊥ restwt
preserve-—→ᶜᶜ (⊢∷ ⊢idᶜ (⊢∷ dwt restwt)) β-idLᶜ =
  ⊢∷ dwt restwt
preserve-—→ᶜᶜ (⊢∷ cwt (⊢∷ ⊢idᶜ restwt)) β-idRᶜ =
  ⊢∷ cwt restwt
preserve-—→ᶜᶜ
  (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢↦ c′wt d′wt) restwt))
  β-↦ᶜ = ⊢∷ (⊢↦ (⊢⨟ c′wt cwt) (⊢⨟ dwt d′wt)) restwt
preserve-—→ᶜᶜ (⊢∷ ⊢⊥ (⊢∷ dwt restwt)) (β-⊥Lᶜ dwt′)
  with coercion-crcn-target-unique dwt dwt′
... | refl = ⊢∷ ⊢⊥ restwt
preserve-—→ᶜᶜ (⊢∷ (⊢! g) (⊢∷ ⊢⊥ restwt)) β-!⊥ᶜ =
  ⊢∷ ⊢⊥ restwt
preserve-—→ᶜᶜ (⊢∷ (⊢↦ cwt dwt) (⊢∷ ⊢⊥ restwt))
  (β-↦⊥ᶜ cwt′ dwt′)
  with coercion-target-unique cwt cwt′ | coercion-source-unique dwt dwt′
... | refl | refl = ⊢∷ ⊢⊥ restwt
preserve-—→ᶜᶜ (⊢∷ cwt restwt) (ξ-∷ᶜ cs→cs′) =
  ⊢∷ cwt (preserve-—→ᶜᶜ restwt cs→cs′)
preserve-—→ᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) (ξ-↦₁ᶜ c→c′) =
  ⊢∷ (⊢↦ (preserve-—→ᶜᶜ cwt c→c′) dwt) restwt
preserve-—→ᶜᶜ (⊢∷ (⊢↦ cwt dwt) restwt) (ξ-↦₂ᶜ d→d′) =
  ⊢∷ (⊢↦ cwt (preserve-—→ᶜᶜ dwt d→d′)) restwt

----------------------------------------------------------------
-- Coercion Normal Forms
----------------------------------------------------------------

data Normalᶜ : Coercion → Set where
  nf-[] : Normalᶜ []

  nf-id : ∀ {A}
    → Normalᶜ (singleᶜ (idᶜ A))

  nf-? : ∀ {G}
    → Ground G
    → ∀ {ℓ} → Normalᶜ (singleᶜ ((_`? {ℓ = ℓ}) G))

  nf-! : ∀ {G}
    → Ground G
    → Normalᶜ (singleᶜ (G !))

  nf-?! : ∀ {G ℓ}
    → Ground G
    → Normalᶜ (((_`? {ℓ = ℓ}) G) ∷ G ! ∷ [])

  nf-↦ : ∀ {c d}
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ (singleᶜ (c ↦ d))

  nf-?↦ : ∀ {G c d ℓ}
    → Ground G
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ (((_`? {ℓ = ℓ}) G) ∷ (c ↦ d) ∷ [])

  nf-↦! : ∀ {c d G}
    → Normalᶜ c
    → Normalᶜ d
    → Ground G
    → Normalᶜ ((c ↦ d) ∷ G ! ∷ [])

  nf-?↦! : ∀ {G c d ℓ}
    → Ground G
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ (((_`? {ℓ = ℓ}) G) ∷ (c ↦ d) ∷ G ! ∷ [])

  nf-?⊥ : ∀ {G A B ℓ}
    → Ground G
    → Normalᶜ (((_`? {ℓ = ℓ}) G) ∷ (⊥ᶜ A ⇨ B) ∷ [])

  nf-⊥ : ∀ {A B}
    → Normalᶜ (singleᶜ (⊥ᶜ A ⇨ B))

Step : Coercion → Set
Step c = Σ[ c′ ∈ Coercion ] c —→ᶜᶜ c′

step : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → Maybe (Step c)
step ⊢[] = nothing
step (⊢∷ ⊢idᶜ ⊢[]) = nothing
step (⊢∷ (⊢! g) ⊢[]) = nothing
step (⊢∷ (⊢? g) ⊢[]) = nothing
step (⊢∷ ⊢⊥ ⊢[]) = nothing
step (⊢∷ ⊢idᶜ (⊢∷ dwt restwt)) = just (_ , β-idLᶜ)
step (⊢∷ (⊢↦ cwt dwt) restwt) with step cwt
step (⊢∷ (⊢↦ cwt dwt) restwt) | just (_ , c→c′) =
  just (_ , ξ-↦₁ᶜ c→c′)
step (⊢∷ (⊢↦ cwt dwt) restwt) | nothing with step dwt
step (⊢∷ (⊢↦ cwt dwt) restwt) | nothing | just (_ , d→d′) =
  just (_ , ξ-↦₂ᶜ d→d′)
step (⊢∷ (⊢↦ cwt dwt) ⊢[]) | nothing | nothing = nothing
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ ⊢idᶜ restwt))
  | nothing | nothing = just (_ , β-idRᶜ)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ (⊢↦ c′wt d′wt) restwt))
  | nothing | nothing = just (_ , β-↦ᶜ)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ ⊢⊥ restwt))
  | nothing | nothing = just (_ , β-↦⊥ᶜ cwt dwt)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ dwt′ restwt))
  | nothing | nothing
  with step (⊢∷ dwt′ restwt)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ dwt′ restwt))
  | nothing | nothing | just (_ , d→d′) = just (_ , ξ-∷ᶜ d→d′)
step (⊢∷ (⊢↦ cwt dwt) (⊢∷ dwt′ restwt))
  | nothing | nothing | nothing = nothing
step (⊢∷ cwt (⊢∷ ⊢idᶜ restwt)) = just (_ , β-idRᶜ)
step (⊢∷ (⊢! {G = G} g) (⊢∷ (⊢? {G = H} h) restwt))
  with G ≟Ty H
step (⊢∷ (⊢! g) (⊢∷ (⊢? h) restwt)) | yes refl =
  just (_ , β-proj-inj-okᶜ)
step (⊢∷ (⊢! g) (⊢∷ (⊢? h) restwt)) | no G≢H =
  just (_ , β-proj-inj-badᶜ G≢H)
step (⊢∷ (⊢! g) (⊢∷ ⊢⊥ restwt)) = just (_ , β-!⊥ᶜ)
step (⊢∷ ⊢⊥ (⊢∷ dwt restwt)) = just (_ , β-⊥Lᶜ dwt)
step (⊢∷ cwt (⊢∷ dwt restwt)) with step (⊢∷ dwt restwt)
step (⊢∷ cwt (⊢∷ dwt restwt)) | just (_ , d→d′) =
  just (_ , ξ-∷ᶜ d→d′)
step (⊢∷ cwt (⊢∷ dwt restwt)) | nothing = nothing

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

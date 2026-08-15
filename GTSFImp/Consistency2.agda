module Consistency2 where

-- File Charter:
--   * Defines a deterministic common-lower selector for type consistency.
--   * Defines consistency as successful selection by `lower?`.
--   * Proves proof irrelevance of the resulting consistency evidence.
--   * Leaves equivalence with declarative consistency to
--     `proof.Consistency2`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Fin.Properties as Fin
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; s≤s)
import Data.Nat as Nat
import Data.Nat.Induction as NatInduction
open import Data.Nat.Properties using
  (+-mono-≤; +-monoʳ-≤; +-suc; m≤m+n; m≤n+m; n<1+n;
   n≤1+n; +-comm; ≤-<-trans)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; inspect; [_])
open import Relation.Nullary using (no; yes)

open import Types
import Consistency as C
import Imprecision as I

------------------------------------------------------------------------
-- The canonical imprecision environments induced by consistency
------------------------------------------------------------------------

leftᵐ : ∀ {Δ} → C.Env∼ Δ → I.ImpEnv Δ
leftᵐ μ X with μ X
leftᵐ μ X | C.X∼X = I.X⊑X
leftᵐ μ X | C.★∼X∼★ = I.X⊑X
leftᵐ μ X | C.X∼★ = I.X⊑X
leftᵐ μ X | C.★∼X = I.X⊑★

rightᵐ : ∀ {Δ} → C.Env∼ Δ → I.ImpEnv Δ
rightᵐ μ X with μ X
rightᵐ μ X | C.X∼X = I.X⊑X
rightᵐ μ X | C.★∼X∼★ = I.X⊑X
rightᵐ μ X | C.X∼★ = I.X⊑★
rightᵐ μ X | C.★∼X = I.X⊑X

------------------------------------------------------------------------
-- Constructing imprecision to the dynamic type
------------------------------------------------------------------------

AllDynamic : ∀ {Δ} → I.ImpEnv Δ → Ty Δ → Set
AllDynamic μ A = ∀ X → X ∈ᵗ A → μ X ≡ I.X⊑★

dynamic-domain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → AllDynamic μ (A ⇒ B)
  → AllDynamic μ A
dynamic-domain dynamic X X∈A = dynamic X (∈-fun-left X∈A)

dynamic-codomain : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → AllDynamic μ (A ⇒ B)
  → AllDynamic μ B
dynamic-codomain {A = A} dynamic X X∈B with occurs? X A
dynamic-codomain dynamic X X∈B | present X∈A =
  dynamic X (∈-fun-left X∈A)
dynamic-codomain dynamic X X∈B | absent X∉A =
  dynamic X (∈-fun-right X∉A X∈B)

dynamic-under-inst : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A : Ty (Nat.suc Δ)}
  → AllDynamic μ (`∀ A)
  → AllDynamic (I.instᵐ μ) A
dynamic-under-inst dynamic zero X∈A = refl
dynamic-under-inst dynamic (suc X) X∈A =
  dynamic X (∈-all X∈A)

dynamic-under-ext : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A : Ty (Nat.suc Δ)}
  → AllDynamic μ (`∀ A)
  → zero ∉ᵗ A
  → AllDynamic (I.extᵐ μ) A
dynamic-under-ext dynamic zero∉A zero X∈A =
  ⊥-elim (not-occurs zero∉A X∈A)
  where
  not-occurs : ∀ {Δ} {X : TyVar Δ} {B : Ty Δ}
    → X ∉ᵗ B
    → X ∈ᵗ B
    → ⊥
  not-occurs (∉-var X≠Y) var-∈ = ≢ᶠ→≢ X≠Y refl
  not-occurs ∉-base ()
  not-occurs ∉-star ()
  not-occurs (∉-fun X∉B X∉C) (∈-fun-left X∈B) =
    not-occurs X∉B X∈B
  not-occurs (∉-fun X∉B X∉C) (∈-fun-right X∉B′ X∈C) =
    not-occurs X∉C X∈C
  not-occurs (∉-all X∉B) (∈-all X∈B) =
    not-occurs X∉B X∈B
dynamic-under-ext dynamic zero∉A (suc X) X∈A =
  dynamic X (∈-all X∈A)

data AllChoice {Δ : TyCtx} : Ty (Nat.suc Δ) → Set where
  bottom-choice : AllChoice (＇ zero)
  star-choice : AllChoice ★
  inst-choice : ∀ {A}
    → NonVar A
    → zero ∈ᵗ A
    → AllChoice A
  structural-choice : ∀ {A}
    → NonStar A
    → zero ∉ᵗ A
    → AllChoice A

all-choice : ∀ {Δ} (A : Ty (Nat.suc Δ)) → AllChoice A
all-choice (＇ zero) = bottom-choice
all-choice (＇ (suc X)) =
  structural-choice nonstar-X (∉-var (≢→≢ᶠ (λ ())))
all-choice (‵ ι) = structural-choice nonstar-ι ∉-base
all-choice ★ = star-choice
all-choice (A ⇒ B) with occurs? zero (A ⇒ B)
all-choice (A ⇒ B) | present zero∈A⇒B =
  inst-choice nonvar-fun zero∈A⇒B
all-choice (A ⇒ B) | absent zero∉A⇒B =
  structural-choice nonstar-⇒ zero∉A⇒B
all-choice (`∀ A) with occurs? zero (`∀ A)
all-choice (`∀ A) | present zero∈∀A =
  inst-choice nonvar-all zero∈∀A
all-choice (`∀ A) | absent zero∉∀A =
  structural-choice nonstar-∀ zero∉∀A

to-star : ∀ {Δ} {μ : I.ImpEnv Δ} (A : Ty Δ)
  → AllDynamic μ A
  → I._⊢_⊑_ μ A ★
to-star (＇ X) dynamic = I.X⊑★ (dynamic X var-∈)
to-star (‵ ι) dynamic = I.ι⊑★
to-star ★ dynamic = I.★⊑★
to-star (A ⇒ B) dynamic =
  I.⇒⊑★ (to-star A (dynamic-domain dynamic))
        (to-star B (dynamic-codomain dynamic))
to-star (`∀ A) dynamic = decide (all-choice A)
  where
  decide : AllChoice A → I._⊢_⊑_ _ (`∀ A) ★
  decide bottom-choice = I.bot⊑★
  decide star-choice = I.∀★⊑★
  decide (inst-choice Anv zero∈A) =
    I.∀⊑ Anv zero∈A (to-star A (dynamic-under-inst dynamic))
  decide (structural-choice Ans zero∉A) =
    I.∀⊑★ Ans (to-star A (dynamic-under-ext dynamic zero∉A))

dynamic? : ∀ {Δ} (μ : I.ImpEnv Δ) (A : Ty Δ)
  → Maybe (AllDynamic μ A)
dynamic? μ (＇ X) with μ X | inspect μ X
dynamic? μ (＇ X) | I.X⊑X | [ eq ] = nothing
dynamic? μ (＇ X) | I.X⊑★ | [ eq ] =
  just (λ { .X var-∈ → eq })
dynamic? μ (‵ ι) = just (λ X ())
dynamic? μ ★ = just (λ X ())
dynamic? μ (A ⇒ B) with dynamic? μ A
dynamic? μ (A ⇒ B) | nothing = nothing
dynamic? μ (A ⇒ B) | just dynamic-A with dynamic? μ B
dynamic? μ (A ⇒ B) | just dynamic-A | nothing = nothing
dynamic? μ (A ⇒ B) | just dynamic-A | just dynamic-B =
  just combine
  where
  combine : AllDynamic μ (A ⇒ B)
  combine X (∈-fun-left X∈A) = dynamic-A X X∈A
  combine X (∈-fun-right X∉A X∈B) = dynamic-B X X∈B
dynamic? μ (`∀ A) with dynamic? (I.instᵐ μ) A
dynamic? μ (`∀ A) | nothing = nothing
dynamic? μ (`∀ A) | just dynamic-A =
  just under-all
  where
  under-all : AllDynamic μ (`∀ A)
  under-all X (∈-all X∈A) = dynamic-A (suc X) X∈A

------------------------------------------------------------------------
-- Proof-carrying search for a common lower bound
------------------------------------------------------------------------

record Lower {Δ : TyCtx} (φ ψ : I.ImpEnv Δ)
    (A B : Ty Δ) : Set where
  constructor lower
  field
    lower-type : Ty Δ
    lower-left : I._⊢_⊑_ φ lower-type A
    lower-right : I._⊢_⊑_ ψ lower-type B

open Lower public

refl⊑ : ∀ {Δ} (μ : I.ImpEnv Δ) (A : Ty Δ)
  → I._⊢_⊑_ μ A A
refl⊑ μ (＇ X) = I.X⊑X
refl⊑ μ (‵ ι) = I.ι⊑ι
refl⊑ μ ★ = I.★⊑★
refl⊑ μ (A ⇒ B) = I.⇒⊑⇒ (refl⊑ μ A) (refl⊑ μ B)
refl⊑ μ (`∀ A) = I.∀⊑∀ (refl⊑ (I.extᵐ μ) A)

nonVar? : ∀ {Δ} (A : Ty Δ) → Maybe (NonVar A)
nonVar? (＇ X) = nothing
nonVar? (‵ ι) = just nonvar-base
nonVar? ★ = just nonvar-star
nonVar? (A ⇒ B) = just nonvar-fun
nonVar? (`∀ A) = just nonvar-all

infixr 3 _orElse_

_orElse_ : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
just x orElse y = just x
nothing orElse y = y

arrow-lower : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A A′ B B′ : Ty Δ}
  → Maybe (Lower ψ φ A′ A)
  → Maybe (Lower φ ψ B B′)
  → Maybe (Lower φ ψ (A ⇒ B) (A′ ⇒ B′))
arrow-lower nothing right = nothing
arrow-lower (just left) nothing = nothing
arrow-lower (just (lower C C⊑A′ C⊑A))
    (just (lower D D⊑B D⊑B′)) =
  just (lower (C ⇒ D) (I.⇒⊑⇒ C⊑A D⊑B)
                         (I.⇒⊑⇒ C⊑A′ D⊑B′))

all-lower : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A B : Ty (Nat.suc Δ)}
  → Maybe (Lower (I.extᵐ φ) (I.extᵐ ψ) A B)
  → Maybe (Lower φ ψ (`∀ A) (`∀ B))
all-lower nothing = nothing
all-lower (just (lower D D⊑A D⊑B)) =
  just (lower (`∀ D) (I.∀⊑∀ D⊑A) (I.∀⊑∀ D⊑B))

inst-lower : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A : Ty (Nat.suc Δ)} {B : Ty Δ}
  → Maybe (Lower (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ B))
  → Maybe (Lower φ ψ (`∀ A) B)
inst-lower nothing = nothing
inst-lower (just (lower D D⊑A D⊑B)) with nonVar? D
inst-lower (just (lower D D⊑A D⊑B)) | nothing = nothing
inst-lower (just (lower D D⊑A D⊑B)) | just Dnv
    with occurs? zero D
inst-lower (just (lower D D⊑A D⊑B)) | just Dnv
    | absent zero∉D = nothing
inst-lower (just (lower D D⊑A D⊑B)) | just Dnv
    | present zero∈D =
  just (lower (`∀ D) (I.∀⊑∀ D⊑A)
                         (I.∀⊑ Dnv zero∈D D⊑B))

gen-lower : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A : Ty Δ} {B : Ty (Nat.suc Δ)}
  → Maybe (Lower (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ A) B)
  → Maybe (Lower φ ψ A (`∀ B))
gen-lower nothing = nothing
gen-lower (just (lower D D⊑A D⊑B)) with nonVar? D
gen-lower (just (lower D D⊑A D⊑B)) | nothing = nothing
gen-lower (just (lower D D⊑A D⊑B)) | just Dnv
    with occurs? zero D
gen-lower (just (lower D D⊑A D⊑B)) | just Dnv
    | absent zero∉D = nothing
gen-lower (just (lower D D⊑A D⊑B)) | just Dnv
    | present zero∈D =
  just (lower (`∀ D) (I.∀⊑ Dnv zero∈D D⊑A)
                         (I.∀⊑∀ D⊑B))

bot-lower : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
  → (A B : Ty (Nat.suc Δ))
  → Maybe (Lower φ ψ (`∀ A) (`∀ B))
bot-lower (＇ zero) ★ =
  just (lower (`∀ (＇ zero)) (refl⊑ _ _) I.bot-elim)
bot-lower ★ (＇ zero) =
  just (lower (`∀ (＇ zero)) I.bot-elim (refl⊑ _ _))
bot-lower A B = nothing

size : ∀ {Δ} → Ty Δ → ℕ
size (＇ X) = 1
size (‵ ι) = 1
size ★ = 1
size (A ⇒ B) = 1 + size A + size B
size (`∀ A) = 1 + size A

size-rename : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty Δ)
  → size (renameᵗ ρ A) ≡ size A
size-rename ρ (＇ X) = refl
size-rename ρ (‵ ι) = refl
size-rename ρ ★ = refl
size-rename ρ (A ⇒ B)
    rewrite size-rename ρ A | size-rename ρ B =
  refl
size-rename ρ (`∀ A) rewrite size-rename (extᵗ ρ) A = refl

size-shift : ∀ {Δ} (A : Ty Δ) → size (⇑ᵗ A) ≡ size A
size-shift = size-rename suc

arrow-left-size : ∀ {Δ} (A B A′ B′ : Ty Δ)
  → size A + size A′ < size (A ⇒ B) + size (A′ ⇒ B′)
arrow-left-size A B A′ B′ =
  ≤-<-trans child≤components components<arrows
  where
  child≤components :
      size A + size A′
      ≤ (size A + size B) + (size A′ + size B′)
  child≤components =
    +-mono-≤ (m≤m+n (size A) (size B))
             (m≤m+n (size A′) (size B′))

  components<arrows :
      (size A + size B) + (size A′ + size B′)
      < size (A ⇒ B) + size (A′ ⇒ B′)
  components<arrows =
    s≤s
      (+-monoʳ-≤ (size A + size B)
        (n≤1+n (size A′ + size B′)))

arrow-left-size-swapped : ∀ {Δ} (A B A′ B′ : Ty Δ)
  → size A′ + size A < size (A ⇒ B) + size (A′ ⇒ B′)
arrow-left-size-swapped A B A′ B′
    rewrite +-comm (size A′) (size A) =
  arrow-left-size A B A′ B′

arrow-right-size : ∀ {Δ} (A B A′ B′ : Ty Δ)
  → size B + size B′ < size (A ⇒ B) + size (A′ ⇒ B′)
arrow-right-size A B A′ B′ =
  ≤-<-trans child≤components components<arrows
  where
  child≤components :
      size B + size B′
      ≤ (size A + size B) + (size A′ + size B′)
  child≤components =
    +-mono-≤ (m≤n+m (size B) (size A))
             (m≤n+m (size B′) (size A′))

  components<arrows :
      (size A + size B) + (size A′ + size B′)
      < size (A ⇒ B) + size (A′ ⇒ B′)
  components<arrows =
    s≤s
      (+-monoʳ-≤ (size A + size B)
        (n≤1+n (size A′ + size B′)))

all-size-less : ∀ {Δ} (A B : Ty (Nat.suc Δ))
  → size A + size B < size (`∀ A) + size (`∀ B)
all-size-less A B =
  s≤s (+-monoʳ-≤ (size A) (n≤1+n (size B)))

inst-size-less : ∀ {Δ} (A : Ty (Nat.suc Δ)) (B : Ty Δ)
  → size A + size (⇑ᵗ B) < size (`∀ A) + size B
inst-size-less A B rewrite size-shift B = n<1+n _

gen-size-less : ∀ {Δ} (A : Ty Δ) (B : Ty (Nat.suc Δ))
  → size (⇑ᵗ A) + size B < size A + size (`∀ B)
gen-size-less A B rewrite size-shift A | +-suc (size A) (size B) =
  n<1+n _

lowerAcc : ∀ {Δ} (φ ψ : I.ImpEnv Δ) (A B : Ty Δ)
  → Acc _<_ (size A + size B)
  → Maybe (Lower φ ψ A B)
lowerAcc φ ψ A ★ access with dynamic? ψ A
lowerAcc φ ψ A ★ access | nothing = nothing
lowerAcc φ ψ A ★ access | just dynamic =
  just (lower A (refl⊑ φ A) (to-star A dynamic))
lowerAcc φ ψ ★ B access with dynamic? φ B
lowerAcc φ ψ ★ B access | nothing = nothing
lowerAcc φ ψ ★ B access | just dynamic =
  just (lower B (to-star B dynamic) (refl⊑ ψ B))
lowerAcc φ ψ (＇ X) (＇ Y) access with X Fin.≟ Y
lowerAcc φ ψ (＇ X) (＇ .X) access | yes refl =
  just (lower (＇ X) I.X⊑X I.X⊑X)
lowerAcc φ ψ (＇ X) (＇ Y) access | no X≠Y = nothing
lowerAcc φ ψ (‵ ι) (‵ ι′) access with ι ≟Base ι′
lowerAcc φ ψ (‵ ι) (‵ .ι) access | yes refl =
  just (lower (‵ ι) I.ι⊑ι I.ι⊑ι)
lowerAcc φ ψ (‵ ι) (‵ ι′) access | no ι≠ι′ = nothing
lowerAcc φ ψ (A ⇒ B) (A′ ⇒ B′) (acc smaller) =
  arrow-lower
    (lowerAcc ψ φ A′ A
      (smaller (arrow-left-size-swapped A B A′ B′)))
    (lowerAcc φ ψ B B′ (smaller (arrow-right-size A B A′ B′)))
lowerAcc φ ψ (`∀ A) (`∀ B) (acc smaller) =
  all-lower
    (lowerAcc (I.extᵐ φ) (I.extᵐ ψ) A B
      (smaller (all-size-less A B)))
  orElse
  (inst-lower
    (lowerAcc (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ (`∀ B))
      (smaller (inst-size-less A (`∀ B)))))
  orElse
  gen-lower
    (lowerAcc (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ (`∀ A)) B
      (smaller (gen-size-less (`∀ A) B)))
  orElse
  bot-lower A B
lowerAcc φ ψ (`∀ A) B (acc smaller) =
  inst-lower
    (lowerAcc (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ B)
      (smaller (inst-size-less A B)))
lowerAcc φ ψ A (`∀ B) (acc smaller) =
  gen-lower
    (lowerAcc (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ A) B
      (smaller (gen-size-less A B)))
lowerAcc φ ψ A B access = nothing

------------------------------------------------------------------------
-- The unique consistency relation
------------------------------------------------------------------------

data IsJust {A : Set} : Maybe A → Set where
  is-just : ∀ {x} → IsJust (just x)

is-just-unique : ∀ {A : Set} {value : Maybe A}
  → (p q : IsJust value)
  → p ≡ q
is-just-unique is-just is-just = refl

lower? : ∀ {Δ} → Ty Δ → Ty Δ → Maybe (Ty Δ)
lower? A B =
  map lower-type
    (lowerAcc I.idᵐ I.idᵐ A B (NatInduction.<-wellFounded _))

infix 4 _∼ᵘ_

_∼ᵘ_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ∼ᵘ B = IsJust (lower? A B)

∼ᵘ-unique : ∀ {Δ} {A B : Ty Δ} (c d : A ∼ᵘ B) → c ≡ d
∼ᵘ-unique = is-just-unique

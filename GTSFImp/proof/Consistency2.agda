module proof.Consistency2 where

-- File Charter:
--   * Proves that the unique consistency relation in `Consistency2` is
--     equivalent to declarative consistency.
--   * Uses the existing common-lower characterization for soundness.
--   * Proves completeness by following a declarative derivation through the
--     deterministic lower-bound search.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Fin.Properties as Fin
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (_+_; _<_)
import Data.Nat as Nat
import Data.Nat.Induction as NatInduction
open import Data.Product using (_×_; _,_; ∃)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; inspect; [_]; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
import Consistency as C
open import Consistency2
import Imprecision as I
open import proof.ImprecisionConsistency
  using (CrossFree; CrossFree∼★; CrossFree★∼; LowerEnv; VarLower;
         both-to-star; cf-!; cf-↦; cf-∀ᶜ; cf-？; cf-bot-elim;
         cf-bot-intro; cf-gen; cf-id; cf-inst; cf-X∼★ᵍ; cf-⇒∼★;
         cf-∀∼★; cf-ι∼★; cf-★∼Xᵍ; cf-★∼⇒; cf-★∼∀;
         cf-★∼ι;
         common-lower-consistent; cross-refl;
         extend-lower-env; identity-lower-env; instantiate-left-lower-env;
         instantiate-right-lower-env; flip-lower-env;
         source-nonvar-from-target;
         target-occurs-source; shift-occurs; unshift-occurs; var-from-star;
         var-refl; var-to-star)

------------------------------------------------------------------------
-- Small facts about successful searches
------------------------------------------------------------------------

map-success : ∀ {A B : Set} {f : A → B} {value : Maybe A}
  → IsJust value
  → IsJust (map f value)
map-success is-just = is-just

orElse-left : ∀ {A : Set} {left right : Maybe A}
  → IsJust left
  → IsJust (left orElse right)
orElse-left is-just = is-just

orElse-right : ∀ {A : Set} {left right : Maybe A}
  → IsJust right
  → IsJust (left orElse right)
orElse-right {left = just x} success = is-just
orElse-right {left = nothing} success = success

four-second : ∀ {A : Set} (first second third fourth : Maybe A)
  → IsJust second
  → IsJust (first orElse second orElse third orElse fourth)
four-second (just x) second third fourth success = is-just
four-second nothing (just x) third fourth is-just = is-just

four-third : ∀ {A : Set} (first second third fourth : Maybe A)
  → IsJust third
  → IsJust (first orElse second orElse third orElse fourth)
four-third (just x) second third fourth success = is-just
four-third nothing (just x) third fourth success = is-just
four-third nothing nothing (just x) fourth is-just = is-just

four-fourth : ∀ {A : Set} (first second third fourth : Maybe A)
  → IsJust fourth
  → IsJust (first orElse second orElse third orElse fourth)
four-fourth (just x) second third fourth success = is-just
four-fourth nothing (just x) third fourth success = is-just
four-fourth nothing nothing (just x) fourth success = is-just
four-fourth nothing nothing nothing (just x) is-just = is-just

arrow-lower-success : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A A′ B B′ : Ty Δ}
    {left : Maybe (Lower ψ φ A′ A)}
    {right : Maybe (Lower φ ψ B B′)}
  → IsJust left
  → IsJust right
  → IsJust (arrow-lower left right)
arrow-lower-success is-just is-just = is-just

all-lower-success : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A B : Ty (Nat.suc Δ)}
    {result : Maybe (Lower (I.extᵐ φ) (I.extᵐ ψ) A B)}
  → IsJust result
  → IsJust (all-lower result)
all-lower-success is-just = is-just

nonVar-success : ∀ {Δ} {A : Ty Δ}
  → NonVar A
  → IsJust (nonVar? A)
nonVar-success nonvar-base = is-just
nonVar-success nonvar-star = is-just
nonVar-success nonvar-fun = is-just
nonVar-success nonvar-all = is-just

not-occurs : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∉ᵗ A
  → X ∈ᵗ A
  → ⊥
not-occurs (∉-var X≠Y) var-∈ = X≠Y refl
not-occurs ∉-base ()
not-occurs ∉-star ()
not-occurs (∉-fun X∉A X∉B) (∈-fun-left X∈A) =
  not-occurs X∉A X∈A
not-occurs (∉-fun X∉A X∉B) (∈-fun-right X∉A′ X∈B) =
  not-occurs X∉B X∈B
not-occurs (∉-all X∉A) (∈-all X∈A) =
  not-occurs X∉A X∈A

occurs-success : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ}
  → X ∈ᵗ A
  → ∃ λ X∈A → occurs? X A ≡ present X∈A
occurs-success {X = X} {A = A} X∈A with occurs? X A
occurs-success X∈A | present X∈A′ = X∈A′ , refl
occurs-success X∈A | absent X∉A = ⊥-elim (not-occurs X∉A X∈A)

inst-lower-success : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A : Ty (Nat.suc Δ)} {B : Ty Δ}
    {result : Maybe (Lower (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ B))}
  → NonVar A
  → zero ∈ᵗ A
  → IsJust result
  → IsJust (inst-lower result)
inst-lower-success {result = just (lower D D⊑A D⊑B)} Anv zero∈A
    is-just
    with nonVar? D | nonVar-success
      (source-nonvar-from-target D⊑A Anv zero∈A)
inst-lower-success {result = just (lower D D⊑A D⊑B)} Anv zero∈A
    is-just | nothing | ()
inst-lower-success {result = just (lower D D⊑A D⊑B)} Anv zero∈A
    is-just | just Dnv | is-just
    with occurs? zero D | occurs-success (target-occurs-source D⊑A zero∈A)
inst-lower-success {result = just (lower D D⊑A D⊑B)} Anv zero∈A
    is-just | just Dnv | is-just | absent zero∉D | D∈ , ()
inst-lower-success {result = just (lower D D⊑A D⊑B)} Anv zero∈A
    is-just | just Dnv | is-just | present zero∈D | D∈ , refl =
  is-just

gen-lower-success : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {A : Ty Δ} {B : Ty (Nat.suc Δ)}
    {result : Maybe (Lower (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ A) B)}
  → NonVar B
  → zero ∈ᵗ B
  → IsJust result
  → IsJust (gen-lower result)
gen-lower-success {result = just (lower D D⊑A D⊑B)} Bnv zero∈B
    is-just
    with nonVar? D | nonVar-success
      (source-nonvar-from-target D⊑B Bnv zero∈B)
gen-lower-success {result = just (lower D D⊑A D⊑B)} Bnv zero∈B
    is-just | nothing | ()
gen-lower-success {result = just (lower D D⊑A D⊑B)} Bnv zero∈B
    is-just | just Dnv | is-just
    with occurs? zero D | occurs-success (target-occurs-source D⊑B zero∈B)
gen-lower-success {result = just (lower D D⊑A D⊑B)} Bnv zero∈B
    is-just | just Dnv | is-just | absent zero∉D | D∈ , ()
gen-lower-success {result = just (lower D D⊑A D⊑B)} Bnv zero∈B
    is-just | just Dnv | is-just | present zero∈D | D∈ , refl =
  is-just

bot-left-success : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
  → IsJust (bot-lower {φ = φ} {ψ = ψ} (＇ zero) ★)
bot-left-success = is-just

bot-right-success : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
  → IsJust (bot-lower {φ = φ} {ψ = ψ} ★ (＇ zero))
bot-right-success = is-just

------------------------------------------------------------------------
-- Dynamic-occurrence tests are complete
------------------------------------------------------------------------

dynamic-success : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ}
  → AllDynamic μ A
  → IsJust (dynamic? μ A)
dynamic-success {μ = μ} {A = ＇ X} dynamic
    with μ X | inspect μ X
dynamic-success {μ = μ} {A = ＇ X} dynamic
    | I.X⊑X | [ eq ] =
  ⊥-elim (not-star (trans (sym eq) (dynamic X var-∈)))
  where
  not-star : I.X⊑X ≢ I.X⊑★
  not-star ()
dynamic-success {μ = μ} {A = ＇ X} dynamic
    | I.X⊑★ | [ eq ] =
  is-just
dynamic-success {A = ‵ ι} dynamic = is-just
dynamic-success {A = ★} dynamic = is-just
dynamic-success {μ = μ} {A = A ⇒ B} dynamic
    with dynamic? μ A | dynamic-success (dynamic-domain dynamic)
dynamic-success {μ = μ} {A = A ⇒ B} dynamic
    | nothing | ()
dynamic-success {μ = μ} {A = A ⇒ B} dynamic
    | just dynamic-A | is-just
    with dynamic? μ B | dynamic-success (dynamic-codomain dynamic)
dynamic-success {μ = μ} {A = A ⇒ B} dynamic
    | just dynamic-A | is-just | nothing | ()
dynamic-success {μ = μ} {A = A ⇒ B} dynamic
    | just dynamic-A | is-just | just dynamic-B | is-just =
  is-just
dynamic-success {μ = μ} {A = `∀ A} dynamic
    with dynamic? (I.instᵐ μ) A
       | dynamic-success (dynamic-under-inst dynamic)
dynamic-success {μ = μ} {A = `∀ A} dynamic | nothing | ()
dynamic-success {μ = μ} {A = `∀ A} dynamic
    | just dynamic-A | is-just =
  is-just

------------------------------------------------------------------------
-- Consistency with ★ makes all variables dynamic on the relevant side
------------------------------------------------------------------------

ground-occurs-to-star : ∀ {Δ} {μ : C.Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ} {g : C._⊢_∼★ μ G}
  → CrossFree∼★ g
  → X ∈ᵗ G
  → μ X ≡ C.X∼★
ground-occurs-to-star cf-⇒∼★ (∈-fun-left ())
ground-occurs-to-star cf-⇒∼★ (∈-fun-right X∉A ())
ground-occurs-to-star cf-ι∼★ ()
ground-occurs-to-star (cf-X∼★ᵍ {eq = eq}) var-∈ = eq
ground-occurs-to-star cf-∀∼★ (∈-all ())

star-no-occurs : ∀ {Δ} {X : TyVar Δ} → X ∈ᵗ ★ → ⊥
star-no-occurs ()

ground-occurs-from-star : ∀ {Δ} {μ : C.Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ} {g : C._⊢★∼_ μ G}
  → CrossFree★∼ g
  → X ∈ᵗ G
  → μ X ≡ C.★∼X
ground-occurs-from-star cf-★∼⇒ (∈-fun-left ())
ground-occurs-from-star cf-★∼⇒ (∈-fun-right X∉A ())
ground-occurs-from-star cf-★∼ι ()
ground-occurs-from-star (cf-★∼Xᵍ {eq = eq}) var-∈ = eq
ground-occurs-from-star cf-★∼∀ (∈-all ())

flip-not-from-star : ∀ {Δ} {μ : C.Env∼ Δ} {X : TyVar Δ}
  → μ X ≢ C.X∼★
  → C.flipᵐ μ X ≢ C.★∼X
flip-not-from-star not-star eq =
  not-star (C.flipVar∼-to-★∼X eq)

flip-not-to-star : ∀ {Δ} {μ : C.Env∼ Δ} {X : TyVar Δ}
  → μ X ≢ C.★∼X
  → C.flipᵐ μ X ≢ C.X∼★
flip-not-to-star not-star eq =
  not-star (C.flipVar∼-to-X∼★ eq)

mutual
  source-occurs-target-safe : ∀ {Δ} {μ : C.Env∼ Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → μ X ≢ C.X∼★
    → (c : C._⊢_∼_ μ A B)
    → CrossFree c
    → X ∈ᵗ A
    → X ∈ᵗ B
  source-occurs-target-safe not-star (C.id a) cf-id X∈A = X∈A
  source-occurs-target-safe {μ = μ} {X = X} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-left X∈A) =
    ∈-fun-left
      (target-occurs-source-safe {μ = C.flipᵐ μ} {X = X}
        (flip-not-from-star {μ = μ} {X = X} not-star)
        c c-free X∈A)
  source-occurs-target-safe {X = X} {B = A′ ⇒ B′} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-right X∉A X∈B)
      with occurs? X A′
  source-occurs-target-safe {X = X} {B = A′ ⇒ B′} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-right X∉A X∈B)
      | present X∈A′ =
    ∈-fun-left X∈A′
  source-occurs-target-safe {X = X} {B = A′ ⇒ B′} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-right X∉A X∈B)
      | absent X∉A′ =
    ∈-fun-right X∉A′
      (source-occurs-target-safe not-star d d-free X∈B)
  source-occurs-target-safe {X = X} not-star (C.∀ᶜ c)
      (cf-∀ᶜ c-free) (∈-all X∈A) =
    ∈-all
      (source-occurs-target-safe {X = suc X} not-star c c-free X∈A)
  source-occurs-target-safe not-star
      (C._! ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans ⦄)
      (cf-! gate-free c-free) X∈A =
    ⊥-elim (not-star (ground-occurs-to-star gate-free
      (source-occurs-target-safe not-star c c-free X∈A)))
  source-occurs-target-safe not-star (C.？_ c)
      (cf-？ gate-free c-free) ()
  source-occurs-target-safe {X = X} not-star
      (C.inst_ c B≢★) (cf-inst c-free) (∈-all X∈A) =
    unshift-occurs
      (source-occurs-target-safe {X = suc X} not-star c c-free X∈A)
  source-occurs-target-safe {X = X} not-star
      (C.gen_ c A≢★) (cf-gen c-free) X∈A =
    ∈-all (source-occurs-target-safe {X = suc X} not-star c c-free
      (shift-occurs X∈A))
  source-occurs-target-safe not-star C.bot-elim cf-bot-elim (∈-all ())
  source-occurs-target-safe not-star C.bot-intro cf-bot-intro (∈-all ())

  target-occurs-source-safe : ∀ {Δ} {μ : C.Env∼ Δ}
      {X : TyVar Δ} {A B : Ty Δ}
    → μ X ≢ C.★∼X
    → (c : C._⊢_∼_ μ A B)
    → CrossFree c
    → X ∈ᵗ B
    → X ∈ᵗ A
  target-occurs-source-safe not-star (C.id a) cf-id X∈B = X∈B
  target-occurs-source-safe {μ = μ} {X = X} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-left X∈A) =
    ∈-fun-left
      (source-occurs-target-safe {μ = C.flipᵐ μ} {X = X}
        (flip-not-to-star {μ = μ} {X = X} not-star)
        c c-free X∈A)
  target-occurs-source-safe {X = X} {A = A ⇒ B} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-right X∉A′ X∈B′)
      with occurs? X A
  target-occurs-source-safe {X = X} {A = A ⇒ B} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-right X∉A′ X∈B′)
      | present X∈A =
    ∈-fun-left X∈A
  target-occurs-source-safe {X = X} {A = A ⇒ B} not-star
      (c C.↦ d) (cf-↦ c-free d-free) (∈-fun-right X∉A′ X∈B′)
      | absent X∉A =
    ∈-fun-right X∉A
      (target-occurs-source-safe not-star d d-free X∈B′)
  target-occurs-source-safe {X = X} not-star (C.∀ᶜ c)
      (cf-∀ᶜ c-free) (∈-all X∈B) =
    ∈-all
      (target-occurs-source-safe {X = suc X} not-star c c-free X∈B)
  target-occurs-source-safe not-star (C._! c)
      (cf-! gate-free c-free) ()
  target-occurs-source-safe not-star
      (C.？_ ⦃ ★∼G = ★∼G ⦄ c) (cf-？ gate-free c-free) X∈B =
    ⊥-elim (not-star (ground-occurs-from-star gate-free
      (target-occurs-source-safe not-star c c-free X∈B)))
  target-occurs-source-safe {X = X} not-star
      (C.inst_ c B≢★) (cf-inst c-free) X∈B =
    ∈-all (target-occurs-source-safe {X = suc X} not-star c c-free
      (shift-occurs X∈B))
  target-occurs-source-safe {X = X} not-star
      (C.gen_ c A≢★) (cf-gen c-free) (∈-all X∈B) =
    unshift-occurs
      (target-occurs-source-safe {X = suc X} not-star c c-free X∈B)
  target-occurs-source-safe not-star C.bot-elim cf-bot-elim (∈-all ())
  target-occurs-source-safe not-star C.bot-intro cf-bot-intro (∈-all ())

right-dynamic-at : ∀ {r : C.Var∼} {l u : I.VarImp}
  → VarLower r l u
  → (r ≢ C.X∼★ → ⊥)
  → u ≡ I.X⊑★
right-dynamic-at var-refl impossible =
  ⊥-elim (impossible (λ ()))
right-dynamic-at cross-refl impossible =
  ⊥-elim (impossible (λ ()))
right-dynamic-at var-to-star impossible = refl
right-dynamic-at var-from-star impossible =
  ⊥-elim (impossible (λ ()))
right-dynamic-at both-to-star impossible = refl

left-dynamic-at : ∀ {r : C.Var∼} {l u : I.VarImp}
  → VarLower r l u
  → (r ≢ C.★∼X → ⊥)
  → l ≡ I.X⊑★
left-dynamic-at var-refl impossible =
  ⊥-elim (impossible (λ ()))
left-dynamic-at cross-refl impossible =
  ⊥-elim (impossible (λ ()))
left-dynamic-at var-to-star impossible =
  ⊥-elim (impossible (λ ()))
left-dynamic-at var-from-star impossible = refl
left-dynamic-at both-to-star impossible = refl

right-dynamic : ∀ {Δ} {μ : C.Env∼ Δ} {φ ψ}
    {A : Ty Δ}
  → LowerEnv μ φ ψ
  → (c : C._⊢_∼_ μ A ★)
  → CrossFree c
  → AllDynamic ψ A
right-dynamic h c c-free X X∈A =
  right-dynamic-at (h X)
    (λ not-star →
      star-no-occurs
        (source-occurs-target-safe not-star c c-free X∈A))

left-dynamic : ∀ {Δ} {μ : C.Env∼ Δ} {φ ψ}
    {B : Ty Δ}
  → LowerEnv μ φ ψ
  → (c : C._⊢_∼_ μ ★ B)
  → CrossFree c
  → AllDynamic φ B
left-dynamic h c c-free X X∈B =
  left-dynamic-at (h X)
    (λ not-star →
      star-no-occurs
        (target-occurs-source-safe not-star c c-free X∈B))

no-success : ∀ {A : Set} → IsJust (nothing {A = A}) → ⊥
no-success ()

right-star-test : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {A : Ty Δ}
    {access : Acc _<_ (size A + 1)}
  → IsJust (dynamic? ψ A)
  → IsJust (lowerAcc φ ψ A ★ access)
right-star-test {ψ = ψ} {A = A} success with dynamic? ψ A
right-star-test success | nothing = ⊥-elim (no-success success)
right-star-test success | just dynamic = is-just

left-star-test : ∀ {Δ} {φ ψ : I.ImpEnv Δ} {B : Ty Δ}
    {access : Acc _<_ (1 + size B)}
  → NonStar B
  → IsJust (dynamic? φ B)
  → IsJust (lowerAcc φ ψ ★ B access)
left-star-test {φ = φ} {B = ＇ X} nonstar-X success
    with dynamic? φ (＇ X)
left-star-test nonstar-X success | nothing =
  ⊥-elim (no-success success)
left-star-test nonstar-X success | just dynamic = is-just
left-star-test {φ = φ} {B = ‵ ι} nonstar-ι success = is-just
left-star-test {φ = φ} {B = A ⇒ B} nonstar-⇒ success
    with dynamic? φ (A ⇒ B)
left-star-test nonstar-⇒ success | nothing =
  ⊥-elim (no-success success)
left-star-test nonstar-⇒ success | just dynamic = is-just
left-star-test {φ = φ} {B = `∀ B} nonstar-∀ success
    with dynamic? φ (`∀ B)
left-star-test nonstar-∀ success | nothing =
  ⊥-elim (no-success success)
left-star-test nonstar-∀ success | just dynamic = is-just

right-star-success : ∀ {Δ} {μ : C.Env∼ Δ} {φ ψ}
    {A : Ty Δ}
  → LowerEnv μ φ ψ
  → (c : C._⊢_∼_ μ A ★)
  → CrossFree c
  → (access : Acc _<_ (size A + 1))
  → IsJust (lowerAcc φ ψ A ★ access)
right-star-success {φ = φ} {ψ = ψ} {A = A} h c c-free access =
  right-star-test {φ = φ} {ψ = ψ} {A = A} {access = access}
    (dynamic-success (right-dynamic h c c-free))

left-star-success : ∀ {Δ} {μ : C.Env∼ Δ} {φ ψ}
    {B : Ty Δ}
  → LowerEnv μ φ ψ
  → (c : C._⊢_∼_ μ ★ B)
  → CrossFree c
  → (access : Acc _<_ (1 + size B))
  → IsJust (lowerAcc φ ψ ★ B access)
left-star-success {B = ★} h c c-free access =
  right-star-success h c c-free access
left-star-success {φ = φ} {ψ = ψ} {B = ＇ X} h c c-free access =
  left-star-test {φ = φ} {ψ = ψ} {B = ＇ X} {access = access}
    nonstar-X (dynamic-success (left-dynamic h c c-free))
left-star-success {φ = φ} {ψ = ψ} {B = ‵ ι} h c c-free access =
  left-star-test {φ = φ} {ψ = ψ} {B = ‵ ι} {access = access}
    nonstar-ι (dynamic-success (left-dynamic h c c-free))
left-star-success {φ = φ} {ψ = ψ} {B = A ⇒ B} h c c-free access =
  left-star-test {φ = φ} {ψ = ψ} {B = A ⇒ B} {access = access}
    nonstar-⇒ (dynamic-success (left-dynamic h c c-free))
left-star-success {φ = φ} {ψ = ψ} {B = `∀ B} h c c-free access =
  left-star-test {φ = φ} {ψ = ψ} {B = `∀ B} {access = access}
    nonstar-∀ (dynamic-success (left-dynamic h c c-free))

------------------------------------------------------------------------
-- Completeness of lower-bound search
------------------------------------------------------------------------

lowerAcc-complete : ∀ {Δ} {μ : C.Env∼ Δ} {φ ψ}
    {A B : Ty Δ}
  → LowerEnv μ φ ψ
  → (c : C._⊢_∼_ μ A B)
  → CrossFree c
  → (access : Acc _<_ (size A + size B))
  → IsJust (lowerAcc φ ψ A B access)
lowerAcc-complete h c@(C.id ★) cf-id access =
  right-star-success h c cf-id access
lowerAcc-complete h (C.id (‵ ι)) cf-id access with ι ≟Base ι
lowerAcc-complete h (C.id (‵ ι)) cf-id access | yes refl = is-just
lowerAcc-complete h (C.id (‵ ι)) cf-id access | no ι≠ι =
  ⊥-elim (ι≠ι refl)
lowerAcc-complete h (C.id (＇ X)) cf-id access
    with X Fin.≟ X
lowerAcc-complete h (C.id (＇ X)) cf-id access | yes refl = is-just
lowerAcc-complete h (C.id (＇ X)) cf-id access | no X≠X =
  ⊥-elim (X≠X refl)
lowerAcc-complete {A = A ⇒ B} {B = A′ ⇒ B′} h
    (c C.↦ d) (cf-↦ c-free d-free) (acc smaller) =
  arrow-lower-success
    (lowerAcc-complete (flip-lower-env h) c c-free
      (smaller (arrow-left-size-swapped A B A′ B′)))
    (lowerAcc-complete h d d-free
      (smaller (arrow-right-size A B A′ B′)))
lowerAcc-complete {φ = φ} {ψ = ψ} {A = `∀ A} {B = `∀ B} h
    (C.∀ᶜ c) (cf-∀ᶜ c-free) (acc smaller) =
  orElse-left
    (all-lower-success
      (lowerAcc-complete (extend-lower-env h) c c-free
        (smaller (all-size-less A B))))
lowerAcc-complete h c@(C._! d) c-free access =
  right-star-success h c c-free access
lowerAcc-complete h c@(C.？_ d) c-free access =
  left-star-success h c c-free access
lowerAcc-complete {A = `∀ A} {B = ＇ X} h
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★) (cf-inst c-free)
    (acc smaller) =
  inst-lower-success Anv zero∈A
    (lowerAcc-complete (instantiate-right-lower-env h) c c-free
      (smaller (inst-size-less A (＇ X))))
lowerAcc-complete {A = `∀ A} {B = ‵ ι} h
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★) (cf-inst c-free)
    (acc smaller) =
  inst-lower-success Anv zero∈A
    (lowerAcc-complete (instantiate-right-lower-env h) c c-free
      (smaller (inst-size-less A (‵ ι))))
lowerAcc-complete {A = `∀ A} {B = ★} h
    (C.inst_ c B≢★) (cf-inst c-free) (acc smaller) =
  ⊥-elim (B≢★ refl)
lowerAcc-complete {A = `∀ A} {B = B₁ ⇒ B₂} h
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★) (cf-inst c-free)
    (acc smaller) =
  inst-lower-success Anv zero∈A
    (lowerAcc-complete (instantiate-right-lower-env h) c c-free
      (smaller (inst-size-less A (B₁ ⇒ B₂))))
lowerAcc-complete {φ = φ} {ψ = ψ} {A = `∀ A} {B = `∀ B} h
    (C.inst_ ⦃ Anv ⦄ ⦃ zero∈A ⦄ c B≢★) (cf-inst c-free)
    (acc smaller) =
  four-second
    (all-lower
      (lowerAcc (I.extᵐ φ) (I.extᵐ ψ) A B
        (smaller (all-size-less A B))))
    (inst-lower
      (lowerAcc (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ (`∀ B))
        (smaller (inst-size-less A (`∀ B)))))
    (gen-lower
      (lowerAcc (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ (`∀ A)) B
        (smaller (gen-size-less (`∀ A) B))))
    (bot-lower A B)
    (inst-lower-success Anv zero∈A
      (lowerAcc-complete (instantiate-right-lower-env h) c c-free
        (smaller (inst-size-less A (`∀ B)))))
lowerAcc-complete {A = ＇ X} {B = `∀ B} h
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★) (cf-gen c-free)
    (acc smaller) =
  gen-lower-success Bnv zero∈B
    (lowerAcc-complete (instantiate-left-lower-env h) c c-free
      (smaller (gen-size-less (＇ X) B)))
lowerAcc-complete {A = ‵ ι} {B = `∀ B} h
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★) (cf-gen c-free)
    (acc smaller) =
  gen-lower-success Bnv zero∈B
    (lowerAcc-complete (instantiate-left-lower-env h) c c-free
      (smaller (gen-size-less (‵ ι) B)))
lowerAcc-complete {A = ★} {B = `∀ B} h
    (C.gen_ c A≢★) (cf-gen c-free) (acc smaller) =
  ⊥-elim (A≢★ refl)
lowerAcc-complete {A = A₁ ⇒ A₂} {B = `∀ B} h
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★) (cf-gen c-free)
    (acc smaller) =
  gen-lower-success Bnv zero∈B
    (lowerAcc-complete (instantiate-left-lower-env h) c c-free
      (smaller (gen-size-less (A₁ ⇒ A₂) B)))
lowerAcc-complete {φ = φ} {ψ = ψ} {A = `∀ A} {B = `∀ B} h
    (C.gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c A≢★) (cf-gen c-free)
    (acc smaller) =
  four-third
    (all-lower
      (lowerAcc (I.extᵐ φ) (I.extᵐ ψ) A B
        (smaller (all-size-less A B))))
    (inst-lower
      (lowerAcc (I.extᵐ φ) (I.instᵐ ψ) A (⇑ᵗ (`∀ B))
        (smaller (inst-size-less A (`∀ B)))))
    (gen-lower
      (lowerAcc (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ (`∀ A)) B
        (smaller (gen-size-less (`∀ A) B))))
    (bot-lower A B)
    (gen-lower-success Bnv zero∈B
      (lowerAcc-complete (instantiate-left-lower-env h) c c-free
        (smaller (gen-size-less (`∀ A) B))))
lowerAcc-complete {Δ = Δ} {φ = φ} {ψ = ψ} h C.bot-elim cf-bot-elim
    (acc smaller) =
  four-fourth
    (all-lower
      (lowerAcc (I.extᵐ φ) (I.extᵐ ψ) (＇ zero) ★
        (smaller (all-size-less {Δ = Δ} (＇ zero) ★))))
    (inst-lower
      (lowerAcc (I.extᵐ φ) (I.instᵐ ψ) (＇ zero) (⇑ᵗ (`∀ ★))
        (smaller (inst-size-less {Δ = Δ} (＇ zero) (`∀ ★)))))
    (gen-lower
      (lowerAcc (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ (`∀ (＇ zero))) ★
        (smaller (gen-size-less {Δ = Δ} (`∀ (＇ zero)) ★))))
    (bot-lower (＇ zero) ★)
    bot-left-success
lowerAcc-complete {Δ = Δ} {φ = φ} {ψ = ψ} h C.bot-intro cf-bot-intro
    (acc smaller) =
  four-fourth
    (all-lower
      (lowerAcc (I.extᵐ φ) (I.extᵐ ψ) ★ (＇ zero)
        (smaller (all-size-less {Δ = Δ} ★ (＇ zero)))))
    (inst-lower
      (lowerAcc (I.extᵐ φ) (I.instᵐ ψ) ★
        (⇑ᵗ (`∀ (＇ zero)))
        (smaller (inst-size-less {Δ = Δ} ★ (`∀ (＇ zero))))))
    (gen-lower
      (lowerAcc (I.instᵐ φ) (I.extᵐ ψ) (⇑ᵗ (`∀ ★)) (＇ zero)
        (smaller (gen-size-less {Δ = Δ} (`∀ ★) (＇ zero)))))
    (bot-lower ★ (＇ zero))
    bot-right-success

------------------------------------------------------------------------
-- Equivalence
------------------------------------------------------------------------

∼→∼ᵘ : ∀ {Δ} {A B : Ty Δ}
  → (c : C._∼_ A B)
  → CrossFree c
  → A ∼ᵘ B
∼→∼ᵘ c c-free =
  map-success
    (lowerAcc-complete identity-lower-env c c-free
      (NatInduction.<-wellFounded _))

∼ᵘ→∼ : ∀ {Δ} {A B : Ty Δ}
  → A ∼ᵘ B
  → C._∼_ A B
∼ᵘ→∼ {A = A} {B = B} unique
    with lowerAcc I.idᵐ I.idᵐ A B
      (NatInduction.<-wellFounded _)
∼ᵘ→∼ unique | nothing with unique
∼ᵘ→∼ unique | nothing | ()
∼ᵘ→∼ unique | just (lower D D⊑A D⊑B) =
  common-lower-consistent (D , D⊑A , D⊑B)

consistency↔consistency2 : ∀ {Δ} {A B : Ty Δ}
  → ((c : C._∼_ A B) → CrossFree c → A ∼ᵘ B)
    × (A ∼ᵘ B → C._∼_ A B)
consistency↔consistency2 = ∼→∼ᵘ , ∼ᵘ→∼

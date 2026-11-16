module proof.DenotSubst where

-- File Charter:
--   * Substitution lemmas for the denotation (Denotation.agda), each in
--     both directions at once: a lemma is stated for a Way w, where
--     Subᴿ fwd R T is R ⊆ᴿ T and Subᴿ bwd R T is T ⊆ᴿ R.
--       - names for type variables (⟦⟧-substᵀ, with ⟦⟧ᶜ-substᵖ and
--         ⟦⟧ˢ-substˢ for casts and stacks): ⟦ substᵀ τ M ⟧ θ ρ ≈
--         ⟦ M ⟧ θ′ ρ when θ′ i ≡ ⟦ τ i ⟧ₙ θ; the instance for β-inst is
--         ⟦⟧-[]ᵀ: ⟦ M [ tseal s ]ᵀ ⟧ θ ≈ ⟦ M ⟧ (s •ᵗ θ);
--       - term renaming (⟦⟧-rename);
--       - term substitution (⟦⟧-subst): ⟦ subst σ M ⟧ θ ρ ≈ ⟦ M ⟧ θ ρ′
--         when each ⟦ σ x ⟧ θ ρ m ≈ retᴿ (ρ′ x) m; the instance for
--         β-letv and β-ƛ is ⟦⟧-[].
--     Each lemma also allows the environment ρ to grow (or shrink, bwd).
--   * The denotation of a stack of casts on a term (⟦stack⟧), and closed
--     precision derivations under substitution (⟦⟧ᵖ-substᵖ).
--   * Consumed by proof/DenotSoundness.agda and the relational proofs.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import Terms
open import GraphModel
open import Denotation
open import proof.DenotProps
open import proof.TermSubst using (substᵖ-fuse)

------------------------------------------------------------------------
-- Inclusions in either direction
------------------------------------------------------------------------

data Way : Set where
  fwd : Way
  bwd : Way

Incl : Way → 𝒱 → 𝒱 → Set
Incl fwd D E = D ⊆ E
Incl bwd D E = E ⊆ D

Inclᴿ : Way → ℛ → ℛ → Set
Inclᴿ fwd R T = R ⊆ᴿ T
Inclᴿ bwd R T = T ⊆ᴿ R

-- wrapped in records, so that Agda can infer the sets from the type
record Sub (w : Way) (D E : 𝒱) : Set where
  constructor sub
  field out : Incl w D E

record Subᴿ (w : Way) (R T : ℛ) : Set where
  constructor subᴿ
  field outᴿ : Inclᴿ w R T

open Sub public
open Subᴿ public

Sub-refl : ∀ w {D} → Sub w D D
Sub-refl fwd = sub ⊆-refl
Sub-refl bwd = sub ⊆-refl

Subᴿ-refl : ∀ w {R} → Subᴿ w R R
Subᴿ-refl fwd = subᴿ ⊆ᴿ-refl
Subᴿ-refl bwd = subᴿ ⊆ᴿ-refl

Subᴿ-trans : ∀ w {R T U} → Subᴿ w R T → Subᴿ w T U → Subᴿ w R U
Subᴿ-trans fwd (subᴿ R⊆) (subᴿ T⊆) = subᴿ (⊆ᴿ-trans R⊆ T⊆)
Subᴿ-trans bwd (subᴿ R⊇) (subᴿ T⊇) = subᴿ (⊆ᴿ-trans T⊇ R⊇)

Subᴿ-≡ : ∀ w {R T} → R ≡ T → Subᴿ w R T
Subᴿ-≡ w refl = Subᴿ-refl w

ext-Sub : ∀ w {D D′ ρ ρ′} → Sub w D D′ → (∀ x → Sub w (ρ x) (ρ′ x))
  → ∀ x → Sub w ((D • ρ) x) ((D′ • ρ′) x)
ext-Sub w D⊆ ρ⊆ zero = D⊆
ext-Sub w D⊆ ρ⊆ (suc x) = ρ⊆ x

------------------------------------------------------------------------
-- The operators in either direction
------------------------------------------------------------------------

ret-sub : ∀ w {D E n} → Sub w D E → Subᴿ w (retᴿ D n) (retᴿ E n)
ret-sub fwd (sub D⊆) = subᴿ (retᴿ-mono D⊆)
ret-sub bwd (sub D⊇) = subᴿ (retᴿ-mono D⊇)

bind-sub : ∀ w {R R′ K K′} → Subᴿ w R R′
  → (∀ {D D′} m → Sub w D D′ → Subᴿ w (K D m) (K′ D′ m))
  → Subᴿ w (R ≫= K) (R′ ≫= K′)
bind-sub fwd (subᴿ R⊆) K⊆ =
  subᴿ (≫=-mono R⊆ (λ m D⊆ → outᴿ (K⊆ m (sub D⊆))))
bind-sub bwd (subᴿ R⊇) K⊇ =
  subᴿ (≫=-mono R⊇ (λ m D⊆ → outᴿ (K⊇ m (sub D⊆))))

guard-sub : ∀ w {v D D′ R R′} → Sub w D D′ → Subᴿ w R R′
  → Subᴿ w (guard v D R) (guard v D′ R′)
guard-sub fwd (sub D⊆) (subᴿ R⊆) = subᴿ (guard-mono D⊆ R⊆)
guard-sub bwd (sub D⊇) (subᴿ R⊇) = subᴿ (guard-mono D⊇ R⊇)

Λ-sub : ∀ w {F F′} → (∀ D m → Subᴿ w (F D m) (F′ D m))
  → Sub w (Λ F) (Λ F′)
Λ-sub fwd F⊆ = sub (Λ-mono (λ D m → outᴿ (F⊆ D m)))
Λ-sub bwd F⊇ = sub (Λ-mono (λ D m → outᴿ (F⊇ D m)))

●-sub : ∀ w {D D′ E E′ m} → Sub w D D′ → Sub w E E′
  → Subᴿ w (D ●[ m ] E) (D′ ●[ m ] E′)
●-sub fwd (sub D⊆) (sub E⊆) = subᴿ (●-mono D⊆ E⊆)
●-sub bwd (sub D⊇) (sub E⊇) = subᴿ (●-mono D⊇ E⊇)

Λᴾ-sub : ∀ w {F F′} → (∀ σ → Subᴿ w (F σ) (F′ σ))
  → Sub w (Λᴾ F) (Λᴾ F′)
Λᴾ-sub fwd F⊆ = sub (Λᴾ-mono (λ σ → outᴿ (F⊆ σ)))
Λᴾ-sub bwd F⊇ = sub (Λᴾ-mono (λ σ → outᴿ (F⊇ σ)))

◆-sub : ∀ w {D D′ σ} → Sub w D D′ → Subᴿ w (D ◆ σ) (D′ ◆ σ)
◆-sub fwd (sub D⊆) = subᴿ (◆-mono D⊆)
◆-sub bwd (sub D⊇) = subᴿ (◆-mono D⊇)

sealᴾ-sub : ∀ w {σ σ′ D D′} → σ ≡ σ′ → Sub w D D′
  → Sub w (sealᴾ σ D) (sealᴾ σ′ D′)
sealᴾ-sub fwd refl (sub D⊆) = sub (sealᴾ-mono D⊆)
sealᴾ-sub bwd refl (sub D⊇) = sub (sealᴾ-mono D⊇)

unsealᴾ-sub : ∀ w {σ σ′ D D′} → σ ≡ σ′ → Sub w D D′
  → Sub w (unsealᴾ σ D) (unsealᴾ σ′ D′)
unsealᴾ-sub fwd refl (sub D⊆) = sub (unsealᴾ-mono D⊆)
unsealᴾ-sub bwd refl (sub D⊇) = sub (unsealᴾ-mono D⊇)

injᴾ-sub : ∀ w {G G′ D D′} → G ≡ G′ → Sub w D D′
  → Sub w (injᴾ G D) (injᴾ G′ D′)
injᴾ-sub fwd refl (sub D⊆) = sub (injᴾ-mono D⊆)
injᴾ-sub bwd refl (sub D⊇) = sub (injᴾ-mono D⊇)

testᴾ-sub : ∀ w {G G′ D D′} → G ≡ G′ → Sub w D D′
  → Sub w (testᴾ G D) (testᴾ G′ D′)
testᴾ-sub fwd refl (sub D⊆) = sub (testᴾ-mono D⊆)
testᴾ-sub bwd refl (sub D⊇) = sub (testᴾ-mono D⊇)

proj-sub : ∀ w {G G′ D D′ m} → G ≡ G′ → Sub w D D′
  → Subᴿ w (proj G D m) (proj G′ D′ m)
proj-sub fwd refl (sub D⊆) = subᴿ (proj-mono D⊆)
proj-sub bwd refl (sub D⊇) = subᴿ (proj-mono D⊇)

condᴿ-sub : ∀ w {D D′ R R′ T T′} → Sub w D D′ → Subᴿ w R R′ → Subᴿ w T T′
  → Subᴿ w (condᴿ D R T) (condᴿ D′ R′ T′)
condᴿ-sub fwd (sub D⊆) (subᴿ R⊆) (subᴿ T⊆) = subᴿ (condᴿ-mono D⊆ R⊆ T⊆)
condᴿ-sub bwd (sub D⊇) (subᴿ R⊇) (subᴿ T⊇) = subᴿ (condᴿ-mono D⊇ R⊇ T⊇)

cast-sub : ∀ w d p θ {E E′ m} → Sub w E E′
  → Subᴿ w (⟦ d , p ⟧ᶜ θ E m) (⟦ d , p ⟧ᶜ θ E′ m)
cast-sub fwd d p θ (sub E⊆) = subᴿ (⟦⟧ᶜ-mono d p θ E⊆)
cast-sub bwd d p θ (sub E⊇) = subᴿ (⟦⟧ᶜ-mono d p θ E⊇)

stack-sub : ∀ w cs θ {R R′} → Subᴿ w R R′
  → Subᴿ w (⟦ cs ⟧ˢ θ R) (⟦ cs ⟧ˢ θ R′)
stack-sub fwd cs θ (subᴿ R⊆) = subᴿ (⟦⟧ˢ-mono cs θ R⊆)
stack-sub bwd cs θ (subᴿ R⊇) = subᴿ (⟦⟧ˢ-mono cs θ R⊇)

------------------------------------------------------------------------
-- Names, grounds and precisions under substitution
------------------------------------------------------------------------

-- θ′ agrees with τ read in θ: the seal of variable i under θ′ is the
-- seal of the name τ i under θ (a record, so that θ θ′ τ are inferred)
record Agree (θ θ′ : SEnv) (τ : NSubst) : Set where
  constructor agree
  field agree-at : ∀ i → θ′ i ≡ ⟦ τ i ⟧ₙ θ
open Agree public

-- a shifted name under one more type variable
⟦⇑ₙ⟧ₙ : ∀ α s θ → ⟦ ⇑ₙ α ⟧ₙ (s •ᵗ θ) ≡ ⟦ α ⟧ₙ θ
⟦⇑ₙ⟧ₙ (tvar i) s θ = refl
⟦⇑ₙ⟧ₙ (tseal t) s θ = refl

⟦⟧ₙ-subst : ∀ {θ θ′ τ} → Agree θ θ′ τ
  → ∀ α → ⟦ substₙ τ α ⟧ₙ θ ≡ ⟦ α ⟧ₙ θ′
⟦⟧ₙ-subst (agree eq) (tvar i) = sym (eq i)
⟦⟧ₙ-subst (agree eq) (tseal s) = refl

⟦⟧ᴳ-subst : ∀ {θ θ′ τ} → Agree θ θ′ τ
  → ∀ G → ⟦ substG τ G ⟧ᴳ θ ≡ ⟦ G ⟧ᴳ θ′
⟦⟧ᴳ-subst eq (G‵ α) = cong (λ s → G‵ (tseal s)) (⟦⟧ₙ-subst eq α)
⟦⟧ᴳ-subst eq G𝔹 = refl
⟦⟧ᴳ-subst eq G⇒ = refl
⟦⟧ᴳ-subst eq G∀ = refl

⟦⟧ᵖ-substᵖ : ∀ {θ θ′ τ} → Agree θ θ′ τ
  → ∀ p → ⟦ substᵖ τ p ⟧ᵖ θ ≡ ⟦ p ⟧ᵖ θ′
⟦⟧ᵖ-substᵖ {θ} {θ′} {τ} (agree eq) p = substᵖ-fuse pt p
  where
  seal-name : ∀ α → substₙ (λ j → tseal (θ j)) α ≡ tseal (⟦ α ⟧ₙ θ)
  seal-name (tvar j) = refl
  seal-name (tseal s) = refl
  pt : ∀ i → substₙ (λ j → tseal (θ j)) (τ i) ≡ tseal (θ′ i)
  pt i = trans (seal-name (τ i)) (cong tseal (sym (eq i)))

-- moving the agreement under a binder
ext-agrees : ∀ {θ θ′ τ} s → Agree θ θ′ τ
  → Agree (s •ᵗ θ) (s •ᵗ θ′) (extₙ τ)
ext-agrees {θ} {θ′} {τ} s (agree eq) = agree pt
  where
  pt : ∀ i → (s •ᵗ θ′) i ≡ ⟦ extₙ τ i ⟧ₙ (s •ᵗ θ)
  pt zero = refl
  pt (suc i) = trans (eq i) (sym (⟦⇑ₙ⟧ₙ (τ i) s θ))

-- instantiation at a seal
single-agrees : ∀ θ s → Agree θ (s •ᵗ θ) (singleₙ (tseal s))
single-agrees θ s = agree pt
  where
  pt : ∀ i → (s •ᵗ θ) i ≡ ⟦ singleₙ (tseal s) i ⟧ₙ θ
  pt zero = refl
  pt (suc i) = refl

-- shifting
shift-agrees : ∀ θ s → Agree (s •ᵗ θ) θ ↑ₙ
shift-agrees θ s = agree (λ i → refl)

------------------------------------------------------------------------
-- Casts and stacks under substitution of names
------------------------------------------------------------------------

⟦⟧ᶜ-substᵖ : ∀ w d p {θ θ′ τ E E′ m} → Agree θ θ′ τ
  → Sub w E E′
  → Subᴿ w (⟦ d , substᵖ τ p ⟧ᶜ θ E m) (⟦ d , p ⟧ᶜ θ′ E′ m)
⟦⟧ᶜ-substᵖ w d ★⊑ eq E⊆ = ret-sub w E⊆
⟦⟧ᶜ-substᵖ w d 𝔹⊑ eq E⊆ = ret-sub w E⊆
⟦⟧ᶜ-substᵖ w d (‵⊑ α) eq E⊆ = ret-sub w E⊆
⟦⟧ᶜ-substᵖ w d (p ⇒⊑ q) eq E⊆ =
  guard-sub w E⊆ (ret-sub w (Λ-sub w (λ D m′ →
    bind-sub w (⟦⟧ᶜ-substᵖ w (flip d) p eq (Sub-refl w)) (λ m₁ D⊆ →
      bind-sub w (●-sub w E⊆ D⊆) (λ m₂ → ⟦⟧ᶜ-substᵖ w d q eq)))))
⟦⟧ᶜ-substᵖ w d (∀⊑ p) eq E⊆ =
  guard-sub w E⊆ (ret-sub w (Λᴾ-sub w (λ σ →
    bind-sub w (◆-sub w E⊆) (λ m₁ →
      ⟦⟧ᶜ-substᵖ w d p (ext-agrees σ eq)))))
⟦⟧ᶜ-substᵖ w up (tag G p) eq E⊆ =
  bind-sub w (⟦⟧ᶜ-substᵖ w up p eq E⊆)
    (λ m₁ D⊆ →
      ret-sub w (injᴾ-sub w (⟦⟧ᴳ-subst eq G) D⊆))
⟦⟧ᶜ-substᵖ w down (tag G p) eq E⊆ =
  bind-sub w (proj-sub w (⟦⟧ᴳ-subst eq G) E⊆)
    (λ m₁ → ⟦⟧ᶜ-substᵖ w down p eq)

⟦⟧ˢ-substˢ : ∀ w cs {θ θ′ τ R R′} → Agree θ θ′ τ
  → Subᴿ w R R′
  → Subᴿ w (⟦ substˢ τ cs ⟧ˢ θ R) (⟦ cs ⟧ˢ θ′ R′)
⟦⟧ˢ-substˢ w [] eq R⊆ = R⊆
⟦⟧ˢ-substˢ w ((d , p) ∷ cs) eq R⊆ =
  bind-sub w (⟦⟧ˢ-substˢ w cs eq R⊆)
    (λ m → ⟦⟧ᶜ-substᵖ w d p eq)

------------------------------------------------------------------------
-- Terms under substitution of names
------------------------------------------------------------------------

⟦⟧-substᵀ : ∀ w M {θ θ′ ρ ρ′ τ n}
  → Agree θ θ′ τ
  → (∀ x → Sub w (ρ x) (ρ′ x))
  → Subᴿ w (⟦ substᵀ τ M ⟧ θ ρ n) (⟦ M ⟧ θ′ ρ′ n)
⟦⟧-substᵀ w (` x) eq ρ⊆ = ret-sub w (ρ⊆ x)
⟦⟧-substᵀ w ℧ eq ρ⊆ = Subᴿ-refl w
⟦⟧-substᵀ w true eq ρ⊆ = Subᴿ-refl w
⟦⟧-substᵀ w false eq ρ⊆ = Subᴿ-refl w
⟦⟧-substᵀ w (if L M N) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w L eq ρ⊆) (λ m D⊆ →
    condᴿ-sub w D⊆ (⟦⟧-substᵀ w M eq ρ⊆) (⟦⟧-substᵀ w N eq ρ⊆))
⟦⟧-substᵀ w (ƛ A M) eq ρ⊆ =
  ret-sub w (Λ-sub w (λ D m →
    ⟦⟧-substᵀ w M eq (ext-Sub w (Sub-refl w) ρ⊆)))
⟦⟧-substᵀ w (L · M) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w L eq ρ⊆) (λ n₁ F⊆ →
    bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ n₂ E⊆ → ●-sub w F⊆ E⊆))
⟦⟧-substᵀ w (letv M N) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ m D⊆ →
    ⟦⟧-substᵀ w N eq (ext-Sub w D⊆ ρ⊆))
⟦⟧-substᵀ w (seal α M) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ m D⊆ →
    ret-sub w (sealᴾ-sub w (⟦⟧ₙ-subst eq α) D⊆))
⟦⟧-substᵀ w (unseal α M) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ m D⊆ →
    ret-sub w (unsealᴾ-sub w (⟦⟧ₙ-subst eq α) D⊆))
⟦⟧-substᵀ w (is G M) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ m D⊆ →
    ret-sub w (testᴾ-sub w (⟦⟧ᴳ-subst eq G) D⊆))
⟦⟧-substᵀ w (inj G M) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ m D⊆ →
    ret-sub w (injᴾ-sub w (⟦⟧ᴳ-subst eq G) D⊆))
⟦⟧-substᵀ w (cast d p M) eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆)
    (λ m → ⟦⟧ᶜ-substᵖ w d p eq)
⟦⟧-substᵀ w (Λν cs M) eq ρ⊆ =
  ret-sub w (Λᴾ-sub w (λ σ →
    ⟦⟧ˢ-substˢ w cs (ext-agrees σ eq)
      (⟦⟧-substᵀ w M (ext-agrees σ eq) ρ⊆)))
⟦⟧-substᵀ w (inst M B N) {θ} {θ′} {ρ} {ρ′} {τ} eq ρ⊆ =
  bind-sub w (⟦⟧-substᵀ w M eq ρ⊆) (λ n₁ F⊆ →
    bind-sub w (◆-sub w F⊆) (λ {E} {E′} n₂ E⊆ →
      ⟦⟧-substᵀ w N {n₁ •ᵗ θ} {n₁ •ᵗ θ′} {E • ρ} {E′ • ρ′} {extₙ τ} {n₂}
        (ext-agrees n₁ eq) (ext-Sub w E⊆ ρ⊆)))

⟦⟧-[]ᵀ : ∀ w M {θ ρ ρ′ n} s → (∀ x → Sub w (ρ x) (ρ′ x))
  → Subᴿ w (⟦ M [ tseal s ]ᵀ ⟧ θ ρ n) (⟦ M ⟧ (s •ᵗ θ) ρ′ n)
⟦⟧-[]ᵀ w M {θ} s ρ⊆ = ⟦⟧-substᵀ w M (single-agrees θ s) ρ⊆

⟦⟧ˢ-[]ᵀ : ∀ w cs {θ R R′} s → Subᴿ w R R′
  → Subᴿ w (⟦ substˢ (singleₙ (tseal s)) cs ⟧ˢ θ R) (⟦ cs ⟧ˢ (s •ᵗ θ) R′)
⟦⟧ˢ-[]ᵀ w cs {θ} s R⊆ = ⟦⟧ˢ-substˢ w cs (single-agrees θ s) R⊆

------------------------------------------------------------------------
-- Stacks
------------------------------------------------------------------------

⟦stack⟧ : ∀ cs M θ ρ n
  → ⟦ stack cs M ⟧ θ ρ n ≡ ⟦ cs ⟧ˢ θ (⟦ M ⟧ θ ρ n)
⟦stack⟧ [] M θ ρ n = refl
⟦stack⟧ ((d , p) ∷ cs) M θ ρ n =
  cong (λ R → R ≫= ⟦ d , p ⟧ᶜ θ) (⟦stack⟧ cs M θ ρ n)

------------------------------------------------------------------------
-- Term renaming
------------------------------------------------------------------------

ext-ren : ∀ w (r : Rename) {D D′} (ρ ρ′ : Env) → Sub w D D′
  → (∀ x → Sub w (ρ (r x)) (ρ′ x))
  → ∀ x → Sub w ((D • ρ) (ext r x)) ((D′ • ρ′) x)
ext-ren w r ρ ρ′ D⊆ h zero = D⊆
ext-ren w r ρ ρ′ D⊆ h (suc x) = h x

⟦⟧-rename : ∀ w M {θ ρ ρ′ n} (r : Rename)
  → (∀ x → Sub w (ρ (r x)) (ρ′ x))
  → Subᴿ w (⟦ rename r M ⟧ θ ρ n) (⟦ M ⟧ θ ρ′ n)
⟦⟧-rename w (` x) r h = ret-sub w (h x)
⟦⟧-rename w ℧ r h = Subᴿ-refl w
⟦⟧-rename w true r h = Subᴿ-refl w
⟦⟧-rename w false r h = Subᴿ-refl w
⟦⟧-rename w (if L M N) r h =
  bind-sub w (⟦⟧-rename w L r h) (λ m D⊆ →
    condᴿ-sub w D⊆ (⟦⟧-rename w M r h) (⟦⟧-rename w N r h))
⟦⟧-rename w (ƛ A M) {ρ = ρ} {ρ′} r h =
  ret-sub w (Λ-sub w (λ D m →
    ⟦⟧-rename w M {ρ = D • ρ} {ρ′ = D • ρ′} (ext r)
      (ext-ren w r ρ ρ′ (Sub-refl w) h)))
⟦⟧-rename w (L · M) r h =
  bind-sub w (⟦⟧-rename w L r h) (λ n₁ F⊆ →
    bind-sub w (⟦⟧-rename w M r h) (λ n₂ E⊆ → ●-sub w F⊆ E⊆))
⟦⟧-rename w (letv M N) {ρ = ρ} {ρ′} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ {D} {D′} m D⊆ →
    ⟦⟧-rename w N {ρ = D • ρ} {ρ′ = D′ • ρ′} (ext r)
      (ext-ren w r ρ ρ′ D⊆ h))
⟦⟧-rename w (seal α M) {θ = θ} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ m D⊆ →
    ret-sub w (sealᴾ-sub w {σ = ⟦ α ⟧ₙ θ} refl D⊆))
⟦⟧-rename w (unseal α M) {θ = θ} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ m D⊆ →
    ret-sub w (unsealᴾ-sub w {σ = ⟦ α ⟧ₙ θ} refl D⊆))
⟦⟧-rename w (is G M) {θ = θ} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ m D⊆ →
    ret-sub w (testᴾ-sub w {G = ⟦ G ⟧ᴳ θ} refl D⊆))
⟦⟧-rename w (inj G M) {θ = θ} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ m D⊆ →
    ret-sub w (injᴾ-sub w {G = ⟦ G ⟧ᴳ θ} refl D⊆))
⟦⟧-rename w (cast d p M) {θ = θ} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ m → cast-sub w d p θ)
⟦⟧-rename w (Λν cs M) {θ = θ} r h =
  ret-sub w (Λᴾ-sub w (λ σ →
    stack-sub w cs (σ •ᵗ θ) (⟦⟧-rename w M r h)))
⟦⟧-rename w (inst M B N) {ρ = ρ} {ρ′} r h =
  bind-sub w (⟦⟧-rename w M r h) (λ n₁ F⊆ →
    bind-sub w (◆-sub w F⊆) (λ {E} {E′} n₂ E⊆ →
      ⟦⟧-rename w N {ρ = E • ρ} {ρ′ = E′ • ρ′} (ext r)
        (ext-ren w r ρ ρ′ E⊆ h)))

------------------------------------------------------------------------
-- Term substitution
------------------------------------------------------------------------

-- extending a substitution under a term binder
exts-agrees : ∀ w (σ : Subst) {θ D D′ ρ} (ρ′ : Env)
  → Sub w D D′
  → (∀ x m → Subᴿ w (⟦ σ x ⟧ θ ρ m) (retᴿ (ρ′ x) m))
  → ∀ x m → Subᴿ w (⟦ exts σ x ⟧ θ (D • ρ) m) (retᴿ ((D′ • ρ′) x) m)
exts-agrees w σ ρ′ D⊆ h zero m = ret-sub w D⊆
exts-agrees w σ {ρ = ρ} ρ′ D⊆ h (suc x) m =
  Subᴿ-trans w (⟦⟧-rename w (σ x) {ρ′ = ρ} suc (λ y → Sub-refl w))
    (h x m)

-- moving a substitution under a type binder
⇑ˢ-agrees : ∀ w (σ : Subst) {θ ρ} (ρ′ : Env) s
  → (∀ x m → Subᴿ w (⟦ σ x ⟧ θ ρ m) (retᴿ (ρ′ x) m))
  → ∀ x m → Subᴿ w (⟦ ⇑ˢ σ x ⟧ (s •ᵗ θ) ρ m) (retᴿ (ρ′ x) m)
⇑ˢ-agrees w σ {θ} {ρ} ρ′ s h x m =
  Subᴿ-trans w
    (⟦⟧-substᵀ w (σ x) {θ = s •ᵗ θ} {θ′ = θ} {ρ = ρ} {ρ′ = ρ} {τ = ↑ₙ}
       (shift-agrees θ s) (λ y → Sub-refl w))
    (h x m)

⟦⟧-subst : ∀ w M {θ ρ ρ′ n} (σ : Subst)
  → (∀ x m → Subᴿ w (⟦ σ x ⟧ θ ρ m) (retᴿ (ρ′ x) m))
  → Subᴿ w (⟦ subst σ M ⟧ θ ρ n) (⟦ M ⟧ θ ρ′ n)
⟦⟧-subst w (` x) {n = n} σ h = h x n
⟦⟧-subst w ℧ σ h = Subᴿ-refl w
⟦⟧-subst w true σ h = Subᴿ-refl w
⟦⟧-subst w false σ h = Subᴿ-refl w
⟦⟧-subst w (if L M N) σ h =
  bind-sub w (⟦⟧-subst w L σ h) (λ m D⊆ →
    condᴿ-sub w D⊆ (⟦⟧-subst w M σ h) (⟦⟧-subst w N σ h))
⟦⟧-subst w (ƛ A M) {ρ′ = ρ′} σ h =
  ret-sub w (Λ-sub w (λ D m →
    ⟦⟧-subst w M (exts σ) (exts-agrees w σ ρ′ (Sub-refl w) h)))
⟦⟧-subst w (L · M) σ h =
  bind-sub w (⟦⟧-subst w L σ h) (λ n₁ F⊆ →
    bind-sub w (⟦⟧-subst w M σ h) (λ n₂ E⊆ → ●-sub w F⊆ E⊆))
⟦⟧-subst w (letv M N) {ρ′ = ρ′} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ m D⊆ →
    ⟦⟧-subst w N (exts σ) (exts-agrees w σ ρ′ D⊆ h))
⟦⟧-subst w (seal α M) {θ = θ} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ m D⊆ →
    ret-sub w (sealᴾ-sub w {σ = ⟦ α ⟧ₙ θ} refl D⊆))
⟦⟧-subst w (unseal α M) {θ = θ} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ m D⊆ →
    ret-sub w (unsealᴾ-sub w {σ = ⟦ α ⟧ₙ θ} refl D⊆))
⟦⟧-subst w (is G M) {θ = θ} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ m D⊆ →
    ret-sub w (testᴾ-sub w {G = ⟦ G ⟧ᴳ θ} refl D⊆))
⟦⟧-subst w (inj G M) {θ = θ} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ m D⊆ →
    ret-sub w (injᴾ-sub w {G = ⟦ G ⟧ᴳ θ} refl D⊆))
⟦⟧-subst w (cast d p M) {θ = θ} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ m → cast-sub w d p θ)
⟦⟧-subst w (Λν cs M) {θ = θ} {ρ′ = ρ′} σ h =
  ret-sub w (Λᴾ-sub w (λ s →
    stack-sub w cs (s •ᵗ θ) (⟦⟧-subst w M (⇑ˢ σ) (⇑ˢ-agrees w σ ρ′ s h))))
⟦⟧-subst w (inst M B N) {θ} {ρ} {ρ′} σ h =
  bind-sub w (⟦⟧-subst w M σ h) (λ n₁ F⊆ →
    bind-sub w (◆-sub w F⊆) (λ {E} {E′} n₂ E⊆ →
      ⟦⟧-subst w N {n₁ •ᵗ θ} {E • ρ} {E′ • ρ′} {n₂} (exts (⇑ˢ σ))
        (exts-agrees w (⇑ˢ σ) ρ′ E⊆ (⇑ˢ-agrees w σ ρ′ n₁ h))))

-- substituting a single value whose denotation is retᴿ D at every
-- counter
⟦⟧-[] : ∀ w N {θ ρ D n} V
  → (∀ m → Subᴿ w (⟦ V ⟧ θ ρ m) (retᴿ D m))
  → Subᴿ w (⟦ N [ V ] ⟧ θ ρ n) (⟦ N ⟧ θ (D • ρ) n)
⟦⟧-[] w N V hV = ⟦⟧-subst w N (single V) h
  where
  h : ∀ x m → Subᴿ w (⟦ single V x ⟧ _ _ m) (retᴿ ((_ • _) x) m)
  h zero m = hV m
  h (suc x) m = Subᴿ-refl w

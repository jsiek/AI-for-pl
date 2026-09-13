module strong.proof.CtxProperties where

-- Strong System F v7 — context facts used by progress and preservation.

open import Data.Nat using (zero; suc)
open import Data.List using (_∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.CtxMorph

fresh-abst-zero : ∀ {Δ} → Unoccupied (abst ∷ Δ) zero
fresh-abst-zero X (suc α , n-over-abst n , ())

ok-Λ : ∀ {Δ}
  → Δ ok
  → (name zero ∷ abst ∷ Δ) ok
ok-Λ ctx-ok = ok-name (ok-abst ctx-ok) a-here-abst fresh-abst-zero

named-anchor : ∀ {Δ X α}
  → Δ ok
  → Δ ∋n X := α
  → Δ ∋a α
named-anchor (ok-name ctx-ok a fresh) n-here = a-over-name a
named-anchor (ok-name ctx-ok a fresh) (n-over-name n) =
  a-over-name (named-anchor ctx-ok n)
named-anchor (ok-abst ctx-ok) (n-over-abst n) =
  a-over-abst (named-anchor ctx-ok n)
named-anchor (ok-bind ctx-ok wf) (n-over-bind n) =
  a-over-bind (named-anchor ctx-ok n)

name-of-tv : ∀ {Δ X}
  → Δ ∋tv X
  → Σ[ α ∈ Anchor ] (Δ ∋n X := α)
name-of-tv {Δ = name α ∷ Δ} tv-here = α , n-here
name-of-tv (tv-over-name x) with name-of-tv x
name-of-tv (tv-over-name x) | α , n = α , n-over-name n
name-of-tv (tv-over-abst x) with name-of-tv x
name-of-tv (tv-over-abst x) | α , n = suc α , n-over-abst n
name-of-tv (tv-over-bind x) with name-of-tv x
name-of-tv (tv-over-bind x) | α , n = suc α , n-over-bind n

quote-rep : ∀ {Δ A}
  → Δ ⊢ᵗ A
  → Σ[ R ∈ RepTy ] (Δ ⊢⌊ A ⌋ R)
quote-rep (wf-var x) with name-of-tv x
quote-rep (wf-var x) | α , n = `α α , quote-var n
quote-rep wf-ℕ = `ℕᴿ , quote-ℕ
quote-rep wf-𝔹 = `𝔹ᴿ , quote-𝔹
quote-rep (wf-⇒ a b) with quote-rep a | quote-rep b
quote-rep (wf-⇒ a b) | R , q | S , r = R ⇒ᴿ S , quote-⇒ q r
quote-rep (wf-∀ a) with quote-rep a
quote-rep (wf-∀ a) | R , q = `∀ᴿ R , quote-∀ q

data AnchorPrefix : Set where
  prefix[] : AnchorPrefix
  prefix-abst : AnchorPrefix → AnchorPrefix
  prefix-bind : RepTy → AnchorPrefix → AnchorPrefix

applyPrefix : AnchorPrefix → Ctxᵗ → Ctxᵗ
applyPrefix prefix[] Δ = Δ
applyPrefix (prefix-abst P) Δ = abst ∷ applyPrefix P Δ
applyPrefix (prefix-bind R P) Δ = bind R ∷ applyPrefix P Δ

drop-name-a-at : ∀ {P Δ β α}
  → applyPrefix P (name β ∷ Δ) ∋a α
  → applyPrefix P Δ ∋a α
drop-name-a-at {P = prefix[]} (a-over-name a) = a
drop-name-a-at {P = prefix-abst P} a-here-abst = a-here-abst
drop-name-a-at {P = prefix-abst P} (a-over-abst a) =
  a-over-abst (drop-name-a-at a)
drop-name-a-at {P = prefix-bind R P} a-here-bind = a-here-bind
drop-name-a-at {P = prefix-bind R P} (a-over-bind a) =
  a-over-bind (drop-name-a-at a)

drop-name-wfᴿ-at : ∀ {P Δ β R}
  → applyPrefix P (name β ∷ Δ) ⊢ᴿ R
  → applyPrefix P Δ ⊢ᴿ R
drop-name-wfᴿ-at (wfᴿ-var a) = wfᴿ-var (drop-name-a-at a)
drop-name-wfᴿ-at wfᴿ-ℕ = wfᴿ-ℕ
drop-name-wfᴿ-at wfᴿ-𝔹 = wfᴿ-𝔹
drop-name-wfᴿ-at (wfᴿ-⇒ r s) =
  wfᴿ-⇒ (drop-name-wfᴿ-at r) (drop-name-wfᴿ-at s)
drop-name-wfᴿ-at {P = P} (wfᴿ-∀ r) =
  wfᴿ-∀ (drop-name-wfᴿ-at {P = prefix-abst P} r)

drop-name-wfᴿ : ∀ {Δ β R}
  → (name β ∷ Δ) ⊢ᴿ R
  → Δ ⊢ᴿ R
drop-name-wfᴿ = drop-name-wfᴿ-at {P = prefix[]}

quote-wfᴿ : ∀ {Δ A R}
  → Δ ok
  → Δ ⊢⌊ A ⌋ R
  → Δ ⊢ᴿ R
quote-wfᴿ ctx-ok (quote-var n) = wfᴿ-var (named-anchor ctx-ok n)
quote-wfᴿ ctx-ok quote-ℕ = wfᴿ-ℕ
quote-wfᴿ ctx-ok quote-𝔹 = wfᴿ-𝔹
quote-wfᴿ ctx-ok (quote-⇒ q r) =
  wfᴿ-⇒ (quote-wfᴿ ctx-ok q) (quote-wfᴿ ctx-ok r)
quote-wfᴿ ctx-ok (quote-∀ q) = wfᴿ-∀ (drop-name-wfᴿ
  (quote-wfᴿ (ok-Λ ctx-ok) q))

ok-store : ∀ {Δ Θ Δ′}
  → Δ ok
  → Δ ⊢ˢ Θ ⇒ Δ′
  → Δ′ ok
ok-store ctx-ok store[] = ctx-ok
ok-store ctx-ok (store-abst s) = ok-store (ok-abst ctx-ok) s
ok-store ctx-ok (store-bind wf s) = ok-store (ok-bind ctx-ok wf) s

pop-a : ∀ {Δ α Δ′ β}
  → Δ ▷ α ↘ Δ′
  → Δ ∋a β
  → Δ′ ∋a β
pop-a pop-here (a-over-name a) = a
pop-a (pop-abst p) a-here-abst = a-here-abst
pop-a (pop-abst p) (a-over-abst a) = a-over-abst (pop-a p a)
pop-a (pop-bind p) a-here-bind = a-here-bind
pop-a (pop-bind p) (a-over-bind a) = a-over-bind (pop-a p a)

pop-wfᴿ : ∀ {Δ α Δ′ R}
  → Δ ▷ α ↘ Δ′
  → Δ ⊢ᴿ R
  → Δ′ ⊢ᴿ R
pop-wfᴿ p (wfᴿ-var a) = wfᴿ-var (pop-a p a)
pop-wfᴿ p wfᴿ-ℕ = wfᴿ-ℕ
pop-wfᴿ p wfᴿ-𝔹 = wfᴿ-𝔹
pop-wfᴿ p (wfᴿ-⇒ r s) = wfᴿ-⇒ (pop-wfᴿ p r) (pop-wfᴿ p s)
pop-wfᴿ p (wfᴿ-∀ r) = wfᴿ-∀ (pop-wfᴿ (pop-abst p) r)

ok-pop : ∀ {Δ α Δ′}
  → Δ ok
  → Δ ▷ α ↘ Δ′
  → Δ′ ok
ok-pop (ok-name ctx-ok a fresh) pop-here = ctx-ok
ok-pop (ok-abst ctx-ok) (pop-abst p) = ok-abst (ok-pop ctx-ok p)
ok-pop (ok-bind ctx-ok wf) (pop-bind p) =
  ok-bind (ok-pop ctx-ok p) (pop-wfᴿ p wf)

ok-change : ∀ {Δ δ Δ′}
  → Δ ok
  → Δ ⊢δ δ ⇒ Δ′
  → Δ′ ok
ok-change ctx-ok (step-reveal a fresh) = ok-name ctx-ok a fresh
ok-change ctx-ok (step-conceal p) = ok-pop ctx-ok p

ok-scope : ∀ {Δ χ Δ′}
  → Δ ok
  → Δ ⊢χ χ ⇒ Δ′
  → Δ′ ok
ok-scope ctx-ok scope[] = ctx-ok
ok-scope ctx-ok (scope∷ d s) = ok-scope (ok-change ctx-ok d) s

ok-boundary : ∀ {Δ Θ ΔΘ χ Δᵢ}
  → Δ ok
  → Δ ⊢ˢ Θ ⇒ ΔΘ
  → ΔΘ ⊢χ χ ⇒ Δᵢ
  → Δᵢ ok
ok-boundary ctx-ok s ch = ok-scope (ok-store ctx-ok s) ch

name-unique : ∀ {Δ X α β}
  → Δ ∋n X := α
  → Δ ∋n X := β
  → α ≡ β
name-unique n-here n-here = Relation.Binary.PropositionalEquality.refl
name-unique (n-over-name a) (n-over-name b) = name-unique a b
name-unique (n-over-abst a) (n-over-abst b)
  rewrite name-unique a b = Relation.Binary.PropositionalEquality.refl
name-unique (n-over-bind a) (n-over-bind b)
  rewrite name-unique a b = Relation.Binary.PropositionalEquality.refl

anchor-binding-unique : ∀ {Δ α a b}
  → Δ ∋ab α := a
  → Δ ∋ab α := b
  → a ≡ b
anchor-binding-unique ab-here-abst ab-here-abst =
  Relation.Binary.PropositionalEquality.refl
anchor-binding-unique ab-here-bind ab-here-bind =
  Relation.Binary.PropositionalEquality.refl
anchor-binding-unique (ab-over-abst a) (ab-over-abst b) =
  anchor-binding-unique a b
anchor-binding-unique (ab-over-bind a) (ab-over-bind b) =
  anchor-binding-unique a b
anchor-binding-unique (ab-over-name a) (ab-over-name b) =
  anchor-binding-unique a b

store-unique : ∀ {Δ Θ Δ₁ Δ₂}
  → Δ ⊢ˢ Θ ⇒ Δ₁
  → Δ ⊢ˢ Θ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
store-unique store[] store[] = Relation.Binary.PropositionalEquality.refl
store-unique (store-abst s₁) (store-abst s₂) = store-unique s₁ s₂
store-unique (store-bind wf₁ s₁) (store-bind wf₂ s₂) = store-unique s₁ s₂

pop-unique : ∀ {Δ α Δ₁ Δ₂}
  → Δ ▷ α ↘ Δ₁
  → Δ ▷ α ↘ Δ₂
  → Δ₁ ≡ Δ₂
pop-unique pop-here pop-here = Relation.Binary.PropositionalEquality.refl
pop-unique (pop-abst p₁) (pop-abst p₂)
  rewrite pop-unique p₁ p₂ = Relation.Binary.PropositionalEquality.refl
pop-unique (pop-bind p₁) (pop-bind p₂)
  rewrite pop-unique p₁ p₂ = Relation.Binary.PropositionalEquality.refl

change-unique : ∀ {Δ δ Δ₁ Δ₂}
  → Δ ⊢δ δ ⇒ Δ₁
  → Δ ⊢δ δ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
change-unique (step-reveal a₁ fresh₁) (step-reveal a₂ fresh₂) =
  Relation.Binary.PropositionalEquality.refl
change-unique (step-conceal p₁) (step-conceal p₂) = pop-unique p₁ p₂

scope-unique : ∀ {Δ χ Δ₁ Δ₂}
  → Δ ⊢χ χ ⇒ Δ₁
  → Δ ⊢χ χ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
scope-unique scope[] scope[] = Relation.Binary.PropositionalEquality.refl
scope-unique (scope∷ d₁ s₁) (scope∷ d₂ s₂)
  rewrite change-unique d₁ d₂ = scope-unique s₁ s₂

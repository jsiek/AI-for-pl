module strong.proof.CtxProperties where

-- Strong System F v7 — context facts used by progress and preservation.
--
-- With merged entries several of these get shorter or disappear.  An
-- anchor carries at most one name by construction, so `∋n → ∋a` needs no
-- well-formedness premise and going under a `∀` needs no freshness check.
-- And `SameBindings` — two contexts with the same anchor SPINE, differing
-- only in which anchors are revealed — is exactly the relation a scope
-- change preserves, which is what carries representations across one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.CtxMorph

private
  variable
    Δ Δ′ Δ₁ Δ₂ Δ₃ : Ctxᵗ
    A : Ty
    R S : RepTy
    X : ℕ
    α β : Anchor
    v w : Vis
    b : AnchorBinding
    δ : Change
    χ : Scope
    Θ : Store

------------------------------------------------------------------------
-- Same anchor spine, different visibility
------------------------------------------------------------------------

-- `SameBindings` itself now lives in strong.Ctx; here are its transports
-- for the judgments that are blind to visibility.
sb-wfᴿ : SameBindings Δ Δ′ → Δ ⊢ᴿ R → Δ′ ⊢ᴿ R
sb-wfᴿ s (wfᴿ-var a) = wfᴿ-var (sb-a s a)
sb-wfᴿ s wfᴿ-ℕ = wfᴿ-ℕ
sb-wfᴿ s wfᴿ-𝔹 = wfᴿ-𝔹
sb-wfᴿ s (wfᴿ-⇒ r t) = wfᴿ-⇒ (sb-wfᴿ s r) (sb-wfᴿ s t)
sb-wfᴿ s (wfᴿ-∀ r) = wfᴿ-∀ (sb-wfᴿ (sb-∷ s) r)

δ-bindings : Δ ⊢δ δ ⇒ Δ′ → SameBindings Δ Δ′
δ-bindings rev-here = sb-∷ sb-refl
δ-bindings (rev-under d) = sb-∷ (δ-bindings d)
δ-bindings con-here = sb-∷ sb-refl
δ-bindings (con-under d) = sb-∷ (δ-bindings d)

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

-- An anchor named by a source variable is in scope — no `ok` needed, the
-- name is a bit on the anchor's own entry.
named-anchor : Δ ∋n X := α → Δ ∋a α
named-anchor n-here = a-here
named-anchor (n-revealed n) = a-there (named-anchor n)
named-anchor (n-concealed n) = a-there (named-anchor n)

name-of-tv : Δ ∋tv X → Σ[ α ∈ Anchor ] (Δ ∋n X := α)
name-of-tv tv-here = zero , n-here
name-of-tv (tv-revealed x) with name-of-tv x
name-of-tv (tv-revealed x) | α , n = suc α , n-revealed n
name-of-tv (tv-concealed x) with name-of-tv x
name-of-tv (tv-concealed x) | α , n = suc α , n-concealed n

tv-of-name : Δ ∋n X := α → Δ ∋tv X
tv-of-name n-here = tv-here
tv-of-name (n-revealed n) = tv-revealed (tv-of-name n)
tv-of-name (n-concealed n) = tv-concealed (tv-of-name n)

name-unique : Δ ∋n X := α → Δ ∋n X := β → α ≡ β
name-unique n-here n-here = refl
name-unique (n-revealed a) (n-revealed b) = cong suc (name-unique a b)
name-unique (n-concealed a) (n-concealed b) = cong suc (name-unique a b)

------------------------------------------------------------------------
-- Quoting
------------------------------------------------------------------------

quote-rep : Δ ⊢ᵗ A → Σ[ R ∈ RepTy ] (Δ ⊢⌊ A ⌋ R)
quote-rep (wf-var x) with name-of-tv x
quote-rep (wf-var x) | α , n = `α α , quote-var n
quote-rep wf-ℕ = `ℕᴿ , quote-ℕ
quote-rep wf-𝔹 = `𝔹ᴿ , quote-𝔹
quote-rep (wf-⇒ a b) with quote-rep a | quote-rep b
quote-rep (wf-⇒ a b) | R , q | S , r = R ⇒ᴿ S , quote-⇒ q r
quote-rep (wf-∀ a) with quote-rep a
quote-rep (wf-∀ a) | R , q = `∀ᴿ R , quote-∀ q

quote-wfᴿ : Δ ⊢⌊ A ⌋ R → Δ ⊢ᴿ R
quote-wfᴿ (quote-var n) = wfᴿ-var (named-anchor n)
quote-wfᴿ quote-ℕ = wfᴿ-ℕ
quote-wfᴿ quote-𝔹 = wfᴿ-𝔹
quote-wfᴿ (quote-⇒ q r) = wfᴿ-⇒ (quote-wfᴿ q) (quote-wfᴿ r)
quote-wfᴿ (quote-∀ q) = wfᴿ-∀ (sb-wfᴿ (sb-∷ sb-refl) (quote-wfᴿ q))

------------------------------------------------------------------------
-- Well-formed contexts
------------------------------------------------------------------------

-- Going under a `∀`: one fresh anchor, abstract, with its name revealed.
ok-Λ : Δ ok → (anch revealed abstA ∷ Δ) ok
ok-Λ = ok-abst

ok-store : Δ ok → Δ ⊢ˢ Θ ⇒ Δ′ → Δ′ ok
ok-store ctx-ok store[] = ctx-ok
ok-store ctx-ok (store-abst s) = ok-store (ok-abst ctx-ok) s
ok-store ctx-ok (store-bind wf s) = ok-store (ok-bind ctx-ok wf) s

ok-change : Δ ok → Δ ⊢δ δ ⇒ Δ′ → Δ′ ok
ok-change (ok-abst o) rev-here = ok-abst o
ok-change (ok-bind o wf) rev-here = ok-bind o wf
ok-change (ok-abst o) con-here = ok-abst o
ok-change (ok-bind o wf) con-here = ok-bind o wf
ok-change (ok-abst o) (rev-under d) = ok-abst (ok-change o d)
ok-change (ok-bind o wf) (rev-under d) =
  ok-bind (ok-change o d) (sb-wfᴿ (δ-bindings d) wf)
ok-change (ok-abst o) (con-under d) = ok-abst (ok-change o d)
ok-change (ok-bind o wf) (con-under d) =
  ok-bind (ok-change o d) (sb-wfᴿ (δ-bindings d) wf)

ok-scope : Δ ok → Δ ⊢χ χ ⇒ Δ′ → Δ′ ok
ok-scope ctx-ok scope[] = ctx-ok
ok-scope ctx-ok (scope∷ d s) = ok-scope (ok-change ctx-ok d) s

ok-boundary : ∀ {ΔΘ Δᵢ} → Δ ok → Δ ⊢ˢ Θ ⇒ ΔΘ → ΔΘ ⊢χ χ ⇒ Δᵢ → Δᵢ ok
ok-boundary ctx-ok s ch = ok-scope (ok-store ctx-ok s) ch

------------------------------------------------------------------------
-- Determinacy
------------------------------------------------------------------------

store-unique : Δ ⊢ˢ Θ ⇒ Δ₁ → Δ ⊢ˢ Θ ⇒ Δ₂ → Δ₁ ≡ Δ₂
store-unique store[] store[] = refl
store-unique (store-abst s₁) (store-abst s₂) = store-unique s₁ s₂
store-unique (store-bind wf₁ s₁) (store-bind wf₂ s₂) = store-unique s₁ s₂

change-unique : Δ ⊢δ δ ⇒ Δ₁ → Δ ⊢δ δ ⇒ Δ₂ → Δ₁ ≡ Δ₂
change-unique rev-here rev-here = refl
change-unique con-here con-here = refl
change-unique (rev-under d₁) (rev-under d₂)
  rewrite change-unique d₁ d₂ = refl
change-unique (con-under d₁) (con-under d₂)
  rewrite change-unique d₁ d₂ = refl

scope-unique : Δ ⊢χ χ ⇒ Δ₁ → Δ ⊢χ χ ⇒ Δ₂ → Δ₁ ≡ Δ₂
scope-unique scope[] scope[] = refl
scope-unique (scope∷ d₁ s₁) (scope∷ d₂ s₂)
  rewrite change-unique d₁ d₂ = scope-unique s₁ s₂

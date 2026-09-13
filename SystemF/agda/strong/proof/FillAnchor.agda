module strong.proof.FillAnchor where

-- Strong System F v7 — giving an abstract anchor its representation.
--
-- `⊢Λ` types its body under `name zero ∷ abst ∷ Δ`: the `∀`'s anchor is
-- ABSTRACT.  `TyBeta` mints a boundary whose interior is
-- `name zero ∷ bind ⌊A⌋Δ ∷ Δ`: the SAME anchor, now REPRESENTED.  Carrying
-- the body across is what `Fill` does.
--
-- Every judgment transports constructor-for-constructor: `abst` and
-- `bind R` occupy one anchor slot each and differ only in that `bind`
-- supplies `∋r`, which is never demanded of an abstract slot.  `SameAnchor`
-- compares anchor LEVELS, and a fill preserves `anchorCount`, so the two
-- sides of a comparison may be filled INDEPENDENTLY — which is what lets
-- `conv-cons`'s existential intermediate context be left alone (`fill-id`).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.proof.CtxProperties using (pop-wfᴿ)

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ Δ₃ Δ₃′ : Ctxᵗ
    Γ : Ctx
    A B : Ty
    R S : RepTy
    k X : ℕ
    α : Anchor
    Θ : Store
    χ : Scope
    δ : Change
    c : Conv
    h : Head
    M : Term

------------------------------------------------------------------------
-- The fill relation
------------------------------------------------------------------------

data Fill (R : RepTy) : Ctxᵗ → Ctxᵗ → Set where
  fill-id   : Fill R Δ Δ
  fill-here : Fill R (abst ∷ Δ) (bind R ∷ Δ)
  fill-abst : Fill R Δ Δ′ → Fill R (abst ∷ Δ) (abst ∷ Δ′)
  fill-bind : Fill R Δ Δ′ → Fill R (bind S ∷ Δ) (bind S ∷ Δ′)
  fill-name : Fill R Δ Δ′ → Fill R (name α ∷ Δ) (name α ∷ Δ′)

fill-Λ : Fill R Δ Δ′
  → Fill R (name zero ∷ abst ∷ Δ) (name zero ∷ abst ∷ Δ′)
fill-Λ f = fill-name (fill-abst f)

fill-count : Fill R Δ Δ′ → anchorCount Δ ≡ anchorCount Δ′
fill-count fill-id = refl
fill-count fill-here = refl
fill-count (fill-abst f) = cong suc (fill-count f)
fill-count (fill-bind f) = cong suc (fill-count f)
fill-count (fill-name f) = fill-count f

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

fill-a : Fill R Δ Δ′ → Δ ∋a α → Δ′ ∋a α
fill-a fill-id t = t
fill-a fill-here a-here-abst = a-here-bind
fill-a fill-here (a-over-abst t) = a-over-bind t
fill-a (fill-abst f) a-here-abst = a-here-abst
fill-a (fill-abst f) (a-over-abst t) = a-over-abst (fill-a f t)
fill-a (fill-bind f) a-here-bind = a-here-bind
fill-a (fill-bind f) (a-over-bind t) = a-over-bind (fill-a f t)
fill-a (fill-name f) (a-over-name t) = a-over-name (fill-a f t)

fill-tv : Fill R Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
fill-tv fill-id t = t
fill-tv fill-here (tv-over-abst t) = tv-over-bind t
fill-tv (fill-abst f) (tv-over-abst t) = tv-over-abst (fill-tv f t)
fill-tv (fill-bind f) (tv-over-bind t) = tv-over-bind (fill-tv f t)
fill-tv (fill-name f) tv-here = tv-here
fill-tv (fill-name f) (tv-over-name t) = tv-over-name (fill-tv f t)

fill-n : Fill R Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := α
fill-n fill-id t = t
fill-n fill-here (n-over-abst t) = n-over-bind t
fill-n (fill-abst f) (n-over-abst t) = n-over-abst (fill-n f t)
fill-n (fill-bind f) (n-over-bind t) = n-over-bind (fill-n f t)
fill-n (fill-name f) n-here = n-here
fill-n (fill-name f) (n-over-name t) = n-over-name (fill-n f t)

unfill-n : Fill R Δ Δ′ → Δ′ ∋n X := α → Δ ∋n X := α
unfill-n fill-id t = t
unfill-n fill-here (n-over-bind t) = n-over-abst t
unfill-n (fill-abst f) (n-over-abst t) = n-over-abst (unfill-n f t)
unfill-n (fill-bind f) (n-over-bind t) = n-over-bind (unfill-n f t)
unfill-n (fill-name f) n-here = n-here
unfill-n (fill-name f) (n-over-name t) = n-over-name (unfill-n f t)

fill-r : Fill R Δ Δ′ → Δ ∋r α := S → Δ′ ∋r α := S
fill-r fill-id t = t
fill-r fill-here (r-over-abst t) = r-over-bind t
fill-r (fill-abst f) (r-over-abst t) = r-over-abst (fill-r f t)
fill-r (fill-bind f) r-here = r-here
fill-r (fill-bind f) (r-over-bind t) = r-over-bind (fill-r f t)
fill-r (fill-name f) (r-over-name t) = r-over-name (fill-r f t)

fill-unoccupied : Fill R Δ Δ′ → Unoccupied Δ α → Unoccupied Δ′ α
fill-unoccupied f u X (β , t , eq) = u X (β , unfill-n f t , eq)

------------------------------------------------------------------------
-- Types, representations, readings, comparison
------------------------------------------------------------------------

fill-SameAnchor : ∀ {R Δ₁ Δ₁′ Δ₂ Δ₂′ α β} → Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
  → SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₁′ α Δ₂′ β
fill-SameAnchor {Δ₁ = Δ₁} {Δ₁′ = Δ₁′} {Δ₂ = Δ₂} {Δ₂′ = Δ₂′} {α = α}
  {β = β} f₁ f₂ (same-anchor a₁ a₂ eq) =
  same-anchor (fill-a f₁ a₁) (fill-a f₂ a₂) lvl
  where
  lvl : anchorLevel Δ₁′ α ≡ anchorLevel Δ₂′ β
  lvl rewrite sym (fill-count f₁) | sym (fill-count f₂) = eq

fill-SameTy : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
  → SameTy k Δ₁ A Δ₂ B → SameTy k Δ₁′ A Δ₂′ B
fill-SameTy f₁ f₂ (same-bound p) = same-bound p
fill-SameTy f₁ f₂ (same-free n₁ n₂ sa) =
  same-free (fill-n f₁ n₁) (fill-n f₂ n₂) (fill-SameAnchor f₁ f₂ sa)
fill-SameTy f₁ f₂ same-ℕ = same-ℕ
fill-SameTy f₁ f₂ same-𝔹 = same-𝔹
fill-SameTy f₁ f₂ (same-⇒ a b) =
  same-⇒ (fill-SameTy f₁ f₂ a) (fill-SameTy f₁ f₂ b)
fill-SameTy f₁ f₂ (same-∀ a) =
  same-∀ (fill-SameTy (fill-Λ f₁) (fill-Λ f₂) a)

fill-wf : Fill R Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
fill-wf f (wf-var x) = wf-var (fill-tv f x)
fill-wf f wf-ℕ = wf-ℕ
fill-wf f wf-𝔹 = wf-𝔹
fill-wf f (wf-⇒ a b) = wf-⇒ (fill-wf f a) (fill-wf f b)
fill-wf f (wf-∀ a) = wf-∀ (fill-wf (fill-Λ f) a)

fill-wfᴿ : Fill R Δ Δ′ → Δ ⊢ᴿ S → Δ′ ⊢ᴿ S
fill-wfᴿ f (wfᴿ-var a) = wfᴿ-var (fill-a f a)
fill-wfᴿ f wfᴿ-ℕ = wfᴿ-ℕ
fill-wfᴿ f wfᴿ-𝔹 = wfᴿ-𝔹
fill-wfᴿ f (wfᴿ-⇒ r s) = wfᴿ-⇒ (fill-wfᴿ f r) (fill-wfᴿ f s)
fill-wfᴿ f (wfᴿ-∀ r) = wfᴿ-∀ (fill-wfᴿ (fill-abst f) r)

fill-read : Fill R Δ Δ′ → Δ ⊢ S ⇓ A → Δ′ ⊢ S ⇓ A
fill-read f (read-var x) = read-var (fill-n f x)
fill-read f read-ℕ = read-ℕ
fill-read f read-𝔹 = read-𝔹
fill-read f (read-⇒ r s) = read-⇒ (fill-read f r) (fill-read f s)
fill-read f (read-∀ r) = read-∀ (fill-read (fill-Λ f) r)

fill-quote : Fill R Δ Δ′ → Δ ⊢⌊ A ⌋ S → Δ′ ⊢⌊ A ⌋ S
fill-quote f (quote-var x) = quote-var (fill-n f x)
fill-quote f quote-ℕ = quote-ℕ
fill-quote f quote-𝔹 = quote-𝔹
fill-quote f (quote-⇒ q r) = quote-⇒ (fill-quote f q) (fill-quote f r)
fill-quote f (quote-∀ q) = quote-∀ (fill-quote (fill-Λ f) q)

------------------------------------------------------------------------
-- Conversions
------------------------------------------------------------------------

mutual
  fill-head : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂′
  fill-head f₁ f₂ (conv-seal x r rd) =
    conv-seal (fill-n f₂ x) (fill-r f₂ r) (fill-read f₁ rd)
  fill-head f₁ f₂ (conv-unseal x r rd) =
    conv-unseal (fill-n f₁ x) (fill-r f₁ r) (fill-read f₂ rd)
  fill-head f₁ f₂ (conv-fun s t) =
    conv-fun (fill-conv f₂ f₁ s) (fill-conv f₁ f₂ t)
  fill-head f₁ f₂ (conv-all s) =
    conv-all (fill-conv (fill-Λ f₁) (fill-Λ f₂) s)

  fill-conv : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢ c ∶ A ⇝ B ⊣ Δ₂′
  fill-conv f₁ f₂ (conv-id same) = conv-id (fill-SameTy f₁ f₂ same)
  fill-conv f₁ f₃ (conv-cons hd tl) =
    conv-cons (fill-head f₁ fill-id hd) (fill-conv fill-id f₃ tl)

------------------------------------------------------------------------
-- Stores and scope changes
------------------------------------------------------------------------

fill-store : Fill R Δ Δ′ → Δ ⊢ˢ Θ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢ˢ Θ ⇒ Δ₂′) × Fill R Δ₂ Δ₂′)
fill-store f store[] = _ , store[] , f
fill-store f (store-abst s) with fill-store (fill-abst f) s
fill-store f (store-abst s) | Δ₂′ , s′ , g = Δ₂′ , store-abst s′ , g
fill-store f (store-bind wf s) with fill-store (fill-bind f) s
fill-store f (store-bind wf s) | Δ₂′ , s′ , g =
  Δ₂′ , store-bind (fill-wfᴿ f wf) s′ , g

fill-pop : Fill R Δ Δ′ → Δ ▷ α ↘ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ▷ α ↘ Δ₂′) × Fill R Δ₂ Δ₂′)
fill-pop fill-id p = _ , p , fill-id
fill-pop fill-here (pop-abst p) = _ , pop-bind p , fill-here
fill-pop (fill-abst f) (pop-abst p) with fill-pop f p
fill-pop (fill-abst f) (pop-abst p) | Δ₂′ , q , g =
  _ , pop-abst q , fill-abst g
fill-pop (fill-bind f) (pop-bind p) with fill-pop f p
fill-pop (fill-bind f) (pop-bind p) | Δ₂′ , q , g =
  _ , pop-bind q , fill-bind g
fill-pop (fill-name f) pop-here = _ , pop-here , f

fill-change : Fill R Δ Δ′ → Δ ⊢δ δ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢δ δ ⇒ Δ₂′) × Fill R Δ₂ Δ₂′)
fill-change f (step-reveal a u) =
  _ , step-reveal (fill-a f a) (fill-unoccupied f u) , fill-name f
fill-change f (step-conceal p) with fill-pop f p
fill-change f (step-conceal p) | Δ₂′ , q , g = Δ₂′ , step-conceal q , g

fill-scope : Fill R Δ Δ′ → Δ ⊢χ χ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢χ χ ⇒ Δ₂′) × Fill R Δ₂ Δ₂′)
fill-scope f scope[] = _ , scope[] , f
fill-scope f (scope∷ d s) with fill-change f d
fill-scope f (scope∷ d s) | Δ₁′ , d′ , g with fill-scope g s
fill-scope f (scope∷ d s) | Δ₁′ , d′ , g | Δ₂′ , s′ , g′ =
  Δ₂′ , scope∷ d′ s′ , g′

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

fill-⊢ : Fill R Δ Δ′ → Δ ∣ Γ ⊢ M ⦂ A → Δ′ ∣ Γ ⊢ M ⦂ A
fill-⊢ f (⊢` x) = ⊢` x
fill-⊢ f ⊢$ = ⊢$
fill-⊢ f ⊢# = ⊢#
fill-⊢ f (⊢⊕ l r) = ⊢⊕ (fill-⊢ f l) (fill-⊢ f r)
fill-⊢ f (⊢ƛ wf body) = ⊢ƛ (fill-wf f wf) (fill-⊢ f body)
fill-⊢ f (⊢· l r) = ⊢· (fill-⊢ f l) (fill-⊢ f r)
fill-⊢ f (⊢Λ body) = ⊢Λ (fill-⊢ (fill-Λ f) body)
fill-⊢ f (⊢•[] l wf) = ⊢•[] (fill-⊢ f l) (fill-wf f wf)
fill-⊢ f (⊢ν store scope nf body conv) with fill-store f store
fill-⊢ f (⊢ν store scope nf body conv) | ΔΘ′ , store′ , g
  with fill-scope g scope
fill-⊢ f (⊢ν store scope nf body conv) | ΔΘ′ , store′ , g
  | Δᵢ′ , scope′ , g′ =
  ⊢ν store′ scope′ nf (fill-⊢ g′ body) (fill-conv g′ g conv)

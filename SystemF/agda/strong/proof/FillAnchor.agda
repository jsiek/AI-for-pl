module strong.proof.FillAnchor where

-- Strong System F v7 — giving an abstract anchor its representation.
--
-- `⊢Λ` types its body under `anch revealed abstA ∷ Δ`: the `∀`'s anchor is
-- ABSTRACT.  `TyBeta` mints a boundary whose interior is
-- `anch revealed (bindA ⌊A⌋Δ) ∷ Δ`: the SAME anchor and the SAME
-- visibility, now REPRESENTED.  With merged entries the fill is a flip of
-- the BINDING field alone, leaving the name where it is — so every
-- judgment transports constructor-for-constructor and `SameAnchor`, which
-- is index equality, is untouched.

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

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ Δ₃ Δ₃′ : Ctxᵗ
    Γ : Ctx
    A B : Ty
    R S : RepTy
    k X : ℕ
    α : Anchor
    v : Vis
    b : AnchorBinding
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
  fill-id    : Fill R Δ Δ
  fill-here  : Fill R (anch v abstA ∷ Δ) (anch v (bindA R) ∷ Δ)
  fill-under : Fill R Δ Δ′ → Fill R (anch v b ∷ Δ) (anch v b ∷ Δ′)

fill-Λ : Fill R Δ Δ′
  → Fill R (anch revealed abstA ∷ Δ) (anch revealed abstA ∷ Δ′)
fill-Λ = fill-under

fill-count : Fill R Δ Δ′ → anchorCount Δ ≡ anchorCount Δ′
fill-count fill-id = refl
fill-count fill-here = refl
fill-count (fill-under f) = cong suc (fill-count f)

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

fill-a : Fill R Δ Δ′ → Δ ∋a α → Δ′ ∋a α
fill-a fill-id t = t
fill-a fill-here a-here = a-here
fill-a fill-here (a-there t) = a-there t
fill-a (fill-under f) a-here = a-here
fill-a (fill-under f) (a-there t) = a-there (fill-a f t)

fill-tv : Fill R Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
fill-tv fill-id t = t
fill-tv fill-here tv-here = tv-here
fill-tv fill-here (tv-revealed t) = tv-revealed t
fill-tv fill-here (tv-concealed t) = tv-concealed t
fill-tv (fill-under f) tv-here = tv-here
fill-tv (fill-under f) (tv-revealed t) = tv-revealed (fill-tv f t)
fill-tv (fill-under f) (tv-concealed t) = tv-concealed (fill-tv f t)

fill-n : Fill R Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := α
fill-n fill-id t = t
fill-n fill-here n-here = n-here
fill-n fill-here (n-revealed t) = n-revealed t
fill-n fill-here (n-concealed t) = n-concealed t
fill-n (fill-under f) n-here = n-here
fill-n (fill-under f) (n-revealed t) = n-revealed (fill-n f t)
fill-n (fill-under f) (n-concealed t) = n-concealed (fill-n f t)

unfill-n : Fill R Δ Δ′ → Δ′ ∋n X := α → Δ ∋n X := α
unfill-n fill-id t = t
unfill-n fill-here n-here = n-here
unfill-n fill-here (n-revealed t) = n-revealed t
unfill-n fill-here (n-concealed t) = n-concealed t
unfill-n (fill-under f) n-here = n-here
unfill-n (fill-under f) (n-revealed t) = n-revealed (unfill-n f t)
unfill-n (fill-under f) (n-concealed t) = n-concealed (unfill-n f t)

-- A fill only ADDS `∋r` facts: an abstract slot is never asked for one.
fill-r : Fill R Δ Δ′ → Δ ∋r α := S → Δ′ ∋r α := S
fill-r fill-id t = t
fill-r fill-here (r-there t) = r-there t
fill-r (fill-under f) r-here = r-here
fill-r (fill-under f) (r-there t) = r-there (fill-r f t)

------------------------------------------------------------------------
-- Types, representations, readings, comparison
------------------------------------------------------------------------

fill-SameAnchor : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
  → ∀ {β} → SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₁′ α Δ₂′ β
fill-SameAnchor f₁ f₂ (same-anchor a₁ a₂ eq) =
  same-anchor (fill-a f₁ a₁) (fill-a f₂ a₂) eq

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
fill-wfᴿ f (wfᴿ-∀ r) = wfᴿ-∀ (fill-wfᴿ (fill-under f) r)

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

fill-cnt : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
  → anchorCount Δ₁ ≡ anchorCount Δ₂ → anchorCount Δ₁′ ≡ anchorCount Δ₂′
fill-cnt f₁ f₂ eq = trans (sym (fill-count f₁)) (trans eq (fill-count f₂))

mutual
  fill-head : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂′
  fill-head f₁ f₂ (conv-seal x r rd cnt) =
    conv-seal (fill-n f₂ x) (fill-r f₂ r) (fill-read f₁ rd)
      (fill-cnt f₁ f₂ cnt)
  fill-head f₁ f₂ (conv-unseal x r rd cnt) =
    conv-unseal (fill-n f₁ x) (fill-r f₁ r) (fill-read f₂ rd)
      (fill-cnt f₁ f₂ cnt)
  fill-head f₁ f₂ (conv-fun s t) =
    conv-fun (fill-conv f₂ f₁ s) (fill-conv f₁ f₂ t)
  fill-head f₁ f₂ (conv-all s) =
    conv-all (fill-conv (fill-Λ f₁) (fill-Λ f₂) s)

  -- The two sides may be filled INDEPENDENTLY, so `conv-cons`'s
  -- existential seam is simply left alone.
  fill-conv : Fill R Δ₁ Δ₁′ → Fill R Δ₂ Δ₂′
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢ c ∶ A ⇝ B ⊣ Δ₂′
  fill-conv f₁ f₂ (conv-id same cnt) =
    conv-id (fill-SameTy f₁ f₂ same) (fill-cnt f₁ f₂ cnt)
  fill-conv f₁ f₃ (conv-cons hd tl) =
    conv-cons (fill-head f₁ fill-id hd) (fill-conv fill-id f₃ tl)

------------------------------------------------------------------------
-- Stores and scope changes
------------------------------------------------------------------------

fill-store : Fill R Δ Δ′ → Δ ⊢ˢ Θ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢ˢ Θ ⇒ Δ₂′) × Fill R Δ₂ Δ₂′)
fill-store f store[] = _ , store[] , f
fill-store f (store-abst s) with fill-store (fill-under f) s
fill-store f (store-abst s) | Δ₂′ , s′ , g = Δ₂′ , store-abst s′ , g
fill-store f (store-bind wf s) with fill-store (fill-under f) s
fill-store f (store-bind wf s) | Δ₂′ , s′ , g =
  Δ₂′ , store-bind (fill-wfᴿ f wf) s′ , g

fill-change : Fill R Δ Δ′ → Δ ⊢δ δ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢δ δ ⇒ Δ₂′) × Fill R Δ₂ Δ₂′)
fill-change fill-id d = _ , d , fill-id
fill-change fill-here rev-here = _ , rev-here , fill-here
fill-change fill-here con-here = _ , con-here , fill-here
fill-change fill-here (rev-under d) = _ , rev-under d , fill-here
fill-change fill-here (con-under d) = _ , con-under d , fill-here
fill-change (fill-under f) rev-here = _ , rev-here , fill-under f
fill-change (fill-under f) con-here = _ , con-here , fill-under f
fill-change (fill-under f) (rev-under d) with fill-change f d
fill-change (fill-under f) (rev-under d) | Δ₂′ , d′ , g =
  _ , rev-under d′ , fill-under g
fill-change (fill-under f) (con-under d) with fill-change f d
fill-change (fill-under f) (con-under d) | Δ₂′ , d′ , g =
  _ , con-under d′ , fill-under g

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

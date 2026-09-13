module strong.proof.FillAnchor where

-- Strong System F v7 — giving an abstract anchor its representation.
--
-- `⊢Λ` types its body under `anch revealed abstA ∷ Δ`; `TyBeta` mints a
-- boundary whose interior is `anch revealed (bindA ⌊A⌋Δ) ∷ Δ`: the same
-- entry with its BINDING filled in.  `Fill R n` is that flip, at spine
-- position n — positional, so that it is DETERMINISTIC (`fill-unique`)
-- and so that two contexts related by the conversion rules' spine
-- discipline can be filled in lockstep: `sb-fill` derives the fill of a
-- `SameBindings`-related context, and `fill-flip` shows a `FlipAt` — a
-- seal or unseal head's one-bit crossing — survives filling both sides.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.proof.ConversionProperties using (head-sb)

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ Δ₃ Δoff Δoff′ Δon Δon′ : Ctxᵗ
    Γ : Ctx
    A B : Ty
    R S : RepTy
    k n X : ℕ
    α : Anchor
    v : Vis
    b : AnchorBinding
    e : Ent
    Θ : Store
    χ : Scope
    δ : Change
    c : Conv
    h : Head
    M : Term

------------------------------------------------------------------------
-- The fill relation
------------------------------------------------------------------------

data Fill (R : RepTy) : ℕ → Ctxᵗ → Ctxᵗ → Set where
  fill-here  : Fill R zero (anch v abstA ∷ Δ) (anch v (bindA R) ∷ Δ)
  fill-there : Fill R n Δ Δ′ → Fill R (suc n) (e ∷ Δ) (e ∷ Δ′)

fill-Λ : Fill R n Δ Δ′
  → Fill R (suc n) (anch revealed abstA ∷ Δ) (anch revealed abstA ∷ Δ′)
fill-Λ = fill-there

fill-unique : Fill R n Δ Δ₁ → Fill R n Δ Δ₂ → Δ₁ ≡ Δ₂
fill-unique fill-here fill-here = refl
fill-unique (fill-there f) (fill-there g)
  rewrite fill-unique f g = refl

------------------------------------------------------------------------
-- Lockstep filling along the spine discipline
------------------------------------------------------------------------

sb-fill : SameBindings Δ₁ Δ₂ → Fill R n Δ₁ Δ₁′
  → Σ[ Δ₂′ ∈ Ctxᵗ ] (Fill R n Δ₂ Δ₂′ × SameBindings Δ₁′ Δ₂′)
sb-fill (sb-∷ s) fill-here = _ , fill-here , sb-∷ s
sb-fill (sb-∷ s) (fill-there f) with sb-fill s f
sb-fill (sb-∷ s) (fill-there f) | Δ₂′ , g , s′ =
  _ , fill-there g , sb-∷ s′

fill-sb : Fill R n Δ₁ Δ₁′ → Fill R n Δ₂ Δ₂′
  → SameBindings Δ₁ Δ₂ → SameBindings Δ₁′ Δ₂′
fill-sb fill-here fill-here (sb-∷ s) = sb-∷ s
fill-sb (fill-there f) (fill-there g) (sb-∷ s) = sb-∷ (fill-sb f g s)

fill-flip : ∀ {α} → Fill R n Δoff Δoff′ → Fill R n Δon Δon′
  → FlipAt α Δoff Δon → FlipAt α Δoff′ Δon′
fill-flip fill-here fill-here flip-here = flip-here
fill-flip fill-here fill-here (flip-there fl) = flip-there fl
fill-flip (fill-there f) (fill-there g) flip-here
  rewrite fill-unique f g = flip-here
fill-flip (fill-there f) (fill-there g) (flip-there fl) =
  flip-there (fill-flip f g fl)

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

fill-a : Fill R n Δ Δ′ → Δ ∋a α → Δ′ ∋a α
fill-a fill-here a-here = a-here
fill-a fill-here (a-there t) = a-there t
fill-a (fill-there f) a-here = a-here
fill-a (fill-there f) (a-there t) = a-there (fill-a f t)

fill-tv : Fill R n Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
fill-tv fill-here tv-here = tv-here
fill-tv fill-here (tv-revealed t) = tv-revealed t
fill-tv fill-here (tv-concealed t) = tv-concealed t
fill-tv (fill-there {e = anch revealed b} f) tv-here = tv-here
fill-tv (fill-there {e = anch revealed b} f) (tv-revealed t) =
  tv-revealed (fill-tv f t)
fill-tv (fill-there {e = anch concealed b} f) (tv-concealed t) =
  tv-concealed (fill-tv f t)

fill-n : Fill R n Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := α
fill-n fill-here n-here = n-here
fill-n fill-here (n-revealed t) = n-revealed t
fill-n fill-here (n-concealed t) = n-concealed t
fill-n (fill-there {e = anch revealed b} f) n-here = n-here
fill-n (fill-there {e = anch revealed b} f) (n-revealed t) =
  n-revealed (fill-n f t)
fill-n (fill-there {e = anch concealed b} f) (n-concealed t) =
  n-concealed (fill-n f t)

unfill-n : Fill R n Δ Δ′ → Δ′ ∋n X := α → Δ ∋n X := α
unfill-n fill-here n-here = n-here
unfill-n fill-here (n-revealed t) = n-revealed t
unfill-n fill-here (n-concealed t) = n-concealed t
unfill-n (fill-there {e = anch revealed b} f) n-here = n-here
unfill-n (fill-there {e = anch revealed b} f) (n-revealed t) =
  n-revealed (unfill-n f t)
unfill-n (fill-there {e = anch concealed b} f) (n-concealed t) =
  n-concealed (unfill-n f t)

-- A fill only ADDS `∋r` facts: an abstract slot is never asked for one.
fill-r : Fill R n Δ Δ′ → Δ ∋r α := S → Δ′ ∋r α := S
fill-r fill-here (r-there t) = r-there t
fill-r (fill-there {e = anch v (bindA _)} f) r-here = r-here
fill-r (fill-there f) (r-there t) = r-there (fill-r f t)

------------------------------------------------------------------------
-- Types, representations, readings, comparison
------------------------------------------------------------------------

fill-SameAnchor : ∀ {β} → Fill R n Δ₁ Δ₁′ → Fill R n Δ₂ Δ₂′
  → SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₁′ α Δ₂′ β
fill-SameAnchor f₁ f₂ (same-anchor a₁ a₂ eq) =
  same-anchor (fill-a f₁ a₁) (fill-a f₂ a₂) eq

fill-SameTy : Fill R n Δ₁ Δ₁′ → Fill R n Δ₂ Δ₂′
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

fill-wf : Fill R n Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
fill-wf f (wf-var x) = wf-var (fill-tv f x)
fill-wf f wf-ℕ = wf-ℕ
fill-wf f wf-𝔹 = wf-𝔹
fill-wf f (wf-⇒ a b) = wf-⇒ (fill-wf f a) (fill-wf f b)
fill-wf f (wf-∀ a) = wf-∀ (fill-wf (fill-Λ f) a)

fill-wfᴿ : Fill R n Δ Δ′ → Δ ⊢ᴿ S → Δ′ ⊢ᴿ S
fill-wfᴿ f (wfᴿ-var a) = wfᴿ-var (fill-a f a)
fill-wfᴿ f wfᴿ-ℕ = wfᴿ-ℕ
fill-wfᴿ f wfᴿ-𝔹 = wfᴿ-𝔹
fill-wfᴿ f (wfᴿ-⇒ r s) = wfᴿ-⇒ (fill-wfᴿ f r) (fill-wfᴿ f s)
fill-wfᴿ f (wfᴿ-∀ r) = wfᴿ-∀ (fill-wfᴿ (fill-there f) r)

fill-read : Fill R n Δ Δ′ → Δ ⊢ S ⇓ A → Δ′ ⊢ S ⇓ A
fill-read f (read-var x) = read-var (fill-n f x)
fill-read f read-ℕ = read-ℕ
fill-read f read-𝔹 = read-𝔹
fill-read f (read-⇒ r s) = read-⇒ (fill-read f r) (fill-read f s)
fill-read f (read-∀ r) = read-∀ (fill-read (fill-Λ f) r)

fill-quote : Fill R n Δ Δ′ → Δ ⊢⌊ A ⌋ S → Δ′ ⊢⌊ A ⌋ S
fill-quote f (quote-var x) = quote-var (fill-n f x)
fill-quote f quote-ℕ = quote-ℕ
fill-quote f quote-𝔹 = quote-𝔹
fill-quote f (quote-⇒ q r) = quote-⇒ (fill-quote f q) (fill-quote f r)
fill-quote f (quote-∀ q) = quote-∀ (fill-quote (fill-Λ f) q)

------------------------------------------------------------------------
-- Conversions
------------------------------------------------------------------------
--
-- The two endpoint fills are given; each seam's fill is DERIVED through
-- the head's spine (`head-sb` + `sb-fill`), so every context along the
-- chain is filled at the same position with the same representation.

mutual
  fill-head : Fill R n Δ₁ Δ₁′ → Fill R n Δ₂ Δ₂′
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂′
  fill-head f₁ f₂ (conv-seal x r rd flip) =
    conv-seal (fill-n f₂ x) (fill-r f₂ r) (fill-read f₁ rd)
      (fill-flip f₁ f₂ flip)
  fill-head f₁ f₂ (conv-unseal x r rd flip) =
    conv-unseal (fill-n f₁ x) (fill-r f₁ r) (fill-read f₂ rd)
      (fill-flip f₂ f₁ flip)
  fill-head f₁ f₂ (conv-fun s t) =
    conv-fun (fill-conv f₂ f₁ s) (fill-conv f₁ f₂ t)
  fill-head f₁ f₂ (conv-all s) =
    conv-all (fill-conv (fill-Λ f₁) (fill-Λ f₂) s)

  fill-conv : Fill R n Δ₁ Δ₁′ → Fill R n Δ₂ Δ₂′
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢ c ∶ A ⇝ B ⊣ Δ₂′
  fill-conv f₁ f₂ (conv-id same sb) =
    conv-id (fill-SameTy f₁ f₂ same) (fill-sb f₁ f₂ sb)
  fill-conv f₁ f₃ (conv-cons hd tl) with fill-tail f₃ tl
  fill-conv f₁ f₃ (conv-cons hd tl) | Δ₂′ , g , tl′ =
    conv-cons (fill-head f₁ g hd) tl′

  -- A TAIL is filled from its EXTERIOR inward: `tail-id` ties its two
  -- contexts together, and each head's entry fill is derived through the
  -- head's own spine.
  fill-tail : ∀ {Δ₁ Δ₂ Δ₂′ c A B} → Fill R n Δ₂ Δ₂′
    → Δ₁ ⊩ c ∶ A ⇝ B ⊣ Δ₂
    → Σ[ Δ₁′ ∈ Ctxᵗ ] (Fill R n Δ₁ Δ₁′ × (Δ₁′ ⊩ c ∶ A ⇝ B ⊣ Δ₂′))
  fill-tail f (tail-id wf) = _ , f , tail-id (fill-wf f wf)
  fill-tail f (tail-cons hd tl) with fill-tail f tl
  fill-tail f (tail-cons hd tl) | Δᵐ′ , g , tl′
    with sb-fill (sb-sym (head-sb hd)) g
  fill-tail f (tail-cons hd tl) | Δᵐ′ , g , tl′ | Δ₁′ , f₁ , _ =
    _ , f₁ , tail-cons (fill-head f₁ g hd) tl′

------------------------------------------------------------------------
-- Stores and scope changes
------------------------------------------------------------------------

fill-store : Fill R n Δ Δ′ → Δ ⊢ˢ Θ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢ˢ Θ ⇒ Δ₂′) × Fill R (length Θ + n) Δ₂ Δ₂′)
fill-store f store[] = _ , store[] , f
fill-store {R = R} {n = n} {Δ₂ = Δ₂} f (store-abst {Θ = Θ} s)
  with fill-store (fill-there f) s
fill-store {R = R} {n = n} {Δ₂ = Δ₂} f (store-abst {Θ = Θ} s)
  | Δ₂′ , s′ , g =
  Δ₂′ , store-abst s′ ,
  subst (λ m → Fill R m Δ₂ Δ₂′) (+-suc (length Θ) n) g
fill-store {R = R} {n = n} {Δ₂ = Δ₂} f (store-bind {Θ = Θ} wf s)
  with fill-store (fill-there f) s
fill-store {R = R} {n = n} {Δ₂ = Δ₂} f (store-bind {Θ = Θ} wf s)
  | Δ₂′ , s′ , g =
  Δ₂′ , store-bind (fill-wfᴿ f wf) s′ ,
  subst (λ m → Fill R m Δ₂ Δ₂′) (+-suc (length Θ) n) g

fill-change : Fill R n Δ Δ′ → Δ ⊢δ δ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢δ δ ⇒ Δ₂′) × Fill R n Δ₂ Δ₂′)
fill-change fill-here rev-here = _ , rev-here , fill-here
fill-change fill-here con-here = _ , con-here , fill-here
fill-change fill-here (rev-under d) = _ , rev-under d , fill-here
fill-change fill-here (con-under d) = _ , con-under d , fill-here
fill-change (fill-there f) rev-here = _ , rev-here , fill-there f
fill-change (fill-there f) con-here = _ , con-here , fill-there f
fill-change (fill-there f) (rev-under d) with fill-change f d
fill-change (fill-there f) (rev-under d) | Δ₂′ , d′ , g =
  _ , rev-under d′ , fill-there g
fill-change (fill-there f) (con-under d) with fill-change f d
fill-change (fill-there f) (con-under d) | Δ₂′ , d′ , g =
  _ , con-under d′ , fill-there g

fill-scope : Fill R n Δ Δ′ → Δ ⊢χ χ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢χ χ ⇒ Δ₂′) × Fill R n Δ₂ Δ₂′)
fill-scope f scope[] = _ , scope[] , f
fill-scope f (scope∷ d s) with fill-change f d
fill-scope f (scope∷ d s) | Δ₁′ , d′ , g with fill-scope g s
fill-scope f (scope∷ d s) | Δ₁′ , d′ , g | Δ₂′ , s′ , g′ =
  Δ₂′ , scope∷ d′ s′ , g′

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

fill-⊢ : Fill R n Δ Δ′ → Δ ∣ Γ ⊢ M ⦂ A → Δ′ ∣ Γ ⊢ M ⦂ A
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

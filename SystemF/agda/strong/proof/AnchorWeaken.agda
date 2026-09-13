module strong.proof.AnchorWeaken where

-- Strong System F v7 — carrying a derivation under NEW ANCHORS.
--
-- `Beta`'s crossΛ sends a value across a `Λ`, `Wrap` sends the argument
-- inside the boundary's store, `TyWrap` and `Merge` re-read a conversion
-- under an extended store.  Each renames the anchor coordinate, and
-- preservation has to show the renamed derivation still types.
--
-- `Wk k p ρ Δ Δ′` says Δ′ is Δ with a BLOCK of k anchor entries inserted at
-- the base — the base being the context of anchor count p — and ρ the
-- induced renaming.  Descending under a binder lifts ρ with `extᴿ` and
-- leaves k and p alone, so one (k, p, ρ) serves a whole conversion, which
-- is what the syntax demands: `renConv` applies ONE renaming throughout.
--
-- The delicate part is `SameAnchor`, which compares de Bruijn LEVELS.  A
-- top insertion leaves every ORIGINAL anchor's level alone and shifts each
-- level introduced by a descent by +k; the split is at p.  Two contexts
-- weakened with the same (k, p) therefore map levels the same way, and the
-- conversion seam condition (`anchorCount Δ₁ ≡ anchorCount Δ₂`) is what
-- makes their p's agree.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using
  (_<?_; +-suc; ≤-refl; ≤-trans; n≤1+n; <-irrefl; ≤∧≢⇒<; <⇒≱; +-cancelˡ-≡)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.proof.RenameAlgebra

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ : Ctxᵗ
    A B : Ty
    R S : RepTy
    k p d X : ℕ
    α β : Anchor
    ρ : Renameᴿ

------------------------------------------------------------------------
-- The inserted block
------------------------------------------------------------------------

data Block : ℕ → Ctxᵗ → Ctxᵗ → Set where
  blk[]    : Block zero Δ Δ
  blk-abst : Block k Δ Δ′ → Block (suc k) Δ (abst ∷ Δ′)
  blk-bind : Block k Δ Δ′ → Block (suc k) Δ (bind S ∷ Δ′)

blk-count : Block k Δ Δ′ → anchorCount Δ′ ≡ k + anchorCount Δ
blk-count blk[] = refl
blk-count (blk-abst b) = cong suc (blk-count b)
blk-count (blk-bind b) = cong suc (blk-count b)

blk-a : Block k Δ Δ′ → Δ ∋a α → Δ′ ∋a (k + α)
blk-a blk[] t = t
blk-a (blk-abst b) t = a-over-abst (blk-a b t)
blk-a (blk-bind b) t = a-over-bind (blk-a b t)

blk-tv : Block k Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
blk-tv blk[] t = t
blk-tv (blk-abst b) t = tv-over-abst (blk-tv b t)
blk-tv (blk-bind b) t = tv-over-bind (blk-tv b t)

blk-n : Block k Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := (k + α)
blk-n blk[] t = t
blk-n (blk-abst b) t = n-over-abst (blk-n b t)
blk-n (blk-bind b) t = n-over-bind (blk-n b t)

blk-unn : Block k Δ Δ′ → Δ′ ∋n X := β
  → Σ[ α ∈ Anchor ] ((Δ ∋n X := α) × (β ≡ k + α))
blk-unn blk[] t = _ , t , refl
blk-unn (blk-abst b) (n-over-abst t) with blk-unn b t
blk-unn (blk-abst b) (n-over-abst t) | α , u , refl = α , u , refl
blk-unn (blk-bind b) (n-over-bind t) with blk-unn b t
blk-unn (blk-bind b) (n-over-bind t) | α , u , refl = α , u , refl

-- Recasting the representation a lookup hands back, without the
-- higher-order unification an inline `subst` motive would need.
r-cast : ∀ {Δ α S T} → S ≡ T → Δ ∋r α := S → Δ ∋r α := T
r-cast refl t = t

blk-r : Block k Δ Δ′ → Δ ∋r α := S
  → Δ′ ∋r (k + α) := renameᴿ (shiftAnchor k) S
blk-r {S = S} blk[] t = r-cast (sym (renameᴿ-id (λ α → refl) S)) t
blk-r {S = S} (blk-abst {k = k} b) t =
  r-cast (renameᴿ-fuse suc (shiftAnchor k) S) (r-over-abst (blk-r b t))
blk-r {S = S} (blk-bind {k = k} b) t =
  r-cast (renameᴿ-fuse suc (shiftAnchor k) S) (r-over-bind (blk-r b t))

------------------------------------------------------------------------
-- The weakening
------------------------------------------------------------------------

data Wk : ℕ → ℕ → Renameᴿ → Ctxᵗ → Ctxᵗ → Set where
  wk-base : Block k Δ Δ′ → Wk k (anchorCount Δ) (shiftAnchor k) Δ Δ′
  wk-abst : Wk k p ρ Δ Δ′ → Wk k p (extᴿ ρ) (abst ∷ Δ) (abst ∷ Δ′)
  wk-bind : Wk k p ρ Δ Δ′
          → Wk k p (extᴿ ρ) (bind S ∷ Δ) (bind (renameᴿ ρ S) ∷ Δ′)
  wk-name : Wk k p ρ Δ Δ′ → Wk k p ρ (name α ∷ Δ) (name (ρ α) ∷ Δ′)

wk-Λ : Wk k p ρ Δ Δ′
  → Wk k p (extᴿ ρ) (name zero ∷ abst ∷ Δ) (name zero ∷ abst ∷ Δ′)
wk-Λ f = wk-name (wk-abst f)

wk-count : Wk k p ρ Δ Δ′ → anchorCount Δ′ ≡ k + anchorCount Δ
wk-count (wk-base b) = blk-count b
wk-count {k = k} (wk-abst f) =
  trans (cong suc (wk-count f)) (sym (+-suc k _))
wk-count {k = k} (wk-bind f) =
  trans (cong suc (wk-count f)) (sym (+-suc k _))
wk-count (wk-name f) = wk-count f

wk-p≤ : Wk k p ρ Δ Δ′ → p ≤ anchorCount Δ
wk-p≤ (wk-base b) = ≤-refl
wk-p≤ (wk-abst f) = ≤-trans (wk-p≤ f) (n≤1+n _)
wk-p≤ (wk-bind f) = ≤-trans (wk-p≤ f) (n≤1+n _)
wk-p≤ (wk-name f) = wk-p≤ f

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

wk-a : Wk k p ρ Δ Δ′ → Δ ∋a α → Δ′ ∋a ρ α
wk-a (wk-base b) t = blk-a b t
wk-a (wk-abst f) a-here-abst = a-here-abst
wk-a (wk-abst f) (a-over-abst t) = a-over-abst (wk-a f t)
wk-a (wk-bind f) a-here-bind = a-here-bind
wk-a (wk-bind f) (a-over-bind t) = a-over-bind (wk-a f t)
wk-a (wk-name f) (a-over-name t) = a-over-name (wk-a f t)

wk-tv : Wk k p ρ Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
wk-tv (wk-base b) t = blk-tv b t
wk-tv (wk-abst f) (tv-over-abst t) = tv-over-abst (wk-tv f t)
wk-tv (wk-bind f) (tv-over-bind t) = tv-over-bind (wk-tv f t)
wk-tv (wk-name f) tv-here = tv-here
wk-tv (wk-name f) (tv-over-name t) = tv-over-name (wk-tv f t)

wk-n : Wk k p ρ Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := ρ α
wk-n (wk-base b) t = blk-n b t
wk-n (wk-abst f) (n-over-abst t) = n-over-abst (wk-n f t)
wk-n (wk-bind f) (n-over-bind t) = n-over-bind (wk-n f t)
wk-n (wk-name f) n-here = n-here
wk-n (wk-name f) (n-over-name t) = n-over-name (wk-n f t)

wk-unn : Wk k p ρ Δ Δ′ → Δ′ ∋n X := β
  → Σ[ α ∈ Anchor ] ((Δ ∋n X := α) × (β ≡ ρ α))
wk-unn (wk-base b) t = blk-unn b t
wk-unn (wk-abst f) (n-over-abst t) with wk-unn f t
wk-unn (wk-abst f) (n-over-abst t) | α , u , refl = _ , n-over-abst u , refl
wk-unn (wk-bind f) (n-over-bind t) with wk-unn f t
wk-unn (wk-bind f) (n-over-bind t) | α , u , refl = _ , n-over-bind u , refl
wk-unn (wk-name f) n-here = _ , n-here , refl
wk-unn (wk-name f) (n-over-name t) with wk-unn f t
wk-unn (wk-name f) (n-over-name t) | α , u , refl = _ , n-over-name u , refl

wk-r : Wk k p ρ Δ Δ′ → Δ ∋r α := S → Δ′ ∋r ρ α := renameᴿ ρ S
wk-r (wk-base b) t = blk-r b t
wk-r (wk-abst {ρ = ρ₀} f) (r-over-abst {R = S₀} t) =
  r-cast (sym (⇑ᴿ-comm ρ₀ S₀)) (r-over-abst (wk-r f t))
wk-r (wk-bind {ρ = ρ₀} f) (r-here {R = S₀}) =
  r-cast (sym (⇑ᴿ-comm ρ₀ S₀)) r-here
wk-r (wk-bind {ρ = ρ₀} f) (r-over-bind {R = S₀} t) =
  r-cast (sym (⇑ᴿ-comm ρ₀ S₀)) (r-over-bind (wk-r f t))
wk-r (wk-name f) (r-over-name t) = r-over-name (wk-r f t)

wk-inj : Wk k p ρ Δ Δ′ → ∀ α β → ρ α ≡ ρ β → α ≡ β
wk-inj {k = k} (wk-base b) α β eq = +-cancelˡ-≡ k α β eq
wk-inj (wk-abst f) zero zero eq = refl
wk-inj (wk-abst f) (suc α) (suc β) eq =
  cong suc (wk-inj f α β (suc-inj eq))
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
wk-inj (wk-bind f) zero zero eq = refl
wk-inj (wk-bind f) (suc α) (suc β) eq =
  cong suc (wk-inj f α β (suc-inj eq))
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
wk-inj (wk-name f) α β eq = wk-inj f α β eq

wk-unoccupied : Wk k p ρ Δ Δ′ → Unoccupied Δ α → Unoccupied Δ′ (ρ α)
wk-unoccupied {α = α} f u X (β , t , eq) with wk-unn f t
wk-unoccupied {α = α} f u X (β , t , eq) | γ , v , refl =
  u X (γ , v , wk-inj f γ α eq)

------------------------------------------------------------------------
-- Levels
------------------------------------------------------------------------
--
-- A top insertion leaves an ORIGINAL anchor's level alone and shifts a
-- level introduced by a descent by +k.  The split is at p.

a-bound : Δ ∋a α → α < anchorCount Δ
a-bound a-here-abst = s≤s z≤n
a-bound a-here-bind = s≤s z≤n
a-bound (a-over-abst t) = s≤s (a-bound t)
a-bound (a-over-bind t) = s≤s (a-bound t)
a-bound (a-over-name t) = a-bound t

∸-drops : ∀ c a → a < c → c ∸ suc a < c
∸-drops (suc c) zero lt = s≤s ≤-refl
∸-drops (suc c) (suc a) (s≤s lt) = ≤-trans (∸-drops c a lt) (n≤1+n c)

+∸+ : ∀ k m n → (k + m) ∸ (k + n) ≡ m ∸ n
+∸+ zero m n = refl
+∸+ (suc k) m n = +∸+ k m n

wk-level-lt : (f : Wk k p ρ Δ Δ′) → Δ ∋a α
  → anchorLevel Δ α < p → anchorLevel Δ′ (ρ α) ≡ anchorLevel Δ α
wk-level-lt {k = k} {ρ = ρ} {Δ = Δ} {α = α} (wk-base b) t lt
  rewrite blk-count b =
  trans (cong (λ m → (k + anchorCount Δ) ∸ m) (sym (+-suc k α)))
        (+∸+ k (anchorCount Δ) (suc α))
wk-level-lt (wk-abst f) a-here-abst lt =
  ⊥-elim (<⇒≱ lt (wk-p≤ f))
wk-level-lt (wk-abst f) (a-over-abst t) lt = wk-level-lt f t lt
wk-level-lt (wk-bind f) a-here-bind lt =
  ⊥-elim (<⇒≱ lt (wk-p≤ f))
wk-level-lt (wk-bind f) (a-over-bind t) lt = wk-level-lt f t lt
wk-level-lt (wk-name f) (a-over-name t) lt = wk-level-lt f t lt

wk-level-ge : (f : Wk k p ρ Δ Δ′) → Δ ∋a α
  → ¬ (anchorLevel Δ α < p) → anchorLevel Δ′ (ρ α) ≡ k + anchorLevel Δ α
wk-level-ge {Δ = Δ} (wk-base b) t ge =
  ⊥-elim (ge (∸-drops (anchorCount Δ) _ (a-bound t)))
wk-level-ge (wk-abst f) a-here-abst ge = wk-count f
wk-level-ge (wk-abst f) (a-over-abst t) ge = wk-level-ge f t ge
wk-level-ge (wk-bind f) a-here-bind ge = wk-count f
wk-level-ge (wk-bind f) (a-over-bind t) ge = wk-level-ge f t ge
wk-level-ge (wk-name f) (a-over-name t) ge = wk-level-ge f t ge

-- Two contexts weakened with the same (k, p) map levels the same way, so
-- an anchor match survives.  Their p's agree because the conversion seam
-- condition makes their anchor counts agree.
wk-level-eq : ∀ {k p ρ Δ₁ Δ₁′ Δ₂ Δ₂′ α β}
  → (f₁ : Wk k p ρ Δ₁ Δ₁′) (f₂ : Wk k p ρ Δ₂ Δ₂′)
  → Δ₁ ∋a α → Δ₂ ∋a β
  → anchorLevel Δ₁ α ≡ anchorLevel Δ₂ β
  → anchorLevel Δ₁′ (ρ α) ≡ anchorLevel Δ₂′ (ρ β)
wk-level-eq {k = k} {p = p} {ρ = ρ} {Δ₁ = Δ₁} {Δ₁′ = Δ₁′} {Δ₂ = Δ₂}
  {Δ₂′ = Δ₂′} {α = α} {β = β} f₁ f₂ a₁ a₂ eq =
  go (anchorLevel Δ₁ α <? p)
  where
  go : Dec (anchorLevel Δ₁ α < p)
     → anchorLevel Δ₁′ (ρ α) ≡ anchorLevel Δ₂′ (ρ β)
  go (yes lt) =
    trans (wk-level-lt f₁ a₁ lt)
      (trans eq (sym (wk-level-lt f₂ a₂ (subst (_< p) eq lt))))
  go (no ge) =
    trans (wk-level-ge f₁ a₁ ge)
      (trans (cong (k +_) eq)
        (sym (wk-level-ge f₂ a₂ (λ l → ge (subst (_< p) (sym eq) l)))))

wk-SameAnchor : ∀ {k p ρ Δ₁ Δ₁′ Δ₂ Δ₂′ α β}
  → Wk k p ρ Δ₁ Δ₁′ → Wk k p ρ Δ₂ Δ₂′
  → SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₁′ (ρ α) Δ₂′ (ρ β)
wk-SameAnchor f₁ f₂ (same-anchor a₁ a₂ eq) =
  same-anchor (wk-a f₁ a₁) (wk-a f₂ a₂) (wk-level-eq f₁ f₂ a₁ a₂ eq)

wk-SameTy : ∀ {j} → Wk k p ρ Δ₁ Δ₁′ → Wk k p ρ Δ₂ Δ₂′
  → SameTy j Δ₁ A Δ₂ B → SameTy j Δ₁′ A Δ₂′ B
wk-SameTy f₁ f₂ (same-bound q) = same-bound q
wk-SameTy f₁ f₂ (same-free n₁ n₂ sa) =
  same-free (wk-n f₁ n₁) (wk-n f₂ n₂) (wk-SameAnchor f₁ f₂ sa)
wk-SameTy f₁ f₂ same-ℕ = same-ℕ
wk-SameTy f₁ f₂ same-𝔹 = same-𝔹
wk-SameTy f₁ f₂ (same-⇒ a b) =
  same-⇒ (wk-SameTy f₁ f₂ a) (wk-SameTy f₁ f₂ b)
wk-SameTy f₁ f₂ (same-∀ a) =
  same-∀ (wk-SameTy (wk-Λ f₁) (wk-Λ f₂) a)

------------------------------------------------------------------------
-- Types, representations, readings
------------------------------------------------------------------------

wk-wf : Wk k p ρ Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
wk-wf f (wf-var x) = wf-var (wk-tv f x)
wk-wf f wf-ℕ = wf-ℕ
wk-wf f wf-𝔹 = wf-𝔹
wk-wf f (wf-⇒ a b) = wf-⇒ (wk-wf f a) (wk-wf f b)
wk-wf f (wf-∀ a) = wf-∀ (wk-wf (wk-Λ f) a)

wk-wfᴿ : Wk k p ρ Δ Δ′ → Δ ⊢ᴿ S → Δ′ ⊢ᴿ renameᴿ ρ S
wk-wfᴿ f (wfᴿ-var a) = wfᴿ-var (wk-a f a)
wk-wfᴿ f wfᴿ-ℕ = wfᴿ-ℕ
wk-wfᴿ f wfᴿ-𝔹 = wfᴿ-𝔹
wk-wfᴿ f (wfᴿ-⇒ r s) = wfᴿ-⇒ (wk-wfᴿ f r) (wk-wfᴿ f s)
wk-wfᴿ f (wfᴿ-∀ r) = wfᴿ-∀ (wk-wfᴿ (wk-abst f) r)

wk-read : Wk k p ρ Δ Δ′ → Δ ⊢ S ⇓ A → Δ′ ⊢ renameᴿ ρ S ⇓ A
wk-read f (read-var x) = read-var (wk-n f x)
wk-read f read-ℕ = read-ℕ
wk-read f read-𝔹 = read-𝔹
wk-read f (read-⇒ r s) = read-⇒ (wk-read f r) (wk-read f s)
wk-read f (read-∀ r) = read-∀ (wk-read (wk-Λ f) r)

wk-quote : Wk k p ρ Δ Δ′ → Δ ⊢⌊ A ⌋ S → Δ′ ⊢⌊ A ⌋ renameᴿ ρ S
wk-quote f (quote-var x) = quote-var (wk-n f x)
wk-quote f quote-ℕ = quote-ℕ
wk-quote f quote-𝔹 = quote-𝔹
wk-quote f (quote-⇒ q r) = quote-⇒ (wk-quote f q) (wk-quote f r)
wk-quote f (quote-∀ q) = quote-∀ (wk-quote (wk-Λ f) q)

------------------------------------------------------------------------
-- The seam
------------------------------------------------------------------------
--
-- `conv-cons`'s intermediate context is existential, and `renConv` applies
-- ONE renaming to the whole conversion, so the seam must admit the SAME
-- insertion.  The seam condition on the conversion judgment says its anchor
-- count matches the endpoints', which is exactly what makes that possible.

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

mutual
  head-count : ∀ {h Δ₁ Δ₂ A B}
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → anchorCount Δ₁ ≡ anchorCount Δ₂
  head-count (conv-seal x r rd cnt) = cnt
  head-count (conv-unseal x r rd cnt) = cnt
  head-count (conv-fun s t) = sym (conv-count s)
  head-count (conv-all s) = suc-inj (conv-count s)

  conv-count : ∀ {c Δ₁ Δ₂ A B}
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → anchorCount Δ₁ ≡ anchorCount Δ₂
  conv-count (conv-id same cnt) = cnt
  conv-count (conv-cons hd tl) = trans (head-count hd) (conv-count tl)

blk-copy : Block k Δ Δ′ → ∀ Δ₂ → Σ[ Δ₂′ ∈ Ctxᵗ ] Block k Δ₂ Δ₂′
blk-copy blk[] Δ₂ = Δ₂ , blk[]
blk-copy (blk-abst b) Δ₂ with blk-copy b Δ₂
blk-copy (blk-abst b) Δ₂ | Δ₂′ , b′ = abst ∷ Δ₂′ , blk-abst b′
blk-copy (blk-bind {S = S} b) Δ₂ with blk-copy b Δ₂
blk-copy (blk-bind {S = S} b) Δ₂ | Δ₂′ , b′ = bind S ∷ Δ₂′ , blk-bind b′

wk-exists : ∀ {k p ρ Δ₁ Δ₁′} → Wk k p ρ Δ₁ Δ₁′
  → ∀ Δ₂ → anchorCount Δ₂ ≡ anchorCount Δ₁
  → Σ[ Δ₂′ ∈ Ctxᵗ ] Wk k p ρ Δ₂ Δ₂′
wk-exists {k = k} (wk-base b) Δ₂ eq with blk-copy b Δ₂
wk-exists {k = k} (wk-base b) Δ₂ eq | Δ₂′ , b′ =
  Δ₂′ , subst (λ q → Wk k q (shiftAnchor k) Δ₂ Δ₂′) eq (wk-base b′)
wk-exists (wk-abst f) [] ()
wk-exists (wk-abst f) (abst ∷ Δ₂) eq with wk-exists f Δ₂ (suc-inj eq)
wk-exists (wk-abst f) (abst ∷ Δ₂) eq | Δ₂′ , g = _ , wk-abst g
wk-exists (wk-abst f) (bind S ∷ Δ₂) eq with wk-exists f Δ₂ (suc-inj eq)
wk-exists (wk-abst f) (bind S ∷ Δ₂) eq | Δ₂′ , g = _ , wk-bind g
wk-exists (wk-abst f) (name α ∷ Δ₂) eq
  with wk-exists (wk-abst f) Δ₂ eq
wk-exists (wk-abst f) (name α ∷ Δ₂) eq | Δ₂′ , g = _ , wk-name g
wk-exists (wk-bind f) [] ()
wk-exists (wk-bind f) (abst ∷ Δ₂) eq with wk-exists f Δ₂ (suc-inj eq)
wk-exists (wk-bind f) (abst ∷ Δ₂) eq | Δ₂′ , g = _ , wk-abst g
wk-exists (wk-bind f) (bind S ∷ Δ₂) eq with wk-exists f Δ₂ (suc-inj eq)
wk-exists (wk-bind f) (bind S ∷ Δ₂) eq | Δ₂′ , g = _ , wk-bind g
wk-exists (wk-bind {S = S₀} f) (name α ∷ Δ₂) eq
  with wk-exists (wk-bind {S = S₀} f) Δ₂ eq
wk-exists (wk-bind {S = S₀} f) (name α ∷ Δ₂) eq | Δ₂′ , g = _ , wk-name g
wk-exists (wk-name f) Δ₂ eq = wk-exists f Δ₂ eq

wk-cnt : ∀ {k p ρ Δ₁ Δ₁′ Δ₂ Δ₂′}
  → Wk k p ρ Δ₁ Δ₁′ → Wk k p ρ Δ₂ Δ₂′
  → anchorCount Δ₁ ≡ anchorCount Δ₂ → anchorCount Δ₁′ ≡ anchorCount Δ₂′
wk-cnt {k = k} f₁ f₂ eq =
  trans (wk-count f₁) (trans (cong (k +_) eq) (sym (wk-count f₂)))

------------------------------------------------------------------------
-- Conversions
------------------------------------------------------------------------

IsIdᵗ : Renameᵗ → Set
IsIdᵗ ρᵗ = ∀ X → ρᵗ X ≡ X

extᵗ-id : ∀ {ρᵗ} → IsIdᵗ ρᵗ → IsIdᵗ (extᵗ ρᵗ)
extᵗ-id h zero = refl
extᵗ-id h (suc X) = cong suc (h X)

mutual
  wk-head : ∀ {ρᵗ h Δ₁ Δ₁′ Δ₂ Δ₂′} → IsIdᵗ ρᵗ
    → Wk k p ρ Δ₁ Δ₁′ → Wk k p ρ Δ₂ Δ₂′
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢̂ renHead ρᵗ ρ h ∶ A ⇝ B ⊣ Δ₂′
  wk-head hid f₁ f₂ (conv-seal x r rd cnt) =
    conv-seal (wk-n f₂ x) (wk-r f₂ r) (wk-read f₁ rd) (wk-cnt f₁ f₂ cnt)
  wk-head hid f₁ f₂ (conv-unseal x r rd cnt) =
    conv-unseal (wk-n f₁ x) (wk-r f₁ r) (wk-read f₂ rd) (wk-cnt f₁ f₂ cnt)
  wk-head hid f₁ f₂ (conv-fun s t) =
    conv-fun (wk-conv hid f₂ f₁ s) (wk-conv hid f₁ f₂ t)
  wk-head hid f₁ f₂ (conv-all s) =
    conv-all (wk-conv (extᵗ-id hid) (wk-Λ f₁) (wk-Λ f₂) s)

  wk-conv : ∀ {ρᵗ c Δ₁ Δ₁′ Δ₂ Δ₂′} → IsIdᵗ ρᵗ
    → Wk k p ρ Δ₁ Δ₁′ → Wk k p ρ Δ₂ Δ₂′
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢ renConv ρᵗ ρ c ∶ A ⇝ B ⊣ Δ₂′
  wk-conv {B = B} hid f₁ f₂ (conv-id same cnt)
    rewrite renameᵗ-id hid B =
    conv-id (wk-SameTy f₁ f₂ same) (wk-cnt f₁ f₂ cnt)
  wk-conv hid f₁ f₃ (conv-cons {Δ₂ = Δmid} hd tl)
    with wk-exists f₁ Δmid (sym (head-count hd))
  wk-conv hid f₁ f₃ (conv-cons hd tl) | Δmid′ , f₂ =
    conv-cons (wk-head hid f₁ f₂ hd) (wk-conv hid f₂ f₃ tl)

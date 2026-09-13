module strong.proof.AnchorWeaken where

-- Strong System F v7 — carrying a derivation under NEW ANCHORS.
--
-- `Beta`'s crossΛ sends a value across a `Λ`, `Wrap` sends the argument
-- inside the boundary's store, `TyWrap` and `Merge` re-read a conversion
-- under an extended store.  Each renames the anchor coordinate, and
-- preservation has to show the renamed derivation still types.
--
-- `Wk k ρ Δ Δ′` says Δ′ is Δ with a BLOCK of k anchor entries inserted at
-- the base, ρ the induced renaming.  The block's entries are CONCEALED — a
-- store introduces anchors, it does not name them — so the weakening moves
-- no source-variable index at all.  Descending under a binder lifts ρ with
-- `extᴿ`, so one (k, ρ) serves a whole conversion, which is what the syntax
-- demands: `renConv` applies ONE renaming throughout.
--
-- With merged entries `SameAnchor` is index equality, so it transports by
-- `cong ρ` and the de Bruijn LEVEL bookkeeping the split representation
-- needed here is gone.

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
open import strong.TermSubst using (renAnchᴹ; idᵗ-ren)
open import strong.proof.RenameAlgebra
open import strong.proof.NormalFormRename using (Injᴿ; NF-ren)

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ : Ctxᵗ
    Γ : Ctx
    A B : Ty
    R S : RepTy
    k X : ℕ
    α β : Anchor
    v : Vis
    b : AnchorBinding
    Θ : Store
    χ : Scope
    δ : Change
    c : Conv
    h : Head
    M : Term
    ρ : Renameᴿ

------------------------------------------------------------------------
-- The inserted block: anchors, CONCEALED
------------------------------------------------------------------------

data Block : ℕ → Ctxᵗ → Ctxᵗ → Set where
  blk[] : Block zero Δ Δ
  blk-∷ : Block k Δ Δ′ → Block (suc k) Δ (anch concealed b ∷ Δ′)

blk-count : Block k Δ Δ′ → anchorCount Δ′ ≡ k + anchorCount Δ
blk-count blk[] = refl
blk-count (blk-∷ b) = cong suc (blk-count b)

blk-a : Block k Δ Δ′ → Δ ∋a α → Δ′ ∋a (k + α)
blk-a blk[] t = t
blk-a (blk-∷ b) t = a-there (blk-a b t)

blk-tv : Block k Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
blk-tv blk[] t = t
blk-tv (blk-∷ b) t = tv-concealed (blk-tv b t)

blk-n : Block k Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := (k + α)
blk-n blk[] t = t
blk-n (blk-∷ b) t = n-concealed (blk-n b t)

blk-unn : Block k Δ Δ′ → Δ′ ∋n X := β
  → Σ[ α ∈ Anchor ] ((Δ ∋n X := α) × (β ≡ k + α))
blk-unn blk[] t = _ , t , refl
blk-unn (blk-∷ b) (n-concealed t) with blk-unn b t
blk-unn (blk-∷ b) (n-concealed t) | α , u , refl = α , u , refl

r-cast : S ≡ R → Δ ∋r α := S → Δ ∋r α := R
r-cast refl t = t

blk-r : Block k Δ Δ′ → Δ ∋r α := S
  → Δ′ ∋r (k + α) := renameᴿ (shiftAnchor k) S
blk-r {S = S} blk[] t = r-cast (sym (renameᴿ-id (λ α → refl) S)) t
blk-r {S = S} (blk-∷ {k = k} b) t =
  r-cast (renameᴿ-fuse suc (shiftAnchor k) S) (r-there (blk-r b t))

blk-copy : Block k Δ Δ′ → ∀ Δ₂ → Σ[ Δ₂′ ∈ Ctxᵗ ] Block k Δ₂ Δ₂′
blk-copy blk[] Δ₂ = Δ₂ , blk[]
blk-copy (blk-∷ {b = b} bl) Δ₂ with blk-copy bl Δ₂
blk-copy (blk-∷ {b = b} bl) Δ₂ | Δ₂′ , bl′ =
  anch concealed b ∷ Δ₂′ , blk-∷ bl′

-- The block is concealed, so a scope change passes straight through it.
blk-change : Block k Δ Δ′ → Δ ⊢δ δ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ]
      ((Δ′ ⊢δ renChange (shiftAnchor k) δ ⇒ Δ₂′) × Block k Δ₂ Δ₂′)
blk-change blk[] rev-here = _ , rev-here , blk[]
blk-change blk[] (rev-under d) = _ , rev-under d , blk[]
blk-change blk[] con-here = _ , con-here , blk[]
blk-change blk[] (con-under d) = _ , con-under d , blk[]
blk-change (blk-∷ b) rev-here with blk-change b rev-here
blk-change (blk-∷ b) rev-here | Δ₂′ , d′ , b′ =
  _ , rev-under d′ , blk-∷ b′
blk-change (blk-∷ b) (rev-under d) with blk-change b (rev-under d)
blk-change (blk-∷ b) (rev-under d) | Δ₂′ , d′ , b′ =
  _ , rev-under d′ , blk-∷ b′
blk-change (blk-∷ b) con-here with blk-change b con-here
blk-change (blk-∷ b) con-here | Δ₂′ , d′ , b′ =
  _ , con-under d′ , blk-∷ b′
blk-change (blk-∷ b) (con-under d) with blk-change b (con-under d)
blk-change (blk-∷ b) (con-under d) | Δ₂′ , d′ , b′ =
  _ , con-under d′ , blk-∷ b′

------------------------------------------------------------------------
-- The weakening
------------------------------------------------------------------------

data Wk : ℕ → Renameᴿ → Ctxᵗ → Ctxᵗ → Set where
  wk-base  : Block k Δ Δ′ → Wk k (shiftAnchor k) Δ Δ′
  wk-under : Wk k ρ Δ Δ′
           → Wk k (extᴿ ρ) (anch v b ∷ Δ) (anch v (renBind ρ b) ∷ Δ′)

wk-Λ : Wk k ρ Δ Δ′
  → Wk k (extᴿ ρ) (anch revealed abstA ∷ Δ) (anch revealed abstA ∷ Δ′)
wk-Λ = wk-under

wk-count : Wk k ρ Δ Δ′ → anchorCount Δ′ ≡ k + anchorCount Δ
wk-count (wk-base b) = blk-count b
wk-count {k = k} (wk-under f) =
  trans (cong suc (wk-count f)) (sym (+-suc k _))

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

wk-a : Wk k ρ Δ Δ′ → Δ ∋a α → Δ′ ∋a ρ α
wk-a (wk-base b) t = blk-a b t
wk-a (wk-under f) a-here = a-here
wk-a (wk-under f) (a-there t) = a-there (wk-a f t)

wk-tv : Wk k ρ Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
wk-tv (wk-base b) t = blk-tv b t
wk-tv (wk-under f) tv-here = tv-here
wk-tv (wk-under f) (tv-revealed t) = tv-revealed (wk-tv f t)
wk-tv (wk-under f) (tv-concealed t) = tv-concealed (wk-tv f t)

wk-n : Wk k ρ Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := ρ α
wk-n (wk-base b) t = blk-n b t
wk-n (wk-under f) n-here = n-here
wk-n (wk-under f) (n-revealed t) = n-revealed (wk-n f t)
wk-n (wk-under f) (n-concealed t) = n-concealed (wk-n f t)

wk-unn : Wk k ρ Δ Δ′ → Δ′ ∋n X := β
  → Σ[ α ∈ Anchor ] ((Δ ∋n X := α) × (β ≡ ρ α))
wk-unn (wk-base b) t = blk-unn b t
wk-unn (wk-under f) n-here = _ , n-here , refl
wk-unn (wk-under f) (n-revealed t) with wk-unn f t
wk-unn (wk-under f) (n-revealed t) | α , u , refl = _ , n-revealed u , refl
wk-unn (wk-under f) (n-concealed t) with wk-unn f t
wk-unn (wk-under f) (n-concealed t) | α , u , refl = _ , n-concealed u , refl

wk-r : Wk k ρ Δ Δ′ → Δ ∋r α := S → Δ′ ∋r ρ α := renameᴿ ρ S
wk-r (wk-base b) t = blk-r b t
wk-r (wk-under {ρ = ρ₀} f) (r-here {R = S₀}) =
  r-cast (sym (⇑ᴿ-comm ρ₀ S₀)) r-here
wk-r (wk-under {ρ = ρ₀} f) (r-there {R = S₀} t) =
  r-cast (sym (⇑ᴿ-comm ρ₀ S₀)) (r-there (wk-r f t))

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

wk-inj : Wk k ρ Δ Δ′ → Injᴿ ρ
wk-inj {k = k} (wk-base b) α β eq = cancel k α β eq
  where
  cancel : ∀ k α β → k + α ≡ k + β → α ≡ β
  cancel zero α β eq = eq
  cancel (suc k) α β eq = cancel k α β (suc-inj eq)
wk-inj (wk-under f) zero zero eq = refl
wk-inj (wk-under f) (suc α) (suc β) eq =
  cong suc (wk-inj f α β (suc-inj eq))

------------------------------------------------------------------------
-- Types, representations, readings, comparison
------------------------------------------------------------------------

-- An anchor match is index equality, so it transports by `cong ρ`.
wk-SameAnchor : ∀ {ρ} → Wk k ρ Δ₁ Δ₁′ → Wk k ρ Δ₂ Δ₂′
  → SameAnchor Δ₁ α Δ₂ β → SameAnchor Δ₁′ (ρ α) Δ₂′ (ρ β)
wk-SameAnchor {ρ = ρ} f₁ f₂ (same-anchor a₁ a₂ eq) =
  same-anchor (wk-a f₁ a₁) (wk-a f₂ a₂) (cong ρ eq)

wk-SameTy : ∀ {j} → Wk k ρ Δ₁ Δ₁′ → Wk k ρ Δ₂ Δ₂′
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

wk-wf : Wk k ρ Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
wk-wf f (wf-var x) = wf-var (wk-tv f x)
wk-wf f wf-ℕ = wf-ℕ
wk-wf f wf-𝔹 = wf-𝔹
wk-wf f (wf-⇒ a b) = wf-⇒ (wk-wf f a) (wk-wf f b)
wk-wf f (wf-∀ a) = wf-∀ (wk-wf (wk-Λ f) a)

wk-wfᴿ : Wk k ρ Δ Δ′ → Δ ⊢ᴿ S → Δ′ ⊢ᴿ renameᴿ ρ S
wk-wfᴿ f (wfᴿ-var a) = wfᴿ-var (wk-a f a)
wk-wfᴿ f wfᴿ-ℕ = wfᴿ-ℕ
wk-wfᴿ f wfᴿ-𝔹 = wfᴿ-𝔹
wk-wfᴿ f (wfᴿ-⇒ r s) = wfᴿ-⇒ (wk-wfᴿ f r) (wk-wfᴿ f s)
wk-wfᴿ f (wfᴿ-∀ r) = wfᴿ-∀ (wk-wfᴿ (wk-under f) r)

wk-read : Wk k ρ Δ Δ′ → Δ ⊢ S ⇓ A → Δ′ ⊢ renameᴿ ρ S ⇓ A
wk-read f (read-var x) = read-var (wk-n f x)
wk-read f read-ℕ = read-ℕ
wk-read f read-𝔹 = read-𝔹
wk-read f (read-⇒ r s) = read-⇒ (wk-read f r) (wk-read f s)
wk-read f (read-∀ r) = read-∀ (wk-read (wk-Λ f) r)

wk-quote : Wk k ρ Δ Δ′ → Δ ⊢⌊ A ⌋ S → Δ′ ⊢⌊ A ⌋ renameᴿ ρ S
wk-quote f (quote-var x) = quote-var (wk-n f x)
wk-quote f quote-ℕ = quote-ℕ
wk-quote f quote-𝔹 = quote-𝔹
wk-quote f (quote-⇒ q r) = quote-⇒ (wk-quote f q) (wk-quote f r)
wk-quote f (quote-∀ q) = quote-∀ (wk-quote (wk-Λ f) q)

------------------------------------------------------------------------
-- The seam
------------------------------------------------------------------------

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

wk-exists : ∀ {k ρ Δ₁ Δ₁′} → Wk k ρ Δ₁ Δ₁′
  → ∀ Δ₂ → anchorCount Δ₂ ≡ anchorCount Δ₁
  → Σ[ Δ₂′ ∈ Ctxᵗ ] Wk k ρ Δ₂ Δ₂′
wk-exists (wk-base b) Δ₂ eq with blk-copy b Δ₂
wk-exists (wk-base b) Δ₂ eq | Δ₂′ , b′ = Δ₂′ , wk-base b′
wk-exists (wk-under f) [] ()
wk-exists (wk-under f) (anch v b ∷ Δ₂) eq with wk-exists f Δ₂ (suc-inj eq)
wk-exists (wk-under f) (anch v b ∷ Δ₂) eq | Δ₂′ , g = _ , wk-under g

wk-cnt : ∀ {k ρ Δ₁ Δ₁′ Δ₂ Δ₂′} → Wk k ρ Δ₁ Δ₁′ → Wk k ρ Δ₂ Δ₂′
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
    → Wk k ρ Δ₁ Δ₁′ → Wk k ρ Δ₂ Δ₂′
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
    → Wk k ρ Δ₁ Δ₁′ → Wk k ρ Δ₂ Δ₂′
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁′ ⊢ renConv ρᵗ ρ c ∶ A ⇝ B ⊣ Δ₂′
  wk-conv {B = B} hid f₁ f₂ (conv-id same cnt)
    rewrite renameᵗ-id hid B =
    conv-id (wk-SameTy f₁ f₂ same) (wk-cnt f₁ f₂ cnt)
  wk-conv hid f₁ f₃ (conv-cons {Δ₂ = Δmid} hd tl)
    with wk-exists f₁ Δmid (sym (head-count hd))
  wk-conv hid f₁ f₃ (conv-cons hd tl) | Δmid′ , f₂ =
    conv-cons (wk-head hid f₁ f₂ hd) (wk-conv hid f₂ f₃ tl)

------------------------------------------------------------------------
-- Stores and scope changes
------------------------------------------------------------------------

extendAnchor-extᴿ : ∀ n (ρ : Renameᴿ)
  → extendAnchor n (extᴿ ρ) ≡ extᴿ (extendAnchor n ρ)
extendAnchor-extᴿ zero ρ = refl
extendAnchor-extᴿ (suc n) ρ = cong extᴿ (extendAnchor-extᴿ n ρ)

wk-change : ∀ {k ρ Δ Δ′ Δ₂ δ} → Wk k ρ Δ Δ′ → Δ ⊢δ δ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢δ renChange ρ δ ⇒ Δ₂′) × Wk k ρ Δ₂ Δ₂′)
wk-change (wk-base b) d with blk-change b d
wk-change (wk-base b) d | Δ₂′ , d′ , b′ = Δ₂′ , d′ , wk-base b′
wk-change (wk-under f) rev-here = _ , rev-here , wk-under f
wk-change (wk-under f) con-here = _ , con-here , wk-under f
wk-change (wk-under f) (rev-under d) with wk-change f d
wk-change (wk-under f) (rev-under d) | Δ₂′ , d′ , g =
  _ , rev-under d′ , wk-under g
wk-change (wk-under f) (con-under d) with wk-change f d
wk-change (wk-under f) (con-under d) | Δ₂′ , d′ , g =
  _ , con-under d′ , wk-under g

wk-scope : ∀ {k ρ Δ Δ′ Δ₂ χ} → Wk k ρ Δ Δ′ → Δ ⊢χ χ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢χ renScope ρ χ ⇒ Δ₂′) × Wk k ρ Δ₂ Δ₂′)
wk-scope f scope[] = _ , scope[] , f
wk-scope f (scope∷ d s) with wk-change f d
wk-scope f (scope∷ d s) | Δ₁′ , d′ , g with wk-scope g s
wk-scope f (scope∷ d s) | Δ₁′ , d′ , g | Δ₂′ , s′ , g′ =
  Δ₂′ , scope∷ d′ s′ , g′

wk-store : ∀ {k ρ Δ Δ′ Δ₂ Θ} → Wk k ρ Δ Δ′ → Δ ⊢ˢ Θ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢ˢ renStore ρ Θ ⇒ Δ₂′)
      × Wk k (extendAnchor (length Θ) ρ) Δ₂ Δ₂′)
wk-store f store[] = _ , store[] , f
wk-store {k = k} {ρ = ρ} {Δ₂ = Δ₂} f (store-abst {Θ = Θ} s)
  with wk-store (wk-under f) s
wk-store {k = k} {ρ = ρ} {Δ₂ = Δ₂} f (store-abst {Θ = Θ} s)
  | Δ₂′ , s′ , g =
  Δ₂′ , store-abst s′ ,
  subst (λ σ → Wk k σ Δ₂ Δ₂′) (extendAnchor-extᴿ (length Θ) ρ) g
wk-store {k = k} {ρ = ρ} {Δ₂ = Δ₂} f (store-bind {Θ = Θ} wf s)
  with wk-store (wk-under f) s
wk-store {k = k} {ρ = ρ} {Δ₂ = Δ₂} f (store-bind {Θ = Θ} wf s)
  | Δ₂′ , s′ , g =
  Δ₂′ , store-bind (wk-wfᴿ f wf) s′ ,
  subst (λ σ → Wk k σ Δ₂ Δ₂′) (extendAnchor-extᴿ (length Θ) ρ) g

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

wk-⊢ : ∀ {k ρ Δ Δ′ Γ M A} → Wk k ρ Δ Δ′
  → Δ ∣ Γ ⊢ M ⦂ A → Δ′ ∣ Γ ⊢ renAnchᴹ ρ M ⦂ A
wk-⊢ f (⊢` x) = ⊢` x
wk-⊢ f ⊢$ = ⊢$
wk-⊢ f ⊢# = ⊢#
wk-⊢ f (⊢⊕ l r) = ⊢⊕ (wk-⊢ f l) (wk-⊢ f r)
wk-⊢ f (⊢ƛ wf body) = ⊢ƛ (wk-wf f wf) (wk-⊢ f body)
wk-⊢ f (⊢· l r) = ⊢· (wk-⊢ f l) (wk-⊢ f r)
wk-⊢ f (⊢Λ body) = ⊢Λ (wk-⊢ (wk-Λ f) body)
wk-⊢ f (⊢•[] l wf) = ⊢•[] (wk-⊢ f l) (wk-wf f wf)
wk-⊢ f (⊢ν store scope nf body conv) with wk-store f store
wk-⊢ f (⊢ν store scope nf body conv) | ΔΘ′ , store′ , g
  with wk-scope g scope
wk-⊢ f (⊢ν store scope nf body conv) | ΔΘ′ , store′ , g
  | Δᵢ′ , scope′ , g′ =
  ⊢ν store′ scope′ (NF-ren (wk-inj g) nf)
     (wk-⊢ g′ body) (wk-conv (λ X → refl) g′ g conv)

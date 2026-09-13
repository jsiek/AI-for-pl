module strong.proof.AnchorWeaken where

-- Strong System F v7 — carrying a derivation under NEW ANCHORS.
--
-- `Beta`'s crossΛ sends a value across a `Λ`, `Wrap` sends the argument
-- inside the boundary's store, `TyWrap` and `Merge` re-read a conversion
-- under an extended store.  Each renames the anchor coordinate, and
-- preservation has to show the renamed derivation still types.
--
-- `Wk P d ρ Δ Δ′` says Δ′ is Δ with the CONCEALED block P inserted at
-- depth d, ρ the induced renaming.  Indexing by the block and the depth
-- makes the relation DETERMINISTIC (`wk-unique`), which is what lets two
-- contexts related by the conversion rules' spine discipline be weakened
-- in lockstep: `sb-wk` derives the weakening of a `SameBindings`-related
-- context, and `wk-flip` shows a `FlipAt` — one seal/unseal head's
-- crossing — survives, at the renamed anchor.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-comm)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (++-assoc; length-++)
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
open import strong.proof.ConversionProperties using (head-sb)

private
  variable
    Δ Δ′ Δ₁ Δ₁′ Δ₂ Δ₂′ Δoff Δoff′ Δon Δon′ : Ctxᵗ
    P : Ctxᵗ
    Γ : Ctx
    A B : Ty
    R S : RepTy
    d k X : ℕ
    α β : Anchor
    v : Vis
    b : AnchorBinding
    e : Ent
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

data Hidden : Ctxᵗ → Set where
  hid[] : Hidden []
  hid-∷ : Hidden P → Hidden (anch concealed b ∷ P)

------------------------------------------------------------------------
-- The weakening
------------------------------------------------------------------------

-- The renaming a weakening performs is a FUNCTION of its block and depth,
-- not an index: the block's length shifts, and each descent lifts.
wkRen : Ctxᵗ → ℕ → Renameᴿ
wkRen P zero    = shiftAnchor (length P)
wkRen P (suc d) = extᴿ (wkRen P d)

data Wk (P : Ctxᵗ) : ℕ → Ctxᵗ → Ctxᵗ → Set where
  wk-base  : Hidden P → Wk P zero Δ (P ++ Δ)
  wk-under : Wk P d Δ Δ′
           → Wk P (suc d) (anch v b ∷ Δ)
                          (anch v (renBind (wkRen P d) b) ∷ Δ′)

wk-Λ : Wk P d Δ Δ′
  → Wk P (suc d) (anch revealed abstA ∷ Δ) (anch revealed abstA ∷ Δ′)
wk-Λ = wk-under

wk-unique : Wk P d Δ Δ₁ → Wk P d Δ Δ₂ → Δ₁ ≡ Δ₂
wk-unique (wk-base _) (wk-base _) = refl
wk-unique (wk-under f) (wk-under g) rewrite wk-unique f g = refl

------------------------------------------------------------------------
-- Lockstep weakening along the spine discipline
------------------------------------------------------------------------

sb-++ : SameBindings Δ₁ Δ₂ → ∀ P → SameBindings (P ++ Δ₁) (P ++ Δ₂)
sb-++ s [] = s
sb-++ s (anch v b ∷ P) = sb-∷ (sb-++ s P)

sb-wk : SameBindings Δ₁ Δ₂ → Wk P d Δ₁ Δ₁′
  → Σ[ Δ₂′ ∈ Ctxᵗ ] (Wk P d Δ₂ Δ₂′ × SameBindings Δ₁′ Δ₂′)
sb-wk {P = P} s (wk-base hid) = _ , wk-base hid , sb-++ s P
sb-wk (sb-∷ s) (wk-under f) with sb-wk s f
sb-wk (sb-∷ s) (wk-under f) | Δ₂′ , g , s′ =
  _ , wk-under g , sb-∷ s′

wk-sb : Wk P d Δ₁ Δ₁′ → Wk P d Δ₂ Δ₂′
  → SameBindings Δ₁ Δ₂ → SameBindings Δ₁′ Δ₂′
wk-sb {P = P} (wk-base _) (wk-base _) s = sb-++ s P
wk-sb (wk-under f) (wk-under g) (sb-∷ s) = sb-∷ (wk-sb f g s)

flip-++ : ∀ {α} P → FlipAt α Δoff Δon
  → FlipAt (length P + α) (P ++ Δoff) (P ++ Δon)
flip-++ [] fl = fl
flip-++ (e ∷ P) fl = flip-there (flip-++ P fl)

wk-flip : ∀ {α} → Wk P d Δoff Δoff′ → Wk P d Δon Δon′
  → FlipAt α Δoff Δon → FlipAt (wkRen P d α) Δoff′ Δon′
wk-flip {P = P} (wk-base _) (wk-base _) fl = flip-++ P fl
wk-flip (wk-under f) (wk-under g) flip-here
  rewrite wk-unique f g = flip-here
wk-flip (wk-under f) (wk-under g) (flip-there fl) =
  flip-there (wk-flip f g fl)

------------------------------------------------------------------------
-- Lookups
------------------------------------------------------------------------

++-a : ∀ P → Δ ∋a α → (P ++ Δ) ∋a (length P + α)
++-a [] t = t
++-a (e ∷ P) t = a-there (++-a P t)

++-tv : Hidden P → Δ ∋tv X → (P ++ Δ) ∋tv X
++-tv hid[] t = t
++-tv (hid-∷ hid) t = tv-concealed (++-tv hid t)

++-n : Hidden P → Δ ∋n X := α → (P ++ Δ) ∋n X := (length P + α)
++-n hid[] t = t
++-n (hid-∷ hid) t = n-concealed (++-n hid t)

++-unn : Hidden P → (P ++ Δ) ∋n X := β
  → Σ[ α ∈ Anchor ] ((Δ ∋n X := α) × (β ≡ length P + α))
++-unn hid[] t = _ , t , refl
++-unn (hid-∷ hid) (n-concealed t) with ++-unn hid t
++-unn (hid-∷ hid) (n-concealed t) | α , u , refl = α , u , refl

r-cast : S ≡ R → Δ ∋r α := S → Δ ∋r α := R
r-cast refl t = t

++-r : Hidden P → Δ ∋r α := S
  → (P ++ Δ) ∋r (length P + α) := renameᴿ (shiftAnchor (length P)) S
++-r {S = S} hid[] t = r-cast (sym (renameᴿ-id (λ α → refl) S)) t
++-r {S = S} (hid-∷ {P = P} hid) t =
  r-cast (renameᴿ-fuse suc (shiftAnchor (length P)) S)
    (r-there (++-r hid t))

wk-a : Wk P d Δ Δ′ → Δ ∋a α → Δ′ ∋a wkRen P d α
wk-a {P = P} (wk-base _) t = ++-a P t
wk-a (wk-under f) a-here = a-here
wk-a (wk-under f) (a-there t) = a-there (wk-a f t)

wk-tv : Wk P d Δ Δ′ → Δ ∋tv X → Δ′ ∋tv X
wk-tv (wk-base hid) t = ++-tv hid t
wk-tv (wk-under {v = revealed} f) tv-here = tv-here
wk-tv (wk-under {v = revealed} f) (tv-revealed t) =
  tv-revealed (wk-tv f t)
wk-tv (wk-under {v = concealed} f) (tv-concealed t) =
  tv-concealed (wk-tv f t)

wk-n : Wk P d Δ Δ′ → Δ ∋n X := α → Δ′ ∋n X := wkRen P d α
wk-n (wk-base hid) t = ++-n hid t
wk-n (wk-under {v = revealed} f) n-here = n-here
wk-n (wk-under {v = revealed} f) (n-revealed t) = n-revealed (wk-n f t)
wk-n (wk-under {v = concealed} f) (n-concealed t) =
  n-concealed (wk-n f t)

wk-unn : Wk P d Δ Δ′ → Δ′ ∋n X := β
  → Σ[ α ∈ Anchor ] ((Δ ∋n X := α) × (β ≡ wkRen P d α))
wk-unn (wk-base hid) t = ++-unn hid t
wk-unn (wk-under {v = revealed} f) n-here = _ , n-here , refl
wk-unn (wk-under {v = revealed} f) (n-revealed t) with wk-unn f t
wk-unn (wk-under {v = revealed} f) (n-revealed t) | α , u , refl =
  _ , n-revealed u , refl
wk-unn (wk-under {v = concealed} f) (n-concealed t) with wk-unn f t
wk-unn (wk-under {v = concealed} f) (n-concealed t) | α , u , refl =
  _ , n-concealed u , refl

wk-r : Wk P d Δ Δ′ → Δ ∋r α := S
  → Δ′ ∋r wkRen P d α := renameᴿ (wkRen P d) S
wk-r (wk-base hid) t = ++-r hid t
wk-r {P = P} (wk-under {d = d} {b = bindA S₀} f) r-here =
  r-cast (sym (⇑ᴿ-comm (wkRen P d) S₀)) r-here
wk-r {P = P} (wk-under {d = d} f) (r-there {R = S₀} t) =
  r-cast (sym (⇑ᴿ-comm (wkRen P d) S₀)) (r-there (wk-r f t))

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

wk-inj : Wk P d Δ Δ′ → Injᴿ (wkRen P d)
wk-inj {P = P} (wk-base _) α β eq = cancel (length P) α β eq
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

wk-SameAnchor : ∀ {β} → Wk P d Δ₁ Δ₁′ → Wk P d Δ₂ Δ₂′
  → SameAnchor Δ₁ α Δ₂ β
  → SameAnchor Δ₁′ (wkRen P d α) Δ₂′ (wkRen P d β)
wk-SameAnchor {P = P} {d = d} f₁ f₂ (same-anchor a₁ a₂ eq) =
  same-anchor (wk-a f₁ a₁) (wk-a f₂ a₂) (cong (wkRen P d) eq)

wk-SameTy : Wk P d Δ₁ Δ₁′ → Wk P d Δ₂ Δ₂′
  → SameTy k Δ₁ A Δ₂ B → SameTy k Δ₁′ A Δ₂′ B
wk-SameTy f₁ f₂ (same-bound q) = same-bound q
wk-SameTy f₁ f₂ (same-free n₁ n₂ sa) =
  same-free (wk-n f₁ n₁) (wk-n f₂ n₂) (wk-SameAnchor f₁ f₂ sa)
wk-SameTy f₁ f₂ same-ℕ = same-ℕ
wk-SameTy f₁ f₂ same-𝔹 = same-𝔹
wk-SameTy f₁ f₂ (same-⇒ a b) =
  same-⇒ (wk-SameTy f₁ f₂ a) (wk-SameTy f₁ f₂ b)
wk-SameTy f₁ f₂ (same-∀ a) =
  same-∀ (wk-SameTy (wk-Λ f₁) (wk-Λ f₂) a)

wk-wf : Wk P d Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
wk-wf f (wf-var x) = wf-var (wk-tv f x)
wk-wf f wf-ℕ = wf-ℕ
wk-wf f wf-𝔹 = wf-𝔹
wk-wf f (wf-⇒ a b) = wf-⇒ (wk-wf f a) (wk-wf f b)
wk-wf f (wf-∀ a) = wf-∀ (wk-wf (wk-Λ f) a)

wk-wfᴿ : Wk P d Δ Δ′ → Δ ⊢ᴿ S → Δ′ ⊢ᴿ renameᴿ (wkRen P d) S
wk-wfᴿ f (wfᴿ-var a) = wfᴿ-var (wk-a f a)
wk-wfᴿ f wfᴿ-ℕ = wfᴿ-ℕ
wk-wfᴿ f wfᴿ-𝔹 = wfᴿ-𝔹
wk-wfᴿ f (wfᴿ-⇒ r s) = wfᴿ-⇒ (wk-wfᴿ f r) (wk-wfᴿ f s)
wk-wfᴿ f (wfᴿ-∀ r) = wfᴿ-∀ (wk-wfᴿ (wk-under f) r)

wk-read : Wk P d Δ Δ′ → Δ ⊢ S ⇓ A → Δ′ ⊢ renameᴿ (wkRen P d) S ⇓ A
wk-read f (read-var x) = read-var (wk-n f x)
wk-read f read-ℕ = read-ℕ
wk-read f read-𝔹 = read-𝔹
wk-read f (read-⇒ r s) = read-⇒ (wk-read f r) (wk-read f s)
wk-read f (read-∀ r) = read-∀ (wk-read (wk-Λ f) r)

wk-quote : Wk P d Δ Δ′ → Δ ⊢⌊ A ⌋ S → Δ′ ⊢⌊ A ⌋ renameᴿ (wkRen P d) S
wk-quote f (quote-var x) = quote-var (wk-n f x)
wk-quote f quote-ℕ = quote-ℕ
wk-quote f quote-𝔹 = quote-𝔹
wk-quote f (quote-⇒ q r) = quote-⇒ (wk-quote f q) (wk-quote f r)
wk-quote f (quote-∀ q) = quote-∀ (wk-quote (wk-Λ f) q)

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
    → Wk P d Δ₁ Δ₁′ → Wk P d Δ₂ Δ₂′
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂
    → Δ₁′ ⊢̂ renHead ρᵗ (wkRen P d) h ∶ A ⇝ B ⊣ Δ₂′
  wk-head hid f₁ f₂ (conv-seal x r rd flip) =
    conv-seal (wk-n f₂ x) (wk-r f₂ r) (wk-read f₁ rd)
      (wk-flip f₁ f₂ flip)
  wk-head hid f₁ f₂ (conv-unseal x r rd flip) =
    conv-unseal (wk-n f₁ x) (wk-r f₁ r) (wk-read f₂ rd)
      (wk-flip f₂ f₁ flip)
  wk-head hid f₁ f₂ (conv-fun s t) =
    conv-fun (wk-conv hid f₂ f₁ s) (wk-conv hid f₁ f₂ t)
  wk-head hid f₁ f₂ (conv-all s) =
    conv-all (wk-conv (extᵗ-id hid) (wk-Λ f₁) (wk-Λ f₂) s)

  wk-conv : ∀ {ρᵗ c Δ₁ Δ₁′ Δ₂ Δ₂′} → IsIdᵗ ρᵗ
    → Wk P d Δ₁ Δ₁′ → Wk P d Δ₂ Δ₂′
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂
    → Δ₁′ ⊢ renConv ρᵗ (wkRen P d) c ∶ A ⇝ B ⊣ Δ₂′
  wk-conv {B = B} hid f₁ f₂ (conv-id same sb)
    rewrite renameᵗ-id hid B =
    conv-id (wk-SameTy f₁ f₂ same) (wk-sb f₁ f₂ sb)
  wk-conv hid f₁ f₃ (conv-cons hd tl) with wk-tail hid f₃ tl
  wk-conv hid f₁ f₃ (conv-cons hd tl) | Δ₂′ , g , tl′ =
    conv-cons (wk-head hid f₁ g hd) tl′

  wk-tail : ∀ {ρᵗ c Δ₁ Δ₂ Δ₂′} → IsIdᵗ ρᵗ → Wk P d Δ₂ Δ₂′
    → Δ₁ ⊩ c ∶ A ⇝ B ⊣ Δ₂
    → Σ[ Δ₁′ ∈ Ctxᵗ ]
        (Wk P d Δ₁ Δ₁′ × (Δ₁′ ⊩ renConv ρᵗ (wkRen P d) c ∶ A ⇝ B ⊣ Δ₂′))
  wk-tail {A = A} hid f (tail-id wf)
    rewrite renameᵗ-id hid A = _ , f , tail-id (wk-wf f wf)
  wk-tail hid f (tail-cons hd tl) with wk-tail hid f tl
  wk-tail hid f (tail-cons hd tl) | Δᵐ′ , g , tl′
    with sb-wk (sb-sym (head-sb hd)) g
  wk-tail hid f (tail-cons hd tl) | Δᵐ′ , g , tl′ | Δ₁′ , f₁ , _ =
    _ , f₁ , tail-cons (wk-head hid f₁ g hd) tl′

------------------------------------------------------------------------
-- Stores and scope changes
------------------------------------------------------------------------

extendAnchor-extᴿ : ∀ n (ρ : Renameᴿ)
  → extendAnchor n (extᴿ ρ) ≡ extᴿ (extendAnchor n ρ)
extendAnchor-extᴿ zero ρ = refl
extendAnchor-extᴿ (suc n) ρ = cong extᴿ (extendAnchor-extᴿ n ρ)

wk-change : ∀ {Δ Δ′ Δ₂ δ} → Wk P d Δ Δ′ → Δ ⊢δ δ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ]
      ((Δ′ ⊢δ renChange (wkRen P d) δ ⇒ Δ₂′) × Wk P d Δ₂ Δ₂′)
wk-change (wk-base hid) d = blk-change hid d
  where
  blk-change : ∀ {P Δ Δ₂ δ} → Hidden P → Δ ⊢δ δ ⇒ Δ₂
    → Σ[ Δ₂′ ∈ Ctxᵗ ]
        (((P ++ Δ) ⊢δ renChange (shiftAnchor (length P)) δ ⇒ Δ₂′)
         × Wk P zero Δ₂ Δ₂′)
  blk-change hid[] rev-here = _ , rev-here , wk-base hid[]
  blk-change hid[] (rev-under d) = _ , rev-under d , wk-base hid[]
  blk-change hid[] con-here = _ , con-here , wk-base hid[]
  blk-change hid[] (con-under d) = _ , con-under d , wk-base hid[]
  blk-change (hid-∷ hid) d with blk-change hid d
  blk-change (hid-∷ hid) rev-here | Δ₂′ , d′ , wk-base h′ =
    _ , rev-under d′ , wk-base (hid-∷ h′)
  blk-change (hid-∷ hid) (rev-under d) | Δ₂′ , d′ , wk-base h′ =
    _ , rev-under d′ , wk-base (hid-∷ h′)
  blk-change (hid-∷ hid) con-here | Δ₂′ , d′ , wk-base h′ =
    _ , con-under d′ , wk-base (hid-∷ h′)
  blk-change (hid-∷ hid) (con-under d) | Δ₂′ , d′ , wk-base h′ =
    _ , con-under d′ , wk-base (hid-∷ h′)
wk-change (wk-under f) rev-here = _ , rev-here , wk-under f
wk-change (wk-under f) con-here = _ , con-here , wk-under f
wk-change (wk-under f) (rev-under d) with wk-change f d
wk-change (wk-under f) (rev-under d) | Δ₂′ , d′ , g =
  _ , rev-under d′ , wk-under g
wk-change (wk-under f) (con-under d) with wk-change f d
wk-change (wk-under f) (con-under d) | Δ₂′ , d′ , g =
  _ , con-under d′ , wk-under g

wk-scope : ∀ {Δ Δ′ Δ₂ χ} → Wk P d Δ Δ′ → Δ ⊢χ χ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ]
      ((Δ′ ⊢χ renScope (wkRen P d) χ ⇒ Δ₂′) × Wk P d Δ₂ Δ₂′)
wk-scope f scope[] = _ , scope[] , f
wk-scope f (scope∷ d s) with wk-change f d
wk-scope f (scope∷ d s) | Δ₁′ , d′ , g with wk-scope g s
wk-scope f (scope∷ d s) | Δ₁′ , d′ , g | Δ₂′ , s′ , g′ =
  Δ₂′ , scope∷ d′ s′ , g′

-- The lift a store performs agrees with the depth the weakening gains.
wkRen-ext : ∀ P k d → extendAnchor k (wkRen P d) ≡ wkRen P (k + d)
wkRen-ext P zero d = refl
wkRen-ext P (suc k) d = cong extᴿ (wkRen-ext P k d)

wk-store : ∀ {Δ Δ′ Δ₂ Θ} → Wk P d Δ Δ′ → Δ ⊢ˢ Θ ⇒ Δ₂
  → Σ[ Δ₂′ ∈ Ctxᵗ ] ((Δ′ ⊢ˢ renStore (wkRen P d) Θ ⇒ Δ₂′)
      × Wk P (length Θ + d) Δ₂ Δ₂′)
wk-store f store[] = _ , store[] , f
wk-store {P = P} {d = d} {Δ₂ = Δ₂} f (store-abst {Θ = Θ} s)
  with wk-store (wk-under f) s
wk-store {P = P} {d = d} {Δ₂ = Δ₂} f (store-abst {Θ = Θ} s)
  | Δ₂′ , s′ , g =
  Δ₂′ , store-abst s′ ,
  subst (λ m → Wk P m Δ₂ Δ₂′) (+-suc (length Θ) d) g
wk-store {P = P} {d = d} {Δ₂ = Δ₂} f (store-bind {Θ = Θ} wf s)
  with wk-store (wk-under f) s
wk-store {P = P} {d = d} {Δ₂ = Δ₂} f (store-bind {Θ = Θ} wf s)
  | Δ₂′ , s′ , g =
  Δ₂′ , store-bind (wk-wfᴿ f wf) s′ ,
  subst (λ m → Wk P m Δ₂ Δ₂′) (+-suc (length Θ) d) g

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

wk-⊢ : ∀ {Δ Δ′ Γ M A} → Wk P d Δ Δ′
  → Δ ∣ Γ ⊢ M ⦂ A → Δ′ ∣ Γ ⊢ renAnchᴹ (wkRen P d) M ⦂ A
wk-⊢ f (⊢` x) = ⊢` x
wk-⊢ f ⊢$ = ⊢$
wk-⊢ f ⊢# = ⊢#
wk-⊢ f (⊢⊕ l r) = ⊢⊕ (wk-⊢ f l) (wk-⊢ f r)
wk-⊢ f (⊢ƛ wf body) = ⊢ƛ (wk-wf f wf) (wk-⊢ f body)
wk-⊢ f (⊢· l r) = ⊢· (wk-⊢ f l) (wk-⊢ f r)
wk-⊢ f (⊢Λ body) = ⊢Λ (wk-⊢ (wk-Λ f) body)
wk-⊢ f (⊢•[] l wf) = ⊢•[] (wk-⊢ f l) (wk-wf f wf)
wk-⊢ {P = P} {d = d} f (⊢ν {Θ = Θ} store scope nf body conv)
  rewrite wkRen-ext P (length Θ) d
  with wk-store f store
wk-⊢ {P = P} {d = d} f (⊢ν {Θ = Θ} store scope nf body conv)
  | ΔΘ′ , store′ , g
  with wk-scope g scope
wk-⊢ {P = P} {d = d} f (⊢ν {Θ = Θ} store scope nf body conv)
  | ΔΘ′ , store′ , g | Δᵢ′ , scope′ , g′ =
  ⊢ν store′ scope′ (NF-ren (wk-inj g) nf)
     (wk-⊢ g′ body) (wk-conv (λ X → refl) g′ g conv)

------------------------------------------------------------------------
-- The store's own weakening: Δ into ΔΘ
------------------------------------------------------------------------
--
-- A store IS a hidden block.  The store recurses at the base while the
-- block sits at the top, so each pushed entry is absorbed by a SNOC.

hidden-snoc : ∀ {P b}
  → Hidden P → Hidden (P ++ (anch concealed b ∷ []))
hidden-snoc hid[] = hid-∷ hid[]
hidden-snoc (hid-∷ h) = hid-∷ (hidden-snoc h)

store-split : ∀ {Δ ΔΘ Θ} → Δ ⊢ˢ Θ ⇒ ΔΘ
  → Σ[ P ∈ Ctxᵗ ]
      (Hidden P × (ΔΘ ≡ P ++ Δ) × (length P ≡ length Θ))
store-split store[] = [] , hid[] , refl , refl
store-split (store-abst s) with store-split s
store-split {Δ = Δ} (store-abst s) | P , hid , refl , eq =
  P ++ (anch concealed abstA ∷ []) , hidden-snoc hid ,
  sym (++-assoc P (anch concealed abstA ∷ []) Δ) ,
  trans (length-++ P) (trans (cong (_+ 1) eq) (+-comm _ 1))
store-split (store-bind {R = R} wf s) with store-split s
store-split {Δ = Δ} (store-bind {R = R} wf s) | P , hid , refl , eq =
  P ++ (anch concealed (bindA R) ∷ []) , hidden-snoc hid ,
  sym (++-assoc P (anch concealed (bindA R) ∷ []) Δ) ,
  trans (length-++ P) (trans (cong (_+ 1) eq) (+-comm _ 1))

store-wk : ∀ {Δ ΔΘ Θ} → Δ ⊢ˢ Θ ⇒ ΔΘ
  → Σ[ P ∈ Ctxᵗ ] (Wk P zero Δ ΔΘ × (length P ≡ length Θ))
store-wk s with store-split s
store-wk s | P , hid , refl , eq = P , wk-base hid , eq

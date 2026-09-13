module strong.ConversionReduction where

-- Strong System F v7 — conversion composition as NORMALIZATION.
--
-- Modelled on GTLC/agda/proof/CoercionReduction.agda.  Composition does
-- not compute its normal form in one fuel-driven pass; instead there is a
-- small-step reduction on conversions — one `fuse` of an adjacent pair of
-- heads, or a congruence step into a `↦` or `all` component — together
-- with
--
--   * progress:  a conversion is `NF` or it steps, decidably and untyped;
--   * a measure: every step strictly decreases `weight`,
--
-- and `normalize` is well-founded recursion on the measure.  The
-- composition the reduction rules use is then
--
--   c ⨟ d = normalize (c ⧺ d)
--
-- and `normalize-↠`/`normalize-NF` hand the metatheory a reduction trace
-- and normality instead of a fuel computation to unwind.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  (_≟_; +-assoc; +-comm; +-suc; +-identityʳ; n<1+n;
   +-monoˡ-<; +-monoʳ-<; ≤-refl; ≤-trans; m≤m+n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types
open import strong.RepresentationTypes using (Anchor)
open import strong.Conversion

private
  variable
    c c′ d d′ s s′ t t′ e : Conv
    h k : Head
    ks : List Head
    α β : Anchor
    A : Ty

------------------------------------------------------------------------
-- One step
------------------------------------------------------------------------

consAll : List Head → Conv → Conv
consAll []       c = c
consAll (h ∷ hs) c = h ∷ᶜ consAll hs c

infix 4 _—→ᶜ_
data _—→ᶜ_ : Conv → Conv → Set where
  ξ-pair : fuse h k ≡ just ks
    → (h ∷ᶜ k ∷ᶜ c) —→ᶜ consAll ks c
  ξ-∷ : c —→ᶜ c′ → (h ∷ᶜ c) —→ᶜ (h ∷ᶜ c′)
  ξ-↦₁ : s —→ᶜ s′ → ((s ↦ t) ∷ᶜ c) —→ᶜ ((s′ ↦ t) ∷ᶜ c)
  ξ-↦₂ : t —→ᶜ t′ → ((s ↦ t) ∷ᶜ c) —→ᶜ ((s ↦ t′) ∷ᶜ c)
  ξ-all : s —→ᶜ s′ → (all s ∷ᶜ c) —→ᶜ (all s′ ∷ᶜ c)

infix 4 _—↠ᶜ_
data _—↠ᶜ_ : Conv → Conv → Set where
  done : c —↠ᶜ c
  step : c —→ᶜ d → d —↠ᶜ e → c —↠ᶜ e

—↠ᶜ-trans : c —↠ᶜ d → d —↠ᶜ e → c —↠ᶜ e
—↠ᶜ-trans done st = st
—↠ᶜ-trans (step s₁ ss) st = step s₁ (—↠ᶜ-trans ss st)

------------------------------------------------------------------------
-- The measure
------------------------------------------------------------------------

weight-⧺ : ∀ c d → suc (weight (c ⧺ d)) ≡ weight c + weight d
weight-⧺ (id A) d = refl
weight-⧺ (h ∷ᶜ c) d = cong suc
  (trans (sym (+-suc (weightHead h) (weight (c ⧺ d))))
    (trans (cong (weightHead h +_) (weight-⧺ c d))
      (sym (+-assoc (weightHead h) (weight c) (weight d)))))

weightHeads⁺ : List Head → ℕ
weightHeads⁺ []       = zero
weightHeads⁺ (h ∷ hs) = suc (weightHead h + weightHeads⁺ hs)

weight-consAll : ∀ ks c
  → weight (consAll ks c) ≡ weightHeads⁺ ks + weight c
weight-consAll [] c = refl
weight-consAll (h ∷ hs) c
  rewrite weight-consAll hs c =
  cong suc (sym (+-assoc (weightHead h) (weightHeads⁺ hs) (weight c)))

less-by : ∀ m k n → suc m + k ≡ n → m < n
less-by m k n eq = subst (suc m ≤_) eq (m≤m+n (suc m) k)

-- Reading `fuse` back out of a success at the two anchor pairs, where its
-- definition decides anchor equality.
fuse-su-inv : ∀ α β ks → fuse (seal α) (unseal β) ≡ just ks → ks ≡ []
fuse-su-inv α β ks eq with α ≟ β | eq
fuse-su-inv α β ks eq | yes p | refl = refl
fuse-su-inv α β ks eq | no _ | ()

fuse-us-inv : ∀ α β ks → fuse (unseal α) (seal β) ≡ just ks → ks ≡ []
fuse-us-inv α β ks eq with α ≟ β | eq
fuse-us-inv α β ks eq | yes p | refl = refl
fuse-us-inv α β ks eq | no _ | ()

private
  open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ˢ_)

  -- The exact bookkeeping of a `↦` fusion: one head constructor and two
  -- terminators disappear, everything else is kept — a decrease of
  -- exactly four in `weight`, of which one is the deleted cons.
  ↦-arith : ∀ a b w x y z → suc a ≡ y + w → suc b ≡ x + z
    → suc (suc (suc (a + b) + 0)) + 3
    ≡ suc (suc (w + x) + suc (suc (y + z)))
  ↦-arith a b w x y z ea eb =
    trans (solve 2 (λ a b → (con 1 :+ (con 1 :+ ((con 1 :+ (a :+ b))
              :+ con 0)) :+ con 3)
              :=ˢ (con 1 :+ a) :+ ((con 1 :+ b) :+ con 4)) refl a b)
      (trans (cong₂ (λ u v → u + (v + 4)) ea eb)
        (solve 4 (λ w x y z → (y :+ w) :+ ((x :+ z) :+ con 4)
              :=ˢ con 1 :+ ((con 1 :+ (w :+ x))
                  :+ (con 1 :+ (con 1 :+ (y :+ z))))) refl w x y z))

  all-arith : ∀ a s t → suc a ≡ s + t
    → suc (suc (suc a + 0)) + 2 ≡ suc (suc s + suc (suc t))
  all-arith a s t ea =
    trans (solve 1 (λ a → (con 1 :+ (con 1 :+ ((con 1 :+ a) :+ con 0))
              :+ con 2) :=ˢ (con 1 :+ a) :+ con 4) refl a)
      (trans (cong (_+ 4) ea)
        (solve 2 (λ s t → (s :+ t) :+ con 4
              :=ˢ con 1 :+ ((con 1 :+ s) :+ (con 1 :+ (con 1 :+ t))))
          refl s t))

fuse-decreases : ∀ h k ks → fuse h k ≡ just ks
  → weightHeads⁺ ks < suc (weightHead h + suc (weightHead k))
fuse-decreases (seal α) (unseal β) ks eq
  rewrite fuse-su-inv α β ks eq = s≤s z≤n
fuse-decreases (unseal α) (seal β) ks eq
  rewrite fuse-us-inv α β ks eq = s≤s z≤n
fuse-decreases (s₁ ↦ t₁) (s₂ ↦ t₂) _ refl =
  less-by _ 3 _
    (↦-arith (weight (s₂ ⧺ s₁)) (weight (t₁ ⧺ t₂))
      (weight s₁) (weight t₁) (weight s₂) (weight t₂)
      (weight-⧺ s₂ s₁) (weight-⧺ t₁ t₂))
fuse-decreases (all s) (all t) _ refl =
  less-by _ 2 _
    (all-arith (weight (s ⧺ t)) (weight s) (weight t) (weight-⧺ s t))
fuse-decreases (seal α) (seal β) ks ()
fuse-decreases (seal α) (c ↦ d) ks ()
fuse-decreases (seal α) (all c) ks ()
fuse-decreases (unseal α) (unseal β) ks ()
fuse-decreases (unseal α) (c ↦ d) ks ()
fuse-decreases (unseal α) (all c) ks ()
fuse-decreases (c ↦ d) (seal β) ks ()
fuse-decreases (c ↦ d) (unseal β) ks ()
fuse-decreases (c ↦ d) (all e) ks ()
fuse-decreases (all c) (seal β) ks ()
fuse-decreases (all c) (unseal β) ks ()
fuse-decreases (all c) (s′ ↦ t′) ks ()

step-decreases : c —→ᶜ c′ → weight c′ < weight c
step-decreases (ξ-pair {h = h} {k = k} {ks = ks} {c = c} eq)
  rewrite weight-consAll ks c =
  subst (weightHeads⁺ ks + weight c <_)
    (solve 3 (λ p q r → (con 1 :+ (p :+ (con 1 :+ q))) :+ r
          :=ˢ con 1 :+ (p :+ (con 1 :+ (q :+ r))))
      refl (weightHead h) (weightHead k) (weight c))
    (+-monoˡ-< (weight c) (fuse-decreases h k ks eq))
  where open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ˢ_)
step-decreases (ξ-∷ {h = h} st) =
  s≤s (+-monoʳ-< (weightHead h) (step-decreases st))
step-decreases (ξ-↦₁ {t = t} {c = c} st) =
  s≤s (+-monoˡ-< (weight c)
    (s≤s (+-monoˡ-< (weight t) (step-decreases st))))
step-decreases (ξ-↦₂ {s = s} {c = c} st) =
  s≤s (+-monoˡ-< (weight c)
    (s≤s (+-monoʳ-< (weight s) (step-decreases st))))
step-decreases (ξ-all {c = c} st) =
  s≤s (+-monoˡ-< (weight c) (s≤s (step-decreases st)))

------------------------------------------------------------------------
-- Progress: a conversion is normal or it steps
------------------------------------------------------------------------

Steps : Conv → Set
Steps c = Σ[ c′ ∈ Conv ] (c —→ᶜ c′)

-- Once the head and the tail are normal, only the seam can fire.
check-seam : ∀ h c → NFHead h → NF c → NF (h ∷ᶜ c) ⊎ Steps (h ∷ᶜ c)
check-seam h (id A) nfh nfc = inj₁ (nf-cons nfh nf-id irr-id)
check-seam h (k ∷ᶜ c) nfh nfc with fuse h k in eq
check-seam h (k ∷ᶜ c) nfh nfc | just ks = inj₂ (_ , ξ-pair eq)
check-seam h (k ∷ᶜ c) nfh nfc | nothing =
  inj₁ (nf-cons nfh nfc (irr-cons eq))

progress : (c : Conv) → NF c ⊎ Steps c
progress (id A) = inj₁ nf-id
progress (seal α ∷ᶜ c) with progress c
progress (seal α ∷ᶜ c) | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (seal α ∷ᶜ c) | inj₁ nfc = check-seam (seal α) c nf-seal nfc
progress (unseal α ∷ᶜ c) with progress c
progress (unseal α ∷ᶜ c) | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (unseal α ∷ᶜ c) | inj₁ nfc = check-seam (unseal α) c nf-unseal nfc
progress ((s ↦ t) ∷ᶜ c) with progress s
progress ((s ↦ t) ∷ᶜ c) | inj₂ (s′ , st) = inj₂ (_ , ξ-↦₁ st)
progress ((s ↦ t) ∷ᶜ c) | inj₁ nfs with progress t
progress ((s ↦ t) ∷ᶜ c) | inj₁ nfs | inj₂ (t′ , st) =
  inj₂ (_ , ξ-↦₂ st)
progress ((s ↦ t) ∷ᶜ c) | inj₁ nfs | inj₁ nft with progress c
progress ((s ↦ t) ∷ᶜ c) | inj₁ nfs | inj₁ nft | inj₂ (c′ , st) =
  inj₂ (_ , ξ-∷ st)
progress ((s ↦ t) ∷ᶜ c) | inj₁ nfs | inj₁ nft | inj₁ nfc =
  check-seam (s ↦ t) c (nf-fun nfs nft) nfc
progress (all s ∷ᶜ c) with progress s
progress (all s ∷ᶜ c) | inj₂ (s′ , st) = inj₂ (_ , ξ-all st)
progress (all s ∷ᶜ c) | inj₁ nfs with progress c
progress (all s ∷ᶜ c) | inj₁ nfs | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (all s ∷ᶜ c) | inj₁ nfs | inj₁ nfc =
  check-seam (all s) c (nf-all nfs) nfc

------------------------------------------------------------------------
-- Normalization, by well-founded recursion on the measure
------------------------------------------------------------------------

normalize-acc : (c : Conv) → Acc _<_ (weight c)
  → Σ[ d ∈ Conv ] ((c —↠ᶜ d) × NF d)
normalize-acc c a with progress c
normalize-acc c a | inj₁ nf = c , done , nf
normalize-acc c (acc rec) | inj₂ (c′ , st)
  with normalize-acc c′ (rec (step-decreases st))
normalize-acc c (acc rec) | inj₂ (c′ , st) | d , tr , nf =
  d , step st tr , nf

normalize : Conv → Conv
normalize c = proj₁ (normalize-acc c (<-wellFounded (weight c)))

normalize-↠ : ∀ c → c —↠ᶜ normalize c
normalize-↠ c = proj₁ (proj₂ (normalize-acc c (<-wellFounded (weight c))))

normalize-NF : ∀ c → NF (normalize c)
normalize-NF c = proj₂ (proj₂ (normalize-acc c (<-wellFounded (weight c))))

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

infixl 5 _⨟_
_⨟_ : Conv → Conv → Conv
c ⨟ d = normalize (c ⧺ d)

⨟-↠ : ∀ c d → (c ⧺ d) —↠ᶜ (c ⨟ d)
⨟-↠ c d = normalize-↠ (c ⧺ d)

⨟-NF : ∀ c d → NF (c ⨟ d)
⨟-NF c d = normalize-NF (c ⧺ d)

------------------------------------------------------------------------
-- The conversion-directed builders
------------------------------------------------------------------------

mutual
  instReveal : ℕ → Anchor → Ty → Conv → Conv
  instReveal X α S (id A) = revTy X α S A
  instReveal X α S (h ∷ᶜ c) =
    normalize (instRevealHead X α S h ∷ᶜ instReveal X α S c)

  instConceal : ℕ → Anchor → Ty → Conv → Conv
  instConceal X α S (id A) = concTy X α S A
  instConceal X α S (h ∷ᶜ c) =
    normalize (instConcealHead X α S h ∷ᶜ instConceal X α S c)

  instRevealHead : ℕ → Anchor → Ty → Head → Head
  instRevealHead X α S (seal β)   = seal β
  instRevealHead X α S (unseal β) = unseal β
  instRevealHead X α S (c ↦ d) =
    instConceal X α S c ↦ instReveal X α S d
  instRevealHead X α S (all c) =
    all (instReveal (suc X) (suc α) (renameᵗ suc S) c)

  instConcealHead : ℕ → Anchor → Ty → Head → Head
  instConcealHead X α S (seal β)   = seal β
  instConcealHead X α S (unseal β) = unseal β
  instConcealHead X α S (c ↦ d) =
    instReveal X α S c ↦ instConceal X α S d
  instConcealHead X α S (all c) =
    all (instConceal (suc X) (suc α) (renameᵗ suc S) c)

------------------------------------------------------------------------
-- The regression checks from the fuel era, now against `normalize`
------------------------------------------------------------------------

private
  nested-cancel :
    normalize (unseal 0 ∷ᶜ unseal 1 ∷ᶜ seal 1 ∷ᶜ seal 0 ∷ᶜ id `ℕ)
      ≡ id `ℕ
  nested-cancel = refl

  arrow-fuse :
    ((id `ℕ ↦ id `ℕ) ∷ᶜ id (`ℕ ⇒ `ℕ)) ⨟ ((id `ℕ ↦ id `ℕ) ∷ᶜ id (`ℕ ⇒ `ℕ))
      ≡ (id `ℕ ↦ id `ℕ) ∷ᶜ id (`ℕ ⇒ `ℕ)
  arrow-fuse = refl

  composition-assoc :
    (((unseal 0 ∷ᶜ unseal 1 ∷ᶜ id `ℕ)
       ⨟ (seal 1 ∷ᶜ id `ℕ))
       ⨟ (seal 0 ∷ᶜ id `ℕ))
      ≡ ((unseal 0 ∷ᶜ unseal 1 ∷ᶜ id `ℕ)
         ⨟ ((seal 1 ∷ᶜ id `ℕ) ⨟ (seal 0 ∷ᶜ id `ℕ)))
  composition-assoc = refl

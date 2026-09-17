module strong.ConversionReduction where

-- Strong System F v8 — conversion composition as NORMALIZATION.
--
-- Modelled on GTLC/agda/proof/CoercionReduction.agda.  Composition does
-- not compute its normal form in one fuel-driven pass; instead there is a
-- small-step reduction on conversions — one `fuse` of an adjacent pair of
-- elements, or a congruence step into a `↦` or `all` component — together
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
open import strong.RepresentationTypes using (Addr; lvl; bse; RepTy; _≟ᵃ_)
open import strong.Ctx using
  (Store; Ctxᵗ; _∥_; StackEnt; bind; asgn; repOf; readOf)
open Ctxᵗ
open import strong.Conversion

private
  variable
    c c′ d d′ s s′ t t′ e : Conv
    ĉ ḓ : ConvElt
    ks : List ConvElt
    α β : Addr
    A : Ty

------------------------------------------------------------------------
-- One step
------------------------------------------------------------------------

consAll : List ConvElt → Conv → Conv
consAll []       c = c
consAll (ĉ ∷ ĉs) c = ĉ ∷ᶜ consAll ĉs c

infix 4 _—→ᶜ_
data _—→ᶜ_ : Conv → Conv → Set where
  ξ-pair : fuse ĉ ḓ ≡ just ks
    → (ĉ ∷ᶜ ḓ ∷ᶜ c) —→ᶜ consAll ks c
  ξ-∷ : c —→ᶜ c′ → (ĉ ∷ᶜ c) —→ᶜ (ĉ ∷ᶜ c′)
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

-- Appending discards one terminator.
weight-⧺ : ∀ c d → suc (weight (c ⧺ d)) ≡ weight c + weight d
weight-⧺ (id A)    d = refl
weight-⧺ (ĉ ∷ᶜ c) d =
  trans (cong suc (sym (+-suc (weightElt ĉ) (weight (c ⧺ d)))))
        (trans (cong suc (cong (weightElt ĉ +_) (weight-⧺ c d)))
               (cong suc (sym (+-assoc (weightElt ĉ) (weight c) (weight d)))))

weightElts⁺ : List ConvElt → ℕ
weightElts⁺ []       = zero
weightElts⁺ (ĉ ∷ ĉs) = suc (weightElt ĉ + weightElts⁺ ĉs)

weight-consAll : ∀ ks c
  → weight (consAll ks c) ≡ weightElts⁺ ks + weight c
weight-consAll [] c = refl
weight-consAll (ĉ ∷ ĉs) c
  rewrite weight-consAll ĉs c =
  cong suc (sym (+-assoc (weightElt ĉ) (weightElts⁺ ĉs) (weight c)))

less-by : ∀ m k n → suc m + k ≡ n → m < n
less-by m k n eq = subst (suc m ≤_) eq (m≤m+n (suc m) k)

-- Reading `fuse` back out of a success at the four atomic cancellation
-- pairs, where its definition decides address equality.

fuse-hs-inv : ∀ X Y α β ks → fuse (hide X α) (show Y β) ≡ just ks → ks ≡ []
fuse-hs-inv X Y α β ks eq with X ≟ Y | eq
fuse-hs-inv X Y α β ks eq | yes _ | refl = refl
fuse-hs-inv X Y α β ks eq | no _ | ()

fuse-sh-inv : ∀ X Y α β ks → fuse (show X α) (hide Y β) ≡ just ks → ks ≡ []
fuse-sh-inv X Y α β ks eq with X ≟ Y | α ≟ᵃ β | eq
fuse-sh-inv X Y α β ks eq | yes _ | yes _ | refl = refl
fuse-sh-inv X Y α β ks eq | yes _ | no _ | ()
fuse-sh-inv X Y α β ks eq | no _ | _ | ()

fuse-su-inv : ∀ X Y α β ks → fuse (seal X α) (unseal Y β) ≡ just ks → ks ≡ []
fuse-su-inv X Y α β ks eq with X ≟ Y | eq
fuse-su-inv X Y α β ks eq | yes _ | refl = refl
fuse-su-inv X Y α β ks eq | no _ | ()

fuse-us-inv : ∀ X Y α β ks → fuse (unseal X α) (seal Y β) ≡ just ks → ks ≡ []
fuse-us-inv X Y α β ks ()

-- The exact bookkeeping of a `↦` fusion: one element constructor and two
-- terminators disappear, everything else is kept — a decrease of exactly
-- four in `weight`, of which one is the deleted cons.

↦-arith : ∀ a b w x y z → suc a ≡ y + w → suc b ≡ x + z
  → suc (suc (suc (a + b) + 0)) + 3
  ≡ suc (suc (w + x) + suc (suc (y + z)))
↦-arith a b w x y z eq1 eq2 =
  trans L≡sum (trans (cong (_+ 4) eq) (sym R≡sum))
  where
    open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ˢ_)
    L≡sum : suc (suc (suc (a + b) + 0)) + 3 ≡ (suc a + suc b) + 4
    L≡sum = solve 2 (λ a b → (con 1 :+ (con 1 :+ ((con 1 :+ (a :+ b)) :+ con 0))) :+ con 3
                        :=ˢ ((con 1 :+ a) :+ (con 1 :+ b)) :+ con 4)
              refl a b
    R≡sum : suc (suc (w + x) + suc (suc (y + z))) ≡ (w + x) + (y + z) + 4
    R≡sum = solve 4 (λ w x y z → con 1 :+ ((con 1 :+ (w :+ x)) :+ (con 1 :+ (con 1 :+ (y :+ z))))
                        :=ˢ ((w :+ x) :+ (y :+ z)) :+ con 4)
              refl w x y z
    eq : suc a + suc b ≡ (w + x) + (y + z)
    eq = trans (cong₂ _+_ eq1 eq2)
          (solve 4 (λ y w x z → (y :+ w) :+ (x :+ z) :=ˢ (w :+ x) :+ (y :+ z)) refl y w x z)

all-arith : ∀ a s t → suc a ≡ s + t
  → suc (suc (suc a + 0)) + 2 ≡ suc (suc s + suc (suc t))
all-arith a s t hyp =
  trans (solve 1 (λ x → (con 1 :+ (con 1 :+ ((con 1 :+ x) :+ con 0))) :+ con 2
                    :=ˢ con 1 :+ (con 1 :+ (con 1 :+ (con 1 :+ (con 1 :+ x)))))
          refl a)
    (trans (cong (λ x → suc (suc (suc (suc x)))) hyp)
      (sym (solve 2 (λ y z → con 1 :+ ((con 1 :+ y) :+ (con 1 :+ (con 1 :+ z)))
                         :=ˢ con 1 :+ (con 1 :+ (con 1 :+ (con 1 :+ (y :+ z)))))
            refl s t)))
  where open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ˢ_)

fuse-decreases : ∀ ĉ ḓ ks → fuse ĉ ḓ ≡ just ks
  → weightElts⁺ ks < suc (weightElt ĉ + suc (weightElt ḓ))
fuse-decreases (seal X α) (seal Y β) ks ()
fuse-decreases (seal X α) (unseal Y β) ks eq with X ≟ Y | eq
fuse-decreases (seal X α) (unseal Y β) ks eq | yes _ | refl =
  less-by zero 3 4 refl
fuse-decreases (seal X α) (unseal Y β) ks eq | no _ | ()
fuse-decreases (seal X α) (hide Y β) ks ()
fuse-decreases (seal X α) (show Y β) ks ()
fuse-decreases (unseal X α) (seal Y β) ks ()
fuse-decreases (unseal X α) (unseal Y β) ks ()
fuse-decreases (unseal X α) (hide Y β) ks ()
fuse-decreases (unseal X α) (show Y β) ks ()
fuse-decreases (hide X α) (seal Y β) ks ()
fuse-decreases (hide X α) (unseal Y β) ks ()
fuse-decreases (hide X α) (hide Y β) ks ()
fuse-decreases (hide X α) (show Y β) ks eq with X ≟ Y | eq
fuse-decreases (hide X α) (show Y β) ks eq | yes _ | refl =
  less-by zero 3 4 refl
fuse-decreases (hide X α) (show Y β) ks eq | no _ | ()
fuse-decreases (show X α) (seal Y β) ks ()
fuse-decreases (show X α) (unseal Y β) ks ()
fuse-decreases (show X α) (hide Y β) ks eq with X ≟ Y | α ≟ᵃ β | eq
fuse-decreases (show X α) (hide Y β) ks eq | yes _ | yes _ | refl =
  less-by zero 3 4 refl
fuse-decreases (show X α) (hide Y β) ks eq | yes _ | no _ | ()
fuse-decreases (show X α) (hide Y β) ks eq | no _ | _ | ()
fuse-decreases (show X α) (show Y β) ks ()
fuse-decreases (s₁ ↦ t₁) (s₂ ↦ t₂) ks refl =
  less-by (weightElts⁺ (((s₂ ⧺ s₁) ↦ (t₁ ⧺ t₂)) ∷ [])) 3
    (suc (weightElt (s₁ ↦ t₁) + suc (weightElt (s₂ ↦ t₂))))
    (↦-arith (weight (s₂ ⧺ s₁)) (weight (t₁ ⧺ t₂))
      (weight s₁) (weight t₁) (weight s₂) (weight t₂)
      (weight-⧺ s₂ s₁) (weight-⧺ t₁ t₂))
fuse-decreases (all s) (all t) ks refl =
  less-by (weightElts⁺ (all (s ⧺ t) ∷ [])) 2
    (suc (weightElt (all s) + suc (weightElt (all t))))
    (all-arith (weight (s ⧺ t)) (weight s) (weight t) (weight-⧺ s t))
fuse-decreases (seal X α) (s ↦ t) ks ()
fuse-decreases (seal X α) (all s) ks ()
fuse-decreases (s ↦ t) (seal Y β) ks ()
fuse-decreases (all s) (seal Y β) ks ()
fuse-decreases (unseal X α) (s ↦ t) ks ()
fuse-decreases (unseal X α) (all s) ks ()
fuse-decreases (s ↦ t) (unseal Y β) ks ()
fuse-decreases (all s) (unseal Y β) ks ()
fuse-decreases (hide X α) (s ↦ t) ks ()
fuse-decreases (hide X α) (all s) ks ()
fuse-decreases (s ↦ t) (hide Y β) ks ()
fuse-decreases (all s) (hide Y β) ks ()
fuse-decreases (show X α) (s ↦ t) ks ()
fuse-decreases (show X α) (all s) ks ()
fuse-decreases (s ↦ t) (show Y β) ks ()
fuse-decreases (all s) (show Y β) ks ()
fuse-decreases (s ↦ t) (all u) ks ()
fuse-decreases (all s) (t ↦ u) ks ()

step-decreases : c —→ᶜ c′ → weight c′ < weight c
step-decreases (ξ-pair {ĉ = ĉ} {ḓ = ḓ} {ks = ks} {c = c} eq)
  rewrite weight-consAll ks c =
  subst (weightElts⁺ ks + weight c <_)
    (solve 3 (λ p q r → (con 1 :+ (p :+ (con 1 :+ q))) :+ r
          :=ˢ con 1 :+ (p :+ (con 1 :+ (q :+ r))))
      refl (weightElt ĉ) (weightElt ḓ) (weight c))
    (+-monoˡ-< (weight c) (fuse-decreases ĉ ḓ ks eq))
  where open +-*-Solver using (solve; _:+_; con) renaming (_:=_ to _:=ˢ_)
step-decreases (ξ-∷ {ĉ = ĉ} st) =
  s≤s (+-monoʳ-< (weightElt ĉ) (step-decreases st))
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

-- Once the element and the tail are normal, only the seam can fire.
check-seam : ∀ ĉ c → NFElt ĉ → NF c → NF (ĉ ∷ᶜ c) ⊎ Steps (ĉ ∷ᶜ c)
check-seam ĉ (id A) nfe nfc = inj₁ (nf-cons nfe nf-id irr-id)
check-seam ĉ (ḓ ∷ᶜ c) nfe nfc with fuse ĉ ḓ in eq
check-seam ĉ (ḓ ∷ᶜ c) nfe nfc | just ks = inj₂ (_ , ξ-pair eq)
check-seam ĉ (ḓ ∷ᶜ c) nfe nfc | nothing =
  inj₁ (nf-cons nfe nfc (irr-cons eq))

progress : (c : Conv) → NF c ⊎ Steps c
progress (id A) = inj₁ nf-id
progress (seal X α ∷ᶜ c) with progress c
progress (seal X α ∷ᶜ c) | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (seal X α ∷ᶜ c) | inj₁ nfc = check-seam (seal X α) c nf-seal nfc
progress (unseal X α ∷ᶜ c) with progress c
progress (unseal X α ∷ᶜ c) | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (unseal X α ∷ᶜ c) | inj₁ nfc = check-seam (unseal X α) c nf-unseal nfc
progress (hide X α ∷ᶜ c) with progress c
progress (hide X α ∷ᶜ c) | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (hide X α ∷ᶜ c) | inj₁ nfc = check-seam (hide X α) c nf-hide nfc
progress (show X α ∷ᶜ c) with progress c
progress (show X α ∷ᶜ c) | inj₂ (c′ , st) = inj₂ (_ , ξ-∷ st)
progress (show X α ∷ᶜ c) | inj₁ nfc = check-seam (show X α) c nf-show nfc
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
-- Instantiating a conversion: +X(c) and -X(c)
------------------------------------------------------------------------
-- Specified by composition with the type-level builders,
--
--   +X(c) ≡ +X(src c) ⨟ c[X:=S]        -X(c) ≡ c[X:=S] ⨟ -X(tgt c)
--
-- placing the single crossing at the stack-correct end of each path.
--
-- `srcᶜ` is TOTAL, and it is total because it CONSULTS THE CONTEXT.  A
-- seal's source is not in the syntax, but it is not missing either:
--
--   conv-seal : Σ ∣ Γₑ ∋r α := R → Σ ∣ Γᵢ ⊢ R ⇓ A → Γₑ ▷ X := α ⇒ Γᵢ
--             → Σ ∣ Γᵢ ⊢̂ seal X α ∶ A ⇝ ` X ⊣ Γₑ
--
-- reads it off α's representation at the element's own INTERIOR.  So
-- `srcᶜ` is given the store and the conversion's interior context, and
-- `repOf`/`readOf` (strong.Ctx) do exactly what `∋r` and `⇓` do.  The
-- other elements move that context as the typing rules do: a `hide`'s
-- tail sits at `pushAsgn`, a `show`'s at `popAsgn`, an `all`'s
-- component under one more `bind`, and an `↦`'s covariant component at
-- the element's own interior.
--
-- The equations that answer `` `ℕ `` are the ones no typed conversion
-- reaches — a lookup that fails, a pop or push that does not fit.
-- `proof.SrcTyping.srcᶜ-sound` is the statement that they are
-- unreachable: on a typed conversion `srcᶜ` answers WITH THE SOURCE.
-- That is why `instReveal` has one equation and no `nothing` branch.

orℕ : Maybe Ty → Ty
orℕ (just A) = A
orℕ nothing  = `ℕ

srcSeal : Ctxᵗ → Maybe RepTy → Ty
srcSeal Γ (just R) = orℕ (readOf Γ R)
srcSeal Γ nothing  = `ℕ

mutual
  srcᶜ : Store → Ctxᵗ → Conv → Ty
  srcᶜ Sg Γ (id A) = A
  -- a seal's source is the read-back of α's representation, HERE
  srcᶜ Sg Γ (seal X α ∷ᶜ c) = srcSeal Γ (repOf Sg Γ α)
  -- an unseal's source IS its name
  srcᶜ Sg Γ (unseal X α ∷ᶜ c) = ` X
  -- a `hide` unshifts its tail's source (X cannot occur in it), and
  -- the tail runs from the context the hide's crossing creates
  srcᶜ Sg Γ (hide X α ∷ᶜ c) =
    closeAt X `ℕ (srcAt Sg (pushAsgn X α Γ) c)
  -- a `show` shifts its tail's source by the crossing it performs
  srcᶜ Sg Γ (show X α ∷ᶜ c) =
    renameᵗ (shiftAtᵗ X) (srcAt Sg (popAsgn X α Γ) c)
  -- the contravariant component's TARGET is the domain
  srcᶜ Sg Γ ((s ↦ t) ∷ᶜ c) = target s ⇒ srcᶜ Sg Γ t
  srcᶜ Sg Γ (all s ∷ᶜ c) = `∀ (srcᶜ Sg (bind ∷ stk Γ ∥ bas Γ) s)

  srcAt : Store → Maybe Ctxᵗ → Conv → Ty
  srcAt Sg (just Γ) c = srcᶜ Sg Γ c
  srcAt Sg nothing  c = `ℕ

instReveal : Store → Ctxᵗ → ℕ → Addr → Ty → Conv → Conv
instReveal Sg Γ X α S c = revTy X α S (srcᶜ Sg Γ c) ⨟ substAnn X S c

instConceal : ℕ → Addr → Ty → Conv → Conv
instConceal X α S c = substAnn X S c ⨟ concTy X α S (target c)

------------------------------------------------------------------------
-- Regression checks, against `normalize`
------------------------------------------------------------------------

private
  nested-cancel :
    normalize (unseal 0 (lvl 0) ∷ᶜ unseal 0 (lvl 1)
                ∷ᶜ seal 0 (lvl 1) ∷ᶜ seal 0 (lvl 0) ∷ᶜ id `ℕ)
      ≡ (unseal 0 (lvl 0) ∷ᶜ unseal 0 (lvl 1)
                ∷ᶜ seal 0 (lvl 1) ∷ᶜ seal 0 (lvl 0) ∷ᶜ id `ℕ)
  nested-cancel = refl

  -- The K example's merged word: nested crossings cancel adjacently.
  k-example :
    normalize (seal 0 (lvl 0) ∷ᶜ hide 0 (lvl 1)
                ∷ᶜ show 0 (lvl 1) ∷ᶜ unseal 0 (lvl 0) ∷ᶜ id `ℕ)
      ≡ id `ℕ
  k-example = refl

  -- The OVERLAPPING word is a normal form: normalization leaves it
  -- alone, and the stack element rules leave it with no typing
  -- derivation — typing, not normalization, excludes it.
  overlap-stuck :
    normalize (seal 0 (lvl 0) ∷ᶜ hide 0 (lvl 1)
                ∷ᶜ unseal 0 (lvl 0) ∷ᶜ show 0 (lvl 1) ∷ᶜ id `ℕ)
      ≡ (seal 0 (lvl 0) ∷ᶜ hide 0 (lvl 1)
                ∷ᶜ unseal 0 (lvl 0) ∷ᶜ show 0 (lvl 1) ∷ᶜ id `ℕ)
  overlap-stuck = refl

  arrow-fuse :
    ((id `ℕ ↦ id `ℕ) ∷ᶜ id (`ℕ ⇒ `ℕ)) ⨟ ((id `ℕ ↦ id `ℕ) ∷ᶜ id (`ℕ ⇒ `ℕ))
      ≡ (id `ℕ ↦ id `ℕ) ∷ᶜ id (`ℕ ⇒ `ℕ)
  arrow-fuse = refl

  composition-assoc :
    (((unseal 0 (lvl 0) ∷ᶜ unseal 0 (lvl 1) ∷ᶜ id `ℕ)
       ⨟ (seal 0 (lvl 1) ∷ᶜ id `ℕ))
       ⨟ (seal 0 (lvl 0) ∷ᶜ id `ℕ))
      ≡ ((unseal 0 (lvl 0) ∷ᶜ unseal 0 (lvl 1) ∷ᶜ id `ℕ)
         ⨟ ((seal 0 (lvl 1) ∷ᶜ id `ℕ) ⨟ (seal 0 (lvl 0) ∷ᶜ id `ℕ)))
  composition-assoc = refl

------------------------------------------------------------------------
-- The views
------------------------------------------------------------------------
-- Assembled from the elementwise folds of `strong.Conversion`.  A
-- component is an APPEND of the pieces the fold collects, and an append
-- can leave a redex at its seam, so each component is NORMALIZED — the
-- same discipline the builders follow, restoring cancellation
-- immediately.  The scrutinees are passed to a plain function so that a
-- proof which knows them can rewrite.

arrFrom : Ty → Maybe (List ConvElt × List ConvElt) → Ty
  → Maybe (Conv × Conv)
arrFrom A₀ (just (Ls , Rs)) (C ⇒ D) =
  just (normalize (attach Ls A₀) , normalize (attach Rs D))
arrFrom A₀ (just p) (` X) = nothing
arrFrom A₀ (just p) `ℕ = nothing
arrFrom A₀ (just p) `𝔹 = nothing
arrFrom A₀ (just p) (`∀ B) = nothing
arrFrom A₀ nothing T = nothing

-- `arr` takes the INTERIOR domain A₀ from the λ annotation at its use
-- site: the contravariant component terminates there, in its own
-- coordinates, so no renaming is involved.
arr : Ty → Conv → Maybe (Conv × Conv)
arr A₀ c = arrFrom A₀ (arrElts (elts c)) (target c)

allFrom : Maybe (List ConvElt) → Ty → Maybe Conv
allFrom (just Es) (`∀ B) = just (normalize (attach Es B))
allFrom (just Es) (` X) = nothing
allFrom (just Es) `ℕ = nothing
allFrom (just Es) `𝔹 = nothing
allFrom (just Es) (C ⇒ D) = nothing
allFrom nothing T = nothing

allView : Conv → Maybe Conv
allView c = allFrom (allElts (elts c)) (target c)

-- `base` is the view `Const` uses: a literal ignores identity
-- crossings.  It reads the syntax directly — there is nothing to
-- compose.
base : Conv → Maybe Ty
base (id `ℕ) = just `ℕ
base (id `𝔹) = just `𝔹
base (id (` X)) = nothing
base (id (A ⇒ B)) = nothing
base (id (`∀ A)) = nothing
base (hide X α ∷ᶜ c) = base c
base (show X α ∷ᶜ c) = base c
base (seal X α ∷ᶜ c) = nothing
base (unseal X α ∷ᶜ c) = nothing
base ((s ↦ t) ∷ᶜ c) = nothing
base (all s ∷ᶜ c) = nothing

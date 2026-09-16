module strong.notes.SrcGap where

-- Strong System F v8 — A SOURCE PROGRAM THAT REACHES `instReveal`'s
-- `nothing` BRANCH (2026-09-16).
--
-- `srcᶜ` gives out on a SEAL-headed conversion, and `tyWrapOk′` still
-- carries `¬ (srcᶜ d ≡ nothing)` because that branch is ill-typed.  The
-- question was whether the branch is reachable.  It is:
--
--     h = ΛX. λk:(∀Z. X). k [ℕ]     : ∀X. (∀Z. X) → X
--     a = ΛZ. true                  : ∀Z. 𝔹
--     -----------------------------------------------
--     (h [𝔹]) a
--
-- The point is the POLYMORPHIC DOMAIN.  Instantiating `h` builds
-- `revTy` at `(∀Z. X) → X`, whose CONTRAVARIANT component is `concTy`
-- at `∀Z. X` — and `concTy` at a hit emits a `seal`.  `Wrap` then hands
-- that component to the argument, so `a` ends up behind an `all`-headed
-- conversion whose body is seal-headed; `k [ℕ]` instantiates it, and
-- `allView` hands `TyWrap` a spine on which `srcᶜ` is undefined.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Bool using (true)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

TZ : Ty                         -- ∀Z. X, with X the enclosing Λ's
TZ = `∀ (` 1)

Bh : Ty                         -- (∀Z. X) → X
Bh = TZ ⇒ ` 0

h a : Term
h = Λ (ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ]))
a = Λ (# true)

prog : Term
prog = (h • Bh [ `𝔹 ]) · a

-- step 1: instantiate `h`
s₁ : [] ∣ ([] ∥ []) ⊢ prog
   —→ (ν `𝔹ᴿ ∙ ((ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ]))
         ⟨ revTy zero (bse zero) `𝔹 Bh ⟩)) · a ⊣ []
s₁ = ξ-·-l (TyBeta (Vs Sƛ) quote-𝔹)

-- step 2: discharge
c : Conv                        -- what TyBeta built, after Alloc
c = revTy zero (lvl 0) `𝔹 Bh

s₂ : [] ∣ ([] ∥ [])
   ⊢ ν `𝔹ᴿ ∙ ((ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) ⟨ revTy zero (bse zero) `𝔹 Bh ⟩)
   —→ (ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) ⟨ c ⟩ ⊣ (`𝔹ᴿ ∷ [])
s₂ = Alloc

-- its contravariant component is `concTy` at the POLYMORPHIC DOMAIN,
-- and `concTy` at a hit emits a `seal`
c₁ : Conv
c₁ = all (seal 1 (lvl 0) ∷ᶜ id (` 1)) ∷ᶜ id TZ

split : arr TZ c ≡ just (c₁ , unseal 0 (lvl 0) ∷ᶜ id `𝔹)
split = refl

-- step 3: `Wrap` hands that component to the ARGUMENT
va : Value a
va = Vs (SΛ (Vs S#))

vc : Value ((ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) ⟨ c ⟩)
vc = V⟨⟩ Sƛ nfc (inert-arr TZ refl)
  where
  nfc : NF c
  nfc = nf-cons
          (nf-fun (nf-cons (nf-all (nf-cons nf-seal nf-id irr-id))
                    nf-id irr-id)
                  (nf-cons nf-unseal nf-id irr-id))
          nf-id irr-id

s₃ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ [])
   ⊢ ((ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) ⟨ c ⟩) · a
   —→ ((ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) · (a ⟨ c₁ ⟩))
        ⟨ unseal 0 (lvl 0) ∷ᶜ id `𝔹 ⟩ ⊣ (`𝔹ᴿ ∷ [])
s₃ = Wrap vc va refl

-- and the wrapped argument IS a value: `all`-headed, so `allView`
-- succeeds and the conversion is inert
vwrap : Value (a ⟨ c₁ ⟩)
vwrap = V⟨⟩ (SΛ (Vs S#))
          (nf-cons (nf-all (nf-cons nf-seal nf-id irr-id)) nf-id irr-id)
          (inert-all refl)

-- step 4: β puts it in the type-application position
s₄ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ [])
   ⊢ (ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) · (a ⟨ c₁ ⟩)
   —→ (a ⟨ c₁ ⟩) • (` 1) [ `ℕ ] ⊣ (`𝔹ᴿ ∷ [])
s₄ = Beta vwrap

------------------------------------------------------------------------
-- THE GAP
------------------------------------------------------------------------
-- `(a ⟨ c₁ ⟩) • (` 1) [ ℕ ]` is a `TyWrap` redex, and the spine
-- `allView` hands it is SEAL-headed — so `srcᶜ` is undefined on it and
-- `instReveal` takes its `nothing` branch.

d : Conv
d = seal 1 (lvl 0) ∷ᶜ id (` 1)

view : allView c₁ ≡ just d
view = refl

gap : srcᶜ d ≡ nothing
gap = refl

redex : (`𝔹ᴿ ∷ []) ∣ ([] ∥ [])
      ⊢ (a ⟨ c₁ ⟩) • (` 1) [ `ℕ ]
      —→ ν `ℕᴿ ∙ ((# true) ⟨ instReveal zero (bse zero) `ℕ d ⟩)
      ⊣ (`𝔹ᴿ ∷ [])
redex = TyWrap vwrap refl quote-ℕ

-- and what that branch builds is a BARE crossing on top of `d` —
-- `show` crosses ONE assignment, while `d` is still typed under the
-- `∀`'s binder, which only `substAnn` removes.  Hence the premise.
built : instReveal zero (bse zero) `ℕ d
      ≡ show 0 (bse 0) ∷ᶜ seal 1 (lvl 0) ∷ᶜ id (` 1)
built = refl

-- The `just` branch is `revTy … ⨟ substAnn …`; by analogy the repair
-- is to substitute here too, `show X α ∷ᶜ substAnn X S c`, which at
-- this word gives
repair : show 0 (bse 0) ∷ᶜ substAnn zero `ℕ d
       ≡ show 0 (bse 0) ∷ᶜ seal 0 (lvl 0) ∷ᶜ id (` 0)
repair = refl

-- which is the coherent word: the slot is dropped, so the seal's name
-- slides 1 ↦ 0, and its target — the crossing's OWN name — slides with
-- it.  The branch as it stands leaves both at 1, naming a binder that
-- is no longer there.

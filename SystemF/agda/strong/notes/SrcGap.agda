module strong.notes.SrcGap where

-- Strong System F v8 — THE SOURCE PROGRAM THAT USED TO REACH
-- `instReveal`'s `nothing` BRANCH (2026-09-16), AND WHAT IT DOES NOW
-- THAT `srcᶜ` CONSULTS THE CONTEXT (2026-09-17).
--
-- `srcᶜ` used to give out on a SEAL-headed conversion, and `tyWrapOk′`
-- carried `¬ (srcᶜ d ≡ nothing)` because that branch was ill-typed.
-- The question was whether the branch is reachable.  It is:
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
-- `allView` hands `TyWrap` a spine that is seal-headed.
--
-- THE BRANCH IS GONE.  A seal's source is not in the syntax, but it is
-- in the CONTEXT: `conv-seal` reads α's representation back at the
-- element's own interior, and `srcᶜ` now does the same (`repOf` and
-- `readOf`, strong.Ctx).  On this very word the answer is `` `𝔹 `` —
-- the store entry `lvl 0` holds — and `instReveal` takes its ONE
-- branch.  It produces the SAME word the repaired `nothing` branch
-- produced (`built` below), which is the check that the repair was
-- right here: for a seal-headed spine `revTy` at the read-back source
-- IS the miss equation.  What it is not, in general, is the same as a
-- bare `show`: see `proof.PreserveTyWrap` §8.3, whose `↦`-shaped redex
-- used to refute `TyWrapOk` and now goes through.

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

-- Both remaining steps happen INSIDE the `unseal` boundary `Wrap` left
-- behind, so their context is that conversion's interior — which is
-- exactly where the assignment `0 := lvl 0` lives.  (Without it the
-- `seal 1 (lvl 0)` below has no assignment to pop and `interior c₁`
-- fails: the trace used to state these steps at the empty context, and
-- that was an accident of the reduction relation not looking.)
Δ₁ : Ctxᵗ
Δ₁ = asgn (lvl 0) ∷ [] ∥ []

frame : interior (unseal 0 (lvl 0) ∷ᶜ id `𝔹) ([] ∥ []) ≡ just Δ₁
frame = refl

-- step 4: β puts it in the type-application position
s₄ : (`𝔹ᴿ ∷ []) ∣ Δ₁
   ⊢ (ƛ TZ ∙ (` 0 • (` 1) [ `ℕ ])) · (a ⟨ c₁ ⟩)
   —→ (a ⟨ c₁ ⟩) • (` 1) [ `ℕ ] ⊣ (`𝔹ᴿ ∷ [])
s₄ = Beta vwrap

------------------------------------------------------------------------
-- THE GAP, AND HOW THE CONTEXT CLOSES IT
------------------------------------------------------------------------
-- `(a ⟨ c₁ ⟩) • (` 1) [ ℕ ]` is a `TyWrap` redex, and the spine
-- `allView` hands it is SEAL-headed — which is where `srcᶜ` used to
-- give out.

d : Conv
d = seal 1 (lvl 0) ∷ᶜ id (` 1)

view : allView c₁ ≡ just d
view = refl

-- `c₁`'s `all` element pops the assignment its seal crosses, so the
-- conversion's interior is the EMPTY context and `d` is typed one
-- `bind` further in — `Γᵢ` is the context `TyWrap` passes on.
int : interior c₁ Δ₁ ≡ just ([] ∥ [])
int = refl

Γᵢ : Ctxᵗ
Γᵢ = bind ∷ [] ∥ []

-- WHERE THE SOURCE WAS ALL ALONG.  `lvl 0` is the store's entry `𝔹ᴿ,
-- and reading it back at `Γᵢ` gives `` `𝔹 `` — the two steps
-- `conv-seal`'s `∋r` and `⇓` premises take.
rep : repOf (`𝔹ᴿ ∷ []) Γᵢ (lvl 0) ≡ just `𝔹ᴿ
rep = refl

read : readOf Γᵢ `𝔹ᴿ ≡ just `𝔹
read = refl

src : srcᶜ (`𝔹ᴿ ∷ []) Γᵢ d ≡ `𝔹
src = refl

redex : (`𝔹ᴿ ∷ []) ∣ Δ₁
      ⊢ (a ⟨ c₁ ⟩) • (` 1) [ `ℕ ]
      —→ ν `ℕᴿ ∙ ((# true)
            ⟨ instReveal (`𝔹ᴿ ∷ []) Γᵢ zero (bse zero) `ℕ d ⟩)
      ⊣ (`𝔹ᴿ ∷ [])
redex = TyWrap vwrap view quote-ℕ int

-- WHAT THE ORIGINAL BRANCH BUILT was a BARE crossing on top of `d` —
-- `show` crosses ONE assignment, while `d` is still typed under the
-- `∀`'s binder, which only `substAnn` removes — so its names pointed
-- at a binder the `ν` had replaced:
--
--     show 0 (bse 0) ∷ᶜ seal 1 (lvl 0) ∷ᶜ id (` 1)
--
-- What `instReveal` builds now is `revTy 0 (bse 0) ℕ 𝔹` — the source
-- `srcᶜ` read out of the store — composed with `d[0 := ℕ]`.  `𝔹` is a
-- MISS, so `revTy` emits the identity crossing, and the composition
-- drops the slot: the seal's name slides 1 ↦ 0 and its target — the
-- crossing's OWN name — slides with it.
built : instReveal (`𝔹ᴿ ∷ []) Γᵢ zero (bse zero) `ℕ d
      ≡ show 0 (bse 0) ∷ᶜ seal 0 (lvl 0) ∷ᶜ id (` 0)
built = refl

-- This is the same word the 2026-09-16 repair of the `nothing` branch
-- produced, and that coincidence is the CONTENT of the repair being
-- right HERE: `d` is seal-HEADED, a seal's source is the read-back of
-- a representation `∋r` reaches, which over an empty base is a store
-- entry, hence CLOSED — so `revTy` at it takes the miss equation, and
-- the miss equation is `show X α`.  The coincidence fails as soon as
-- the source is not closed: `proof.PreserveTyWrap` §8.3's `↦`-shaped
-- redex has source `` ` 0 ⇒ `𝔹 ``, where `revTy` HITS and emits a
-- `seal` in the domain that no bare `show` supplies.  That redex used
-- to have no typing derivation at all; with `srcᶜ` reading the
-- context it is typed by `tyWrapOk′` (`reduct-okₖ`).

------------------------------------------------------------------------
-- WHAT THIS EXAMPLE DOES NOT TEST
------------------------------------------------------------------------
-- The repair's `substAnn` takes only trivial steps here.  In this
-- family the seal's name is always the slot PLUS ONE — both count from
-- the same place, but the seal's name is the Λ's variable, one binder
-- deeper than the ∀ being instantiated — so no crossing ever sits at a
-- name ≤ the slot and the threading never fires.

noMove : slotOut d 0 ≡ 0
noMove = refl

-- Nor does taking a deeper domain, `∀Z.∀W. X`, help: the seal descends
-- to name 2 but so does the slot's index under the `all`, keeping the
-- gap of one.
d′ : Conv
d′ = all (seal 2 (lvl 0) ∷ᶜ id (` 2)) ∷ᶜ id (`∀ (` 2))

noMove′ : slotOut d′ 0 ≡ 0
noMove′ = refl

-- The `all` stepping — `slotOutElt (all s) X = slotOut s (suc X) ∸ 1`,
-- derived by hand — fires only when a crossing INSIDE the `all` sits at
-- a name ≤ the slot there:
d″ : Conv
d″ = all (seal 1 (lvl 0) ∷ᶜ id (` 1)) ∷ᶜ id (`∀ (` 1))

doesMove : slotOut d″ 0 ≡ 1
doesMove = refl

-- WHERE I EXPECTED A NAME-0 CROSSING, AND WHY THERE IS NONE.  I
-- guessed the color wrap would supply one — `crossΛ` emits
-- `hide 0 (bse 0)`, and `TyWrap`'s slot is also 0.  It does not:
-- `all⁺` SHIFTS an ambient crossing when it lifts it past the `∀`,
--
--     all⁺ (hide 0 (bse 0)) ≡ just (hide 1 (bse 0) ∷ [])
--
-- so it lands strictly above the slot.  What DOES lower a name is
-- `substAnn` itself (`nameSub 0 1 = 0`), so the repaired branch above
-- emits `seal 0 …` — but a value sealed at the top has a type
-- VARIABLE for its target, so it cannot be type-applied again, and
-- `allView` fails on a `seal` anyway.
--
-- THE GENERAL STATEMENT IS ALREADY A THEOREM.  There is no combined
-- example to find at this level, and not because none has been
-- constructed: `proof.SubstAnnTyping.slotOut-bind` proves
--
--     Sg ∣ (bind ∷ Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (bind ∷ Ssₑ ∥ Bs)
--     → slotOut c zero ≡ zero
--
-- from the bind-rank invariant — no element touches the bind skeleton,
-- so the slot keeps its rank among the binds.  A `TyWrap`'s spine runs
-- between two bind-headed contexts, so its slot provably cannot move.
--
-- Where the threading does earn its keep is DEEPER in a spine, inside
-- `↦` and `all`, where the corresponding theorem is `slotOut-round`.
-- That is where `notes/SubstAnnTest`'s hand-written word lives, and it
-- is why that word is hand-written rather than traced.

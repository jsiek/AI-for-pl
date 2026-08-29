module alt.probes.RepExchangeRoutingOnlyReopen where

-- File Charter:
--   * Tests the conjecture that routing-only exchange is Φ-stable: if
--     `strengthenᵗ? X E ≡ just E₀`, then moving `end[X]` left across
--     the ν carrying `E` preserves `rep?` after adversarial extensions.
--   * The instances cover the exact killed-anchor reopening with closed
--     function and `★` payloads, `E` naming a different live crossing,
--     reopening the other old anchor, simultaneous and repeated reopenings,
--     a live-then-dead crossing resolving through the swapped ν, a second
--     dead-anchor hop, nested kills, exact fuel boundaries, nonzero `X`, and
--     routing beneath `∀`.
--   * Every equality is instance evidence by normalization, not a proof of
--     the conjecture.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import alt.Conversion
open import alt.ThetaTyping

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

no-live-empty : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-empty ()

------------------------------------------------------------------------
-- Exact two-anchor reopening geometry with closed payloads
------------------------------------------------------------------------

closed-base : TyEnv 1 0 Vec.[]
closed-base = ∅ ,:= ℕᵗ

closed-crossed : TyEnv 1 1 (just zero Vec.∷ Vec.[])
closed-crossed =
  closed-base ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

closed-app-strengthens :
  strengthenᵗ? zero (ℕ⇒ℕ {Δ = 1}) ≡ just (ℕ⇒ℕ {Δ = 0})
closed-app-strengthens = refl

closed-app-left : TyEnv 2 0 Vec.[]
closed-app-left = (closed-crossed ,:= ℕ⇒ℕ) ,end[ zero ]

closed-app-right : TyEnv 2 0 Vec.[]
closed-app-right = (closed-crossed ,end[ zero ]) ,:= ℕ⇒ℕ

closed-app-reopen-left : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
closed-app-reopen-left =
  closed-app-left ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩

closed-app-reopen-right : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
closed-app-reopen-right =
  closed-app-right ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩

closed-app-young :
  rep? closed-app-reopen-left zero ≡ rep? closed-app-reopen-right zero
closed-app-young = refl

closed-app-reopened :
  rep? closed-app-reopen-left (suc zero)
    ≡ rep? closed-app-reopen-right (suc zero)
closed-app-reopened = refl

closed-app-young-result : rep? closed-app-reopen-left zero ≡ just ℕ⇒ℕ
closed-app-young-result = refl

closed-star-strengthens :
  strengthenᵗ? zero (★ {Δ = 1}) ≡ just (★ {Δ = 0})
closed-star-strengthens = refl

closed-star-left : TyEnv 2 0 Vec.[]
closed-star-left = (closed-crossed ,:= ★) ,end[ zero ]

closed-star-right : TyEnv 2 0 Vec.[]
closed-star-right = (closed-crossed ,end[ zero ]) ,:= ★

closed-star-reopen-left : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
closed-star-reopen-left =
  closed-star-left ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩

closed-star-reopen-right : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
closed-star-reopen-right =
  closed-star-right ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩

closed-star-young :
  rep? closed-star-reopen-left zero ≡ rep? closed-star-reopen-right zero
closed-star-young = refl

closed-star-reopened :
  rep? closed-star-reopen-left (suc zero)
    ≡ rep? closed-star-reopen-right (suc zero)
closed-star-reopened = refl

closed-star-young-result : rep? closed-star-reopen-left zero ≡ just ★
closed-star-young-result = refl

------------------------------------------------------------------------
-- The guarded swap: E names a live crossing other than X
------------------------------------------------------------------------

-- The oldest anchor A is live at variable zero.
old-a : TyEnv 1 1 (just zero Vec.∷ Vec.[])
old-a = (∅ ,:= ℕᵗ) ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

-- The next anchor B is represented by A's crossing.
old-a-new-b : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
old-a-new-b = old-a ,:= ＇ zero

zero-fresh-among-a :
  (zero {n = 1}) ∉ᵛ (just (suc (zero {n = 0})) Vec.∷ Vec.[])
zero-fresh-among-a zero ()
zero-fresh-among-a (suc ())

-- X is B's crossing at zero; A's distinct live crossing is at `suc zero`.
both-crossed : TyEnv 2 2
  (just zero Vec.∷ just (suc zero) Vec.∷ Vec.[])
both-crossed =
  old-a-new-b ,begin[ zero ≔ zero ]⟨ zero-fresh-among-a ⟩

routing-E : Ty 2
routing-E = ＇ (suc zero)

routing-E₀ : Ty 1
routing-E₀ = ＇ zero

routing-strengthens : strengthenᵗ? zero routing-E ≡ just routing-E₀
routing-strengthens = refl

swap-left : TyEnv 3 1 (just (suc (suc zero)) Vec.∷ Vec.[])
swap-left = (both-crossed ,:= routing-E) ,end[ zero ]

swap-right : TyEnv 3 1 (just (suc (suc zero)) Vec.∷ Vec.[])
swap-right = (both-crossed ,end[ zero ]) ,:= routing-E₀

swap-young : rep? swap-left zero ≡ rep? swap-right zero
swap-young = refl

swap-ended-b : rep? swap-left (suc zero) ≡ rep? swap-right (suc zero)
swap-ended-b = refl

swap-old-a :
  rep? swap-left (suc (suc zero))
    ≡ rep? swap-right (suc (suc zero))
swap-old-a = refl

------------------------------------------------------------------------
-- Exact counterexample geometry, now under the strengthening guard
------------------------------------------------------------------------

b-fresh-among-a :
  (suc (zero {n = 1})) ∉ᵛ
    (just (suc (suc (zero {n = 0}))) Vec.∷ Vec.[])
b-fresh-among-a zero ()
b-fresh-among-a (suc ())

-- Reopen the crossing killed by the guarded swap.  This is the exact outer
-- begin that distinguished the unrestricted pair when E was `＇X`.
reopen-b-left : TyEnv 3 2
  (just (suc zero) Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
reopen-b-left =
  swap-left ,begin[ zero ≔ suc zero ]⟨ b-fresh-among-a ⟩

reopen-b-right : TyEnv 3 2
  (just (suc zero) Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
reopen-b-right =
  swap-right ,begin[ zero ≔ suc zero ]⟨ b-fresh-among-a ⟩

reopen-b-young : rep? reopen-b-left zero ≡ rep? reopen-b-right zero
reopen-b-young = refl

reopen-b-reopened :
  rep? reopen-b-left (suc zero) ≡ rep? reopen-b-right (suc zero)
reopen-b-reopened = refl

reopen-b-old :
  rep? reopen-b-left (suc (suc zero))
    ≡ rep? reopen-b-right (suc (suc zero))
reopen-b-old = refl

reopen-b-young-result : rep? reopen-b-left zero ≡ just (＇ (suc zero))
reopen-b-young-result = refl

reopen-b-reopened-result :
  rep? reopen-b-left (suc zero) ≡ just (＇ (suc zero))
reopen-b-reopened-result = refl

reopen-b-old-result : rep? reopen-b-left (suc (suc zero)) ≡ just ℕᵗ
reopen-b-old-result = refl

------------------------------------------------------------------------
-- Reopen the other old anchor
------------------------------------------------------------------------

reopen-a-left : TyEnv 3 1 (just (suc (suc zero)) Vec.∷ Vec.[])
reopen-a-left =
  (swap-left ,end[ zero ])
    ,begin[ zero ≔ suc (suc zero) ]⟨ no-live-empty ⟩

reopen-a-right : TyEnv 3 1 (just (suc (suc zero)) Vec.∷ Vec.[])
reopen-a-right =
  (swap-right ,end[ zero ])
    ,begin[ zero ≔ suc (suc zero) ]⟨ no-live-empty ⟩

reopen-a-young : rep? reopen-a-left zero ≡ rep? reopen-a-right zero
reopen-a-young = refl

reopen-a-dead-b :
  rep? reopen-a-left (suc zero) ≡ rep? reopen-a-right (suc zero)
reopen-a-dead-b = refl

reopen-a-reopened :
  rep? reopen-a-left (suc (suc zero))
    ≡ rep? reopen-a-right (suc (suc zero))
reopen-a-reopened = refl

reopen-a-young-result : rep? reopen-a-left zero ≡ just (＇ zero)
reopen-a-young-result = refl

------------------------------------------------------------------------
-- Double and repeated reopenings
------------------------------------------------------------------------

a-fresh-among-b :
  (suc (suc (zero {n = 0}))) ∉ᵛ
    (just (suc (zero {n = 1})) Vec.∷ Vec.[])
a-fresh-among-b zero ()
a-fresh-among-b (suc ())

double-left : TyEnv 3 2
  (just (suc (suc zero)) Vec.∷ just (suc zero) Vec.∷ Vec.[])
double-left =
  ((swap-left ,end[ zero ])
    ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩)
    ,begin[ zero ≔ suc (suc zero) ]⟨ a-fresh-among-b ⟩

double-right : TyEnv 3 2
  (just (suc (suc zero)) Vec.∷ just (suc zero) Vec.∷ Vec.[])
double-right =
  ((swap-right ,end[ zero ])
    ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩)
    ,begin[ zero ≔ suc (suc zero) ]⟨ a-fresh-among-b ⟩

double-young : rep? double-left zero ≡ rep? double-right zero
double-young = refl

double-b : rep? double-left (suc zero) ≡ rep? double-right (suc zero)
double-b = refl

double-a :
  rep? double-left (suc (suc zero))
    ≡ rep? double-right (suc (suc zero))
double-a = refl

repeated-left : TyEnv 3 2
  (just (suc zero) Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
repeated-left =
  (reopen-b-left ,end[ zero ])
    ,begin[ zero ≔ suc zero ]⟨ b-fresh-among-a ⟩

repeated-right : TyEnv 3 2
  (just (suc zero) Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
repeated-right =
  (reopen-b-right ,end[ zero ])
    ,begin[ zero ≔ suc zero ]⟨ b-fresh-among-a ⟩

repeated-young : rep? repeated-left zero ≡ rep? repeated-right zero
repeated-young = refl

repeated-b :
  rep? repeated-left (suc zero) ≡ rep? repeated-right (suc zero)
repeated-b = refl

repeated-a :
  rep? repeated-left (suc (suc zero))
    ≡ rep? repeated-right (suc (suc zero))
repeated-a = refl

------------------------------------------------------------------------
-- A region with a further dead crossing resolving through the swapped ν
------------------------------------------------------------------------

young-fresh-among-b-a :
  (zero {n = 2}) ∉ᵛ
    (just (suc (zero {n = 1})) Vec.∷
      just (suc (suc (zero {n = 0}))) Vec.∷ Vec.[])
young-fresh-among-b-a zero ()
young-fresh-among-b-a (suc zero) ()
young-fresh-among-b-a (suc (suc ()))

through-open-left : TyEnv 4 3
  (just (suc zero) Vec.∷ just (suc (suc zero)) Vec.∷
    just (suc (suc (suc zero))) Vec.∷ Vec.[])
through-open-left =
  (reopen-b-left
    ,begin[ zero ≔ zero ]⟨ young-fresh-among-b-a ⟩)
    ,:= ＇ zero

through-open-right : TyEnv 4 3
  (just (suc zero) Vec.∷ just (suc (suc zero)) Vec.∷
    just (suc (suc (suc zero))) Vec.∷ Vec.[])
through-open-right =
  (reopen-b-right
    ,begin[ zero ≔ zero ]⟨ young-fresh-among-b-a ⟩)
    ,:= ＇ zero

through-live-prefix :
  rep? through-open-left zero ≡ rep? through-open-right zero
through-live-prefix = refl

through-open-result : rep? through-open-left zero ≡ just (＇ zero)
through-open-result = refl

-- Killing the inner crossing makes the newest prefix anchor resolve its
-- stored crossing through the swapped ν.
through-left : TyEnv 4 2
  (just (suc (suc zero)) Vec.∷
    just (suc (suc (suc zero))) Vec.∷ Vec.[])
through-left = through-open-left ,end[ zero ]

through-right : TyEnv 4 2
  (just (suc (suc zero)) Vec.∷
    just (suc (suc (suc zero))) Vec.∷ Vec.[])
through-right = through-open-right ,end[ zero ]

through-dead-prefix : rep? through-left zero ≡ rep? through-right zero
through-dead-prefix = refl

through-swapped :
  rep? through-left (suc zero) ≡ rep? through-right (suc zero)
through-swapped = refl

through-b :
  rep? through-left (suc (suc zero))
    ≡ rep? through-right (suc (suc zero))
through-b = refl

through-a :
  rep? through-left (suc (suc (suc zero)))
    ≡ rep? through-right (suc (suc (suc zero)))
through-a = refl

through-result : rep? through-left zero ≡ just (＇ (suc zero))
through-result = refl

through-one-short : repFuel? 1 through-left zero ≡ nothing
through-one-short = refl

through-exact-fuel : repFuel? 2 through-left zero ≡ just (＇ (suc zero))
through-exact-fuel = refl

-- Nested kills leave B dead, then A dead.  The same dead crossing through the
-- swapped ν first routes to live A and then resolves A to its closed payload.
through-kill-b-left : TyEnv 4 1
  (just (suc (suc (suc zero))) Vec.∷ Vec.[])
through-kill-b-left = through-left ,end[ zero ]

through-kill-b-right : TyEnv 4 1
  (just (suc (suc (suc zero))) Vec.∷ Vec.[])
through-kill-b-right = through-right ,end[ zero ]

through-kill-b :
  rep? through-kill-b-left zero ≡ rep? through-kill-b-right zero
through-kill-b = refl

through-kill-a-left : TyEnv 4 0 Vec.[]
through-kill-a-left = through-kill-b-left ,end[ zero ]

through-kill-a-right : TyEnv 4 0 Vec.[]
through-kill-a-right = through-kill-b-right ,end[ zero ]

through-kill-a :
  rep? through-kill-a-left zero ≡ rep? through-kill-a-right zero
through-kill-a = refl

through-kill-a-result : rep? through-kill-a-left zero ≡ just ℕᵗ
through-kill-a-result = refl

------------------------------------------------------------------------
-- A second dead-anchor hop and its exact fuel boundary
------------------------------------------------------------------------

prefix-fresh-among-b-a :
  (zero {n = 3}) ∉ᵛ
    (just (suc (suc (zero {n = 1}))) Vec.∷
      just (suc (suc (suc (zero {n = 0})))) Vec.∷ Vec.[])
prefix-fresh-among-b-a zero ()
prefix-fresh-among-b-a (suc zero) ()
prefix-fresh-among-b-a (suc (suc ()))

multi-open-left : TyEnv 5 3
  (just (suc zero) Vec.∷ just (suc (suc (suc zero))) Vec.∷
    just (suc (suc (suc (suc zero)))) Vec.∷ Vec.[])
multi-open-left =
  (through-left
    ,begin[ zero ≔ zero ]⟨ prefix-fresh-among-b-a ⟩)
    ,:= ＇ zero

multi-open-right : TyEnv 5 3
  (just (suc zero) Vec.∷ just (suc (suc (suc zero))) Vec.∷
    just (suc (suc (suc (suc zero)))) Vec.∷ Vec.[])
multi-open-right =
  (through-right
    ,begin[ zero ≔ zero ]⟨ prefix-fresh-among-b-a ⟩)
    ,:= ＇ zero

multi-left : TyEnv 5 2
  (just (suc (suc (suc zero))) Vec.∷
    just (suc (suc (suc (suc zero)))) Vec.∷ Vec.[])
multi-left = multi-open-left ,end[ zero ]

multi-right : TyEnv 5 2
  (just (suc (suc (suc zero))) Vec.∷
    just (suc (suc (suc (suc zero)))) Vec.∷ Vec.[])
multi-right = multi-open-right ,end[ zero ]

multi-newest : rep? multi-left zero ≡ rep? multi-right zero
multi-newest = refl

multi-prefix :
  rep? multi-left (suc zero) ≡ rep? multi-right (suc zero)
multi-prefix = refl

multi-swapped :
  rep? multi-left (suc (suc zero))
    ≡ rep? multi-right (suc (suc zero))
multi-swapped = refl

multi-b :
  rep? multi-left (suc (suc (suc zero)))
    ≡ rep? multi-right (suc (suc (suc zero)))
multi-b = refl

multi-a :
  rep? multi-left (suc (suc (suc (suc zero))))
    ≡ rep? multi-right (suc (suc (suc (suc zero))))
multi-a = refl

multi-result : rep? multi-left zero ≡ just (＇ (suc zero))
multi-result = refl

multi-one-short : repFuel? 2 multi-left zero ≡ nothing
multi-one-short = refl

multi-exact-fuel : repFuel? 3 multi-left zero ≡ just (＇ (suc zero))
multi-exact-fuel = refl

------------------------------------------------------------------------
-- Nonzero X and routing under a universal binder
------------------------------------------------------------------------

lex-crossed : TyEnv 1 2
  (nothing Vec.∷ just zero Vec.∷ Vec.[])
lex-crossed =
  ((∅ ,:= ℕᵗ) ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩) ,typ

forall-E : Ty 2
forall-E = `∀ (＇ zero ⇒ ＇ (suc zero))

forall-E₀ : Ty 1
forall-E₀ = `∀ (＇ zero ⇒ ＇ (suc zero))

forall-strengthens :
  strengthenᵗ? (suc zero) forall-E ≡ just forall-E₀
forall-strengthens = refl

nonzero-left : TyEnv 2 1 (nothing Vec.∷ Vec.[])
nonzero-left = (lex-crossed ,:= forall-E) ,end[ suc zero ]

nonzero-right : TyEnv 2 1 (nothing Vec.∷ Vec.[])
nonzero-right = (lex-crossed ,end[ suc zero ]) ,:= forall-E₀

nonzero-young : rep? nonzero-left zero ≡ rep? nonzero-right zero
nonzero-young = refl

nonzero-old :
  rep? nonzero-left (suc zero) ≡ rep? nonzero-right (suc zero)
nonzero-old = refl

old-fresh-among-lex :
  (suc (zero {n = 0})) ∉ᵛ (nothing Vec.∷ Vec.[])
old-fresh-among-lex zero ()
old-fresh-among-lex (suc ())

nonzero-reopen-left : TyEnv 2 2
  (nothing Vec.∷ just (suc zero) Vec.∷ Vec.[])
nonzero-reopen-left =
  nonzero-left
    ,begin[ suc zero ≔ suc zero ]⟨ old-fresh-among-lex ⟩

nonzero-reopen-right : TyEnv 2 2
  (nothing Vec.∷ just (suc zero) Vec.∷ Vec.[])
nonzero-reopen-right =
  nonzero-right
    ,begin[ suc zero ≔ suc zero ]⟨ old-fresh-among-lex ⟩

nonzero-reopen-young :
  rep? nonzero-reopen-left zero ≡ rep? nonzero-reopen-right zero
nonzero-reopen-young = refl

nonzero-reopen-old :
  rep? nonzero-reopen-left (suc zero)
    ≡ rep? nonzero-reopen-right (suc zero)
nonzero-reopen-old = refl

nonzero-reopen-result :
  rep? nonzero-reopen-left zero ≡ just forall-E
nonzero-reopen-result = refl

module alt.probes.RepExchangeAdversarial where

-- File Charter:
--   * Adversarially checks concrete instances of the proposed
--     `rep?-exchange` equation before `ν-push-conceal′` is trusted.
--   * The instances cover the U49 pocket, both U40 chain-ν representations,
--     multi-hop dead-anchor resolution through the swap, nested ends,
--     exact fuel boundaries, nonzero crossing positions, `∀` binder routing,
--     and both live and killing unbalanced prefixes.
--   * Every result below is instance evidence by definitional equality.  It
--     is not a proof of the general exchange theorem.  Such a proof would
--     run an outer induction on lookup fuel and an inner structural induction
--     on the scanned telescope, with `repoint?` handling crossing and lexical
--     variables separately.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import alt.Conversion
open import alt.ThetaTyping

------------------------------------------------------------------------
-- Probe-local concealment computation
------------------------------------------------------------------------

-- Resolve X directly to C while every other variable is routed through
-- `punchOut X`.  This is the total substitution equivalent of first
-- replacing X by `wkᵗ X C` and then strengthening away X.
concealRep? : ∀ {Δ}
  → (X : TyVar (suc Δ))
  → Ty Δ
  → Ty (suc Δ)
  → Maybe (Ty Δ)
concealRep? X C E = just (substᵗ (resolveSubᵗ X C) E)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

no-live-empty : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-empty ()

-- At the swap, scanning the left telescope reaches the newest ν and calls
--
--   repoint? resolve target σ φ (route-end X route) live-ren E.
--
-- The intended local equation is that this call computes the same `just E₀`
-- as `concealRep? X C E`, where resolving the dead crossing X yields C.
-- `swap-point-repoint` below checks that equation at the U49 geometry.

base : (C : Ty zero) → TyEnv 1 zero Vec.[]
base C = ∅ ,:= C

crossed : (C : Ty zero)
  → TyEnv 1 1 (just zero Vec.∷ Vec.[])
crossed C = base C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

swap-left : (C : Ty zero) → TyEnv 2 zero Vec.[]
swap-left C = (crossed C ,:= ＇ zero) ,end[ zero ]

swap-right : (C : Ty zero) → TyEnv 2 zero Vec.[]
swap-right C = (crossed C ,end[ zero ]) ,:= C

conceal-variable : ∀ (C : Ty zero)
  → concealRep? zero C (＇ zero) ≡ just C
conceal-variable C = refl

conceal-via-strengthen-u49 :
    strengthenᵗ? {Δ = 0} zero
      (replaceTy zero (wkᵗ zero ℕ⇒ℕ) (＇ zero))
    ≡ concealRep? zero ℕ⇒ℕ (＇ zero)
conceal-via-strengthen-u49 = refl

swap-point-scan :
    scanRep?
      (repFuel? 1 (swap-left ℕ⇒ℕ))
      (swap-left ℕ⇒ℕ)
      (swap-left ℕ⇒ℕ)
      (λ X → X)
      (λ X → just X)
      zero
    ≡ concealRep? zero ℕ⇒ℕ (＇ zero)
swap-point-scan = refl

swap-point-repoint :
    repointAtν?
      (repFuel? 1 (swap-left ℕ⇒ℕ))
      (swap-left ℕ⇒ℕ)
      (crossed ℕ⇒ℕ)
      (λ X → X)
      (route-end zero (λ X → just X))
      (＇ zero)
    ≡ concealRep? zero ℕ⇒ℕ (＇ zero)
swap-point-repoint = refl

------------------------------------------------------------------------
-- U49 and the two U40 chain-ν representations
------------------------------------------------------------------------

u49-young : rep? (swap-left ℕ⇒ℕ) zero
  ≡ rep? (swap-right ℕ⇒ℕ) zero
u49-young = refl

u49-old : rep? (swap-left ℕ⇒ℕ) (suc zero)
  ≡ rep? (swap-right ℕ⇒ℕ) (suc zero)
u49-old = refl

-- The application trace allocates `ℕ⇒ℕ`; the ★ trace allocates `★`.
u40-app-young : rep? (swap-left ℕ⇒ℕ) zero
  ≡ rep? (swap-right ℕ⇒ℕ) zero
u40-app-young = refl

u40-app-old : rep? (swap-left ℕ⇒ℕ) (suc zero)
  ≡ rep? (swap-right ℕ⇒ℕ) (suc zero)
u40-app-old = refl

u40-star-young : rep? (swap-left ★) zero
  ≡ rep? (swap-right ★) zero
u40-star-young = refl

u40-star-old : rep? (swap-left ★) (suc zero)
  ≡ rep? (swap-right ★) (suc zero)
u40-star-old = refl

------------------------------------------------------------------------
-- A dead prefix anchor resolves through the swapped E and an older anchor
------------------------------------------------------------------------

chain-left : (C : Ty zero) → TyEnv 3 zero Vec.[]
chain-left C =
  ((swap-left C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩)
    ,:= ＇ zero)
  ,end[ zero ]

chain-right : (C : Ty zero) → TyEnv 3 zero Vec.[]
chain-right C =
  ((swap-right C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩)
    ,:= ＇ zero)
  ,end[ zero ]

chain-prefix : rep? (chain-left ℕ⇒ℕ) zero
  ≡ rep? (chain-right ℕ⇒ℕ) zero
chain-prefix = refl

chain-swap-young : rep? (chain-left ℕ⇒ℕ) (suc zero)
  ≡ rep? (chain-right ℕ⇒ℕ) (suc zero)
chain-swap-young = refl

chain-old : rep? (chain-left ℕ⇒ℕ) (suc (suc zero))
  ≡ rep? (chain-right ℕ⇒ℕ) (suc (suc zero))
chain-old = refl

chain-one-short : repFuel? 2 (chain-left ℕ⇒ℕ) zero ≡ nothing
chain-one-short = refl

chain-exact-fuel : repFuel? 3 (chain-left ℕ⇒ℕ) zero ≡ just ℕ⇒ℕ
chain-exact-fuel = refl

------------------------------------------------------------------------
-- Nested ends around a prefix whose payload resolves across the swap
------------------------------------------------------------------------

one-fresh-among-lex-and-zero :
  (suc (zero {n = 0})) ∉ᵛ
    (nothing Vec.∷ just (zero {n = 1}) Vec.∷ Vec.[])
one-fresh-among-lex-and-zero zero ()
one-fresh-among-lex-and-zero (suc zero) ()
one-fresh-among-lex-and-zero (suc (suc ()))

nested-open-left : (C : Ty zero) → TyEnv 2 3
  (nothing Vec.∷ just (suc zero) Vec.∷ just zero Vec.∷ Vec.[])
nested-open-left C =
  ((swap-left C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩) ,typ)
    ,begin[ suc zero ≔ suc zero ]⟨ one-fresh-among-lex-and-zero ⟩

nested-open-right : (C : Ty zero) → TyEnv 2 3
  (nothing Vec.∷ just (suc zero) Vec.∷ just zero Vec.∷ Vec.[])
nested-open-right C =
  ((swap-right C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩) ,typ)
    ,begin[ suc zero ≔ suc zero ]⟨ one-fresh-among-lex-and-zero ⟩

nested-allocated-left : (C : Ty zero) → TyEnv 3 3
  (nothing Vec.∷ just (suc (suc zero)) Vec.∷
    just (suc zero) Vec.∷ Vec.[])
nested-allocated-left C =
  nested-open-left C ,:= ＇ (suc (suc zero))

nested-allocated-right : (C : Ty zero) → TyEnv 3 3
  (nothing Vec.∷ just (suc (suc zero)) Vec.∷
    just (suc zero) Vec.∷ Vec.[])
nested-allocated-right C =
  nested-open-right C ,:= ＇ (suc (suc zero))

nested-left : (C : Ty zero) → TyEnv 3 zero Vec.[]
nested-left C =
  ((nested-allocated-left C ,end[ suc zero ]) ,end[ suc zero ])
    ,end[ zero ]

nested-right : (C : Ty zero) → TyEnv 3 zero Vec.[]
nested-right C =
  ((nested-allocated-right C ,end[ suc zero ]) ,end[ suc zero ])
    ,end[ zero ]

nested-prefix : rep? (nested-left ℕ⇒ℕ) zero
  ≡ rep? (nested-right ℕ⇒ℕ) zero
nested-prefix = refl

nested-swap-young : rep? (nested-left ℕ⇒ℕ) (suc zero)
  ≡ rep? (nested-right ℕ⇒ℕ) (suc zero)
nested-swap-young = refl

nested-old : rep? (nested-left ℕ⇒ℕ) (suc (suc zero))
  ≡ rep? (nested-right ℕ⇒ℕ) (suc (suc zero))
nested-old = refl

nested-one-short : repFuel? 2 (nested-left ℕ⇒ℕ) zero ≡ nothing
nested-one-short = refl

nested-exact-fuel : repFuel? 3 (nested-left ℕ⇒ℕ) zero ≡ just ℕ⇒ℕ
nested-exact-fuel = refl

------------------------------------------------------------------------
-- Four anchors: two Φ entries resolve through E and then the oldest anchor
------------------------------------------------------------------------

deep-left : (C : Ty zero) → TyEnv 4 zero Vec.[]
deep-left C =
  ((nested-left C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩)
    ,:= ＇ zero)
  ,end[ zero ]

deep-right : (C : Ty zero) → TyEnv 4 zero Vec.[]
deep-right C =
  ((nested-right C ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩)
    ,:= ＇ zero)
  ,end[ zero ]

deep-newest-prefix : rep? (deep-left ℕ⇒ℕ) zero
  ≡ rep? (deep-right ℕ⇒ℕ) zero
deep-newest-prefix = refl

deep-older-prefix : rep? (deep-left ℕ⇒ℕ) (suc zero)
  ≡ rep? (deep-right ℕ⇒ℕ) (suc zero)
deep-older-prefix = refl

deep-swap-young : rep? (deep-left ℕ⇒ℕ) (suc (suc zero))
  ≡ rep? (deep-right ℕ⇒ℕ) (suc (suc zero))
deep-swap-young = refl

deep-old : rep? (deep-left ℕ⇒ℕ) (suc (suc (suc zero)))
  ≡ rep? (deep-right ℕ⇒ℕ) (suc (suc (suc zero)))
deep-old = refl

deep-one-short : repFuel? 3 (deep-left ℕ⇒ℕ) zero ≡ nothing
deep-one-short = refl

deep-exact-fuel : repFuel? 4 (deep-left ℕ⇒ℕ) zero ≡ just ℕ⇒ℕ
deep-exact-fuel = refl

------------------------------------------------------------------------
-- C is itself a live crossing; an unbalanced Φ then kills that alias
------------------------------------------------------------------------

dependent-old : TyEnv 1 1 (just zero Vec.∷ Vec.[])
dependent-old =
  (∅ ,:= ℕᵗ) ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

dependent-middle : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
dependent-middle = dependent-old ,:= ＇ zero

zero-fresh-among-one :
  (zero {n = 1}) ∉ᵛ
    (just (suc (zero {n = 0})) Vec.∷ Vec.[])
zero-fresh-among-one zero ()
zero-fresh-among-one (suc ())

dependent-crossed : TyEnv 2 2
  (just zero Vec.∷ just (suc zero) Vec.∷ Vec.[])
dependent-crossed =
  dependent-middle ,begin[ zero ≔ zero ]⟨ zero-fresh-among-one ⟩

dependent-left : TyEnv 3 1
  (just (suc (suc zero)) Vec.∷ Vec.[])
dependent-left =
  (dependent-crossed ,:= ＇ zero) ,end[ zero ]

dependent-right : TyEnv 3 1
  (just (suc (suc zero)) Vec.∷ Vec.[])
dependent-right =
  (dependent-crossed ,end[ zero ]) ,:= ＇ zero

dependent-conceal : concealRep? {Δ = 1} zero (＇ zero) (＇ zero)
  ≡ just (＇ zero)
dependent-conceal = refl

dependent-via-strengthen :
    strengthenᵗ? zero
      (replaceTy zero (wkᵗ zero (＇ zero)) (＇ zero))
    ≡ concealRep? {Δ = 1} zero (＇ zero) (＇ zero)
dependent-via-strengthen = refl

dependent-young-live : rep? dependent-left zero
  ≡ rep? dependent-right zero
dependent-young-live = refl

dependent-middle-live : rep? dependent-left (suc zero)
  ≡ rep? dependent-right (suc zero)
dependent-middle-live = refl

dependent-old-live : rep? dependent-left (suc (suc zero))
  ≡ rep? dependent-right (suc (suc zero))
dependent-old-live = refl

dependent-young-live-result : rep? dependent-left zero ≡ just (＇ zero)
dependent-young-live-result = refl

dependent-dead-left : TyEnv 3 zero Vec.[]
dependent-dead-left = dependent-left ,end[ zero ]

dependent-dead-right : TyEnv 3 zero Vec.[]
dependent-dead-right = dependent-right ,end[ zero ]

dependent-young-dead : rep? dependent-dead-left zero
  ≡ rep? dependent-dead-right zero
dependent-young-dead = refl

dependent-middle-dead : rep? dependent-dead-left (suc zero)
  ≡ rep? dependent-dead-right (suc zero)
dependent-middle-dead = refl

dependent-old-dead : rep? dependent-dead-left (suc (suc zero))
  ≡ rep? dependent-dead-right (suc (suc zero))
dependent-old-dead = refl

dependent-one-short : repFuel? 2 dependent-dead-left zero ≡ nothing
dependent-one-short = refl

dependent-exact-fuel : repFuel? 3 dependent-dead-left zero ≡ just ℕᵗ
dependent-exact-fuel = refl

dependent-young-dead-result : rep? dependent-dead-left zero ≡ just ℕᵗ
dependent-young-dead-result = refl

two-fresh-among-lex :
  (suc (suc (zero {n = 0}))) ∉ᵛ (nothing Vec.∷ Vec.[])
two-fresh-among-lex zero ()
two-fresh-among-lex (suc ())

dependent-rebased-left : TyEnv 3 2
  (nothing Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
dependent-rebased-left =
  (dependent-dead-left ,typ)
    ,begin[ suc zero ≔ suc (suc zero) ]⟨ two-fresh-among-lex ⟩

dependent-rebased-right : TyEnv 3 2
  (nothing Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
dependent-rebased-right =
  (dependent-dead-right ,typ)
    ,begin[ suc zero ≔ suc (suc zero) ]⟨ two-fresh-among-lex ⟩

dependent-rebased-young : rep? dependent-rebased-left zero
  ≡ rep? dependent-rebased-right zero
dependent-rebased-young = refl

dependent-rebased-middle : rep? dependent-rebased-left (suc zero)
  ≡ rep? dependent-rebased-right (suc zero)
dependent-rebased-middle = refl

dependent-rebased-old : rep? dependent-rebased-left (suc (suc zero))
  ≡ rep? dependent-rebased-right (suc (suc zero))
dependent-rebased-old = refl

dependent-rebased-result : rep? dependent-rebased-left zero
  ≡ just (＇ (suc zero))
dependent-rebased-result = refl

------------------------------------------------------------------------
-- C is lexical; ending that variable probes route-then-resolve ordering
------------------------------------------------------------------------

lexical-base : TyEnv zero 1 (nothing Vec.∷ Vec.[])
lexical-base = ∅ ,typ

lexical-anchor : TyEnv 1 1 (nothing Vec.∷ Vec.[])
lexical-anchor = lexical-base ,:= ＇ zero

zero-fresh-among-lex : (zero {n = 0}) ∉ᵛ
  (nothing Vec.∷ Vec.[])
zero-fresh-among-lex zero ()
zero-fresh-among-lex (suc ())

lexical-crossed : TyEnv 1 2
  (just zero Vec.∷ nothing Vec.∷ Vec.[])
lexical-crossed =
  lexical-anchor ,begin[ zero ≔ zero ]⟨ zero-fresh-among-lex ⟩

lexical-left : TyEnv 2 1 (nothing Vec.∷ Vec.[])
lexical-left = (lexical-crossed ,:= ＇ zero) ,end[ zero ]

lexical-right : TyEnv 2 1 (nothing Vec.∷ Vec.[])
lexical-right = (lexical-crossed ,end[ zero ]) ,:= ＇ zero

lexical-young-live : rep? lexical-left zero
  ≡ rep? lexical-right zero
lexical-young-live = refl

lexical-old-live : rep? lexical-left (suc zero)
  ≡ rep? lexical-right (suc zero)
lexical-old-live = refl

lexical-young-live-result : rep? lexical-left zero ≡ just (＇ zero)
lexical-young-live-result = refl

lexical-dead-left : TyEnv 2 zero Vec.[]
lexical-dead-left = lexical-left ,end[ zero ]

lexical-dead-right : TyEnv 2 zero Vec.[]
lexical-dead-right = lexical-right ,end[ zero ]

lexical-young-dead : rep? lexical-dead-left zero
  ≡ rep? lexical-dead-right zero
lexical-young-dead = refl

lexical-old-dead : rep? lexical-dead-left (suc zero)
  ≡ rep? lexical-dead-right (suc zero)
lexical-old-dead = refl

lexical-young-dead-result : rep? lexical-dead-left zero ≡ nothing
lexical-young-dead-result = refl

zero-fresh-among-lex₂ : (zero {n = 1}) ∉ᵛ
  (nothing Vec.∷ Vec.[])
zero-fresh-among-lex₂ zero ()
zero-fresh-among-lex₂ (suc ())

lexical-routed-left : TyEnv 2 2
  (just zero Vec.∷ nothing Vec.∷ Vec.[])
lexical-routed-left =
  lexical-left ,begin[ zero ≔ zero ]⟨ zero-fresh-among-lex₂ ⟩

lexical-routed-right : TyEnv 2 2
  (just zero Vec.∷ nothing Vec.∷ Vec.[])
lexical-routed-right =
  lexical-right ,begin[ zero ≔ zero ]⟨ zero-fresh-among-lex₂ ⟩

lexical-routed-young : rep? lexical-routed-left zero
  ≡ rep? lexical-routed-right zero
lexical-routed-young = refl

lexical-routed-old : rep? lexical-routed-left (suc zero)
  ≡ rep? lexical-routed-right (suc zero)
lexical-routed-old = refl

lexical-routed-result : rep? lexical-routed-left zero
  ≡ just (＇ (suc zero))
lexical-routed-result = refl

lexical-routed-killed-left : TyEnv 2 1
  (just zero Vec.∷ Vec.[])
lexical-routed-killed-left = lexical-routed-left ,end[ suc zero ]

lexical-routed-killed-right : TyEnv 2 1
  (just zero Vec.∷ Vec.[])
lexical-routed-killed-right = lexical-routed-right ,end[ suc zero ]

lexical-routed-killed-young : rep? lexical-routed-killed-left zero
  ≡ rep? lexical-routed-killed-right zero
lexical-routed-killed-young = refl

lexical-routed-killed-old :
  rep? lexical-routed-killed-left (suc zero)
    ≡ rep? lexical-routed-killed-right (suc zero)
lexical-routed-killed-old = refl

lexical-routed-killed-result :
  rep? lexical-routed-killed-left zero ≡ nothing
lexical-routed-killed-result = refl

------------------------------------------------------------------------
-- C mixes a crossing and a lexical variable, then Φ kills and rebases it
------------------------------------------------------------------------

compound-old-crossed : TyEnv 1 2
  (nothing Vec.∷ just zero Vec.∷ Vec.[])
compound-old-crossed =
  ((∅ ,:= ℕᵗ) ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩) ,typ

compound-middle : TyEnv 2 2
  (nothing Vec.∷ just (suc zero) Vec.∷ Vec.[])
compound-middle =
  compound-old-crossed ,:= (＇ (suc zero) ⇒ ＇ zero)

zero-fresh-among-lex-and-one : (zero {n = 1}) ∉ᵛ
  (nothing Vec.∷ just (suc (zero {n = 0})) Vec.∷ Vec.[])
zero-fresh-among-lex-and-one zero ()
zero-fresh-among-lex-and-one (suc zero) ()
zero-fresh-among-lex-and-one (suc (suc ()))

compound-crossed : TyEnv 2 3
  (just zero Vec.∷ nothing Vec.∷
    just (suc zero) Vec.∷ Vec.[])
compound-crossed =
  compound-middle
    ,begin[ zero ≔ zero ]⟨ zero-fresh-among-lex-and-one ⟩

compound-C : Ty 2
compound-C = ＇ (suc zero) ⇒ ＇ zero

compound-left : TyEnv 3 2
  (nothing Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
compound-left = (compound-crossed ,:= ＇ zero) ,end[ zero ]

compound-right : TyEnv 3 2
  (nothing Vec.∷ just (suc (suc zero)) Vec.∷ Vec.[])
compound-right =
  (compound-crossed ,end[ zero ]) ,:= compound-C

compound-young : rep? compound-left zero
  ≡ rep? compound-right zero
compound-young = refl

compound-middle-anchor : rep? compound-left (suc zero)
  ≡ rep? compound-right (suc zero)
compound-middle-anchor = refl

compound-old : rep? compound-left (suc (suc zero))
  ≡ rep? compound-right (suc (suc zero))
compound-old = refl

compound-result : rep? compound-left zero ≡ just compound-C
compound-result = refl

compound-killed-left : TyEnv 3 1 (nothing Vec.∷ Vec.[])
compound-killed-left = compound-left ,end[ suc zero ]

compound-killed-right : TyEnv 3 1 (nothing Vec.∷ Vec.[])
compound-killed-right = compound-right ,end[ suc zero ]

compound-killed-young : rep? compound-killed-left zero
  ≡ rep? compound-killed-right zero
compound-killed-young = refl

compound-killed-middle : rep? compound-killed-left (suc zero)
  ≡ rep? compound-killed-right (suc zero)
compound-killed-middle = refl

compound-killed-old : rep? compound-killed-left (suc (suc zero))
  ≡ rep? compound-killed-right (suc (suc zero))
compound-killed-old = refl

compound-killed-result : rep? compound-killed-left zero
  ≡ just (ℕᵗ ⇒ ＇ zero)
compound-killed-result = refl

compound-rebased-left : TyEnv 3 2
  (just (suc (suc zero)) Vec.∷ nothing Vec.∷ Vec.[])
compound-rebased-left =
  compound-killed-left
    ,begin[ zero ≔ suc (suc zero) ]⟨ two-fresh-among-lex ⟩

compound-rebased-right : TyEnv 3 2
  (just (suc (suc zero)) Vec.∷ nothing Vec.∷ Vec.[])
compound-rebased-right =
  compound-killed-right
    ,begin[ zero ≔ suc (suc zero) ]⟨ two-fresh-among-lex ⟩

compound-rebased-young : rep? compound-rebased-left zero
  ≡ rep? compound-rebased-right zero
compound-rebased-young = refl

compound-rebased-middle : rep? compound-rebased-left (suc zero)
  ≡ rep? compound-rebased-right (suc zero)
compound-rebased-middle = refl

compound-rebased-old : rep? compound-rebased-left (suc (suc zero))
  ≡ rep? compound-rebased-right (suc (suc zero))
compound-rebased-old = refl

compound-rebased-result : rep? compound-rebased-left zero
  ≡ just (＇ zero ⇒ ＇ (suc zero))
compound-rebased-result = refl

------------------------------------------------------------------------
-- Nonzero X mixes a crossing replacement with a routed lexical variable
------------------------------------------------------------------------

nonzero-crossed : TyEnv 1 2
  (nothing Vec.∷ just zero Vec.∷ Vec.[])
nonzero-crossed =
  ((∅ ,:= ℕᵗ) ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩) ,typ

nonzero-E : Ty 2
nonzero-E = ＇ (suc zero) ⇒ ＇ zero

nonzero-E₀ : Ty 1
nonzero-E₀ = ℕᵗ ⇒ ＇ zero

nonzero-conceal : concealRep? (suc zero) ℕᵗ nonzero-E
  ≡ just nonzero-E₀
nonzero-conceal = refl

nonzero-left : TyEnv 2 1 (nothing Vec.∷ Vec.[])
nonzero-left = (nonzero-crossed ,:= nonzero-E) ,end[ suc zero ]

nonzero-right : TyEnv 2 1 (nothing Vec.∷ Vec.[])
nonzero-right =
  (nonzero-crossed ,end[ suc zero ]) ,:= nonzero-E₀

nonzero-young-live : rep? nonzero-left zero
  ≡ rep? nonzero-right zero
nonzero-young-live = refl

nonzero-old-live : rep? nonzero-left (suc zero)
  ≡ rep? nonzero-right (suc zero)
nonzero-old-live = refl

nonzero-dead-left : TyEnv 2 zero Vec.[]
nonzero-dead-left = nonzero-left ,end[ zero ]

nonzero-dead-right : TyEnv 2 zero Vec.[]
nonzero-dead-right = nonzero-right ,end[ zero ]

nonzero-young-dead : rep? nonzero-dead-left zero
  ≡ rep? nonzero-dead-right zero
nonzero-young-dead = refl

nonzero-old-dead : rep? nonzero-dead-left (suc zero)
  ≡ rep? nonzero-dead-right (suc zero)
nonzero-old-dead = refl

nonzero-young-live-result : rep? nonzero-left zero
  ≡ just nonzero-E₀
nonzero-young-live-result = refl

nonzero-young-dead-result : rep? nonzero-dead-left zero ≡ nothing
nonzero-young-dead-result = refl

------------------------------------------------------------------------
-- A still-live, unmatched prefix begin tests anchor-directed aliasing
------------------------------------------------------------------------

live-prefix-left : TyEnv 3 1 (just (suc zero) Vec.∷ Vec.[])
live-prefix-left =
  (swap-left ℕ⇒ℕ ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩)
    ,:= ＇ zero

live-prefix-right : TyEnv 3 1 (just (suc zero) Vec.∷ Vec.[])
live-prefix-right =
  (swap-right ℕ⇒ℕ ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩)
    ,:= ＇ zero

live-prefix-newest : rep? live-prefix-left zero
  ≡ rep? live-prefix-right zero
live-prefix-newest = refl

live-prefix-swap-young : rep? live-prefix-left (suc zero)
  ≡ rep? live-prefix-right (suc zero)
live-prefix-swap-young = refl

live-prefix-old : rep? live-prefix-left (suc (suc zero))
  ≡ rep? live-prefix-right (suc (suc zero))
live-prefix-old = refl

live-prefix-result : rep? live-prefix-left zero ≡ just (＇ zero)
live-prefix-result = refl

------------------------------------------------------------------------
-- Universal payload: route and resolve beneath the `∀` binder
------------------------------------------------------------------------

forall-E : Ty 2
forall-E =
  `∀ (＇ zero ⇒ (＇ (suc (suc zero)) ⇒ ＇ (suc zero)))

forall-E₀ : Ty 1
forall-E₀ = `∀ (＇ zero ⇒ (ℕᵗ ⇒ ＇ (suc zero)))

forall-conceal : concealRep? (suc zero) ℕᵗ forall-E
  ≡ just forall-E₀
forall-conceal = refl

forall-left : TyEnv 2 1 (nothing Vec.∷ Vec.[])
forall-left = (nonzero-crossed ,:= forall-E) ,end[ suc zero ]

forall-right : TyEnv 2 1 (nothing Vec.∷ Vec.[])
forall-right =
  (nonzero-crossed ,end[ suc zero ]) ,:= forall-E₀

forall-young-live : rep? forall-left zero
  ≡ rep? forall-right zero
forall-young-live = refl

forall-old-live : rep? forall-left (suc zero)
  ≡ rep? forall-right (suc zero)
forall-old-live = refl

forall-live-result : rep? forall-left zero ≡ just forall-E₀
forall-live-result = refl

forall-dead-left : TyEnv 2 zero Vec.[]
forall-dead-left = forall-left ,end[ zero ]

forall-dead-right : TyEnv 2 zero Vec.[]
forall-dead-right = forall-right ,end[ zero ]

forall-young-dead : rep? forall-dead-left zero
  ≡ rep? forall-dead-right zero
forall-young-dead = refl

forall-old-dead : rep? forall-dead-left (suc zero)
  ≡ rep? forall-dead-right (suc zero)
forall-old-dead = refl

forall-dead-result : rep? forall-dead-left zero ≡ nothing
forall-dead-result = refl

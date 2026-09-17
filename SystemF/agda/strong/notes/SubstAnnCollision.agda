module strong.notes.SubstAnnCollision where

-- WHERE M₅'s BAD HIDE COMES FROM.  Every step below is `refl`.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

-- the ∀-body conversion `TyWrap` gets from `allView` (PreserveTyWrap
-- §8.1b's `dₘ`), and the type it is instantiated at
d : Conv
d = hide (suc zero) (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹)

S : Ty
S = ` zero

-- BEFORE.  The hide is at name 1 — the crossing assignment `X:=α` — and
-- the terminator mentions name 0, the ∀'S OWN BINDER.  Different
-- variables, so the hide is not at the variable it hides.
--
-- AFTER `substAnn 0 S`.  The ∀'s binder is instantiated AT `X` and its
-- slot removed, so every name above it drops by one:
step-name : nameSub zero (suc zero) ≡ zero
step-name = refl

-- the terminator's `` ` 0 `` was the binder and becomes `S`
step-ann : closeAt zero S (` zero ⇒ `𝔹) ≡ (` zero ⇒ `𝔹)
step-ann = refl

-- and `S` itself is carried past the crossing unchanged, since the
-- crossing's slot (1) is above it
step-carry : tyOutElt (hide (suc zero) (lvl zero)) S ≡ ` zero
step-carry = refl

-- so the whole substitution gives a hide AT NAME 0 whose type MENTIONS
-- NAME 0 — the collision
collision : substAnn zero S d
          ≡ hide zero (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹)
collision = refl

-- It is not a capture bug: `tyOutElt` does protect `S` from the
-- crossing's slot.  The two names genuinely coincide, because the
-- SOURCE PROGRAM instantiates the ∀ at the very variable the boundary
-- hides —
--
--     ( ΛX. λf:(∀S. S→𝔹). f [X] ) [𝔹] · ( ΛS. λz:S. true )
--
-- (notes/SourceToTyWrapGap).  `substAnn` renames the crossing's NAME
-- and never its KIND, so an `id` crossing that lands on the
-- instantiated variable stays an `id` crossing — and by Jeremy's rule
-- it should have become a renaming.

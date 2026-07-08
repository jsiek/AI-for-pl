module Untyped where

-- File Charter:
--   * Untyped PolyNuBar source syntax and the Scheme-style elaborator.
--   * Ports `untyped` from `interp-nu/type-check.ss`, inserting casts around
--     untyped constants, lambdas, application, products, conditionals, and
--     primitives.
--   * Uses de Bruijn term variables, matching the typed target syntax.

open import Data.Nat using (ℕ; suc; _+_)
open import Terms public

------------------------------------------------------------------------
-- Untyped source syntax
------------------------------------------------------------------------

infix  9 #_
infix  9 lit_
infix  5 ƛᵘ_
infixl 7 _·ᵘ_

data UTerm : Set where
  #_     : Var → UTerm
  lit_   : Const → UTerm
  ƛᵘ_    : UTerm → UTerm
  _·ᵘ_   : UTerm → UTerm → UTerm
  isᵘ    : Label → UTerm → Ty → UTerm
  pairᵘ  : UTerm → UTerm → UTerm
  fstᵘ   : UTerm → UTerm
  sndᵘ   : UTerm → UTerm
  ifᵘ    : UTerm → UTerm → UTerm → UTerm
  primᵘ  : Prim → UTerm → UTerm

------------------------------------------------------------------------
-- Elaboration
------------------------------------------------------------------------

autoLabel : ℕ → Label
autoLabel n = ℓ (1000 + n)

record Elab : Set where
  constructor elabbed
  field
    next : ℕ
    term : Term

open Elab public

elabFrom : ℕ → UTerm → Elab
elabFrom n (# x) = elabbed n (` x)
elabFrom n (lit c) = elabbed n (($ c) ⦂ typeOfConst c ⇒[ - ] ★)
elabFrom n (ƛᵘ M) with elabFrom (suc n) M
elabFrom n (ƛᵘ M) | elabbed n′ M′ =
  elabbed n′ ((ƛ[ ★ ] M′) ⦂ (★ ⇒ ★) ⇒[ autoLabel n ] ★)
elabFrom n (L ·ᵘ M) with elabFrom (suc n) L
elabFrom n (L ·ᵘ M) | elabbed n′ L′ with elabFrom n′ M
elabFrom n (L ·ᵘ M) | elabbed n′ L′ | elabbed n″ M′ =
  elabbed n″ ((L′ ⦂ ★ ⇒[ autoLabel n ] (★ ⇒ ★)) · M′)
elabFrom n (isᵘ p M G) with elabFrom n M
elabFrom n (isᵘ p M G) | elabbed n′ M′ = elabbed n′ (is p M′ G)
elabFrom n (pairᵘ L M) with elabFrom (suc n) L
elabFrom n (pairᵘ L M) | elabbed n′ L′ with elabFrom n′ M
elabFrom n (pairᵘ L M) | elabbed n′ L′ | elabbed n″ M′ =
  elabbed n″ ((pair L′ M′) ⦂ (★ `× ★) ⇒[ autoLabel n ] ★)
elabFrom n (fstᵘ M) with elabFrom (suc n) M
elabFrom n (fstᵘ M) | elabbed n′ M′ =
  elabbed n′ (fst (M′ ⦂ ★ ⇒[ autoLabel n ] (★ `× ★)))
elabFrom n (sndᵘ M) with elabFrom (suc n) M
elabFrom n (sndᵘ M) | elabbed n′ M′ =
  elabbed n′ (snd (M′ ⦂ ★ ⇒[ autoLabel n ] (★ `× ★)))
elabFrom n (ifᵘ L M N) with elabFrom (suc n) L
elabFrom n (ifᵘ L M N) | elabbed n′ L′ with elabFrom n′ M
elabFrom n (ifᵘ L M N) | elabbed n′ L′ | elabbed n″ M′
  with elabFrom n″ N
elabFrom n (ifᵘ L M N) | elabbed n′ L′ | elabbed n″ M′
  | elabbed n‴ N′ =
  elabbed n‴ (ifte (L′ ⦂ ★ ⇒[ autoLabel n ] (`ι 𝔹)) M′ N′)
elabFrom n (primᵘ op M) with typeOfPrim op
elabFrom n (primᵘ op M) | A ⇒ B with elabFrom (suc (suc n)) M
elabFrom n (primᵘ op M) | A ⇒ B | elabbed n′ M′ =
  elabbed n′
    ((prim op (M′ ⦂ ★ ⇒[ autoLabel n ] A)) ⦂ B ⇒[ autoLabel (suc n) ] ★)
elabFrom n (primᵘ op M) | _ = elabbed n (blame (autoLabel n))

elaborateFrom : ℕ → UTerm → Term
elaborateFrom n M = term (elabFrom n M)

elaborate : UTerm → Term
elaborate = elaborateFrom 0

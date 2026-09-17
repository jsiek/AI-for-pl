module strong.notes.ReadAtExterior where

-- Jeremy: read the representation at the EXTERIOR OF THE WHOLE
-- CONVERSION, not at the element's own interior.  For M₅'s inner
-- conversion that exterior is the ν's body context, which still has
-- the name `X` for `α` — the `id{-X:=α}` has not been crossed yet.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ

Sg : Store
Sg = `𝔹ᴿ ∷ []

R : RepTy
R = `ᵃ (lvl zero)

-- where the seal is read TODAY: the ↦'s exterior, after the hide.
Γnow : Ctxᵗ
Γnow = [] ∥ nuBind R ∷ []

-- where Jeremy proposes reading it: the whole conversion's exterior,
-- i.e. the ν's body context.
Γext : Ctxᵗ
Γext = asgn (lvl zero) ∷ [] ∥ nuBind R ∷ []

-- today: no derivation, because `read-var` has no name to land on
now-⊥ : ∀ {A} → ¬ (Sg ∣ Γnow ⊢ R ⇓ A)
now-⊥ (read-var ())

-- proposed: it reads back, to the name `X`
ext-ok : Sg ∣ Γext ⊢ R ⇓ ` zero
ext-ok = read-var n-here-asgn

-- BUT the type it produces is NOT well formed where the element sits:
-- `Γnow`'s stack is empty, so `X` is out of scope there.
scope-gap : ¬ (Γnow ⊢ᵗ ` zero)
scope-gap (wf-var ())

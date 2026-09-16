module strong.proof.Flat where

-- Strong System F v8 — the shape of a REDUCTION context.
--
-- No term rule ever pushes a `bind`: only conversion typing does, and
-- `conv-all` pushes it around the nested conversion, not around the
-- element, so a boundary's interior gains none.  The base is empty at
-- every redex too: there is no `ξ-Λ` (a `Λ`'s body is already a value)
-- and no `ξ-ν` (a `ν` discharges on the spot).  So the only entries a
-- reduction context accumulates are the `asgn`s a boundary's crossings
-- push.
--
-- That invariant is what makes `Alloc` sound: over a flat context a
-- representation can only mention store levels, so it is closed and
-- can go into the global store.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion

private
  variable
    Σ : Store
    Ss Ts : List StackEnt
    Bs : List BaseEnt
    Δ Δᵢ Δₑ : Ctxᵗ
    A B : Ty
    R : RepTy
    X : ℕ
    α : Addr

------------------------------------------------------------------------
-- Flatness
------------------------------------------------------------------------

data NoBinds : List StackEnt → Set where
  nb-[]   : NoBinds []
  nb-asgn : NoBinds Ss → NoBinds (asgn α ∷ Ss)

-- The stack holds EXACTLY n binds — the conversion judgment descends
-- under one at every `all`, and a crossing may push an `asgn` above
-- them, so the count is the invariant, not a prefix shape.  `n ≡ 0` is
-- the reduction-context case.
data FlatU : ℕ → List StackEnt → Set where
  fu-[]   : FlatU zero []
  fu-asgn : ∀ {n} → FlatU n Ss → FlatU n (asgn α ∷ Ss)
  fu-bind : ∀ {n} → FlatU n Ss → FlatU (suc n) (bind ∷ Ss)

fu-nobinds : FlatU zero Ss → NoBinds Ss
fu-nobinds fu-[] = nb-[]
fu-nobinds (fu-asgn fu) = nb-asgn (fu-nobinds fu)

record Flatn (n : ℕ) (Δ : Ctxᵗ) : Set where
  constructor flat
  field
    flat-stk : FlatU n (stk Δ)
    flat-bas : bas Δ ≡ []
open Flatn

Flat : Ctxᵗ → Set
Flat = Flatn zero

flat-[] : Flat ([] ∥ [])
flat-[] = flat fu-[] refl

------------------------------------------------------------------------
-- Over a flat context a representation is CLOSED
------------------------------------------------------------------------
-- Stated with a prefix `Ts` of binders, which is what `∀ᴿ` accumulates
-- as the induction descends.

∋a-closed : NoBinds Ss → Σ ∣ (Ts ++ Ss ∥ []) ∋a α → Σ ∣ (Ts ∥ []) ∋a α
∋a-closed nb (a-lvl l) = a-lvl l
∋a-closed {Ts = []} (nb-asgn nb) (a-skip-asgn p) = ∋a-closed nb p
∋a-closed {Ts = bind ∷ Ts} nb a-here-bind = a-here-bind
∋a-closed {Ts = bind ∷ Ts} nb (a-skip-bind p) =
  a-skip-bind (∋a-closed nb p)
∋a-closed {Ts = asgn β ∷ Ts} nb (a-skip-asgn p) =
  a-skip-asgn (∋a-closed nb p)

wfᴿ-closed : NoBinds Ss → Σ ∣ (Ts ++ Ss ∥ []) ⊢ᴿ R → Σ ∣ (Ts ∥ []) ⊢ᴿ R
wfᴿ-closed nb (wfᴿ-var a) = wfᴿ-var (∋a-closed nb a)
wfᴿ-closed nb wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-closed nb wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-closed nb (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-closed nb a) (wfᴿ-closed nb b)
wfᴿ-closed {Ts = Ts} nb (wfᴿ-∀ a) =
  wfᴿ-∀ (wfᴿ-closed {Ts = bind ∷ Ts} nb a)

-- what `Alloc` needs
flat-closed : Flat Δ → Σ ∣ Δ ⊢ᴿ R → Σ ∣ ([] ∥ []) ⊢ᴿ R
flat-closed {Δ = Ss ∥ .[]} (flat fu refl) wf =
  wfᴿ-closed {Ts = []} (fu-nobinds fu) wf

------------------------------------------------------------------------
-- Flatness travels along the interior walk
------------------------------------------------------------------------
-- A crossing pushes or pops exactly one `asgn`, and `↦` and `all` do
-- not change the context at all — `all` only descends under a `bind`,
-- which the index counts.

pop-flat : ∀ {n} → Δₑ ▷ X := α ⇒ Δᵢ → Flatn n Δₑ → Flatn n Δᵢ
pop-flat pop-here (flat (fu-asgn fu) refl) = flat fu refl
pop-flat (pop-bind-b p) (flat (fu-bind fu) refl)
  with pop-flat p (flat fu refl)
pop-flat (pop-bind-b p) (flat (fu-bind fu) refl) | flat fu′ refl =
  flat (fu-bind fu′) refl
pop-flat (pop-bind-l p) (flat (fu-bind fu) refl)
  with pop-flat p (flat fu refl)
pop-flat (pop-bind-l p) (flat (fu-bind fu) refl) | flat fu′ refl =
  flat (fu-bind fu′) refl
pop-flat (pop-bind-e p) (flat (fu-bind fu) refl)
  with pop-flat p (flat fu refl)
pop-flat (pop-bind-e p) (flat (fu-bind fu) refl) | flat fu′ refl =
  flat (fu-bind fu′) refl

push-flat : ∀ {n} → Δᵢ ▷ X := α ⇒ Δₑ → Flatn n Δₑ → Flatn n Δᵢ
push-flat pop-here (flat fu refl) = flat (fu-asgn fu) refl
push-flat (pop-bind-b p) (flat (fu-bind fu) refl)
  with push-flat p (flat fu refl)
push-flat (pop-bind-b p) (flat (fu-bind fu) refl) | flat fu′ refl =
  flat (fu-bind fu′) refl
push-flat (pop-bind-l p) (flat (fu-bind fu) refl)
  with push-flat p (flat fu refl)
push-flat (pop-bind-l p) (flat (fu-bind fu) refl) | flat fu′ refl =
  flat (fu-bind fu′) refl
push-flat (pop-bind-e p) (flat (fu-bind fu) refl)
  with push-flat p (flat fu refl)
push-flat (pop-bind-e p) (flat (fu-bind fu) refl) | flat fu′ refl =
  flat (fu-bind fu′) refl

mutual
  convElt-flat : ∀ {n ĉ} → Σ ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δₑ → Flatn n Δₑ → Flatn n Δᵢ
  convElt-flat (conv-seal rep rd pop) fl = pop-flat pop fl
  convElt-flat (conv-unseal rep rd pop na) fl = push-flat pop fl
  convElt-flat (conv-hide sc wf pop na) fl = pop-flat pop fl
  convElt-flat (conv-show sc wf pop na) fl = push-flat pop fl
  convElt-flat (conv-fun s t) fl = conv-flat t fl
  convElt-flat (conv-all s) (flat fu refl) with conv-flat s (flat (fu-bind fu) refl)
  convElt-flat (conv-all s) (flat fu refl) | flat (fu-bind fu′) refl =
    flat fu′ refl

  conv-flat : ∀ {n c} → Σ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δₑ → Flatn n Δₑ → Flatn n Δᵢ
  conv-flat (conv-id wf) fl = fl
  conv-flat (conv-cons hd tl) fl = convElt-flat hd (conv-flat tl fl)

module strong.proof.AllTyping where

-- Strong System F v8 — `allView` takes a typed conversion between two
-- `∀`s to a typed conversion between their bodies, under one more
-- binder assignment.
--
-- This is the `arr` story (`proof.ArrTyping`) with one side instead of
-- two: the split is elementwise, an `all` element contributes its own
-- nested conversion, and an identity crossing contributes ITSELF with
-- its name and address shifted past the new `bind`.  That shift is
-- exactly `⇑ᵃ` on the address and `suc` on the name, and the pop
-- judgment already carries a crossing past a `bind` — one rule per
-- address form, which is why `all⁺` needs no case analysis.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.proof.CompositionTyping using
  (⧺-typing; preserve-↠; conv-namefn; namefn-bind)
open import strong.proof.Canonical using (conv-target)
open import strong.proof.Interior using (pop-base)
open import strong.proof.ArrTyping using
  (attach-elts; attach-elts-at; attach-++; attach-++ˡ)

private
  variable
    Sg : Store
    Δ Δᵢ : Ctxᵗ
    A B A₀ A′ : Ty
    c : Conv
    X : ℕ
    α : Addr

------------------------------------------------------------------------
-- Going under one binder assignment
------------------------------------------------------------------------

⇑ᶜ : Ctxᵗ → Ctxᵗ
⇑ᶜ Δ = bind ∷ stk Δ ∥ bas Δ

wf-∀-inv : Δ ⊢ᵗ `∀ A → ⇑ᶜ Δ ⊢ᵗ A
wf-∀-inv (wf-∀ a) = a

-- A rename cannot turn a non-∀ into a ∀; and `shiftAtᵗ` commutes with
-- `∀` definitionally, since `shiftAtᵗ (suc X) = extᵗ (shiftAtᵗ X)`.
shift-∀-inv : ∀ X A {B} → renameᵗ (shiftAtᵗ X) A ≡ `∀ B
  → Σ[ A₁ ∈ Ty ] ((A ≡ `∀ A₁) × (renameᵗ (shiftAtᵗ (suc X)) A₁ ≡ B))
shift-∀-inv X (`∀ A) refl = A , refl , refl
shift-∀-inv X (` Y) ()
shift-∀-inv X `ℕ ()
shift-∀-inv X `𝔹 ()
shift-∀-inv X (A ⇒ B) ()

-- The crossing itself travels past the new `bind` — and now nothing
-- happens to its ADDRESS, because a `∀` binds no address.  Only the
-- name shifts.
pop-⇑ : ∀ {Δₑ Δᵢ} → Δₑ ▷ X := α ⇒ Δᵢ → ⇑ᶜ Δₑ ▷ suc X := α ⇒ ⇑ᶜ Δᵢ
pop-⇑ {Δₑ = Ss ∥ Bs} {Δᵢ = Ss′ ∥ Bs′} p with pop-base p
pop-⇑ {Δₑ = Ss ∥ Bs} {Δᵢ = Ss′ ∥ .Bs} p | refl = pop-bind p

∋a-⇑ : ∀ {Sg Ss Bs α} → Sg ∣ (Ss ∥ Bs) ∋a α → Sg ∣ (bind ∷ Ss ∥ Bs) ∋a α
∋a-⇑ = ∋a-restk

notasgn-⇑ : NotAssigned Δ α → NotAssigned (⇑ᶜ Δ) α
notasgn-⇑ na (n-skip-bind q) = na q

------------------------------------------------------------------------
-- The elementwise view, before normalization
------------------------------------------------------------------------
-- As in `arrElts-typing` the SOURCE is carried as an equation: the
-- crossing rules state their types as renames, which the unifier
-- cannot match against a `∀`.

consAllE-inv : ∀ {es q Es}
  → consAllE (just es) q ≡ just Es
  → Σ[ Es′ ∈ List ConvElt ] ((q ≡ just Es′) × (Es ≡ es ++ Es′))
consAllE-inv {q = just Es′} refl = Es′ , refl , refl
consAllE-inv {q = nothing} ()

allElts-typing : ∀ {Sg Δᵢ Δ c S A₀ A′ Es}
  → Sg ∣ Δᵢ ⊢ c ∶ S ⇝ `∀ A′ ⊣ Δ
  → S ≡ `∀ A₀
  → allElts (elts c) ≡ just Es
  → Sg ∣ ⇑ᶜ Δᵢ ⊢ attach Es A′ ∶ A₀ ⇝ A′ ⊣ ⇑ᶜ Δ

allElts-typing (conv-id wf) refl refl = conv-id (wf-∀-inv wf)

-- an `all` element contributes its own nested conversion
allElts-typing {A′ = A′} (conv-cons (conv-all {s = s} ⊢s) tl) refl eq
  with consAllE-inv eq
allElts-typing {A′ = A′} (conv-cons (conv-all {s = s} ⊢s) tl) refl eq
  | Es′ , eq′ , refl with allElts-typing tl refl eq′
allElts-typing {A′ = A′} (conv-cons (conv-all {s = s} ⊢s) tl) refl eq
  | Es′ , eq′ , refl | ih
  rewrite attach-++ˡ s Es′ A′ = ⧺-typing ⊢s ih

-- a `hide`: itself, with its name and address moved past the `bind`
allElts-typing {A′ = A′}
  (conv-cons (conv-hide {α = α} {A = A} {X = X} sc wf p na) tl) refl eq
  with consAllE-inv eq
allElts-typing {A′ = A′}
  (conv-cons (conv-hide {α = α} {A = A} {X = X} sc wf p na) tl) refl eq
  | Es′ , eq′ , refl with allElts-typing tl refl eq′
allElts-typing {A₀ = A₀} {A′ = A′}
  (conv-cons (conv-hide {α = α} {A = A} {X = X} sc wf p na) tl) refl eq
  | Es′ , eq′ , refl | ih
  rewrite attach-++ (hide (suc X) α ∷ []) Es′
            (renameᵗ (shiftAtᵗ (suc X)) A₀) A′ =
  conv-cons (conv-hide (∋a-⇑ sc) (wf-∀-inv wf) (pop-⇑ p) (notasgn-⇑ na)) ih

-- a `show`: the source is a SHIFT, so the `∀` is recovered by
-- inversion
allElts-typing {A′ = A′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  with shift-∀-inv X A seq
allElts-typing {A′ = A′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  | A₁ , refl , refl with consAllE-inv eq
allElts-typing {A′ = A′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  | A₁ , refl , refl | Es′ , eq′ , refl with allElts-typing tl refl eq′
allElts-typing {A′ = A′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  | A₁ , refl , refl | Es′ , eq′ , refl | ih
  rewrite attach-++ (show (suc X) α ∷ []) Es′ A₁ A′ =
  conv-cons (conv-show (∋a-⇑ sc) (wf-∀-inv wf) (pop-⇑ p) (notasgn-⇑ na)) ih

-- the sealing elements and `↦` are not view-accepted
allElts-typing (conv-cons (conv-seal rep rd p) tl) refl ()
allElts-typing (conv-cons (conv-unseal rep rd p na) tl) () eq
allElts-typing (conv-cons (conv-fun ⊢s ⊢t) tl) () eq

------------------------------------------------------------------------
-- `allView` itself: the component is normalized
------------------------------------------------------------------------

allView-inv : ∀ {c d} → allView c ≡ just d
  → Σ[ Es ∈ List ConvElt ] Σ[ B ∈ Ty ]
      ((allElts (elts c) ≡ just Es) × (target c ≡ `∀ B)
       × (d ≡ normalize (attach Es B)))
allView-inv {c = c} eq with allElts (elts c) | target c
allView-inv {c = c} refl | just Es | `∀ B = Es , B , refl , refl , refl
allView-inv {c = c} () | just Es | ` X
allView-inv {c = c} () | just Es | `ℕ
allView-inv {c = c} () | just Es | `𝔹
allView-inv {c = c} () | just Es | C ⇒ D
allView-inv {c = c} () | nothing | _

allView-typing : ∀ {Sg Δᵢ Δ c A₀ A′ d}
  → NameFn Δ
  → Sg ∣ Δᵢ ⊢ c ∶ `∀ A₀ ⇝ `∀ A′ ⊣ Δ
  → allView c ≡ just d
  → (Sg ∣ ⇑ᶜ Δᵢ ⊢ d ∶ A₀ ⇝ A′ ⊣ ⇑ᶜ Δ) × NF d
allView-typing {c = c} nf conv eq with allView-inv {c = c} eq
allView-typing {c = c} nf conv eq | Es , B , eqE , teq , refl
  with trans (sym teq) (conv-target conv)
allView-typing {c = c} nf conv eq | Es , B , eqE , teq , refl | refl
  with allElts-typing conv refl eqE
allView-typing {c = c} {A′ = A′} nf conv eq
  | Es , B , eqE , teq , refl | refl | ty =
    preserve-↠ (namefn-bind nf) ty (normalize-↠ (attach Es A′))
  , normalize-NF (attach Es A′)

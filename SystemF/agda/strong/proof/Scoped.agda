module strong.proof.Scoped where

-- Strong System F v8 — the context invariant the notes call `Γ ok`:
-- every name assignment names an address that is IN SCOPE.
--
-- This is exactly what the repair of 2026-09-15 bought.  Before it,
-- `conv-show` could introduce an assignment to an address nothing had
-- bound, so the invariant was not preservable and `⌊·⌋ → ⊢ᴿ` was out
-- of reach.  Now all four atomic elements scope their address —
-- `seal`/`unseal` through `∋r`, `hide`/`show` through `∋a` — and the
-- invariant travels along the interior walk.
--
-- Two things fall out.  `quote-wfᴿ`, which `TyBeta` and `TyWrap` need
-- to build their `ν`; and freshness of the store's next level, which
-- `Alloc` needs, since `Fresh (length Σ)` IS `∋a` read at a level.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.proof.ArrTyping using (pop-renames)
open import strong.proof.AllTyping using (∋a-⇑)
open import strong.Terms
open import strong.proof.PreserveAlloc using
  (Fresh; fr-lvl; fr-bnd; fr-bse; FreshStk; fs-[]; fs-bind; fs-asgn;
   FreshElt; fe-seal; fe-unseal; fe-hide; fe-show; fe-fun; fe-all;
   FreshConv; fc-id; fc-cons;
   FreshM; fm-`; fm-$; fm-#; fm-⊕; fm-ƛ; fm-·; fm-Λ; fm-•[]; fm-ν; fm-⟨⟩;
   fresh-of-∋a; fresh-of-∋r)

private
  variable
    Sg : Store
    Δ Δᵢ Δₑ : Ctxᵗ
    Ss Ss′ : List StackEnt
    Bs : List BaseEnt
    A B : Ty
    R : RepTy
    X : ℕ
    α : Addr

------------------------------------------------------------------------
-- The invariant
------------------------------------------------------------------------

Scoped : Store → Ctxᵗ → Set
Scoped Sg Δ = ∀ {X α} → Δ ∋n X := α → Sg ∣ Δ ∋a α

scoped-[] : ∀ {Sg Bs} → Scoped Sg ([] ∥ Bs)
scoped-[] ()

-- a `bind` names the address it binds, and every older name shifts
-- with its address
scoped-bind : ∀ {Sg Ss Bs} → Scoped Sg (Ss ∥ Bs)
  → Scoped Sg (bind ∷ Ss ∥ Bs)
scoped-bind sc n-here-bind = a-here-bind
scoped-bind sc (n-skip-bind-b p) = ∋a-⇑ (sc p)
scoped-bind sc (n-skip-bind-l p) = ∋a-⇑ (sc p)
scoped-bind sc (n-skip-bind-e p) = ∋a-⇑ (sc p)

-- an `asgn` is scoped exactly when its own address is
scoped-asgn : ∀ {Sg Ss Bs α} → Sg ∣ (Ss ∥ Bs) ∋a α → Scoped Sg (Ss ∥ Bs)
  → Scoped Sg (asgn α ∷ Ss ∥ Bs)
scoped-asgn a sc n-here-asgn = ∋a-push pop-here a
scoped-asgn a sc (n-skip-asgn p) = ∋a-push pop-here (sc p)

-- Going under a `bind` shifts a name AND its address, so both moves
-- are invertible — which is what lets the invariant come back out.
∋n-⇑ : ∀ {Ss Bs Y β} → (Ss ∥ Bs) ∋n Y := β
  → (bind ∷ Ss ∥ Bs) ∋n suc Y := ⇑ᵃ β
∋n-⇑ {β = lvl ℓ} r = n-skip-bind-l r
∋n-⇑ {β = bnd i} r = n-skip-bind-b r
∋n-⇑ {β = bse j} r = n-skip-bind-e r

∋a-unbind : ∀ {Sg Ss Bs β} → Sg ∣ (bind ∷ Ss ∥ Bs) ∋a ⇑ᵃ β
  → Sg ∣ (Ss ∥ Bs) ∋a β
∋a-unbind {β = lvl ℓ} (a-lvl l) = a-lvl l
∋a-unbind {β = bnd i} (a-skip-bind r) = r
∋a-unbind {β = bse j} r = ∋a-restk r

scoped-unbind : ∀ {Sg Ss Bs} → Scoped Sg (bind ∷ Ss ∥ Bs)
  → Scoped Sg (Ss ∥ Bs)
scoped-unbind s q = ∋a-unbind (s (∋n-⇑ q))

------------------------------------------------------------------------
-- A representation of a well-formed type is well formed
------------------------------------------------------------------------

quote-wfᴿ : Scoped Sg Δ → Sg ∣ Δ ⊢⌊ A ⌋ R → Sg ∣ Δ ⊢ᴿ R
quote-wfᴿ sc (quote-var n) = wfᴿ-var (sc n)
quote-wfᴿ sc quote-ℕ = wfᴿ-ℕ
quote-wfᴿ sc quote-𝔹 = wfᴿ-𝔹
quote-wfᴿ sc (quote-⇒ a b) = wfᴿ-⇒ (quote-wfᴿ sc a) (quote-wfᴿ sc b)
quote-wfᴿ sc (quote-∀ a) = wfᴿ-∀ (quote-wfᴿ (scoped-bind sc) a)

------------------------------------------------------------------------
-- The invariant travels along the interior walk
------------------------------------------------------------------------
-- Going inward, an element either REMOVES an assignment (`seal`,
-- `hide`), where every surviving name lifts back out by `pop-renames`
-- and its address comes along by `∋a-pop`; or ADDS one (`unseal`,
-- `show`), where the new name's address is scoped by the rule's own
-- premise — `∋r` for `unseal`, `∋a` for `show`.

pop-scoped : ∀ {Sg Δₑ Δᵢ X α} → Δₑ ▷ X := α ⇒ Δᵢ
  → Scoped Sg Δₑ → Scoped Sg Δᵢ
pop-scoped p sc q = ∋a-pop p (sc (pop-renames p q))

push-scoped : ∀ {Sg Δₑ Δᵢ X α} → Δᵢ ▷ X := α ⇒ Δₑ
  → Sg ∣ Δₑ ∋a α → Scoped Sg Δₑ → Scoped Sg Δᵢ
push-scoped pop-here a sc = scoped-asgn a sc
push-scoped (pop-bind-b p) a sc =
  scoped-bind (push-scoped p (∋a-unbind a) (scoped-unbind sc))
push-scoped (pop-bind-l p) a sc =
  scoped-bind (push-scoped p (∋a-unbind a) (scoped-unbind sc))
push-scoped (pop-bind-e p) a sc =
  scoped-bind (push-scoped p (∋a-restk a) (scoped-unbind sc))

mutual
  convElt-scoped : ∀ {Sg Δᵢ Δₑ ĉ A B} → Sg ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δₑ
    → Scoped Sg Δₑ → Scoped Sg Δᵢ
  convElt-scoped (conv-seal rep rd p) sc = pop-scoped p sc
  convElt-scoped (conv-unseal rep rd p na) sc =
    push-scoped p (∋a-pop p (∋r→∋a rep)) sc
  convElt-scoped (conv-hide a wf p na) sc = pop-scoped p sc
  convElt-scoped (conv-show a wf p na) sc = push-scoped p a sc
  convElt-scoped (conv-fun ⊢s ⊢t) sc = conv-scoped ⊢t sc
  convElt-scoped (conv-all ⊢s) sc =
    scoped-unbind (conv-scoped ⊢s (scoped-bind sc))

  conv-scoped : ∀ {Sg Δᵢ Δₑ c A B} → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δₑ
    → Scoped Sg Δₑ → Scoped Sg Δᵢ
  conv-scoped (conv-id wf) sc = sc
  conv-scoped (conv-cons hd tl) sc = convElt-scoped hd (conv-scoped tl sc)

------------------------------------------------------------------------
-- A scoped context's assignments avoid the store's next level
------------------------------------------------------------------------

scoped-freshStk : ∀ {Sg Ss Bs} → Scoped Sg (Ss ∥ Bs)
  → FreshStk (length Sg) Ss
scoped-freshStk {Ss = []} sc = fs-[]
scoped-freshStk {Ss = bind ∷ Ss} sc =
  fs-bind (scoped-freshStk (scoped-unbind sc))
scoped-freshStk {Ss = asgn α ∷ Ss} sc =
  fs-asgn (fresh-of-∋a (sc n-here-asgn))
          (scoped-freshStk (λ q → ∋a-pop pop-here (sc (n-skip-asgn q))))

------------------------------------------------------------------------
-- And so does a well-typed term
------------------------------------------------------------------------
-- Every address a conversion mentions is in scope, by the premise of
-- whichever rule introduced it, so none of them is the store's next
-- level.  The term case is then a plain structural walk.

mutual
  convElt-fresh : ∀ {Sg Δᵢ Δₑ ĉ A B} → Sg ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δₑ
    → FreshElt (length Sg) ĉ
  convElt-fresh (conv-seal rep rd p) = fe-seal (fresh-of-∋r rep)
  convElt-fresh (conv-unseal rep rd p na) = fe-unseal (fresh-of-∋r rep)
  convElt-fresh (conv-hide a wf p na) = fe-hide (fresh-of-∋a a)
  convElt-fresh (conv-show a wf p na) = fe-show (fresh-of-∋a a)
  convElt-fresh (conv-fun ⊢s ⊢t) = fe-fun (conv-fresh ⊢s) (conv-fresh ⊢t)
  convElt-fresh (conv-all ⊢s) = fe-all (conv-fresh ⊢s)

  conv-fresh : ∀ {Sg Δᵢ Δₑ c A B} → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δₑ
    → FreshConv (length Sg) c
  conv-fresh (conv-id wf) = fc-id
  conv-fresh (conv-cons hd tl) = fc-cons (convElt-fresh hd) (conv-fresh tl)

typing-fresh : ∀ {Sg Δ Γ M A} → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A → FreshM (length Sg) M
typing-fresh (⊢` x) = fm-`
typing-fresh ⊢$ = fm-$
typing-fresh ⊢# = fm-#
typing-fresh (⊢⊕ m n) = fm-⊕ (typing-fresh m) (typing-fresh n)
typing-fresh (⊢ƛ wf body) = fm-ƛ (typing-fresh body)
typing-fresh (⊢· l m) = fm-· (typing-fresh l) (typing-fresh m)
typing-fresh (⊢Λ v body) = fm-Λ (typing-fresh body)
typing-fresh (⊢•[] l wf) = fm-•[] (typing-fresh l)
typing-fresh (⊢ν wfR body) = fm-ν (typing-fresh body)
typing-fresh (⊢⟨⟩ nf body conv) =
  fm-⟨⟩ (typing-fresh body) (conv-fresh conv)

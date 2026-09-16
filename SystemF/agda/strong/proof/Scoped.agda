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

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_<_ to _<ᵗ_)
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
open import strong.proof.Interior using (pop-base)
open import strong.Terms
open import strong.proof.Flat using (NoBinds; nb-[]; nb-asgn)
open import strong.proof.PreserveAlloc using
  (Fresh; fr-lvl; fr-bse; FreshStk; fs-[]; fs-bind; fs-asgn;
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
-- A `bind` adds a NAME and no address, so it neither creates nor
-- disturbs an assignment — one clause where there were four.
scoped-bind : ∀ {Sg Ss Bs} → Scoped Sg (Ss ∥ Bs)
  → Scoped Sg (bind ∷ Ss ∥ Bs)
scoped-bind sc (n-skip-bind p) = ∋a-restk (sc p)

scoped-unbind : ∀ {Sg Ss Bs} → Scoped Sg (bind ∷ Ss ∥ Bs)
  → Scoped Sg (Ss ∥ Bs)
scoped-unbind sc p = ∋a-restk (sc (n-skip-bind p))

-- an `asgn` is scoped exactly when its own address is
scoped-asgn : ∀ {Sg Ss Bs α} → Sg ∣ (Ss ∥ Bs) ∋a α → Scoped Sg (Ss ∥ Bs)
  → Scoped Sg (asgn α ∷ Ss ∥ Bs)
scoped-asgn a sc n-here-asgn = ∋a-restk a
scoped-asgn a sc (n-skip-asgn p) = ∋a-restk (sc p)

------------------------------------------------------------------------
-- A representation of a well-formed type is well formed
------------------------------------------------------------------------

-- Every `∀`-bound variable in the stack is bound by one of the `n`
-- binders passed so far.  At a REDEX the ambient stack has no binds at
-- all, so this starts at zero.
BindsBelow : ℕ → List StackEnt → Set
BindsBelow n Ss = ∀ {X i} → Ss ∋b X at i → i <ᵗ n

bb-bind : ∀ {n Ss} → BindsBelow n Ss → BindsBelow (suc n) (bind ∷ Ss)
bb-bind bb b-here = s≤s z≤n
bb-bind bb (b-bind p) = s≤s (bb p)

-- a FLAT context has no binds at all, so nothing is `∀`-bound in it
flat-bindsBelow : ∀ {Ss} → NoBinds Ss → BindsBelow zero Ss
flat-bindsBelow (nb-asgn nb) (b-asgn p) = flat-bindsBelow nb p

quote-wfᴿ : ∀ {Sg Γ A R} → Scoped Sg Γ → BindsBelow zero (stk Γ)
  → Sg ∣ Γ ⊢⌊ A ⌋ R → Sg ∣ Γ ⊢ᴿ R
quote-wfᴿ sc bb q = go zero sc bb q
  where
  go : ∀ {Sg Ss Bs A R} n → Scoped Sg (Ss ∥ Bs) → BindsBelow n Ss
     → Sg ∣ (Ss ∥ Bs) ⊢⌊ A ⌋ R → Sg ∣ (Ss ∥ Bs) ⊢ᴿ[ n ] R
  go n sc′ bb′ (quote-var x) = wfᴿ-var (sc′ x)
  go n sc′ bb′ (quote-bv x) = wfᴿ-bv (bb′ x)
  go n sc′ bb′ quote-ℕ = wfᴿ-ℕ
  go n sc′ bb′ quote-𝔹 = wfᴿ-𝔹
  go n sc′ bb′ (quote-⇒ a b) = wfᴿ-⇒ (go n sc′ bb′ a) (go n sc′ bb′ b)
  go n sc′ bb′ (quote-∀ a) =
    wfᴿ-∀ (wfᴿ-restk′ (go (suc n) (scoped-bind sc′) (bb-bind bb′) a))
    where
    wfᴿ-restk′ : ∀ {Sg Ss Ss′ Bs m R} → Sg ∣ (Ss ∥ Bs) ⊢ᴿ[ m ] R
      → Sg ∣ (Ss′ ∥ Bs) ⊢ᴿ[ m ] R
    wfᴿ-restk′ (wfᴿ-var a) = wfᴿ-var (∋a-restk a)
    wfᴿ-restk′ (wfᴿ-bv lt) = wfᴿ-bv lt
    wfᴿ-restk′ wfᴿ-ℕ = wfᴿ-ℕ
    wfᴿ-restk′ wfᴿ-𝔹 = wfᴿ-𝔹
    wfᴿ-restk′ (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-restk′ a) (wfᴿ-restk′ b)
    wfᴿ-restk′ (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-restk′ a)

------------------------------------------------------------------------
-- The invariant travels along the interior walk
------------------------------------------------------------------------

pop-scoped : ∀ {Sg Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → Scoped Sg (Ss ∥ Bs) → Scoped Sg (Ss′ ∥ Bs)
pop-scoped p sc q = ∋a-restk (sc (pop-renames p q))

push-scoped : ∀ {Sg Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → Sg ∣ (Ss′ ∥ Bs) ∋a α → Scoped Sg (Ss′ ∥ Bs) → Scoped Sg (Ss ∥ Bs)
push-scoped pop-here a sc = scoped-asgn a sc
push-scoped (pop-bind p) a sc =
  scoped-bind (push-scoped p (∋a-restk a) (scoped-unbind sc))

mutual
  convElt-scoped : ∀ {Sg Δᵢ Δₑ ĉ A B} → Sg ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δₑ
    → Scoped Sg Δₑ → Scoped Sg Δᵢ
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ Bsₑ} (conv-seal rep rd p) sc
    with pop-base p
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ .Bsᵢ} (conv-seal rep rd p) sc
    | refl = pop-scoped p sc
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ Bsₑ} (conv-unseal rep rd p na) sc
    with pop-base p
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ .Bsᵢ} (conv-unseal rep rd p na) sc
    | refl = push-scoped p (∋a-restk (∋r→∋a rep)) sc
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ Bsₑ} (conv-hide a wf p na) sc
    with pop-base p
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ .Bsᵢ} (conv-hide a wf p na) sc
    | refl = pop-scoped p sc
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ Bsₑ} (conv-show a wf p na) sc
    with pop-base p
  convElt-scoped {Δᵢ = Ssᵢ ∥ Bsᵢ} {Δₑ = Ssₑ ∥ .Bsᵢ} (conv-show a wf p na) sc
    | refl = push-scoped p a sc
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
          (scoped-freshStk (λ q → ∋a-restk (sc (n-skip-asgn q))))

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

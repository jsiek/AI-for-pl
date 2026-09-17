module strong.proof.PreserveAlloc where

-- Strong System F v8 — discharging a `ν` into the global store.
--
-- `Alloc` (strong.Reduction) reads
--
--   Σ ∣ Δ ⊢ ν R ∙ M —→ M [ lvl (length Σ) ]ᵃᴹ ⊣ (Σ ∷ʳ R)
--
-- so preservation for it is a SUBSTITUTION lemma for the base address
-- family: the body lives one base entry up (⊢ν pushes `nuBind R` and
-- shifts the stack by `⤒`), and `σ = instᵉ₀ (lvl (length Σ))` sends the
-- ν's own address `bse 0` to the fresh level and un-shifts everything
-- else.  `substStk σ (⤒ Ss) ≡ Ss` is the pivot.
--
-- The development mirrors proof.AddrWeaken one-for-one: a record
-- `Substsᵇ` of closure properties over the lookups, closed under the
-- stack binders (`sub-bind`, `sub-asgn`, `sub-stk`) and under a base
-- binder (`sub-ext`), lifted to `⊢ᵗ`, `⊢ᴿ`, `⇓`, the pop judgment,
-- `NotAssigned`, conversion typing, and finally to terms (`⊢-inst`).
--
-- ONE THING IS GENUINELY DIFFERENT FROM A RENAMING.  σ is NOT
-- injective: it maps `bse 0` and `lvl (length Σ)` to the same address,
-- so a conversion that was a NORMAL FORM can acquire a redex, and
-- `⊢Λ`'s `Value V` premise then fails.  σ IS injective away from
-- `lvl (length Σ)`, so everything goes through under a freshness
-- hypothesis `Fresh L` (L = length Σ) on the addresses that actually
-- occur — in the conversions of the term, and in the crossing
-- assignments of the ambient context.
--
-- WHAT THE ADDRESS SPLIT BOUGHT.  With `bnd` gone (a `∀` binds a type
-- VARIABLE, `RepTy`'s `ᵛ, not an address) an address is a level or a
-- base index and NOTHING ELSE.  So the v7 side condition "σ never
-- produces a bound stack address" is vacuous and its whole plumbing —
-- `NoBnd`, the `AddrOK` view on every lookup, the three-way `pop-bind`
-- and `n-skip-bind` reconstructions, the commutation of a base
-- substitution with a stack renaming — is gone.  What is left is the
-- ordinary substitution lemma plus freshness.
--
-- WHY THE FRESHNESS HYPOTHESIS IS STATED AND NOT DERIVED.  `Fresh
-- (length Σ)` is exactly "in scope in Σ" for a level, so it is a
-- reading of `∋a`, which every crossing now carries (§20).  Deriving it
-- from typing is proof.Scoped's job; here it is a premise.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; map; length)
open import Data.List.Properties using (map-++)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.proof.Flat
open Flatn
open import strong.proof.StoreWeaken using (⊢-snoc; storeOk-snoc)
open import strong.proof.AddrWeaken using
  (Renamesᵇ; ren-wk; convElt-base; conv-base)
open Renamesᵇ using (ren-a; ren-r)
open import strong.proof.InertRenaming using (suc-injᵉ)

private
  variable
    Sg : Store
    L n : ℕ
    σ : SubstAddr
    Γ Γ′ : Ctxᵗ
    Ss Ss′ : List StackEnt
    Bs Bs′ : List BaseEnt
    A B C D : Ty
    R T : RepTy
    X : ℕ
    α β : Addr
    c s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- 1.  Levels: the fresh one is the last, and it is not there yet
------------------------------------------------------------------------

∋ˡ-last : ∀ Σ {R} → (Σ ∷ʳ R) ∋ˡ length Σ := R
∋ˡ-last [] = l-here
∋ˡ-last (S ∷ Σ) = l-there (∋ˡ-last Σ)

-- The fresh level is not in the store yet — what §20 turns on.
∋ˡ-fresh : ∀ {Σ : Store} {R} → Σ ∋ˡ length Σ := R → ⊥
∋ˡ-fresh {[]} ()
∋ˡ-fresh {S ∷ Σ} (l-there p) = ∋ˡ-fresh p

------------------------------------------------------------------------
-- 2.  The store stays well formed
------------------------------------------------------------------------
-- Immediate: over a flat context a representation is base-closed, which
-- is exactly the grading `StoreOk` asks of the new entry.

alloc-storeOk : ∀ {Sg Δ R} → StoreOk Sg → Flat Δ → Sg ∣ Δ ⊢ᴿ R
  → StoreOk (Sg ∷ʳ R)
alloc-storeOk sok fl wf = storeOk-snoc sok (flat-closed fl wf)

------------------------------------------------------------------------
-- 3.  Address disequalities, and what a base shift cannot produce
------------------------------------------------------------------------
-- Two forms, so two disequalities; and `renᵃᵉ suc` fixes a level and
-- never lands on `bse zero`, which is all §7 needs of it.

lvl≢bse : ∀ {ℓ j} → lvl ℓ ≡ bse j → ⊥
lvl≢bse ()

bse≢lvl : ∀ {j ℓ} → bse j ≡ lvl ℓ → ⊥
bse≢lvl ()

shift-lvl : ∀ {α ℓ} → renᵃᵉ suc α ≡ lvl ℓ → α ≡ lvl ℓ
shift-lvl {lvl m} refl = refl
shift-lvl {bse j} ()

shift-bse0 : ∀ {α} → renᵃᵉ suc α ≡ bse zero → ⊥
shift-bse0 {lvl m} ()
shift-bse0 {bse j} ()

------------------------------------------------------------------------
-- 4.  The commutations
------------------------------------------------------------------------
-- The ext/base-shift square: UNCONDITIONAL, since `extsᵃᵉ` is defined
-- by exactly this shift.  `∀ᴿ` binds a type variable, so a base
-- substitution passes through it unextended.

substAddrᵉ-ext : ∀ σ α
  → substAddrᵉ (extsᵃᵉ σ) (renᵃᵉ suc α) ≡ renᵃᵉ suc (substAddrᵉ σ α)
substAddrᵉ-ext σ (lvl ℓ) = refl
substAddrᵉ-ext σ (bse j) = refl

substᴿᵉ-ext : ∀ σ R → substᴿᵉ (extsᵃᵉ σ) (⇑ᴿᵉ R) ≡ ⇑ᴿᵉ (substᴿᵉ σ R)
substᴿᵉ-ext σ (`ᵃ α) = cong `ᵃ_ (substAddrᵉ-ext σ α)
substᴿᵉ-ext σ (`ᵛ i) = refl
substᴿᵉ-ext σ `ℕᴿ = refl
substᴿᵉ-ext σ `𝔹ᴿ = refl
substᴿᵉ-ext σ (R ⇒ᴿ T) = cong₂ _⇒ᴿ_ (substᴿᵉ-ext σ R) (substᴿᵉ-ext σ T)
substᴿᵉ-ext σ (`∀ᴿ R) = cong `∀ᴿ (substᴿᵉ-ext σ R)

-- THE PIVOT.  `instᵉ₀` un-shifts the base exactly.
inst-unshiftᵃ : ∀ β α → substAddrᵉ (instᵉ₀ β) (renᵃᵉ suc α) ≡ α
inst-unshiftᵃ β (lvl ℓ) = refl
inst-unshiftᵃ β (bse j) = refl

inst-unshiftᴿ : ∀ β R → substᴿᵉ (instᵉ₀ β) (⇑ᴿᵉ R) ≡ R
inst-unshiftᴿ β (`ᵃ α) = cong `ᵃ_ (inst-unshiftᵃ β α)
inst-unshiftᴿ β (`ᵛ i) = refl
inst-unshiftᴿ β `ℕᴿ = refl
inst-unshiftᴿ β `𝔹ᴿ = refl
inst-unshiftᴿ β (R ⇒ᴿ T) =
  cong₂ _⇒ᴿ_ (inst-unshiftᴿ β R) (inst-unshiftᴿ β T)
inst-unshiftᴿ β (`∀ᴿ R) = cong `∀ᴿ (inst-unshiftᴿ β R)

------------------------------------------------------------------------
-- 5.  The stack travels
------------------------------------------------------------------------

substStk : SubstAddr → List StackEnt → List StackEnt
substStk σ [] = []
substStk σ (bind ∷ Ss) = bind ∷ substStk σ Ss
substStk σ (asgn α ∷ Ss) = asgn (substAddrᵉ σ α) ∷ substStk σ Ss

substStk-ext : ∀ σ Ss → substStk (extsᵃᵉ σ) (⤒ Ss) ≡ ⤒ (substStk σ Ss)
substStk-ext σ [] = refl
substStk-ext σ (bind ∷ Ss) = cong (bind ∷_) (substStk-ext σ Ss)
substStk-ext σ (asgn α ∷ Ss)
  rewrite substAddrᵉ-ext σ α | substStk-ext σ Ss = refl

inst-unshiftˢ : ∀ β Ss → substStk (instᵉ₀ β) (⤒ Ss) ≡ Ss
inst-unshiftˢ β [] = refl
inst-unshiftˢ β (bind ∷ Ss) = cong (bind ∷_) (inst-unshiftˢ β Ss)
inst-unshiftˢ β (asgn α ∷ Ss)
  rewrite inst-unshiftᵃ β α | inst-unshiftˢ β Ss = refl

------------------------------------------------------------------------
-- 6.  Freshness: the level L occurs nowhere
------------------------------------------------------------------------

data Fresh (L : ℕ) : Addr → Set where
  fr-lvl : ∀ {ℓ} → ¬ (ℓ ≡ L) → Fresh L (lvl ℓ)
  fr-bse : ∀ {j} → Fresh L (bse j)

fresh-⇑ᵃᵉ : Fresh L α → Fresh L (renᵃᵉ suc α)
fresh-⇑ᵃᵉ (fr-lvl ne) = fr-lvl ne
fresh-⇑ᵃᵉ fr-bse = fr-bse

data FreshStk (L : ℕ) : List StackEnt → Set where
  fs-[]   : FreshStk L []
  fs-bind : ∀ {Ss} → FreshStk L Ss → FreshStk L (bind ∷ Ss)
  fs-asgn : ∀ {α Ss} → Fresh L α → FreshStk L Ss
          → FreshStk L (asgn α ∷ Ss)

freshStk-⤒ : ∀ {L Ss} → FreshStk L Ss → FreshStk L (⤒ Ss)
freshStk-⤒ fs-[] = fs-[]
freshStk-⤒ (fs-bind fs) = fs-bind (freshStk-⤒ fs)
freshStk-⤒ (fs-asgn f fs) = fs-asgn (fresh-⇑ᵃᵉ f) (freshStk-⤒ fs)

mutual
  data FreshElt (L : ℕ) : ConvElt → Set where
    fe-seal   : ∀ {X α} → Fresh L α → FreshElt L (seal X α)
    fe-unseal : ∀ {X α} → Fresh L α → FreshElt L (unseal X α)
    fe-hide   : ∀ {X α} → Fresh L α → FreshElt L (hide X α)
    fe-show   : ∀ {X α} → Fresh L α → FreshElt L (show X α)
    fe-fun    : ∀ {s t} → FreshConv L s → FreshConv L t
              → FreshElt L (s ↦ t)
    fe-all    : ∀ {s} → FreshConv L s → FreshElt L (all s)

  data FreshConv (L : ℕ) : Conv → Set where
    fc-id   : ∀ {A} → FreshConv L (id A)
    fc-cons : ∀ {ĉ c} → FreshElt L ĉ → FreshConv L c
            → FreshConv L (ĉ ∷ᶜ c)

data FreshM (L : ℕ) : Term → Set where
  fm-`   : ∀ {x} → FreshM L (` x)
  fm-$   : ∀ {n} → FreshM L ($ n)
  fm-#   : ∀ {b} → FreshM L (# b)
  fm-⊕   : ∀ {M N p} → FreshM L M → FreshM L N → FreshM L (M ⊕[ p ] N)
  fm-ƛ   : ∀ {A N} → FreshM L N → FreshM L (ƛ A ∙ N)
  fm-·   : ∀ {M N} → FreshM L M → FreshM L N → FreshM L (M · N)
  fm-Λ   : ∀ {V} → FreshM L V → FreshM L (Λ V)
  fm-•[] : ∀ {M B A} → FreshM L M → FreshM L (M • B [ A ])
  fm-ν   : ∀ {R M} → FreshM L M → FreshM L (ν R ∙ M)
  fm-⟨⟩  : ∀ {M c} → FreshM L M → FreshConv L c → FreshM L (M ⟨ c ⟩)

-- Away from `lvl L` the substitution IS injective; this is the only
-- thing the normal-form argument needs.
InjF : ℕ → SubstAddr → Set
InjF L σ = ∀ {α β} → Fresh L α → Fresh L β
         → substAddrᵉ σ α ≡ substAddrᵉ σ β → α ≡ β

------------------------------------------------------------------------
-- 7.  Injectivity away from the fresh level
------------------------------------------------------------------------
-- σ IS non-injective: `instᵉ₀ (lvl L)` sends `bse 0` and `lvl L` to the
-- same address.  That is the ONLY collision, so on `Fresh L` addresses
-- the map is injective, and `extsᵃᵉ` preserves the property.

inj-inst₀ : ∀ L → InjF L (instᵉ₀ (lvl L))
inj-inst₀ L {lvl ℓ} {lvl m} f g eq = eq
inj-inst₀ L {lvl ℓ} {bse zero} (fr-lvl ne) g eq = ⊥-elim (ne (lvl-inj eq))
inj-inst₀ L {lvl ℓ} {bse (suc j)} f g ()
inj-inst₀ L {bse zero} {lvl m} f (fr-lvl ne) eq =
  ⊥-elim (ne (sym (lvl-inj eq)))
inj-inst₀ L {bse zero} {bse zero} f g eq = refl
inj-inst₀ L {bse zero} {bse (suc j)} f g ()
inj-inst₀ L {bse (suc i)} {lvl m} f g ()
inj-inst₀ L {bse (suc i)} {bse zero} f g ()
inj-inst₀ L {bse (suc i)} {bse (suc j)} f g eq =
  cong (λ k → bse (suc k)) (bse-inj eq)

-- `extsᵃᵉ σ` sends `bse (suc j)` to `renᵃᵉ suc (σ j)`, and a base
-- shift is injective and form-preserving (§3), so the inner
-- injectivity fires on the mixed rows.
inj-ext : ∀ {L σ} → InjF L σ → InjF L (extsᵃᵉ σ)
inj-ext inj {lvl ℓ} {lvl m} f g eq = eq
inj-ext inj {lvl ℓ} {bse zero} f g ()
inj-ext inj {lvl ℓ} {bse (suc j)} f g eq =
  ⊥-elim (lvl≢bse (inj f fr-bse (sym (shift-lvl (sym eq)))))
inj-ext inj {bse zero} {lvl m} f g ()
inj-ext inj {bse zero} {bse zero} f g eq = refl
inj-ext inj {bse zero} {bse (suc j)} f g eq =
  ⊥-elim (shift-bse0 (sym eq))
inj-ext inj {bse (suc i)} {lvl m} f g eq =
  ⊥-elim (bse≢lvl (inj fr-bse g (shift-lvl eq)))
inj-ext inj {bse (suc i)} {bse zero} f g eq = ⊥-elim (shift-bse0 eq)
inj-ext inj {bse (suc i)} {bse (suc j)} f g eq =
  cong (λ k → bse (suc k)) (bse-inj (inj fr-bse fr-bse (suc-injᵉ eq)))

------------------------------------------------------------------------
-- 8.  Freshness travels along a conversion
------------------------------------------------------------------------
-- A crossing pops an assignment (whose address was already in the
-- stack) or pushes one (whose address the ELEMENT carries), so the
-- stack's freshness is exactly the conversion's.  Passing a `bind`
-- moves no address, so both directions are structural.

pop-fresh : ∀ {L Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → FreshStk L Ss → Fresh L α × FreshStk L Ss′
pop-fresh pop-here (fs-asgn f fs) = f , fs
pop-fresh (pop-bind p) (fs-bind fs) with pop-fresh p fs
pop-fresh (pop-bind p) (fs-bind fs) | f , fs′ = f , fs-bind fs′

push-fresh : ∀ {L Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → Fresh L α → FreshStk L Ss′ → FreshStk L Ss
push-fresh pop-here f fs = fs-asgn f fs
push-fresh (pop-bind p) f (fs-bind fs) = fs-bind (push-fresh p f fs)

mutual
  convElt-freshStk : ∀ {L Sg Ssᵢ Ssₑ Bs ĉ A B}
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → FreshElt L ĉ → FreshStk L Ssₑ → FreshStk L Ssᵢ
  convElt-freshStk (conv-seal rep rd pop) (fe-seal f) fs =
    proj₂ (pop-fresh pop fs)
  convElt-freshStk (conv-unseal rep rd pop na) (fe-unseal f) fs =
    push-fresh pop f fs
  convElt-freshStk (conv-hide sc wf pop na) (fe-hide f) fs =
    proj₂ (pop-fresh pop fs)
  convElt-freshStk (conv-show sc wf pop na) (fe-show f) fs =
    push-fresh pop f fs
  convElt-freshStk (conv-fun s t) (fe-fun fs′ ft) fs = conv-freshStk t ft fs
  convElt-freshStk (conv-all s) (fe-all f) fs
    with conv-freshStk s f (fs-bind fs)
  convElt-freshStk (conv-all s) (fe-all f) fs | fs-bind fs′ = fs′

  conv-freshStk : ∀ {L Sg Ssᵢ Ssₑ Bs c A B}
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → FreshConv L c → FreshStk L Ssₑ → FreshStk L Ssᵢ
  conv-freshStk (conv-id wf) fc fs = fs
  conv-freshStk (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) (fc-cons fe fc) fs
    with convElt-base hd
  conv-freshStk (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) (fc-cons fe fc) fs
    | refl = convElt-freshStk hd fe (conv-freshStk tl fc fs)

------------------------------------------------------------------------
-- 9.  A stored representation is untouched
------------------------------------------------------------------------
-- It is well formed over the EMPTY base, so no `bse` occurs in it and
-- a base substitution leaves it alone — the `lvl-fixed` of
-- proof.AddrWeaken, for substitutions.

wfᴿ-nobse-sub : ∀ {Sg Ss n R} σ → Sg ∣ (Ss ∥ []) ⊢ᴿ[ n ] R
  → substᴿᵉ σ R ≡ R
wfᴿ-nobse-sub σ (wfᴿ-var (a-lvl l)) = refl
wfᴿ-nobse-sub σ (wfᴿ-bv lt) = refl
wfᴿ-nobse-sub σ wfᴿ-ℕ = refl
wfᴿ-nobse-sub σ wfᴿ-𝔹 = refl
wfᴿ-nobse-sub σ (wfᴿ-⇒ a b) =
  cong₂ _⇒ᴿ_ (wfᴿ-nobse-sub σ a) (wfᴿ-nobse-sub σ b)
wfᴿ-nobse-sub σ (wfᴿ-∀ a) = cong `∀ᴿ (wfᴿ-nobse-sub σ a)

lvl-fixed-sub : ∀ {Sg ℓ R} σ → StoreOk Sg → Sg ∋ˡ ℓ := R
  → substᴿᵉ σ R ≡ R
lvl-fixed-sub σ sok l = wfᴿ-nobse-sub σ (sok l)

------------------------------------------------------------------------
-- 10.  The pop judgment travels
------------------------------------------------------------------------
-- Pure stack structure, with no address arithmetic: a substitution
-- passes straight through it, exactly as a renaming does.

pop-inst : ∀ {σ Ss Ss′ Bs Bs′ X α}
  → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → (substStk σ Ss ∥ Bs′) ▷ X := substAddrᵉ σ α ⇒ (substStk σ Ss′ ∥ Bs′)
pop-inst pop-here = pop-here
pop-inst (pop-bind p) = pop-bind (pop-inst p)

------------------------------------------------------------------------
-- 11.  A base SUBSTITUTION between contexts
------------------------------------------------------------------------
-- The mirror of `Renamesᵇ` (proof.AddrWeaken): one closure property per
-- lookup, plus the reflection `sub-n⁻` that the NEGATIVE premises need.
-- `sub-n⁻` also reports that the reflected address is FRESH — the
-- context's crossing assignments are store-scoped — which is exactly
-- what `notasgn-inst` must feed to `sub-inj`.

record Substsᵇ (Sg : Store) (L : ℕ) (σ : SubstAddr) (Γ Γ′ : Ctxᵗ) : Set
  where
  field
    sub-ok  : StoreOk Sg
    sub-inj : InjF L σ
    sub-a   : ∀ {α} → Sg ∣ Γ ∋a α → Sg ∣ Γ′ ∋a substAddrᵉ σ α
    sub-n   : ∀ {X α} → Γ ∋n X := α → Γ′ ∋n X := substAddrᵉ σ α
    -- scope alone, which is all `⊢ᵗ` reads, and the `∀`-bound variables
    -- a `ᵛ reads back through
    sub-t   : ∀ {X} → stk Γ ∋ᵗ X → stk Γ′ ∋ᵗ X
    sub-b   : ∀ {X i} → stk Γ ∋b X at i → stk Γ′ ∋b X at i
    sub-r   : ∀ {α R} → Sg ∣ Γ ∋r α := R
            → Sg ∣ Γ′ ∋r substAddrᵉ σ α := substᴿᵉ σ R
    sub-n⁻  : ∀ {X α} → Γ′ ∋n X := α
            → Σ[ β ∈ Addr ]
                ((Γ ∋n X := β) × (Fresh L β × (α ≡ substAddrᵉ σ β)))
open Substsᵇ

------------------------------------------------------------------------
-- 12.  Closure under the stack binders
------------------------------------------------------------------------
-- Neither address lookup reads the stack, so a stack entry has only to
-- be carried by the NAME components.

sub-bind : Substsᵇ Sg L σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Substsᵇ Sg L σ (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
sub-ok (sub-bind r) = sub-ok r
sub-inj (sub-bind r) = sub-inj r
sub-t (sub-bind r) t-here = t-here
sub-t (sub-bind r) (t-there p) = t-there (sub-t r p)
sub-b (sub-bind r) b-here = b-here
sub-b (sub-bind r) (b-bind p) = b-bind (sub-b r p)
sub-a (sub-bind r) p = ∋a-restk (sub-a r (∋a-restk p))
sub-r (sub-bind r) p = ∋r-restk (sub-r r (∋r-restk p))
sub-n (sub-bind r) (n-skip-bind p) = n-skip-bind (sub-n r p)
sub-n⁻ (sub-bind r) (n-skip-bind p) with sub-n⁻ r p
sub-n⁻ (sub-bind r) (n-skip-bind p) | β , q , f , eq =
  β , n-skip-bind q , f , eq

sub-asgn : Fresh L α → Substsᵇ Sg L σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Substsᵇ Sg L σ (asgn α ∷ Ss ∥ Bs) (asgn (substAddrᵉ σ α) ∷ Ss′ ∥ Bs′)
sub-ok (sub-asgn f r) = sub-ok r
sub-inj (sub-asgn f r) = sub-inj r
sub-t (sub-asgn f r) t-here = t-here
sub-t (sub-asgn f r) (t-there p) = t-there (sub-t r p)
sub-b (sub-asgn f r) (b-asgn p) = b-asgn (sub-b r p)
sub-a (sub-asgn f r) p = ∋a-restk (sub-a r (∋a-restk p))
sub-r (sub-asgn f r) p = ∋r-restk (sub-r r (∋r-restk p))
sub-n (sub-asgn f r) n-here-asgn = n-here-asgn
sub-n (sub-asgn f r) (n-skip-asgn p) = n-skip-asgn (sub-n r p)
sub-n⁻ (sub-asgn {α = α} f r) n-here-asgn = α , n-here-asgn , f , refl
sub-n⁻ (sub-asgn f r) (n-skip-asgn p) with sub-n⁻ r p
sub-n⁻ (sub-asgn f r) (n-skip-asgn p) | β , q , g , eq =
  β , n-skip-asgn q , g , eq

-- The whole stack rides along, one entry at a time; its crossing
-- assignments must be fresh, which is what `FreshStk` records.
sub-stk : ∀ {Sg L σ Bs Bs′ Ss} → Substsᵇ Sg L σ ([] ∥ Bs) ([] ∥ Bs′)
  → FreshStk L Ss
  → Substsᵇ Sg L σ (Ss ∥ Bs) (substStk σ Ss ∥ Bs′)
sub-stk {Ss = []} r fs = r
sub-stk {Ss = bind ∷ Ss} r (fs-bind fs) = sub-bind (sub-stk r fs)
sub-stk {Ss = asgn α ∷ Ss} r (fs-asgn f fs) = sub-asgn f (sub-stk r fs)

------------------------------------------------------------------------
-- 13.  Closure under a BASE binder, and the discharge instance
------------------------------------------------------------------------
-- `Λ` and `ν` bind on the base, so they are where the substitution
-- extends; `∀` and `∀ᴿ` bind no address, so they do not.

substEnt : SubstAddr → BaseEnt → BaseEnt
substEnt σ addr = addr
substEnt σ (nuBind R) = nuBind (substᴿᵉ σ R)

sub-ext : ∀ {Sg L σ Bs Bs′ e}
  → Substsᵇ Sg L σ ([] ∥ Bs) ([] ∥ Bs′)
  → Substsᵇ Sg L (extsᵃᵉ σ) ([] ∥ e ∷ Bs) ([] ∥ substEnt σ e ∷ Bs′)
sub-ok (sub-ext r) = sub-ok r
sub-inj (sub-ext r) = inj-ext (sub-inj r)
sub-n (sub-ext r) ()
sub-n⁻ (sub-ext r) ()
sub-t (sub-ext r) ()
sub-b (sub-ext r) ()
sub-a (sub-ext r) (a-lvl l) = a-lvl l
sub-a (sub-ext {e = addr} r) a-here-addr = a-here-addr
sub-a (sub-ext {e = nuBind T} r) a-here-nu = a-here-nu
sub-a (sub-ext {e = addr} r) (a-skip-addr p) =
  ren-a (ren-wk (sub-ok r)) (sub-a r p)
sub-a (sub-ext {e = nuBind T} r) (a-skip-nu p) =
  ren-a (ren-wk (sub-ok r)) (sub-a r p)
sub-r (sub-ext {σ = σ} r) (r-lvl l)
  rewrite lvl-fixed-sub (extsᵃᵉ σ) (sub-ok r) l = r-lvl l
sub-r (sub-ext {σ = σ} {e = nuBind T} r) r-here
  rewrite substᴿᵉ-ext σ T = r-here
sub-r (sub-ext {σ = σ} {e = addr} r) (r-skip-addr {R = R} p)
  rewrite substᴿᵉ-ext σ R = ren-r (ren-wk (sub-ok r)) (sub-r r p)
sub-r (sub-ext {σ = σ} {e = nuBind T} r) (r-skip-nu {R = R} p)
  rewrite substᴿᵉ-ext σ R = ren-r (ren-wk (sub-ok r)) (sub-r r p)

-- THE INSTANCE `Alloc` uses: the ν's entry is discharged to the fresh
-- store level, and every older base address slides down one.
sub-inst₀ : ∀ Sg {Bs R} → StoreOk (Sg ∷ʳ R)
  → Substsᵇ (Sg ∷ʳ R) (length Sg) (instᵉ₀ (lvl (length Sg)))
      ([] ∥ nuBind R ∷ Bs) ([] ∥ Bs)
sub-ok (sub-inst₀ Sg sok) = sok
sub-inj (sub-inst₀ Sg sok) = inj-inst₀ (length Sg)
sub-n (sub-inst₀ Sg sok) ()
sub-n⁻ (sub-inst₀ Sg sok) ()
sub-t (sub-inst₀ Sg sok) ()
sub-b (sub-inst₀ Sg sok) ()
sub-a (sub-inst₀ Sg sok) (a-lvl l) = a-lvl l
sub-a (sub-inst₀ Sg sok) a-here-nu = a-lvl (∋ˡ-last Sg)
sub-a (sub-inst₀ Sg sok) (a-skip-nu p) = p
sub-r (sub-inst₀ Sg sok) (r-lvl l)
  rewrite lvl-fixed-sub (instᵉ₀ (lvl (length Sg))) sok l = r-lvl l
sub-r (sub-inst₀ Sg {R = R} sok) r-here
  rewrite inst-unshiftᴿ (lvl (length Sg)) R = r-lvl (∋ˡ-last Sg)
sub-r (sub-inst₀ Sg sok) (r-skip-nu {R = S} p)
  rewrite inst-unshiftᴿ (lvl (length Sg)) S = p

------------------------------------------------------------------------
-- 14.  The judgments travel
------------------------------------------------------------------------
-- A base substitution leaves NAMES alone, so source types are
-- unchanged; only the representation types move.

wfᵗ-inst : ∀ {Sg L σ Γ Γ′ A} → Substsᵇ Sg L σ Γ Γ′ → Γ ⊢ᵗ A → Γ′ ⊢ᵗ A
wfᵗ-inst r (wf-var n) = wf-var (sub-t r n)
wfᵗ-inst r wf-ℕ = wf-ℕ
wfᵗ-inst r wf-𝔹 = wf-𝔹
wfᵗ-inst r (wf-⇒ a b) = wf-⇒ (wfᵗ-inst r a) (wfᵗ-inst r b)
wfᵗ-inst r (wf-∀ a) = wf-∀ (wfᵗ-inst (sub-bind r) a)

wfᴿ-inst : ∀ {Sg L σ Γ Γ′ n R} → Substsᵇ Sg L σ Γ Γ′
  → Sg ∣ Γ ⊢ᴿ[ n ] R → Sg ∣ Γ′ ⊢ᴿ[ n ] substᴿᵉ σ R
wfᴿ-inst r (wfᴿ-var a) = wfᴿ-var (sub-a r a)
wfᴿ-inst r (wfᴿ-bv lt) = wfᴿ-bv lt
wfᴿ-inst r wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-inst r wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-inst r (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-inst r a) (wfᴿ-inst r b)
wfᴿ-inst r (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-inst r a)

read-inst : ∀ {Sg L σ Γ Γ′ R A} → Substsᵇ Sg L σ Γ Γ′
  → Sg ∣ Γ ⊢ R ⇓ A → Sg ∣ Γ′ ⊢ substᴿᵉ σ R ⇓ A
read-inst r (read-var n) = read-var (sub-n r n)
read-inst r (read-bv n) = read-bv (sub-b r n)
read-inst r read-ℕ = read-ℕ
read-inst r read-𝔹 = read-𝔹
read-inst r (read-⇒ a b) = read-⇒ (read-inst r a) (read-inst r b)
read-inst r (read-∀ a) = read-∀ (read-inst (sub-bind r) a)

-- The one place the restricted injectivity is needed inside the
-- CONTEXT layer: a name for σα in the image must come from a name for
-- α, and only injectivity says so.
notasgn-inst : ∀ {Sg L σ Γ Γ′ α} → Substsᵇ Sg L σ Γ Γ′ → Fresh L α
  → NotAssigned Γ α → NotAssigned Γ′ (substAddrᵉ σ α)
notasgn-inst r f na p with sub-n⁻ r p
notasgn-inst r f na p | β , q , g , eq with sub-inj r f g eq
notasgn-inst r f na p | β , q , g , eq | refl = na q

------------------------------------------------------------------------
-- 15.  A conversion travels
------------------------------------------------------------------------
-- Interior and exterior differ only in the STACK, so one base
-- substitution serves both ends; the crossings keep their names, and
-- their addresses move by `substAddrElt`.

mutual
  convElt-inst : ∀ {Sg L σ Bs Bs′ Ssᵢ Ssₑ ĉ A B}
    → Substsᵇ Sg L σ ([] ∥ Bs) ([] ∥ Bs′)
    → FreshElt L ĉ → FreshStk L Ssₑ
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Sg ∣ (substStk σ Ssᵢ ∥ Bs′) ⊢̂ substAddrElt σ ĉ ∶ A ⇝ B
        ⊣ (substStk σ Ssₑ ∥ Bs′)
  convElt-inst r (fe-seal f) fs (conv-seal rep rd pop) =
    conv-seal (sub-r (sub-stk r fs) rep)
              (read-inst (sub-stk r (proj₂ (pop-fresh pop fs))) rd)
              (pop-inst pop)
  convElt-inst r (fe-unseal f) fs (conv-unseal rep rd pop na) =
    conv-unseal (sub-r (sub-stk r (push-fresh pop f fs)) rep)
                (read-inst (sub-stk r fs) rd)
                (pop-inst pop)
                (notasgn-inst (sub-stk r fs) f na)
  convElt-inst r (fe-hide f) fs (conv-hide sc wf pop na) =
    conv-hide (sub-a (sub-stk r (proj₂ (pop-fresh pop fs))) sc)
              (wfᵗ-inst (sub-stk r (proj₂ (pop-fresh pop fs))) wf)
              (pop-inst pop)
              (notasgn-inst (sub-stk r (proj₂ (pop-fresh pop fs))) f na)
  convElt-inst r (fe-show f) fs (conv-show sc wf pop na) =
    conv-show (sub-a (sub-stk r fs) sc) (wfᵗ-inst (sub-stk r fs) wf)
              (pop-inst pop)
              (notasgn-inst (sub-stk r fs) f na)
  convElt-inst r (fe-fun gs gt) fs (conv-fun s t) =
    conv-fun (conv-inst r gs (conv-freshStk t gt fs) s)
             (conv-inst r gt fs t)
  convElt-inst r (fe-all g) fs (conv-all s) =
    conv-all (conv-inst r g (fs-bind fs) s)

  conv-inst : ∀ {Sg L σ Bs Bs′ Ssᵢ Ssₑ c A B}
    → Substsᵇ Sg L σ ([] ∥ Bs) ([] ∥ Bs′)
    → FreshConv L c → FreshStk L Ssₑ
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Sg ∣ (substStk σ Ssᵢ ∥ Bs′) ⊢ substAddrConv σ c ∶ A ⇝ B
        ⊣ (substStk σ Ssₑ ∥ Bs′)
  conv-inst r fc fs (conv-id wf) = conv-id (wfᵗ-inst (sub-stk r fs) wf)
  conv-inst r (fc-cons fe fc) fs (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl)
    with convElt-base hd
  conv-inst r (fc-cons fe fc) fs (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl)
    | refl = conv-cons (convElt-inst r fe (conv-freshStk tl fc fs) hd)
                       (conv-inst r fc fs tl)

------------------------------------------------------------------------
-- 16.  Inertness survives a base substitution — unconditionally
------------------------------------------------------------------------
-- The mirror of proof.InertRenaming §1-§4.  `substAddrConv σ` leaves
-- every NAME and every `Ty` alone, and passes through `all` unextended
-- (an `all` binds no address), so everything the views decide by
-- looking at a type is literally unchanged and everything they decide
-- by looking at element shapes commutes.  `all⁺` hoists a crossing
-- under the ∀ element's binder, which used to shift its address; with
-- a `∀` binding a type variable it does not, so even that row is refl.

target-inst : ∀ σ c → target (substAddrConv σ c) ≡ target c
target-inst σ (id A) = refl
target-inst σ (ĉ ∷ᶜ c) = target-inst σ c

elts-inst : ∀ σ c → elts (substAddrConv σ c) ≡ map (substAddrElt σ) (elts c)
elts-inst σ (id A) = refl
elts-inst σ (ĉ ∷ᶜ c) = cong (substAddrElt σ ĉ ∷_) (elts-inst σ c)

mapEls′ : SubstAddr → Maybe (List ConvElt) → Maybe (List ConvElt)
mapEls′ σ (just es) = just (map (substAddrElt σ) es)
mapEls′ σ nothing   = nothing

mapPr′ : SubstAddr → Maybe (List ConvElt × List ConvElt)
  → Maybe (List ConvElt × List ConvElt)
mapPr′ σ (just (Ls , Rs)) =
  just (map (substAddrElt σ) Ls , map (substAddrElt σ) Rs)
mapPr′ σ nothing = nothing

arr⁻-inst : ∀ σ ĉ → arr⁻ (substAddrElt σ ĉ) ≡ mapEls′ σ (arr⁻ ĉ)
arr⁻-inst σ (seal X α)   = refl
arr⁻-inst σ (unseal X α) = refl
arr⁻-inst σ (hide X α)   = refl
arr⁻-inst σ (show X α)   = refl
arr⁻-inst σ (s ↦ t)      = cong just (elts-inst σ s)
arr⁻-inst σ (all s)      = refl

arr⁺-inst : ∀ σ ĉ → arr⁺ (substAddrElt σ ĉ) ≡ mapEls′ σ (arr⁺ ĉ)
arr⁺-inst σ (seal X α)   = refl
arr⁺-inst σ (unseal X α) = refl
arr⁺-inst σ (hide X α)   = refl
arr⁺-inst σ (show X α)   = refl
arr⁺-inst σ (s ↦ t)      = cong just (elts-inst σ t)
arr⁺-inst σ (all s)      = refl

all⁺-inst : ∀ σ ĉ → all⁺ (substAddrElt σ ĉ) ≡ mapEls′ σ (all⁺ ĉ)
all⁺-inst σ (seal X α)   = refl
all⁺-inst σ (unseal X α) = refl
all⁺-inst σ (hide X α)   = refl
all⁺-inst σ (show X α)   = refl
all⁺-inst σ (s ↦ t)      = refl
all⁺-inst σ (all s)      = cong just (elts-inst σ s)

consArr-inst : ∀ σ l r q
  → consArr (mapEls′ σ l) (mapEls′ σ r) (mapPr′ σ q)
  ≡ mapPr′ σ (consArr l r q)
consArr-inst σ (just ls) (just rs) (just (Ls , Rs)) =
  cong₂ (λ x y → just (x , y))
    (sym (map-++ (substAddrElt σ) Ls ls))
    (sym (map-++ (substAddrElt σ) rs Rs))
consArr-inst σ (just ls) (just rs) nothing = refl
consArr-inst σ (just ls) nothing q = refl
consArr-inst σ nothing r q = refl

arrElts-inst : ∀ σ Es
  → arrElts (map (substAddrElt σ) Es) ≡ mapPr′ σ (arrElts Es)
arrElts-inst σ [] = refl
arrElts-inst σ (ĉ ∷ Es)
  rewrite arr⁻-inst σ ĉ | arr⁺-inst σ ĉ | arrElts-inst σ Es =
  consArr-inst σ (arr⁻ ĉ) (arr⁺ ĉ) (arrElts Es)

consAllE-inst : ∀ σ e E
  → consAllE (mapEls′ σ e) (mapEls′ σ E) ≡ mapEls′ σ (consAllE e E)
consAllE-inst σ (just es) (just Es) =
  cong just (sym (map-++ (substAddrElt σ) es Es))
consAllE-inst σ (just es) nothing = refl
consAllE-inst σ nothing E = refl

allElts-inst : ∀ σ Es
  → allElts (map (substAddrElt σ) Es) ≡ mapEls′ σ (allElts Es)
allElts-inst σ [] = refl
allElts-inst σ (ĉ ∷ Es)
  rewrite all⁺-inst σ ĉ | allElts-inst σ Es =
  consAllE-inst σ (all⁺ ĉ) (allElts Es)

arrFrom-inst : ∀ σ A₀ q T {c₁ c₂} → arrFrom A₀ q T ≡ just (c₁ , c₂)
  → Σ[ d₁ ∈ Conv ] Σ[ d₂ ∈ Conv ]
      arrFrom A₀ (mapPr′ σ q) T ≡ just (d₁ , d₂)
arrFrom-inst σ A₀ (just (Ls , Rs)) (C ⇒ D) eq =
    normalize (attach (map (substAddrElt σ) Ls) A₀)
  , normalize (attach (map (substAddrElt σ) Rs) D)
  , refl
arrFrom-inst σ A₀ (just p) (` X) ()
arrFrom-inst σ A₀ (just p) `ℕ ()
arrFrom-inst σ A₀ (just p) `𝔹 ()
arrFrom-inst σ A₀ (just p) (`∀ B) ()
arrFrom-inst σ A₀ nothing T ()

arr-inst : ∀ σ A₀ c {c₁ c₂} → arr A₀ c ≡ just (c₁ , c₂)
  → Σ[ d₁ ∈ Conv ] Σ[ d₂ ∈ Conv ]
      arr A₀ (substAddrConv σ c) ≡ just (d₁ , d₂)
arr-inst σ A₀ c eq with arrFrom-inst σ A₀ (arrElts (elts c)) (target c) eq
arr-inst σ A₀ c eq | d₁ , d₂ , eq′ = d₁ , d₂ , unfolded
  where
  unfolded :
      arrFrom A₀ (arrElts (elts (substAddrConv σ c)))
              (target (substAddrConv σ c))
    ≡ just (d₁ , d₂)
  unfolded
    rewrite elts-inst σ c | arrElts-inst σ (elts c) | target-inst σ c =
    eq′

allFrom-inst : ∀ σ Es T {d} → allFrom Es T ≡ just d
  → Σ[ e ∈ Conv ] allFrom (mapEls′ σ Es) T ≡ just e
allFrom-inst σ (just es) (`∀ B) eq =
  normalize (attach (map (substAddrElt σ) es) B) , refl
allFrom-inst σ (just es) (` X) ()
allFrom-inst σ (just es) `ℕ ()
allFrom-inst σ (just es) `𝔹 ()
allFrom-inst σ (just es) (C ⇒ D) ()
allFrom-inst σ nothing T ()

allView-inst : ∀ σ c {d} → allView c ≡ just d
  → Σ[ e ∈ Conv ] allView (substAddrConv σ c) ≡ just e
allView-inst σ c eq
  with allFrom-inst σ (allElts (elts c)) (target c) eq
allView-inst σ c eq | e , eq′ = e , unfolded
  where
  unfolded :
      allFrom (allElts (elts (substAddrConv σ c)))
              (target (substAddrConv σ c))
    ≡ just e
  unfolded
    rewrite elts-inst σ c | allElts-inst σ (elts c) | target-inst σ c =
    eq′

inert-inst : ∀ {σ c} → Inert c → Inert (substAddrConv σ c)
inert-inst {σ} {c} (inert-arr A₀ eq) with arr-inst σ A₀ c eq
inert-inst {σ} {c} (inert-arr A₀ eq) | d₁ , d₂ , eq′ = inert-arr A₀ eq′
inert-inst {σ} {c} (inert-all eq) with allView-inst σ c eq
inert-inst {σ} {c} (inert-all eq) | e , eq′ = inert-all eq′
inert-inst {σ} {c} (inert-var eq) =
  inert-var (trans (target-inst σ c) eq)

------------------------------------------------------------------------
-- 17.  Normal forms survive, PROVIDED the addresses are fresh
------------------------------------------------------------------------
-- `fuse` cancels on an address EQUALITY, so a substitution that
-- identifies two addresses turns a normal form into a redex.  Away from
-- `lvl L` the substitution is injective (§7), so a pair that did not
-- cancel still does not — and `Fresh` is what supplies the two sides.

fuse-inst : ∀ {L σ} → InjF L σ → ∀ ĉ ḓ → FreshElt L ĉ → FreshElt L ḓ
  → fuse ĉ ḓ ≡ nothing
  → fuse (substAddrElt σ ĉ) (substAddrElt σ ḓ) ≡ nothing
fuse-inst inj (seal X α) (seal Y β) f g eq = refl
fuse-inst {σ = σ} inj (seal X α) (unseal Y β) (fe-seal f) (fe-unseal g) eq
  with X ≟ Y | α ≟ᵃ β | substAddrᵉ σ α ≟ᵃ substAddrᵉ σ β
fuse-inst {σ = σ} inj (seal X α) (unseal Y β) (fe-seal f) (fe-unseal g) ()
  | yes _ | yes _ | _
fuse-inst {σ = σ} inj (seal X α) (unseal Y β) (fe-seal f) (fe-unseal g) eq
  | yes _ | no ne | yes e = ⊥-elim (ne (inj f g e))
fuse-inst {σ = σ} inj (seal X α) (unseal Y β) (fe-seal f) (fe-unseal g) eq
  | yes _ | no _ | no _ = refl
fuse-inst {σ = σ} inj (seal X α) (unseal Y β) (fe-seal f) (fe-unseal g) eq
  | no _ | _ | _ = refl
fuse-inst inj (seal X α) (hide Y β) f g eq = refl
fuse-inst inj (seal X α) (show Y β) f g eq = refl
fuse-inst inj (seal X α) (s₂ ↦ t₂) f g eq = refl
fuse-inst inj (seal X α) (all s₂) f g eq = refl
fuse-inst inj (unseal X α) (seal Y β) f g eq = refl
fuse-inst inj (unseal X α) (unseal Y β) f g eq = refl
fuse-inst inj (unseal X α) (hide Y β) f g eq = refl
fuse-inst inj (unseal X α) (show Y β) f g eq = refl
fuse-inst inj (unseal X α) (s₂ ↦ t₂) f g eq = refl
fuse-inst inj (unseal X α) (all s₂) f g eq = refl
fuse-inst inj (hide X α) (seal Y β) f g eq = refl
fuse-inst inj (hide X α) (unseal Y β) f g eq = refl
fuse-inst inj (hide X α) (hide Y β) f g eq = refl
fuse-inst {σ = σ} inj (hide X α) (show Y β) (fe-hide f) (fe-show g) eq
  with X ≟ Y | α ≟ᵃ β | substAddrᵉ σ α ≟ᵃ substAddrᵉ σ β
fuse-inst {σ = σ} inj (hide X α) (show Y β) (fe-hide f) (fe-show g) ()
  | yes _ | yes _ | _
fuse-inst {σ = σ} inj (hide X α) (show Y β) (fe-hide f) (fe-show g) eq
  | yes _ | no ne | yes e = ⊥-elim (ne (inj f g e))
fuse-inst {σ = σ} inj (hide X α) (show Y β) (fe-hide f) (fe-show g) eq
  | yes _ | no _ | no _ = refl
fuse-inst {σ = σ} inj (hide X α) (show Y β) (fe-hide f) (fe-show g) eq
  | no _ | _ | _ = refl
fuse-inst inj (hide X α) (s₂ ↦ t₂) f g eq = refl
fuse-inst inj (hide X α) (all s₂) f g eq = refl
fuse-inst inj (show X α) (seal Y β) f g eq = refl
fuse-inst inj (show X α) (unseal Y β) f g eq = refl
fuse-inst {σ = σ} inj (show X α) (hide Y β) (fe-show f) (fe-hide g) eq
  with X ≟ Y | α ≟ᵃ β | substAddrᵉ σ α ≟ᵃ substAddrᵉ σ β
fuse-inst {σ = σ} inj (show X α) (hide Y β) (fe-show f) (fe-hide g) ()
  | yes _ | yes _ | _
fuse-inst {σ = σ} inj (show X α) (hide Y β) (fe-show f) (fe-hide g) eq
  | yes _ | no ne | yes e = ⊥-elim (ne (inj f g e))
fuse-inst {σ = σ} inj (show X α) (hide Y β) (fe-show f) (fe-hide g) eq
  | yes _ | no _ | no _ = refl
fuse-inst {σ = σ} inj (show X α) (hide Y β) (fe-show f) (fe-hide g) eq
  | no _ | _ | _ = refl
fuse-inst inj (show X α) (show Y β) f g eq = refl
fuse-inst inj (show X α) (s₂ ↦ t₂) f g eq = refl
fuse-inst inj (show X α) (all s₂) f g eq = refl
fuse-inst inj (s₁ ↦ t₁) (seal Y β) f g eq = refl
fuse-inst inj (s₁ ↦ t₁) (unseal Y β) f g eq = refl
fuse-inst inj (s₁ ↦ t₁) (hide Y β) f g eq = refl
fuse-inst inj (s₁ ↦ t₁) (show Y β) f g eq = refl
fuse-inst inj (s₁ ↦ t₁) (s₂ ↦ t₂) f g ()
fuse-inst inj (s₁ ↦ t₁) (all s₂) f g eq = refl
fuse-inst inj (all s₁) (seal Y β) f g eq = refl
fuse-inst inj (all s₁) (unseal Y β) f g eq = refl
fuse-inst inj (all s₁) (hide Y β) f g eq = refl
fuse-inst inj (all s₁) (show Y β) f g eq = refl
fuse-inst inj (all s₁) (s₂ ↦ t₂) f g eq = refl
fuse-inst inj (all s₁) (all s₂) f g ()

mutual
  nfElt-inst : ∀ {L σ ĉ} → InjF L σ → FreshElt L ĉ → NFElt ĉ
    → NFElt (substAddrElt σ ĉ)
  nfElt-inst inj f nf-seal = nf-seal
  nfElt-inst inj f nf-unseal = nf-unseal
  nfElt-inst inj f nf-hide = nf-hide
  nfElt-inst inj f nf-show = nf-show
  nfElt-inst inj (fe-fun gs gt) (nf-fun s t) =
    nf-fun (nf-inst inj gs s) (nf-inst inj gt t)
  nfElt-inst inj (fe-all g) (nf-all s) = nf-all (nf-inst inj g s)

  irr-inst : ∀ {L σ ĉ c} → InjF L σ → FreshElt L ĉ → FreshConv L c
    → IrreducibleAfter ĉ c
    → IrreducibleAfter (substAddrElt σ ĉ) (substAddrConv σ c)
  irr-inst inj f fc irr-id = irr-id
  irr-inst {ĉ = ĉ} inj f (fc-cons g fc) (irr-cons {ḓ = ḓ} e) =
    irr-cons (fuse-inst inj ĉ ḓ f g e)

  nf-inst : ∀ {L σ c} → InjF L σ → FreshConv L c → NF c
    → NF (substAddrConv σ c)
  nf-inst inj fc nf-id = nf-id
  nf-inst inj (fc-cons f fc) (nf-cons hd tl irr) =
    nf-cons (nfElt-inst inj f hd) (nf-inst inj fc tl)
            (irr-inst inj f fc irr)

------------------------------------------------------------------------
-- 18.  Valuehood survives
------------------------------------------------------------------------
-- `Λ` is a base binder, so the substitution extends there — and
-- `extsᵃᵉ` preserves the restricted injectivity.

mutual
  simple-inst : ∀ {L σ V} → InjF L σ → FreshM L V → Simple V
    → Simple (substAddrᴹ σ V)
  simple-inst inj f S$ = S$
  simple-inst inj f S# = S#
  simple-inst inj f Sƛ = Sƛ
  simple-inst inj (fm-Λ f) (SΛ v) = SΛ (value-inst (inj-ext inj) f v)

  value-inst : ∀ {L σ V} → InjF L σ → FreshM L V → Value V
    → Value (substAddrᴹ σ V)
  value-inst inj f (Vs s) = Vs (simple-inst inj f s)
  value-inst inj (fm-⟨⟩ f g) (V⟨⟩ s nf inrt) =
    V⟨⟩ (simple-inst inj f s) (nf-inst inj g nf) (inert-inst inrt)

------------------------------------------------------------------------
-- 19.  A term travels
------------------------------------------------------------------------
-- `Λ` and `ν` are the base's binders, so they are where the
-- substitution extends; `⟨ c ⟩` is where the stack/base split pays off,
-- since the boundary's interior differs only in the stack.

⊢-inst : ∀ {Sg L σ Bs Bs′ Ss Γ M A}
  → Substsᵇ Sg L σ ([] ∥ Bs) ([] ∥ Bs′)
  → FreshStk L Ss → FreshM L M
  → Sg ∣ (Ss ∥ Bs) ∣ Γ ⊢ M ⦂ A
  → Sg ∣ (substStk σ Ss ∥ Bs′) ∣ Γ ⊢ substAddrᴹ σ M ⦂ A
⊢-inst r fs fm (⊢` x) = ⊢` x
⊢-inst r fs fm ⊢$ = ⊢$
⊢-inst r fs fm ⊢# = ⊢#
⊢-inst r fs (fm-⊕ f g) (⊢⊕ m n) =
  ⊢⊕ (⊢-inst r fs f m) (⊢-inst r fs g n)
⊢-inst r fs (fm-ƛ f) (⊢ƛ wf n) =
  ⊢ƛ (wfᵗ-inst (sub-stk r fs) wf) (⊢-inst r fs f n)
⊢-inst r fs (fm-· f g) (⊢· l m) =
  ⊢· (⊢-inst r fs f l) (⊢-inst r fs g m)
⊢-inst r fs (fm-•[] f) (⊢•[] l wf) =
  ⊢•[] (⊢-inst r fs f l) (wfᵗ-inst (sub-stk r fs) wf)
⊢-inst r fs (fm-⟨⟩ f g) (⊢⟨⟩ {Δᵢ = Ssᵢ ∥ Bsᵢ} nf ⊢M ⊢c) with conv-base ⊢c
⊢-inst r fs (fm-⟨⟩ f g) (⊢⟨⟩ {Δᵢ = Ssᵢ ∥ Bsᵢ} nf ⊢M ⊢c) | refl =
  ⊢⟨⟩ (nf-inst (sub-inj r) g nf)
      (⊢-inst r (conv-freshStk ⊢c g fs) f ⊢M)
      (conv-inst r g fs ⊢c)
⊢-inst {σ = σ} {Ss = Ss} r fs (fm-Λ f) (⊢Λ v ⊢V)
  with ⊢-inst (sub-ext {e = addr} r)
              (fs-asgn fr-bse (freshStk-⤒ fs)) f ⊢V
     | substStk-ext σ Ss
⊢-inst {σ = σ} {Ss = Ss} r fs (fm-Λ f) (⊢Λ v ⊢V) | ⊢V′ | eq
  rewrite eq = ⊢Λ (value-inst (inj-ext (sub-inj r)) f v) ⊢V′
⊢-inst {σ = σ} {Ss = Ss} r fs (fm-ν f) (⊢ν {R = R} wf ⊢M)
  with ⊢-inst (sub-ext {e = nuBind R} r) (freshStk-⤒ fs) f ⊢M
     | substStk-ext σ Ss
⊢-inst {σ = σ} {Ss = Ss} r fs (fm-ν f) (⊢ν {R = R} wf ⊢M) | ⊢M′ | eq
  rewrite eq = ⊢ν (wfᴿ-inst (sub-stk r fs) wf) ⊢M′

------------------------------------------------------------------------
-- 20.  PRESERVATION FOR `Alloc`
------------------------------------------------------------------------
-- The store grows on the right, the ν's binder is discharged to the new
-- level, and the body's stack un-shifts back to the ambient one.
--
-- The two freshness premises say that the new level `length Sg` occurs
-- nowhere yet: not in the ambient context's crossing assignments, and
-- not in the body's conversions.  They are not a new invariant in
-- search of a home: `Fresh (length Sg)` is exactly "in scope in Sg"
-- read at a level, which every crossing carries — through `∋r` on
-- `conv-seal`/`conv-unseal` and through `∋a` on `conv-hide`/
-- `conv-show` — and `fresh-of-∋a`/`fresh-of-∋r` below are that reading.
-- proof.Scoped discharges them from typing.

preserve-Alloc : ∀ {Sg Δ Γ R M A}
  → StoreOk Sg → Flat Δ
  → FreshStk (length Sg) (stk Δ) → FreshM (length Sg) M
  → Sg ∣ Δ ∣ Γ ⊢ ν R ∙ M ⦂ A
  → (Sg ∷ʳ R) ∣ Δ ∣ Γ ⊢ M [ lvl (length Sg) ]ᵃᴹ ⦂ A
preserve-Alloc {Sg} sok fl fs fm (⊢ν {Ss = Ss} {Bs = Bs} wf ⊢M)
  with flat-bas fl
preserve-Alloc {Sg} sok fl fs fm (⊢ν {Ss = Ss} {Bs = Bs} wf ⊢M) | refl
  with ⊢-inst (sub-inst₀ Sg (alloc-storeOk sok fl wf))
              (freshStk-⤒ fs) fm (⊢-snoc ⊢M)
     | inst-unshiftˢ (lvl (length Sg)) Ss
preserve-Alloc {Sg} sok fl fs fm (⊢ν {Ss = Ss} {Bs = Bs} wf ⊢M) | refl
  | res | eq rewrite eq = res

------------------------------------------------------------------------
-- 21.  FRESHNESS IS SCOPING, READ AT THE NEXT LEVEL
------------------------------------------------------------------------
-- The refutation that used to stand here — a store, a flat context and
-- a typed `ν` whose contractum was not typable — no longer typechecks:
-- `conv-hide` and `conv-show` now SCOPE their address, and its witness
-- named `lvl 0` over the empty store.  See notes/DECISIONS.md
-- (2026-09-15).  What survives is the positive reading.

fresh-of-∋a : ∀ {Sg Γ α} → Sg ∣ Γ ∋a α → Fresh (length Sg) α
fresh-of-∋a (a-lvl l) = fr-lvl λ { refl → ∋ˡ-fresh l }
fresh-of-∋a a-here-addr = fr-bse
fresh-of-∋a a-here-nu = fr-bse
fresh-of-∋a (a-skip-addr p) = fr-bse
fresh-of-∋a (a-skip-nu p) = fr-bse

fresh-of-∋r : ∀ {Sg Γ α R} → Sg ∣ Γ ∋r α := R → Fresh (length Sg) α
fresh-of-∋r (r-lvl l) = fr-lvl λ { refl → ∋ˡ-fresh l }
fresh-of-∋r r-here = fr-bse
fresh-of-∋r (r-skip-addr p) = fr-bse
fresh-of-∋r (r-skip-nu p) = fr-bse

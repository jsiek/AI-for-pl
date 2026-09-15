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
-- `Substsᵇ` of closure properties over the three lookups, closed under
-- the stack binders (`sub-bind`, `sub-asgn`, `sub-stk`) and under a base
-- binder (`sub-ext`), lifted to `⊢ᵗ`, `⊢ᴿ`, `⇓`, the pop judgment,
-- `NotAssigned`, conversion typing, and finally to terms (`⊢-inst`).
--
-- TWO THINGS ARE GENUINELY DIFFERENT FROM A RENAMING.
--
-- (1) `substAddrᵉ σ` can turn a `bse` into a `lvl`.  So the judgments
--     that are indexed by the ADDRESS FORM need a view: the pop rules
--     `pop-bind-b`/`-l`/`-e`, the name rules `n-skip-bind-b`/`-l`/`-e`,
--     and `∋a`/`∋r` restacking.  The side condition is that σ never
--     produces a BOUND STACK address (`NoBnd`), which holds of
--     `instᵉ₀ (lvl ℓ)` and is preserved by `extsᵃᵉ`.
--
-- (2) σ is NOT injective: it maps `bse 0` and `lvl (length Σ)` to the
--     same address, so a conversion that was a NORMAL FORM can acquire
--     a redex, and `⊢Λ`'s `Value V` premise then fails.  σ IS injective
--     away from `lvl (length Σ)`, so everything goes through under a
--     freshness hypothesis `Fresh L` (L = length Σ) on the addresses
--     that actually occur — in the conversions of the term, and in the
--     crossing assignments of the ambient context.
--
-- WHY THE FRESHNESS HYPOTHESIS CANNOT BE DROPPED.  The task's plan was
-- to DERIVE it: "a well-typed term cannot mention lvl (length Σ),
-- because every address in it is in scope".  That is true of `seal` and
-- `unseal`, which carry `∋r` (§22), but FALSE of `hide` and `show`:
-- their premises are `⊢ᵗ`, a pop, and `NotAssigned`, none of which
-- constrains the address to the store — a `hide X (lvl ℓ)` is well
-- typed as soon as the context happens to assign X to `lvl ℓ`, and the
-- context is not required to be store-scoped either.  §21 exhibits a
-- store, a flat context, and a typed `ν` whose contractum is NOT
-- typable, refuting the unqualified statement outright.  The fix is a
-- design decision for the RULES (adding `Σ ∣ Γ ∋a α` to `conv-hide` and
-- `conv-show` would make `Fresh` derivable from typing — §22); until then
-- the hypothesis is stated explicitly.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
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
open import strong.proof.AddrWeaken using (convElt-base; conv-base; lvl-fixed)
open import strong.proof.InertRenaming using (suc-injᵉ)

private
  variable
    Sg : Store
    L : ℕ
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

-- The fresh level is not in the store yet — what §22 turns on.
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
-- 3.  Address disequalities, once and for all
------------------------------------------------------------------------

lvl≢bnd : ∀ {ℓ i} → lvl ℓ ≡ bnd i → ⊥
lvl≢bnd ()

lvl≢bse : ∀ {ℓ j} → lvl ℓ ≡ bse j → ⊥
lvl≢bse ()

bnd≢lvl : ∀ {i ℓ} → bnd i ≡ lvl ℓ → ⊥
bnd≢lvl ()

bnd≢bse : ∀ {i j} → bnd i ≡ bse j → ⊥
bnd≢bse ()

bse≢lvl : ∀ {j ℓ} → bse j ≡ lvl ℓ → ⊥
bse≢lvl ()

bse≢bnd : ∀ {j i} → bse j ≡ bnd i → ⊥
bse≢bnd ()

bse0≢bseS : ∀ {k} → bse zero ≡ bse (suc k) → ⊥
bse0≢bseS ()

bseS≢bse0 : ∀ {k} → bse (suc k) ≡ bse zero → ⊥
bseS≢bse0 ()

------------------------------------------------------------------------
-- 4.  σ never produces a bound STACK address
------------------------------------------------------------------------
-- `instᵉ₀ (lvl ℓ)` produces levels and base addresses only, and
-- `extsᵃᵉ` preserves that.  Everything that is indexed by the address
-- FORM consults this view.

NoBnd : SubstAddr → Set
NoBnd σ = ∀ j → (Σ[ ℓ ∈ ℕ ] σ j ≡ lvl ℓ) ⊎ (Σ[ k ∈ ℕ ] σ j ≡ bse k)

noBnd-inst₀ : ∀ ℓ → NoBnd (instᵉ₀ (lvl ℓ))
noBnd-inst₀ ℓ zero = inj₁ (ℓ , refl)
noBnd-inst₀ ℓ (suc j) = inj₂ (j , refl)

noBnd-ext : NoBnd σ → NoBnd (extsᵃᵉ σ)
noBnd-ext nb zero = inj₂ (zero , refl)
noBnd-ext nb (suc j) with nb j
noBnd-ext nb (suc j) | inj₁ (ℓ , e) = inj₁ (ℓ , cong (renᵃᵉ suc) e)
noBnd-ext nb (suc j) | inj₂ (k , e) = inj₂ (suc k , cong (renᵃᵉ suc) e)

------------------------------------------------------------------------
-- 5.  The commutations
------------------------------------------------------------------------
-- A base substitution commutes with a STACK renaming, because the two
-- act on disjoint address forms — PROVIDED σ produces no `bnd`.

substAddrᵉ-renᵃ : NoBnd σ → ∀ η α
  → substAddrᵉ σ (renᵃ η α) ≡ renᵃ η (substAddrᵉ σ α)
substAddrᵉ-renᵃ nb η (lvl ℓ) = refl
substAddrᵉ-renᵃ nb η (bnd i) = refl
substAddrᵉ-renᵃ nb η (bse j) with nb j
substAddrᵉ-renᵃ nb η (bse j) | inj₁ (ℓ , e) rewrite e = refl
substAddrᵉ-renᵃ nb η (bse j) | inj₂ (k , e) rewrite e = refl

substᴿᵉ-renameᴿ : NoBnd σ → ∀ η R
  → substᴿᵉ σ (renameᴿ η R) ≡ renameᴿ η (substᴿᵉ σ R)
substᴿᵉ-renameᴿ nb η (`ᵃ α) = cong `ᵃ_ (substAddrᵉ-renᵃ nb η α)
substᴿᵉ-renameᴿ nb η `ℕᴿ = refl
substᴿᵉ-renameᴿ nb η `𝔹ᴿ = refl
substᴿᵉ-renameᴿ nb η (R ⇒ᴿ T) =
  cong₂ _⇒ᴿ_ (substᴿᵉ-renameᴿ nb η R) (substᴿᵉ-renameᴿ nb η T)
substᴿᵉ-renameᴿ nb η (`∀ᴿ R) = cong `∀ᴿ (substᴿᵉ-renameᴿ nb (extᵇ η) R)

substᴿᵉ-⇑ᴿ : NoBnd σ → ∀ R → substᴿᵉ σ (⇑ᴿ R) ≡ ⇑ᴿ (substᴿᵉ σ R)
substᴿᵉ-⇑ᴿ nb R = substᴿᵉ-renameᴿ nb suc R

-- a `bse` image is its own stack shift
nobnd-⇑ᵃ : NoBnd σ → ∀ j
  → ⇑ᵃ (substAddrᵉ σ (bse j)) ≡ substAddrᵉ σ (bse j)
nobnd-⇑ᵃ nb j with nb j
nobnd-⇑ᵃ nb j | inj₁ (ℓ , e) rewrite e = refl
nobnd-⇑ᵃ nb j | inj₂ (k , e) rewrite e = refl

-- The ext/base-shift square: UNCONDITIONAL, since `extsᵃᵉ` is defined
-- by exactly this shift.
substAddrᵉ-ext : ∀ σ α
  → substAddrᵉ (extsᵃᵉ σ) (renᵃᵉ suc α) ≡ renᵃᵉ suc (substAddrᵉ σ α)
substAddrᵉ-ext σ (lvl ℓ) = refl
substAddrᵉ-ext σ (bnd i) = refl
substAddrᵉ-ext σ (bse j) = refl

substᴿᵉ-ext : ∀ σ R → substᴿᵉ (extsᵃᵉ σ) (⇑ᴿᵉ R) ≡ ⇑ᴿᵉ (substᴿᵉ σ R)
substᴿᵉ-ext σ (`ᵃ α) = cong `ᵃ_ (substAddrᵉ-ext σ α)
substᴿᵉ-ext σ `ℕᴿ = refl
substᴿᵉ-ext σ `𝔹ᴿ = refl
substᴿᵉ-ext σ (R ⇒ᴿ T) = cong₂ _⇒ᴿ_ (substᴿᵉ-ext σ R) (substᴿᵉ-ext σ T)
substᴿᵉ-ext σ (`∀ᴿ R) = cong `∀ᴿ (substᴿᵉ-ext σ R)

-- THE PIVOT.  `instᵉ₀` un-shifts the base exactly.
inst-unshiftᵃ : ∀ β α → substAddrᵉ (instᵉ₀ β) (renᵃᵉ suc α) ≡ α
inst-unshiftᵃ β (lvl ℓ) = refl
inst-unshiftᵃ β (bnd i) = refl
inst-unshiftᵃ β (bse j) = refl

inst-unshiftᴿ : ∀ β R → substᴿᵉ (instᵉ₀ β) (⇑ᴿᵉ R) ≡ R
inst-unshiftᴿ β (`ᵃ α) = cong `ᵃ_ (inst-unshiftᵃ β α)
inst-unshiftᴿ β `ℕᴿ = refl
inst-unshiftᴿ β `𝔹ᴿ = refl
inst-unshiftᴿ β (R ⇒ᴿ T) =
  cong₂ _⇒ᴿ_ (inst-unshiftᴿ β R) (inst-unshiftᴿ β T)
inst-unshiftᴿ β (`∀ᴿ R) = cong `∀ᴿ (inst-unshiftᴿ β R)

------------------------------------------------------------------------
-- 6.  The stack travels
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
-- 7.  Freshness: the level L occurs nowhere
------------------------------------------------------------------------

data Fresh (L : ℕ) : Addr → Set where
  fr-lvl : ∀ {ℓ} → ¬ (ℓ ≡ L) → Fresh L (lvl ℓ)
  fr-bnd : ∀ {i} → Fresh L (bnd i)
  fr-bse : ∀ {j} → Fresh L (bse j)

fresh-⇑ᵃᵉ : Fresh L α → Fresh L (renᵃᵉ suc α)
fresh-⇑ᵃᵉ (fr-lvl ne) = fr-lvl ne
fresh-⇑ᵃᵉ fr-bnd = fr-bnd
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
-- 8.  Freshness travels along a conversion
------------------------------------------------------------------------
-- A crossing pops an assignment (whose address was already in the
-- stack) or pushes one (whose address the ELEMENT carries), so the
-- stack's freshness is exactly the conversion's.

pop-fresh : ∀ {L Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → FreshStk L Ss → Fresh L α × FreshStk L Ss′
pop-fresh pop-here (fs-asgn f fs) = f , fs
pop-fresh (pop-bind-b p) (fs-bind fs) =
  fr-bnd , fs-bind (proj₂ (pop-fresh p fs))
pop-fresh (pop-bind-l p) (fs-bind fs) with pop-fresh p fs
pop-fresh (pop-bind-l p) (fs-bind fs) | f , fs′ = f , fs-bind fs′
pop-fresh (pop-bind-e p) (fs-bind fs) =
  fr-bse , fs-bind (proj₂ (pop-fresh p fs))

push-fresh : ∀ {L Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → Fresh L α → FreshStk L Ss′ → FreshStk L Ss
push-fresh pop-here f fs = fs-asgn f fs
push-fresh (pop-bind-b p) f (fs-bind fs) = fs-bind (push-fresh p fr-bnd fs)
push-fresh (pop-bind-l p) f (fs-bind fs) = fs-bind (push-fresh p f fs)
push-fresh (pop-bind-e p) f (fs-bind fs) = fs-bind (push-fresh p fr-bse fs)

mutual
  convElt-freshStk : ∀ {L Sg Ssᵢ Ssₑ Bs ĉ A B}
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → FreshElt L ĉ → FreshStk L Ssₑ → FreshStk L Ssᵢ
  convElt-freshStk (conv-seal rep rd pop) (fe-seal f) fs =
    proj₂ (pop-fresh pop fs)
  convElt-freshStk (conv-unseal rep rd pop na) (fe-unseal f) fs =
    push-fresh pop f fs
  convElt-freshStk (conv-hide wf pop na) (fe-hide f) fs =
    proj₂ (pop-fresh pop fs)
  convElt-freshStk (conv-show wf pop na) (fe-show f) fs =
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
-- 9.  Injectivity away from the fresh level
------------------------------------------------------------------------
-- σ IS non-injective: `instᵉ₀ (lvl L)` sends `bse 0` and `lvl L` to the
-- same address.  That is the ONLY collision, so on `Fresh L` addresses
-- the map is injective, and `extsᵃᵉ` preserves the property.

inj-inst₀ : ∀ L → InjF L (instᵉ₀ (lvl L))
inj-inst₀ L {lvl ℓ} {lvl m} f g eq = eq
inj-inst₀ L {lvl ℓ} {bse zero} (fr-lvl ne) g eq = ⊥-elim (ne (lvl-inj eq))
inj-inst₀ L {bnd i} {bnd j} f g eq = eq
inj-inst₀ L {bnd i} {bse zero} f g ()
inj-inst₀ L {bnd i} {bse (suc j)} f g ()
inj-inst₀ L {bse zero} {lvl m} f (fr-lvl ne) eq =
  ⊥-elim (ne (sym (lvl-inj eq)))
inj-inst₀ L {bse zero} {bse zero} f g eq = refl
inj-inst₀ L {bse (suc i)} {bse (suc j)} f g eq =
  cong (λ k → bse (suc k)) (bse-inj eq)

-- What `extsᵃᵉ σ` does to a shifted base index, in the two forms σ can
-- take; the `lvl` branch remembers σ's own value, which is what lets the
-- inner injectivity fire.
ext-view : ∀ {σ} → NoBnd σ → ∀ j
  → (Σ[ ℓ ∈ ℕ ] ((σ j ≡ lvl ℓ)
      × (substAddrᵉ (extsᵃᵉ σ) (bse (suc j)) ≡ lvl ℓ)))
  ⊎ (Σ[ k ∈ ℕ ] substAddrᵉ (extsᵃᵉ σ) (bse (suc j)) ≡ bse (suc k))
ext-view nb j with nb j
ext-view nb j | inj₁ (ℓ , e) = inj₁ (ℓ , e , cong (renᵃᵉ suc) e)
ext-view nb j | inj₂ (k , e) = inj₂ (k , cong (renᵃᵉ suc) e)

inj-ext : ∀ {L σ} → NoBnd σ → InjF L σ → InjF L (extsᵃᵉ σ)
inj-ext nb inj {lvl ℓ} {lvl m} f g eq = eq
inj-ext nb inj {bnd i} {bnd j} f g eq = eq
inj-ext nb inj {bse zero} {bse zero} f g eq = refl
inj-ext {σ = σ} nb inj {lvl ℓ} {bse (suc j)} f g eq with ext-view nb j
inj-ext {σ = σ} nb inj {lvl ℓ} {bse (suc j)} f g eq | inj₁ (p , e1 , e2) =
  ⊥-elim (lvl≢bse (inj f fr-bse (trans (trans eq e2) (sym e1))))
inj-ext {σ = σ} nb inj {lvl ℓ} {bse (suc j)} f g eq | inj₂ (k , e2) =
  ⊥-elim (lvl≢bse (trans eq e2))
inj-ext {σ = σ} nb inj {bse (suc i)} {lvl m} f g eq with ext-view nb i
inj-ext {σ = σ} nb inj {bse (suc i)} {lvl m} f g eq | inj₁ (p , e1 , e2) =
  ⊥-elim (bse≢lvl (inj fr-bse g (trans e1 (trans (sym e2) eq))))
inj-ext {σ = σ} nb inj {bse (suc i)} {lvl m} f g eq | inj₂ (k , e2) =
  ⊥-elim (bse≢lvl (trans (sym e2) eq))
inj-ext {σ = σ} nb inj {bnd i} {bse (suc j)} f g eq with ext-view nb j
inj-ext {σ = σ} nb inj {bnd i} {bse (suc j)} f g eq | inj₁ (p , e1 , e2) =
  ⊥-elim (bnd≢lvl (trans eq e2))
inj-ext {σ = σ} nb inj {bnd i} {bse (suc j)} f g eq | inj₂ (k , e2) =
  ⊥-elim (bnd≢bse (trans eq e2))
inj-ext {σ = σ} nb inj {bse (suc i)} {bnd j} f g eq with ext-view nb i
inj-ext {σ = σ} nb inj {bse (suc i)} {bnd j} f g eq | inj₁ (p , e1 , e2) =
  ⊥-elim (lvl≢bnd (trans (sym e2) eq))
inj-ext {σ = σ} nb inj {bse (suc i)} {bnd j} f g eq | inj₂ (k , e2) =
  ⊥-elim (bse≢bnd (trans (sym e2) eq))
inj-ext {σ = σ} nb inj {bse zero} {bse (suc j)} f g eq with ext-view nb j
inj-ext {σ = σ} nb inj {bse zero} {bse (suc j)} f g eq | inj₁ (p , e1 , e2) =
  ⊥-elim (bse≢lvl (trans eq e2))
inj-ext {σ = σ} nb inj {bse zero} {bse (suc j)} f g eq | inj₂ (k , e2) =
  ⊥-elim (bse0≢bseS (trans eq e2))
inj-ext {σ = σ} nb inj {bse (suc i)} {bse zero} f g eq with ext-view nb i
inj-ext {σ = σ} nb inj {bse (suc i)} {bse zero} f g eq | inj₁ (p , e1 , e2) =
  ⊥-elim (lvl≢bse (trans (sym e2) eq))
inj-ext {σ = σ} nb inj {bse (suc i)} {bse zero} f g eq | inj₂ (k , e2) =
  ⊥-elim (bseS≢bse0 (trans (sym e2) eq))
inj-ext {σ = σ} nb inj {bse (suc i)} {bse (suc j)} f g eq =
  cong (λ k → bse (suc k)) (bse-inj (inj fr-bse fr-bse (suc-injᵉ eq)))

------------------------------------------------------------------------
-- 10.  The lookups, re-indexed by the address FORM
------------------------------------------------------------------------
-- A base substitution may turn a `bse` into a `lvl`, so every rule that
-- is chosen by the address form needs the view.

AddrOK : Addr → Set
AddrOK α = (Σ[ ℓ ∈ ℕ ] α ≡ lvl ℓ) ⊎ (Σ[ j ∈ ℕ ] α ≡ bse j)

∋a-move : ∀ {Σ Ss Ss′ Bs α} → AddrOK α
  → Σ ∣ (Ss ∥ Bs) ∋a α → Σ ∣ (Ss′ ∥ Bs) ∋a α
∋a-move (inj₁ (ℓ , refl)) (a-lvl l) = a-lvl l
∋a-move (inj₂ (j , refl)) p = ∋a-restk p

∋r-move : ∀ {Σ Ss Ss′ Bs α R} → AddrOK α
  → Σ ∣ (Ss ∥ Bs) ∋r α := R → Σ ∣ (Ss′ ∥ Bs) ∋r α := R
∋r-move (inj₁ (ℓ , refl)) (r-lvl l) = r-lvl l
∋r-move (inj₂ (j , refl)) p = ∋r-restk p

∋a-wk : ∀ {Σ Ss Bs e α} → AddrOK α
  → Σ ∣ (Ss ∥ Bs) ∋a α → Σ ∣ (Ss ∥ e ∷ Bs) ∋a renᵃᵉ suc α
∋a-wk (inj₁ (ℓ , refl)) (a-lvl l) = a-lvl l
∋a-wk {e = addr} (inj₂ (j , refl)) p = a-skip-addr p
∋a-wk {e = nuBind T} (inj₂ (j , refl)) p = a-skip-nu p

∋r-wk : ∀ {Σ Ss Bs e α R} → StoreOk Σ → AddrOK α
  → Σ ∣ (Ss ∥ Bs) ∋r α := R → Σ ∣ (Ss ∥ e ∷ Bs) ∋r renᵃᵉ suc α := ⇑ᴿᵉ R
∋r-wk sok (inj₁ (ℓ , refl)) (r-lvl l) rewrite lvl-fixed suc sok l = r-lvl l
∋r-wk {e = addr} sok (inj₂ (j , refl)) p = r-skip-addr p
∋r-wk {e = nuBind T} sok (inj₂ (j , refl)) p = r-skip-nu p

n-skip-bind : ∀ {Ss Bs X α} → AddrOK α
  → (Ss ∥ Bs) ∋n X := α → (bind ∷ Ss ∥ Bs) ∋n suc X := α
n-skip-bind (inj₁ (ℓ , refl)) p = n-skip-bind-l p
n-skip-bind (inj₂ (j , refl)) p = n-skip-bind-e p

-- The three `pop-bind-*` rules are one rule, up to the stack shift the
-- binder performs on the address.
pop-bind′ : ∀ {Ss Ss′ Bs X α β} → α ≡ ⇑ᵃ β
  → (Ss ∥ Bs) ▷ X := β ⇒ (Ss′ ∥ Bs)
  → (bind ∷ Ss ∥ Bs) ▷ suc X := α ⇒ (bind ∷ Ss′ ∥ Bs)
pop-bind′ {β = lvl ℓ} refl p = pop-bind-l p
pop-bind′ {β = bnd i} refl p = pop-bind-b p
pop-bind′ {β = bse j} refl p = pop-bind-e p

pop-inst : ∀ {σ Ss Ss′ Bs Bs′ X α} → NoBnd σ
  → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → (substStk σ Ss ∥ Bs′) ▷ X := substAddrᵉ σ α ⇒ (substStk σ Ss′ ∥ Bs′)
pop-inst nb pop-here = pop-here
pop-inst nb (pop-bind-b p) = pop-bind′ refl (pop-inst nb p)
pop-inst nb (pop-bind-l p) = pop-bind′ refl (pop-inst nb p)
pop-inst nb (pop-bind-e {j = j} p) =
  pop-bind′ (sym (nobnd-⇑ᵃ nb j)) (pop-inst nb p)

bnd≢sub : ∀ {σ i j} → NoBnd σ → bnd i ≡ substAddrᵉ σ (bse j) → ⊥
bnd≢sub {j = j} nb eq with nb j
bnd≢sub {j = j} nb eq | inj₁ (ℓ , e) = bnd≢lvl (trans eq e)
bnd≢sub {j = j} nb eq | inj₂ (k , e) = bnd≢bse (trans eq e)

-- A STORED representation mentions no base address, so a base
-- substitution leaves it alone — the `lvl-fixed` of proof.AddrWeaken.
wfᴿ-nobse-sub : ∀ {Sg Ss R} σ → Sg ∣ (Ss ∥ []) ⊢ᴿ R → substᴿᵉ σ R ≡ R
wfᴿ-nobse-sub σ (wfᴿ-var (a-lvl l)) = refl
wfᴿ-nobse-sub σ (wfᴿ-var a-here-bind) = refl
wfᴿ-nobse-sub σ (wfᴿ-var (a-skip-bind p)) = refl
wfᴿ-nobse-sub σ (wfᴿ-var (a-skip-asgn p)) = refl
wfᴿ-nobse-sub σ wfᴿ-ℕ = refl
wfᴿ-nobse-sub σ wfᴿ-𝔹 = refl
wfᴿ-nobse-sub σ (wfᴿ-⇒ a b) =
  cong₂ _⇒ᴿ_ (wfᴿ-nobse-sub σ a) (wfᴿ-nobse-sub σ b)
wfᴿ-nobse-sub σ (wfᴿ-∀ a) = cong `∀ᴿ (wfᴿ-nobse-sub σ a)

lvl-fixed-sub : ∀ {Sg ℓ R} σ → StoreOk Sg → Sg ∋ˡ ℓ := R
  → substᴿᵉ σ R ≡ R
lvl-fixed-sub σ sok l = wfᴿ-nobse-sub σ (sok l)

------------------------------------------------------------------------
-- 11.  A base SUBSTITUTION between contexts
------------------------------------------------------------------------
-- The mirror of `Renamesᵇ` (proof.AddrWeaken): three closure properties,
-- one per lookup, plus the reflection `sub-n⁻` that the NEGATIVE
-- premises need.  `sub-n⁻` also reports that the reflected address is
-- FRESH — the context's crossing assignments are store-scoped — which is
-- exactly what `notasgn-inst` must feed to `sub-inj`.

record Substsᵇ (Sg : Store) (L : ℕ) (σ : SubstAddr) (Γ Γ′ : Ctxᵗ) : Set
  where
  field
    sub-ok  : StoreOk Sg
    sub-nb  : NoBnd σ
    sub-inj : InjF L σ
    sub-a   : ∀ {α} → Sg ∣ Γ ∋a α → Sg ∣ Γ′ ∋a substAddrᵉ σ α
    sub-n   : ∀ {X α} → Γ ∋n X := α → Γ′ ∋n X := substAddrᵉ σ α
    sub-r   : ∀ {α R} → Sg ∣ Γ ∋r α := R
            → Sg ∣ Γ′ ∋r substAddrᵉ σ α := substᴿᵉ σ R
    sub-n⁻  : ∀ {X α} → Γ′ ∋n X := α
            → Σ[ β ∈ Addr ]
                ((Γ ∋n X := β) × (Fresh L β × (α ≡ substAddrᵉ σ β)))
open Substsᵇ

------------------------------------------------------------------------
-- 12.  Closure under the stack binders
------------------------------------------------------------------------

sub-bind : Substsᵇ Sg L σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Substsᵇ Sg L σ (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
sub-ok (sub-bind r) = sub-ok r
sub-nb (sub-bind r) = sub-nb r
sub-inj (sub-bind r) = sub-inj r
sub-a (sub-bind r) a-here-bind = a-here-bind
sub-a (sub-bind r) (a-skip-bind p) = a-skip-bind (sub-a r p)
sub-a (sub-bind r) (a-lvl l) = a-lvl l
sub-a (sub-bind r) a-here-addr = ∋a-move (sub-nb r zero) (sub-a r a-here-addr)
sub-a (sub-bind r) a-here-nu = ∋a-move (sub-nb r zero) (sub-a r a-here-nu)
sub-a (sub-bind r) (a-skip-addr {j = j} p) =
  ∋a-move (sub-nb r (suc j)) (sub-a r (a-skip-addr (∋a-restk p)))
sub-a (sub-bind r) (a-skip-nu {j = j} p) =
  ∋a-move (sub-nb r (suc j)) (sub-a r (a-skip-nu (∋a-restk p)))
sub-n (sub-bind r) n-here-bind = n-here-bind
sub-n (sub-bind r) (n-skip-bind-b p) = n-skip-bind-b (sub-n r p)
sub-n (sub-bind r) (n-skip-bind-l p) = n-skip-bind-l (sub-n r p)
sub-n (sub-bind r) (n-skip-bind-e {j = j} p) =
  n-skip-bind (sub-nb r j) (sub-n r p)
sub-r (sub-bind {σ = σ} r) (r-skip-bind {R = R} p)
  rewrite substᴿᵉ-⇑ᴿ (sub-nb r) R = r-skip-bind (sub-r r p)
sub-r (sub-bind r) r-here = ∋r-move (sub-nb r zero) (sub-r r r-here)
sub-r (sub-bind r) (r-skip-addr {j = j} p) =
  ∋r-move (sub-nb r (suc j)) (sub-r r (r-skip-addr (∋r-restk p)))
sub-r (sub-bind r) (r-skip-nu {j = j} p) =
  ∋r-move (sub-nb r (suc j)) (sub-r r (r-skip-nu (∋r-restk p)))
sub-r (sub-bind {σ = σ} r) (r-lvl l)
  rewrite lvl-fixed-sub σ (sub-ok r) l = r-lvl l
sub-n⁻ (sub-bind r) n-here-bind = bnd zero , n-here-bind , fr-bnd , refl
sub-n⁻ (sub-bind r) (n-skip-bind-b p) with sub-n⁻ r p
sub-n⁻ (sub-bind r) (n-skip-bind-b p) | bnd i , q , f , refl =
  bnd (suc i) , n-skip-bind-b q , fr-bnd , refl
sub-n⁻ (sub-bind r) (n-skip-bind-b p) | bse j , q , f , eq =
  ⊥-elim (bnd≢sub (sub-nb r) eq)
sub-n⁻ (sub-bind r) (n-skip-bind-l p) with sub-n⁻ r p
sub-n⁻ (sub-bind r) (n-skip-bind-l p) | lvl m , q , f , eq =
  lvl m , n-skip-bind-l q , f , eq
sub-n⁻ (sub-bind r) (n-skip-bind-l p) | bse j , q , f , eq =
  bse j , n-skip-bind-e q , fr-bse , eq
sub-n⁻ (sub-bind r) (n-skip-bind-e p) with sub-n⁻ r p
sub-n⁻ (sub-bind r) (n-skip-bind-e p) | bse k , q , f , eq =
  bse k , n-skip-bind-e q , fr-bse , eq

sub-asgn : Fresh L α → Substsᵇ Sg L σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Substsᵇ Sg L σ (asgn α ∷ Ss ∥ Bs) (asgn (substAddrᵉ σ α) ∷ Ss′ ∥ Bs′)
sub-ok (sub-asgn f r) = sub-ok r
sub-nb (sub-asgn f r) = sub-nb r
sub-inj (sub-asgn f r) = sub-inj r
sub-a (sub-asgn f r) (a-skip-asgn p) = a-skip-asgn (sub-a r p)
sub-a (sub-asgn f r) (a-lvl l) = a-lvl l
sub-a (sub-asgn f r) a-here-addr =
  ∋a-move (sub-nb r zero) (sub-a r a-here-addr)
sub-a (sub-asgn f r) a-here-nu = ∋a-move (sub-nb r zero) (sub-a r a-here-nu)
sub-a (sub-asgn f r) (a-skip-addr {j = j} p) =
  ∋a-move (sub-nb r (suc j)) (sub-a r (a-skip-addr (∋a-restk p)))
sub-a (sub-asgn f r) (a-skip-nu {j = j} p) =
  ∋a-move (sub-nb r (suc j)) (sub-a r (a-skip-nu (∋a-restk p)))
sub-n (sub-asgn f r) n-here-asgn = n-here-asgn
sub-n (sub-asgn f r) (n-skip-asgn p) = n-skip-asgn (sub-n r p)
sub-r (sub-asgn f r) (r-skip-asgn p) = r-skip-asgn (sub-r r p)
sub-r (sub-asgn f r) r-here = ∋r-move (sub-nb r zero) (sub-r r r-here)
sub-r (sub-asgn f r) (r-skip-addr {j = j} p) =
  ∋r-move (sub-nb r (suc j)) (sub-r r (r-skip-addr (∋r-restk p)))
sub-r (sub-asgn f r) (r-skip-nu {j = j} p) =
  ∋r-move (sub-nb r (suc j)) (sub-r r (r-skip-nu (∋r-restk p)))
sub-r (sub-asgn {σ = σ} f r) (r-lvl l)
  rewrite lvl-fixed-sub σ (sub-ok r) l = r-lvl l
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
-- extends; `∀` and `∀ᴿ` bind on the stack, so they do not.

substEnt : SubstAddr → BaseEnt → BaseEnt
substEnt σ addr = addr
substEnt σ (nuBind R) = nuBind (substᴿᵉ σ R)

sub-ext : ∀ {Sg L σ Bs Bs′ e}
  → Substsᵇ Sg L σ ([] ∥ Bs) ([] ∥ Bs′)
  → Substsᵇ Sg L (extsᵃᵉ σ) ([] ∥ e ∷ Bs) ([] ∥ substEnt σ e ∷ Bs′)
sub-ok (sub-ext r) = sub-ok r
sub-nb (sub-ext r) = noBnd-ext (sub-nb r)
sub-inj (sub-ext r) = inj-ext (sub-nb r) (sub-inj r)
sub-n (sub-ext r) ()
sub-n⁻ (sub-ext r) ()
sub-a (sub-ext r) (a-lvl l) = a-lvl l
sub-a (sub-ext {e = addr} r) a-here-addr = a-here-addr
sub-a (sub-ext {e = nuBind T} r) a-here-nu = a-here-nu
sub-a (sub-ext {e = addr} r) (a-skip-addr {j = j} p) =
  ∋a-wk (sub-nb r j) (sub-a r p)
sub-a (sub-ext {e = nuBind T} r) (a-skip-nu {j = j} p) =
  ∋a-wk (sub-nb r j) (sub-a r p)
sub-r (sub-ext {σ = σ} r) (r-lvl l)
  rewrite lvl-fixed-sub (extsᵃᵉ σ) (sub-ok r) l = r-lvl l
sub-r (sub-ext {σ = σ} {e = nuBind T} r) r-here
  rewrite substᴿᵉ-ext σ T = r-here
sub-r (sub-ext {σ = σ} {e = addr} r) (r-skip-addr {j = j} {R = R} p)
  rewrite substᴿᵉ-ext σ R = ∋r-wk (sub-ok r) (sub-nb r j) (sub-r r p)
sub-r (sub-ext {σ = σ} {e = nuBind T} r) (r-skip-nu {j = j} {R = R} p)
  rewrite substᴿᵉ-ext σ R = ∋r-wk (sub-ok r) (sub-nb r j) (sub-r r p)

-- THE INSTANCE `Alloc` uses: the ν's entry is discharged to the fresh
-- store level, and every older base address slides down one.
sub-inst₀ : ∀ Sg {Bs R} → StoreOk (Sg ∷ʳ R)
  → Substsᵇ (Sg ∷ʳ R) (length Sg) (instᵉ₀ (lvl (length Sg)))
      ([] ∥ nuBind R ∷ Bs) ([] ∥ Bs)
sub-ok (sub-inst₀ Sg sok) = sok
sub-nb (sub-inst₀ Sg sok) = noBnd-inst₀ (length Sg)
sub-inj (sub-inst₀ Sg sok) = inj-inst₀ (length Sg)
sub-n (sub-inst₀ Sg sok) ()
sub-n⁻ (sub-inst₀ Sg sok) ()
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
wfᵗ-inst r (wf-var n) = wf-var (sub-n r n)
wfᵗ-inst r wf-ℕ = wf-ℕ
wfᵗ-inst r wf-𝔹 = wf-𝔹
wfᵗ-inst r (wf-⇒ a b) = wf-⇒ (wfᵗ-inst r a) (wfᵗ-inst r b)
wfᵗ-inst r (wf-∀ a) = wf-∀ (wfᵗ-inst (sub-bind r) a)

wfᴿ-inst : ∀ {Sg L σ Γ Γ′ R} → Substsᵇ Sg L σ Γ Γ′
  → Sg ∣ Γ ⊢ᴿ R → Sg ∣ Γ′ ⊢ᴿ substᴿᵉ σ R
wfᴿ-inst r (wfᴿ-var a) = wfᴿ-var (sub-a r a)
wfᴿ-inst r wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-inst r wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-inst r (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-inst r a) (wfᴿ-inst r b)
wfᴿ-inst r (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-inst (sub-bind r) a)

read-inst : ∀ {Sg L σ Γ Γ′ R A} → Substsᵇ Sg L σ Γ Γ′
  → Sg ∣ Γ ⊢ R ⇓ A → Sg ∣ Γ′ ⊢ substᴿᵉ σ R ⇓ A
read-inst r (read-var n) = read-var (sub-n r n)
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
              (pop-inst (sub-nb r) pop)
  convElt-inst r (fe-unseal f) fs (conv-unseal rep rd pop na) =
    conv-unseal (sub-r (sub-stk r (push-fresh pop f fs)) rep)
                (read-inst (sub-stk r fs) rd)
                (pop-inst (sub-nb r) pop)
                (notasgn-inst (sub-stk r fs) f na)
  convElt-inst r (fe-hide f) fs (conv-hide wf pop na) =
    conv-hide (wfᵗ-inst (sub-stk r (proj₂ (pop-fresh pop fs))) wf)
              (pop-inst (sub-nb r) pop)
              (notasgn-inst (sub-stk r (proj₂ (pop-fresh pop fs))) f na)
  convElt-inst r (fe-show f) fs (conv-show wf pop na) =
    conv-show (wfᵗ-inst (sub-stk r fs) wf)
              (pop-inst (sub-nb r) pop)
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
-- (an `all` binds a STACK address), so everything the views decide by
-- looking at a type is literally unchanged and everything they decide by
-- looking at element shapes commutes.  The one place the substitution is
-- visible is `all⁺`, which hoists a crossing under the ∀ element's
-- binder — and that shift commutes because σ produces no `bnd`.

target-inst : ∀ σ c → target (substAddrConv σ c) ≡ target c
target-inst σ (id A) = refl
target-inst σ (ĉ ∷ᶜ c) = target-inst σ c

elts-inst : ∀ σ c → elts (substAddrConv σ c) ≡ map (substAddrElt σ) (elts c)
elts-inst σ (id A) = refl
elts-inst σ (ĉ ∷ᶜ c) = cong (substAddrElt σ ĉ ∷_) (elts-inst σ c)

substAddrᵉ-⇑ᵃ : NoBnd σ → ∀ α → substAddrᵉ σ (⇑ᵃ α) ≡ ⇑ᵃ (substAddrᵉ σ α)
substAddrᵉ-⇑ᵃ nb α = substAddrᵉ-renᵃ nb suc α

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

all⁺-inst : ∀ {σ} → NoBnd σ → ∀ ĉ
  → all⁺ (substAddrElt σ ĉ) ≡ mapEls′ σ (all⁺ ĉ)
all⁺-inst nb (seal X α)   = refl
all⁺-inst nb (unseal X α) = refl
all⁺-inst nb (hide X α) =
  cong (λ β → just (hide (suc X) β ∷ [])) (sym (substAddrᵉ-⇑ᵃ nb α))
all⁺-inst nb (show X α) =
  cong (λ β → just (show (suc X) β ∷ [])) (sym (substAddrᵉ-⇑ᵃ nb α))
all⁺-inst nb (s ↦ t)      = refl
all⁺-inst {σ} nb (all s)  = cong just (elts-inst σ s)

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

allElts-inst : ∀ {σ} → NoBnd σ → ∀ Es
  → allElts (map (substAddrElt σ) Es) ≡ mapEls′ σ (allElts Es)
allElts-inst nb [] = refl
allElts-inst {σ} nb (ĉ ∷ Es)
  rewrite all⁺-inst nb ĉ | allElts-inst nb Es =
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

allView-inst : ∀ {σ} → NoBnd σ → ∀ c {d} → allView c ≡ just d
  → Σ[ e ∈ Conv ] allView (substAddrConv σ c) ≡ just e
allView-inst {σ} nb c eq
  with allFrom-inst σ (allElts (elts c)) (target c) eq
allView-inst {σ} nb c eq | e , eq′ = e , unfolded
  where
  unfolded :
      allFrom (allElts (elts (substAddrConv σ c)))
              (target (substAddrConv σ c))
    ≡ just e
  unfolded
    rewrite elts-inst σ c | allElts-inst nb (elts c) | target-inst σ c =
    eq′

inert-inst : ∀ {σ c} → NoBnd σ → Inert c → Inert (substAddrConv σ c)
inert-inst {σ} {c} nb (inert-arr A₀ eq) with arr-inst σ A₀ c eq
inert-inst {σ} {c} nb (inert-arr A₀ eq) | d₁ , d₂ , eq′ = inert-arr A₀ eq′
inert-inst {σ} {c} nb (inert-all eq) with allView-inst nb c eq
inert-inst {σ} {c} nb (inert-all eq) | e , eq′ = inert-all eq′
inert-inst {σ} {c} nb (inert-var eq) =
  inert-var (trans (target-inst σ c) eq)

------------------------------------------------------------------------
-- 17.  Normal forms survive, PROVIDED the addresses are fresh
------------------------------------------------------------------------
-- `fuse` cancels on an address EQUALITY, so a substitution that
-- identifies two addresses turns a normal form into a redex.  Away from
-- `lvl L` the substitution is injective (§9), so a pair that did not
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
fuse-inst {σ = σ} inj (unseal X α) (seal Y β) (fe-unseal f) (fe-seal g) eq
  with X ≟ Y | α ≟ᵃ β | substAddrᵉ σ α ≟ᵃ substAddrᵉ σ β
fuse-inst {σ = σ} inj (unseal X α) (seal Y β) (fe-unseal f) (fe-seal g) ()
  | yes _ | yes _ | _
fuse-inst {σ = σ} inj (unseal X α) (seal Y β) (fe-unseal f) (fe-seal g) eq
  | yes _ | no ne | yes e = ⊥-elim (ne (inj f g e))
fuse-inst {σ = σ} inj (unseal X α) (seal Y β) (fe-unseal f) (fe-seal g) eq
  | yes _ | no _ | no _ = refl
fuse-inst {σ = σ} inj (unseal X α) (seal Y β) (fe-unseal f) (fe-seal g) eq
  | no _ | _ | _ = refl
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
-- `extsᵃᵉ` preserves both `NoBnd` and the restricted injectivity.

mutual
  simple-inst : ∀ {L σ V} → InjF L σ → NoBnd σ → FreshM L V → Simple V
    → Simple (substAddrᴹ σ V)
  simple-inst inj nb f S$ = S$
  simple-inst inj nb f S# = S#
  simple-inst inj nb f Sƛ = Sƛ
  simple-inst inj nb (fm-Λ f) (SΛ v) =
    SΛ (value-inst (inj-ext nb inj) (noBnd-ext nb) f v)

  value-inst : ∀ {L σ V} → InjF L σ → NoBnd σ → FreshM L V → Value V
    → Value (substAddrᴹ σ V)
  value-inst inj nb f (Vs s) = Vs (simple-inst inj nb f s)
  value-inst inj nb (fm-⟨⟩ f g) (V⟨⟩ s nf inrt) =
    V⟨⟩ (simple-inst inj nb f s) (nf-inst inj g nf) (inert-inst nb inrt)

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
  rewrite eq =
  ⊢Λ (value-inst (inj-ext (sub-nb r) (sub-inj r)) (noBnd-ext (sub-nb r))
                 f v)
     ⊢V′
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
-- not in the body's conversions.  §21 shows they cannot be dropped.

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
-- 21.  THE FRESHNESS PREMISES ARE NECESSARY
------------------------------------------------------------------------
-- Without them the statement is FALSE, and not marginally so: the
-- witness below is a one-crossing boundary over a numeral.
--
-- The ambient context assigns the name 0 to the level 0, which the
-- EMPTY store does not contain — nothing in the system forbids that,
-- because `conv-hide`'s address comes from the CONTEXT (its premises
-- are `⊢ᵗ`, a pop, and `NotAssigned`) and never from the store.  The
-- body's conversion crosses `bse 0` (the ν's own address) inward and
-- `lvl 0` outward; the two addresses differ, so the pair does not
-- `fuse` and the conversion is a normal form.  `Alloc` then sends
-- `bse 0` to `lvl 0` — the two crossings become a cancelling pair, the
-- conversion is no longer normal, and `⊢⟨⟩` cannot fire.

private
  Δ₀ : Ctxᵗ
  Δ₀ = asgn (lvl zero) ∷ [] ∥ []

  flat-Δ₀ : Flat Δ₀
  flat-Δ₀ = flat (fu-asgn fu-[]) refl

  sok-[] : StoreOk []
  sok-[] ()

  Δ₁ Δ₃ : Ctxᵗ
  Δ₁ = asgn (lvl zero) ∷ [] ∥ nuBind `ℕᴿ ∷ []
  Δ₃ = asgn (bse zero) ∷ [] ∥ nuBind `ℕᴿ ∷ []

  c₀ : Conv
  c₀ = show zero (bse zero) ∷ᶜ hide zero (lvl zero) ∷ᶜ id `ℕ

  ⊢c₀ : [] ∣ Δ₃ ⊢ c₀ ∶ `ℕ ⇝ `ℕ ⊣ Δ₁
  ⊢c₀ = conv-cons (conv-show wf-ℕ pop-here (λ ()))
          (conv-cons (conv-hide wf-ℕ pop-here (λ ())) (conv-id wf-ℕ))

  nf-c₀ : NF c₀
  nf-c₀ = nf-cons nf-show (nf-cons nf-hide nf-id irr-id) (irr-cons refl)

  M₀ : Term
  M₀ = ($ zero) ⟨ c₀ ⟩

  ⊢νM₀ : [] ∣ Δ₀ ∣ [] ⊢ ν `ℕᴿ ∙ M₀ ⦂ `ℕ
  ⊢νM₀ = ⊢ν wfᴿ-ℕ (⊢⟨⟩ nf-c₀ ⊢$ ⊢c₀)

  -- after the substitution the two crossings FUSE
  ¬⊢M₀ : ¬ (([] ∷ʳ `ℕᴿ) ∣ Δ₀ ∣ [] ⊢ M₀ [ lvl zero ]ᵃᴹ ⦂ `ℕ)
  ¬⊢M₀ (⊢⟨⟩ (nf-cons hd tl (irr-cons ())) m c)

-- The statement WITHOUT the freshness premises.
AllocClaim : Set
AllocClaim = ∀ {Sg Δ Γ R M A}
  → StoreOk Sg → Flat Δ
  → Sg ∣ Δ ∣ Γ ⊢ ν R ∙ M ⦂ A
  → (Sg ∷ʳ R) ∣ Δ ∣ Γ ⊢ M [ lvl (length Sg) ]ᵃᴹ ⦂ A

alloc-claim-refuted : ¬ AllocClaim
alloc-claim-refuted f = ¬⊢M₀ (f sok-[] flat-Δ₀ ⊢νM₀)

------------------------------------------------------------------------
-- 22.  WHAT A GROUNDED RULE SET WOULD GIVE
------------------------------------------------------------------------
-- `Fresh (length Sg)` is exactly "in scope in Sg" for a level, and THAT
-- is derivable from `∋a` — which `conv-seal` and `conv-unseal` already
-- carry (through `∋r`), and which `conv-hide` and `conv-show` do not.
-- So the premises of §20 are not a new invariant in search of a home:
-- they are the reading of `∋a` that the two identity crossings are
-- currently missing.

∋a-fresh : ∀ {Sg Γ} → Sg ∣ Γ ∋a lvl (length Sg) → ⊥
∋a-fresh (a-lvl l) = ∋ˡ-fresh l

∋r-fresh : ∀ {Sg Γ R} → Sg ∣ Γ ∋r lvl (length Sg) := R → ⊥
∋r-fresh (r-lvl l) = ∋ˡ-fresh l

fresh-of-∋a : ∀ {Sg Γ α} → Sg ∣ Γ ∋a α → Fresh (length Sg) α
fresh-of-∋a (a-lvl l) = fr-lvl λ { refl → ∋ˡ-fresh l }
fresh-of-∋a a-here-bind = fr-bnd
fresh-of-∋a (a-skip-bind p) = fr-bnd
fresh-of-∋a (a-skip-asgn p) = fr-bnd
fresh-of-∋a a-here-addr = fr-bse
fresh-of-∋a a-here-nu = fr-bse
fresh-of-∋a (a-skip-addr p) = fr-bse
fresh-of-∋a (a-skip-nu p) = fr-bse

fresh-of-∋r : ∀ {Sg Γ α R} → Sg ∣ Γ ∋r α := R → Fresh (length Sg) α
fresh-of-∋r (r-lvl l) = fr-lvl λ { refl → ∋ˡ-fresh l }
fresh-of-∋r (r-skip-bind p) = fr-bnd
fresh-of-∋r (r-skip-asgn p) = fr-bnd
fresh-of-∋r r-here = fr-bse
fresh-of-∋r (r-skip-addr p) = fr-bse
fresh-of-∋r (r-skip-nu p) = fr-bse

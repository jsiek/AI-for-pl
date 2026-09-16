module strong.proof.SubstAnnTyping where

-- Strong System F v8 — the typing of `substAnn`, the type substitution
-- that `instReveal`/`instConceal` perform on a conversion's
-- ANNOTATIONS when a `∀` is instantiated.
--
-- `substAnn X S c` REMOVES the name slot X from the context: the
-- annotations are closed over X by `closeAt X S`, and every crossing's
-- NAME is decremented by `nameSub X` exactly when it lies above the
-- slot.  So the lemma transports a typing derivation from a context
-- that still has the slot to the one that has lost it.  It is the
-- exact inverse of `proof.ArrTyping`'s `pop-renames`/`wf-shift`, which
-- INSERT a slot and rename by `shiftAtᵗ X`.
--
-- THE SHAPE OF THE RELATION.  `DropBind` is an inductive relation in
-- constructor form, not an equation on lists, because every judgment
-- this proof lifts (`∋n`, `∋ᵗ`, `∋b`, `⊢ᵗ`, `⇓`, `▷ := ⇒`) is itself
-- defined by recursion down the stack: a `here`/`there` relation
-- unifies with those derivations one constructor at a time, while `Δ ≡
-- Ss ++ bind ∷ Ss′` would leave every case blocked on an append.  Two
-- further choices:
--
--   * `drop-there` steps past a `bind` ONLY.  The slot removed is
--     always a `∀`'s binder assignment, and the pop judgment already
--     insists that a crossing assignment has nothing but `bind`s above
--     it (`pop-bind` is its only non-base rule).  Making `DropBind`
--     agree with that discipline is what makes the crossing name Y and
--     the slot X comparable at all: the slot sits at stack position X
--     with X `bind`s above it, a crossing sits at position Y with Y
--     `bind`s above it, so X ≢ Y comes for free (`slot-≢`), and in the
--     `seal`/`hide` direction X < Y is derivable rather than assumed.
--
--   * the relation is defined on STACKS (`DropBindS`) and wrapped by a
--     one-constructor context relation (`DropBind`, via `drop-ctx`)
--     that pins the two bases to be the SAME list.  Dropping a binder
--     assignment is a pure stack operation — that is the whole point of
--     the v8 stack/base split — and the wrapper means a single pattern
--     match puts both contexts in `_∥_` form over one base, so none of
--     the lemmas below has to re-derive `bas Γ ≡ bas Γ′`.
--
-- WHAT V8 MADE FREE.  In v7 this file carried three side conditions.
-- Two of them are gone:
--
--   * `NotBnd α` — "the crossing's address is not a `bnd`".  There IS
--     no `bnd`: a `∀` binds a type VARIABLE, not an address, so every
--     address is a store level or a base binder, and NEITHER address
--     lookup reads the stack (`∋a-restk`, `∋r-restk`).  Both the
--     predicate and the case analyses it drove are deleted.
--
--   * `NoBndReps Sg` — "a representation reached at a non-`bnd`
--     address mentions no `bnd`".  A `∀ᴿ`-bound variable is now a
--     SEPARATE constructor `` `ᵛ_ ``, so it cannot be confused with a
--     free address, and its scope discipline is exactly `⊢ᴿ`'s index:
--     what `read-drop` needs is that `R`'s `` `ᵛ ``s are bound by `R`'s
--     own `∀ᴿ`s, i.e. `Sg ∣ Γ ⊢ᴿ[ 0 ] R`, which is `StoreOk` for a
--     level and `⊢ν`'s own first premise for a `ν`.  `RepsWf` (§6) is
--     that residue, and it is the ONLY thing left of condition (3).
--
-- The genuine side conditions are `Closedᵗ S` (§2) and `SlotFree` (§6).

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (_≟_; _<?_; ≤-refl; ≤-trans; ≰⇒>)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.TypeSubst using (rename-subst-commute; rename-subst)
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.proof.Interior using (pop-base)
open import strong.proof.AddrWeaken using (conv-base)
open import strong.proof.SrcTyping using (shiftAt-below; shiftAt-above)

private
  variable
    Sg : Store
    Bs Bs′ : List BaseEnt
    Ss Ss′ Ss″ Ssₑ : List StackEnt
    Γ Γ′ Γ″ Γᵢ : Ctxᵗ
    A B S : Ty
    R : RepTy
    X Y Z : ℕ
    α : Addr
    c s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- §0  Arithmetic, kept local and minimal
------------------------------------------------------------------------

¬<-¬≡-> : ¬ (X < Z) → ¬ (X ≡ Z) → Z < X
¬<-¬≡-> {zero} {zero} nlt ne = ⊥-elim (ne refl)
¬<-¬≡-> {zero} {suc Z} nlt ne = ⊥-elim (nlt (s≤s z≤n))
¬<-¬≡-> {suc X} {zero} nlt ne = s≤s z≤n
¬<-¬≡-> {suc X} {suc Z} nlt ne =
  s≤s (¬<-¬≡-> (λ lt → nlt (s≤s lt)) (λ eq → ne (cong suc eq)))

<-irr : X < X → ⊥
<-irr (s≤s lt) = <-irr lt

<-asym : X < Z → Z < X → ⊥
<-asym (s≤s p) (s≤s q) = <-asym q p

<-≢ : X < Y → ¬ (X ≡ Y)
<-≢ lt refl = <-irr lt

<-zero : X < zero → ⊥
<-zero ()

pos-of : X < Z → zero < Z
pos-of {Z = suc Z} lt = s≤s z≤n

suc-pred : zero < Z → suc (Z ∸ 1) ≡ Z
suc-pred {Z = suc Z} lt = refl

pred-< : zero < Z → (Z ∸ 1) < Z
pred-< {Z = suc Z} lt = ≤-refl

le-pred : suc Z ≤ Y → Z ≤ (Y ∸ 1)
le-pred {Y = suc Y} (s≤s le) = le

pred≤ : suc Z ≤ suc Y → Z ≤ Y
pred≤ (s≤s le) = le

n≤suc : ∀ n → n ≤ suc n
n≤suc zero = z≤n
n≤suc (suc n) = s≤s (n≤suc n)

------------------------------------------------------------------------
-- §1  `nameSub` and `closeEnv`, pointwise
------------------------------------------------------------------------

nameSub-gt : ∀ X Y → X < Y → nameSub X Y ≡ (Y ∸ 1)
nameSub-gt X Y lt with X <? Y
nameSub-gt X Y lt | yes _ = refl
nameSub-gt X Y lt | no nlt = ⊥-elim (nlt lt)

nameSub-le : ∀ X Y → ¬ (X < Y) → nameSub X Y ≡ Y
nameSub-le X Y nlt with X <? Y
nameSub-le X Y nlt | yes lt = ⊥-elim (nlt lt)
nameSub-le X Y nlt | no _ = refl

-- the one fact every `there`/`all` step needs: the slot and the name
-- it reindexes move up together
nameSub-suc : ∀ X Y → nameSub (suc X) (suc Y) ≡ suc (nameSub X Y)
nameSub-suc X Y with X <? Y
nameSub-suc X Y | yes lt
  rewrite nameSub-gt (suc X) (suc Y) (s≤s lt) =
  sym (suc-pred (pos-of lt))
nameSub-suc X Y | no nlt =
  nameSub-le (suc X) (suc Y) (λ lt → nlt (pred≤ lt))

closeEnv-eq : ∀ X S → closeEnv X S X ≡ S
closeEnv-eq X S with X ≟ X
closeEnv-eq X S | yes _ = refl
closeEnv-eq X S | no ne = ⊥-elim (ne refl)

closeEnv-gt : ∀ X S Z → X < Z → closeEnv X S Z ≡ ` (Z ∸ 1)
closeEnv-gt X S Z lt with X ≟ Z
closeEnv-gt X S Z lt | yes refl = ⊥-elim (<-irr lt)
closeEnv-gt X S Z lt | no _ with X <? Z
closeEnv-gt X S Z lt | no _ | yes _ = refl
closeEnv-gt X S Z lt | no _ | no nlt = ⊥-elim (nlt lt)

closeEnv-lt : ∀ X S Z → Z < X → closeEnv X S Z ≡ ` Z
closeEnv-lt X S Z lt with X ≟ Z
closeEnv-lt X S Z lt | yes refl = ⊥-elim (<-irr lt)
closeEnv-lt X S Z lt | no _ with X <? Z
closeEnv-lt X S Z lt | no _ | yes gt = ⊥-elim (<-asym gt lt)
closeEnv-lt X S Z lt | no _ | no _ = refl

closeEnv-≢ : ∀ X S Z → ¬ (X ≡ Z) → closeEnv X S Z ≡ ` (nameSub X Z)
closeEnv-≢ X S Z ne with X <? Z
closeEnv-≢ X S Z ne | yes lt = closeEnv-gt X S Z lt
closeEnv-≢ X S Z ne | no nlt = closeEnv-lt X S Z (¬<-¬≡-> nlt ne)

------------------------------------------------------------------------
-- §2  Closed types: SIDE CONDITION (1) on S
------------------------------------------------------------------------
-- Going inward a conversion PUSHES assignments, so the small contexts
-- grow and a type living at the exterior must be shifted to be read in
-- the interior — but `substAnn` carries the same S past every
-- crossing (it shifts S only under `all`).  `closeEnv-shift` below
-- isolates this exactly: every variable but the slot itself matches on
-- the nose, and the slot needs `renameᵗ (shiftAtᵗ (nameSub X Y)) S ≡
-- S`.  A closed S — the type argument of a `•B[A]` on ground data, as
-- in `Examples.§14`, where S is `𝔹 — supplies it.

data NoFreeᵗ : ℕ → Ty → Set where
  nf-var : ∀ {n} → X < n → NoFreeᵗ n (` X)
  nf-ℕ   : ∀ {n} → NoFreeᵗ n `ℕ
  nf-𝔹   : ∀ {n} → NoFreeᵗ n `𝔹
  nf-⇒   : ∀ {n} → NoFreeᵗ n A → NoFreeᵗ n B → NoFreeᵗ n (A ⇒ B)
  nf-∀   : ∀ {n} → NoFreeᵗ (suc n) A → NoFreeᵗ n (`∀ A)

Closedᵗ : Ty → Set
Closedᵗ S = NoFreeᵗ zero S

nofree-ren : ∀ {n ρ} → NoFreeᵗ n S → (∀ Y → Y < n → ρ Y ≡ Y)
  → renameᵗ ρ S ≡ S
nofree-ren (nf-var {X = X} lt) h = cong `_ (h X lt)
nofree-ren nf-ℕ h = refl
nofree-ren nf-𝔹 h = refl
nofree-ren (nf-⇒ a b) h = cong₂ _⇒_ (nofree-ren a h) (nofree-ren b h)
nofree-ren {ρ = ρ} (nf-∀ {n = n} a) h = cong `∀ (nofree-ren a h-ext)
  where
  h-ext : ∀ Y → Y < suc n → extᵗ ρ Y ≡ Y
  h-ext zero lt = refl
  h-ext (suc Y) (s≤s lt) = cong suc (h Y lt)

closed-ren : Closedᵗ S → ∀ ρ → renameᵗ ρ S ≡ S
closed-ren cl ρ = nofree-ren cl (λ Y ())

closed-⇑ : Closedᵗ S → Closedᵗ (renameᵗ suc S)
closed-⇑ cl rewrite closed-ren cl suc = cl

------------------------------------------------------------------------
-- §3  The renaming and substitution algebras on name lookups
------------------------------------------------------------------------
-- The mirror of `proof.ArrTyping`'s `Renamesᵗ`/`ext-renames`/`wf-ren`.
-- Well-formedness of a TYPE reads only WHICH NAMES are in scope, and
-- in v8 `∋ᵗ` is address-free — so the whole algebra is stated on `∋ᵗ`
-- and not a single address is mentioned.

RenNamesᵗ : Renameᵗ → List StackEnt → List StackEnt → Set
RenNamesᵗ ρ Ss Ss′ = ∀ {Y} → Ss ∋ᵗ Y → Ss′ ∋ᵗ ρ Y

ext-rennames : ∀ {ρ} → RenNamesᵗ ρ Ss Ss′
  → RenNamesᵗ (extᵗ ρ) (bind ∷ Ss) (bind ∷ Ss′)
ext-rennames r t-here = t-here
ext-rennames r (t-there p) = t-there (r p)

wf-rn : ∀ {ρ} → RenNamesᵗ ρ Ss Ss′
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ renameᵗ ρ A
wf-rn r (wf-var n) = wf-var (r n)
wf-rn r wf-ℕ = wf-ℕ
wf-rn r wf-𝔹 = wf-𝔹
wf-rn r (wf-⇒ a b) = wf-⇒ (wf-rn r a) (wf-rn r b)
wf-rn r (wf-∀ a) = wf-∀ (wf-rn (ext-rennames r) a)

wf-⇑ : (Ss ∥ Bs) ⊢ᵗ A → (bind ∷ Ss ∥ Bs) ⊢ᵗ renameᵗ suc A
wf-⇑ = wf-rn (λ p → t-there p)

-- the SOURCE is just a stack, since that is all a lookup reads
SubstsᵗM : Substᵗ → List StackEnt → Ctxᵗ → Set
SubstsᵗM σ Ss Γ′ = ∀ {Y} → Ss ∋ᵗ Y → Γ′ ⊢ᵗ σ Y

ext-substs : ∀ {σ} → SubstsᵗM σ Ss (Ss′ ∥ Bs′)
  → SubstsᵗM (extsᵗ σ) (bind ∷ Ss) (bind ∷ Ss′ ∥ Bs′)
ext-substs m t-here = wf-var t-here
ext-substs m (t-there p) = wf-⇑ (m p)

wf-substM : ∀ {σ} → SubstsᵗM σ Ss (Ss′ ∥ Bs′)
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ substᵗ σ A
wf-substM m (wf-var n) = m n
wf-substM m wf-ℕ = wf-ℕ
wf-substM m wf-𝔹 = wf-𝔹
wf-substM m (wf-⇒ a b) = wf-⇒ (wf-substM m a) (wf-substM m b)
wf-substM m (wf-∀ a) = wf-∀ (wf-substM (ext-substs m) a)

-- a closed type is well formed anywhere
Names< : ℕ → List StackEnt → Set
Names< n Ss = ∀ {Y} → Y < n → Ss ∋ᵗ Y

ext-names : ∀ {n} → Names< n Ss → Names< (suc n) (bind ∷ Ss)
ext-names h {zero} lt = t-here
ext-names h {suc Y} (s≤s lt) = t-there (h lt)

wf-nofree : ∀ {n} → NoFreeᵗ n S → Names< n Ss → (Ss ∥ Bs) ⊢ᵗ S
wf-nofree (nf-var lt) h = wf-var (h lt)
wf-nofree nf-ℕ h = wf-ℕ
wf-nofree nf-𝔹 h = wf-𝔹
wf-nofree (nf-⇒ a b) h = wf-⇒ (wf-nofree a h) (wf-nofree b h)
wf-nofree (nf-∀ a) h = wf-∀ (wf-nofree a (ext-names h))

wf-closed : Closedᵗ S → (Ss ∥ Bs) ⊢ᵗ S
wf-closed cl = wf-nofree cl (λ ())

------------------------------------------------------------------------
-- §4  `closeAt` at a `∀` and across a crossing's shift
------------------------------------------------------------------------

extsᵗ-closeEnv : ∀ X S Z
  → extsᵗ (closeEnv X S) Z ≡ closeEnv (suc X) (renameᵗ suc S) Z
extsᵗ-closeEnv X S zero = refl
extsᵗ-closeEnv X S (suc Z) with X ≟ Z
extsᵗ-closeEnv X S (suc Z) | yes eq
  rewrite eq
        | closeEnv-eq (suc Z) (renameᵗ suc S) = refl
extsᵗ-closeEnv X S (suc Z) | no ne with X <? Z
extsᵗ-closeEnv X S (suc Z) | no ne | yes lt
  rewrite closeEnv-gt (suc X) (renameᵗ suc S) (suc Z) (s≤s lt)
        | suc-pred (pos-of lt) = refl
extsᵗ-closeEnv X S (suc Z) | no ne | no nlt
  rewrite closeEnv-lt (suc X) (renameᵗ suc S) (suc Z)
                      (s≤s (¬<-¬≡-> nlt ne)) = refl

closeAt-∀ : ∀ X S A
  → closeAt X S (`∀ A) ≡ `∀ (closeAt (suc X) (renameᵗ suc S) A)
closeAt-∀ X S A = cong `∀ (substᵗ-cong (extsᵗ-closeEnv X S) A)

-- The crux for `hide`/`show`: those rules state their types as
-- `shiftAtᵗ Y` renames, and closing over a slot STRICTLY BELOW the
-- crossing's name commutes with that rename, the crossing's own name
-- sliding down by `nameSub X`.  Only the slot variable itself needs
-- anything — and what it needs is that S survives the shift, which is
-- side condition (1).
closeEnv-shift : ∀ X W S → X ≤ W → renameᵗ (shiftAtᵗ W) S ≡ S → ∀ Z
  → closeEnv X S (shiftAtᵗ (suc W) Z)
    ≡ renameᵗ (shiftAtᵗ W) (closeEnv X S Z)
closeEnv-shift X W S le inv Z with W <? Z
closeEnv-shift X W S le inv Z | yes w<z
  rewrite shiftAt-above (suc W) Z w<z
        | closeEnv-gt X S (suc Z)
            (≤-trans (s≤s le) (≤-trans w<z (n≤suc Z)))
        | closeEnv-gt X S Z (≤-trans (s≤s le) w<z)
        | shiftAt-above W (Z ∸ 1) (le-pred w<z)
        | suc-pred (pos-of w<z) = refl
closeEnv-shift X W S le inv Z | no ¬w<z with X ≟ Z
closeEnv-shift X W S le inv Z | no ¬w<z | yes eq
  rewrite shiftAt-below (suc W) Z (≰⇒> ¬w<z)
        | eq
        | closeEnv-eq Z S = sym inv
closeEnv-shift X W S le inv Z | no ¬w<z | no ne with X <? Z
closeEnv-shift X W S le inv Z | no ¬w<z | no ne | yes lt
  rewrite shiftAt-below (suc W) Z (≰⇒> ¬w<z)
        | closeEnv-gt X S Z lt
        | shiftAt-below W (Z ∸ 1)
            (≤-trans (pred-< (pos-of lt)) (pred≤ (≰⇒> ¬w<z))) = refl
closeEnv-shift X W S le inv Z | no ¬w<z | no ne | no nlt
  rewrite shiftAt-below (suc W) Z (≰⇒> ¬w<z)
        | closeEnv-lt X S Z (¬<-¬≡-> nlt ne)
        | shiftAt-below W Z (≤-trans (¬<-¬≡-> nlt ne) le) = refl

closeAt-shift : ∀ X Y S A → X < Y → Closedᵗ S
  → closeAt X S (renameᵗ (shiftAtᵗ Y) A)
    ≡ renameᵗ (shiftAtᵗ (nameSub X Y)) (closeAt X S A)
closeAt-shift X (suc W) S A (s≤s le) cl
  rewrite nameSub-gt X (suc W) (s≤s le) =
  trans (rename-subst-commute (shiftAtᵗ (suc W)) (closeEnv X S) A)
        (trans (substᵗ-cong
                  (closeEnv-shift X W S le (closed-ren cl (shiftAtᵗ W))) A)
               (sym (rename-subst (shiftAtᵗ W) (closeEnv X S) A)))

------------------------------------------------------------------------
-- §5  The relation: dropping the slot
------------------------------------------------------------------------

data DropBindS : ℕ → List StackEnt → List StackEnt → Set where
  drop-here  : DropBindS zero (bind ∷ Ss) Ss
  drop-there : DropBindS X Ss Ss′
             → DropBindS (suc X) (bind ∷ Ss) (bind ∷ Ss′)

data DropBind : ℕ → Ctxᵗ → Ctxᵗ → Set where
  drop-ctx : DropBindS X Ss Ss′ → DropBind X (Ss ∥ Bs) (Ss′ ∥ Bs)

drop-uniqueS : DropBindS X Ss Ss′ → DropBindS X Ss Ss″ → Ss′ ≡ Ss″
drop-uniqueS drop-here drop-here = refl
drop-uniqueS (drop-there d₁) (drop-there d₂) =
  cong (bind ∷_) (drop-uniqueS d₁ d₂)

drop-unique : DropBind X Γ Γ′ → DropBind X Γ Γ″ → Γ′ ≡ Γ″
drop-unique (drop-ctx d₁) (drop-ctx d₂) rewrite drop-uniqueS d₁ d₂ = refl

-- going under one more binder assignment: the `all` step
drop-⇑ : DropBind X Γ Γ′
  → DropBind (suc X) (bind ∷ stk Γ ∥ bas Γ) (bind ∷ stk Γ′ ∥ bas Γ′)
drop-⇑ (drop-ctx d) = drop-ctx (drop-there d)

------------------------------------------------------------------------
-- §6  The remaining side conditions
------------------------------------------------------------------------
-- (2) `RepsWf` — every representation a `∋r` reaches has its `` `ᵛ ``s
-- bound by its OWN `∀ᴿ`s.  It is what lets `∋r` and the read-back `⇓`
-- travel across the drop with the SAME `R`: `seal`/`unseal` read their
-- type off a representation the syntax does not carry, so `R` cannot be
-- renamed by `substAnn` — and the drop REMOVES one of the `bind`s that
-- `read-bv` counts, so a `` `ᵛ `` escaping `R`'s own `∀ᴿ`s would have
-- to move.  `StoreOk` gives it for every `lvl`; for a `bse` it is
-- `⊢ν`'s own first premise on the base's ν-binders.
--
-- This is all that is left of v7's `NoBndReps`: there the danger was a
-- `bnd` address masquerading as a free one, here it is a genuinely free
-- `` `ᵛ ``, and `⊢ᴿ`'s index rules it out by construction.

-- INDEXED BY THE BASE.  Quantifying over every context makes this
-- REFUTABLE: `nuBind (`ᵛ 0)` is a legal base entry and `r-here`
-- reaches it, but `⇑ᴿᵉ (`ᵛ 0)` is not `⊢ᴿ[ 0 ]`-well-formed.  A
-- conversion never changes the base (`conv-base`), so one base serves
-- the whole recursion, and at the empty base the condition is just
-- `StoreOk`.
RepsWf : Store → List BaseEnt → Set
RepsWf Sg Bs =
  ∀ {Ss α R} → Sg ∣ (Ss ∥ Bs) ∋r α := R → Sg ∣ (Ss ∥ Bs) ⊢ᴿ R

-- (3) `SlotFree`, on the conversion, mirroring `substAnn`'s own
-- recursion: every crossing names a slot strictly BELOW X.  For `seal`
-- and `hide` — which POP the assignment going inward — `X < Y` is
-- derivable from the typing; for `unseal` and `show` — which PUSH one
-- — it is not, and it is genuinely needed: a `show 0 α` under a slot
-- at 0 inserts its assignment ABOVE the slot, moving the slot to name
-- 1, while `substAnn` goes on substituting at 0.
--
-- In v7 each atomic case ALSO demanded `NotBnd α`.  With `bnd` gone
-- that half is vacuous and has been deleted.
mutual
  data SlotFreeElt (X : ℕ) : ConvElt → Set where
    sf-seal   : ∀ {Y α} → X < Y → SlotFreeElt X (seal Y α)
    sf-unseal : ∀ {Y α} → X < Y → SlotFreeElt X (unseal Y α)
    sf-hide   : ∀ {Y α} → X < Y → SlotFreeElt X (hide Y α)
    sf-show   : ∀ {Y α} → X < Y → SlotFreeElt X (show Y α)
    sf-fun    : ∀ {s t} → SlotFree X s → SlotFree X t
              → SlotFreeElt X (s ↦ t)
    sf-all    : ∀ {s} → SlotFree (suc X) s → SlotFreeElt X (all s)

  data SlotFree (X : ℕ) : Conv → Set where
    sf-id   : ∀ {A} → SlotFree X (id A)
    sf-cons : ∀ {ĉ c} → SlotFreeElt X ĉ → SlotFree X c
            → SlotFree X (ĉ ∷ᶜ c)

------------------------------------------------------------------------
-- §7  Transporting the lookups across the drop
------------------------------------------------------------------------

-- The slot is a `bind`, and only an `asgn` assigns an address, so no
-- name lookup lands on the slot.
slot-∌ : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n X := α → ⊥
slot-∌ drop-here ()
slot-∌ (drop-there d) (n-skip-bind p) = slot-∌ d p

slot-≢ : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n Y := α → ¬ (X ≡ Y)
slot-≢ d n refl = slot-∌ d n

-- A name lookup survives the drop with the SAME address: the drop is a
-- stack operation and v8 renames no address across the stack.
∋n-dropS : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n Y := α
  → (Ss′ ∥ Bs) ∋n nameSub X Y := α
∋n-dropS drop-here (n-skip-bind {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = p
∋n-dropS (drop-there {X = X} d) (n-skip-bind {X = Y} p)
  rewrite nameSub-suc X Y = n-skip-bind (∋n-dropS d p)

-- The same for a variable merely IN SCOPE, which is what `⊢ᵗ` reads.
∋ᵗ-dropS : DropBindS X Ss Ss′ → Ss ∋ᵗ Y → ¬ (X ≡ Y)
  → Ss′ ∋ᵗ nameSub X Y
∋ᵗ-dropS drop-here t-here ne = ⊥-elim (ne refl)
∋ᵗ-dropS drop-here (t-there {X = Y} p) ne
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = p
∋ᵗ-dropS (drop-there d) t-here ne = t-here
∋ᵗ-dropS (drop-there {X = X} d) (t-there {X = Y} p) ne
  rewrite nameSub-suc X Y =
  t-there (∋ᵗ-dropS d p (λ eq → ne (cong suc eq)))

-- A `∀`-bound variable: `∋b` counts the `bind`s, and the drop removes
-- the X-th of them, so a variable bound by one of the X ABOVE it keeps
-- its index `i` and only its NAME slides down.
∋b-≢ : DropBindS X Ss Ss′ → Ss ∋b Z at Y → Y < X → ¬ (X ≡ Z)
∋b-≢ drop-here b ()
∋b-≢ (drop-there d) b-here lt ()
∋b-≢ (drop-there d) (b-bind p) (s≤s lt) refl = ∋b-≢ d p lt refl

∋b-dropS : DropBindS X Ss Ss′ → Ss ∋b Z at Y → Y < X
  → Ss′ ∋b nameSub X Z at Y
∋b-dropS drop-here b ()
∋b-dropS (drop-there d) b-here lt = b-here
∋b-dropS (drop-there {X = X} d) (b-bind {X = Z} p) (s≤s lt)
  rewrite nameSub-suc X Z = b-bind (∋b-dropS d p lt)

-- the other direction, for `NotAssigned`: putting the slot back
∋n-undropS : DropBindS X Ss Ss′ → (Ss′ ∥ Bs) ∋n Y := α
  → (Ss ∥ Bs) ∋n shiftAtᵗ X Y := α
∋n-undropS drop-here p = n-skip-bind p
∋n-undropS (drop-there d) (n-skip-bind p) =
  n-skip-bind (∋n-undropS d p)

notasgn-drop : DropBindS X Ss Ss′ → NotAssigned (Ss ∥ Bs) α
  → NotAssigned (Ss′ ∥ Bs) α
notasgn-drop d na q = na (∋n-undropS d q)

-- well-formedness: the substitution algebra instantiated at the drop
drop-substs : ∀ {Bs} → DropBindS X Ss Ss′ → Closedᵗ S
  → SubstsᵗM (closeEnv X S) Ss (Ss′ ∥ Bs)
-- the decision is taken in a helper: a `with X ≟ Y` at the top level
-- would abstract the very `X ≟ Y` that `closeEnv X S Y` is waiting on,
-- and no equation about `closeEnv` could then be applied to the goal
drop-substs {X = X} {S = S} d cl {Y = Y} n = go (X ≟ Y)
  where
  go : Dec (X ≡ Y) → _ ⊢ᵗ closeEnv X S Y
  go (yes eq) rewrite eq | closeEnv-eq Y S = wf-closed cl
  go (no ne) rewrite closeEnv-≢ X S Y ne = wf-var (∋ᵗ-dropS d n ne)

wf-drop : DropBindS X Ss Ss′ → Closedᵗ S → (Ss ∥ Bs) ⊢ᵗ A
  → (Ss′ ∥ Bs) ⊢ᵗ closeAt X S A
wf-drop d cl = wf-substM (drop-substs d cl)

-- A represented address reads the STORE or the BASE, and the drop is a
-- pure STACK operation, so it touches neither.
∋r-drop : Sg ∣ (Ss ∥ Bs) ∋r α := R → Sg ∣ (Ss′ ∥ Bs) ∋r α := R
∋r-drop = ∋r-restk

-- The read-back travels with its representation UNCHANGED, provided
-- R's bound variables are its own: `n` counts the `∀ᴿ`s entered so
-- far, and `n ≤ X` says the slot is BELOW all of them, so `read-bv`
-- lands on a `bind` the drop keeps.
read-drop : ∀ {Sg X S n Γᴿ Ss Ss′ Bs R A}
  → n ≤ X → DropBindS X Ss Ss′
  → Sg ∣ Γᴿ ⊢ᴿ[ n ] R → Sg ∣ (Ss ∥ Bs) ⊢ R ⇓ A
  → Sg ∣ (Ss′ ∥ Bs) ⊢ R ⇓ closeAt X S A
read-drop {X = X} {S = S} le d (wfᴿ-var a) (read-var {X = Z} n)
  rewrite closeEnv-≢ X S Z (slot-≢ d n) = read-var (∋n-dropS d n)
read-drop {X = X} {S = S} le d (wfᴿ-bv i<n) (read-bv {X = Z} b)
  rewrite closeEnv-≢ X S Z (∋b-≢ d b (≤-trans i<n le)) =
  read-bv (∋b-dropS d b (≤-trans i<n le))
read-drop le d wfᴿ-ℕ read-ℕ = read-ℕ
read-drop le d wfᴿ-𝔹 read-𝔹 = read-𝔹
read-drop le d (wfᴿ-⇒ wr wt) (read-⇒ r t) =
  read-⇒ (read-drop le d wr r) (read-drop le d wt t)
read-drop {X = X} {S = S} le d (wfᴿ-∀ wr) (read-∀ {A = A} r)
  rewrite closeAt-∀ X S A =
  read-∀ (read-drop (s≤s le) (drop-there d) wr r)

------------------------------------------------------------------------
-- §8  Transporting the pop judgment
------------------------------------------------------------------------
-- Both directions produce the far context, so the caller never has to
-- know it in advance; the `DropBind` wrapper it comes in carries the
-- base equality along with it.

-- POP: the crossing removes its assignment going inward (`seal`,
-- `hide`).  X < Y is not needed here — it is forced, since the slot's
-- position holds a `bind` and Y's holds the `asgn`.
drop-pop : DropBindS X Ssₑ Ss′
  → (Ssₑ ∥ Bs) ▷ Y := α ⇒ Γᵢ
  → Σ[ Γᵢ′ ∈ Ctxᵗ ]
      (DropBind X Γᵢ Γᵢ′ × ((Ss′ ∥ Bs) ▷ nameSub X Y := α ⇒ Γᵢ′))
drop-pop drop-here (pop-bind {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = _ , drop-ctx drop-here , p
drop-pop (drop-there {X = X} d) (pop-bind {X = Y} p) with drop-pop d p
drop-pop (drop-there {X = X} d) (pop-bind {X = Y} p)
  | Γ″ , drop-ctx d″ , p″ rewrite nameSub-suc X Y =
  _ , drop-ctx (drop-there d″) , pop-bind p″

-- PUSH: the crossing ADDS its assignment going inward (`unseal`,
-- `show`).  Here X < Y is a hypothesis: without it `pop-here` could
-- push the assignment above the slot — which is exactly how the two
-- `pop-here` clauses below are discharged.
drop-push : DropBindS X Ssₑ Ss′ → X < Y
  → Γᵢ ▷ Y := α ⇒ (Ssₑ ∥ Bs)
  → Σ[ Γᵢ′ ∈ Ctxᵗ ]
      (DropBind X Γᵢ Γᵢ′ × (Γᵢ′ ▷ nameSub X Y := α ⇒ (Ss′ ∥ Bs)))
drop-push drop-here lt pop-here = ⊥-elim (<-zero lt)
drop-push (drop-there d) lt pop-here = ⊥-elim (<-zero lt)
drop-push drop-here lt (pop-bind {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = _ , drop-ctx drop-here , p
drop-push (drop-there {X = X} d) (s≤s lt) (pop-bind {X = Y} p)
  with drop-push d lt p
drop-push (drop-there {X = X} d) (s≤s lt) (pop-bind {X = Y} p)
  | Γ″ , drop-ctx d″ , p″ rewrite nameSub-suc X Y =
  _ , drop-ctx (drop-there d″) , pop-bind p″

------------------------------------------------------------------------
-- §9  The theorem
------------------------------------------------------------------------
-- Stated so that the EXTERIOR drop is given and the INTERIOR one is
-- produced: the conversion judgment threads its contexts from the
-- terminator inward, so that is the direction in which the spine
-- recursion has its context available.  `conv-fun`, whose two
-- components run in opposite directions, closes the circle with
-- `drop-unique`.

mutual
  substAnnElt-typing : ∀ {Sg X S ĉ A B Ssₑ Ss′ Bs Γᵢ}
    → RepsWf Sg Bs → Closedᵗ S → SlotFreeElt X ĉ
    → DropBindS X Ssₑ Ss′
    → Sg ∣ Γᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Γᵢ′ ∈ Ctxᵗ ]
        (DropBind X Γᵢ Γᵢ′
         × Sg ∣ Γᵢ′ ⊢̂ substAnnElt X S ĉ
             ∶ closeAt X S A ⇝ closeAt X S B ⊣ (Ss′ ∥ Bs))

  -- a `seal`: its target IS the crossing's name, which slides down
  substAnnElt-typing {X = X} {S = S} rw cl (sf-seal {Y = Y} lt) d
    (conv-seal rep rd p) with drop-pop d p
  substAnnElt-typing {X = X} {S = S} rw cl (sf-seal {Y = Y} lt) d
    (conv-seal rep rd p) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeEnv-≢ X S Y (<-≢ lt) =
    Γᵢ′ , drop-ctx dᵢ
    , conv-seal (∋r-drop rep) (read-drop z≤n dᵢ (rw rep) rd) p′

  -- an `unseal`: dual, and its freshness side condition comes back
  -- the interior's base is the exterior's (`pop-base`), which is what
  -- lets the base-indexed `RepsWf` read this `∋r`
  substAnnElt-typing {X = X} {S = S} {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl
    (sf-unseal {Y = Y} lt) d (conv-unseal rep rd p na) with pop-base p
  substAnnElt-typing {X = X} {S = S} {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl
    (sf-unseal {Y = Y} lt) d (conv-unseal rep rd p na) | refl
    with drop-push d lt p
  substAnnElt-typing {X = X} {S = S} {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl
    (sf-unseal {Y = Y} lt) d (conv-unseal rep rd p na) | refl
    | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeEnv-≢ X S Y (<-≢ lt) =
    _ , drop-ctx dᵢ
    , conv-unseal (∋r-drop rep) (read-drop z≤n d (rw rep) rd) p′
                  (notasgn-drop d na)

  -- a `hide`: its target is a `shiftAtᵗ` rename, and `closeAt-shift`
  -- slides the shift's cutoff down with the name
  substAnnElt-typing {X = X} {S = S} rw cl (sf-hide {Y = Y} lt) d
    (conv-hide {A = A} sc wf p na) with drop-pop d p
  substAnnElt-typing {X = X} {S = S} rw cl (sf-hide {Y = Y} lt) d
    (conv-hide {A = A} sc wf p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeAt-shift X Y S A lt cl =
    _ , drop-ctx dᵢ
    , conv-hide (∋a-restk sc) (wf-drop dᵢ cl wf) p′
        (notasgn-drop dᵢ na)

  -- a `show`: the SOURCE is the rename, so the same equation is used
  -- in the other position
  substAnnElt-typing {X = X} {S = S} rw cl (sf-show {Y = Y} lt) d
    (conv-show {A = A} sc wf p na) with drop-push d lt p
  substAnnElt-typing {X = X} {S = S} rw cl (sf-show {Y = Y} lt) d
    (conv-show {A = A} sc wf p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeAt-shift X Y S A lt cl =
    _ , drop-ctx dᵢ
    , conv-show (∋a-restk sc) (wf-drop d cl wf) p′
        (notasgn-drop d na)

  -- a `↦`: the components run in opposite directions, so the
  -- covariant one is substituted first and hands the contravariant one
  -- its context back
  -- a conversion never changes the base (`conv-base`), which is what
  -- keeps one `RepsWf` good for both components
  substAnnElt-typing {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl (sf-fun sfs sft) d
    (conv-fun ⊢s ⊢t) with conv-base ⊢t
  substAnnElt-typing {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl (sf-fun sfs sft) d
    (conv-fun ⊢s ⊢t) | refl with substAnn-typing rw cl sft d ⊢t
  substAnnElt-typing {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl (sf-fun sfs sft) d
    (conv-fun ⊢s ⊢t) | refl | Γᵢ′ , drop-ctx dᵢ , ty-t
    with substAnn-typing rw cl sfs dᵢ ⊢s
  substAnnElt-typing {Γᵢ = Ssᵢ ∥ Bsᵢ} rw cl (sf-fun sfs sft) d
    (conv-fun ⊢s ⊢t) | refl | Γᵢ′ , drop-ctx dᵢ , ty-t
    | Γₑ″ , drop-ctx dₑ″ , ty-s
    rewrite drop-uniqueS d dₑ″ =
    _ , drop-ctx dᵢ , conv-fun ty-s ty-t

  -- an `all`: one more binder assignment on both sides, so the slot
  -- moves up by one and S shifts with it
  substAnnElt-typing {X = X} {S = S} rw cl (sf-all sfs) d
    (conv-all {A = A} {B = B} ⊢s)
    with substAnn-typing rw (closed-⇑ cl) sfs (drop-there d) ⊢s
  substAnnElt-typing {X = X} {S = S} rw cl (sf-all sfs) d
    (conv-all {A = A} {B = B} ⊢s)
    | Γ″ , drop-ctx (drop-there dᵢ) , ty
    rewrite closeAt-∀ X S A | closeAt-∀ X S B =
    _ , drop-ctx dᵢ , conv-all ty

  substAnn-typing : ∀ {Sg X S c A B Ssₑ Ss′ Bs Γᵢ}
    → RepsWf Sg Bs → Closedᵗ S → SlotFree X c
    → DropBindS X Ssₑ Ss′
    → Sg ∣ Γᵢ ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Γᵢ′ ∈ Ctxᵗ ]
        (DropBind X Γᵢ Γᵢ′
         × Sg ∣ Γᵢ′ ⊢ substAnn X S c ∶ closeAt X S A ⇝ closeAt X S B
             ⊣ (Ss′ ∥ Bs))

  substAnn-typing rw cl sf-id d (conv-id wf) =
    _ , drop-ctx d , conv-id (wf-drop d cl wf)
  substAnn-typing rw cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) with conv-base tl
  substAnn-typing rw cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    with substAnn-typing rw cl sfc d tl
  substAnn-typing rw cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    | Γ₂′ , drop-ctx d₂ , ty-tl
    with substAnnElt-typing rw cl sfĉ d₂ hd
  substAnn-typing rw cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    | Γ₂′ , drop-ctx d₂ , ty-tl | Γ₁′ , dr₁ , ty-hd =
    _ , dr₁ , conv-cons ty-hd ty-tl

------------------------------------------------------------------------
-- §10  The form the statement was asked for: both drops given
------------------------------------------------------------------------

substAnn-typing′ : ∀ {Sg X S c A B Δᵢ Δᵢ′ Ss Bs Δ′}
  → RepsWf Sg Bs → Closedᵗ S → SlotFree X c
  → DropBind X Δᵢ Δᵢ′ → DropBind X (Ss ∥ Bs) Δ′
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ (Ss ∥ Bs)
  → Sg ∣ Δᵢ′ ⊢ substAnn X S c ∶ closeAt X S A ⇝ closeAt X S B ⊣ Δ′
substAnn-typing′ rw cl sf drᵢ (drop-ctx d) ⊢c
  with substAnn-typing rw cl sf d ⊢c
substAnn-typing′ rw cl sf drᵢ (drop-ctx d) ⊢c | Δᵢ″ , drᵢ″ , ty
  rewrite drop-unique drᵢ drᵢ″ = ty

------------------------------------------------------------------------
-- §11  Sanity check against `Examples.§14`
------------------------------------------------------------------------
-- There `allView c₂` is `d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)`, typed
-- under the ∀'s binder assignment — slot 0 — and `instReveal zero (bse
-- zero) `𝔹 d` composes the builder with `substAnn zero `𝔹 d`.  The
-- crossing's name (1) is strictly below the slot, so `SlotFree` holds;
-- the type argument is ground, so `Closedᵗ` holds; and the substituted
-- conversion is the one `inst-agrees` checks.

private
  §14-d : Conv
  §14-d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)

  §14-subst : substAnn zero `𝔹 §14-d ≡ show 0 (lvl 0) ∷ᶜ id (`𝔹 ⇒ `𝔹)
  §14-subst = refl

  §14-slotfree : SlotFree zero §14-d
  §14-slotfree = sf-cons (sf-show (s≤s z≤n)) sf-id

  §14-closed : Closedᵗ `𝔹
  §14-closed = nf-𝔹

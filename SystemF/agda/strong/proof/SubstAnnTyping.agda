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
-- this proof lifts (`∋n`, `⊢ᵗ`, `⇓`, `▷ := ⇒`) is itself defined by
-- recursion down the stack: a `here`/`there` relation unifies with
-- those derivations one constructor at a time, while `Δ ≡ Ss ++ bind ∷
-- Ss′` would leave every case blocked on an append.  Two further
-- choices:
--
--   * `drop-there` steps past a `bind` ONLY.  The slot removed is
--     always a `∀`'s binder assignment, and the pop judgment already
--     insists that a crossing assignment has nothing but `bind`s above
--     it (`pop-bind-b`/`-l`/`-e` are its only non-base rules).  Making
--     `DropBind` agree with that discipline is what makes the crossing
--     name Y and the slot X comparable at all: the slot sits at stack
--     position X with X `bind`s above it, a crossing sits at position Y
--     with Y `bind`s above it, so X ≢ Y comes for free, and in the
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
-- THE SIDE CONDITIONS, and what they are really saying.  Each is a
-- place where the DEFINITION of `substAnn` assumes something the
-- syntax does not record; they are collected in `SlotFree`, `Closedᵗ`
-- and `NoBndReps`, and each is documented where it is defined.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (_≟_; _<?_; ≤-refl; ≤-trans; ≰⇒>)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.TypeSubst using (rename-subst-commute; rename-subst)
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.proof.SrcTyping using (shiftAt-below; shiftAt-above)

private
  variable
    Sg : Store
    Bs Bs′ : List BaseEnt
    Ss Ss′ Ss″ Ssᵢ Ssₑ : List StackEnt
    Γ Γ′ Γ″ Γᵢ Γₑ : Ctxᵗ
    A B C D S : Ty
    R : RepTy
    X Y Z W : ℕ
    α β : Addr
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

pos-of : X < Z → zero < Z
pos-of {Z = suc Z} lt = s≤s z≤n

suc-pred : zero < Z → suc (Z ∸ 1) ≡ Z
suc-pred {Z = suc Z} lt = refl

pred-< : zero < Z → (Z ∸ 1) < Z
pred-< {Z = suc Z} lt = ≤-refl

le-pred : suc W ≤ Z → W ≤ (Z ∸ 1)
le-pred {Z = suc Z} (s≤s le) = le

pred≤ : suc Z ≤ suc W → Z ≤ W
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
-- Both are ADDRESS-OBLIVIOUS: `wf-var` needs only that SOME address
-- carries the name, and passing a `bind` changes a `bnd` address.

shift-names : (Ss ∥ Bs) ∋n Y := α
  → Σ[ β ∈ Addr ] (bind ∷ Ss ∥ Bs) ∋n suc Y := β
shift-names {α = lvl ℓ} n = lvl ℓ , n-skip-bind-l n
shift-names {α = bnd i} n = bnd (suc i) , n-skip-bind-b n
shift-names {α = bse j} n = bse j , n-skip-bind-e n

RenNames : Renameᵗ → Ctxᵗ → Ctxᵗ → Set
RenNames ρ Γ Γ′ = ∀ {Y α} → Γ ∋n Y := α → Σ[ β ∈ Addr ] Γ′ ∋n ρ Y := β

ext-rennames : ∀ {ρ} → RenNames ρ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → RenNames (extᵗ ρ) (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
ext-rennames r n-here-bind = bnd zero , n-here-bind
ext-rennames r (n-skip-bind-b p) with r p
ext-rennames r (n-skip-bind-b p) | β , q = shift-names q
ext-rennames r (n-skip-bind-l p) with r p
ext-rennames r (n-skip-bind-l p) | β , q = shift-names q
ext-rennames r (n-skip-bind-e p) with r p
ext-rennames r (n-skip-bind-e p) | β , q = shift-names q

wf-rn : ∀ {ρ} → RenNames ρ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ renameᵗ ρ A
wf-rn r (wf-var n) with r n
wf-rn r (wf-var n) | β , q = wf-var q
wf-rn r wf-ℕ = wf-ℕ
wf-rn r wf-𝔹 = wf-𝔹
wf-rn r (wf-⇒ a b) = wf-⇒ (wf-rn r a) (wf-rn r b)
wf-rn r (wf-∀ a) = wf-∀ (wf-rn (ext-rennames r) a)

wf-⇑ : (Ss ∥ Bs) ⊢ᵗ A → (bind ∷ Ss ∥ Bs) ⊢ᵗ renameᵗ suc A
wf-⇑ = wf-rn shift-names

SubstsᵗM : Substᵗ → Ctxᵗ → Ctxᵗ → Set
SubstsᵗM σ Γ Γ′ = ∀ {Y α} → Γ ∋n Y := α → Γ′ ⊢ᵗ σ Y

ext-substs : ∀ {σ} → SubstsᵗM σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → SubstsᵗM (extsᵗ σ) (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
ext-substs m n-here-bind = wf-var n-here-bind
ext-substs m (n-skip-bind-b p) = wf-⇑ (m p)
ext-substs m (n-skip-bind-l p) = wf-⇑ (m p)
ext-substs m (n-skip-bind-e p) = wf-⇑ (m p)

wf-substM : ∀ {σ} → SubstsᵗM σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ substᵗ σ A
wf-substM m (wf-var n) = m n
wf-substM m wf-ℕ = wf-ℕ
wf-substM m wf-𝔹 = wf-𝔹
wf-substM m (wf-⇒ a b) = wf-⇒ (wf-substM m a) (wf-substM m b)
wf-substM m (wf-∀ a) = wf-∀ (wf-substM (ext-substs m) a)

-- a closed type is well formed anywhere
Names< : ℕ → Ctxᵗ → Set
Names< n Γ = ∀ {Y} → Y < n → Σ[ α ∈ Addr ] Γ ∋n Y := α

ext-names : ∀ {n} → Names< n (Ss ∥ Bs) → Names< (suc n) (bind ∷ Ss ∥ Bs)
ext-names h {zero} lt = bnd zero , n-here-bind
ext-names h {suc Y} (s≤s lt) with h lt
ext-names h {suc Y} (s≤s lt) | α , p = shift-names p

wf-nofree : ∀ {n} → NoFreeᵗ n S → Names< n (Ss ∥ Bs) → (Ss ∥ Bs) ⊢ᵗ S
wf-nofree (nf-var lt) h with h lt
wf-nofree (nf-var lt) h | α , p = wf-var p
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
-- §6  SIDE CONDITIONS (2) and (3), on addresses
------------------------------------------------------------------------
-- (2) No crossing's address is a `bnd`.  A `bnd i` counts the stack's
-- `bind`s, and the slot IS one of them; the pop rules show that a
-- crossing at name Y with a `bnd` address has index i ≥ Y > X, so it
-- always points BELOW the slot and always needs decrementing — which
-- `substAnn` never does (`substAnnElt X S (seal Y α) = seal (nameSub X
-- Y) α` leaves the address alone).  The crossings the reduction rules
-- build address a store level or the ν's `bse zero`, so the condition
-- holds where it is used; but it is a real gap in the definition, and
-- `substAnnElt` ought to rename `bnd` addresses by `nameSub X` too.
--
-- (3) `NoBndReps` says a representation reached at a non-`bnd` address
-- mentions no `bnd` address.  It is what lets `∋r` and the read-back
-- `⇓` travel across the drop with the SAME `R`: `seal`/`unseal` read
-- their type off a representation the syntax does not carry, so `R`
-- cannot be renamed by `substAnn`.  `StoreOk` gives it for every
-- `lvl`; for a `bse` it is a statement about the base's ν-binders.

data NotBnd : Addr → Set where
  nb-lvl : ∀ {ℓ} → NotBnd (lvl ℓ)
  nb-bse : ∀ {j} → NotBnd (bse j)

data NoBndᴿ : RepTy → Set where
  nbr-var : ∀ {α} → NotBnd α → NoBndᴿ (`ᵃ α)
  nbr-ℕ   : NoBndᴿ `ℕᴿ
  nbr-𝔹   : NoBndᴿ `𝔹ᴿ
  nbr-⇒   : ∀ {R T} → NoBndᴿ R → NoBndᴿ T → NoBndᴿ (R ⇒ᴿ T)
  nbr-∀   : ∀ {R} → NoBndᴿ R → NoBndᴿ (`∀ᴿ R)

NoBndReps : Store → Set
NoBndReps Sg = ∀ {Γ α R} → NotBnd α → Sg ∣ Γ ∋r α := R → NoBndᴿ R

-- SIDE CONDITION (4), on the conversion, mirroring `substAnn`'s own
-- recursion: every crossing names a slot strictly BELOW X and
-- addresses no stack binder.  For `seal` and `hide` — which POP the
-- assignment going inward — `X < Y` is derivable from the typing; for
-- `unseal` and `show` — which PUSH one — it is not, and it is
-- genuinely needed: a `show 0 α` under a slot at 0 inserts its
-- assignment ABOVE the slot, moving the slot to name 1, while
-- `substAnn` goes on substituting at 0.
mutual
  data SlotFreeElt (X : ℕ) : ConvElt → Set where
    sf-seal   : ∀ {Y α} → X < Y → NotBnd α → SlotFreeElt X (seal Y α)
    sf-unseal : ∀ {Y α} → X < Y → NotBnd α → SlotFreeElt X (unseal Y α)
    sf-hide   : ∀ {Y α} → X < Y → NotBnd α → SlotFreeElt X (hide Y α)
    sf-show   : ∀ {Y α} → X < Y → NotBnd α → SlotFreeElt X (show Y α)
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

-- the slot's OWN address is the `bnd` that counts the binds above it
slot-addrS : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n X := α → α ≡ bnd X
slot-addrS drop-here n-here-bind = refl
slot-addrS (drop-there d) (n-skip-bind-b p) with slot-addrS d p
slot-addrS (drop-there d) (n-skip-bind-b p) | refl = refl
slot-addrS (drop-there d) (n-skip-bind-l p) with slot-addrS d p
slot-addrS (drop-there d) (n-skip-bind-l p) | ()
slot-addrS (drop-there d) (n-skip-bind-e p) with slot-addrS d p
slot-addrS (drop-there d) (n-skip-bind-e p) | ()

-- hence a non-`bnd` address never carries the slot's name
nb-≢ : DropBindS X Ss Ss′ → NotBnd α → (Ss ∥ Bs) ∋n Y := α → ¬ (X ≡ Y)
nb-≢ d nb-lvl n refl with slot-addrS d n
nb-≢ d nb-lvl n refl | ()
nb-≢ d nb-bse n refl with slot-addrS d n
nb-≢ d nb-bse n refl | ()

-- a lookup at a non-`bnd` address survives the drop unchanged
∋n-dropS : DropBindS X Ss Ss′ → NotBnd α → (Ss ∥ Bs) ∋n Y := α
  → (Ss′ ∥ Bs) ∋n nameSub X Y := α
∋n-dropS (drop-here {Ss = Ss}) nb-lvl (n-skip-bind-l {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = p
∋n-dropS (drop-here {Ss = Ss}) nb-bse (n-skip-bind-e {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = p
∋n-dropS (drop-there {X = X} d) nb-lvl (n-skip-bind-l {X = Y} p)
  rewrite nameSub-suc X Y = n-skip-bind-l (∋n-dropS d nb-lvl p)
∋n-dropS (drop-there {X = X} d) nb-bse (n-skip-bind-e {X = Y} p)
  rewrite nameSub-suc X Y = n-skip-bind-e (∋n-dropS d nb-bse p)

-- any other lookup survives with SOME address: enough for `wf-var`
∋n-drop∃ : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n Y := α → ¬ (X ≡ Y)
  → Σ[ β ∈ Addr ] (Ss′ ∥ Bs) ∋n nameSub X Y := β
∋n-drop∃ drop-here n-here-bind ne = ⊥-elim (ne refl)
∋n-drop∃ (drop-here {Ss = Ss}) (n-skip-bind-b {X = Y} {i = i} p) ne
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = bnd i , p
∋n-drop∃ (drop-here {Ss = Ss}) (n-skip-bind-l {X = Y} {ℓ = ℓ} p) ne
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = lvl ℓ , p
∋n-drop∃ (drop-here {Ss = Ss}) (n-skip-bind-e {X = Y} {j = j} p) ne
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = bse j , p
∋n-drop∃ (drop-there {X = X} d) n-here-bind ne
  rewrite nameSub-le (suc X) zero (λ ()) = bnd zero , n-here-bind
∋n-drop∃ (drop-there {X = X} d) (n-skip-bind-b {X = Y} p) ne
  with ∋n-drop∃ d p (λ eq → ne (cong suc eq))
∋n-drop∃ (drop-there {X = X} d) (n-skip-bind-b {X = Y} p) ne | β , q
  rewrite nameSub-suc X Y = shift-names q
∋n-drop∃ (drop-there {X = X} d) (n-skip-bind-l {X = Y} p) ne
  with ∋n-drop∃ d p (λ eq → ne (cong suc eq))
∋n-drop∃ (drop-there {X = X} d) (n-skip-bind-l {X = Y} p) ne | β , q
  rewrite nameSub-suc X Y = shift-names q
∋n-drop∃ (drop-there {X = X} d) (n-skip-bind-e {X = Y} p) ne
  with ∋n-drop∃ d p (λ eq → ne (cong suc eq))
∋n-drop∃ (drop-there {X = X} d) (n-skip-bind-e {X = Y} p) ne | β , q
  rewrite nameSub-suc X Y = shift-names q

-- the other direction, for `NotAssigned`: putting the slot back
∋n-undropS : DropBindS X Ss Ss′ → NotBnd α → (Ss′ ∥ Bs) ∋n Y := α
  → (Ss ∥ Bs) ∋n shiftAtᵗ X Y := α
∋n-undropS drop-here nb-lvl p = n-skip-bind-l p
∋n-undropS drop-here nb-bse p = n-skip-bind-e p
∋n-undropS (drop-there d) nb-lvl (n-skip-bind-l p) =
  n-skip-bind-l (∋n-undropS d nb-lvl p)
∋n-undropS (drop-there d) nb-bse (n-skip-bind-e p) =
  n-skip-bind-e (∋n-undropS d nb-bse p)

notasgn-drop : DropBindS X Ss Ss′ → NotBnd α
  → NotAssigned (Ss ∥ Bs) α → NotAssigned (Ss′ ∥ Bs) α
notasgn-drop d nb na q = na (∋n-undropS d nb q)

-- well-formedness: the substitution algebra instantiated at the drop
drop-substs : DropBindS X Ss Ss′ → Closedᵗ S
  → SubstsᵗM (closeEnv X S) (Ss ∥ Bs) (Ss′ ∥ Bs)
-- the decision is taken in a helper: a `with X ≟ Y` at the top level
-- would abstract the very `X ≟ Y` that `closeEnv X S Y` is waiting on,
-- and no equation about `closeEnv` could then be applied to the goal
drop-substs {X = X} {S = S} d cl {Y = Y} n = go (X ≟ Y)
  where
  go : Dec (X ≡ Y) → _ ⊢ᵗ closeEnv X S Y
  go (yes eq) rewrite eq | closeEnv-eq Y S = wf-closed cl
  go (no ne) rewrite closeEnv-≢ X S Y ne with ∋n-drop∃ d n ne
  go (no ne) | β , q = wf-var q

wf-drop : DropBindS X Ss Ss′ → Closedᵗ S → (Ss ∥ Bs) ⊢ᵗ A
  → (Ss′ ∥ Bs) ⊢ᵗ closeAt X S A
wf-drop d cl = wf-substM (drop-substs d cl)

-- the represented-address lookup at a non-`bnd` address reads the
-- STORE or the BASE, and the drop touches neither
∋r-drop : NotBnd α → Sg ∣ (Ss ∥ Bs) ∋r α := R → Sg ∣ (Ss′ ∥ Bs) ∋r α := R
∋r-drop nb-lvl (r-lvl l) = r-lvl l
∋r-drop nb-bse p = ∋r-restk p

-- the read-back travels with its representation UNCHANGED
read-drop : ∀ {S} → DropBindS X Ss Ss′ → NoBndᴿ R
  → Sg ∣ (Ss ∥ Bs) ⊢ R ⇓ A
  → Sg ∣ (Ss′ ∥ Bs) ⊢ R ⇓ closeAt X S A
read-drop {X = X} {S = S} d (nbr-var nb) (read-var {X = Z} n)
  rewrite closeEnv-≢ X S Z (nb-≢ d nb n) =
  read-var (∋n-dropS d nb n)
read-drop d nbr-ℕ read-ℕ = read-ℕ
read-drop d nbr-𝔹 read-𝔹 = read-𝔹
read-drop d (nbr-⇒ nr nt) (read-⇒ r t) =
  read-⇒ (read-drop d nr r) (read-drop d nt t)
read-drop {X = X} {S = S} d (nbr-∀ nr) (read-∀ {A = A} r)
  rewrite closeAt-∀ X S A = read-∀ (read-drop (drop-there d) nr r)

------------------------------------------------------------------------
-- §8  Transporting the pop judgment
------------------------------------------------------------------------
-- Both directions produce the far context, so the caller never has to
-- know it in advance; the `DropBind` wrapper it comes in carries the
-- base equality along with it.

-- POP: the crossing removes its assignment going inward (`seal`,
-- `hide`).  X < Y is not needed here — it is forced, since the slot's
-- position holds a `bind` and Y's holds the `asgn`.
drop-pop : DropBindS X Ssₑ Ss′ → NotBnd α
  → (Ssₑ ∥ Bs) ▷ Y := α ⇒ Γᵢ
  → Σ[ Γᵢ′ ∈ Ctxᵗ ]
      (DropBind X Γᵢ Γᵢ′ × ((Ss′ ∥ Bs) ▷ nameSub X Y := α ⇒ Γᵢ′))
drop-pop drop-here nb-lvl (pop-bind-l {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = _ , drop-ctx drop-here , p
drop-pop drop-here nb-bse (pop-bind-e {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = _ , drop-ctx drop-here , p
drop-pop (drop-there {X = X} d) nb-lvl (pop-bind-l {X = Y} p)
  with drop-pop d nb-lvl p
drop-pop (drop-there {X = X} d) nb-lvl (pop-bind-l {X = Y} p)
  | Γ″ , drop-ctx d″ , p″ rewrite nameSub-suc X Y =
  _ , drop-ctx (drop-there d″) , pop-bind-l p″
drop-pop (drop-there {X = X} d) nb-bse (pop-bind-e {X = Y} p)
  with drop-pop d nb-bse p
drop-pop (drop-there {X = X} d) nb-bse (pop-bind-e {X = Y} p)
  | Γ″ , drop-ctx d″ , p″ rewrite nameSub-suc X Y =
  _ , drop-ctx (drop-there d″) , pop-bind-e p″

-- PUSH: the crossing ADDS its assignment going inward (`unseal`,
-- `show`).  Here X < Y is a hypothesis: without it `pop-here` could
-- push the assignment above the slot.
drop-push : DropBindS X Ssₑ Ss′ → NotBnd α → X < Y
  → Γᵢ ▷ Y := α ⇒ (Ssₑ ∥ Bs)
  → Σ[ Γᵢ′ ∈ Ctxᵗ ]
      (DropBind X Γᵢ Γᵢ′ × (Γᵢ′ ▷ nameSub X Y := α ⇒ (Ss′ ∥ Bs)))
drop-push drop-here nb-lvl (s≤s z≤n) (pop-bind-l {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = _ , drop-ctx drop-here , p
drop-push drop-here nb-bse (s≤s z≤n) (pop-bind-e {X = Y} p)
  rewrite nameSub-gt zero (suc Y) (s≤s z≤n) = _ , drop-ctx drop-here , p
drop-push (drop-there {X = X} d) nb-lvl (s≤s lt) (pop-bind-l {X = Y} p)
  with drop-push d nb-lvl lt p
drop-push (drop-there {X = X} d) nb-lvl (s≤s lt) (pop-bind-l {X = Y} p)
  | Γ″ , drop-ctx d″ , p″ rewrite nameSub-suc X Y =
  _ , drop-ctx (drop-there d″) , pop-bind-l p″
drop-push (drop-there {X = X} d) nb-bse (s≤s lt) (pop-bind-e {X = Y} p)
  with drop-push d nb-bse lt p
drop-push (drop-there {X = X} d) nb-bse (s≤s lt) (pop-bind-e {X = Y} p)
  | Γ″ , drop-ctx d″ , p″ rewrite nameSub-suc X Y =
  _ , drop-ctx (drop-there d″) , pop-bind-e p″

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
    → NoBndReps Sg → Closedᵗ S → SlotFreeElt X ĉ
    → DropBindS X Ssₑ Ss′
    → Sg ∣ Γᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Γᵢ′ ∈ Ctxᵗ ]
        (DropBind X Γᵢ Γᵢ′
         × Sg ∣ Γᵢ′ ⊢̂ substAnnElt X S ĉ
             ∶ closeAt X S A ⇝ closeAt X S B ⊣ (Ss′ ∥ Bs))

  -- a `seal`: its target IS the crossing's name, which slides down
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-seal {Y = Y} lt nb) d
    (conv-seal rep rd p) with drop-pop d nb p
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-seal {Y = Y} lt nb) d
    (conv-seal rep rd p) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeEnv-≢ X S Y (<-≢ lt) =
    Γᵢ′ , drop-ctx dᵢ
    , conv-seal (∋r-drop nb rep) (read-drop dᵢ (nbr nb rep) rd) p′

  -- an `unseal`: dual, and its freshness side condition comes back
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-unseal {Y = Y} lt nb) d
    (conv-unseal rep rd p na) with drop-push d nb lt p
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-unseal {Y = Y} lt nb) d
    (conv-unseal rep rd p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeEnv-≢ X S Y (<-≢ lt) =
    _ , drop-ctx dᵢ
    , conv-unseal (∋r-drop nb rep) (read-drop d (nbr nb rep) rd) p′
                  (notasgn-drop d nb na)

  -- a `hide`: its target is a `shiftAtᵗ` rename, and `closeAt-shift`
  -- slides the shift's cutoff down with the name
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-hide {Y = Y} lt nb) d
    (conv-hide {A = A} wf p na) with drop-pop d nb p
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-hide {Y = Y} lt nb) d
    (conv-hide {A = A} wf p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeAt-shift X Y S A lt cl =
    _ , drop-ctx dᵢ
    , conv-hide (wf-drop dᵢ cl wf) p′ (notasgn-drop dᵢ nb na)

  -- a `show`: the SOURCE is the rename, so the same equation is used
  -- in the other position
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-show {Y = Y} lt nb) d
    (conv-show {A = A} wf p na) with drop-push d nb lt p
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-show {Y = Y} lt nb) d
    (conv-show {A = A} wf p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeAt-shift X Y S A lt cl =
    _ , drop-ctx dᵢ
    , conv-show (wf-drop d cl wf) p′ (notasgn-drop d nb na)

  -- a `↦`: the components run in opposite directions, so the
  -- covariant one is substituted first and hands the contravariant one
  -- its context back
  substAnnElt-typing nbr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t)
    with substAnn-typing nbr cl sft d ⊢t
  substAnnElt-typing nbr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t)
    | Γᵢ′ , drop-ctx dᵢ , ty-t with substAnn-typing nbr cl sfs dᵢ ⊢s
  substAnnElt-typing nbr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t)
    | Γᵢ′ , drop-ctx dᵢ , ty-t | Γₑ″ , drop-ctx dₑ″ , ty-s
    rewrite drop-uniqueS d dₑ″ =
    _ , drop-ctx dᵢ , conv-fun ty-s ty-t

  -- an `all`: one more binder assignment on both sides, so the slot
  -- moves up by one and S shifts with it
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-all sfs) d
    (conv-all {A = A} {B = B} ⊢s)
    with substAnn-typing nbr (closed-⇑ cl) sfs (drop-there d) ⊢s
  substAnnElt-typing {X = X} {S = S} nbr cl (sf-all sfs) d
    (conv-all {A = A} {B = B} ⊢s)
    | Γ″ , drop-ctx (drop-there dᵢ) , ty
    rewrite closeAt-∀ X S A | closeAt-∀ X S B =
    _ , drop-ctx dᵢ , conv-all ty

  substAnn-typing : ∀ {Sg X S c A B Ssₑ Ss′ Bs Γᵢ}
    → NoBndReps Sg → Closedᵗ S → SlotFree X c
    → DropBindS X Ssₑ Ss′
    → Sg ∣ Γᵢ ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Γᵢ′ ∈ Ctxᵗ ]
        (DropBind X Γᵢ Γᵢ′
         × Sg ∣ Γᵢ′ ⊢ substAnn X S c ∶ closeAt X S A ⇝ closeAt X S B
             ⊣ (Ss′ ∥ Bs))

  substAnn-typing nbr cl sf-id d (conv-id wf) =
    _ , drop-ctx d , conv-id (wf-drop d cl wf)
  substAnn-typing nbr cl (sf-cons sfĉ sfc) d (conv-cons hd tl)
    with substAnn-typing nbr cl sfc d tl
  substAnn-typing nbr cl (sf-cons sfĉ sfc) d (conv-cons hd tl)
    | Γ₂′ , drop-ctx d₂ , ty-tl
    with substAnnElt-typing nbr cl sfĉ d₂ hd
  substAnn-typing nbr cl (sf-cons sfĉ sfc) d (conv-cons hd tl)
    | Γ₂′ , drop-ctx d₂ , ty-tl | Γ₁′ , dr₁ , ty-hd =
    _ , dr₁ , conv-cons ty-hd ty-tl

------------------------------------------------------------------------
-- §10  The form the statement was asked for: both drops given
------------------------------------------------------------------------

substAnn-typing′ : ∀ {Sg X S c A B Δᵢ Δᵢ′ Δ Δ′}
  → NoBndReps Sg → Closedᵗ S → SlotFree X c
  → DropBind X Δᵢ Δᵢ′ → DropBind X Δ Δ′
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
  → Sg ∣ Δᵢ′ ⊢ substAnn X S c ∶ closeAt X S A ⇝ closeAt X S B ⊣ Δ′
substAnn-typing′ nbr cl sf drᵢ (drop-ctx d) ⊢c
  with substAnn-typing nbr cl sf d ⊢c
substAnn-typing′ nbr cl sf drᵢ (drop-ctx d) ⊢c | Δᵢ″ , drᵢ″ , ty
  rewrite drop-unique drᵢ drᵢ″ = ty

------------------------------------------------------------------------
-- §11  Sanity check against `Examples.§14`
------------------------------------------------------------------------
-- There `allView c₂` is `d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)`, typed
-- under the ∀'s binder assignment — slot 0 — and `instReveal zero (bse
-- zero) `𝔹 d` composes the builder with `substAnn zero `𝔹 d`.  The
-- crossing's name (1) is strictly below the slot and its address is a
-- store level, so `SlotFree` holds; the type argument is ground, so
-- `Closedᵗ` holds; and the substituted conversion is the one
-- `inst-agrees` checks.

private
  §14-d : Conv
  §14-d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)

  §14-subst : substAnn zero `𝔹 §14-d ≡ show 0 (lvl 0) ∷ᶜ id (`𝔹 ⇒ `𝔹)
  §14-subst = refl

  §14-slotfree : SlotFree zero §14-d
  §14-slotfree = sf-cons (sf-show (s≤s z≤n) nb-lvl) sf-id

  §14-closed : Closedᵗ `𝔹
  §14-closed = nf-𝔹

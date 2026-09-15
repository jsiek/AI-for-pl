module strong.proof.SubstAnnTyping where

-- Strong System F v8 — the typing of `substAnn`, the type substitution
-- that `instReveal`/`instConceal` perform on a conversion's
-- ANNOTATIONS when a `∀` is instantiated.
--
-- `substAnn X S c` REMOVES the name slot X from the context: the
-- annotations are closed over X by `closeAt X S`, and every crossing's
-- NAME is decremented by `nameSub X` exactly when it lies above the
-- slot.  So the lemma transports a typing derivation from a context
-- that still has the slot to the one that has lost it.
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
-- THE SIDE CONDITIONS, and what they are really saying.  Three of them
-- are needed, and each is a place where the DEFINITION of `substAnn`
-- assumes something the syntax does not record:
--
--   (1) `SlotFree X c` demands X < Y at every crossing.  For `seal`
--       and `hide` (which POP the assignment, going inward) this is
--       derivable; for `unseal` and `show` (which PUSH one) it is not,
--       and it is genuinely needed: a `show 0 α` under a slot at 0
--       would insert its assignment ABOVE the slot, moving the slot to
--       name 1, and `substAnn` goes on substituting at 0.
--
--   (2) `SlotFree X c` also demands that no crossing's ADDRESS is a
--       `bnd`.  A `bnd i` counts the stack's `bind`s, and the slot IS
--       one of them; the pop rules show a crossing at name Y with a
--       `bnd` address has index i ≥ Y > X, i.e. it always points below
--       the slot and always needs decrementing — which `substAnn`
--       never does (`substAnnElt X S (seal Y α) = seal (nameSub X Y)
--       α`, address untouched).  The crossings the reduction rules
--       actually build address a store level or the ν's `bse zero`, so
--       the condition holds where it is used, but it is a real gap in
--       the definition: `substAnnElt` should rename `bnd` addresses by
--       `nameSub X` as well.
--
--   (3) `Closedᵗ S`.  Going inward a conversion PUSHES assignments, so
--       the small contexts grow and a type living at the exterior must
--       be shifted to be read in the interior — but `substAnn` carries
--       the same S past every crossing (it shifts S only under `all`).
--       The pointwise computation in `closeEnv-shift` isolates this
--       exactly: every variable but the slot itself matches on the
--       nose, and the slot needs `renameᵗ (shiftAtᵗ (nameSub X Y)) S ≡
--       S`.  A closed S — the type argument of a `•B[A]` on ground
--       data, as in `Examples.§14` — supplies it.
--
--   (4) `NoBndReps Sg` says a representation reached at a non-`bnd`
--       address mentions no `bnd` address.  It is what lets `∋r` and
--       the read-back `⇓` travel across the drop with the SAME `R`
--       (the seal/unseal rules read their type off a representation the
--       syntax does not carry, so `R` cannot be renamed by `substAnn`).
--       `StoreOk` gives it for every `lvl`; for a `bse` it is a
--       statement about the ν-binders in the base.
--
-- What is lifted, in order: `∋n`, `⊢ᵗ` (through a substitution algebra
-- `SubstsᵗM` mirroring `proof.ArrTyping`'s `Renamesᵗ`), the read-back
-- `⇓`, the pop judgment `▷ := ⇒` in both directions, `NotAssigned`,
-- and then the two conversion judgments mutually.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (_≟_; _<?_; ≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
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
    Bs : List BaseEnt
    Ss Ss′ Ssᵢ Ssₑ : List StackEnt
    A B C D S T : Ty
    R : RepTy
    X Y Z W : ℕ
    α β : Addr
    c s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- §0  Arithmetic, kept local so the file depends on no unstable names
------------------------------------------------------------------------

¬<-¬≡-> : ¬ (X < Z) → ¬ (X ≡ Z) → Z < X
¬<-¬≡-> {zero} {zero} nlt ne = ⊥-elim (ne refl)
¬<-¬≡-> {zero} {suc Z} nlt ne = ⊥-elim (nlt (s≤s z≤n))
¬<-¬≡-> {suc X} {zero} nlt ne = s≤s z≤n
¬<-¬≡-> {suc X} {suc Z} nlt ne =
  s≤s (¬<-¬≡-> (λ lt → nlt (s≤s lt)) (λ eq → ne (cong suc eq)))

pos-of : X < Z → zero < Z
pos-of {Z = suc Z} lt = s≤s z≤n

suc-pred : zero < Z → suc (Z ∸ 1) ≡ Z
suc-pred {Z = suc Z} lt = refl

pred-< : zero < Z → (Z ∸ 1) < Z
pred-< {Z = suc Z} lt = ≤-refl

le-pred : suc W ≤ Z → W ≤ (Z ∸ 1)
le-pred {Z = suc Z} (s≤s le) = le

<-le-trans : X < Z → Z ≤ W → X < W
<-le-trans (s≤s z≤n) (s≤s le) = s≤s z≤n
<-le-trans (s≤s (s≤s lt)) (s≤s le) = s≤s (<-le-trans (s≤s lt) le)

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

-- the one fact the `there`/`all` steps need: the slot and the name it
-- reindexes move up together
nameSub-suc : ∀ X Y → nameSub (suc X) (suc Y) ≡ suc (nameSub X Y)
nameSub-suc X Y with X <? Y
nameSub-suc X Y | yes lt
  rewrite nameSub-gt (suc X) (suc Y) (s≤s lt) = sym (suc-pred (pos-of lt))
nameSub-suc X Y | no nlt =
  nameSub-le (suc X) (suc Y) (λ where (s≤s lt) → nlt lt)

closeEnv-eq : ∀ X S → closeEnv X S X ≡ S
closeEnv-eq X S with X ≟ X
closeEnv-eq X S | yes _ = refl
closeEnv-eq X S | no ne = ⊥-elim (ne refl)

closeEnv-gt : ∀ X S Z → X < Z → closeEnv X S Z ≡ ` (Z ∸ 1)
closeEnv-gt X S Z lt with X ≟ Z
closeEnv-gt X S Z lt | yes refl = ⊥-elim (lt-irr lt)
  where
  lt-irr : X < X → ⊥
  lt-irr (s≤s le) = irr le
    where
    irr : ∀ {n} → suc n ≤ n → ⊥
    irr (s≤s q) = irr q
closeEnv-gt X S Z lt | no _ with X <? Z
closeEnv-gt X S Z lt | no _ | yes _ = refl
closeEnv-gt X S Z lt | no _ | no nlt = ⊥-elim (nlt lt)

closeEnv-lt : ∀ X S Z → Z < X → closeEnv X S Z ≡ ` Z
closeEnv-lt X S Z lt with X ≟ Z
closeEnv-lt X S Z lt | yes refl = ⊥-elim (lt-irr lt)
  where
  lt-irr : X < X → ⊥
  lt-irr (s≤s le) = irr le
    where
    irr : ∀ {n} → suc n ≤ n → ⊥
    irr (s≤s q) = irr q
closeEnv-lt X S Z lt | no _ with X <? Z
closeEnv-lt X S Z lt | no _ | yes gt = ⊥-elim (both lt gt)
  where
  both : Z < X → X < Z → ⊥
  both (s≤s p) (s≤s q) = asym p q
    where
    asym : ∀ {m n} → m ≤ n → suc n ≤ m → ⊥
    asym (s≤s p) (s≤s q) = asym q p
    asym z≤n ()
closeEnv-lt X S Z lt | no _ | no _ = refl

closeEnv-≢ : ∀ X S Z → ¬ (X ≡ Z) → closeEnv X S Z ≡ ` (nameSub X Z)
closeEnv-≢ X S Z ne with X <? Z
closeEnv-≢ X S Z ne | yes lt
  rewrite nameSub-gt X Z lt = closeEnv-gt X S Z lt
closeEnv-≢ X S Z ne | no nlt
  rewrite nameSub-le X Z nlt = closeEnv-lt X S Z (¬<-¬≡-> nlt ne)

------------------------------------------------------------------------
-- §2  Closed types: the side condition on S
------------------------------------------------------------------------

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
nofree-ren {ρ = ρ} (nf-∀ a) h = cong `∀ (nofree-ren a h-ext)
  where
  h-ext : ∀ Y → Y < suc _ → extᵗ ρ Y ≡ Y
  h-ext zero lt = refl
  h-ext (suc Y) (s≤s lt) = cong suc (h Y lt)

closed-ren : Closedᵗ S → ∀ ρ → renameᵗ ρ S ≡ S
closed-ren cl ρ = nofree-ren cl (λ Y ())

closed-⇑ : Closedᵗ S → Closedᵗ (renameᵗ suc S)
closed-⇑ {S = S} cl
  rewrite closed-ren cl suc = cl

------------------------------------------------------------------------
-- §3  The renaming and substitution algebras on name lookups
------------------------------------------------------------------------
-- The mirror of `proof.ArrTyping`'s `Renamesᵗ`/`ext-renames`/`wf-ren`.
-- Both are ADDRESS-OBLIVIOUS: `wf-var` needs only that SOME address
-- carries the name, and a shift past a `bind` changes a `bnd` address.

shift-names : (Ss ∥ Bs) ∋n Y := α
  → Σ[ β ∈ Addr ] (bind ∷ Ss ∥ Bs) ∋n suc Y := β
shift-names {α = lvl ℓ} n = lvl ℓ , n-skip-bind-l n
shift-names {α = bnd i} n = bnd (suc i) , n-skip-bind-b n
shift-names {α = bse j} n = bse j , n-skip-bind-e n

RenNames : Renameᵗ → Ctxᵗ → Ctxᵗ → Set
RenNames ρ Γ Γ′ = ∀ {Y α} → Γ ∋n Y := α → Σ[ β ∈ Addr ] Γ′ ∋n ρ Y := β

ext-rennames : ∀ {ρ Bs′} → RenNames ρ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → RenNames (extᵗ ρ) (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
ext-rennames r n-here-bind = bnd zero , n-here-bind
ext-rennames r (n-skip-bind-b p) with r p
ext-rennames r (n-skip-bind-b p) | β , q = shift-names q
ext-rennames r (n-skip-bind-l p) with r p
ext-rennames r (n-skip-bind-l p) | β , q = shift-names q
ext-rennames r (n-skip-bind-e p) with r p
ext-rennames r (n-skip-bind-e p) | β , q = shift-names q

wf-rn : ∀ {ρ Bs′} → RenNames ρ (Ss ∥ Bs) (Ss′ ∥ Bs′)
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

ext-substs : ∀ {σ Bs′} → SubstsᵗM σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → SubstsᵗM (extsᵗ σ) (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
ext-substs m n-here-bind = wf-var n-here-bind
ext-substs m (n-skip-bind-b p) = wf-⇑ (m p)
ext-substs m (n-skip-bind-l p) = wf-⇑ (m p)
ext-substs m (n-skip-bind-e p) = wf-⇑ (m p)

wf-substM : ∀ {σ Bs′} → SubstsᵗM σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
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
wf-nofree (nf-var {X = X} lt) h with h lt
wf-nofree (nf-var {X = X} lt) h | α , p = wf-var p
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
extsᵗ-closeEnv X S (suc Z) | yes refl =
  trans (cong (renameᵗ suc) (closeEnv-eq X S))
        (sym (closeEnv-eq (suc X) (renameᵗ suc S)))
extsᵗ-closeEnv X S (suc Z) | no ne with X <? Z
extsᵗ-closeEnv X S (suc Z) | no ne | yes lt =
  trans (cong (renameᵗ suc) (closeEnv-gt X S Z lt))
        (trans (cong `_ (suc-pred (pos-of lt)))
               (sym (closeEnv-gt (suc X) (renameᵗ suc S) (suc Z)
                                 (s≤s lt))))
extsᵗ-closeEnv X S (suc Z) | no ne | no nlt =
  trans (cong (renameᵗ suc) (closeEnv-lt X S Z (¬<-¬≡-> nlt ne)))
        (sym (closeEnv-lt (suc X) (renameᵗ suc S) (suc Z)
                          (s≤s (¬<-¬≡-> nlt ne))))

closeAt-∀ : ∀ X S A
  → closeAt X S (`∀ A) ≡ `∀ (closeAt (suc X) (renameᵗ suc S) A)
closeAt-∀ X S A = cong `∀ (substᵗ-cong (extsᵗ-closeEnv X S) A)

-- The crux for `hide`/`show`: those rules state their types as
-- `shiftAtᵗ Y` renames, and closing over a slot STRICTLY ABOVE the
-- crossing commutes with that rename, the crossing's own name sliding
-- down by `nameSub X`.  Only the slot variable itself needs anything —
-- and what it needs is that S survives the shift, which is (3).
closeEnv-shift : ∀ X W S → X ≤ W → renameᵗ (shiftAtᵗ W) S ≡ S → ∀ Z
  → closeEnv X S (shiftAtᵗ (suc W) Z)
    ≡ renameᵗ (shiftAtᵗ W) (closeEnv X S Z)
closeEnv-shift X W S le inv Z with W <? Z
closeEnv-shift X W S le inv Z | yes w<z
  rewrite shiftAt-above (suc W) Z w<z
        | closeEnv-gt X S (suc Z) (s≤s (<-le-trans (s≤s le) (le-pred w<z)))
        | closeEnv-gt X S Z (<-le-trans (s≤s le) (le-pred w<z))
        | shiftAt-above W (Z ∸ 1) (le-pred w<z)
        | suc-pred (pos-of w<z) = refl
closeEnv-shift X W S le inv Z | no ¬w<z with X ≟ Z
closeEnv-shift X W S le inv Z | no ¬w<z | yes refl
  rewrite shiftAt-below (suc W) Z (s≤s (¬<-¬≡-> ¬w<z (λ ()) ))
  = ⊥-elim (impossible)
  where postulate impossible : ⊥
closeEnv-shift X W S le inv Z | no ¬w<z | no ne = ⊥-elim impossible
  where postulate impossible : ⊥

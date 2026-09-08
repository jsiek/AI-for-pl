module strong.Ctx where

-- Strong System F — THE TYPE CONTEXT (type contexts) and its transports.
--
-- AN ENTRY IS TWO LAYERS: WHAT THE SLOT BINDS, AND WHETHER IT IS HIDDEN.
--
-- The inner layer is a `Binding` — the knowledge at the slot:
--
--   abst      a Λ-bound variable — no representation, and none can be
--             invented.
--   bind A    THE BINDER of an instantiation event.  A is the
--             representation, stored ONCE, as a type over this entry's
--             bind tail.  Every inner boundary that talks about this
--             variable carries only its NAME.
--
-- The outer layer is the LOCK, and there is AT MOST ONE OF IT:
--
--   unmasked b  the slot may be NAMED.
--   masked b    the slot is CONCEALED here: it may not be NAMED
--               (tightness), but its binding b is RETAINED, so the
--               knowledge is still on the type context for a later
--               re-exposure (`unlock`) to point back at.
--
-- SPLITTING THE ENTRY THIS WAY MAKES "AT MOST ONE MASK" TRUE BY
-- CONSTRUCTION.  `masked` no longer takes an entry, so `masked (masked …)`
-- is not a term; `Nameable`/`Locked` are then the two constructors' own
-- discriminations, each with ONE clause and NO premise, and every lemma
-- that used to reason about a stack of masks (`Locked`'s `Nameable`
-- premise, `mask-unmask`'s side condition, `⊑ᵉ-trans`'s le-mu/le-mm
-- interplay, `unmaskEnt-nameable`) either shrinks or disappears.
--
-- Under Jeremy's Q1 ruling (BINDER-SYNTACTIC, 2026-09-05) a variable's
-- representation lives ONLY at its binder; every conversion and every
-- licence resolves the rep by LOOKING THE NAME UP along the enclosing
-- type context.  There is no store and no copy, so knowledge transport
-- (`ren-kn`, `⊑-kn`) is definitional and the old design's demotion is
-- not expressible.
--
-- This module also carries the POSITIONAL machinery the boundary needs:
-- injective renamings (`Inj`), one-slot entry update
-- (`updateAt`/`mask`/`unmask`) with its transports, and the bind prefix
-- `pushBinds` (with `shiftBy`).

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.TypeSubst using (rename-cong; rename-rename-commute)

------------------------------------------------------------------------
-- 0.  Two type-renaming facts we need over and over
------------------------------------------------------------------------

-- The single de Bruijn commutation: renaming past one extra binder.
ren-⇑-comm : (ρ : Renameᵗ) (A : Ty)
  → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
ren-⇑-comm ρ A =
  trans (rename-rename-commute suc (extᵗ ρ) A)
        (trans (rename-cong (λ X → refl) A)
               (sym (rename-rename-commute ρ suc A)))

map-length : ∀ {a} {S T : Set a} (f : S → T) (xs : List S)
           → length (map f xs) ≡ length xs
map-length f []       = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

------------------------------------------------------------------------
-- 1.  The type context:  type contexts with BINDER entries and BLOCKED entries
------------------------------------------------------------------------

-- WHAT A SLOT BINDS.  No lock lives here.
data Binding : Set where
  abst : Binding
  bind : Ty → Binding

-- A TYPE-CONTEXT ENTRY: a binding, plus AT MOST ONE lock.
data Ent : Set where
  unmasked : Binding → Ent
  masked   : Binding → Ent

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ Δ′ Δ″ : Ctxᵗ
    E E′ E″ F : Ent
    b b′ b″ : Binding
    A A′ B B′ C : Ty
    X Y Z : ℕ
    ρ ρ′ : Renameᵗ

-- Renaming acts on the BINDING — the lock carries no spelling — and
-- `renᵉ` is that action lifted through the lock layer.
renᵇ : Renameᵗ → Binding → Binding
renᵇ ρ abst     = abst
renᵇ ρ (bind A) = bind (renameᵗ ρ A)

renᵉ : Renameᵗ → Ent → Ent
renᵉ ρ (unmasked b) = unmasked (renᵇ ρ b)
renᵉ ρ (masked b)   = masked (renᵇ ρ b)

⇑ᵉ : Ent → Ent
⇑ᵉ = renᵉ suc

renᵇ-⇑-comm : (ρ : Renameᵗ) (b : Binding)
  → renᵇ (extᵗ ρ) (renᵇ suc b) ≡ renᵇ suc (renᵇ ρ b)
renᵇ-⇑-comm ρ abst     = refl
renᵇ-⇑-comm ρ (bind A) = cong bind (ren-⇑-comm ρ A)

renᵉ-⇑-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ (extᵗ ρ) (⇑ᵉ E) ≡ ⇑ᵉ (renᵉ ρ E)
renᵉ-⇑-comm ρ (unmasked b) = cong unmasked (renᵇ-⇑-comm ρ b)
renᵉ-⇑-comm ρ (masked b)   = cong masked (renᵇ-⇑-comm ρ b)

-- Entry lookup.  The entry is returned SHIFTED into the ambient context, so
-- `Δ ∋e X , bind A` means "slot X is a binder whose rep, read in Δ, is A".
-- One relation serves every purpose: knowledge, nameability, and masking.
infix 4 _∋e_,_
data _∋e_,_ : Ctxᵗ → ℕ → Ent → Set where
  ez : (E ∷ Δ) ∋e zero , ⇑ᵉ E
  es : Δ ∋e X , E → (F ∷ Δ) ∋e suc X , ⇑ᵉ E

-- A slot may be NAMED iff its entry is UNMASKED.  This is the whole of
-- the tightness discipline: `masked` is unnameable in types and in terms.
-- The predicate is now a pure discrimination on the lock layer — it says
-- NOTHING about the binding, so there is one constructor and no premise.
data Nameable : Ent → Set where
  nameable : Nameable (unmasked b)

renᵉ-Nameable : Nameable E → Nameable (renᵉ ρ E)
renᵉ-Nameable nameable = nameable

infix 4 _∋tv_
_∋tv_ : Ctxᵗ → ℕ → Set
Δ ∋tv X = ∃[ E ] ((Δ ∋e X , E) × Nameable E)

-- THE COMPLEMENT OF `Nameable`, and the whole of what an `unlock` may
-- restore.  `Locked` is what `sw-u` (strong.CtxMorph) demands and what
-- makes `mask ∘ unmask` the identity at the slot (`mask-unmask`) — the
-- fact the dual's restoring `lock` needs.  IT NEEDS NO `Nameable`
-- PREMISE ANY MORE: "masked over a nameable entry" is the only shape a
-- masked entry HAS, because `masked` takes a `Binding`.  The
-- one-mask-deep property that the premise used to enforce is now BY
-- CONSTRUCTION, so `Locked` is exactly the complement of `Nameable`.
data Locked : Ent → Set where
  locked : Locked (masked b)

renᵉ-Locked : Locked E → Locked (renᵉ ρ E)
renᵉ-Locked locked = locked

renᵉ-Nameable⁻ : Nameable (renᵉ ρ E) → Nameable E
renᵉ-Nameable⁻ {E = unmasked b} v = nameable
renᵉ-Nameable⁻ {E = masked b}   ()

Locked-ren⁻ : Locked (renᵉ ρ E) → Locked E
Locked-ren⁻ {E = unmasked b} ()
Locked-ren⁻ {E = masked b}   locked = locked

infix 4 _∋lk_
_∋lk_ : Ctxᵗ → ℕ → Set
Δ ∋lk X = ∃[ E ] ((Δ ∋e X , E) × Locked E)

-- BINDER-SYNTACTIC LOOKUP.  This is the only way any rep is ever read.
infix 4 _∋_:=_
_∋_:=_ : Ctxᵗ → ℕ → Ty → Set
Δ ∋ X := A = Δ ∋e X , unmasked (bind A)

∋:=→∋tv : Δ ∋ X := A → Δ ∋tv X
∋:=→∋tv d = unmasked (bind _) , d , nameable

-- Lookup is a partial FUNCTION, which is what makes every rule that mints an
-- identity conversion at a looked-up rep deterministic.
∋e-det : Δ ∋e X , E → Δ ∋e X , E′ → E ≡ E′
∋e-det ez     ez      = refl
∋e-det (es d) (es d′) = cong ⇑ᵉ (∋e-det d d′)

bind-inj : _≡_ {A = Ent} (unmasked (bind A)) (unmasked (bind B)) → A ≡ B
bind-inj refl = refl

∋:=-det : Δ ∋ X := A → Δ ∋ X := B → A ≡ B
∋:=-det d d′ = bind-inj (∋e-det d d′)

------------------------------------------------------------------------
-- 2.  Well-formed types over a type context
------------------------------------------------------------------------

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X
  wf-ℕ   : Δ ⊢ᵗ `ℕ
  wf-𝔹   : Δ ⊢ᵗ `𝔹
  wf-⇒   : Δ ⊢ᵗ A → Δ ⊢ᵗ B → Δ ⊢ᵗ (A ⇒ B)
  wf-∀   : (unmasked abst ∷ Δ) ⊢ᵗ A → Δ ⊢ᵗ (`∀ A)

data Base : Ty → Set where
  base-ℕ : Base `ℕ
  base-𝔹 : Base `𝔹

base-wf : Base A → Δ ⊢ᵗ A
base-wf base-ℕ = wf-ℕ
base-wf base-𝔹 = wf-𝔹

base-ren : Base A → renameᵗ ρ A ≡ A
base-ren base-ℕ = refl
base-ren base-𝔹 = refl

------------------------------------------------------------------------
-- 3.  TRANSPORT I — type context renaming
------------------------------------------------------------------------

-- A renaming of type contexts.  ONE field: it moves the ENTRY at every slot,
-- blocked entries included.  Knowledge transport (`ren-kn` below) is then
-- DEFINITIONAL — which is the whole bet of the binder design: a name is
-- moved by ρ, a spelling would have had to be re-derived.
record Ren (ρ : Renameᵗ) (Δ Δ′ : Ctxᵗ) : Set where
  constructor mkRen
  field ren∋ : ∀ {X E} → Δ ∋e X , E → Δ′ ∋e ρ X , renᵉ ρ E

open Ren public

ren-kn : Ren ρ Δ Δ′ → Δ ∋ X := A → Δ′ ∋ ρ X := renameᵗ ρ A
ren-kn r d = ren∋ r d

ren-tv : Ren ρ Δ Δ′ → Δ ∋tv X → Δ′ ∋tv ρ X
ren-tv r (E , d , v) = renᵉ _ E , ren∋ r d , renᵉ-Nameable v

ren-ext : Ren ρ Δ Δ′ → Ren (extᵗ ρ) (F ∷ Δ) (renᵉ ρ F ∷ Δ′)
ren-ext {ρ = ρ} {Δ = Δ} {Δ′ = Δ′} {F = F} r = mkRen go
  where
  go : ∀ {X E} → (F ∷ Δ) ∋e X , E
     → (renᵉ ρ F ∷ Δ′) ∋e extᵗ ρ X , renᵉ (extᵗ ρ) E
  go ez     rewrite renᵉ-⇑-comm ρ F = ez
  go (es {E = E₀} d) rewrite renᵉ-⇑-comm ρ E₀ = es (ren∋ r d)

wf-ren : Ren ρ Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ renameᵗ ρ A
wf-ren r (wf-var tv)  = wf-var (ren-tv r tv)
wf-ren r wf-ℕ         = wf-ℕ
wf-ren r wf-𝔹         = wf-𝔹
wf-ren r (wf-⇒ wA wB) = wf-⇒ (wf-ren r wA) (wf-ren r wB)
wf-ren r (wf-∀ wA)    = wf-∀ (wf-ren (ren-ext r) wA)

------------------------------------------------------------------------
-- 4.  TRANSPORT II — type context growth / knowledge refinement
------------------------------------------------------------------------

-- b ⊑ᵇ b′ : b′ knows at least what b knows, AT THE BINDING LAYER.  Each
-- constructor's two letters are the two bindings it relates — `a` = abst,
-- `b` = bind.
--   le-aa : abst stays abst
--   le-ab : a Λ-bound slot may become a binder              (TyBeta)
--   le-bb : a binder keeps its rep
-- There is NO clause in the other direction: a binder never loses its rep.
data _⊑ᵇ_ : Binding → Binding → Set where
  le-aa : abst ⊑ᵇ abst
  le-ab : abst ⊑ᵇ bind A
  le-bb : bind A ⊑ᵇ bind A

-- … and E ⊑ᵉ E′ lifts it through the LOCK LAYER.  `u` = unmasked,
-- `m` = masked; the pair of letters is the pair of locks.
--   le-uu : a nameable slot stays nameable
--   le-mm : concealment is monotone in what it hides
--   le-mu : a concealed slot may be re-exposed              (Cancel)
-- There is no `le-um`: refinement never hides.
data _⊑ᵉ_ : Ent → Ent → Set where
  le-uu : b ⊑ᵇ b′ → unmasked b ⊑ᵉ unmasked b′
  le-mm : b ⊑ᵇ b′ → masked b   ⊑ᵉ masked b′
  le-mu : b ⊑ᵇ b′ → masked b   ⊑ᵉ unmasked b′

infix 4 _⊑_
data _⊑_ : Ctxᵗ → Ctxᵗ → Set where
  le[] : [] ⊑ []
  le∷  : E ⊑ᵉ E′ → Δ ⊑ Δ′ → (E ∷ Δ) ⊑ (E′ ∷ Δ′)

⊑ᵇ-refl : (b : Binding) → b ⊑ᵇ b
⊑ᵇ-refl abst     = le-aa
⊑ᵇ-refl (bind A) = le-bb

⊑ᵉ-refl : (E : Ent) → E ⊑ᵉ E
⊑ᵉ-refl (unmasked b) = le-uu (⊑ᵇ-refl b)
⊑ᵉ-refl (masked b)   = le-mm (⊑ᵇ-refl b)

⊑-refl : (Δ : Ctxᵗ) → Δ ⊑ Δ
⊑-refl []      = le[]
⊑-refl (E ∷ Δ) = le∷ (⊑ᵉ-refl E) (⊑-refl Δ)

⊑ᵇ-⇑ : b ⊑ᵇ b′ → renᵇ ρ b ⊑ᵇ renᵇ ρ b′
⊑ᵇ-⇑ le-aa = le-aa
⊑ᵇ-⇑ le-ab = le-ab
⊑ᵇ-⇑ le-bb = le-bb

⊑ᵉ-⇑ : E ⊑ᵉ E′ → ⇑ᵉ E ⊑ᵉ ⇑ᵉ E′
⊑ᵉ-⇑ (le-uu l) = le-uu (⊑ᵇ-⇑ l)
⊑ᵉ-⇑ (le-mm l) = le-mm (⊑ᵇ-⇑ l)
⊑ᵉ-⇑ (le-mu l) = le-mu (⊑ᵇ-⇑ l)

⊑-∋e : Δ ⊑ Δ′ → Δ ∋e X , E → ∃[ E′ ] ((Δ′ ∋e X , E′) × E ⊑ᵉ E′)
⊑-∋e (le∷ l ls) ez     = _ , ez , ⊑ᵉ-⇑ l
⊑-∋e (le∷ l ls) (es d) with ⊑-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵉ-⇑ l′

nameable-mono : E ⊑ᵉ E′ → Nameable E → Nameable E′
nameable-mono (le-uu _) nameable = nameable
nameable-mono (le-mm _) ()
nameable-mono (le-mu _) ()

⊑-tv : Δ ⊑ Δ′ → Δ ∋tv X → Δ′ ∋tv X
⊑-tv ls (E , d , v) with ⊑-∋e ls d
... | E′ , d′ , l′ = E′ , d′ , nameable-mono l′ v

-- A binder is never lost and never re-spelled: the ONLY ⊑ᵉ clause whose
-- source is `bind A` is `le-bb`.  This is the deleted demotion, as a theorem.
⊑-kn : Δ ⊑ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A
⊑-kn ls d with ⊑-∋e ls d
... | unmasked (bind A) , d′ , le-uu le-bb = d′

-- Refinement composes.  Transitivity is now the LOCK LAYER's four legal
-- compositions over `⊑ᵇ-trans`, and no clause has to carry a `Nameable`
-- witness: the second step's lock is read off its constructor.
⊑ᵇ-trans : b ⊑ᵇ b′ → b′ ⊑ᵇ b″ → b ⊑ᵇ b″
⊑ᵇ-trans le-aa l′    = l′
⊑ᵇ-trans le-ab le-bb = le-ab
⊑ᵇ-trans le-bb le-bb = le-bb

⊑ᵉ-trans : E ⊑ᵉ E′ → E′ ⊑ᵉ E″ → E ⊑ᵉ E″
⊑ᵉ-trans (le-uu l) (le-uu l′) = le-uu (⊑ᵇ-trans l l′)
⊑ᵉ-trans (le-mm l) (le-mm l′) = le-mm (⊑ᵇ-trans l l′)
⊑ᵉ-trans (le-mm l) (le-mu l′) = le-mu (⊑ᵇ-trans l l′)
⊑ᵉ-trans (le-mu l) (le-uu l′) = le-mu (⊑ᵇ-trans l l′)

⊑-trans : Δ ⊑ Δ′ → Δ′ ⊑ Δ″ → Δ ⊑ Δ″
⊑-trans le[]       le[]         = le[]
⊑-trans (le∷ l ls) (le∷ l′ ls′) = le∷ (⊑ᵉ-trans l l′) (⊑-trans ls ls′)

⊑-wf : Δ ⊑ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
⊑-wf ls (wf-var tv)  = wf-var (⊑-tv ls tv)
⊑-wf ls wf-ℕ         = wf-ℕ
⊑-wf ls wf-𝔹         = wf-𝔹
⊑-wf ls (wf-⇒ wA wB) = wf-⇒ (⊑-wf ls wA) (⊑-wf ls wB)
⊑-wf ls (wf-∀ wA)    = wf-∀ (⊑-wf (le∷ (le-uu le-aa) ls) wA)

------------------------------------------------------------------------
-- 4b.  TRANSPORT IIa — refinement THAT DOES NOT RE-EXPOSE
------------------------------------------------------------------------

-- `_⊑ᵃ_` is `_⊑_` WITHOUT `le-mu`: the refinement may learn a rep at an
-- abstract slot, but it may NOT un-mask a slot.  This is the transport a
-- TERM may travel along (`⊢retag`, strong.TermSubst), and it has to be,
-- because an `unlock X` in a boundary CLAIMS that X is locked
-- (`sw-u`, strong.CtxMorph) and `le-mu` destroys the claim.  Types and
-- conversions keep the full `_⊑_` (`⊑-wf`, `conv-⊑`): a TYPE claims
-- nameability, which only grows.
-- The BINDING layer is shared with `_⊑ᵉ_` — learning a rep at an
-- abstract slot is legal for both.  Only the LOCK layer differs: the two
-- locks must AGREE.
data _⊑ᵃᵉ_ : Ent → Ent → Set where
  la-uu : b ⊑ᵇ b′ → unmasked b ⊑ᵃᵉ unmasked b′
  la-mm : b ⊑ᵇ b′ → masked b   ⊑ᵃᵉ masked b′

infix 4 _⊑ᵃ_
data _⊑ᵃ_ : Ctxᵗ → Ctxᵗ → Set where
  la[] : [] ⊑ᵃ []
  la∷  : E ⊑ᵃᵉ E′ → Δ ⊑ᵃ Δ′ → (E ∷ Δ) ⊑ᵃ (E′ ∷ Δ′)

⊑ᵃᵉ→⊑ᵉ : E ⊑ᵃᵉ E′ → E ⊑ᵉ E′
⊑ᵃᵉ→⊑ᵉ (la-uu l) = le-uu l
⊑ᵃᵉ→⊑ᵉ (la-mm l) = le-mm l

⊑ᵃ→⊑ : Δ ⊑ᵃ Δ′ → Δ ⊑ Δ′
⊑ᵃ→⊑ la[]        = le[]
⊑ᵃ→⊑ (la∷ l ls)  = le∷ (⊑ᵃᵉ→⊑ᵉ l) (⊑ᵃ→⊑ ls)

⊑ᵃᵉ-refl : (E : Ent) → E ⊑ᵃᵉ E
⊑ᵃᵉ-refl (unmasked b) = la-uu (⊑ᵇ-refl b)
⊑ᵃᵉ-refl (masked b)   = la-mm (⊑ᵇ-refl b)

⊑ᵃ-refl : (Δ : Ctxᵗ) → Δ ⊑ᵃ Δ
⊑ᵃ-refl []      = la[]
⊑ᵃ-refl (E ∷ Δ) = la∷ (⊑ᵃᵉ-refl E) (⊑ᵃ-refl Δ)

⊑ᵃᵉ-⇑ : E ⊑ᵃᵉ E′ → ⇑ᵉ E ⊑ᵃᵉ ⇑ᵉ E′
⊑ᵃᵉ-⇑ (la-uu l) = la-uu (⊑ᵇ-⇑ l)
⊑ᵃᵉ-⇑ (la-mm l) = la-mm (⊑ᵇ-⇑ l)

⊑ᵃ-∋e : Δ ⊑ᵃ Δ′ → Δ ∋e X , E → ∃[ E′ ] ((Δ′ ∋e X , E′) × E ⊑ᵃᵉ E′)
⊑ᵃ-∋e (la∷ l ls) ez     = _ , ez , ⊑ᵃᵉ-⇑ l
⊑ᵃ-∋e (la∷ l ls) (es d) with ⊑ᵃ-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵃᵉ-⇑ l′

-- THE CLAUSE THAT MAKES `⊑ᵃ` THE RIGHT TRANSPORT FOR A BOUNDARY: a
-- LOCKED slot stays locked.  (Under `_⊑_` it need not — that is `le-mu`.)
⊑ᵃᵉ-Locked : E ⊑ᵃᵉ E′ → Locked E → Locked E′
⊑ᵃᵉ-Locked (la-uu l) ()
⊑ᵃᵉ-Locked (la-mm l) locked = locked

⊑ᵃ-tv : Δ ⊑ᵃ Δ′ → Δ ∋tv X → Δ′ ∋tv X
⊑ᵃ-tv ls tv = ⊑-tv (⊑ᵃ→⊑ ls) tv

⊑ᵃ-lk : Δ ⊑ᵃ Δ′ → Δ ∋lk X → Δ′ ∋lk X
⊑ᵃ-lk ls (E , d , lk) with ⊑ᵃ-∋e ls d
... | E′ , d′ , l′ = E′ , d′ , ⊑ᵃᵉ-Locked l′ lk

------------------------------------------------------------------------
-- 5.  Injective renamings, iterated extension, iterated lifting
------------------------------------------------------------------------

-- The ONE hypothesis the transport needs beyond `Ren`: ρ must not confuse two
-- slots, since masking is positional.  Every use site is `suc` or an `extᵗ`
-- of an injective renaming, so it is discharged structurally.  It mentions no
-- representation at all.
Inj : Renameᵗ → Set
Inj ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

Inj-suc : Inj suc
Inj-suc = suc-injective

Inj-ext : Inj ρ → Inj (extᵗ ρ)
Inj-ext i {zero}  {zero}  eq = refl
Inj-ext i {suc X} {suc Y} eq = cong suc (i (suc-injective eq))

extN : ℕ → Renameᵗ → Renameᵗ
extN zero    ρ = ρ
extN (suc n) ρ = extᵗ (extN n ρ)

Inj-extN : (n : ℕ) → Inj ρ → Inj (extN n ρ)
Inj-extN zero    i = i
Inj-extN (suc n) i = Inj-ext (Inj-extN n i)

shiftBy : ℕ → Ty → Ty
shiftBy zero    A = A
shiftBy (suc n) A = ⇑ᵗ (shiftBy n A)

shiftBy-ren : (n : ℕ) (ρ : Renameᵗ) (A : Ty)
  → renameᵗ (extN n ρ) (shiftBy n A) ≡ shiftBy n (renameᵗ ρ A)
shiftBy-ren zero    ρ A = refl
shiftBy-ren (suc n) ρ A =
  trans (ren-⇑-comm (extN n ρ) (shiftBy n A))
        (cong ⇑ᵗ (shiftBy-ren n ρ A))

-- The SAME lifting, read UNDER one binder: `shiftBy n` on a `` `∀ `` body.
-- TyPeelR needs it, because a ∀ conversion's TARGET body is the
-- exterior type's body lifted past the boundary's binders.
shiftBodyBy : ℕ → Ty → Ty
shiftBodyBy zero    B = B
shiftBodyBy (suc n) B = renameᵗ (extᵗ suc) (shiftBodyBy n B)

shiftBy-shiftBodyBy : (n : ℕ) (B : Ty) → shiftBy n (`∀ B) ≡ `∀ (shiftBodyBy n B)
shiftBy-shiftBodyBy zero    B = refl
shiftBy-shiftBodyBy (suc n) B rewrite shiftBy-shiftBodyBy n B = refl

shiftBy-base : (n : ℕ) → Base A → shiftBy n A ≡ A
shiftBy-base zero    b = refl
shiftBy-base (suc n) b rewrite shiftBy-base n b = base-ren b

shiftBy-var : (n Y : ℕ) → shiftBy n (` Y) ≡ ` (n + Y)
shiftBy-var zero    Y = refl
shiftBy-var (suc n) Y rewrite shiftBy-var n Y = refl

tvar-inj : _≡_ {A = Ty} (` X) (` Y) → X ≡ Y
tvar-inj refl = refl

-- A base type is never a variable, at any lifting.
base≢var : (n : ℕ) → Base A → shiftBy n A ≡ ` X → ⊥
base≢var n base-ℕ eq with trans (sym (shiftBy-base n base-ℕ)) eq
... | ()
base≢var n base-𝔹 eq with trans (sym (shiftBy-base n base-𝔹)) eq
... | ()

------------------------------------------------------------------------
-- 6.  Masking a slot in place  (the conceal/alias mechanism)
------------------------------------------------------------------------

-- One entry update at one slot: `mask = updateAt maskEnt` and
-- `unmask = updateAt unmaskEnt`.
updateAt : (Ent → Ent) → ℕ → Ctxᵗ → Ctxᵗ
updateAt f X       []      = []
updateAt f zero    (E ∷ Δ) = f E ∷ Δ
updateAt f (suc X) (E ∷ Δ) = E ∷ updateAt f X Δ

-- SETTING THE LOCK, AND CLEARING IT.  Both are TOTAL and IDEMPOTENT:
-- there is only one lock to set or clear.  `maskEnt` is never applied to
-- an already-masked slot in a well-formed term — `sw-l`
-- (strong.CtxMorph), the change half of `Δ ⊢ᵐ Θ`, admits `lock X` only at
-- a NAMEABLE slot — but the function does not have to know that, and that
-- is the point: nothing has to rule out a second mask, because a second
-- mask is not expressible.
maskEnt : Ent → Ent
maskEnt (unmasked b) = masked b
maskEnt (masked b)   = masked b

unmaskEnt : Ent → Ent
unmaskEnt (unmasked b) = unmasked b
unmaskEnt (masked b)   = unmasked b

mask unmask : ℕ → Ctxᵗ → Ctxᵗ
mask   = updateAt maskEnt
unmask = updateAt unmaskEnt

-- Both update functions commute with renaming — they touch no spelling.
maskEnt-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ ρ (maskEnt E) ≡ maskEnt (renᵉ ρ E)
maskEnt-comm ρ (unmasked b) = refl
maskEnt-comm ρ (masked b)   = refl

unmaskEnt-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ ρ (unmaskEnt E) ≡ unmaskEnt (renᵉ ρ E)
unmaskEnt-comm ρ (unmasked b) = refl
unmaskEnt-comm ρ (masked b)   = refl

_≟ℕ_ : (X Y : ℕ) → Dec (X ≡ Y)
zero  ≟ℕ zero  = yes refl
zero  ≟ℕ suc Y = no (λ ())
suc X ≟ℕ zero  = no (λ ())
suc X ≟ℕ suc Y with X ≟ℕ Y
... | yes refl = yes refl
... | no ne    = no (λ eq → ne (suc-injective eq))

module _ (f : Ent → Ent)
         (fc : ∀ ρ E → renᵉ ρ (f E) ≡ f (renᵉ ρ E)) where

  updateAt-hit : ∀ {Δ X E} → Δ ∋e X , E → updateAt f X Δ ∋e X , f E
  updateAt-hit (ez {E = E₁})   rewrite sym (fc suc E₁) = ez
  updateAt-hit (es {E = E₀} d) rewrite sym (fc suc E₀) = es (updateAt-hit d)

  updateAt-hit⁻ : ∀ {Δ X E} → updateAt f X Δ ∋e X , E
           → ∃[ E₀ ] ((Δ ∋e X , E₀) × (E ≡ f E₀))
  updateAt-hit⁻ {E₁ ∷ Δ} {zero}  ez     = _ , ez , fc suc E₁
  updateAt-hit⁻ {E₁ ∷ Δ} {suc X} (es d) with updateAt-hit⁻ d
  ... | E₀ , d₀ , eq = _ , es d₀ , trans (cong ⇑ᵉ eq) (fc suc E₀)

  updateAt-miss : ∀ {Δ X Y E} → X ≢ Y → Δ ∋e Y , E → updateAt f X Δ ∋e Y , E
  updateAt-miss {X = zero}  ne ez     = ⊥-elim (ne refl)
  updateAt-miss {X = suc X} ne ez     = ez
  updateAt-miss {X = zero}  ne (es d) = es d
  updateAt-miss {X = suc X} ne (es d) =
    es (updateAt-miss (λ eq → ne (cong suc eq)) d)

  updateAt-miss⁻ : ∀ {Δ X Y E} → X ≢ Y → updateAt f X Δ ∋e Y , E → Δ ∋e Y , E
  updateAt-miss⁻ {Δ = E₁ ∷ Δ} {zero}  ne ez     = ⊥-elim (ne refl)
  updateAt-miss⁻ {Δ = E₁ ∷ Δ} {suc X} ne ez     = ez
  updateAt-miss⁻ {Δ = E₁ ∷ Δ} {zero}  ne (es d) = es d
  updateAt-miss⁻ {Δ = E₁ ∷ Δ} {suc X} ne (es d) =
    es (updateAt-miss⁻ (λ eq → ne (cong suc eq)) d)

  -- TRANSPORT of one mask/unmask across a type context renaming.
  ren-updateAt : ∀ {Δ Δ′ ρ X} → Ren ρ Δ Δ′ → Inj ρ
          → Ren ρ (updateAt f X Δ) (updateAt f (ρ X) Δ′)
  ren-updateAt {ρ = ρ} {X = X} r i = mkRen go
    where
    go : ∀ {Y E} → updateAt f X _ ∋e Y , E
       → updateAt f (ρ X) _ ∋e ρ Y , renᵉ ρ E
    go {Y} d with X ≟ℕ Y
    ... | yes refl with updateAt-hit⁻ d
    ...   | E₀ , d₀ , refl =
            subst (λ e → updateAt f (ρ X) _ ∋e ρ X , e) (sym (fc ρ E₀))
                  (updateAt-hit (ren∋ r d₀))
    go {Y} d | no ne =
      updateAt-miss (λ eq → ne (i eq)) (ren∋ r (updateAt-miss⁻ ne d))

  -- TRANSPORT of one mask/unmask across knowledge refinement.
  ⊑-updateAt : ∀ {X Δ Δ′} → (∀ {E E′} → E ⊑ᵉ E′ → f E ⊑ᵉ f E′)
        → Δ ⊑ Δ′ → updateAt f X Δ ⊑ updateAt f X Δ′
  ⊑-updateAt {zero}  fm (le∷ l ls) = le∷ (fm l) ls
  ⊑-updateAt {suc X} fm (le∷ l ls) = le∷ l (⊑-updateAt fm ls)
  ⊑-updateAt         fm le[]       = le[]

maskEnt-mono : E ⊑ᵉ E′ → maskEnt E ⊑ᵉ maskEnt E′
maskEnt-mono (le-uu l) = le-mm l
maskEnt-mono (le-mm l) = le-mm l
maskEnt-mono (le-mu l) = le-mm l

-- Masking a slot only LOSES nameability, so a masked type context refines
-- to the unmasked one.  (There is no converse: that is the deleted
-- demotion.)
-- Every clause is now ONE lock step, with no recursion and no `Nameable`
-- witness to invent — the target's lock is read off its constructor.
maskEnt-le : E ⊑ᵉ E′ → maskEnt E ⊑ᵉ E′
maskEnt-le (le-uu l) = le-mu l
maskEnt-le (le-mm l) = le-mm l
maskEnt-le (le-mu l) = le-mu l

unmaskEnt-mono : E ⊑ᵉ E′ → unmaskEnt E ⊑ᵉ unmaskEnt E′
unmaskEnt-mono (le-uu l) = le-uu l
unmaskEnt-mono (le-mm l) = le-uu l
unmaskEnt-mono (le-mu l) = le-uu l

ren-mask : Ren ρ Δ Δ′ → Inj ρ → Ren ρ (mask X Δ) (mask (ρ X) Δ′)
ren-mask = ren-updateAt maskEnt maskEnt-comm

ren-unmask : Ren ρ Δ Δ′ → Inj ρ → Ren ρ (unmask X Δ) (unmask (ρ X) Δ′)
ren-unmask = ren-updateAt unmaskEnt unmaskEnt-comm

mask-⊑ : (Y : ℕ) → Δ ⊑ Δ′ → mask Y Δ ⊑ Δ′
mask-⊑ Y       le[]        = le[]
mask-⊑ zero    (le∷ l ls)  = le∷ (maskEnt-le l) ls
mask-⊑ (suc Y) (le∷ l ls)  = le∷ l (mask-⊑ Y ls)

-- Unmasking only ADDS nameability, so the type context refines to its own
-- unmasking.  (The `masked` clause is the ⊑ᵉ step `le-mu` itself: there
-- is exactly one lock to clear.)
⊑ᵉ-unmaskEnt : (E : Ent) → E ⊑ᵉ unmaskEnt E
⊑ᵉ-unmaskEnt (unmasked b) = le-uu (⊑ᵇ-refl b)
⊑ᵉ-unmaskEnt (masked b)   = le-mu (⊑ᵇ-refl b)

unmask-⊑ : (Y : ℕ) (Δ : Ctxᵗ) → Δ ⊑ unmask Y Δ
unmask-⊑ Y       []      = le[]
unmask-⊑ zero    (E ∷ Δ) = le∷ (⊑ᵉ-unmaskEnt E) (⊑-refl Δ)
unmask-⊑ (suc Y) (E ∷ Δ) = le∷ (⊑ᵉ-refl E) (unmask-⊑ Y Δ)

-- The `_⊑ᵃ_` transport of a one-slot update.  Both `maskEnt` and
-- `unmaskEnt` are monotone for it: each simply rewrites the LOCK layER
-- and passes the binding step through.
maskEnt-monoᵃ : E ⊑ᵃᵉ E′ → maskEnt E ⊑ᵃᵉ maskEnt E′
maskEnt-monoᵃ (la-uu l) = la-mm l
maskEnt-monoᵃ (la-mm l) = la-mm l

unmaskEnt-monoᵃ : E ⊑ᵃᵉ E′ → unmaskEnt E ⊑ᵃᵉ unmaskEnt E′
unmaskEnt-monoᵃ (la-uu l) = la-uu l
unmaskEnt-monoᵃ (la-mm l) = la-uu l

⊑ᵃ-updateAt : (f : Ent → Ent) → (∀ {E E′} → E ⊑ᵃᵉ E′ → f E ⊑ᵃᵉ f E′)
  → ∀ {X Δ Δ′} → Δ ⊑ᵃ Δ′ → updateAt f X Δ ⊑ᵃ updateAt f X Δ′
⊑ᵃ-updateAt f fm {zero}  (la∷ l ls) = la∷ (fm l) ls
⊑ᵃ-updateAt f fm {suc X} (la∷ l ls) = la∷ l (⊑ᵃ-updateAt f fm ls)
⊑ᵃ-updateAt f fm         la[]       = la[]

------------------------------------------------------------------------
-- 6b.  Locking and unlocking are EXACT INVERSES at a LOCKED slot
------------------------------------------------------------------------

-- THE TWO INVERSES ARE NOW SYMMETRIC, and each carries the one-clause
-- premise its own direction needs.
--
-- Unmasking undoes masking ONLY AT A NAMEABLE SLOT.  This is the ONE
-- place the two-layer entry costs something: with a stack of masks,
-- `unmask ∘ mask` was the identity everywhere (`masked` was injective and
-- the extra lock was simply popped); with one lock, `maskEnt` is
-- IDEMPOTENT, so at an already-masked slot `unmask (mask X Δ)` exposes
-- what Δ had hidden.  The premise is always at hand: `sw-l`
-- (strong.CtxMorph) admits `lock X` only at a `∋tv` slot, which is
-- exactly the discipline that made double masking unreachable before.
unmaskEnt-maskEnt : Nameable E → unmaskEnt (maskEnt E) ≡ E
unmaskEnt-maskEnt nameable = refl

unmask-mask : ∀ {Δ X} → Δ ∋tv X → unmask X (mask X Δ) ≡ Δ
unmask-mask (_ , ez   , v) =
  cong (_∷ _) (unmaskEnt-maskEnt (renᵉ-Nameable⁻ v))
unmask-mask (_ , es d , v) =
  cong (_ ∷_) (unmask-mask (_ , d , renᵉ-Nameable⁻ v))

-- Masking undoes unmasking ONLY at a LOCKED slot — which is exactly what
-- `sw-u` (strong.CtxMorph) demands of every `unlock`, and exactly why a
-- vacuous unlock had to be refused: at an already-nameable slot the
-- restoring `lock` of the dual would mask what the exterior left visible.
maskEnt-unmask : Locked E → maskEnt (unmaskEnt E) ≡ E
maskEnt-unmask locked = refl

mask-unmask : ∀ {Δ X} → Δ ∋lk X → mask X (unmask X Δ) ≡ Δ
mask-unmask (_ , ez     , lk) =
  cong (_∷ _) (maskEnt-unmask (Locked-ren⁻ lk))
mask-unmask (_ , es d   , lk) =
  cong (_ ∷_) (mask-unmask (_ , d , Locked-ren⁻ lk))

-- The two entry-level moves the dual performs, as lookup facts.
unmask-∋tv : ∀ {Δ X} → Δ ∋lk X → unmask X Δ ∋tv X
unmask-∋tv (masked b , d , locked) =
  _ , updateAt-hit unmaskEnt unmaskEnt-comm d , nameable

mask-∋lk : ∀ {Δ X} → Δ ∋tv X → mask X Δ ∋lk X
mask-∋lk (unmasked b , d , nameable) =
  _ , updateAt-hit maskEnt maskEnt-comm d , locked

------------------------------------------------------------------------
-- 7.  The bind prefix
------------------------------------------------------------------------

-- The `bind` entries of a boundary, pushed on as ordinary de Bruijn
-- binders.  The head of the list is interior slot 0; a rep uses the
-- exterior's slots, so it is lifted past the binders INSIDE it and past
-- nothing else — a bind is never blocked by its own frame's locks, and
-- sibling binds never interfere.
pushBinds : List Ty → Ctxᵗ → Ctxᵗ
pushBinds []       Δ = Δ
pushBinds (A ∷ As) Δ =
  unmasked (bind (shiftBy (length As) A)) ∷ pushBinds As Δ

-- As a well-formedness fact: a type over the exterior is a type inside
-- the bind prefix, lifted past exactly the binders in that prefix.
wf-shiftBy-pushBinds : (As : List Ty) → Δ ⊢ᵗ A
  → pushBinds As Δ ⊢ᵗ shiftBy (length As) A
wf-shiftBy-pushBinds []       w = w
wf-shiftBy-pushBinds (C ∷ As) w =
  wf-ren Ren-wk-pushBinds (wf-shiftBy-pushBinds As w)
  where
  Ren-wk-pushBinds : ∀ {E Δ″} → Ren suc Δ″ (E ∷ Δ″)
  Ren-wk-pushBinds = mkRen es

-- A one-slot update PAST the bind prefix is the update on the tail: the
-- prefix has `length As` entries and neither of them is touched.  This is
-- what lets a boundary's own masking be re-indexed INTO an inner frame
-- (strong.CtxMorph, `shiftScope`).
updateAt-pushBinds : (f : Ent → Ent) (As : List Ty) (X : ℕ) (Δ : Ctxᵗ)
  → updateAt f (length As + X) (pushBinds As Δ) ≡ pushBinds As (updateAt f X Δ)
updateAt-pushBinds f []       X Δ = refl
updateAt-pushBinds f (C ∷ As) X Δ =
  cong (unmasked (bind (shiftBy (length As) C)) ∷_)
       (updateAt-pushBinds f As X Δ)

-- A well-formed variable type IS a visible slot.
wf-var⁻ : Δ ⊢ᵗ ` X → Δ ∋tv X
wf-var⁻ (wf-var tv) = tv

⊑-pushBinds : (As : List Ty) → Δ ⊑ Δ′ → pushBinds As Δ ⊑ pushBinds As Δ′
⊑-pushBinds []       ls = ls
⊑-pushBinds (A ∷ As) ls = le∷ (le-uu le-bb) (⊑-pushBinds As ls)

⊑ᵃ-pushBinds : (As : List Ty) → Δ ⊑ᵃ Δ′ → pushBinds As Δ ⊑ᵃ pushBinds As Δ′
⊑ᵃ-pushBinds []       ls = ls
⊑ᵃ-pushBinds (A ∷ As) ls = la∷ (la-uu le-bb) (⊑ᵃ-pushBinds As ls)

-- The bind prefix transports the three entry-level lookups the boundary
-- judgement reads: a rep, a nameable slot, and a LOCKED slot.
pushBinds-∋tv : (As : List Ty) → Δ ∋tv X → pushBinds As Δ ∋tv (length As + X)
pushBinds-∋tv []       tv = tv
pushBinds-∋tv (C ∷ As) tv with pushBinds-∋tv As tv
... | E , d , v = _ , es d , renᵉ-Nameable v

pushBinds-∋lk : (As : List Ty) → Δ ∋lk X → pushBinds As Δ ∋lk (length As + X)
pushBinds-∋lk []       lk = lk
pushBinds-∋lk (C ∷ As) lk with pushBinds-∋lk As lk
... | E , d , l = _ , es d , renᵉ-Locked l

ren-∋lk : Ren ρ Δ Δ′ → Δ ∋lk X → Δ′ ∋lk ρ X
ren-∋lk r (E , d , l) = renᵉ _ E , ren∋ r d , renᵉ-Locked l

ren-pushBinds : (As : List Ty) (ρ : Renameᵗ) → Ren ρ Δ Δ′
         → Ren (extN (length As) ρ) (pushBinds As Δ)
               (pushBinds (map (renameᵗ ρ) As) Δ′)
ren-pushBinds []       ρ r = r
ren-pushBinds (A ∷ As) ρ r
  rewrite map-length (renameᵗ ρ) As
        | sym (shiftBy-ren (length As) ρ A) =
  ren-ext (ren-pushBinds As ρ r)

Inj-pushBinds : (As : List Ty) → Inj ρ → Inj (extN (length As) ρ)
Inj-pushBinds As i = Inj-extN (length As) i

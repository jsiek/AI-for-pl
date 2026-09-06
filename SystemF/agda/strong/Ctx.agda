module strong.Ctx where

-- Strong System F — THE TYPE CONTEXT (type contexts) and its transports.
--
-- A type context entry is one of
--
--   abst      a Λ-bound variable — no representation, and none can be
--             invented.
--   bind A    THE BINDER of an instantiation event.  A is the
--             representation, stored ONCE, as a type over this entry's
--             bind tail.  Every inner boundary that talks about this
--             variable carries only its NAME.
--   masked E  the slot is CONCEALED here: it may not be NAMED
--             (tightness), but its entry E is RETAINED, so the knowledge
--             is still on the type context for a later re-exposure
--             (`unlock`) to point back at.
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

data Ent : Set where
  abst   : Ent
  bind   : Ty → Ent
  masked : Ent → Ent

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ Δ′ Δ″ : Ctxᵗ
    E E′ E″ F : Ent
    A A′ B B′ C : Ty
    X Y Z : ℕ
    ρ ρ′ : Renameᵗ

renᵉ : Renameᵗ → Ent → Ent
renᵉ ρ abst       = abst
renᵉ ρ (bind A)   = bind (renameᵗ ρ A)
renᵉ ρ (masked E) = masked (renᵉ ρ E)

⇑ᵉ : Ent → Ent
⇑ᵉ = renᵉ suc

renᵉ-⇑-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ (extᵗ ρ) (⇑ᵉ E) ≡ ⇑ᵉ (renᵉ ρ E)
renᵉ-⇑-comm ρ abst       = refl
renᵉ-⇑-comm ρ (bind A)   = cong bind (ren-⇑-comm ρ A)
renᵉ-⇑-comm ρ (masked E) = cong masked (renᵉ-⇑-comm ρ E)

-- Entry lookup.  The entry is returned SHIFTED into the ambient context, so
-- `Δ ∋e X , bind A` means "slot X is a binder whose rep, read in Δ, is A".
-- One relation serves every purpose: knowledge, nameability, and masking.
infix 4 _∋e_,_
data _∋e_,_ : Ctxᵗ → ℕ → Ent → Set where
  ez : (E ∷ Δ) ∋e zero , ⇑ᵉ E
  es : Δ ∋e X , E → (F ∷ Δ) ∋e suc X , ⇑ᵉ E

-- A slot may be NAMED iff its entry is not masked.  This is the whole of
-- the tightness discipline: `masked` is unnameable in types and in terms.
data Nameable : Ent → Set where
  nameable-a : Nameable abst
  nameable-b : Nameable (bind A)

renᵉ-Nameable : Nameable E → Nameable (renᵉ ρ E)
renᵉ-Nameable nameable-a = nameable-a
renᵉ-Nameable nameable-b = nameable-b

infix 4 _∋tv_
_∋tv_ : Ctxᵗ → ℕ → Set
Δ ∋tv X = ∃[ E ] ((Δ ∋e X , E) × Nameable E)

-- THE COMPLEMENT OF `Nameable`, and the whole of what an `unlock` may
-- restore: an entry masked ONCE over a nameable one.  `Locked` is what
-- `mw-u` (strong.Terms) demands and what makes `mask ∘ unmask` the
-- identity at the slot (`mask-unmask`) — the fact the dual's restoring
-- `lock` needs.  A doubly masked entry is NOT `Locked`, and no
-- `Δ ⊢ᵐ Θ` ever produces one (`mw-l` masks only a nameable slot).
data Locked : Ent → Set where
  locked : Nameable E → Locked (masked E)

renᵉ-Locked : Locked E → Locked (renᵉ ρ E)
renᵉ-Locked (locked v) = locked (renᵉ-Nameable v)

renᵉ-Nameable⁻ : Nameable (renᵉ ρ E) → Nameable E
renᵉ-Nameable⁻ {E = abst}     v = nameable-a
renᵉ-Nameable⁻ {E = bind A}   v = nameable-b
renᵉ-Nameable⁻ {E = masked E} ()

Locked-ren⁻ : Locked (renᵉ ρ E) → Locked E
Locked-ren⁻ {E = abst}     ()
Locked-ren⁻ {E = bind A}   ()
Locked-ren⁻ {E = masked E} (locked v) = locked (renᵉ-Nameable⁻ v)

infix 4 _∋lk_
_∋lk_ : Ctxᵗ → ℕ → Set
Δ ∋lk X = ∃[ E ] ((Δ ∋e X , E) × Locked E)

-- BINDER-SYNTACTIC LOOKUP.  This is the only way any rep is ever read.
infix 4 _∋_:=_
_∋_:=_ : Ctxᵗ → ℕ → Ty → Set
Δ ∋ X := A = Δ ∋e X , bind A

∋:=→∋tv : Δ ∋ X := A → Δ ∋tv X
∋:=→∋tv d = bind _ , d , nameable-b

-- Lookup is a partial FUNCTION, which is what makes every rule that mints an
-- identity conversion at a looked-up rep deterministic.
∋e-det : Δ ∋e X , E → Δ ∋e X , E′ → E ≡ E′
∋e-det ez     ez      = refl
∋e-det (es d) (es d′) = cong ⇑ᵉ (∋e-det d d′)

bind-inj : _≡_ {A = Ent} (bind A) (bind B) → A ≡ B
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
  wf-∀   : (abst ∷ Δ) ⊢ᵗ A → Δ ⊢ᵗ (`∀ A)

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

-- E ⊑ᵉ E′ : E′ knows at least what E knows.  Each constructor's two
-- letters are the two entries it relates — `a` = abst, `b` = bind,
-- `m` = masked — with `u` for "unmasked, whatever it is".
--   le-aa : abst stays abst
--   le-ab : a Λ-bound slot may become a binder              (TyBeta)
--   le-bb : a binder keeps its rep
--   le-mm : concealment is monotone in what it hides
--   le-mu : a concealed slot may be re-exposed              (Cancel)
-- There is NO clause in the other direction: a binder never loses its rep.
data _⊑ᵉ_ : Ent → Ent → Set where
  le-aa : abst ⊑ᵉ abst
  le-ab : abst ⊑ᵉ bind A
  le-bb : bind A ⊑ᵉ bind A
  le-mm : E ⊑ᵉ E′ → masked E ⊑ᵉ masked E′
  le-mu : E ⊑ᵉ E′ → Nameable E′ → masked E ⊑ᵉ E′

infix 4 _⊑_
data _⊑_ : Ctxᵗ → Ctxᵗ → Set where
  le[] : [] ⊑ []
  le∷  : E ⊑ᵉ E′ → Δ ⊑ Δ′ → (E ∷ Δ) ⊑ (E′ ∷ Δ′)

⊑ᵉ-refl : (E : Ent) → E ⊑ᵉ E
⊑ᵉ-refl abst    = le-aa
⊑ᵉ-refl (bind A) = le-bb
⊑ᵉ-refl (masked E) = le-mm (⊑ᵉ-refl E)

⊑-refl : (Δ : Ctxᵗ) → Δ ⊑ Δ
⊑-refl []      = le[]
⊑-refl (E ∷ Δ) = le∷ (⊑ᵉ-refl E) (⊑-refl Δ)

⊑ᵉ-⇑ : E ⊑ᵉ E′ → ⇑ᵉ E ⊑ᵉ ⇑ᵉ E′
⊑ᵉ-⇑ le-aa        = le-aa
⊑ᵉ-⇑ le-ab        = le-ab
⊑ᵉ-⇑ le-bb        = le-bb
⊑ᵉ-⇑ (le-mm l)    = le-mm (⊑ᵉ-⇑ l)
⊑ᵉ-⇑ (le-mu l v)  = le-mu (⊑ᵉ-⇑ l) (renᵉ-Nameable v)

⊑-∋e : Δ ⊑ Δ′ → Δ ∋e X , E → ∃[ E′ ] ((Δ′ ∋e X , E′) × E ⊑ᵉ E′)
⊑-∋e (le∷ l ls) ez     = _ , ez , ⊑ᵉ-⇑ l
⊑-∋e (le∷ l ls) (es d) with ⊑-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵉ-⇑ l′

nameable-mono : E ⊑ᵉ E′ → Nameable E → Nameable E′
nameable-mono le-aa        nameable-a = nameable-a
nameable-mono le-ab        nameable-a = nameable-b
nameable-mono le-bb        nameable-b = nameable-b
nameable-mono (le-mm _)    ()
nameable-mono (le-mu _ _)  ()

⊑-tv : Δ ⊑ Δ′ → Δ ∋tv X → Δ′ ∋tv X
⊑-tv ls (E , d , v) with ⊑-∋e ls d
... | E′ , d′ , l′ = E′ , d′ , nameable-mono l′ v

-- A binder is never lost and never re-spelled: the ONLY ⊑ᵉ clause whose
-- source is `bind A` is `le-bb`.  This is the deleted demotion, as a theorem.
⊑-kn : Δ ⊑ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A
⊑-kn ls d with ⊑-∋e ls d
... | bind A , d′ , le-bb = d′

-- Refinement composes.  (The only clause that has to think is `le-mu`:
-- an entry that stops being blocked stays unblocked, and `nameable-mono`
-- carries its visibility along the second step.)
⊑ᵉ-trans : E ⊑ᵉ E′ → E′ ⊑ᵉ E″ → E ⊑ᵉ E″
⊑ᵉ-trans le-aa       l′           = l′
⊑ᵉ-trans le-ab       le-bb        = le-ab
⊑ᵉ-trans le-bb       le-bb        = le-bb
⊑ᵉ-trans (le-mm l)   (le-mm l′)   = le-mm (⊑ᵉ-trans l l′)
⊑ᵉ-trans (le-mm l)   (le-mu l′ v) = le-mu (⊑ᵉ-trans l l′) v
⊑ᵉ-trans (le-mu l v) l′           = le-mu (⊑ᵉ-trans l l′) (nameable-mono l′ v)

⊑-trans : Δ ⊑ Δ′ → Δ′ ⊑ Δ″ → Δ ⊑ Δ″
⊑-trans le[]       le[]         = le[]
⊑-trans (le∷ l ls) (le∷ l′ ls′) = le∷ (⊑ᵉ-trans l l′) (⊑-trans ls ls′)

⊑-wf : Δ ⊑ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
⊑-wf ls (wf-var tv)  = wf-var (⊑-tv ls tv)
⊑-wf ls wf-ℕ         = wf-ℕ
⊑-wf ls wf-𝔹         = wf-𝔹
⊑-wf ls (wf-⇒ wA wB) = wf-⇒ (⊑-wf ls wA) (⊑-wf ls wB)
⊑-wf ls (wf-∀ wA)    = wf-∀ (⊑-wf (le∷ le-aa ls) wA)

------------------------------------------------------------------------
-- 4b.  TRANSPORT IIa — refinement THAT DOES NOT RE-EXPOSE
------------------------------------------------------------------------

-- `_⊑ᵃ_` is `_⊑_` WITHOUT `le-mu`: the refinement may learn a rep at an
-- abstract slot, but it may NOT un-mask a slot.  This is the transport a
-- TERM may travel along (`⊢retag`, strong.TermSubst), and it has to be,
-- because an `unlock X` in a boundary CLAIMS that X is locked
-- (`mw-u`, strong.Terms) and `le-mu` destroys the claim.  Types and
-- conversions keep the full `_⊑_` (`⊑-wf`, `conv-⊑`): a TYPE claims
-- nameability, which only grows.
data _⊑ᵃᵉ_ : Ent → Ent → Set where
  la-aa : abst ⊑ᵃᵉ abst
  la-ab : abst ⊑ᵃᵉ bind A
  la-bb : bind A ⊑ᵃᵉ bind A
  la-mm : E ⊑ᵃᵉ E′ → masked E ⊑ᵃᵉ masked E′

infix 4 _⊑ᵃ_
data _⊑ᵃ_ : Ctxᵗ → Ctxᵗ → Set where
  la[] : [] ⊑ᵃ []
  la∷  : E ⊑ᵃᵉ E′ → Δ ⊑ᵃ Δ′ → (E ∷ Δ) ⊑ᵃ (E′ ∷ Δ′)

⊑ᵃᵉ→⊑ᵉ : E ⊑ᵃᵉ E′ → E ⊑ᵉ E′
⊑ᵃᵉ→⊑ᵉ la-aa     = le-aa
⊑ᵃᵉ→⊑ᵉ la-ab     = le-ab
⊑ᵃᵉ→⊑ᵉ la-bb     = le-bb
⊑ᵃᵉ→⊑ᵉ (la-mm l) = le-mm (⊑ᵃᵉ→⊑ᵉ l)

⊑ᵃ→⊑ : Δ ⊑ᵃ Δ′ → Δ ⊑ Δ′
⊑ᵃ→⊑ la[]        = le[]
⊑ᵃ→⊑ (la∷ l ls)  = le∷ (⊑ᵃᵉ→⊑ᵉ l) (⊑ᵃ→⊑ ls)

⊑ᵃᵉ-refl : (E : Ent) → E ⊑ᵃᵉ E
⊑ᵃᵉ-refl abst       = la-aa
⊑ᵃᵉ-refl (bind A)   = la-bb
⊑ᵃᵉ-refl (masked E) = la-mm (⊑ᵃᵉ-refl E)

⊑ᵃ-refl : (Δ : Ctxᵗ) → Δ ⊑ᵃ Δ
⊑ᵃ-refl []      = la[]
⊑ᵃ-refl (E ∷ Δ) = la∷ (⊑ᵃᵉ-refl E) (⊑ᵃ-refl Δ)

⊑ᵃᵉ-⇑ : E ⊑ᵃᵉ E′ → ⇑ᵉ E ⊑ᵃᵉ ⇑ᵉ E′
⊑ᵃᵉ-⇑ la-aa     = la-aa
⊑ᵃᵉ-⇑ la-ab     = la-ab
⊑ᵃᵉ-⇑ la-bb     = la-bb
⊑ᵃᵉ-⇑ (la-mm l) = la-mm (⊑ᵃᵉ-⇑ l)

⊑ᵃ-∋e : Δ ⊑ᵃ Δ′ → Δ ∋e X , E → ∃[ E′ ] ((Δ′ ∋e X , E′) × E ⊑ᵃᵉ E′)
⊑ᵃ-∋e (la∷ l ls) ez     = _ , ez , ⊑ᵃᵉ-⇑ l
⊑ᵃ-∋e (la∷ l ls) (es d) with ⊑ᵃ-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵃᵉ-⇑ l′

-- THE CLAUSE THAT MAKES `⊑ᵃ` THE RIGHT TRANSPORT FOR A BOUNDARY: a
-- LOCKED slot stays locked.  (Under `_⊑_` it need not — that is `le-mu`.)
⊑ᵃᵉ-Locked : E ⊑ᵃᵉ E′ → Locked E → Locked E′
⊑ᵃᵉ-Locked (la-mm l) (locked v) = locked (nameable-mono (⊑ᵃᵉ→⊑ᵉ l) v)

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

-- One entry update at one slot: `mask = updateAt masked` and
-- `unmask = updateAt unmaskEnt`.
updateAt : (Ent → Ent) → ℕ → Ctxᵗ → Ctxᵗ
updateAt f X       []      = []
updateAt f zero    (E ∷ Δ) = f E ∷ Δ
updateAt f (suc X) (E ∷ Δ) = E ∷ updateAt f X Δ

unmaskEnt : Ent → Ent
unmaskEnt abst       = abst
unmaskEnt (bind A)   = bind A
unmaskEnt (masked E) = E

mask unmask : ℕ → Ctxᵗ → Ctxᵗ
mask   = updateAt masked
unmask = updateAt unmaskEnt

-- Both update functions commute with renaming — they touch no spelling.
masked-comm : (ρ : Renameᵗ) (E : Ent) → renᵉ ρ (masked E) ≡ masked (renᵉ ρ E)
masked-comm ρ E = refl

unmaskEnt-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ ρ (unmaskEnt E) ≡ unmaskEnt (renᵉ ρ E)
unmaskEnt-comm ρ abst       = refl
unmaskEnt-comm ρ (bind A)   = refl
unmaskEnt-comm ρ (masked E) = refl

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

masked-mono : E ⊑ᵉ E′ → masked E ⊑ᵉ masked E′
masked-mono = le-mm

-- Masking a slot only LOSES nameability, so a masked type context refines to the
-- unmasked one.  (There is no converse: that is the deleted demotion.)
masked-le : E ⊑ᵉ E′ → masked E ⊑ᵉ E′
masked-le le-aa       = le-mu le-aa nameable-a
masked-le le-ab       = le-mu le-ab nameable-b
masked-le le-bb       = le-mu le-bb nameable-b
masked-le (le-mm l)   = le-mm (masked-le l)
masked-le (le-mu l v) = le-mu (le-mu l v) v

unmaskEnt-nameable : E ⊑ᵉ E′ → Nameable E′ → E ⊑ᵉ unmaskEnt E′
unmaskEnt-nameable l nameable-a = l
unmaskEnt-nameable l nameable-b = l

unmaskEnt-mono : E ⊑ᵉ E′ → unmaskEnt E ⊑ᵉ unmaskEnt E′
unmaskEnt-mono le-aa       = le-aa
unmaskEnt-mono le-ab       = le-ab
unmaskEnt-mono le-bb       = le-bb
unmaskEnt-mono (le-mm l)   = l
unmaskEnt-mono (le-mu l v) = unmaskEnt-nameable l v

ren-mask : Ren ρ Δ Δ′ → Inj ρ → Ren ρ (mask X Δ) (mask (ρ X) Δ′)
ren-mask = ren-updateAt masked masked-comm

ren-unmask : Ren ρ Δ Δ′ → Inj ρ → Ren ρ (unmask X Δ) (unmask (ρ X) Δ′)
ren-unmask = ren-updateAt unmaskEnt unmaskEnt-comm

mask-⊑ : (Y : ℕ) → Δ ⊑ Δ′ → mask Y Δ ⊑ Δ′
mask-⊑ Y       le[]        = le[]
mask-⊑ zero    (le∷ l ls)  = le∷ (masked-le l) ls
mask-⊑ (suc Y) (le∷ l ls)  = le∷ l (mask-⊑ Y ls)

-- Unmasking only ADDS nameability, so the type context refines to its own
-- unmasking.  (The `masked` clause is `masked-le` at reflexivity: peeling one
-- `masked` is the ⊑ᵉ step `le-mu`.)
⊑ᵉ-unmaskEnt : (E : Ent) → E ⊑ᵉ unmaskEnt E
⊑ᵉ-unmaskEnt abst        = le-aa
⊑ᵉ-unmaskEnt (bind A)    = le-bb
⊑ᵉ-unmaskEnt (masked E)  = masked-le (⊑ᵉ-refl E)

unmask-⊑ : (Y : ℕ) (Δ : Ctxᵗ) → Δ ⊑ unmask Y Δ
unmask-⊑ Y       []      = le[]
unmask-⊑ zero    (E ∷ Δ) = le∷ (⊑ᵉ-unmaskEnt E) (⊑-refl Δ)
unmask-⊑ (suc Y) (E ∷ Δ) = le∷ (⊑ᵉ-refl E) (unmask-⊑ Y Δ)

-- The `_⊑ᵃ_` transport of a one-slot update.  Both `masked` and
-- `unmaskEnt` are monotone for it — and `unmaskEnt` is TOTAL here only
-- because `_⊑ᵃᵉ_` has no `le-mu` clause to think about.
masked-monoᵃ : E ⊑ᵃᵉ E′ → masked E ⊑ᵃᵉ masked E′
masked-monoᵃ = la-mm

unmaskEnt-monoᵃ : E ⊑ᵃᵉ E′ → unmaskEnt E ⊑ᵃᵉ unmaskEnt E′
unmaskEnt-monoᵃ la-aa     = la-aa
unmaskEnt-monoᵃ la-ab     = la-ab
unmaskEnt-monoᵃ la-bb     = la-bb
unmaskEnt-monoᵃ (la-mm l) = l

⊑ᵃ-updateAt : (f : Ent → Ent) → (∀ {E E′} → E ⊑ᵃᵉ E′ → f E ⊑ᵃᵉ f E′)
  → ∀ {X Δ Δ′} → Δ ⊑ᵃ Δ′ → updateAt f X Δ ⊑ᵃ updateAt f X Δ′
⊑ᵃ-updateAt f fm {zero}  (la∷ l ls) = la∷ (fm l) ls
⊑ᵃ-updateAt f fm {suc X} (la∷ l ls) = la∷ l (⊑ᵃ-updateAt f fm ls)
⊑ᵃ-updateAt f fm         la[]       = la[]

------------------------------------------------------------------------
-- 6b.  Locking and unlocking are EXACT INVERSES at a LOCKED slot
------------------------------------------------------------------------

-- Unmasking undoes masking, always: `masked` is injective.
unmask-mask : (X : ℕ) (Δ : Ctxᵗ) → unmask X (mask X Δ) ≡ Δ
unmask-mask X       []      = refl
unmask-mask zero    (E ∷ Δ) = refl
unmask-mask (suc X) (E ∷ Δ) = cong (E ∷_) (unmask-mask X Δ)

-- Masking undoes unmasking ONLY at a LOCKED slot — which is exactly what
-- `mw-u` (strong.Terms) demands of every `unlock`, and exactly why a
-- vacuous unlock had to be refused: at an already-nameable slot the
-- restoring `lock` of the dual would mask what the exterior left visible.
maskEnt-unmask : Locked E → masked (unmaskEnt E) ≡ E
maskEnt-unmask (locked v) = refl

mask-unmask : ∀ {Δ X} → Δ ∋lk X → mask X (unmask X Δ) ≡ Δ
mask-unmask (_ , ez     , lk) =
  cong (_∷ _) (maskEnt-unmask (Locked-ren⁻ lk))
mask-unmask (_ , es d   , lk) =
  cong (_ ∷_) (mask-unmask (_ , d , Locked-ren⁻ lk))

-- The two entry-level moves the dual performs, as lookup facts.
unmask-∋tv : ∀ {Δ X} → Δ ∋lk X → unmask X Δ ∋tv X
unmask-∋tv (E , d , locked v) =
  _ , updateAt-hit unmaskEnt unmaskEnt-comm d , v

mask-∋lk : ∀ {Δ X} → Δ ∋tv X → mask X Δ ∋lk X
mask-∋lk (E , d , v) =
  _ , updateAt-hit masked masked-comm d , locked v

------------------------------------------------------------------------
-- 7.  The bind prefix
------------------------------------------------------------------------

-- The `bind` entries of a boundary, pushed on as ordinary de Bruijn
-- binders.  The head of the list is interior slot 0; a rep is a type over
-- the PLAIN exterior, so it is lifted past the binders INSIDE it and past
-- nothing else (SIMULTANEITY: boundary entries never interfere).
pushBinds : List Ty → Ctxᵗ → Ctxᵗ
pushBinds []       Δ = Δ
pushBinds (A ∷ As) Δ = bind (shiftBy (length As) A) ∷ pushBinds As Δ

-- SIMULTANEITY, as a well-formedness fact: a type over the plain exterior
-- is a type inside the bind prefix, lifted past exactly the binders in
-- that prefix.
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
-- (strong.Reduction, `scopeOf`).
updateAt-pushBinds : (f : Ent → Ent) (As : List Ty) (X : ℕ) (Δ : Ctxᵗ)
  → updateAt f (length As + X) (pushBinds As Δ) ≡ pushBinds As (updateAt f X Δ)
updateAt-pushBinds f []       X Δ = refl
updateAt-pushBinds f (C ∷ As) X Δ =
  cong (bind (shiftBy (length As) C) ∷_) (updateAt-pushBinds f As X Δ)

-- A well-formed variable type IS a visible slot.
wf-var⁻ : Δ ⊢ᵗ ` X → Δ ∋tv X
wf-var⁻ (wf-var tv) = tv

⊑-pushBinds : (As : List Ty) → Δ ⊑ Δ′ → pushBinds As Δ ⊑ pushBinds As Δ′
⊑-pushBinds []       ls = ls
⊑-pushBinds (A ∷ As) ls = le∷ le-bb (⊑-pushBinds As ls)

⊑ᵃ-pushBinds : (As : List Ty) → Δ ⊑ᵃ Δ′ → pushBinds As Δ ⊑ᵃ pushBinds As Δ′
⊑ᵃ-pushBinds []       ls = ls
⊑ᵃ-pushBinds (A ∷ As) ls = la∷ la-bb (⊑ᵃ-pushBinds As ls)

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

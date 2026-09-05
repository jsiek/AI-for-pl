module strong.Ctx where

-- Strong System F — THE TYPE CONTEXT (type contexts) and its transports.
--
-- A type context entry is one of
--
--   abst    a Λ-bound variable — no representation, and none can be invented.
--   bind A   THE OWNER of an instantiation event.  A is the representation,
--           stored ONCE, as a type over this entry's bind tail.  Every inner
--           boundary that talks about this variable carries only its NAME.
--   blk E   the slot is CONCEALED here: it may not be NAMED (tightness), but
--           its entry E is RETAINED, so the knowledge is still on the type context
--           for a later re-exposure (`unlock`) to point back at.
--
-- Under Jeremy's Q1 ruling (OWNER-SYNTACTIC, 2026-09-05) a variable's
-- representation lives ONLY at its owner; every face and every licence
-- resolves the rep by LOOKING THE NAME UP along the enclosing type context.  There
-- is no store and no copy, so knowledge transport (`ren-kn`, `⊑-kn`) is
-- definitional and the old design's demotion is not expressible.
--
-- This module also carries the POSITIONAL machinery the boundary needs:
-- injective renamings (`Inj`), one-slot entry update (`upd`/`mask`/`unmask`)
-- with its transports, and the owner prefix `prep` (with `liftN`).

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
-- 1.  The type context:  type contexts with OWNER entries and BLOCKED entries
------------------------------------------------------------------------

data Ent : Set where
  abst : Ent
  bind  : Ty → Ent
  blk  : Ent → Ent

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ Δ′ Δ″ : Ctxᵗ
    E E′ F : Ent
    A A′ B B′ C : Ty
    X Y Z : ℕ
    ρ ρ′ : Renameᵗ

renᵉ : Renameᵗ → Ent → Ent
renᵉ ρ abst    = abst
renᵉ ρ (bind A) = bind (renameᵗ ρ A)
renᵉ ρ (blk E) = blk (renᵉ ρ E)

⇑ᵉ : Ent → Ent
⇑ᵉ = renᵉ suc

renᵉ-⇑-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ (extᵗ ρ) (⇑ᵉ E) ≡ ⇑ᵉ (renᵉ ρ E)
renᵉ-⇑-comm ρ abst    = refl
renᵉ-⇑-comm ρ (bind A) = cong bind (ren-⇑-comm ρ A)
renᵉ-⇑-comm ρ (blk E) = cong blk (renᵉ-⇑-comm ρ E)

-- Entry lookup.  The entry is returned SHIFTED into the ambient context, so
-- `Δ ∋e X , bind A` means "slot X is an owner whose rep, read in Δ, is A".
-- One relation serves every purpose: knowledge, visibility, and blocking.
infix 4 _∋e_,_
data _∋e_,_ : Ctxᵗ → ℕ → Ent → Set where
  ez : (E ∷ Δ) ∋e zero , ⇑ᵉ E
  es : Δ ∋e X , E → (F ∷ Δ) ∋e suc X , ⇑ᵉ E

-- A slot may be NAMED iff its entry is not blocked.  This is the whole of
-- the tightness discipline: `blk` is invisible to types and to terms.
data Vis : Ent → Set where
  vis-a : Vis abst
  vis-o : Vis (bind A)

renᵉ-Vis : Vis E → Vis (renᵉ ρ E)
renᵉ-Vis vis-a = vis-a
renᵉ-Vis vis-o = vis-o

infix 4 _∋tv_
_∋tv_ : Ctxᵗ → ℕ → Set
Δ ∋tv X = ∃[ E ] ((Δ ∋e X , E) × Vis E)

-- OWNER-SYNTACTIC LOOKUP.  This is the only way any rep is ever read.
infix 4 _∋_:=_
_∋_:=_ : Ctxᵗ → ℕ → Ty → Set
Δ ∋ X := A = Δ ∋e X , bind A

∋:=→∋tv : Δ ∋ X := A → Δ ∋tv X
∋:=→∋tv d = bind _ , d , vis-o

-- Lookup is a partial FUNCTION, which is what makes every rule that mints an
-- identity face at a looked-up rep deterministic.
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
-- DEFINITIONAL — which is the whole bet of the ownership design: a name is
-- moved by ρ, a spelling would have had to be re-derived.
record Ren (ρ : Renameᵗ) (Δ Δ′ : Ctxᵗ) : Set where
  constructor mkRen
  field ren∋ : ∀ {X E} → Δ ∋e X , E → Δ′ ∋e ρ X , renᵉ ρ E

open Ren public

ren-kn : Ren ρ Δ Δ′ → Δ ∋ X := A → Δ′ ∋ ρ X := renameᵗ ρ A
ren-kn r d = ren∋ r d

ren-tv : Ren ρ Δ Δ′ → Δ ∋tv X → Δ′ ∋tv ρ X
ren-tv r (E , d , v) = renᵉ _ E , ren∋ r d , renᵉ-Vis v

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

-- E ⊑ᵉ E′ : E′ knows at least what E knows.
--   le-ao : a Λ-bound slot may become an owner              (TyBeta)
--   le-bu : a concealed slot may be re-exposed              (Cancel)
--   le-bb : concealment is monotone in what it hides
-- There is NO clause in the other direction: an owner never loses its rep.
data _⊑ᵉ_ : Ent → Ent → Set where
  le-aa : abst ⊑ᵉ abst
  le-ao : abst ⊑ᵉ bind A
  le-oo : bind A ⊑ᵉ bind A
  le-bb : E ⊑ᵉ E′ → blk E ⊑ᵉ blk E′
  le-bu : E ⊑ᵉ E′ → Vis E′ → blk E ⊑ᵉ E′

infix 4 _⊑_
data _⊑_ : Ctxᵗ → Ctxᵗ → Set where
  le[] : [] ⊑ []
  le∷  : E ⊑ᵉ E′ → Δ ⊑ Δ′ → (E ∷ Δ) ⊑ (E′ ∷ Δ′)

⊑ᵉ-refl : (E : Ent) → E ⊑ᵉ E
⊑ᵉ-refl abst    = le-aa
⊑ᵉ-refl (bind A) = le-oo
⊑ᵉ-refl (blk E) = le-bb (⊑ᵉ-refl E)

⊑-refl : (Δ : Ctxᵗ) → Δ ⊑ Δ
⊑-refl []      = le[]
⊑-refl (E ∷ Δ) = le∷ (⊑ᵉ-refl E) (⊑-refl Δ)

⊑ᵉ-⇑ : E ⊑ᵉ E′ → ⇑ᵉ E ⊑ᵉ ⇑ᵉ E′
⊑ᵉ-⇑ le-aa        = le-aa
⊑ᵉ-⇑ le-ao        = le-ao
⊑ᵉ-⇑ le-oo        = le-oo
⊑ᵉ-⇑ (le-bb l)    = le-bb (⊑ᵉ-⇑ l)
⊑ᵉ-⇑ (le-bu l v)  = le-bu (⊑ᵉ-⇑ l) (renᵉ-Vis v)

⊑-∋e : Δ ⊑ Δ′ → Δ ∋e X , E → ∃[ E′ ] ((Δ′ ∋e X , E′) × E ⊑ᵉ E′)
⊑-∋e (le∷ l ls) ez     = _ , ez , ⊑ᵉ-⇑ l
⊑-∋e (le∷ l ls) (es d) with ⊑-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵉ-⇑ l′

vis-mono : E ⊑ᵉ E′ → Vis E → Vis E′
vis-mono le-aa        vis-a = vis-a
vis-mono le-ao        vis-a = vis-o
vis-mono le-oo        vis-o = vis-o
vis-mono (le-bb _)    ()
vis-mono (le-bu _ _)  ()

⊑-tv : Δ ⊑ Δ′ → Δ ∋tv X → Δ′ ∋tv X
⊑-tv ls (E , d , v) with ⊑-∋e ls d
... | E′ , d′ , l′ = E′ , d′ , vis-mono l′ v

-- An owner is never lost and never re-spelled: the ONLY ⊑ᵉ clause whose
-- source is `bind A` is `le-oo`.  This is the deleted demotion, as a theorem.
⊑-kn : Δ ⊑ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A
⊑-kn ls d with ⊑-∋e ls d
... | bind A , d′ , le-oo = d′

⊑-wf : Δ ⊑ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
⊑-wf ls (wf-var tv)  = wf-var (⊑-tv ls tv)
⊑-wf ls wf-ℕ         = wf-ℕ
⊑-wf ls wf-𝔹         = wf-𝔹
⊑-wf ls (wf-⇒ wA wB) = wf-⇒ (⊑-wf ls wA) (⊑-wf ls wB)
⊑-wf ls (wf-∀ wA)    = wf-∀ (⊑-wf (le∷ le-aa ls) wA)

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

liftN : ℕ → Ty → Ty
liftN zero    A = A
liftN (suc n) A = ⇑ᵗ (liftN n A)

liftN-ren : (n : ℕ) (ρ : Renameᵗ) (A : Ty)
  → renameᵗ (extN n ρ) (liftN n A) ≡ liftN n (renameᵗ ρ A)
liftN-ren zero    ρ A = refl
liftN-ren (suc n) ρ A =
  trans (ren-⇑-comm (extN n ρ) (liftN n A))
        (cong ⇑ᵗ (liftN-ren n ρ A))

liftN-base : (n : ℕ) → Base A → liftN n A ≡ A
liftN-base zero    b = refl
liftN-base (suc n) b rewrite liftN-base n b = base-ren b

liftN-var : (n Y : ℕ) → liftN n (` Y) ≡ ` (n + Y)
liftN-var zero    Y = refl
liftN-var (suc n) Y rewrite liftN-var n Y = refl

tvar-inj : _≡_ {A = Ty} (` X) (` Y) → X ≡ Y
tvar-inj refl = refl

-- A base type is never a variable, at any lifting.
base≢var : (n : ℕ) → Base A → liftN n A ≡ ` X → ⊥
base≢var n base-ℕ eq with trans (sym (liftN-base n base-ℕ)) eq
... | ()
base≢var n base-𝔹 eq with trans (sym (liftN-base n base-𝔹)) eq
... | ()

------------------------------------------------------------------------
-- 6.  Masking a slot in place  (the conceal/alias mechanism)
------------------------------------------------------------------------

-- One entry update at one slot.  `mask = upd blk`, `unmask = upd unblk`.
upd : (Ent → Ent) → ℕ → Ctxᵗ → Ctxᵗ
upd f X       []      = []
upd f zero    (E ∷ Δ) = f E ∷ Δ
upd f (suc X) (E ∷ Δ) = E ∷ upd f X Δ

unblk : Ent → Ent
unblk abst    = abst
unblk (bind A) = bind A
unblk (blk E) = E

mask unmask : ℕ → Ctxᵗ → Ctxᵗ
mask   = upd blk
unmask = upd unblk

-- Both update functions commute with renaming — they touch no spelling.
blk-comm : (ρ : Renameᵗ) (E : Ent) → renᵉ ρ (blk E) ≡ blk (renᵉ ρ E)
blk-comm ρ E = refl

unblk-comm : (ρ : Renameᵗ) (E : Ent) → renᵉ ρ (unblk E) ≡ unblk (renᵉ ρ E)
unblk-comm ρ abst    = refl
unblk-comm ρ (bind A) = refl
unblk-comm ρ (blk E) = refl

_≟ℕ_ : (X Y : ℕ) → Dec (X ≡ Y)
zero  ≟ℕ zero  = yes refl
zero  ≟ℕ suc Y = no (λ ())
suc X ≟ℕ zero  = no (λ ())
suc X ≟ℕ suc Y with X ≟ℕ Y
... | yes refl = yes refl
... | no ne    = no (λ eq → ne (suc-injective eq))

module _ (f : Ent → Ent)
         (fc : ∀ ρ E → renᵉ ρ (f E) ≡ f (renᵉ ρ E)) where

  upd-hit : ∀ {Δ X E} → Δ ∋e X , E → upd f X Δ ∋e X , f E
  upd-hit (ez {E = E₁})   rewrite sym (fc suc E₁) = ez
  upd-hit (es {E = E₀} d) rewrite sym (fc suc E₀) = es (upd-hit d)

  upd-hit⁻ : ∀ {Δ X E} → upd f X Δ ∋e X , E
           → ∃[ E₀ ] ((Δ ∋e X , E₀) × (E ≡ f E₀))
  upd-hit⁻ {E₁ ∷ Δ} {zero}  ez     = _ , ez , fc suc E₁
  upd-hit⁻ {E₁ ∷ Δ} {suc X} (es d) with upd-hit⁻ d
  ... | E₀ , d₀ , eq = _ , es d₀ , trans (cong ⇑ᵉ eq) (fc suc E₀)

  upd-miss : ∀ {Δ X Y E} → X ≢ Y → Δ ∋e Y , E → upd f X Δ ∋e Y , E
  upd-miss {X = zero}  ne ez     = ⊥-elim (ne refl)
  upd-miss {X = suc X} ne ez     = ez
  upd-miss {X = zero}  ne (es d) = es d
  upd-miss {X = suc X} ne (es d) = es (upd-miss (λ eq → ne (cong suc eq)) d)

  upd-miss⁻ : ∀ {Δ X Y E} → X ≢ Y → upd f X Δ ∋e Y , E → Δ ∋e Y , E
  upd-miss⁻ {Δ = E₁ ∷ Δ} {zero}  ne ez     = ⊥-elim (ne refl)
  upd-miss⁻ {Δ = E₁ ∷ Δ} {suc X} ne ez     = ez
  upd-miss⁻ {Δ = E₁ ∷ Δ} {zero}  ne (es d) = es d
  upd-miss⁻ {Δ = E₁ ∷ Δ} {suc X} ne (es d) =
    es (upd-miss⁻ (λ eq → ne (cong suc eq)) d)

  -- TRANSPORT of one mask/unmask across a type context renaming.
  ren-upd : ∀ {Δ Δ′ ρ X} → Ren ρ Δ Δ′ → Inj ρ
          → Ren ρ (upd f X Δ) (upd f (ρ X) Δ′)
  ren-upd {ρ = ρ} {X = X} r i = mkRen go
    where
    go : ∀ {Y E} → upd f X _ ∋e Y , E → upd f (ρ X) _ ∋e ρ Y , renᵉ ρ E
    go {Y} d with X ≟ℕ Y
    ... | yes refl with upd-hit⁻ d
    ...   | E₀ , d₀ , refl =
            subst (λ e → upd f (ρ X) _ ∋e ρ X , e) (sym (fc ρ E₀))
                  (upd-hit (ren∋ r d₀))
    go {Y} d | no ne =
      upd-miss (λ eq → ne (i eq)) (ren∋ r (upd-miss⁻ ne d))

  -- TRANSPORT of one mask/unmask across knowledge refinement.
  ⊑-upd : ∀ {X Δ Δ′} → (∀ {E E′} → E ⊑ᵉ E′ → f E ⊑ᵉ f E′)
        → Δ ⊑ Δ′ → upd f X Δ ⊑ upd f X Δ′
  ⊑-upd {zero}  fm (le∷ l ls) = le∷ (fm l) ls
  ⊑-upd {suc X} fm (le∷ l ls) = le∷ l (⊑-upd fm ls)
  ⊑-upd         fm le[]       = le[]

blk-mono : E ⊑ᵉ E′ → blk E ⊑ᵉ blk E′
blk-mono = le-bb

-- Masking a slot only LOSES nameability, so a masked type context refines to the
-- unmasked one.  (There is no converse: that is the deleted demotion.)
blk-le : E ⊑ᵉ E′ → blk E ⊑ᵉ E′
blk-le le-aa       = le-bu le-aa vis-a
blk-le le-ao       = le-bu le-ao vis-o
blk-le le-oo       = le-bu le-oo vis-o
blk-le (le-bb l)   = le-bb (blk-le l)
blk-le (le-bu l v) = le-bu (le-bu l v) v

unblk-vis : E ⊑ᵉ E′ → Vis E′ → E ⊑ᵉ unblk E′
unblk-vis l vis-a = l
unblk-vis l vis-o = l

unblk-mono : E ⊑ᵉ E′ → unblk E ⊑ᵉ unblk E′
unblk-mono le-aa       = le-aa
unblk-mono le-ao       = le-ao
unblk-mono le-oo       = le-oo
unblk-mono (le-bb l)   = l
unblk-mono (le-bu l v) = unblk-vis l v

ren-mask : Ren ρ Δ Δ′ → Inj ρ → Ren ρ (mask X Δ) (mask (ρ X) Δ′)
ren-mask = ren-upd blk blk-comm

ren-unmask : Ren ρ Δ Δ′ → Inj ρ → Ren ρ (unmask X Δ) (unmask (ρ X) Δ′)
ren-unmask = ren-upd unblk unblk-comm

mask-⊑ : (Y : ℕ) → Δ ⊑ Δ′ → mask Y Δ ⊑ Δ′
mask-⊑ Y       le[]        = le[]
mask-⊑ zero    (le∷ l ls)  = le∷ (blk-le l) ls
mask-⊑ (suc Y) (le∷ l ls)  = le∷ l (mask-⊑ Y ls)

------------------------------------------------------------------------
-- 7.  The owner prefix
------------------------------------------------------------------------

-- The owners of a boundary, pushed on as ordinary de Bruijn binders.  The
-- head of the list is interior slot 0; a rep is a type over the PLAIN
-- exterior, so it is lifted past the owners bound INSIDE it and past nothing
-- else (SIMULTANEITY: boundary entries never interfere).
prep : List Ty → Ctxᵗ → Ctxᵗ
prep []       Δ = Δ
prep (A ∷ As) Δ = bind (liftN (length As) A) ∷ prep As Δ

⊑-prep : (As : List Ty) → Δ ⊑ Δ′ → prep As Δ ⊑ prep As Δ′
⊑-prep []       ls = ls
⊑-prep (A ∷ As) ls = le∷ le-oo (⊑-prep As ls)

ren-prep : (As : List Ty) (ρ : Renameᵗ) → Ren ρ Δ Δ′
         → Ren (extN (length As) ρ) (prep As Δ) (prep (map (renameᵗ ρ) As) Δ′)
ren-prep []       ρ r = r
ren-prep (A ∷ As) ρ r
  rewrite map-length (renameᵗ ρ) As
        | sym (liftN-ren (length As) ρ A) =
  ren-ext (ren-prep As ρ r)

Inj-prep : (As : List Ty) → Inj ρ → Inj (extN (length As) ρ)
Inj-prep As i = Inj-extN (length As) i

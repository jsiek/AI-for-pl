module strong.notes.probes.ConvBoundaryTerms where

-- THE CONVERSION-BOUNDARY REDESIGN PROBE — part 2: the BOUNDARY and TERMS.
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : List BEnt   the SCOPE SKELETON, rep-free except for owners
--        own A   BINDS a fresh interior slot; A is its representation, read
--                in the PLAIN EXTERIOR (simultaneity: never through Θ's other
--                entries).  The only rep-carrying form; born once, bound once.
--        cnc X   MASKS exterior slot X: the interior may not NAME it.  The
--                entry is retained on the spine — nothing is dropped, nothing
--                is re-spelled, so there is no demotion to perform.
--        ali X   UNMASKS exterior slot X; well formed only under a mask.
--                Name only: it claims nothing, it merely restores nameability.
--   c : Conv       the FACE, a GTSF conversion checked on the FACE SPINE
--                  (the interior spine with Θ's masks lifted).
--
-- Frames change ONLY at binders: `intC Θ Δ` is `Δ` with the masks applied and
-- Θ's owners pushed on.  There is no `dropN`, no `cmax`, no `swapᵇ`.
--
-- Q1 is answered at the foot of this file: `⊢rename` and `⊢retag`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.TypeSubst
  using (rename-cong; rename-rename-commute; rename-[]ᵗ-commute)
open import strong.notes.probes.ConvBoundaryCore

------------------------------------------------------------------------
-- 1.  Injective renamings, iterated extension, iterated lifting
------------------------------------------------------------------------

private
  variable
    Δ Δ′ : Ctxᵗ
    E E′ : Ent
    A A′ B B′ : Ty
    X Y : ℕ
    ρ : Renameᵗ
    p : Pol

-- The ONE hypothesis the transport needs beyond `Ren`: ρ must not confuse two
-- slots, since masking is positional.  Every use site is `suc` or an `extᵗ`
-- of an injective renaming, so it is discharged structurally (`Inj-suc`,
-- `Inj-ext`, `Inj-extN` below).  This is the mini-core's SkelX analogue, and
-- it mentions no representation at all.
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

------------------------------------------------------------------------
-- 2.  Masking a slot in place  (the conceal/alias mechanism)
------------------------------------------------------------------------

-- One entry update at one slot.  `mask = upd blk`, `unmask = upd unblk`.
upd : (Ent → Ent) → ℕ → Ctxᵗ → Ctxᵗ
upd f X       []      = []
upd f zero    (E ∷ Δ) = f E ∷ Δ
upd f (suc X) (E ∷ Δ) = E ∷ upd f X Δ

unblk : Ent → Ent
unblk abst    = abst
unblk (own A) = own A
unblk (blk E) = E

mask unmask : ℕ → Ctxᵗ → Ctxᵗ
mask   = upd blk
unmask = upd unblk

-- Both update functions commute with renaming — they touch no spelling.
blk-comm : (ρ : Renameᵗ) (E : Ent) → renᵉ ρ (blk E) ≡ blk (renᵉ ρ E)
blk-comm ρ E = refl

unblk-comm : (ρ : Renameᵗ) (E : Ent) → renᵉ ρ (unblk E) ≡ unblk (renᵉ ρ E)
unblk-comm ρ abst    = refl
unblk-comm ρ (own A) = refl
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

  -- TRANSPORT of one mask/unmask across a spine renaming.
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

-- Masking a slot only LOSES nameability, so a masked spine refines to the
-- unmasked one.  (There is no converse: that is the deleted demotion.)
blk-le : E ⊑ᵉ E′ → blk E ⊑ᵉ E′
blk-le le-aa       = le-bu le-aa vis-a
blk-le le-ao       = le-bu le-ao vis-o
blk-le le-oo       = le-bu le-oo vis-o
blk-le (le-bb l)   = le-bb (blk-le l)
blk-le (le-bu l v) = le-bu (le-bu l v) v

unblk-mono : E ⊑ᵉ E′ → unblk E ⊑ᵉ unblk E′
unblk-mono le-aa       = le-aa
unblk-mono le-ao       = le-ao
unblk-mono le-oo       = le-oo
unblk-mono (le-bb l)   = l
unblk-mono (le-bu l v) = unblk-vis l v
  where
  unblk-vis : ∀ {E E′} → E ⊑ᵉ E′ → Vis E′ → E ⊑ᵉ unblk E′
  unblk-vis l vis-a = l
  unblk-vis l vis-o = l

------------------------------------------------------------------------
-- 3.  The boundary skeleton
------------------------------------------------------------------------

data BEnt : Set where
  own : Ty → BEnt      -- BINDS a fresh slot at rep A (A over the exterior)
  ali : ℕ → BEnt       -- unmask exterior slot X   (name only)
  cnc : ℕ → BEnt       -- mask   exterior slot X   (name only)

BCtx : Set
BCtx = List BEnt

reps : BCtx → List Ty
reps []            = []
reps (own A ∷ Θ)   = A ∷ reps Θ
reps (ali X ∷ Θ)   = reps Θ
reps (cnc X ∷ Θ)   = reps Θ

-- `nrev` is the boundary's FRAME EXTENSION: the number of binders it adds.
-- It is the only surviving list arithmetic (the old `revs`); `cmax`/`dropN`
-- have no analogue, because conceal masks in place.
nrev : BCtx → ℕ
nrev Θ = length (reps Θ)

-- The owners, pushed on as ordinary de Bruijn binders.  Head of `reps` is
-- interior slot 0; a rep is a type over the PLAIN exterior, so it is lifted
-- past the owners bound INSIDE it and past nothing else (simultaneity).
prep : List Ty → Ctxᵗ → Ctxᵗ
prep []       Δ = Δ
prep (A ∷ As) Δ = own (liftN (length As) A) ∷ prep As Δ

-- The masks (`cnc`) and unmasks (`ali`), applied in place.
scp : BCtx → Ctxᵗ → Ctxᵗ
scp []          Δ = Δ
scp (own A ∷ Θ) Δ = scp Θ Δ
scp (ali X ∷ Θ) Δ = unmask X (scp Θ Δ)
scp (cnc X ∷ Θ) Δ = mask X (scp Θ Δ)

-- The FACE spine: like `scp` but WITHOUT the conceal masks, so a `csl X`
-- can resolve X at its owner.  This is owner-syntactic lookup: the licence
-- is read on the spine that encloses the boundary, never inside it.
fscp : BCtx → Ctxᵗ → Ctxᵗ
fscp []          Δ = Δ
fscp (own A ∷ Θ) Δ = fscp Θ Δ
fscp (ali X ∷ Θ) Δ = unmask X (fscp Θ Δ)
fscp (cnc X ∷ Θ) Δ = fscp Θ Δ

-- What replaces `intOf`: the same slot list, the interior mask, and the
-- owner extension.  Nothing is dropped and no rep is recomputed.
intC : BCtx → Ctxᵗ → Ctxᵗ
intC Θ Δ = prep (reps Θ) (scp Θ Δ)

fceC : BCtx → Ctxᵗ → Ctxᵗ
fceC Θ Δ = prep (reps Θ) (fscp Θ Δ)

-- The interior spine is the face spine with Θ's own masks on, so anything
-- well formed inside is well formed on the face spine.
scp⊑fscp : (Θ : BCtx) (Δ : Ctxᵗ) → scp Θ Δ ⊑ fscp Θ Δ
scp⊑fscp []          Δ = ⊑-refl Δ
scp⊑fscp (own A ∷ Θ) Δ = scp⊑fscp Θ Δ
scp⊑fscp (ali X ∷ Θ) Δ = ⊑-upd unblk unblk-comm unblk-mono (scp⊑fscp Θ Δ)
scp⊑fscp (cnc X ∷ Θ) Δ = mask⊑ (scp⊑fscp Θ Δ)
  where
  mask⊑ : ∀ {Δ₁ Δ₂} → Δ₁ ⊑ Δ₂ → mask X Δ₁ ⊑ Δ₂
  mask⊑ {Δ₁} {Δ₂} l = go X l
    where
    go : ∀ {Δ₁ Δ₂} (Y : ℕ) → Δ₁ ⊑ Δ₂ → mask Y Δ₁ ⊑ Δ₂
    go Y       le[]        = le[]
    go zero    (le∷ l ls)  = le∷ (blk-le l) ls
    go (suc Y) (le∷ l ls)  = le∷ l (go Y ls)

⊑-prep : (As : List Ty) → Δ ⊑ Δ′ → prep As Δ ⊑ prep As Δ′
⊑-prep []       ls = ls
⊑-prep (A ∷ As) ls = le∷ le-oo (⊑-prep As ls)

intC⊑fceC : (Θ : BCtx) (Δ : Ctxᵗ) → intC Θ Δ ⊑ fceC Θ Δ
intC⊑fceC Θ Δ = ⊑-prep (reps Θ) (scp⊑fscp Θ Δ)

------------------------------------------------------------------------
-- 4.  Boundary well-formedness
------------------------------------------------------------------------

-- Every premise names a slot or checks a rep in the PLAIN exterior.  There
-- is no `Reversal≈`, no `starOnly`, no `SkelEq`, no x-lookup: an `ali`
-- claims nothing at all, and a `cnc` claims nothing either — the claim lives
-- in the FACE (`csl X`, which must cite a live owner).
-- An `ali X` premise asks only that the slot EXISTS.  It cannot ask that the
-- slot be masked and stay stable under refinement (a `Cancel` may already
-- have un-masked it), and it need not: `unmask` is total and an alias at an
-- un-masked slot is a no-op.  Note the distinction the mask discipline
-- forces: `ali X`/`cnc X` NAME a masked index — that is an ENTRY, not a type
-- — while `Δ ⊢ᵗ ` X` at a masked slot is refused.  Tightness is about USE in
-- a type, not about mentioning the index in the skeleton.
data Bwf (Δ : Ctxᵗ) : BCtx → Set where
  bw[] : Bwf Δ []
  bw-o : ∀ {A Θ} → Δ ⊢ᵗ A → Bwf Δ Θ → Bwf Δ (own A ∷ Θ)
  bw-c : ∀ {X Θ} → Δ ∋tv X → Bwf Δ Θ → Bwf Δ (cnc X ∷ Θ)
  bw-a : ∀ {X E Θ} → Δ ∋e X , E → Bwf Δ Θ → Bwf Δ (ali X ∷ Θ)

------------------------------------------------------------------------
-- 5.  Terms
------------------------------------------------------------------------

infix  9 `_
infix  9 $_
infixl 7 _·_
infix  6 ƛ_∙_
infix  5 _⟪_,_⟫

data Term : Set where
  `_      : ℕ → Term
  $_      : ℕ → Term
  ƛ_∙_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _·[_,_] : Term → Ty → Ty → Term
  _⟪_,_⟫  : Term → BCtx → Conv → Term

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  here  : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  there : ∀ {Γ x A B} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

infix 3 _∣_⊢_⦂_
data _∣_⊢_⦂_ : Ctxᵗ → Ctx → Term → Ty → Set where

  ⊢` : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Δ Γ n} → Δ ∣ Γ ⊢ $ n ⦂ `ℕ

  ⊢ƛ : ∀ {Δ Γ A B N} → Δ ⊢ᵗ A → Δ ∣ A ∷ Γ ⊢ N ⦂ B
     → Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Δ Γ A B L M} → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γ ⊢ M ⦂ A
     → Δ ∣ Γ ⊢ L · M ⦂ B

  ⊢Λ : ∀ {Δ Γ C N} → (abst ∷ Δ) ∣ ⤊ Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  ⊢·[] : ∀ {Δ Γ A B L} → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
       → Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  -- (env).  ONE frame change.  The interior is term-closed and typed on the
  -- interior spine; the face conversion is checked on the FACE spine, where
  -- the boundary's owners and the slots it masks are both live; the exterior
  -- face is a type over the plain exterior.  R3 is closed: both faces are on
  -- the wrapper.
  env : ∀ {Δ Γ Θ c M Bᵢ Bₑ p}
      → Bwf Δ Θ
      → intC Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
      → fceC Θ Δ ⊢ c ∶ Bᵢ ⇝ liftN (nrev Θ) Bₑ ∙ p
      → Δ ⊢ᵗ Bₑ
        --------------------------------------------
      → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

------------------------------------------------------------------------
-- 6.  Renaming of terms and boundaries
------------------------------------------------------------------------

renᴮ : Renameᵗ → BCtx → BCtx
renᴮ ρ []            = []
renᴮ ρ (own A ∷ Θ)   = own (renameᵗ ρ A) ∷ renᴮ ρ Θ
renᴮ ρ (ali X ∷ Θ)   = ali (ρ X) ∷ renᴮ ρ Θ
renᴮ ρ (cnc X ∷ Θ)   = cnc (ρ X) ∷ renᴮ ρ Θ

reps-ren : (ρ : Renameᵗ) (Θ : BCtx)
  → reps (renᴮ ρ Θ) ≡ map (renameᵗ ρ) (reps Θ)
reps-ren ρ []          = refl
reps-ren ρ (own A ∷ Θ) = cong (renameᵗ ρ A ∷_) (reps-ren ρ Θ)
reps-ren ρ (ali X ∷ Θ) = reps-ren ρ Θ
reps-ren ρ (cnc X ∷ Θ) = reps-ren ρ Θ

map-length : ∀ {a} {S T : Set a} (f : S → T) (xs : List S)
           → length (map f xs) ≡ length xs
map-length f []       = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

nrev-ren : (ρ : Renameᵗ) (Θ : BCtx) → nrev (renᴮ ρ Θ) ≡ nrev Θ
nrev-ren ρ Θ =
  trans (cong length (reps-ren ρ Θ)) (map-length (renameᵗ ρ) (reps Θ))

renᴹ : Renameᵗ → Term → Term
renᴹ ρ (` x)          = ` x
renᴹ ρ ($ n)          = $ n
renᴹ ρ (ƛ A ∙ N)      = ƛ renameᵗ ρ A ∙ renᴹ ρ N
renᴹ ρ (L · M)        = renᴹ ρ L · renᴹ ρ M
renᴹ ρ (Λ N)          = Λ (renᴹ (extᵗ ρ) N)
renᴹ ρ (L ·[ B , A ]) = renᴹ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renᴹ ρ (M ⟪ Θ , c ⟫)  =
  renᴹ (extN (nrev Θ) ρ) M ⟪ renᴮ ρ Θ , renᶜ (extN (nrev Θ) ρ) c ⟫

------------------------------------------------------------------------
-- 7.  The spine operations transport (Q1, the structural half)
------------------------------------------------------------------------

ren-mask : ∀ {X} → Ren ρ Δ Δ′ → Inj ρ → Ren ρ (mask X Δ) (mask (ρ X) Δ′)
ren-mask = ren-upd blk blk-comm

ren-unmask : ∀ {X} → Ren ρ Δ Δ′ → Inj ρ → Ren ρ (unmask X Δ) (unmask (ρ X) Δ′)
ren-unmask = ren-upd unblk unblk-comm

ren-scp : (Θ : BCtx) → Ren ρ Δ Δ′ → Inj ρ
        → Ren ρ (scp Θ Δ) (scp (renᴮ ρ Θ) Δ′)
ren-scp []          r i = r
ren-scp (own A ∷ Θ) r i = ren-scp Θ r i
ren-scp (ali X ∷ Θ) r i = ren-unmask (ren-scp Θ r i) i
ren-scp (cnc X ∷ Θ) r i = ren-mask (ren-scp Θ r i) i

ren-fscp : (Θ : BCtx) → Ren ρ Δ Δ′ → Inj ρ
         → Ren ρ (fscp Θ Δ) (fscp (renᴮ ρ Θ) Δ′)
ren-fscp []          r i = r
ren-fscp (own A ∷ Θ) r i = ren-fscp Θ r i
ren-fscp (ali X ∷ Θ) r i = ren-unmask (ren-fscp Θ r i) i
ren-fscp (cnc X ∷ Θ) r i = ren-fscp Θ r i

ren-prep : (As : List Ty) (ρ : Renameᵗ) → Ren ρ Δ Δ′
         → Ren (extN (length As) ρ) (prep As Δ) (prep (map (renameᵗ ρ) As) Δ′)
ren-prep []       ρ r = r
ren-prep (A ∷ As) ρ r
  rewrite map-length (renameᵗ ρ) As
        | sym (liftN-ren (length As) ρ A) =
  ren-ext (ren-prep As ρ r)

Inj-prep : (As : List Ty) → Inj ρ → Inj (extN (length As) ρ)
Inj-prep As i = Inj-extN (length As) i

------------------------------------------------------------------------
-- 8.  Q1a — THE RENAMING TRANSPORT  (the ⊢renameᵀ analogue)
------------------------------------------------------------------------

ren-intC : (Θ : BCtx) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (nrev Θ) ρ) (intC Θ Δ) (intC (renᴮ ρ Θ) Δ′)
ren-intC Θ ρ r i rewrite reps-ren ρ Θ = ren-prep (reps Θ) ρ (ren-scp Θ r i)

ren-fceC : (Θ : BCtx) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (nrev Θ) ρ) (fceC Θ Δ) (fceC (renᴮ ρ Θ) Δ′)
ren-fceC Θ ρ r i rewrite reps-ren ρ Θ = ren-prep (reps Θ) ρ (ren-fscp Θ r i)

Bwf-ren : ∀ {Θ} → Ren ρ Δ Δ′ → Inj ρ → Bwf Δ Θ → Bwf Δ′ (renᴮ ρ Θ)
Bwf-ren r i bw[]         = bw[]
Bwf-ren r i (bw-o w b)   = bw-o (wf-ren r w) (Bwf-ren r i b)
Bwf-ren r i (bw-c tv b)  = bw-c (ren-tv r tv) (Bwf-ren r i b)
Bwf-ren r i (bw-a d b)   = bw-a (ren∋ r d) (Bwf-ren r i b)

renΓ : Renameᵗ → Ctx → Ctx
renΓ ρ Γ = map (renameᵗ ρ) Γ

∋⦂-ren : ∀ {Γ x A} (ρ : Renameᵗ) → Γ ∋ x ⦂ A → renΓ ρ Γ ∋ x ⦂ renameᵗ ρ A
∋⦂-ren ρ here      = here
∋⦂-ren ρ (there d) = there (∋⦂-ren ρ d)

⤊-ren : (ρ : Renameᵗ) (Γ : Ctx) → ⤊ (renΓ ρ Γ) ≡ renΓ (extᵗ ρ) (⤊ Γ)
⤊-ren ρ []      = refl
⤊-ren ρ (A ∷ Γ) = cong₂ _∷_ (sym (ren-⇑-comm ρ A)) (⤊-ren ρ Γ)

-- THE THEOREM (Q1a).  A spine renaming moves a whole typing derivation, with
-- the ONE hypothesis `Inj ρ`.  No hypothesis mentions a representation.
⊢rename : ∀ {Δ Δ′ Γ M A ρ}
  → Ren ρ Δ Δ′ → Inj ρ
  → Δ  ∣ Γ ⊢ M ⦂ A
    ------------------------------------------------
  → Δ′ ∣ renΓ ρ Γ ⊢ renᴹ ρ M ⦂ renameᵗ ρ A
⊢rename {ρ = ρ} r i (⊢` d)      = ⊢` (∋⦂-ren ρ d)
⊢rename r i ⊢$                  = ⊢$
⊢rename r i (⊢ƛ w ⊢N)           = ⊢ƛ (wf-ren r w) (⊢rename r i ⊢N)
⊢rename r i (⊢· ⊢L ⊢M)          = ⊢· (⊢rename r i ⊢L) (⊢rename r i ⊢M)
⊢rename {Γ = Γ} {ρ = ρ} r i (⊢Λ ⊢N) =
  ⊢Λ (subst (λ Γ′ → _ ∣ Γ′ ⊢ _ ⦂ _) (sym (⤊-ren ρ Γ))
            (⊢rename (ren-ext r) (Inj-ext i) ⊢N))
⊢rename {ρ = ρ} r i (⊢·[] {A = A} {B = B} ⊢L w)
  rewrite rename-[]ᵗ-commute ρ B A =
  ⊢·[] (⊢rename r i ⊢L) (wf-ren r w)
⊢rename {Δ′ = Δ′} {ρ = ρ} r i
        (env {Θ = Θ} {c = c} {Bᵢ = Bᵢ} {Bₑ = Bₑ} {p = p} bw ⊢M ⊢c wE) =
  env (Bwf-ren r i bw)
      (⊢rename (ren-intC Θ ρ r i) (Inj-extN (nrev Θ) i) ⊢M)
      cprem
      (wf-ren r wE)
  where
  cprem : fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nrev Θ) ρ) c
            ∶ renameᵗ (extN (nrev Θ) ρ) Bᵢ
            ⇝ liftN (nrev (renᴮ ρ Θ)) (renameᵗ ρ Bₑ) ∙ p
  cprem = subst (λ n → fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nrev Θ) ρ) c
                         ∶ renameᵗ (extN (nrev Θ) ρ) Bᵢ
                         ⇝ liftN n (renameᵗ ρ Bₑ) ∙ p)
                (sym (nrev-ren ρ Θ))
                (subst (λ t → fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nrev Θ) ρ) c
                                ∶ renameᵗ (extN (nrev Θ) ρ) Bᵢ ⇝ t ∙ p)
                       (liftN-ren (nrev Θ) ρ Bₑ)
                       (conv-ren (ren-fceC Θ ρ r i) ⊢c))

------------------------------------------------------------------------
-- 9.  Q1b — THE RETAGGING TRANSPORT  (the ⊢retag analogue)
------------------------------------------------------------------------

⊑-scp : (Θ : BCtx) → Δ ⊑ Δ′ → scp Θ Δ ⊑ scp Θ Δ′
⊑-scp []          ls = ls
⊑-scp (own A ∷ Θ) ls = ⊑-scp Θ ls
⊑-scp (ali X ∷ Θ) ls = ⊑-upd unblk unblk-comm unblk-mono (⊑-scp Θ ls)
⊑-scp (cnc X ∷ Θ) ls = ⊑-upd blk blk-comm blk-mono (⊑-scp Θ ls)

⊑-fscp : (Θ : BCtx) → Δ ⊑ Δ′ → fscp Θ Δ ⊑ fscp Θ Δ′
⊑-fscp []          ls = ls
⊑-fscp (own A ∷ Θ) ls = ⊑-fscp Θ ls
⊑-fscp (ali X ∷ Θ) ls = ⊑-upd unblk unblk-comm unblk-mono (⊑-fscp Θ ls)
⊑-fscp (cnc X ∷ Θ) ls = ⊑-fscp Θ ls

⊑-intC : (Θ : BCtx) → Δ ⊑ Δ′ → intC Θ Δ ⊑ intC Θ Δ′
⊑-intC Θ ls = ⊑-prep (reps Θ) (⊑-scp Θ ls)

⊑-fceC : (Θ : BCtx) → Δ ⊑ Δ′ → fceC Θ Δ ⊑ fceC Θ Δ′
⊑-fceC Θ ls = ⊑-prep (reps Θ) (⊑-fscp Θ ls)

Bwf-⊑ : ∀ {Θ} → Δ ⊑ Δ′ → Bwf Δ Θ → Bwf Δ′ Θ
Bwf-⊑ ls bw[]        = bw[]
Bwf-⊑ ls (bw-o w b)  = bw-o (⊑-wf ls w) (Bwf-⊑ ls b)
Bwf-⊑ ls (bw-c tv b) = bw-c (⊑-tv ls tv) (Bwf-⊑ ls b)
Bwf-⊑ ls (bw-a d b)  with ⊑-∋e ls d
... | E′ , d′ , _ = bw-a d′ (Bwf-⊑ ls b)

-- THE THEOREM (Q1b).  Knowledge refinement moves a whole typing derivation
-- with the TYPE AND THE TERM UNCHANGED.  There is no ≈, no unfolding, and no
-- residue: the old design's `DualInt≈`/`DualRep≈`/`≼≈` obligations have no
-- analogue, because nothing on the spine is ever destroyed.
⊢retag : ∀ {Δ Δ′ Γ M A}
  → Δ ⊑ Δ′
  → Δ  ∣ Γ ⊢ M ⦂ A
    ---------------
  → Δ′ ∣ Γ ⊢ M ⦂ A
⊢retag ls (⊢` d)       = ⊢` d
⊢retag ls ⊢$           = ⊢$
⊢retag ls (⊢ƛ w ⊢N)    = ⊢ƛ (⊑-wf ls w) (⊢retag ls ⊢N)
⊢retag ls (⊢· ⊢L ⊢M)   = ⊢· (⊢retag ls ⊢L) (⊢retag ls ⊢M)
⊢retag ls (⊢Λ ⊢N)      = ⊢Λ (⊢retag (le∷ le-aa ls) ⊢N)
⊢retag ls (⊢·[] ⊢L w)  = ⊢·[] (⊢retag ls ⊢L) (⊑-wf ls w)
⊢retag ls (env {Θ = Θ} bw ⊢M ⊢c wE) =
  env (Bwf-⊑ ls bw)
      (⊢retag (⊑-intC Θ ls) ⊢M)
      (conv-⊑ (⊑-fceC Θ ls) ⊢c)
      (⊑-wf ls wE)

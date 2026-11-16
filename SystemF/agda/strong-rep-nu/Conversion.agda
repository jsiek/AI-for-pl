module strong-rep-nu.Conversion where

-- File Charter:
--   * CONVERSIONS, the `c` of a boundary `M ⟪ Θ , c ⟫`, as NORMAL
--     FORMS in three sorts (notes/MergeSketch.md): §1 the grammar —
--     a structural middle `Mid`, a seal chain `Tail` (associates
--     LEFT), an unseal chain `Conv` (associates RIGHT) — with renaming,
--     §1b the syntactic identity `IsId` and the `NoCancel` side
--     condition, §2 the three typing judgements
--     `Γ ∣ Θ ⊢ c ∶ R ⇝ S`, the permissions they read off the
--     scope, and the permission maps `PermMap`, §2b `SameConv` (two
--     spellings of one conversion) and RESPELLING (`respellᶜ`, per
--     name, from the scopes alone), §2c
--     reading a typed conversion and weakening a type, §2d
--     representation renaming, §3 `mkId`, §4 `reveal`/`conceal`,
--     §4b COMPOSITION `Δ ⊢ c₁ ⨟ c₂`, §5 the inversions, §6
--     `conv-types-unique`, §7 concrete checks.
--   * THE SCOPE IS A PARAMETER (the Δ ∣ Θ experiment, 2026-10-25).
--     A boundary's scope `Θ` grants PERMISSIONS: a `seal` needs an
--     unbind of its representation variable and an `unseal` a bind;
--     in `c ↦ d`, `c` is checked under the DUAL scope `dual Θ` (the
--     dual-scope variant, 2026-10-26d; it replaced a polarity index).
--     The two types are REPRESENTATION types, so no context spells
--     them.
--   * CONVERSIONS ARE REP-FREE.  `seal` and `unseal` carry an ordinary
--     type-variable NAME, never a representation spelling; the leaf
--     `Γ ∋ X ⊸ α := R` follows that name to its representation, and
--     `Γ` (the conversion context) is used for nothing else.
--     Composition reads the lookup square too (`repOf`), which is why
--     it takes the context.
--   * TIGHT.  A bare `seal X`/`unseal X` stands for an identity
--     middle; a chain extends only a NON-identity (`¬ IsId`); and
--     `NoCancel` forbids `unseal X` directly before a bare `seal X`.
-- Commentary: Commentary.md § Conversion.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans; cong₂; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; Base; base-ℕ; base-𝔹)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Lookup using (∋:=?)

private
  variable
    Δ Δ′ : Ctxᵗ
    η η′ : TyCtx
    A A′ B B′ C R : Ty
    X Y : ℕ
    α α′ : RVar
    ρ : Renameᵗ

------------------------------------------------------------------------
-- 1.  The grammar — three sorts
------------------------------------------------------------------------

-- `id A` is restricted to BASE TYPES AND VARIABLES by the typing
-- judgement; compound identities stay structural (`mkId`, §3).
infixr 7 _↦_
infixl 6 _⨾seal_
infixr 6 unseal_⨾_

mutual
  -- the structural middle
  data Mid : Set where
    id  : Ty → Mid
    _↦_ : Conv → Conv → Mid
    `∀  : Conv → Mid

  -- a seal chain over a middle; bare `seal X` is the identity middle
  -- followed by `seal X`
  data Tail : Set where
    mid     : Mid → Tail
    seal    : ℕ → Tail
    _⨾seal_ : Tail → ℕ → Tail

  -- an unseal chain over a tail; bare `unseal X` is `unseal X` followed
  -- by the identity middle
  data Conv : Set where
    tail      : Tail → Conv
    unseal    : ℕ → Conv
    unseal_⨾_ : ℕ → Conv → Conv

-- a middle as a whole conversion
⌞_⌟ : Mid → Conv
⌞ g ⌟ = tail (mid g)

private
  variable
    g g′ : Mid
    t t′ : Tail
    c c′ s s′ r u : Conv

mutual
  renᵐ : Renameᵗ → Mid → Mid
  renᵐ ρ (id A)  = id (renameᵗ ρ A)
  renᵐ ρ (s ↦ t) = renᶜ ρ s ↦ renᶜ ρ t
  renᵐ ρ (`∀ s)  = `∀ (renᶜ (extᵗ ρ) s)

  renᵀ : Renameᵗ → Tail → Tail
  renᵀ ρ (mid g)      = mid (renᵐ ρ g)
  renᵀ ρ (seal X)     = seal (ρ X)
  renᵀ ρ (t ⨾seal X)  = renᵀ ρ t ⨾seal ρ X

  renᶜ : Renameᵗ → Conv → Conv
  renᶜ ρ (tail t)       = tail (renᵀ ρ t)
  renᶜ ρ (unseal X)     = unseal (ρ X)
  renᶜ ρ (unseal X ⨾ c) = unseal (ρ X) ⨾ renᶜ ρ c

------------------------------------------------------------------------
-- 1b.  Identity and the cancellation side condition
------------------------------------------------------------------------

-- SYNTACTIC identity, structural identities included, so that
-- `(id ℕ ↦ id ℕ) ⨾seal Y` is not a second spelling of `seal Y`.
mutual
  IsIdᵐ : Mid → Set
  IsIdᵐ (id A)  = ⊤
  IsIdᵐ (s ↦ t) = IsIdᶜ s × IsIdᶜ t
  IsIdᵐ (`∀ s)  = IsIdᶜ s

  IsIdᵀ : Tail → Set
  IsIdᵀ (mid g)     = IsIdᵐ g
  IsIdᵀ (seal X)    = ⊥
  IsIdᵀ (t ⨾seal X) = ⊥

  IsIdᶜ : Conv → Set
  IsIdᶜ (tail t)       = IsIdᵀ t
  IsIdᶜ (unseal X)     = ⊥
  IsIdᶜ (unseal X ⨾ c) = ⊥

-- `c` does not open by resealing `X`: its seal chain does not begin
-- with a bare `seal X`.  (A non-identity middle blocks the cancel.)
NoCancelᵀ : ℕ → Tail → Set
NoCancelᵀ X (mid g)     = ⊤
NoCancelᵀ X (seal Y)    = X ≢ Y
NoCancelᵀ X (t ⨾seal Y) = NoCancelᵀ X t

NoCancel : ℕ → Conv → Set
NoCancel X (tail t)       = NoCancelᵀ X t
NoCancel X (unseal Y)     = ⊤
NoCancel X (unseal Y ⨾ c) = ⊤

mutual
  isIdᵐ? : (g : Mid) → Dec (IsIdᵐ g)
  isIdᵐ? (id A) = yes tt
  isIdᵐ? (s ↦ t) with isIdᶜ? s | isIdᶜ? t
  isIdᵐ? (s ↦ t) | yes p | yes q = yes (p , q)
  isIdᵐ? (s ↦ t) | yes p | no ¬q = no (λ { (_ , q) → ¬q q })
  isIdᵐ? (s ↦ t) | no ¬p | _     = no (λ { (p , _) → ¬p p })
  isIdᵐ? (`∀ s) = isIdᶜ? s

  isIdᵀ? : (t : Tail) → Dec (IsIdᵀ t)
  isIdᵀ? (mid g)     = isIdᵐ? g
  isIdᵀ? (seal X)    = no (λ ())
  isIdᵀ? (t ⨾seal X) = no (λ ())

  isIdᶜ? : (c : Conv) → Dec (IsIdᶜ c)
  isIdᶜ? (tail t)       = isIdᵀ? t
  isIdᶜ? (unseal X)     = no (λ ())
  isIdᶜ? (unseal X ⨾ c) = no (λ ())

------------------------------------------------------------------------
-- 2.  Typing — `Γ ∣ Θ ⊢ c ∶ R ⇝ S`
------------------------------------------------------------------------

-- THE Δ ∣ Θ EXPERIMENT (2026-10-25).  The boundary scope `Θ` is a
-- PARAMETER of the judgement instead of being applied to the context:
-- it grants PERMISSIONS.  The context `Γ` only resolves the names a
-- conversion mentions (it is the union reading of `Θ`, so every
-- de Bruijn spelling is the old one), and both types are
-- REPRESENTATION types, so a chain's intermediate type needs no
-- spelling on either side.
-- Commentary.md § Conversion.agda / §2

-- THE PERMISSIONS (the sketch's `−Xᵅ ∈ δ` and `+Xᵅ ∈ δ`): a `seal`
-- needs an UNBIND of its representation variable in `Θ`, an `unseal`
-- a BIND.  A function domain carries its argument INWARD, so it is
-- checked under the DUAL scope `dual Θ` (the sketch's `−δ`), which
-- grants a seal where `Θ` binds and an unseal where `Θ` unbinds.
SealOK : Boundary → RVar → Set
SealOK Θ α = InUnbinds α Θ

UnsealOK : Boundary → RVar → Set
UnsealOK Θ α = InBinds α Θ

-- the leaf lookup (the sketch's `α:=A ∈ Δ`): X names α, α is
-- represented by R, and R is a type here — the composition of a seal
-- with its unseal (`Merge`'s cancellation) writes that type down.
infix 4 _∋_⊸_:=_
_∋_⊸_:=_ : Ctxᵗ → ℕ → RVar → Ty → Set
Γ ∋ X ⊸ α := R =
  (names Γ ∋ˡ X := α) × (Γ ∋rep α := R) × (∃[ A ] (names Γ ⊢ A ~ R))

private
  variable
    Θ Θ′ : Boundary

infix 4 _∣_⊢ᵐ_∶_⇝_ _∣_⊢ᵀ_∶_⇝_ _∣_⊢_∶_⇝_

mutual
  data _∣_⊢ᵐ_∶_⇝_
    : Ctxᵗ → Boundary → Mid → Ty → Ty → Set where
    conv-id : Base A
        --------------------------------
      → Δ ∣ Θ ⊢ᵐ id A ∶ A ⇝ A

    conv-idv : names Δ ∋ˡ X := α
        --------------------------------
      → Δ ∣ Θ ⊢ᵐ id (` X) ∶ ` α ⇝ ` α

    -- the domain runs the other way: it is checked under the DUAL
    conv-fun : Δ ∣ dual Θ ⊢ s ∶ A′ ⇝ A
      → Δ ∣ Θ ⊢ c ∶ B ⇝ B′
        ----------------------------------------------
      → Δ ∣ Θ ⊢ᵐ s ↦ c ∶ (A ⇒ B) ⇝ (A′ ⇒ B′)

    conv-all : underΛ Δ ∣ liftᴮ Θ ⊢ s ∶ A ⇝ B
        --------------------------------------
      → Δ ∣ Θ ⊢ᵐ `∀ s ∶ `∀ A ⇝ `∀ B

  data _∣_⊢ᵀ_∶_⇝_
    : Ctxᵗ → Boundary → Tail → Ty → Ty → Set where
    conv-mid : Δ ∣ Θ ⊢ᵐ g ∶ A ⇝ B
        --------------------------------
      → Δ ∣ Θ ⊢ᵀ mid g ∶ A ⇝ B

    -- CONCEAL: needs `Θ`'s permission (an unbind)
    conv-seal : Δ ∋ X ⊸ α := A → SealOK Θ α
        --------------------------------
      → Δ ∣ Θ ⊢ᵀ seal X ∶ A ⇝ ` α

    conv-seal-seq : Δ ∣ Θ ⊢ᵀ t ∶ A ⇝ B
      → Δ ∋ X ⊸ α := B → SealOK Θ α → ¬ IsIdᵀ t
        --------------------------------
      → Δ ∣ Θ ⊢ᵀ t ⨾seal X ∶ A ⇝ ` α

  data _∣_⊢_∶_⇝_
    : Ctxᵗ → Boundary → Conv → Ty → Ty → Set where
    conv-tail : Δ ∣ Θ ⊢ᵀ t ∶ A ⇝ B
        --------------------------------
      → Δ ∣ Θ ⊢ tail t ∶ A ⇝ B

    -- REVEAL: needs `Θ`'s permission (a bind)
    conv-unseal : Δ ∋ X ⊸ α := A → UnsealOK Θ α
        --------------------------------
      → Δ ∣ Θ ⊢ unseal X ∶ ` α ⇝ A

    conv-unseal-seq : Δ ∋ X ⊸ α := A → UnsealOK Θ α
      → Δ ∣ Θ ⊢ c ∶ A ⇝ B
      → ¬ IsIdᶜ c → NoCancel X c
        --------------------------------
      → Δ ∣ Θ ⊢ unseal X ⨾ c ∶ ` α ⇝ B

-- A PERMISSION MAP: everything `Θ` grants, `Θ′` grants too.  It is
-- what a conversion needs to move to another scope (`Merge`'s merged
-- scope); it passes through `_↦_` (`pm-dual-map`) and `∀` (`pm-lift`).
-- `Wrap` needs none: the domain is already checked under the dual.
record PermMap (Θ Θ′ : Boundary) : Set where
  constructor permmap
  field
    pm-seal   : ∀ {α} → SealOK Θ α → SealOK Θ′ α
    pm-unseal : ∀ {α} → UnsealOK Θ α → UnsealOK Θ′ α
open PermMap public

-- a map between two scopes is one between their duals
pm-dual-map : PermMap Θ Θ′ → PermMap (dual Θ) (dual Θ′)
pm-dual-map {Θ = Θ} {Θ′ = Θ′} m =
  permmap (λ ok → binds→dual Θ′ (pm-unseal m (dual→binds Θ ok)))
          (λ ok → unbinds→dual Θ′ (pm-seal m (dual→unbinds Θ ok)))

pm-lift : PermMap Θ Θ′ → PermMap (liftᴮ Θ) (liftᴮ Θ′)
pm-lift {Θ = Θ} {Θ′ = Θ′} m = permmap seal′ unseal′
  where
  seal′ : ∀ {α} → SealOK (liftᴮ Θ) α → SealOK (liftᴮ Θ′) α
  seal′ {zero} ok = ⊥-elim (liftᴮ-no-unbind-zero Θ ok)
  seal′ {suc α} ok = in-unbinds-liftᴮ (pm-seal m (in-unbinds-liftᴮ⁻ Θ ok))

  unseal′ : ∀ {α} → UnsealOK (liftᴮ Θ) α → UnsealOK (liftᴮ Θ′) α
  unseal′ {zero} ok = ⊥-elim (liftᴮ-no-bind-zero Θ ok)
  unseal′ {suc α} ok = in-binds-liftᴮ (pm-unseal m (in-binds-liftᴮ⁻ Θ ok))

-- `Wrap` moves the domain into a boundary whose scope IS the dual it
-- was checked under: nothing to map
pm-id : PermMap Θ Θ
pm-id = permmap (λ ok → ok) (λ ok → ok)

pm-++ˡ : (Θ₂ : Boundary) → PermMap Θ (Θ ++ Θ₂)
pm-++ˡ Θ₂ = permmap in-unbinds-++ˡ in-binds-++ˡ

pm-++ʳ : (Θ₁ : Boundary) → PermMap Θ (Θ₁ ++ Θ)
pm-++ʳ Θ₁ = permmap (in-unbinds-++ʳ Θ₁) (in-binds-++ʳ Θ₁)

------------------------------------------------------------------------
-- 2b.  Two spellings of one conversion
------------------------------------------------------------------------

-- `SameConv` is `_⊢_≈_⊣_` (strong-rep-nu.Ctx §5) for a CONVERSION:
-- `_⊢_~_` one universe up at the `id`/`seal`/`unseal` leaves,
-- structural everywhere else.
-- Commentary.md § Conversion.agda / §2b
infix 4 _⊩ᵐ_~_ _⊩ᵀ_~_ _⊩_~_

mutual
  data _⊩ᵐ_~_ (η : TyCtx) : Mid → Mid → Set where
    sameᶜ-id  : η ⊢ A ~ R → η ⊩ᵐ id A ~ id R
    sameᶜ-fun : η ⊩ s ~ r → η ⊩ c ~ u → η ⊩ᵐ s ↦ c ~ r ↦ u
    sameᶜ-all : (zero ∷ shiftReps η) ⊩ s ~ r → η ⊩ᵐ `∀ s ~ `∀ r

  data _⊩ᵀ_~_ (η : TyCtx) : Tail → Tail → Set where
    sameᶜ-mid      : η ⊩ᵐ g ~ g′ → η ⊩ᵀ mid g ~ mid g′
    sameᶜ-seal     : η ∋ˡ X := α → η ⊩ᵀ seal X ~ seal α
    sameᶜ-seal-seq : η ⊩ᵀ t ~ t′ → η ∋ˡ X := α
      → η ⊩ᵀ t ⨾seal X ~ t′ ⨾seal α

  data _⊩_~_ (η : TyCtx) : Conv → Conv → Set where
    sameᶜ-tail       : η ⊩ᵀ t ~ t′ → η ⊩ tail t ~ tail t′
    sameᶜ-unseal     : η ∋ˡ X := α → η ⊩ unseal X ~ unseal α
    sameᶜ-unseal-seq : η ∋ˡ X := α → η ⊩ c ~ r
      → η ⊩ unseal X ⨾ c ~ unseal α ⨾ r

sameᶜ-cast : η ≡ η′ → η ⊩ s ~ r → η′ ⊩ s ~ r
sameᶜ-cast refl p = p

mutual
  sameᵐ-ren : (ρ : Renameᵗ) → η ⊩ᵐ g ~ g′ → map ρ η ⊩ᵐ g ~ renᵐ ρ g′
  sameᵐ-ren ρ (sameᶜ-id p) = sameᶜ-id (same-ren ρ p)
  sameᵐ-ren ρ (sameᶜ-fun p q) = sameᶜ-fun (sameᶜ-ren ρ p) (sameᶜ-ren ρ q)
  sameᵐ-ren {η = η} ρ (sameᶜ-all p) =
    sameᶜ-all
      (sameᶜ-cast (names-underΛ-ren ρ η) (sameᶜ-ren (extᵗ ρ) p))

  sameᵀ-ren : (ρ : Renameᵗ) → η ⊩ᵀ t ~ t′ → map ρ η ⊩ᵀ t ~ renᵀ ρ t′
  sameᵀ-ren ρ (sameᶜ-mid p) = sameᶜ-mid (sameᵐ-ren ρ p)
  sameᵀ-ren ρ (sameᶜ-seal d) = sameᶜ-seal (∋ˡ-ren ρ d)
  sameᵀ-ren ρ (sameᶜ-seal-seq p d) =
    sameᶜ-seal-seq (sameᵀ-ren ρ p) (∋ˡ-ren ρ d)

  sameᶜ-ren : (ρ : Renameᵗ) → η ⊩ s ~ r → map ρ η ⊩ s ~ renᶜ ρ r
  sameᶜ-ren ρ (sameᶜ-tail p) = sameᶜ-tail (sameᵀ-ren ρ p)
  sameᶜ-ren ρ (sameᶜ-unseal d) = sameᶜ-unseal (∋ˡ-ren ρ d)
  sameᶜ-ren ρ (sameᶜ-unseal-seq d p) =
    sameᶜ-unseal-seq (∋ˡ-ren ρ d) (sameᶜ-ren ρ p)

SameConv : Ctxᵗ → Conv → Ctxᵗ → Conv → Set
SameConv Γ s Γ′ s′ = ∃[ r ] ((names Γ ⊩ s ~ r) × (names Γ′ ⊩ s′ ~ r))

-- RESPELLING.  A crossing moves a conversion to another position, where
-- other scopes overlap; it is RENAMED there, PER NAME and from the
-- scopes alone: each name is DECODED back through the conversion
-- reading it was written in, carried along the crossing's PATH (an
-- interior reading), and ENCODED into the target conversion reading.
-- A name is traced as a TOKEN: a position, or "the name for α" while α
-- has none.  Whether a `bind` finds its name already live is read off
-- the scope too (`Mentions`): a well-formed scope binds a name the
-- context has only after unbinding it.  A renaming that RESPECTS the
-- two name maps keeps the reading (`sameᶜ-respects`); that this one
-- does is strong-rep-nu.proof.Respell.
-- Commentary.md § Conversion.agda / §2b

data Tok : Set where
  pos  : ℕ → Tok
  gone : RVar → Tok

-- inserting a name at Y moves the positions at or above Y up one
punchIn : ℕ → ℕ → ℕ
punchIn zero    p       = suc p
punchIn (suc Y) zero    = zero
punchIn (suc Y) (suc p) = suc (punchIn Y p)

upTok : Tok → Tok
upTok (pos p)  = pos (suc p)
upTok (gone α) = gone α

-- removing the name at Y, which names α: position Y becomes α's token,
-- the positions above it move down one
peel : ℕ → RVar → ℕ → Tok
peel zero    α zero    = gone α
peel zero    α (suc X) = pos X
peel (suc Y) α zero    = pos zero
peel (suc Y) α (suc X) = upTok (peel Y α X)

thenTok : Tok → (ℕ → Tok) → Tok
thenTok (pos p)  k = k p
thenTok (gone α) k = gone α

-- one change, forward, as the interior reading performs it
stepTok : Change → Tok → Tok
stepTok (unbind Y β) (pos p)  = peel Y β p
stepTok (unbind Y β) (gone α) = gone α
stepTok (bind Y β)   (pos p)  = pos (punchIn Y p)
stepTok (bind Y β)   (gone α) with α ≟ β
stepTok (bind Y β)   (gone α) | yes eq = pos Y
stepTok (bind Y β)   (gone α) | no ne  = gone α

-- forward through an interior reading (the tail acts first)
encodeI : Boundary → Tok → Tok
encodeI []      t = t
encodeI (δ ∷ χ) t = stepTok δ (encodeI χ t)

-- forward through a conversion reading: unbinds are skipped, and a bind
-- whose name an earlier-acting change mentions finds it live
encodeU : Boundary → Tok → Tok
encodeU []               t = t
encodeU (unbind Y β ∷ χ) t = encodeU χ t
encodeU (bind Y β ∷ χ)   t with mentions? β χ
encodeU (bind Y β ∷ χ)   t | yes m  = encodeU χ t
encodeU (bind Y β ∷ χ)   t | no nm = stepTok (bind Y β) (encodeU χ t)

-- backward through a conversion reading, the last-acting change first
decodeU : Boundary → ℕ → Tok
decodeU []               X = pos X
decodeU (unbind Y β ∷ χ) X = decodeU χ X
decodeU (bind Y β ∷ χ)   X with mentions? β χ
decodeU (bind Y β ∷ χ)   X | yes m  = decodeU χ X
decodeU (bind Y β ∷ χ)   X | no nm = thenTok (peel Y β X) (decodeU χ)

-- a token that ends without a position was no name of the source, and
-- keeps its spelling (a typed conversion has none)
finish : ℕ → Tok → ℕ
finish X (pos q)  = q
finish X (gone α) = X

-- `respell Θₛ Π Θₜ`: from `Θₛ`'s conversion reading back to its
-- exterior, along the interior reading of `Π`, into `Θₜ`'s conversion
-- reading.  Wrap's is `respell Θ Θ (dual Θ)`; Merge's are
-- `respell Θ₁ (dual Θ₂) (Θ₁ ++ Θ₂)` and `respell Θ₂ [] (Θ₁ ++ Θ₂)`.
respell : Boundary → Boundary → Boundary → Renameᵗ
respell Θₛ Π Θₜ X = finish X (encodeU Θₜ (encodeI Π (decodeU Θₛ X)))

respellᶜ : Boundary → Boundary → Boundary → Conv → Conv
respellᶜ Θₛ Π Θₜ = renᶜ (respell Θₛ Π Θₜ)

Respects : Renameᵗ → TyCtx → TyCtx → Set
Respects ρ η η′ = ∀ {X α} → η ∋ˡ X := α → η′ ∋ˡ ρ X := α

∋ˡ-shift⁻ : ∀ {η : TyCtx} {X α} → shiftReps η ∋ˡ X := α
  → ∃[ β ] ((α ≡ suc β) × (η ∋ˡ X := β))
∋ˡ-shift⁻ {η = []} ()
∋ˡ-shift⁻ {η = β ∷ η} here = β , refl , here
∋ˡ-shift⁻ {η = β ∷ η} (there d) with ∋ˡ-shift⁻ d
∋ˡ-shift⁻ {η = β ∷ η} (there d) | γ , eq , d′ = γ , eq , there d′

respects-ext : Respects ρ η η′
  → Respects (extᵗ ρ) (zero ∷ shiftReps η) (zero ∷ shiftReps η′)
respects-ext r here = here
respects-ext r (there d) with ∋ˡ-shift⁻ d
respects-ext r (there d) | β , refl , d′ = there (∋ˡ-ren suc (r d′))

same-respects : Respects ρ η η′ → η ⊢ A ~ R → η′ ⊢ renameᵗ ρ A ~ R
same-respects r (same-var d) = same-var (r d)
same-respects r same-ℕ = same-ℕ
same-respects r same-𝔹 = same-𝔹
same-respects r (same-⇒ a b) = same-⇒ (same-respects r a) (same-respects r b)
same-respects r (same-∀ a) = same-∀ (same-respects (respects-ext r) a)

mutual
  sameᵐ-respects : Respects ρ η η′ → η ⊩ᵐ g ~ g′ → η′ ⊩ᵐ renᵐ ρ g ~ g′
  sameᵐ-respects r (sameᶜ-id a) = sameᶜ-id (same-respects r a)
  sameᵐ-respects r (sameᶜ-fun a b) =
    sameᶜ-fun (sameᶜ-respects r a) (sameᶜ-respects r b)
  sameᵐ-respects r (sameᶜ-all a) =
    sameᶜ-all (sameᶜ-respects (respects-ext r) a)

  sameᵀ-respects : Respects ρ η η′ → η ⊩ᵀ t ~ t′ → η′ ⊩ᵀ renᵀ ρ t ~ t′
  sameᵀ-respects r (sameᶜ-mid a) = sameᶜ-mid (sameᵐ-respects r a)
  sameᵀ-respects r (sameᶜ-seal d) = sameᶜ-seal (r d)
  sameᵀ-respects r (sameᶜ-seal-seq a d) =
    sameᶜ-seal-seq (sameᵀ-respects r a) (r d)

  sameᶜ-respects : Respects ρ η η′ → η ⊩ s ~ s′ → η′ ⊩ renᶜ ρ s ~ s′
  sameᶜ-respects r (sameᶜ-tail a) = sameᶜ-tail (sameᵀ-respects r a)
  sameᶜ-respects r (sameᶜ-unseal d) = sameᶜ-unseal (r d)
  sameᶜ-respects r (sameᶜ-unseal-seq d a) =
    sameᶜ-unseal-seq (r d) (sameᶜ-respects r a)

------------------------------------------------------------------------
-- 2c. Reading a typed conversion; weakening a type
------------------------------------------------------------------------

-- `Q` and `dual-conversion-exists` live with the relational context
-- readings in strong-rep-nu.Boundary; this section transports the
-- actual type and conversion spellings.
-- Commentary.md § Conversion.agda / §2c

weaken-ty : η ⊆ᵃ η′ → η ⊢ A ~ R
  → ∃[ A′ ] (η′ ⊢ A′ ~ R)
weaken-ty f (same-var d) with f (_ , d)
weaken-ty f (same-var d) | X , d′ = ` X , same-var d′
weaken-ty f same-ℕ = `ℕ , same-ℕ
weaken-ty f same-𝔹 = `𝔹 , same-𝔹
weaken-ty f (same-⇒ a b) with weaken-ty f a
weaken-ty f (same-⇒ a b) | A′ , a′ with weaken-ty f b
weaken-ty f (same-⇒ a b) | A′ , a′ | B′ , b′ =
  A′ ⇒ B′ , same-⇒ a′ b′
weaken-ty f (same-∀ a) with weaken-ty (⊆ᵃ-underΛ f) a
weaken-ty f (same-∀ a) | A′ , a′ = `∀ A′ , same-∀ a′


mutual
  readableᵐ : Δ ∣ Θ ⊢ᵐ g ∶ A ⇝ B → ∃[ r ] (names Δ ⊩ᵐ g ~ r)
  readableᵐ (conv-id base-ℕ) = id `ℕ , sameᶜ-id same-ℕ
  readableᵐ (conv-id base-𝔹) = id `𝔹 , sameᶜ-id same-𝔹
  readableᵐ (conv-idv d) = id (` _) , sameᶜ-id (same-var d)
  readableᵐ (conv-fun a b) with readable a
  readableᵐ (conv-fun a b) | r₁ , a′ with readable b
  readableᵐ (conv-fun a b) | r₁ , a′ | r₂ , b′ =
    r₁ ↦ r₂ , sameᶜ-fun a′ b′
  readableᵐ (conv-all a) with readable a
  readableᵐ (conv-all a) | r₁ , a′ = `∀ r₁ , sameᶜ-all a′

  readableᵀ : Δ ∣ Θ ⊢ᵀ t ∶ A ⇝ B → ∃[ r ] (names Δ ⊩ᵀ t ~ r)
  readableᵀ (conv-mid a) with readableᵐ a
  readableᵀ (conv-mid a) | r , a′ = mid r , sameᶜ-mid a′
  readableᵀ (conv-seal (d , rd , _) ok) = seal _ , sameᶜ-seal d
  readableᵀ (conv-seal-seq a (d , rd , _) ok ¬id) with readableᵀ a
  readableᵀ (conv-seal-seq a (d , rd , _) ok ¬id) | r , a′ =
    r ⨾seal _ , sameᶜ-seal-seq a′ d

  readable : Δ ∣ Θ ⊢ c ∶ A ⇝ B → ∃[ r ] (names Δ ⊩ c ~ r)
  readable (conv-tail a) with readableᵀ a
  readable (conv-tail a) | r , a′ = tail r , sameᶜ-tail a′
  readable (conv-unseal (d , rd , _) ok) = unseal _ , sameᶜ-unseal d
  readable (conv-unseal-seq (d , rd , _) ok a ¬id nc) with readable a
  readable (conv-unseal-seq (d , rd , _) ok a ¬id nc) | r , a′ =
    unseal _ ⨾ r , sameᶜ-unseal-seq d a′

------------------------------------------------------------------------
-- 2d. Renaming the representation universe
------------------------------------------------------------------------

-- A conversion's SPELLING survives a representation-only renaming
-- unchanged; its context, its scope and its two REPRESENTATION types
-- are renamed.
-- Commentary.md § Conversion.agda / §2d

conv-cast : ∀ {Ξ : RepCtx} → η ≡ η′ → Θ ≡ Θ′
  → (Ξ ∣ η) ∣ Θ ⊢ c ∶ A ⇝ B → (Ξ ∣ η′) ∣ Θ′ ⊢ c ∶ A ⇝ B
conv-cast refl refl ⊢c = ⊢c

base-ren : Base A → renameᵗ ρ A ≡ A
base-ren base-ℕ = refl
base-ren base-𝔹 = refl


leaf-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
  → (Ξ ∣ η) ∋ X ⊸ α := A → (Ξ′ ∣ map ρ η) ∋ X ⊸ ρ α := renameᵗ ρ A
leaf-ren {ρ = ρ} w (d , rd , A , q) =
  ∋ˡ-ren ρ d , wk-bind w rd , A , same-ren ρ q

mutual
  convᵐ-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
    → (Ξ ∣ η) ∣ Θ ⊢ᵐ g ∶ A ⇝ B
    → (Ξ′ ∣ map ρ η) ∣ renᴮᴿ ρ Θ ⊢ᵐ g
        ∶ renameᵗ ρ A ⇝ renameᵗ ρ B
  convᵐ-ren {ρ = ρ} w (conv-id {A = A} b) rewrite base-ren {ρ = ρ} b =
    conv-id b
  convᵐ-ren {ρ = ρ} w (conv-idv d) = conv-idv (∋ˡ-ren ρ d)
  convᵐ-ren {ρ = ρ} {Θ = Θ} w (conv-fun p q) =
    conv-fun (conv-cast refl (renᴮᴿ-dual ρ Θ) (conv-ren w p))
             (conv-ren w q)
  convᵐ-ren {ρ = ρ} {η = η} {Θ = Θ} w (conv-all q) =
    conv-all (conv-cast (names-underΛ-ren ρ η) (renᴮᴿ-liftᴮ ρ Θ)
                        (conv-ren (repwk-abst w) q))

  convᵀ-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
    → (Ξ ∣ η) ∣ Θ ⊢ᵀ t ∶ A ⇝ B
    → (Ξ′ ∣ map ρ η) ∣ renᴮᴿ ρ Θ ⊢ᵀ t
        ∶ renameᵗ ρ A ⇝ renameᵗ ρ B
  convᵀ-ren w (conv-mid q) = conv-mid (convᵐ-ren w q)
  convᵀ-ren {ρ = ρ} w (conv-seal d ok) =
    conv-seal (leaf-ren w d) (in-unbinds-ren ρ ok)
  convᵀ-ren {ρ = ρ} w (conv-seal-seq q d ok ¬id) =
    conv-seal-seq (convᵀ-ren w q) (leaf-ren w d) (in-unbinds-ren ρ ok) ¬id

  conv-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
    → (Ξ ∣ η) ∣ Θ ⊢ c ∶ A ⇝ B
    → (Ξ′ ∣ map ρ η) ∣ renᴮᴿ ρ Θ ⊢ c
        ∶ renameᵗ ρ A ⇝ renameᵗ ρ B
  conv-ren w (conv-tail q) = conv-tail (convᵀ-ren w q)
  conv-ren {ρ = ρ} w (conv-unseal d ok) =
    conv-unseal (leaf-ren w d) (in-binds-ren ρ ok)
  conv-ren {ρ = ρ} w (conv-unseal-seq d ok q ¬id nc) =
    conv-unseal-seq (leaf-ren w d) (in-binds-ren ρ ok)
                    (conv-ren w q) ¬id nc

------------------------------------------------------------------------
-- 3.  The identity conversion at an arbitrary type
------------------------------------------------------------------------

mkId : Ty → Conv
mkId (` X)   = ⌞ id (` X) ⌟
mkId `ℕ      = ⌞ id `ℕ ⌟
mkId `𝔹      = ⌞ id `𝔹 ⌟
mkId (A ⇒ B) = ⌞ mkId A ↦ mkId B ⌟
mkId (`∀ A)  = ⌞ `∀ (mkId A) ⌟

-- the identity at a type is typed at the type's representation, under
-- any scope: an `id` needs no permission
mkId-⊢ : names Δ ⊢ A ~ R → Δ ∣ Θ ⊢ mkId A ∶ R ⇝ R
mkId-⊢ (same-var d)  = conv-tail (conv-mid (conv-idv d))
mkId-⊢ same-ℕ        = conv-tail (conv-mid (conv-id base-ℕ))
mkId-⊢ same-𝔹        = conv-tail (conv-mid (conv-id base-𝔹))
mkId-⊢ (same-⇒ a b)  = conv-tail (conv-mid (conv-fun (mkId-⊢ a) (mkId-⊢ b)))
mkId-⊢ (same-∀ a)    = conv-tail (conv-mid (conv-all (mkId-⊢ a)))

mkId-isId : (A : Ty) → IsIdᶜ (mkId A)
mkId-isId (` X)   = tt
mkId-isId `ℕ      = tt
mkId-isId `𝔹      = tt
mkId-isId (A ⇒ B) = mkId-isId A , mkId-isId B
mkId-isId (`∀ A)  = mkId-isId A

------------------------------------------------------------------------
-- 4.  The canonical conversions at a slot
------------------------------------------------------------------------

-- Unseal every occurrence of X where the conversion runs covariantly,
-- seal it back where it runs contravariantly.  DERIVED FROM THE TYPE.
-- Commentary.md § Conversion.agda / §4
mutual
  reveal : ℕ → Ty → Conv
  reveal X (` Y) with X ≟ Y
  reveal X (` Y) | yes _ = unseal X
  reveal X (` Y) | no  _ = ⌞ id (` Y) ⌟
  reveal X `ℕ      = ⌞ id `ℕ ⌟
  reveal X `𝔹      = ⌞ id `𝔹 ⌟
  reveal X (A ⇒ B) = ⌞ conceal X A ↦ reveal X B ⌟
  reveal X (`∀ A)  = ⌞ `∀ (reveal (suc X) A) ⌟

  conceal : ℕ → Ty → Conv
  conceal X (` Y) with X ≟ Y
  conceal X (` Y) | yes _ = tail (seal X)
  conceal X (` Y) | no  _ = ⌞ id (` Y) ⌟
  conceal X `ℕ      = ⌞ id `ℕ ⌟
  conceal X `𝔹      = ⌞ id `𝔹 ⌟
  conceal X (A ⇒ B) = ⌞ reveal X A ↦ conceal X B ⌟
  conceal X (`∀ A)  = ⌞ `∀ (conceal (suc X) A) ⌟

------------------------------------------------------------------------
-- 4b.  Composition — `Δ ⊢ c₁ ⨟ c₂`, first c₁ then c₂
------------------------------------------------------------------------

-- The representation a name denotes at `Δ`, spelled with `Δ`'s own
-- names: the lookup square as a function.  The fallback is never
-- reached on well-typed input (`conv-seal` carries the square).
repOf : Ctxᵗ → ℕ → Ty
repOf Δ X with ∋:=? Δ X
repOf Δ X | just (A , _) = A
repOf Δ X | nothing      = `ℕ

-- The two smart constructors keep a chain TIGHT: a seal or unseal over
-- an identity is the bare form, and `unseal X` before a bare `seal X`
-- cancels (the rest of that seal chain survives).
infixl 6 _⨾sealˢ_
_⨾sealˢ_ : Tail → ℕ → Tail
t ⨾sealˢ X with isIdᵀ? t
t ⨾sealˢ X | yes _ = seal X
t ⨾sealˢ X | no  _ = t ⨾seal X

-- `cancelᵀ X t` is `unseal X ; t` for a NON-identity tail `t`: a tail
-- if the unseal cancelled against `t`'s first seal, an unseal chain if
-- it did not.
cancelᵀ : ℕ → Tail → Conv
cancelᵀ X (mid g) = unseal X ⨾ tail (mid g)
cancelᵀ X (seal Y) with X ≟ Y
cancelᵀ X (seal Y) | yes _ = ⌞ id (` X) ⌟
cancelᵀ X (seal Y) | no  _ = unseal X ⨾ tail (seal Y)
cancelᵀ X (t ⨾seal Y) with cancelᵀ X t
cancelᵀ X (t ⨾seal Y) | tail t′       = tail (t′ ⨾sealˢ Y)
cancelᵀ X (t ⨾seal Y) | unseal Z      = unseal X ⨾ tail (t ⨾seal Y)
cancelᵀ X (t ⨾seal Y) | unseal Z ⨾ c  = unseal X ⨾ tail (t ⨾seal Y)

infixr 6 unseal_⨾ˢ_
unseal_⨾ˢ_ : ℕ → Conv → Conv
unseal X ⨾ˢ tail t with isIdᵀ? t
unseal X ⨾ˢ tail t | yes _ = unseal X
unseal X ⨾ˢ tail t | no  _ = cancelᵀ X t
unseal X ⨾ˢ unseal Y       = unseal X ⨾ unseal Y
unseal X ⨾ˢ (unseal Y ⨾ c) = unseal X ⨾ (unseal Y ⨾ c)

-- One operator per sort, recursing on the sorts alone.  Where a clause
-- relies on typing, the comment says why; the pairs typing rules out
-- return their first argument.
-- Commentary.md § Conversion.agda / §4b
infix 4 _⊢_⨟_ _⊢_⨟ᵀ_ _⊢_⨟ᵀᵀ_ _⊢_⨟ᵐ_
mutual
  _⊢_⨟_ : Ctxᵗ → Conv → Conv → Conv
  Δ ⊢ unseal X ⨟ c₂       = unseal X ⨾ˢ c₂
  Δ ⊢ (unseal X ⨾ c₁) ⨟ c₂ = unseal X ⨾ˢ (Δ ⊢ c₁ ⨟ c₂)
  Δ ⊢ tail t ⨟ c₂          = Δ ⊢ t ⨟ᵀ c₂

  _⊢_⨟ᵀ_ : Ctxᵗ → Tail → Conv → Conv
  Δ ⊢ t ⨟ᵀ tail t₂ = tail (Δ ⊢ t ⨟ᵀᵀ t₂)
  -- a seal then an unseal: the types force the same name (CancelR)
  Δ ⊢ seal X ⨟ᵀ unseal Y           = mkId (repOf Δ X)
  Δ ⊢ seal X ⨟ᵀ (unseal Y ⨾ c)     = c
  Δ ⊢ (t ⨾seal X) ⨟ᵀ unseal Y      = tail t
  Δ ⊢ (t ⨾seal X) ⨟ᵀ (unseal Y ⨾ c) = Δ ⊢ t ⨟ᵀ c
  -- a middle whose target is a variable is `id (` Y)`
  Δ ⊢ mid g ⨟ᵀ unseal Y       = unseal Y
  Δ ⊢ mid g ⨟ᵀ (unseal Y ⨾ c) = unseal Y ⨾ c

  _⊢_⨟ᵀᵀ_ : Ctxᵗ → Tail → Tail → Tail
  Δ ⊢ t ⨟ᵀᵀ seal Y         = t ⨾sealˢ Y
  Δ ⊢ t ⨟ᵀᵀ (t₂ ⨾seal Y)   = (Δ ⊢ t ⨟ᵀᵀ t₂) ⨾sealˢ Y
  Δ ⊢ mid g ⨟ᵀᵀ mid g₂     = mid (Δ ⊢ g ⨟ᵐ g₂)
  -- a middle whose source is a variable is `id (` X)`
  Δ ⊢ seal X ⨟ᵀᵀ mid g₂     = seal X
  Δ ⊢ (t ⨾seal X) ⨟ᵀᵀ mid g₂ = t ⨾seal X

  _⊢_⨟ᵐ_ : Ctxᵗ → Mid → Mid → Mid
  Δ ⊢ id A ⨟ᵐ g₂               = g₂
  Δ ⊢ (s ↦ c) ⨟ᵐ id B          = s ↦ c
  -- the domain flips
  Δ ⊢ (s ↦ c) ⨟ᵐ (s′ ↦ c′)     = (Δ ⊢ s′ ⨟ s) ↦ (Δ ⊢ c ⨟ c′)
  Δ ⊢ (s ↦ c) ⨟ᵐ `∀ s′         = s ↦ c
  Δ ⊢ `∀ s ⨟ᵐ id B             = `∀ s
  Δ ⊢ `∀ s ⨟ᵐ (s′ ↦ c′)        = `∀ s
  Δ ⊢ `∀ s ⨟ᵐ `∀ s′            = `∀ (underΛ Δ ⊢ s ⨟ s′)

------------------------------------------------------------------------
-- 5. Conversion inversions
------------------------------------------------------------------------

-- Every rep a conversion mentions IS the binder's rep — there is no
-- second spelling.
seal-source-is-rep : Δ ∣ Θ ⊢ tail (seal X) ∶ A ⇝ B
  → ∃[ α ] ((Δ ∋ X ⊸ α := A) × (B ≡ ` α))
seal-source-is-rep (conv-tail (conv-seal d ok)) = _ , d , refl

unseal-target-is-rep : Δ ∣ Θ ⊢ unseal X ∶ A ⇝ B
  → ∃[ α ] ((Δ ∋ X ⊸ α := B) × (A ≡ ` α))
unseal-target-is-rep (conv-unseal d ok) = _ , d , refl

conv-id-base-src : Base A → Δ ∣ Θ ⊢ ⌞ id A ⌟ ∶ B ⇝ C → B ≡ A
conv-id-base-src bA (conv-tail (conv-mid (conv-id _)))  = refl
conv-id-base-src () (conv-tail (conv-mid (conv-idv _)))

conv-id-refl : Δ ∣ Θ ⊢ ⌞ id A ⌟ ∶ B ⇝ C → B ≡ C
conv-id-refl (conv-tail (conv-mid (conv-id _)))  = refl
conv-id-refl (conv-tail (conv-mid (conv-idv _))) = refl

-- A ∀ conversion's body, as an inversion returning the two `∀` shapes
-- AS EQUATIONS.
-- Commentary.md § Conversion.agda / §5
conv-all-inv : Δ ∣ Θ ⊢ ⌞ `∀ s ⌟ ∶ A ⇝ B
  → Σ[ A₀ ∈ Ty ] Σ[ B₀ ∈ Ty ]
      ((A ≡ `∀ A₀) ×
       (B ≡ `∀ B₀) ×
       (underΛ Δ ∣ liftᴮ Θ ⊢ s ∶ A₀ ⇝ B₀))
conv-all-inv (conv-tail (conv-mid (conv-all ⊢s))) =
  _ , _ , refl , refl , ⊢s

conv-fun-inv : Δ ∣ Θ ⊢ ⌞ s ↦ c ⌟ ∶ A ⇝ B
  → Σ[ A₁ ∈ Ty ] Σ[ B₁ ∈ Ty ] Σ[ A₂ ∈ Ty ] Σ[ B₂ ∈ Ty ]
      ((A ≡ A₁ ⇒ B₁) ×
       (B ≡ A₂ ⇒ B₂) ×
       (Δ ∣ dual Θ ⊢ s ∶ A₂ ⇝ A₁) ×
       (Δ ∣ Θ ⊢ c ∶ B₁ ⇝ B₂))
conv-fun-inv (conv-tail (conv-mid (conv-fun ⊢s ⊢c))) =
  _ , _ , _ , _ , refl , refl , ⊢s , ⊢c

------------------------------------------------------------------------
-- 6. Conversion types are unique
------------------------------------------------------------------------

-- With representation types no `Unique` premise is needed: a name
-- determines its representation variable, and that its payload.
leaf-det : Δ ∋ X ⊸ α := A → Δ ∋ X ⊸ α′ := B → (α ≡ α′) × (A ≡ B)
leaf-det (d , rd , _) (d′ , rd′ , _) with ∋ˡ-det d d′
leaf-det (d , rd , _) (d′ , rd′ , _) | refl with ∋ʳ-det rd rd′
leaf-det (d , rd , _) (d′ , rd′ , _) | refl | refl = refl , refl

mutual
  convᵐ-types-unique : Δ ∣ Θ ⊢ᵐ g ∶ A ⇝ B
    → Δ ∣ Θ ⊢ᵐ g ∶ A′ ⇝ B′ → (A ≡ A′) × (B ≡ B′)
  convᵐ-types-unique (conv-id b) (conv-id b′) = refl , refl
  convᵐ-types-unique (conv-id ()) (conv-idv d′)
  convᵐ-types-unique (conv-idv d) (conv-id ())
  convᵐ-types-unique (conv-idv d) (conv-idv d′) with ∋ˡ-det d d′
  ... | refl = refl , refl
  convᵐ-types-unique (conv-fun s t) (conv-fun s′ t′)
    with conv-types-unique s s′ | conv-types-unique t t′
  ... | refl , refl | refl , refl = refl , refl
  convᵐ-types-unique (conv-all s) (conv-all s′)
    with conv-types-unique s s′
  ... | refl , refl = refl , refl

  convᵀ-types-unique : Δ ∣ Θ ⊢ᵀ t ∶ A ⇝ B
    → Δ ∣ Θ ⊢ᵀ t ∶ A′ ⇝ B′ → (A ≡ A′) × (B ≡ B′)
  convᵀ-types-unique (conv-mid q) (conv-mid q′) =
    convᵐ-types-unique q q′
  convᵀ-types-unique (conv-seal d ok) (conv-seal d′ ok′)
    with leaf-det d d′
  ... | refl , refl = refl , refl
  convᵀ-types-unique (conv-seal-seq q d ok n) (conv-seal-seq q′ d′ ok′ n′)
    with convᵀ-types-unique q q′ | leaf-det d d′
  ... | refl , _ | refl , _ = refl , refl

  conv-types-unique : Δ ∣ Θ ⊢ c ∶ A ⇝ B
    → Δ ∣ Θ ⊢ c ∶ A′ ⇝ B′ → (A ≡ A′) × (B ≡ B′)
  conv-types-unique (conv-tail q) (conv-tail q′) =
    convᵀ-types-unique q q′
  conv-types-unique (conv-unseal d ok) (conv-unseal d′ ok′)
    with leaf-det d d′
  ... | refl , refl = refl , refl
  conv-types-unique (conv-unseal-seq d ok q n m)
                    (conv-unseal-seq d′ ok′ q′ n′ m′)
    with leaf-det d d′
  ... | refl , refl with conv-types-unique q q′
  ...   | _ , refl = refl , refl

conv-src-unique : Δ ∣ Θ ⊢ c ∶ A ⇝ B → Δ ∣ Θ ⊢ c ∶ A′ ⇝ B′
  → A ≡ A′
conv-src-unique ⊢c ⊢c′ with conv-types-unique ⊢c ⊢c′
... | eq , _ = eq

------------------------------------------------------------------------
-- 7. Concrete permission and composition checks
------------------------------------------------------------------------

-- `TyBeta`'s context: one cell for ℕ, named 0, bound by the scope
βCtx : Ctxᵗ
βCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

β-leaf : βCtx ∋ zero ⊸ zero := `ℕ
β-leaf = here , r-here , `ℕ , same-ℕ

-- `bind 0 0` licenses `unseal 0` …
β-unseal : βCtx ∣ (bind 0 0 ∷ []) ⊢ unseal zero ∶ ` zero ⇝ `ℕ
β-unseal = conv-unseal β-leaf ib-here

-- … and `seal 0` only in a function domain, under the dual
β-seal : βCtx ∣ dual (bind 0 0 ∷ []) ⊢ tail (seal zero) ∶ `ℕ ⇝ ` zero
β-seal = conv-tail (conv-seal β-leaf iu-here)

β-reveal : βCtx ∣ (bind 0 0 ∷ []) ⊢
  ⌞ tail (seal zero) ↦ unseal zero ⌟ ∶ (` zero ⇒ ` zero) ⇝ (`ℕ ⇒ `ℕ)
β-reveal = conv-tail (conv-mid (conv-fun β-seal β-unseal))

-- THE TIGHTENING: a bind does not license a seal outside a domain
¬β-seal : ¬ (βCtx ∣ (bind 0 0 ∷ []) ⊢ tail (seal zero) ∶ `ℕ ⇝ ` zero)
¬β-seal (conv-tail (conv-seal d (iu-there ())))

-- run P's CancelR, as a composition: the identity at X's rep
_ : (βCtx ⊢ tail (seal 0) ⨟ unseal 0) ≡ ⌞ id `ℕ ⌟
_ = refl

-- run K's alias: two seals chain, the identity middle stays implicit
_ : (βCtx ⊢ tail (seal 1) ⨟ tail (seal 0)) ≡ tail (seal 1 ⨾seal 0)
_ = refl

-- an identity middle absorbs into a seal: run B's `(id ℕ ↦ id ℕ) ; seal Y`
_ : (βCtx ⊢ ⌞ ⌞ id `ℕ ⌟ ↦ ⌞ id `ℕ ⌟ ⌟ ⨟ tail (seal 0)) ≡ tail (seal 0)
_ = refl

-- unseal then reseal the same name cancels to the identity at the name
_ : (βCtx ⊢ unseal 0 ⨟ tail (seal 0)) ≡ ⌞ id (` 0) ⌟
_ = refl

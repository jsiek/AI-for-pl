module strong-rep-nu.Conversion where

-- File Charter:
--   * CONVERSIONS, the `c` of a boundary `M ⟪ Θ , c ⟫`, as NORMAL
--     FORMS in three sorts (notes/MergeSketch.md): §1 the grammar —
--     a structural middle `Mid`, a seal chain `Tail` (associates
--     LEFT), an unseal chain `Conv` (associates RIGHT) — with renaming,
--     §1b the syntactic identity `IsId` and the `NoCancel` side
--     condition, §2 the three typing judgements with NO polarity
--     index, §2b the weakening relation `SameConv`, §2c weakening
--     across a crossing, §2d representation renaming, §3 `mkId`,
--     §4 `reveal`/`conceal`, §4b COMPOSITION `Δ ⊢ c₁ ⨟ c₂`, §5 the
--     inversions, §6 `conv-types-unique`, §7 concrete checks.
--   * CONVERSIONS ARE REP-FREE.  `seal` and `unseal` carry an ordinary
--     type-variable NAME, never a representation spelling; the lookup
--     square `Δ ∋ X := A` follows that name to its representation.
--     Composition reads that square too (`repOf`), which is why it
--     takes the context.
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
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans; cong₂; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ; extᵗ;
         ⇑ᵗ)
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
    α : RVar
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
-- 2.  Typing — one judgement per sort, no polarity index
------------------------------------------------------------------------

-- Δ ⊢ c ∶ A ⇝ B — c converts the SOURCE type A to the TARGET type B,
-- all read on the CONVERSION CONTEXT Δ.  `conv-fun` is CONTRAVARIANT
-- in its domain.
-- Commentary.md § Conversion.agda / §2
infix 4 _⊢ᵐ_∶_⇝_ _⊢ᵀ_∶_⇝_ _⊢_∶_⇝_

mutual
  data _⊢ᵐ_∶_⇝_ : Ctxᵗ → Mid → Ty → Ty → Set where
    conv-id : Base A
        --------------------------------
      → Δ ⊢ᵐ id A ∶ A ⇝ A

    conv-idv : Δ ∋tv X
        --------------------------------
      → Δ ⊢ᵐ id (` X) ∶ ` X ⇝ ` X

    conv-fun : Δ ⊢ s ∶ A′ ⇝ A → Δ ⊢ c ∶ B ⇝ B′
        ----------------------------------------------
      → Δ ⊢ᵐ s ↦ c ∶ (A ⇒ B) ⇝ (A′ ⇒ B′)

    conv-all : underΛ Δ ⊢ s ∶ A ⇝ B
        --------------------------------------
      → Δ ⊢ᵐ `∀ s ∶ `∀ A ⇝ `∀ B

  data _⊢ᵀ_∶_⇝_ : Ctxᵗ → Tail → Ty → Ty → Set where
    conv-mid : Δ ⊢ᵐ g ∶ A ⇝ B
        --------------------------------
      → Δ ⊢ᵀ mid g ∶ A ⇝ B

    -- CONCEAL: the interior sees the rep, the exterior the name.
    -- THE SOUNDNESS GATE: a seal must cite a LIVE BINDER.
    conv-seal : Δ ∋ X := R
        --------------------------------
      → Δ ⊢ᵀ seal X ∶ R ⇝ ` X

    conv-seal-seq : Δ ⊢ᵀ t ∶ A ⇝ R → Δ ∋ X := R → ¬ IsIdᵀ t
        --------------------------------
      → Δ ⊢ᵀ t ⨾seal X ∶ A ⇝ ` X

  data _⊢_∶_⇝_ : Ctxᵗ → Conv → Ty → Ty → Set where
    conv-tail : Δ ⊢ᵀ t ∶ A ⇝ B
        --------------------------------
      → Δ ⊢ tail t ∶ A ⇝ B

    -- REVEAL: the interior sees the name, the exterior its rep.
    conv-unseal : Δ ∋ X := R
        --------------------------------
      → Δ ⊢ unseal X ∶ ` X ⇝ R

    conv-unseal-seq : Δ ∋ X := R → Δ ⊢ c ∶ R ⇝ B
      → ¬ IsIdᶜ c → NoCancel X c
        --------------------------------
      → Δ ⊢ unseal X ⨾ c ∶ ` X ⇝ B

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

-- It determines the spelling, so a rule carrying it stays a function.
mutual
  sameᵐ-rep-unique : ∀ {g₁ g₂} → η ⊩ᵐ g ~ g₁ → η ⊩ᵐ g ~ g₂ → g₁ ≡ g₂
  sameᵐ-rep-unique (sameᶜ-id a) (sameᶜ-id a′) =
    cong id (same-rep-unique a a′)
  sameᵐ-rep-unique (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
    cong₂ _↦_ (sameᶜ-rep-unique a a′) (sameᶜ-rep-unique b b′)
  sameᵐ-rep-unique (sameᶜ-all a) (sameᶜ-all a′) =
    cong `∀ (sameᶜ-rep-unique a a′)

  sameᵀ-rep-unique : ∀ {t₁ t₂} → η ⊩ᵀ t ~ t₁ → η ⊩ᵀ t ~ t₂ → t₁ ≡ t₂
  sameᵀ-rep-unique (sameᶜ-mid a) (sameᶜ-mid a′) =
    cong mid (sameᵐ-rep-unique a a′)
  sameᵀ-rep-unique (sameᶜ-seal d) (sameᶜ-seal d′) =
    cong seal (∋ˡ-det d d′)
  sameᵀ-rep-unique (sameᶜ-seal-seq a d) (sameᶜ-seal-seq a′ d′) =
    cong₂ _⨾seal_ (sameᵀ-rep-unique a a′) (∋ˡ-det d d′)

  sameᶜ-rep-unique : ∀ {c₁ c₂} → η ⊩ c ~ c₁ → η ⊩ c ~ c₂ → c₁ ≡ c₂
  sameᶜ-rep-unique (sameᶜ-tail a) (sameᶜ-tail a′) =
    cong tail (sameᵀ-rep-unique a a′)
  sameᶜ-rep-unique (sameᶜ-unseal d) (sameᶜ-unseal d′) =
    cong unseal (∋ˡ-det d d′)
  sameᶜ-rep-unique (sameᶜ-unseal-seq d a) (sameᶜ-unseal-seq d′ a′) =
    cong₂ unseal_⨾_ (∋ˡ-det d d′) (sameᶜ-rep-unique a a′)

mutual
  sameᵐ-target-unique : ∀ {g₁ g₂} → Unique η
    → η ⊩ᵐ g₁ ~ g → η ⊩ᵐ g₂ ~ g → g₁ ≡ g₂
  sameᵐ-target-unique uq (sameᶜ-id a) (sameᶜ-id a′) =
    cong id (same-target-unique uq a a′)
  sameᵐ-target-unique uq (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
    cong₂ _↦_ (sameᶜ-target-unique uq a a′)
              (sameᶜ-target-unique uq b b′)
  sameᵐ-target-unique uq (sameᶜ-all a) (sameᶜ-all a′) =
    cong `∀ (sameᶜ-target-unique
               (unique∷ fresh-zero-shift (unique-shift uq)) a a′)

  sameᵀ-target-unique : ∀ {t₁ t₂} → Unique η
    → η ⊩ᵀ t₁ ~ t → η ⊩ᵀ t₂ ~ t → t₁ ≡ t₂
  sameᵀ-target-unique uq (sameᶜ-mid a) (sameᶜ-mid a′) =
    cong mid (sameᵐ-target-unique uq a a′)
  sameᵀ-target-unique uq (sameᶜ-seal d) (sameᶜ-seal d′) =
    cong seal (unique-lookup uq d d′)
  sameᵀ-target-unique uq (sameᶜ-seal-seq a d) (sameᶜ-seal-seq a′ d′) =
    cong₂ _⨾seal_ (sameᵀ-target-unique uq a a′) (unique-lookup uq d d′)

  sameᶜ-target-unique : ∀ {c₁ c₂} → Unique η
    → η ⊩ c₁ ~ c → η ⊩ c₂ ~ c → c₁ ≡ c₂
  sameᶜ-target-unique uq (sameᶜ-tail a) (sameᶜ-tail a′) =
    cong tail (sameᵀ-target-unique uq a a′)
  sameᶜ-target-unique uq (sameᶜ-unseal d) (sameᶜ-unseal d′) =
    cong unseal (unique-lookup uq d d′)
  sameᶜ-target-unique uq (sameᶜ-unseal-seq d a) (sameᶜ-unseal-seq d′ a′) =
    cong₂ unseal_⨾_ (unique-lookup uq d d′) (sameᶜ-target-unique uq a a′)

-- `Peel`'s determinism case, in the shape `sameTy-src-unique` has.
sameConv-src-unique : Unique η
  → ∃[ r ] ((η ⊩ s ~ r) × (η′ ⊩ c ~ r))
  → ∃[ r ] ((η ⊩ s′ ~ r) × (η′ ⊩ c ~ r))
  → s ≡ s′
sameConv-src-unique uq (r , p , q) (r′ , p′ , q′)
  with sameᶜ-rep-unique q q′
sameConv-src-unique uq (r , p , q) (r′ , p′ , q′) | refl =
  sameᶜ-target-unique uq p p′

sameConv-∀ : ∀ {Γ Γ′ : Ctxᵗ}
  → SameConv (underΛ Γ) s (underΛ Γ′) s′
  → SameConv Γ ⌞ `∀ s ⌟ Γ′ ⌞ `∀ s′ ⌟
sameConv-∀ (r , p , q) =
  ⌞ `∀ r ⌟ , sameᶜ-tail (sameᶜ-mid (sameᶜ-all p))
           , sameᶜ-tail (sameᶜ-mid (sameᶜ-all q))

------------------------------------------------------------------------
-- 2c. Weakening a conversion across a boundary scope crossing
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
  weakenᵐ : ∀ {g₀} → η ⊆ᵃ η′ → η ⊩ᵐ g ~ g₀ → ∃[ g′ ] (η′ ⊩ᵐ g′ ~ g₀)
  weakenᵐ f (sameᶜ-id a) with weaken-ty f a
  weakenᵐ f (sameᶜ-id a) | A′ , a′ = id A′ , sameᶜ-id a′
  weakenᵐ f (sameᶜ-fun a b) with weaken f a
  weakenᵐ f (sameᶜ-fun a b) | s₁ , a′ with weaken f b
  weakenᵐ f (sameᶜ-fun a b) | s₁ , a′ | s₂ , b′ =
    s₁ ↦ s₂ , sameᶜ-fun a′ b′
  weakenᵐ f (sameᶜ-all a) with weaken (⊆ᵃ-underΛ f) a
  weakenᵐ f (sameᶜ-all a) | s₁ , a′ = `∀ s₁ , sameᶜ-all a′

  weakenᵀ : ∀ {t₀} → η ⊆ᵃ η′ → η ⊩ᵀ t ~ t₀ → ∃[ t′ ] (η′ ⊩ᵀ t′ ~ t₀)
  weakenᵀ f (sameᶜ-mid a) with weakenᵐ f a
  weakenᵀ f (sameᶜ-mid a) | g′ , a′ = mid g′ , sameᶜ-mid a′
  weakenᵀ f (sameᶜ-seal d) with f (_ , d)
  weakenᵀ f (sameᶜ-seal d) | X , d′ = seal X , sameᶜ-seal d′
  weakenᵀ f (sameᶜ-seal-seq a d) with weakenᵀ f a | f (_ , d)
  weakenᵀ f (sameᶜ-seal-seq a d) | t′ , a′ | X , d′ =
    t′ ⨾seal X , sameᶜ-seal-seq a′ d′

  weaken : ∀ {c₀} → η ⊆ᵃ η′ → η ⊩ c ~ c₀ → ∃[ c′ ] (η′ ⊩ c′ ~ c₀)
  weaken f (sameᶜ-tail a) with weakenᵀ f a
  weaken f (sameᶜ-tail a) | t′ , a′ = tail t′ , sameᶜ-tail a′
  weaken f (sameᶜ-unseal d) with f (_ , d)
  weaken f (sameᶜ-unseal d) | X , d′ = unseal X , sameᶜ-unseal d′
  weaken f (sameᶜ-unseal-seq d a) with f (_ , d) | weaken f a
  weaken f (sameᶜ-unseal-seq d a) | X , d′ | c′ , a′ =
    unseal X ⨾ c′ , sameᶜ-unseal-seq d′ a′

mutual
  readableᵐ : ∀ {Γ : Ctxᵗ} → Γ ⊢ᵐ g ∶ A ⇝ B → ∃[ r ] (names Γ ⊩ᵐ g ~ r)
  readableᵐ (conv-id base-ℕ) = id `ℕ , sameᶜ-id same-ℕ
  readableᵐ (conv-id base-𝔹) = id `𝔹 , sameᶜ-id same-𝔹
  readableᵐ (conv-idv (α , d)) = id (` α) , sameᶜ-id (same-var d)
  readableᵐ (conv-fun a b) with readable a
  readableᵐ (conv-fun a b) | r₁ , a′ with readable b
  readableᵐ (conv-fun a b) | r₁ , a′ | r₂ , b′ =
    r₁ ↦ r₂ , sameᶜ-fun a′ b′
  readableᵐ (conv-all a) with readable a
  readableᵐ (conv-all a) | r₁ , a′ = `∀ r₁ , sameᶜ-all a′

  readableᵀ : ∀ {Γ : Ctxᵗ} → Γ ⊢ᵀ t ∶ A ⇝ B → ∃[ r ] (names Γ ⊩ᵀ t ~ r)
  readableᵀ (conv-mid a) with readableᵐ a
  readableᵀ (conv-mid a) | r , a′ = mid r , sameᶜ-mid a′
  readableᵀ (conv-seal (α , R , d , rd , sm)) = seal α , sameᶜ-seal d
  readableᵀ (conv-seal-seq a (α , R , d , rd , sm) ¬id) with readableᵀ a
  readableᵀ (conv-seal-seq a (α , R , d , rd , sm) ¬id) | r , a′ =
    r ⨾seal α , sameᶜ-seal-seq a′ d

  readable : ∀ {Γ : Ctxᵗ} → Γ ⊢ c ∶ A ⇝ B → ∃[ r ] (names Γ ⊩ c ~ r)
  readable (conv-tail a) with readableᵀ a
  readable (conv-tail a) | r , a′ = tail r , sameᶜ-tail a′
  readable (conv-unseal (α , R , d , rd , sm)) = unseal α , sameᶜ-unseal d
  readable (conv-unseal-seq (α , R , d , rd , sm) a ¬id nc)
    with readable a
  readable (conv-unseal-seq (α , R , d , rd , sm) a ¬id nc) | r , a′ =
    unseal α ⨾ r , sameᶜ-unseal-seq d a′

premise-exists : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ
  → Γᶜ ⊢ s ∶ A ⇝ B
  → ∃[ s′ ] SameConv Γᵈ s′ Γᶜ s
premise-exists int conv dconv ⊢s with readable ⊢s
premise-exists int conv dconv ⊢s | r , rd
  with weaken (Q int conv dconv) rd
premise-exists int conv dconv ⊢s | r , rd | s′ , rd′ =
  s′ , (r , rd′ , rd)

peel-premises : ∀ {Γ Γᵢ Γᶜ : Ctxᵗ} {Θ : Boundary}
  → Unique (names Γ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᶜ ⊢ s ∶ A ⇝ B
  → ∃[ Γᵈ ] ∃[ s′ ]
      ((Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ) × SameConv Γᵈ s′ Γᶜ s)
peel-premises uq int conv ⊢s with dual-conversion-exists uq int
peel-premises uq int conv ⊢s | Γᵈ , dconv
  with premise-exists int conv dconv ⊢s
peel-premises uq int conv ⊢s | Γᵈ , dconv | s′ , sc =
  Γᵈ , s′ , dconv , sc

peel-premises-env : ∀ {Γ Γᵢ Γᶜ : Ctxᵗ} {Θ : Boundary}
  → BoundaryWf Γ Θ Γᵢ Γᶜ
  → Γᶜ ⊢ s ∶ A ⇝ B
  → ∃[ Γᵈ ] ∃[ s′ ]
      ((Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ) × SameConv Γᵈ s′ Γᶜ s)
peel-premises-env mwΘ ⊢s =
  peel-premises (name-fn (bw-exterior mwΘ)) (bw-interior mwΘ)
                (bw-conversion mwΘ) ⊢s

------------------------------------------------------------------------
-- 2d. Renaming the representation universe
------------------------------------------------------------------------

-- A conversion and both of its types survive a representation-only
-- renaming UNCHANGED; what moves is the context it is read on.
-- Commentary.md § Conversion.agda / §2d

conv-cast : ∀ {Ξ : RepCtx} → η ≡ η′
  → (Ξ ∣ η) ⊢ c ∶ A ⇝ B → (Ξ ∣ η′) ⊢ c ∶ A ⇝ B
conv-cast refl ⊢c = ⊢c

mutual
  convᵐ-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
    → (Ξ ∣ η) ⊢ᵐ g ∶ A ⇝ B
    → (Ξ′ ∣ map ρ η) ⊢ᵐ g ∶ A ⇝ B
  convᵐ-ren w (conv-id b) = conv-id b
  convᵐ-ren {ρ = ρ} w (conv-idv tv) = conv-idv (tv-ren ρ tv)
  convᵐ-ren w (conv-fun p q) = conv-fun (conv-ren w p) (conv-ren w q)
  convᵐ-ren {ρ = ρ} {η = η} w (conv-all p) =
    conv-all (conv-cast (names-underΛ-ren ρ η)
                        (conv-ren (repwk-abst w) p))

  convᵀ-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
    → (Ξ ∣ η) ⊢ᵀ t ∶ A ⇝ B
    → (Ξ′ ∣ map ρ η) ⊢ᵀ t ∶ A ⇝ B
  convᵀ-ren w (conv-mid p) = conv-mid (convᵐ-ren w p)
  convᵀ-ren w (conv-seal d) = conv-seal (∋:=-ren w d)
  convᵀ-ren w (conv-seal-seq p d ¬id) =
    conv-seal-seq (convᵀ-ren w p) (∋:=-ren w d) ¬id

  conv-ren : ∀ {Ξ Ξ′ : RepCtx} → RepWk ρ Ξ Ξ′
    → (Ξ ∣ η) ⊢ c ∶ A ⇝ B
    → (Ξ′ ∣ map ρ η) ⊢ c ∶ A ⇝ B
  conv-ren w (conv-tail p) = conv-tail (convᵀ-ren w p)
  conv-ren w (conv-unseal d) = conv-unseal (∋:=-ren w d)
  conv-ren w (conv-unseal-seq d p ¬id nc) =
    conv-unseal-seq (∋:=-ren w d) (conv-ren w p) ¬id nc

------------------------------------------------------------------------
-- 3.  The identity conversion at an arbitrary type
------------------------------------------------------------------------

mkId : Ty → Conv
mkId (` X)   = ⌞ id (` X) ⌟
mkId `ℕ      = ⌞ id `ℕ ⌟
mkId `𝔹      = ⌞ id `𝔹 ⌟
mkId (A ⇒ B) = ⌞ mkId A ↦ mkId B ⌟
mkId (`∀ A)  = ⌞ `∀ (mkId A) ⌟

mkId-⊢ : Δ ⊢ᵗ A → Δ ⊢ mkId A ∶ A ⇝ A
mkId-⊢ (wf-var tv)  = conv-tail (conv-mid (conv-idv tv))
mkId-⊢ wf-ℕ         = conv-tail (conv-mid (conv-id base-ℕ))
mkId-⊢ wf-𝔹         = conv-tail (conv-mid (conv-id base-𝔹))
mkId-⊢ (wf-⇒ wA wB) = conv-tail (conv-mid (conv-fun (mkId-⊢ wA) (mkId-⊢ wB)))
mkId-⊢ (wf-∀ wA)    = conv-tail (conv-mid (conv-all (mkId-⊢ wA)))

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
seal-source-is-rep : Δ ⊢ tail (seal X) ∶ A ⇝ B → Δ ∋ X := A
seal-source-is-rep (conv-tail (conv-seal d)) = d

unseal-target-is-rep : Δ ⊢ unseal X ∶ A ⇝ B → Δ ∋ X := B
unseal-target-is-rep (conv-unseal d) = d

conv-unseal-src : Δ ⊢ unseal X ∶ A ⇝ B → A ≡ ` X
conv-unseal-src (conv-unseal _) = refl

conv-seal-tgt : Δ ⊢ tail (seal X) ∶ A ⇝ B → B ≡ ` X
conv-seal-tgt (conv-tail (conv-seal _)) = refl

conv-idv-src : Δ ⊢ ⌞ id (` X) ⌟ ∶ A ⇝ B → A ≡ ` X
conv-idv-src (conv-tail (conv-mid (conv-idv _))) = refl

conv-idv-tgt : Δ ⊢ ⌞ id (` X) ⌟ ∶ A ⇝ B → B ≡ ` X
conv-idv-tgt (conv-tail (conv-mid (conv-idv _))) = refl

conv-id-base-src : Base A → Δ ⊢ ⌞ id A ⌟ ∶ B ⇝ C → B ≡ A
conv-id-base-src bA (conv-tail (conv-mid (conv-id _)))  = refl
conv-id-base-src () (conv-tail (conv-mid (conv-idv _)))

conv-id-refl : Δ ⊢ ⌞ id A ⌟ ∶ B ⇝ C → B ≡ C
conv-id-refl (conv-tail (conv-mid (conv-id _)))  = refl
conv-id-refl (conv-tail (conv-mid (conv-idv _))) = refl

-- A ∀ conversion's body, as an inversion returning the two `∀` shapes
-- AS EQUATIONS: at the use sites `env` constrains the conversion's
-- types only relationally, so `conv-all` does not unify directly.
-- Commentary.md § Conversion.agda / §5
conv-all-inv : Δ ⊢ ⌞ `∀ s ⌟ ∶ A ⇝ B
  → Σ[ A₀ ∈ Ty ] Σ[ B₀ ∈ Ty ]
      ((A ≡ `∀ A₀) ×
       (B ≡ `∀ B₀) ×
       (underΛ Δ ⊢ s ∶ A₀ ⇝ B₀))
conv-all-inv (conv-tail (conv-mid (conv-all ⊢s))) =
  _ , _ , refl , refl , ⊢s

conv-fun-inv : Δ ⊢ ⌞ s ↦ c ⌟ ∶ A ⇝ B
  → Σ[ A₁ ∈ Ty ] Σ[ B₁ ∈ Ty ] Σ[ A₂ ∈ Ty ] Σ[ B₂ ∈ Ty ]
      ((A ≡ A₁ ⇒ B₁) ×
       (B ≡ A₂ ⇒ B₂) ×
       (Δ ⊢ s ∶ A₂ ⇝ A₁) ×
       (Δ ⊢ c ∶ B₁ ⇝ B₂))
conv-fun-inv (conv-tail (conv-mid (conv-fun ⊢s ⊢c))) =
  _ , _ , _ , _ , refl , refl , ⊢s , ⊢c

------------------------------------------------------------------------
-- 6. Conversion types are unique on a well-formed name map
------------------------------------------------------------------------

-- The premise is the invariant used at `seal` and `unseal`: one
-- representation variable has at most one ordinary name.
mutual
  convᵐ-types-unique : Unique (names Δ)
    → Δ ⊢ᵐ g ∶ A ⇝ B → Δ ⊢ᵐ g ∶ A′ ⇝ B′ → (A ≡ A′) × (B ≡ B′)
  convᵐ-types-unique uq (conv-id b) (conv-id b′) = refl , refl
  convᵐ-types-unique uq (conv-id ()) (conv-idv tv′)
  convᵐ-types-unique uq (conv-idv tv) (conv-id ())
  convᵐ-types-unique uq (conv-idv tv) (conv-idv tv′) = refl , refl
  convᵐ-types-unique uq (conv-fun s t) (conv-fun s′ t′)
    with conv-types-unique uq s s′ | conv-types-unique uq t t′
  ... | refl , refl | refl , refl = refl , refl
  convᵐ-types-unique {Δ = Δ} uq (conv-all s) (conv-all s′)
    with conv-types-unique (unique-underΛ {Γ = Δ} uq) s s′
  ... | refl , refl = refl , refl

  convᵀ-types-unique : Unique (names Δ)
    → Δ ⊢ᵀ t ∶ A ⇝ B → Δ ⊢ᵀ t ∶ A′ ⇝ B′ → (A ≡ A′) × (B ≡ B′)
  convᵀ-types-unique uq (conv-mid p) (conv-mid p′) =
    convᵐ-types-unique uq p p′
  convᵀ-types-unique uq (conv-seal d) (conv-seal d′) =
    ∋:=-det uq d d′ , refl
  convᵀ-types-unique uq (conv-seal-seq p d n) (conv-seal-seq p′ d′ n′)
    with convᵀ-types-unique uq p p′
  ... | refl , _ = refl , refl

  conv-types-unique : Unique (names Δ)
    → Δ ⊢ c ∶ A ⇝ B → Δ ⊢ c ∶ A′ ⇝ B′ → (A ≡ A′) × (B ≡ B′)
  conv-types-unique uq (conv-tail p) (conv-tail p′) =
    convᵀ-types-unique uq p p′
  conv-types-unique uq (conv-unseal d) (conv-unseal d′) =
    refl , ∋:=-det uq d d′
  conv-types-unique uq (conv-unseal-seq d p n m)
                       (conv-unseal-seq d′ p′ n′ m′)
    with ∋:=-det uq d d′
  ... | refl with conv-types-unique uq p p′
  ...   | _ , refl = refl , refl

conv-src-unique : Unique (names Δ)
  → Δ ⊢ c ∶ A ⇝ B → Δ ⊢ c ∶ A′ ⇝ B′ → A ≡ A′
conv-src-unique uq ⊢c ⊢c′ with conv-types-unique uq ⊢c ⊢c′
... | eq , _ = eq

------------------------------------------------------------------------
-- 7. Concrete lookup-square and composition checks
------------------------------------------------------------------------

βCtx : Ctxᵗ
βCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

β-lookup : βCtx ∋ zero := `ℕ
β-lookup = zero , `ℕ , here , r-here , same-ℕ

β-unseal : βCtx ⊢ unseal zero ∶ ` zero ⇝ `ℕ
β-unseal = conv-unseal β-lookup

β-seal : βCtx ⊢ tail (seal zero) ∶ `ℕ ⇝ ` zero
β-seal = conv-tail (conv-seal β-lookup)

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

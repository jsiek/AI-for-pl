module strong-rep-store.Conversion where

-- File Charter:
--   * CONVERSIONS, the `c` of a boundary `M ⟪ Θ , c ⟫`: §1 the grammar
--     (`id`/`seal`/`unseal`/`_↦_`/`` `∀ ``, the names are GTSF's),
--     §2 the typing judgement `Δ ⊢ c ∶ A ⇝ B` with NO polarity index,
--     §2b the re-spelling relation `SameConv`, §2c re-spelling across
--     a crossing, §2d representation renaming, §3 `mkId`, §4 the
--     canonical mints at a slot, §5 the inversions,
--     §6 `conv-types-unique`, §7 concrete lookup-square checks.
--   * CONVERSIONS ARE REP-FREE.  `seal` and `unseal` carry an ordinary
--     type-variable NAME, never a representation spelling; the lookup
--     square `Δ ∋ X := A` follows that name to its representation
--     variable.  Hence a representation-only renaming leaves a
--     conversion and both of its types UNCHANGED (§2d).
-- Commentary: Commentary.md § Conversion.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; cong₂; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ; extᵗ;
         ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Boundary

private
  variable
    Δ Δ′ : Ctxᵗ
    η η′ : TyCtx
    A A′ B B′ R : Ty
    X Y : ℕ
    α : RVar
    ρ : Renameᵗ

-- `id A` is restricted to BASE TYPES AND VARIABLES by the typing
-- judgment (conv-id / conv-idv); compound identities stay structural
-- (`mkId`, §3).
data Conv : Set where
  id     : Ty → Conv          -- ACTIVE at a base type, INERT at a variable
  seal   : ℕ → Conv           -- seal   at the binder named       INERT
  unseal : ℕ → Conv           -- unseal at the binder named       ACTIVE
  _↦_    : Conv → Conv → Conv -- s ↦ t, contravariant domain      INERT
  `∀     : Conv → Conv        -- ∀ s                              INERT

infixr 7 _↦_

private
  variable
    s t s′ r u : Conv

renᶜ : Renameᵗ → Conv → Conv
renᶜ ρ (id A)      = id (renameᵗ ρ A)
renᶜ ρ (seal X)    = seal (ρ X)
renᶜ ρ (unseal X)  = unseal (ρ X)
renᶜ ρ (s ↦ t)     = renᶜ ρ s ↦ renᶜ ρ t
renᶜ ρ (`∀ s)      = `∀ (renᶜ (extᵗ ρ) s)

-- Δ ⊢ c ∶ A ⇝ B — c converts the SOURCE type A to the TARGET type B,
-- both read on the CONVERSION CONTEXT Δ.  `conv-fun` is CONTRAVARIANT
-- in its domain — the only trace the retired polarity index leaves.
-- Commentary.md § Conversion.agda / §2
infix 4 _⊢_∶_⇝_
data _⊢_∶_⇝_ : Ctxᵗ → Conv → Ty → Ty → Set where

  conv-id : Base A
      --------------------------------
    → Δ ⊢ id A ∶ A ⇝ A

  conv-idv : Δ ∋tv X
      --------------------------------
    → Δ ⊢ id (` X) ∶ ` X ⇝ ` X

  -- REVEAL: the interior sees the abstract name, the exterior its rep.
  conv-unseal : Δ ∋ X := A
      --------------------------------
    → Δ ⊢ unseal X ∶ ` X ⇝ A

  -- CONCEAL: the interior sees the rep, the exterior the abstract name.
  -- THE SOUNDNESS GATE: a seal must cite a LIVE BINDER on its type context.
  conv-seal : Δ ∋ X := A
      --------------------------------
    → Δ ⊢ seal X ∶ A ⇝ ` X

  conv-fun : ∀ {s t}
    → Δ ⊢ s ∶ A′ ⇝ A → Δ ⊢ t ∶ B ⇝ B′
      ----------------------------------------------
    → Δ ⊢ s ↦ t ∶ (A ⇒ B) ⇝ (A′ ⇒ B′)

  conv-all : ∀ {s} → underΛ Δ ⊢ s ∶ A ⇝ B
      --------------------------------------
    → Δ ⊢ `∀ s ∶ `∀ A ⇝ `∀ B

------------------------------------------------------------------------
-- 2b.  Two spellings of one conversion
------------------------------------------------------------------------

-- `SameConv` is `_⊢_≈_⊣_` (strong-rep-store.Ctx §5) for a CONVERSION:
-- a conversion mentions ordinary names at exactly three leaves, so the
-- judgement is `_⊢_~_` one universe up, structural everywhere else.
-- Commentary.md § Conversion.agda / §2b
infix 4 _⊩_~_
data _⊩_~_ (η : TyCtx) : Conv → Conv → Set where
  sameᶜ-id     : η ⊢ A ~ R → η ⊩ id A ~ id R
  sameᶜ-seal   : η ∋ˡ X := α → η ⊩ seal X ~ seal α
  sameᶜ-unseal : η ∋ˡ X := α → η ⊩ unseal X ~ unseal α
  sameᶜ-fun    : η ⊩ s ~ r → η ⊩ t ~ u → η ⊩ s ↦ t ~ r ↦ u
  sameᶜ-all    : (zero ∷ shiftReps η) ⊩ s ~ r → η ⊩ `∀ s ~ `∀ r

sameᶜ-cast : ∀ {η η′ : TyCtx} → η ≡ η′ → η ⊩ s ~ r → η′ ⊩ s ~ r
sameᶜ-cast refl p = p

sameᶜ-ren : (ρ : Renameᵗ) → η ⊩ s ~ r → map ρ η ⊩ s ~ renᶜ ρ r
sameᶜ-ren ρ (sameᶜ-id p) = sameᶜ-id (same-ren ρ p)
sameᶜ-ren ρ (sameᶜ-seal d) = sameᶜ-seal (∋ˡ-ren ρ d)
sameᶜ-ren ρ (sameᶜ-unseal d) = sameᶜ-unseal (∋ˡ-ren ρ d)
sameᶜ-ren ρ (sameᶜ-fun p q) =
  sameᶜ-fun (sameᶜ-ren ρ p) (sameᶜ-ren ρ q)
sameᶜ-ren {η = η} ρ (sameᶜ-all p) =
  sameᶜ-all
    (sameᶜ-cast (names-underΛ-ren ρ η) (sameᶜ-ren (extᵗ ρ) p))

SameConv : Ctxᵗ → Conv → Ctxᵗ → Conv → Set
SameConv Γ s Γ′ s′ = ∃[ r ] ((names Γ ⊩ s ~ r) × (names Γ′ ⊩ s′ ~ r))

-- It determines the spelling, so a rule carrying it stays a function.
sameᶜ-rep-unique : η ⊩ s ~ r → η ⊩ s ~ u → r ≡ u
sameᶜ-rep-unique (sameᶜ-id a) (sameᶜ-id a′) =
  cong id (same-rep-unique a a′)
sameᶜ-rep-unique (sameᶜ-seal d) (sameᶜ-seal d′) =
  cong seal (∋ˡ-det d d′)
sameᶜ-rep-unique (sameᶜ-unseal d) (sameᶜ-unseal d′) =
  cong unseal (∋ˡ-det d d′)
sameᶜ-rep-unique (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
  cong₂ _↦_ (sameᶜ-rep-unique a a′) (sameᶜ-rep-unique b b′)
sameᶜ-rep-unique (sameᶜ-all a) (sameᶜ-all a′) =
  cong `∀ (sameᶜ-rep-unique a a′)

sameᶜ-target-unique : Unique η → η ⊩ s ~ r → η ⊩ s′ ~ r → s ≡ s′
sameᶜ-target-unique uq (sameᶜ-id a) (sameᶜ-id a′) =
  cong id (same-target-unique uq a a′)
sameᶜ-target-unique uq (sameᶜ-seal d) (sameᶜ-seal d′) =
  cong seal (unique-lookup uq d d′)
sameᶜ-target-unique uq (sameᶜ-unseal d) (sameᶜ-unseal d′) =
  cong unseal (unique-lookup uq d d′)
sameᶜ-target-unique uq (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
  cong₂ _↦_ (sameᶜ-target-unique uq a a′)
            (sameᶜ-target-unique uq b b′)
sameᶜ-target-unique uq (sameᶜ-all a) (sameᶜ-all a′) =
  cong `∀ (sameᶜ-target-unique
             (unique∷ fresh-zero-shift (unique-shift uq)) a a′)

-- `Peel`'s determinism case, in the shape `sameTy-src-unique` has.
sameConv-src-unique : Unique η
  → ∃[ r ] ((η ⊩ s ~ r) × (η′ ⊩ t ~ r))
  → ∃[ r ] ((η ⊩ s′ ~ r) × (η′ ⊩ t ~ r))
  → s ≡ s′
sameConv-src-unique uq (r , p , q) (r′ , p′ , q′)
  with sameᶜ-rep-unique q q′
sameConv-src-unique uq (r , p , q) (r′ , p′ , q′) | refl =
  sameᶜ-target-unique uq p p′

sameConv-∀ : ∀ {Γ Γ′ : Ctxᵗ}
  → SameConv (underΛ Γ) s (underΛ Γ′) s′
  → SameConv Γ (`∀ s) Γ′ (`∀ s′)
sameConv-∀ (r , p , q) = `∀ r , sameᶜ-all p , sameᶜ-all q

------------------------------------------------------------------------
-- 2c. Re-spelling a conversion across a boundary scope crossing
------------------------------------------------------------------------

-- `Q` and `dual-conversion-exists` live with the relational context
-- readings in strong-rep-store.Boundary; this section transports the
-- actual type and conversion spellings.
-- Commentary.md § Conversion.agda / §2c

respell-ty : η ⊆ᵃ η′ → η ⊢ A ~ R
  → ∃[ A′ ] (η′ ⊢ A′ ~ R)
respell-ty f (same-var d) with f (_ , d)
respell-ty f (same-var d) | X , d′ = ` X , same-var d′
respell-ty f same-ℕ = `ℕ , same-ℕ
respell-ty f same-𝔹 = `𝔹 , same-𝔹
respell-ty f (same-⇒ a b) with respell-ty f a
respell-ty f (same-⇒ a b) | A′ , a′ with respell-ty f b
respell-ty f (same-⇒ a b) | A′ , a′ | B′ , b′ =
  A′ ⇒ B′ , same-⇒ a′ b′
respell-ty f (same-∀ a) with respell-ty (⊆ᵃ-underΛ f) a
respell-ty f (same-∀ a) | A′ , a′ = `∀ A′ , same-∀ a′

respell : η ⊆ᵃ η′ → η ⊩ s ~ r → ∃[ s′ ] (η′ ⊩ s′ ~ r)
respell f (sameᶜ-id a) with respell-ty f a
respell f (sameᶜ-id a) | A′ , a′ = id A′ , sameᶜ-id a′
respell f (sameᶜ-seal d) with f (_ , d)
respell f (sameᶜ-seal d) | X , d′ = seal X , sameᶜ-seal d′
respell f (sameᶜ-unseal d) with f (_ , d)
respell f (sameᶜ-unseal d) | X , d′ = unseal X , sameᶜ-unseal d′
respell f (sameᶜ-fun a b) with respell f a
respell f (sameᶜ-fun a b) | s₁ , a′ with respell f b
respell f (sameᶜ-fun a b) | s₁ , a′ | s₂ , b′ =
  s₁ ↦ s₂ , sameᶜ-fun a′ b′
respell f (sameᶜ-all a) with respell (⊆ᵃ-underΛ f) a
respell f (sameᶜ-all a) | s₁ , a′ = `∀ s₁ , sameᶜ-all a′

readable : ∀ {Γ : Ctxᵗ} {c} → Γ ⊢ c ∶ A ⇝ B
  → ∃[ r ] (names Γ ⊩ c ~ r)
readable (conv-id base-ℕ) = id `ℕ , sameᶜ-id same-ℕ
readable (conv-id base-𝔹) = id `𝔹 , sameᶜ-id same-𝔹
readable (conv-idv (α , d)) = id (` α) , sameᶜ-id (same-var d)
readable (conv-unseal (α , R , d , rd , sm)) =
  unseal α , sameᶜ-unseal d
readable (conv-seal (α , R , d , rd , sm)) = seal α , sameᶜ-seal d
readable (conv-fun a b) with readable a
readable (conv-fun a b) | r₁ , a′ with readable b
readable (conv-fun a b) | r₁ , a′ | r₂ , b′ =
  r₁ ↦ r₂ , sameᶜ-fun a′ b′
readable (conv-all a) with readable a
readable (conv-all a) | r₁ , a′ = `∀ r₁ , sameᶜ-all a′

premise-exists : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ
  → Γᶜ ⊢ s ∶ A ⇝ B
  → ∃[ s′ ] SameConv Γᵈ s′ Γᶜ s
premise-exists int conv dconv ⊢s with readable ⊢s
premise-exists int conv dconv ⊢s | r , rd
  with respell (Q int conv dconv) rd
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

conv-cast : ∀ {Ξ : RepCtx} {c : Conv} → η ≡ η′
  → (Ξ ∣ η) ⊢ c ∶ A ⇝ B → (Ξ ∣ η′) ⊢ c ∶ A ⇝ B
conv-cast refl ⊢c = ⊢c

conv-ren : ∀ {Ξ Ξ′ : RepCtx} {c : Conv} → RepWk ρ Ξ Ξ′
  → (Ξ ∣ η) ⊢ c ∶ A ⇝ B
  → (Ξ′ ∣ map ρ η) ⊢ c ∶ A ⇝ B
conv-ren w (conv-id b) = conv-id b
conv-ren {ρ = ρ} w (conv-idv tv) = conv-idv (tv-ren ρ tv)
conv-ren w (conv-unseal d) = conv-unseal (∋:=-ren w d)
conv-ren w (conv-seal d) = conv-seal (∋:=-ren w d)
conv-ren w (conv-fun p q) = conv-fun (conv-ren w p) (conv-ren w q)
conv-ren {ρ = ρ} {η = η} w (conv-all p) =
  conv-all (conv-cast (names-underΛ-ren ρ η)
                      (conv-ren (repwk-abst w) p))

------------------------------------------------------------------------
-- 3.  The identity conversion at an arbitrary type
------------------------------------------------------------------------

mkId : Ty → Conv
mkId (` X)   = id (` X)
mkId `ℕ      = id `ℕ
mkId `𝔹      = id `𝔹
mkId (A ⇒ B) = mkId A ↦ mkId B
mkId (`∀ A)  = `∀ (mkId A)

mkId-⊢ : Δ ⊢ᵗ A → Δ ⊢ mkId A ∶ A ⇝ A
mkId-⊢ (wf-var tv)  = conv-idv tv
mkId-⊢ wf-ℕ         = conv-id base-ℕ
mkId-⊢ wf-𝔹         = conv-id base-𝔹
mkId-⊢ (wf-⇒ wA wB) = conv-fun (mkId-⊢ wA) (mkId-⊢ wB)
mkId-⊢ (wf-∀ wA)    = conv-all (mkId-⊢ wA)

------------------------------------------------------------------------
-- 4.  The canonical conversions at a slot
------------------------------------------------------------------------

-- Unseal every occurrence of X where the conversion runs covariantly,
-- seal it back where it runs contravariantly.  DERIVED FROM THE TYPE.
-- Commentary.md § Conversion.agda / §4
mutual
  reveal : ℕ → Ty → Conv
  reveal X (` Y) with X ≟ Y
  ... | yes _ = unseal X
  ... | no  _ = id (` Y)
  reveal X `ℕ      = id `ℕ
  reveal X `𝔹      = id `𝔹
  reveal X (A ⇒ B) = conceal X A ↦ reveal X B
  reveal X (`∀ A)  = `∀ (reveal (suc X) A)

  conceal : ℕ → Ty → Conv
  conceal X (` Y) with X ≟ Y
  ... | yes _ = seal X
  ... | no  _ = id (` Y)
  conceal X `ℕ      = id `ℕ
  conceal X `𝔹      = id `𝔹
  conceal X (A ⇒ B) = reveal X A ↦ conceal X B
  conceal X (`∀ A)  = `∀ (conceal (suc X) A)

-- THE SAME MINT, APPLIED TO A CONVERSION: each leaf of a `` `∀ ``
-- conversion that reads the newly bound slot 0 becomes the
-- instantiation step.
-- Commentary.md § Conversion.agda / §4
mutual
  instReveal : ℕ → Conv → Conv
  instReveal X (id A)     = reveal X A
  instReveal X (seal Y)   = seal Y
  instReveal X (unseal Y) = unseal Y
  instReveal X (s ↦ t)    = instConceal X s ↦ instReveal X t
  instReveal X (`∀ s)     = `∀ (instReveal (suc X) s)

  instConceal : ℕ → Conv → Conv
  instConceal X (id A)     = conceal X A
  instConceal X (seal Y)   = seal Y
  instConceal X (unseal Y) = unseal Y
  instConceal X (s ↦ t)    = instReveal X s ↦ instConceal X t
  instConceal X (`∀ s)     = `∀ (instConceal (suc X) s)

-- TyBeta's minted conversion IS this operation at an identity
-- conversion: the type version is the conversion version on `mkId`.
mutual
  instReveal-mkId : (X : ℕ) (B : Ty) → instReveal X (mkId B) ≡ reveal X B
  instReveal-mkId X (` Y)   = refl
  instReveal-mkId X `ℕ      = refl
  instReveal-mkId X `𝔹      = refl
  instReveal-mkId X (A ⇒ B) =
    cong₂ _↦_ (instConceal-mkId X A) (instReveal-mkId X B)
  instReveal-mkId X (`∀ A)  = cong `∀ (instReveal-mkId (suc X) A)

  instConceal-mkId : (X : ℕ) (B : Ty)
    → instConceal X (mkId B) ≡ conceal X B
  instConceal-mkId X (` Y)   = refl
  instConceal-mkId X `ℕ      = refl
  instConceal-mkId X `𝔹      = refl
  instConceal-mkId X (A ⇒ B) =
    cong₂ _↦_ (instReveal-mkId X A) (instConceal-mkId X B)
  instConceal-mkId X (`∀ A)  = cong `∀ (instConceal-mkId (suc X) A)

------------------------------------------------------------------------
-- 5. Conversion inversions
------------------------------------------------------------------------

-- Every rep a conversion mentions IS the binder's rep — there is no
-- second spelling.
seal-source-is-rep :
  Δ ⊢ seal X ∶ A ⇝ B → Δ ∋ X := A
seal-source-is-rep (conv-seal d) = d

unseal-target-is-rep :
  Δ ⊢ unseal X ∶ A ⇝ B → Δ ∋ X := B
unseal-target-is-rep (conv-unseal d) = d

conv-unseal-src : Δ ⊢ unseal X ∶ A ⇝ B → A ≡ ` X
conv-unseal-src (conv-unseal _) = refl

conv-seal-tgt : Δ ⊢ seal X ∶ A ⇝ B → B ≡ ` X
conv-seal-tgt (conv-seal _) = refl

conv-idv-src : Δ ⊢ id (` X) ∶ A ⇝ B → A ≡ ` X
conv-idv-src (conv-idv _) = refl

conv-idv-tgt : Δ ⊢ id (` X) ∶ A ⇝ B → B ≡ ` X
conv-idv-tgt (conv-idv _) = refl

conv-id-base-src : ∀ {C} → Base A → Δ ⊢ id A ∶ B ⇝ C → B ≡ A
conv-id-base-src bA (conv-id _)  = refl
conv-id-base-src () (conv-idv _)

conv-id-refl : ∀ {C} → Δ ⊢ id A ∶ B ⇝ C → B ≡ C
conv-id-refl (conv-id _)  = refl
conv-id-refl (conv-idv _) = refl

-- A ∀ conversion's body, as an inversion returning the two `∀` shapes
-- AS EQUATIONS: at the use sites `env` constrains the conversion's
-- types only relationally, so `conv-all` does not unify directly.
-- Commentary.md § Conversion.agda / §5
conv-all-inv : ∀ {s A B} → Δ ⊢ `∀ s ∶ A ⇝ B
  → Σ[ A₀ ∈ Ty ] Σ[ B₀ ∈ Ty ]
      ((A ≡ `∀ A₀) ×
       (B ≡ `∀ B₀) ×
       (underΛ Δ ⊢ s ∶ A₀ ⇝ B₀))
conv-all-inv (conv-all ⊢s) = _ , _ , refl , refl , ⊢s

------------------------------------------------------------------------
-- 6. Conversion types are unique on a well-formed name map
------------------------------------------------------------------------

-- The premise is the invariant used at `seal` and `unseal`: one
-- representation variable has at most one ordinary name.
conv-types-unique : ∀ {c A A′ B B′}
  → Unique (names Δ)
  → Δ ⊢ c ∶ A  ⇝ B
  → Δ ⊢ c ∶ A′ ⇝ B′
  → (A ≡ A′) × (B ≡ B′)
conv-types-unique unique (conv-id b) (conv-id b′) = refl , refl
conv-types-unique unique (conv-id ()) (conv-idv tv′)
conv-types-unique unique (conv-idv tv) (conv-id ())
conv-types-unique unique (conv-idv tv) (conv-idv tv′) = refl , refl
conv-types-unique unique (conv-unseal d) (conv-unseal d′) =
  refl , ∋:=-det unique d d′
conv-types-unique unique (conv-seal d) (conv-seal d′) =
  ∋:=-det unique d d′ , refl
conv-types-unique unique (conv-fun s t) (conv-fun s′ t′)
  with conv-types-unique unique s s′ | conv-types-unique unique t t′
... | refl , refl | refl , refl = refl , refl
conv-types-unique {Δ = Δ} unique (conv-all s) (conv-all s′)
  with conv-types-unique (unique-underΛ {Γ = Δ} unique) s s′
... | refl , refl = refl , refl

conv-src-unique : ∀ {c A A′ B B′}
  → Unique (names Δ)
  → Δ ⊢ c ∶ A ⇝ B
  → Δ ⊢ c ∶ A′ ⇝ B′
  → A ≡ A′
conv-src-unique unique ⊢c ⊢c′
  with conv-types-unique unique ⊢c ⊢c′
... | eq , _ = eq

------------------------------------------------------------------------
-- 7. Concrete lookup-square checks
------------------------------------------------------------------------

βCtx : Ctxᵗ
βCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

β-lookup : βCtx ∋ zero := `ℕ
β-lookup = zero , `ℕ , here , r-here , same-ℕ

β-unseal : βCtx ⊢ unseal zero ∶ ` zero ⇝ `ℕ
β-unseal = conv-unseal β-lookup

β-seal : βCtx ⊢ seal zero ∶ `ℕ ⇝ ` zero
β-seal = conv-seal β-lookup

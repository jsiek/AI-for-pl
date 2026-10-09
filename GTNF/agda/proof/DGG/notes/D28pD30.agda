module proof.DGG.notes.D28pD30 where

-- File Charter:
--   * D28′ + D30 CHECKED TOGETHER (D28pD30.md; design.md §9, §10.5,
--     §10.8, §C9.2, §C9.3).  A local variant `_∣_⊢_⊑ᴰ_∶[_]_` of the
--     real relation (TermImprecision at HEAD: D27, D28, D29), with:
--     - D28′: NO grants.  `⊑cast` is GTSFImp's plain rule (no
--       CastGrant, no RaiseCtx).  A boundary rule may add to κ, for its
--       interior only, the right rep. vars of the type variables it
--       JOINS (`JoinRep`: a rejoin or matched fresh pair through ϱ, or
--       a new opening, D30), and pays by its interior index read at the
--       interior world WITHOUT them (`pay`).  R1 → R1′ (`UnbindOK′`: a
--       left unbind whose rep. var does not occur in the exterior type
--       needs no unpermitted partner).  R2 unchanged.
--     - D30: the openings are in the INDEX, not the world.  The index
--       `A ⊑ᴰ⟨ W ∣ O ⟩ A′` opens the left type's outer ∀s at the slots O
--       (`OpenO`); the world's `πʷ` field is NEVER READ (by the index,
--       the rules, the side relations or `WfWorldᴰ`): the variant's
--       world is ImprecisionWorld's `World` minus πʷ, and every world
--       below has πʷ = [].  Only `⊑⟪⟫` creates openings (`PushD`), only
--       `Λ⊑` consumes one by changing the world (`Bind`, `b-join`), and
--       `cast⊑` consumes or passes them along the coercion's binder
--       layers (`CastOpen`; NOT `drop k O`, see D28pD30.md §2), with no
--       world change.
--     - TwoGen (iii) in D30 form: a slot is an opening `opn k` or a SKIP
--       `skp` (the next left ∀ waits, left-only, X⊑★); a skip is
--       created only for a left gen-cast value, and a later `⊑⟪⟫` may
--       FILL a carried skip with a new opening (`Fill`).  TwoGen (i)
--       (a cast⊑cast that pops) is NOT included: it is not needed.
--   * WHERE THE PERMISSION OF A PUSHED TYPE VARIABLE SITS: at `⊑⟪⟫`,
--     where its opening is created (a term binder: a boundary entry),
--     paying with the OPENED interior index.  `Λ⊑`'s join takes none.
--   * Contents.  §1 slots and the index; §2 side relations; §3 the
--     relation; §4 its typings; §5 the real grant-free relation is a
--     sub-relation (`toD`); §6 the corpus (6a through `toD`; 6b-6e the
--     grant users re-derived; 6f P5; 6g R2c); §7 the fixed pairs (P4k,
--     P4h, TwoGen's seven); §8 the dead pairs (C1-C5, C4g, C5 hidden);
--     8b DGG part 1 witnesses; §9 the hunt (a gen-valued C4).
--   * RESULTS.  Corpus: `CorpusA.*` … `CorpusE.*`, `P5ᴰ.*`, `R2cᴰ.*`.
--     Fixed: `P4kᴰ.post`, `P4hᴰ.post`, `TwoGenᴰ.*-final`,
--     `TwoGenᴰ.G0ᴰ.g0-final`, `TwoGenᴰ.N2ᴰ.{nrm,nr}-final`,
--     `DGG1ᴰ.*`.  Dead: `C1ᴰ.c1-unrelated`, `C2ᴰ.c2-unrelated`,
--     `C3ᴰ.c3-unrelated`, `C4ᴰ.c4-unrelated`, `C4gᴰ.c4g-unrelated`,
--     `C5ᴰ.{c5-unrelated, c5-redex-unrelated, hidden-unrelated}`.
--     Hunt: `Hunt.c4gen-unrelated` (no counterexample found).
--   * Not a Def module; All.agda does not import it.  No holes, no
--     postulates.  LEFT is the more precise side.

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision as R
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; nu-ty;
         BdyTy; bdy-ty; NuConversionImp; BdyConversionImp;
         ⊢lit; ⊢cast′; ⊢ν′; ⊢⟪⟫′)
open import proof.DGG.CtxWeaken using (⊢closed)
open import proof.DGG.notes.TwoGen using (GenLayer; gl-gen; gl-∀;
  GenCastValue; gcv)

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Slots and the index (D30)
------------------------------------------------------------------------

-- a slot of the index: open the next left ∀ at the right type variable
-- k (a position of the right context), or SKIP it: the left ∀ waits,
-- left-only at X⊑★ (TwoGen (iii), as type imprecision's ∀⊑)
data Slot : Set where
  opn : ℕ → Slot
  skp : Slot

-- `OpenO μ e O ρ A B`: A with its outer ∀s opened at the slots O
-- (outermost first; e embeds right positions into center type
-- variables),
-- renamed by ρ, is below B.  A skip adds a left-only center type
-- variable, as
-- `∀⊑` does (with its side conditions).
OpenO : ImpEnv → (ℕ → ℕ) → List Slot → Renameᵗ → Ty → Ty → Set
OpenO μ e []          ρ A        B = μ ⊢ renameᵗ ρ A ⊑ B
OpenO μ e (opn k ∷ O) ρ (`∀ A)   B = OpenO μ e O (e k ⊳ ρ) A B
OpenO μ e (skp ∷ O)   ρ (`∀ A)   B =
  NonVar A × 0 ∈ᵗ A
  × OpenO (instᵐ μ) (λ k → suc (e k)) O (extᵗ ρ) A (⇑ᵗ B)
OpenO μ e (_ ∷ _)     ρ (` X)    B = ⊥
OpenO μ e (_ ∷ _)     ρ `ℕ       B = ⊥
OpenO μ e (_ ∷ _)     ρ `𝔹       B = ⊥
OpenO μ e (_ ∷ _)     ρ ★        B = ⊥
OpenO μ e (_ ∷ _)     ρ (A ⇒ A′) B = ⊥

-- THE INDEX `A ⊑_W^O A′`; at O = [] it is the plain
-- `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′`, definitionally
infix 4 _⊑ᴰ⟨_∣_⟩_
_⊑ᴰ⟨_∣_⟩_ : Ty → World Δ Δ′ → List Slot → Ty → Set
A ⊑ᴰ⟨ W ∣ O ⟩ A′ =
  OpenO (marksʷ W) (emb (ηᴿʷ W)) O (emb (ηᴸʷ W)) A (embᴿ W A′)

------------------------------------------------------------------------
-- 2. Side relations
------------------------------------------------------------------------

-- well-formedness of a world: WfWorld without its D27 parts (the
-- conditions on openings are checked where an opening is created, at
-- ⊑⟪⟫: `SlotOK`, `SlotNe`)
record WfWorldᴰ (W : World Δ Δ′) : Set where
  constructor wfᴰ
  field
    wd-joint   : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wd-agree   : ∀ {α β} → Paired W α β → Agree W α β
    wd-namedᴸ  : NamedUniqueᴸ W
    wd-namedᴿ  : NamedUniqueᴿ W
    wd-permits : All (reps Δ′ ∋ʳ_) (κʷ W)
open WfWorldᴰ public

-- the permissions a boundary adds for its interior (D28′)
infixl 6 _+κ_
_+κ_ : World Δ Δ′ → List RVar → World Δ Δ′
W +κ K = record W { κʷ = K ++ κʷ W }

-- Λ⊑'s JOIN of the opening k (D27's pop, now consuming an index slot):
-- the left binder joins the right-only type variable k, bound to a ★
-- rep. var β; the binder's abstract rep. var is paired lexically with β
data Join1 {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → ℕ → World (underΛ Δ) Δ′ → Set where
  join1 : ∀ {n ϱᵍ ϱˡ κ k β} {ι : names Δ ↪ n} {ι′ : names Δ′ ↪ n}
      {ι⁺ : names (underΛ Δ) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Join1 (world n ι ι′ ϱᵍ ϱˡ κ []) k
            (world n ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ [])

-- Λ⊑'s binder: fresh (left-only), the JOIN of the next opening, or
-- claim-rep (D29); fresh and claim-rep take the plain index
data Bind {Δ Δ′ : Ctxᵗ}
    : World Δ Δ′ → List Slot → World (underΛ Δ) Δ′ → List Slot → Set where
  b-fresh : ∀ {W} → Bind W [] (W ⊕ᴸ) []
  b-join  : ∀ {W W₁ k O} → Join1 W k W₁ → Bind W (opn k ∷ O) W₁ O
  b-rep   : ∀ {W β}
    → Δ′ ∋rep β := ★
    → ¬ (names Δ′ ∋ᵅ β)
    → NoNamedPartner W β
    → Bind W [] (W ⊕ᴸ⇔ β) []

-- cast⊑'s openings (conclusion, premise), along the coercion's binder
-- layers: a ∀ layer passes its slot to the cast value, a gen layer
-- consumes its slot (the value under the gen does not see the binder);
-- every other cast has none.  (TwoGen's CastClaimG on slots.)
data CastOpen (M : Term) : Coercion → List Slot → List Slot → Set where
  co-plain : ∀ {c} → CastOpen M c [] []
  co-∀     : ∀ {c s O Oₚ} → Value M → CastOpen M c O Oₚ
    → CastOpen M (∀ᵖ c) (s ∷ O) (s ∷ Oₚ)
  co-gen   : ∀ {c s O Oₚ} → Value M → CastOpen M c O Oₚ
    → CastOpen M (genᵖ c) (s ∷ O) Oₚ

-- a ∀ conversion layer per slot (⟪⟫⊑'s pass, D27's `bc-∀`)
data ForallConvS : Conv → List Slot → Set where
  fs-[] : ∀ {c} → ForallConvS c []
  fs-∷  : ∀ {s c O} → ForallConvS s O → ForallConvS ⌞ `∀ s ⌟ (c ∷ O)

data BdyOpen (M : Term) (c : Conv) : List Slot → Set where
  bo-plain : BdyOpen M c []
  bo-∀     : ∀ {s O} → Simple M → ForallConvS c (s ∷ O)
    → BdyOpen M c (s ∷ O)

-- ⊑⟪⟫: the carried slots (an opening continues through Θ′; k′ is its
-- interior position) ...
data CarriedS (Θ′ : Boundary) : List Slot → List Slot → Set where
  cs-[]  : CarriedS Θ′ [] []
  cs-opn : ∀ {k k′ O O′} → toExt Θ′ k′ ≡ just k → CarriedS Θ′ O O′
    → CarriedS Θ′ (opn k ∷ O) (opn k′ ∷ O′)
  cs-skp : ∀ {O O′} → CarriedS Θ′ O O′ → CarriedS Θ′ (skp ∷ O) (skp ∷ O′)

-- ... the new slots, each an opening of a type variable Θ′ introduces,
-- or a skip (only for a left gen-cast value, TwoGen (iii)) ...
data NewSlot (Θ′ : Boundary) (M : Term) : Slot → Set where
  ns-opn : ∀ {k} → Fresh Θ′ k → NewSlot Θ′ M (opn k)
  ns-skp : GenCastValue M → NewSlot Θ′ M skp

-- ... merged: carried slots keep their order; a new opening may FILL a
-- carried skip (left to right); the remaining new slots go last
data Fill : List Slot → List Slot → List Slot → Set where
  f-end  : ∀ {N} → Fill [] N N
  f-keep : ∀ {s O N Oᵢ} → Fill O N Oᵢ → Fill (s ∷ O) N (s ∷ Oᵢ)
  f-fill : ∀ {k O N Oᵢ} → Fill O N Oᵢ
    → Fill (skp ∷ O) (opn k ∷ N) (opn k ∷ Oᵢ)

-- THE PUSH (conclusion O, new slots N, interior Oᵢ); new slots need a
-- left value
data PushD (Θ′ : Boundary) (M : Term) (O : List Slot)
    : List Slot → List Slot → Set where
  pushD : ∀ {O′ N Oᵢ}
    → CarriedS Θ′ O O′
    → Fill O′ N Oᵢ
    → All (NewSlot Θ′ M) N
    → (N ≡ [] ⊎ Value M)
    → PushD Θ′ M O N Oᵢ

-- well-formed openings (D30, design.md §9): right-only, bound to a ★
-- rep. var with no left partner bound to a type variable (`PendingOK`),
-- distinct
SlotOK : World Δ Δ′ → Slot → Set
SlotOK W (opn k) = PendingOK W k
SlotOK W skp     = ⊤

SlotNe : Slot → Slot → Set
SlotNe (opn k) (opn k′) = k ≢ k′
SlotNe (opn k) skp      = ⊤
SlotNe skp     _        = ⊤

-- k is a new opening
infix 4 _∋ᵒ_
data _∋ᵒ_ : List Slot → ℕ → Set where
  oh : ∀ {k N} → (opn k ∷ N) ∋ᵒ k
  ot : ∀ {s k N} → N ∋ᵒ k → (s ∷ N) ∋ᵒ k

-- D28′: β may be permitted for the interior only if this boundary JOINS
-- a type variable bound to β: a fresh type variable joined through ϱ
-- (a matched fresh pair, or a rejoin), or a new opening
data JoinRep {Δᵢ Δ′ᵢ : Ctxᵗ} (Wᵢ : World Δᵢ Δ′ᵢ) (Θ Θ′ : Boundary)
    (N : List Slot) (β : RVar) : Set where
  jr-join : ∀ {X X′}
    → Δᵢ ∋tv X → Δ′ᵢ ∋ᵗ X′ := β
    → Fresh Θ X ⊎ Fresh Θ′ X′
    → Joins Wᵢ X X′
    → JoinRep Wᵢ Θ Θ′ N β
  jr-open : ∀ {k} → N ∋ᵒ k → Δ′ᵢ ∋ᵗ k := β → JoinRep Wᵢ Θ Θ′ N β

-- R1′ (D28′): a left unbind whose rep. var does not occur in the
-- boundary's EXTERIOR type A needs nothing; otherwise R1
data UnbindOK′ (W : World Δ Δ′) (A : Ty) : Change → Set where
  ok-bind′   : ∀ {X α} → UnbindOK′ W A (bind X α)
  ok-hidden  : ∀ {Y α}
    → (∀ {X} → Δ ∋ᵗ X := α → occurs X A ≡ false)
    → UnbindOK′ W A (unbind Y α)
  ok-unbind′ : ∀ {Y α} → Unpermitted W α → UnbindOK′ W A (unbind Y α)

------------------------------------------------------------------------
-- 3. The relation: D28′ + D30 (15 rules)
------------------------------------------------------------------------

infix 3 _∣_⊢_⊑ᴰ_∶[_]_

data _∣_⊢_⊑ᴰ_∶[_]_ {Δ Δ′ : Ctxᵗ}
    : (W : World Δ Δ′) → CtxImp W → Term → Term → (O : List Slot)
    → {A A′ : Ty} → A ⊑ᴰ⟨ W ∣ O ⟩ A′ → Set where

  -- congruence, blame: no opening
  x⊑x : ∀ {W γ x A A′} {p : A ⊑ᴰ⟨ W ∣ [] ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ᴰ ` x ∶[ [] ] p

  κ⊑κ : ∀ {W γ k ι}
    → Lit k ι
    → (p : ι ⊑ᴰ⟨ W ∣ [] ⟩ ι)
    → W ∣ γ ⊢ k ⊑ᴰ k ∶[ [] ] p

  ƛ⊑ƛ : ∀ {W γ N N′ A A′ B B′}
      {pA : A ⊑ᴰ⟨ W ∣ [] ⟩ A′} {pB : B ⊑ᴰ⟨ W ∣ [] ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ᴰ N′ ∶[ [] ] pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ᴰ ƛ A′ ∙ N′ ∶[ [] ] ⇒⊑⇒ pA pB

  ·⊑· : ∀ {W γ L L′ M M′ A A′ B B′}
      {pA : A ⊑ᴰ⟨ W ∣ [] ⟩ A′} {pB : B ⊑ᴰ⟨ W ∣ [] ⟩ B′}
    → W ∣ γ ⊢ L ⊑ᴰ L′ ∶[ [] ] ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ᴰ M′ ∶[ [] ] pA
    → W ∣ γ ⊢ L · M ⊑ᴰ L′ · M′ ∶[ [] ] pB

  blame⊑ : ∀ {W γ ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᴰ⟨ W ∣ [] ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ᴰ M′ ∶[ [] ] p

  -- casts: no rule changes the world
  cast⊑cast : ∀ {W γ M M′ μ μ′ c c′ B B′ A A′}
      {p : B ⊑ᴰ⟨ W ∣ [] ⟩ B′}
    → W ∣ γ ⊢ M ⊑ᴰ M′ ∶[ [] ] p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᴰ⟨ W ∣ [] ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ᴰ M′ ⟨ μ′ ∣ c′ ⟩ ∶[ [] ] q

  -- D30: ONE cast⊑ rule; the premise openings follow the coercion
  cast⊑ : ∀ {W γ M M′ μ c B A A′ O Oₚ} {p : B ⊑ᴰ⟨ W ∣ Oₚ ⟩ A′}
    → CastOpen M c O Oₚ
    → W ∣ γ ⊢ M ⊑ᴰ M′ ∶[ Oₚ ] p
    → CastTy Δ μ c B A
    → (q : A ⊑ᴰ⟨ W ∣ O ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ᴰ M′ ∶[ O ] q

  -- D28′: GTSFImp's plain ⊑cast (keeps the openings)
  ⊑cast : ∀ {W γ M M′ μ′ c′ A B′ A′ O} {p : A ⊑ᴰ⟨ W ∣ O ⟩ B′}
    → W ∣ γ ⊢ M ⊑ᴰ M′ ∶[ O ] p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᴰ⟨ W ∣ O ⟩ A′)
    → W ∣ γ ⊢ M ⊑ᴰ M′ ⟨ μ′ ∣ c′ ⟩ ∶[ O ] q

  -- type abstraction
  Λ⊑Λ : ∀ {W γ γ′ V V′ A A′} {r : A ⊑ᴰ⟨ W ⊕² ∣ [] ⟩ A′}
    → LiftCtx γ γ′
    → Value V
    → Value V′
    → W ⊕² ∣ γ′ ⊢ V ⊑ᴰ V′ ∶[ [] ] r
    → (q : `∀ A ⊑ᴰ⟨ W ∣ [] ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ᴰ Λ V′ ∶[ [] ] q

  -- D30: the join of an opening is the only consumption that changes
  -- the world (a term binder)
  Λ⊑ : ∀ {W W₁ γ γ′ V M′ A B′ O O₁} {r : A ⊑ᴰ⟨ W₁ ∣ O₁ ⟩ B′}
    → Bind W O W₁ O₁
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ᴰ M′ ∶[ O₁ ] r
    → (q : `∀ A ⊑ᴰ⟨ W ∣ O ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ᴰ M′ ∶[ O ] q

  -- instantiation
  ν⊑ν : ∀ {W γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᴰ⟨ W ∣ [] ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ᴰ L′ ∶[ [] ] r
    → A ⊑ᴰ⟨ W ∣ [] ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᴰ⟨ W ∣ [] ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ᴰ ν A′ · L′ ⟨ c′ ⟩ ∶[ [] ] q

  ν⊑ : ∀ {W γ L M′ A C c B B′} {r : `∀ C ⊑ᴰ⟨ W ∣ [] ⟩ B′}
    → W ∣ γ ⊢ L ⊑ᴰ M′ ∶[ [] ] r
    → A ⊑ᴰ⟨ W ∣ [] ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᴰ⟨ W ∣ [] ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ᴰ M′ ∶[ [] ] q

  -- boundaries: D28′'s K (JoinRep) and the payment `pay` (the interior
  -- index read WITHOUT K: the joined type variables at X⊑X)
  ⟪⟫⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {K}
      {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᴰ⟨ Wᵢ +κ K ∣ [] ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → All (JoinRep Wᵢ Θ Θ′ []) K
    → WfWorldᴰ (Wᵢ +κ K)
    → (pay : Aᵢ ⊑ᴰ⟨ Wᵢ ∣ [] ⟩ A′ᵢ)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ᴰ M′ ∶[ [] ] r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᴰ⟨ W ∣ [] ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ᴰ M′ ⟪ Θ′ , c′ ⟫ ∶[ [] ] q

  -- R1′ reads the exterior type A
  ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′} {K}
      {γ M M′ Θ c Aᵢ A A′ O} {r : Aᵢ ⊑ᴰ⟨ Wᵢ +κ K ∣ O ⟩ A′}
    → Interior W Θ [] Wᵢ
    → All (UnbindOK′ W A) Θ
    → BdyOpen M c O
    → All (JoinRep Wᵢ Θ [] []) K
    → WfWorldᴰ (Wᵢ +κ K)
    → (pay : Aᵢ ⊑ᴰ⟨ Wᵢ ∣ O ⟩ A′)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ᴰ M′ ∶[ O ] r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᴰ⟨ W ∣ O ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ᴰ M′ ∶[ O ] q

  -- D30: the only rule that creates openings
  ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ} {K}
      {γ M M′ Θ′ c′ A A′ᵢ A′ O N Oᵢ} {r : A ⊑ᴰ⟨ Wᵢ +κ K ∣ Oᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → PushD Θ′ M O N Oᵢ
    → All (SlotOK Wᵢ) Oᵢ
    → AllPairs SlotNe Oᵢ
    → All (JoinRep Wᵢ [] Θ′ N) K
    → WfWorldᴰ (Wᵢ +κ K)
    → (pay : A ⊑ᴰ⟨ Wᵢ ∣ Oᵢ ⟩ A′ᵢ)
    → Wᵢ +κ K ∣ [] ⊢ M ⊑ᴰ M′ ∶[ Oᵢ ] r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᴰ⟨ W ∣ O ⟩ A′)
    → W ∣ γ ⊢ M ⊑ᴰ M′ ⟪ Θ′ , c′ ⟫ ∶[ O ] q

-- the relation with its two types explicit
infix 3 _∣_⊢_⊑ᴰ_∶⟨_,_⟩[_]_
_∣_⊢_⊑ᴰ_∶⟨_,_⟩[_]_ : (W : World Δ Δ′) → CtxImp W → Term → Term
  → (A A′ : Ty) → (O : List Slot) → A ⊑ᴰ⟨ W ∣ O ⟩ A′ → Set
W ∣ γ ⊢ M ⊑ᴰ M′ ∶⟨ A , A′ ⟩[ O ] p = _∣_⊢_⊑ᴰ_∶[_]_ W γ M M′ O {A} {A′} p

------------------------------------------------------------------------
-- 4. A derivation gives both typings (as proof/DGG/ImprecisionTyping)
------------------------------------------------------------------------

open import proof.DGG.ImprecisionTypingProof
  using (∋ʷ-lhs; ∋ʷ-rhs; lift-lhs; lift-rhs; liftᴸ-lhs; liftᴸ-rhs; ⊢Γ-cast)

typingD : ∀ {W : World Δ Δ′} {γ M M′ O A A′} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
  → W ∣ γ ⊢ M ⊑ᴰ M′ ∶⟨ A , A′ ⟩[ O ] q
  → (Δ ∣ lhs γ ⊢ M ⦂ A) × (Δ′ ∣ rhs γ ⊢ M′ ⦂ A′)
typingD (x⊑x x) = ⊢` (∋ʷ-lhs x) , ⊢` (∋ʷ-rhs x)
typingD (κ⊑κ k p) = ⊢lit k , ⊢lit k
typingD (ƛ⊑ƛ wA wA′ d) with typingD d
... | ⊢N , ⊢N′ = ⊢ƛ wA ⊢N , ⊢ƛ wA′ ⊢N′
typingD (·⊑· d e) with typingD d | typingD e
... | ⊢L , ⊢L′ | ⊢M , ⊢M′ = ⊢· ⊢L ⊢M , ⊢· ⊢L′ ⊢M′
typingD (blame⊑ wA ⊢M′ p) = ⊢blame wA , ⊢M′
typingD (cast⊑cast d ct ct′ q) with typingD d
... | ⊢M , ⊢M′ = ⊢cast′ ct ⊢M , ⊢cast′ ct′ ⊢M′
typingD (cast⊑ co d ct q) with typingD d
... | ⊢M , ⊢M′ = ⊢cast′ ct ⊢M , ⊢M′
typingD (⊑cast d ct′ q) with typingD d
... | ⊢M , ⊢M′ = ⊢M , ⊢cast′ ct′ ⊢M′
typingD (Λ⊑Λ l v v′ d q) with typingD d
... | ⊢V , ⊢V′ =
  ⊢Λ v (⊢Γ-cast (lift-lhs l) ⊢V) , ⊢Λ v′ (⊢Γ-cast (lift-rhs l) ⊢V′)
typingD (Λ⊑ bd nv occ l v d q) with typingD d
... | ⊢V , ⊢M′ = ⊢Λ v (⊢Γ-cast (liftᴸ-lhs l) ⊢V) , ⊢Γ-cast (liftᴸ-rhs l) ⊢M′
typingD (ν⊑ν d pA n n′ ci q) with typingD d
... | ⊢L , ⊢L′ = ⊢ν′ n ⊢L , ⊢ν′ n′ ⊢L′
typingD (ν⊑ d pA n q) with typingD d
... | ⊢L , ⊢M′ = ⊢ν′ n ⊢L , ⊢M′
typingD (⟪⟫⊑⟪⟫ I K wf pay d b b′ ci q) with typingD d
... | ⊢M , ⊢M′ = ⊢⟪⟫′ b ⊢M , ⊢⟪⟫′ b′ ⊢M′
typingD (⟪⟫⊑ I ok bo K wf pay d b q) with typingD d
... | ⊢M , ⊢M′ = ⊢⟪⟫′ b ⊢M , ⊢closed ⊢M′
typingD (⊑⟪⟫ I pu so sn K wf pay d b′ q) with typingD d
... | ⊢M , ⊢M′ = ⊢closed ⊢M , ⊢⟪⟫′ b′ ⊢M′

ltyD : ∀ {W : World Δ Δ′} {γ M M′ O A A′} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
  → W ∣ γ ⊢ M ⊑ᴰ M′ ∶⟨ A , A′ ⟩[ O ] q → Δ ∣ lhs γ ⊢ M ⦂ A
ltyD d = proj₁ (typingD d)

rtyD : ∀ {W : World Δ Δ′} {γ M M′ O A A′} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
  → W ∣ γ ⊢ M ⊑ᴰ M′ ∶⟨ A , A′ ⟩[ O ] q → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
rtyD d = proj₂ (typingD d)

------------------------------------------------------------------------
-- 5. The real relation WITHOUT GRANTS is a sub-relation.  A real world
-- W goes to `W ⁰` (its πʷ emptied; nothing else changes, so CtxImp,
-- marks and joins are the same definitionally), its pending type
-- variables to
-- the openings `map opn (πʷ W)`.  `GF d`: d uses no grant (and every
-- RaiseCtx is the identity).  So every grant-free corpus derivation is
-- a variant derivation (`toD`); the grant users are re-derived in §6.
------------------------------------------------------------------------

infix 10 _⁰
_⁰ : World Δ Δ′ → World Δ Δ′
W ⁰ = record W { πʷ = [] }

toO : ∀ μ e π ρ A B → OpenImp μ (map e π) ρ A B → OpenO μ e (map opn π) ρ A B
toO μ e []      ρ A        B x = x
toO μ e (k ∷ π) ρ (`∀ A)   B x = toO μ e π (e k ⊳ ρ) A B x
toO μ e (k ∷ π) ρ (` X)    B ()
toO μ e (k ∷ π) ρ `ℕ       B ()
toO μ e (k ∷ π) ρ `𝔹       B ()
toO μ e (k ∷ π) ρ ★        B ()
toO μ e (k ∷ π) ρ (A ⇒ A′) B ()

toIx : ∀ {W : World Δ Δ′} {A A′} → A ⊑ᵂ⟨ W ⟩ A′
  → A ⊑ᴰ⟨ W ⁰ ∣ map opn (πʷ W) ⟩ A′
toIx {W = W} {A} {A′} =
  toO (marksʷ W) (emb (ηᴿʷ W)) (πʷ W) (emb (ηᴸʷ W)) A (embᴿ W A′)

int⁰ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ → Interior (W ⁰) Θ Θ′ (Wᵢ ⁰)
int⁰ I = record
  { int-left = int-left I ; int-right = int-right I
  ; same-ϱᵍ = same-ϱᵍ I ; same-ϱˡ = same-ϱˡ I ; same-κ = same-κ I
  ; join-cont = join-cont I ; join-fresh = join-fresh I }

-- a world with the same ϱ has the same payload imprecision and agreement
module _ {W W′ : World Δ Δ′}
    (pp : ∀ {α β} → Paired W α β → Paired W′ α β) where
  repW : ∀ {μ R R′} → RepImp W μ R R′ → RepImp W′ μ R R′
  repW ★⊑★          = ★⊑★
  repW (ι⊑ι b)      = ι⊑ι b
  repW (X⊑X h)      = X⊑X h
  repW (α⊑β p)      = α⊑β (pp p)
  repW (⇒⊑⇒ a b)    = ⇒⊑⇒ (repW a) (repW b)
  repW (∀⊑∀ a)      = ∀⊑∀ (repW a)
  repW (⇒⊑★ a b)    = ⇒⊑★ (repW a) (repW b)
  repW (ι⊑★ b)      = ι⊑★ b
  repW (X⊑★ h)      = X⊑★ h
  repW α⊑★          = α⊑★
  repW (∀⊑ nv o a)  = ∀⊑ nv o (repW a)
  repW ∀★⊑★         = ∀★⊑★
  repW (∀⊑★ ns a)   = ∀⊑★ ns (repW a)
  repW bot-elim     = bot-elim
  repW bot⊑★        = bot⊑★

  agreeW : ∀ {α β} → Agree W α β → Agree W′ α β
  agreeW (abst-abst a b) = abst-abst a b
  agreeW (abst-★ a b)    = abst-★ a b
  agreeW (rep-rep a b r) = rep-rep a b (repW r)

agreeπ : ∀ {W : World Δ Δ′} {π α β} → Agree W α β
  → Agree (record W { πʷ = π }) α β
agreeπ {W = W} {π} = agreeW {W = W} {W′ = record W { πʷ = π }} (λ p → p)

wfᴰ⁰ : ∀ {W : World Δ Δ′} → WfWorld W → WfWorldᴰ (W ⁰)
wfᴰ⁰ {W = W} wf = wfᴰ (wf-joint wf) (λ pr → agreeπ {W = W} (wf-agree wf pr))
  (wf-namedᴸ wf) (wf-namedᴿ wf) (wf-permits wf)

-- permissions added to a well-formed world (D28′'s Wᵢ +κ K)
++All : ∀ {A : Set} {P : A → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
++All []       qs = qs
++All (p ∷ ps) qs = p ∷ ++All ps qs

wf+κ : ∀ {W : World Δ Δ′} {K} → WfWorldᴰ W → All (reps Δ′ ∋ʳ_) K
  → WfWorldᴰ (W +κ K)
wf+κ {W = W} {K} w ps = wfᴰ (wd-joint w)
  (λ pr → agreeW {W = W} {W′ = W +κ K} (λ p → p) (wd-agree w pr))
  (wd-namedᴸ w) (wd-namedᴿ w) (++All ps (wd-permits w))

-- the same at a world whose πʷ is already [] (no conversion)
wf→ᴰ : ∀ {W : World Δ Δ′} → WfWorld W → WfWorldᴰ W
wf→ᴰ wf = wfᴰ (wf-joint wf) (wf-agree wf) (wf-namedᴸ wf) (wf-namedᴿ wf)
  (wf-permits wf)

claim→bind : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
  → R.Claim W W₁ → Bind (W ⁰) (map opn (πʷ W)) (W₁ ⁰) (map opn (πʷ W₁))
claim→bind R.claim-fresh = b-fresh
claim→bind (R.claim-pop (open1 j rk rβ)) = b-join (join1 j rk rβ)
claim→bind (R.claim-rep h nn np) = b-rep h nn np

cc→co : ∀ {M c π πₚ} → R.CastClaim M c π πₚ
  → CastOpen M c (map opn π) (map opn πₚ)
cc→co R.cc-plain     = co-plain
cc→co (R.cc-∀ v cc)  = co-∀ v (cc→co cc)
cc→co (R.cc-gen v)   = co-gen v co-plain

fc→fs : ∀ {c π} → R.ForallConv c π → ForallConvS c (map opn π)
fc→fs R.fc-[]     = fs-[]
fc→fs (R.fc-∷ fc) = fs-∷ (fc→fs fc)

bc→bo : ∀ {M c π πᵢ} → R.BdyClaim M c π πᵢ
  → (πᵢ ≡ π) × BdyOpen M c (map opn π)
bc→bo R.bc-plain    = refl , bo-plain
bc→bo (R.bc-∀ s fc) = refl , bo-∀ s (fc→fs fc)

ca→cs : ∀ {Θ′ π π′} → R.Carried Θ′ π π′
  → CarriedS Θ′ (map opn π) (map opn π′)
ca→cs R.ca-[]      = cs-[]
ca→cs (R.ca-∷ e c) = cs-opn e (ca→cs c)

fill-map : ∀ π′ nw → Fill (map opn π′) (map opn nw) (map opn (π′ ++ nw))
fill-map []       nw = f-end
fill-map (k ∷ π′) nw = f-keep (fill-map π′ nw)

news→ : ∀ {Θ′ M nw} → All (Fresh Θ′) nw → All (NewSlot Θ′ M) (map opn nw)
news→ []       = []
news→ (f ∷ fs) = ns-opn f ∷ news→ fs

push→ : ∀ {Θ′ M π πᵢ} → R.Push Θ′ M π πᵢ
  → Σ[ N ∈ List Slot ] PushD Θ′ M (map opn π) N (map opn πᵢ)
push→ (R.push {π′ = π′} {nw} c fs (inj₁ refl)) =
  _ , pushD (ca→cs c) (fill-map π′ nw) (news→ fs) (inj₁ refl)
push→ (R.push {π′ = π′} {nw} c fs (inj₂ v)) =
  _ , pushD (ca→cs c) (fill-map π′ nw) (news→ fs) (inj₂ v)

slots-ok : ∀ {W : World Δ Δ′} {π} → All (PendingOK W) π
  → All (SlotOK (W ⁰)) (map opn π)
slots-ok []       = []
slots-ok {W = W} (p ∷ ps) = p ∷ slots-ok {W = W} ps

slots-ne : ∀ {π} → AllPairs _≢_ π → AllPairs SlotNe (map opn π)
slots-ne [] = []
slots-ne (n ∷ ns) = ne-all n ∷ slots-ne ns
  where
  ne-all : ∀ {k π} → All (k ≢_) π → All (SlotNe (opn k)) (map opn π)
  ne-all []       = []
  ne-all (x ∷ xs) = x ∷ ne-all xs

r1→r1′ : ∀ {W : World Δ Δ′} {A Θ} → All (UnbindOK W) Θ
  → All (UnbindOK′ (W ⁰) A) Θ
r1→r1′ []                 = []
r1→r1′ (ok-bind ∷ r)      = ok-bind′ ∷ r1→r1′ r
r1→r1′ (ok-unbind u ∷ r)  = ok-unbind′ u ∷ r1→r1′ r

-- grant-freedom, solved by instance search on concrete derivations
record _∧_ (A B : Set) : Set where
  constructor _,,_
  field
    ∧₁ : A
    ∧₂ : B
open _∧_ public

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

instance
  ∧-i : ∀ {A B : Set} → {{A}} → {{B}} → A ∧ B
  ∧-i {{a}} {{b}} = a ,, b

  ⊤-i : ⊤
  ⊤-i = tt

  refl-i : ∀ {a} {A : Set a} {x : A} → x ≡ x
  refl-i = refl

GF : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → W R.∣ γ ⊢ M ⊑ M′ ∶ q → Set
GF (R.x⊑x _)                 = ⊤
GF (R.κ⊑κ _ _)               = ⊤
GF (R.ƛ⊑ƛ _ _ d)             = GF d
GF (R.·⊑· d e)               = GF d ∧ GF e
GF (R.blame⊑ _ _ _)          = ⊤
GF (R.cast⊑cast d _ _ _)     = GF d
GF (R.cast⊑ _ d _ _)         = GF d
GF (R.⊑cast {γ = γ} {γ′ = γ′} R.no-grant _ d _ _) = (γ′ ≡ γ) ∧ GF d
GF (R.⊑cast (R.grant _) _ _ _ _) = ⊥
GF (R.Λ⊑Λ _ _ _ d _)         = GF d
GF (R.Λ⊑ _ _ _ _ _ d _)      = GF d
GF (R.ν⊑ν d _ _ _ _ _)       = GF d
GF (R.ν⊑ d _ _ _)            = GF d
GF (R.⟪⟫⊑⟪⟫ _ _ d _ _ _ _)   = GF d
GF (R.⟪⟫⊑ _ _ _ _ d _ _)     = GF d
GF (R.⊑⟪⟫ _ _ _ d _ _)       = GF d

toD : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → (d : W R.∣ γ ⊢ M ⊑ M′ ∶ q) → GF d
  → W ⁰ ∣ γ ⊢ M ⊑ᴰ M′ ∶⟨ A , A′ ⟩[ map opn (πʷ W) ] toIx {W = W} q
toD (R.x⊑x h) _ = x⊑x h
toD (R.κ⊑κ l p) _ = κ⊑κ l p
toD (R.ƛ⊑ƛ wA wA′ d) g = ƛ⊑ƛ wA wA′ (toD d g)
toD (R.·⊑· d e) (g ,, h) = ·⊑· (toD d g) (toD e h)
toD (R.blame⊑ w ⊢M′ p) _ = blame⊑ w ⊢M′ p
toD (R.cast⊑cast d ct ct′ q) g = cast⊑cast (toD d g) ct ct′ q
toD {W = W} (R.cast⊑ cc d ct q) g =
  cast⊑ (cc→co cc) (toD d g) ct (toIx {W = W} q)
toD {W = W} {M = M} {M′ ⟨ μ′ ∣ c′ ⟩}
  (R.⊑cast {γ = γ} {γ′} {p = p} R.no-grant r d ct q) (e ,, g) =
  ⊑cast (subst (λ g′ → W ⁰ ∣ g′ ⊢ M ⊑ᴰ M′ ∶[ map opn (πʷ W) ] toIx {W = W} p)
           e (toD d g))
    ct (toIx {W = W} q)
toD (R.Λ⊑Λ l v v′ d q) g = Λ⊑Λ l v v′ (toD d g) q
toD {W = W} (R.Λ⊑ cl nv occ l v d q) g =
  Λ⊑ (claim→bind cl) nv occ l v (toD d g) (toIx {W = W} q)
toD (R.ν⊑ν d a n n′ nc q) g = ν⊑ν (toD d g) a n n′ nc q
toD (R.ν⊑ d a n q) g = ν⊑ (toD d g) a n q
toD (R.⟪⟫⊑⟪⟫ {r = r} I wf d b b′ bc q) g =
  ⟪⟫⊑⟪⟫ I [] (wf→ᴰ wf) r (toD d g) b b′ bc q
toD {W = W} (R.⟪⟫⊑ {Wᵢ = Wᵢ} {Aᵢ = Aᵢ} {A} {A′} {r = r} I ok R.bc-plain
    wf d b q) g =
  ⟪⟫⊑ (int⁰ I) (r1→r1′ ok) bo-plain [] (wfᴰ⁰ wf)
    (toIx {W = Wᵢ} {Aᵢ} {A′} r) (toD d g) b (toIx {W = W} {A} {A′} q)
toD {W = W} (R.⟪⟫⊑ {Wᵢ = Wᵢ} {Aᵢ = Aᵢ} {A} {A′} {r = r} I ok
    (R.bc-∀ s fc) wf d b q) g =
  ⟪⟫⊑ (int⁰ I) (r1→r1′ ok) (bo-∀ s (fc→fs fc)) [] (wfᴰ⁰ wf)
    (toIx {W = Wᵢ} {Aᵢ} {A′} r) (toD d g) b (toIx {W = W} {A} {A′} q)
toD {W = W} (R.⊑⟪⟫ {Wᵢ = Wᵢ} {A = A} {A′ᵢ} {A′} {r = r} I pu wf d b q) g =
  ⊑⟪⟫ (int⁰ I) (proj₂ (push→ pu)) (slots-ok {W = Wᵢ} (wf-pending wf))
    (slots-ne (wf-distinct wf)) [] (wfᴰ⁰ wf) (toIx {W = Wᵢ} {A} {A′ᵢ} r)
    (toD d g) b (toIx {W = W} {A} {A′} q)

------------------------------------------------------------------------
-- 6. THE CORPUS.  6a: every grant-free corpus derivation, through `toD`
-- (the world's πʷ emptied, its pending type variables turned into
-- openings).
-- 6b-6e: the grant users, re-derived with D28′'s permissions at the
-- joining boundary.
------------------------------------------------------------------------

import examples.TermImprecisionExamples as TIE
import examples.TermImprecisionRegressionExamples as RG
import examples.TermImprecisionH1Examples as H1
import examples.TermImprecisionRebaseExamples as RB
import examples.TermImprecisionPermissionExamples as PE
import proof.DGG.notes.NoPush as NP
import proof.DGG.notes.TwoGen as TG
import proof.DGG.notes.ReductionAudit as RA

module CorpusA where
  -- P1, P2, P3 (= Ch X0, D27's push and pop), P6
  p1-init   = toD TIE.p1-init it
  p1-tybeta = toD TIE.p1-tybeta it
  p2-tybeta = toD TIE.p2-tybeta it
  p3-inst   = toD TIE.p3-inst it
  p6-tybeta = toD TIE.p6-tybeta it
  -- K (D26's counterexample): every block, and the final pair VL ⊑ RF
  lk⊑rk     = toD RG.lk⊑rk it
  lk₁⊑rk₁   = toD RG.lk₁⊑rk₁ it
  VL⊑RF     = toD RG.VL⊑RF it
  lk₁⊑rk₄   = toD RG.lk₁⊑rk₄ it
  lk₁⊑rk₃   = toD RG.lk₁⊑rk₃ it
  VL⊑Rarg₃  = toD RG.VL⊑Rarg₃ it
  -- H1 (D29): init, state 2, the final pair (claim, push, carry, pop)
  -- and the push-free final pair (two claims)
  h1-init   = toD H1.init it
  h1-st2    = toD H1.st2 it
  h1-final  = toD H1.final it
  h1-final-no-push = toD H1.final-no-push it
  -- the cambridge blocks without a grant
  ch-b0  = toD RB.ch-b0 it
  ch-x0  = toD RB.ch-x0 it
  ch-b1  = toD RB.ch-b1 it
  cg-b0  = toD RB.cg-b0 it
  c2-b0  = toD RB.c2-b0 it
  c2-b6  = toD RB.c2-b6 it
  c2-b7  = toD RB.c2-b7 it
  c12-b0 = toD RB.c12-b0 it
  c12-x0 = toD RB.c12-x0 it
  -- P4's grant-free blocks
  p4-B1  = toD PE.P4.p4-B1 it
  p4-B1′ = toD PE.P4.p4-B1′ it
  p4-B5  = toD PE.P4.p4-B5 it
  p4-B6  = toD PE.P4.p4-B6 it
  -- L3c (pre, post) and L3d (before): NoPush's claim-rep derivations
  l3c-pre    = toD (NP.toReal NP.Corpus.l3c-pre) it
  l3c-post   = toD (NP.toReal NP.Corpus.l3c-post) it
  l3d-before = toD (NP.toReal NP.Corpus.l3d-before) it
  -- the initial pairs of the fixed examples (§7)
  g0-init  = toD TG.G0.init it
  g2m-init = toD TG.G2m.init it
  g2-init  = toD TG.G2.init it
  hrm-init = toD TG.HRm.init it
  hr-init  = toD TG.HR.init it
  n2-init  = toD TG.N2.init it
  n2-init-m = toD TG.N2.init-m it
  p4k-init = toD RA.P4k.init it
  p4k-pre  = toD RA.P4k.pre it
  p4h-init = toD RA.P4h.init it
  p4h-pre  = toD RA.P4h.pre it

-- 6b. P4 (cambridge Cf from its second block), every block.  Under D28
-- the gen wrapper `X! → X?` (B2) and the check `X?` (B3, B4) GRANTED
-- αᴿ.  Under D28′ the matched TyBeta boundary `+X ∥ +X` (a matched
-- fresh pair, JOINED through ϱᵍ) permits αᴿ for its interior (K = [0])
-- and pays with its interior index at X⊑X (`c⊑c²`, `X⊑X`); everything
-- inside is the real (grant-free) derivation.
module CorpusB where
  open PE.P4 using (v₀; W₄; W₄²; W₄²¹; W₄²-wf; W₄²¹-wf; idX⊑I★⁻;
    tagᵍ-ty; bBg; Ξ₄; ϱ₄; S⊑S!; chkᵍ-ty; bUnsealL₃; bUnsealR₄; S⊑J; bJ⁻;
    W₄ᴸ-wf; bUnsealL; bUnsealR; nth; Ls; Rs)
  open RB using (Wc-bind²; Wc-bind²-conv; c⊑c²; ℕ⇒ℕ; Wc-unbindᴿ; Wc²)
  open TIE using (bL-ty; revX⊑revX)

  -- the matched TyBeta boundary joins its fresh pair (D28′)
  jr₀ : ∀ {Ξ ϱ κ} → JoinRep (Wc² {Ξ} {ϱ} κ 0) TIE.Θ₀ TIE.Θ₀ [] 0
  jr₀ = jr-join (_ , here) here (inj₁ refl) refl

  conv₄ : BdyConversionImp W₄ bL-ty bBg
  conv₄ = W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl

  p4-B2 : W₄ ∣ [] ⊢ nth Ls 2 ⊑ᴰ nth Rs 2 ∶[ [] ] ι⊑ι base-ℕ
  p4-B2 =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf)
        (c⊑c² Ξ₄ ϱ₄ [] 0)
        (⊑cast (toD idX⊑I★⁻ it) tagᵍ-ty (c⊑c² Ξ₄ ϱ₄ (0 ∷ []) 0))
        bL-ty bBg conv₄ (ℕ⇒ℕ W₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  p4-B3 : W₄ ∣ [] ⊢ nth Ls 3 ⊑ᴰ nth Rs 4 ∶[ [] ] ι⊑ι base-ℕ
  p4-B3 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf) X⊑X
      (⊑cast (toD (R.·⊑· idX⊑I★⁻ S⊑S!) it) chkᵍ-ty X⊑X)
      bUnsealL₃ bUnsealR₄ (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

  -- B4: the J pair `S ⊑ J` is the real one (X left-only inside the
  -- right's −X, rejoined at its +X, αᴿ still permitted: a rejoin
  -- inside a permitted region pays nothing)
  p4-B4 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ᴰ nth Rs 6 ∶[ [] ] ι⊑ι base-ℕ
  p4-B4 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf) X⊑X
      (⊑cast (toD (R.⊑⟪⟫ (Wc-unbindᴿ v₀) R.push-none W₄ᴸ-wf S⊑J bJ⁻
                  (X⊑★ here)) it)
        chkᵍ-ty X⊑X)
      bUnsealL bUnsealR (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

-- a right-only boundary with no opening and no permission
⊑⟪⟫₀ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ} {γ M M′ Θ′ c′ A A′ᵢ A′}
    {r : A ⊑ᴰ⟨ Wᵢ ∣ [] ⟩ A′ᵢ}
  → Interior W [] Θ′ Wᵢ
  → WfWorldᴰ Wᵢ
  → Wᵢ ∣ [] ⊢ M ⊑ᴰ M′ ∶[ [] ] r
  → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
  → (q : A ⊑ᴰ⟨ W ∣ [] ⟩ A′)
  → W ∣ γ ⊢ M ⊑ᴰ M′ ⟪ Θ′ , c′ ⟫ ∶[ [] ] q
⊑⟪⟫₀ {r = r} I wf d b q =
  ⊑⟪⟫ I (pushD cs-[] f-end [] (inj₁ refl)) [] [] [] wf r d b q

-- 6c. The D25 chains (C12-C14 B1): every gen layer's REJOIN `+Y^β` of
-- the left's c permits β for its interior (K = [β]) and pays with
-- `c ⊑ c` at X⊑X; the outermost layer is the matched TyBeta boundary
module CorpusC where
  open RB using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ;
    Wc-bindᴿ; c⊑★ᴸ; c⊑★²; c⊑c²; genLayer; id★↦; id★→; tagX↦; core⊑; p0;
    p10; ℕ⇒ℕ; ℕ⇒ℕ⊑★⇒★)
  open TIE using (L1′)
  open import proof.ImprecisionWorld using (permit-here)
  open CorpusB using (jr₀)

  jrR : ∀ {Ξ ϱ κ β} → JoinRep (Wc² {Ξ} {ϱ} κ β) [] (bind 0 β ∷ []) [] β
  jrR = jr-join (_ , here) here (inj₂ refl) refl

  layer⊑ᴰ : ∀ {Ξ′ ϱ κ β M}
    → Ξ′ ∋ʳ β → ϱ ∋ᵨ 0 ⇔ β
    → WfWorld (Wc² {Ξ′} {ϱ} (β ∷ κ) β)
    → WfWorld (Wcᴸ {Ξ′} {ϱ} (β ∷ κ))
    → (Wcᴸ {Ξ′} {ϱ} (β ∷ κ)) ∣ [] ⊢ TIE.idX ⊑ᴰ M ∶⟨ ` 0 ⇒ ` 0 , ★ ⇒ ★ ⟩[ [] ]
        c⊑★ᴸ Ξ′ ϱ (β ∷ κ)
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (β ∷ [])) (unbind 0 β ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (β ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → BdyTy (Ξ′ ∣ []) (bind 0 β ∷ []) (Ξ′ ∣ (β ∷ [])) (` 0 ⇒ ` 0) TIE.revX
        (★ ⇒ ★)
    → (Wcᴸ {Ξ′} {ϱ} κ) ∣ [] ⊢ TIE.idX ⊑ᴰ genLayer β M
        ∶⟨ ` 0 ⇒ ` 0 , ★ ⇒ ★ ⟩[ [] ] c⊑★ᴸ Ξ′ ϱ κ
  layer⊑ᴰ {Ξ′} {ϱ} {κ} {β} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b =
    ⊑⟪⟫ (Wc-bindᴿ v p) (pushD cs-[] f-end [] (inj₁ refl)) [] []
      (jrR ∷ []) (wf→ᴰ W²-wf) (c⊑c² Ξ′ ϱ κ β)
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫₀ (Wc-unbindᴿ v) (wf→ᴰ Wᴸ-wf)
          (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ (β ∷ κ))) bᵤ
          (c⊑★² Ξ′ ϱ (β ∷ κ) β (permit-here β κ)))
        cₜ (c⊑c² Ξ′ ϱ (β ∷ κ) β))
      b (c⊑★ᴸ Ξ′ ϱ κ)

  outer⊑ᴰ : ∀ {Ξ′ ϱ M B′}
    → (v : Ξ′ ∋ʳ 0) → (p : ϱ ∋ᵨ 0 ⇔ 0)
    → WfWorld (Wc² {Ξ′} {ϱ} (0 ∷ []) 0)
    → WfWorld (Wcᴸ {Ξ′} {ϱ} (0 ∷ []))
    → (Wcᴸ {Ξ′} {ϱ} (0 ∷ [])) ∣ [] ⊢ TIE.idX ⊑ᴰ M ∶⟨ ` 0 ⇒ ` 0 , ★ ⇒ ★ ⟩[ [] ]
        c⊑★ᴸ Ξ′ ϱ (0 ∷ [])
    → CastTy (Ξ′ ∣ []) [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
    → BdyTy (Ξ′ ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (Ξ′ ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
    → CastTy (Ξ′ ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
    → (b : BdyTy (Ξ′ ∣ []) TIE.Θ₀ (Ξ′ ∣ (0 ∷ [])) (` 0 ⇒ ` 0) TIE.revX B′)
    → BdyConversionImp (Wc⁰ {Ξ′} {ϱ}) TIE.bL-ty b
    → (q : (`ℕ ⇒ `ℕ) ⊑ᴰ⟨ Wc⁰ {Ξ′} {ϱ} ∣ [] ⟩ B′)
    → (Wc⁰ {Ξ′} {ϱ}) ∣ [] ⊢ TIE.idX ⟪ TIE.Θ₀ , TIE.revX ⟫ ⊑ᴰ genLayer 0 M
        ∶⟨ `ℕ ⇒ `ℕ , B′ ⟩[ [] ] q
  outer⊑ᴰ {Ξ′} {ϱ} v p W²-wf Wᴸ-wf M⊑ cᵢ bᵤ cₜ b bc q =
    ⟪⟫⊑⟪⟫ (Wc-bind² v p) (jr₀ ∷ []) (wf→ᴰ W²-wf) (c⊑c² Ξ′ ϱ [] 0)
      (⊑cast {A = ` 0 ⇒ ` 0}
        (⊑⟪⟫₀ (Wc-unbindᴿ v) (wf→ᴰ Wᴸ-wf)
          (⊑cast M⊑ cᵢ (c⊑★ᴸ Ξ′ ϱ (0 ∷ []))) bᵤ
          (c⊑★² Ξ′ ϱ (0 ∷ []) 0 refl))
        cₜ (c⊑c² Ξ′ ϱ (0 ∷ []) 0))
      TIE.bL-ty b bc q

  open RB using (W₁₂; W₁₂²-wf; W₁₂ᴸ-wf; W₁₂ˣ-wf; B12x-ty; id★↦-ty;
    B12ᵤ-ty; B12ₜ-ty; B12-ty; C12-R₃; W₁₃; W₁₃²-wf; W₁₃ᴸ-wf; B13x-ty;
    B13ᵤ-ty; B13ₜ-ty; B13-ty; C13-R₄; W₁₄; W₁₄²-wf; W₁₄ᴸ-wf; B14x-ty;
    B14yᵤ-ty; B14yₜ-ty; B14y-ty; B14ᵤ-ty; B14ₜ-ty; B14-ty; C14-R₅)

  c12-b1 : W₁₂ ∣ [] ⊢ L1′ ⊑ᴰ C12-R₃ ∶[ [] ] ι⊑ι base-ℕ
  c12-b1 =
    ·⊑·
      (outer⊑ᴰ (_ , here) here⇔ (W₁₂²-wf p0) (W₁₂ᴸ-wf p0)
        (toD (core⊑ (_ , there here) (there⇔ here⇔) (W₁₂ˣ-wf p0) B12x-ty) it)
        id★↦-ty B12ᵤ-ty B12ₜ-ty B12-ty
        (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , TIE.revX⊑revX refl)
        (ℕ⇒ℕ W₁₂))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  c13-b1 : W₁₃ ∣ [] ⊢ L1′ ⊑ᴰ C13-R₄ ∶[ [] ] TIE.ℕ⊑★
  c13-b1 =
    ·⊑·
      (⊑cast
        (outer⊑ᴰ (_ , here) here⇔ (W₁₃²-wf here⇔ p0) (W₁₃ᴸ-wf p0)
          (toD (core⊑ (_ , there here) (there⇔ here⇔)
                 (W₁₃²-wf (there⇔ here⇔) p0) B13x-ty) it)
          id★↦-ty B13ᵤ-ty B13ₜ-ty B13-ty
          (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , TIE.revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ W₁₃))
        id★↦-ty (ℕ⇒ℕ⊑★⇒★ W₁₃))
      (toD (TIE.five⊑ {Ω = 0} {ηᴸ = []↪} {ηᴿ = []↪} {γ = []}) it)

  c14-b1 : W₁₄ ∣ [] ⊢ L1′ ⊑ᴰ C14-R₅ ∶[ [] ] ι⊑ι base-ℕ
  c14-b1 =
    ·⊑·
      (outer⊑ᴰ (_ , here) here⇔ (W₁₄²-wf here⇔ p0) (W₁₄ᴸ-wf p0)
        (layer⊑ᴰ (_ , there here) (there⇔ here⇔)
          (W₁₄²-wf (there⇔ here⇔) p10) (W₁₄ᴸ-wf p10)
          (toD (core⊑ (_ , there (there here)) (there⇔ (there⇔ here⇔))
                 (W₁₄²-wf (there⇔ (there⇔ here⇔)) p10) B14x-ty) it)
          id★↦-ty B14yᵤ-ty B14yₜ-ty B14y-ty)
        id★↦-ty B14ᵤ-ty B14ₜ-ty B14-ty
        (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , TIE.revX⊑revX refl)
        (ℕ⇒ℕ W₁₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- 6d. P4c (P4's right states 7-10 against B4's left), Cg B1, C18b B7:
-- the matched outer boundary permits the rep. var its check used to
-- grant
module CorpusD where
  open PE.P4 using (v₀; W₄; W₄²; W₄²¹; W₄²¹-wf; S⊑S; tagˣ-ty; chkᵍ-ty;
    bUnsealL; nth; Ls; Rs; p0; S)
  open PE.P4c using (IntRR; bBm7; bBi8; S⊑S3; bR7; bR8; bR9; R7; R8; R9)
  open RB using (Wc-bind²; Wc-bind²-conv; Wc²; Wcᴸ; Wc⁰; Wc-unbindᴿ; c⊑★²;
    c⊑c²; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; id★↦ᴿ-ty; ℕ⇒ℕ⊑★⇒★)
  open CorpusB using (jr₀)

  outer : ∀ {M′} → (b′ : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ (` 0) (unseal 0) `ℕ)
    → BdyConversionImp W₄ bUnsealL b′
    → W₄²¹ ∣ [] ⊢ S ⊑ᴰ M′ ∶⟨ ` 0 , ` 0 ⟩[ [] ] X⊑X
    → W₄ ∣ [] ⊢ nth Ls 4 ⊑ᴰ M′ ⟪ TIE.Θ₀ , unseal 0 ⟫ ∶[ [] ] ι⊑ι base-ℕ
  outer b′ bc d =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf) X⊑X d bUnsealL b′
      bc (ι⊑ι base-ℕ)

  p4-R7 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ᴰ R7 ∶[ [] ] ι⊑ι base-ℕ
  p4-R7 = outer bR7
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast
      (toD (R.⊑⟪⟫ IntRR R.push-none W₄²¹-wf (R.⊑cast₀ S⊑S tagˣ-ty (X⊑★ here))
              bBm7 (X⊑★ here)) it)
      chkᵍ-ty X⊑X)

  p4-R8 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ᴰ R8 ∶[ [] ] ι⊑ι base-ℕ
  p4-R8 = outer bR8
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast
      (toD (R.⊑cast₀ {p = X⊑X} (R.⊑⟪⟫ IntRR R.push-none W₄²¹-wf S⊑S bBi8 X⊑X)
              tagˣ-ty (X⊑★ here)) it)
      chkᵍ-ty X⊑X)

  p4-R9 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ᴰ R9 ∶[ [] ] ι⊑ι base-ℕ
  p4-R9 = outer bR9
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast (toD (R.⊑cast₀ {p = X⊑X} (S⊑S3 p0) tagˣ-ty (X⊑★ here)) it)
      chkᵍ-ty X⊑X)

  p4-R10 = toD PE.P4c.p4-R10 it

  -- Cg B1
  module Cg where
    open PE.CgB1 using (Ξg; ϱg; Wg²-wf; Wgᴴ-wf; idX⊑I★)
    open TIE using (L1′; bL-ty; revX⊑revX)
    open RB using (Cg-R₂)

    cg-b1 : Wc⁰ {Ξg} {ϱg} ∣ [] ⊢ L1′ ⊑ᴰ Cg-R₂ ∶[ [] ] ι⊑★ base-ℕ
    cg-b1 =
      ·⊑·
        (⊑cast
          (⟪⟫⊑⟪⟫ (Wc-bind² (_ , here) here⇔) (jr₀ ∷ [])
            (wf+κ (wf→ᴰ Wg²-wf) ((_ , here) ∷ [])) (c⊑c² Ξg ϱg [] 0)
            (⊑cast {A = ` 0 ⇒ ` 0}
              (toD (R.⊑⟪⟫ (Wc-unbindᴿ (_ , here)) R.push-none Wgᴴ-wf
                     idX⊑I★ I★⁻ᴿ-ty (c⊑★² Ξg ϱg (0 ∷ []) 0 refl)) it)
              tagᴿ-ty (c⊑c² Ξg ϱg (0 ∷ []) 0))
            bL-ty Bg-ty
            (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
            (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
          id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
        (toD (TIE.five⊑ {Ω = 0} {ηᴸ = []↪} {ηᴿ = []↪} {γ = []}) it)

  -- C18b B7: the matched outer (+Y,+X) permits X's rep. var 1 (K = [1])
  module C18b where
    open PE.C18bB7 using (IntO; IntH; IntJ; Wb; Wh; W₀; Wb-wf; Wh-wf; p1;
      inner; bJ2; bRH; X★; chk-ty; bL7; bR12; ConvO; L7; R12)

    jr₁ : JoinRep (Wb []) PE.C18bB7.Θo PE.C18bB7.Θo [] 1
    jr₁ = jr-join (_ , there here) (there here) (inj₁ refl) refl

    c18b-b7 : W₀ [] ∣ [] ⊢ L7 ⊑ᴰ R12 ∶[ [] ] ι⊑ι base-ℕ
    c18b-b7 =
      ⟪⟫⊑⟪⟫ IntO (jr₁ ∷ []) (wf→ᴰ (Wb-wf p1)) X⊑X
        (⊑cast
          (toD (R.⊑⟪⟫ IntH R.push-none (Wh-wf p1)
                  (R.⊑⟪⟫ IntJ R.push-none (Wb-wf p1) inner bJ2
                    (X⊑★ (there here)))
                  bRH (X⊑★ X★)) it)
          chk-ty X⊑X)
        bL7 bR12 (Wb [] , ConvO , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

-- 6e. The right-led blocks whose pushed type variable needed a grant
-- (Cg X0, C2 X0) and G1 (NoPush §3).  ⊑⟪⟫ OPENS the left's ∀ at the
-- Inst boundary's X (D30) and permits X's rep. var (K = [0], the new
-- opening, `jr-open`), paying with the OPENED interior index
-- `X→X ⊑ X→X` at X⊑X.  Cg X0: Λ⊑ JOINS the opening; C2 X0 and G1: the
-- left's gen cast consumes it (`co-gen`), with no world change.
module CorpusE where
  open TIE using (W₃; int-ro₃; Wi₃-wf; vΛidX; νL-ty; five⊑)
  open RB using (Bg; Bg-ty; I★gen; I★genI; vI★genI; genIᴸ-ty; tagᴿ-ty;
    id★↦ᴿ-ty; ∀id⊑★; ℕ⇒ℕ⊑★⇒★; IntN; W₃-wf; I★⁻ᴿ-ty; Cg-R₂; C2-L-ν-ty;
    Wg⁻-int; Wg⁻-wf; Wg⁺¹; X⇒X⊑★⇒★; p0)
  open import examples.ImprecisionExamples using (L1)
  open import examples.CambridgeExamples using (C2-L)
  open import examples.TypeCheck using (tf)

  -- inside the Inst boundary `+X^αᴿ`: X right-only, its opening permitted
  Wi : World empty RB.ΔRₓ
  Wi = W₃ ⊕ʳ^ 0

  Wi¹ : World empty RB.ΔRₓ
  Wi¹ = Wi +κ (0 ∷ [])

  push₀ : ∀ {M} → Value M
    → PushD TIE.Θ₀ M [] (opn 0 ∷ []) (opn 0 ∷ [])
  push₀ v = pushD cs-[] f-end (ns-opn refl ∷ []) (inj₂ v)

  ok₀ : All (SlotOK Wi) (opn 0 ∷ [])
  ok₀ = slots-ok {W = record Wi { πʷ = 0 ∷ [] }} (wf-pending Wi₃-wf)

  ne₀ : AllPairs SlotNe (opn 0 ∷ [])
  ne₀ = [] ∷ []

  jo₀ : JoinRep Wi [] TIE.Θ₀ (opn 0 ∷ []) 0
  jo₀ = jr-open oh here

  wf¹ : WfWorldᴰ Wi¹
  wf¹ = wf+κ (wfᴰ⁰ Wi₃-wf) ((_ , here) ∷ [])

  -- the opened index ∀X.X→X ⊑^[X] X→X: X ⊑ X
  pay₀ : `∀ (` 0 ⇒ ` 0) ⊑ᴰ⟨ Wi ∣ opn 0 ∷ [] ⟩ (` 0 ⇒ ` 0)
  pay₀ = ⇒⊑⇒ X⊑X X⊑X

  -- ... and inside, with X permitted: ∀X.X→X ⊑^[X] ★→★
  open★ : `∀ (` 0 ⇒ ` 0) ⊑ᴰ⟨ Wi¹ ∣ opn 0 ∷ [] ⟩ (★ ⇒ ★)
  open★ = ⇒⊑⇒ (X⊑★ here) (X⊑★ here)

  -- C2 X0's (and G1's) body: the left gen value against the right's
  -- `[−X^α] (λx:★. x)…⟨X! → X?⟩`: ⊑cast at X⊑★ (X permitted), then the
  -- gen CONSUMES the opening, then the right's hide
  c2-body : Wi¹ ∣ [] ⊢ I★genI ⊑ᴰ I★gen ∶⟨ `∀ (` 0 ⇒ ` 0) , ` 0 ⇒ ` 0 ⟩[
    opn 0 ∷ [] ] ⇒⊑⇒ X⊑X X⊑X
  c2-body =
    ⊑cast
      (cast⊑ (co-gen (V-simple S-ƛ) co-plain)
        (toD (R.⊑⟪⟫ IntN R.push-none (W₃-wf p0)
               (R.ƛ⊑ƛ {pA = ★⊑★} wf-★ wf-★ (R.x⊑x Zʷ)) I★⁻ᴿ-ty
               (⇒⊑⇒ ★⊑★ ★⊑★)) it)
        genIᴸ-ty open★)
      tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X)

  c2-core : W₃ ∣ [] ⊢ I★genI ⊑ᴰ Bg ∶[ [] ] ∀id⊑★ W₃
  c2-core =
    ⊑⟪⟫ (int⁰ int-ro₃) (push₀ vI★genI) ok₀ ne₀ (jo₀ ∷ []) wf¹ pay₀ c2-body
      Bg-ty (∀id⊑★ W₃)

  c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ᴰ Cg-R₂ ∶[ [] ] TIE.ℕ⊑★
  c2-x0 =
    ·⊑·
      (ν⊑ (⊑cast c2-core id★↦ᴿ-ty (∀id⊑★ W₃)) TIE.ℕ⊑★ C2-L-ν-ty
        (ℕ⇒ℕ⊑★⇒★ W₃))
      (toD (five⊑ {Ω = 0} {ηᴸ = []↪} {ηᴿ = []↪} {γ = []}) it)

  -- Cg X0: the left Λ JOINS the opening (b-join); inside, the gen
  -- wrapper is peeled at the joined, permitted X
  cg-core : W₃ ∣ [] ⊢ Λ TIE.idX ⊑ᴰ Bg ∶[ [] ] ∀id⊑★ W₃
  cg-core =
    ⊑⟪⟫ (int⁰ int-ro₃) (push₀ vΛidX) ok₀ ne₀ (jo₀ ∷ []) wf¹ pay₀
      (Λ⊑ (b-join (join1 join-here here r-here)) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[]
        (V-simple S-ƛ)
        (⊑cast {A = ` 0 ⇒ ` 0}
          (toD (R.⊑⟪⟫ Wg⁻-int R.push-none (Wg⁻-wf p0)
                 (R.ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (R.x⊑x Zʷ))
                 I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺¹} here)) it)
          tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
        (⇒⊑⇒ X⊑X X⊑X))
      Bg-ty (∀id⊑★ W₃)

  cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ᴰ Cg-R₂ ∶[ [] ] TIE.ℕ⊑★
  cg-x0 =
    ·⊑·
      (ν⊑ (⊑cast cg-core id★↦ᴿ-ty (∀id⊑★ W₃)) TIE.ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
      (toD (five⊑ {Ω = 0} {ηᴸ = []↪} {ηᴿ = []↪} {γ = []}) it)

  -- G1 (DGG part 1 pair from related sources): the final pair
  g1-final : W₃ ∣ [] ⊢ NP.C2X0.G-L ⊑ᴰ NP.C2X0.G-R₂ ∶[ [] ] ∀id⊑★ W₃
  g1-final = ⊑cast c2-core id★↦ᴿ-ty (∀id⊑★ W₃)

  g1-init = toD NP.C2X0.g1-init-real it

-- 6f. P5 (no derivation existed for the real relation; derived here
-- from its programs): the left blames on an escaped tag, the right
-- succeeds.  The initial pair; the pair before the left's TagUntagBad-⟪⟫
-- (the left's seal is a payload view under its own `+X`, X left-only:
-- R1′ reads the seal's exterior X, and α has no partner); the blame.
module P5ᴰ where
  open import examples.ImprecisionExamples using (L5; R5; L5-⊢; R5-⊢)
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.Examples using (ℓ; μX)
  open PE.P4 using (nth; S; bS)
  open TIE using (ΔL; ΔLᵢ; W₂; Wᵢ₂; Wᵢ₂-int; Wᵢ₂-wf; ℕ⊑★)

  ι : ∀ {μ} → μ ⊢ `ℕ ⊑ `ℕ
  ι = ι⊑ι base-ℕ

  ℕ?-ty : ∀ {Ξ} → CastTy (Ξ ∣ []) [] (`ℕ ？ ℓ) ★ `ℕ
  ℕ?-ty = cast-ty (⊢check g-ℕ) refl

  idℕ⊑ : ∀ {W : World Δ Δ′} {γ}
    → W ∣ γ ⊢ ƛ `ℕ ∙ ` 0 ⊑ᴰ ƛ `ℕ ∙ ` 0 ∶[ [] ] ⇒⊑⇒ ι ι
  idℕ⊑ = ƛ⊑ƛ {pA = ι} {pB = ι} wf-ℕ wf-ℕ (x⊑x Zʷ)

  five : ∀ {Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ}
    → W ∣ γ ⊢ $ 5 ⊑ᴰ TIE.5⟨ℕ!⟩ ∶[ [] ] ℕ⊑★
  five = ⊑cast (κ⊑κ lit-$ ι) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

  -- the initial pair: ν⊑ over Λ⊑ (Y left-only); the left's tag x⟨Y!⟩
  -- against the right's x by cast⊑
  inner-ty : NuTy empty `ℕ (` 0 ⇒ ★) (reveal 0 (` 0 ⇒ ★)) (`ℕ ⇒ ★)
  inner-ty = proj₂ (proj₂ (R.ν-inv {Γ = []}
    (tc {Δ = empty} {M = examples.Examples.ex4-inner})))

  tagY-ty : CastTy (underΛ empty) μX ((` 0) !) (` 0) ★
  tagY-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  init : ∅ʷ ∣ [] ⊢ L5 ⊑ᴰ R5 ∶[ [] ] ι
  init =
    ·⊑· idℕ⊑
      (cast⊑cast
        (·⊑· {pA = ℕ⊑★} {pB = ★⊑★}
          (ν⊑
            (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
              (ƛ⊑ƛ {pA = X⊑★ here} {pB = ★⊑★} tf wf-★
                (·⊑· {pA = ★⊑★} {pB = ★⊑★}
                  (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} wf-★ wf-★ (x⊑x Zʷ))
                  (cast⊑ co-plain (x⊑x Zʷ) tagY-ty ★⊑★)))
              (∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) ★⊑★)))
            ℕ⊑★ inner-ty (⇒⊑⇒ ℕ⊑★ ★⊑★))
          five)
        ℕ?-ty ℕ?-ty ι)

  -- the left's state 4 against the right's state 2
  T L₄ R₂ : Term
  T  = (S ⟨ μX ∣ (` 0) ! ⟩) ⟪ PE.Θ₀ , ⌞ id ★ ⌟ ⟫
  L₄ = (ƛ `ℕ ∙ ` 0) · (T ⟨ [] ∣ `ℕ ？ ℓ ⟩)
  R₂ = (ƛ `ℕ ∙ ` 0) · (TIE.5⟨ℕ!⟩ ⟨ [] ∣ `ℕ ？ ℓ ⟩)

  L₄-state : nth (evalTerms 20 L5-⊢) 4 ≡ L₄
  L₄-state = refl

  R₂-state : nth (evalTerms 20 R5-⊢) 2 ≡ R₂
  R₂-state = refl

  bT : BdyTy ΔL PE.Θ₀ ΔLᵢ ★ ⌞ id ★ ⌟ ★
  bT = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = T}))))

  tagX-ty : CastTy ΔLᵢ μX ((` 0) !) (` 0) ★
  tagX-ty = cast-ty (⊢tag-var (_ , here) here tag-cross) refl

  -- the left's seal alone: X goes away
  intS : Interior Wᵢ₂ (unbind 0 0 ∷ []) [] W₂
  intS = record
    { int-left   = RB.unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  wf₂ : WfWorldᴰ W₂
  wf₂ = wfᴰ joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ }) []

  p5-mid : W₂ ∣ [] ⊢ L₄ ⊑ᴰ R₂ ∶[ [] ] ι
  p5-mid =
    ·⊑· idℕ⊑
      (cast⊑cast
        (⟪⟫⊑ Wᵢ₂-int (ok-bind′ ∷ []) bo-plain [] (wf→ᴰ Wᵢ₂-wf) ★⊑★
          (cast⊑ co-plain
            (⟪⟫⊑ intS (ok-unbind′ (λ { (inj₁ ()) ; (inj₂ ()) }) ∷ [])
              bo-plain [] wf₂ ℕ⊑★ five bS (X⊑★ here))
            tagX-ty ★⊑★)
          bT ★⊑★)
        ℕ?-ty ℕ?-ty ι)

  -- the left blames; blame ⊑ anything
  fin : W₂ ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) · blame ℓ ⊑ᴰ (ƛ `ℕ ∙ ` 0) · $ 5 ∶[ [] ] ι
  fin = ·⊑· idℕ⊑ (blame⊑ wf-ℕ ⊢$ ι)

-- 6g. R2c (ForallBoundaryRisks §3; its old derivations no longer
-- check): a left gen-cast value over a boundary value against the
-- right's Inst boundary, before and after the right's Merge INSIDE it.
--   L  (λh:∀X.X→X. h) ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
--   R  (λh:★→★. h)    ((λg:∀X.X→X. g) ((ΛX.λx:X.x)[★]))
-- The Inst boundary +Y^β OPENS the left's ∀ at Y and permits β; the
-- right's gen wrapper is peeled at Y⊑★; the left's gen CONSUMES the
-- opening; then the matched +X ∥ +X (before the Merge: under the
-- right's −Y; after it: one merged −Y, +X boundary).
module R2cᴰ where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I; genI; instI)
  open import proof.ImprecisionWorld using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[];
    ≤1-∷[])
  open TIE using (idX; revX; ∀X⇒X; Θ₀; ΔR; revX⊑revX)
  open RB using (id★↦; id★→; tagX↦; ∀id⊑★)
  open PE.P4 using (nth)

  I[★] Gc L2c R2c : Term
  I[★] = ν ★ · I ⟨ revX ⟩
  Gc   = (ƛ ∀X⇒X ∙ ` 0) · (I[★] ⟨ [] ∣ genI ⟩)
  L2c  = (ƛ ∀X⇒X ∙ ` 0) · Gc
  R2c  = (ƛ (★ ⇒ ★) ∙ ` 0) · (Gc ⟨ [] ∣ instI ⟩)

  L2c-⊢ : empty ∣ [] ⊢ L2c ⦂ ∀X⇒X
  L2c-⊢ = tc

  R2c-⊢ : empty ∣ [] ⊢ R2c ⦂ (★ ⇒ ★)
  R2c-⊢ = tc

  Θ₁ Θm : Boundary
  Θ₁ = bind 0 1 ∷ []
  Θm = bind 0 1 ∷ unbind 0 0 ∷ []

  Bα V2 L2c₂ Bin Nu N N₀ R2c₄ R2c₅ : Term
  Bα   = idX ⟪ Θ₀ , revX ⟫
  V2   = Bα ⟨ [] ∣ genI ⟩
  L2c₂ = (ƛ ∀X⇒X ∙ ` 0) · V2
  Bin  = idX ⟪ Θ₁ , revX ⟫
  Nu   = Bin ⟪ unbind 0 0 ∷ [] , id★→ ⟫
  N    = Nu ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
  N₀   = (idX ⟪ Θm , revX ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
  R2c₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
  R2c₅ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N₀ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)

  L2c₂-state : nth (evalTerms 20 L2c-⊢) 2 ≡ L2c₂
  L2c₂-state = refl

  R2c₄-state : nth (evalTerms 20 R2c-⊢) 4 ≡ R2c₄
  R2c₄-state = refl

  R2c₅-state : nth (evalTerms 20 R2c-⊢) 5 ≡ R2c₅
  R2c₅-state = refl

  vBα : Value Bα
  vBα = V-⟪⟫ S-ƛ I-fun

  vV2 : Value V2
  vV2 = V-simple (S-cast vBα I-gen)

  -- contexts: left αᴸ:=★ (rep. var 0); right β:=★ (0, the Inst's), αᴿ:=★ (1)
  ΞR : RepCtx
  ΞR = bindR ★ ∷ bindR ★ ∷ []

  ΔR2 ΔRY ΔRX ΔLX : Ctxᵗ
  ΔR2 = ΞR ∣ []
  ΔRY = ΞR ∣ (0 ∷ [])
  ΔRX = ΞR ∣ (1 ∷ [])
  ΔLX = (bindR ★ ∷ []) ∣ (0 ∷ [])

  ϱ : RepRel
  ϱ = (0 , 1) ∷ []

  -- the worlds (κ = the permission of β where it holds)
  W4 : World ΔR ΔR2
  W4 = world 0 []↪ []↪ ϱ [] [] []

  W4¹ : World ΔR ΔR2
  W4¹ = world 0 []↪ []↪ ϱ [] (0 ∷ []) []

  Wy : World ΔR ΔRY
  Wy = world 1 (skip []↪) (keep []↪) ϱ [] [] []

  Wb : World ΔLX ΔRX
  Wb = world 1 (keep []↪) (keep []↪) ϱ [] (0 ∷ []) []

  agreeR : ∀ {n nsL nsR κ} {η : nsL ↪ n} {η′ : nsR ↪ n} {α β}
    → let W = world {(bindR ★ ∷ []) ∣ nsL} {ΞR ∣ nsR} n η η′ ϱ [] κ [] in
      Paired W α β → Agree W α β
  agreeR (inj₁ here⇔) = rep-rep r-here (r-there r-here) ★⊑★
  agreeR (inj₁ (there⇔ ()))
  agreeR (inj₂ ())

  -- +Y^β alone: Y right-only, opened
  intY : Interior W4 [] Θ₀ Wy
  intY = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  okY : All (SlotOK Wy) (opn 0 ∷ [])
  okY = (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

  wfY¹ : WfWorldᴰ (Wy +κ (0 ∷ []))
  wfY¹ = wfᴰ (right-only joint[]) agreeR (namedᴸ-≤1 W ≤1-[])
    (namedᴿ-≤1 W ≤1-∷[]) ((_ , here) ∷ [])
    where W = Wy +κ (0 ∷ [])

  wf4¹ : WfWorldᴰ W4¹
  wf4¹ = wfᴰ joint[] agreeR (namedᴸ-≤1 W4¹ ≤1-[]) (namedᴿ-≤1 W4¹ ≤1-[])
    ((_ , here) ∷ [])

  wfb : WfWorldᴰ (Wb +κ [])
  wfb = wfᴰ (both (inj₁ here⇔) joint[]) agreeR (namedᴸ-≤1 Wb ≤1-∷[])
    (namedᴿ-≤1 Wb ≤1-∷[]) ((_ , here) ∷ [])

  -- the right's −Y alone, under β's permission
  intU : Interior (Wy +κ (0 ∷ [])) [] (unbind 0 0 ∷ []) W4¹
  intU = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  bindL : ΔR ⊢ⁱ Θ₀ ⇒ ΔLX
  bindL = interior (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

  bindLc : ΔR ⊢ᶜ Θ₀ ⇒ ΔLX
  bindLc = conversion (conv-bind (_ , here) conv[] fresh[] ins-here)

  -- the matched +X ∥ +X (αᴸ, αᴿ paired in ϱᵍ: X joins)
  intB : Interior W4¹ Θ₀ Θ₁ Wb
  intB = record
    { int-left   = bindL
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , there here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  intBc : ConversionInterior W4¹ Θ₀ Θ₁ Wb
  intBc = record
    { conv-left       = bindLc
    ; conv-right      = conversion (conv-bind (_ , there here) conv[] fresh[]
                          ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  -- typing side premises, read off `tc`
  genI-ty : CastTy ΔR [] genI (★ ⇒ ★) ∀X⇒X
  genI-ty = proj₂ (proj₂ (R.cast-inv {Γ = []} (tc {Δ = ΔR} {M = V2})))

  tag-ty : CastTy ΔRY (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tag-ty = proj₂ (proj₂ (R.cast-inv {Γ = []} (tc {Δ = ΔRY} {M = N})))

  tag₀-ty : CastTy ΔRY (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tag₀-ty = proj₂ (proj₂ (R.cast-inv {Γ = []} (tc {Δ = ΔRY} {M = N₀})))

  bBα : BdyTy ΔR Θ₀ ΔLX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBα = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = Bα}))))

  bBin : BdyTy ΔR2 Θ₁ ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bBin = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = ΔR2} {M = Bin}))))

  bNu : BdyTy ΔRY (unbind 0 0 ∷ []) ΔR2 (★ ⇒ ★) id★→ (★ ⇒ ★)
  bNu = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = ΔRY} {M = Nu}))))

  bM : BdyTy ΔRY Θm ΔRX (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bM = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []}
    (tc {Δ = ΔRY} {M = idX ⟪ Θm , revX ⟫}))))

  bOut₄ : BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOut₄ = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR2} {M = N ⟪ Θ₀ , revX ⟫}))))

  bOut₅ : BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
  bOut₅ = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR2} {M = N₀ ⟪ Θ₀ , revX ⟫}))))

  id★↦-ty : CastTy ΔR2 [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
  id★↦-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

  idX⊑ : Wb ∣ [] ⊢ idX ⊑ᴰ idX ∶[ [] ] ⇒⊑⇒ X⊑X X⊑X
  idX⊑ = ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)

  Bα⊑Bin : W4¹ ∣ [] ⊢ Bα ⊑ᴰ Bin ∶[ [] ] ⇒⊑⇒ ★⊑★ ★⊑★
  Bα⊑Bin = ⟪⟫⊑⟪⟫ intB [] wfb (⇒⊑⇒ X⊑X X⊑X) idX⊑ bBα bBin
    (Wb , intBc , revX⊑revX refl) (⇒⊑⇒ ★⊑★ ★⊑★)

  -- the Inst boundary: open Y, permit β (pay: ∀X.X→X ⊑^[Y] Y→Y)
  instB : ∀ {M′} {r : ∀X⇒X ⊑ᴰ⟨ Wy +κ (0 ∷ []) ∣ opn 0 ∷ [] ⟩ (` 0 ⇒ ` 0)}
    → Wy +κ (0 ∷ []) ∣ [] ⊢ V2 ⊑ᴰ M′ ∶[ opn 0 ∷ [] ] r
    → BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → W4 ∣ [] ⊢ V2 ⊑ᴰ (M′ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩ ∶[ [] ] ∀id⊑★ W4
  instB d b =
    ⊑cast
      (⊑⟪⟫ intY (pushD cs-[] f-end (ns-opn refl ∷ []) (inj₂ vV2)) okY
        ([] ∷ []) (jr-open oh here ∷ []) wfY¹ (⇒⊑⇒ X⊑X X⊑X) d b
        (∀id⊑★ W4))
      id★↦-ty (∀id⊑★ W4)

  outer : ∀ {M′} {r : ∀X⇒X ⊑ᴰ⟨ Wy +κ (0 ∷ []) ∣ opn 0 ∷ [] ⟩ (` 0 ⇒ ` 0)}
    → Wy +κ (0 ∷ []) ∣ [] ⊢ V2 ⊑ᴰ M′ ∶[ opn 0 ∷ [] ] r
    → BdyTy ΔR2 Θ₀ ΔRY (` 0 ⇒ ` 0) revX (★ ⇒ ★)
    → W4 ∣ [] ⊢ L2c₂ ⊑ᴰ (ƛ (★ ⇒ ★) ∙ ` 0) · ((M′ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
        ∶[ [] ] ∀id⊑★ W4
  outer d b = ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ)) (instB d b)

  -- before the right's Merge
  r2c-pre : W4 ∣ [] ⊢ L2c₂ ⊑ᴰ R2c₄ ∶[ [] ] ∀id⊑★ W4
  r2c-pre = outer
    (⊑cast {A = ∀X⇒X}
      (cast⊑ (co-gen vBα co-plain)
        (⊑⟪⟫₀ intU wf4¹ Bα⊑Bin bNu (⇒⊑⇒ ★⊑★ ★⊑★))
        genI-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tag-ty (⇒⊑⇒ X⊑X X⊑X))
    bOut₄

  -- after it: the merged −Y, +X on the right; the conversion contexts
  -- keep Y (center 1, right-only)
  Wcm : World ΔLX (ΞR ∣ (1 ∷ 0 ∷ []))
  Wcm = world 2 (keep (skip []↪)) (keep (keep []↪)) ϱ [] (0 ∷ []) []

  intM : Interior (Wy +κ (0 ∷ [])) Θ₀ Θm Wb
  intM = record
    { int-left   = bindL
    ; int-right  = interior (changes∷
        (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
        (step-bind (_ , there here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  intMc : ConversionInterior (Wy +κ (0 ∷ [])) Θ₀ Θm Wcm
  intMc = record
    { conv-left       = bindLc
    ; conv-right      = conversion (conv-bind (_ , there here)
        (conv-unbind (_ , here) conv[]) (fresh∷ (λ ()) fresh[]) ins-here)
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ
        { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ ()) })
        ; here (there (there ())) _
        ; (there ()) _ _
        }
    }

  r2c-post : W4 ∣ [] ⊢ L2c₂ ⊑ᴰ R2c₅ ∶[ [] ] ∀id⊑★ W4
  r2c-post = outer
    (⊑cast {A = ∀X⇒X}
      (cast⊑ (co-gen vBα co-plain)
        (⟪⟫⊑⟪⟫ intM [] wfb (⇒⊑⇒ X⊑X X⊑X) idX⊑ bBα bM
          (Wcm , intMc , revX⊑revX refl) (⇒⊑⇒ ★⊑★ ★⊑★))
        genI-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tag₀-ty (⇒⊑⇒ X⊑X X⊑X))
    bOut₅

  -- the final pair (left state 3, right state 6): DGG part 1's witness
  R2c₆ : Term
  R2c₆ = (N₀ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩

  R2c₆-state : nth (evalTerms 20 R2c-⊢) 6 ≡ R2c₆
  R2c₆-state = refl

  V2-state : nth (evalTerms 20 L2c-⊢) 3 ≡ V2
  V2-state = refl

  r2c-final : W4 ∣ [] ⊢ V2 ⊑ᴰ R2c₆ ∶[ [] ] ∀id⊑★ W4
  r2c-final = instB
    (⊑cast {A = ∀X⇒X}
      (cast⊑ (co-gen vBα co-plain)
        (⟪⟫⊑⟪⟫ intM [] wfb (⇒⊑⇒ X⊑X X⊑X) idX⊑ bBα bM
          (Wcm , intMc , revX⊑revX refl) (⇒⊑⇒ ★⊑★ ★⊑★))
        genI-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      tag₀-ty (⇒⊑⇒ X⊑X X⊑X))
    bOut₅

------------------------------------------------------------------------
-- 7. THE FIXED PAIRS.  P4k and P4h (ReductionAudit: `¬ Sim` under D28):
-- the pair after both TyBetas is now related, so the left's TyBeta from
-- the related ν pair (`CorpusA.p4k-pre`, `p4h-pre`) is caught up by the
-- right's matched TyBeta.  TwoGen's seven final pairs (`¬ DGG` under
-- D28): each is related at the top-level world the right's run ends in
-- (no permission, no opening), so DGG part 1's witness exists.
------------------------------------------------------------------------

-- a world with its permissions replaced and its πʷ emptied
infix 10 _⟨κ:=_⟩
_⟨κ:=_⟩ : World Δ Δ′ → List RVar → World Δ Δ′
W ⟨κ:= κ ⟩ = record W { κʷ = κ ; πʷ = [] }

intκ : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ → (κ : List RVar)
  → Interior (W ⟨κ:= κ ⟩) Θ Θ′ (Wᵢ ⟨κ:= κ ⟩)
intκ I κ = record
  { int-left = int-left I ; int-right = int-right I
  ; same-ϱᵍ = same-ϱᵍ I ; same-ϱˡ = same-ϱˡ I ; same-κ = refl
  ; join-cont = join-cont I ; join-fresh = join-fresh I }

slotsW : ∀ {W W′ : World Δ Δ′} → (∀ {k} → PendingOK W k → PendingOK W′ k)
  → ∀ {O} → All (SlotOK W) O → All (SlotOK W′) O
slotsW f {[]}        []       = []
slotsW f {opn k ∷ O} (p ∷ ps) = f p ∷ slotsW f ps
slotsW f {skp ∷ O}   (p ∷ ps) = tt ∷ slotsW f ps

wfκ : ∀ {W : World Δ Δ′} {κ} → WfWorld W → All (reps Δ′ ∋ʳ_) κ
  → WfWorldᴰ (W ⟨κ:= κ ⟩)
wfκ {W = W} {κ} wf ps = wfᴰ (wf-joint wf)
  (λ pr → agreeW {W = W} {W′ = W ⟨κ:= κ ⟩} (λ p → p) (wf-agree wf pr))
  (wf-namedᴸ wf) (wf-namedᴿ wf) ps

module P4kᴰ where
  open RA.P4k using (LB; RB; L₂; R₂; IF; UF; pF; cK⊑cK)
  open PE.P4 using (v₀; W₄; W₄²; W₄²¹; W₄²¹-wf; W₄ᴸ-wf)
  open RB using (Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ)
  open CorpusB using (jr₀)
  open import examples.TypeCheck using (tc; tf)

  bLB : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ (` 0 ⇒ `ℕ) RA.cK (`ℕ ⇒ `ℕ)
  bLB = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = LB}))))

  bRB : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ (` 0 ⇒ `ℕ) RA.cK (`ℕ ⇒ `ℕ)
  bRB = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = RB}))))

  pF-ty : CastTy TIE.ΔLᵢ (★∼X ∷ []) pF (★ ⇒ `ℕ) (` 0 ⇒ `ℕ)
  pF-ty = proj₂ (proj₂ (R.cast-inv {Γ = []} (tc {Δ = TIE.ΔLᵢ} {M = IF})))

  bUF : BdyTy TIE.ΔLᵢ (unbind 0 0 ∷ []) TIE.ΔL (★ ⇒ `ℕ)
    (tail (mid (tail (mid (id ★)) ↦ tail (mid (id `ℕ))))) (★ ⇒ `ℕ)
  bUF = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔLᵢ} {M = UF}))))

  -- inside the matched +X, αᴿ permitted: the left's λx:X. 5 against the
  -- gen wrapper (peeled at X→ℕ ⊑ ★→ℕ, no grant), and against its body
  body : W₄²¹ ∣ [] ⊢ ƛ (` 0) ∙ $ 5 ⊑ᴰ UF ∶[ [] ] ⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ)
  body =
    ⊑⟪⟫₀ (Wc-unbindᴿ v₀) (wf→ᴰ W₄ᴸ-wf)
      (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (κ⊑κ lit-$ (ι⊑ι base-ℕ))) bUF
      (⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ))

  fun : W₄²¹ ∣ [] ⊢ ƛ (` 0) ∙ $ 5 ⊑ᴰ IF ∶[ [] ] ⇒⊑⇒ X⊑X (ι⊑ι base-ℕ)
  fun = ⊑cast {A = ` 0 ⇒ `ℕ} body pF-ty (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ))

  -- THE TyBeta PAIR IS RELATED: the matched +X permits αᴿ (K = [0]),
  -- paying with X→ℕ ⊑ X→ℕ at X⊑X; inside, the gen wrapper `X! → id(ℕ)`
  -- is peeled at X→ℕ ⊑ ★→ℕ with no grant
  post : W₄ ∣ [] ⊢ L₂ ⊑ᴰ R₂ ∶[ [] ] ι⊑ι base-ℕ
  post =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf)
        (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ)) fun
        bLB bRB (W₄² , Wc-bind²-conv v₀ here⇔ , cK⊑cK refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  -- ... and the run goes on: the left's Wrap against the right's Wrap
  -- (state 3, 3) and the right's CastFun (state 3, 4; D28's R12 site).
  -- The Wrap duals are the matched seals `[−X^α] 5 ⟨−X⟩`
  open PE.P4 using (S; S⊑Sκ; tagˣ-ty; p0)
  open RA.P4k using (nth)
  open import examples.Eval using (evalTerms)

  L₃ R₃ R₄ : Term
  L₃ = ((ƛ (` 0) ∙ $ 5) · S) ⟪ TIE.Θ₀ , ⌞ id `ℕ ⌟ ⟫
  R₃ = (IF · S) ⟪ TIE.Θ₀ , ⌞ id `ℕ ⌟ ⟫
  R₄ = ((UF · (S ⟨ X∼★ ∷ [] ∣ (` 0) ! ⟩)) ⟨ ★∼X ∷ [] ∣ idᵖ `ℕ ⟩)
         ⟪ TIE.Θ₀ , ⌞ id `ℕ ⌟ ⟫

  L₃-state : nth (evalTerms 10 RA.LK-⊢) 3 ≡ L₃
  L₃-state = refl

  R₃-state : nth (evalTerms 20 RA.RK-⊢) 3 ≡ R₃
  R₃-state = refl

  R₄-state : nth (evalTerms 20 RA.RK-⊢) 4 ≡ R₄
  R₄-state = refl

  bL₃ : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bL₃ = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = L₃}))))

  bR₃ : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bR₃ = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = R₃}))))

  bR₄ : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bR₄ = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = R₄}))))

  idℕ-ty : CastTy TIE.ΔLᵢ (★∼X ∷ []) (idᵖ `ℕ) `ℕ `ℕ
  idℕ-ty = cast-ty (⊢id atom-ℕ wf-ℕ) refl

  idℕ⊑ : ConvImp W₄² ⌞ id `ℕ ⌟ ⌞ id `ℕ ⌟
  idℕ⊑ = conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ)))

  S⊑S : W₄²¹ ∣ [] ⊢ S ⊑ᴰ S ∶[ [] ] X⊑X
  S⊑S = toD (S⊑Sκ p0) it

  wrap : W₄ ∣ [] ⊢ L₃ ⊑ᴰ R₃ ∶[ [] ] ι⊑ι base-ℕ
  wrap =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf) (ι⊑ι base-ℕ)
      (·⊑· {pA = X⊑X} fun S⊑S)
      bL₃ bR₃ (W₄² , Wc-bind²-conv v₀ here⇔ , idℕ⊑) (ι⊑ι base-ℕ)

  castfun : W₄ ∣ [] ⊢ L₃ ⊑ᴰ R₄ ∶[ [] ] ι⊑ι base-ℕ
  castfun =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf) (ι⊑ι base-ℕ)
      (⊑cast (·⊑· {pA = X⊑★ here} body (⊑cast S⊑S tagˣ-ty (X⊑★ here)))
        idℕ-ty (ι⊑ι base-ℕ))
      bL₃ bR₄ (W₄² , Wc-bind²-conv v₀ here⇔ , idℕ⊑) (ι⊑ι base-ℕ)

module P4hᴰ where
  open RA.P4h using (LB; RB; L₃; R₃; IF; UF; pI; H₀; idℕ; bodyL; bodyR;
    idℕ⇒ℕ; id★⇒★)
  open PE.P4 using (v₀; W₄; W₄²; W₄²¹; W₄²¹-wf; W₄ᴸ-wf; W₄⁰; W₄⁰-wf; p0;
    bdy-wf)
  open RB using (Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; c⊑c²; c⊑★²)
  open CorpusB using (jr₀)
  open import examples.TypeCheck using (tc; tf)

  bLB : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ (` 0 ⇒ ` 0) TIE.revX (`ℕ ⇒ `ℕ)
  bLB = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = LB}))))

  bRB : BdyTy TIE.ΔL TIE.Θ₀ TIE.ΔLᵢ (` 0 ⇒ ` 0) TIE.revX (`ℕ ⇒ `ℕ)
  bRB = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔL} {M = RB}))))

  pI-ty : CastTy TIE.ΔLᵢ (★∼X ∷ []) pI (★ ⇒ ★) (` 0 ⇒ ` 0)
  pI-ty = proj₂ (proj₂ (R.cast-inv {Γ = []} (tc {Δ = TIE.ΔLᵢ} {M = IF})))

  bUF : BdyTy TIE.ΔLᵢ (unbind 0 0 ∷ []) TIE.ΔL (★ ⇒ ★) id★⇒★ (★ ⇒ ★)
  bUF = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔLᵢ} {M = UF}))))

  bH : BdyTy TIE.ΔLᵢ (unbind 0 0 ∷ []) TIE.ΔL (`ℕ ⇒ `ℕ) idℕ⇒ℕ (`ℕ ⇒ `ℕ)
  bH = proj₂ (proj₂ (proj₂ (R.⟪⟫-inv {Γ = []} (tc {Δ = TIE.ΔLᵢ} {M = H₀}))))

  -- the left's crossΛ hide alone, inside the right's −X: the left X
  -- goes away; αᴸ is paired with the PERMITTED αᴿ, so R1 would reject it;
  -- R1′ admits it, because its exterior type ℕ→ℕ does not mention α
  intH : Interior (RB.Wcᴸ {PE.P4.Ξ₄} {PE.P4.ϱ₄} (0 ∷ [])) (unbind 0 0 ∷ [])
    [] (W₄⁰ (0 ∷ []))
  intH = record
    { int-left   = bw-interior (proj₂ (bdy-wf bH))
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  H⊑ : ∀ {γ} → RB.Wcᴸ {PE.P4.Ξ₄} {PE.P4.ϱ₄} (0 ∷ []) ∣ γ ⊢ H₀ ⊑ᴰ idℕ
    ∶[ [] ] ⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)
  H⊑ = ⟪⟫⊑ intH (ok-hidden (λ _ → refl) ∷ []) bo-plain [] (wf→ᴰ (W₄⁰-wf p0))
    (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ))
    (ƛ⊑ƛ {pA = ι⊑ι base-ℕ} {pB = ι⊑ι base-ℕ} tf tf (x⊑x Zʷ)) bH
    (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ))

  -- R1 (the real ⟪⟫⊑'s premise) fails at this very step: αᴸ = 0 has the
  -- permitted partner αᴿ = 0
  r1-rejects : ¬ All (UnbindOK (RB.Wcᴸ {PE.P4.Ξ₄} {PE.P4.ϱ₄} (0 ∷ [])))
    (unbind 0 0 ∷ [])
  r1-rejects (ok-unbind u ∷ []) with u (inj₁ here⇔)
  ... | ()

  body⊑ : RB.Wcᴸ {PE.P4.Ξ₄} {PE.P4.ϱ₄} (0 ∷ []) ∣ []
    ⊢ ƛ (` 0) ∙ bodyL ⊑ᴰ ƛ ★ ∙ bodyR ∶[ [] ] ⇒⊑⇒ (X⊑★ here) (X⊑★ here)
  body⊑ =
    ƛ⊑ƛ {pA = X⊑★ here} tf wf-★
      (·⊑· {pA = ι⊑ι base-ℕ}
        (ƛ⊑ƛ {pA = ι⊑ι base-ℕ} {pB = X⊑★ here} tf tf (x⊑x (Sʷ Zʷ)))
        (·⊑· {pA = ι⊑ι base-ℕ} H⊑ (κ⊑κ lit-$ (ι⊑ι base-ℕ))))

  -- THE TyBeta PAIR IS RELATED (R1′ + the binder's permission)
  post : W₄ ∣ [] ⊢ L₃ ⊑ᴰ R₃ ∶[ [] ] ι⊑ι base-ℕ
  post =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) (wf→ᴰ W₄²¹-wf)
        (c⊑c² PE.P4.Ξ₄ PE.P4.ϱ₄ [] 0)
        (⊑cast {A = ` 0 ⇒ ` 0}
          (⊑⟪⟫₀ (Wc-unbindᴿ v₀) (wf→ᴰ W₄ᴸ-wf) body⊑ bUF
            (c⊑★² PE.P4.Ξ₄ PE.P4.ϱ₄ (0 ∷ []) 0 refl))
          pI-ty (c⊑c² PE.P4.Ξ₄ PE.P4.ϱ₄ (0 ∷ []) 0))
        bLB bRB (W₄² , Wc-bind²-conv v₀ here⇔ , TIE.revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

-- TwoGen's seven pairs.  No TwoGen (i): a left gen layer CONSUMES its
-- opening in `cast⊑` (no world change), after the right's cast over the
-- instantiated gen body has been peeled by ⊑cast at the OPENED type
-- variable, which the ⊑⟪⟫ that opened it permitted (paying with the
-- opened interior index at X⊑X).  G2, HR, N2.TwoCast need TwoGen (iii):
-- the outer +Y^β opens [skip, Y] (the left's outer ∀ waits, left-only),
-- and the inner +X^α FILLS the skip with X.
module TwoGenᴰ where
  open TG using (Wm; WYg; W₁h; Wq; wfm; wfYg; wfq; intXYW; intYg; intXg;
    intU2; intUH; vGL; vHL; vK★; vKΛ; vNΛ; gcvGL; gcvHL; genK-ty; ∀gen-ty;
    GL; HL; NΛ; KΛ)
  open import examples.CambridgeExamples using (K★)
  open H1 using (W₄; W₄-wf; cf-ty; ci-ty; bX; bY; q-top; K2)
  open import examples.TypeCheck using (tf)

  κ10 : List RVar
  κ10 = 1 ∷ 0 ∷ []

  p10 : ∀ {b b′ Ξ} → All ((b ∷ b′ ∷ Ξ) ∋ʳ_) κ10
  p10 = (_ , there here) ∷ (_ , here) ∷ []

  -- the merged / inner Inst boundaries' interior: X (type variable 1,
  -- rep. var 1) and Y (type variable 0, rep. var 0), both right-only and
  -- opened
  okm : ∀ {κ} → All (SlotOK (Wm ⟨κ:= κ ⟩)) (opn 1 ∷ opn 0 ∷ [])
  okm {κ} = slotsW {W = Wm ⁰} {W′ = Wm ⟨κ:= κ ⟩} (λ p → p)
    (slots-ok {W = Wm} (wf-pending wfm))

  nem : AllPairs SlotNe (opn 1 ∷ opn 0 ∷ [])
  nem = ((λ ()) ∷ []) ∷ [] ∷ []

  jrXY : ∀ {κ Θ′} → All (JoinRep (Wm ⟨κ:= κ ⟩) [] Θ′ (opn 1 ∷ opn 0 ∷ []))
    (1 ∷ 0 ∷ [])
  jrXY = jr-open oh (there here) ∷ jr-open (ot oh) here ∷ []

  -- K2 opened at X then Y against X→Y→X (any κ: X ⊑ X, Y ⊑ Y)
  qm : ∀ κ → K2 ⊑ᴰ⟨ Wm ⟨κ:= κ ⟩ ∣ opn 1 ∷ opn 0 ∷ [] ⟩ (` 1 ⇒ (` 0 ⇒ ` 1))
  qm _ = ⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)

  -- ... and against ★→★→★ with both permitted
  q★ : K2 ⊑ᴰ⟨ Wm ⟨κ:= κ10 ⟩ ∣ opn 1 ∷ opn 0 ∷ [] ⟩ (★ ⇒ (★ ⇒ ★))
  q★ = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here)))

  K★⊑K★ᴰ : W₄ ⟨κ:= κ10 ⟩ ∣ [] ⊢ K★ ⊑ᴰ K★ ∶[ [] ] ⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)
  K★⊑K★ᴰ = ƛ⊑ƛ {pA = ★⊑★} tf tf
    (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} tf tf (x⊑x (Sʷ Zʷ)))

  -- G2m's (and G2's) gen body: ⊑cast `X! → Y! → X?` at the permitted
  -- X, Y; then BOTH gen layers consume their openings; then the right's
  -- `−Y^β, −X^α`
  bodyK : Wm ⟨κ:= κ10 ⟩ ∣ [] ⊢ GL ⊑ᴰ TG.CK ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
  bodyK =
    ⊑cast
      (cast⊑ (co-gen vK★ (co-gen vK★ co-plain))
        (⊑⟪⟫₀ (intκ intU2 κ10) (wfκ W₄-wf p10) K★⊑K★ᴰ TG.Tys.UK-ty
          (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)))
        genK-ty q★)
      TG.Tys.pK-ty (qm κ10)

  -- the merged boundary opens X then Y and permits both (K = [1, 0])
  merged : ∀ {M M′ c′} {A′ᵢ} {r : K2 ⊑ᴰ⟨ Wm ⟨κ:= κ10 ⟩ ∣ opn 1 ∷ opn 0 ∷ [] ⟩ A′ᵢ}
    → Value M → K2 ⊑ᴰ⟨ Wm ⟨κ:= [] ⟩ ∣ opn 1 ∷ opn 0 ∷ [] ⟩ A′ᵢ
    → Wm ⟨κ:= κ10 ⟩ ∣ [] ⊢ M ⊑ᴰ M′ ∶[ opn 1 ∷ opn 0 ∷ [] ] r
    → BdyTy H1.ΔT2 TG.ΘXY H1.ΔXY A′ᵢ c′ (★ ⇒ (★ ⇒ ★))
    → W₄ ∣ [] ⊢ M ⊑ᴰ M′ ⟪ TG.ΘXY , c′ ⟫ ∶⟨ K2 , ★ ⇒ (★ ⇒ ★) ⟩[ [] ] q-top
  merged v pay d b =
    ⊑⟪⟫ (intκ intXYW []) (pushD cs-[] f-end (ns-opn refl ∷ ns-opn refl ∷ [])
      (inj₂ v)) okm nem jrXY (wfκ wfm p10) pay d b q-top

  g2m-final : W₄ ∣ [] ⊢ GL ⊑ᴰ TG.G2m.GmF ∶[ [] ] q-top
  g2m-final = ⊑cast (merged vGL (qm []) bodyK TG.Tys.BXY-ty) cf-ty q-top

  -- HRm's (and HR's) body: ⊑cast `id(X) → Y! → id(X)` at the permitted
  -- Y; the ∀ layer passes X to the Λ, the gen layer consumes Y; the Λ
  -- JOINS X (b-join); then the right's `−Y^β`
  qH : ∀ κ → `∀ (` 0 ⇒ (★ ⇒ ` 0)) ⊑ᴰ⟨ Wm ⟨κ:= κ ⟩ ∣ opn 1 ∷ [] ⟩
    (` 1 ⇒ (★ ⇒ ` 1))
  qH _ = ⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)

  qH★ : K2 ⊑ᴰ⟨ Wm ⟨κ:= κ10 ⟩ ∣ opn 1 ∷ opn 0 ∷ [] ⟩ (` 1 ⇒ (★ ⇒ ` 1))
  qH★ = ⇒⊑⇒ X⊑X (⇒⊑⇒ (X⊑★ here) X⊑X)

  NΛ⊑NΛᴰ : Wq ⟨κ:= κ10 ⟩ ∣ [] ⊢ NΛ ⊑ᴰ NΛ ∶[ [] ] ⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)
  NΛ⊑NΛᴰ = ƛ⊑ƛ {pA = X⊑X} tf tf
    (ƛ⊑ƛ {pA = ★⊑★} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ)))

  bodyH : Wm ⟨κ:= κ10 ⟩ ∣ [] ⊢ HL ⊑ᴰ TG.CH ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
  bodyH =
    ⊑cast
      (cast⊑ (co-∀ vKΛ (co-gen vKΛ co-plain))
        (Λ⊑ (b-join (join1 (join-there join-here) (there here)
                      (r-there r-here)))
          nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] vNΛ
          (⊑⟪⟫₀ (intκ intUH κ10) (wfκ wfq p10) NΛ⊑NΛᴰ TG.Tys.UH-ty
            (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)))
          (qH κ10))
        ∀gen-ty qH★)
      TG.Tys.pH-ty (qm κ10)

  hrm-final : W₄ ∣ [] ⊢ HL ⊑ᴰ TG.HRm.HmF ∶[ [] ] q-top
  hrm-final = ⊑cast (merged vHL (qm []) bodyH TG.Tys.BXYh-ty) cf-ty q-top

  -- G0: one gen layer, body `X! → id(ℕ)` (no covariant check): the push
  -- permits X; the gen consumes the opening
  module G0ᴰ where
    open CorpusE using (Wi; Wi¹; ok₀; ne₀; jo₀; wf¹)
    open TG.G0 using (vFL; genX5-ty; q0; FR₂)
    open TG using (FL)
    open RB using (IntN; W₃-wf; p0)

    g0-final : TIE.W₃ ∣ [] ⊢ FL ⊑ᴰ FR₂ ∶[ [] ] q0
    g0-final =
      ⊑cast
        (⊑⟪⟫ (int⁰ TIE.int-ro₃) (CorpusE.push₀ vFL) ok₀ ne₀ (jo₀ ∷ []) wf¹
          (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ))
          (⊑cast {A = `∀ (` 0 ⇒ `ℕ)}
            (cast⊑ (co-gen (V-simple S-ƛ) co-plain)
              (toD (R.⊑⟪⟫ IntN R.push-none (W₃-wf p0)
                     (R.ƛ⊑ƛ {pA = ★⊑★} tf tf
                       (R.κ⊑κ lit-$ (ι⊑ι base-ℕ)))
                     TG.Tys.UF-ty (⇒⊑⇒ ★⊑★ (ι⊑ι base-ℕ))) it)
              genX5-ty (⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ)))
            TG.Tys.pF-ty (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ)))
          TG.Tys.BF-ty q0)
        TG.Tys.cF-ty q0

  -- THE SKIP (TwoGen (iii)): at the outer +Y^β, K2's outer ∀ waits
  -- left-only and its inner ∀ opens at Y
  qY : ∀ κ → K2 ⊑ᴰ⟨ WYg ⟨κ:= κ ⟩ ∣ skp ∷ opn 0 ∷ [] ⟩ (★ ⇒ (` 0 ⇒ ★))
  qY _ = nv-∀ , ∈-∀ (∈-⇒ˡ ∈-var) , ⇒⊑⇒ (X⊑★ here) (⇒⊑⇒ X⊑X (X⊑★ here))

  okY : All (SlotOK (WYg ⟨κ:= [] ⟩)) (skp ∷ opn 0 ∷ [])
  okY = tt ∷ slotsW {W = WYg ⁰} {W′ = WYg ⟨κ:= [] ⟩} (λ p → p)
    (slots-ok {W = WYg} (wf-pending wfYg))

  neY : AllPairs SlotNe (skp ∷ opn 0 ∷ [])
  neY = (tt ∷ []) ∷ [] ∷ []

  -- two casts: +Y^β opens [skip, Y] and permits β; +X^α FILLS the skip
  -- with X and permits α; then the merged case's body
  twoCast : ∀ {M M′} → Value M → GenCastValue M
    → Wm ⟨κ:= κ10 ⟩ ∣ [] ⊢ M ⊑ᴰ M′ ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
    → W₄ ∣ [] ⊢ M ⊑ᴰ ((M′ ⟪ H1.ΘX , H1.cX ⟫) ⟨ X∼X ∷ [] ∣ H1.ci ⟩)
        ⟪ H1.ΘY , H1.cY ⟫ ∶⟨ K2 , ★ ⇒ (★ ⇒ ★) ⟩[ [] ] q-top
  twoCast v g d =
    ⊑⟪⟫ (intκ intYg [])
      (pushD cs-[] f-end (ns-skp g ∷ ns-opn refl ∷ []) (inj₂ v)) okY neY
      (jr-open (ot oh) here ∷ []) (wfκ wfYg ((_ , here) ∷ [])) (qY [])
      (⊑cast
        (⊑⟪⟫ (intκ intXg (0 ∷ []))
          (pushD (cs-skp (cs-opn refl cs-[])) (f-fill (f-keep f-end))
            (ns-opn refl ∷ []) (inj₂ v))
          okm nem (jr-open oh (there here) ∷ []) (wfκ wfm p10) (qm (0 ∷ [])) d bX
          (qY (0 ∷ [])))
        ci-ty (qY (0 ∷ [])))
      bY q-top

  g2-final : W₄ ∣ [] ⊢ GL ⊑ᴰ TG.G2.GF ∶[ [] ] q-top
  g2-final = ⊑cast (twoCast vGL gcvGL bodyK) cf-ty q-top

  hr-final : W₄ ∣ [] ⊢ HL ⊑ᴰ TG.HR.HF ∶[ [] ] q-top
  hr-final = ⊑cast (twoCast vHL gcvHL bodyH) cf-ty q-top

  -- N2: nested gen casts.  The outer cast `gen X. ∀Y. …` consumes X and
  -- passes Y; the right's −X^α carries Y; the inner `gen Y. …` consumes
  -- Y
  module N2ᴰ where
    open TG.N2 using (vNL₁; vNL; gcvNL; genY-ty; genX∀-ty; pY-ty; pX-ty;
      UY-ty; UX-ty; BXYn-ty; intUX; intUY; NCX; NF; NmF)
    open TG using (NL)

    qXY : ∀ κ → H1.KY ⊑ᴰ⟨ WYg ⟨κ:= κ ⟩ ∣ opn 0 ∷ [] ⟩ (★ ⇒ (` 0 ⇒ ★))
    qXY _ = ⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★)

    qXYm : H1.KY ⊑ᴰ⟨ Wm ⟨κ:= κ10 ⟩ ∣ opn 0 ∷ [] ⟩ (★ ⇒ (` 0 ⇒ ★))
    qXYm = ⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★)

    qY★ : H1.KY ⊑ᴰ⟨ WYg ⟨κ:= κ10 ⟩ ∣ opn 0 ∷ [] ⟩ (★ ⇒ (★ ⇒ ★))
    qY★ = ⇒⊑⇒ ★⊑★ (⇒⊑⇒ (X⊑★ here) ★⊑★)

    qX★ : K2 ⊑ᴰ⟨ Wm ⟨κ:= κ10 ⟩ ∣ opn 1 ∷ opn 0 ∷ [] ⟩ (★ ⇒ (` 0 ⇒ ★))
    qX★ = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))

    okUX : All (SlotOK (WYg ⟨κ:= κ10 ⟩)) (opn 0 ∷ [])
    okUX = slotsW {W = WYg ⁰} {W′ = WYg ⟨κ:= κ10 ⟩} (λ p → p)
      (slots-ok {W = WYg} (wf-pending wfYg))

    inner : WYg ⟨κ:= κ10 ⟩ ∣ [] ⊢ TG.N2.NL₁ ⊑ᴰ TG.N2.NCY ∶[ opn 0 ∷ [] ] qXY κ10
    inner =
      ⊑cast
        (cast⊑ (co-gen vK★ co-plain)
          (⊑⟪⟫₀ (intκ intUY κ10) (wfκ W₄-wf p10) K★⊑K★ᴰ UY-ty
            (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)))
          genY-ty qY★)
        pY-ty (qXY κ10)

    bodyN : Wm ⟨κ:= κ10 ⟩ ∣ [] ⊢ NL ⊑ᴰ NCX ∶[ opn 1 ∷ opn 0 ∷ [] ] qm κ10
    bodyN =
      ⊑cast
        (cast⊑ (co-gen vNL₁ (co-∀ vNL₁ co-plain))
          (⊑⟪⟫ (intκ intUX κ10) (pushD (cs-opn refl cs-[]) (f-keep f-end) []
                  (inj₁ refl))
            okUX ([] ∷ []) [] (wfκ wfYg p10) (qXY κ10) inner UX-ty qXYm)
          genX∀-ty qX★)
        pX-ty (qm κ10)

    nrm-final : W₄ ∣ [] ⊢ NL ⊑ᴰ NmF ∶[ [] ] q-top
    nrm-final = ⊑cast (merged vNL (qm []) bodyN BXYn-ty) cf-ty q-top

    nr-final : W₄ ∣ [] ⊢ NL ⊑ᴰ NF ∶[ [] ] q-top
    nr-final = ⊑cast (twoCast vNL gcvNL bodyN) cf-ty q-top

------------------------------------------------------------------------
-- 8. THE DEAD PAIRS stay dead: C1 (all routes), C2 (late), C3 (early),
-- C4, C4g (with claim-rep and the new openings), C5 and its hidden
-- variant (matched and one-sided hides).  Each is NOT DERIVABLE in the
-- variant at every top-level world (κʷ ≡ []; C5: any κ), at any
-- openings and in any term context.  A permission can now enter at a
-- JOINING boundary; the proofs read that boundary's payment (`pay`):
-- the joined type variable faces ★ there, at X⊑X, so the join it
-- would pay for is impossible.
------------------------------------------------------------------------

open PE using (NonForall; nf-var; nf-ℕ; nf-𝔹; nf-★; nf-⇒; lookup-unique;
  dmarks-emb; no★-right; no-tag★; var⊑var; var⊑★; G; gℕ; g★; GCast;
  gc-ℕ!; gc-ℕ?; gc-id★; gsrc; gtrg; no-G⊑varᵖ; ct-X!; ct-ℕ!; ct-ℕ?;
  ct-id★; sealed; idX′; ct-X?; joint-pair; bdy-C5)
open RA using (ty-cast; ty-ƛ; ty-$; ty-Λ; dom⊑)

-- an opening at a non-∀ left type: the index is empty
nfO : ∀ {μ e O ρ A B} → NonForall A → OpenO μ e O ρ A B → O ≡ []
nfO {O = []}        _      _  = refl
nfO {O = opn _ ∷ _} nf-var ()
nfO {O = opn _ ∷ _} nf-ℕ   ()
nfO {O = opn _ ∷ _} nf-𝔹   ()
nfO {O = opn _ ∷ _} nf-★   ()
nfO {O = opn _ ∷ _} nf-⇒   ()
nfO {O = skp ∷ _}   nf-var ()
nfO {O = skp ∷ _}   nf-ℕ   ()
nfO {O = skp ∷ _}   nf-𝔹   ()
nfO {O = skp ∷ _}   nf-★   ()
nfO {O = skp ∷ _}   nf-⇒   ()

plainᴰ : ∀ {W : World Δ Δ′} {O A A′} → NonForall A → A ⊑ᴰ⟨ W ∣ O ⟩ A′
  → marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′
plainᴰ {W = W} {O} {A} {A′} nf q =
  subst (λ O → A ⊑ᴰ⟨ W ∣ O ⟩ A′) (nfO {μ = marksʷ W} {e = emb (ηᴿʷ W)}
    {O = O} {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} nf q) q

-- a new opening makes the interior's openings nonempty
fill-∋ᵒ : ∀ {O′ N Oᵢ k} → Fill O′ N Oᵢ → N ∋ᵒ k → Oᵢ ≢ []
fill-∋ᵒ f-end      oh ()
fill-∋ᵒ f-end      (ot _) ()
fill-∋ᵒ (f-keep _) _ ()
fill-∋ᵒ (f-fill _) _ ()

push-∋ᵒ : ∀ {Θ′ M O N Oᵢ k} → PushD Θ′ M O N Oᵢ → N ∋ᵒ k → Oᵢ ≢ []
push-∋ᵒ (pushD _ f _ _) n = fill-∋ᵒ f n

-- no permission can be added
K-none : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ N K}
  → (∀ {β} → ¬ JoinRep Wᵢ Θ Θ′ N β) → All (JoinRep Wᵢ Θ Θ′ N) K → K ≡ []
K-none no []      = refl
K-none no (j ∷ _) = ⊥-elim (no j)

κ-keep : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ K}
  → Interior W Θ Θ′ Wᵢ → K ≡ [] → κʷ W ≡ [] → κʷ (Wᵢ +κ K) ≡ []
κ-keep I refl eκ = trans (same-κ I) eκ

-- the left variable 0, facing ★ at a world without permissions, joins
-- no right variable (THE PAYMENT'S CONSEQUENCE)
no-join★ : ∀ {V : World Δ Δ′} → κʷ V ≡ [] → (` 0) ⊑ᴰ⟨ V ∣ [] ⟩ ★
  → ∀ {X′ β} → Δ′ ∋ᵗ X′ := β → ¬ Joins V 0 X′
no-join★ {V = V} eκ q rh j = no-tag★ {V = V} eκ rh j (var⊑★ q)

-- the left context has the one variable 0
OnlyZero : Ctxᵗ → Set
OnlyZero Δ = ∀ {X} → Δ ∋tv X → X ≡ 0

-- ... so a boundary whose payment puts it against ★ joins nothing
K-pay : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ K}
  → OnlyZero Δᵢ → κʷ Wᵢ ≡ [] → (` 0) ⊑ᴰ⟨ Wᵢ ∣ [] ⟩ ★
  → All (JoinRep Wᵢ Θ Θ′ []) K → K ≡ []
K-pay {Wᵢ = Wᵢ} {Θ} {Θ′} oz eκ q = K-none no
  where
  no : ∀ {β} → ¬ JoinRep Wᵢ Θ Θ′ [] β
  no (jr-join tv rh _ j) with oz tv
  ... | refl = no-join★ {V = Wᵢ} eκ q rh j
  no (jr-open () _)

-- the exterior and interior types of an `id(★)` boundary
bdy-id★ : ∀ {Δ₀ Θ Δᵢ Aᵢ A} → BdyTy Δ₀ Θ Δᵢ Aᵢ ⌞ id ★ ⌟ A
  → (Aᵢ ≡ ★) × (A ≡ ★)
bdy-id★ (bdy-ty _ (conv-tail (conv-mid (conv-id ()))) _ _ _)
bdy-id★ (bdy-ty _ (conv-tail (conv-mid conv-id★)) (_ , same-★ , same-★)
  (_ , same-★ , same-★) _) = refl , refl

G-nf : ∀ {A} → G A → NonForall A
G-nf gℕ = nf-ℕ
G-nf g★ = nf-★

module C3ᴰ where
  open PE.C3 using (LE₁; RE₁; LA; RA; LB₁; RB₁; LE; RE; matched-conv;
    ct-genE-body)
  open TIE using (ΔL)

  no-fun : ∀ {V : World ΔL ΔL} {γ A A′ B B′} {q : A ⊑ᴰ⟨ V ∣ [] ⟩ A′}
    → κʷ V ≡ [] → A ≡ `ℕ ⇒ B → A′ ≡ `ℕ ⇒ B′
    → ¬ (V ∣ γ ⊢ LB₁ ⊑ᴰ RB₁ ∶⟨ A , A′ ⟩[ [] ] q)
  no-fun eκ _ _ (⟪⟫⊑⟪⟫ _ _ _ _ _ b b′ bc _) = matched-conv eκ b b′ bc
  no-fun eκ eA refl
    (⟪⟫⊑ {Wᵢ = Vi} {K = K} {Aᵢ = Aᵢ} {A′ = A′} {O = O} {r = r}
      _ _ _ _ _ _ d _ _)
    with ty-ƛ (ltyD d)
  ... | _ , refl , _
    with plainᴰ {W = Vi +κ K} {O = O} {A = Aᵢ} {A′ = A′} nf-⇒ r
  ... | ⇒⊑⇒ () _
  no-fun eκ refl _
    (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A = A} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} {r = r}
      _ _ _ _ _ _ _ d _ _)
    with ty-cast (rtyD d)
  ... | refl with plainᴰ {W = Vi +κ K} {O = Oᵢ} {A = A} {A′ = A′ᵢ} nf-⇒ r
  ... | ⇒⊑⇒ () _

  no-app : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ᴰ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-app eκ (·⊑· f (κ⊑κ lit-$ _)) = no-fun eκ refl refl f

  no-LAℕ!-RA : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ᴰ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-LAℕ!-RA eκ (cast⊑ co-plain d _ _) = no-app eκ d

  no-LE₁-RA : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LE₁ ⊑ᴰ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-LE₁-RA eκ (cast⊑ co-plain d _ _) = no-LAℕ!-RA eκ d

  no-LA-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ᴰ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  no-LA-RE₁ eκ (⊑cast d _ _) = no-app eκ d

  no-LAℕ!-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ᴰ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  no-LAℕ!-RE₁ eκ (cast⊑cast d _ _ _) = no-app eκ d
  no-LAℕ!-RE₁ eκ (⊑cast d _ _) = no-LAℕ!-RA eκ d
  no-LAℕ!-RE₁ eκ (cast⊑ co-plain d _ _) = no-LA-RE₁ eκ d

  -- C3 IS UNRELATED: every world over (ΔL, ΔL) with no permission, any
  -- openings
  c3-unrelated : ∀ {W : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₁ ⊑ᴰ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  c3-unrelated eκ (cast⊑cast d _ _ _) = no-LAℕ!-RA eκ d
  c3-unrelated eκ (⊑cast d _ _) = no-LE₁-RA eκ d
  c3-unrelated eκ (cast⊑ co-plain d _ _) = no-LAℕ!-RE₁ eκ d

-- THE SPINE (C1, C2).  A right spine of ground casts and `id(★)`
-- boundaries reaching a tag `X!`; a left term outside its own
-- `[+X^α] (sealed m) ⟨+X⟩` under ground casts.  Every boundary on the
-- way is entered with no permission: outside the left boundary nothing
-- left is bound to a type variable (no join); at the left boundary and
-- inside it, the
-- payment reads the left's X against ★ (`K-pay`), so X joins no right
-- variable and no permission is added; the decisive ⊑cast of the tag
-- then needs X ⊑ X′ and X ⊑ ★ at κ = [] (`no-tag★`).
data ReachD : Term → Set where
  r-tag  : ∀ {U μ k} → ReachD (U ⟨ μ ∣ (` k) ! ⟩)
  r-cast : ∀ {R μ c} → GCast c → ReachD R → ReachD (R ⟨ μ ∣ c ⟩)
  r-⟪⟫   : ∀ {R Θ} → ReachD R → ReachD (R ⟪ Θ , ⌞ id ★ ⌟ ⟫)

gc-trg : ∀ {c} → GCast c → G (trgᵖ c)
gc-trg gc-ℕ! = g★
gc-trg gc-ℕ? = gℕ
gc-trg gc-id★ = g★

reach-G : ∀ {Γ R A′} → ReachD R → Δ′ ∣ Γ ⊢ R ⦂ A′ → G A′
reach-G r-tag ⊢R with ty-cast ⊢R
... | refl = g★
reach-G (r-cast gc _) ⊢R with ty-cast ⊢R
... | refl = gc-trg gc
reach-G (r-⟪⟫ _) ⊢R with R.⟪⟫-inv ⊢R
... | _ , _ , _ , b = G-from (proj₂ (bdy-id★ b))
  where
  G-from : ∀ {A} → A ≡ ★ → G A
  G-from refl = g★

module SpineD (m : Term)
  (no-leaf : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R O A A′}
     {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
     → ReachD R → ¬ (V ∣ γ ⊢ m ⊑ᴰ R ∶⟨ A , A′ ⟩[ O ] q))
  (Δ₀ : Ctxᵗ)
  (no-names : ∀ {X} → ¬ (Δ₀ ∋tv X))
  (bdy : ∀ {Δᵢ Aᵢ A} → BdyTy Δ₀ PE.Θ₀ Δᵢ Aᵢ (unseal 0) A
     → (Aᵢ ≡ ` 0) × G A × OnlyZero Δᵢ)
  where

  -- INSIDE the left boundary: the sealed leaf (type X) against the spine
  no-S : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → OnlyZero Δ₁ → κʷ V ≡ [] → A ≡ ` 0 → ReachD R
    → ¬ (V ∣ γ ⊢ sealed m ⊑ᴰ R ∶⟨ A , A′ ⟩[ O ] q)
  no-S {V = V} {O = O} oz eκ refl r-tag (⊑cast {B′ = B′} {p = p} d ct q)
    with ct-X! ct
  ... | (_ , rh) , refl , refl =
    no-tag★ {V = V} eκ rh
      (var⊑var (plainᴰ {W = V} {O = O} {A′ = B′} nf-var p))
      (var⊑★ (plainᴰ {W = V} {O = O} {A′ = ★} nf-var q))
  no-S oz eκ eA (r-cast _ r) (⊑cast d _ _) = no-S oz eκ eA r d
  no-S {Δ₁} {V = V} oz eκ refl (r-⟪⟫ r)
    (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} I pu _ _ ks _ pay d b _)
    with bdy-id★ b
  ... | refl , _ with nfO {O = Oᵢ} nf-var pay
  ... | refl =
    no-S oz (κ-keep I (K-none no ks) eκ) refl r d
    where
    eκᵢ : κʷ Vi ≡ []
    eκᵢ = trans (same-κ I) eκ
    no : ∀ {β} → ¬ JoinRep Vi [] _ _ β
    no (jr-join tv rh _ j) with oz tv
    ... | refl = no-join★ {V = Vi} eκᵢ pay rh j
    no (jr-open n _) = push-∋ᵒ pu n refl
  no-S oz eκ eA r (⟪⟫⊑⟪⟫ _ _ _ _ d _ _ _ _) = no-leaf (r-inner r) d
    where
    r-inner : ∀ {R′ Θ′ c′} → ReachD (R′ ⟪ Θ′ , c′ ⟫) → ReachD R′
    r-inner (r-⟪⟫ r′) = r′
  no-S oz eκ eA r (⟪⟫⊑ _ _ _ _ _ _ d _ _) = no-leaf r d

  B : Term
  B = sealed m ⟪ PE.Θ₀ , unseal 0 ⟫

  data LO : Term → Set where
    lo-B : LO B
    lo-c : ∀ {M c} → GCast c → LO M → LO (M ⟨ [] ∣ c ⟩)

  lo-ty : ∀ {Γ M A} → LO M → Δ₀ ∣ Γ ⊢ M ⦂ A → G A
  lo-ty lo-B ⊢M with R.⟪⟫-inv ⊢M
  ... | _ , _ , _ , b = proj₁ (proj₂ (bdy b))
  lo-ty (lo-c gc _) ⊢M with ty-cast ⊢M
  ... | refl = gc-trg gc

  -- OUTSIDE: the left under its ground casts
  no-LO : ∀ {Δ₂} {V : World Δ₀ Δ₂} {γ M R O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → LO M → ReachD R
    → ¬ (V ∣ γ ⊢ M ⊑ᴰ R ∶⟨ A , A′ ⟩[ O ] q)
  no-LO {V = V} {O = O} eκ lo r-tag
    (⊑cast {A = A} {B′ = B′} {p = p} d ct _) with ct-X! ct
  ... | _ , refl , refl with lo-ty lo (ltyD d)
  ... | g = no-G⊑varᵖ g (plainᴰ {W = V} {O = O} {A = A} {A′ = B′} (G-nf g) p)
  no-LO eκ lo (r-cast _ r) (⊑cast d _ _) = no-LO eκ lo r d
  no-LO eκ (lo-c gc lo) r-tag (cast⊑cast {p = p} d ct ct′ _)
    with ct-X! ct′
  ... | _ , refl , refl = no-G⊑varᵖ (gsrc gc ct) p
  no-LO eκ (lo-c gc lo) (r-cast _ r) (cast⊑cast d _ _ _) = no-LO eκ lo r d
  no-LO eκ (lo-c gc lo) r (cast⊑ co-plain d _ _) = no-LO eκ lo r d
  no-LO {V = V} eκ lo (r-⟪⟫ r)
    (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A = A} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} I pu _ _ ks _ pay
      d b _) =
    no-LO (κ-keep I (K-none no ks) eκ) lo r d
    where
    no : ∀ {β} → ¬ JoinRep Vi [] _ _ β
    no (jr-join tv _ _ _) = no-names tv
    no (jr-open n _) = push-∋ᵒ pu n
      (nfO {O = Oᵢ} (G-nf (lo-ty lo (ltyD d))) pay)
  no-LO {V = V} eκ lo-B r
    (⟪⟫⊑ {Wᵢ = Vi} {K = K} {A′ = A′} {O = O} I _ _ ks _ pay d b _)
    with bdy b | reach-G r (rtyD d)
  ... | refl , _ , oz | g with nfO {O = O} nf-var pay
  ... | refl with g
  ...   | gℕ with pay
  ...     | ()
  no-LO {V = V} eκ lo-B r
    (⟪⟫⊑ {Wᵢ = Vi} {K = K} {A′ = A′} {O = O} I _ _ ks _ pay d b _)
    | refl , _ , oz | g | refl | g★ =
    no-S oz (κ-keep I (K-pay oz (trans (same-κ I) eκ) pay ks) eκ) refl r d
  no-LO {V = V} eκ lo-B (r-⟪⟫ r)
    (⟪⟫⊑⟪⟫ {Wᵢ = Vi} {K = K} I ks _ pay d b b′ _ _)
    with bdy b | bdy-id★ b′
  ... | refl , _ , oz | refl , _ =
    no-S oz (κ-keep I (K-pay oz (trans (same-κ I) eκ) pay ks) eκ) refl r d

-- the leaves against a spine (by types alone)
no-$ᴰ : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ n R O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
  → ReachD R → ¬ (V ∣ γ ⊢ $ n ⊑ᴰ R ∶⟨ A , A′ ⟩[ O ] q)
no-$ᴰ {V = V} {O = O} r-tag (⊑cast {A = A} {B′ = B′} {p = p} d ct _)
  with ct-X! ct | ty-$ (ltyD d)
... | _ , refl , refl | refl with plainᴰ {W = V} {O = O} {A = A} {A′ = B′} nf-ℕ p
... | ()
no-$ᴰ (r-cast _ r) (⊑cast d _ _) = no-$ᴰ r d
no-$ᴰ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ _ _ _ _ d _ _) = no-$ᴰ r d

no-n★ᴰ : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ n μ R O A A′}
    {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
  → ReachD R → ¬ (V ∣ γ ⊢ $ n ⟨ μ ∣ `ℕ ! ⟩ ⊑ᴰ R ∶⟨ A , A′ ⟩[ O ] q)
no-n★ᴰ {V = V} {O = O} r-tag (⊑cast {A = A} {B′ = B′} {p = p} d ct _)
  with ct-X! ct | ty-cast (ltyD d)
... | _ , refl , refl | refl
  with plainᴰ {W = V} {O = O} {A = A} {A′ = B′} nf-★ p
... | ()
no-n★ᴰ r-tag (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ! ct | ct-X! ct′
... | refl , refl | _ , refl , refl with p
... | ()
no-n★ᴰ (r-cast _ r) (cast⊑cast d _ _ _) = no-$ᴰ r d
no-n★ᴰ (r-cast _ r) (⊑cast d _ _) = no-n★ᴰ r d
no-n★ᴰ r (cast⊑ co-plain d _ _) = no-$ᴰ r d
no-n★ᴰ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ _ _ _ _ d _ _) = no-n★ᴰ r d

-- the type variables of the left boundary's interior: just X
oz₀ : ∀ {R} → OnlyZero ((bindR R ∷ []) ∣ (0 ∷ []))
oz₀ (_ , here) = refl
oz₀ (_ , there ())

module C1ᴰ where
  open PE.C1 using (5★; L₆; R₇; L₀; R₀; ΔR; R₇-blames; L₆-never-blames)

  bdy-LB : ∀ {Δᵢ Aᵢ A} → BdyTy ΔR PE.Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Aᵢ ≡ ` 0) × G A × OnlyZero Δᵢ
  bdy-LB b with PE.C1.bdy-LB b
  bdy-LB (bdy-ty (bw _ i _) _ _ _ _) | e , g
    with interior-functional i (TIE.int₀ {★})
  ... | refl = e , g , oz₀ {★}

  open SpineD 5★ no-n★ᴰ ΔR (λ { (_ , ()) }) bdy-LB

  -- C1 IS UNRELATED: every world over (ΔR, ΔR) with no permission, any
  -- openings; all routes (matched, left first, right first)
  c1-unrelated : ∀ {W : World ΔR ΔR} {γ A A′ O} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₆ ⊑ᴰ R₇ ∶⟨ A , A′ ⟩[ O ] q)
  c1-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-id★ lo-B)) (r-cast gc-ℕ? (r-⟪⟫ r-tag))

module C2ᴰ where
  open PE.C2 using (LE₃; RE₅)
  open TIE using (ΔL)

  bdy-LB₄ : ∀ {Δᵢ Aᵢ A} → BdyTy ΔL PE.Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Aᵢ ≡ ` 0) × G A × OnlyZero Δᵢ
  bdy-LB₄ b with PE.C2.bdy-LB₄ b
  bdy-LB₄ (bdy-ty (bw _ i _) _ _ _ _) | e , g
    with interior-functional i (TIE.int₀ {`ℕ})
  ... | refl = e , g , oz₀ {`ℕ}

  open SpineD ($ 5) no-$ᴰ ΔL (λ { (_ , ()) }) bdy-LB₄

  -- C2 (the late pair; its right spine passes P4 B4's J) IS UNRELATED
  c2-unrelated : ∀ {W : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₃ ⊑ᴰ RE₅ ∶⟨ A , A′ ⟩[ O ] q)
  c2-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-ℕ! lo-B))
      (r-cast gc-ℕ? (r-⟪⟫ (r-cast gc-id★ (r-⟪⟫ (r-⟪⟫ r-tag)))))

-- THE POP WALK (C4, C4g): the left has not instantiated; the right's
-- Inst boundary `[+X^α] Bd ⟨−X → id(★)⟩` holds a body of type X → ★.
-- Whatever the left offers it (λx:X.x, ΛX.λx:X.x, the inst cast),
-- possibly OPENED at X and PERMITTING α (D30, D28′), the boundary's
-- payment reads that left type against X → ★ at κ = []: the codomain
-- needs X ⊑ ★ at a type variable the right sees (or the domain fails).
open PE using (instL)

data LeftT : Term → Set where
  l-id  : LeftT idX′
  l-Λ   : LeftT (Λ idX′)
  l-F   : LeftT (Λ idX′ ⟨ [] ∣ instL ⟩)
  -- the gen-valued left (the hunt, §9): ((λx:★.x : ∀X.X→X) : ★→★)
  l-I★  : LeftT (ƛ ★ ∙ ` 0)
  l-g   : LeftT ((ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩)
  l-gF  : LeftT (((ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩)
                   ⟨ [] ∣ instL ⟩)

-- ∀X.X→X against X′→★, opened or not, at κ = []
pay-∀ : ∀ {Δᵢ Δ′ᵢ} {Vᵢ : World Δᵢ Δ′ᵢ} {Oᵢ k β}
  → κʷ Vᵢ ≡ [] → All (SlotOK Vᵢ) Oᵢ → Δ′ᵢ ∋ᵗ k := β
  → ¬ (`∀ (` 0 ⇒ ` 0) ⊑ᴰ⟨ Vᵢ ∣ Oᵢ ⟩ (` k ⇒ ★))
pay-∀ {Oᵢ = []} eκ so rh (∀⊑ _ _ (⇒⊑⇒ p₁ _)) with var⊑var p₁
... | ()
pay-∀ {Vᵢ = Vᵢ} {Oᵢ = opn j ∷ []} eκ ((β , rj , _) ∷ []) rh (⇒⊑⇒ _ p₂) =
  no★-right {V = Vᵢ} eκ rj (var⊑★ p₂)
pay-∀ {Oᵢ = skp ∷ []} eκ so rh (_ , _ , ⇒⊑⇒ p₁ _) with var⊑var p₁
... | ()
pay-∀ {Oᵢ = opn _ ∷ opn _ ∷ _} eκ so rh ()
pay-∀ {Oᵢ = opn _ ∷ skp ∷ _} eκ so rh ()
pay-∀ {Oᵢ = skp ∷ opn _ ∷ _} eκ so rh (_ , _ , ())
pay-∀ {Oᵢ = skp ∷ skp ∷ _} eκ so rh (_ , _ , ())

-- ★→★ against X′→★: ★ ⊑ X′
pay-★ : ∀ {Δᵢ Δ′ᵢ} {Vᵢ : World Δᵢ Δ′ᵢ} {Oᵢ k}
  → ¬ ((★ ⇒ ★) ⊑ᴰ⟨ Vᵢ ∣ Oᵢ ⟩ (` k ⇒ ★))
pay-★ {Vᵢ = Vᵢ} {Oᵢ} {k} pay
  with plainᴰ {W = Vᵢ} {O = Oᵢ} {A = ★ ⇒ ★} {A′ = ` k ⇒ ★} nf-⇒ pay
... | ⇒⊑⇒ () _

-- the payment at the right's Inst boundary is impossible
pay-RBd : ∀ {Δᵢ Δ′ᵢ} {Vᵢ : World Δᵢ Δ′ᵢ} {Oᵢ M A k β}
  → κʷ Vᵢ ≡ [] → All (SlotOK Vᵢ) Oᵢ → LeftT M → Δᵢ ∣ [] ⊢ M ⦂ A
  → Δ′ᵢ ∋ᵗ k := β → ¬ (A ⊑ᴰ⟨ Vᵢ ∣ Oᵢ ⟩ (` k ⇒ ★))
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} eκ so l-id (⊢ƛ _ (⊢` here)) rh pay
  with plainᴰ {W = Vᵢ} {O = Oᵢ} {A = ` 0 ⇒ ` 0} nf-⇒ pay
... | ⇒⊑⇒ p₁ p₂ = no-tag★ {V = Vᵢ} eκ rh (var⊑var p₁) (var⊑★ p₂)
pay-RBd eκ so l-Λ (⊢Λ _ (⊢ƛ _ (⊢` here))) rh pay = pay-∀ eκ so rh pay
pay-RBd eκ so l-g ⊢g rh pay with ty-cast ⊢g
... | refl = pay-∀ eκ so rh pay
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} {k = k} eκ so l-F ⊢F rh pay with ty-cast ⊢F
... | refl = pay-★ {Vᵢ = Vᵢ} {Oᵢ = Oᵢ} {k = k} pay
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} {k = k} eκ so l-gF ⊢F rh pay with ty-cast ⊢F
... | refl = pay-★ {Vᵢ = Vᵢ} {Oᵢ = Oᵢ} {k = k} pay
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} {k = k} eκ so l-I★ (⊢ƛ _ (⊢` here)) rh pay =
  pay-★ {Vᵢ = Vᵢ} {Oᵢ = Oᵢ} {k = k} pay

bind-κ : ∀ {W : World Δ Δ′} {W₁ O O₁} → Bind W O W₁ O₁ → κʷ W₁ ≡ κʷ W
bind-κ b-fresh                = refl
bind-κ (b-join (join1 _ _ _)) = refl
bind-κ (b-rep _ _ _)          = refl

-- the left function: ΛX.λx:X.x (C4, C4g) or the gen value (the hunt)
data LeftF : Term → Term → Set where
  lf-Λ : LeftF (Λ idX′) (Λ idX′ ⟨ [] ∣ instL ⟩)
  lf-g : LeftF ((ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩)
               (((ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩)
                  ⟨ [] ∣ instL ⟩)

lf-v : ∀ {Lv F} → LeftF Lv F → LeftT Lv
lf-v lf-Λ = l-Λ
lf-v lf-g = l-g

lf-F : ∀ {Lv F} → LeftF Lv F → LeftT F
lf-F lf-Λ = l-F
lf-F lf-g = l-gF

module PopWalkD (Bd : Term)
  (bd-ty : ∀ {Δ′ Γ A′} → Δ′ ∣ Γ ⊢ Bd ⦂ A′
     → Σ[ k ∈ ℕ ] (A′ ≡ ` k ⇒ ★) × (Δ′ ∋tv k))
  where

  RBd GR : Term
  RBd = Bd ⟪ PE.Θ₀ , PE.C3.cE ⟫
  GR  = RBd ⟨ [] ∣ RB.id★↦ ⟩

  w-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ M O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → LeftT M → ¬ (V ∣ γ ⊢ M ⊑ᴰ RBd ∶⟨ A , A′ ⟩[ O ] q)
  w-RB {V = V} eκ l (⊑⟪⟫ I _ so _ _ _ pay d _ _)
    with bd-ty (rtyD d)
  ... | k , refl , (β , rh) =
    pay-RBd (trans (same-κ I) eκ) so l (ltyD d) rh pay
  w-RB eκ l-Λ (Λ⊑ bd _ _ _ _ d _) = w-RB (trans (bind-κ bd) eκ) l-id d
  w-RB eκ l-F (cast⊑ co-plain d _ _) = w-RB eκ l-Λ d
  w-RB eκ l-gF (cast⊑ co-plain d _ _) = w-RB eκ l-g d
  w-RB eκ l-g (cast⊑ co-plain d _ _) = w-RB eκ l-I★ d
  w-RB eκ l-g (cast⊑ (co-gen _ co-plain) d _ _) = w-RB eκ l-I★ d

  w-GR : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ M O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → κʷ V ≡ [] → LeftT M → ¬ (V ∣ γ ⊢ M ⊑ᴰ GR ∶⟨ A , A′ ⟩[ O ] q)
  w-GR eκ l (⊑cast d _ _) = w-RB eκ l d
  w-GR eκ l-Λ (Λ⊑ bd _ _ _ _ d _) = w-GR (trans (bind-κ bd) eκ) l-id d
  w-GR eκ l-F (cast⊑ co-plain d _ _) = w-GR eκ l-Λ d
  w-GR eκ l-F (cast⊑cast d _ _ _) = w-RB eκ l-Λ d
  w-GR eκ l-gF (cast⊑ co-plain d _ _) = w-GR eκ l-g d
  w-GR eκ l-gF (cast⊑cast d _ _ _) = w-RB eκ l-g d
  w-GR eκ l-g (cast⊑ co-plain d _ _) = w-GR eκ l-I★ d
  w-GR eκ l-g (cast⊑ (co-gen _ co-plain) d _ _) = w-GR eκ l-I★ d
  w-GR eκ l-g (cast⊑cast d _ _ _) = w-RB eκ l-I★ d

  module _ {Lv F : Term} (lf : LeftF Lv F) where
    w-app : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ F · PE.C1.5★ ⊑ᴰ GR · PE.C1.5★ ∶⟨ A , A′ ⟩[ O ] q)
    w-app eκ (·⊑· f _) = w-GR eκ (lf-F lf) f

    w-L-app : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ (F · PE.C1.5★) ⟨ [] ∣ PE.C1.ℕ? ⟩ ⊑ᴰ GR · PE.C1.5★
             ∶⟨ A , A′ ⟩[ O ] q)
    w-L-app eκ (cast⊑ co-plain d _ _) = w-app eκ d

    w-app-R : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ F · PE.C1.5★ ⊑ᴰ (GR · PE.C1.5★) ⟨ [] ∣ PE.C1.ℕ? ⟩
             ∶⟨ A , A′ ⟩[ O ] q)
    w-app-R eκ (⊑cast d _ _) = w-app eκ d

    -- THE WALK: the initial-shaped pair is unrelated with no permission
    walk : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ (F · PE.C1.5★) ⟨ [] ∣ PE.C1.ℕ? ⟩
             ⊑ᴰ (GR · PE.C1.5★) ⟨ [] ∣ PE.C1.ℕ? ⟩ ∶⟨ A , A′ ⟩[ O ] q)
    walk eκ (cast⊑cast d _ _ _) = w-app eκ d
    walk eκ (⊑cast d _ _) = w-L-app eκ d
    walk eκ (cast⊑ co-plain d _ _) = w-app-R eκ d

module C4ᴰ where
  open PE.C4 using (bodyR; R₂; source-unrelated)
  open PE.C1 using (L₀; ΔR)

  bd-ty : ∀ {Δ′ Γ A′} → Δ′ ∣ Γ ⊢ bodyR ⦂ A′
    → Σ[ k ∈ ℕ ] (A′ ≡ ` k ⇒ ★) × (Δ′ ∋tv k)
  bd-ty (⊢ƛ (wf-var tv) ⊢b) with ty-cast ⊢b
  ... | refl = 0 , refl , tv

  open PopWalkD bodyR bd-ty

  -- C4 IS UNRELATED: every world over (empty, ΔR) with no permission,
  -- any openings (with claim-rep, D30's openings and D28′'s
  -- permissions)
  c4-unrelated : ∀ {W : World empty ΔR} {γ A A′ O} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₀ ⊑ᴰ R₂ ∶⟨ A , A′ ⟩[ O ] q)
  c4-unrelated = walk lf-Λ

module C4gᴰ where
  open PE.C4g using (Bdg; R2g; ct-genE′)
  open PE.C1 using (L₀; ΔR)

  bd-ty : ∀ {Δ′ Γ A′} → Δ′ ∣ Γ ⊢ Bdg ⦂ A′
    → Σ[ k ∈ ℕ ] (A′ ≡ ` k ⇒ ★) × (Δ′ ∋tv k)
  bd-ty (⊢cast _ ⊢p len) with ct-genE′ (cast-ty ⊢p len)
  ... | tv , refl = 0 , refl , tv

  open PopWalkD Bdg bd-ty

  c4g-unrelated : ∀ {W : World empty ΔR} {γ A A′ O} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₀ ⊑ᴰ R2g ∶⟨ A , A′ ⟩[ O ] q)
  c4g-unrelated = walk lf-Λ

-- C5 (and its hidden variant, matched and one-sided hides): dead at ANY
-- κ.  Below the right's check `X?` the left's X is joined to the
-- right's X and X⊑★ in the SAME world (D28′: no grant; ⊑cast keeps the
-- world), so X's rep. var has a permitted partner.  The left's seal
-- `[−X^α] 5 ⟨−X⟩` has exterior type X, so R1′ still needs α
-- unpermitted (`ok-hidden` fails: X occurs in X); R2 kills the matched
-- hides.
open import proof.ImprecisionWorld
  using (HasPermittedPartner; r1-fails; hasPP-int; hasPP-conv)
open PE using (unb1-lookup; unb1-conv)

T-≡ᵇ : ∀ m n → (m Data.Nat.≡ᵇ n) ≡ true → m ≡ n
T-≡ᵇ zero    zero    _  = refl
T-≡ᵇ zero    (suc n) ()
T-≡ᵇ (suc m) zero    ()
T-≡ᵇ (suc m) (suc n) e  = cong suc (T-≡ᵇ m n e)

-- more permissions keep a permission
permit-++ : ∀ β K κ → permit β κ ≡ X⊑★ → permit β (K ++ κ) ≡ X⊑★
permit-++ β []      κ p = p
permit-++ β (γ ∷ K) κ p with β Data.Nat.≡ᵇ γ
... | true  = refl
... | false = permit-++ β K κ p

hasPP-+κ : ∀ {W : World Δ Δ′} {K α} → HasPermittedPartner W α
  → HasPermittedPartner (W +κ K) α
hasPP-+κ {W = W} {K} (β , pr , pm) = β , pr , permit-++ β K (κʷ W) pm

module C5ᴰ where
  open PE.P4 using (S; unb₀; id★ᶜ)
  open PE.C5 using (5★ˣ; C5L; C5R)
  open PE.C1 using (5★)
  open TIE using (ΔL)

  HP0 : World Δ Δ′ → Set
  HP0 {Δ = Δ} U = ∀ {α} → Δ ∋ᵗ 0 := α → HasPermittedPartner U α

  -- THE CHECK FACT, in one world: `a ⊑ X′` and `a ⊑ ★`
  hasPP-chk : ∀ {V : World Δ Δ′} {a X′ α β}
    → WfWorldᴰ V → Δ ∋ᵗ a := α → Δ′ ∋ᵗ X′ := β
    → marksʷ V ⊢ embᴸ V (` a) ⊑ embᴿ V (` X′)
    → marksʷ V ⊢ embᴸ V (` a) ⊑ ★
    → HasPermittedPartner V α
  hasPP-chk {V = V} {a} {X′} {β = β} wf lh rh q p =
    β , joint-pair (wd-joint wf) lh rh j , sym (lookup-unique h′ hβ)
    where
    j : Joins V a X′
    j = var⊑var q
    h′ : marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := X⊑★
    h′ = subst (λ c → marksʷ V ∋ˡ c := X⊑★) j (var⊑★ p)
    hβ : marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := permit β (κʷ V)
    hβ = dmarks-emb (ηᴿʷ V) (κʷ V) rh

  no-$-chk : ∀ {V : World Δ Δ′} {γ n M′ μ′ X ℓ O A A′}
      {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → ¬ (V ∣ γ ⊢ $ n ⊑ᴰ M′ ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  no-$-chk {V = V} {O = O} (⊑cast {A = A} {A′ = A′} d ct q)
    with ct-X? ct | ty-$ (ltyD d)
  ... | _ , refl , refl | refl
    with plainᴰ {W = V} {O = O} {A = `ℕ} {A′ = A′} nf-ℕ q
  ... | ()

  data Core : Term → Set where
    c-5   : ∀ {n μ} → Core ($ n ⟨ μ ∣ `ℕ ! ⟩)
    c-hid : Core (5★ ⟪ unb₀ , id★ᶜ ⟫)

  -- R1′ at the left's seal: α occurs in its exterior type X
  r1′-fails : ∀ {U : World Δ Δ′} {α} → HasPermittedPartner U α
    → Δ ∋ᵗ 0 := α → ¬ UnbindOK′ U (` 0) (unbind 0 α)
  r1′-fails hp lh (ok-hidden f) with f lh
  ... | ()
  r1′-fails {U = U} hp lh (ok-unbind′ u) = r1-fails {W = U} hp u

  no-S-5 : ∀ {U : World Δ Δ′} {γ n μ O A A′} {q : A ⊑ᴰ⟨ U ∣ O ⟩ A′}
    → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ᴰ $ n ⟨ μ ∣ `ℕ ! ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  no-S-5 {U = U} {O = O} refl hp (⊑cast {B′ = B′} {p = p} d ct _)
    with ct-ℕ! ct
  ... | refl , refl with plainᴰ {W = U} {O = O} {A = ` 0} {A′ = `ℕ} nf-var p
  ... | ()
  no-S-5 refl hp (⟪⟫⊑ I (ok ∷ []) _ _ _ _ _ _ _) =
    r1′-fails (hp lh) lh ok
    where lh = unb1-lookup (int-left I)

  no-S-core : ∀ {U : World Δ Δ′} {γ Q O A A′} {q : A ⊑ᴰ⟨ U ∣ O ⟩ A′}
    → Core Q → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ᴰ Q ∶⟨ A , A′ ⟩[ O ] q)
  no-S-core c-5 eA hp d = no-S-5 eA hp d
  no-S-core c-hid eA hp (⊑⟪⟫ {Wᵢ = Ui} {K = K} I _ _ _ _ _ _ d _ _) =
    no-S-5 eA (λ lh → hasPP-+κ {W = Ui} {K = K} (hasPP-int I (hp lh))) d
  no-S-core c-hid refl hp (⟪⟫⊑ I (ok ∷ []) _ _ _ _ _ _ _) =
    r1′-fails (hp lh) lh ok
    where lh = unb1-lookup (int-left I)
  no-S-core c-hid eA hp
    (⟪⟫⊑⟪⟫ I _ _ _ _ (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _)
      (Wᶜ , ci , conv-tail⊑tail (conv-seal⊑id★ _ lu)) _) =
    r1-fails {W = Wᶜ} (hasPP-conv ci (hp lh))
      (lu (unb1-conv (conv-left ci) lh))
    where lh = unb1-lookup (int-left I)

  -- S against a core under the right check `X?`
  no-S-chk : ∀ {V : World Δ Δ′} {γ Q μ′ X ℓ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → Core Q → WfWorldᴰ V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ᴰ Q ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  no-S-chk {V = V} {O = O} core wf refl
    (⊑cast {B′ = B′} {A′ = A′} {p = p} d ct q) with ct-X? ct
  ... | (_ , rh) , refl , refl =
    no-S-core core refl
      (λ lh → hasPP-chk {V = V} wf lh rh
        (plainᴰ {W = V} {O = O} {A = ` 0} {A′ = A′} nf-var q)
        (plainᴰ {W = V} {O = O} {A = ` 0} {A′ = ★} nf-var p))
      d
  no-S-chk core wf eA (⟪⟫⊑ _ _ _ _ _ _ d _ _) = no-$-chk d

  module Outer (Q : Term) (core : Core Q) where
    RinQ RQ : Term
    RinQ = Q ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩
    RQ   = RinQ ⟪ PE.Θ₀ , unseal 0 ⟫

    no-S-RQ : ∀ {Δ₁} {V : World Δ₁ ΔL} {γ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
      → A ≡ ` 0 → ¬ (V ∣ γ ⊢ S ⊑ᴰ RQ ∶⟨ A , A′ ⟩[ O ] q)
    no-S-RQ eA (⊑⟪⟫ _ _ _ _ _ wf _ d _ _) = no-S-chk core wf eA d
    no-S-RQ {V = V} {O = O} refl (⟪⟫⊑ {A′ = A′} _ _ _ _ _ _ d _ q)
      with ty-$ (ltyD d) | proj₂ (bdy-C5 (proj₂ (proj₂ (proj₂
             (R.⟪⟫-inv (rtyD d))))))
    ... | refl | refl with plainᴰ {W = V} {O = O} {A = ` 0} {A′ = `ℕ} nf-var q
    ... | ()
    no-S-RQ eA (⟪⟫⊑⟪⟫ _ _ _ _ d _ _ _ _) = no-$-chk d

    no-L-RinQ : ∀ {Δ₂} {V : World ΔL Δ₂} {γ O A A′} {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
      → ¬ (V ∣ γ ⊢ C5L ⊑ᴰ RinQ ∶⟨ A , A′ ⟩[ O ] q)
    no-L-RinQ {V = V} {O = O} (⊑cast {A = A} d ct q) with ct-X? ct
      | R.⟪⟫-inv (ltyD d)
    ... | _ , refl , refl | _ , _ , _ , b with bdy-C5 b
    ... | _ , refl with plainᴰ {W = V} {O = O} {A = `ℕ} {A′ = ` 0} nf-ℕ q
    ... | ()
    no-L-RinQ (⟪⟫⊑ _ _ _ _ wf _ d b _) = no-S-chk core wf (proj₁ (bdy-C5 b)) d

    -- THE TOP: every world over (ΔL, ΔL), ANY κ, any openings
    no-top : ∀ {W : World ΔL ΔL} {γ O A A′} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
      → ¬ (W ∣ γ ⊢ C5L ⊑ᴰ RQ ∶⟨ A , A′ ⟩[ O ] q)
    no-top (⟪⟫⊑⟪⟫ _ _ wf _ d b _ _ _) = no-S-chk core wf (proj₁ (bdy-C5 b)) d
    no-top (⟪⟫⊑ _ _ _ _ _ _ d b _)    = no-S-RQ (proj₁ (bdy-C5 b)) d
    no-top (⊑⟪⟫ _ _ _ _ _ _ _ d _ _)  = no-L-RinQ d

  -- C5 IS UNRELATED (L state 3, R state 5), in every world, at any κ
  c5-unrelated : ∀ {W : World ΔL ΔL} {γ O A A′} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ᴰ C5R ∶⟨ A , A′ ⟩[ O ] q)
  c5-unrelated = Outer.no-top 5★ˣ c-5

  -- ... its failing redex against the left value S (any well-formed
  -- world, any κ)
  c5-redex-unrelated : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′}
      {q : A ⊑ᴰ⟨ V ∣ O ⟩ A′}
    → WfWorldᴰ V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ᴰ 5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  c5-redex-unrelated = no-S-chk c-5

  -- ... and THE HIDDEN VARIANT (the right's hide `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`
  -- under the check), with its matched-hides route (R2)
  hidden-unrelated : ∀ {W : World ΔL ΔL} {γ O A A′} {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ᴰ PE.C5Dead.RH ∶⟨ A , A′ ⟩[ O ] q)
  hidden-unrelated = Outer.no-top (5★ ⟪ unb₀ , id★ᶜ ⟫) c-hid

------------------------------------------------------------------------
-- 8b. DGG PART 1 for TwoGen's pairs and H1 in the variant: the left
-- is a value; the right's run (pinned by TwoGen / the examples) reaches
-- its value; the variant relates them at a well-formed top-level world
-- (no permission, no opening)
------------------------------------------------------------------------

module DGG1ᴰ where
  open import Reduction using (_⊢_-→*_; runCtx; done; _then_)
  open import examples.Eval using (eval)
  open TG using (runOf; vEnd; FL; FR; FR-⊢; GL; GR; GR-⊢; GRm; GRm-⊢;
    HL; HR; HR-⊢; HRm; HRm-⊢; NL; NR; NR-⊢; NRm; NRm-⊢)
  open H1 using (W₄; W₄-wf; q-top; K2)
  open TwoGenᴰ using (g2m-final; hrm-final; g2-final; hr-final)
  open TwoGenᴰ.G0ᴰ using (g0-final)
  open TwoGenᴰ.N2ᴰ using (nrm-final; nr-final)

  Part1ᴰ : Term → Term → Ty → Ty → Set
  Part1ᴰ M M′ A A′ =
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ] Value V′
      × Σ[ W ∈ World empty (runCtx r′) ] WfWorldᴰ W × κʷ W ≡ []
        × Σ[ q ∈ A ⊑ᴰ⟨ W ∣ [] ⟩ A′ ] (W ∣ [] ⊢ M ⊑ᴰ V′ ∶[ [] ] q)

  g0 : Part1ᴰ FL FR (`∀ (` 0 ⇒ `ℕ)) (★ ⇒ `ℕ)
  g0 = _ , runOf (eval 40 FR FR-⊢) tt , vEnd (eval 40 FR FR-⊢) tt ,
       TIE.W₃ , wf→ᴰ (RB.W₃-wf []) , refl , TG.G0.q0 , g0-final

  g2m : Part1ᴰ GL GRm K2 (★ ⇒ (★ ⇒ ★))
  g2m = _ , runOf (eval 40 GRm GRm-⊢) tt , vEnd (eval 40 GRm GRm-⊢) tt ,
        W₄ , wf→ᴰ W₄-wf , refl , q-top , g2m-final

  g2 : Part1ᴰ GL GR K2 (★ ⇒ (★ ⇒ ★))
  g2 = _ , runOf (eval 40 GR GR-⊢) tt , vEnd (eval 40 GR GR-⊢) tt ,
       W₄ , wf→ᴰ W₄-wf , refl , q-top , g2-final

  hrm : Part1ᴰ HL HRm K2 (★ ⇒ (★ ⇒ ★))
  hrm = _ , runOf (eval 40 HRm HRm-⊢) tt , vEnd (eval 40 HRm HRm-⊢) tt ,
        W₄ , wf→ᴰ W₄-wf , refl , q-top , hrm-final

  hr : Part1ᴰ HL HR K2 (★ ⇒ (★ ⇒ ★))
  hr = _ , runOf (eval 40 HR HR-⊢) tt , vEnd (eval 40 HR HR-⊢) tt ,
       W₄ , wf→ᴰ W₄-wf , refl , q-top , hr-final

  nrm : Part1ᴰ NL NRm K2 (★ ⇒ (★ ⇒ ★))
  nrm = _ , runOf (eval 40 NRm NRm-⊢) tt , vEnd (eval 40 NRm NRm-⊢) tt ,
        W₄ , wf→ᴰ W₄-wf , refl , q-top , nrm-final

  nr : Part1ᴰ NL NR K2 (★ ⇒ (★ ⇒ ★))
  nr = _ , runOf (eval 40 NR NR-⊢) tt , vEnd (eval 40 NR NR-⊢) tt ,
       W₄ , wf→ᴰ W₄-wf , refl , q-top , nr-final

  -- H1 (final, D29): the real witness, through toD
  -- K (D26's counterexample): the real witness `dgg1-K`, through toD
  k : ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RG.RK -→* V′ ] Value V′
    × Σ[ W′ ∈ World TIE.ΔL (runCtx r′) ]
        Σ[ q ∈ TIE.∀X⇒X ⊑ᴰ⟨ W′ ∣ [] ⟩ (★ ⇒ ★) ]
          (W′ ∣ [] ⊢ RG.VL ⊑ᴰ V′ ∶[ [] ] q)
  k = RG.RF ,
      (RG.st₀ then RG.st₁ then RG.st₂ then RG.st₃ then RG.st₄ then done) ,
      RG.vRF , RG.Wk , RB.∀id⊑★ RG.Wk , toD RG.VL⊑RF it

  h1 : Part1ᴰ H1.L₀ H1.R₀ K2 (★ ⇒ (★ ⇒ ★))
  h1 = H1.R₄ , (H1.st₀ then H1.st₁ then H1.st₂ then H1.st₃ then done) ,
       H1.vR₄ , W₄ , wf→ᴰ W₄-wf , refl , q-top , toD H1.final it

------------------------------------------------------------------------
-- 9. THE HUNT.  A gen-VALUED left against C4's right exercises every
-- new freedom at once: ⊑⟪⟫ may OPEN the left's ∀ at the right's Inst
-- type variable X and PERMIT α (D30, D28′), the left's gen layer may
-- CONSUME the opening (cast⊑, no world change), and the left may SKIP
-- (TwoGen (iii), it is a gen-cast value).  Sources UNRELATED
-- (∀X.X→X ⋢ ∀X.X→★, `PE.C4.source-unrelated`):
--   L:  ((λx:★. x : ∀X.X→X) : ★→★) 5 : ℕ          (gen, then inst)
--   R:  ((ΛX. λx:X. (x : ★))  : ★→★) 5 : ℕ        (C4's right)
-- The left answers 5; the right blames (`PE.C4.R₂-blames`).  The left's
-- initial term against the right's state 2 is NOT related in the
-- variant: the payment at the Inst boundary reads ∀X.X→X (opened or
-- skipped) or ★→★ against X→★ at κ = [] (`walk lf-g`).
------------------------------------------------------------------------

module Hunt where
  open import examples.TypeCheck using (tc)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open PE.Runs using (all-reach; NotBlame; last)
  open PE.C4 using (bodyR; R₂; R₂-blames; source-unrelated)
  open PE.C1 using (5★; ℕ?; ΔR)
  open C4ᴰ using (bd-ty)

  Lg₀ : Term
  Lg₀ = ((((ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩)
            ⟨ [] ∣ instL ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  Lg₀-⊢ : empty ∣ [] ⊢ Lg₀ ⦂ `ℕ
  Lg₀-⊢ = tc

  -- the left answers 5 and never blames
  Lg₀-answers : last (evalTerms 30 Lg₀-⊢) ≡ $ 5
  Lg₀-answers = refl

  Lg₀-never-blames : ∀ {ℓ} → ¬ (empty ⊢ Lg₀ -→* blame ℓ)
  Lg₀-never-blames r = all-reach {P = NotBlame} 30 Lg₀-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  open PopWalkD bodyR bd-ty

  -- NOT DERIVABLE: every world over (empty, ΔR) with no permission, any
  -- openings
  c4gen-unrelated : ∀ {W : World empty ΔR} {γ A A′ O}
      {q : A ⊑ᴰ⟨ W ∣ O ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ Lg₀ ⊑ᴰ R₂ ∶⟨ A , A′ ⟩[ O ] q)
  c4gen-unrelated = walk lf-g

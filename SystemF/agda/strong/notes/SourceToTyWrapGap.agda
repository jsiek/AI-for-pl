module strong.notes.SourceToTyWrapGap where

-- A CLOSED SOURCE PROGRAM that reduces to `PreserveTyWrap`'s refuting
-- configuration (§8.1b, `closed-neededₘ`).  Jeremy asked whether that
-- refutation bites on REACHABLE states or only on `TyWrapOk`'s
-- over-general statement.  This says: reachable.
--
-- THE PROGRAM.  No boundaries, no store, no conversions — just source.
--
--   ( Λ λf:(∀X. X→𝔹). f •[X]    )  •[ℕ]  ·  ( ΛY. λz:Y. true )
--
-- The outer Λ takes a polymorphic f and instantiates it AT THE Λ'S OWN
-- TYPE VARIABLE.  That is the whole trick: after the outer `•[ℕ]`
-- allocates, the Λ's variable is a CROSSING ASSIGNMENT to a store
-- level, and `f`'s instantiation type names it.
--
-- THE ROUTE (each step checked below):
--
--   TyBeta   the outer instantiation mints the boundary, `revTy`
--            putting a `↦` at the head
--   Alloc    `bse 0` becomes `lvl 0`; the store gains `ℕ`
--   Wrap     the polymorphic argument acquires the CONTRAVARIANT half
--            `hide 0 (lvl 0) ∷ᶜ id (∀X. X→𝔹)` …
--   ξ-⟨⟩/Beta … and is substituted for `f` INSIDE the covariant
--            boundary, whose interior is `asgn (lvl 0) ∷ [] ∥ []`
--
-- and the result is `closed-neededₘ`'s redex on the nose.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.Interior using (conv-interior)

------------------------------------------------------------------------
-- The source program
------------------------------------------------------------------------

T : Ty                      -- the ∀-BODY:  X → 𝔹
T = ` zero ⇒ `𝔹

B : Ty                      -- the outer Λ's body type: (∀X.X→𝔹) → (Y→𝔹)
B = (`∀ T) ⇒ (` zero ⇒ `𝔹)

P : Term                    -- ΛY. λz:Y. true      : ∀X. X→𝔹
P = Λ (ƛ (` zero) ∙ (# true))

F : Term                    -- λf. f •[Y]
F = ƛ (`∀ T) ∙ ((` zero) • T [ ` zero ])

M₀ : Term
M₀ = ((Λ F) • B [ `𝔹 ]) · P

⊢P : ∀ {Sg Γ Δ} → Sg ∣ Δ ∣ Γ ⊢ P ⦂ `∀ T
⊢P = ⊢Λ (Vs Sƛ) (⊢ƛ (wf-var t-here) ⊢#)

⊢F : ∀ {Sg Ss Bs}
  → Sg ∣ (asgn (bse zero) ∷ Ss ∥ addr ∷ Bs) ∣ [] ⊢ F ⦂ B
⊢F = ⊢ƛ (wf-∀ (wf-⇒ (wf-var t-here) wf-𝔹))
       (⊢•[] (⊢` here) (wf-var t-here))

⊢M₀ : [] ∣ ([] ∥ []) ∣ [] ⊢ M₀ ⦂ (`𝔹 ⇒ `𝔹)
⊢M₀ = ⊢· (⊢•[] (⊢Λ (Vs Sƛ) ⊢F) wf-𝔹) ⊢P

------------------------------------------------------------------------
-- The trace
------------------------------------------------------------------------

cTop : Conv                 -- what `revTy` mints at the outer Λ
cTop = revTy zero (bse zero) `𝔹 B

M₁ : Term
M₁ = (ν `𝔹ᴿ ∙ (F ⟨ cTop ⟩)) · P

step₁ : [] ∣ ([] ∥ []) ⊢ M₀ —→ M₁ ⊣ []
step₁ = ξ-·-l (TyBeta (Vs Sƛ) quote-𝔹)

Sg : Store
Sg = `𝔹ᴿ ∷ []      -- = PreserveTyWrap §8.1b's `Sgₘ`

M₂ : Term                   -- the allocation discharged: bse 0 ↦ lvl 0
M₂ = ((F ⟨ cTop ⟩) [ lvl zero ]ᵃᴹ) · P

step₂ : [] ∣ ([] ∥ []) ⊢ M₁ —→ M₂ ⊣ Sg
step₂ = ξ-·-l Alloc

-- the allocated conversion, written directly
cA : Conv
cA = revTy zero (lvl zero) `𝔹 B

allocated : (F ⟨ cTop ⟩) [ lvl zero ]ᵃᴹ ≡ F ⟨ cA ⟩
allocated = refl

-- `arr` splits it: the CONTRAVARIANT half is the `hide` that will wrap
-- the polymorphic argument, the covariant half carries the `show`
c₁ c₂ : Conv
c₁ = hide zero (lvl zero) ∷ᶜ id (`∀ T)
c₂ = ((seal zero (lvl zero) ∷ᶜ id (` zero))
        ↦ (show zero (lvl zero) ∷ᶜ id `𝔹))
       ∷ᶜ id (`𝔹 ⇒ `𝔹)

split : arr (`∀ T) cA ≡ just (c₁ , c₂)
split = refl

nf-cA : NF cA
nf-cA = nf-cons (nf-fun (nf-cons nf-hide nf-id irr-id)
                        (nf-cons (nf-fun (nf-cons nf-seal nf-id irr-id)
                                         (nf-cons nf-show nf-id irr-id))
                                 nf-id irr-id))
                nf-id irr-id

M₃ : Term                   -- the Wrap contractum
M₃ = ((ƛ (`∀ T) ∙ ((` zero) • T [ ` zero ])) · (P ⟨ c₁ ⟩)) ⟨ c₂ ⟩

step₃ : Sg ∣ ([] ∥ []) ⊢ M₂ —→ M₃ ⊣ Sg
step₃ = Wrap (V⟨⟩ Sƛ nf-cA (inert-arr (`∀ T) split))
             (Vs (SΛ (Vs Sƛ))) split

------------------------------------------------------------------------
-- The interior the boundary hands its body: THE ASSIGNMENT IS THERE
------------------------------------------------------------------------

Δₘ : Ctxᵗ
Δₘ = asgn (lvl zero) ∷ [] ∥ []      -- = PreserveTyWrap §8.1b's `Δₘ`

int₂ : interior c₂ ([] ∥ []) ≡ just Δₘ
int₂ = refl

------------------------------------------------------------------------
-- Inside that boundary: Beta, and then the TyWrap redex itself
------------------------------------------------------------------------

d : Conv                    -- = PreserveTyWrap §8.1b's `dₘ`
d = hide (suc zero) (lvl zero) ∷ᶜ id T

view₁ : allView c₁ ≡ just d
view₁ = refl

v-arg : Value (P ⟨ c₁ ⟩)
v-arg = V⟨⟩ (SΛ (Vs Sƛ)) (nf-cons nf-hide nf-id irr-id) (inert-all view₁)

M₄ : Term
M₄ = ((P ⟨ c₁ ⟩) • T [ ` zero ]) ⟨ c₂ ⟩

step₄ : Sg ∣ ([] ∥ []) ⊢ M₃ —→ M₄ ⊣ Sg
step₄ = ξ-⟨⟩ int₂ (Beta v-arg)

-- THE REDEX, at `Δₘ`, instantiating at the variable that names the
-- assignment — `closed-neededₘ`'s configuration, reached from source.
R : RepTy                   -- = §8.1b's `Rₘ`
R = `ᵃ (lvl zero)

q : Sg ∣ Δₘ ⊢⌊ ` zero ⌋ R
q = quote-var n-here-asgn

int₁ : interior c₁ Δₘ ≡ just ([] ∥ [])
int₁ = refl

W : Conv                    -- = §8.1b's `Wₘ`, verbatim
W = ((seal zero (bse zero) ∷ᶜ id (` zero))
      ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
    ∷ᶜ hide zero (lvl zero) ∷ᶜ id T

built : instReveal Sg (bind ∷ [] ∥ []) zero (bse zero) (` zero) d ≡ W
built = refl

M₅ : Term
M₅ = (ν R ∙ ((ƛ (` zero) ∙ (# true)) ⟨ W ⟩)) ⟨ c₂ ⟩

step₅ : Sg ∣ ([] ∥ []) ⊢ M₄ —→ M₅ ⊣ Sg
step₅ = ξ-⟨⟩ int₂ (TyWrap v-arg view₁ q int₁)

------------------------------------------------------------------------
-- The whole run
------------------------------------------------------------------------

run : [] ∣ ([] ∥ []) ⊢ M₀ —↠ M₅ ⊣ Sg
run = step₁ then step₂ then step₃ then step₄ then step₅ then done

------------------------------------------------------------------------
-- … AND THE RESULT HAS NO TYPE
------------------------------------------------------------------------
-- §8.1b's refutation, restated at this run's own term (it is `private`
-- there).  The `hide` in the tail pins the `↦`'s exterior to a context
-- with an EMPTY STACK, and there the `seal`'s read-back — which must
-- turn `` `ᵃ (lvl 0) `` into a TYPE — has no name to land on.

id-ctx : ∀ {Γ Γ′ A B C} → Sg ∣ Γ ⊢ id A ∶ B ⇝ C ⊣ Γ′ → Γ ≡ Γ′
id-ctx (conv-id wf) = refl

tail-open : ∀ {Γ₁ B C}
  → Sg ∣ Γ₁ ⊢ hide zero (lvl zero) ∷ᶜ id T ∶ B ⇝ C
      ⊣ (asgn (lvl zero) ∷ [] ∥ nuBind R ∷ [])
  → Γ₁ ≡ ([] ∥ nuBind R ∷ [])
tail-open (conv-cons (conv-hide sc wf pop-here na) tl) with id-ctx tl
tail-open (conv-cons (conv-hide sc wf pop-here na) tl) | refl = refl

seal-⊥ : ∀ {Γ′ A C}
  → ¬ (Sg ∣ ([] ∥ nuBind R ∷ [])
         ⊢ seal zero (bse zero) ∷ᶜ id (` zero) ∶ A ⇝ C ⊣ Γ′)
seal-⊥ (conv-cons (conv-seal r-here (read-var ()) pop-here) tl)

inner-⊥ : ∀ {C} → ¬ (Sg ∣ Δₘ ∣ [] ⊢ ν R ∙ ((ƛ (` zero) ∙ (# true)) ⟨ W ⟩) ⦂ C)
inner-⊥ (⊢ν wfR (⊢⟨⟩ nf (⊢ƛ wf ⊢#) (conv-cons (conv-fun ⊢s ⊢t) tl)))
  with tail-open tl
inner-⊥ (⊢ν wfR (⊢⟨⟩ nf (⊢ƛ wf ⊢#) (conv-cons (conv-fun ⊢s ⊢t) tl)))
  | refl = seal-⊥ ⊢s

-- so the whole run's result is untypable: PRESERVATION IS FALSE for v8
-- as it stands, on a term reachable from a closed source program.
just-inj : ∀ {Γ Γ′ : Ctxᵗ} → just Γ ≡ just Γ′ → Γ ≡ Γ′
just-inj refl = refl

M₅-⊥ : ∀ {C} → ¬ (Sg ∣ ([] ∥ []) ∣ [] ⊢ M₅ ⦂ C)
M₅-⊥ (⊢⟨⟩ nf ⊢M conv)
  with just-inj (trans (sym (conv-interior conv)) int₂)
M₅-⊥ (⊢⟨⟩ nf ⊢M conv) | refl = inner-⊥ ⊢M

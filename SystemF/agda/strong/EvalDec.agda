module strong.EvalDec where

-- Strong System F — the DECIDERS the evaluator (strong.Eval) runs on.
--
-- Everything the reduction relation _⊢_-→_ (strong.BReduction) asks of a
-- redex is decidable, and this module decides it WITH WITNESSES, so that
-- `step` can build the derivation as it builds the contractum.  Nothing
-- here is assumed and nothing is a Bool: every function returns a
-- `Dec P` whose `yes` carries the proof the rule needs.
--
-- WHAT IS DECIDED
--
--   _≟ᵗ_       syntactic type equality (ported from notes/old/CancelProbe)
--   ≈?         the unfolding congruence _≈Δ̄⟨_⟩_ — which IS an equality of
--              unfoldings (strong.Unfold's ≈unf/≈unf⁻), hence _≟ᵗ_ after
--              computing unfoldᵉ
--   ∋tv? wf?   type-variable scope and type well-formedness
--   know?      the two knowledge lookups Γ ∋ X := A₀ and Γ ∋ X :=x A′,
--   knowx?     together with their uniqueness and their exclusivity
--   ∋ok?       boundary-frame accessibility, and Scoped over it
--   scoped?
--   skel?      SkelEq — the (bwf-↓x) rep comparison
--   cncOK?     a conceal entry's LICENCE: bwf↓ or bwf↓x, decided by the
--   bwf?       exterior's entry at the concealed slot; hence Bwf itself
--   ≼≈?        the knowledge ordering, entrywise
--   mergeOK?   *** ALL FIVE MergeOK components, fully decided ***
--   inert? active? gval? value?
--              the syntactic classifiers of strong.BReduction §Inert
--
-- NOTHING HERE IS A PARTIAL GUARD: `mergeOK?` is a genuine `Dec`, so a
-- `no` is a PROOF that the merge is refused, which is what makes
-- strong.Eval's "stuck exactly here" assertions (gauntlet §9m) meaningful.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _<?_; _≤?_)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _⊢_;
         wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; here-xrvld;
         skip-abst; skip-rvld; skip-xrvld;
         _∋_:=_; here; _∋_:=x_; herex; skipx)
open import strong.Unfold using (_≈Δ̄⟨_⟩_; ≈unf; ≈unf⁻; unfoldᵉ)
open import strong.Boundary
open import strong.BReduction

------------------------------------------------------------------------
-- Syntactic type equality (ported from notes/old/CancelProbe.agda §1.2,
-- which pinned an older relation; the deciders themselves are unchanged).
------------------------------------------------------------------------

`-inj : ∀ {X Y : ℕ} → _≡_ {A = Ty} (` X) (` Y) → X ≡ Y
`-inj refl = refl

⇒-injˡ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → A ≡ C
⇒-injˡ refl = refl

⇒-injʳ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → B ≡ D
⇒-injʳ refl = refl

∀-inj : ∀ {A B} → `∀ A ≡ `∀ B → A ≡ B
∀-inj refl = refl

infix 4 _≟ᵗ_
_≟ᵗ_ : (A B : Ty) → Dec (A ≡ B)
(` X)   ≟ᵗ (` Y)   with X ≟ Y
(` X)   ≟ᵗ (` Y)   | yes refl = yes refl
(` X)   ≟ᵗ (` Y)   | no  ne   = no λ e → ne (`-inj e)
(` X)   ≟ᵗ `ℕ      = no λ ()
(` X)   ≟ᵗ `𝔹      = no λ ()
(` X)   ≟ᵗ (C ⇒ D) = no λ ()
(` X)   ≟ᵗ `∀ D    = no λ ()
`ℕ      ≟ᵗ (` Y)   = no λ ()
`ℕ      ≟ᵗ `ℕ      = yes refl
`ℕ      ≟ᵗ `𝔹      = no λ ()
`ℕ      ≟ᵗ (C ⇒ D) = no λ ()
`ℕ      ≟ᵗ `∀ D    = no λ ()
`𝔹      ≟ᵗ (` Y)   = no λ ()
`𝔹      ≟ᵗ `ℕ      = no λ ()
`𝔹      ≟ᵗ `𝔹      = yes refl
`𝔹      ≟ᵗ (C ⇒ D) = no λ ()
`𝔹      ≟ᵗ `∀ D    = no λ ()
(A ⇒ B) ≟ᵗ (` Y)   = no λ ()
(A ⇒ B) ≟ᵗ `ℕ      = no λ ()
(A ⇒ B) ≟ᵗ `𝔹      = no λ ()
(A ⇒ B) ≟ᵗ `∀ D    = no λ ()
(A ⇒ B) ≟ᵗ (C ⇒ D) with A ≟ᵗ C
(A ⇒ B) ≟ᵗ (C ⇒ D) | no  ne   = no λ e → ne (⇒-injˡ e)
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl with B ≟ᵗ D
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl | yes refl = yes refl
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl | no  ne   = no λ e → ne (⇒-injʳ e)
`∀ A    ≟ᵗ (` Y)   = no λ ()
`∀ A    ≟ᵗ `ℕ      = no λ ()
`∀ A    ≟ᵗ `𝔹      = no λ ()
`∀ A    ≟ᵗ (C ⇒ D) = no λ ()
`∀ A    ≟ᵗ `∀ D    with A ≟ᵗ D
`∀ A    ≟ᵗ `∀ D    | yes refl = yes refl
`∀ A    ≟ᵗ `∀ D    | no  ne   = no λ e → ne (∀-inj e)

------------------------------------------------------------------------
-- The unfolding congruence.  ≈Δ̄ is BY DEFINITION an equality of
-- unfoldings (strong.Unfold's design choice), so deciding it is _≟ᵗ_
-- after running unfoldᵉ.
------------------------------------------------------------------------

≈? : (Γ : TCtx) (A B : Ty) → Dec (A ≈Δ̄⟨ Γ ⟩ B)
≈? Γ A B = map′ ≈unf ≈unf⁻ (unfoldᵉ Γ A ≟ᵗ unfoldᵉ Γ B)

------------------------------------------------------------------------
-- Type-variable scope and type well-formedness
------------------------------------------------------------------------

∋tv-abst : ∀ {Γ X} → (abst ∷ Γ) ∋tv suc X → Γ ∋tv X
∋tv-abst (skip-abst p) = p

∋tv-rvld : ∀ {Γ X A} → (rvld A ∷ Γ) ∋tv suc X → Γ ∋tv X
∋tv-rvld (skip-rvld p) = p

∋tv-xrvld : ∀ {Γ X A} → (xrvld A ∷ Γ) ∋tv suc X → Γ ∋tv X
∋tv-xrvld (skip-xrvld p) = p

∋tv? : (Γ : TCtx) (X : ℕ) → Dec (Γ ∋tv X)
∋tv? []              X       = no λ ()
∋tv? (abst    ∷ Γ)   zero    = yes here-abst
∋tv? (rvld A  ∷ Γ)   zero    = yes here-rvld
∋tv? (xrvld A ∷ Γ)   zero    = yes here-xrvld
∋tv? (abst    ∷ Γ) (suc X) =
  map′ skip-abst  ∋tv-abst  (∋tv? Γ X)
∋tv? (rvld A  ∷ Γ) (suc X) =
  map′ skip-rvld  ∋tv-rvld  (∋tv? Γ X)
∋tv? (xrvld A ∷ Γ) (suc X) =
  map′ skip-xrvld ∋tv-xrvld (∋tv? Γ X)

wf-var⁻ : ∀ {Γ X} → Γ ⊢ ` X → Γ ∋tv X
wf-var⁻ (wf-var p) = p

wf-⇒⁻ˡ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A
wf-⇒⁻ˡ (wf-⇒ a b) = a

wf-⇒⁻ʳ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ B
wf-⇒⁻ʳ (wf-⇒ a b) = b

wf-∀⁻ : ∀ {Γ A} → Γ ⊢ `∀ A → (abst ∷ Γ) ⊢ A
wf-∀⁻ (wf-∀ a) = a

wf? : (Γ : TCtx) (A : Ty) → Dec (Γ ⊢ A)
wf? Γ (` X)   = map′ wf-var wf-var⁻ (∋tv? Γ X)
wf? Γ `ℕ      = yes wf-ℕ
wf? Γ `𝔹      = yes wf-𝔹
wf? Γ (A ⇒ B) with wf? Γ A
wf? Γ (A ⇒ B) | no  ¬a = no λ w → ¬a (wf-⇒⁻ˡ w)
wf? Γ (A ⇒ B) | yes a  with wf? Γ B
wf? Γ (A ⇒ B) | yes a  | yes b  = yes (wf-⇒ a b)
wf? Γ (A ⇒ B) | yes a  | no  ¬b = no λ w → ¬b (wf-⇒⁻ʳ w)
wf? Γ (`∀ A)  = map′ wf-∀ wf-∀⁻ (wf? (abst ∷ Γ) A)

------------------------------------------------------------------------
-- The two knowledge lookups.  Both are FUNCTIONAL (uniqueness below) and
-- MUTUALLY EXCLUSIVE — an entry is `rvld` or `xrvld`, never both — which
-- is what makes the conceal licence decidable by a single lookup.
------------------------------------------------------------------------

Know : TCtx → ℕ → Set
Know Γ X = Σ Ty λ A₀ → Γ ∋ X := A₀

Knowx : TCtx → ℕ → Set
Knowx Γ X = Σ Ty λ A′ → Γ ∋ X :=x A′

¬kn-[] : ∀ {X} → ¬ Know [] X
¬kn-[] (A₀ , ())

¬kn-abst : ∀ {Γ} → ¬ Know (abst ∷ Γ) zero
¬kn-abst (A₀ , ())

¬kn-xrvld : ∀ {Γ A} → ¬ Know (xrvld A ∷ Γ) zero
¬kn-xrvld (A₀ , ())

kn-cons : ∀ {Γ X} (E : TyEntry) → Know Γ X → Know (E ∷ Γ) (suc X)
kn-cons abst      (A₀ , k) = A₀ , skip-abst  k
kn-cons (rvld B)  (A₀ , k) = A₀ , skip-rvld  k
kn-cons (xrvld B) (A₀ , k) = A₀ , skip-xrvld k

kn-uncons : ∀ {Γ X} (E : TyEntry) → Know (E ∷ Γ) (suc X) → Know Γ X
kn-uncons abst      (A₀ , skip-abst  k) = A₀ , k
kn-uncons (rvld B)  (A₀ , skip-rvld  k) = A₀ , k
kn-uncons (xrvld B) (A₀ , skip-xrvld k) = A₀ , k

know? : (Γ : TCtx) (X : ℕ) → Dec (Know Γ X)
know? []              X       = no ¬kn-[]
know? (abst    ∷ Γ)   zero    = no ¬kn-abst
know? (rvld A  ∷ Γ)   zero    = yes (A , here)
know? (xrvld A ∷ Γ)   zero    = no ¬kn-xrvld
know? (E       ∷ Γ) (suc X) =
  map′ (kn-cons E) (kn-uncons E) (know? Γ X)

¬knx-[] : ∀ {X} → ¬ Knowx [] X
¬knx-[] (A′ , ())

¬knx-abst : ∀ {Γ} → ¬ Knowx (abst ∷ Γ) zero
¬knx-abst (A′ , ())

¬knx-rvld : ∀ {Γ A} → ¬ Knowx (rvld A ∷ Γ) zero
¬knx-rvld (A′ , ())

knx-cons : ∀ {Γ X} (E : TyEntry) → Knowx Γ X → Knowx (E ∷ Γ) (suc X)
knx-cons E (A′ , k) = A′ , skipx k

knx-uncons : ∀ {Γ X} (E : TyEntry) → Knowx (E ∷ Γ) (suc X) → Knowx Γ X
knx-uncons E (A′ , skipx k) = A′ , k

knowx? : (Γ : TCtx) (X : ℕ) → Dec (Knowx Γ X)
knowx? []              X       = no ¬knx-[]
knowx? (abst    ∷ Γ)   zero    = no ¬knx-abst
knowx? (rvld A  ∷ Γ)   zero    = no ¬knx-rvld
knowx? (xrvld A ∷ Γ)   zero    = yes (A , herex)
knowx? (E       ∷ Γ) (suc X) =
  map′ (knx-cons E) (knx-uncons E) (knowx? Γ X)

know-uniq : ∀ {Γ X A₀ A₁} → Γ ∋ X := A₀ → Γ ∋ X := A₁ → A₀ ≡ A₁
know-uniq here             here             = refl
know-uniq (skip-abst  k) (skip-abst  k′) = know-uniq k k′
know-uniq (skip-rvld  k) (skip-rvld  k′) = know-uniq k k′
know-uniq (skip-xrvld k) (skip-xrvld k′) = know-uniq k k′

knowx-uniq : ∀ {Γ X A₀ A₁} → Γ ∋ X :=x A₀ → Γ ∋ X :=x A₁ → A₀ ≡ A₁
knowx-uniq herex     herex      = refl
knowx-uniq (skipx k) (skipx k′) = knowx-uniq k k′

know-not-knowx : ∀ {Γ X A₀ A′} → Γ ∋ X := A₀ → Γ ∋ X :=x A′ → ⊥
know-not-knowx here             ()
know-not-knowx (skip-abst  k) (skipx kx) = know-not-knowx k kx
know-not-knowx (skip-rvld  k) (skipx kx) = know-not-knowx k kx
know-not-knowx (skip-xrvld k) (skipx kx) = know-not-knowx k kx

------------------------------------------------------------------------
-- Boundary-frame accessibility and Scoped
------------------------------------------------------------------------

∋ok-suc : ∀ {s Ψ X} → (s ∷ Ψ) ∋ok suc X → Ψ ∋ok X
∋ok-suc (thereᵒ p) = p

∋ok? : (Ψ : SCtx) (X : ℕ) → Dec (Ψ ∋ok X)
∋ok? []          X     = no λ ()
∋ok? (ok  ∷ Ψ) zero    = yes hereᵒ
∋ok? (blk ∷ Ψ) zero    = no λ ()
∋ok? (s   ∷ Ψ) (suc X) = map′ thereᵒ ∋ok-suc (∋ok? Ψ X)

sc-var⁻ : ∀ {Ψ X} → Scoped Ψ (` X) → Ψ ∋ok X
sc-var⁻ (sc-var p) = p

sc-⇒⁻ˡ : ∀ {Ψ A B} → Scoped Ψ (A ⇒ B) → Scoped Ψ A
sc-⇒⁻ˡ (sc-⇒ a b) = a

sc-⇒⁻ʳ : ∀ {Ψ A B} → Scoped Ψ (A ⇒ B) → Scoped Ψ B
sc-⇒⁻ʳ (sc-⇒ a b) = b

sc-∀⁻ : ∀ {Ψ A} → Scoped Ψ (`∀ A) → Scoped (ok ∷ Ψ) A
sc-∀⁻ (sc-∀ a) = a

scoped? : (Ψ : SCtx) (A : Ty) → Dec (Scoped Ψ A)
scoped? Ψ (` X)   = map′ sc-var sc-var⁻ (∋ok? Ψ X)
scoped? Ψ `ℕ      = yes sc-ℕ
scoped? Ψ `𝔹      = yes sc-𝔹
scoped? Ψ (A ⇒ B) with scoped? Ψ A
scoped? Ψ (A ⇒ B) | no  ¬a = no λ s → ¬a (sc-⇒⁻ˡ s)
scoped? Ψ (A ⇒ B) | yes a  with scoped? Ψ B
scoped? Ψ (A ⇒ B) | yes a  | yes b  = yes (sc-⇒ a b)
scoped? Ψ (A ⇒ B) | yes a  | no  ¬b = no λ s → ¬b (sc-⇒⁻ʳ s)
scoped? Ψ (`∀ A)  = map′ sc-∀ sc-∀⁻ (scoped? (ok ∷ Ψ) A)

------------------------------------------------------------------------
-- SkelEq — the (bwf-↓x) rep comparison
------------------------------------------------------------------------

sk-⇒⁻ˡ : ∀ {A B A′ B′} → SkelEq (A ⇒ B) (A′ ⇒ B′) → SkelEq A A′
sk-⇒⁻ˡ (sk-⇒ a b) = a

sk-⇒⁻ʳ : ∀ {A B A′ B′} → SkelEq (A ⇒ B) (A′ ⇒ B′) → SkelEq B B′
sk-⇒⁻ʳ (sk-⇒ a b) = b

sk-∀⁻ : ∀ {A A′} → SkelEq (`∀ A) (`∀ A′) → SkelEq A A′
sk-∀⁻ (sk-∀ a) = a

skel? : (A B : Ty) → Dec (SkelEq A B)
skel? (` X)   (` Y)   = yes sk-var
skel? (` X)   `ℕ      = no λ ()
skel? (` X)   `𝔹      = no λ ()
skel? (` X)   (C ⇒ D) = no λ ()
skel? (` X)   (`∀ D)  = no λ ()
skel? `ℕ      (` Y)   = no λ ()
skel? `ℕ      `ℕ      = yes sk-ℕ
skel? `ℕ      `𝔹      = no λ ()
skel? `ℕ      (C ⇒ D) = no λ ()
skel? `ℕ      (`∀ D)  = no λ ()
skel? `𝔹      (` Y)   = no λ ()
skel? `𝔹      `ℕ      = no λ ()
skel? `𝔹      `𝔹      = yes sk-𝔹
skel? `𝔹      (C ⇒ D) = no λ ()
skel? `𝔹      (`∀ D)  = no λ ()
skel? (A ⇒ B) (` Y)   = no λ ()
skel? (A ⇒ B) `ℕ      = no λ ()
skel? (A ⇒ B) `𝔹      = no λ ()
skel? (A ⇒ B) (`∀ D)  = no λ ()
skel? (A ⇒ B) (C ⇒ D) with skel? A C
skel? (A ⇒ B) (C ⇒ D) | no  ¬a = no λ s → ¬a (sk-⇒⁻ˡ s)
skel? (A ⇒ B) (C ⇒ D) | yes a  with skel? B D
skel? (A ⇒ B) (C ⇒ D) | yes a  | yes b  = yes (sk-⇒ a b)
skel? (A ⇒ B) (C ⇒ D) | yes a  | no  ¬b = no λ s → ¬b (sk-⇒⁻ʳ s)
skel? (`∀ A)  (` Y)   = no λ ()
skel? (`∀ A)  `ℕ      = no λ ()
skel? (`∀ A)  `𝔹      = no λ ()
skel? (`∀ A)  (C ⇒ D) = no λ ()
skel? (`∀ A)  (`∀ D)  = map′ sk-∀ sk-∀⁻ (skel? A D)

------------------------------------------------------------------------
-- THE CONCEAL LICENCE.  A `cnc X A` entry is licensed in exactly two
-- ways — bwf↓ (ordinary knowledge at X) and bwf↓x (exterior-read
-- knowledge at X) — and the exterior's entry at X decides WHICH: ∋:=
-- reads an `rvld` slot and ∋:=x an `xrvld` one, and know-not-knowx says
-- no slot answers both.  CncOK packages the head premises so that the
-- decision is a single case split.
------------------------------------------------------------------------

data CncOK (Γ Ψ : TCtx) (Θ : BCtx) (X : ℕ) (A : Ty) : Set where
  cnc-know : ∀ {A₀} → Γ ∋ X := A₀ → Reversal≈ Γ Θ X A A₀ → Ψ ⊢ A
           → CncOK Γ Ψ Θ X A
  cnc-x    : ∀ {A′} → Γ ∋ X :=x A′ → starOnly Θ 0 A ≡ true
           → SkelEq A A′ → Ψ ⊢ A → CncOK Γ Ψ Θ X A

¬cnc-wf : ∀ {Γ Ψ Θ X A} → ¬ (Ψ ⊢ A) → ¬ CncOK Γ Ψ Θ X A
¬cnc-wf ¬w (cnc-know k r w)   = ¬w w
¬cnc-wf ¬w (cnc-x kx s sk w)  = ¬w w

¬cnc-rev : ∀ {Γ Ψ Θ X A A₀} → Γ ∋ X := A₀ → ¬ Reversal≈ Γ Θ X A A₀
         → ¬ CncOK Γ Ψ Θ X A
¬cnc-rev {Γ} {Ψ} {Θ} {X} {A} k ¬r (cnc-know k′ r′ w) =
  ¬r (subst (Reversal≈ Γ Θ X A) (know-uniq k′ k) r′)
¬cnc-rev k ¬r (cnc-x kx s sk w) = ⊥-elim (know-not-knowx k kx)

¬cnc-none : ∀ {Γ Ψ Θ X A} → ¬ Know Γ X → ¬ Knowx Γ X
          → ¬ CncOK Γ Ψ Θ X A
¬cnc-none ¬k ¬kx (cnc-know {A₀} k r w)  = ¬k (A₀ , k)
¬cnc-none ¬k ¬kx (cnc-x {A′} kx s sk w) = ¬kx (A′ , kx)

¬cnc-star : ∀ {Γ Ψ Θ X A} → ¬ Know Γ X → ¬ (starOnly Θ 0 A ≡ true)
          → ¬ CncOK Γ Ψ Θ X A
¬cnc-star ¬k ¬s (cnc-know {A₀} k r w)  = ¬k (A₀ , k)
¬cnc-star ¬k ¬s (cnc-x kx s sk w)      = ¬s s

¬cnc-skel : ∀ {Γ Ψ Θ X A A′} → ¬ Know Γ X → Γ ∋ X :=x A′
          → ¬ SkelEq A A′ → ¬ CncOK Γ Ψ Θ X A
¬cnc-skel ¬k kx ¬sk (cnc-know {A₀} k r w) = ¬k (A₀ , k)
¬cnc-skel {A = A} ¬k kx ¬sk (cnc-x kx′ s sk w) =
  ¬sk (subst (SkelEq A) (knowx-uniq kx′ kx) sk)

cncOK? : (Γ Ψ : TCtx) (Θ : BCtx) (X : ℕ) (A : Ty)
       → Dec (CncOK Γ Ψ Θ X A)
cncOK? Γ Ψ Θ X A with wf? Ψ A
cncOK? Γ Ψ Θ X A | no  ¬w = no (¬cnc-wf ¬w)
cncOK? Γ Ψ Θ X A | yes w  with know? Γ X
cncOK? Γ Ψ Θ X A | yes w | yes (A₀ , k)
  with ≈? Γ (outRead Θ A) (upRep X A₀)
cncOK? Γ Ψ Θ X A | yes w | yes (A₀ , k) | yes r =
  yes (cnc-know k r w)
cncOK? Γ Ψ Θ X A | yes w | yes (A₀ , k) | no ¬r =
  no (¬cnc-rev k ¬r)
cncOK? Γ Ψ Θ X A | yes w | no ¬k with knowx? Γ X
cncOK? Γ Ψ Θ X A | yes w | no ¬k | no ¬kx = no (¬cnc-none ¬k ¬kx)
cncOK? Γ Ψ Θ X A | yes w | no ¬k | yes (A′ , kx)
  with starOnly Θ 0 A ≟ᵇ true
cncOK? Γ Ψ Θ X A | yes w | no ¬k | yes (A′ , kx) | no ¬s =
  no (¬cnc-star ¬k ¬s)
cncOK? Γ Ψ Θ X A | yes w | no ¬k | yes (A′ , kx) | yes s
  with skel? A A′
cncOK? Γ Ψ Θ X A | yes w | no ¬k | yes (A′ , kx) | yes s | yes sk =
  yes (cnc-x kx s sk w)
cncOK? Γ Ψ Θ X A | yes w | no ¬k | yes (A′ , kx) | yes s | no ¬sk =
  no (¬cnc-skel ¬k kx ¬sk)

------------------------------------------------------------------------
-- Boundary well-formedness, entry by entry
------------------------------------------------------------------------

cncOK→bwf : ∀ {Γ Ψ Θ X A Ξ} → CncOK Γ Ψ Θ X A → Bwf Γ Ψ Θ Ξ
          → Bwf Γ Ψ Θ (cnc X A ∷ Ξ)
cncOK→bwf (cnc-know k r w)  b = bwf↓ k r w b
cncOK→bwf (cnc-x kx s sk w) b = bwf↓x kx s sk w b

bwf-rvl-hd : ∀ {Γ Ψ Θ A Ξ} → Bwf Γ Ψ Θ (rvl A ∷ Ξ) → Γ ⊢ A
bwf-rvl-hd (bwf↑ w b) = w

bwf-rvl-tl : ∀ {Γ Ψ Θ A Ξ} → Bwf Γ Ψ Θ (rvl A ∷ Ξ) → Bwf Γ Ψ Θ Ξ
bwf-rvl-tl (bwf↑ w b) = b

bwf-rvl⋆-tl : ∀ {Γ Ψ Θ Ξ} → Bwf Γ Ψ Θ (rvl⋆ ∷ Ξ) → Bwf Γ Ψ Θ Ξ
bwf-rvl⋆-tl (bwf⋆ b) = b

bwf-cnc-hd : ∀ {Γ Ψ Θ X A Ξ} → Bwf Γ Ψ Θ (cnc X A ∷ Ξ) → CncOK Γ Ψ Θ X A
bwf-cnc-hd (bwf↓  k r w b)    = cnc-know k r w
bwf-cnc-hd (bwf↓x kx s sk w b) = cnc-x kx s sk w

bwf-cnc-tl : ∀ {Γ Ψ Θ X A Ξ} → Bwf Γ Ψ Θ (cnc X A ∷ Ξ) → Bwf Γ Ψ Θ Ξ
bwf-cnc-tl (bwf↓  k r w b)     = b
bwf-cnc-tl (bwf↓x kx s sk w b) = b

bwf-cnc⋆-hd : ∀ {Γ Ψ Θ X Ξ} → Bwf Γ Ψ Θ (cnc⋆ X ∷ Ξ) → Γ ∋tv X
bwf-cnc⋆-hd (bwf⋆↓ p b) = p

bwf-cnc⋆-tl : ∀ {Γ Ψ Θ X Ξ} → Bwf Γ Ψ Θ (cnc⋆ X ∷ Ξ) → Bwf Γ Ψ Θ Ξ
bwf-cnc⋆-tl (bwf⋆↓ p b) = b

bwf? : (Γ Ψ : TCtx) (Θ Ξ : BCtx) → Dec (Bwf Γ Ψ Θ Ξ)
bwf? Γ Ψ Θ []             = yes bwf[]
bwf? Γ Ψ Θ (rvl A ∷ Ξ)   with wf? Γ A
bwf? Γ Ψ Θ (rvl A ∷ Ξ)   | no  ¬w = no λ b → ¬w (bwf-rvl-hd b)
bwf? Γ Ψ Θ (rvl A ∷ Ξ)   | yes w  =
  map′ (bwf↑ w) bwf-rvl-tl (bwf? Γ Ψ Θ Ξ)
bwf? Γ Ψ Θ (rvl⋆ ∷ Ξ)    =
  map′ bwf⋆ bwf-rvl⋆-tl (bwf? Γ Ψ Θ Ξ)
bwf? Γ Ψ Θ (cnc X A ∷ Ξ) with cncOK? Γ Ψ Θ X A
bwf? Γ Ψ Θ (cnc X A ∷ Ξ) | no  ¬c = no λ b → ¬c (bwf-cnc-hd b)
bwf? Γ Ψ Θ (cnc X A ∷ Ξ) | yes c  =
  map′ (cncOK→bwf c) bwf-cnc-tl (bwf? Γ Ψ Θ Ξ)
bwf? Γ Ψ Θ (cnc⋆ X ∷ Ξ)  with ∋tv? Γ X
bwf? Γ Ψ Θ (cnc⋆ X ∷ Ξ)  | no  ¬p = no λ b → ¬p (bwf-cnc⋆-hd b)
bwf? Γ Ψ Θ (cnc⋆ X ∷ Ξ)  | yes p  =
  map′ (bwf⋆↓ p) bwf-cnc⋆-tl (bwf? Γ Ψ Θ Ξ)

⊢ᵇ? : (Γ Ψ : TCtx) (Θ : BCtx) → Dec (Γ ∣ Ψ ⊢ᵇ Θ)
⊢ᵇ? Γ Ψ Θ = bwf? Γ Ψ Θ Θ

------------------------------------------------------------------------
-- The knowledge ordering _≼≈_, entrywise.  The LEFT entry decides the
-- clause: `abst` takes ≼≈abst against ANY right entry, `xrvld A` forces
-- the same x-rep on the right, `rvld A` forces an `rvld B` with
-- A ≈Δ̄⟨ Δ′ ⟩ B — so there is never a choice to make.
------------------------------------------------------------------------

≼≈-abst⁻ : ∀ {Δ Δ′ E} → (abst ∷ Δ) ≼≈ (E ∷ Δ′) → Δ ≼≈ Δ′
≼≈-abst⁻ (≼≈abst p) = p

≼≈-x⁻ : ∀ {Δ Δ′ A} → (xrvld A ∷ Δ) ≼≈ (xrvld A ∷ Δ′) → Δ ≼≈ Δ′
≼≈-x⁻ (≼≈xrvld p) = p

≼≈-r⁻ : ∀ {Δ Δ′ A B} → (rvld A ∷ Δ) ≼≈ (rvld B ∷ Δ′) → Δ ≼≈ Δ′
≼≈-r⁻ (≼≈rvld p e) = p

≼≈-r≈ : ∀ {Δ Δ′ A B} → (rvld A ∷ Δ) ≼≈ (rvld B ∷ Δ′) → A ≈Δ̄⟨ Δ′ ⟩ B
≼≈-r≈ (≼≈rvld p e) = e

-- an xrvld on the left against an xrvld on the right whose rep DIFFERS
-- is refuted by the constructor's own index, once the reps are compared
≼≈-x-rep : ∀ {Δ Δ′ A B} → (xrvld A ∷ Δ) ≼≈ (xrvld B ∷ Δ′) → A ≡ B
≼≈-x-rep (≼≈xrvld p) = refl

≼≈? : (Δ Δ′ : TCtx) → Dec (Δ ≼≈ Δ′)
≼≈? []              []               = yes ≼≈[]
≼≈? []              (F ∷ Δ′)         = no λ ()
≼≈? (E ∷ Δ)         []               = no λ ()
≼≈? (abst ∷ Δ)      (F ∷ Δ′)         =
  map′ ≼≈abst ≼≈-abst⁻ (≼≈? Δ Δ′)
≼≈? (xrvld A ∷ Δ)   (abst ∷ Δ′)      = no λ ()
≼≈? (xrvld A ∷ Δ)   (rvld B ∷ Δ′)    = no λ ()
≼≈? (xrvld A ∷ Δ)   (xrvld B ∷ Δ′)   with A ≟ᵗ B
≼≈? (xrvld A ∷ Δ)   (xrvld B ∷ Δ′)   | no  ne =
  no λ p → ne (≼≈-x-rep p)
≼≈? (xrvld A ∷ Δ)   (xrvld B ∷ Δ′)   | yes refl =
  map′ ≼≈xrvld ≼≈-x⁻ (≼≈? Δ Δ′)
≼≈? (rvld A ∷ Δ)    (abst ∷ Δ′)      = no λ ()
≼≈? (rvld A ∷ Δ)    (xrvld B ∷ Δ′)   = no λ ()
≼≈? (rvld A ∷ Δ)    (rvld B ∷ Δ′)    with ≈? Δ′ A B
≼≈? (rvld A ∷ Δ)    (rvld B ∷ Δ′)    | no  ¬e =
  no λ p → ¬e (≼≈-r≈ p)
≼≈? (rvld A ∷ Δ)    (rvld B ∷ Δ′)    | yes e  =
  map′ (λ p → ≼≈rvld p e) ≼≈-r⁻ (≼≈? Δ Δ′)

------------------------------------------------------------------------
-- *** THE MERGE GUARD ***  All five MergeOK components, fully decided:
--
--   (1) the composite's INTERNAL face is the inner boundary's own   ≟ᵗ
--   (2) the composite is a well-formed boundary over Δ              ⊢ᵇ?
--   (3) the merged face is Scoped over the composite's stack        scoped?
--   (4) the contexts compose, in ⊢retag≈'s direction                ≼≈?
--   (5) the composite's EXTERNAL face is the redex's own type       ≟ᵗ
------------------------------------------------------------------------

mergeOK? : (Δ : TCtx) (Θ₁ Θ₂ : BCtx) (B₁ B₂ : Ty)
         → Dec (MergeOK Δ Θ₁ Θ₂ B₁ B₂)
mergeOK? Δ Θ₁ Θ₂ B₁ B₂ =
  (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≟ᵗ substᵗ (γᵇ Θ₁) B₁)
    ×-dec
  (⊢ᵇ? Δ (intOf Δ (Θ₁ ⊕ Θ₂)) (Θ₁ ⊕ Θ₂)
    ×-dec
  (scoped? (baseS (Θ₁ ⊕ Θ₂) Δ) (mrgB Θ₁ Θ₂ B₁)
    ×-dec
  (≼≈? (intOf (intOf Δ Θ₂) Θ₁) (intOf Δ (Θ₁ ⊕ Θ₂))
    ×-dec
  (substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≟ᵗ substᵗ (ρᵇ Θ₂) B₂))))

------------------------------------------------------------------------
-- The syntactic classifiers: Inert / Active / GVal / Value.
-- ActiveOrInert (strong.BReduction) already says the face split is
-- total; these are the two halves as deciders, plus the value predicate
-- the ξ frames and the redex rules are guarded by.
------------------------------------------------------------------------

I-var⁻ : ∀ {Θ X} → Inert Θ (` X) → revs Θ ≤ X
I-var⁻ (I-var p) = p

A-var⁻ : ∀ {Θ X} → Active Θ (` X) → X < revs Θ
A-var⁻ (A-var p) = p

inert? : (Θ : BCtx) (B₀ : Ty) → Dec (Inert Θ B₀)
inert? Θ (` X)   = map′ I-var I-var⁻ (revs Θ ≤? X)
inert? Θ `ℕ      = no λ ()
inert? Θ `𝔹      = no λ ()
inert? Θ (A ⇒ B) = yes I-⇒
inert? Θ (`∀ B)  = yes I-∀

active? : (Θ : BCtx) (B₀ : Ty) → Dec (Active Θ B₀)
active? Θ (` X)   = map′ A-var A-var⁻ (X <? revs Θ)
active? Θ `ℕ      = yes A-ℕ
active? Θ `𝔹      = yes A-𝔹
active? Θ (A ⇒ B) = no λ ()
active? Θ (`∀ B)  = no λ ()

¬gval-` : ∀ {x} → ¬ GVal (` x)
¬gval-` ()

G-Λ⁻ : ∀ {N} → GVal (Λ N) → Value N
G-Λ⁻ (G-Λ v) = v

V-Λ⁻ : ∀ {N} → Value (Λ N) → Value N
V-Λ⁻ (V-G (G-Λ v)) = v

V-⟪⟫⁻ᵥ : ∀ {M Θ B₀} → Value (M ⟪ Θ , B₀ ⟫) → Value M
V-⟪⟫⁻ᵥ (V-⟪⟫ v i) = v

V-⟪⟫⁻ᵢ : ∀ {M Θ B₀} → Value (M ⟪ Θ , B₀ ⟫) → Inert Θ B₀
V-⟪⟫⁻ᵢ (V-⟪⟫ v i) = i

¬val-` : ∀ {x} → ¬ Value (` x)
¬val-` (V-G ())

¬val-· : ∀ {L M} → ¬ Value (L · M)
¬val-· (V-G ())

¬val-·[] : ∀ {L B A} → ¬ Value (L ·[ B , A ])
¬val-·[] (V-G ())

gval? : (M : Term) → Dec (GVal M)
value? : (M : Term) → Dec (Value M)

gval? (` x)          = no ¬gval-`
gval? ($ n)          = no λ ()
gval? (ƛ A ∙ N)      = yes G-ƛ
gval? (L · M)        = no λ ()
gval? (Λ N)          = map′ G-Λ G-Λ⁻ (value? N)
gval? (L ·[ B , A ]) = no λ ()
gval? (M ⟪ Θ , B₀ ⟫) = no λ ()

value? (` x)          = no ¬val-`
value? ($ n)          = yes V-$
value? (ƛ A ∙ N)      = yes (V-G G-ƛ)
value? (L · M)        = no ¬val-·
value? (Λ N)          = map′ (λ v → V-G (G-Λ v)) V-Λ⁻ (value? N)
value? (L ·[ B , A ]) = no ¬val-·[]
value? (M ⟪ Θ , B₀ ⟫) with value? M
value? (M ⟪ Θ , B₀ ⟫) | no  ¬v = no λ w → ¬v (V-⟪⟫⁻ᵥ w)
value? (M ⟪ Θ , B₀ ⟫) | yes v  with inert? Θ B₀
value? (M ⟪ Θ , B₀ ⟫) | yes v  | yes i  = yes (V-⟪⟫ v i)
value? (M ⟪ Θ , B₀ ⟫) | yes v  | no  ¬i = no λ w → ¬i (V-⟪⟫⁻ᵢ w)

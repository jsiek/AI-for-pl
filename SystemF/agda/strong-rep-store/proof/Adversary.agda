module strong-rep-store.proof.Adversary where

-- File Charter:
--   * THE SOUNDNESS GATE, and the adversaries of the previous design,
--     refuted.  §1 the gate; §2 the abstract-slot adversary; §2b the
--     unbound-name adversary, new on this branch; §3 `bad`, two
--     spellings of one fact; §4 cancel's type equation.
--   * A CONCEAL MUST CITE A REPRESENTED BINDER — a one-line inversion
--     of `conv-seal`.  With two universes `Δ ∋ X := A` is a SQUARE, so
--     the gate refuses a seal for TWO independent reasons: the name
--     may be absent from the map, or the representation variable it
--     names may be `abstR`.  No change list repairs either.
-- Commentary: Commentary.md § proof/Adversary.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary

------------------------------------------------------------------------
-- 1.  The gate
------------------------------------------------------------------------

seal-cites-binder : ∀ {Δ X A B c}
  → Δ ⊢ c ∶ A ⇝ B → c ≡ seal X → Δ ∋ X := A
seal-cites-binder (conv-seal d) refl = d

-- Spelled out: the cited ordinary name is LIVE, the representation
-- variable it names is REPRESENTED, and the seal's source type is that
-- representation read on the conversion context.  No other premise exists.
seal-cites-representation : ∀ {Δ X A B} → Δ ⊢ seal X ∶ A ⇝ B
  → ∃[ α ] ∃[ R ]
      ((Δ ∋ᵗ X := α) × (Δ ∋rep α := R) × (Δ ⊢ᶜ A ~ R))
seal-cites-representation (conv-seal d) = d

------------------------------------------------------------------------
-- 2.  THE ADVERSARY (the old ⊢3n-adv): a conceal asserting false knowledge
------------------------------------------------------------------------

-- Ordinary name 0 names an ABSTRACT representation variable, so
-- `seal 0` asks `abstR` to be a `bindR`: the boundary is UNMINTABLE.
-- Commentary.md § proof/Adversary.agda / §2

Δadv : Ctxᵗ
Δadv = (abstR ∷ []) ∣ (zero ∷ [])

-- the abstract slot has no representation to cite
¬rep-adv : ∀ {R} → Δadv ∋rep zero := R → ⊥
¬rep-adv ()

¬know-adv : ∀ {A} → Δadv ∋ 0 := A → ⊥
¬know-adv (α , R , here , rep , same) = ¬rep-adv rep

¬seal-adv : ∀ {A B} → Δadv ⊢ seal 0 ∶ A ⇝ B → ⊥
¬seal-adv (conv-seal d) = ¬know-adv d

-- The boundary scope the adversary used to hide behind: it unbinds the very name
-- its conversion cites.  A conversion context SKIPS an unbind, so the unbind
-- buys nothing — the seal is still read where the slot is abstract.
Θadv : Boundary
Θadv = (unbind 0 zero ∷ [])

conv-Θadv : ∀ {Δᶜ} → Δadv ⊢ᶜ Θadv ⇒ Δᶜ → Δᶜ ≡ Δadv
conv-Θadv (conversion (conv-unbind valid conv[])) = refl

¬⊢adv : ∀ {Γ} → ¬ (Δadv ∣ Γ ⊢ ($ 7) ⟪ Θadv , seal 0 ⟫ ⦂ ` 0)
¬⊢adv (env mwᵥ ⊢M ⊢c smᵢ smₑ wE)
  with conv-Θadv (bw-conversion mwᵥ)
... | refl = ¬seal-adv ⊢c

------------------------------------------------------------------------
-- 2b.  THE SECOND GATE, NEW ON THIS BRANCH: a conceal at a UNBOUND name
------------------------------------------------------------------------

-- An unbind DELETES the ordinary name, so a seal at a name the interior
-- lost is refused by the NAME half of the square.

Δlk : Ctxᵗ
Δlk = (bindR `ℕ ∷ []) ∣ []

¬name-lk : ∀ {α} → Δlk ∋ᵗ 0 := α → ⊥
¬name-lk ()

¬seal-lk : ∀ {A B} → Δlk ⊢ seal 0 ∶ A ⇝ B → ⊥
¬seal-lk (conv-seal (α , R , name , rep , same)) = ¬name-lk name

------------------------------------------------------------------------
-- 3.  `bad`: two spellings of one fact — inexpressible
------------------------------------------------------------------------

-- `seal 0` reads the binder, so the source type IS the binder's
-- representation: there are not two spellings to disagree.
-- Commentary.md § proof/Adversary.agda / §3

∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

Δbad : Ctxᵗ
Δbad = (bindR ∀ZZ ∷ []) ∣ (zero ∷ [])

-- The stored payload, looked up, is ∀ZZ again: `⇑ᵗ` moves only the FREE
-- representation occurrences, and ∀ZZ has none.
bad-lookup : Δbad ∋rep zero := ∀ZZ
bad-lookup = r-here

-- … and ∀ZZ has exactly one ordinary reading on `names Δbad`.
bad-reading : Δbad ⊢ᶜ ∀ZZ ~ ∀ZZ
bad-reading = same-∀ (same-⇒ (same-var here) (same-var here))

seal-bad-conv : ∀ {A B} → Δbad ⊢ seal 0 ∶ A ⇝ B → A ≡ ∀ZZ
seal-bad-conv (conv-seal (α , R , here , rep , same))
  with ∋ʳ-det rep bad-lookup
... | refl =
  same-target-unique (unique∷ fresh[] unique[]) same bad-reading

-- The adversary's term is `7` behind that conceal, presented at `` ` 0 ``.
-- It is refused by the seal's SOURCE type alone: `env` makes the boundary's
-- interior type and the conversion's source two spellings of one
-- representation, and `7 : ℕ` cannot spell ∀Z.Z→Z.
¬same-ℕ-∀ : ∀ {η η′ R} → η ⊢ `ℕ ~ R → η′ ⊢ ∀ZZ ~ R → ⊥
¬same-ℕ-∀ same-ℕ ()

¬⊢bad : ∀ {Γ Θ} → Δbad ⊢ᶜ Θ ⇒ Δbad
  → ¬ (Δbad ∣ Γ ⊢ ($ 7) ⟪ Θ , seal 0 ⟫ ⦂ ` 0)
¬⊢bad rc (env mwᵥ ⊢$ ⊢c (R , pᵢ , qᵢ) smₑ wE)
  with conversion-functional (bw-conversion mwᵥ) rc
¬⊢bad rc (env mwᵥ ⊢$ ⊢c (R , pᵢ , qᵢ) smₑ wE) | refl
  with seal-bad-conv ⊢c
¬⊢bad rc (env mwᵥ ⊢$ ⊢c (R , pᵢ , qᵢ) smₑ wE) | refl | refl =
  ¬same-ℕ-∀ pᵢ qᵢ

------------------------------------------------------------------------
-- 4.  CANCEL'S TYPE EQUATION
------------------------------------------------------------------------

-- The inner conceal's SOURCE and the outer reveal's TARGET are the SAME
-- lookup square on the SAME conversion context, hence equal — once the
-- name map is a function, which every `BoundaryWf` supplies.
cancel-types-agree : ∀ {Δ X A B A′ B′}
  → Unique (names Δ)
  → Δ ⊢ seal X ∶ A ⇝ B       -- the inner conceal
  → Δ ⊢ unseal X ∶ A′ ⇝ B′   -- the binder it names
    ---------------------------
  → A ≡ B′
cancel-types-agree uq cs cu =
  ∋:=-det uq (seal-source-is-rep cs)
             (unseal-target-is-rep cu)

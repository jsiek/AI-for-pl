module strong-rep-nu.proof.Adversary where

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
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary

------------------------------------------------------------------------
-- 1.  The gate
------------------------------------------------------------------------

seal-cites-binder : ∀ {Δ Θ X A B c}
  → Δ ∣ Θ ⊢ c ∶ A ⇝ B → c ≡ tail (seal X)
  → ∃[ α ] ((Δ ∋ X ⊸ α := A) × SealOK Θ α)
seal-cites-binder (conv-tail (conv-seal d ok)) refl = _ , d , ok

-- Spelled out: the cited ordinary name is LIVE, the representation
-- variable it names is REPRESENTED — and the seal's source type IS that
-- representation, readable on the conversion context — and the scope
-- GRANTS the seal.  No other premise exists.
seal-cites-representation : ∀ {Δ Θ X A B}
  → Δ ∣ Θ ⊢ tail (seal X) ∶ A ⇝ B
  → ∃[ α ] ((Δ ∋ᵗ X := α) × (Δ ∋rep α := A)
             × (∃[ A′ ] (Δ ⊢ᶜ A′ ~ A)) × SealOK Θ α)
seal-cites-representation (conv-tail (conv-seal (nm , rp , rd) ok)) =
  _ , nm , rp , rd , ok

------------------------------------------------------------------------
-- 2.  THE ADVERSARY (the old ⊢3n-adv): a conceal asserting false knowledge
------------------------------------------------------------------------

-- Ordinary name 0 names an ABSTRACT representation variable, so
-- `seal 0` asks `abstR` to be a `bindR`: the boundary cannot be created.
-- Commentary.md § proof/Adversary.agda / §2

Δadv : Ctxᵗ
Δadv = (abstR ∷ []) ∣ (zero ∷ [])

-- the abstract slot has no representation to cite
¬rep-adv : ∀ {R} → Δadv ∋rep zero := R → ⊥
¬rep-adv ()

¬know-adv : ∀ {α A} → Δadv ∋ 0 ⊸ α := A → ⊥
¬know-adv (here , rep , _) = ¬rep-adv rep

¬seal-adv : ∀ {Θ A B} → Δadv ∣ Θ ⊢ tail (seal 0) ∶ A ⇝ B → ⊥
¬seal-adv (conv-tail (conv-seal d ok)) = ¬know-adv d

-- The boundary scope the adversary used to hide behind: it unbinds the
-- very name its conversion cites.  That grants the PERMISSION, but a
-- conversion context SKIPS an unbind, so the seal is still read where
-- the slot is abstract.
Θadv : Boundary
Θadv = (unbind 0 zero ∷ [])

conv-Θadv : ∀ {Δᶜ} → Δadv ⊢ᶜ Θadv ⇒ Δᶜ → Δᶜ ≡ Δadv
conv-Θadv (conversion (conv-unbind valid conv[])) = refl

¬⊢adv : ∀ {Γ} → ¬ (Δadv ∣ Γ ⊢ ($ 7) ⟪ Θadv , tail (seal 0) ⟫ ⦂ ` 0)
¬⊢adv (boundary mwᵥ ⊢M ⊢c smᵢ smₑ wE)
  with conv-Θadv (bw-conversion mwᵥ)
... | refl = ¬seal-adv ⊢c

------------------------------------------------------------------------
-- 2b.  THE SECOND GATE: a conceal at an UNBOUND name
------------------------------------------------------------------------

-- An unbind DELETES the ordinary name, so a seal at a name the interior
-- lost is refused by the NAME half of the leaf.

Δlk : Ctxᵗ
Δlk = (bindR `ℕ ∷ []) ∣ []

¬name-lk : ∀ {α} → Δlk ∋ᵗ 0 := α → ⊥
¬name-lk ()

¬seal-lk : ∀ {Θ A B} → Δlk ∣ Θ ⊢ tail (seal 0) ∶ A ⇝ B → ⊥
¬seal-lk (conv-tail (conv-seal (name , rep , _) ok)) = ¬name-lk name

------------------------------------------------------------------------
-- 2c.  THE THIRD GATE, NEW WITH THE Δ ∣ Θ EXPERIMENT: the permission
------------------------------------------------------------------------

-- Before 2026-10-25 a seal needed only a live, represented name, so
-- `($ 7) ⟪ [] , seal 0 ⟫` typed at an ambient that names a cell.  The
-- empty scope unbinds nothing, so it grants no seal.

Δnm : Ctxᵗ
Δnm = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

¬seal-empty : ∀ {A B} → Δnm ∣ [] ⊢ tail (seal 0) ∶ A ⇝ B → ⊥
¬seal-empty {⁺} (conv-tail (conv-seal d ()))
¬seal-empty {⁻} (conv-tail (conv-seal d ()))

empty-conv : ∀ {Δᶜ} → Δnm ⊢ᶜ [] ⇒ Δᶜ → Δᶜ ≡ Δnm
empty-conv (conversion conv[]) = refl

¬⊢empty : ∀ {Γ} → ¬ (Δnm ∣ Γ ⊢ ($ 7) ⟪ [] , tail (seal 0) ⟫ ⦂ ` 0)
¬⊢empty (boundary mwᵥ ⊢M ⊢c smᵢ smₑ wE)
  with empty-conv (bw-conversion mwᵥ)
... | refl = ¬seal-empty ⊢c

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

seal-bad-conv : ∀ {Θ A B} → Δbad ∣ Θ ⊢ tail (seal 0) ∶ A ⇝ B
  → A ≡ ∀ZZ
seal-bad-conv (conv-tail (conv-seal (here , rep , _) ok))
  with ∋ʳ-det rep bad-lookup
... | refl = refl

-- The adversary's term is `7` behind that conceal, presented at `` ` 0 ``.
-- It is refused by the seal's SOURCE type alone: `boundary` reads the
-- boundary's interior type as the conversion's source representation,
-- and `7 : ℕ` does not denote ∀Z.Z→Z.
¬same-ℕ-∀ : ∀ {η} → η ⊢ `ℕ ~ ∀ZZ → ⊥
¬same-ℕ-∀ ()

¬⊢bad : ∀ {Γ Θ} → Δbad ⊢ᶜ Θ ⇒ Δbad
  → ¬ (Δbad ∣ Γ ⊢ ($ 7) ⟪ Θ , tail (seal 0) ⟫ ⦂ ` 0)
¬⊢bad rc (boundary mwᵥ ⊢$ ⊢c pᵢ smₑ wE)
  with conversion-functional (bw-conversion mwᵥ) rc
¬⊢bad rc (boundary mwᵥ ⊢$ ⊢c pᵢ smₑ wE) | refl
  with seal-bad-conv ⊢c
¬⊢bad rc (boundary mwᵥ ⊢$ ⊢c pᵢ smₑ wE) | refl | refl = ¬same-ℕ-∀ pᵢ

------------------------------------------------------------------------
-- 4.  THE CANCELLED PAIR'S TYPE EQUATION (composition's seal ⨟ unseal)
------------------------------------------------------------------------

-- The inner conceal's SOURCE and the outer reveal's TARGET are the SAME
-- leaf on the SAME conversion context, hence equal.  With
-- representation types no `Unique` premise is needed.
cancel-types-agree : ∀ {Δ Θ Θ′ X A B A′ B′}
  → Δ ∣ Θ ⊢ tail (seal X) ∶ A ⇝ B       -- the inner conceal
  → Δ ∣ Θ′ ⊢ unseal X ∶ A′ ⇝ B′   -- the binder it names
    ---------------------------
  → A ≡ B′
cancel-types-agree cs cu with seal-source-is-rep cs | unseal-target-is-rep cu
... | α , d , _ | α′ , d′ , _ = proj₂ (leaf-det d d′)

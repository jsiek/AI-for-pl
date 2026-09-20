module strong.proof.Adversary where

-- THE SOUNDNESS GATE, and the adversaries of the previous design, refuted.
--
-- A CONCEAL MUST CITE A REPRESENTED BINDER.  That is the whole gate, and it
-- is a one-line inversion: `conv-seal` has no other premise.  Under the
-- design before the representation-variable split the same fact needed
-- mwf↓ + Reversal≈, or mwf↓x + starOnly + SkelEq, and the adversary passed
-- ≡, ≈Δ̄ and SkelEq (only `starOnly` refused it).
--
-- WHAT THE TWO UNIVERSES CHANGE.  `Δ ∋ X := A` is now a SQUARE (strong.Ctx
-- §5): ordinary name X names a representation variable α, α carries a
-- `bindR R`, and A is R read back through the current ordinary name map.
-- The gate therefore refuses a seal for two independent reasons — the name
-- may be absent from the map (§2b), or the representation variable it names
-- may be `abstR` (§2).  Neither can be repaired by a change list: a `lock`
-- deletes a name and an `unlock` restores one, and NO change rewrites a
-- representation binding.
--
-- WHAT WAS DELETED (2026-09-19).  The masking half of this module —
-- `unlock-claims-a-lock` and `unlock-mentions-no-rep`, statements about
-- `∋lk`, `Nameable` and `applyChanges` — has no two-universe counterpart:
-- an unlock no longer clears a bit at a retained entry, it INSERTS a name,
-- and what it claims is `Ξ ∋ʳ α` plus freshness, which is already the
-- rule's own premise (`step-unlock`, strong.CtxMorph §2).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph

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

-- At a type context where ordinary name 0 names an ABSTRACT representation
-- variable — Λ-bound, no payload — the adversary exported `7 : ℕ` at the
-- abstract type.  Here the boundary is unmintable, because `seal 0` demands
-- `Δadv ∋ 0 := A`, whose middle component asks `abstR` to be a `bindR`.

Δadv : Ctxᵗ
Δadv = (abstR ∷ []) ∣ (zero ∷ [])

-- the abstract slot has no representation to cite
¬rep-adv : ∀ {R} → Δadv ∋rep zero := R → ⊥
¬rep-adv ()

¬know-adv : ∀ {A} → Δadv ∋ 0 := A → ⊥
¬know-adv (α , R , here , rep , same) = ¬rep-adv rep

¬seal-adv : ∀ {A B} → Δadv ⊢ seal 0 ∶ A ⇝ B → ⊥
¬seal-adv (conv-seal d) = ¬know-adv d

-- The morphism the adversary used to hide behind: it locks the very name
-- its conversion cites.  A conversion context SKIPS a lock, so the lock
-- buys nothing — the seal is still read where the slot is abstract.
Θadv : CtxMorph
Θadv = morph [] (lock 0 zero ∷ [])

conv-Θadv : ∀ {Δᶜ} → Δadv ⊢ᶜ Θadv ⇒ Δᶜ → Δᶜ ≡ Δadv
conv-Θadv (conversion (conv-lock valid conv[])) = refl

¬⊢adv : ∀ {Γ} → ¬ (Δadv ∣ Γ ⊢ ($ 7) ⟪ Θadv , seal 0 ⟫ ⦂ ` 0)
¬⊢adv (env mwᵥ ⊢M ⊢c smᵢ smₑ wE)
  with conv-Θadv (mw-conversion mwᵥ)
... | refl = ¬seal-adv ⊢c

------------------------------------------------------------------------
-- 2b.  THE SECOND GATE, NEW ON THIS BRANCH: a conceal at a LOCKED name
------------------------------------------------------------------------

-- The old design kept a locked slot's entry and marked it; here a lock
-- DELETES the ordinary name.  A seal at a name the interior lost is
-- therefore refused by the name half of the square rather than by the
-- representation half — and this is the reading that replaces `∋lk`.

Δlk : Ctxᵗ
Δlk = (bindR `ℕ ∷ []) ∣ []

¬name-lk : ∀ {α} → Δlk ∋ᵗ 0 := α → ⊥
¬name-lk ()

¬seal-lk : ∀ {A B} → Δlk ⊢ seal 0 ∶ A ⇝ B → ⊥
¬seal-lk (conv-seal (α , R , name , rep , same)) = ¬name-lk name

------------------------------------------------------------------------
-- 3.  `bad`: two spellings of one fact — inexpressible
------------------------------------------------------------------------

-- An inner conceal at representation ℕ under a binder whose representation
-- is ∀Z.Z→Z.  The two spellings cannot disagree, because there is only
-- ONE: `seal 0` reads the binder, so the source type IS the binder's
-- representation, read back through the name map.

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
  with conversion-functional (mw-conversion mwᵥ) rc
... | refl with seal-bad-conv ⊢c
...   | refl = ¬same-ℕ-∀ pᵢ qᵢ

------------------------------------------------------------------------
-- 4.  CANCEL'S TYPE EQUATION
------------------------------------------------------------------------

-- At a cancel the inner conceal's SOURCE type and the outer reveal's
-- TARGET type are the SAME lookup square on the SAME conversion context,
-- hence equal — once the name map is a function, which is exactly what
-- `WfCtx.name-fn` says and what every `MorphWf` supplies.  This one lemma
-- replaces cancel-agree + Reversal≈ + SkelEq + xrep-stored + MergeOK's two
-- type equations.
cancel-types-agree : ∀ {Δ X A B A′ B′}
  → Unique (names Δ)
  → Δ ⊢ seal X ∶ A ⇝ B       -- the inner conceal
  → Δ ⊢ unseal X ∶ A′ ⇝ B′   -- the binder it names
    ---------------------------
  → A ≡ B′
cancel-types-agree uq cs cu =
  ∋:=-det uq (seal-source-is-rep cs)
             (unseal-target-is-rep cu)

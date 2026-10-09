module proof.DGG.KappaWeakenDef where

-- File Charter:
--   * THE STATEMENT of κ-weakening at rep. vars bound to joined type
--     variables (design.md D32, §C9.2; DRAFT for Jeremy's review,
--     2026-10-09, NOT approved, NOT proved: major-lemma check-in).  A
--     closed derivation at W relates the same terms at `W +κ K` when
--     every added right rep. var β is bound to a right type variable
--     joined, in W, to a left one (`BoundJoined`).
--   * WHY THE SIDE CONDITION.  Unrestricted κ-weakening is FALSE:
--     examples/TermImprecisionD32Examples `KW.kw-left-only` (the seal
--     `[−X^α] 5 ⟨−X⟩ ⊑ 5⟨ℕ!⟩` at a left-only X is related with αᴿ
--     unpermitted and unrelated with it permitted: R1′).  At a β bound
--     to a joined type variable the R1′/R2 uses of the derivation sit
--     inside right boundaries that unjoin β's type variable (a joined,
--     unpermitted X admits no one-sided left seal against ★), and each
--     such boundary may now REVOKE β, paying with its own exterior index
--     read without β, which is the index the original derivation already
--     had
--     (`KW.kw-joined-uses-drop`: the revocation is necessary).
--   * WHO USES IT (Wrap; M16 SimApp, M19 SimBackApp).  Wrap moves the
--     argument W into the dual `[dual Θ] W ⟨s′⟩` inside the function's
--     boundary, whose premise world is `Wᵢ ⇂κ κ₁ +κ K`.  The dual
--     UNJOINS the type variables the function boundary joined by a
--     fresh entry (`jr-join`), so it revokes those permissions, paying
--     with the domain half of the function boundary's payment; it
--     REJOINS the type variables the function boundary unjoined, so it
--     may permit again the permissions that boundary revoked, paying
--     with the domain half of that boundary's revocation payment; what
--     remains are the permissions of rebinds (`jr-rebind`), whose type
--     variables continue through the dual and are joined in the
--     argument's world: BoundJoined, so this lemma.
--     (`KW.post-uses-drop` is the instance where the dual must revoke.)
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)

open import Types using (Ty)
open import Ctx using (Ctxᵗ; RVar; _∋tv_; _∋ᵗ_:=_)
open import Terms using (Term)
open import ImprecisionWorld
  using (World; WfWorld; Joins; Slot; _⊑ᵂ⟨_⟩[_]_; _+κ_)
open import TermImprecision using (_∣_⊢_⊑_∶⟨_,_⟩[_]_)

-- β is bound to a right type variable joined to a left one
BoundJoined : ∀ {Δ Δ′ : Ctxᵗ} → World Δ Δ′ → RVar → Set
BoundJoined {Δ} {Δ′} W β =
  Σ[ X ∈ ℕ ] Σ[ X′ ∈ ℕ ] (Δ ∋tv X) × (Δ′ ∋ᵗ X′ := β) × Joins W X X′

KappaWeaken : Set
KappaWeaken = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {K : List RVar}
    {M M′ : Term} {A A′ : Ty} {O : List Slot} {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → WfWorld W
  → WfWorld (W +κ K)
  → All (BoundJoined W) K
  → W ∣ [] ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p
  → Σ[ p′ ∈ A ⊑ᵂ⟨ W +κ K ⟩[ O ] A′ ]
      (W +κ K ∣ [] ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p′)

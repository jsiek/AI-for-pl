module strong.proof.IdLayer where

-- THE ID-LAYER FACTS — what makes IdPush and CancelR legitimate.
--
-- §1  the pushed name is ALREADY WRITTEN in the id-face (idpush-name), and
--     the same argument fixes CancelR's two names (cancel-name): typing
--     forces X ≡ nbind Θ₁ + Y in both cases, so neither rule moves an index
--     or invents a slot, and neither needs an equation as a premise.
-- §2  `unseal` is the ONLY active face an id-(` X) layer can ever meet, so
--     the id-base branch of `Active` is vacuous for these rules.
-- §3  the naked drop `V ⟪ Θ , id A ⟫ -→ V` — the door, closed: it is sound
--     exactly when the boundary changes NO FRAME.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

------------------------------------------------------------------------
-- §1  THE NAMES ARE FORCED
------------------------------------------------------------------------

-- In any typed id-layer under an `unseal`, the id-face's variable IS the
-- pushed conversion's name.  IdPush therefore moves no index.
idpush-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → X ≡ nbind Θ₁ + Y
idpush-name {Θ₁ = Θ₁} (env _ (env _ _ ⊢cᵢ _) ⊢cₒ _)
  with conv-unseal-src ⊢cₒ
... | refl = tvar-inj (trans (sym (conv-idv-tgt ⊢cᵢ))
                            (liftN-var (nbind Θ₁) _))

-- THE SAME FACT FOR CANCEL.  The mini-core's Cancel wrote one name on both
-- faces, which presumes nbind Θ₁ ≡ 0.  strong.Reduction's CancelR carries two
-- names; this lemma is why no premise has to relate them.
cancel-name : ∀ {Δ Γ V Θ₁ Θ₂ X Y C}
  → Δ ∣ Γ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → X ≡ nbind Θ₁ + Y
cancel-name {Θ₁ = Θ₁} (env _ (env _ _ ⊢cᵢ _) ⊢cₒ _)
  with conv-unseal-src ⊢cₒ
... | refl = tvar-inj (trans (sym (conv-seal-tgt ⊢cᵢ))
                            (liftN-var (nbind Θ₁) _))

------------------------------------------------------------------------
-- §2  THE ONLY ACTIVE FACE AN ID-LAYER MEETS IS `unseal`
------------------------------------------------------------------------

-- An `id (` X)`-faced wrapper has a VARIABLE exterior type, and an outer
-- `id A` face at a BASE type demands a base interior.  So the id-base
-- branch of `Active` is unreachable over this LHS.
outer-id-base-untypeable : ∀ {Δ Γ V Θ₁ Θ₂ X A C} → Base A
  → ¬ (Δ ∣ Γ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , id A ⟫ ⦂ C)
outer-id-base-untypeable {Θ₁ = Θ₁} bA (env _ (env _ _ ⊢cᵢ _) ⊢cₒ _)
  with conv-id-base-src bA ⊢cₒ
... | refl = base≢var (nbind Θ₁) bA (conv-idv-tgt ⊢cᵢ)

-- The mask jam is a phantom, twice over.  (1) A conceal is INVISIBLE to the
-- face type context: `fscp` skips `lock`, so a face never lands on a slot the layer
-- masks.
fceC-lock : ∀ {X} (Θ : CtxMorph) (Δ : Ctxᵗ) → fceC (lock X ∷ Θ) Δ ≡ fceC Θ Δ
fceC-lock Θ Δ = refl

-- (2) And a boundary can never conceal the slot its OWN face names —
-- `value-var-visible` (strong.Terms) says a value's variable type is
-- visible on the value's bind type context, because `env`'s last conjunct checks it
-- there.  So "Θ₁ contains `lock Y` while the face cites Y" is untypeable.

------------------------------------------------------------------------
-- §3  THE NAKED DROP — the door, closed
------------------------------------------------------------------------

-- `V ⟪ Θ , id A ⟫ -→ V` is unsound because V is typed on `intC Θ Δ`, not on
-- Δ.  A concrete failing instance: the boundary binds an owner, and V's
-- licence cites a slot Δ does not even have.

Δₑ : Ctxᵗ
Δₑ = bind `ℕ ∷ []

Δₑ-no-1 : ∀ {E} → Δₑ ∋e 1 , E → ⊥
Δₑ-no-1 (es ())

naked-drop-trap : ∀ {C} → ¬ (Δₑ ∣ [] ⊢ ($ 7) ⟪ [] , seal 1 ⟫ ⦂ C)
naked-drop-trap (env _ _ (conv-seal d) _) = Δₑ-no-1 d

-- THE SOUND SIDE CONDITION: the drop is sound exactly when the boundary
-- changes NO FRAME.  Then `intC [] Δ ≡ Δ` and the identity face fixes the
-- type, so the interior derivation is already the exterior one.
drop-empty-frame : ∀ {Δ Γ V A B} → Δ ∣ Γ ⊢ V ⟪ [] , id A ⟫ ⦂ B
                 → Δ ∣ [] ⊢ V ⦂ B
drop-empty-frame {Δ = Δ} {V = V} (env _ ⊢V ⊢c _) =
  subst (λ T → Δ ∣ [] ⊢ V ⦂ T) (conv-id-refl ⊢c) ⊢V

module strong.proof.CancelFaces where

-- CANCELR'S PRESERVATION CASE, over ONE interface.
--
-- THE RULE (strong.Reduction, repair 3a as re-ruled):
--
--   (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
--     -→ (V ⟪ Θ₁ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ Θ₂ , idc A ⟫
--
-- Both FRAMES stay, both FACES are neutralised: composition happens only
-- on the faces, where `unseal ∘ seal = id` is the algebra the design
-- already trusts.  So `V` retypes exactly where it was typed — which is
-- what the dropped-frame form (`reps→bind (reps Θ₂)`) could not do.
--
-- WHAT HAS TO BE PROVEN, and it is one equation.  The contractum's INNER
-- face is `idc (liftN (nbind Θ₁) A)`, so `V`'s interior type must BE
-- `liftN (nbind Θ₁) A`.  It is:
--
--   * `seal X`'s source IS X's rep, read on `fceC Θ₁ (intC Θ₂ Δ)`
--     (`seal-face-is-the-owners-rep`);
--   * the two names are forced equal by the typing, `X ≡ nbind Θ₁ + Y`
--     (the inner face's exterior is `liftN (nbind Θ₁) (` Y)`);
--   * Y's rep is A, first moved INSIDE Θ₂ (`mask-only`: `intC` and `fceC`
--     differ only by masking), then along Θ₁'s unmasks (`fscp-∋bind`) and
--     past Θ₁'s own owners (`prep-∋`), which lifts it to
--     `liftN (nbind Θ₁) A` at slot `nbind Θ₁ + Y`;
--   * `∋:=-det` closes it.
--
-- This is `proof/Adversary.cancel-faces-agree` — "the inner conceal's
-- interior face and the outer reveal's exterior face are the SAME lookup"
-- — with the two lookups no longer on the same type context, so the
-- transport chain above replaces the single `∋:=-det`.
--
-- THE ONE INTERFACE: `ScopedAtUnseal` (proof/ScopedAtUnsealDef).  Both
-- new wrappers PRESENT the rep `A` inside `Θ₂`'s interior, so `env`'s last
-- premise asks for `intC Θ₂ Δ ⊢ᵗ A` — the common wall.  Nothing else is
-- assumed: `MaskOnly` is now a theorem (proof/MaskFacts.mask-only).

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction using (unsealAt)
open import strong.proof.Preserve using (CancelRCase)
open import strong.proof.MaskFacts using (mask-only)
open import strong.proof.IdPushReach using (fscp-∋bind; prep-∋)
open import strong.proof.ScopedAtUnsealDef using (ScopedAtUnseal)

------------------------------------------------------------------------
-- §1  A rep survives Θ's unmasks
------------------------------------------------------------------------

-- `fscp` only UNMASKS (it skips the binds and the locks), and unmasking
-- adds nameability, so a type well formed outside is well formed on the
-- face type context.  (`scp` would not do: masking is exactly what the
-- wall is about.)
wf-fscp : ∀ {Δ A} (Θ : CtxMorph) → Δ ⊢ᵗ A → fscp Θ Δ ⊢ᵗ A
wf-fscp []             w = w
wf-fscp (bind B ∷ Θ)   w = wf-fscp Θ w
wf-fscp (lock X ∷ Θ)   w = wf-fscp Θ w
wf-fscp (unlock X ∷ Θ) w = ⊑-wf (unmask-⊑ X _) (wf-fscp Θ w)

wf-fceC : ∀ {Δ A} (Θ : CtxMorph)
  → Δ ⊢ᵗ A → fceC Θ Δ ⊢ᵗ liftN (nbind Θ) A
wf-fceC Θ w = wf-liftN-prep (reps Θ) (wf-fscp Θ w)

------------------------------------------------------------------------
-- §2  The case
------------------------------------------------------------------------

preserve-CancelR : ScopedAtUnseal → CancelRCase
preserve-CancelR sc {Δ = Δ} {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                    {A = A} {C = C} v d ⊢R with ⊢R
... | env bw₂ (env bw₁ ⊢V ⊢c₁ wE′) (conv-unseal dₒ) wE =
  env {p = ↑ˢ} bw₂
      (env {p = ↑ˢ} bw₁ ⊢V′ faceᵢ scoped)
      faceₒ
      wE
  where
  -- THE INTERFACE, at the redex.
  scoped : intC Θ₂ Δ ⊢ᵗ A
  scoped = sc ⊢R d

  -- The outer reveal's rep IS A.
  eqAC : A ≡ liftN (nbind Θ₂) C
  eqAC = ∋:=-det d dₒ

  -- Y is an owner INSIDE Θ₂ too: it is visible there (the inner
  -- wrapper's exterior type is `` ` Y ``) and an owner outside.
  owner : intC Θ₂ Δ ∋ Y := A
  owner = mask-only Θ₂ Δ (wf-var⁻ wE′) d

  -- The two names, forced equal by the inner face's exterior.
  eqX : nbind Θ₁ + Y ≡ X
  eqX = tvar-inj (trans (sym (liftN-var (nbind Θ₁) Y)) (conv-seal-tgt ⊢c₁))

  -- … so X is an owner on Θ₁'s face type context, at A lifted past Θ₁'s
  -- own owners.
  dX : fceC Θ₁ (intC Θ₂ Δ) ∋ X := liftN (nbind Θ₁) A
  dX = subst (λ Z → fceC Θ₁ (intC Θ₂ Δ) ∋ Z := liftN (nbind Θ₁) A) eqX
             (prep-∋ (reps Θ₁) (fscp-∋bind Θ₁ owner))

  -- THE FACE EQUATION: V's interior type is exactly the new inner face.
  eqV : _ ≡ liftN (nbind Θ₁) A
  eqV = ∋:=-det (seal-face-is-the-owners-rep ⊢c₁) dX

  ⊢V′ : intC Θ₁ (intC Θ₂ Δ) ∣ [] ⊢ V ⦂ liftN (nbind Θ₁) A
  ⊢V′ = subst (λ T → intC Θ₁ (intC Θ₂ Δ) ∣ [] ⊢ V ⦂ T) eqV ⊢V

  faceᵢ : fceC Θ₁ (intC Θ₂ Δ) ⊢ idc (liftN (nbind Θ₁) A)
            ∶ liftN (nbind Θ₁) A ⇝ liftN (nbind Θ₁) A ∙ ↑ˢ
  faceᵢ = idc-⊢ (wf-fceC Θ₁ scoped)

  faceₒ : fceC Θ₂ Δ ⊢ idc A ∶ A ⇝ liftN (nbind Θ₂) C ∙ ↑ˢ
  faceₒ = subst (λ T → fceC Θ₂ Δ ⊢ idc A ∶ A ⇝ T ∙ ↑ˢ) eqAC
                (idc-⊢ (⊑-wf (intC⊑fceC Θ₂ Δ) scoped))

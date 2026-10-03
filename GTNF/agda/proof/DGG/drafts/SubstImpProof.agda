open import proof.DGG.drafts.AllocImpDef using (AllocImp)
open import proof.DGG.ImprecisionTypingDef using (ImprecisionTyping)

module proof.DGG.drafts.SubstImpProof
  (alloc-imp : AllocImp) (imprecision-typing : ImprecisionTyping) where

-- File Charter:
--   * DRAFT SKELETON (2026-10-03) of `SubstImp` (drafts/SubstImpDef),
--     by induction on the `⊑` derivation, and the consumer form
--     `SubstImpBeta` from it (complete).
--   * Module parameters: `AllocImp` (a value image crossing `Λ` is
--     `crossΛᴹ V A = renᴹᴿ suc V ⟪ unbind 0 0 ∷ [] , … ⟫`, related by
--     `⟪⟫⊑⟪⟫`/`⟪⟫⊑` over AllocImp at ρ = suc), `ImprecisionTyping`
--     (the right typing that `blame⊑` carries, after substitution).
--   * IH FIT.  `ƛ⊑ƛ` (with `ext-env`, complete), the casts, `ν⊑ν`, `ν⊑`,
--     `Λ⊑Λ`, `Λ⊑` call the IH on their premise; boundaries and
--     `∀⊑⟪+⟫` need none (`substᵐ` stops at a boundary; the ∀-value of
--     `∀⊑⟪+⟫` is closed).  Glue that is not the IH:
--     - `·⊑·`: reindexing, as in AllocImp (`⊑-unique`);
--     - `x⊑x` at a value image: weakening a `[]`-derivation to γ₁;
--     - `⟪⟫⊑`, `⊑⟪⟫`, `∀⊑⟪+⟫`: the other side's term is related at
--       `[]`, hence closed, and `substᵐ` fixes it (needs a
--       closed-term lemma through `imprecision-typing`).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Types using (Ty)
open import Ctx using (Ctxᵗ)
open import Terms
open import TermSubst
open import Imprecision using (VarImp; X⊑X; ⇒⊑⇒)
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.drafts.SubstImpDef

private
  variable
    Δ Δ′ : Ctxᵗ

Env : ∀ {W : World Δ Δ′} → CtxImp W → CtxImp W → (Var → Img)
  → (Var → Img) → Set
Env γ γ₁ σ σ′ = ∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp γ₁ (σ x) (σ′ x) e

------------------------------------------------------------------------
-- Glue
------------------------------------------------------------------------

-- under ƛ⊑ƛ (complete)
ext-env : ∀ {W : World Δ Δ′} {γ γ₁ : CtxImp W} {σ σ′} {e₀}
  → Env γ γ₁ σ σ′ → Env (e₀ ∷ γ) (e₀ ∷ γ₁) (extᴵ σ) (extᴵ σ′)
ext-env {e₀ = ctx-imp A A′ p} env Zʷ = ivar⊑ivar {q = p} Zʷ
ext-env {σ = σ} {σ′} env (Sʷ {x = x} x∈)
  with σ x | σ′ x | env x∈
ext-env {σ = σ} {σ′} env (Sʷ {x = x} x∈)
  | .(ivar _) | .(ivar _) | ivar⊑ivar y∈ = ivar⊑ivar (Sʷ y∈)
ext-env {σ = σ} {σ′} env (Sʷ {x = x} x∈)
  | .(ival _ _) | .(ival _ _) | ival⊑ival vV vV′ V⊑ = ival⊑ival vV vV′ V⊑

-- under Λ⊑Λ: the lifted target context, and the images crossing Λ
-- (a value image becomes crossΛᴹ, related through AllocImp at suc)
lift-env : ∀ {W : World Δ Δ′} {γ γ₁ : CtxImp W} {γ′ : CtxImp (W ⊕ X⊑X)}
    {σ σ′}
  → LiftCtx X⊑X γ γ′ → Env γ γ₁ σ σ′
  → Σ[ γ₁′ ∈ CtxImp (W ⊕ X⊑X) ]
      (LiftCtx X⊑X γ₁ γ₁′
      × Env γ′ γ₁′ (λ x → ⇑ᴵ (σ x)) (λ x → ⇑ᴵ (σ′ x)))
lift-env l env = {!!}

-- under Λ⊑: only the left images cross the binder
liftᴸ-env : ∀ {W : World Δ Δ′} {γ γ₁ : CtxImp W} {γ′ : CtxImp (W ⊕ᴸ)}
    {σ σ′}
  → LiftCtxᴸ γ γ′ → Env γ γ₁ σ σ′
  → Σ[ γ₁′ ∈ CtxImp (W ⊕ᴸ) ]
      (LiftCtxᴸ γ₁ γ₁′ × Env γ′ γ₁′ (λ x → ⇑ᴵ (σ x)) σ′)
liftᴸ-env l env = {!!}

-- a value stays a value (a variable is never in value position)
value-subst : ∀ {V σ} → Value V → Value (substᵐ σ V)
value-subst v = {!!}

------------------------------------------------------------------------
-- The skeleton
------------------------------------------------------------------------

subst-imp : SubstImp
subst-imp {σ = σ} {σ′} env (x⊑x {x = x} x∈) with σ x | σ′ x | env x∈
subst-imp {σ = σ} {σ′} env (x⊑x {x = x} x∈)
  | .(ivar _) | .(ivar _) | ivar⊑ivar {q = q} y∈ = q , x⊑x y∈
subst-imp {σ = σ} {σ′} env (x⊑x {x = x} x∈)
  | .(ival _ _) | .(ival _ _) | ival⊑ival {q = q} vV vV′ V⊑ =
  q , {!weaken V⊑ from [] to γ₁ (closed terms)!}
subst-imp env (κ⊑κ lit-$ p) = p , κ⊑κ lit-$ p
subst-imp env (κ⊑κ lit-true p) = p , κ⊑κ lit-true p
subst-imp env (κ⊑κ lit-false p) = p , κ⊑κ lit-false p
subst-imp env (ƛ⊑ƛ {pA = pA} wA wA′ N⊑)
  with subst-imp (ext-env env) N⊑
subst-imp env (ƛ⊑ƛ {pA = pA} wA wA′ N⊑) | qB , N₁ =
  ⇒⊑⇒ pA qB , ƛ⊑ƛ wA wA′ N₁
subst-imp env (·⊑· {pB = pB} L⊑ M⊑)
  with subst-imp env L⊑ | subst-imp env M⊑
subst-imp env (·⊑· {pB = pB} L⊑ M⊑) | qL , L₁ | qM , M₁ =
  -- REINDEX: L₁ is at qL; ·⊑· wants ⇒⊑⇒ qM pB
  pB , ·⊑· {!L₁!} M₁
subst-imp env (blame⊑ wA ⊢M′ p) =
  p , blame⊑ wA {!typing substitution on the right (images typed by imprecision-typing)!} p
subst-imp env (cast⊑cast M⊑ ct ct′ q) with subst-imp env M⊑
subst-imp env (cast⊑cast M⊑ ct ct′ q) | r , M₁ = q , cast⊑cast M₁ ct ct′ q
subst-imp env (cast⊑ M⊑ ct q) with subst-imp env M⊑
subst-imp env (cast⊑ M⊑ ct q) | r , M₁ = q , cast⊑ M₁ ct q
subst-imp env (⊑cast M⊑ ct′ q) with subst-imp env M⊑
subst-imp env (⊑cast M⊑ ct′ q) | r , M₁ = q , ⊑cast M₁ ct′ q
subst-imp env (Λ⊑Λ l vV vV′ V⊑ q) with lift-env l env
subst-imp env (Λ⊑Λ l vV vV′ V⊑ q) | γ₁′ , l₁ , env′
  with subst-imp env′ V⊑
subst-imp env (Λ⊑Λ l vV vV′ V⊑ q) | γ₁′ , l₁ , env′ | r , V₁ =
  q , Λ⊑Λ l₁ (value-subst vV) (value-subst vV′) V₁ q
subst-imp env (Λ⊑ nv occ l vV V⊑ q) with liftᴸ-env l env
subst-imp env (Λ⊑ nv occ l vV V⊑ q) | γ₁′ , l₁ , env′
  with subst-imp env′ V⊑
subst-imp env (Λ⊑ nv occ l vV V⊑ q) | γ₁′ , l₁ , env′ | r , V₁ =
  q , Λ⊑ nv occ l₁ (value-subst vV) V₁ q
subst-imp env (∀⊑⟪+⟫ nv occ vV ⊢V i N⊑ β★ b q) =
  q , {!∀⊑⟪+⟫ nv occ vV ⊢V i N⊑ β★ b q, after substᵐ σ V ≡ V (V closed)!}
subst-imp env (ν⊑ν L⊑ a n n′ nc q) with subst-imp env L⊑
subst-imp env (ν⊑ν L⊑ a n n′ nc q) | r , L₁ = q , ν⊑ν L₁ a n n′ nc q
subst-imp env (ν⊑ L⊑ a n q) with subst-imp env L⊑
subst-imp env (ν⊑ L⊑ a n q) | r , L₁ = q , ν⊑ L₁ a n q
subst-imp env (⟪⟫⊑⟪⟫ int wi M⊑ b b′ bc q) =
  q , ⟪⟫⊑⟪⟫ int wi M⊑ b b′ bc q
-- the other side is closed (related at []), so substᵐ fixes it
subst-imp env (⟪⟫⊑ int wi M⊑ b q) =
  q , {!⟪⟫⊑ int wi M⊑ b q, after substᵐ σ′ M′ ≡ M′ (M′ closed)!}
subst-imp env (⊑⟪⟫ int wi M⊑ b′ q) =
  q , {!⊑⟪⟫ int wi M⊑ b′ q, after substᵐ σ M ≡ M (M closed)!}

------------------------------------------------------------------------
-- The consumer form (complete given subst-imp)
------------------------------------------------------------------------

subst-imp-beta : SubstImpBeta
subst-imp-beta {V = V} {V′} {A} {A′} N⊑ vV vV′ V⊑ =
  subst-imp env N⊑
  where
  env : ∀ {x e} → _ ∋ʷ x ⦂ e
    → ImgImp [] (betaEnv V A x) (betaEnv V′ A′ x) e
  env Zʷ = ival⊑ival vV vV′ V⊑
  env (Sʷ ())

open import proof.DGG.drafts.AllocImpDef using (AllocImpInterior)

module proof.DGG.drafts.AllocImpProof (alloc-interior : AllocImpInterior) where

-- File Charter:
--   * DRAFT SKELETON (2026-10-03) of `AllocImp` (drafts/AllocImpDef),
--     by induction on the `⊑` derivation: every rule, every IH call,
--     holes for the glue.  The test of the statement; findings in
--     drafts/STATEMENTS.md.
--   * Module parameter: the interior commutation `AllocImpInterior`
--     (its Def is in the same draft module).
--   * IH FIT.  Every IH call is on a premise of the rule at the world
--     the rule names, renamed by the same (ρ, ρ′) or by its `extᵗ`
--     under a binder.  Two kinds of glue do not come from the IH:
--     - `·⊑·`: the IH for `L` returns its own index, which must be
--       `⇒⊑⇒ qM qB` with qM the IH's index for `M` (reindexing; needs
--       `⊑-unique`, to be ported from GTSFImp/proof/Imprecision);
--     - the boundary rules: `WfWorld Wᵢ₁` of the renamed interior.
--       Derivable when W₁ adds no pair (the `ev-L`/`ev-R` instances);
--       FALSE when it does (`ev-2`, `ev-L⇔`): the new pair's payload
--       may have no reading through the interior's names, so `Agree`
--       fails (checked: drafts/EvolveImpWfInteriorCounterexample).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; Renameᵗ; extᵗ)
open import Ctx
open import Terms
open import TermSubst using (renᴹᴿ)
open import Boundary using (renᴮᴿ)
open import Reduction using (InstX)
open import Imprecision using (VarImp; X⊑X; ⇒⊑⇒)
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.drafts.AllocImpDef

private
  variable
    Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ
    ρ ρ′ : Renameᵗ

------------------------------------------------------------------------
-- Glue (statements only; bodies are holes)
------------------------------------------------------------------------

-- the type index moves with the world (renameᵗ-cong on the emb's)
⊑ᵂ-ren : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {A A′}
  → WorldRen ρ ρ′ W W₁ → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W₁ ⟩ A′
⊑ᵂ-ren wr p = {!!}

-- a lookup in γ has a lookup with the same types in γ₁
same-∋ : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁} {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → SameTys γ γ₁ → γ ∋ʷ x ⦂ ctx-imp A A′ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (γ₁ ∋ʷ x ⦂ ctx-imp A A′ q)
same-∋ (same-∷ s) Zʷ = _ , Zʷ
same-∋ (same-∷ s) (Sʷ x∈) with same-∋ s x∈
same-∋ (same-∷ s) (Sʷ x∈) | q , x∈₁ = q , Sʷ x∈₁

-- side premises under the renaming (⊢renᴿ, coercion-renᴿ, …)
⊢ᵗ-ren : ∀ {A} → CtxRen ρ Δ Δ₁ → Δ ⊢ᵗ A → Δ₁ ⊢ᵗ A
⊢ᵗ-ren cr wA = {!!}

castTy-ren : ∀ {μ c B A} → CtxRen ρ Δ Δ₁ → CastTy Δ μ c B A
  → CastTy Δ₁ μ c B A
castTy-ren cr ct = {!!}

nuTy-ren : ∀ {A C c B} → CtxRen ρ Δ Δ₁ → NuTy Δ A C c B
  → NuTy Δ₁ A C c B
nuTy-ren cr n = {!!}

value-ren : ∀ {V} → CtxRen ρ Δ Δ₁ → Value V → Value (renᴹᴿ ρ V)
value-ren cr v = {!!}

instX-ren : ∀ {V N} → InstX V N → InstX (renᴹᴿ ρ V) (renᴹᴿ (extᵗ ρ) N)
instX-ren i = {!!}

-- the world moves under each binder of a ⊑ rule
wr-⊕ : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {m}
  → WorldRen ρ ρ′ W W₁ → WorldRen (extᵗ ρ) (extᵗ ρ′) (W ⊕ m) (W₁ ⊕ m)
wr-⊕ wr = {!!}

wr-⊕ᴸ : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
  → WorldRen ρ ρ′ W W₁ → WorldRen (extᵗ ρ) ρ′ (W ⊕ᴸ) (W₁ ⊕ᴸ)
wr-⊕ᴸ wr = {!!}

wr-⊕⁺ : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {m β}
  → WorldRen ρ ρ′ W W₁
  → WorldRen (extᵗ ρ) ρ′ (W ⊕⁺ m ^ β) (W₁ ⊕⁺ m ^ ρ′ β)
wr-⊕⁺ wr = {!!}

lift-same : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {m}
    {γ : CtxImp W} {γ′ : CtxImp (W ⊕ m)} {γ₁ : CtxImp W₁}
  → WorldRen ρ ρ′ W W₁ → LiftCtx m γ γ′ → SameTys γ γ₁
  → Σ[ γ₁′ ∈ CtxImp (W₁ ⊕ m) ] (LiftCtx m γ₁ γ₁′ × SameTys γ′ γ₁′)
lift-same wr l s = {!!}

liftᴸ-same : ∀ {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ′ : CtxImp (W ⊕ᴸ)} {γ₁ : CtxImp W₁}
  → WorldRen ρ ρ′ W W₁ → LiftCtxᴸ γ γ′ → SameTys γ γ₁
  → Σ[ γ₁′ ∈ CtxImp (W₁ ⊕ᴸ) ] (LiftCtxᴸ γ₁ γ₁′ × SameTys γ′ γ₁′)
liftᴸ-same wr l s = {!!}

------------------------------------------------------------------------
-- The skeleton
------------------------------------------------------------------------

alloc-imp : AllocImp
alloc-imp wr s (x⊑x x∈) with same-∋ s x∈
alloc-imp wr s (x⊑x x∈) | q , x∈₁ = q , x⊑x x∈₁
alloc-imp wr s (κ⊑κ lit-$ p) =
  ⊑ᵂ-ren wr p , κ⊑κ lit-$ (⊑ᵂ-ren wr p)
alloc-imp wr s (κ⊑κ lit-true p) =
  ⊑ᵂ-ren wr p , κ⊑κ lit-true (⊑ᵂ-ren wr p)
alloc-imp wr s (κ⊑κ lit-false p) =
  ⊑ᵂ-ren wr p , κ⊑κ lit-false (⊑ᵂ-ren wr p)
alloc-imp wr s (ƛ⊑ƛ {pA = pA} wA wA′ N⊑)
  with alloc-imp wr (same-∷ {p₁ = ⊑ᵂ-ren wr pA} s) N⊑
alloc-imp wr s (ƛ⊑ƛ {pA = pA} wA wA′ N⊑) | qB , N₁ =
  ⇒⊑⇒ (⊑ᵂ-ren wr pA) qB
  , ƛ⊑ƛ (⊢ᵗ-ren (wr-left wr) wA) (⊢ᵗ-ren (wr-right wr) wA′) N₁
alloc-imp wr s (·⊑· {pB = pB} L⊑ M⊑)
  with alloc-imp wr s L⊑ | alloc-imp wr s M⊑
alloc-imp wr s (·⊑· {pB = pB} L⊑ M⊑) | qL , L₁ | qM , M₁ =
  -- REINDEX: L₁ is at qL; ·⊑· wants ⇒⊑⇒ qM (⊑ᵂ-ren wr pB)
  ⊑ᵂ-ren wr pB , ·⊑· {!L₁!} M₁
alloc-imp wr s (blame⊑ wA ⊢M′ p) =
  ⊑ᵂ-ren wr p
  , blame⊑ (⊢ᵗ-ren (wr-left wr) wA) {!⊢renᴿ ⊢M′!} (⊑ᵂ-ren wr p)
alloc-imp wr s (cast⊑cast M⊑ ct ct′ q) with alloc-imp wr s M⊑
alloc-imp wr s (cast⊑cast M⊑ ct ct′ q) | r , M₁ =
  ⊑ᵂ-ren wr q
  , cast⊑cast M₁ (castTy-ren (wr-left wr) ct)
      (castTy-ren (wr-right wr) ct′) (⊑ᵂ-ren wr q)
alloc-imp wr s (cast⊑ M⊑ ct q) with alloc-imp wr s M⊑
alloc-imp wr s (cast⊑ M⊑ ct q) | r , M₁ =
  ⊑ᵂ-ren wr q , cast⊑ M₁ (castTy-ren (wr-left wr) ct) (⊑ᵂ-ren wr q)
alloc-imp wr s (⊑cast M⊑ ct′ q) with alloc-imp wr s M⊑
alloc-imp wr s (⊑cast M⊑ ct′ q) | r , M₁ =
  ⊑ᵂ-ren wr q , ⊑cast M₁ (castTy-ren (wr-right wr) ct′) (⊑ᵂ-ren wr q)
alloc-imp wr s (Λ⊑Λ l vV vV′ V⊑ q) with lift-same wr l s
alloc-imp wr s (Λ⊑Λ l vV vV′ V⊑ q) | γ₁′ , l₁ , s′
  with alloc-imp (wr-⊕ wr) s′ V⊑
alloc-imp wr s (Λ⊑Λ l vV vV′ V⊑ q) | γ₁′ , l₁ , s′ | r , V₁ =
  ⊑ᵂ-ren wr q
  , Λ⊑Λ l₁ (value-ren (wr-left (wr-⊕ {m = X⊑X} wr)) vV)
      (value-ren (wr-right (wr-⊕ {m = X⊑X} wr)) vV′) V₁ (⊑ᵂ-ren wr q)
alloc-imp wr s (Λ⊑ nv occ l vV V⊑ q) with liftᴸ-same wr l s
alloc-imp wr s (Λ⊑ nv occ l vV V⊑ q) | γ₁′ , l₁ , s′
  with alloc-imp (wr-⊕ᴸ wr) s′ V⊑
alloc-imp wr s (Λ⊑ nv occ l vV V⊑ q) | γ₁′ , l₁ , s′ | r , V₁ =
  ⊑ᵂ-ren wr q
  , Λ⊑ nv occ l₁ (value-ren (wr-left (wr-⊕ᴸ wr)) vV) V₁ (⊑ᵂ-ren wr q)
alloc-imp wr s (∀⊑⟪+⟫ nv occ vV ⊢V i N⊑ β★ b q)
  with alloc-imp (wr-⊕⁺ wr) same-[] N⊑
alloc-imp wr s (∀⊑⟪+⟫ nv occ vV ⊢V i N⊑ β★ b q) | r , N₁ =
  ⊑ᵂ-ren wr q
  , ∀⊑⟪+⟫ nv occ (value-ren (wr-left wr) vV) {!⊢renᴿ ⊢V!} (instX-ren i) N₁
      {!wk-bind of RepWk ρ′ on β★!} {!BdyTy under ρ′!} (⊑ᵂ-ren wr q)
alloc-imp wr s (ν⊑ν L⊑ a n n′ nc q) with alloc-imp wr s L⊑
alloc-imp wr s (ν⊑ν L⊑ a n n′ nc q) | r , L₁ =
  ⊑ᵂ-ren wr q
  , ν⊑ν L₁ (⊑ᵂ-ren wr a) (nuTy-ren (wr-left wr) n)
      (nuTy-ren (wr-right wr) n′) {!NuConversionImp under ρ, ρ′!}
      (⊑ᵂ-ren wr q)
alloc-imp wr s (ν⊑ L⊑ a n q) with alloc-imp wr s L⊑
alloc-imp wr s (ν⊑ L⊑ a n q) | r , L₁ =
  ⊑ᵂ-ren wr q
  , ν⊑ L₁ (⊑ᵂ-ren wr a) (nuTy-ren (wr-left wr) n) (⊑ᵂ-ren wr q)
alloc-imp wr s (⟪⟫⊑⟪⟫ int wi M⊑ b b′ bc q) with alloc-interior wr int
alloc-imp wr s (⟪⟫⊑⟪⟫ int wi M⊑ b b′ bc q) | Δᵢ₁ , Δ′ᵢ₁ , Wᵢ₁ , int₁ , wrᵢ
  with alloc-imp wrᵢ same-[] M⊑
alloc-imp wr s (⟪⟫⊑⟪⟫ int wi M⊑ b b′ bc q)
  | Δᵢ₁ , Δ′ᵢ₁ , Wᵢ₁ , int₁ , wrᵢ | r , M₁ =
  ⊑ᵂ-ren wr q
  , ⟪⟫⊑⟪⟫ int₁ {!MISFIT: WfWorld Wᵢ₁!} M₁ {!BdyTy under ρ!}
      {!BdyTy under ρ′!} {!BdyConversionImp under ρ, ρ′!} (⊑ᵂ-ren wr q)
alloc-imp wr s (⟪⟫⊑ int wi M⊑ b q) with alloc-interior wr int
alloc-imp wr s (⟪⟫⊑ int wi M⊑ b q) | Δᵢ₁ , Δ′ᵢ₁ , Wᵢ₁ , int₁ , wrᵢ
  with alloc-imp wrᵢ same-[] M⊑
alloc-imp wr s (⟪⟫⊑ int wi M⊑ b q) | Δᵢ₁ , Δ′ᵢ₁ , Wᵢ₁ , int₁ , wrᵢ
  | r , M₁ =
  ⊑ᵂ-ren wr q
  , ⟪⟫⊑ {!int₁ (Interior at renᴮᴿ ρ′ [] = [])!} {!MISFIT: WfWorld Wᵢ₁!}
      {!M₁!} {!BdyTy under ρ!} (⊑ᵂ-ren wr q)
alloc-imp wr s (⊑⟪⟫ int wi M⊑ b′ q) with alloc-interior wr int
alloc-imp wr s (⊑⟪⟫ int wi M⊑ b′ q) | Δᵢ₁ , Δ′ᵢ₁ , Wᵢ₁ , int₁ , wrᵢ
  with alloc-imp wrᵢ same-[] M⊑
alloc-imp wr s (⊑⟪⟫ int wi M⊑ b′ q) | Δᵢ₁ , Δ′ᵢ₁ , Wᵢ₁ , int₁ , wrᵢ
  | r , M₁ =
  ⊑ᵂ-ren wr q
  , ⊑⟪⟫ {!int₁ (Interior at renᴮᴿ ρ [] = [])!} {!MISFIT: WfWorld Wᵢ₁!}
      {!M₁!} {!BdyTy under ρ′!} (⊑ᵂ-ren wr q)

open import proof.DGG.drafts.AllocImpDef using (AllocImp)
open import proof.DGG.drafts.InstXImpDef using (InstXImpOpenR)

module proof.DGG.drafts.InstXImpProof
  (alloc-imp : AllocImp) (instx-open-r : InstXImpOpenR) where

-- File Charter:
--   * DRAFT SKELETONS (2026-10-03) of `InstXImp2` and `InstXImpL`
--     (drafts/InstXImpDef), by induction on the `⊑` derivation of the
--     ∀-value(s), with `InstX` inverted alongside.
--   * Module parameters: `AllocImp` (the `inst-gen` layer is
--     `crossΛᴹ W …`, `renᴹᴿ suc W` under `unbind 0 0`), and the
--     sibling `InstXImpOpenR` (the `Λ⊑` case of InstXImp2; it is not
--     an IH).
--   * IH FIT (details in STATEMENTS.md):
--     - fits: the `inst-∀` layers under `cast⊑cast`/`cast⊑`/`⊑cast`,
--       and the `inst-⟪⟫` layers under the three boundary rules (each
--       IH at the interior world, then `liftᴮ Θ`);
--     - InstXImp2: the IH's premise `C₀ ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C₀′` (binders
--       matched) is NOT AVAILABLE under a cast (coercions are not
--       compared) nor under a one-sided boundary;
--     - mixed layers (`inst-gen` against `inst-∀`, either way round,
--       and `∀⊑⟪+⟫` against `inst-⟪⟫`) need forms that are not the IH;
--     - InstXImpL: the `Λ⊑Λ` case has no rule to conclude with (there is
--       no ⊑Λ), and the `∀⊑⟪+⟫` case belongs to `ev-L⇔`, not to `ev-L`.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; `∀)
open import Ctx using (Ctxᵗ)
open import Conversion using (Conv; ⌞_⌟; `∀)
open import Boundary using (Boundary)
open import Coercion
open import Terms
open import Reduction using (InstX; inst-Λ; inst-gen; inst-∀; inst-⟪⟫)
open import Imprecision using (VarImp; X⊑X; X⊑★)
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.drafts.InstXImpDef

private
  variable
    Δ Δᵢ : Ctxᵗ

-- an interior under a ∀ conversion has a ∀ type (sameTy-target-∀⁻)
bdy-∀ : ∀ {Θ Aᵢ s A} → BdyTy Δ Θ Δᵢ Aᵢ ⌞ `∀ s ⌟ A
  → Σ[ C₀ ∈ Ty ] (Aᵢ ≡ `∀ C₀)
bdy-∀ b = {!!}

------------------------------------------------------------------------
-- InstXImp2: both sides instantiate
------------------------------------------------------------------------

instx-imp2 : InstXImp2
instx-imp2 pC vV vV′ iV iV′ (x⊑x ())
instx-imp2 pC vV vV′ iV iV′ (κ⊑κ () p)
instx-imp2 pC vV vV′ () iV′ (·⊑· L⊑ M⊑)
instx-imp2 pC vV vV′ () iV′ (blame⊑ wA ⊢M′ p)
-- cast ⊑ cast: four layer pairs
instx-imp2 pC vV vV′ (inst-∀ vW iW) (inst-∀ vW′ iW′)
    (cast⊑cast M⊑ (cast-ty (⊢all ⊢p) len) (cast-ty (⊢all ⊢p′) len′) q)
  with instx-imp2 {!NOT AVAILABLE: the inner bodies' C₀ ⊑ C₀′!}
         vW vW′ iW iW′ M⊑
instx-imp2 pC vV vV′ (inst-∀ vW iW) (inst-∀ vW′ iW′)
    (cast⊑cast M⊑ (cast-ty (⊢all ⊢p) len) (cast-ty (⊢all ⊢p′) len′) q)
  | m , r , N⊑ =
  m , {!q₀ (pC, mark-weakened to m)!}
  , cast⊑cast N⊑ {!CastTy (X∼X ∷ μ) p!} {!CastTy (X∼X ∷ μ′) p′!}
      {!q₀!}
instx-imp2 pC vV vV′ (inst-gen vW) (inst-gen vW′) (cast⊑cast M⊑ ct ct′ q) =
  {!no IH: crossΛᴹ both sides (alloc-imp at suc, suc; ⟪⟫⊑⟪⟫ over unbind 0 0), then cast⊑cast under ★∼X!}
instx-imp2 pC vV vV′ (inst-gen vW) (inst-∀ vW′ iW′) (cast⊑cast M⊑ ct ct′ q) =
  {!MISSING FORM: the left crosses Λ (crossΛᴹ), the right instantiates!}
instx-imp2 pC vV vV′ (inst-∀ vW iW) (inst-gen vW′) (cast⊑cast M⊑ ct ct′ q) =
  {!MISSING FORM: the left instantiates, the right crosses Λ!}
-- a left cast alone
instx-imp2 pC vV vV′ (inst-∀ vW iW) iV′
    (cast⊑ M⊑ (cast-ty (⊢all ⊢p) len) q)
  with instx-imp2 {!NOT AVAILABLE: C₀ ⊑ C′!} vW vV′ iW iV′ M⊑
instx-imp2 pC vV vV′ (inst-∀ vW iW) iV′
    (cast⊑ M⊑ (cast-ty (⊢all ⊢p) len) q) | m , r , N⊑ =
  m , {!q₀!} , cast⊑ N⊑ {!CastTy (X∼X ∷ μ) p!} {!q₀!}
instx-imp2 pC vV vV′ (inst-gen vW) iV′ (cast⊑ M⊑ ct q) =
  {!MISSING FORM: the left crosses Λ (crossΛᴹ), the right instantiates!}
-- a right cast alone
instx-imp2 pC vV vV′ iV (inst-∀ vW′ iW′)
    (⊑cast M⊑ (cast-ty (⊢all ⊢p′) len′) q)
  with instx-imp2 {!NOT AVAILABLE: C ⊑ C₀′!} vV vW′ iV iW′ M⊑
instx-imp2 pC vV vV′ iV (inst-∀ vW′ iW′)
    (⊑cast M⊑ (cast-ty (⊢all ⊢p′) len′) q) | m , r , N⊑ =
  m , {!q₀!} , ⊑cast N⊑ {!CastTy (X∼X ∷ μ′) p′!} {!q₀!}
instx-imp2 pC vV vV′ iV (inst-gen vW′) (⊑cast M⊑ ct′ q) =
  {!MISSING FORM: the left instantiates, the right crosses Λ!}
-- type abstraction
instx-imp2 pC vV vV′ (inst-Λ vN) (inst-Λ vN′)
    (Λ⊑Λ {r = r} lift-[] vN₁ vN₁′ V⊑ q) =
  X⊑X , r , V⊑
instx-imp2 pC vV vV′ (inst-Λ vN) iV′ (Λ⊑ nv occ liftᴸ-[] vN₁ V⊑ q)
  with instx-open-r vV′ iV′ V⊑
instx-imp2 pC vV vV′ (inst-Λ vN) iV′ (Λ⊑ nv occ liftᴸ-[] vN₁ V⊑ q)
  | q′ , N⊑ = X⊑★ , q′ , N⊑
instx-imp2 pC vV vV′ iV (inst-⟪⟫ uV′ iV′) (∀⊑⟪+⟫ nv occ vV₁ ⊢V iN N⊑ β★ b q) =
  {!MISSING FORM: the left opened at W ⊕⁺ m ^ β, the right instantiates under its boundary!}
instx-imp2 pC vV vV′ () iV′ (ν⊑ν L⊑ a n n′ nc q)
instx-imp2 pC vV vV′ () iV′ (ν⊑ L⊑ a n q)
-- boundaries: the IH at the interior world, then liftᴮ Θ
instx-imp2 pC vV vV′ (inst-⟪⟫ uU iU) (inst-⟪⟫ uU′ iU′)
    (⟪⟫⊑⟪⟫ int wi U⊑ b b′ bc q)
  with bdy-∀ b | bdy-∀ b′
instx-imp2 pC vV vV′ (inst-⟪⟫ uU iU) (inst-⟪⟫ uU′ iU′)
    (⟪⟫⊑⟪⟫ int wi U⊑ b b′ bc q) | C₀ , refl | C₀′ , refl
  with instx-imp2 {!C₀ ⊑ C₀′ from bc (conv-∀⊑∀) and conversion typing!}
         (V-simple uU) (V-simple uU′) iU iU′ U⊑
instx-imp2 pC vV vV′ (inst-⟪⟫ uU iU) (inst-⟪⟫ uU′ iU′)
    (⟪⟫⊑⟪⟫ int wi U⊑ b b′ bc q) | C₀ , refl | C₀′ , refl | m , r , N⊑ =
  m , {!q₀!}
  , ⟪⟫⊑⟪⟫ {!Interior (W ⊕ m) (liftᴮ Θ) (liftᴮ Θ′) (Wᵢ ⊕ m)!}
      {!WfWorld (Wᵢ ⊕ m) from wi!} N⊑ {!BdyTy!} {!BdyTy!}
      {!BdyConversionImp: s ⊑ s′ (conv-∀⊑∀; mark-weakened to m)!} {!q₀!}
instx-imp2 pC vV vV′ (inst-⟪⟫ uU iU) iV′ (⟪⟫⊑ int wi U⊑ b q)
  with bdy-∀ b
instx-imp2 pC vV vV′ (inst-⟪⟫ uU iU) iV′ (⟪⟫⊑ int wi U⊑ b q)
  | C₀ , refl
  with instx-imp2 {!NOT AVAILABLE: C₀ ⊑ C′ across a one-sided boundary!}
         (V-simple uU) vV′ iU iV′ U⊑
instx-imp2 pC vV vV′ (inst-⟪⟫ uU iU) iV′ (⟪⟫⊑ int wi U⊑ b q)
  | C₀ , refl | m , r , N⊑ =
  m , {!q₀!}
  , ⟪⟫⊑ {!Interior (W ⊕ m) (liftᴮ Θ) [] (Wᵢ ⊕ m)!}
      {!WfWorld (Wᵢ ⊕ m) from wi!} N⊑ {!BdyTy!} {!q₀!}
instx-imp2 pC vV vV′ iV (inst-⟪⟫ uU′ iU′) (⊑⟪⟫ int wi U⊑ b′ q)
  with bdy-∀ b′
instx-imp2 pC vV vV′ iV (inst-⟪⟫ uU′ iU′) (⊑⟪⟫ int wi U⊑ b′ q)
  | C₀′ , refl
  with instx-imp2 {!NOT AVAILABLE: C ⊑ C₀′ across a one-sided boundary!}
         vV (V-simple uU′) iV iU′ U⊑
instx-imp2 pC vV vV′ iV (inst-⟪⟫ uU′ iU′) (⊑⟪⟫ int wi U⊑ b′ q)
  | C₀′ , refl | m , r , N⊑ =
  m , {!q₀!}
  , ⊑⟪⟫ {!Interior (W ⊕ m) [] (liftᴮ Θ′) (Wᵢ ⊕ m)!}
      {!WfWorld (Wᵢ ⊕ m) from wi!} N⊑ {!BdyTy!} {!q₀!}

------------------------------------------------------------------------
-- InstXImpL: the left alone instantiates
------------------------------------------------------------------------

instx-impL : InstXImpL
instx-impL vV iV (x⊑x ())
instx-impL vV iV (κ⊑κ () p)
instx-impL vV () (·⊑· L⊑ M⊑)
instx-impL vV () (blame⊑ wA ⊢M′ p)
instx-impL vV (inst-∀ vW iW)
    (cast⊑cast M⊑ (cast-ty (⊢all ⊢p) len) ct′ q)
  with instx-impL vW iW M⊑
instx-impL vV (inst-∀ vW iW)
    (cast⊑cast M⊑ (cast-ty (⊢all ⊢p) len) ct′ q) | r , N⊑ =
  {!q₀!} , cast⊑cast N⊑ {!CastTy (X∼X ∷ μ) p!} ct′ {!q₀!}
instx-impL vV (inst-gen vW) (cast⊑cast M⊑ ct ct′ q) =
  {!no IH: crossΛᴹ W ⊑ W′ at W ⊕ᴸ (alloc-imp at suc, id; ⟪⟫⊑ over unbind 0 0), then cast⊑cast!}
instx-impL vV (inst-∀ vW iW) (cast⊑ M⊑ (cast-ty (⊢all ⊢p) len) q)
  with instx-impL vW iW M⊑
instx-impL vV (inst-∀ vW iW) (cast⊑ M⊑ (cast-ty (⊢all ⊢p) len) q)
  | r , N⊑ = {!q₀!} , cast⊑ N⊑ {!CastTy (X∼X ∷ μ) p!} {!q₀!}
instx-impL vV (inst-gen vW) (cast⊑ M⊑ ct q) =
  {!no IH: crossΛᴹ W ⊑ M′ at W ⊕ᴸ, then cast⊑!}
instx-impL vV iV (⊑cast M⊑ ct′ q) with instx-impL vV iV M⊑
instx-impL vV iV (⊑cast M⊑ ct′ q) | r , N⊑ = {!q₀!} , ⊑cast N⊑ ct′ {!q₀!}
instx-impL vV (inst-Λ vN) (Λ⊑Λ lift-[] vN₁ vN₁′ V⊑ q) =
  {!MISFIT: N ⊑ Λ N′ at W ⊕ᴸ — no rule (there is no ⊑Λ)!}
instx-impL vV (inst-Λ vN) (Λ⊑ nv occ liftᴸ-[] vN₁ V⊑ q) = _ , V⊑
instx-impL vV iV (∀⊑⟪+⟫ nv occ vV₁ ⊢V iN N⊑ β★ b q) =
  {!MISFIT: this is the ev-L⇔ catch-up (N ⊑ V′ at W ⊕⁺ m ^ β is the premise); W ⊕ᴸ does not pair 0 with β!}
instx-impL vV () (ν⊑ν L⊑ a n n′ nc q)
instx-impL vV () (ν⊑ L⊑ a n q)
instx-impL vV (inst-⟪⟫ uU iU) (⟪⟫⊑⟪⟫ int wi U⊑ b b′ bc q)
  with bdy-∀ b
instx-impL vV (inst-⟪⟫ uU iU) (⟪⟫⊑⟪⟫ int wi U⊑ b b′ bc q) | C₀ , refl
  with instx-impL (V-simple uU) iU U⊑
instx-impL vV (inst-⟪⟫ uU iU) (⟪⟫⊑⟪⟫ int wi U⊑ b b′ bc q) | C₀ , refl
  | r , N⊑ =
  {!q₀!}
  , ⟪⟫⊑⟪⟫ {!Interior (W ⊕ᴸ) (liftᴮ Θ) Θ′ (Wᵢ ⊕ᴸ)!}
      {!WfWorld (Wᵢ ⊕ᴸ) from wi!} N⊑ {!BdyTy!} b′
      {!BdyConversionImp: s ⊑ c′ (conv-∀⊑; MISFIT if conv-∀⊑∀)!} {!q₀!}
instx-impL vV (inst-⟪⟫ uU iU) (⟪⟫⊑ int wi U⊑ b q) with bdy-∀ b
instx-impL vV (inst-⟪⟫ uU iU) (⟪⟫⊑ int wi U⊑ b q) | C₀ , refl
  with instx-impL (V-simple uU) iU U⊑
instx-impL vV (inst-⟪⟫ uU iU) (⟪⟫⊑ int wi U⊑ b q) | C₀ , refl
  | r , N⊑ =
  {!q₀!}
  , ⟪⟫⊑ {!Interior (W ⊕ᴸ) (liftᴮ Θ) [] (Wᵢ ⊕ᴸ)!}
      {!WfWorld (Wᵢ ⊕ᴸ) from wi!} N⊑ {!BdyTy!} {!q₀!}
instx-impL vV iV (⊑⟪⟫ int wi U⊑ b′ q) with instx-impL vV iV U⊑
instx-impL vV iV (⊑⟪⟫ int wi U⊑ b′ q) | r , N⊑ =
  {!q₀!}
  , ⊑⟪⟫ {!Interior (W ⊕ᴸ) [] Θ′ (Wᵢ ⊕ᴸ)!}
      {!WfWorld (Wᵢ ⊕ᴸ) from wi!} N⊑ b′ {!q₀!}

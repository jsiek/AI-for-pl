module proof.LR.Case6 where

-- File Charter:
--   * Case 6 of the cast lemma (left `∀ᶜ`, right `inst`, from `∀⊑∀` to
--     `∀⊑`), assembled from `proof.LR.CastLemma` (module `Case6`), the
--     cast substitution laws (`proof.LR.CastSubst`) and the identity-cast
--     lemma (`proof.LR.IdentityCast`).  It is a separate file because
--     `IdentityCast` imports `CastLemma`.
--   * At each replay (`Replay`), the obligations `AtReplay.Ob`
--     (`Assemble.ob`):
--       - the casts read through the extended interpretation (`hyp₂`):
--         the environments `CastL.envL`, `CastR.envR`; the leaves good;
--         the closure of the old leaves (`FreshP`, `FreshO`, `FreshR`)
--         moved along the composite extension from the cast's world
--         (`E`), and of the new leaf from the oracle; `VarI` in every
--         future w‴ of a future w″ of the replay world (module `Var`):
--         at the old variables from `CastHyp.var` at `E`, through
--         agreeing environments (`CastL.envL-old`, `CastR.envR-old`,
--         `agree-ren`) and equivalent leaves; at the new variable from
--         `selfO-only` (`VarI-ext`);
--       - `preC₂`, `preA₂` (`PreB` moved, and opened at `★`);
--       - `castL₂`, `castR₂` (`CastL.castL`, `CastR.castR`);
--       - `typed` (`typedI`, as in preservation's `β-inst` case);
--       - `inner` (`innerFrom`): a bind around the right's reveal of α′,
--         from the hypothesis's clause at the replay world, at the goal's
--         descriptor sealed at α′ on the right (`clauseP`: the clause at
--         stage s + 1, brought down by `ℰ-down`), and the reveal
--         (`RevealK`); then the substitution instance at `pairStarˢ`
--         reading X paired at `★` as X left-only (`starOnly`, `subI`:
--         after the reveal X's leaf is already the goal's).
--   * `RevealK` (`revealK`): the right-only reveal of α′ as `★`, from
--     the clause's interpretation `δP` to `δQ`, is `revR` at p₁ in mode
--     `r-pair ↔-here 0`.  Its hypotheses (`RConvI-newR`) hold at the
--     extension `E₁ : wR ⊒ W₀`, where W₀ is w′'s scope over the cast's
--     store (α′ reserved; `replay-⊒`) and wR allocates α′ (ρS that of
--     `bind ★`, coherent by `grows-unique`): the old leaves closed from
--     `CastHyp.freshR`, the target leaf at `★` by `leafFreshR★`, and the
--     seal hypotheses from `SealNewR` (bounds s + 1) moved from the
--     unsealed clause leaf to the goal's leaf (`SealR-tgt`; `leafRev`,
--     `leafCon`: equal in `≺`, `𝒱≻★-G` at positive stages in `≻`,
--     `G 0 = ⊤` at the reveal's stage 0).
--   * `case6R`: the case, from the induction hypothesis at `c₁` against
--     `c₁′ [ ★/0 ]ᶜ`.  The induction that will supply it (on the sum of
--     the casts' sizes) needs `castSize-case6` and `eager-close`
--     (`proof.LR.CastSubst`).

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _≤′_; ≤′-refl)
open import Data.Nat.Properties using (≤-refl; n≤1+n; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  m≤n⇒m≤1+n; <⇒≤)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩; ⟨_,_,_⟩; _⊢_⦂_; ⊢•;
  renameᵗᵐ; ⇑ᵗᵐ; _⦂∀_[_])
open import Data.List using ([]; _∷_; map)
open import Reduction using (StoreChanges; bind; []; _∷_; applyBody)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import LR.Steps using (_—→^_[_]_; embedᶜˢ)
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
open import proof.TypeInTermSubst using (toRename-id-eq; toRename-wk-eq;
  typing-shiftᵗ-bind)
open import proof.TypeSafety.Preservation using (reveal-zero-typing;
  applyBody-open-zero)
open import proof.LR.WorldProps using (renameTy-id; ⊒-trans; ∘↪-idʳ;
  ⊒-refl; renameDesc-id; map-renameVar-id)
open import proof.LR.InterpProps using (_≈ˡ_; _≈ᴵ_; δl≡; δr≡; leaf≈;
  ≈ˡ-refl; ≈ˡ-sym; ≈ˡ-trans; ≈ᴵ-sym; ≈ᴵ-trans; ↑ᴵ-trans; ↑ᴵ-resp;
  transportLeaf-resp; leafRel-resp; extPairI-resp; exts-cong; ℰᵍ-≡;
  ℰᵍ-map; 𝒱≤-resp; 𝒱-resp; ℰ-resp; transportI-id)
open import proof.LR.Expression using (ℰ-bind₂; MFrame; mplug;
  renameMFrame)
open import proof.TermRename using (renameEnv∼-∘)
open import proof.LR.Monotone using (GoodI; GoodI-↑; GoodI-extOnlyI;
  GoodI-extPairI; onlyLeafS-good; leafBelowS-good; 𝒱≤-cast; peelSL-map)
open import proof.LR.SubstLemma using (SubI; sl≡; sr≡; sonly; spair;
  SubI-↑; 𝒱-subst; 𝒱-XY; 𝒱-X★; to; from; ℰᵍ-map⁺; leafBelow-⇔; leafG-⇔;
  𝒱≻★-G)
open import proof.LR.PrecisionSubst using (substᵖ)
open import LR.Frame using (reveal)
open import Conversion using (〖_,_↑_〗)
open import proof.LR.SubstLemma using (substᵗ-∘)
open import proof.LR.ConvLemma using (FreshP; FreshO; both; PreB; pre≡;
  PreB-↑; _↑ˢ_; ∀-inj; ℰL-resp; FreshP-↑; FreshO-↑; embed-bind; pre-typed;
  PreB-body; annot; ιT; PreS; PreS-↑; _,ᵖ_; PreB-ext; open0; pk-〖〗; pk-ren↑;
  new-bind; bind-Σ)
open import proof.LR.ConvSyntax using (↑-pk)
open import proof.LR.ConvBase using (sealedR-map)
open import proof.LR.ConvRight using (FreshR; FreshR-↑; FreshIR; SealR;
  r-pair; rStage; rBelow; UpBR; RConvI; RConvI-↑; RConvI-newR; revR;
  rcRenR; module SealNewR)
open import proof.LR.ConvClose using (PreB-map; oracle-all; oracleR-all;
  leafFreshR★)
open import proof.LR.Replay using (replay-⊒; replayW; replayPre;
  grows-unique)
open import proof.LR.CastLemma
open import proof.LR.CastSubst using (module CastL; module CastR; Agree;
  agree-ren)
open import proof.LR.IdentityCast using (selfO-only; refl-rename)

------------------------------------------------------------------------
-- Closure of a leaf respects equivalent leaves
------------------------------------------------------------------------

FreshP-resp : ∀ {d rk w} {L L′ : Leaf (ΔL w) (ΔR w)} {T T′}
  → L ≈ˡ L′ → FreshP d rk w L T T′ → FreshP d rk w L′ T T′
FreshP-resp {d} l≈ f e′ rc ok nb nrc rs {k} =
  (λ vl vr r → ℰL-resp d k _ L≈
     (proj₁ g vl vr (leafRel-resp d k _ (≈ˡ-sym L≈) r))) ,
  (λ wl wr r → ℰL-resp d k _ L≈
     (proj₂ g wl wr (leafRel-resp d k _ (≈ˡ-sym L≈) r)))
  where
  L≈ = transportLeaf-resp (ρL e′) (ρR e′) l≈
  g = f e′ rc ok nb nrc rs {k}

FreshO-resp : ∀ {d w} {L L′ : Leaf (ΔL w) (ΔR w)} {T}
  → L ≈ˡ L′ → FreshO d w L T → FreshO d w L′ T
FreshO-resp {d} l≈ f e′ nb {k} =
  (λ vl vr r → ℰL-resp d k _ L≈
     (proj₁ g vl vr (leafRel-resp d k _ (≈ˡ-sym L≈) r))) ,
  (λ wl vr r → ℰL-resp d k _ L≈
     (proj₂ g wl vr (leafRel-resp d k _ (≈ˡ-sym L≈) r)))
  where
  L≈ = transportLeaf-resp (ρL e′) (ρR e′) l≈
  g = f e′ nb {k}

FreshR-resp : ∀ {d w} {L L′ : Leaf (ΔL w) (ΔR w)} {T′}
  → L ≈ˡ L′ → FreshR d w L T′ → FreshR d w L′ T′
FreshR-resp {d} l≈ f e′ nb bs {k} =
  (λ vl vr r → ℰL-resp d k _ L≈
     (proj₁ g vl vr (leafRel-resp d k _ (≈ˡ-sym L≈) r))) ,
  (λ vl wr r → ℰL-resp d k _ L≈
     (proj₂ g vl wr (leafRel-resp d k _ (≈ˡ-sym L≈) r)))
  where
  L≈ = transportLeaf-resp (ρL e′) (ρR e′) l≈
  g = f e′ nb bs {k}

------------------------------------------------------------------------
-- Store preimages, opened at `★`
------------------------------------------------------------------------

PreB-σ : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ σ′ : Δ′ ⇒ˢ storeR w} {B}
  → (∀ Y → σ Y ≡ σ′ Y) → PreB w ρ σ B → PreB w ρ σ′ B
pre≡ (PreB-σ {w = w} {B = B} eqs h) =
  trans (pre≡ h) (cong (renameᵗ (toRenameᵗ (ιʷ w))) (substᵗ-cong B eqs))

-- substitution commutes with the opening at `★`
open-subst : ∀ {Δ Θ} (σ : Δ ⇒ˢ Θ) (C : Ty (suc Δ))
  → substᵗ σ (C [ ★ ]ᵗ) ≡ (substᵗ (extsᵗ σ) C) [ ★ ]ᵗ
open-subst σ C =
  trans (substᵗ-∘ σ (singleSubᵗ ★) C)
    (trans (substᵗ-cong C pw) (sym (substᵗ-∘ (singleSubᵗ ★) (extsᵗ σ) C)))
  where
  pw : ∀ X → substᵗ σ (singleSubᵗ ★ X)
    ≡ substᵗ (singleSubᵗ ★) (extsᵗ σ X)
  pw zero = refl
  pw (suc X) = sym (shift-openᵗ (σ X) ★)

-- and so does renaming
ren-open : ∀ {Δ Θ} (ι : Δ ⇒ʳ Θ) (A : Ty (suc Δ))
  → (renameᵗ (extᵗ ι) A) [ ★ ]ᵗ ≡ renameᵗ ι (A [ ★ ]ᵗ)
ren-open ι A =
  trans (substᵗ-rename (singleSubᵗ ★) (extᵗ ι) A)
    (trans (substᵗ-cong A pw) (sym (renameᵗ-subst ι (singleSubᵗ ★) A)))
  where
  pw : ∀ X → singleSubᵗ ★ (extᵗ ι X) ≡ renameᵗ ι (singleSubᵗ ★ X)
  pw zero = refl
  pw (suc X) = refl

PreB-open : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ : Δ′ ⇒ˢ storeR w}
    {C : Ty (suc Δ′)}
  → PreB w ρ σ (`∀ C) → PreB w ρ σ (C [ ★ ]ᵗ)
pre≡ (PreB-open {w = w} {ρ} {σ} {C} h) =
  trans (open-subst ρ C)
    (trans (cong (_[ ★ ]ᵗ) (∀-inj (pre≡ h)))
      (trans (ren-open (toRenameᵗ (ιʷ w)) (substᵗ (extsᵗ σ) C))
        (cong (renameᵗ (toRenameᵗ (ιʷ w))) (sym (open-subst σ C)))))

retype : ∀ {Γ M A B} → A ≡ B → Γ ⊢ M ⦂ A → Γ ⊢ M ⦂ B
retype refl t = t

------------------------------------------------------------------------
-- The reveal's target leaf: the goal's left-only leaf against the
-- unsealed clause leaf (`𝒱≻★-G` at positive stages)
------------------------------------------------------------------------

≈ˡ-≡ : ∀ {ΘL ΘR} {l l′ : Leaf ΘL ΘR} → l ≡ l′ → l ≈ˡ l′
≈ˡ-≡ refl = ≈ˡ-refl

coreStar : ∀ {ΘL ΘR} (c : Desc ΘL ΘR) → CoreStar c → rightTy c ≡ ★
coreStar (desc p env envR) refl = refl

upRefl : ∀ d n → UpBR d n n
upRefl ≺ n = ≤-refl
upRefl ≻ n = tt

-- the clause leaf without its right seal, read at the goal's leaf, at
-- the stages of a reveal's contents
leafRev : ∀ d {ΘL ΘR s} (c : SDesc ΘL ΘR) → OnlyS c → ∀ {k} → 0 < k
  → k ≤ suc s → ∀ w τL τR {V V′}
  → leafBelowS d (≤′-refl {suc s}) (sdesc (sealsL c) [] (core c))
      (rStage d k) w τL τR V V′
  → onlyLeafS d (≤′-refl {suc s}) c (rStage d k) w τL τR V V′
leafRev ≺ (sdesc Xs Ys cd) oc pos le w τL τR r = r
leafRev ≻ (sdesc Xs Ys (desc q env envR)) (wf , refl) {zero} () le w τL τR r
leafRev ≻ {s = s} (sdesc Xs Ys (desc q env envR)) (wf , refl) {suc zero}
    pos le w τL τR r =
  peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR (desc q env envR))
    (λ {V} {V′} _ →
      from (leafG-⇔ (≤′-refl {suc s}) q env envR z≤n w τL τR {V} {V′}) tt)
    r
leafRev ≻ (sdesc Xs Ys (desc q env envR)) (wf , refl) {suc (suc j)} pos
    (s≤s le) w τL τR r =
  peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR (desc q env envR))
    (λ r′ → from (leafG-⇔ ≤′-refl q env envR (m≤n⇒m≤1+n le) w τL τR)
      (to (𝒱≻★-G j q w)
        (to (leafBelow-⇔ ≻ ≤′-refl q env envR (s≤s le) w τL τR) r′)))
    r

-- the goal's leaf read at the clause leaf, at the stages of a conceal
leafCon : ∀ d {ΘL ΘR s} (c : SDesc ΘL ΘR) → OnlyS c → ∀ {k} → 0 < k
  → rBelow d k (suc s) → ∀ w τL τR {V V′}
  → onlyLeafS d (≤′-refl {suc s}) c k w τL τR V V′
  → leafBelowS d (≤′-refl {suc s}) (sdesc (sealsL c) [] (core c))
      k w τL τR V V′
leafCon ≺ (sdesc Xs Ys cd) oc pos lt w τL τR r = r
leafCon ≻ (sdesc Xs Ys (desc q env envR)) (wf , refl) {zero} () lt w τL τR r
leafCon ≻ (sdesc Xs Ys (desc q env envR)) (wf , refl) {suc j} pos lt
    w τL τR r =
  peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR (desc q env envR))
    (λ r′ → from (leafBelow-⇔ ≻ ≤′-refl q env envR lt w τL τR)
      (from (𝒱≻★-G j q w)
        (to (leafG-⇔ ≤′-refl q env envR (<⇒≤ lt) w τL τR) r′)))
    r

-- the seal hypotheses at another target leaf for X
SealR-tgt : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X Y} {x : Φ ∋ X ↔ Y} {d N}
    {w : World} {α′} {δs δt δt′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {σt}
  → (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → k ≤ N → ∀ {Vl Vr}
       → leafRel d (rStage d k) w′ (leaf (δt ↑ᴵ e) X) Vl Vr
       → leafRel d (rStage d k) w′ (leaf (δt′ ↑ᴵ e) X) Vl Vr)
  → (∀ {w′} (e : w′ ⊒ w) {k} → 0 < k → rBelow d k N → ∀ {Vl Vr}
       → leafRel d k w′ (leaf (δt′ ↑ᴵ e) X) Vl Vr
       → leafRel d k w′ (leaf (δt ↑ᴵ e) X) Vl Vr)
  → SealR d N w (r-pair x α′) δs δt σt
  → SealR d N w (r-pair x α′) δs δt′ σt
SealR-tgt f g (hrev , hcon) =
  (λ e pos le r → sealedR-map refl refl (f e pos le) (hrev e pos le r)) ,
  (λ e pos lt r → hcon e pos lt (g e pos lt r))

------------------------------------------------------------------------
-- Case 6
------------------------------------------------------------------------

-- the `∀⊑∀` value relation is its clause
allPair-of : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : pair Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱 d n (∀⊑∀ p) w δ V V′ → allPair d n p w δ V V′
allPair-of ≺ n p w r = r
allPair-of ≻ n p w r = r

-- three embeddings in turn
to-∘∘ : ∀ {Δ₁ Δ₂ Δ₃ Δ₄} (a : Δ₃ ↪ᵗ Δ₄) (b : Δ₂ ↪ᵗ Δ₃) (c : Δ₁ ↪ᵗ Δ₂) X
  → toRenameᵗ a (toRenameᵗ b (toRenameᵗ c X))
    ≡ toRenameᵗ ((a ∘↪ b) ∘↪ c) X
to-∘∘ a b c X =
  sym (trans (toRenameᵗ-∘ (a ∘↪ b) c X) (toRenameᵗ-∘ a b (toRenameᵗ c X)))

env-∘∘ : ∀ {Δ₁ Δ₂ Δ₃ Δ₄} (a : Δ₃ ↪ᵗ Δ₄) (b : Δ₂ ↪ᵗ Δ₃) (c : Δ₁ ↪ᵗ Δ₂)
    (μ : Env∼ Δ₁)
  → renameEnv∼ a (renameEnv∼ b (renameEnv∼ c μ))
    ≡ renameEnv∼ ((a ∘↪ b) ∘↪ c) μ
env-∘∘ a b c μ =
  trans (renameEnv∼-∘ a b (renameEnv∼ c μ)) (renameEnv∼-∘ (a ∘↪ b) c μ)

module _ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C₁ A₁ : Ty (suc Δ)}
    {C₁′ : Ty (suc Δ′)} {B′ : Ty Δ′}
    (c₁ : extᵐ ν ⊢ C₁ ∼ A₁)
    ⦃ Anv′ : NonVar C₁′ ⦄ ⦃ z′ : zero ∈ᵗ C₁′ ⦄
    (c₁′ : instᵐ ν′ ⊢ C₁′ ∼ ⇑ᵗ B′) (B≢★ : B′ ≢ ★)
    (d : Dir) (n : ℕ) {Φ : Corr Δ Δ′}
    (p₁ : pair Φ ⊢ C₁ ⊑ C₁′) (Anv : NonVar A₁) (z : zero ∈ᵗ A₁)
    (r₁ : only Φ ⊢ A₁ ⊑ B′) (w : World)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (h : CastHyp Φ d w δ ν ν′)
    (preC : PreB w (δr δ) (σR h) (`∀ C₁′))
    (preA : PreB w (δr δ) (σR h) B′)
    {Vl : Term (ΔL w)} {Vr : Term (storeR w)} (vl : Value Vl)
    (vr : Value Vr)
  where

  open Case6 c₁ c₁′ B≢★ d n p₁ Anv z r₁ w h preC vl vr

  module Replay (hyp : 𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr)
      {Θ₂ k₀} {χs₀ : StoreChanges (suc (storeR w)) Θ₂} {U : Term Θ₂}
      (run : Mr₁ —→^ k₀ [ χs₀ ] U) (vU : Value U)
      {Δ₂} {pr₂ : Prefix Θ₂ Δ₂} {ρ₂} (st : Steps (pre w₁) χs₀ pr₂ ρ₂)
      {w′} (e : w′ ⊒ arrW w₁ st) {n′ s} (rs : RStage d k₀ n′ s)
      (s<n : suc s ≤ n) (c : SDesc (ΔL w′) (ΔR w′)) (oc : OnlyS c)
    where

    open AtReplay hyp run vU st e rs s<n c oc

    -- the old variables' interpretation at wR
    δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)
    δ₀ = ((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e

    g₀ : GoodI δ₀
    g₀ = GoodI-↑ {δ = (δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st}
      (GoodI-↑ {δ = δ ↑ᴵ e₁} (GoodI-↑ {δ = δ} (good h) e₁) (arrE w₁ st)) e

    -- wR is a future of the cast's world
    E₀ : wR ⊒ w
    E₀ = ⊒-trans (replay-⊒ (⊒-trans e (arrE w₁ st))) e₁

    E : ∀ {w″} → w″ ⊒ wR → w″ ⊒ w
    E e″ = ⊒-trans e″ E₀

    D₀ : δ₀ ≈ᴵ δ ↑ᴵ E₀
    D₀ = ≈ᴵ-trans (↑ᴵ-trans (δ ↑ᴵ e₁) e (arrE w₁ st))
      (↑ᴵ-trans δ (replay-⊒ (⊒-trans e (arrE w₁ st))) e₁)

    D : ∀ {w″} (e″ : w″ ⊒ wR) → δ₀ ↑ᴵ e″ ≈ᴵ δ ↑ᴵ E e″
    D e″ = ≈ᴵ-trans (↑ᴵ-resp D₀ e″) (↑ᴵ-trans δ e″ E₀)

    -- the left's old variables, renamed into w′
    eqδ : ∀ X → δl δ₀ X ≡ renameᵗ (toRenameᵗ ρ) (δl δ X)
    eqδ X = cong (renameᵗ (toRenameᵗ ρ))
      (trans (renameTy-id _) (renameTy-id (δl δ X)))

    -- the composite substitutions of `CastL` and `CastR` are δ₃'s
    hL : ∀ {w″} (e″ : w″ ⊒ wR) X
      → CastL.σC (sL h) ρ T (ρL e″) X ≡ δl (δ₃ ↑ᴵ e″) X
    hL e″ zero = refl
    hL e″ (suc X) =
      trans (CastL.σC-suc (sL h) ρ T (ρL e″) X)
        (trans (sym (renameᵗ-comp (toRenameᵗ ρ) (toRenameᵗ (ρL e″))
                       (δl δ X)))
          (cong (renameᵗ (toRenameᵗ (ρL e″))) (sym (eqδ X))))

    σ₂ : ∀ {w″} → w″ ⊒ wR → Δ′ ⇒ˢ storeR w″
    σ₂ e″ = CastR.σC (sR h) (ρS e″)

    σeq : ∀ {w″} (e″ : w″ ⊒ wR) Y
      → renameᵗ (toRenameᵗ (ρS (E e″))) (σR h Y) ≡ σ₂ e″ Y
    σeq e″ Y =
      trans (renameᵗ-cong (σR h Y) pw)
        (sym (CastR.σC-eq (sR h) (ρS e″) Y))
      where
      pw : ∀ X → toRenameᵗ (ρS (E e″)) X
        ≡ toRenameᵗ (ρS e″) (toRenameᵗ wk↪ᵗ X)
      pw X = trans (toRenameᵗ-∘ (ρS e″) _ X)
        (cong (toRenameᵗ (ρS e″))
          (trans (toRenameᵗ-∘ id↪ᵗ (embedᶜˢ (bind ★ ∷ [])) X)
            (trans (toRename-id-eq _)
              (cong (λ r → toRenameᵗ r X) (embed-bind ★)))))

    sL₂ : ∀ {w″} (e″ : w″ ⊒ wR)
      → SubstEnv∼ (extᵐ ν) (renameEnv∼ (ρL e″) (renameEnv∼ ρ (νL h)))
          (δl (δ₃ ↑ᴵ e″))
    sL₂ e″ = CastL.envL (sL h) ρ T (ρL e″) (hL e″)

    νR₂ : ∀ {w″} → w″ ⊒ wR → Env∼ (storeR w″)
    νR₂ e″ = CastR.νC (sR h) (ρS e″)

    sR₂ : ∀ {w″} (e″ : w″ ⊒ wR) → SubstEnv∼ ν′ (νR₂ e″) (σ₂ e″)
    sR₂ e″ = CastR.envR (sR h) (ρS e″) (λ X → refl)

    -- the right's instantiation is typed in the store binding α′ to `★`
    -- (as in preservation's `β-inst` case), at the store preimage of
    -- the opened right type
    typedI : Typedᴿ wR (substᵗ (δr δ₃) (C₁′ [ ★ ]ᵗ)) Ir
    typedI = typedᴿ (⇑ᵗ (A₀ [ ★ ]ᵗ))
      (trans (pre≡ PB) (cong (renameᵗ (toRenameᵗ (ιʷ wR))) eqT))
      (reveal-zero-typing A₀ ★
        (retype (applyBody-open-zero A₀)
          (⊢• (typing-shiftᵗ-bind (pre-typed preC (proj₁ hyp))))))
      where
      PB : PreB wR (δr δ₀) (σR h ↑ˢ E₀) (C₁′ [ ★ ]ᵗ)
      PB = PreB-map (δr≡ D₀) (PreB-open (PreB-↑ preC E₀))

      pwS : ∀ X → toRenameᵗ (ρS E₀) X ≡ suc X
      pwS X = trans (toRenameᵗ-∘ id↪ᵗ (embedᶜˢ (bind ★ ∷ [])) X)
        (trans (toRename-id-eq _)
          (trans (cong (λ r → toRenameᵗ r X) (embed-bind ★))
            (toRename-wk-eq X)))

      pw : ∀ X → substᵗ (σR h ↑ˢ E₀) (singleSubᵗ ★ X)
        ≡ ⇑ᵗ (substᵗ (singleSubᵗ ★) (extsᵗ (σR h) X))
      pw zero = refl
      pw (suc Y) = trans (renameᵗ-cong (σR h Y) pwS)
        (cong ⇑ᵗ (sym (shift-openᵗ (σR h Y) ★)))

      eqT : substᵗ (σR h ↑ˢ E₀) (C₁′ [ ★ ]ᵗ) ≡ ⇑ᵗ (A₀ [ ★ ]ᵗ)
      eqT = trans (substᵗ-∘ (σR h ↑ˢ E₀) (singleSubᵗ ★) C₁′)
        (trans (substᵗ-cong C₁′ pw)
          (trans (sym (renameᵗ-subst suc
                         (λ X → substᵗ (singleSubᵗ ★) (extsᵗ (σR h) X))
                         C₁′))
            (cong ⇑ᵗ (sym (substᵗ-∘ (singleSubᵗ ★) (extsᵗ (σR h)) C₁′)))))

    -- the embeddings from the cast's world into wR's
    ρE₀ : ρL E₀ ≡ ρ
    ρE₀ = trans (∘↪-idʳ _) (∘↪-idʳ ρ)

    ρSE₀ : ρS E₀ ≡ wk↪ᵗ
    ρSE₀ = trans (∘↪-idˡ _) (embed-bind ★)

    -- VarI in a future w‴ of a future w″ of wR: at the old variables
    -- from the cast's VarI there (`CastHyp.var` along `E`), at the new
    -- one from `selfO-only`
    module Var {w″} (e″ : w″ ⊒ wR) {w‴} (e‴ : w‴ ⊒ w″) where

      E′ : w‴ ⊒ w
      E′ = E (⊒-trans e‴ e″)

      lv : ∀ Z → leaf (δ ↑ᴵ E′) Z ≈ˡ leaf ((δ₃ ↑ᴵ e″) ↑ᴵ e‴) (suc Z)
      lv Z = ≈ˡ-sym (≈ˡ-trans (leaf≈ (↑ᴵ-trans δ₀ e‴ e″) Z)
        (leaf≈ (D (⊒-trans e‴ e″)) Z))

      envL≡ : renameEnv∼ (ρL e‴) (renameEnv∼ (ρL e″) (renameEnv∼ ρ (νL h)))
        ≡ renameEnv∼ (ρL E′) (νL h)
      envL≡ = trans (env-∘∘ (ρL e‴) (ρL e″) ρ (νL h))
        (cong (λ r → renameEnv∼ ((ρL e‴ ∘↪ ρL e″) ∘↪ r) (νL h)) (sym ρE₀))

      envR≡ : renameEnv∼ (ρS e‴) (CastR.νC (sR h) (ρS e″))
        ≡ renameEnv∼ (ρS E′) (νR h)
      envR≡ = trans (env-∘∘ (ρS e‴) (ρS e″) wk↪ᵗ (νR h))
        (cong (λ r → renameEnv∼ ((ρS e‴ ∘↪ ρS e″) ∘↪ r) (νR h)) (sym ρSE₀))

      aL : Agree suc (renSE (ρL E′) (sL h)) (renSE (ρL e‴) (sL₂ e″))
      aL = agree-ren (CastL.πL (sL h) ρ T (ρL e″)) (toRenameᵗ (ρL e‴))
        (toRenameᵗ (ρL E′)) (CastL.eπL (sL h) ρ T (ρL e″))
        (renameEnv∼-preserves (ρL e‴) _)
        (renameEnv∼-preserves (ρL E′) (νL h)) envL≡
        (λ X → trans (to-∘∘ (ρL e‴) (ρL e″) ρ X)
          (cong (λ r → toRenameᵗ ((ρL e‴ ∘↪ ρL e″) ∘↪ r) X) (sym ρE₀)))
        (CastL.envL-old (sL h) ρ T (ρL e″) (hL e″))

      aR : Agree (λ Y → Y) (renSE (ρS E′) (sR h)) (renSE (ρS e‴) (sR₂ e″))
      aR = agree-ren (CastR.ρC (sR h) (ρS e″)) (toRenameᵗ (ρS e‴))
        (toRenameᵗ (ρS E′)) (CastR.eC (sR h) (ρS e″))
        (renameEnv∼-preserves (ρS e‴) _)
        (renameEnv∼-preserves (ρS E′) (νR h)) envR≡
        (λ X → trans (to-∘∘ (ρS e‴) (ρS e″) wk↪ᵗ X)
          (cong (λ r → toRenameᵗ ((ρS e‴ ∘↪ ρS e″) ∘↪ r) X) (sym ρSE₀)))
        (CastR.envR-old (sR h) (ρS e″) (λ X → refl))

      -- the new variable's world cast is `refl∼` of its left type
      νL‴ = renameEnv∼ (ρL e‴) (renameEnv∼ (ρL e″) (renameEnv∼ ρ (νL h)))

      selfZ : ∀ (Wl : Term (ΔL w‴))
        → Wl ⟨ SubstEnv∼.self (renSE (ρL e‴) (sL₂ e″)) zero ⟩
          ≡ Wl ⟨ refl∼ {μ = νL‴}
                   (renameᵗ (toRenameᵗ (ρL (⊒-trans e‴ e″))) T) ⟩
      selfZ Wl =
        trans (cong (λ cc → Wl ⟨ rename∼ (toRenameᵗ (ρL e‴)) h‴ cc ⟩)
                (refl-rename (toRenameᵗ (ρL e″)) h″ T))
          (trans (cong (λ cc → Wl ⟨ cc ⟩)
                   (refl-rename (toRenameᵗ (ρL e‴)) h‴
                     (renameᵗ (toRenameᵗ (ρL e″)) T)))
            (cong (λ A → Wl ⟨ refl∼ {μ = νL‴} A ⟩)
              (trans (renameᵗ-comp (toRenameᵗ (ρL e″)) (toRenameᵗ (ρL e‴)) T)
                (renameᵗ-cong T
                  (λ X → sym (toRenameᵗ-∘ (ρL e‴) (ρL e″) X))))))
        where
        h″ = renameEnv∼-preserves (ρL e″) (renameEnv∼ ρ (νL h))
        h‴ = renameEnv∼-preserves (ρL e‴)
          (renameEnv∼ (ρL e″) (renameEnv∼ ρ (νL h)))

      new : ∀ k → CastRel d k (X⊑★ (only-here {Φ = Φ})) (X⊑★ only-here) w‴
        ((δ₃ ↑ᴵ e″) ↑ᴵ e‴)
        (λ V → V ⟨ SubstEnv∼.self (renSE (ρL e‴) (sL₂ e″)) zero ⟩)
        (λ V → V ⟨ id {μ = renameEnv∼ (ρS e‴) (νR₂ e″)} ★ ⟩)
      new k {Wl} {Wr} wl wr r =
        subst (λ M → ℰ d k (X⊑★ (only-here {Φ = Φ})) w‴ ((δ₃ ↑ᴵ e″) ↑ᴵ e‴) M
                       (Wr ⟨ id {μ = renameEnv∼ (ρS e‴) (νR₂ e″)} ★ ⟩))
          (sym (selfZ Wl))
          (CastRel-resp d k (X⊑★ only-here) (X⊑★ only-here) w‴
            (≈ᴵ-sym (↑ᴵ-trans δ₃ e‴ e″))
            (selfO-only d k (≤′-refl {suc s}) {wR} c δ₀ g₀ (⊒-trans e‴ e″))
            wl wr r)

      var₂ : VarI (only Φ) d w‴ ((δ₃ ↑ᴵ e″) ↑ᴵ e‴)
        (renSE (ρL e‴) (sL₂ e″)) (renSE (ρS e‴) (sR₂ e″))
      var₂ = VarI-ext d w‴ lv aL aR (sym envR≡) (CastHyp.var h E′) new

    ------------------------------------------------------------------
    -- `inner`: the hypothesis's clause, the reveal of α′, and the
    -- substitution instance (notes/logrel-dgg.md, "Case 6")
    ------------------------------------------------------------------

    -- α′ in the scope
    α″ : TyVar (ΔR wR)
    α″ = toRenameᵗ (ιʷ wR) zero

    -- the clause's interpretation: X paired at α′, its leaf the goal's
    -- descriptor sealed at α′ on the right, at the hypothesis's stage
    -- above s
    cP : SDesc (ΔL wR) (ΔR wR)
    cP = sdesc (SDesc.sealsL c) (α″ ∷ []) (SDesc.core c)

    δP : Interp (suc Δ) (suc Δ′) (ΔL wR) (ΔR wR)
    δP = extPairI T (ιT wR (＇ zero)) (sem (leafBelowS d (≤⇒≤′ s<n) cP)) δ₀

    -- after the reveal: X paired at `★`, its leaf the goal's
    δQ : Interp (suc Δ) (suc Δ′) (ΔL wR) (ΔR wR)
    δQ = extPairI T ★ (sem (onlyLeafS d (≤′-refl {suc s}) c)) δ₀

    -- the right's instantiation, before its reveal
    Ir₀ : Term (storeR wR)
    Ir₀ = ⇑ᵗᵐ Vr ⦂∀ (bind ★ ▷ᵇ A₀) [ ＇ zero ]

    revα : MFrame (storeR wR)
    revα = just (reveal 〖 zero , ★ ↑ A₀ 〗)

    -- the right-only reveal of α′ as `★` (`revR`, mode `r-pair`), in
    -- every future of wR; proved below (`revealK`)
    RevealK : Set
    RevealK = ∀ {w₂} (e₂ : w₂ ⊒ wR) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 d k p₁ w₂ (δP ↑ᴵ e₂) Ql Qr
      → ℰ d k p₁ w₂ (δQ ↑ᴵ e₂) Ql (mplug (renameMFrame (ρS e₂) revα) Qr)

    -- the hypothesis's clause at wR, at the stage above s, brought down
    clauseP : ℰ d s p₁ wR δP Il Ir₀
    clauseP =
      ℰ-down d (n≤1+n s) p₁ wR
        (GoodI-extPairI {T = T} {T′ = ιT wR (＇ zero)} {δ = δ₀}
          (leafBelowS-good d (≤⇒≤′ s<n) cP) g₀)
        (ℰᵍ-≡ eqL eqR
          (ℰᵍ-map d (suc s) wR
            (λ le′ w″ e′ V V′ a →
              𝒱≤-cast d (≤′-trans le′ le) le′ p₁ w″
                (𝒱≤-resp d (≤′-trans le′ le) p₁ w″ (↑ᴵ-resp eqv e′) a))
            (allPair-of d n p₁ w (proj₂ hyp) E₀ le cP (proj₁ oc) (＇ zero)
              refl B₀ (PreB-body C₁′ (PreB-↑ preC E₀)))))
      where
      le = ≤⇒≤′ s<n
      B₀ = substᵗ (extsᵗ (σR h ↑ˢ E₀)) C₁′

      eqv : extPairI T (ιT wR (＇ zero)) (sem (leafBelowS d le cP))
          (δ ↑ᴵ E₀) ≈ᴵ δP
      eqv = extPairI-resp ≈ˡ-refl (≈ᴵ-sym D₀)

      eqL : renameᵗᵐ (ρL E₀) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ E₀))) C₁ [ T ]
        ≡ Il
      eqL = cong₂ (λ M C → M ⦂∀ C [ T ]) (cong (λ r → renameᵗᵐ r Vl) ρE₀)
        (trans (substᵗ-cong C₁ (exts-cong
                 (λ X → cong (λ r → renameᵗ (toRenameᵗ r) (δl δ X)) ρE₀)))
          (sym (∀-inj (renameᵗ-subst (toRenameᵗ ρ) (δl δ) (`∀ C₁)))))

      pw : ∀ Y → (σR h ↑ˢ E₀) Y
        ≡ renameᵗ (toRenameᵗ (embedᶜˢ (bind ★ ∷ []))) (σR h Y)
      pw Y = renameᵗ-cong (σR h Y)
        (λ X → trans (toRenameᵗ-∘ id↪ᵗ (embedᶜˢ (bind ★ ∷ [])) X)
          (toRename-id-eq _))

      eqR : renameᵗᵐ (ρS E₀) Vr ⦂∀ B₀ [ ＇ zero ] ≡ Ir₀
      eqR = cong₂ (λ M C → M ⦂∀ C [ ＇ zero ])
        (cong (λ r → renameᵗᵐ r Vr) ρSE₀)
        (trans (substᵗ-cong C₁′ (exts-cong pw)) (annot ★ (σR h) C₁′))

    -- X paired at right type `★` read as X left-only, at the same leaf
    subI : SubI (pairStarˢ {Ψ = Φ}) d (suc s) wR δQ δ₃
    sl≡ subI zero = refl
    sl≡ subI (suc X) = refl
    sr≡ subI zero = refl
    sr≡ subI (suc Y) = refl
    sonly subI (only-pair x) e″ {k} pos lt = 𝒱-X★ d k (only-only x) _
    spair subI ↔-here e″ {k} lt = 𝒱-X★ d k only-here _
    spair subI (↔-pair x) e″ {k} lt = 𝒱-XY d k (↔-only x) _

    starOnly : ∀ {w₂} (e₂ : w₂ ⊒ wR) {k} → 0 < k → k ≤ s → ∀ {V V′}
      → 𝒱 d k p₁ w₂ (δQ ↑ᴵ e₂) V V′ → 𝒱 d k p₂ w₂ (δ₃ ↑ᴵ e₂) V V′
    starOnly {w₂} e₂ {k} pos le r =
      𝒱-at d k (substᵗ-id C₁) refl (substᵖ pairStarˢ p₁) p₂ w₂
        (to (𝒱-subst d k pairStarˢ p₁ w₂ (SubI-↑ subI e₂) pos (s≤s le))
          r)

    -- `inner` from the reveal
    innerFrom : RevealK → ℰ d s p₂ wR δ₃ Il Ir
    innerFrom revK =
      ℰᵍ-map⁺ d s wR
        (λ le pos w₂ e₂ V V′ a →
          𝒱≤-cast d ≤′-refl le p₂ w₂
            (starOnly e₂ pos (≤′⇒≤ le) (𝒱≤-cast d le ≤′-refl p₁ w₂ a)))
        (ℰ-bind₂ d s p₁ p₁ wR {δ₁ = δP} {δ₂ = δQ} nothing revα clauseP
          revK)

    ------------------------------------------------------------------
    -- `RevealK`: the right-only lemma (`revR`, mode `r-pair`) at the
    -- extension of wR's scope over the cast's store, where α′ is
    -- reserved, to wR, where it is allocated (`RConvI-newR`)
    ------------------------------------------------------------------

    X₁ : w′ ⊒ w₁
    X₁ = ⊒-trans e (arrE w₁ st)

    E″ : w′ ⊒ w
    E″ = ⊒-trans X₁ e₁

    -- w′'s scope and tags over the cast's store
    W₀ : World
    W₀ = replayW w′ (replayPre E″) (ΣR w)

    R₀ : W₀ ⊒ w
    R₀ = replay-⊒ E″

    -- wR allocates α′ over W₀: its store embeds as by the right's
    -- `bind ★`, its scope and left store do not move
    cohE : Coh (replayPre E″) (replayPre X₁) (ρS e₁) id↪ᵗ
    cohE Y =
      trans (grows-unique (replayPre E″) (replayPre E″) Grows-id Y)
        (trans (sym (grows-unique (pre w) (replayPre E″) (grows E″) Y))
          (trans (toRenameᵗ-∘ (ρR X₁) (ρR e₁) _)
            (trans (cong (toRenameᵗ (ρR X₁)) (coh e₁ Y))
              (grows-unique (pre w₁) (replayPre X₁) (grows X₁) _))))

    E₁ : wR ⊒ W₀
    E₁ = ext id↪ᵗ id↪ᵗ (ρS e₁) cohE Grows-id (tags≡ (⊒-refl w′)) (ΣR⊒ e₁)

    -- the old variables' store types at W₀; their leaves are closed
    -- under right conversions (`CastHyp.freshR` along R₀)
    σ₀ : Δ′ ⇒ˢ storeR w
    σ₀ = σR h ↑ˢ R₀

    fIR : FreshIR Φ d (suc s) W₀ δ₀ σ₀
    fIR = record
      { fgoodR = g₀
      ; fR = λ {Z} z → FreshR-resp (≈ˡ-sym (leaf≈ D₀ Z))
               (FreshR-↑ {d = d} R₀ {L = leaf δ Z} (freshR h z))
      ; forcR = oracleR-all d (suc s)
      }

    -- X's leaves: the clause's (as `SealNewR` writes cP) and the goal's
    le₀ : suc s ≤′ n
    le₀ = ≤⇒≤′ s<n

    cS : SDesc (ΔL wR) (ΔR wR)
    cS = sdesc (map (renameVar id↪ᵗ) (SDesc.sealsL c)) (α″ ∷ [])
      (renameDesc id↪ᵗ id↪ᵗ (SDesc.core c))

    Ls : Leaf (ΔL wR) (ΔR wR)
    Ls = sem (leafBelowS d le₀ cS)

    Lt : Leaf (ΔL wR) (ΔR wR)
    Lt = sem (onlyLeafS d (≤′-refl {suc s}) c)

    gLt = onlyLeafS-good d (≤′-refl {suc s}) c

    Ls≈ : sem (leafBelowS d le₀ cP) ≈ˡ Ls
    Ls≈ =
      ≈ˡ-≡ (cong₂ (λ Xs cd → sem (leafBelowS d le₀ (sdesc Xs (α″ ∷ []) cd)))
        (sym (map-renameVar-id (SDesc.sealsL c)))
        (sym (renameDesc-id (SDesc.core c))))

    -- X's seal hypotheses: `SealNewR` (bounds s + 1), moved to the
    -- goal's leaf
    τLe : ∀ {w₃} → w₃ ⊒ wR → ΔL wR ↪ᵗ ΔL w₃
    τLe e₃ = (id↪ᵗ ∘↪ ρL e₃) ∘↪ id↪ᵗ

    τRe : ∀ {w₃} → w₃ ⊒ wR → ΔR wR ↪ᵗ ΔR w₃
    τRe e₃ = (id↪ᵗ ∘↪ ρR e₃) ∘↪ id↪ᵗ

    sealβ : SealR d (suc s) wR (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
      (extPairI T (ιT wR (＇ zero)) Ls (δ₀ ↑ᴵ E₁))
      (extPairI T ★ Lt δ₀ ↑ᴵ E₁) ((★ •ˢ σ₀) ↑ˢ E₁)
    sealβ =
      SealR-tgt {Φ = pair Φ} {x = ↔-here} {α′ = zero}
        {δs = extPairI T (ιT wR (＇ zero)) Ls (δ₀ ↑ᴵ E₁)}
        {δt = extPairI (repL (SDesc.sealsL c) (SDesc.core c)) ★
                (sem (leafBelowS d (≤′-refl {suc s})
                  (sdesc (SDesc.sealsL c) [] (SDesc.core c))))
                δ₀ ↑ᴵ E₁}
        {δt′ = extPairI T ★ Lt δ₀ ↑ᴵ E₁} {σt = (★ •ˢ σ₀) ↑ˢ E₁}
        (λ e₃ pos le r → leafRev d c oc pos le _ (τLe e₃) (τRe e₃) r)
        (λ e₃ pos lt r → leafCon d c oc pos lt _ (τLe e₃) (τRe e₃) r)
        (SealNewR.sealNewR d le₀ (≤′-refl {suc s}) ≤-refl E₁
          (SDesc.sealsL c) [] (SDesc.core c) {Φ = Φ} {δt = δ₀} {σt = σ₀}
          {T = T} zero (coreStar (SDesc.core c) (proj₂ oc))
          (upRefl d (suc s)))

    hβ : RConvI d (suc s) wR (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
      (extPairI T (ιT wR (＇ zero)) Ls (δ₀ ↑ᴵ E₁))
      (extPairI T ★ Lt δ₀ ↑ᴵ E₁)
      (＇ zero •ˢ (σ₀ ↑ˢ E₁)) ((★ •ˢ σ₀) ↑ˢ E₁)
    hβ = RConvI-newR E₁ (new-bind ★) {Ls = Ls} {Lt = Lt} {Tr = ★} {Tl = T}
      {T = T} (sym (renameTy-id T)) ≤-refl fIR (leafBelowS-good d le₀ cS)
      gLt (leafFreshR★ gLt) sealβ (bind-Σ (ΣR w) ★)

    psβ : PreS wR (extPairI T (ιT wR (＇ zero)) Ls (δ₀ ↑ᴵ E₁))
      (extPairI T ★ Lt δ₀ ↑ᴵ E₁)
      (＇ zero •ˢ (σ₀ ↑ˢ E₁)) ((★ •ˢ σ₀) ↑ˢ E₁) C₁′
    psβ = PreB-ext C₁′ (PreB-↑ pre₀ E₁) (＇ zero) ,ᵖ
      PreB-↑ (PreB-ext C₁′ pre₀ ★) E₁
      where
      pre₀ : PreB W₀ (δr δ₀) σ₀ (`∀ C₁′)
      pre₀ = PreB-map (δr≡ D₀) (PreB-↑ preC R₀)

    -- the reveal's annotation is A₀
    eqA : substᵗ (＇ zero •ˢ (σ₀ ↑ˢ E₁)) C₁′ ≡ A₀
    eqA = trans (open0 ★ σ₀ C₁′)
      (substᵗ-cong C₁′ (exts-cong (λ Y → renameTy-id (σR h Y))))

    revealK : RevealK
    revealK {w₂} e₂ {k} k≤s {Ql} {Qr} ql qr q =
      ℰ-resp d k p₁ w₂ (↑ᴵ-resp (transportI-id (extPairI T ★ Lt δ₀)) e₂)
        (ℰᵍ-≡ refl
          (trans (rcRenR e₂ (r-pair {Φ = pair Φ} {X = zero} ↔-here zero)
                    (＇ zero •ˢ (σ₀ ↑ˢ E₁)) ((★ •ˢ σ₀) ↑ˢ E₁) Qr C₁′)
            (↑-pk (pk-ren↑ (toRenameᵗ (ρS e₂)) (pk-〖〗 refl refl eqA))))
          (revR d p₁ (RConvI-↑ e₂ hβ) (PreS-↑ psβ e₂)
            (≤-trans k≤s (n≤1+n s)) ql qr
            (𝒱-resp d k p₁ w₂
              (↑ᴵ-resp (extPairI-resp Ls≈ (≈ᴵ-sym (transportI-id δ₀))) e₂)
              q)))

    -- the obligations at the replay
    module Assemble where

      inner : ℰ d s p₂ wR δ₃ Il Ir
      inner = innerFrom revealK

      fP : ∀ {w″} (e″ : w″ ⊒ wR) {Z Y′} → only Φ ∋ Z ↔ Y′
        → FreshP d both w″ (leaf (δ₃ ↑ᴵ e″) Z) (δl (δ₃ ↑ᴵ e″) Z) (σ₂ e″ Y′)
      fP e″ {suc Z} {Y′} (↔-only x) =
        subst₂ (FreshP d both _ (leaf (δ₃ ↑ᴵ e″) (suc Z)))
          (sym (δl≡ (D e″) Z)) (σeq e″ Y′)
          (FreshP-resp {rk = both} (≈ˡ-sym (leaf≈ (D e″) Z))
            (FreshP-↑ {d = d} (E e″) {L = leaf δ Z} {rk = both}
              (freshP h x)))

      fO : ∀ {w″} (e″ : w″ ⊒ wR) {Z} → only Φ ∋ Z only
        → FreshO d w″ (leaf (δ₃ ↑ᴵ e″) Z) (δl (δ₃ ↑ᴵ e″) Z)
      fO e″ only-here =
        FreshO-↑ {d = d} e″ {L = leaf δ₃ zero}
          (proj₂ (oracle-all d (suc s)) {wR} (≤′-refl {suc s}) ≤-refl c)
      fO e″ {suc Z} (only-only o) =
        subst (FreshO d _ (leaf (δ₃ ↑ᴵ e″) (suc Z)))
          (sym (δl≡ (D e″) Z))
          (FreshO-resp (≈ˡ-sym (leaf≈ (D e″) Z))
            (FreshO-↑ {d = d} (E e″) {L = leaf δ Z} (freshO h o)))

      fR : ∀ {w″} (e″ : w″ ⊒ wR) {Z Y′} → only Φ ∋ Z ↔ Y′
        → FreshR d w″ (leaf (δ₃ ↑ᴵ e″) Z) (σ₂ e″ Y′)
      fR e″ {suc Z} {Y′} (↔-only x) =
        subst (FreshR d _ (leaf (δ₃ ↑ᴵ e″) (suc Z))) (σeq e″ Y′)
          (FreshR-resp (≈ˡ-sym (leaf≈ (D e″) Z))
            (FreshR-↑ {d = d} (E e″) {L = leaf δ Z} (freshR h x)))

      hyp₂ : ∀ {w″} (e″ : w″ ⊒ wR)
        → CastHyp (only Φ) d w″ (δ₃ ↑ᴵ e″) (extᵐ ν) ν′
      hyp₂ e″ = record
        { sL = sL₂ e″
        ; σR = σ₂ e″
        ; sR = sR₂ e″
        ; good = GoodI-↑ {δ = δ₃}
            (GoodI-extOnlyI {T = T} {δ = δ₀}
              (onlyLeafS-good d (≤′-refl {suc s}) c) g₀) e″
        ; freshP = fP e″
        ; freshO = fO e″
        ; freshR = fR e″
        ; var = Var.var₂ e″
        }

      ob : Ob
      ob = record
        { inner = inner
        ; typed = typedI
        ; hyp₂ = hyp₂
        ; preC₂ = λ e″ → PreB-σ (σeq e″)
            (PreB-map (δr≡ (D e″)) (PreB-open (PreB-↑ preC (E e″))))
        ; preA₂ = λ e″ → PreB-σ (σeq e″)
            (PreB-map (δr≡ (D e″)) (PreB-↑ preA (E e″)))
        ; castL₂ = λ e″ Q → CastL.castL (sL h) ρ T (ρL e″) (hL e″) c₁ Q
        ; castR₂ = λ e″ Q →
            CastR.castR (sR h) (ρS e″) (λ X → refl) c₁′ Q
        }

  -- case 6, from the induction hypothesis
  case6R : CastCase c₁ (c₁′ [ ★/0 ]ᶜ)
    → 𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr
    → ℰ d n (∀⊑ Anv z r₁) w δ (Vl ⟨ subst∼ (sL h) (∀ᶜ c₁) ⟩)
        (Vr ⟨ subst∼ (sR h) ((inst c₁′) B≢★) ⟩)
  case6R =
    case6′ (λ hyp run vU st e rs s<n c oc →
      Replay.Assemble.ob hyp run vU st e rs s<n c oc)

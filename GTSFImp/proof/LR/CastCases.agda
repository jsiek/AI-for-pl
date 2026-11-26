module proof.LR.CastCases where

-- File Charter:
--   * Cases of the cast lemma (`proof.LR.CastLemma`, `CastCase`) that
--     need no world change and no induction hypothesis
--     (notes/logrel-dgg.md, "The cast lemma: the case table"):
--       - `caseBotL`, `caseBotR`: a source `∀X.X` on either side.  The
--         hypothesis is empty: at `bot-elim` and `bot⊑★` by the value
--         relation, at `∀X.X ⊑ ∀Y.Y` because the right value is typed
--         and no value has type `∀X.X` (`no-bot-value`).
--       - `caseBotIntroL`: a left `bot-intro` blames in one step.
--       - `caseAllVar`: a left `∀ᶜ` into `∀X.X`; its body cast ends in
--         X of mode `X∼X`, so it is `id X` (`castVar`) and the source
--         is `∀X.X` (empty).  Used against a right `inst` into
--         `∀X.X ⊑ ∀★` and, with `belowBot`, against a right
--         `bot-intro` (`caseAllBotIntro`).
--       - `rowId`: every right cast against a left `id`.  Besides the
--         cases of `proof.LR.CastLemma` (`id` against `id` at `★`, at
--         base types and at variables), a left `id ι` against a right
--         `id ★`, `ι!` and `？ι`.
--   * The one-sided rule `⊑⟨⟩` of `LR.CastPrecision` (a right cast
--     only): its lemma `CastLemmaR`, at one cast `CastCaseR`, with
--     the hypotheses `CastHypR` (those of `CastHyp` without the left
--     environment; its base case `VarIR` is the right's `id` at a
--     paired variable).  Proved: `rowIdR`, a right `id`;
--     `caseBotElimR`, `caseBotIntroR` (both empty).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)


open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩; $; _《_》; inj; blame)
open import Reduction using (_—→_; β-id; tag-untag; blame-bot-intro)
open import LR.Precision
open import LR.World
open import LR.Relation
open import LR.EagerCast using (Eager)
open import proof.TypeSafety.Progress using (no-bot-value)
open import proof.LR.Expression using (ℰ-stepL; ℰᵍ-blame)
open import proof.LR.ConvBase using (ℰ-zero; ℰ-steps?; stay; step;
  ↔-only-⊥)
open import proof.LR.CastLemma using (CastCase; CastHyp; good; ℰ-ids;
  caseId★; caseIdι; caseVarP; caseVarO; CastRel; renSE; ren-refl)
open import proof.LR.ConvBase using (ℰ-stepR?)
open import proof.LR.ConvLemma using (FreshP; FreshO; both; PreB)
open import proof.LR.ConvRight using (FreshR)
open import proof.LR.Monotone using (GoodI)
open import proof.LR.WorldProps using (⊒-refl)
open import proof.LR.InterpProps using (ℰᵍ-≡; ℰ-resp; 𝒱-resp; ↑ᴵ-refl;
  ≈ᴵ-sym)
open import proof.LR.PrecisionUnique using (⊑-unique; ↔-unique)

------------------------------------------------------------------------
-- A source `∀X.X`: the hypothesis is empty
------------------------------------------------------------------------

-- no typed right value has type `∀X.X`
noBotR : ∀ {w : World} {Vr : Term (storeR w)}
  → Value Vr → Typedᴿ w (`∀ (＇ zero)) Vr → ⊥
noBotR v (typedᴿ (`∀ (＇ zero)) refl t) = no-bot-value v t
noBotR v (typedᴿ (`∀ (＇ suc X)) () t)
noBotR v (typedᴿ (`∀ (‵ ι)) () t)
noBotR v (typedᴿ (`∀ ★) () t)
noBotR v (typedᴿ (`∀ (A ⇒ B)) () t)
noBotR v (typedᴿ (`∀ (`∀ A)) () t)
noBotR v (typedᴿ (＇ X) () t)
noBotR v (typedᴿ (‵ ι) () t)
noBotR v (typedᴿ ★ () t)
noBotR v (typedᴿ (A ⇒ B) () t)

-- a left source `∀X.X` (a left `bot-elim`, or `∀ᶜ` over `id X`)
caseBotL : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A} {C′ A′}
    (c : ν ⊢ `∀ (＇ zero) ∼ A) (c′ : ν′ ⊢ C′ ∼ A′)
  → CastCase c c′
caseBotL c c′ d n (∀⊑∀ (X⊑Y ↔-here)) r w h pC pA vl vr (t , a) =
  ⊥-elim (noBotR vr t)
caseBotL c c′ d n (∀⊑ () z q) r w h pC pA vl vr hyp
caseBotL c c′ d n (∀⊑★ ns (X⊑★ ())) r w h pC pA vl vr hyp
caseBotL c c′ ≺ n bot-elim r w h pC pA vl vr (t , ())
caseBotL c c′ ≻ n bot-elim r w h pC pA vl vr (t , ())
caseBotL c c′ ≺ n bot⊑★ r w h pC pA vl vr (t , ())
caseBotL c c′ ≻ n bot⊑★ r w h pC pA vl vr (t , ())

-- a right source `∀Y.Y`
caseBotR : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A} {A′}
    (c : ν ⊢ C ∼ A) (c′ : ν′ ⊢ `∀ (＇ zero) ∼ A′)
  → CastCase c c′
caseBotR c c′ d n p r w h pC pA vl vr (t , a) = ⊥-elim (noBotR vr t)

------------------------------------------------------------------------
-- A left `∀ᶜ` into `∀X.X`
------------------------------------------------------------------------

-- a cast into a variable is its identity, or a projection from `★`
-- at a mode that allows it (an `inst` would need its body to be the
-- variable, against `NonVar`, or `★`, against the occurrence)
castVar : ∀ {Δ} {μ : Env∼ Δ} {A X} → μ ⊢ A ∼ ＇ X
  → A ≡ ＇ X ⊎ (A ≡ ★ × (μ ‼ X ≡ ★∼X ⊎ μ ‼ X ≡ ★∼X∼★))
castVar (id (＇ X)) = inj₁ refl
castVar (？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) with castVar c
castVar (？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) | inj₁ refl = inj₂ (refl , inj₁ eq)
castVar (？_ ⦃ ★∼G = ★∼Xᵍ eq ⦄ c) | inj₂ (() , m)
castVar (？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) with castVar c
castVar (？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) | inj₁ refl = inj₂ (refl , inj₂ eq)
castVar (？_ ⦃ ★∼G = ★∼Xᶜ eq ⦄ c) | inj₂ (() , m)
castVar (？_ ⦃ ★∼G = ★∼ι ⦄ c) with castVar c
castVar (？_ ⦃ ★∼G = ★∼ι ⦄ c) | inj₁ ()
castVar (？_ ⦃ ★∼G = ★∼ι ⦄ c) | inj₂ (() , m)
castVar (？_ ⦃ ★∼G = ★∼⇒ ⦄ c) with castVar c
castVar (？_ ⦃ ★∼G = ★∼⇒ ⦄ c) | inj₁ ()
castVar (？_ ⦃ ★∼G = ★∼⇒ ⦄ c) | inj₂ (() , m)
castVar (？_ ⦃ ★∼G = ★∼∀ ⦄ c) with castVar c
castVar (？_ ⦃ ★∼G = ★∼∀ ⦄ c) | inj₁ ()
castVar (？_ ⦃ ★∼G = ★∼∀ ⦄ c) | inj₂ (() , m)
castVar (inst_ ⦃ Anv = Anv ⦄ ⦃ z∈A = z ⦄ c n) with castVar c
castVar (inst_ ⦃ Anv = () ⦄ ⦃ z∈A = z ⦄ c n) | inj₁ refl
castVar (inst_ ⦃ Anv = Anv ⦄ ⦃ z∈A = () ⦄ c n) | inj₂ (refl , m)

-- a left-only variable does not occur in a type below a right variable
onlyNotIn : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X A Y}
  → Φ ∋ X only → Φ ⊢ A ⊑ ＇ Y → X ∈ᵗ A → ⊥
onlyNotIn o (X⊑Y x) var-∈ = ↔-only-⊥ x o
onlyNotIn o (∀⊑ nv z q) (∈-all i) = onlyNotIn (only-only o) q i

-- no variable occurs in a type below `∀Y.Y`
belowBot : ∀ {Δ Δ′} {Ψ : Corr Δ Δ′} {A X}
  → Ψ ⊢ A ⊑ `∀ (＇ zero) → X ∈ᵗ A → ⊥
belowBot (∀⊑∀ (X⊑Y ↔-here)) (∈-all ())
belowBot (∀⊑∀ (∀⊑ nv z q)) i = onlyNotIn only-here q z
belowBot (∀⊑ nv z q) (∈-all i) = belowBot q i

-- left `∀ᶜ` into `∀X.X ⊑ ∀Y.Y`: the left source is `∀X.X` (empty)
caseAllVar : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C₁ : Ty (suc Δ)}
    {C′ A′} (c₁ : extᵐ ν ⊢ C₁ ∼ ＇ zero) (c′ : ν′ ⊢ C′ ∼ A′)
  → CastCase (∀ᶜ c₁) c′
caseAllVar c₁ c′ with castVar c₁
caseAllVar c₁ c′ | inj₁ refl = caseBotL (∀ᶜ c₁) c′
caseAllVar c₁ c′ | inj₂ (refl , inj₁ ())
caseAllVar c₁ c′ | inj₂ (refl , inj₂ ())

-- left `∀ᶜ` against a right `bot-intro`
caseAllBotIntro : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C₁ A₁ : Ty (suc Δ)}
    (c₁ : extᵐ ν ⊢ C₁ ∼ A₁)
  → CastCase (∀ᶜ c₁) (bot-intro {μ = ν′})
caseAllBotIntro c₁ d n p (∀⊑∀ (X⊑Y ↔-here)) =
  caseAllVar c₁ bot-intro d n p (∀⊑∀ (X⊑Y ↔-here))
caseAllBotIntro c₁ d n p (∀⊑∀ (∀⊑ nv z q)) =
  ⊥-elim (onlyNotIn only-here q z)
caseAllBotIntro c₁ d n p (∀⊑ nv z q) = ⊥-elim (belowBot q z)

------------------------------------------------------------------------
-- A left `bot-intro` blames
------------------------------------------------------------------------

ℰ-blameStep : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (r : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr}
  → Ml —→ blame → ℰ d n r w δ Ml Mr
ℰ-blameStep ≺ zero r w s = ℰ-zero ≺ r w
ℰ-blameStep ≺ (suc m) r w {δ} s =
  ℰ-stepL ≺ m r w {δ} s (ℰᵍ-blame ≺ m w
    {VR = λ le w′ e → 𝒱≤ ≺ le r w′ (δ ↑ᴵ e)})
ℰ-blameStep ≻ n r w {δ} s =
  ℰ-stepL ≻ n r w {δ} s
    (ℰᵍ-blame ≻ n w {VR = λ le w′ e → 𝒱≤ ≻ le r w′ (δ ↑ᴵ e)})

caseBotIntroL : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C′ A′}
    (c′ : ν′ ⊢ C′ ∼ A′)
  → CastCase (bot-intro {μ = ν}) c′
caseBotIntroL c′ d n p r w h pC pA vl vr hyp =
  ℰ-blameStep d n r w (blame-bot-intro vl)

------------------------------------------------------------------------
-- A left `id ι`
------------------------------------------------------------------------

-- against `id ★`, at `ι ⊑ ★`
caseIdι★ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {ι}
  → CastCase (id {μ = ν} (‵ ι)) (id {μ = ν′} ★)
caseIdι★ {ι = ι} d n ι⊑★ ι⊑★ w h pC pA vl vr (t , r) =
  ℰ-ids d n ι⊑★ w (‵ ι) ★ (good h) vl vr r

-- against the injection `ι!`: the right is already a value
caseIdιInj : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {ι}
    ⦃ g : ν′ ⊢ ‵ ι ∼★ ⦄ ⦃ ns : NonStar (‵ ι) ⦄
  → CastCase (id {μ = ν} (‵ ι))
      (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = g ⦄ (id (‵ ι)) ⦃ Ans = ns ⦄)
caseIdιInj ≺ zero ι⊑ι ι⊑★ w h pC pA vl vr hyp = ℰ-zero ≺ ι⊑★ w
caseIdιInj ≺ (suc m) ι⊑ι ι⊑★ w h pC pA ($ κ) vr (t , κ , refl , refl) =
  ℰ-steps? ≺ (suc m) ι⊑★ w (good h) (step (β-id ($ κ))) stay ($ κ)
    (($ κ) 《 inj 》) (refl , refl)
caseIdιInj ≻ zero ι⊑ι ι⊑★ w h pC pA vl vr hyp = ℰ-zero ≻ ι⊑★ w
caseIdιInj ≻ (suc m) ι⊑ι ι⊑★ w h pC pA ($ κ) vr (t , κ , refl , refl) =
  ℰ-steps? ≻ (suc m) ι⊑★ w (good h) (step (β-id ($ κ))) stay ($ κ)
    (($ κ) 《 inj 》) (refl , refl)

-- the projection after the injection, when the proofs that the ground
-- is not `★` are given separately
untag : ∀ {Δ} {μ ν : Env∼ Δ} {ι} {V : Term Δ}
    ⦃ g : μ ⊢ ‵ ι ∼★ ⦄ ⦃ g′ : ν ⊢★∼ ‵ ι ⦄ (ns ns′ : NonStar (‵ ι))
  → Value V
  → V ⟨ _! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = g ⦄ (id (‵ ι)) ⦃ Ans = ns ⦄ ⟩
      ⟨ ？_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = g′ ⦄ (id (‵ ι)) ⦃ Bns = ns′ ⦄ ⟩
    —→ V
untag ⦃ g ⦄ ⦃ g′ ⦄ nonstar-ι nonstar-ι v =
  tag-untag ⦃ G∼★ = g ⦄ ⦃ ★∼G = g′ ⦄ ⦃ Gns = nonstar-ι ⦄ v

-- against the projection `？ι`: the right takes the projection step
caseIdιProj : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {ι}
    ⦃ g : ν′ ⊢★∼ ‵ ι ⦄ ⦃ ns : NonStar (‵ ι) ⦄
  → CastCase (id {μ = ν} (‵ ι))
      (？_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = g ⦄ (id (‵ ι)) ⦃ Bns = ns ⦄)
caseIdιProj ≺ zero ι⊑★ ι⊑ι w h pC pA vl vr hyp = ℰ-zero ≺ ι⊑ι w
caseIdιProj ≺ (suc m) ι⊑★ ι⊑ι w h pC pA ($ κ)
    (_《_》 ($ κ′) (inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = g₀ ⦄ ⦃ Gns = ns₀ ⦄))
    (t , refl , refl) =
  ℰ-steps? ≺ (suc m) ι⊑ι w (good h) (step (β-id ($ κ)))
    (step (untag ⦃ g = g₀ ⦄ ⦃ g′ = ★∼ι ⦄ ns₀ _ ($ κ))) ($ κ) ($ κ)
    (κ , refl , refl)
caseIdιProj ≻ zero ι⊑★ ι⊑ι w h pC pA vl vr hyp = ℰ-zero ≻ ι⊑ι w
caseIdιProj ≻ (suc m) ι⊑★ ι⊑ι w h pC pA ($ κ)
    (_《_》 ($ κ′) (inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = g₀ ⦄ ⦃ Gns = ns₀ ⦄))
    (t , refl , refl) =
  ℰ-steps? ≻ (suc m) ι⊑ι w (good h) (step (β-id ($ κ)))
    (step (untag ⦃ g = g₀ ⦄ ⦃ g′ = ★∼ι ⦄ ns₀ _ ($ κ))) ($ κ) ($ κ)
    (κ , refl , refl)

------------------------------------------------------------------------
-- The row of a left `id`
------------------------------------------------------------------------

rowId : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A} (a : Atom A) {C′ A′}
    (c′ : ν′ ⊢ C′ ∼ A′)
  → CastCase (id {μ = ν} a) c′
rowId ★ (id ★) = caseId★
rowId ★ (_! c ⦃ () ⦄) d n ★⊑★ r
rowId ★ (？_ c ⦃ () ⦄) d n p ★⊑★
rowId (‵ ι) (id (‵ ι′)) d n ι⊑ι ι⊑ι = caseIdι d n ι⊑ι ι⊑ι
rowId (‵ ι) (id ★) d n ι⊑★ ι⊑★ = caseIdι★ d n ι⊑★ ι⊑★
rowId (‵ ι) (_! ⦃ Gᵍ = ‵ ι′ ⦄ ⦃ G∼★ = g ⦄ (id (‵ ι″)) ⦃ Ans = ns ⦄) d n
    ι⊑ι ι⊑★ =
  caseIdιInj ⦃ g = g ⦄ ⦃ ns = ns ⦄ d n ι⊑ι ι⊑★
rowId (‵ ι) (_! ⦃ Gᵍ = ＇ X ⦄ ()) d n ι⊑ι r
rowId (‵ ι) (_! ⦃ Gᵍ = ★⇒★ ⦄ ()) d n ι⊑ι r
rowId (‵ ι) (_! ⦃ Gᵍ = ∀★ ⦄ ((gen_ ⦃ z∈B = () ⦄ c) ne)) d n ι⊑ι r
rowId (‵ ι) (？_ ⦃ Gᵍ = ‵ ι′ ⦄ ⦃ ★∼G = g ⦄ (id (‵ ι″)) ⦃ Bns = ns ⦄) d n
    ι⊑★ ι⊑ι =
  caseIdιProj ⦃ g = g ⦄ ⦃ ns = ns ⦄ d n ι⊑★ ι⊑ι
rowId (‵ ι) (？_ ⦃ Gᵍ = ＇ X ⦄ ()) d n p ι⊑ι
rowId (‵ ι) (？_ ⦃ Gᵍ = ★⇒★ ⦄ ()) d n p ι⊑ι
rowId (‵ ι) (？_ ⦃ Gᵍ = ∀★ ⦄ ((inst_ ⦃ z∈A = () ⦄ c) ne)) d n p ι⊑ι
rowId (＇ X) (id (＇ Y)) d n (X⊑Y x) (X⊑Y y) = caseVarP d n (X⊑Y x) (X⊑Y y)
rowId (＇ X) (id ★) d n (X⊑★ o) (X⊑★ o′) = caseVarO d n (X⊑★ o) (X⊑★ o′)
rowId (＇ X) (_! c) d n (X⊑Y x) (X⊑★ o) = ⊥-elim (↔-only-⊥ x o)
rowId (＇ X) (？_ c) d n (X⊑★ o) (X⊑Y x) = ⊥-elim (↔-only-⊥ x o)

------------------------------------------------------------------------
-- The one-sided rule `⊑⟨⟩`: the statement
------------------------------------------------------------------------

module _ {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (w : World)
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) where

  -- the base case: the right's world cast at a paired variable,
  -- against the left value itself
  record VarIR {ν′ : Env∼ Δ′} {νR : Env∼ (storeR w)}
      {σR : Δ′ ⇒ˢ storeR w} (sR : SubstEnv∼ ν′ νR σR) : Set where
    field
      selfR : ∀ {Z Y′} (x : Φ ∋ Z ↔ Y′) k
        → CastRel d k (X⊑Y x) (X⊑Y x) w δ (λ V → V)
            (λ V → V ⟨ SubstEnv∼.self sR Y′ ⟩)

module _ {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (w : World)
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) where

  -- `CastHyp` without the left environment
  record CastHypR (ν′ : Env∼ Δ′) : Set₁ where
    field
      {νRʳ} : Env∼ (storeR w)
      σRʳ : Δ′ ⇒ˢ storeR w
      sRʳ : SubstEnv∼ ν′ νRʳ σRʳ
      goodʳ : GoodI δ
      freshPʳ : ∀ {Z Y′} → Φ ∋ Z ↔ Y′
        → FreshP d both w (leaf δ Z) (δl δ Z) (σRʳ Y′)
      freshOʳ : ∀ {Z} → Φ ∋ Z only → FreshO d w (leaf δ Z) (δl δ Z)
      freshRʳ : ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → FreshR d w (leaf δ Z) (σRʳ Y′)
      varʳ : ∀ {w″} (e″ : w″ ⊒ w)
        → VarIR Φ d w″ (δ ↑ᴵ e″) (renSE (ρS e″) sRʳ)

  open CastHypR public

-- the one-sided lemma at a given right cast
CastCaseR : ∀ {Δ′} {ν′ : Env∼ Δ′} {C′ A′ : Ty Δ′} → ν′ ⊢ C′ ∼ A′ → Set₁
CastCaseR {Δ′} {ν′} {C′} {A′} c′ =
  ∀ {Δ} d n {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ C′) (r : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (h : CastHypR Φ d w δ ν′)
  → PreB w (δr δ) (σRʳ h) C′ → PreB w (δr δ) (σRʳ h) A′
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱ᵀ d n p w δ Vl Vr
  → ℰ d n r w δ Vl (Vr ⟨ subst∼ (sRʳ h) c′ ⟩)

CastLemmaR : Set₁
CastLemmaR =
  ∀ {Δ′} {ν′ : Env∼ Δ′} {C′ A′ : Ty Δ′} (c′ : ν′ ⊢ C′ ∼ A′) → Eager c′
  → CastCaseR c′

------------------------------------------------------------------------
-- The one-sided rule: a right `id`
------------------------------------------------------------------------

-- the right's identity step at an atom
caseIdR : ∀ {Δ Δ′} d n {Φ : Corr Δ Δ′} {A A′} (p r : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} → GoodI δ
  → ∀ {μ : Env∼ (storeR w)} {B} (b : Atom B)
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d n p w δ Vl Vr
  → ℰ d n r w δ Vl (Vr ⟨ id {μ = μ} b ⟩)
caseIdR d n p r w {δ} g b {Vl} {Vr} vl vr a′ =
  subst (λ q → ℰ d n q w δ Vl (Vr ⟨ id b ⟩)) (⊑-unique p r)
    (ℰ-stepR? d n p w g (step (β-id vr)) vl vr a′)

rowIdR : ∀ {Δ′} {ν′ : Env∼ Δ′} {A′} (a : Atom A′)
  → CastCaseR (id {μ = ν′} a)
rowIdR ★ d n p r w h pC pA vl vr (t , a′) =
  caseIdR d n p r w (goodʳ h) ★ vl vr a′
rowIdR (‵ ι) d n p r w h pC pA vl vr (t , a′) =
  caseIdR d n p r w (goodʳ h) (‵ ι) vl vr a′
rowIdR (＇ Y) d n (∀⊑ nv z q) r w h pC pA vl vr hyp =
  ⊥-elim (onlyNotIn only-here q z)
rowIdR (＇ Y) d n (X⊑Y x) (X⊑Y y) w {δ} h pC pA vl vr (t , a′)
    with ↔-unique x y
rowIdR (＇ Y) d n (X⊑Y x) (X⊑Y .x) w {δ} h pC pA vl vr (t , a′)
    | refl =
  ℰᵍ-≡ refl (ren-refl {μ = νRʳ h} (SubstEnv∼.self (sRʳ h) Y) _)
    (ℰ-resp d n (X⊑Y x) w (↑ᴵ-refl {w = w} δ)
      (VarIR.selfR (varʳ h (⊒-refl w)) x n vl vr
        (𝒱-resp d n (X⊑Y x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a′)))

------------------------------------------------------------------------
-- The one-sided rule: a right `bot-elim` or `bot-intro`
------------------------------------------------------------------------

-- the right source `∀Y.Y` has no typed value
caseBotElimR : ∀ {Δ′} {ν′ : Env∼ Δ′} → CastCaseR (bot-elim {μ = ν′})
caseBotElimR d n p r w h pC pA vl vr (t , a) = ⊥-elim (noBotR vr t)

-- the left type is `∀X.X` (it is below `∀Y.Y`), which is below `∀★`
-- only by `bot-elim`, where the value relation is empty
caseBotIntroR : ∀ {Δ′} {ν′ : Env∼ Δ′} → CastCaseR (bot-intro {μ = ν′})
caseBotIntroR d n p (∀⊑ nv z q) w h pC pA vl vr hyp =
  ⊥-elim (belowBot q z)
caseBotIntroR d n p (∀⊑∀ (∀⊑ nv z q)) w h pC pA vl vr hyp =
  ⊥-elim (onlyNotIn only-here q z)
caseBotIntroR ≺ n bot-elim (∀⊑∀ (X⊑Y ↔-here)) w h pC pA vl vr (t , ())
caseBotIntroR ≻ n bot-elim (∀⊑∀ (X⊑Y ↔-here)) w h pC pA vl vr (t , ())
caseBotIntroR d n (∀⊑∀ (X⊑★ ())) (∀⊑∀ (X⊑Y ↔-here)) w h pC pA vl vr hyp
caseBotIntroR d n (∀⊑ () z q) (∀⊑∀ (X⊑Y ↔-here)) w h pC pA vl vr hyp

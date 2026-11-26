module proof.LR.CastInduction where

-- File Charter:
--   * The induction of the cast lemma (`proof.LR.CastLemma`,
--     `CastLemma`): well-founded recursion on the sum of the two casts'
--     sizes (`castSize`), dispatched on the left cast's head
--     (notes/logrel-dgg.md, "The cast lemma: the case table").
--   * `Below k`: the lemma at every pair of eager casts whose sizes sum
--     below k, the induction hypothesis.  `Step c c′`: the lemma at c,
--     c′ from the hypothesis below their sizes.  `CaseAt c c′ p r`: the
--     lemma at given casts and given derivations.
--   * The cases not yet proved are the fields of `Rows`, stated with
--     the induction hypothesis they may use; `castLemma` proves
--     `CastLemma` from them.  Proved and used here:
--       - the row of a left `id` (`proof.LR.CastCases`, `rowId`);
--       - a left `↦` against a right `↦` (`proof.LR.CastCases2`,
--         `case↦↦`), its hypotheses at the domains and at the
--         codomains (`↦-lt₁`, `↦-lt₂`);
--       - a left `∀ᶜ` against a right `bot-intro`
--         (`caseAllBotIntro`);
--       - a left `bot-elim` (its source is `∀X.X`, `caseBotL`) and a
--         left `bot-intro` (it blames, `caseBotIntroL`);
--       - case 6, left `∀ᶜ` against right `inst` from `∀⊑∀` to `∀⊑`
--         (`proof.LR.Case6`, `case6R`), its hypothesis at `c₁`
--         against `c₁′ [ ★/0 ]ᶜ` (`eager-close`, `castSize-case6`);
--       - a left `∀ᶜ` against a right `bot-elim` (`caseBotR`), and
--         against a right `inst` with `p = bot-elim` (source
--         `∀X.X`), or into `∀X.X ⊑ ∀★` (`caseAllVar`);
--       - a left `!` and a left `？` against a right `id ★`
--         (`proof.LR.CastCases3`, `case!★`, `case？★`), their hypothesis
--         at c against `id ★`; against `id ι`, `id Y` the precisions do
--         not exist.
--       - a left `!` against a right `!` (`proof.LR.CastCases4`,
--         `case!!`), but for `RowIdR` (a field: the right the identity
--         at its ground `★ ⇒ ★` or `∀★`, the left not);
--       - a left `inst` against a right `(inst c′) !` at `★ ⇒ ★` into
--         `⇒⊑★` (`caseInst!⇒`), its hypothesis at `inst` against `inst`.
--   * `Open↦`, `Open∀`, `Open!`, `Open!?`: the right heads still open
--     against a left `↦`, `∀ᶜ`, `!` and `？`.  A left `inst` is split by
--     the right's head: `rowInst` (`NotBang`) and `rowInst!`
--     (`OpenInst!`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; +-monoʳ-≤;
  +-monoʳ-<; n≤1+n; n<1+n)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩)
open import LR.Precision
open import LR.World
open import LR.Relation
open import LR.EagerCast using (Eager; e-id; e-↦; e-∀; e-!; e-？;
  e-inst; e-gen; e-bot-elim; e-bot-intro)
open import proof.Consistency using (castSize)
open import proof.LR.ConvLemma using (PreB)
open import proof.LR.CastLemma using (CastCase; CastLemma; CastHyp; sL;
  sR; σR)
open import proof.LR.CastSubst using (eager-close; castSize-case6)
open import proof.LR.Case6 using (case6R)
open import proof.LR.CastCases using (rowId; caseBotL; caseBotR;
  caseBotIntroL; caseAllVar; caseAllBotIntro)
open import proof.LR.CastCases2 using (case↦↦; ↦-lt₁; ↦-lt₂)
open import proof.LR.CastCases3 using (case!★; case？★)
open import proof.LR.CastCases4 using (RowIdR; case!!; caseInst!⇒)

------------------------------------------------------------------------
-- The shapes of the obligations
------------------------------------------------------------------------

-- the lemma at every pair of eager casts whose sizes sum below k
Below : ℕ → Set₁
Below k = ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A : Ty Δ}
    {C′ A′ : Ty Δ′} (c : ν ⊢ C ∼ A) (c′ : ν′ ⊢ C′ ∼ A′)
  → Eager c → Eager c′ → castSize c + castSize c′ < k → CastCase c c′

-- the lemma at two given casts, from the hypothesis below their sizes
Step : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A : Ty Δ}
    {C′ A′ : Ty Δ′} → ν ⊢ C ∼ A → ν′ ⊢ C′ ∼ A′ → Set₁
Step c c′ =
  Eager c → Eager c′ → Below (castSize c + castSize c′) → CastCase c c′

-- the lemma at two given casts and two given derivations
CaseAt : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A : Ty Δ}
    {C′ A′ : Ty Δ′} → ν ⊢ C ∼ A → ν′ ⊢ C′ ∼ A′
  → {Φ : Corr Δ Δ′} → Φ ⊢ C ⊑ C′ → Φ ⊢ A ⊑ A′ → Set₁
CaseAt {Δ} {Δ′} {ν} {ν′} {C} {A} {C′} {A′} c c′ {Φ} p r =
  ∀ d n w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (h : CastHyp Φ d w δ ν ν′)
  → PreB w (δr δ) (σR h) C′ → PreB w (δr δ) (σR h) A′
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱ᵀ d n p w δ Vl Vr
  → ℰ d n r w δ (Vl ⟨ subst∼ (sL h) c ⟩) (Vr ⟨ subst∼ (sR h) c′ ⟩)

------------------------------------------------------------------------
-- The cases not yet proved
------------------------------------------------------------------------

-- the right casts against which a left `↦` is open
Open↦ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
Open↦ (id a) = ⊤
Open↦ (c ↦ d) = ⊥
Open↦ (∀ᶜ c) = ⊤
Open↦ (c !) = ⊤
Open↦ (？ c) = ⊤
Open↦ ((inst c) B≢★) = ⊤
Open↦ ((gen c) A≢★) = ⊤
Open↦ bot-elim = ⊥
Open↦ bot-intro = ⊤

-- the right casts against which a left `∀ᶜ` is open
Open∀ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
Open∀ (id a) = ⊤
Open∀ (c ↦ d) = ⊤
Open∀ (∀ᶜ c) = ⊤
Open∀ (c !) = ⊤
Open∀ (？ c) = ⊤
Open∀ ((inst c) B≢★) = ⊥
Open∀ ((gen c) A≢★) = ⊤
Open∀ bot-elim = ⊥
Open∀ bot-intro = ⊥

-- the right casts against which a left `!` or `？` is open: all but an
-- identity (`id ★` is done; at `ι` or `Y` the precisions do not exist)
Open!? : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
Open!? (id a) = ⊥
Open!? (c ↦ d) = ⊤
Open!? (∀ᶜ c) = ⊤
Open!? (c !) = ⊤
Open!? (？ c) = ⊤
Open!? ((inst c) B≢★) = ⊤
Open!? ((gen c) A≢★) = ⊤
Open!? bot-elim = ⊤
Open!? bot-intro = ⊤

-- against a left `!`, a right `!` is done too (`case!!`), but for
-- `RowIdR`
Open! : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
Open! (id a) = ⊥
Open! (c ↦ d) = ⊤
Open! (∀ᶜ c) = ⊤
Open! (c !) = ⊥
Open! (？ c) = ⊤
Open! ((inst c) B≢★) = ⊤
Open! ((gen c) A≢★) = ⊤
Open! bot-elim = ⊤
Open! bot-intro = ⊤

-- the right casts other than an injection
NotBang : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ} → μ ⊢ A ∼ B → Set
NotBang (id a) = ⊤
NotBang (c ↦ d) = ⊤
NotBang (∀ᶜ c) = ⊤
NotBang (c !) = ⊥
NotBang (？ c) = ⊤
NotBang ((inst c) B≢★) = ⊤
NotBang ((gen c) A≢★) = ⊤
NotBang bot-elim = ⊤
NotBang bot-intro = ⊤

-- a left `inst` against a right `c′ !`: open except for `(inst _) !`
-- at `★ ⇒ ★` into `⇒⊑★` (`caseInst!⇒`)
OpenInst! : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : Env∼ Δ′} {C′ G′ : Ty Δ′} {B}
  → Ground G′ → μ ⊢ C′ ∼ G′ → Φ ⊢ B ⊑ ★ → Set
OpenInst! ★⇒★ ((inst c) n) (⇒⊑★ q₁ q₂) = ⊥
OpenInst! g c r = ⊤

record Rows : Set₁ where
  field
    -- left `↦`, against the right casts still open (`Open↦`)
    row↦ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A A′ B B′ : Ty Δ}
        {C′ D′ : Ty Δ′} (c : flipᵐ ν ⊢ A′ ∼ A) (d : ν ⊢ B ∼ B′)
        (c′ : ν′ ⊢ C′ ∼ D′)
      → Open↦ c′ → Step (c ↦ d) c′
    -- left `∀ᶜ`, against the right casts still open (`Open∀`)
    row∀ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A B : Ty (suc Δ)}
        {C′ D′ : Ty Δ′} (c : extᵐ ν ⊢ A ∼ B) (c′ : ν′ ⊢ C′ ∼ D′)
      → Open∀ c′ → Step (∀ᶜ c) c′
    -- left `∀ᶜ` against right `inst`, X paired, at `∀⊑∀` to `∀⊑∀`
    -- (the right's binder instantiated, the target's paired)
    ∀inst∀ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C₁ A₁ : Ty (suc Δ)}
        {C₁′ B₁ : Ty (suc Δ′)} (c₁ : extᵐ ν ⊢ C₁ ∼ A₁)
        ⦃ Anv′ : NonVar C₁′ ⦄ ⦃ z′ : zero ∈ᵗ C₁′ ⦄
        (c₁′ : instᵐ ν′ ⊢ C₁′ ∼ ⇑ᵗ (`∀ B₁)) (B≢★ : `∀ B₁ ≢ ★)
      → Eager c₁ → Eager c₁′
      → Below (castSize (∀ᶜ c₁) + castSize ((inst c₁′) B≢★))
      → ∀ {Φ : Corr Δ Δ′} (p₁ : pair Φ ⊢ C₁ ⊑ C₁′) (r₁ : pair Φ ⊢ A₁ ⊑ B₁)
      → CaseAt (∀ᶜ c₁) ((inst c₁′) B≢★) (∀⊑∀ p₁) (∀⊑∀ r₁)
    -- left `∀ᶜ` against right `inst`, X left-only
    ∀instOnly : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C₁ A₁ : Ty (suc Δ)}
        {C₁′ : Ty (suc Δ′)} {B′ : Ty Δ′} (c₁ : extᵐ ν ⊢ C₁ ∼ A₁)
        ⦃ Anv′ : NonVar C₁′ ⦄ ⦃ z′ : zero ∈ᵗ C₁′ ⦄
        (c₁′ : instᵐ ν′ ⊢ C₁′ ∼ ⇑ᵗ B′) (B≢★ : B′ ≢ ★)
      → Eager c₁ → Eager c₁′
      → Below (castSize (∀ᶜ c₁) + castSize ((inst c₁′) B≢★))
      → ∀ {Φ : Corr Δ Δ′} (Cnv : NonVar C₁) (z : zero ∈ᵗ C₁)
          (q : only Φ ⊢ C₁ ⊑ `∀ C₁′) (r : Φ ⊢ `∀ A₁ ⊑ B′)
      → CaseAt (∀ᶜ c₁) ((inst c₁′) B≢★) (∀⊑ Cnv z q) r
    -- left `!`, against the right casts still open (`Open!`)
    row! : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A G : Ty Δ}
        {C′ D′ : Ty Δ′} ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
        (c : ν ⊢ A ∼ G) ⦃ Ans : NonStar A ⦄ (c′ : ν′ ⊢ C′ ∼ D′)
      → Open! c′ → Step (c !) c′
    -- left `c !`, c not the identity, against right `(idᵍ G) !` at
    -- `★ ⇒ ★` or `∀★`
    row!id : RowIdR
    -- left `？`, against the right casts still open (`Open!?`)
    row？ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {G B : Ty Δ}
        {C′ D′ : Ty Δ′} ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
        (c : ν ⊢ G ∼ B) ⦃ Bns : NonStar B ⦄ (c′ : ν′ ⊢ C′ ∼ D′)
      → Open!? c′ → Step (？ c) c′
    -- left `inst`, against every right cast but an injection
    rowInst : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty (suc Δ)}
        {B : Ty Δ} {C′ D′ : Ty Δ′} ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
        (c : instᵐ ν ⊢ A ∼ ⇑ᵗ B) (B≢★ : B ≢ ★) (c′ : ν′ ⊢ C′ ∼ D′)
      → NotBang c′ → Step ((inst c) B≢★) c′
    -- left `inst` against a right injection, still open (`OpenInst!`)
    rowInst! : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty (suc Δ)}
        {B : Ty Δ} {C′ G′ : Ty Δ′} ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
        (c : instᵐ ν ⊢ A ∼ ⇑ᵗ B) (B≢★ : B ≢ ★) (Hᵍ : Ground G′)
        ⦃ H∼★ : ν′ ⊢ G′ ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ G′) ⦃ Cns : NonStar C′ ⦄
      → Eager c → Eager c′
      → Below (castSize ((inst c) B≢★)
          + castSize (_! ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄))
      → ∀ {Φ : Corr Δ Δ′} (p : Φ ⊢ `∀ A ⊑ C′) (r : Φ ⊢ B ⊑ ★)
      → OpenInst! Hᵍ c′ r
      → CaseAt ((inst c) B≢★)
          (_! ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄) p r
    -- left `gen`, against every right cast
    rowGen : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty Δ}
        {B : Ty (suc Δ)} {C′ D′ : Ty Δ′} ⦃ Bnv : NonVar B ⦄
        ⦃ z∈B : zero ∈ᵗ B ⦄ (c : genᵐ ν ⊢ ⇑ᵗ A ∼ B) (A≢★ : A ≢ ★)
        (c′ : ν′ ⊢ C′ ∼ D′)
      → Step ((gen c) A≢★) c′

------------------------------------------------------------------------
-- The induction
------------------------------------------------------------------------

module _ (rows : Rows) where

  open Rows rows

  -- a left `∀ᶜ`, by the right cast's head; against `inst`, by the
  -- shapes of the derivations
  step∀ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A B : Ty (suc Δ)}
      {C′ D′ : Ty Δ′} (c : extᵐ ν ⊢ A ∼ B) (c′ : ν′ ⊢ C′ ∼ D′)
    → Step (∀ᶜ c) c′
  step∀ c c′@(id a) = row∀ c c′ tt
  step∀ c c′@(c₁′ ↦ c₂′) = row∀ c c′ tt
  step∀ c c′@(∀ᶜ c₁′) = row∀ c c′ tt
  step∀ c c′@(c₁′ !) = row∀ c c′ tt
  step∀ c c′@(？ c₁′) = row∀ c c′ tt
  step∀ c c′@((gen c₁′) A≢★) = row∀ c c′ tt
  step∀ c c′@bot-elim e e′ ih = caseBotR (∀ᶜ c) c′
  step∀ c c′@bot-intro e e′ ih = caseAllBotIntro c
  step∀ c ((inst_ ⦃ Anv′ ⦄ ⦃ z′ ⦄ c₁′) B≢★) (e-∀ e) (e-inst e′) ih
      d n (∀⊑∀ p₁) (∀⊑ Anv z r₁) w h pC pA vl vr hyp =
    case6R c c₁′ B≢★ d n p₁ Anv z r₁ w h pC pA vl vr
      (ih c (c₁′ [ ★/0 ]ᶜ) e (eager-close c₁′ e′)
        (castSize-case6 c c₁′ B≢★))
      hyp
  step∀ c ((inst c₁′) B≢★) (e-∀ e) (e-inst e′) ih
      d n (∀⊑∀ p₁) (∀⊑∀ r₁) w h pC pA vl vr hyp =
    ∀inst∀ c c₁′ B≢★ e e′ ih p₁ r₁ d n w h pC pA vl vr hyp
  step∀ c c′@((inst c₁′) B≢★) e e′ ih d n (∀⊑∀ p₁) bot-elim =
    caseAllVar c c′ d n (∀⊑∀ p₁) bot-elim
  step∀ c ((inst c₁′) B≢★) (e-∀ e) (e-inst e′) ih
      d n (∀⊑∀ p₁) ∀★⊑★ w h pC pA vl vr hyp = ⊥-elim (B≢★ refl)
  step∀ c ((inst c₁′) B≢★) (e-∀ e) (e-inst e′) ih
      d n (∀⊑∀ p₁) (∀⊑★ ns r₁) w h pC pA vl vr hyp = ⊥-elim (B≢★ refl)
  step∀ c ((inst c₁′) B≢★) (e-∀ e) (e-inst e′) ih
      d n (∀⊑∀ p₁) bot⊑★ w h pC pA vl vr hyp = ⊥-elim (B≢★ refl)
  step∀ c ((inst c₁′) B≢★) (e-∀ e) (e-inst e′) ih
      d n (∀⊑ Cnv z q) r w h pC pA vl vr hyp =
    ∀instOnly c c₁′ B≢★ e e′ ih Cnv z q r d n w h pC pA vl vr hyp
  step∀ c c′@((inst c₁′) B≢★) e e′ ih d n p@bot-elim r =
    caseBotL (∀ᶜ c) c′ d n p r

  -- a left `↦`, by the right cast's head
  step↦ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A A′ B B′ : Ty Δ}
      {C′ D′ : Ty Δ′} (c : flipᵐ ν ⊢ A′ ∼ A) (d : ν ⊢ B ∼ B′)
      (c′ : ν′ ⊢ C′ ∼ D′)
    → Step (c ↦ d) c′
  step↦ c d c′@(id a) = row↦ c d c′ tt
  step↦ c d (c₁′ ↦ d₁′) (e-↦ e₁ e₂) (e-↦ e₁′ e₂′) ih =
    case↦↦ c d c₁′ d₁′
      (ih c c₁′ e₁ e₁′
        (↦-lt₁ (castSize c) (castSize d) (castSize c₁′) (castSize d₁′)))
      (ih d d₁′ e₂ e₂′
        (↦-lt₂ (castSize c) (castSize d) (castSize c₁′) (castSize d₁′)))
  step↦ c d c′@(∀ᶜ c₁′) = row↦ c d c′ tt
  step↦ c d c′@(c₁′ !) = row↦ c d c′ tt
  step↦ c d c′@(？ c₁′) = row↦ c d c′ tt
  step↦ c d c′@((inst c₁′) B≢★) = row↦ c d c′ tt
  step↦ c d c′@((gen c₁′) A≢★) = row↦ c d c′ tt
  step↦ c d c′@bot-elim e e′ ih = caseBotR (c ↦ d) c′
  step↦ c d c′@bot-intro = row↦ c d c′ tt

  -- a left `!`, by the right cast's head
  step! : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A G : Ty Δ}
      {C′ D′ : Ty Δ′} ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
      (c : ν ⊢ A ∼ G) ⦃ Ans : NonStar A ⦄ (c′ : ν′ ⊢ C′ ∼ D′)
    → Step (c !) c′
  step! c (id ★) (e-! e) e′ ih =
    case!★ c (ih c (id ★) e e-id ≤-refl)
  step! c (id (‵ ι)) e e′ ih d n p ()
  step! c (id (＇ Y)) e e′ ih d n p ()
  step! c c′@(c₁′ ↦ d₁′) = row! c c′ tt
  step! c c′@(∀ᶜ c₁′) = row! c c′ tt
  step! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄
      (_! ⦃ Gᵍ = g′ ⦄ ⦃ G∼★ = s′ ⦄ c₁′ ⦃ Ans = a′ ⦄) (e-! e) (e-! e′) ih =
    case!! row!id ⦃ Gᵍ = g ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ g′ ⦃ H∼★ = s′ ⦄
      c₁′ ⦃ Cns = a′ ⦄
      (ih c c₁′ e e′
        (s≤s (+-monoʳ-≤ (castSize c) (n≤1+n (castSize c₁′)))))
  step! c c′@(？ c₁′) = row! c c′ tt
  step! c c′@((inst c₁′) B≢★) = row! c c′ tt
  step! c c′@((gen c₁′) A≢★) = row! c c′ tt
  step! c c′@bot-elim = row! c c′ tt
  step! c c′@bot-intro = row! c c′ tt

  -- a left `？`, by the right cast's head
  step？ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {G B : Ty Δ}
      {C′ D′ : Ty Δ′} ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
      (c : ν ⊢ G ∼ B) ⦃ Bns : NonStar B ⦄ (c′ : ν′ ⊢ C′ ∼ D′)
    → Step (？ c) c′
  step？ c (id ★) (e-？ e) e′ ih =
    case？★ c (ih c (id ★) e e-id ≤-refl)
  step？ c (id (‵ ι)) e e′ ih d n ()
  step？ c (id (＇ Y)) e e′ ih d n ()
  step？ c c′@(c₁′ ↦ d₁′) = row？ c c′ tt
  step？ c c′@(∀ᶜ c₁′) = row？ c c′ tt
  step？ c c′@(c₁′ !) = row？ c c′ tt
  step？ c c′@(？ c₁′) = row？ c c′ tt
  step？ c c′@((inst c₁′) B≢★) = row？ c c′ tt
  step？ c c′@((gen c₁′) A≢★) = row？ c c′ tt
  step？ c c′@bot-elim = row？ c c′ tt
  step？ c c′@bot-intro = row？ c c′ tt

  -- a left `inst` against a right injection, by its ground, its cast
  -- and the target precision
  stepInst! : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty (suc Δ)}
      {B : Ty Δ} {C′ G′ : Ty Δ′} ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
      (c : instᵐ ν ⊢ A ∼ ⇑ᵗ B) (B≢★ : B ≢ ★) (Hᵍ : Ground G′)
      ⦃ H∼★ : ν′ ⊢ G′ ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ G′) ⦃ Cns : NonStar C′ ⦄
    → Step ((inst c) B≢★) (_! ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄)
  stepInst! c B≢★ (＇ Y) ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p r =
    rowInst! c B≢★ (＇ Y) ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ (‵ ι) ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p r =
    rowInst! c B≢★ (‵ ι) ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ∀★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p r =
    rowInst! c B≢★ ∀★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ (id ())
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@(c₁′ ↦ d₁′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p r =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@(？ c₁′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p r =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = ⇒∼★ ⦄ (inst_ ⦃ Anv′ ⦄ ⦃ z′ ⦄ c₁′ n′)
      ⦃ Cns = a′ ⦄ (e-inst e) (e-! (e-inst e′)) ih d n p (⇒⊑★ q₁ q₂) =
    caseInst!⇒ c B≢★ ⦃ Anv′ = Anv′ ⦄ ⦃ z′ = z′ ⦄ c₁′ n′ ⦃ Cns = a′ ⦄
      (ih ((inst c) B≢★) ((inst c₁′) n′) (e-inst e) (e-inst e′)
        (+-monoʳ-< (castSize ((inst c) B≢★))
          (n<1+n (castSize ((inst c₁′) n′)))))
      d n p q₁ q₂
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@★⊑★ =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@ι⊑★ =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@(X⊑★ o) =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@(∀⊑ a z q) =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@∀★⊑★ =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@(∀⊑★ ns q) =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n
  stepInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′@((inst c₁′) n′) ⦃ Cns = a′ ⦄
      (e-inst e) (e-! e′) ih d n p
      r@bot⊑★ =
    rowInst! c B≢★ ★⇒★ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ e e′ ih p r tt
      d n

  -- a left `inst`, by the right cast's head
  stepInst : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty (suc Δ)}
      {B : Ty Δ} {C′ D′ : Ty Δ′} ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
      (c : instᵐ ν ⊢ A ∼ ⇑ᵗ B) (B≢★ : B ≢ ★) (c′ : ν′ ⊢ C′ ∼ D′)
    → Step ((inst c) B≢★) c′
  stepInst c B≢★ c′@(id a) = rowInst c B≢★ c′ tt
  stepInst c B≢★ c′@(c₁′ ↦ d₁′) = rowInst c B≢★ c′ tt
  stepInst c B≢★ c′@(∀ᶜ c₁′) = rowInst c B≢★ c′ tt
  stepInst c B≢★ (_! ⦃ Gᵍ = g′ ⦄ ⦃ G∼★ = s′ ⦄ c₁′ ⦃ Ans = a′ ⦄) =
    stepInst! c B≢★ g′ ⦃ H∼★ = s′ ⦄ c₁′ ⦃ Cns = a′ ⦄
  stepInst c B≢★ c′@(？ c₁′) = rowInst c B≢★ c′ tt
  stepInst c B≢★ c′@((inst c₁′) n′) = rowInst c B≢★ c′ tt
  stepInst c B≢★ c′@((gen c₁′) n′) = rowInst c B≢★ c′ tt
  stepInst c B≢★ c′@bot-elim = rowInst c B≢★ c′ tt
  stepInst c B≢★ c′@bot-intro = rowInst c B≢★ c′ tt

  -- the lemma at two casts, by the left cast's head
  step : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A : Ty Δ}
      {C′ A′ : Ty Δ′} (c : ν ⊢ C ∼ A) (c′ : ν′ ⊢ C′ ∼ A′)
    → Step c c′
  step (id a) c′ e e′ ih = rowId a c′
  step (c ↦ d) c′ = step↦ c d c′
  step (∀ᶜ c) c′ = step∀ c c′
  step (c !) c′ = step! c c′
  step (？ c) c′ = step？ c c′
  step ((inst c) B≢★) c′ = stepInst c B≢★ c′
  step ((gen c) A≢★) c′ = rowGen c A≢★ c′
  step bot-elim c′ e e′ ih = caseBotL bot-elim c′
  step bot-intro c′ e e′ ih = caseBotIntroL c′

  -- the hypothesis below every bound, by induction on the bound
  below : ∀ k → Below k
  below zero c c′ e e′ ()
  below (suc k) c c′ e e′ (s≤s le) =
    step c c′ e e′ (λ d d′ ed ed′ lt → below k d d′ ed ed′ (≤-trans lt le))

  castLemma : CastLemma
  castLemma c c′ e e′ = step c c′ e e′ (below (castSize c + castSize c′))

module proof.DGG.notes.ForallBoundaryFixes where

-- File Charter:
--   * PROPOSED FIXES for the two open items of ForallBoundaryRisks.md
--     (R3, R2); findings in ForallBoundaryFixes.md.  NOT a Def module,
--     not imported by All.agda.  Works against ∀⊑⟪+⟫ with D22's
--     `NonVar A`/`0 ∈ᵗ A` premises (0f83de9f).
--   * §1 (R3) THE SHADOWING PREMISE WORLD `W ⊕⁺ˢ m ^ β`: as `W ⊕⁺ m ^ β`,
--     but every pair whose right member is β is dropped (from ϱᵍ and
--     ϱˡ) before the lexical pair (0, β) is added.
--   * §2 renaming lemmas: the reading `_⊢_~_` along a renaming of name
--     POSITIONS, and type imprecision along a mark-respecting renaming.
--   * §3 THE WELL-FORMEDNESS LEMMA `wf-⊕⁺ˢ : WfWorld W → names Δ′ ∌ʳ β
--     → Δ′ ∋rep β := ★ → WfWorld (W ⊕⁺ˢ m ^ β)`; both hypotheses come
--     from ∀⊑⟪+⟫'s own premises (`wf-premise`).
--   * §4 a LOCAL COPY of the relation, `_∣_⊢_⊑_∶_` with the same
--     constructor names, whose ∀⊑⟪+⟫ reads `W ⊕⁺ˢ m ^ β`.
--   * §5 (R3, b) the five existing ∀⊑⟪+⟫ derivations (p3-inst = ch-x0,
--     cg-x0, c2-x0, c12-x0), copied verbatim into the local relation.
--   * §6 (R3, c) L3c/R3c: the pair before and after the left's TyBeta;
--     the premise world after it is well formed under ⊕⁺ˢ and is not
--     under ⊕⁺.
--   * §7 (R3, beyond) L3d/R3d: BOTH copies instantiated on the left;
--     the second catch-up gives αᴿ a second left partner (D13).
--   * §8 (R2) L2c/R2c: the pair at the right's TyBeta (`r2c-pre`) and
--     after the right's Merge with the left unmoved, derived twice:
--     (A) with ∀⊑⟪+⟫ as it is (`r2c-post-A`, premise N ⊑ merged), and
--     (B) with the candidate `∀⊑⟪+⟫ᵃ` (`r2c-post-B`, premise read after
--     the left's own administrative Merge).
--   * §9 (R2) the statements: `allocᴿ-⊕⁺ˢ` (proved), `InstExpand`
--     (left-expansion), `B-admissible` (B follows from A + InstExpand,
--     proved), and the child `SimBackInstX` (statement only).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; head; drop)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction
  using (InstX; inst-Λ; inst-gen; _⊢_-→_∣_; _⊢_-→*_; done; _then_)
open import Data.Unit using (⊤; tt)
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision
  using (Lit; lit-$; lit-true; lit-false; CastTy; cast-ty; NuTy; BdyTy;
         bdy-ty; NuConversionImp; BdyConversionImp; ⟪⟫-inv; cast-inv; ν-inv)
open import proof.Ctx using (renameᵗ-fuse; renameᵗ-cong; renameᵗ-⇑;
  ∋ˡ-ren; ∋ˡ-ren⁻; same-ren)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-L⇔; ev-noneᴿ; ev-done; applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms; eval-sound)
open import examples.CambridgeExamples using (I; instI; genI; C2-L; C12-L)
open import examples.ImprecisionExamples using (L1)
open import examples.TermImprecisionExamples
  using (idX; revX; ℕ⊑★; 5⟨ℕ!⟩; Θ₀; L1′; ΔL; ΔR; W₁; Wᵢ₁; Wᵢ₁-int;
         Wᵢ₁-wf; bL-ty; bR-ty; bLR-conv; revX⊑revX; νL-ty; W₃; R3′)
open import examples.TermImprecisionRebaseExamples
  using (id★↦; id★→; tagX↦; ∀id⊑★; ∀id⊑∀id; ★⇒★; ℕ⇒ℕ; ℕ⇒ℕ⊑★⇒★; id★→⊑id★→;
         X⇒X⊑★⇒★; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty; id★↦ᴿ-ty; ΛidX-⊢; Cg-R₂;
         Wg⁺; Wg⁻-int; Wg⁻-wf; I★genI-⊢; C2-L-ν-ty; W2⁺; W2⁻-int; W2⁻-wf;
         W2⁺-conv; I★⁻ᴸ-ty; tagᴸ-ty; C12-R₂; C12-ν₂-ty; genIᴿ-ty; Wν₂;
         Wν₂-conv)
open import proof.DGG.notes.ForallBoundaryRisks
  using (L2c-⊢; R2c-⊢; L3c-⊢; R3c-⊢)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The shadowing premise world
------------------------------------------------------------------------

-- drop every pair whose right member is β
dropᴿ : RVar → RepRel → RepRel
dropᴿ β [] = []
dropᴿ β ((α , β′) ∷ ϱ) with β′ ≟ β
dropᴿ β ((α , β′) ∷ ϱ) | yes _ = dropᴿ β ϱ
dropᴿ β ((α , β′) ∷ ϱ) | no _  = (α , β′) ∷ dropᴿ β ϱ

-- the premise world of ∀⊑⟪+⟫, PROPOSED: the boundary's lexical pair
-- (0, β) shadows every pair β had outside
infixl 6 _⊕⁺ˢ_^_
_⊕⁺ˢ_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕⁺ˢ m ^ β =
  world (m ∷ μ) (keep (relabel suc η)) (keep η′)
        (dropᴿ β (shiftᴸ ϱᵍ)) ((zero , β) ∷ dropᴿ β (shiftᴸ ϱˡ))

drop-keep : ∀ {β α β′} (ϱ : RepRel) → ϱ ∋ᵨ α ⇔ β′ → β′ ≢ β
  → dropᴿ β ϱ ∋ᵨ α ⇔ β′
drop-keep {β} ((a , b) ∷ ϱ) here⇔ ne with b ≟ β
drop-keep {β} ((a , b) ∷ ϱ) here⇔ ne | yes e = ⊥-elim (ne e)
drop-keep {β} ((a , b) ∷ ϱ) here⇔ ne | no _  = here⇔
drop-keep {β} ((a , b) ∷ ϱ) (there⇔ x) ne with b ≟ β
drop-keep {β} ((a , b) ∷ ϱ) (there⇔ x) ne | yes _ = drop-keep ϱ x ne
drop-keep {β} ((a , b) ∷ ϱ) (there⇔ x) ne | no _  =
  there⇔ (drop-keep ϱ x ne)

drop-sound : ∀ {β α β′} (ϱ : RepRel) → dropᴿ β ϱ ∋ᵨ α ⇔ β′
  → (ϱ ∋ᵨ α ⇔ β′) × (β′ ≢ β)
drop-sound {β} ((a , b) ∷ ϱ) x with b ≟ β
drop-sound {β} ((a , b) ∷ ϱ) x | yes _ with drop-sound ϱ x
drop-sound {β} ((a , b) ∷ ϱ) x | yes _ | y , ne = there⇔ y , ne
drop-sound {β} ((a , b) ∷ ϱ) here⇔ | no ne = here⇔ , ne
drop-sound {β} ((a , b) ∷ ϱ) (there⇔ x) | no _ with drop-sound ϱ x
drop-sound {β} ((a , b) ∷ ϱ) (there⇔ x) | no _ | y , ne = there⇔ y , ne

shiftᴸ-∋ : ∀ {ϱ α β′} → ϱ ∋ᵨ α ⇔ β′ → shiftᴸ ϱ ∋ᵨ suc α ⇔ β′
shiftᴸ-∋ here⇔      = here⇔
shiftᴸ-∋ (there⇔ x) = there⇔ (shiftᴸ-∋ x)

shiftᴸ-∋⁻ : ∀ {a β′} (ϱ : RepRel) → shiftᴸ ϱ ∋ᵨ a ⇔ β′
  → ∃[ α ] ((a ≡ suc α) × (ϱ ∋ᵨ α ⇔ β′))
shiftᴸ-∋⁻ ((α , b) ∷ ϱ) here⇔ = α , refl , here⇔
shiftᴸ-∋⁻ ((α , b) ∷ ϱ) (there⇔ x) with shiftᴸ-∋⁻ ϱ x
shiftᴸ-∋⁻ ((α , b) ∷ ϱ) (there⇔ x) | α′ , eq , y = α′ , eq , there⇔ y

module _ {W : World Δ Δ′} {m : VarImp} {β : RVar} where

  -- a pair of W whose right member is not β survives, shifted
  paired-⊕⁺ˢ : ∀ {α β′} → Paired W α β′ → β′ ≢ β
    → Paired (W ⊕⁺ˢ m ^ β) (suc α) β′
  paired-⊕⁺ˢ (inj₁ x) ne = inj₁ (drop-keep (shiftᴸ (ϱᵍʷ W)) (shiftᴸ-∋ x) ne)
  paired-⊕⁺ˢ (inj₂ x) ne =
    inj₂ (there⇔ (drop-keep (shiftᴸ (ϱˡʷ W)) (shiftᴸ-∋ x) ne))

  -- ... and every pair of the premise world is (0, β) or such a pair
  paired-⊕⁺ˢ⁻ : ∀ {a β′} → Paired (W ⊕⁺ˢ m ^ β) a β′
    → ((a ≡ zero) × (β′ ≡ β))
      ⊎ (∃[ α ] ((a ≡ suc α) × Paired W α β′ × (β′ ≢ β)))
  paired-⊕⁺ˢ⁻ (inj₁ x) with drop-sound (shiftᴸ (ϱᵍʷ W)) x
  paired-⊕⁺ˢ⁻ (inj₁ x) | y , ne with shiftᴸ-∋⁻ (ϱᵍʷ W) y
  paired-⊕⁺ˢ⁻ (inj₁ x) | y , ne | α , eq , z = inj₂ (α , eq , inj₁ z , ne)
  paired-⊕⁺ˢ⁻ (inj₂ here⇔) = inj₁ (refl , refl)
  paired-⊕⁺ˢ⁻ (inj₂ (there⇔ x)) with drop-sound (shiftᴸ (ϱˡʷ W)) x
  paired-⊕⁺ˢ⁻ (inj₂ (there⇔ x)) | y , ne with shiftᴸ-∋⁻ (ϱˡʷ W) y
  paired-⊕⁺ˢ⁻ (inj₂ (there⇔ x)) | y , ne | α , eq , z =
    inj₂ (α , eq , inj₂ z , ne)

------------------------------------------------------------------------
-- 2. Renaming lemmas
------------------------------------------------------------------------

-- the reading of an ordinary type along a renaming of name positions
PosRen : TyCtx → TyCtx → Renameᵗ → Set
PosRen η η′ ρ = ∀ {X α} → η ∋ˡ X := α → η′ ∋ˡ ρ X := α

pos-ext : ∀ {η′ ρ} (η : TyCtx) → PosRen η η′ ρ
  → PosRen (zero ∷ shiftReps η) (zero ∷ shiftReps η′) (extᵗ ρ)
pos-ext η h here = here
pos-ext η h (there d) with ∋ˡ-ren⁻ suc η d
pos-ext η h (there d) | α , d′ , refl = there (∋ˡ-ren suc (h d′))

same-pos : ∀ {η η′ ρ A R} → PosRen η η′ ρ → η ⊢ A ~ R
  → η′ ⊢ renameᵗ ρ A ~ R
same-pos h (same-var d)   = same-var (h d)
same-pos h same-ℕ         = same-ℕ
same-pos h same-𝔹         = same-𝔹
same-pos h same-★         = same-★
same-pos h (same-⇒ p q)   = same-⇒ (same-pos h p) (same-pos h q)
same-pos {η = η} h (same-∀ p) = same-∀ (same-pos (pos-ext η h) p)

-- type imprecision along a renaming that keeps every X⊑★ mark
MarkRen : ImpEnv → ImpEnv → Renameᵗ → Set
MarkRen μ μ′ ρ = ∀ {X} → μ ∋ˡ X := X⊑★ → μ′ ∋ˡ ρ X := X⊑★

mark-ext : ∀ {μ μ′ ρ} → MarkRen μ μ′ ρ
  → MarkRen (extᵐ μ) (extᵐ μ′) (extᵗ ρ)
mark-ext h (there d) = there (h d)

mark-inst : ∀ {μ μ′ ρ} → MarkRen μ μ′ ρ
  → MarkRen (instᵐ μ) (instᵐ μ′) (extᵗ ρ)
mark-inst h here      = here
mark-inst h (there d) = there (h d)

∈ᵗ-ren : ∀ {X A} (ρ : Renameᵗ) → X ∈ᵗ A → ρ X ∈ᵗ renameᵗ ρ A
∈ᵗ-ren ρ ∈-var    = ∈-var
∈ᵗ-ren ρ (∈-⇒ˡ p) = ∈-⇒ˡ (∈ᵗ-ren ρ p)
∈ᵗ-ren ρ (∈-⇒ʳ p) = ∈-⇒ʳ (∈ᵗ-ren ρ p)
∈ᵗ-ren ρ (∈-∀ p)  = ∈-∀ (∈ᵗ-ren (extᵗ ρ) p)

nonvar-ren : ∀ {A} (ρ : Renameᵗ) → NonVar A → NonVar (renameᵗ ρ A)
nonvar-ren ρ nv-ℕ = nv-ℕ
nonvar-ren ρ nv-𝔹 = nv-𝔹
nonvar-ren ρ nv-★ = nv-★
nonvar-ren ρ nv-⇒ = nv-⇒
nonvar-ren ρ nv-∀ = nv-∀

nonstar-ren : ∀ {A} (ρ : Renameᵗ) → NonStar A → NonStar (renameᵗ ρ A)
nonstar-ren ρ ns-var = ns-var
nonstar-ren ρ ns-ℕ   = ns-ℕ
nonstar-ren ρ ns-𝔹   = ns-𝔹
nonstar-ren ρ ns-⇒   = ns-⇒
nonstar-ren ρ ns-∀   = ns-∀

⊑-ren : ∀ {μ μ′ ρ A B} → MarkRen μ μ′ ρ → μ ⊢ A ⊑ B
  → μ′ ⊢ renameᵗ ρ A ⊑ renameᵗ ρ B
⊑-ren h ★⊑★            = ★⊑★
⊑-ren h (ι⊑ι base-ℕ)   = ι⊑ι base-ℕ
⊑-ren h (ι⊑ι base-𝔹)   = ι⊑ι base-𝔹
⊑-ren h X⊑X            = X⊑X
⊑-ren h (⇒⊑⇒ p q)      = ⇒⊑⇒ (⊑-ren h p) (⊑-ren h q)
⊑-ren h (∀⊑∀ p)        = ∀⊑∀ (⊑-ren (mark-ext h) p)
⊑-ren h (⇒⊑★ p q)      = ⇒⊑★ (⊑-ren h p) (⊑-ren h q)
⊑-ren h (ι⊑★ base-ℕ)   = ι⊑★ base-ℕ
⊑-ren h (ι⊑★ base-𝔹)   = ι⊑★ base-𝔹
⊑-ren h (X⊑★ d)        = X⊑★ (h d)
⊑-ren {μ′ = μ′} {ρ = ρ} {A = `∀ A} {B = B} h (∀⊑ nv occ p) =
  ∀⊑ (nonvar-ren (extᵗ ρ) nv) (∈ᵗ-ren (extᵗ ρ) occ)
     (subst₂ (instᵐ μ′ ⊢_⊑_) refl (renameᵗ-⇑ ρ B) (⊑-ren (mark-inst h) p))
⊑-ren h ∀★⊑★           = ∀★⊑★
⊑-ren {ρ = ρ} h (∀⊑★ ns p) =
  ∀⊑★ (nonstar-ren (extᵗ ρ) ns) (⊑-ren (mark-ext h) p)
⊑-ren h bot-elim       = bot-elim
⊑-ren h bot⊑★          = bot⊑★

emb-relabel : ∀ {η Ω} (f : RVar → RVar) (ι : η ↪ Ω) (X : ℕ)
  → emb (relabel f ι) X ≡ emb ι X
emb-relabel f []↪      X       = refl
emb-relabel f (keep ι) zero    = refl
emb-relabel f (keep ι) (suc X) = cong suc (emb-relabel f ι X)
emb-relabel f (skip ι) X       = cong suc (emb-relabel f ι X)

------------------------------------------------------------------------
-- 3. The well-formedness lemma
------------------------------------------------------------------------

joint-⊕⁺ˢ : ∀ {P Q : RVar → RVar → Set} {β ns ns′ Ω}
    {ι : ns ↪ Ω} {ι′ : ns′ ↪ Ω}
  → (∀ {α β′} → P α β′ → β′ ≢ β → Q (suc α) β′)
  → ns′ ∌ʳ β
  → Joint P ι ι′
  → Joint Q (relabel suc ι) ι′
joint-⊕⁺ˢ h fr joint[] = joint[]
joint-⊕⁺ˢ h (fresh∷ ne fr) (both p j) =
  both (h p (λ e → ne (sym e))) (joint-⊕⁺ˢ h fr j)
joint-⊕⁺ˢ h fr (left-only j) = left-only (joint-⊕⁺ˢ h fr j)
joint-⊕⁺ˢ h (fresh∷ ne fr) (right-only j) = right-only (joint-⊕⁺ˢ h fr j)

module _ {W : World Δ Δ′} {m : VarImp} {β : RVar} where

  private
    W⁺ = W ⊕⁺ˢ m ^ β

  ⇑ᴸ-emb : ∀ A
    → renameᵗ (emb (ηᴸʷ W⁺)) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ (emb (ηᴸʷ W)) A)
  ⇑ᴸ-emb A =
    trans (renameᵗ-fuse (emb (ηᴸʷ W⁺)) suc A)
      (trans (renameᵗ-cong (λ X → cong suc (emb-relabel suc (ηᴸʷ W) X)) A)
             (sym (renameᵗ-fuse suc (emb (ηᴸʷ W)) A)))

  ⇑ᴿ-emb : ∀ A
    → renameᵗ (emb (ηᴿʷ W⁺)) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ (emb (ηᴿʷ W)) A)
  ⇑ᴿ-emb A =
    trans (renameᵗ-fuse (emb (ηᴿʷ W⁺)) suc A)
          (sym (renameᵗ-fuse suc (emb (ηᴿʷ W)) A))

  -- a pair's agreement survives: the left side is under one more Λ,
  -- the right side has one more name (β's, at position 0)
  agree-⊕⁺ˢ : ∀ {α β′} → Agree W α β′ → Agree W⁺ (suc α) β′
  agree-⊕⁺ˢ (abst-abst l r) = abst-abst (r-there-abst l) r
  agree-⊕⁺ˢ (abst-★ l r)    = abst-★ (r-there-abst l) r
  agree-⊕⁺ˢ (rep-rep {A = A} {A′ = A′} l r sA sA′ p) =
    rep-rep (r-there-abst l) r
      (same-pos there (same-ren suc sA)) (same-pos there sA′)
      (subst₂ (μʷ W⁺ ⊢_⊑_) (sym (⇑ᴸ-emb A)) (sym (⇑ᴿ-emb A′))
              (⊑-ren there p))

  wf-⊕⁺ˢ : WfWorld W → names Δ′ ∌ʳ β → Δ′ ∋rep β := ★ → WfWorld W⁺
  wf-⊕⁺ˢ wf fr hβ = wf-world joint agree uniq
    where
    joint : Joint (Paired W⁺) (ηᴸʷ W⁺) (ηᴿʷ W⁺)
    joint = both (inj₂ here⇔)
      (joint-⊕⁺ˢ (paired-⊕⁺ˢ {W = W} {m} {β}) fr (wf-joint wf))

    agree : ∀ {a β′} → Paired W⁺ a β′ → Agree W⁺ a β′
    agree x with paired-⊕⁺ˢ⁻ {W = W} {m} {β} x
    agree x | inj₁ (refl , refl)     = abst-★ r-here hβ
    agree x | inj₂ (α , refl , p , _) = agree-⊕⁺ˢ (wf-agree wf p)

    uniq : ∀ {a a′ β′} → Paired W⁺ a β′ → Paired W⁺ a′ β′ → a ≡ a′
    uniq x y with paired-⊕⁺ˢ⁻ {W = W} {m} {β} x
      | paired-⊕⁺ˢ⁻ {W = W} {m} {β} y
    uniq x y | inj₁ (refl , refl) | inj₁ (refl , refl) = refl
    uniq x y | inj₁ (refl , refl) | inj₂ (_ , _ , _ , ne) = ⊥-elim (ne refl)
    uniq x y | inj₂ (_ , _ , _ , ne) | inj₁ (refl , refl) = ⊥-elim (ne refl)
    uniq x y | inj₂ (α , refl , p , _) | inj₂ (α′ , refl , p′ , _) =
      cong suc (wf-right-unique wf p p′)

-- the freshness hypothesis is the boundary's own `bind` premise
bdy-fresh : ∀ {β Δᵢ A′ c′ B′}
  → BdyTy Δ′ (bind 0 β ∷ []) Δᵢ A′ c′ B′ → names Δ′ ∌ʳ β
bdy-fresh (bdy-ty (bw _ (interior (changes∷ changes[]
  (step-bind _ fr _))) _) _ _ _ _) = fr

-- so the premise world of ∀⊑⟪+⟫ is well formed whenever W is: the
-- hypotheses are the rule's premises `Δ′ ∋rep β := ★` and `BdyTy …`
wf-premise : ∀ {W : World Δ Δ′} {m β A′ c′ B′}
  → WfWorld W → Δ′ ∋rep β := ★
  → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
  → WfWorld (W ⊕⁺ˢ m ^ β)
wf-premise wf hβ b = wf-⊕⁺ˢ wf (bdy-fresh b) hβ

------------------------------------------------------------------------
-- 3½. Administrative runs: no step allocates
------------------------------------------------------------------------

Admin : ∀ {Δ M N} → Δ ⊢ M -→* N → Set
Admin done = ⊤
Admin (_then_ {δ = none} st r)  = Admin r
Admin (_then_ {δ = new R} st r) = ⊥

------------------------------------------------------------------------
-- 4. A local copy of the relation; only ∀⊑⟪+⟫'s premise world differs
------------------------------------------------------------------------

infix 3 _∣_⊢_⊑_∶_

data _∣_⊢_⊑_∶_ {Δ Δ′ : Ctxᵗ} (W : World Δ Δ′) (γ : CtxImp W)
    : Term → Term → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ ` x ∶ p

  κ⊑κ : ∀ {k ι} → Lit k ι → (p : ι ⊑ᵂ⟨ W ⟩ ι) → W ∣ γ ⊢ k ⊑ k ∶ p

  ƛ⊑ƛ : ∀ {N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ L′ · M′ ∶ pB

  blame⊑ : ∀ {ℓ M′ A A′}
    → Δ ⊢ᵗ A → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′ → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ M′ ∶ p

  cast⊑cast : ∀ {M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  cast⊑ : ∀ {M M′ μ c B A A′} {p : B ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ μ c B A → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q

  ⊑cast : ∀ {M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ p → CastTy Δ′ μ′ c′ B′ A′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕ X⊑X ⟩ A′}
    → LiftCtx X⊑X γ γ′ → Value V → Value V′
    → W ⊕ X⊑X ∣ γ′ ⊢ V ⊑ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ Λ V′ ∶ q

  Λ⊑ : ∀ {γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′}
    → NonVar A → 0 ∈ᵗ A → LiftCtxᴸ γ γ′ → Value V
    → W ⊕ᴸ ∣ γ′ ⊢ V ⊑ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ M′ ∶ q

  -- THE ONLY CHANGE: the premise world is `W ⊕⁺ˢ m ^ β`
  ∀⊑⟪+⟫ : ∀ {V N V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ˢ m ^ β ⟩ A′}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → W ⊕⁺ˢ m ^ β ∣ [] ⊢ N ⊑ V′ ∶ r
    → Δ′ ∋rep β := ★
    → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q

  -- (R2, candidate B; §8) the premise may be read after an
  -- administrative (non-allocating) run of the inst_X image
  ∀⊑⟪+⟫ᵃ : ∀ {V N N₀ V′ β m c′ A A′ B′} {r : A ⊑ᵂ⟨ W ⊕⁺ˢ m ^ β ⟩ A′}
    → NonVar A
    → 0 ∈ᵗ A
    → Value V
    → Δ ∣ lhs γ ⊢ V ⦂ `∀ A
    → InstX V N
    → (ρ : underΛ Δ ⊢ N -→* N₀) → Admin ρ
    → W ⊕⁺ˢ m ^ β ∣ [] ⊢ N₀ ⊑ V′ ∶ r
    → Δ′ ∋rep β := ★
    → BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q

  ν⊑ν : ∀ {L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ L′ ∶ r → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B) → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′ → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ M′ ∶ r → A ⊑ᵂ⟨ W ⟩ ★ → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ}
      {M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A) → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⟪⟫⊑ : ∀ {Δᵢ} {Wᵢ : World Δᵢ Δ′}
      {M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q

  ⊑⟪⟫ : ∀ {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
      {M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ → WfWorld Wᵢ → Wᵢ ∣ [] ⊢ M ⊑ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′ → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ M′ ⟪ Θ′ , c′ ⟫ ∶ q

------------------------------------------------------------------------
-- 5. (R3, b) The five existing ∀⊑⟪+⟫ derivations still go through
------------------------------------------------------------------------

-- On W₃ (ϱᵍ = ϱˡ = []) nothing is dropped: the premise worlds coincide
-- definitionally, for every mark.
W₃-same : ∀ m → W₃ ⊕⁺ˢ m ^ 0 ≡ W₃ ⊕⁺ m ^ 0
W₃-same m = refl

five⊑ : ∀ {Δ Ξ′} {W : World Δ (Ξ′ ∣ [])} {γ : CtxImp W}
  → W ∣ γ ⊢ $ 5 ⊑ 5⟨ℕ!⟩ ∶ ℕ⊑★
five⊑ = ⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) (cast-ty (⊢tag g-ℕ) refl) ℕ⊑★

-- p3-inst (TermImprecisionExamples) = ch-x0, verbatim but `∀id⊑★ W₃`
p3-inst : W₃ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
p3-inst =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
                    (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
                    (inst-Λ (V-simple S-ƛ))
                    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                    r-here bR-ty (∀id⊑★ W₃))
                 id★↦ᴿ-ty (∀id⊑★ W₃))
          ℕ⊑★ νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

-- cg-x0, verbatim (its Wg⁻-int is an `Interior Wg⁺ …`, Wg⁺ = W₃ ⊕⁺ …)
cg-x0 : W₃ ∣ [] ⊢ L1 ⊑ Cg-R₂ ∶ ℕ⊑★
cg-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (∀⊑⟪+⟫ {m = X⊑★} nv-⇒ (∈-⇒ˡ ∈-var)
          (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
          (inst-Λ (V-simple S-ƛ))
          (⊑cast
            (⊑⟪⟫ Wg⁻-int Wg⁻-wf
              (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ))
              I★⁻ᴿ-ty (X⇒X⊑★⇒★ {W = Wg⁺} here))
            tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ νL-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- c2-x0, verbatim
c2-x0 : W₃ ∣ [] ⊢ C2-L ⊑ Cg-R₂ ∶ ℕ⊑★
c2-x0 =
  ·⊑·
    (ν⊑
      (⊑cast
        (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
          (V-simple (S-cast (V-simple S-ƛ) I-gen))
          I★genI-⊢ (inst-gen (V-simple S-ƛ))
          (cast⊑cast
            (⟪⟫⊑⟪⟫ W2⁻-int W2⁻-wf
              (ƛ⊑ƛ {pA = ★⊑★} tf tf (x⊑x Zʷ))
              I★⁻ᴸ-ty I★⁻ᴿ-ty
              (W2⁺ , W2⁺-conv , id★→⊑id★→) (★⇒★ W2⁺))
            tagᴸ-ty tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X))
          r-here Bg-ty (∀id⊑★ W₃))
        id★↦ᴿ-ty (∀id⊑★ W₃))
      ℕ⊑★ C2-L-ν-ty (ℕ⇒ℕ⊑★⇒★ W₃))
    five⊑

-- c12-x0, verbatim
c12-x0 : W₃ ∣ [] ⊢ C12-L ⊑ C12-R₂ ∶ ι⊑ι base-ℕ
c12-x0 =
  ·⊑·
    (ν⊑ν
      (⊑cast
        (⊑cast
          (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
            (V-simple (S-Λ (V-simple S-ƛ))) ΛidX-⊢
            (inst-Λ (V-simple S-ƛ))
            (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
            r-here bR-ty (∀id⊑★ W₃))
          id★↦ᴿ-ty (∀id⊑★ W₃))
        genIᴿ-ty (∀id⊑∀id W₃))
      (ι⊑ι base-ℕ) νL-ty C12-ν₂-ty (Wν₂ , Wν₂-conv , revX⊑revX refl)
      (ℕ⇒ℕ W₃))
    (κ⊑κ lit-$ (ι⊑ι base-ℕ))

------------------------------------------------------------------------
-- 6. (R3, c) L3c/R3c: the left's TyBeta of copy 1
------------------------------------------------------------------------

-- the right's Inst boundary over αᴿ:=★, under its `id(★) → id(★)` cast
B⟨id⟩ : Term
B⟨id⟩ = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩

-- left after Beta (copy 1 is the ν, copy 2 the Λ under λy); left after
-- the TyBeta of copy 1; right after Inst, TyBeta and Beta
L3c₁ L3c₂ R3c₃ : Term
L3c₁ = (ƛ `ℕ ∙ I) · L1
L3c₂ = (ƛ `ℕ ∙ I) · L1′
R3c₃ = (ƛ ★ ∙ B⟨id⟩) · R3′

L3c₁-state : head (drop 1 (evalTerms 20 L3c-⊢)) ≡ just L3c₁
L3c₁-state = refl

L3c₂-state : head (drop 2 (evalTerms 20 L3c-⊢)) ≡ just L3c₂
L3c₂-state = refl

R3c₃-state : head (drop 3 (evalTerms 25 R3c-⊢)) ≡ just R3c₃
R3c₃-state = refl

-- copy 2, `Λ ⊑ [+X^αᴿ] … ⟨id(★) → id(★)⟩`, under λy:ℕ ⊑ λy:★, in any
-- world over the two runtime contexts
copy2 : ∀ {Ξ} {W : World (Ξ ∣ []) ΔR}
  → (Ξ ∣ []) ∣ `ℕ ∷ [] ⊢ I ⦂ `∀ (` 0 ⇒ ` 0)
  → W ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ I ⊑ B⟨id⟩ ∶ ∀id⊑★ W
copy2 {W = W} ⊢I =
  ⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
           (V-simple (S-Λ (V-simple S-ƛ))) ⊢I (inst-Λ (V-simple S-ƛ))
           (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
           r-here bR-ty (∀id⊑★ W))
        id★↦ᴿ-ty (∀id⊑★ W)

-- BEFORE the TyBeta: both copies by ∀⊑⟪+⟫, in W₃ (αᴿ unpaired)
l3c-pre : W₃ ∣ [] ⊢ L3c₁ ⊑ R3c₃ ∶ ∀id⊑★ W₃
l3c-pre = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc)) p3-inst

-- AFTER it: copy 1 by ⟪⟫⊑⟪⟫ through the new global pair (αᴸ, αᴿ)
-- (= ch-b1), copy 2 still by ∀⊑⟪+⟫, now in W₁
l3c-post : W₁ ∣ [] ⊢ L3c₂ ⊑ R3c₃ ∶ ∀id⊑★ W₁
l3c-post =
  ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 tc))
    (·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ Wᵢ₁-int Wᵢ₁-wf
          (ƛ⊑ƛ {pA = X⊑X {X = 0}} {pB = X⊑X {X = 0}} tf tf (x⊑x Zʷ))
          bL-ty bR-ty bLR-conv (ℕ⇒ℕ⊑★⇒★ W₁))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ W₁))
      five⊑)

-- the world evolution of the step (Evolve's catch-up `ev-L⇔`) and
-- the well-formedness of both worlds
no-partner : ∀ α → ¬ Paired W₃ α 0
no-partner α (inj₁ ())
no-partner α (inj₂ ())

W₁-agree : ∀ {α β} → Paired W₁ α β → Agree W₁ α β
W₁-agree (inj₁ here⇔)         = rep-rep r-here r-here same-ℕ same-★ ℕ⊑★
W₁-agree (inj₁ (there⇔ ()))
W₁-agree (inj₂ ())

W₁-uniq : ∀ {α α′ β} → Paired W₁ α β → Paired W₁ α′ β → α ≡ α′
W₁-uniq (inj₁ here⇔) (inj₁ here⇔)       = refl
W₁-uniq (inj₁ here⇔) (inj₁ (there⇔ ()))
W₁-uniq (inj₁ (there⇔ ())) _
W₁-uniq (inj₁ here⇔) (inj₂ ())
W₁-uniq (inj₂ ()) _

W₁-wf : WfWorld W₁
W₁-wf = wf-world joint[] W₁-agree W₁-uniq

l3c-evolve : W₃ ⟿[ new `ℕ ∷ [] ∣ [] ] W₁
l3c-evolve = ev-L⇔ wfᴿ-ℕ r-here no-partner (W₁-agree (inj₁ here⇔)) ev-done

-- copy 2's premise world: under ⊕⁺ˢ the global (αᴸ+1, αᴿ) is dropped
-- and the lexical (0, αᴿ) stays ...
post-premise : W₁ ⊕⁺ˢ X⊑X ^ 0
  ≡ world (X⊑X ∷ []) (keep []↪) (keep []↪) [] ((0 , 0) ∷ [])
post-premise = refl

post-premise-wf : WfWorld (W₁ ⊕⁺ˢ X⊑X ^ 0)
post-premise-wf = wf-premise W₁-wf r-here bR-ty

-- ... while under ⊕⁺ αᴿ has the two left partners αᴸ+1 and 0 (D13)
old-premise-¬wf : ¬ WfWorld (W₁ ⊕⁺ X⊑X ^ 0)
old-premise-¬wf wf with wf-right-unique wf (inj₁ here⇔) (inj₂ here⇔)
old-premise-¬wf wf | ()

------------------------------------------------------------------------
-- 7. (R3, beyond) both copies instantiated on the left
------------------------------------------------------------------------

--   L  (λf:∀X.X→X. (λy:ℕ. f[ℕ] 5) (f[ℕ] 5)) (ΛX.λx:X.x)
--   R  (λf:★→★.    (λy:★. f 5)    (f 5))    (ΛX.λx:X.x)
L3d R3d : Term
L3d = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙
        ((ƛ `ℕ ∙ ((ν `ℕ · ` 1 ⟨ revX ⟩) · $ 5))
          · ((ν `ℕ · ` 0 ⟨ revX ⟩) · $ 5))) · I
R3d = (ƛ (★ ⇒ ★) ∙ ((ƛ ★ ∙ (` 1 · 5⟨ℕ!⟩)) · (` 0 · 5⟨ℕ!⟩)))
    · (I ⟨ [] ∣ instI ⟩)

L3d-⊢ : empty ∣ [] ⊢ L3d ⦂ `ℕ
L3d-⊢ = tc

R3d-⊢ : empty ∣ [] ⊢ R3d ⦂ ★
R3d-⊢ = tc

-- the left's second TyBeta (copy 2) meets the right's copy 2: the pair
-- is P3's (L1, R3′) again, now in W₁ (αᴸ of copy 1 paired with αᴿ)
L3d₇-state : head (drop 7 (evalTerms 30 L3d-⊢)) ≡ just L1
L3d₇-state = refl

L3d₈-state : head (drop 8 (evalTerms 30 L3d-⊢)) ≡ just L1′
L3d₈-state = refl

R3d₁₂-state : head (drop 12 (evalTerms 40 R3d-⊢)) ≡ just R3′
R3d₁₂-state = refl

νLₗ-ty : NuTy ΔL `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
νLₗ-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = ΔL} {M = ν `ℕ · I ⟨ revX ⟩})))

l3d-before : W₁ ∣ [] ⊢ L1 ⊑ R3′ ∶ ℕ⊑★
l3d-before =
  ·⊑· (ν⊑ (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var)
                    (V-simple (S-Λ (V-simple S-ƛ))) tc
                    (inst-Λ (V-simple S-ƛ))
                    (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ))
                    r-here bR-ty (∀id⊑★ W₁))
                 id★↦ᴿ-ty (∀id⊑★ W₁))
          ℕ⊑★ νLₗ-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
      five⊑

-- the second catch-up: copy 2's left TyBeta finds αᴿ already paired
-- (with copy 1's αᴸ), so Evolve's `ev-L⇔` is unavailable ...
no-second-catchup : ¬ (∀ α → ¬ Paired W₁ α 0)
no-second-catchup h = h 0 (inj₁ here⇔)

-- ... `ev-L` leaves the new left rep. var (0) unpaired, so copy 2's
-- ⟪⟫⊑⟪⟫ (whose Interior joins the two fresh names iff Paired) cannot
-- join X with X′ ...
second-unpaired : ¬ Paired (allocᴸ `ℕ W₁) 0 0
second-unpaired (inj₁ (there⇔ ()))
second-unpaired (inj₂ ())

-- ... and pairing it anyway gives αᴿ two left partners (D13)
second-paired-¬wf : ¬ WfWorld (allocᴸ⇔ `ℕ 0 W₁)
second-paired-¬wf wf with wf-right-unique wf (inj₁ here⇔)
                                              (inj₁ (there⇔ here⇔))
second-paired-¬wf wf | ()

------------------------------------------------------------------------
-- 8. (R2) L2c/R2c: the right's Merge inside its Inst boundary
------------------------------------------------------------------------

-- the left after its TyBeta (αᴸ:=★) and one Beta: a gen-cast ∀-value
-- over a boundary value
Bα V2 L2c₂ : Term
Bα   = idX ⟪ Θ₀ , revX ⟫
V2   = Bα ⟨ [] ∣ genI ⟩
L2c₂ = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ` 0) · V2

L2c₂-state : head (drop 2 (evalTerms 20 L2c-⊢)) ≡ just L2c₂
L2c₂-state = refl

-- N = inst_Y(V2) (Y at rep. var 0, αᴸ at 1); the right's interior
-- after Inst and TyBeta (β at 0, αᴿ at 1) is the same term
Θ₁ Θm : Boundary
Θ₁ = bind 0 1 ∷ []
Θm = bind 0 1 ∷ unbind 0 0 ∷ []

Bin Nu N N₀ : Term
Bin = idX ⟪ Θ₁ , revX ⟫
Nu  = Bin ⟪ unbind 0 0 ∷ [] , id★→ ⟫
N   = Nu ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩
-- ... and after the Merge (left: N₀; right: the interior of R2c₅)
N₀  = (idX ⟪ Θm , revX ⟫) ⟨ ★∼X ∷ [] ∣ tagX↦ ⟩

R2c₄ R2c₅ : Term
R2c₄ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)
R2c₅ = (ƛ (★ ⇒ ★) ∙ ` 0) · ((N₀ ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ id★↦ ⟩)

R2c₄-state : head (drop 4 (evalTerms 20 R2c-⊢)) ≡ just R2c₄
R2c₄-state = refl

R2c₅-state : head (drop 5 (evalTerms 20 R2c-⊢)) ≡ just R2c₅
R2c₅-state = refl

vBα : Value Bα
vBα = V-⟪⟫ S-ƛ I-fun

vV2 : Value V2
vV2 = V-simple (S-cast vBα I-gen)

instV2 : InstX V2 N
instV2 = inst-gen vBα

-- the contexts and worlds
ΔR2 : Ctxᵗ
ΔR2 = allocate ★ ΔR

ΞL ΞR : RepCtx
ΞL = abstR ∷ bindR ★ ∷ []
ΞR = bindR ★ ∷ bindR ★ ∷ []

-- after the matched TyBetas of αᴸ/αᴿ (ev-2) and the right's β (ev-R)
W4 : World ΔR ΔR2
W4 = world [] []↪ []↪ ((0 , 1) ∷ []) []

-- every world below has ϱᵍ = {(αᴸ, αᴿ)} and ϱˡ = {(Y, β)}
module P {nsL nsR : TyCtx} (μ : ImpEnv) (η : nsL ↪ μ) (η′ : nsR ↪ μ) where

  W : World (ΞL ∣ nsL) (ΞR ∣ nsR)
  W = world μ η η′ ((1 , 1) ∷ []) ((0 , 0) ∷ [])

  agree : ∀ {α β} → Paired W α β → Agree W α β
  agree (inj₁ here⇔) =
    rep-rep (r-there-abst r-here) (r-there r-here) same-★ same-★ ★⊑★
  agree (inj₁ (there⇔ ()))
  agree (inj₂ here⇔) = abst-★ r-here r-here
  agree (inj₂ (there⇔ ()))

  uniq : ∀ {α α′ β} → Paired W α β → Paired W α′ β → α ≡ α′
  uniq (inj₁ here⇔) (inj₁ here⇔) = refl
  uniq (inj₁ here⇔) (inj₁ (there⇔ ()))
  uniq (inj₁ here⇔) (inj₂ (there⇔ ()))
  uniq (inj₁ (there⇔ ())) _
  uniq (inj₂ here⇔) (inj₂ here⇔) = refl
  uniq (inj₂ here⇔) (inj₁ (there⇔ ()))
  uniq (inj₂ here⇔) (inj₂ (there⇔ ()))
  uniq (inj₂ (there⇔ ())) _

-- the premise world of ∀⊑⟪+⟫ (nothing dropped: β = 0 has no pair in W4)
Pw : World (underΛ ΔR) (ΞR ∣ (0 ∷ []))
Pw = W4 ⊕⁺ˢ X⊑X ^ 0

Pw-is : Pw ≡ P.W (X⊑X ∷ []) (keep []↪) (keep []↪)
Pw-is = refl

-- inside both −Y: no names
Pu : World (ΞL ∣ []) (ΞR ∣ [])
Pu = P.W [] []↪ []↪

Pu-wf : WfWorld Pu
Pu-wf = wf-world joint[] agree uniq where open P [] []↪ []↪

-- inside both +X^α: X both-sided at X⊑X
Pb : World (ΞL ∣ (1 ∷ [])) (ΞR ∣ (1 ∷ []))
Pb = P.W (X⊑X ∷ []) (keep []↪) (keep []↪)

Pb-wf : WfWorld Pb
Pb-wf = wf-world (both (inj₁ here⇔) joint[]) agree uniq
  where open P (X⊑X ∷ []) (keep []↪) (keep []↪)

-- the boundary readings
unb-int : ∀ {b Ξ} → ((b ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ (unbind 0 0 ∷ [])
  ⇒ ((b ∷ Ξ) ∣ [])
unb-int = interior (changes∷ changes[]
  (step-unbind (_ , here) del-here fresh[]))

unb-conv-self : ∀ {b b′ Ξ Ξ′}
    {W : World ((b ∷ Ξ) ∣ (0 ∷ [])) ((b′ ∷ Ξ′) ∣ (0 ∷ []))}
  → ConversionInterior W (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) W
unb-conv-self = record
  { conv-left       = conversion (conv-unbind (_ , here) conv[])
  ; conv-right      = conversion (conv-unbind (_ , here) conv[])
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { here here here here → (λ j → j) , (λ j → j)
      ; here here here (there ())
      ; here here (there ()) _
      ; here (there ()) _ _
      ; (there ()) _ _ _
      }
  ; conv-join-fresh = λ
      { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  ; conv-mark-right = λ { here here m → m ; here (there ()) _
                        ; (there ()) _ _ }
  }

bind₁-int : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ []) ⊢ⁱ Θ₁
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ []))
bind₁-int = interior (changes∷ changes[]
  (step-bind (_ , there here) fresh[] ins-here))

bind₁-conv : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ []) ⊢ᶜ Θ₁
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ []))
bind₁-conv = conversion (conv-bind (_ , there here) conv[] fresh[] ins-here)

Θm-int : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ (0 ∷ [])) ⊢ⁱ Θm
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ []))
Θm-int = interior (changes∷
  (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))
  (step-bind (_ , there here) fresh[] ins-here))

Θm-conv : ∀ {Ξ} {b₀ b₁ : RepBinding} → ((b₀ ∷ b₁ ∷ Ξ) ∣ (0 ∷ [])) ⊢ᶜ Θm
  ⇒ ((b₀ ∷ b₁ ∷ Ξ) ∣ (1 ∷ 0 ∷ []))
Θm-conv = conversion (conv-bind (_ , there here)
  (conv-unbind (_ , here) conv[]) (fresh∷ (λ ()) fresh[]) ins-here)

Iu : Interior Pw (unbind 0 0 ∷ []) (unbind 0 0 ∷ []) Pu
Iu = record
  { int-left   = unb-int
  ; int-right  = unb-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , ()) _ _ }
  }

Ib : Interior Pu Θ₁ Θ₁ Pb
Ib = record
  { int-left   = bind₁-int
  ; int-right  = bind₁-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Ibc : ConversionInterior Pu Θ₁ Θ₁ Pb
Ibc = record
  { conv-left       = bind₁-conv
  ; conv-right      = bind₁-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there ()) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ { _ () _ }
  }

-- typing side premises, read off `tc`
bBᴸ : BdyTy (ΞL ∣ []) Θ₁ (ΞL ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBᴸ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΞL ∣ []} {M = Bin}))))

bBᴿ : BdyTy (ΞR ∣ []) Θ₁ (ΞR ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bBᴿ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΞR ∣ []} {M = Bin}))))

bUᴸ : BdyTy (underΛ ΔR) (unbind 0 0 ∷ []) (ΞL ∣ []) (★ ⇒ ★) id★→ (★ ⇒ ★)
bUᴸ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = Nu}))))

bUᴿ : BdyTy (ΞR ∣ (0 ∷ [])) (unbind 0 0 ∷ []) (ΞR ∣ []) (★ ⇒ ★) id★→
  (★ ⇒ ★)
bUᴿ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = Nu}))))

bMᴸ : BdyTy (underΛ ΔR) Θm (ΞL ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bMᴸ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = idX ⟪ Θm , revX ⟫}))))

bMᴿ : BdyTy (ΞR ∣ (0 ∷ [])) Θm (ΞR ∣ (1 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bMᴿ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = idX ⟪ Θm , revX ⟫}))))

tagNᴸ : CastTy (underΛ ΔR) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagNᴸ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = N})))

tagNᴿ : CastTy (ΞR ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagNᴿ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = N})))

bOut₄ : BdyTy ΔR2 Θ₀ (ΞR ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOut₄ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔR2} {M = N ⟪ Θ₀ , revX ⟫}))))

bOut₅ : BdyTy ΔR2 Θ₀ (ΞR ∣ (0 ∷ [])) (` 0 ⇒ ` 0) revX (★ ⇒ ★)
bOut₅ = proj₂ (proj₂ (proj₂
  (⟪⟫-inv {Γ = []} (tc {Δ = ΔR2} {M = N₀ ⟪ Θ₀ , revX ⟫}))))

id★↦ᴿ₂-ty : CastTy ΔR2 [] id★↦ (★ ⇒ ★) (★ ⇒ ★)
id★↦ᴿ₂-ty = cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl

V2-⊢ : ΔR ∣ [] ⊢ V2 ⦂ `∀ (` 0 ⇒ ` 0)
V2-⊢ = tc

-- the pair at the right's TyBeta (before its Merge): ∀⊑⟪+⟫ with
-- premise N ⊑ N, two nested ⟪⟫⊑⟪⟫ under the matched tag casts
N⊑N : Pw ∣ [] ⊢ N ⊑ N ∶ ⇒⊑⇒ X⊑X X⊑X
N⊑N =
  cast⊑cast
    (⟪⟫⊑⟪⟫ Iu Pu-wf
      (⟪⟫⊑⟪⟫ Ib Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bBᴸ bBᴿ
        (Pb , Ibc , revX⊑revX refl) (★⇒★ Pu))
      bUᴸ bUᴿ (Pw , unb-conv-self , id★→⊑id★→) (★⇒★ Pw))
    tagNᴸ tagNᴿ (⇒⊑⇒ X⊑X X⊑X)

r2c-pre : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₄ ∶ ∀id⊑★ W4
r2c-pre =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 N⊑N r-here
              bOut₄ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

-- the right's Merge step is matched by ev-noneᴿ: the world stays W4

-- (B) the left's own Merge, as the administrative run of the premise
N-⊢ : underΛ ΔR ∣ [] ⊢ N ⦂ (` 0 ⇒ ` 0)
N-⊢ = tc

N-merge : underΛ ΔR ⊢ N -→* N₀
N-merge = eval-sound 1 N-⊢

N-merge-admin : Admin N-merge
N-merge-admin = tt

-- the final interior world of Θm ∥ Θm is Pb again; the conversion
-- contexts keep Y (Θm's unbind is skipped)
Pcm : World (ΞL ∣ (1 ∷ 0 ∷ [])) (ΞR ∣ (1 ∷ 0 ∷ []))
Pcm = P.W (X⊑X ∷ X⊑X ∷ []) (keep (keep []↪)) (keep (keep []↪))

Im : Interior Pw Θm Θm Pb
Im = record
  { int-left   = Θm-int
  ; int-right  = Θm-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Imc : ConversionInterior Pw Θm Θm Pcm
Imc = record
  { conv-left       = Θm-conv
  ; conv-right      = Θm-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ
      { (there here) (there here) here here → (λ _ → refl) , (λ _ → refl)
      ; here _ (there ()) _
      ; (there here) here _ (there ())
      ; (there here) (there (there ())) _ _
      ; (there (there ())) _ _ _
      }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; (there here) (there here) (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
      ; (there here) (there here) (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
      ; here (there (there ())) _
      ; (there here) (there (there ())) _
      ; (there (there ())) _ _
      }
  ; conv-mark-left  = λ
      { (there here) here here → there here ; here (there ()) _
      ; (there here) (there ()) _ ; (there (there ())) _ _ }
  ; conv-mark-right = λ
      { (there here) here here → there here ; here (there ()) _
      ; (there here) (there ()) _ ; (there (there ())) _ _ }
  }

tagN₀ᴸ : CastTy (underΛ ΔR) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagN₀ᴸ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = underΛ ΔR} {M = N₀})))

tagN₀ᴿ : CastTy (ΞR ∣ (0 ∷ [])) (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
tagN₀ᴿ = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΞR ∣ (0 ∷ [])} {M = N₀})))

N₀⊑N₀ : Pw ∣ [] ⊢ N₀ ⊑ N₀ ∶ ⇒⊑⇒ X⊑X X⊑X
N₀⊑N₀ =
  cast⊑cast
    (⟪⟫⊑⟪⟫ Im Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bMᴸ bMᴿ
      (Pcm , Imc , revX⊑revX refl) (★⇒★ Pw))
    tagN₀ᴸ tagN₀ᴿ (⇒⊑⇒ X⊑X X⊑X)

r2c-post-B : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
r2c-post-B =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ᵃ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2
              N-merge N-merge-admin N₀⊑N₀ r-here bOut₅ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

-- (A) the left unmerged against the right merged: the left's −Y is
-- one-sided (Y goes right-only, keeping X⊑X), then [+X^α] ∥ [−Y, +X^α]
Pu′ : World (ΞL ∣ []) (ΞR ∣ (0 ∷ []))
Pu′ = P.W (X⊑X ∷ []) (skip []↪) (keep []↪)

Pu′-wf : WfWorld Pu′
Pu′-wf = wf-world (right-only joint[]) agree uniq
  where open P (X⊑X ∷ []) (skip []↪) (keep []↪)

Pc′ : World (ΞL ∣ (1 ∷ [])) (ΞR ∣ (1 ∷ 0 ∷ []))
Pc′ = P.W (X⊑X ∷ X⊑X ∷ []) (keep (skip []↪)) (keep (keep []↪))

Iu′ : Interior Pw (unbind 0 0 ∷ []) [] Pu′
Iu′ = record
  { int-left   = unb-int
  ; int-right  = interior changes[]
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  ; mark-left  = λ { (_ , ()) _ _ }
  ; mark-right = λ { (_ , here) refl m → m ; (_ , there ()) _ _ }
  }

Ib′ : Interior Pu′ Θ₁ Θm Pb
Ib′ = record
  { int-left   = bind₁-int
  ; int-right  = Θm-int
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
                   ; here (there ()) _ ; (there ()) _ _ }
  ; mark-left  = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  ; mark-right = λ { (_ , here) () _ ; (_ , there ()) _ _ }
  }

Ibc′ : ConversionInterior Pu′ Θ₁ Θm Pc′
Ibc′ = record
  { conv-left       = bind₁-conv
  ; conv-right      = Θm-conv
  ; conv-same-ϱᵍ    = refl
  ; conv-same-ϱˡ    = refl
  ; conv-join-cont  = λ { _ _ () _ }
  ; conv-join-fresh = λ
      { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
      ; here (there (there ())) _
      ; (there ()) _ _
      }
  ; conv-mark-left  = λ { _ () _ }
  ; conv-mark-right = λ
      { (there here) here here → there here ; here (there ()) _
      ; (there here) (there ()) _ ; (there (there ())) _ _ }
  }

N⊑N₀ : Pw ∣ [] ⊢ N ⊑ N₀ ∶ ⇒⊑⇒ X⊑X X⊑X
N⊑N₀ =
  cast⊑cast
    (⟪⟫⊑ Iu′ Pu′-wf
      (⟪⟫⊑⟪⟫ Ib′ Pb-wf (ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)) bBᴸ bMᴿ
        (Pc′ , Ibc′ , revX⊑revX refl) (★⇒★ Pu′))
      bUᴸ (★⇒★ Pw))
    tagNᴸ tagN₀ᴿ (⇒⊑⇒ X⊑X X⊑X)

-- with the UNCHANGED ∀⊑⟪+⟫ (premise at N = inst_Y(V2) itself)
r2c-post-A : W4 ∣ [] ⊢ L2c₂ ⊑ R2c₅ ∶ ∀id⊑★ W4
r2c-post-A =
  ·⊑· (ƛ⊑ƛ {pA = ∀id⊑★ W4} tf tf (x⊑x Zʷ))
    (⊑cast (∀⊑⟪+⟫ {m = X⊑X} nv-⇒ (∈-⇒ˡ ∈-var) vV2 V2-⊢ instV2 N⊑N₀ r-here
              bOut₅ (∀id⊑★ W4))
           id★↦ᴿ₂-ty (∀id⊑★ W4))

W4-same : W4 ⟿[ [] ∣ none ∷ [] ] W4
W4-same = ev-noneᴿ ev-done

------------------------------------------------------------------------
-- 9. (R2) What SimBackFrame-∀⊑⟪+⟫ needs
------------------------------------------------------------------------

-- (i) the right's allocations inside the boundary commute with the
-- premise world: the IH's world can be read back as `W′ ⊕⁺ˢ m ^ β′`
drop-shiftᴿ : ∀ β (ϱ : RepRel)
  → shiftᴿ (dropᴿ β ϱ) ≡ dropᴿ (suc β) (shiftᴿ ϱ)
drop-shiftᴿ β [] = refl
drop-shiftᴿ β ((a , b) ∷ ϱ) with b ≟ β
drop-shiftᴿ β ((a , b) ∷ ϱ) | yes refl with suc b ≟ suc b
drop-shiftᴿ β ((a , b) ∷ ϱ) | yes refl | yes _ = drop-shiftᴿ β ϱ
drop-shiftᴿ β ((a , b) ∷ ϱ) | yes refl | no ne = ⊥-elim (ne refl)
drop-shiftᴿ β ((a , b) ∷ ϱ) | no ne with suc b ≟ suc β
drop-shiftᴿ β ((a , b) ∷ ϱ) | no ne | yes e =
  ⊥-elim (ne (cong pred e))
drop-shiftᴿ β ((a , b) ∷ ϱ) | no ne | no _ =
  cong ((a , suc b) ∷_) (drop-shiftᴿ β ϱ)

shiftᴿᴸ : (ϱ : RepRel) → shiftᴿ (shiftᴸ ϱ) ≡ shiftᴸ (shiftᴿ ϱ)
shiftᴿᴸ []      = refl
shiftᴿᴸ (π ∷ ϱ) = cong (_ ∷_) (shiftᴿᴸ ϱ)

allocᴿ-⊕⁺ˢ : ∀ {Δ Δ′} (R′ : Ty) (W : World Δ Δ′) (m : VarImp) (β : RVar)
  → allocᴿ R′ (W ⊕⁺ˢ m ^ β) ≡ allocᴿ R′ W ⊕⁺ˢ m ^ suc β
allocᴿ-⊕⁺ˢ R′ (world μ η η′ ϱᵍ ϱˡ) m β =
  cong₂ (world (m ∷ μ) (keep (relabel suc η)) (keep (relabel suc η′)))
    (trans (drop-shiftᴿ β (shiftᴸ ϱᵍ))
           (cong (dropᴿ (suc β)) (shiftᴿᴸ ϱᵍ)))
    (cong ((zero , suc β) ∷_)
      (trans (drop-shiftᴿ β (shiftᴸ ϱˡ))
             (cong (dropᴿ (suc β)) (shiftᴿᴸ ϱˡ))))

-- (ii) LEFT-EXPANSION along an administrative run of an inst_X image
-- (candidate A's lemma; on L2c/R2c it is `N⊑N₀` from `N₀⊑N₀`)
InstExpand : Set
InstExpand = ∀ {Δ Δ′ᵢ} {Wᵢ : World (underΛ Δ) Δ′ᵢ} {V N N₂ M′ A A′}
    {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′}
  → Value V → InstX V N
  → (ρ : underΛ Δ ⊢ N -→* N₂) → Admin ρ
  → WfWorld Wᵢ
  → Wᵢ ∣ [] ⊢ N₂ ⊑ M′ ∶ r
  → Wᵢ ∣ [] ⊢ N ⊑ M′ ∶ r

-- with InstExpand, candidate B's rule is admissible from the existing
-- one: B adds no derivable pair, it only moves the expansion
B-admissible : InstExpand
  → ∀ {Δ Δ′} {W : World Δ Δ′} {γ : CtxImp W} {V N N₀ V′ β m c′ A A′ B′}
      {r : A ⊑ᵂ⟨ W ⊕⁺ˢ m ^ β ⟩ A′}
  → WfWorld W
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ lhs γ ⊢ V ⦂ `∀ A → InstX V N
  → (ρ : underΛ Δ ⊢ N -→* N₀) → Admin ρ
  → W ⊕⁺ˢ m ^ β ∣ [] ⊢ N₀ ⊑ V′ ∶ r
  → Δ′ ∋rep β := ★
  → (b : BdyTy Δ′ (bind 0 β ∷ []) (reps Δ′ ∣ (β ∷ names Δ′)) A′ c′ B′)
  → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢ V ⊑ V′ ⟪ bind 0 β ∷ [] , c′ ⟫ ∶ q
B-admissible ex wf nv occ v ⊢V i ρ a d hβ b q =
  ∀⊑⟪+⟫ nv occ v ⊢V i (ex v i ρ a (wf-premise wf hβ b) d) hβ b q

-- (iii) THE CHILD the frame needs: backward simulation INSIDE a
-- ∀⊑⟪+⟫ premise with the left UNMOVED (the left value V cannot step,
-- so the IH of SimBack, which may answer with any left run, is too
-- weak).  The right's allocations are read back through allocᴿ-⊕⁺ˢ.
shiftβ : List Alloc → RVar → RVar
shiftβ []           β = β
shiftβ (none  ∷ ξs) β = shiftβ ξs β
shiftβ (new R ∷ ξs) β = shiftβ ξs (suc β)

SimBackInstX : Set
SimBackInstX = ∀ {Δ Δ′} {W : World Δ Δ′} {V N M′ M₁′ β m A A′ δ′}
    {r : A ⊑ᵂ⟨ W ⊕⁺ˢ m ^ β ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → NonVar A → 0 ∈ᵗ A → Value V → Δ ∣ [] ⊢ V ⦂ `∀ A → InstX V N
  → Δ′ ∋rep β := ★
  → W ⊕⁺ˢ m ^ β ∣ [] ⊢ N ⊑ M′ ∶ r
  → (st′ : (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ M′ -→ M₁′ ∣ δ′)
  → ∃[ M₂′ ] Σ[ r″ ∈ apply δ′ (reps Δ′ ∣ (β ∷ names Δ′)) ⊢ M₁′ -→* M₂′ ]
      Σ[ W′ ∈ World Δ (applyˢ (allocs (st′ then r″)) Δ′) ]
        (W ⟿[ [] ∣ allocs (st′ then r″) ] W′) × WfWorld W′
        × Σ[ r′ ∈ A ⊑ᵂ⟨ W′ ⊕⁺ˢ m ^ shiftβ (allocs (st′ then r″)) β ⟩ A′ ]
            (W′ ⊕⁺ˢ m ^ shiftβ (allocs (st′ then r″)) β ∣ [] ⊢ N ⊑ M₂′ ∶ r′)

module proof.LR.CastCases2 where

-- File Charter:
--   * Cases of the cast lemma (`proof.LR.CastLemma`, `CastCase`) that
--     use the induction hypothesis but no world change
--     (notes/logrel-dgg.md, "The cast lemma: the case table"):
--       - `case↦↦`: a left `↦` against a right `↦`.  Both wrappers are
--         values; applied, both take `β-⇒` (`ℰ-both`), then the
--         argument casts are related by the hypothesis at the domains,
--         read at the flipped environments (`flipHyp`), the functions
--         by `app-core`, and the result casts by the hypothesis at the
--         codomains, all in the future of the application
--         (`CastHyp-↑`).
--   * Plumbing: the casts of a renamed cast term (`renCast`, from
--     `rns`), `PreB` at a function type's parts, a right cast term
--     typed (`typedCast`).

open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; ≤′-refl)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; ≤′⇒≤;
  n≤1+n; m≤m+n; m≤n+m; +-mono-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩; _·_; renameᵗᵐ; _《_》;
  fun; ⊢⟨⟩; ⊢·)
open import Reduction using (_—→_; β-⇒)
open import LR.Precision
open import LR.World
open import LR.Relation
open import LR.Frame using (cast)
open import proof.Consistency using (castSize)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.LR.InterpProps using (ℰᵍ-≡; Typedᴿ-≡)
open import proof.LR.Monotone using (GoodI-↑; 𝒱≤-cast; 𝒱-down;
  funRel-mono; funRel-down)
open import proof.LR.Expression using (ℰ-value; ℰ-stepL; ℰ-stepR;
  ℰ-bind₂ᵀ; Typedᴿ-mono)
open import proof.LR.ConvBase using (ℰ-zero; app-core)
open import proof.LR.ConvLemma using (PreB; preB; pre≡; PreB-↑; _↑ˢ_;
  pre-typed)
open import proof.LR.IdentityCast using (fromℰ)
open import proof.LR.CastSubst using (≅ᶜ-⟨⟩; rns; ren-after)
open import proof.LR.CastLemma using (CastCase; CastHyp; sL; sR; σR;
  νL; νR; good; renSE; flipHyp; CastHyp-↑)

------------------------------------------------------------------------
-- Plumbing
------------------------------------------------------------------------

-- both sides take a step
ℰ-both : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Ml′ Mr Mr′}
  → Ml —→ Ml′ → Mr —→ Mr′
  → (∀ {s} → s < n → ℰ d s p w δ Ml′ Mr′)
  → ℰ d n p w δ Ml Mr
ℰ-both d zero p w sl sr k = ℰ-zero d p w
ℰ-both ≺ (suc m) p w sl sr k =
  ℰ-stepL ≺ m p w sl (ℰ-stepR ≺ m p w sr (k ≤-refl))
ℰ-both ≻ (suc m) p w sl sr k =
  ℰ-stepR ≻ m p w sr (ℰ-stepL ≻ m p w sl (k ≤-refl))

-- a cast term at a substituted cast, renamed
castRen : ∀ {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    (ρ : Θ ↪ᵗ Θ′) (s : SubstEnv∼ μ ν σ) {A B} (c : μ ⊢ A ∼ B)
    (Q : Term Θ′)
  → Q ⟨ renameᵐᶜ ρ (subst∼ s c) ⟩ ≡ Q ⟨ subst∼ (renSE ρ s) c ⟩
castRen {ν = ν} ρ s c Q =
  ≅ᶜ-⟨⟩ Q (rns (toRenameᵗ ρ) (renameEnv∼-preserves ρ ν)
    (ren-after (toRenameᵗ ρ) (renameEnv∼-preserves ρ ν) s) c)

private
  ⇒-inj : ∀ {Δ} {A B A′ B′ : Ty Δ} → A ⇒ B ≡ A′ ⇒ B′
    → (A ≡ A′) × (B ≡ B′)
  ⇒-inj refl = refl , refl

PreB-dom : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ A B}
  → PreB w ρ σ (A ⇒ B) → PreB w ρ σ A
PreB-dom pb = preB (proj₁ (⇒-inj (pre≡ pb)))

PreB-cod : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ A B}
  → PreB w ρ σ (A ⇒ B) → PreB w ρ σ B
PreB-cod pb = preB (proj₂ (⇒-inj (pre≡ pb)))

-- a right value cast between preimages, typed
typedCast : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ A B} {V}
    {μ : Env∼ (storeR w)}
  → PreB w ρ σ A → PreB w ρ σ B → Typedᴿ w (substᵗ ρ A) V
  → (c : μ ⊢ substᵗ σ A ∼ substᵗ σ B)
  → Typedᴿ w (substᵗ ρ B) (V ⟨ c ⟩)
typedCast {σ = σ} {B = B} pa pb t c =
  typedᴿ (substᵗ σ B) (pre≡ pb) (⊢⟨⟩ (pre-typed pa t) c)

------------------------------------------------------------------------
-- A left `↦` against a right `↦`
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′} {p : Φ ⊢ A ⊑ A′}
    {q : Φ ⊢ B ⊑ B′} {n w} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr} where

  -- the value relation at `⇒⊑⇒` is `funRel`
  to⇒ : ∀ d → funRel d n p q w δ Vl Vr → 𝒱 d n (⇒⊑⇒ p q) w δ Vl Vr
  to⇒ ≺ f = f
  to⇒ ≻ f = f

  from⇒ : ∀ d → 𝒱 d n (⇒⊑⇒ p q) w δ Vl Vr → funRel d n p q w δ Vl Vr
  from⇒ ≺ f = f
  from⇒ ≻ f = f

case↦↦ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A A′ B B′ : Ty Δ}
    {C C′ D D′ : Ty Δ′}
    (c : flipᵐ ν ⊢ A′ ∼ A) (d : ν ⊢ B ∼ B′)
    (c′ : flipᵐ ν′ ⊢ C′ ∼ C) (d′ : ν′ ⊢ D ∼ D′)
  → CastCase c c′ → CastCase d d′
  → CastCase (c ↦ d) (c′ ↦ d′)
case↦↦ {C = C} {C′} {D} c d c′ d′ ihc ihd dr n (⇒⊑⇒ p₁ p₂) (⇒⊑⇒ r₁ r₂)
    w {δ} h pC pA {Vl} {Vr} vl vr (t , f) =
  ℰ-value dr n (⇒⊑⇒ r₁ r₂) w (vl 《 fun 》) (vr 《 fun 》) (to⇒ dr g)
  where
  f′ = from⇒ dr f

  g : funRel dr n r₁ r₂ w δ (Vl ⟨ subst∼ (sL h) (c ↦ d) ⟩)
        (Vr ⟨ subst∼ (sR h) (c′ ↦ d′) ⟩)
  g {w′} e {n′} le Wl Wr wl wr a tW =
    ℰᵍ-≡ (sym (cong (_· Wl) (castRen (ρL e) (sL h) (c ↦ d) Vl′)))
      (sym (cong (_· Wr) (castRen (ρS e) (sR h) (c′ ↦ d′) Vr′)))
      (fromℰ dr le r₂ w′
        (ℰ-both dr n′ r₂ w′ (β-⇒ vl′ wl) (β-⇒ vr′ wr) (λ {s} s< →
          ℰ-bind₂ᵀ dr s p₂ r₂ w′ (just (cast dL)) (just (cast dR)) tApp
            (app-core dr s p₁ p₂ w′ vl′ vr′ nothing nothing tU
              (inner s<) (funAt s<)
              (λ e″ k≤ ql qr r → ℰ-value dr _ p₂ _ ql qr r))
            (Kd s))))
    where
    δ′ = δ ↑ᴵ e
    h′ = CastHyp-↑ h e
    Vl′ = renameᵗᵐ (ρL e) Vl
    Vr′ = renameᵗᵐ (ρS e) Vr
    vl′ = renameᵗᵐ-preserves-Value (ρL e) vl
    vr′ = renameᵗᵐ-preserves-Value (ρS e) vr
    cL = subst∼ (sL (flipHyp h′)) c
    cR = subst∼ (sR (flipHyp h′)) c′
    dL = subst∼ (sL h′) d
    dR = subst∼ (sR h′) d′

    pC′ = PreB-↑ pC e
    pA′ = PreB-↑ pA e
    pCdom = PreB-dom pC′
    pCcod = PreB-cod pC′
    pAdom = PreB-dom pA′
    pAcod = PreB-cod pA′

    tU : Typedᴿ w′ (substᵗ (δr δ′) C) (Wr ⟨ cR ⟩)
    tU = typedCast pAdom pCdom tW cR

    tF : Typedᴿ w′ (substᵗ (δr δ′) (C ⇒ D)) Vr′
    tF = Typedᴿ-≡ (renameᵗ-subst (toRenameᵗ (ρR e)) (δr δ) (C ⇒ D))
      (Typedᴿ-mono e t)

    tApp : Typedᴿ w′ (substᵗ (δr δ′) D) (Vr′ · (Wr ⟨ cR ⟩))
    tApp = typedᴿ (substᵗ (σR h′) D) (pre≡ pCcod)
      (⊢· (pre-typed pC′ tF) (⊢⟨⟩ (pre-typed pAdom tW) cR))

    inner : ∀ {s} → s < n′ → ℰ dr s p₁ w′ δ′ (Wl ⟨ cL ⟩) (Wr ⟨ cR ⟩)
    inner {s} s< =
      ihc dr s r₁ p₁ w′ (flipHyp h′) pAdom pCdom wl wr
        (tW , 𝒱-down dr (<⇒≤ s<) r₁ w′ (good h′)
                (𝒱≤-cast dr le ≤′-refl r₁ w′ a))

    funAt : ∀ {s} → s < n′ → funRel dr s p₁ p₂ w′ δ′ Vl′ Vr′
    funAt s< = funRel-down dr (≤-trans (<⇒≤ s<) (≤′⇒≤ le)) p₁ p₂ w′
      (funRel-mono dr n p₁ p₂ e f′)

    Kd : ∀ s {w″} (e″ : w″ ⊒ w′) {k} → k ≤ s → ∀ {Ql Qr}
      → Value Ql → Value Qr → 𝒱 dr k p₂ w″ (δ′ ↑ᴵ e″) Ql Qr
      → Typedᴿ w″ (substᵗ (δr (δ′ ↑ᴵ e″)) D) Qr
      → ℰ dr k r₂ w″ (δ′ ↑ᴵ e″) (Ql ⟨ renameᵐᶜ (ρL e″) dL ⟩)
          (Qr ⟨ renameᵐᶜ (ρS e″) dR ⟩)
    Kd s e″ {k} k≤ {Ql} {Qr} ql qr r tq =
      ℰᵍ-≡ (sym (castRen (ρL e″) (sL h′) d Ql))
        (sym (castRen (ρS e″) (sR h′) d′ Qr))
        (ihd dr k p₂ r₂ _ (CastHyp-↑ h′ e″) (PreB-↑ pCcod e″)
          (PreB-↑ pAcod e″) ql qr (tq , r))

-- the measure at the two halves
↦-lt₁ : ∀ a b a′ b′ → a + a′ < suc (a + b) + suc (a′ + b′)
↦-lt₁ a b a′ b′ =
  s≤s (+-mono-≤ (m≤m+n a b) (≤-trans (m≤m+n a′ b′) (n≤1+n _)))

↦-lt₂ : ∀ a b a′ b′ → b + b′ < suc (a + b) + suc (a′ + b′)
↦-lt₂ a b a′ b′ =
  s≤s (+-mono-≤ (m≤n+m b a) (≤-trans (m≤n+m b′ a′) (n≤1+n _)))

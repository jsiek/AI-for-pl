module proof.LR.ConvBase where

-- File Charter:
--   * Machinery for the conversion lemma (notes/logrel-dgg.md,
--     Section 6.9, item 5) that does not depend on its hypotheses:
--       - kinds of variables (dead ones, and disjointness);
--       - the right side's conversion, if any, as an optional frame;
--       - sealed values;
--       - at most one pure step on each side, and the stages of an
--         application's step;
--       - renaming the generated conversions inside terms and frames;
--       - the application of a converted function as two binds;
--       - relations that do not read the interpretation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  ≤-<-trans; <⇒≤)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import proof.DGG.CenterRename using (toRenameᵗ-∘)
open import proof.TypeInTermSubst using (toRename-id-eq;
  renameᵗᵐ-preserves-Value)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open import Conversion
open import CastTerms using (Term; `_; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_;
  _⟨_⟩; _↑_; _↓_; blame; Value; RevealValue; ConcealValue; renameᵗᵐ)
import CastTerms as CT
open import Reduction using (_—→_; id-reveal; id-conceal; conceal-reveal;
  β-reveal-⇒; β-conceal-⇒)
open import LR.Frame using (Frame; reveal; conceal; app₂; plug;
  renameFrame)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone
open import proof.LR.Expression
open import proof.LR.SubstLemma using (ℰᵍ-zero; _⇔_; to; from; 𝒱-XY; 𝒱-X★)
open import proof.LR.ConvSyntax

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Dead variables, and how variables of different kinds differ
------------------------------------------------------------------------

infix 4 _∋_dead

data _∋_dead : ∀ {Δ Δ′} → Corr Δ Δ′ → TyVar Δ → Set where
  dead-here : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} → dead Φ ∋ zero dead
  dead-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X dead → pair Φ ∋ suc X dead
  dead-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X dead → only Φ ∋ suc X dead
  dead-dead : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    → Φ ∋ X dead → dead Φ ∋ suc X dead

↔-functional : ∀ {Φ : Corr Δ Δ′} {X Y Y′}
  → Φ ∋ X ↔ Y → Φ ∋ X ↔ Y′ → Y ≡ Y′
↔-functional ↔-here ↔-here = refl
↔-functional (↔-pair x) (↔-pair y) = cong suc (↔-functional x y)
↔-functional (↔-only x) (↔-only y) = ↔-functional x y
↔-functional (↔-dead x) (↔-dead y) = ↔-functional x y

↔-injective : ∀ {Φ : Corr Δ Δ′} {X X′ Y}
  → Φ ∋ X ↔ Y → Φ ∋ X′ ↔ Y → X ≡ X′
↔-injective ↔-here ↔-here = refl
↔-injective (↔-pair x) (↔-pair y) = cong suc (↔-injective x y)
↔-injective (↔-only x) (↔-only y) = cong suc (↔-injective x y)
↔-injective (↔-dead x) (↔-dead y) = cong suc (↔-injective x y)

↔-only-⊥ : ∀ {Φ : Corr Δ Δ′} {X Y} → Φ ∋ X ↔ Y → Φ ∋ X only → ⊥
↔-only-⊥ ↔-here ()
↔-only-⊥ (↔-pair x) (only-pair y) = ↔-only-⊥ x y
↔-only-⊥ (↔-only x) (only-only y) = ↔-only-⊥ x y
↔-only-⊥ (↔-dead x) (only-dead y) = ↔-only-⊥ x y

↔-dead-⊥ : ∀ {Φ : Corr Δ Δ′} {X Y} → Φ ∋ X ↔ Y → Φ ∋ X dead → ⊥
↔-dead-⊥ ↔-here ()
↔-dead-⊥ (↔-pair x) (dead-pair y) = ↔-dead-⊥ x y
↔-dead-⊥ (↔-only x) (dead-only y) = ↔-dead-⊥ x y
↔-dead-⊥ (↔-dead x) (dead-dead y) = ↔-dead-⊥ x y

only-dead-⊥ : ∀ {Φ : Corr Δ Δ′} {X} → Φ ∋ X only → Φ ∋ X dead → ⊥
only-dead-⊥ only-here ()
only-dead-⊥ (only-pair x) (dead-pair y) = only-dead-⊥ x y
only-dead-⊥ (only-only x) (dead-only y) = only-dead-⊥ x y
only-dead-⊥ (only-dead x) (dead-dead y) = only-dead-⊥ x y

------------------------------------------------------------------------
-- The right side's conversion
------------------------------------------------------------------------

-- the right side's conversion, if any: its store variable and
-- representation
RConv : TyCtx → Set
RConv Θ = Maybe (TyVar Θ × Ty Θ)

renRConv : ∀ {Θ Θ′} → Θ ↪ᵗ Θ′ → RConv Θ → RConv Θ′
renRConv ρ nothing = nothing
renRConv ρ (just (α′ , R)) =
  just (toRenameᵗ ρ α′ , renameᵗ (toRenameᵗ ρ) R)

-- the frames of the right side's reveal and conceal at the type B
revFrame : ∀ {Θ} → RConv Θ → Ty Θ → MFrame Θ
revFrame nothing B = nothing
revFrame (just (α′ , R)) B = just (reveal 〖 α′ , R ↑ B 〗)

conFrame : ∀ {Θ} → RConv Θ → Ty Θ → MFrame Θ
conFrame nothing B = nothing
conFrame (just (α′ , R)) B = just (conceal (makeConceal α′ R B))

revM : ∀ {Θ} → RConv Θ → Ty Θ → Term Θ → Term Θ
revM rc B V = mplug (revFrame rc B) V

conM : ∀ {Θ} → RConv Θ → Ty Θ → Term Θ → Term Θ
conM rc B V = mplug (conFrame rc B) V

-- the stages at which a conceal is needed: below N when the counted
-- side converts, up to N otherwise (`≻`, the right not converting)
ConB : ∀ {Θ} → Dir → RConv Θ → ℕ → ℕ → Set
ConB ≺ rc k N = k < N
ConB ≻ nothing k N = k ≤ N
ConB ≻ (just c) k N = k < N

------------------------------------------------------------------------
-- Sealed values
------------------------------------------------------------------------

sealedL : TyVar ΘL → Ty ΘL → (Term ΘL → Term ΘR → Set)
  → Term ΘL → Term ΘR → Set
sealedL α R P (W ↓ s) Vr = IsSeal α R s × P W Vr
sealedL α R P Vl Vr = ⊥

sealedR : TyVar ΘR → Ty ΘR → (Term ΘL → Term ΘR → Set)
  → Term ΘL → Term ΘR → Set
sealedR α R P Vl (W ↓ s) = IsSeal α R s × P Vl W
sealedR α R P Vl Vr = ⊥

sealedL-inv : ∀ {α : TyVar ΘL} {R} {P : Term ΘL → Term ΘR → Set} {Vl Vr}
  → sealedL α R P Vl Vr → Σ[ W ∈ Term ΘL ] (Vl ≡ W ↓ seal α R × P W Vr)
sealedL-inv {Vl = W ↓ seal X R′} ((refl , refl) , r) = W , refl , r
sealedL-inv {Vl = W ↓ (c ↦↓ d)} (() , r)
sealedL-inv {Vl = W ↓ (`∀↓ c)} (() , r)
sealedL-inv {Vl = W ↓ id↓ A} (() , r)
sealedL-inv {Vl = ` x} ()
sealedL-inv {Vl = ƛ M} ()
sealedL-inv {Vl = L · M} ()
sealedL-inv {Vl = Λ M} ()
sealedL-inv {Vl = L ⦂∀ C [ T ]} ()
sealedL-inv {Vl = $ κ} ()
sealedL-inv {Vl = L ⊕[ op ] M} ()
sealedL-inv {Vl = W ⟨ c ⟩} ()
sealedL-inv {Vl = M ↑ c} ()
sealedL-inv {Vl = blame} ()

sealedR-inv : ∀ {α : TyVar ΘR} {R} {P : Term ΘL → Term ΘR → Set} {Vl Vr}
  → sealedR α R P Vl Vr → Σ[ W ∈ Term ΘR ] (Vr ≡ W ↓ seal α R × P Vl W)
sealedR-inv {Vr = W ↓ seal X R′} ((refl , refl) , r) = W , refl , r
sealedR-inv {Vr = W ↓ (c ↦↓ d)} (() , r)
sealedR-inv {Vr = W ↓ (`∀↓ c)} (() , r)
sealedR-inv {Vr = W ↓ id↓ A} (() , r)
sealedR-inv {Vr = ` x} ()
sealedR-inv {Vr = ƛ M} ()
sealedR-inv {Vr = L · M} ()
sealedR-inv {Vr = Λ M} ()
sealedR-inv {Vr = L ⦂∀ C [ T ]} ()
sealedR-inv {Vr = $ κ} ()
sealedR-inv {Vr = L ⊕[ op ] M} ()
sealedR-inv {Vr = W ⟨ c ⟩} ()
sealedR-inv {Vr = M ↑ c} ()
sealedR-inv {Vr = blame} ()

value-sealed : ∀ {W : Term Δ} {A B} {s : Conv↓ Δ A B}
  → Value (W ↓ s) → Value W
value-sealed (v CT.↓ cv) = v

-- the stage of a left-only leaf's contents: one down in `≺`, the same
-- in `≻`
onlyStage : Dir → ℕ → ℕ
onlyStage ≺ k = pred k
onlyStage ≻ k = k

-- the strict bound for sealing, inclusive for a left-only `≻` leaf
onlyBelow : Dir → ℕ → ℕ → Set
onlyBelow ≺ k N = k < N
onlyBelow ≻ k N = k ≤ N

------------------------------------------------------------------------
-- Sealed values under equal names, representations and relations
------------------------------------------------------------------------

sealedL-map : ∀ {α α′ : TyVar ΘL} {R R′}
    {P P′ : Term ΘL → Term ΘR → Set} {Vl Vr}
  → α ≡ α′ → R ≡ R′ → (∀ {W V} → P W V → P′ W V)
  → sealedL α R P Vl Vr → sealedL α′ R′ P′ Vl Vr
sealedL-map refl refl f s with sealedL-inv s
sealedL-map refl refl f s | W , refl , r = (refl , refl) , f r

sealedR-map : ∀ {α α′ : TyVar ΘR} {R R′}
    {P P′ : Term ΘL → Term ΘR → Set} {Vl Vr}
  → α ≡ α′ → R ≡ R′ → (∀ {W V} → P W V → P′ W V)
  → sealedR α R P Vl Vr → sealedR α′ R′ P′ Vl Vr
sealedR-map refl refl f s with sealedR-inv s
sealedR-map refl refl f s | W , refl , r = (refl , refl) , f r

------------------------------------------------------------------------
-- At most one pure step on each side
------------------------------------------------------------------------

ℰ-≡ : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) {Ml Ml′ Mr Mr′}
  → Ml ≡ Ml′ → Mr ≡ Mr′ → ℰ d n p w δ Ml Mr → ℰ d n p w δ Ml′ Mr′
ℰ-≡ d n p w δ refl refl r = r

-- the expression relation at stage zero
ℰ-zero : ∀ d {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr} → ℰ d zero p w δ Ml Mr
ℰ-zero d p w {δ} = ℰᵍ-zero d w {VR = λ le w′ e → 𝒱≤ d le p w′ (δ ↑ᴵ e)}

infix 2 _—→?_

data _—→?_ {Δ} : Term Δ → Term Δ → Set where
  stay : ∀ {M} → M —→? M
  step : ∀ {M N} → M —→ N → M —→? N

-- the left is already a value
ℰ-stepR? : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} → GoodI δ
  → ∀ {Vl Mr Vr} → Mr —→? Vr → Value Vl → Value Vr
  → 𝒱 d n p w δ Vl Vr → ℰ d n p w δ Vl Mr
ℰ-stepR? d n p w g stay vl vr r = ℰ-value d n p w vl vr r
ℰ-stepR? ≺ n p w g (step s) vl vr r =
  ℰ-stepR ≺ n p w s (ℰ-value ≺ n p w vl vr r)
ℰ-stepR? ≻ zero p w g (step s) vl vr r = ℰ-zero ≻ p w
ℰ-stepR? ≻ (suc k) p w g (step s) vl vr r =
  ℰ-stepR ≻ k p w s (ℰ-value ≻ k p w vl vr (𝒱-down ≻ (n≤1+n k) p w g r))

ℰ-steps? : ∀ d n {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} → GoodI δ
  → ∀ {Ml Mr Vl Vr} → Ml —→? Vl → Mr —→? Vr → Value Vl → Value Vr
  → 𝒱 d n p w δ Vl Vr → ℰ d n p w δ Ml Mr
ℰ-steps? d n p w g stay sr vl vr r = ℰ-stepR? d n p w g sr vl vr r
ℰ-steps? ≺ zero p w g (step s) sr vl vr r = ℰ-zero ≺ p w
ℰ-steps? ≺ (suc k) p w g (step s) sr vl vr r =
  ℰ-stepL ≺ k p w s
    (ℰ-stepR? ≺ k p w g sr vl vr (𝒱-down ≺ (n≤1+n k) p w g r))
ℰ-steps? ≻ n p w g (step s) sr vl vr r =
  ℰ-stepL ≻ n p w s (ℰ-stepR? ≻ n p w g sr vl vr r)

------------------------------------------------------------------------
-- Renaming the conversions of a reveal and of a conceal
------------------------------------------------------------------------

module _ {Θ Θ′ : TyCtx} (ρ : Θ ↪ᵗ Θ′) where

  private
    ρv = toRenameᵗ ρ
    inj = toRenameᵗ-injective ρ

  〖〗-ren : ∀ (α : TyVar Θ) R (σ : Δ ⇒ˢ Θ) A
    → ⟪ rename↑ ρv 〖 α , R ↑ substᵗ σ A 〗 ⟫↑
      ≡ ⟪ 〖 ρv α , renameᵗ ρv R ↑ substᵗ (λ Z → renameᵗ ρv (σ Z)) A 〗 ⟫↑
  〖〗-ren α R σ A =
    trans (〖〗-rename ρv inj α R (substᵗ σ A))
      (cong (λ B → ⟪ 〖 ρv α , renameᵗ ρv R ↑ B 〗 ⟫↑)
        (renameᵗ-subst ρv σ A))

  makeConceal-ren : ∀ (α : TyVar Θ) R (σ : Δ ⇒ˢ Θ) A
    → ⟪ rename↓ ρv (makeConceal α R (substᵗ σ A)) ⟫↓
      ≡ ⟪ makeConceal (ρv α) (renameᵗ ρv R)
            (substᵗ (λ Z → renameᵗ ρv (σ Z)) A) ⟫↓
  makeConceal-ren α R σ A =
    trans (makeConceal-rename ρv inj α R (substᵗ σ A))
      (cong (λ B → ⟪ makeConceal (ρv α) (renameᵗ ρv R) B ⟫↓)
        (renameᵗ-subst ρv σ A))

  revM-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ)
    → renameᵗᵐ ρ (revM rc (substᵗ σ A) V)
      ≡ revM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A)
          (renameᵗᵐ ρ V)
  revM-ren nothing σ A V = refl
  revM-ren (just (α′ , R)) σ A V = ↑-pk (〖〗-ren α′ R σ A)

  conM-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ)
    → renameᵗᵐ ρ (conM rc (substᵗ σ A) V)
      ≡ conM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A)
          (renameᵗᵐ ρ V)
  conM-ren nothing σ A V = refl
  conM-ren (just (α′ , R)) σ A V = ↓-pk (makeConceal-ren α′ R σ A)

  revFrame-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ′)
    → mplug (renameMFrame ρ (revFrame rc (substᵗ σ A))) V
      ≡ revM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A) V
  revFrame-ren nothing σ A V = refl
  revFrame-ren (just (α′ , R)) σ A V = ↑-pk (〖〗-ren α′ R σ A)

  conFrame-ren : ∀ (rc : RConv Θ) (σ : Δ ⇒ˢ Θ) A (V : Term Θ′)
    → mplug (renameMFrame ρ (conFrame rc (substᵗ σ A))) V
      ≡ conM (renRConv ρ rc) (substᵗ (λ Z → renameᵗ ρv (σ Z)) A) V
  conFrame-ren nothing σ A V = refl
  conFrame-ren (just (α′ , R)) σ A V = ↓-pk (makeConceal-ren α′ R σ A)

------------------------------------------------------------------------
-- Applications of converted functions
------------------------------------------------------------------------

-- the argument, the application, and the conversion of the result
app-core : ∀ d s {Φ : Corr Δ Δ′} {A A′ B B′} (p : Φ ⊢ A ⊑ A′)
    (q : Φ ⊢ B ⊑ B′) w {δ₁ δ₂ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {Vl Vr Ul Ur} (vl : Value Vl) (vr : Value Vr)
    (FL : MFrame (ΔL w)) (FR : MFrame (ΔR w))
  → ℰ d s p w δ₁ Ul Ur
  → funRel d s p q w δ₁ Vl Vr
  → (∀ {w′} (e : w′ ⊒ w) {k} → k ≤ s → ∀ {Ql Qr} → Value Ql → Value Qr
       → 𝒱 d k q w′ (δ₁ ↑ᴵ e) Ql Qr
       → ℰ d k q w′ (δ₂ ↑ᴵ e) (mplug (renameMFrame (ρL e) FL) Ql)
           (mplug (renameMFrame (ρR e) FR) Qr))
  → ℰ d s q w δ₂ (mplug FL (Vl · Ul)) (mplug FR (Vr · Ur))
app-core d s p q w {δ₁} {δ₂} vl vr FL FR inner f K =
  ℰ-bind₂ d s q q w {δ₁ = δ₁} {δ₂ = δ₂} FL FR
    (ℰ-bind₂ d s p q w {δ₁ = δ₁} {δ₂ = δ₁}
      (just (app₂ _ vl)) (just (app₂ _ vr)) inner K₁)
    K
  where
  K₁ : ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ s → ∀ {Pl Pr} → Value Pl → Value Pr
    → 𝒱 d k p w′ (δ₁ ↑ᴵ e) Pl Pr → _
  K₁ e {k} k≤s {Pl} {Pr} pl pr r =
    ℰᵍ-map d k _
      (λ le′ w″ e′ V V′ → 𝒱≤-cast d (≤′-trans le′ (≤⇒≤′ k≤s)) le′ q w″)
      (f e (≤⇒≤′ k≤s) Pl Pr pl pr (𝒱≤-cast d ≤′-refl (≤⇒≤′ k≤s) p _ r))

-- a right step exactly when the right converts
RStep : ∀ {Θ} → RConv Θ → Term Θ → Term Θ → Set
RStep nothing M M′ = M ≡ M′
RStep (just c) M M′ = M —→ M′

-- the stages of an application's step: the counted side steps, unless
-- in `≻` the right does not convert
ℰ-app-steps : ∀ d {n N} {Φ : Corr Δ Δ′} {B B′} (q : Φ ⊢ B ⊑ B′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (rc : RConv (ΔR w))
    {Ml Ml′ Mr Mr′}
  → n ≤ N → Ml —→ Ml′ → RStep rc Mr Mr′
  → (∀ {s} → s ≤ n → ConB d rc s N → ℰ d s q w δ Ml′ Mr′)
  → ℰ d n q w δ Ml Mr
ℰ-app-steps ≺ {zero} q w rc le sl sr k = ℰ-zero ≺ q w
ℰ-app-steps ≺ {suc n} q w nothing le sl refl k =
  ℰ-stepL ≺ n q w sl (k (n≤1+n n) le)
ℰ-app-steps ≺ {suc n} q w (just c) le sl sr k =
  ℰ-stepL ≺ n q w sl (ℰ-stepR ≺ n q w sr (k (n≤1+n n) le))
ℰ-app-steps ≻ {n} q w nothing le sl refl k =
  ℰ-stepL ≻ n q w sl (k ≤-refl le)
ℰ-app-steps ≻ {zero} q w (just c) le sl sr k = ℰ-zero ≻ q w
ℰ-app-steps ≻ {suc n} q w (just c) le sl sr k =
  ℰ-stepL ≻ (suc n) q w sl (ℰ-stepR ≻ n q w sr (k (n≤1+n n) le))

-- the right's application of a converted function, when it converts
rightApp : ∀ {Θ} (rc : RConv Θ) {A B} {Vr Ur : Term Θ}
  → Value Vr → Value Ur
  → RStep rc (revM rc (A ⇒ B) Vr · Ur)
      (mplug (revFrame rc B) (Vr · conM rc A Ur))
rightApp nothing vr ur = refl
rightApp (just (α′ , R)) vr ur = β-reveal-⇒ vr ur

rightAppC : ∀ {Θ} (rc : RConv Θ) {A B} {Vr Ur : Term Θ}
  → Value Vr → Value Ur
  → RStep rc (conM rc (A ⇒ B) Vr · Ur)
      (mplug (conFrame rc B) (Vr · revM rc A Ur))
rightAppC nothing vr ur = refl
rightAppC (just (α′ , R)) vr ur = β-conceal-⇒ vr ur

ConB-ren : ∀ {Θ Θ′} d (ρ : Θ ↪ᵗ Θ′) (rc : RConv Θ) {k N}
  → ConB d rc k N → ConB d (renRConv ρ rc) k N
ConB-ren ≺ ρ rc cb = cb
ConB-ren ≻ ρ nothing cb = cb
ConB-ren ≻ ρ (just c) cb = cb

ConB-down : ∀ {Θ} d (rc : RConv Θ) {k n N} → k ≤ n
  → ConB d rc n N → ConB d rc k N
ConB-down ≺ rc le cb = ≤-<-trans le cb
ConB-down ≻ nothing le cb = ≤-trans le cb
ConB-down ≻ (just c) le cb = ≤-<-trans le cb

ConB-≤ : ∀ {Θ} d (rc : RConv Θ) {k N} → ConB d rc k N → k ≤ N
ConB-≤ ≺ rc cb = <⇒≤ cb
ConB-≤ ≻ nothing cb = cb
ConB-≤ ≻ (just c) cb = <⇒≤ cb

------------------------------------------------------------------------
-- Relations that do not read the interpretation
------------------------------------------------------------------------

module _ {Φ : Corr Δ Δ′} {w : World} {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {Vl Vr} where

  ★★-δ : ∀ d n → 𝒱 d n (★⊑★ {Φ = Φ}) w δ Vl Vr
    → 𝒱 d n (★⊑★ {Φ = Φ}) w δ′ Vl Vr
  ★★-δ ≺ n r = r
  ★★-δ ≻ zero r = r
  ★★-δ ≻ (suc k) r = r

  ι★-δ : ∀ d n {ι} → 𝒱 d n (ι⊑★ {Φ = Φ} {ι = ι}) w δ Vl Vr
    → 𝒱 d n (ι⊑★ {Φ = Φ} {ι = ι}) w δ′ Vl Vr
  ι★-δ ≺ n r = r
  ι★-δ ≻ zero r = r
  ι★-δ ≻ (suc k) r = r

  ιι-δ : ∀ d n {ι} → 𝒱 d n (ι⊑ι {Φ = Φ} {ι = ι}) w δ Vl Vr
    → 𝒱 d n (ι⊑ι {Φ = Φ} {ι = ι}) w δ′ Vl Vr
  ιι-δ ≺ n r = r
  ιι-δ ≻ n r = r

-- the right side of `⇒⊑★`: a function injected into `★`
funStar-map : ∀ {d n} {Φ : Corr Δ Δ′} {A B} {p : Φ ⊢ A ⊑ ★} {q : Φ ⊢ B ⊑ ★}
    {w} {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vl′ Vr}
  → (∀ {Wr} → Value Wr → funRel d n p q w δ Vl Wr
       → funRel d n p q w δ′ Vl′ Wr)
  → Value Vr → funStar d n p q w δ Vl Vr → funStar d n p q w δ′ Vl′ Vr
funStar-map f (v CT.《 i 》) (inj , r) = inj , f v r
funStar-map f (CT.ƛ N) ()
funStar-map f (CT.Λ v) ()
funStar-map f (CT.$ k) ()
funStar-map f (v CT.↑ rv) ()
funStar-map f (v CT.↓ cv) ()


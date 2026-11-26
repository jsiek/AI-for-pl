module proof.LR.CastCases4 where

-- File Charter:
--   * Two rows of the cast lemma (`proof.LR.CastLemma`, `CastCase`;
--     notes/logrel-dgg.md, "The cast lemma: the case table"):
--       - `case!!`: a left `c !` against a right `c′ !`.  The grounds
--         are related by precision (`ground⊑` of `groundAgree`).  At a
--         ground variable it is the base case `VarI.toP`.  At a closed
--         ground: if both casts are the identity at the ground, both
--         sides are injections already (`injPairι`, `injPair⇒`,
--         `injPair∀`); if neither is, both take their `ground` step and
--         the hypothesis at c against c′ is followed by the two
--         injections.  A cast that is the identity at its ground only
--         after the interpretation is refuted by `starFree` on the left
--         and `starFreeR` on the right.  If only the left is the
--         identity, the right is too (`aboveι`, `above⇒`, `above∀`).
--         If only the right is, at ground ι the left is refuted
--         (`belowι`); at `★ ⇒ ★` and `∀★` it is left open (`RowIdR`):
--         the hypothesis at c against `idᵍ G` relates the left to the
--         right's identity proxy, whose uses take counted right steps
--         that the real run does not take.
--       - `caseInst!⇒`: a left `inst c` against a right `(inst c′) !`
--         at ground `★ ⇒ ★`, into `⇒⊑★`: the right's `ground` step,
--         the hypothesis at `inst c` against `inst c′` at `⇒⊑⇒`, and
--         the right's injection alone (`injR⇒`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩; _《_》; inj)
open import Reduction using (_—→_; ground)
open import LR.Precision
open import LR.World
open import LR.Relation
open import LR.Frame using (cast)
open import proof.TypeSafety.Progress using (to-ground; same; other)
open import proof.LR.InterpProps using (ℰᵍ-≡; ℰᵍ-map; ℰ-resp; 𝒱-resp;
  ↑ᴵ-refl; ≈ᴵ-sym)
open import proof.LR.Monotone using (𝒱-down; funRel-down; 𝒱≤-cast)
open import proof.LR.Expression using (ℰ-value; ℰ-stepL; ℰ-stepR;
  ℰ-bind₂)
open import proof.LR.ConvBase using (ℰ-zero)
open import proof.LR.ConvLemma using (PreB; preB)
open import proof.LR.IdentityCast using (ℰ-stepL≤; 𝒱→starAt)
open import proof.LR.PrecisionUnique using (⊑-unique)
open import proof.LR.WorldProps using (⊒-refl)
open import proof.LR.CastLemma using (CastCase; CastHyp; sL; sR; σR; νL;
  νR; good; var; ren-refl; toW; VarI; starFree; starFreeR)
open import proof.LR.CastCases3 using (★-at; fun★-at; collapse!ι;
  collapse!⇒; collapse!∀)
open import proof.LR.GroundAgree using (groundAgree; ShapeRel; shapeOf; rb; rv;
  rf; ra)

------------------------------------------------------------------------
-- Both sides step
------------------------------------------------------------------------

ℰ-step2 : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Ml′ Mr Mr′}
  → Ml —→ Ml′ → Mr —→ Mr′ → (∀ {s} → s ≤ n → ℰ d s p w δ Ml′ Mr′)
  → ℰ d n p w δ Ml Mr
ℰ-step2 ≺ n p w sl sr k =
  ℰ-stepL≤ ≺ n p w sl (λ s≤ → ℰ-stepR ≺ _ p w sr (k s≤))
ℰ-step2 ≻ zero p w sl sr k = ℰ-zero ≻ p w
ℰ-step2 ≻ (suc m) p w sl sr k =
  ℰ-stepR ≻ m p w sr (ℰ-stepL ≻ m p w sl (k (n≤1+n m)))

------------------------------------------------------------------------
-- Injections on both sides, and on the right alone
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} where

  injPairι : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ μ′} {ι} {W Wr}
    → 𝒱 d k (ι⊑ι {Φ = Φ} {ι = ι}) w δ W Wr
    → 𝒱 d k (★⊑★ {Φ = Φ}) w δ
        (W ⟨ _! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (idᵍ {μ = μ} (‵ ι))
               ⦃ Ans = nonstar-ι ⦄ ⟩)
        (Wr ⟨ _! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (idᵍ {μ = μ′} (‵ ι))
               ⦃ Ans = nonstar-ι ⦄ ⟩)
  injPairι ≺ k w (κ , refl , refl) = refl , refl
  injPairι ≻ zero w a = tt
  injPairι ≻ (suc k) w (κ , refl , refl) = refl , refl

  injPair⇒ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ μ′} {W Wr}
    → 𝒱 d k (⇒⊑⇒ (★⊑★ {Φ = Φ}) ★⊑★) w δ W Wr
    → 𝒱 d k (★⊑★ {Φ = Φ}) w δ
        (W ⟨ _! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (idᵍ {μ = μ} ★⇒★)
               ⦃ Ans = nonstar-⇒ ⦄ ⟩)
        (Wr ⟨ _! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (idᵍ {μ = μ′} ★⇒★)
               ⦃ Ans = nonstar-⇒ ⦄ ⟩)
  injPair⇒ ≺ zero w f = tt
  injPair⇒ ≺ (suc k) w f =
    tt , fun★-at ≺ k w (funRel-down ≺ (n≤1+n k) ★⊑★ ★⊑★ w f)
  injPair⇒ ≻ zero w f = tt
  injPair⇒ ≻ (suc k) w f =
    tt , fun★-at ≻ k w (funRel-down ≻ (n≤1+n k) ★⊑★ ★⊑★ w f)

  -- the pair clause at `★ ⊑ ★` is `★`'s `∀★` payload one stage down
  pair→starAll : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ′} {W Wr}
    → allPair d (suc k) (★⊑★ {Φ = pair Φ}) w δ W Wr
    → starAll d k w W
        (Wr ⟨ _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (idᵍ {μ = μ′} ∀★)
               ⦃ Ans = nonstar-∀ ⦄ ⟩)
  pair→starAll d k w f =
    tt , λ e le c₀ wf T₀ eqT →
      ℰᵍ-map d _ _
        (λ le′ w″ e′ V V′ a →
          𝒱→starAt d (≤′-trans le′ le) w″
            (★-at d _ w″
              (𝒱≤-cast d (≤′-trans le′ (≤′-step le)) ≤′-refl ★⊑★ w″ a)))
        (f e (≤′-step le) c₀ wf T₀ eqT ★ refl)

  injPair∀ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ μ′} {W Wr}
    → 𝒱 d k (∀⊑∀ (★⊑★ {Φ = pair Φ})) w δ W Wr
    → 𝒱 d k (★⊑★ {Φ = Φ}) w δ
        (W ⟨ _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (idᵍ {μ = μ} ∀★)
               ⦃ Ans = nonstar-∀ ⦄ ⟩)
        (Wr ⟨ _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (idᵍ {μ = μ′} ∀★)
               ⦃ Ans = nonstar-∀ ⦄ ⟩)
  injPair∀ ≺ zero w f = tt
  injPair∀ ≺ (suc k) w {δ} {μ′ = μ′} f =
    pair→starAll ≺ k w {δ = δ} {μ′ = μ′} f
  injPair∀ ≻ zero w f = tt
  injPair∀ ≻ (suc k) w {δ} {μ′ = μ′} f =
    pair→starAll ≻ k w {δ = δ} {μ′ = μ′} f

  -- the right alone injects at `★ ⇒ ★`
  injR⇒ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ′} {A B}
      {p : Φ ⊢ A ⊑ ★} {q : Φ ⊢ B ⊑ ★} {W Wr}
    → 𝒱 d k (⇒⊑⇒ p q) w δ W Wr
    → 𝒱 d k (⇒⊑★ p q) w δ W
        (Wr ⟨ _! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (idᵍ {μ = μ′} ★⇒★)
               ⦃ Ans = nonstar-⇒ ⦄ ⟩)
  injR⇒ ≺ k w f = tt , f
  injR⇒ ≻ zero w f = tt
  injR⇒ ≻ (suc k) w {p = p} {q} f =
    tt , funRel-down ≻ (n≤1+n k) p q w f

------------------------------------------------------------------------
-- Precision at closed grounds
------------------------------------------------------------------------

private
  variable
    Δ Δ′ : TyCtx

-- a closed ground is below itself only, besides `★`
aboveι : ∀ {Φ : Corr Δ Δ′} {ι C′} → Φ ⊢ ‵ ι ⊑ C′ → C′ ≢ ★ → C′ ≡ ‵ ι
aboveι ι⊑ι ne = refl
aboveι ι⊑★ ne = ⊥-elim (ne refl)

above⇒ : ∀ {Φ : Corr Δ Δ′} {C′} → Φ ⊢ ★ ⇒ ★ ⊑ C′ → C′ ≢ ★
  → C′ ≡ ★ ⇒ ★
above⇒ (⇒⊑⇒ ★⊑★ ★⊑★) ne = refl
above⇒ (⇒⊑★ p q) ne = ⊥-elim (ne refl)

above∀ : ∀ {Φ : Corr Δ Δ′} {C′} → Φ ⊢ `∀ ★ ⊑ C′ → C′ ≢ ★ → C′ ≡ `∀ ★
above∀ (∀⊑∀ ★⊑★) ne = refl
above∀ (∀⊑ a () p) ne
above∀ ∀★⊑★ ne = ⊥-elim (ne refl)
above∀ (∀⊑★ ns p) ne = ⊥-elim (ne refl)

-- no variable occurs below a base type
noOccι : ∀ {Φ : Corr Δ Δ′} {B ι} {X} → Φ ⊢ B ⊑ ‵ ι → X ∈ᵗ B → ⊥
noOccι ι⊑ι ()
noOccι (∀⊑ a z p) (∈-all i) = noOccι p i

-- below a base type is that type only
belowι : ∀ {Φ : Corr Δ Δ′} {B ι} → Φ ⊢ B ⊑ ‵ ι → B ≡ ‵ ι
belowι ι⊑ι = refl
belowι (∀⊑ a z p) = ⊥-elim (noOccι p z)

------------------------------------------------------------------------
-- A left `c !` against a right `c′ !`
------------------------------------------------------------------------

-- the left is not the identity at its ground, the right is, at
-- `★ ⇒ ★` or `∀★` (left open)
OpenG : ∀ {Θ} {G : Ty Θ} → Ground G → Set
OpenG (＇ X) = ⊥
OpenG (‵ ι) = ⊥
OpenG ★⇒★ = ⊤
OpenG ∀★ = ⊤

RowIdR : Set₁
RowIdR = ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A G : Ty Δ} {G′ : Ty Δ′}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄ (c : ν ⊢ A ∼ G)
    ⦃ Ans : NonStar A ⦄ (Hᵍ : Ground G′) ⦃ H∼★ : ν′ ⊢ G′ ∼★ ⦄
    ⦃ Hns : NonStar G′ ⦄
  → OpenG Hᵍ → A ≢ G
  → CastCase (_! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄)
      (_! ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ (idᵍ {μ = ν′} Hᵍ) ⦃ Ans = Hns ⦄)

-- the two grounds, related by their shapes
data GPair {Δ Δ′} (Φ : Corr Δ Δ′) : ∀ {G : Ty Δ} {G′ : Ty Δ′}
    → Ground G → Ground G′ → Set where
  pv : ∀ {X Y} → Φ ∋ X ↔ Y → GPair Φ (＇ X) (＇ Y)
  pι : ∀ {ι} → GPair Φ (‵ ι) (‵ ι)
  p⇒ : GPair Φ ★⇒★ ★⇒★
  p∀ : GPair Φ ∀★ ∀★

gpair : ∀ {Φ : Corr Δ Δ′} {G G′} (g : Ground G) (g′ : Ground G′)
  → ShapeRel Φ (shapeOf G) (shapeOf G′) → GPair Φ g g′
gpair (＇ X) (＇ Y) (rv x) = pv x
gpair (‵ ι) (‵ ι′) rb = pι
gpair ★⇒★ ★⇒★ rf = p⇒
gpair ∀★ ∀★ ra = p∀
gpair (＇ X) (‵ ι) ()
gpair (＇ X) ★⇒★ ()
gpair (＇ X) ∀★ ()
gpair (‵ ι) (＇ Y) ()
gpair (‵ ι) ★⇒★ ()
gpair (‵ ι) ∀★ ()
gpair ★⇒★ (＇ Y) ()
gpair ★⇒★ (‵ ι) ()
gpair ★⇒★ ∀★ ()
gpair ∀★ (＇ Y) ()
gpair ∀★ (‵ ι) ()
gpair ∀★ ★⇒★ ()

-- at a ground variable: the base case
varCase : ∀ d n {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {Φ : Corr Δ Δ′} {X Y}
    (x : Φ ∋ X ↔ Y) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    (h : CastHyp Φ d w δ ν ν′) {v v′} (eq : ν ‼ X ≡ v) (t : VarTo★ v)
    (eq′ : ν′ ‼ Y ≡ v′) (t′ : VarTo★ v′) {Vl Vr}
  → Value Vl → Value Vr → 𝒱 d n (X⊑Y x) w δ Vl Vr
  → ℰ d n (★⊑★ {Φ = Φ}) w δ (Vl ⟨ toW (sL h) X eq t ⟩)
      (Vr ⟨ toW (sR h) Y eq′ t′ ⟩)
varCase d n x w {δ} h eq to★-dynamic eq′ to★-dynamic vl vr a =
  ℰᵍ-≡ (ren-refl {μ = νL h} (toW (sL h) _ eq to★-dynamic) _)
    (ren-refl {μ = νR h} (toW (sR h) _ eq′ to★-dynamic) _)
    (ℰ-resp d n ★⊑★ w (↑ᴵ-refl {w = w} δ)
      (VarI.toP (var h (⊒-refl w)) x eq to★-dynamic eq′ to★-dynamic n vl vr
        (𝒱-resp d n (X⊑Y x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
varCase d n x w {δ} h eq to★-dynamic eq′ to★-cross vl vr a =
  ℰᵍ-≡ (ren-refl {μ = νL h} (toW (sL h) _ eq to★-dynamic) _)
    (ren-refl {μ = νR h} (toW (sR h) _ eq′ to★-cross) _)
    (ℰ-resp d n ★⊑★ w (↑ᴵ-refl {w = w} δ)
      (VarI.toP (var h (⊒-refl w)) x eq to★-dynamic eq′ to★-cross n vl vr
        (𝒱-resp d n (X⊑Y x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
varCase d n x w {δ} h eq to★-cross eq′ to★-dynamic vl vr a =
  ℰᵍ-≡ (ren-refl {μ = νL h} (toW (sL h) _ eq to★-cross) _)
    (ren-refl {μ = νR h} (toW (sR h) _ eq′ to★-dynamic) _)
    (ℰ-resp d n ★⊑★ w (↑ᴵ-refl {w = w} δ)
      (VarI.toP (var h (⊒-refl w)) x eq to★-cross eq′ to★-dynamic n vl vr
        (𝒱-resp d n (X⊑Y x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
varCase d n x w {δ} h eq to★-cross eq′ to★-cross vl vr a =
  ℰᵍ-≡ (ren-refl {μ = νL h} (toW (sL h) _ eq to★-cross) _)
    (ren-refl {μ = νR h} (toW (sR h) _ eq′ to★-cross) _)
    (ℰ-resp d n ★⊑★ w (↑ᴵ-refl {w = w} δ)
      (VarI.toP (var h (⊒-refl w)) x eq to★-cross eq′ to★-cross n vl vr
        (𝒱-resp d n (X⊑Y x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))

caseV : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty Δ} {C′ : Ty Δ′}
    {X Y} ⦃ G∼★ : ν ⊢ ＇ X ∼★ ⦄ (c : ν ⊢ A ∼ ＇ X) ⦃ Ans : NonStar A ⦄
    ⦃ H∼★ : ν′ ⊢ ＇ Y ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ ＇ Y) ⦃ Cns : NonStar C′ ⦄
  → CastCase (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄)
      (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄)
caseV (？ c) ⦃ Ans = () ⦄
caseV c@((inst c₀) B≢★) ⦃ Ans = a ⦄ c′ =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all a)
caseV (id (＇ _)) (？ c′) ⦃ Cns = () ⦄
caseV (id (＇ _)) c′@((inst c₀′) B≢★) ⦃ Cns = a′ ⦄ =
  ⊥-elim (nonstar-nonvar-to-var-impossible c′ nonvar-all a′)
caseV ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ _)) ⦃ H∼★ = X∼★ᵍ eq′ ⦄ (id (＇ _))
    d n (X⊑Y x) ★⊑★ w h pC pA vl vr (t , a) =
  varCase d n x w h eq to★-dynamic eq′ to★-dynamic vl vr a
caseV ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ _)) ⦃ H∼★ = X∼★ᶜ eq′ ⦄ (id (＇ _))
    d n (X⊑Y x) ★⊑★ w h pC pA vl vr (t , a) =
  varCase d n x w h eq to★-dynamic eq′ to★-cross vl vr a
caseV ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ _)) ⦃ H∼★ = X∼★ᵍ eq′ ⦄ (id (＇ _))
    d n (X⊑Y x) ★⊑★ w h pC pA vl vr (t , a) =
  varCase d n x w h eq to★-cross eq′ to★-dynamic vl vr a
caseV ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ _)) ⦃ H∼★ = X∼★ᶜ eq′ ⦄ (id (＇ _))
    d n (X⊑Y x) ★⊑★ w h pC pA vl vr (t , a) =
  varCase d n x w h eq to★-cross eq′ to★-cross vl vr a

-- the closed grounds
module _ (op : RowIdR) where

  caseι : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty Δ} {C′ : Ty Δ′}
      {ι} ⦃ G∼★ : ν ⊢ ‵ ι ∼★ ⦄ (c : ν ⊢ A ∼ ‵ ι) ⦃ Ans : NonStar A ⦄
      ⦃ H∼★ : ν′ ⊢ ‵ ι ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ ‵ ι) ⦃ Cns : NonStar C′ ⦄
    → CastCase c c′
    → CastCase (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄)
        (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄)
  caseι {ι = ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ c′ ih d n p ★⊑★ w h pC pA
      vl vr hyp
      with to-ground (‵ ι) c | to-ground (‵ ι) c′
  caseι {ι = ι} ⦃ G∼★ = ι∼★ ⦄ .(id (‵ ι)) ⦃ H∼★ = ι∼★ ⦄ .(id (‵ ι)) ih
      d n p ★⊑★ w {δ} h pC pA {Vl} {Vr} vl vr (t , a) | same | same =
    ℰ-value d n ★⊑★ w (vl 《 inj 》) (vr 《 inj 》)
      (injPairι d n w (subst (λ q → 𝒱 d n q w δ Vl Vr) (⊑-unique p ι⊑ι) a))
  caseι {ι = ι} ⦃ G∼★ = ι∼★ ⦄ .(id (‵ ι)) ⦃ H∼★ = ι∼★ ⦄ c′
      ⦃ Cns = a′ ⦄ ih d n p ★⊑★ w h pC pA vl vr hyp | same | other C≢ =
    ⊥-elim (C≢ (aboveι p (nonStar≢★ a′)))
  caseι {ι = ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ .(id (‵ ι)) ih
      d n p ★⊑★ w h pC pA vl vr hyp | other A≢ | same =
    ⊥-elim (A≢ (belowι p))
  caseι {A = A} {C′} {ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      with substᵗ (δl δ) A ≟Ty ‵ ι | substᵗ (σR h) C′ ≟Ty ‵ ι
  caseι {A = A} {C′} {ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | yes eq | yes eq′ =
    ⊥-elim (collapse!ι (starFree h) c A≢ eq)
  caseι {A = A} {C′} {ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | yes eq | no ne′ =
    ⊥-elim (collapse!ι (starFree h) c A≢ eq)
  caseι {A = A} {C′} {ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | no ne | yes eq′ =
    ⊥-elim (collapse!ι (starFreeR h) c′ C≢ eq′)
  caseι {A = A} {C′} {ι} ⦃ G∼★ = ι∼★ ⦄ c ⦃ H∼★ = ι∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr (t , a) | other A≢ | other C≢
      | no ne | no ne′ =
    ℰ-step2 d n ★⊑★ w
      (ground ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-ι ⦄
        vl ne)
      (ground ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-ι ⦄
        vr ne′)
      (λ {s} s≤ → ℰ-bind₂ d s ι⊑ι ★⊑★ w
        (just (cast (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (id (‵ ι))
          ⦃ Ans = nonstar-ι ⦄)))
        (just (cast (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (id (‵ ι))
          ⦃ Ans = nonstar-ι ⦄)))
        (ih d s p ι⊑ι w h pC (preB refl) vl vr
          (t , 𝒱-down d s≤ p w (good h) a))
        (λ e k≤ ql qr r →
          ℰ-value d _ ★⊑★ _ (ql 《 inj 》) (qr 《 inj 》) (injPairι d _ _ r)))

  case⇒ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty Δ} {C′ : Ty Δ′}
      ⦃ G∼★ : ν ⊢ ★ ⇒ ★ ∼★ ⦄ (c : ν ⊢ A ∼ ★ ⇒ ★) ⦃ Ans : NonStar A ⦄
      ⦃ H∼★ : ν′ ⊢ ★ ⇒ ★ ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ ★ ⇒ ★)
      ⦃ Cns : NonStar C′ ⦄
    → CastCase c c′
    → CastCase (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄)
        (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄)
  case⇒ ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ H∼★ = ⇒∼★ ⦄ c′ ih d n p ★⊑★ w h pC pA
      vl vr hyp
      with to-ground ★⇒★ c | to-ground ★⇒★ c′
  case⇒ ⦃ G∼★ = ⇒∼★ ⦄ .(id ★ ↦ id ★) ⦃ H∼★ = ⇒∼★ ⦄ .(id ★ ↦ id ★) ih
      d n p ★⊑★ w {δ} h pC pA {Vl} {Vr} vl vr (t , a) | same | same =
    ℰ-value d n ★⊑★ w (vl 《 inj 》) (vr 《 inj 》)
      (injPair⇒ d n w
        (subst (λ q → 𝒱 d n q w δ Vl Vr) (⊑-unique p (⇒⊑⇒ ★⊑★ ★⊑★)) a))
  case⇒ ⦃ G∼★ = ⇒∼★ ⦄ .(id ★ ↦ id ★) ⦃ H∼★ = ⇒∼★ ⦄ c′ ⦃ Cns = a′ ⦄ ih
      d n p ★⊑★ w h pC pA vl vr hyp | same | other C≢ =
    ⊥-elim (C≢ (above⇒ p (nonStar≢★ a′)))
  case⇒ ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ Ans = a ⦄ ⦃ H∼★ = ⇒∼★ ⦄ .(id ★ ↦ id ★)
      ⦃ Cns = a′ ⦄ ih d n p ★⊑★ w h pC pA vl vr hyp | other A≢ | same =
    op ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ Ans = a ⦄ ★⇒★ ⦃ H∼★ = ⇒∼★ ⦄
      ⦃ Hns = a′ ⦄ tt A≢ d n p ★⊑★ w h pC pA vl vr hyp
  case⇒ {A = A} {C′} ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ H∼★ = ⇒∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      with substᵗ (δl δ) A ≟Ty ★ ⇒ ★ | substᵗ (σR h) C′ ≟Ty ★ ⇒ ★
  case⇒ {A = A} {C′} ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ H∼★ = ⇒∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | yes eq | yes eq′ =
    ⊥-elim (collapse!⇒ (starFree h) c A≢ eq)
  case⇒ {A = A} {C′} ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ H∼★ = ⇒∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | yes eq | no ne′ =
    ⊥-elim (collapse!⇒ (starFree h) c A≢ eq)
  case⇒ {A = A} {C′} ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ H∼★ = ⇒∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | no ne | yes eq′ =
    ⊥-elim (collapse!⇒ (starFreeR h) c′ C≢ eq′)
  case⇒ {A = A} {C′} ⦃ G∼★ = ⇒∼★ ⦄ c ⦃ H∼★ = ⇒∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr (t , a) | other A≢ | other C≢
      | no ne | no ne′ =
    ℰ-step2 d n ★⊑★ w
      (ground ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-⇒ ⦄
        vl ne)
      (ground ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-⇒ ⦄
        vr ne′)
      (λ {s} s≤ → ℰ-bind₂ d s (⇒⊑⇒ ★⊑★ ★⊑★) ★⊑★ w
        (just (cast (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (id ★ ↦ id ★)
          ⦃ Ans = nonstar-⇒ ⦄)))
        (just (cast (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (id ★ ↦ id ★)
          ⦃ Ans = nonstar-⇒ ⦄)))
        (ih d s p (⇒⊑⇒ ★⊑★ ★⊑★) w h pC (preB refl) vl vr
          (t , 𝒱-down d s≤ p w (good h) a))
        (λ e k≤ ql qr r →
          ℰ-value d _ ★⊑★ _ (ql 《 inj 》) (qr 《 inj 》)
            (injPair⇒ d _ _ r)))

  case∀ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty Δ} {C′ : Ty Δ′}
      ⦃ G∼★ : ν ⊢ `∀ ★ ∼★ ⦄ (c : ν ⊢ A ∼ `∀ ★) ⦃ Ans : NonStar A ⦄
      ⦃ H∼★ : ν′ ⊢ `∀ ★ ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ `∀ ★)
      ⦃ Cns : NonStar C′ ⦄
    → CastCase c c′
    → CastCase (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄)
        (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄)
  case∀ ⦃ G∼★ = ∀∼★ ⦄ c ⦃ H∼★ = ∀∼★ ⦄ c′ ih d n p ★⊑★ w h pC pA
      vl vr hyp
      with to-ground ∀★ c | to-ground ∀★ c′
  case∀ ⦃ G∼★ = ∀∼★ ⦄ .(∀ᶜ (id ★)) ⦃ H∼★ = ∀∼★ ⦄ .(∀ᶜ (id ★)) ih
      d n p ★⊑★ w {δ} h pC pA {Vl} {Vr} vl vr (t , a) | same | same =
    ℰ-value d n ★⊑★ w (vl 《 inj 》) (vr 《 inj 》)
      (injPair∀ d n w
        (subst (λ q → 𝒱 d n q w δ Vl Vr) (⊑-unique p (∀⊑∀ ★⊑★)) a))
  case∀ ⦃ G∼★ = ∀∼★ ⦄ .(∀ᶜ (id ★)) ⦃ H∼★ = ∀∼★ ⦄ c′ ⦃ Cns = a′ ⦄ ih
      d n p ★⊑★ w h pC pA vl vr hyp | same | other C≢ =
    ⊥-elim (C≢ (above∀ p (nonStar≢★ a′)))
  case∀ ⦃ G∼★ = ∀∼★ ⦄ c ⦃ Ans = a ⦄ ⦃ H∼★ = ∀∼★ ⦄ .(∀ᶜ (id ★))
      ⦃ Cns = a′ ⦄ ih d n p ★⊑★ w h pC pA vl vr hyp | other A≢ | same =
    op ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ c ⦃ Ans = a ⦄ ∀★ ⦃ H∼★ = ∀∼★ ⦄
      ⦃ Hns = a′ ⦄ tt A≢ d n p ★⊑★ w h pC pA vl vr hyp
  case∀ {A = A} {C′} ⦃ G∼★ = ∀∼★ ⦄ c ⦃ H∼★ = ∀∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      with substᵗ (δl δ) A ≟Ty `∀ ★ | substᵗ (σR h) C′ ≟Ty `∀ ★
  case∀ {A = A} {C′} ⦃ G∼★ = ∀∼★ ⦄ c ⦃ H∼★ = ∀∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | yes eq | yes eq′ =
    ⊥-elim (collapse!∀ (starFree h) c A≢ eq)
  case∀ {A = A} {C′} ⦃ G∼★ = ∀∼★ ⦄ c ⦃ H∼★ = ∀∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | yes eq | no ne′ =
    ⊥-elim (collapse!∀ (starFree h) c A≢ eq)
  case∀ {A = A} {C′} ⦃ G∼★ = ∀∼★ ⦄ c ⦃ H∼★ = ∀∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr hyp | other A≢ | other C≢
      | no ne | yes eq′ =
    ⊥-elim (collapse!∀ (starFreeR h) c′ C≢ eq′)
  case∀ {A = A} {C′} ⦃ G∼★ = ∀∼★ ⦄ c ⦃ H∼★ = ∀∼★ ⦄ c′ ih
      d n p ★⊑★ w {δ} h pC pA vl vr (t , a) | other A≢ | other C≢
      | no ne | no ne′ =
    ℰ-step2 d n ★⊑★ w
      (ground ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-∀ ⦄
        vl ne)
      (ground ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-∀ ⦄
        vr ne′)
      (λ {s} s≤ → ℰ-bind₂ d s (∀⊑∀ ★⊑★) ★⊑★ w
        (just (cast (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (∀ᶜ (id ★))
          ⦃ Ans = nonstar-∀ ⦄)))
        (just (cast (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (∀ᶜ (id ★))
          ⦃ Ans = nonstar-∀ ⦄)))
        (ih d s p (∀⊑∀ ★⊑★) w h pC (preB refl) vl vr
          (t , 𝒱-down d s≤ p w (good h) a))
        (λ e k≤ ql qr r →
          ℰ-value d _ ★⊑★ _ (ql 《 inj 》) (qr 《 inj 》)
            (injPair∀ d _ _ r)))

  -- the row: by the grounds, which are related (`groundAgree`)
  case!! : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A G : Ty Δ}
      {C′ G′ : Ty Δ′} ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
      (c : ν ⊢ A ∼ G) ⦃ Ans : NonStar A ⦄ (Hᵍ : Ground G′)
      ⦃ H∼★ : ν′ ⊢ G′ ∼★ ⦄ (c′ : ν′ ⊢ C′ ∼ G′) ⦃ Cns : NonStar C′ ⦄
    → CastCase c c′
    → CastCase (_! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ c ⦃ Ans = Ans ⦄)
        (_! ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ c′ ⦃ Ans = Cns ⦄)
  case!! ⦃ Gᵍ = g ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ g′ ⦃ H∼★ = s′ ⦄ c′
      ⦃ Cns = a′ ⦄ ih d n p r w h pC pA vl vr hyp
      with gpair g g′
             (groundAgree p (nonStar≢★ a′) c (ground≢★ g) c′ (ground≢★ g′))
  case!! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ (＇ Y)
      ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih d n p r w h pC pA vl vr hyp
      | pv x =
    caseV ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄
      d n p r w h pC pA vl vr hyp
  case!! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ (‵ ι)
      ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih d n p r w h pC pA vl vr hyp
      | pι =
    caseι ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih
      d n p r w h pC pA vl vr hyp
  case!! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ ★⇒★
      ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih d n p r w h pC pA vl vr hyp
      | p⇒ =
    case⇒ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih
      d n p r w h pC pA vl vr hyp
  case!! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ ∀★
      ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih d n p r w h pC pA vl vr hyp
      | p∀ =
    case∀ ⦃ G∼★ = s ⦄ c ⦃ Ans = a ⦄ ⦃ H∼★ = s′ ⦄ c′ ⦃ Cns = a′ ⦄ ih
      d n p r w h pC pA vl vr hyp

------------------------------------------------------------------------
-- A left `inst c` against a right `(inst c′) !` at `★ ⇒ ★`, into
-- `⇒⊑★`
------------------------------------------------------------------------

caseInst!⇒ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A : Ty (suc Δ)}
    {B₁ B₂ : Ty Δ} {A′ : Ty (suc Δ′)} ⦃ Anv : NonVar A ⦄
    ⦃ z : zero ∈ᵗ A ⦄ (c : instᵐ ν ⊢ A ∼ ⇑ᵗ (B₁ ⇒ B₂))
    (B≢★ : B₁ ⇒ B₂ ≢ ★) ⦃ Anv′ : NonVar A′ ⦄ ⦃ z′ : zero ∈ᵗ A′ ⦄
    (c′ : instᵐ ν′ ⊢ A′ ∼ ⇑ᵗ (★ ⇒ ★)) (n′ : ★ ⇒ ★ ≢ ★)
    ⦃ Cns : NonStar (`∀ A′) ⦄
  → CastCase ((inst c) B≢★) ((inst c′) n′)
  → ∀ d n {Φ : Corr Δ Δ′} (p : Φ ⊢ `∀ A ⊑ `∀ A′) (q₁ : Φ ⊢ B₁ ⊑ ★)
      (q₂ : Φ ⊢ B₂ ⊑ ★) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
      (h : CastHyp Φ d w δ ν ν′)
  → PreB w (δr δ) (σR h) (`∀ A′) → PreB w (δr δ) (σR h) ★
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱ᵀ d n p w δ Vl Vr
  → ℰ d n (⇒⊑★ q₁ q₂) w δ (Vl ⟨ subst∼ (sL h) ((inst c) B≢★) ⟩)
      (Vr ⟨ subst∼ (sR h)
              (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ((inst c′) n′)
                ⦃ Ans = Cns ⦄) ⟩)
caseInst!⇒ c B≢★ c′ n′ ih ≺ n p q₁ q₂ w h pC pA vl vr hyp =
  ℰ-stepR ≺ n (⇒⊑★ q₁ q₂) w
    (ground ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-⇒ ⦄
      vr (λ ()))
    (ℰ-bind₂ ≺ n (⇒⊑⇒ q₁ q₂) (⇒⊑★ q₁ q₂) w nothing
      (just (cast (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (id ★ ↦ id ★)
        ⦃ Ans = nonstar-⇒ ⦄)))
      (ih ≺ n p (⇒⊑⇒ q₁ q₂) w h pC (preB refl) vl vr hyp)
      (λ e k≤ ql qr r →
        ℰ-value ≺ _ (⇒⊑★ q₁ q₂) _ ql (qr 《 inj 》) (tt , r)))
caseInst!⇒ c B≢★ c′ n′ ih ≻ zero p q₁ q₂ w h pC pA vl vr hyp =
  ℰ-zero ≻ (⇒⊑★ q₁ q₂) w
caseInst!⇒ c B≢★ c′ n′ ih ≻ (suc m) p q₁ q₂ w h pC pA vl vr (t , a) =
  ℰ-stepR ≻ m (⇒⊑★ q₁ q₂) w
    (ground ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-⇒ ⦄
      vr (λ ()))
    (ℰ-bind₂ ≻ m (⇒⊑⇒ q₁ q₂) (⇒⊑★ q₁ q₂) w nothing
      (just (cast (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (id ★ ↦ id ★)
        ⦃ Ans = nonstar-⇒ ⦄)))
      (ih ≻ m p (⇒⊑⇒ q₁ q₂) w h pC (preB refl) vl vr
        (t , 𝒱-down ≻ (n≤1+n m) p w (good h) a))
      (λ e k≤ ql qr r →
        ℰ-value ≻ _ (⇒⊑★ q₁ q₂) _ ql (qr 《 inj 》) (injR⇒ ≻ _ _ r)))

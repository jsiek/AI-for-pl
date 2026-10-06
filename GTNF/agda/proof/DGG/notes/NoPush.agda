module proof.DGG.notes.NoPush where

-- File Charter:
--   * WITH CLAIM-REP (design.md D29), CAN PUSHES GO?  (NoPush.md.)  A
--     local copy of the real relation (TermImprecision) with NO pending
--     names: every rule is stated at a world with `πʷ = []` (so the
--     index is the plain `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′`), `Λ⊑`
--     claims only `claim-fresh` or `claim-rep`, `cast⊑`, `⟪⟫⊑` and
--     `⊑⟪⟫` have no `CastClaim`, `BdyClaim`, `Push`.  13 relation
--     rules are verbatim; the 4 changed rules lose their side relation.
--   * §1 the relation `_∣_⊢_⊑ⁿ_∶_`; §2 `toReal`: it is a SUB-relation
--     of the real one (so every non-derivability result of the real
--     relation holds here: C1-C5, C4g); §3 `lift`: a real derivation
--     with no push, pop or pass (`NoPend d`, which normalizes to ⊤ on
--     push-free derivations) is one here, so every push-free corpus
--     block carries over by `lift d _`; §4 the corpus blocks that
--     PUSH, re-derived with claim-rep and no push: P3 = Ch X0, Cg X0,
--     C12 X0, L3c pre/post, L3d before, K (`VL⊑RF`, `lk₁⊑rk₄`,
--     `lk₁⊑rk₃`, `sim-K`, `dgg1-K`), H1 (state 2 and the final pair);
--     §5 C2 X0 (a left GEN value against a right Inst boundary) is NOT
--     derivable here, in any world, at any index: the boundary's
--     premise index `∀X.X→X ⊑ X→X` (or `★→★ ⊑ X→X`, `ℕ→ℕ ⊑ X→X` for
--     the other routes) is empty at a world with no pending name.
--   * Not a Def module, not imported by All.agda.  No holes, no
--     postulates.  LEFT is the more precise side.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product
  using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision using (ConvImp)
open import TermImprecision
  using (Lit; lit-$; CastTy; cast-ty; NuTy; BdyTy; NuConversionImp;
         BdyConversionImp; Claim; claim-fresh; claim-pop; claim-rep;
         CastClaim; cc-plain; cc-∀; cc-gen; BdyClaim; bc-plain; bc-∀;
         Push; push; Carried; ca-[]; ca-∷; push-none; CastGrant;
         no-grant; grant; Grants; cast-inv; ⟪⟫-inv; ν-inv)
import TermImprecision as R

private
  variable
    Δ Δ′ Δᵢ : Ctxᵗ

------------------------------------------------------------------------
-- 1. The relation with no pending names
------------------------------------------------------------------------

-- `Λ⊑`'s binder: fresh and left-only, or claim-rep (D29); no pop
data ClaimN : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  n-fresh : ∀ {Ω ϱᵍ ϱˡ κ} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
    → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in ClaimN W (W ⊕ᴸ)
  n-rep   : ∀ {Ω ϱᵍ ϱˡ κ β} {ηᴸ : names Δ ↪ Ω} {ηᴿ : names Δ′ ↪ Ω}
    → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      Δ′ ∋rep β := ★
    → ¬ (names Δ′ ∋ᵅ β)
    → NoNamedPartner W β
    → ClaimN W (W ⊕ᴸ⇔ β)

claimN→ : ∀ {W : World Δ Δ′} {W₁} → ClaimN W W₁ → Claim W W₁
claimN→ n-fresh          = claim-fresh
claimN→ (n-rep h n np)   = claim-rep h n np

infix 3 _∣_⊢_⊑ⁿ_∶_

data _∣_⊢_⊑ⁿ_∶_ {Δ Δ′ : Ctxᵗ}
    : (W : World Δ Δ′) → CtxImp W → Term → Term
    → {A A′ : Ty} → A ⊑ᵂ⟨ W ⟩ A′ → Set where

  x⊑x : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
    → γ ∋ʷ x ⦂ ctx-imp A A′ p
    → W ∣ γ ⊢ ` x ⊑ⁿ ` x ∶ p

  κ⊑κ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ k ι}
    → Lit k ι
    → (p : ι ⊑ᵂ⟨ W ⟩ ι)
    → W ∣ γ ⊢ k ⊑ⁿ k ∶ p

  ƛ⊑ƛ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → Δ ⊢ᵗ A
    → Δ′ ⊢ᵗ A′
    → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ⁿ N′ ∶ pB
    → W ∣ γ ⊢ ƛ A ∙ N ⊑ⁿ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

  ·⊑· : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ L L′ M M′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ⁿ L′ ∶ ⇒⊑⇒ pA pB
    → W ∣ γ ⊢ M ⊑ⁿ M′ ∶ pA
    → W ∣ γ ⊢ L · M ⊑ⁿ L′ · M′ ∶ pB

  blame⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ ℓ M′ A A′}
    → Δ ⊢ᵗ A
    → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
    → (p : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ blame ℓ ⊑ⁿ M′ ∶ p

  cast⊑cast : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ M M′ μ μ′ c c′ B B′ A A′} {p : B ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ⁿ M′ ∶ p
    → CastTy Δ μ c B A
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ⁿ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  -- CHANGED: no CastClaim (plain only)
  cast⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ M M′ μ c B A A′} {p : B ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ⁿ M′ ∶ p
    → CastTy Δ μ c B A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ⁿ M′ ∶ q

  ⊑cast : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {κₚ γ γ′ M M′ μ′ c′ A B′ A′}
      {p : A ⊑ᵂ⟨ world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κₚ [] ⟩ B′}
    → CastGrant Δ′ c′ κ κₚ
    → RaiseCtx γ γ′
    → world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κₚ [] ∣ γ′ ⊢ M ⊑ⁿ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ⁿ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

  Λ⊑Λ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕² ⟩ A′}
    → LiftCtx γ γ′
    → Value V
    → Value V′
    → W ⊕² ∣ γ′ ⊢ V ⊑ⁿ V′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
    → W ∣ γ ⊢ Λ V ⊑ⁿ Λ V′ ∶ q

  -- CHANGED: `ClaimN` (no pop)
  Λ⊑ : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
      {γ γ′ V M′ A B′} {r : A ⊑ᵂ⟨ W₁ ⟩ B′}
    → ClaimN W W₁
    → NonVar A
    → 0 ∈ᵗ A
    → LiftCtxᴸ γ γ′
    → Value V
    → W₁ ∣ γ′ ⊢ V ⊑ⁿ M′ ∶ r
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ Λ V ⊑ⁿ M′ ∶ q

  ν⊑ν : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
    → W ∣ γ ⊢ L ⊑ⁿ L′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ A′
    → (n : NuTy Δ A C c B)
    → (n′ : NuTy Δ′ A′ C′ c′ B′)
    → NuConversionImp W n n′
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ⁿ ν A′ · L′ ⟨ c′ ⟩ ∶ q

  ν⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
    → W ∣ γ ⊢ L ⊑ⁿ M′ ∶ r
    → A ⊑ᵂ⟨ W ⟩ ★
    → NuTy Δ A C c B
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
    → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ⁿ M′ ∶ q

  ⟪⟫⊑⟪⟫ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {Δᵢ Δ′ᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ}
    → let Wᵢ = world {Δᵢ} {Δ′ᵢ} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ [] in
      ∀ {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W Θ Θ′ Wᵢ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ⁿ M′ ∶ r
    → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
    → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
    → BdyConversionImp W b b′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ⁿ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  -- CHANGED: no BdyClaim
  ⟪⟫⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {Δᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ}
    → let Wᵢ = world {Δᵢ} {Δ′} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ [] in
      ∀ {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′}
    → Interior W Θ [] Wᵢ
    → All (UnbindOK W) Θ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ⁿ M′ ∶ r
    → BdyTy Δ Θ Δᵢ Aᵢ c A
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ⁿ M′ ∶ q

  -- CHANGED: no Push
  ⊑⟪⟫ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      ∀ {Δ′ᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ}
    → let Wᵢ = world {Δ} {Δ′ᵢ} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ [] in
      ∀ {γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
    → Interior W [] Θ′ Wᵢ
    → WfWorld Wᵢ
    → Wᵢ ∣ [] ⊢ M ⊑ⁿ M′ ∶ r
    → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
    → (q : A ⊑ᵂ⟨ W ⟩ A′)
    → W ∣ γ ⊢ M ⊑ⁿ M′ ⟪ Θ′ , c′ ⟫ ∶ q

-- `⊑cast` with no grant
⊑cast₀ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world {Δ} {Δ′} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
    ∀ {γ M M′ μ′ c′ A B′ A′} {p : A ⊑ᵂ⟨ W ⟩ B′}
  → W ∣ γ ⊢ M ⊑ⁿ M′ ∶ p
  → CastTy Δ′ μ′ c′ B′ A′
  → (q : A ⊑ᵂ⟨ W ⟩ A′)
  → W ∣ γ ⊢ M ⊑ⁿ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q
⊑cast₀ {γ = γ} d ct q = ⊑cast no-grant (raise-refl γ) d ct q

------------------------------------------------------------------------
-- 2. A sub-relation of the real one (so C1-C5 and C4g stay dead here)
------------------------------------------------------------------------

toReal : ∀ {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ⁿ M′ ∶ p → W R.∣ γ ⊢ M ⊑ M′ ∶ p
toReal (x⊑x h) = R.x⊑x h
toReal (κ⊑κ l p) = R.κ⊑κ l p
toReal (ƛ⊑ƛ a a′ d) = R.ƛ⊑ƛ a a′ (toReal d)
toReal (·⊑· d e) = R.·⊑· (toReal d) (toReal e)
toReal (blame⊑ a ⊢M′ p) = R.blame⊑ a ⊢M′ p
toReal (cast⊑cast d ct ct′ q) = R.cast⊑cast (toReal d) ct ct′ q
toReal (cast⊑ d ct q) = R.cast⊑ cc-plain (toReal d) ct q
toReal (⊑cast g r d ct q) = R.⊑cast g r (toReal d) ct q
toReal (Λ⊑Λ l v v′ d q) = R.Λ⊑Λ l v v′ (toReal d) q
toReal (Λ⊑ c nv occ l v d q) = R.Λ⊑ (claimN→ c) nv occ l v (toReal d) q
toReal (ν⊑ν d a n n′ nc q) = R.ν⊑ν (toReal d) a n n′ nc q
toReal (ν⊑ d a n q) = R.ν⊑ (toReal d) a n q
toReal (⟪⟫⊑⟪⟫ i w d b b′ bc q) = R.⟪⟫⊑⟪⟫ i w (toReal d) b b′ bc q
toReal (⟪⟫⊑ i ok w d b q) = R.⟪⟫⊑ i ok bc-plain w (toReal d) b q
toReal (⊑⟪⟫ i w d b q) = R.⊑⟪⟫ i push-none w (toReal d) b q

------------------------------------------------------------------------
-- 3. Lifting a real derivation with no push, pop or pass.  `NoPend d`
-- is ⊤ on every push-free derivation (Agda fills it with `_`)
------------------------------------------------------------------------

-- a push with nothing carried and nothing new
NoPush′ : ∀ {Θ′ M π πᵢ} → Push Θ′ M π πᵢ → Set
NoPush′ (push ca-[] [] _) = ⊤
NoPush′ (push ca-[] (_ ∷ _) _) = ⊥
NoPush′ (push (ca-∷ _ _) _ _) = ⊥

NoPend : ∀ {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W R.∣ γ ⊢ M ⊑ M′ ∶ p → Set
NoPend (R.x⊑x _) = ⊤
NoPend (R.κ⊑κ _ _) = ⊤
NoPend (R.ƛ⊑ƛ _ _ d) = NoPend d
NoPend (R.·⊑· d e) = NoPend d × NoPend e
NoPend (R.blame⊑ _ _ _) = ⊤
NoPend (R.cast⊑cast d _ _ _) = NoPend d
NoPend (R.cast⊑ cc-plain d _ _) = NoPend d
NoPend (R.cast⊑ (cc-∀ _ _) _ _ _) = ⊥
NoPend (R.cast⊑ (cc-gen _) _ _ _) = ⊥
NoPend (R.⊑cast _ _ d _ _) = NoPend d
NoPend (R.Λ⊑Λ _ _ _ d _) = NoPend d
NoPend (R.Λ⊑ claim-fresh _ _ _ _ d _) = NoPend d
NoPend (R.Λ⊑ (claim-rep _ _ _) _ _ _ _ d _) = NoPend d
NoPend (R.Λ⊑ (claim-pop _) _ _ _ _ _ _) = ⊥
NoPend (R.ν⊑ν d _ _ _ _ _) = NoPend d
NoPend (R.ν⊑ d _ _ _) = NoPend d
NoPend (R.⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = NoPend d
NoPend (R.⟪⟫⊑ _ _ bc-plain _ d _ _) = NoPend d
NoPend (R.⟪⟫⊑ _ _ (bc-∀ _ _) _ _ _ _) = ⊥
NoPend (R.⊑⟪⟫ _ pu _ d _ _) = NoPush′ pu × NoPend d

lift : ∀ {W : World Δ Δ′} {γ M M′ A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → πʷ W ≡ [] → (d : W R.∣ γ ⊢ M ⊑ M′ ∶ p) → NoPend d
  → W ∣ γ ⊢ M ⊑ⁿ M′ ∶ p
lift refl (R.x⊑x h) _ = x⊑x h
lift refl (R.κ⊑κ l p) _ = κ⊑κ l p
lift refl (R.ƛ⊑ƛ a a′ d) n = ƛ⊑ƛ a a′ (lift refl d n)
lift refl (R.·⊑· d e) (n , m) = ·⊑· (lift refl d n) (lift refl e m)
lift refl (R.blame⊑ a ⊢M′ p) _ = blame⊑ a ⊢M′ p
lift refl (R.cast⊑cast d ct ct′ q) n = cast⊑cast (lift refl d n) ct ct′ q
lift refl (R.cast⊑ cc-plain d ct q) n = cast⊑ (lift refl d n) ct q
lift refl (R.⊑cast g r d ct q) n = ⊑cast g r (lift refl d n) ct q
lift refl (R.Λ⊑Λ l v v′ d q) n = Λ⊑Λ l v v′ (lift refl d n) q
lift refl (R.Λ⊑ claim-fresh nv occ l v d q) n =
  Λ⊑ n-fresh nv occ l v (lift refl d n) q
lift refl (R.Λ⊑ (claim-rep h nβ np) nv occ l v d q) n =
  Λ⊑ (n-rep h nβ np) nv occ l v (lift refl d n) q
lift refl (R.ν⊑ν d a nt nt′ nc q) n = ν⊑ν (lift refl d n) a nt nt′ nc q
lift refl (R.ν⊑ d a nt q) n = ν⊑ (lift refl d n) a nt q
lift refl (R.⟪⟫⊑⟪⟫ i w d b b′ bc q) n = ⟪⟫⊑⟪⟫ i w (lift refl d n) b b′ bc q
lift refl (R.⟪⟫⊑ i ok bc-plain w d b q) n =
  ⟪⟫⊑ i ok w (lift refl d n) b q
lift refl (R.⊑⟪⟫ i (push ca-[] [] _) w d b q)
  (_ , n) = ⊑⟪⟫ i w (lift refl d n) b q

------------------------------------------------------------------------
-- 4. The corpus blocks that PUSH, with claim-rep and no push.  In each,
-- the left binder claims the right's still-unnamed ★ rep. var ABOVE
-- the right boundary that will name it, and that boundary rejoins it.
------------------------------------------------------------------------

module Corpus where
  open import examples.TypeCheck using (tc; tf)
  import examples.TermImprecisionExamples as TIE
  import examples.TermImprecisionRebaseExamples as RB
  import examples.TermImprecisionRegressionExamples as RG
  import examples.TermImprecisionPermissionExamples as PE
  import examples.TermImprecisionH1Examples as H1
  open import examples.ImprecisionExamples using (L1)
  open import examples.CambridgeExamples using (instI; C12-L; C2-L)
  open TIE using (idX; revX; Θ₀; ΔR; ΔL; ΔRᵢ; int₀; bR-ty; ℕ⊑★)
  open import proof.ImprecisionWorld
    using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])

  ----------------------------------------------------------------------
  -- 4a. THE CORE without a push (P3's core₃, Cg X0, C12 X0, L3c, L3d):
  -- a left Λ against the right Inst boundary `[+X^αᴿ] λx:X.x` (αᴿ:=★,
  -- rep. var 0 of ΔR, no right name outside the boundary).  The left Λ
  -- claims αᴿ (claim-rep), the boundary's fresh X rejoins it, and
  -- `ƛ⊑ƛ` reads X ⊑ X.  Generic over the left store and ϱᵍ.

  Wo : ∀ {Ξ} → RepRel → World (Ξ ∣ []) ΔR
  Wo ϱ = world⁰ 0 []↪ []↪ ϱ [] []

  Wiₒ : ∀ {Ξ} → RepRel → World (underΛ (Ξ ∣ [])) ΔRᵢ
  Wiₒ ϱ = world⁰ 1 (keep []↪) (keep []↪) (shiftᴸ ϱ) ((0 , 0) ∷ []) []

  claimₒ : ∀ {Ξ ϱ} → ClaimN (Wo {Ξ} ϱ) (Wo ϱ ⊕ᴸ⇔ 0)
  claimₒ = n-rep r-here (λ { (_ , ()) }) (λ { (_ , ()) })

  Intₒ : ∀ {Ξ ϱ} → Interior (Wo {Ξ} ϱ ⊕ᴸ⇔ 0) [] Θ₀ (Wiₒ ϱ)
  Intₒ = record
    { int-left   = interior changes[]
    ; int-right  = int₀
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  coreN : ∀ {Ξ ϱ} {γ : CtxImp (Wo {Ξ} ϱ)} {γ′ : CtxImp (Wo {Ξ} ϱ ⊕ᴸ⇔ 0)}
    → LiftCtxᴸ γ γ′ → WfWorld (Wiₒ {Ξ} ϱ)
    → Wo ϱ ∣ γ ⊢ Λ idX ⊑ⁿ idX ⟪ Θ₀ , revX ⟫ ∶ RB.∀id⊑★ (Wo {Ξ} ϱ)
  coreN {Ξ} {ϱ} l wf =
    Λ⊑ claimₒ nv-⇒ (∈-⇒ˡ ∈-var) l (V-simple S-ƛ)
      (⊑⟪⟫ Intₒ wf
        (ƛ⊑ƛ {pA = X⊑X} (wf-var (_ , here)) (wf-var (_ , here)) (x⊑x Zʷ))
        bR-ty (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
      (RB.∀id⊑★ (Wo {Ξ} ϱ))

  -- at W₃ the interior world is Cg's popped world Wg⁺ (checked there)
  Wiₒ-W₃-wf : WfWorld (Wiₒ {[]} [])
  Wiₒ-W₃-wf = RB.Wg⁺-wf

  -- at W₁ (after the left's TyBeta, (αᴸ:=ℕ, αᴿ:=★) global): αᴿ has
  -- two left partners, αᴸ (unnamed) and the claimed binder (named)
  Wiₒ-W₁-wf : WfWorld (Wiₒ {bindR `ℕ ∷ []} ((0 , 0) ∷ []))
  Wiₒ-W₁-wf = wf-world (both (inj₂ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] []
    where
    W = Wiₒ {bindR `ℕ ∷ []} ((0 , 0) ∷ [])
    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔)         = rep-rep (r-there-abst r-here) r-here
                                   (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ here⇔)         = abst-★ r-here r-here
    agree (inj₂ (there⇔ ()))

  five⊑N : ∀ {Ξ ϱ} → Wo {Ξ} ϱ ∣ [] ⊢ $ 5 ⊑ⁿ TIE.5⟨ℕ!⟩ ∶ ℕ⊑★
  five⊑N = lift refl TIE.five⊑ _

  -- P3 = Ch X0 (TIE.p3-inst, RB.ch-x0)
  p3-inst : TIE.W₃ ∣ [] ⊢ L1 ⊑ⁿ TIE.R3′ ∶ ℕ⊑★
  p3-inst =
    ·⊑· (ν⊑ (⊑cast₀ (coreN liftᴸ-[] Wiₒ-W₃-wf)
                   (cast-ty (⊢fun (⊢id atom-★ wf-★) (⊢id atom-★ wf-★)) refl)
                   TIE.∀id⊑★)
            ℕ⊑★ TIE.νL-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑N

  -- C12 X0 (RB.c12-x0): ν⊑ν around the core
  c12-x0 : TIE.W₃ ∣ [] ⊢ C12-L ⊑ⁿ RB.C12-R₂ ∶ ι⊑ι base-ℕ
  c12-x0 =
    ·⊑·
      (ν⊑ν
        (⊑cast₀
          (⊑cast₀ (coreN liftᴸ-[] Wiₒ-W₃-wf) RB.id★↦ᴿ-ty
            (RB.∀id⊑★ TIE.W₃))
          RB.genIᴿ-ty (RB.∀id⊑∀id TIE.W₃))
        (ι⊑ι base-ℕ) TIE.νL-ty RB.C12-ν₂-ty
        (RB.Wν₂ , RB.Wν₂-conv , TIE.revX⊑revX refl) (RB.ℕ⇒ℕ TIE.W₃))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  -- Cg X0 (RB.cg-x0): the left Λ claims αᴿ above the right's Inst
  -- boundary; inside, the gen wrapper grants αᴿ (`⊑cast` with
  -- `grant`), under which the rejoined X is X⊑★; the right's −X makes
  -- it left-only.  The inner part is RB.cg-body's below its pop.
  cg-inner : Wiₒ {[]} [] ∣ [] ⊢ idX ⊑ⁿ RB.I★gen ∶ ⇒⊑⇒ X⊑X X⊑X
  cg-inner =
    ⊑cast (grant RB.tagX↦-grants) raise-[]
      (⊑⟪⟫ RB.Wg⁻-int (RB.Wg⁻-wf RB.p0)
        (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) RB.I★⁻ᴿ-ty
        (RB.X⇒X⊑★⇒★ {W = RB.Wg⁺¹} here))
      RB.tagᴿ-ty (⇒⊑⇒ X⊑X X⊑X)

  cg-x0 : TIE.W₃ ∣ [] ⊢ L1 ⊑ⁿ RB.Cg-R₂ ∶ ℕ⊑★
  cg-x0 =
    ·⊑·
      (ν⊑
        (⊑cast₀
          (Λ⊑ claimₒ nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (⊑⟪⟫ Intₒ Wiₒ-W₃-wf cg-inner RB.Bg-ty
              (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
            (RB.∀id⊑★ TIE.W₃))
          RB.id★↦ᴿ-ty (RB.∀id⊑★ TIE.W₃))
        ℕ⊑★ TIE.νL-ty (RB.ℕ⇒ℕ⊑★⇒★ TIE.W₃))
      five⊑N

  -- L3c (ForallBoundaryRisks §3; PushTypePremise `Corpus.l3c-*`): the
  -- right's Inst boundary DUPLICATED by Beta (both copies name αᴿ); the
  -- left instantiates copy 1.  Each copy's left Λ claims αᴿ separately.
  --   L  (λf:∀X.X→X. (λy:ℕ. f) (f[ℕ] 5)) (ΛX.λx:X.x)
  --   R  (λf:★→★.    (λy:★. f) (f 5))    (ΛX.λx:X.x)⟨inst⟩
  B⟨id⟩ L3c₁ L3c₂ R3c₃ : Term
  B⟨id⟩ = (idX ⟪ Θ₀ , revX ⟫) ⟨ [] ∣ RB.id★↦ ⟩
  L3c₁ = (ƛ `ℕ ∙ Λ idX) · L1
  L3c₂ = (ƛ `ℕ ∙ Λ idX) · TIE.L1′
  R3c₃ = (ƛ ★ ∙ B⟨id⟩) · TIE.R3′

  copy2 : ∀ {Ξ ϱ} → WfWorld (Wiₒ {Ξ} ϱ)
    → Wo ϱ ∣ ctx-imp `ℕ ★ ℕ⊑★ ∷ [] ⊢ Λ idX ⊑ⁿ B⟨id⟩ ∶ RB.∀id⊑★ (Wo {Ξ} ϱ)
  copy2 {Ξ} {ϱ} wf =
    ⊑cast₀ (coreN (liftᴸ-∷ {p′ = ι⊑★ base-ℕ} liftᴸ-[]) wf) RB.id★↦ᴿ-ty
      (RB.∀id⊑★ (Wo {Ξ} ϱ))

  l3c-pre : TIE.W₃ ∣ [] ⊢ L3c₁ ⊑ⁿ R3c₃ ∶ RB.∀id⊑★ TIE.W₃
  l3c-pre = ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 Wiₒ-W₃-wf)) p3-inst

  l3c-post : TIE.W₁ ∣ [] ⊢ L3c₂ ⊑ⁿ R3c₃ ∶ RB.∀id⊑★ TIE.W₁
  l3c-post =
    ·⊑· {pA = ℕ⊑★} (ƛ⊑ƛ tf tf (copy2 Wiₒ-W₁-wf)) (lift refl RB.ch-b1 _)

  -- L3d before (ForallBoundaryFixes §7): the left's second copy against
  -- the right's copy 2 at W₁
  νLₗ-ty : NuTy ΔL `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νLₗ-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = ΔL} {M = ν `ℕ · Λ idX ⟨ revX ⟩})))

  l3d-before : TIE.W₁ ∣ [] ⊢ L1 ⊑ⁿ TIE.R3′ ∶ ℕ⊑★
  l3d-before =
    ·⊑· (ν⊑ (⊑cast₀ (coreN liftᴸ-[] Wiₒ-W₁-wf) RB.id★↦ᴿ-ty
               (RB.∀id⊑★ TIE.W₁))
            ℕ⊑★ νLₗ-ty (⇒⊑⇒ ℕ⊑★ ℕ⊑★))
        five⊑N

  ----------------------------------------------------------------------
  -- 4b. K (examples/TermImprecisionRegressionExamples) without a push.
  -- The left's ∀-boundary VL = [+Y^αᴸ] (ΛX.λx:X.x) ⟨∀X.cId⟩ is entered
  -- FIRST (⟪⟫⊑, X... Y left-only), its ΛX claims the right's β (the Inst
  -- rep. var, unnamed outside the right boundary), and then the right's
  -- boundaries rejoin: the merged Θ₂ = (+Y^β, +X^αᴿ) at once (VL⊑RF), or
  -- +Y^β then +X^αᴿ (lk₁⊑rk₃).  In the real relation the same pairs need
  -- a push of Y, a pass into VL (bc-∀) and a pop (claim-pop).

  open RG using (Wk; VL; Bm; RF; Rarg₃; LK₁; RK₄; RK₃; ΔRk; ΔLX; ΔRX;
                 Θ₂; ΘX; int-Θ₂; bindX-int; Θ₀-int; bVL; bBm; bNR; bOutK;
                 id★↦ᴿk-ty; agreeₖ)

  -- inside the left's boundary: Y (αᴸ:=ℕ) left-only
  Wl : World TIE.ΔLᵢ ΔRk
  Wl = world⁰ 1 (keep []↪) (skip []↪) ((0 , 1) ∷ []) [] []

  IntL : Interior Wk Θ₀ [] Wl
  IntL = record
    { int-left   = int₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there ()) _ _ _ }
    ; join-fresh = λ { _ () _ }
    }

  Wl-wf : WfWorld Wl
  Wl-wf = wf-world (left-only joint[])
    (agreeₖ r-here (r-there r-here) refl refl)
    (namedᴸ-≤1 Wl ≤1-∷[]) (namedᴿ-≤1 Wl ≤1-[]) [] [] []

  -- the left's ΛX claims β (rep. var 0 of ΔRk, :=★, no name)
  claimK : ClaimN Wl (Wl ⊕ᴸ⇔ 0)
  claimK = n-rep r-here (λ { (_ , ()) })
    (λ { (_ , here) (inj₁ (there⇔ ())) ; (_ , here) (inj₂ ())
       ; (_ , there ()) _ })

  -- the pairs (1, 1) global (αᴸ, αᴿ) and (0, 0) lexical (X, β) are
  -- one-to-one
  uniqK : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂}
    → ϱᵍʷ W ≡ (1 , 1) ∷ [] → ϱˡʷ W ≡ (0 , 0) ∷ []
    → ∀ {α α′ β β′} → Paired W α β → Paired W α′ β′
    → (α ≡ α′ → β ≡ β′) × (β ≡ β′ → α ≡ α′)
  uniqK eg el (inj₁ p) (inj₁ p′) rewrite eg with p | p′
  ... | here⇔ | here⇔ = (λ _ → refl) , (λ _ → refl)
  ... | there⇔ () | _
  ... | _ | there⇔ ()
  uniqK eg el (inj₁ p) (inj₂ p′) rewrite eg | el with p | p′
  ... | here⇔ | here⇔ = (λ ()) , (λ ())
  ... | there⇔ () | _
  ... | _ | there⇔ ()
  uniqK eg el (inj₂ p) (inj₁ p′) rewrite eg | el with p | p′
  ... | here⇔ | here⇔ = (λ ()) , (λ ())
  ... | there⇔ () | _
  ... | _ | there⇔ ()
  uniqK eg el (inj₂ p) (inj₂ p′) rewrite el with p | p′
  ... | here⇔ | here⇔ = (λ _ → refl) , (λ _ → refl)
  ... | there⇔ () | _
  ... | _ | there⇔ ()

  agreeK : ∀ {Δ₂} {W : World ΔLX Δ₂} → Δ₂ ∋rep 0 := ★ → Δ₂ ∋rep 1 := `ℕ
    → ϱᵍʷ W ≡ (1 , 1) ∷ [] → ϱˡʷ W ≡ (0 , 0) ∷ []
    → ∀ {α β} → Paired W α β → Agree W α β
  agreeK h0 h1 eg el (inj₁ p) rewrite eg with p
  ... | here⇔     = rep-rep (r-there-abst r-here) h1 (ι⊑ι base-ℕ)
  ... | there⇔ ()
  agreeK h0 h1 eg el (inj₂ p) rewrite el with p
  ... | here⇔     = abst-★ r-here h0
  ... | there⇔ ()

  WK : ∀ {Δ₂ n} → names ΔLX ↪ n → names Δ₂ ↪ n → World ΔLX Δ₂
  WK {n = n} ηL ηR = world⁰ n ηL ηR ((1 , 1) ∷ []) ((0 , 0) ∷ []) []

  wfK : ∀ {Δ₂ n} (ηL : names ΔLX ↪ n) (ηR : names Δ₂ ↪ n)
    → Δ₂ ∋rep 0 := ★ → Δ₂ ∋rep 1 := `ℕ
    → Joint (Paired (WK {Δ₂} ηL ηR)) ηL ηR → WfWorld (WK {Δ₂} ηL ηR)
  wfK {Δ₂} ηL ηR h0 h1 j = wf-world j
    (agreeK {W = W} h0 h1 refl refl)
    (λ _ _ _ p p′ → proj₂ (uniqK {W = W} refl refl p p′) refl)
    (λ _ _ _ p p′ → proj₁ (uniqK {W = W} refl refl p p′) refl)
    [] [] []
    where W = WK {Δ₂} ηL ηR

  -- inside the merged Θ₂: X ↦ β (lexical), Y ↦ αᴿ (global)
  WX2 : World ΔLX ΔRX
  WX2 = world⁰ 2 (keep (keep []↪)) (keep (keep []↪))
          ((1 , 1) ∷ []) ((0 , 0) ∷ []) []

  WX2-wf : WfWorld WX2
  WX2-wf = wfK _ _ r-here (r-there r-here)
    (both (inj₂ here⇔) (both (inj₁ here⇔) joint[]))

  IntΘ₂ : Interior (Wl ⊕ᴸ⇔ 0) [] Θ₂ WX2
  IntΘ₂ = record
    { int-left   = interior changes[]
    ; int-right  = int-Θ₂
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there here) _ ()
                     ; _ (_ , there (there ())) _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) here _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; _ (there (there ())) _ ; (there (there ())) _ _ }
    }

  idX⊑idX : WX2 ∣ [] ⊢ idX ⊑ⁿ idX ∶ ⇒⊑⇒ X⊑X X⊑X
  idX⊑idX = ƛ⊑ƛ {pA = X⊑X} tf tf (x⊑x Zʷ)

  -- VL ⊑ Bm: ⟪⟫⊑, then ΛX claims β, then the merged ⊑⟪⟫ rejoins both
  VL⊑Bm : Wk ∣ [] ⊢ VL ⊑ⁿ Bm ∶ RB.∀id⊑★ Wk
  VL⊑Bm =
    ⟪⟫⊑ IntL (ok-bind ∷ []) Wl-wf
      (Λ⊑ claimK nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
        (⊑⟪⟫ IntΘ₂ WX2-wf idX⊑idX bBm (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
        (RB.∀id⊑★ Wl))
      bVL (RB.∀id⊑★ Wk)

  VL⊑RF : Wk ∣ [] ⊢ VL ⊑ⁿ RF ∶ RB.∀id⊑★ Wk
  VL⊑RF = ⊑cast₀ VL⊑Bm id★↦ᴿk-ty (RB.∀id⊑★ Wk)

  lk₁⊑rk₄ : Wk ∣ [] ⊢ LK₁ ⊑ⁿ RK₄ ∶ RB.∀id⊑★ Wk
  lk₁⊑rk₄ = ·⊑· (ƛ⊑ƛ {pA = RB.∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑RF

  -- before the Merge: +Y^β rejoins X, then +X^αᴿ rejoins Y
  WY : World ΔLX (reps ΔRk ∣ (0 ∷ []))
  WY = world⁰ 2 (keep (keep []↪)) (keep (skip []↪))
         ((1 , 1) ∷ []) ((0 , 0) ∷ []) []

  WY-wf : WfWorld WY
  WY-wf = wfK _ _ r-here (r-there r-here)
    (both (inj₂ here⇔) (left-only joint[]))

  IntY : Interior (Wl ⊕ᴸ⇔ 0) [] Θ₀ WY
  IntY = record
    { int-left   = interior changes[]
    ; int-right  = Θ₀-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ
        { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
        ; (there here) here _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; _ (there ()) _ ; (there (there ())) _ _ }
    }

  IntX : Interior WY [] ΘX WX2
  IntX = record
    { int-left   = interior changes[]
    ; int-right  = bindX-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
        ; (_ , there here) (_ , here) refl refl → (λ ()) , (λ ())
        ; _ (_ , there here) _ ()
        ; _ (_ , there (there ())) _ _
        ; (_ , there (there ())) _ _ _ }
    ; join-fresh = λ
        { here (there here) _ →
            (λ ()) , (λ { (inj₁ (there⇔ ())) ; (inj₂ (there⇔ ())) })
        ; (there here) (there here) _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
        ; _ here (inj₁ ()) ; _ here (inj₂ ())
        ; _ (there (there ())) _ ; (there (there ())) _ _ }
    }

  VL⊑Rarg₃ : Wk ∣ [] ⊢ VL ⊑ⁿ Rarg₃ ∶ RB.∀id⊑★ Wk
  VL⊑Rarg₃ =
    ⊑cast₀
      (⟪⟫⊑ IntL (ok-bind ∷ []) Wl-wf
        (Λ⊑ claimK nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
          (⊑⟪⟫ IntY WY-wf
            (⊑⟪⟫ IntX WX2-wf idX⊑idX bNR (⇒⊑⇒ X⊑X X⊑X))
            bOutK (⇒⊑⇒ (X⊑★ here) (X⊑★ here)))
          (RB.∀id⊑★ Wl))
        bVL (RB.∀id⊑★ Wk))
      id★↦ᴿk-ty (RB.∀id⊑★ Wk)

  lk₁⊑rk₃ : Wk ∣ [] ⊢ LK₁ ⊑ⁿ RK₃ ∶ RB.∀id⊑★ Wk
  lk₁⊑rk₃ = ·⊑· (ƛ⊑ƛ {pA = RB.∀id⊑★ Wk} tf tf (x⊑x Zʷ)) VL⊑Rarg₃

  -- the push-free pairs of K, lifted
  lk⊑rk   = lift refl RG.lk⊑rk _
  lk₁⊑rk₁ = lift refl RG.lk₁⊑rk₁ _

  -- K's obligations, with no push
  open import Reduction using (_⊢_-→*_; done; _then_)
  open import proof.DGG.Evolve using (applyˢ; allocs)

  dgg1-K :
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ RG.RK -→* V′ ] Value V′
      × Σ[ W′ ∈ World ΔL (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ TIE.∀X⇒X ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ] (W′ ∣ [] ⊢ VL ⊑ⁿ V′ ∶ q)
  dgg1-K =
    RF , (RG.st₀ then RG.st₁ then RG.st₂ then RG.st₃ then RG.st₄ then done) ,
    RG.vRF , Wk , RB.∀id⊑★ Wk , VL⊑RF

  ----------------------------------------------------------------------
  -- 4c. H1 (examples/TermImprecisionH1Examples): its final pair already
  -- needs no push (`final-no-push`); its state 2 (P3's push and pop in
  -- the real `st2`) by claim-rep of α above the casts

  open H1 using (L₀; R₂; R₄; W₂; W₄; Δ1; ΔT1; ΔA; ΘA; bA; ∀ci-ty;
                 instY-ty₂; q-top; idK; vNL; vL1; rK★)

  h1-final : W₄ ∣ [] ⊢ L₀ ⊑ⁿ R₄ ∶ q-top
  h1-final = lift refl H1.final-no-push _

  h1-init = lift refl H1.init _

  WA : World Δ1 ΔA
  WA = world⁰ 1 (keep []↪) (keep []↪) [] ((0 , 0) ∷ []) []

  intA : Interior (W₂ ⊕ᴸ⇔ 0) [] ΘA WA
  intA = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
                     (step-bind (_ , here) fresh[] ins-here))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
    ; join-fresh = λ { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
                     ; here (there ()) _ ; (there ()) _ _ }
    }

  wfA : WfWorld WA
  wfA = wf-world (both (inj₂ here⇔) joint[])
    (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here r-here
       ; (inj₂ (there⇔ ())) })
    (namedᴸ-≤1 WA ≤1-∷[]) (namedᴿ-≤1 WA ≤1-∷[]) [] [] []

  qKY : ∀ {μ} → (X⊑★ ∷ μ) ⊢ `∀ (` 1 ⇒ (` 0 ⇒ ` 1)) ⊑ H1.KY
  qKY = ∀⊑∀ (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here))))

  h1-st2 : W₂ ∣ [] ⊢ L₀ ⊑ⁿ R₂ ∶ q-top
  h1-st2 =
    Λ⊑ (n-rep r-here (λ { (_ , ()) }) (λ { (_ , ()) }))
      nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
      (⊑cast₀
        (⊑cast₀
          (⊑⟪⟫ intA wfA
            (Λ⊑Λ lift-[] vNL vNL
              (ƛ⊑ƛ {pA = X⊑X} tf tf
                (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
              idK)
            bA qKY)
          ∀ci-ty qKY)
        instY-ty₂ rK★)
      q-top

  ----------------------------------------------------------------------
  -- 4d. The push-free corpus, lifted (`NoPend` is ⊤ on each)

  p1-init   = lift refl TIE.p1-init _
  p1-tybeta = lift refl TIE.p1-tybeta _
  p2-tybeta = lift refl TIE.p2-tybeta _
  p6-init-ν = lift refl TIE.p6-init-ν _
  p6-tybeta = lift refl TIE.p6-tybeta _
  ch-b0  = lift refl RB.ch-b0 _
  ch-b1  = lift refl RB.ch-b1 _
  cg-b0  = lift refl RB.cg-b0 _
  c2-b0  = lift refl RB.c2-b0 _
  c2-b6  = lift refl RB.c2-b6 _
  c2-b7  = lift refl RB.c2-b7 _
  c12-b0 = lift refl RB.c12-b0 _
  c12-b1 = lift refl RB.c12-b1 _
  c13-b1 = lift refl RB.c13-b1 _
  c14-b1 = lift refl RB.c14-b1 _
  p4-B1  = lift refl PE.P4.p4-B1 _
  p4-B1′ = lift refl PE.P4.p4-B1′ _
  p4-B2  = lift refl PE.P4.p4-B2 _
  p4-B3  = lift refl PE.P4.p4-B3 _
  p4-B4  = lift refl PE.P4.p4-B4 _
  p4-B5  = lift refl PE.P4.p4-B5 _
  p4-B6  = lift refl PE.P4.p4-B6 _
  p4-R7  = lift refl PE.P4c.p4-R7 _
  p4-R8  = lift refl PE.P4c.p4-R8 _
  p4-R9  = lift refl PE.P4c.p4-R9 _
  p4-R10 = lift refl PE.P4c.p4-R10 _
  cg-b1   = lift refl PE.CgB1.cg-b1 _
  c18b-b7 = lift refl PE.C18bB7.c18b-b7 _

------------------------------------------------------------------------
-- 5. C2 X0 (RB.c2-x0: the right-led block of C2 = Ex 2/21, related in
-- the real relation by a push and a `cc-gen` pop) is NOT derivable
-- without pushes.  The left's ∀ is a GEN cast `(λx:★.x)⟨gen X.(X! → X?)⟩`:
-- it binds nothing in the left context, so the left stays CLOSED
-- (`empty`) down to the right's Inst boundary `+X^αᴿ`, whose interior
-- `([−X^αᴿ] λx:★.x ⟨…⟩)⟨X! → X?⟩` has type X → X at the right NAME X.
-- At a world with no pending name the index is plain, and no closed
-- left type A has `A ⊑ X → X` (`not⊑var⇒`): its domain would have to
-- be a left name.  This holds for EVERY left term, so no ordering of
-- the left's ν, gen cast and λ helps (`walk`), and no claim-rep-like
-- rule at the gen cast can help either (the gen binder scopes over no
-- left term, so the left context stays closed; only an index opened at
-- X, i.e. a pending name, relates it).
------------------------------------------------------------------------

module C2X0 where
  open import Data.Nat.Properties using (suc-injective)
  open import proof.DGG.ImprecisionTyping using (imprecision-typing)
  open import proof.TypeSafety.PreservationSupport using (⊢ᵗ-of)
  open import proof.TypeSafety.CoercionTyping
    using (coercion-trg; underΛ-tv-tail)
  open import examples.CambridgeExamples using (I★; C2-L)
  import examples.TermImprecisionRebaseExamples as RB

  -- a renaming that avoids t on the names of Γ
  Avoid : Ctxᵗ → Renameᵗ → ℕ → Set
  Avoid Γ ρ t = ∀ {X} → Γ ∋tv X → ρ X ≢ t

  avoid-ext : ∀ {Γ ρ t} → Avoid Γ ρ t → Avoid (underΛ Γ) (extᵗ ρ) (suc t)
  avoid-ext av {zero}  _  ()
  avoid-ext {Γ} av {suc X} tv e =
    av (underΛ-tv-tail {Γ} tv) (suc-injective e)

  -- a well-formed type is not below a type variable outside its names
  not⊑var : ∀ {Γ μ ρ A t} → Γ ⊢ᵗ A → Avoid Γ ρ t
    → ¬ (μ ⊢ renameᵗ ρ A ⊑ ` t)
  not⊑var (wf-var tv) av X⊑X = av tv refl
  not⊑var wf-ℕ av ()
  not⊑var wf-𝔹 av ()
  not⊑var wf-★ av ()
  not⊑var (wf-⇒ _ _) av ()
  not⊑var {Γ} {ρ = ρ} (wf-∀ w) av (∀⊑ _ _ p) =
    not⊑var {ρ = extᵗ ρ} w (avoid-ext {Γ} {ρ} av) p

  -- ... nor below an arrow whose domain is such a variable
  not⊑var⇒ : ∀ {Γ μ ρ A t B} → Γ ⊢ᵗ A → Avoid Γ ρ t
    → ¬ (μ ⊢ renameᵗ ρ A ⊑ (` t ⇒ B))
  not⊑var⇒ (wf-var _) av ()
  not⊑var⇒ wf-ℕ av ()
  not⊑var⇒ wf-𝔹 av ()
  not⊑var⇒ wf-★ av ()
  not⊑var⇒ {ρ = ρ} (wf-⇒ a _) av p = not⊑var {ρ = ρ} a av (dom⊑ p)
    where
    dom⊑ : ∀ {μ C D E F} → μ ⊢ C ⇒ D ⊑ E ⇒ F → μ ⊢ C ⊑ E
    dom⊑ (⇒⊑⇒ p _) = p
    dom⊑ (ι⊑ι ())
  not⊑var⇒ {Γ} {ρ = ρ} (wf-∀ w) av p =
    not⊑var⇒ {ρ = extᵗ ρ} w (avoid-ext {Γ} {ρ} av) (body⊑ p)
    where
    body⊑ : ∀ {μ C E F} → μ ⊢ `∀ C ⊑ E ⇒ F → instᵐ μ ⊢ C ⊑ ⇑ᵗ (E ⇒ F)
    body⊑ (∀⊑ _ _ p) = p

  -- every world of this relation has no pending name
  πN : ∀ {V : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → V ∣ γ ⊢ M ⊑ⁿ M′ ∶ q → πʷ V ≡ []
  πN (x⊑x _) = refl
  πN (κ⊑κ _ _) = refl
  πN (ƛ⊑ƛ _ _ _) = refl
  πN (·⊑· _ _) = refl
  πN (blame⊑ _ _ _) = refl
  πN (cast⊑cast _ _ _ _) = refl
  πN (cast⊑ _ _ _) = refl
  πN (⊑cast _ _ _ _ _) = refl
  πN (Λ⊑Λ _ _ _ _ _) = refl
  πN (Λ⊑ n-fresh _ _ _ _ _ _) = refl
  πN (Λ⊑ (n-rep _ _ _) _ _ _ _ _ _) = refl
  πN (ν⊑ν _ _ _ _ _ _) = refl
  πN (ν⊑ _ _ _ _) = refl
  πN (⟪⟫⊑⟪⟫ _ _ _ _ _ _ _) = refl
  πN (⟪⟫⊑ _ _ _ _ _ _) = refl
  πN (⊑⟪⟫ _ _ _ _ _) = refl

  plainN : ∀ {V : World Δ Δ′} {A A′} → πʷ V ≡ [] → A ⊑ᵂ⟨ V ⟩ A′
    → marksʷ V ⊢ embᴸ V A ⊑ embᴿ V A′
  plainN {V = V} {A} {A′} e q =
    Relation.Binary.PropositionalEquality.subst
      (λ π → OpenImp (marksʷ V) (map (emb (ηᴿʷ V)) π) (emb (ηᴸʷ V)) A
               (embᴿ V A′)) e q

  -- THE INTERIOR: no CLOSED left term is related to the right's tagged
  -- `I★gen : X → X`, at any index
  no-at-I★gen : ∀ {Δ′} {V : World empty Δ′} {M A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ [] ⊢ M ⊑ⁿ RB.I★gen ∶ q)
  no-at-I★gen {V = V} {q = q} d with imprecision-typing (toReal d)
  ... | ⊢M , ⊢R with cast-inv {Γ = []} ⊢R
  ... | _ , _ , cast-ty ⊢p _ with coercion-trg ⊢p
  ... | refl =
    not⊑var⇒ (⊢ᵗ-of (λ ()) ⊢M) (λ { (_ , ()) }) (plainN {V = V} (πN d) q)

  data LeftC : Term → Set where
    l-ν : LeftC RB.C2-L-ν
    l-g : LeftC RB.I★genI
    l-I : LeftC I★

  data RightC : Term → Set where
    r-c : RightC (RB.Bg ⟨ [] ∣ RB.id★↦ ⟩)
    r-b : RightC RB.Bg

  -- THE WALK: whatever the order, the right boundary is entered with a
  -- closed left term
  walk : ∀ {Δ′} {V : World empty Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LeftC M → RightC M′ → ¬ (V ∣ γ ⊢ M ⊑ⁿ M′ ∶ q)
  walk l-ν r (ν⊑ d _ _ _) = walk l-g r d
  walk l-g r (cast⊑ d _ _) = walk l-I r d
  walk l-g r-c (cast⊑cast d _ _ _) = walk l-I r-b d
  walk l r-c (⊑cast _ _ d _ _) = walk l r-b d
  walk l r-b (⊑⟪⟫ _ _ e _ _) = no-at-I★gen e

  -- C2 X0 IS NOT DERIVABLE without pushes: every world, every index,
  -- every term context
  c2-x0-unrelated : ∀ {Δ′} {W : World empty Δ′} {γ A A′}
      {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C2-L ⊑ⁿ RB.Cg-R₂ ∶ q)
  c2-x0-unrelated (·⊑· f _) = walk l-ν r-c f

  -- ... while the real relation (D27's push, cc-gen pop) relates it
  c2-x0-real = RB.c2-x0

  ----------------------------------------------------------------------
  -- G1: the same obstacle as a DGG PART 1 counterexample for the
  -- push-free relation, from RELATED sources.  A gen-cast ∀-value
  -- against its own instantiation at ★ (cambridge-imprecision-check
  -- F2's block, as a final pair):
  --   L:  ((λx:★. x) : ∀X.X→X)            (cast insertion: gen)
  --   R:  (((λx:★. x) : ∀X.X→X) : ★→★)    (gen, then inst)
  -- The sources are related (the same term; ∀X.X→X ⊑ ★→★, `g1-src`).
  -- Initial cast terms (rendered):
  --   L₀ = (λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]
  --   R₀ = (λx:★. x)⟨gen X. (X! → X?ℓ0)⟩^[]⟨inst Y. (Y?ℓ0 → Y!)⟩^[]
  -- The left is a value.  The right runs Inst, TyBeta to its value
  --   R₂ = ([+X^α] ([−X^α] (λx:★. x) ⟨id(★) → id(★)⟩)⟨X! → X?ℓ0⟩^[X:★∼X]
  --          ⟨−X → +X⟩)⟨id(★) → id(★)⟩^[]
  -- The real relation relates (L₀, R₂) (push X, grant, cc-gen pop:
  -- `g1-final-real`); the push-free one relates it in no world
  -- (`g1-final-unrelated`).

  open import examples.TypeCheck using (tc)
  open import examples.Eval using (evalTerms; step; StepResult)
  open import examples.CambridgeExamples using (instI)
  import examples.TermImprecisionExamples as TIE
  import examples.TermImprecisionRegressionExamples as RG
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
  open import proof.DGG.Evolve using (applyˢ; allocs)

  g1-src : [] ⊢ `∀ (` 0 ⇒ ` 0) ⊑ (★ ⇒ ★)
  g1-src = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  G-L G-R G-R₁ G-R₂ : Term
  G-L  = RB.I★genI
  G-R  = RB.I★genI ⟨ [] ∣ instI ⟩
  G-R₁ = (ν ★ · RB.I★genI ⟨ TIE.revX ⟩) ⟨ [] ∣ RB.id★↦ ⟩
  G-R₂ = RB.Bg ⟨ [] ∣ RB.id★↦ ⟩

  G-R-⊢ : empty ∣ [] ⊢ G-R ⦂ ★ ⇒ ★
  G-R-⊢ = tc

  G-R-states : evalTerms 20 G-R-⊢ ≡ G-R ∷ G-R₁ ∷ G-R₂ ∷ []
  G-R-states = refl

  justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
    → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
  justStep {r = r} _ = proj₂ (proj₂ r)

  g-st₀ : empty ⊢ G-R -→ G-R₁ ∣ none
  g-st₀ = justStep refl

  g-st₁ : empty ⊢ G-R₁ -→ G-R₂ ∣ new ★
  g-st₁ = justStep refl

  vG-L : Value G-L
  vG-L = RB.vI★genI

  vG-R₂ : Value G-R₂
  vG-R₂ = V-simple (S-cast (V-⟪⟫ (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦) I-fun) I-↦)

  -- R₂ is the right's only value (R₀, R₁ are not; the run is
  -- deterministic)
  G-R-nv : ¬ Value G-R
  G-R-nv (V-simple (S-cast _ ()))

  G-R₁-nv : ¬ Value G-R₁
  G-R₁-nv (V-simple (S-cast (V-simple ()) _))

  -- the initial pair, related in both relations
  g1-init-real : ∅ʷ R.∣ [] ⊢ G-L ⊑ G-R ∶ RB.∀id⊑★ ∅ʷ
  g1-init-real =
    R.⊑cast₀
      (R.cast⊑cast (R.ƛ⊑ƛ {pA = ★⊑★} wf-★ wf-★ (R.x⊑x Zʷ))
        RB.genI-ty RB.genI-ty (RB.∀id⊑∀id ∅ʷ))
      RG.instI₀-ty (RB.∀id⊑★ ∅ʷ)

  g1-init : ∅ʷ ∣ [] ⊢ G-L ⊑ⁿ G-R ∶ RB.∀id⊑★ ∅ʷ
  g1-init = lift refl g1-init-real _

  -- the final pair: related by the real relation (the inner part of
  -- RB.c2-x0: push X, the gen wrapper's grant, cc-gen pop) ...
  g1-final-real : TIE.W₃ R.∣ [] ⊢ G-L ⊑ G-R₂ ∶ RB.∀id⊑★ TIE.W₃
  g1-final-real =
    R.⊑cast₀
      (R.⊑⟪⟫ TIE.int-ro₃ (push ca-[] (refl ∷ []) (inj₂ RB.vI★genI))
        TIE.Wi₃-wf RB.c2-body RB.Bg-ty (RB.∀id⊑★ TIE.W₃))
      RB.id★↦ᴿ-ty (RB.∀id⊑★ TIE.W₃)

  -- ... and by the push-free relation in NO world, at no index: DGG
  -- part 1 fails for (L₀, R₀) without pushes
  g1-final-unrelated : ∀ {Δ′} {W : World empty Δ′} {γ A A′}
      {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ G-L ⊑ⁿ G-R₂ ∶ q)
  g1-final-unrelated = walk l-g r-c

  -- DGG part 1 on (L₀, R₀) in the real relation
  g1-dgg1-real :
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ G-R -→* V′ ] Value V′
      × Σ[ W′ ∈ World empty (applyˢ (allocs r′) empty) ]
          Σ[ q ∈ `∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ W′ ⟩ (★ ⇒ ★) ]
            (W′ R.∣ [] ⊢ G-L ⊑ V′ ∶ q)
  g1-dgg1-real =
    G-R₂ , (g-st₀ then g-st₁ then done) , vG-R₂ ,
    TIE.W₃ , RB.∀id⊑★ TIE.W₃ , g1-final-real

------------------------------------------------------------------------
-- 6. The counterexamples stay dead here (sub-relation, §2)
------------------------------------------------------------------------

module Dead where
  import examples.TermImprecisionPermissionExamples as PE
  open import examples.TermImprecisionExamples using (ΔL)
  open PE using (module C1; module C2; module C3; module C4; module C4g;
                 module C5; module C5Dead)

  c1 : ∀ {W : World C1.ΔR C1.ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C1.L₆ ⊑ⁿ C1.R₇ ∶ q)
  c1 eκ d = C1.c1-unrelated eκ (toReal d)

  c2 : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C2.LE₃ ⊑ⁿ C2.RE₅ ∶ q)
  c2 eκ d = C2.c2-unrelated eκ (toReal d)

  c3 : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C3.LE₁ ⊑ⁿ C3.RE₁ ∶ q)
  c3 eκ d = C3.c3-unrelated eκ (toReal d)

  c4 : ∀ {W : World empty C1.ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C1.L₀ ⊑ⁿ C4.R₂ ∶ q)
  c4 eκ d = C4.c4-unrelated eκ (toReal d)

  c4g : ∀ {W : World empty C1.ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C1.L₀ ⊑ⁿ C4g.R2g ∶ q)
  c4g eκ d = C4g.c4g-unrelated eκ (toReal d)

  c5 : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5.C5L ⊑ⁿ C5.C5R ∶ q)
  c5 d = C5Dead.c5-unrelated (toReal d)

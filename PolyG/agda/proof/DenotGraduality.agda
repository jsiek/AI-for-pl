module proof.DenotGraduality where

-- File Charter:
--   * Graduality for PolyGν, by the denotational method
--     (PolyG/notes/denotational-graduality.md, Section 8): for closed
--     surface derivations dₗ ⊑ᴳ dᵣ, the elaborations L and R satisfy
--       (a) L ⇓ V gives R ⇓ V′ with the same observation;
--       (b) R ⇓ V′ gives L ⇓ V with the same observation, or L fails;
--       (c) if R fails, L fails;
--       (d) if L diverges, R diverges;
--       (e) if R diverges, L diverges or fails.
--   * Ingredients: elaboration preserves precision and typing
--     (CompileMeta.agda), the fundamental lemma at the empty world
--     (proof/DenotFundamental.agda), soundness and adequacy
--     (DenotationMeta.agda), type safety and irreducibility of values
--     and ℧ (TypeSafety.agda), and obs-▹ / obs-◃: related values have
--     the same observation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Types
open import Terms using (Term; ℧)
open import Reduction
open import GraphModel
open import Denotation
open import GradualityDefinitions
open import GradualTerms using (_∣_⊢ᴳ_⦂_)
open import GradualTermPrecision using (_∣_⊢_⊑ᴳ_⦂_)
open import TermPrecision using (_∣_⊢_⊑_⦂_)
open import Compile using (elab)
open import CompileMeta
  using (elab-preserves-precision-closed; elab-preserves-typing-closed)
open import DenotationMeta
  using (sound-val; sound-℧; adequacy-val; adequacy-err; elab-scoped)
open import TypeSafety
  using (type-safety-[]; value-irreducible; ℧-irreducible)
open import proof.DenotConsistency using (ρ₀-consistent)
open import proof.DenotRelation
open import proof.DenotRelationProps
open import proof.DenotFundamental

------------------------------------------------------------------------
-- Related values have the same observation
------------------------------------------------------------------------

obs-𝔹 : ∀ {D} v → IsBool D v → Σ[ v′ ∈ Val ] (v′ ∈ D × obs v ≡ obs v′)
obs-𝔹 vtrue t∈ = vtrue , t∈ , refl
obs-𝔹 vfalse f∈ = vfalse , f∈ , refl
obs-𝔹 (sealᵛ σ u) ()
obs-𝔹 (injᵛ G u) ()
obs-𝔹 (U ⟼ r at m) ()
obs-𝔹 (σ ⟼∀ r) ()
obs-𝔹 νλ ()
obs-𝔹 ν∀ ()

obs-fun : ∀ {D} v → IsFun v → νλ ∈ D
  → Σ[ v′ ∈ Val ] (v′ ∈ D × obs v ≡ obs v′)
obs-fun v is-entry ν∈ = νλ , ν∈ , refl
obs-fun v is-νλ ν∈ = νλ , ν∈ , refl

obs-poly : ∀ {D} v → IsPoly v → ν∀ ∈ D
  → Σ[ v′ ∈ Val ] (v′ ∈ D × obs v ≡ obs v′)
obs-poly v is-pentry ν∈ = ν∀ , ν∈ , refl
obs-poly v is-ν∀ ν∈ = ν∀ , ν∈ , refl

obs-▹ : ∀ k {W θ p L D′ v} → Rel▹ k W θ p L D′ → v ⋵ L
  → Σ[ v′ ∈ Val ] (v′ ∈ D′ × obs v ≡ obs v′)
obs-▹ k {L = []} rel ()
obs-▹ zero {L = x ∷ L} (lift ()) v∈
obs-▹ (suc k) {p = ★⊑} {L = x ∷ L} (lift all , f) v∈
  with All-lookup all v∈
obs-▹ (suc k) {p = ★⊑} {L = x ∷ L} {v = injᵛ G u} (lift all , f) v∈
  | is-inj with obs-▹ k (f G) (untag-∈⁺ v∈)
... | v″ , v″∈ , eq = injᵛ G v″ , v″∈ , eq
obs-▹ (suc k) {θ = θ} {p = tag G p} {L = x ∷ L} rel v∈
  with obs-▹ (suc k) {p = p} rel v∈
... | v″ , v″∈ , eq = injᵛ (⟦ G ⟧ᴳ θ) v″ , v″∈ , eq
obs-▹ (suc k) {θ = θ} {p = ‵⊑ α} {L = x ∷ L} (lift all , q , w∋ , rel) v∈
  with All-lookup all v∈
obs-▹ (suc k) {θ = θ} {p = ‵⊑ α} {L = x ∷ L} {v = sealᵛ σ u}
    (lift all , q , w∋ , rel) v∈ | is-seal-at
  with obs-▹ k rel (unseal-∈⁺ v∈)
... | v″ , v″∈ , eq = sealᵛ σ v″ , v″∈ , eq
obs-▹ (suc k) {p = 𝔹⊑} {L = x ∷ L} {v = v} (lift all) v∈ =
  obs-𝔹 v (All-lookup all v∈)
obs-▹ (suc k) {p = p ⇒⊑ q} {L = x ∷ L} {v = v} (lift all , lift ν∈ , f) v∈ =
  obs-fun v (All-lookup all v∈) ν∈
obs-▹ (suc k) {p = ∀⊑ p} {L = x ∷ L} {v = v} (lift all , lift ν∈ , f) v∈ =
  obs-poly v (All-lookup all v∈) ν∈

obs-◃ : ∀ k {W θ p D L′ v′} → Rel◃ k W θ p D L′ → v′ ⋵ L′
  → Σ[ v ∈ Val ] (v ∈ D × obs v′ ≡ obs v)
obs-◃ k {L′ = []} rel ()
obs-◃ zero {L′ = x ∷ L} (lift ()) v∈
obs-◃ (suc k) {p = ★⊑} {L′ = x ∷ L} (lift all , f) v∈
  with All-lookup all v∈
obs-◃ (suc k) {p = ★⊑} {L′ = x ∷ L} {v′ = injᵛ G u} (lift all , f) v∈
  | is-inj with obs-◃ k (f G) (untag-∈⁺ v∈)
... | v″ , v″∈ , eq = injᵛ G v″ , v″∈ , eq
obs-◃ (suc k) {p = tag G p} {L′ = x ∷ L} (lift all , rel) v∈
  with All-lookup all v∈
obs-◃ (suc k) {p = tag G p} {L′ = x ∷ L} {v′ = injᵛ H u} (lift all , rel) v∈
  | is-inj-at with obs-◃ k rel (untag-∈⁺ v∈)
... | v″ , v″∈ , eq = v″ , v″∈ , eq
obs-◃ (suc k) {p = ‵⊑ α} {L′ = x ∷ L} (lift all , q , w∋ , rel) v∈
  with All-lookup all v∈
obs-◃ (suc k) {p = ‵⊑ α} {L′ = x ∷ L} {v′ = sealᵛ σ u}
    (lift all , q , w∋ , rel) v∈ | is-seal-at
  with obs-◃ k rel (unseal-∈⁺ v∈)
... | v″ , v″∈ , eq = sealᵛ σ v″ , v″∈ , eq
obs-◃ (suc k) {p = 𝔹⊑} {L′ = x ∷ L} {v′ = v} (lift all) v∈ =
  obs-𝔹 v (All-lookup all v∈)
obs-◃ (suc k) {p = p ⇒⊑ q} {L′ = x ∷ L} {v′ = v}
    (lift all , lift ν∈ , f) v∈ = obs-fun v (All-lookup all v∈) ν∈
obs-◃ (suc k) {p = ∀⊑ p} {L′ = x ∷ L} {v′ = v}
    (lift all , lift ν∈ , f) v∈ = obs-poly v (All-lookup all v∈) ν∈

------------------------------------------------------------------------
-- The fundamental lemma for closed programs
------------------------------------------------------------------------

tok₀ : TOK [] θ₀ []
tok₀ ()

env▹₀ : Env▹ [] θ₀ [] ρ₀ ρ₀
env▹₀ ()

env◃₀ : Env◃ [] θ₀ [] ρ₀ ρ₀
env◃₀ ()

-- a left value of L at counter m has a right counterpart of the same
-- observation
closed▹ : ∀ {L R p} → [] ∣ [] ⊢ L ⊑ R ⦂ p
  → ∀ {v m} → ret v m ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
  → Σ[ v′ ∈ Val ] (ret v′ m ∈ᴿ ⟦ R ⟧ θ₀ ρ₀ 0 × obs v ≡ obs v′)
closed▹ {L} {R} {p} d {v} {m} v∈
  with fundamental▹ d {θ₀} {[]} {ρ₀} {ρ₀} {0} tok₀ env▹₀ ρ₀-consistent refl
         (ret v m ∷ []) (λ { r (here refl) → v∈ })
         m (nonempty (values-∈⁺ {Rs = ret v m ∷ []} (here refl)))
... | W′ , ext , len , rel =
  obs-▹ (suc (sizeᴿᴸ (ret v m ∷ []))) rel
    (values-∈⁺ {Rs = ret v m ∷ []} (here refl))

-- a right value of R at counter m has a left counterpart of the same
-- observation, or L errs
closed◃ : ∀ {L R p} → [] ∣ [] ⊢ L ⊑ R ⦂ p
  → ∀ {v′ m} → ret v′ m ∈ᴿ ⟦ R ⟧ θ₀ ρ₀ 0
  → (Σ[ v ∈ Val ] (ret v m ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0 × obs v′ ≡ obs v))
    ⊎ err ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
closed◃ {L} {R} {p} d {v′} {m} v∈ =
  out (fundamental◃ d {θ₀} {[]} {ρ₀} {ρ₀} {0} tok₀ env◃₀ ρ₀-consistent
         refl (ret v′ m ∷ []) (λ { r (here refl) → v∈ }))
  where
  Rs = ret v′ m ∷ []
  out : [] ∣ θ₀ ⊢ p ⊢ ⟦ L ⟧ θ₀ ρ₀ 0 ◃ᶜ Rs
    → (Σ[ v ∈ Val ] (ret v m ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0 × obs v′ ≡ obs v))
      ⊎ err ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
  out (inj₁ (lift e)) = inj₂ e
  out (inj₂ (lift ne , h))
    with h m (nonempty (values-∈⁺ {Rs = Rs} (here refl)))
  out (inj₂ (lift ne , h)) | W′ , ext , len , rel =
    inj₁ (obs-◃ (suc (sizeᴿᴸ Rs)) rel (values-∈⁺ {Rs = Rs} (here refl)))

-- an error of R is an error of L
closed-err : ∀ {L R p} → [] ∣ [] ⊢ L ⊑ R ⦂ p
  → err ∈ᴿ ⟦ R ⟧ θ₀ ρ₀ 0 → err ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
closed-err {L} {R} {p} d e∈ =
  out (fundamental◃ d {θ₀} {[]} {ρ₀} {ρ₀} {0} tok₀ env◃₀ ρ₀-consistent
         refl (err ∷ []) (λ { r (here refl) → e∈ }))
  where
  out : [] ∣ θ₀ ⊢ p ⊢ ⟦ L ⟧ θ₀ ρ₀ 0 ◃ᶜ (err ∷ []) → err ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
  out (inj₁ (lift e)) = e
  out (inj₂ (lift ne , h)) = ⊥-elim (ne (here refl))

-- a run to a value or to ℧ does not diverge
value-stuck : ∀ {M Σ V} → Diverges M → [] ▷ M —↠ Σ ▷ V → Value V → ⊥
value-stuck div M↠V vV with div M↠V
value-stuck div M↠V vV | Σ′ , N′ , s = value-irreducible vV s

℧-stuck : ∀ {M Σ} → Diverges M → [] ▷ M —↠ Σ ▷ ℧ → ⊥
℧-stuck div M↠℧ with div M↠℧
℧-stuck div M↠℧ | Σ′ , N′ , s = ℧-irreducible s

------------------------------------------------------------------------
-- Graduality
------------------------------------------------------------------------

module _ {M M′ A A′ p}
  {dₗ : [] ∣ [] ⊢ᴳ M ⦂ A} {dᵣ : [] ∣ [] ⊢ᴳ M′ ⦂ A′}
  (d⊑ : [] ∣ [] ⊢ dₗ ⊑ᴳ dᵣ ⦂ p) where

  private
    L = elab dₗ
    R = elab dᵣ
    prec = elab-preserves-precision-closed d⊑
    ⊢L = elab-preserves-typing-closed {Σ = []} dₗ
    ⊢R = elab-preserves-typing-closed {Σ = []} dᵣ

  graduality-⇓ : ∀ {V} → (L⇓ : L ⇓ V)
    → ∃[ V′ ] Σ[ R⇓ ∈ R ⇓ V′ ]
        (observe (proj₂ (proj₂ L⇓)) ≡ observe (proj₂ (proj₂ R⇓)))
  graduality-⇓ (Σ , L↠V , vV) with sound-val ⊢L L↠V vV
  ... | v , v∈ , eq with closed▹ prec v∈
  ... | v′ , v′∈ , eq′ with adequacy-val (elab-scoped dᵣ) v′∈
  ... | Σ′ , V′ , vV′ , R↠V′ , len , eq″ =
    V′ , (Σ′ , R↠V′ , vV′) , trans (sym eq) (trans eq′ eq″)

  graduality-⇓′ : ∀ {V′} → (R⇓ : R ⇓ V′)
    → (∃[ V ] Σ[ L⇓ ∈ L ⇓ V ]
         (observe (proj₂ (proj₂ L⇓)) ≡ observe (proj₂ (proj₂ R⇓))))
      ⊎ Fails L
  graduality-⇓′ {V′} (Σ , R↠V′ , vV′) with sound-val ⊢R R↠V′ vV′
  ... | v′ , v′∈ , eq = out (closed◃ prec v′∈)
    where
    out : (Σ[ v ∈ Val ] (ret v (length Σ) ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
                         × obs v′ ≡ obs v))
          ⊎ err ∈ᴿ ⟦ L ⟧ θ₀ ρ₀ 0
      → (∃[ V ] Σ[ L⇓ ∈ L ⇓ V ]
           (observe (proj₂ (proj₂ L⇓)) ≡ observe vV′))
        ⊎ Fails L
    out (inj₂ e) = inj₂ (adequacy-err (elab-scoped dₗ) e)
    out (inj₁ (v , v∈ , eq′)) with adequacy-val (elab-scoped dₗ) v∈
    out (inj₁ (v , v∈ , eq′)) | Σ″ , V , vV , L↠V , len , eq″ =
      inj₁ (V , (Σ″ , L↠V , vV) , trans (sym eq″) (trans (sym eq′) eq))

  graduality-fails : Fails R → Fails L
  graduality-fails (Σ , R↠℧) =
    adequacy-err (elab-scoped dₗ) (closed-err prec (sound-℧ ⊢R R↠℧))

  graduality-diverges : Diverges L → Diverges R
  graduality-diverges divL {Σ} {N} R↠N = out (type-safety-[] ⊢R R↠N)
    where
    fromVal : ∀ (vN : Value N)
      → (∃[ V ] Σ[ L⇓ ∈ L ⇓ V ]
           (observe (proj₂ (proj₂ L⇓)) ≡ observe vN))
        ⊎ Fails L
      → ⊥
    fromVal vN (inj₁ (V , (Σ″ , L↠V , vV) , eq)) = value-stuck divL L↠V vV
    fromVal vN (inj₂ (Σ″ , L↠℧)) = ℧-stuck divL L↠℧
    fromErr : N ≡ ℧ → ⊥
    fromErr refl with graduality-fails (Σ , R↠N)
    fromErr refl | Σ″ , L↠℧ = ℧-stuck divL L↠℧
    out : Value N ⊎ N ≡ ℧ ⊎ ∃[ Σ″ ] ∃[ N′ ] (Σ ▷ N —→ Σ″ ▷ N′)
      → ∃[ Σ″ ] ∃[ N′ ] (Σ ▷ N —→ Σ″ ▷ N′)
    out (inj₁ vN) = ⊥-elim (fromVal vN (graduality-⇓′ (Σ , R↠N , vN)))
    out (inj₂ (inj₁ eq)) = ⊥-elim (fromErr eq)
    out (inj₂ (inj₂ step)) = step

  graduality-diverges′ : Diverges R → DivergesOrFails L
  graduality-diverges′ divR {Σ} {N} L↠N = out (type-safety-[] ⊢L L↠N)
    where
    out : Value N ⊎ N ≡ ℧ ⊎ ∃[ Σ″ ] ∃[ N′ ] (Σ ▷ N —→ Σ″ ▷ N′)
      → ∃[ Σ″ ] ∃[ N′ ] (Σ ▷ N —→ Σ″ ▷ N′) ⊎ N ≡ ℧
    out (inj₁ vN) with graduality-⇓ (Σ , L↠N , vN)
    out (inj₁ vN) | V′ , (Σ′ , R↠V′ , vV′) , eq =
      ⊥-elim (value-stuck divR R↠V′ vV′)
    out (inj₂ (inj₁ eq)) = inj₂ eq
    out (inj₂ (inj₂ step)) = inj₁ step

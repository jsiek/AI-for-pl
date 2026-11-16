module proof.DenotSoundness where

-- File Charter:
--   * Soundness of the denotation (Denotation.agda) for reduction:
--     subject expansion, `Σ ▷ M —→ Σ′ ▷ N` gives
--     ⟦ N ⟧ θ₀ ρ₀ (length Σ′) ⊆ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ) for a closed
--     well-typed M (expand, expand*), via the substitution lemmas
--     (proof/DenotSubst.agda), the β law of Λ and associativity of bind
--     (proof/DenotProps.agda), and consistency
--     (proof/DenotConsistency.agda).
--   * Typing is needed for one reason: a value must denote a nonempty
--     set, and a function cast `cast d (p ⇒⊑ q) V` denotes a nonempty set
--     only if V is a function (its cast is guarded by νλ).  For example
--     `(ƛ x. true) · cast up (𝔹⊑ ⇒⊑ 𝔹⊑) true` reduces to `true` but
--     denotes nothing.  Closed typed values are nonempty (value-den).
--     Typing also makes the grounds of a closed term closed, which the
--     tag-mismatch rules need.
--   * Consequences: sound-val and sound-℧.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to substEq)

open import Types
open import Terms
open import Reduction
open import Typing
open import StoreWf
open import GraphModel
open import Denotation
open import GradualityDefinitions using (observe)
open import proof.TypeSubst using (stack-substᵀ)
open import proof.Progress using (Fun; c-ƛ; c-cast⇒; canonical-⇒)
open import proof.Preservation using (preserve)
open import proof.Determinism
  using (Plug; ≡-Plug; p-if; p-□·; p-app; p-letv; p-seal; p-unseal; p-is;
         p-inj; p-cast; p-inst)
open import proof.DenotProps
open import proof.DenotSubst
open import proof.DenotConsistency

------------------------------------------------------------------------
-- Closed grounds
------------------------------------------------------------------------

⟦⟧ᴳ-closed : ∀ {G θ} → WfGround 0 G → ⟦ G ⟧ᴳ θ ≡ G
⟦⟧ᴳ-closed (wfG‵ {α = tseal s} tt) = refl
⟦⟧ᴳ-closed (wfG‵ {α = tvar i} ())
⟦⟧ᴳ-closed wfG𝔹 = refl
⟦⟧ᴳ-closed wfG⇒ = refl
⟦⟧ᴳ-closed wfG∀ = refl

⟦⟧ᴳ-≢ : ∀ {G H θ} → WfGround 0 G → WfGround 0 H → G ≢ H
  → ⟦ H ⟧ᴳ θ ≢ ⟦ G ⟧ᴳ θ
⟦⟧ᴳ-≢ wfG wfH G≢H e =
  G≢H (trans (sym (⟦⟧ᴳ-closed wfG)) (trans (sym e) (⟦⟧ᴳ-closed wfH)))

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

cast⇒-den : ∀ {Σ d p q V A B} (vV : Value V) → Σ ∣ [] ∣ [] ⊢ V ⦂ A ⇒ B
  → ∀ θ ρ
  → Σ[ D ∈ 𝒱 ]
      (Σ[ v ∈ Val ] (v ∈ D × obs v ≡ observe (V-cast⇒ {d = d} {p} {q} vV)))
      × (Fun (cast d (p ⇒⊑ q) V) → νλ ∈ D)
      × (∀ n → ⟦ cast d (p ⇒⊑ q) V ⟧ θ ρ n ⊆ᴿ retᴿ D n)
      × (∀ n → retᴿ D n ⊆ᴿ ⟦ cast d (p ⇒⊑ q) V ⟧ θ ρ n)
-- a closed typed value denotes `retᴿ D n` for a nonempty D that does
-- not depend on n and has an element of the value's observation; a
-- function value has νλ
value-den : ∀ {Σ V A} (vV : Value V) → Σ ∣ [] ∣ [] ⊢ V ⦂ A → ∀ θ ρ
  → Σ[ D ∈ 𝒱 ]
      (Σ[ v ∈ Val ] (v ∈ D × obs v ≡ observe vV))
      × (Fun V → νλ ∈ D)
      × (∀ n → ⟦ V ⟧ θ ρ n ⊆ᴿ retᴿ D n)
      × (∀ n → retᴿ D n ⊆ᴿ ⟦ V ⟧ θ ρ n)
value-den V-true ⊢V θ ρ =
  ⌈ vtrue ⌉ , (vtrue , refl , refl) , (λ ()) ,
  (λ n → ⊆ᴿ-refl) , (λ n → ⊆ᴿ-refl)
value-den V-false ⊢V θ ρ =
  ⌈ vfalse ⌉ , (vfalse , refl , refl) , (λ ()) ,
  (λ n → ⊆ᴿ-refl) , (λ n → ⊆ᴿ-refl)
value-den (V-ƛ {A = A} {M = M}) ⊢V θ ρ =
  Λ (λ E m → ⟦ M ⟧ θ (E • ρ) m) , (νλ , tt , refl) , (λ f → tt) ,
  (λ n → ⊆ᴿ-refl) , (λ n → ⊆ᴿ-refl)
value-den (V-Λν {cs = cs} {M = M}) ⊢V θ ρ =
  Λᴾ (λ σ → ⟦ cs ⟧ˢ (σ •ᵗ θ) (⟦ M ⟧ (σ •ᵗ θ) ρ (suc σ))) ,
  (ν∀ , tt , refl) , (λ ()) , (λ n → ⊆ᴿ-refl) , (λ n → ⊆ᴿ-refl)
value-den (V-seal {α = α} v) (⊢seal nt ⊢V) θ ρ with value-den v ⊢V θ ρ
value-den (V-seal {α = α} v) (⊢seal nt ⊢V) θ ρ
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  sealᴾ σ D , (sealᵛ σ u , (refl , u∈) , ob) , (λ ()) ,
  (λ n → ≫=-retᴸ (⊆D n) Km) , (λ n → ≫=-retᴿ (D⊆ n) (u , u∈) Km)
  where
  σ = ⟦ α ⟧ₙ θ
  Km : ∀ {E E′} m → E ⊆ E′ → retᴿ (sealᴾ σ E) m ⊆ᴿ retᴿ (sealᴾ σ E′) m
  Km m E⊆ = retᴿ-mono (sealᴾ-mono E⊆)
value-den (V-inj {G = G} v) (⊢inj wfG ⊢V) θ ρ with value-den v ⊢V θ ρ
value-den (V-inj {G = G} v) (⊢inj wfG ⊢V) θ ρ
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  injᴾ G′ D , (injᵛ G′ u , (refl , u∈) , ob) , (λ ()) ,
  (λ n → ≫=-retᴸ (⊆D n) Km) , (λ n → ≫=-retᴿ (D⊆ n) (u , u∈) Km)
  where
  G′ = ⟦ G ⟧ᴳ θ
  Km : ∀ {E E′} m → E ⊆ E′ → retᴿ (injᴾ G′ E) m ⊆ᴿ retᴿ (injᴾ G′ E′) m
  Km m E⊆ = retᴿ-mono (injᴾ-mono E⊆)
value-den (V-cast⇒ v) (⊢up (⊑⇒ p⊢ q⊢) ⊢V) θ ρ = cast⇒-den v ⊢V θ ρ
value-den (V-cast⇒ v) (⊢down (⊑⇒ p⊢ q⊢) ⊢V) θ ρ = cast⇒-den v ⊢V θ ρ

cast⇒-den {d = d} {p} {q} v ⊢V θ ρ with value-den v ⊢V θ ρ
cast⇒-den {d = d} {p} {q} v ⊢V θ ρ | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  Λ (λ E′ m′ → ⟦ flip d , p ⟧ᶜ θ E′ m′ ≫= λ E₁ m₁ →
               (D ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ) ,
  (νλ , tt , refl) , (λ f → tt) ,
  (λ n → ⊆ᴿ-trans (≫=-retᴸ (⊆D n) (λ m → ⟦⟧ᶜ-mono d (p ⇒⊑ q) θ))
                  (guard-elim {v = νλ} {D = D})) ,
  (λ n → ⊆ᴿ-trans (guard-intro {D = D} νλ∈)
           (≫=-retᴿ (D⊆ n) (u , u∈) (λ m → ⟦⟧ᶜ-mono d (p ⇒⊑ q) θ)))
  where
  νλ∈ : νλ ∈ D
  νλ∈ = fν (canonical-⇒ v ⊢V)

-- the set of a value is consistent
value-consistent : ∀ {D V θ} → (∀ n → retᴿ D n ⊆ᴿ ⟦ V ⟧ θ ρ₀ n)
  → Consistent D
value-consistent {V = V} {θ} D⊆ u w u∈ w∈ =
  ⌊⌋-consistent (⟦⟧-consistent V θ {n = 0} ρ₀-consistent) 0 u w
    (D⊆ 0 (ret u 0) (refl , u∈)) (D⊆ 0 (ret w 0) (refl , w∈))

------------------------------------------------------------------------
-- The β-steps
------------------------------------------------------------------------

β-cast⇒-sound : ∀ {Σ d p q V W A B C} n
  → Value V → Σ ∣ [] ∣ [] ⊢ V ⦂ A ⇒ B
  → Value W → Σ ∣ [] ∣ [] ⊢ W ⦂ C
  → ⟦ cast d q (V · cast (flip d) p W) ⟧ θ₀ ρ₀ n
    ⊆ᴿ ⟦ cast d (p ⇒⊑ q) V · W ⟧ θ₀ ρ₀ n
β-cast⇒-sound {d = d} {p} {q} {V} {W} n v ⊢V w ⊢W
  with value-den v ⊢V θ₀ ρ₀ | value-den w ⊢W θ₀ ρ₀
β-cast⇒-sound {d = d} {p} {q} {V} {W} n v ⊢V w ⊢W
  | DV , (u , u∈ , ob) , fν , ⊆DV , DV⊆
  | DW , (u′ , u′∈ , ob′) , fν′ , ⊆DW , DW⊆ =
  ⊆ᴿ-trans step₁ (⊆ᴿ-trans step₂ (⊆ᴿ-trans step₃
    (⊆ᴿ-trans (Λ-βᶜ d p q θ₀ DV (value-consistent {V = W} {θ₀} DW⊆)
                (u′ , u′∈))
              step₅)))
  where
  Cp = ⟦ flip d , p ⟧ᶜ θ₀
  Cq = ⟦ d , q ⟧ᶜ θ₀
  Cpm : ∀ {E E′} m → E ⊆ E′ → Cp E m ⊆ᴿ Cp E′ m
  Cpm m = ⟦⟧ᶜ-mono (flip d) p θ₀
  Cqm : ∀ {E E′} m → E ⊆ E′ → Cq E m ⊆ᴿ Cq E′ m
  Cqm m = ⟦⟧ᶜ-mono d q θ₀
  G : 𝒱 → ℕ → ℛ
  G E′ m′ = Cp E′ m′ ≫= λ E₁ m₁ → (DV ●[ m₁ ] E₁) ≫= Cq
  step₁ : ⟦ cast d q (V · cast (flip d) p W) ⟧ θ₀ ρ₀ n
    ⊆ᴿ (((⟦ W ⟧ θ₀ ρ₀ n ≫= Cp) ≫= λ E n₂ → DV ●[ n₂ ] E) ≫= Cq)
  step₁ = ≫=-mono (≫=-retᴸ (⊆DV n) (λ m F⊆ →
            ≫=-mono (⊆ᴿ-refl {R = ⟦ W ⟧ θ₀ ρ₀ m ≫= Cp})
                    (λ n₂ E⊆ → ●-mono F⊆ E⊆)))
            Cqm
  step₂ : (((⟦ W ⟧ θ₀ ρ₀ n ≫= Cp) ≫= λ E n₂ → DV ●[ n₂ ] E) ≫= Cq)
    ⊆ᴿ ((Cp DW n ≫= λ E n₂ → DV ●[ n₂ ] E) ≫= Cq)
  step₂ = ≫=-mono (≫=-mono (≫=-retᴸ (⊆DW n) Cpm)
                    (λ n₂ E⊆ → ●-mono {D = DV} ⊆-refl E⊆)) Cqm
  step₃ : ((Cp DW n ≫= λ E n₂ → DV ●[ n₂ ] E) ≫= Cq) ⊆ᴿ G DW n
  step₃ = ≫=-assoc {R = Cp DW n} {K = λ E n₂ → DV ●[ n₂ ] E}
            (⟦⟧ᶜ-pure (flip d) p θ₀) Cqm
  step₅ : (Λ G ●[ n ] DW) ⊆ᴿ ⟦ cast d (p ⇒⊑ q) V · W ⟧ θ₀ ρ₀ n
  step₅ =
    ⊆ᴿ-trans
      (≫=-retᴿ {K = λ E n₂ → Λ G ●[ n₂ ] E} (DW⊆ n) (u′ , u′∈)
        (λ m E⊆ → ●-mono {D = Λ G} ⊆-refl E⊆))
      (≫=-retᴿ {K = λ F n₁ → ⟦ W ⟧ θ₀ ρ₀ n₁ ≫= λ E n₂ → F ●[ n₂ ] E}
        (⊆ᴿ-trans (guard-intro {D = DV} (fν (canonical-⇒ v ⊢V)))
          (≫=-retᴿ (DV⊆ n) (u , u∈) (λ m → ⟦⟧ᶜ-mono d (p ⇒⊑ q) θ₀)))
        (νλ , tt)
        (λ m F⊆ → ≫=-mono (⊆ᴿ-refl {R = ⟦ W ⟧ θ₀ ρ₀ m})
                           (λ n₂ E⊆ → ●-mono F⊆ E⊆)))

β-inst-sound : ∀ cs M B N n
  → ⟦ letv (stack cs M [ tseal n ]ᵀ) (N [ tseal n ]ᵀ) ⟧ θ₀ ρ₀ (suc n)
    ⊆ᴿ ⟦ inst (Λν cs M) B N ⟧ θ₀ ρ₀ n
β-inst-sound cs M B N n =
  ⊆ᴿ-trans
    (≫=-mono body (λ {E} {E′} m E⊆ →
      outᴿ (⟦⟧-[]ᵀ fwd N {θ₀} {E • ρ₀} {E′ • ρ₀} {m} n
             (ext-Sub fwd (sub E⊆) (λ x → sub ⊆-refl)))))
    (≫=-retᴿ ⊆ᴿ-refl (ν∀ , tt) (λ m F⊆ →
      ≫=-mono (◆-mono {σ = m} F⊆)
        (λ m₂ E⊆ → ⟦⟧-mono N (ext-⊆ₑ E⊆ ⊆ₑ-refl))))
  where
  α = tseal n
  stack≡ : ⟦ stack cs M [ α ]ᵀ ⟧ θ₀ ρ₀ (suc n)
         ≡ ⟦ substˢ (singleₙ α) cs ⟧ˢ θ₀ (⟦ M [ α ]ᵀ ⟧ θ₀ ρ₀ (suc n))
  stack≡ =
    trans (cong (λ T → ⟦ T ⟧ θ₀ ρ₀ (suc n)) (stack-substᵀ (singleₙ α) cs M))
          (⟦stack⟧ (substˢ (singleₙ α) cs) (M [ α ]ᵀ) θ₀ ρ₀ (suc n))
  body : ⟦ stack cs M [ α ]ᵀ ⟧ θ₀ ρ₀ (suc n)
    ⊆ᴿ ⟦ cs ⟧ˢ (n •ᵗ θ₀) (⟦ M ⟧ (n •ᵗ θ₀) ρ₀ (suc n))
  body r r∈ =
    outᴿ (⟦⟧ˢ-[]ᵀ fwd cs n (⟦⟧-[]ᵀ fwd M n (λ x → sub ⊆-refl))) r
      (substEq (λ R → r ∈ᴿ R) stack≡ r∈)

------------------------------------------------------------------------
-- Subject expansion
------------------------------------------------------------------------

length-snoc : ∀ (Σ : Store) B → length (Σ ++ (B ∷ [])) ≡ suc (length Σ)
length-snoc [] B = refl
length-snoc (A ∷ Σ) B = cong suc (length-snoc Σ B)

-- the error results of a frame around ℧
℧-frame : ∀ {Σ A} F → Σ ∣ [] ∣ [] ⊢ plug F ℧ ⦂ A → ∀ n
  → err ∈ᴿ ⟦ plug F ℧ ⟧ θ₀ ρ₀ n
℧-frame (if□ M N) ⊢T n = inj₁ (refl , tt)
℧-frame (□· M) ⊢T n = inj₁ (refl , tt)
℧-frame (app□ V v) (⊢· ⊢V ⊢℧) n with value-den v ⊢V θ₀ ρ₀
℧-frame (app□ V v) (⊢· ⊢V ⊢℧) n | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  inj₂ (n , (u , D⊆ n (ret u n) (refl , u∈)) , inj₁ (refl , tt))
℧-frame (letv□ N) ⊢T n = inj₁ (refl , tt)
℧-frame (seal□ α) ⊢T n = inj₁ (refl , tt)
℧-frame (unseal□ α) ⊢T n = inj₁ (refl , tt)
℧-frame (is□ G) ⊢T n = inj₁ (refl , tt)
℧-frame (inj□ G) ⊢T n = inj₁ (refl , tt)
℧-frame (cast□ d p) ⊢T n = inj₁ (refl , tt)
℧-frame (inst□ B N) ⊢T n = inj₁ (refl , tt)

-- applying a value, as a function of the argument's results
app-value : ∀ {Σ V A n n′ M M′} → Value V → Σ ∣ [] ∣ [] ⊢ V ⦂ A
  → ⟦ M′ ⟧ θ₀ ρ₀ n′ ⊆ᴿ ⟦ M ⟧ θ₀ ρ₀ n
  → ⟦ V · M′ ⟧ θ₀ ρ₀ n′ ⊆ᴿ ⟦ V · M ⟧ θ₀ ρ₀ n
app-value {V = V} {n = n} {n′} {M} {M′} v ⊢V M⊆ with value-den v ⊢V θ₀ ρ₀
app-value {V = V} {n = n} {n′} {M} {M′} v ⊢V M⊆
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans (≫=-retᴸ (⊆D n′) (Km M′))
    (⊆ᴿ-trans (≫=-mono M⊆ (λ n₂ E⊆ → ●-mono {D = D} ⊆-refl E⊆))
      (≫=-retᴿ (D⊆ n) (u , u∈) (Km M)))
  where
  Km : ∀ L {F F′} m → F ⊆ F′
    → (⟦ L ⟧ θ₀ ρ₀ m ≫= λ E n₂ → F ●[ n₂ ] E)
      ⊆ᴿ (⟦ L ⟧ θ₀ ρ₀ m ≫= λ E n₂ → F′ ●[ n₂ ] E)
  Km L m F⊆ = ≫=-mono (⊆ᴿ-refl {R = ⟦ L ⟧ θ₀ ρ₀ m})
                      (λ n₂ E⊆ → ●-mono F⊆ E⊆)

expand-plug : ∀ {Σ Σ′ F M N T A} → Plug F M T
  → Σ ∣ [] ∣ [] ⊢ T ⦂ A → Σ ▷ M —→ Σ′ ▷ N
  → ⟦ plug F N ⟧ θ₀ ρ₀ (length Σ′) ⊆ᴿ ⟦ T ⟧ θ₀ ρ₀ (length Σ)

expand : ∀ {Σ Σ′ M N A} → Σ ∣ [] ∣ [] ⊢ M ⦂ A → Σ ▷ M —→ Σ′ ▷ N
  → ⟦ N ⟧ θ₀ ρ₀ (length Σ′) ⊆ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ)
expand ⊢T (ξξ F eq refl s) = expand-plug (≡-Plug F eq) ⊢T s
expand {Σ = Σ} {A = A} ⊢T (ξξ-℧ F eq) err tt =
  substEq (λ T → err ∈ᴿ ⟦ T ⟧ θ₀ ρ₀ (length Σ)) (sym eq)
    (℧-frame F (substEq (λ T → Σ ∣ [] ∣ [] ⊢ T ⦂ A) eq ⊢T) (length Σ))
expand {Σ = Σ} (⊢letv {N = N} ⊢V ⊢N) (β-letv {V = V} v)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢letv {N = N} ⊢V ⊢N) (β-letv {V = V} v)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans (outᴿ (⟦⟧-[] fwd N V (λ m → subᴿ (⊆D m))))
    (≫=-retᴿ (D⊆ (length Σ)) (u , u∈)
      (λ m E⊆ → ⟦⟧-mono N (ext-⊆ₑ E⊆ ⊆ₑ-refl)))
expand {Σ = Σ} (⊢unseal nt (⊢seal nt′ ⊢V)) (β-unseal {α = α} {V = V} v)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢unseal nt (⊢seal nt′ ⊢V)) (β-unseal {α = α} {V = V} v)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans (⊆D n)
    (⊆ᴿ-trans (retᴿ-mono (λ w w∈ → refl , w∈))
      (≫=-retᴿ
        (≫=-retᴿ (D⊆ n) (u , u∈) (λ m E⊆ → retᴿ-mono (sealᴾ-mono E⊆)))
        (sealᵛ σ u , refl , u∈)
        (λ m E⊆ → retᴿ-mono (unsealᴾ-mono {σ = σ} E⊆))))
  where
  n = length Σ
  σ = ⟦ α ⟧ₙ θ₀
expand {Σ = Σ} (⊢is wfG (⊢inj wfG′ ⊢V)) (β-is-yes {G = G} v)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢is wfG (⊢inj wfG′ ⊢V)) (β-is-yes {G = G} v)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans (retᴿ-mono (λ { w refl → u , refl , u∈ }))
    (≫=-retᴿ
      (≫=-retᴿ (D⊆ n) (u , u∈) (λ m E⊆ → retᴿ-mono (injᴾ-mono E⊆)))
      (injᵛ G′ u , refl , u∈)
      (λ m E⊆ → retᴿ-mono (testᴾ-mono {G = G′} E⊆)))
  where
  n = length Σ
  G′ = ⟦ G ⟧ᴳ θ₀
expand {Σ = Σ} (⊢is wfG (⊢inj wfH ⊢V)) (β-is-no {G = G} {H = H} v G≢H)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢is wfG (⊢inj wfH ⊢V)) (β-is-no {G = G} {H = H} v G≢H)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans
    (retᴿ-mono (λ { w refl → H′ , u , (refl , u∈) , ⟦⟧ᴳ-≢ wfG wfH G≢H }))
    (≫=-retᴿ
      (≫=-retᴿ (D⊆ n) (u , u∈) (λ m E⊆ → retᴿ-mono (injᴾ-mono E⊆)))
      (injᵛ H′ u , refl , u∈)
      (λ m E⊆ → retᴿ-mono (testᴾ-mono {G = ⟦ G ⟧ᴳ θ₀} E⊆)))
  where
  n = length Σ
  H′ = ⟦ H ⟧ᴳ θ₀
expand {Σ = Σ} ⊢T β-if-true r r∈ =
  inj₂ (length Σ , (vtrue , refl , refl) , inj₁ ((refl , refl) , r∈))
expand {Σ = Σ} ⊢T β-if-false r r∈ =
  inj₂ (length Σ , (vfalse , refl , refl) , inj₂ ((refl , refl) , r∈))
expand {Σ = Σ} (⊢· (⊢ƛ {M = M} ⊢M) ⊢V) (β-ƛ {A = A} {V = V} v)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢· (⊢ƛ {M = M} ⊢M) ⊢V) (β-ƛ {A = A} {V = V} v)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans (outᴿ (⟦⟧-[] fwd M V (λ m → subᴿ (⊆D m))))
    (⊆ᴿ-trans
      (Λ-β M θ₀ ρ₀ (value-consistent {V = V} {θ₀} D⊆) (u , u∈))
      (⊆ᴿ-trans
        (≫=-retᴿ {K = λ E n₂ → Λ F ●[ n₂ ] E} (D⊆ n) (u , u∈)
          (λ m E⊆ → ●-mono {D = Λ F} ⊆-refl E⊆))
        (≫=-retᴿ {K = λ F′ n₁ → ⟦ V ⟧ θ₀ ρ₀ n₁ ≫= λ E n₂ → F′ ●[ n₂ ] E}
          ⊆ᴿ-refl (νλ , tt)
          (λ m F⊆ → ≫=-mono (⊆ᴿ-refl {R = ⟦ V ⟧ θ₀ ρ₀ m})
                             (λ n₂ E⊆ → ●-mono F⊆ E⊆)))))
  where
  n = length Σ
  F : 𝒱 → ℕ → ℛ
  F E m = ⟦ M ⟧ θ₀ (E • ρ₀) m
expand (⊢· (⊢up (⊑⇒ p⊢ q⊢) ⊢V) ⊢W) (β-cast⇒ {d = d} {p} {q} v w) =
  β-cast⇒-sound {d = d} {p} {q} _ v ⊢V w ⊢W
expand (⊢· (⊢down (⊑⇒ p⊢ q⊢) ⊢V) ⊢W) (β-cast⇒ {d = d} {p} {q} v w) =
  β-cast⇒-sound {d = d} {p} {q} _ v ⊢V w ⊢W
expand {Σ = Σ} ⊢T (β-inst {cs = cs} {M = M} {B = B} {N = N}) =
  substEq (λ k → ⟦ letv (stack cs M [ tseal (length Σ) ]ᵀ)
                         (N [ tseal (length Σ) ]ᵀ) ⟧ θ₀ ρ₀ k
                 ⊆ᴿ ⟦ inst (Λν cs M) B N ⟧ θ₀ ρ₀ (length Σ))
    (sym (length-snoc Σ B)) (β-inst-sound cs M B N (length Σ))
expand ⊢T (β-id at★ v) = ≫=-unit
expand ⊢T (β-id at𝔹 v) = ≫=-unit
expand ⊢T (β-id at‵ v) = ≫=-unit
expand {Σ = Σ} (⊢up (⊑tag wfG p⊢) ⊢V) (β-tag-up {G = G} {p = p} v)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢up (⊑tag wfG p⊢) ⊢V) (β-tag-up {G = G} {p = p} v)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans
    (≫=-mono (≫=-retᴸ (⊆D n) (λ m → ⟦⟧ᶜ-mono up p θ₀))
      (λ m₁ E⊆ → retᴿ-mono (injᴾ-mono E⊆)))
    (≫=-retᴿ (D⊆ n) (u , u∈) (λ m → ⟦⟧ᶜ-mono up (tag G p) θ₀))
  where
  n = length Σ
expand {Σ = Σ} (⊢down (⊑tag wfG p⊢) (⊢inj wfG′ ⊢V))
    (β-tag-down {G = G} {p = p} v)
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢down (⊑tag wfG p⊢) (⊢inj wfG′ ⊢V))
    (β-tag-down {G = G} {p = p} v)
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  ⊆ᴿ-trans (≫=-retᴸ (⊆D n) (λ m → ⟦⟧ᶜ-mono down p θ₀))
    (⊆ᴿ-trans
      (≫=-retᴿ {R = proj G′ (injᴾ G′ D) n} {K = ⟦ down , p ⟧ᶜ θ₀}
        (λ { (ret w m) (e , w∈) → e , refl , w∈ }) (u , u∈)
        (λ m → ⟦⟧ᶜ-mono down p θ₀))
      (≫=-retᴿ
        (≫=-retᴿ (D⊆ n) (u , u∈) (λ m E⊆ → retᴿ-mono (injᴾ-mono E⊆)))
        (injᵛ G′ u , refl , u∈)
        (λ m → ⟦⟧ᶜ-mono down (tag G p) θ₀)))
  where
  n = length Σ
  G′ = ⟦ G ⟧ᴳ θ₀
expand {Σ = Σ} (⊢down (⊑tag wfG p⊢) (⊢inj wfH ⊢V))
    (β-tag-down-℧ {G = G} {H = H} v G≢H) err tt
  with value-den v ⊢V θ₀ ρ₀
expand {Σ = Σ} (⊢down (⊑tag wfG p⊢) (⊢inj {M = V} wfH ⊢V))
    (β-tag-down-℧ {G = G} {H = H} v G≢H) err tt
  | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  inj₂ (n , (injᵛ H′ u , inj∈) ,
        inj₁ (refl , H′ , u , inj∈ , ⟦⟧ᴳ-≢ wfG wfH G≢H))
  where
  n = length Σ
  H′ = ⟦ H ⟧ᴳ θ₀
  inj∈ : ret (injᵛ H′ u) n ∈ᴿ ⟦ inj H V ⟧ θ₀ ρ₀ n
  inj∈ = ≫=-retᴿ (D⊆ n) (u , u∈) (λ m E⊆ → retᴿ-mono (injᴾ-mono E⊆))
           (ret (injᵛ H′ u) n) (refl , refl , u∈)
expand {Σ = Σ} ⊢T (β-cast∀ {d = d} {p = p} {cs = cs} {M = M}) =
  ⊆ᴿ-trans
    (guard-intro {v = ν∀}
      {D = Λᴾ (λ σ → ⟦ cs ⟧ˢ (σ •ᵗ θ₀) (⟦ M ⟧ (σ •ᵗ θ₀) ρ₀ (suc σ)))} tt)
    (≫=-retᴿ ⊆ᴿ-refl (ν∀ , tt) (λ m → ⟦⟧ᶜ-mono d (∀⊑ p) θ₀))

expand-plug (p-if {M = M} {N = N}) (⊢if ⊢L ⊢M ⊢N) s =
  ≫=-mono (expand ⊢L s)
    (λ m D⊆ → condᴿ-mono D⊆ (⊆ᴿ-refl {R = ⟦ M ⟧ θ₀ ρ₀ m})
                            (⊆ᴿ-refl {R = ⟦ N ⟧ θ₀ ρ₀ m}))
expand-plug (p-□· {M = M}) (⊢· ⊢L ⊢M) s =
  ≫=-mono (expand ⊢L s) (λ n₁ F⊆ →
    ≫=-mono (⊆ᴿ-refl {R = ⟦ M ⟧ θ₀ ρ₀ n₁}) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
expand-plug {N = N₁} (p-app {v = v} {M = M₁}) (⊢· ⊢V ⊢M) s =
  app-value {M = M₁} {M′ = N₁} v ⊢V (expand ⊢M s)
expand-plug (p-letv {N = N}) (⊢letv ⊢M ⊢N) s =
  ≫=-mono (expand ⊢M s) (λ m D⊆ → ⟦⟧-mono N (ext-⊆ₑ D⊆ ⊆ₑ-refl))
expand-plug p-seal (⊢seal nt ⊢M) s =
  ≫=-mono (expand ⊢M s) (λ m D⊆ → retᴿ-mono (sealᴾ-mono D⊆))
expand-plug p-unseal (⊢unseal nt ⊢M) s =
  ≫=-mono (expand ⊢M s) (λ m D⊆ → retᴿ-mono (unsealᴾ-mono D⊆))
expand-plug p-is (⊢is wfG ⊢M) s =
  ≫=-mono (expand ⊢M s) (λ m D⊆ → retᴿ-mono (testᴾ-mono D⊆))
expand-plug p-inj (⊢inj wfG ⊢M) s =
  ≫=-mono (expand ⊢M s) (λ m D⊆ → retᴿ-mono (injᴾ-mono D⊆))
expand-plug (p-cast {p = p}) (⊢up p⊢ ⊢M) s =
  ≫=-mono (expand ⊢M s) (λ m → ⟦⟧ᶜ-mono up p θ₀)
expand-plug (p-cast {p = p}) (⊢down p⊢ ⊢M) s =
  ≫=-mono (expand ⊢M s) (λ m → ⟦⟧ᶜ-mono down p θ₀)
expand-plug (p-inst {N = N}) (⊢inst ⊢M wfB ⊢N) s =
  ≫=-mono (expand ⊢M s) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆) (λ n₂ E⊆ → ⟦⟧-mono N (ext-⊆ₑ E⊆ ⊆ₑ-refl)))

expand* : ∀ {Σ Σ′ M N A} → StoreWf Σ → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —↠ Σ′ ▷ N
  → ⟦ N ⟧ θ₀ ρ₀ (length Σ′) ⊆ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ)
expand* wfΣ ⊢M (M ∎) = ⊆ᴿ-refl
expand* wfΣ ⊢M (M —→⟨ s ⟩ M↠N) with preserve wfΣ ⊢M s
expand* wfΣ ⊢M (M —→⟨ s ⟩ M↠N) | ⊢M′ , wfΣ′ =
  ⊆ᴿ-trans (expand* wfΣ′ ⊢M′ M↠N) (expand ⊢M s)

------------------------------------------------------------------------
-- Soundness
------------------------------------------------------------------------

typed-steps : ∀ {Σ Σ′ M N A} → StoreWf Σ → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —↠ Σ′ ▷ N → Σ′ ∣ [] ∣ [] ⊢ N ⦂ A
typed-steps wfΣ ⊢M (M ∎) = ⊢M
typed-steps wfΣ ⊢M (M —→⟨ s ⟩ M↠N) with preserve wfΣ ⊢M s
typed-steps wfΣ ⊢M (M —→⟨ s ⟩ M↠N) | ⊢M′ , wfΣ′ =
  typed-steps wfΣ′ ⊢M′ M↠N

sound-val : ∀ {Σ Σ′ M V A} → StoreWf Σ → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —↠ Σ′ ▷ V → (vV : Value V)
  → Σ[ v ∈ Val ] (ret v (length Σ′) ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ)
                  × obs v ≡ observe vV)
sound-val {Σ′ = Σ′} wfΣ ⊢M M↠V vV
  with value-den vV (typed-steps wfΣ ⊢M M↠V) θ₀ ρ₀
sound-val {Σ′ = Σ′} wfΣ ⊢M M↠V vV | D , (u , u∈ , ob) , fν , ⊆D , D⊆ =
  u , expand* wfΣ ⊢M M↠V _ (D⊆ (length Σ′) _ (refl , u∈)) , ob

sound-℧ : ∀ {Σ Σ′ M A} → StoreWf Σ → Σ ∣ [] ∣ [] ⊢ M ⦂ A
  → Σ ▷ M —↠ Σ′ ▷ ℧ → err ∈ᴿ ⟦ M ⟧ θ₀ ρ₀ (length Σ)
sound-℧ wfΣ ⊢M M↠℧ = expand* wfΣ ⊢M M↠℧ err tt

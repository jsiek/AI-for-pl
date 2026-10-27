module proof.LabelIrrelevance where

-- File Charter:
--   * Labels on instantiations do not affect evaluation: the
--     label-insensitive equalities `_≈ˡ_` on terms and `_≈ˢ_` on stores
--     (proof/Relabel.agda) form a lockstep bisimulation for reduction.
--   * Syntactic closure of ≈ˡ: name substitution (substᵀ), term
--     renaming and substitution, `stack`, and plugging into related
--     frames (`_≈ᶠ_`); values and ℧ are preserved and reflected, and
--     related values have the same observation.
--   * Main theorems, stated at the end of the file:
--       - `label-irrelevance-step` and `label-irrelevance-multi`
--         (simulation, one step and many steps);
--       - `converge-transfer`, `fails-transfer`, `diverges-transfer`
--         for closed programs run from the empty store, in the
--         vocabulary of GradualityDefinitions.agda.
--   * ≈ˡ and ≈ˢ are symmetric, so each statement also holds with the
--     two sides swapped.

open import Data.List using ([]; _∷_; length; _++_)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Types
open import Terms
open import Reduction
open import GradualityDefinitions
open import proof.Relabel

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

substᵀ-≈ : ∀ σ {M M′} → M ≈ˡ M′ → substᵀ σ M ≈ˡ substᵀ σ M′
substᵀ-≈ σ ≈` = ≈`
substᵀ-≈ σ ≈℧ = ≈℧
substᵀ-≈ σ ≈true = ≈true
substᵀ-≈ σ ≈false = ≈false
substᵀ-≈ σ (≈if L≈ M≈ N≈) =
  ≈if (substᵀ-≈ σ L≈) (substᵀ-≈ σ M≈) (substᵀ-≈ σ N≈)
substᵀ-≈ σ (≈ƛ M≈) = ≈ƛ (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈· L≈ M≈) = ≈· (substᵀ-≈ σ L≈) (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈letv M≈ N≈) = ≈letv (substᵀ-≈ σ M≈) (substᵀ-≈ σ N≈)
substᵀ-≈ σ (≈seal M≈) = ≈seal (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈unseal M≈) = ≈unseal (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈is M≈) = ≈is (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈inj M≈) = ≈inj (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈cast M≈) = ≈cast (substᵀ-≈ σ M≈)
substᵀ-≈ σ (≈Λν M≈) = ≈Λν (substᵀ-≈ (extₙ σ) M≈)
substᵀ-≈ σ (≈inst M≈ N≈) =
  ≈inst (substᵀ-≈ σ M≈) (substᵀ-≈ (extₙ σ) N≈)

rename-≈ : ∀ ρ {M M′} → M ≈ˡ M′ → rename ρ M ≈ˡ rename ρ M′
rename-≈ ρ ≈` = ≈`
rename-≈ ρ ≈℧ = ≈℧
rename-≈ ρ ≈true = ≈true
rename-≈ ρ ≈false = ≈false
rename-≈ ρ (≈if L≈ M≈ N≈) =
  ≈if (rename-≈ ρ L≈) (rename-≈ ρ M≈) (rename-≈ ρ N≈)
rename-≈ ρ (≈ƛ M≈) = ≈ƛ (rename-≈ (ext ρ) M≈)
rename-≈ ρ (≈· L≈ M≈) = ≈· (rename-≈ ρ L≈) (rename-≈ ρ M≈)
rename-≈ ρ (≈letv M≈ N≈) = ≈letv (rename-≈ ρ M≈) (rename-≈ (ext ρ) N≈)
rename-≈ ρ (≈seal M≈) = ≈seal (rename-≈ ρ M≈)
rename-≈ ρ (≈unseal M≈) = ≈unseal (rename-≈ ρ M≈)
rename-≈ ρ (≈is M≈) = ≈is (rename-≈ ρ M≈)
rename-≈ ρ (≈inj M≈) = ≈inj (rename-≈ ρ M≈)
rename-≈ ρ (≈cast M≈) = ≈cast (rename-≈ ρ M≈)
rename-≈ ρ (≈Λν M≈) = ≈Λν (rename-≈ ρ M≈)
rename-≈ ρ (≈inst M≈ N≈) = ≈inst (rename-≈ ρ M≈) (rename-≈ (ext ρ) N≈)

infix 4 _≈ᵛ_

-- pointwise label-insensitive equality of term substitutions
_≈ᵛ_ : Subst → Subst → Set
σ ≈ᵛ τ = ∀ x → σ x ≈ˡ τ x

exts-≈ : ∀ {σ τ} → σ ≈ᵛ τ → exts σ ≈ᵛ exts τ
exts-≈ eq zero = ≈`
exts-≈ eq (suc x) = rename-≈ suc (eq x)

⇑ˢ-≈ : ∀ {σ τ} → σ ≈ᵛ τ → ⇑ˢ σ ≈ᵛ ⇑ˢ τ
⇑ˢ-≈ eq x = substᵀ-≈ ↑ₙ (eq x)

subst-≈ : ∀ {σ τ M M′} → σ ≈ᵛ τ → M ≈ˡ M′ → subst σ M ≈ˡ subst τ M′
subst-≈ eq (≈` {x = x}) = eq x
subst-≈ eq ≈℧ = ≈℧
subst-≈ eq ≈true = ≈true
subst-≈ eq ≈false = ≈false
subst-≈ eq (≈if L≈ M≈ N≈) =
  ≈if (subst-≈ eq L≈) (subst-≈ eq M≈) (subst-≈ eq N≈)
subst-≈ eq (≈ƛ M≈) = ≈ƛ (subst-≈ (exts-≈ eq) M≈)
subst-≈ eq (≈· L≈ M≈) = ≈· (subst-≈ eq L≈) (subst-≈ eq M≈)
subst-≈ eq (≈letv M≈ N≈) = ≈letv (subst-≈ eq M≈) (subst-≈ (exts-≈ eq) N≈)
subst-≈ eq (≈seal M≈) = ≈seal (subst-≈ eq M≈)
subst-≈ eq (≈unseal M≈) = ≈unseal (subst-≈ eq M≈)
subst-≈ eq (≈is M≈) = ≈is (subst-≈ eq M≈)
subst-≈ eq (≈inj M≈) = ≈inj (subst-≈ eq M≈)
subst-≈ eq (≈cast M≈) = ≈cast (subst-≈ eq M≈)
subst-≈ eq (≈Λν M≈) = ≈Λν (subst-≈ (⇑ˢ-≈ eq) M≈)
subst-≈ eq (≈inst M≈ N≈) =
  ≈inst (subst-≈ eq M≈) (subst-≈ (exts-≈ (⇑ˢ-≈ eq)) N≈)

single-≈ : ∀ {V V′} → V ≈ˡ V′ → single V ≈ᵛ single V′
single-≈ V≈ zero = V≈
single-≈ V≈ (suc x) = ≈`

[]-≈ : ∀ {N N′ V V′} → N ≈ˡ N′ → V ≈ˡ V′ → N [ V ] ≈ˡ N′ [ V′ ]
[]-≈ N≈ V≈ = subst-≈ (single-≈ V≈) N≈

stack-≈ : ∀ cs {M M′} → M ≈ˡ M′ → stack cs M ≈ˡ stack cs M′
stack-≈ [] M≈ = M≈
stack-≈ ((d , p) ∷ cs) M≈ = ≈cast (stack-≈ cs M≈)

------------------------------------------------------------------------
-- Values, ℧ and observations
------------------------------------------------------------------------

value-≈ : ∀ {V V′} → V ≈ˡ V′ → Value V → Value V′
value-≈ ≈true V-true = V-true
value-≈ ≈false V-false = V-false
value-≈ (≈ƛ M≈) V-ƛ = V-ƛ
value-≈ (≈Λν M≈) V-Λν = V-Λν
value-≈ (≈seal V≈) (V-seal v) = V-seal (value-≈ V≈ v)
value-≈ (≈inj V≈) (V-inj v) = V-inj (value-≈ V≈ v)
value-≈ (≈cast V≈) (V-cast⇒ v) = V-cast⇒ (value-≈ V≈ v)

observe-≈ : ∀ {V V′} → V ≈ˡ V′ → (v : Value V) (v′ : Value V′)
  → observe v ≡ observe v′
observe-≈ ≈true V-true V-true = refl
observe-≈ ≈false V-false V-false = refl
observe-≈ (≈ƛ M≈) V-ƛ V-ƛ = refl
observe-≈ (≈Λν M≈) V-Λν V-Λν = refl
observe-≈ (≈seal V≈) (V-seal v) (V-seal v′) = observe-≈ V≈ v v′
observe-≈ (≈inj V≈) (V-inj v) (V-inj v′) = observe-≈ V≈ v v′
observe-≈ (≈cast V≈) (V-cast⇒ v) (V-cast⇒ v′) = refl

℧-≈ : ∀ {M} → ℧ ≈ˡ M → M ≡ ℧
℧-≈ ≈℧ = refl

≈-℧ : ∀ {M} → M ≈ˡ ℧ → M ≡ ℧
≈-℧ ≈℧ = refl

------------------------------------------------------------------------
-- Frames
------------------------------------------------------------------------

infix 4 _≈ᶠ_

data _≈ᶠ_ : Frame → Frame → Set where
  ≈if□ : ∀ {M M′ N N′} → M ≈ˡ M′ → N ≈ˡ N′ → if□ M N ≈ᶠ if□ M′ N′
  ≈□· : ∀ {M M′} → M ≈ˡ M′ → (□· M) ≈ᶠ (□· M′)
  ≈app□ : ∀ {V V′ v v′} → V ≈ˡ V′ → app□ V v ≈ᶠ app□ V′ v′
  ≈letv□ : ∀ {N N′} → N ≈ˡ N′ → letv□ N ≈ᶠ letv□ N′
  ≈seal□ : ∀ {α} → seal□ α ≈ᶠ seal□ α
  ≈unseal□ : ∀ {α} → unseal□ α ≈ᶠ unseal□ α
  ≈is□ : ∀ {G} → is□ G ≈ᶠ is□ G
  ≈inj□ : ∀ {G} → inj□ G ≈ᶠ inj□ G
  ≈cast□ : ∀ {d p} → cast□ d p ≈ᶠ cast□ d p
  ≈inst□ : ∀ {B ℓ ℓ′ N N′} → N ≈ˡ N′ → inst□ B ℓ N ≈ᶠ inst□ B ℓ′ N′

plug-≈ : ∀ {F F′ M M′} → F ≈ᶠ F′ → M ≈ˡ M′ → plug F M ≈ˡ plug F′ M′
plug-≈ (≈if□ M≈ N≈) L≈ = ≈if L≈ M≈ N≈
plug-≈ (≈□· M≈) L≈ = ≈· L≈ M≈
plug-≈ (≈app□ V≈) M≈ = ≈· V≈ M≈
plug-≈ (≈letv□ N≈) M≈ = ≈letv M≈ N≈
plug-≈ ≈seal□ M≈ = ≈seal M≈
plug-≈ ≈unseal□ M≈ = ≈unseal M≈
plug-≈ ≈is□ M≈ = ≈is M≈
plug-≈ ≈inj□ M≈ = ≈inj M≈
plug-≈ ≈cast□ M≈ = ≈cast M≈
plug-≈ (≈inst□ N≈) M≈ = ≈inst M≈ N≈

-- a term related to a plugged term is itself a plugged term
plug-inv : ∀ F {M T}
  → plug F M ≈ˡ T
  → ∃[ F′ ] ∃[ M′ ] (T ≡ plug F′ M′ × F ≈ᶠ F′ × M ≈ˡ M′)
plug-inv (if□ M N) (≈if L≈ M≈ N≈) = _ , _ , refl , ≈if□ M≈ N≈ , L≈
plug-inv (□· M) (≈· L≈ M≈) = _ , _ , refl , ≈□· M≈ , L≈
plug-inv (app□ V v) (≈· V≈ M≈) =
  app□ _ (value-≈ V≈ v) , _ , refl , ≈app□ V≈ , M≈
plug-inv (letv□ N) (≈letv M≈ N≈) = _ , _ , refl , ≈letv□ N≈ , M≈
plug-inv (seal□ α) (≈seal M≈) = _ , _ , refl , ≈seal□ , M≈
plug-inv (unseal□ α) (≈unseal M≈) = _ , _ , refl , ≈unseal□ , M≈
plug-inv (is□ G) (≈is M≈) = _ , _ , refl , ≈is□ , M≈
plug-inv (inj□ G) (≈inj M≈) = _ , _ , refl , ≈inj□ , M≈
plug-inv (cast□ d p) (≈cast M≈) = _ , _ , refl , ≈cast□ , M≈
plug-inv (inst□ B ℓ N) (≈inst M≈ N≈) = _ , _ , refl , ≈inst□ N≈ , M≈

------------------------------------------------------------------------
-- Stores
------------------------------------------------------------------------

≈ˢ-length : ∀ {Σ Σ′} → Σ ≈ˢ Σ′ → length Σ ≡ length Σ′
≈ˢ-length ≈[] = refl
≈ˢ-length (≈∷ Σ≈) = cong suc (≈ˢ-length Σ≈)

≈ˢ-snoc : ∀ {Σ Σ′ B ℓ ℓ′} → Σ ≈ˢ Σ′
  → (Σ ++ ((B , ℓ) ∷ [])) ≈ˢ (Σ′ ++ ((B , ℓ′) ∷ []))
≈ˢ-snoc ≈[] = ≈∷ ≈[]
≈ˢ-snoc (≈∷ Σ≈) = ≈∷ (≈ˢ-snoc Σ≈)

------------------------------------------------------------------------
-- Lockstep simulation
------------------------------------------------------------------------

-- the result of instantiating related proxies with the same seal
inst-body-≈ : ∀ cs {m n M M′ N N′} → m ≡ n → M ≈ˡ M′ → N ≈ˡ N′
  → letv (stack cs M [ tseal m ]ᵀ) (N [ tseal m ]ᵀ)
    ≈ˡ letv (stack cs M′ [ tseal n ]ᵀ) (N′ [ tseal n ]ᵀ)
inst-body-≈ cs refl M≈ N≈ =
  ≈letv (substᵀ-≈ _ (stack-≈ cs M≈)) (substᵀ-≈ _ N≈)

sim : ∀ {Σ₁ Σ₂ Σ₁′ M₁ M₂ N₁}
  → Σ₁ ≈ˢ Σ₂
  → M₁ ≈ˡ M₂
  → Σ₁ ▷ M₁ —→ Σ₁′ ▷ N₁
  → ∃[ Σ₂′ ] ∃[ N₂ ]
      ((Σ₂ ▷ M₂ —→ Σ₂′ ▷ N₂) × Σ₁′ ≈ˢ Σ₂′ × N₁ ≈ˡ N₂)
sim Σ≈ M≈ (ξξ F refl refl s) with plug-inv F M≈
sim Σ≈ M≈ (ξξ F refl refl s) | F′ , M′ , refl , F≈ , M≈′
  with sim Σ≈ M≈′ s
sim Σ≈ M≈ (ξξ F refl refl s) | F′ , M′ , refl , F≈ , M≈′
  | Σ₂′ , N₂ , s′ , Σ≈′ , N≈ =
  Σ₂′ , plug F′ N₂ , ξ F′ s′ , Σ≈′ , plug-≈ F≈ N≈
sim Σ≈ M≈ (ξξ-℧ F refl) with plug-inv F M≈
sim Σ≈ M≈ (ξξ-℧ F refl) | F′ , M′ , refl , F≈ , ≈℧ =
  _ , ℧ , ξ-℧ F′ , Σ≈ , ≈℧
sim Σ≈ (≈letv V≈ N≈) (β-letv v) =
  _ , _ , β-letv (value-≈ V≈ v) , Σ≈ , []-≈ N≈ V≈
sim Σ≈ (≈unseal (≈seal V≈)) (β-unseal v) =
  _ , _ , β-unseal (value-≈ V≈ v) , Σ≈ , V≈
sim Σ≈ (≈is (≈inj V≈)) (β-is-yes v) =
  _ , _ , β-is-yes (value-≈ V≈ v) , Σ≈ , ≈true
sim Σ≈ (≈is (≈inj V≈)) (β-is-no v G≢H) =
  _ , _ , β-is-no (value-≈ V≈ v) G≢H , Σ≈ , ≈false
sim Σ≈ (≈if ≈true M≈ N≈) β-if-true = _ , _ , β-if-true , Σ≈ , M≈
sim Σ≈ (≈if ≈false M≈ N≈) β-if-false = _ , _ , β-if-false , Σ≈ , N≈
sim Σ≈ (≈· (≈ƛ M≈) V≈) (β-ƛ v) =
  _ , _ , β-ƛ (value-≈ V≈ v) , Σ≈ , []-≈ M≈ V≈
sim Σ≈ (≈· (≈cast V≈) W≈) (β-cast⇒ v w) =
  _ , _ , β-cast⇒ (value-≈ V≈ v) (value-≈ W≈ w) , Σ≈ ,
  ≈cast (≈· V≈ (≈cast W≈))
sim Σ≈ (≈inst (≈Λν M≈) N≈) (β-inst {cs = cs}) =
  _ , _ , β-inst , ≈ˢ-snoc Σ≈ , inst-body-≈ cs (≈ˢ-length Σ≈) M≈ N≈
sim Σ≈ (≈cast V≈) (β-id a v) = _ , _ , β-id a (value-≈ V≈ v) , Σ≈ , V≈
sim Σ≈ (≈cast V≈) (β-tag-up v) =
  _ , _ , β-tag-up (value-≈ V≈ v) , Σ≈ , ≈inj (≈cast V≈)
sim Σ≈ (≈cast (≈inj V≈)) (β-tag-down v) =
  _ , _ , β-tag-down (value-≈ V≈ v) , Σ≈ , ≈cast V≈
sim Σ≈ (≈cast (≈inj V≈)) (β-tag-down-℧ v G≢H) =
  _ , _ , β-tag-down-℧ (value-≈ V≈ v) G≢H , Σ≈ , ≈℧
sim Σ≈ (≈cast (≈Λν M≈)) β-cast∀ = _ , _ , β-cast∀ , Σ≈ , ≈Λν M≈

sim* : ∀ {Σ₁ Σ₂ Σ₁′ M₁ M₂ N₁}
  → Σ₁ ≈ˢ Σ₂
  → M₁ ≈ˡ M₂
  → Σ₁ ▷ M₁ —↠ Σ₁′ ▷ N₁
  → ∃[ Σ₂′ ] ∃[ N₂ ]
      ((Σ₂ ▷ M₂ —↠ Σ₂′ ▷ N₂) × Σ₁′ ≈ˢ Σ₂′ × N₁ ≈ˡ N₂)
sim* Σ≈ M≈ (_ ∎) = _ , _ , (_ ∎) , Σ≈ , M≈
sim* Σ≈ M≈ (_ —→⟨ s ⟩ ss) with sim Σ≈ M≈ s
sim* Σ≈ M≈ (_ —→⟨ s ⟩ ss) | Σ₂ , N₂ , s′ , Σ≈′ , N≈
  with sim* Σ≈′ N≈ ss
sim* Σ≈ M≈ (_ —→⟨ s ⟩ ss) | Σ₂ , N₂ , s′ , Σ≈′ , N≈
  | Σ₂′ , P₂ , ss′ , Σ≈″ , P≈ =
  Σ₂′ , P₂ , (_ —→⟨ s′ ⟩ ss′) , Σ≈″ , P≈

------------------------------------------------------------------------
-- Transfers for closed programs from the empty store
------------------------------------------------------------------------

-- the value proof of a run
value-of : ∀ {M V} → M ⇓ V → Value V
value-of (Σ , ss , v) = v

converge-≈ : ∀ {M₁ M₂ V₁}
  → M₁ ≈ˡ M₂
  → (h₁ : M₁ ⇓ V₁)
  → ∃[ V₂ ] Σ[ h₂ ∈ M₂ ⇓ V₂ ]
      (V₁ ≈ˡ V₂ × observe (value-of h₁) ≡ observe (value-of h₂))
converge-≈ M≈ (Σ , ss , v) with sim* ≈[] M≈ ss
converge-≈ M≈ (Σ , ss , v) | Σ₂ , V₂ , ss′ , Σ≈ , V≈ =
  V₂ , (Σ₂ , ss′ , value-≈ V≈ v) , V≈ , observe-≈ V≈ v (value-≈ V≈ v)

fails-≈ : ∀ {M₁ M₂} → M₁ ≈ˡ M₂ → Fails M₁ → Fails M₂
fails-≈ M≈ (Σ , ss) with sim* ≈[] M≈ ss
fails-≈ M≈ (Σ , ss) | Σ₂ , N₂ , ss′ , Σ≈ , ≈℧ = Σ₂ , ss′

diverges-≈ : ∀ {M₁ M₂} → M₁ ≈ˡ M₂ → Diverges M₁ → Diverges M₂
diverges-≈ M≈ div ss₂ with sim* ≈[] (≈ˡ-sym M≈) ss₂
diverges-≈ M≈ div ss₂ | Σ₁ , N₁ , ss₁ , Σ≈ , N≈ with div ss₁
diverges-≈ M≈ div ss₂ | Σ₁ , N₁ , ss₁ , Σ≈ , N≈ | Σ₁′ , N₁′ , s₁
  with sim (≈ˢ-sym Σ≈) (≈ˡ-sym N≈) s₁
diverges-≈ M≈ div ss₂ | Σ₁ , N₁ , ss₁ , Σ≈ , N≈ | Σ₁′ , N₁′ , s₁
  | Σ′ , N′ , s , Σ≈′ , N≈′ = Σ′ , N′ , s

------------------------------------------------------------------------
-- Main theorems
------------------------------------------------------------------------

label-irrelevance-step : ∀ {Σ₁ Σ₂ Σ₁′ M₁ M₂ N₁}
  → Σ₁ ≈ˢ Σ₂
  → M₁ ≈ˡ M₂
  → Σ₁ ▷ M₁ —→ Σ₁′ ▷ N₁
  → ∃[ Σ₂′ ] ∃[ N₂ ]
      ((Σ₂ ▷ M₂ —→ Σ₂′ ▷ N₂) × Σ₁′ ≈ˢ Σ₂′ × N₁ ≈ˡ N₂)
label-irrelevance-step = sim

label-irrelevance-multi : ∀ {Σ₁ Σ₂ Σ₁′ M₁ M₂ N₁}
  → Σ₁ ≈ˢ Σ₂
  → M₁ ≈ˡ M₂
  → Σ₁ ▷ M₁ —↠ Σ₁′ ▷ N₁
  → ∃[ Σ₂′ ] ∃[ N₂ ]
      ((Σ₂ ▷ M₂ —↠ Σ₂′ ▷ N₂) × Σ₁′ ≈ˢ Σ₂′ × N₁ ≈ˡ N₂)
label-irrelevance-multi = sim*

converge-transfer : ∀ {M₁ M₂ V₁}
  → M₁ ≈ˡ M₂
  → (h₁ : M₁ ⇓ V₁)
  → ∃[ V₂ ] Σ[ h₂ ∈ M₂ ⇓ V₂ ]
      (V₁ ≈ˡ V₂ × observe (value-of h₁) ≡ observe (value-of h₂))
converge-transfer = converge-≈

fails-transfer : ∀ {M₁ M₂} → M₁ ≈ˡ M₂ → Fails M₁ → Fails M₂
fails-transfer = fails-≈

diverges-transfer : ∀ {M₁ M₂} → M₁ ≈ˡ M₂ → Diverges M₁ → Diverges M₂
diverges-transfer = diverges-≈

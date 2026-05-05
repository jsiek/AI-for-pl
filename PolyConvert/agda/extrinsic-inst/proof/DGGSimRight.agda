module proof.DGGSimRight where

-- File Charter:
--   * Right-to-left simulation interface for the PolyConvert DGG proof.
--   * Owns `sim-right` and its multi-step closure.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([]; length)
open import Data.Nat using (ℕ; _≤_; suc; z≤n; s≤s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import Types
open import Imprecision
open import Store
open import Terms
open import TermImprecision
open import Reduction
import proof.Preservation as Preservation
open import proof.DGGCommon
open import proof.DGGMultistep using
  ( multi-trans; appL-↠; appR-↠; tyapp-↠
  ; up-↠; down-↠; reveal-↠; conceal-↠
  )
open import proof.DGGTermImprecision using (wk-left-world-⊑)

≤-step :
  ∀ {m n : ℕ} →
  m ≤ n →
  m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

length-⊆ˢ :
  ∀ {Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  length Σ ≤ length Σ′
length-⊆ˢ done = z≤n
length-⊆ˢ (keep wΣ) = s≤s (length-⊆ˢ wΣ)
length-⊆ˢ (drop wΣ) = ≤-step (length-⊆ˢ wΣ)

storeWf-⊆ˢ-≤ :
  ∀ {Ψ Ψ′ Σ Σ′} →
  StoreWf 0 Ψ Σ →
  StoreWf 0 Ψ′ Σ′ →
  Σ ⊆ˢ Σ′ →
  Ψ ≤ Ψ′
storeWf-⊆ˢ-≤ wfΣ wfΣ′ wΣ
  rewrite sym (storeWf-length wfΣ) | sym (storeWf-length wfΣ′) =
    length-⊆ˢ wΣ

multi-store-growth :
  ∀ {Σ Σ′ : Store} {M N : Term} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ⊆ˢ Σ′
multi-store-growth (M ∎) = ⊆ˢ-refl
multi-store-growth (M —→⟨ M→N ⟩ N↠K) =
  ⊆ˢ-trans (Preservation.store-growth M→N) (multi-store-growth N↠K)

prefix-blames :
  ∀ {Σ Σ′ M N} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Blames Σ′ N →
  Blames Σ M
prefix-blames M↠N (Σᵇ , ℓ , N↠blame) =
  Σᵇ , ℓ , multi-trans M↠N N↠blame

blame-blames :
  ∀ {Σ ℓ} →
  Blames Σ (blame ℓ)
blame-blames {ℓ = ℓ} = _ , ℓ , (blame ℓ ∎)

appL-blames :
  ∀ {Σ L M} →
  Blames Σ L →
  Blames Σ (L · M)
appL-blames {M = M} (Σ′ , ℓ , L↠blame) =
  Σ′ , ℓ ,
  multi-trans (appL-↠ L↠blame)
    ((blame ℓ · M) —→⟨ pure-step blame-·₁ ⟩ blame ℓ ∎)

appR-blames :
  ∀ {Σ V M} →
  Value V →
  Blames Σ M →
  Blames Σ (V · M)
appR-blames {V = V} vV (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (appR-↠ vV M↠blame)
    ((V · blame ℓ) —→⟨ pure-step (blame-·₂ vV) ⟩ blame ℓ ∎)

tyapp-blames :
  ∀ {Σ M B T} →
  Blames Σ M →
  Blames Σ (M ⦂∀ B [ T ])
tyapp-blames {B = B} {T = T} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (tyapp-↠ M↠blame)
    ((blame ℓ ⦂∀ B [ T ])
      —→⟨ pure-step blame-·α ⟩ blame ℓ ∎)

up-blames :
  ∀ {Σ M p} →
  Blames Σ M →
  Blames Σ (M ⇑ p)
up-blames {p = p} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (up-↠ M↠blame)
    ((blame ℓ ⇑ p) —→⟨ pure-step blame-up ⟩ blame ℓ ∎)

down-blames :
  ∀ {Σ M p} →
  Blames Σ M →
  Blames Σ (M ⇓ p)
down-blames {p = p} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (down-↠ M↠blame)
    ((blame ℓ ⇓ p) —→⟨ pure-step blame-down ⟩ blame ℓ ∎)

reveal-blames :
  ∀ {Σ M c} →
  Blames Σ M →
  Blames Σ (M ↑ c)
reveal-blames {c = c} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (reveal-↠ M↠blame)
    ((blame ℓ ↑ c) —→⟨ pure-step blame-reveal ⟩ blame ℓ ∎)

conceal-blames :
  ∀ {Σ M c} →
  Blames Σ M →
  Blames Σ (M ↓ c)
conceal-blames {c = c} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (conceal-↠ M↠blame)
    ((blame ℓ ↓ c) —→⟨ pure-step blame-conceal ⟩ blame ℓ ∎)

SimRightSuccess :
  SealCtx → Store → Term → Store → Term → Ty → Ty → Set
SimRightSuccess Ψˡ Σˡ M Σʳ′ N′ A B =
  ∃[ Ψʳ′ ]
    (StoreWf 0 Ψʳ′ Σʳ′ ×
     ∃[ Ψˡ′ ] ∃[ Σˡ′ ] ∃[ N ]
       (StoreWf 0 Ψˡ′ Σˡ′ ×
        (Σˡ ∣ M —↠ Σˡ′ ∣ N) ×
        TermRel Ψˡ′ Σˡ′ Ψʳ′ Σʳ′ N N′ A B))

SimRightResult :
  SealCtx → Store → Term → Store → Term → Ty → Ty → Set
SimRightResult Ψˡ Σˡ M Σʳ′ N′ A B =
  SimRightSuccess Ψˡ Σˡ M Σʳ′ N′ A B ⊎ Blames Σˡ M

same-right-step-store-wf :
  ∀ {Ψ Σ Σ′ M M′ N′ A B} →
  StoreWf 0 Ψ Σ →
  TermRel Ψ Σ Ψ Σ M M′ A B →
  Σ ∣ M′ —→ Σ′ ∣ N′ →
  ∃[ Ψ′ ] StoreWf 0 Ψ′ Σ′
same-right-step-store-wf wfΣ M⊑M′ red =
  Preservation.step-preserves-store-wf wfΣ (⊑-right-typed M⊑M′) red

sim-right-blameR :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M′ N′ A B ℓ} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  0 ∣ Ψˡ ∣ Σˡ ∣ [] ⊢ M′ ⦂ B →
  Σʳ ∣ M′ —→ Σʳ′ ∣ N′ →
  SimRightResult Ψˡ Σˡ (blame ℓ) Σʳ′ N′ A B
sim-right-blameR {ℓ = ℓ} wfΣˡ wfΣʳ M′⊢ red =
  inj₂ (_ , ℓ , (blame ℓ ∎))

postulate
  sim-right-rest :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    Σʳ ∣ M′ —→ Σʳ′ ∣ N′ →
    SimRightResult Ψˡ Σˡ M Σʳ′ N′ A B

sim-right :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
  Σʳ ∣ M′ —→ Σʳ′ ∣ N′ →
  SimRightResult Ψˡ Σˡ M Σʳ′ N′ A B
sim-right wfΣˡ wfΣʳ (⊑blameL M′⊢ p⊢) red =
  sim-right-blameR wfΣˡ wfΣʳ M′⊢ red
sim-right wfΣˡ wfΣʳ (⊑· (⊑blameL {ℓ = ℓ} L′⊢ p⊢) relM)
    (pure-step blame-·₁) =
  inj₂ (appL-blames (blame-blames {ℓ = ℓ}))
sim-right wfΣˡ wfΣʳ
    (⊑⦂∀ (⊑blameL {ℓ = ℓ} M′⊢ p⊢) wfA wfB wfT pT⊢)
    (pure-step blame-·α) =
  inj₂ (tyapp-blames (blame-blames {ℓ = ℓ}))
sim-right wfΣˡ wfΣʳ
    (⊑⇑ (⊑blameL {ℓ = ℓ} M′⊢ p⊢) p⊢′ p′⊢ pB⊢)
    (pure-step blame-up) =
  inj₂ (up-blames (blame-blames {ℓ = ℓ}))
sim-right wfΣˡ wfΣʳ
    (⊑⇑R (⊑blameL {ℓ = ℓ} M′⊢ p⊢) p′⊢ pB⊢)
    (pure-step blame-up) =
  inj₂ (blame-blames {ℓ = ℓ})
sim-right wfΣˡ wfΣʳ
    (⊑⇓ (⊑blameL {ℓ = ℓ} M′⊢ p⊢) p⊢′ p′⊢ pB⊢)
    (pure-step blame-down) =
  inj₂ (down-blames (blame-blames {ℓ = ℓ}))
sim-right wfΣˡ wfΣʳ
    (⊑⇓R (⊑blameL {ℓ = ℓ} M′⊢ p⊢) p′⊢ pB⊢)
    (pure-step blame-down) =
  inj₂ (blame-blames {ℓ = ℓ})
sim-right wfΣˡ wfΣʳ
    (⊑↑ (⊑blameL {ℓ = ℓ} M′⊢ p⊢) c⊢ c′⊢ pB⊢)
    (pure-step blame-reveal) =
  inj₂ (reveal-blames (blame-blames {ℓ = ℓ}))
sim-right wfΣˡ wfΣʳ
    (⊑↓ (⊑blameL {ℓ = ℓ} M′⊢ p⊢) c⊢ c′⊢ pB⊢)
    (pure-step blame-conceal) =
  inj₂ (conceal-blames (blame-blames {ℓ = ℓ}))
sim-right wfΣˡ wfΣʳ
    (⊑⊕ {op = op} (⊑blameL {ℓ = ℓ} L′⊢ p⊢) relM)
    (pure-step blame-⊕₁) =
  inj₂ (_ , ℓ ,
    ((blame ℓ ⊕[ op ] _)
      —→⟨ pure-step blame-⊕₁ ⟩ blame ℓ ∎))
sim-right {Ψʳ = Ψʳ} {Σʳ = Σʳ} {Σʳ′ = Σʳ′}
    wfΣˡ wfΣʳ rel@(⊑· relL relM) (ξ-·₁ redL)
    with sim-right wfΣˡ wfΣʳ relL redL
... | inj₂ L↠blame = inj₂ (appL-blames L↠blame)
... | inj₁ (Ψʳ′ , wfΣʳ′ , Ψˡ′ , Σˡ′ , N ,
            wfΣˡ′ , L↠N , N⊑N′) =
  inj₁
    (Ψʳ′ , wfΣʳ′ , Ψˡ′ , Σˡ′ , (N · _) , wfΣˡ′ ,
     appL-↠ L↠N ,
     ⊑· N⊑N′
       (wk-left-world-⊑
         {Ψʳ = Ψʳ} {Ψʳ′ = Ψʳ′} {Σʳ = Σʳ} {Σʳ′ = Σʳ′}
         wfΣˡ′ wfΣʳ′
         (storeWf-⊆ˢ-≤ wfΣˡ wfΣˡ′ (multi-store-growth L↠N))
         (multi-store-growth L↠N)
         relM))
sim-right wfΣˡ wfΣʳ rel@(⊑⦂∀ relM wfA wfB wfT pT⊢) (ξ-·α redM)
    with sim-right wfΣˡ wfΣʳ relM redM
... | inj₂ M↠blame = inj₂ (tyapp-blames M↠blame)
... | inj₁ success = sim-right-rest wfΣˡ wfΣʳ rel (ξ-·α redM)
sim-right wfΣˡ wfΣʳ rel@(⊑⇑ relM p⊢ p′⊢ pB⊢) (ξ-⇑ redM)
    with sim-right wfΣˡ wfΣʳ relM redM
... | inj₂ M↠blame = inj₂ (up-blames M↠blame)
... | inj₁ success = sim-right-rest wfΣˡ wfΣʳ rel (ξ-⇑ redM)
sim-right wfΣˡ wfΣʳ rel@(⊑⇓ relM p⊢ p′⊢ pB⊢) (ξ-⇓ redM)
    with sim-right wfΣˡ wfΣʳ relM redM
... | inj₂ M↠blame = inj₂ (down-blames M↠blame)
... | inj₁ success = sim-right-rest wfΣˡ wfΣʳ rel (ξ-⇓ redM)
sim-right wfΣˡ wfΣʳ rel@(⊑↑ relM c⊢ c′⊢ pB⊢) (ξ-↑ redM)
    with sim-right wfΣˡ wfΣʳ relM redM
... | inj₂ M↠blame = inj₂ (reveal-blames M↠blame)
... | inj₁ success = sim-right-rest wfΣˡ wfΣʳ rel (ξ-↑ redM)
sim-right wfΣˡ wfΣʳ rel@(⊑↓ relM c⊢ c′⊢ pB⊢) (ξ-↓ redM)
    with sim-right wfΣˡ wfΣʳ relM redM
... | inj₂ M↠blame = inj₂ (conceal-blames M↠blame)
... | inj₁ success = sim-right-rest wfΣˡ wfΣʳ rel (ξ-↓ redM)
sim-right wfΣˡ wfΣʳ rel red = sim-right-rest wfΣˡ wfΣʳ rel red

sim-right* :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σʳ′ M M′ N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    Σʳ ∣ M′ —↠ Σʳ′ ∣ N′ →
    SimRightResult Ψˡ Σˡ M Σʳ′ N′ A B
sim-right* {M = M} wfΣˡ wfΣʳ M⊑M′ (M′ ∎) =
  inj₁ (_ , wfΣʳ , _ , _ , _ , wfΣˡ , (M ∎) , M⊑M′)
sim-right* wfΣˡ wfΣʳ M⊑M′ (M′ —→⟨ M′→N′ ⟩ N′↠K′)
  with sim-right wfΣˡ wfΣʳ M⊑M′ M′→N′
sim-right* wfΣˡ wfΣʳ M⊑M′ (M′ —→⟨ M′→N′ ⟩ N′↠K′)
  | inj₂ M↠blame = inj₂ M↠blame
sim-right* wfΣˡ wfΣʳ M⊑M′ (M′ —→⟨ M′→N′ ⟩ N′↠K′)
  | inj₁ (Ψʳ′ , wfΣʳ′ , Ψˡ′ , Σˡ′ , N ,
          wfΣˡ′ , M↠N , N⊑N′)
  with sim-right* wfΣˡ′ wfΣʳ′ N⊑N′ N′↠K′
sim-right* wfΣˡ wfΣʳ M⊑M′ (M′ —→⟨ M′→N′ ⟩ N′↠K′)
  | inj₁ (Ψʳ′ , wfΣʳ′ , Ψˡ′ , Σˡ′ , N ,
          wfΣˡ′ , M↠N , N⊑N′)
  | inj₂ N↠blame =
  inj₂ (prefix-blames M↠N N↠blame)
sim-right* wfΣˡ wfΣʳ M⊑M′ (M′ —→⟨ M′→N′ ⟩ N′↠K′)
  | inj₁ (Ψʳ′ , wfΣʳ′ , Ψˡ′ , Σˡ′ , N ,
          wfΣˡ′ , M↠N , N⊑N′)
  | inj₁ (Ψʳ″ , wfΣʳ″ , Ψˡ″ , Σˡ″ , K ,
          wfΣˡ″ , N↠K , K⊑K′) =
  inj₁
    (Ψʳ″ , wfΣʳ″ , Ψˡ″ , Σˡ″ , K , wfΣˡ″ ,
     multi-trans M↠N N↠K , K⊑K′)

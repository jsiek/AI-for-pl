module DynamicGradualGuarantee where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst)

open import Types
open import Contexts
open import GTLC
open import CastCalculus
open import Coercions
open import Compile using (compile; compile-preserves; compile-precision)

open import DynamicGradualGuaranteeCore public

--------------------------------------------------------------------------------
-- Lemmas for Backward Simulation
--------------------------------------------------------------------------------

inj-left-typed
  : ∀{V M′ G A′}
  → []⊑[] ⊢ cast V [ G ! ] ⦂ ★ ⊑ᶜᵀ M′ ⦂ A′
  → [] ⊢ᶜ V ⦂ G
inj-left-typed injV⊑M′
  with ⊑ᶜᵀ-left-typed injV⊑M′
... | ⊢cast V⦂ (⊢! g) = V⦂

sim*-value-right : ∀ {V M′ N A A′}
  → Valueᶜ V
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M′ —↠ᶜ N
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ N ⦂ A′
sim*-value-right vV V⊑M′ M′—↠N
    with sim* V⊑M′ M′—↠N
... | N₁ , V—↠N₁ , N₁⊑N
    with value-—↠ᶜ-refl vV V—↠N₁
... | refl = N₁⊑N

blame-right-catchup : ∀ {M′ A A′}
  → []⊑[] ⊢ blame ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M′ —↠ᶜ blame
blame-right-catchup (⊑blameR M⦂A A⊑A′) = blame ∎ᶜ
blame-right-catchup (⊑castR {M′ = M′} {c′ = c′} blame⊑M′ c′⦂ id≤c′)
    with blame-right-catchup blame⊑M′
... | M′—↠blame =
    cast M′ [ c′ ]
      —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠blame ⟩
    cast blame [ c′ ]
      —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
    blame
    ∎ᶜ

cast-value-catchup : ∀ {V A B c}
  → Valueᶜ V
  → [] ⊢ᶜ V ⦂ A
  → ⊢ c ⦂ A ⇨ B
  → ∃[ N ] ((cast V [ c ] —↠ᶜ N) × ((Valueᶜ N ⊎ (N ≡ blame)) × ([] ⊢ᶜ N ⦂ B)))
cast-value-catchup {V = V} vV V⦂ ⊢idᶜ =
  V
  , (cast V [ idᶜ _ ]
       —→ᶜ⟨ β-id vV ⟩
     V
     ∎ᶜ)
  , (inj₁ vV , V⦂)
cast-value-catchup {V = V} vV V⦂ (⊢! g) =
  cast V [ _ ! ]
  , (cast V [ _ ! ] ∎ᶜ)
  , (inj₁ (V-cast! vV) , ⊢cast V⦂ (⊢! g))
cast-value-catchup {V = V} vV V⦂ (⊢? {G = G} g)
    with canonical-★-inj vV V⦂
... | H , W , vW , refl
    with H ≟Ty G | V⦂
... | yes refl | ⊢cast W⦂ (⊢! gW) =
  W
  , (cast (cast W [ G ! ]) [ G `? ]
       —→ᶜ⟨ β-proj-inj-ok vW ⟩
     W
     ∎ᶜ)
  , (inj₁ vW , W⦂)
... | no H≢G | ⊢cast W⦂ (⊢! gW) =
  blame
  , (cast (cast W [ H ! ]) [ G `? ]
       —→ᶜ⟨ β-proj-inj-bad vW H≢G ⟩
     blame
     ∎ᶜ)
  , (inj₂ refl , ⊢blame)
cast-value-catchup {V = V} vV V⦂ (⊢↦ c⦂ d⦂) =
  cast V [ _ ↦ _ ]
  , (cast V [ _ ↦ _ ] ∎ᶜ)
  , (inj₁ (V-cast↦ vV) , ⊢cast V⦂ (⊢↦ c⦂ d⦂))
cast-value-catchup {V = V} vV V⦂ (⊢⨟ {c = c} {d = d} c⦂ d⦂)
    with cast-value-catchup vV V⦂ c⦂
... | N₁ , V-c—↠N₁ , (inj₂ N₁≡blame , N₁⦂) rewrite N₁≡blame =
  blame
  , (cast V [ c ⨟ d ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) V-c—↠N₁ ⟩
     cast blame [ d ]
       —→ᶜ⟨ ξ-blame (cast□[ d ]) ⟩
     blame
     ∎ᶜ)
  , (inj₂ refl , ⊢blame)
... | N₁ , V-c—↠N₁ , (inj₁ vN₁ , N₁⦂)
    with cast-value-catchup vN₁ N₁⦂ d⦂
... | N₂ , N₁-d—↠N₂ , (N₂vb , N₂⦂) =
  N₂
  , (cast V [ c ⨟ d ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) V-c—↠N₁ ⟩
     cast N₁ [ d ]
       —↠ᶜ⟨ N₁-d—↠N₂ ⟩
     N₂
     ∎ᶜ)
  , (N₂vb , N₂⦂)

value-right-catchup : ∀ {V M′ A A′}
  → Valueᶜ V
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → ∃[ N ] ((M′ —↠ᶜ N)
       × ((Valueᶜ N × ([]⊑[] ⊢ V ⦂ A ⊑ᶜᵀ N ⦂ A′)) ⊎ (N ≡ blame)))
value-right-catchup vV (⊑` _ ()) 
value-right-catchup vV ⊑$ = $ _ , ($ _ ∎ᶜ) , inj₁ (V-$ , ⊑$)
value-right-catchup vV (⊑ƛ A⊑A′ N⊑M) =
  ƛ _ ⇒ _ , (ƛ _ ⇒ _ ∎ᶜ) , inj₁ (V-ƛ , ⊑ƛ A⊑A′ N⊑M)
value-right-catchup () (⊑· L⊑L′ M⊑M′)
value-right-catchup (V-cast! vM) (⊑cast {M = M} {M′ = M′} {c = c} {c′ = c′} M⊑M′ c≤c′ c⦂ c′⦂)
    with value-right-catchup vM M⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , inj₂ refl
... | W′ , M′—↠W′ , inj₁ (vW′ , M⊑W′)
    with cast-value-catchup vW′ (⊑ᶜᵀ-right-typed M⊑W′) c′⦂
... | N , castW′-c′—↠N , (inj₁ vN , N⦂) =
  N
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N ⟩
     N
     ∎ᶜ)
  , inj₁ (vN , sim*-value-right (V-cast! vM) (⊑cast M⊑W′ c≤c′ c⦂ c′⦂) castW′-c′—↠N)
... | N , castW′-c′—↠N , (inj₂ refl , N⦂) =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N ⟩
     blame
     ∎ᶜ)
  , inj₂ refl
value-right-catchup (V-cast! vM) (⊑castL {M = M} {M′ = M′} {c = c} M⊑M′ c⦂ c≤id)
    with value-right-catchup vM M⊑M′
... | W′ , M′—↠W′ , inj₁ (vW′ , M⊑W′) =
  W′
  , M′—↠W′
  , inj₁ (vW′ , sim*-value-right (V-cast! vM) (⊑castL M⊑M′ c⦂ c≤id) M′—↠W′)
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , M′—↠W′
  , inj₂ refl
value-right-catchup (V-cast↦ vM) (⊑cast {M = M} {M′ = M′} {c = c} {c′ = c′} M⊑M′ c≤c′ c⦂ c′⦂)
    with value-right-catchup vM M⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , inj₂ refl
... | W′ , M′—↠W′ , inj₁ (vW′ , M⊑W′)
    with cast-value-catchup vW′ (⊑ᶜᵀ-right-typed M⊑W′) c′⦂
... | N , castW′-c′—↠N , (inj₁ vN , N⦂) =
  N
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N ⟩
     N
     ∎ᶜ)
  , inj₁ (vN , sim*-value-right (V-cast↦ vM) (⊑cast M⊑W′ c≤c′ c⦂ c′⦂) castW′-c′—↠N)
... | N , castW′-c′—↠N , (inj₂ refl , N⦂) =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N ⟩
     blame
     ∎ᶜ)
  , inj₂ refl
value-right-catchup (V-cast↦ vM) (⊑castL {M = M} {M′ = M′} {c = c} M⊑M′ c⦂ c≤id)
    with value-right-catchup vM M⊑M′
... | W′ , M′—↠W′ , inj₁ (vW′ , M⊑W′) =
  W′
  , M′—↠W′
  , inj₁ (vW′ , sim*-value-right (V-cast↦ vM) (⊑castL M⊑M′ c⦂ c≤id) M′—↠W′)
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , M′—↠W′
  , inj₂ refl
value-right-catchup vV (⊑castR {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
    with value-right-catchup vV M⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , inj₂ refl
... | W′ , M′—↠W′ , inj₁ (vW′ , V⊑W′)
    with cast-value-catchup vW′ (⊑ᶜᵀ-right-typed V⊑W′) c′⦂
... | N , castW′-c′—↠N , (inj₁ vN , N⦂) =
  N
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N ⟩
     N
     ∎ᶜ)
  , inj₁ (vN , sim*-value-right vV (⊑castR V⊑W′ c′⦂ id≤c′) castW′-c′—↠N)
... | N , castW′-c′—↠N , (inj₂ refl , N⦂) =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N ⟩
     blame
     ∎ᶜ)
  , inj₂ refl
value-right-catchup vV (⊑blameR M⦂A A⊑A′) = blame , (blame ∎ᶜ) , inj₂ refl

sim-back-beta : ∀ {A A₁ A′ B B′ N F′ M′ V}
  → []⊑[] ⊢ ƛ A ⇒ N ⦂ A₁ ⇒ B ⊑ᶜᵀ F′ ⦂ A′ ⇒ B′
  → Valueᶜ F′
  → []⊑[] ⊢ V ⦂ A₁ ⊑ᶜᵀ M′ ⦂ A′
  → Valueᶜ V
  → ∃[ N′ ] ((F′ · M′ —↠ᶜ N′) × ([]⊑[] ⊢ N [ V ]ᶜ ⦂ B ⊑ᶜᵀ N′ ⦂ B′))
sim-back-beta {M′ = M″} (⊑ƛ {M = N′} A⊑A′ N⊑N′) V-ƛ V⊑M′ vV
    with value-right-catchup vV V⊑M′
... | W′ , M′—↠W′ , inj₁ (vW′ , V⊑W′) =
  N′ [ W′ ]ᶜ
  , ((ƛ _ ⇒ N′) · M″
       —↠ᶜ⟨ ξ* ((ƛ _ ⇒ N′) ·□ V-ƛ) M′—↠W′ ⟩
     (ƛ _ ⇒ N′) · W′
       —→ᶜ⟨ β-ƛ vW′ ⟩
     N′ [ W′ ]ᶜ
     ∎ᶜ)
  , []ᶜ-⊑ A⊑A′ N⊑N′ V⊑W′
... | W′ , M′—↠W′ , inj₂ refl
    with ⊑ᶜᵀ-type-precision (⊑ƛ A⊑A′ N⊑N′)
... | ⊑-⇒ A⊑A′₁ B⊑B′ =
  blame
  , ((ƛ _ ⇒ N′) · M″
       —↠ᶜ⟨ ξ* ((ƛ _ ⇒ N′) ·□ V-ƛ) M′—↠W′ ⟩
     (ƛ _ ⇒ N′) · blame
       —→ᶜ⟨ ξ-blame ((ƛ _ ⇒ N′) ·□ V-ƛ) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ (⊢· (⊢ƛ (⊑ᶜᵀ-left-typed N⊑N′)) (⊑ᶜᵀ-left-typed V⊑M′)) (β-ƛ vV))
      B⊑B′
sim-back-beta {M′ = W′}
  (⊑castR {M′ = F′} {c′ = c ↦ d} λN⊑F′ (⊢↦ c⦂ d⦂) (⊑idL↦ c≤id d≤id))
  (V-cast↦ vF′)
  V⊑W′
  vV
    with value-right-catchup vV V⊑W′
       | ⊑ᶜᵀ-type-precision (⊑castR λN⊑F′ (⊢↦ c⦂ d⦂) (⊑idL↦ c≤id d≤id))
... | W₁′ , W′—↠W₁′ , inj₂ refl | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (cast F′ [ c ↦ d ] · W′
       —↠ᶜ⟨ ξ* (cast F′ [ c ↦ d ] ·□ (V-cast↦ vF′)) W′—↠W₁′ ⟩
     cast F′ [ c ↦ d ] · blame
       —→ᶜ⟨ ξ-blame (cast F′ [ c ↦ d ] ·□ (V-cast↦ vF′)) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ (⊢· (⊑ᶜᵀ-left-typed λN⊑F′) (⊑ᶜᵀ-left-typed V⊑W′)) (β-ƛ vV))
      B⊑B′
... | W₁′ , W′—↠W₁′ , inj₁ (vW₁′ , V⊑W₁′) | _
    with sim-back-beta λN⊑F′ vF′ (⊑castR V⊑W₁′ c⦂ c≤id) vV
... | N₂ , F′W₁′—↠N₂ , N[V]⊑N₂ =
  cast N₂ [ d ]
  , (cast F′ [ c ↦ d ] · W′
       —↠ᶜ⟨ ξ* (cast F′ [ c ↦ d ] ·□ (V-cast↦ vF′)) W′—↠W₁′ ⟩
     cast F′ [ c ↦ d ] · W₁′
       —→ᶜ⟨ β-↦ vF′ vW₁′ ⟩
     cast (F′ · cast W₁′ [ c ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) F′W₁′—↠N₂ ⟩
     cast N₂ [ d ]
     ∎ᶜ)
  , ⊑castR N[V]⊑N₂ d⦂ d≤id

sim-back-beta-cast : ∀ {A A′ B B′ V W F′ M′ c d}
  → []⊑[] ⊢ cast V [ c ↦ d ] ⦂ A ⇒ B ⊑ᶜᵀ F′ ⦂ A′ ⇒ B′
  → Valueᶜ F′
  → []⊑[] ⊢ W ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → Valueᶜ V
  → Valueᶜ W
  → ∃[ N′ ] ((F′ · M′ —↠ᶜ N′)
       × ([]⊑[] ⊢ cast (V · cast W [ c ]) [ d ] ⦂ B ⊑ᶜᵀ N′ ⦂ B′))
sim-back-beta-cast
  {V = V} {W = W} {F′ = cast V′ [ c′ ↦ d′ ]} {M′ = M″} {c = c} {d = d}
  (⊑cast {M = V} {M′ = V′} V⊑V′ (⊑↦ c≤c′ d≤d′) (⊢↦ c⦂ d⦂) (⊢↦ c′⦂ d′⦂))
  (V-cast↦ vV′)
  W⊑M′
  vV
  vW
    with value-right-catchup vW W⊑M′
       | ⊑ᶜᵀ-type-precision
           (⊑cast {M = V} {M′ = V′} V⊑V′ (⊑↦ c≤c′ d≤d′) (⊢↦ c⦂ d⦂) (⊢↦ c′⦂ d′⦂))
... | W′ , M′—↠W′ , inj₂ refl | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (cast V′ [ c′ ↦ d′ ] · M″
       —↠ᶜ⟨ ξ* (cast V′ [ c′ ↦ d′ ] ·□ (V-cast↦ vV′)) M′—↠W′ ⟩
     cast V′ [ c′ ↦ d′ ] · blame
       —→ᶜ⟨ ξ-blame (cast V′ [ c′ ↦ d′ ] ·□ (V-cast↦ vV′)) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ
        (⊢·
          (⊑ᶜᵀ-left-typed
            (⊑cast {M = V} {M′ = V′} V⊑V′ (⊑↦ c≤c′ d≤d′) (⊢↦ c⦂ d⦂) (⊢↦ c′⦂ d′⦂)))
          (⊑ᶜᵀ-left-typed W⊑M′))
        (β-↦ vV vW))
      B⊑B′
... | W′ , M′—↠W′ , inj₁ (vW′ , W⊑W′) | _ =
  cast (V′ · cast W′ [ c′ ]) [ d′ ]
  , (cast V′ [ c′ ↦ d′ ] · M″
       —↠ᶜ⟨ ξ* (cast V′ [ c′ ↦ d′ ] ·□ (V-cast↦ vV′)) M′—↠W′ ⟩
     cast V′ [ c′ ↦ d′ ] · W′
       —→ᶜ⟨ β-↦ vV′ vW′ ⟩
     cast (V′ · cast W′ [ c′ ]) [ d′ ]
     ∎ᶜ)
  , ⊑cast (⊑· V⊑V′ (⊑cast W⊑W′ c≤c′ c⦂ c′⦂)) d≤d′ d⦂ d′⦂
sim-back-beta-cast
  {M′ = M′}
  (⊑castL {M = V} {M′ = F′} V⊑F′ (⊢↦ c⦂ d⦂) (⊑idR↦ c≤id d≤id))
  vF′
  W⊑M′
  vV
  vW =
  F′ · M′
  , ((F′ · M′) ∎ᶜ)
  , ⊑castL (⊑· V⊑F′ (⊑castL W⊑M′ c⦂ c≤id)) d⦂ d≤id
sim-back-beta-cast
  {V = V} {W = W} {M′ = M″} {c = c} {d = d}
  (⊑castR {M = cast V [ c ↦ d ]} {M′ = F′} {c′ = c′ ↦ d′}
    castV⊑F′
    (⊢↦ c′⦂ d′⦂)
    (⊑idL↦ c≤c′ d≤d′))
  (V-cast↦ vF′)
  W⊑M′
  vV
  vW
    with value-right-catchup vW W⊑M′
       | ⊑ᶜᵀ-type-precision
           (⊑castR castV⊑F′ (⊢↦ c′⦂ d′⦂) (⊑idL↦ c≤c′ d≤d′))
... | W′ , M′—↠W′ , inj₂ refl | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (cast F′ [ c′ ↦ d′ ] · M″
       —↠ᶜ⟨ ξ* (cast F′ [ c′ ↦ d′ ] ·□ (V-cast↦ vF′)) M′—↠W′ ⟩
     cast F′ [ c′ ↦ d′ ] · blame
       —→ᶜ⟨ ξ-blame (cast F′ [ c′ ↦ d′ ] ·□ (V-cast↦ vF′)) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ
        (⊢· (⊑ᶜᵀ-left-typed (⊑castR castV⊑F′ (⊢↦ c′⦂ d′⦂) (⊑idL↦ c≤c′ d≤d′)))
            (⊑ᶜᵀ-left-typed W⊑M′))
        (β-↦ vV vW))
      B⊑B′
... | W′ , M′—↠W′ , inj₁ (vW′ , W⊑W′) | _
    with sim-back-beta-cast castV⊑F′ vF′ (⊑castR W⊑W′ c′⦂ c≤c′) vV vW
... | N₂ , F′castW′—↠N₂ , VW⊑N₂ =
  cast N₂ [ d′ ]
  , (cast F′ [ c′ ↦ d′ ] · M″
       —↠ᶜ⟨ ξ* (cast F′ [ c′ ↦ d′ ] ·□ (V-cast↦ vF′)) M′—↠W′ ⟩
     cast F′ [ c′ ↦ d′ ] · W′
       —→ᶜ⟨ β-↦ vF′ vW′ ⟩
     cast (F′ · cast W′ [ c′ ]) [ d′ ]
       —↠ᶜ⟨ ξ* (cast□[ d′ ]) F′castW′—↠N₂ ⟩
     cast N₂ [ d′ ]
     ∎ᶜ)
  , ⊑castR VW⊑N₂ d′⦂ d≤d′

cast-proj-not-value : ∀ {V G H} → Valueᶜ (cast (cast V [ G ! ]) [ H `? ]) → ⊥
cast-proj-not-value ()

blame-—↠ᶜ-value-impossible : ∀ {V} → Valueᶜ V → blame —↠ᶜ V → ⊥
blame-—↠ᶜ-value-impossible vV (blame ∎ᶜ) = value-not-blame vV
blame-—↠ᶜ-value-impossible vV (blame —→ᶜ⟨ blame→N ⟩ N—↠V) =
  ⊥-elim (blame-irreducible blame→N)

blame-—↠ᶜ-refl : ∀ {N} → blame —↠ᶜ N → N ≡ blame
blame-—↠ᶜ-refl (blame ∎ᶜ) = refl
blame-—↠ᶜ-refl (blame —→ᶜ⟨ blame→N ⟩ N—↠N′) =
  ⊥-elim (blame-irreducible blame→N)

cast-!-step-inv : ∀ {V G N}
  → Valueᶜ V
  → cast V [ G ! ] —→ᶜ N
  → ⊥
cast-!-step-inv vV (ξξ {F = cast□[ _ ! ]} refl refl V→N) =
  ⊥-elim (value-irreducible vV V→N)
cast-!-step-inv vV (ξξ-blame {F = cast□[ _ ! ]} refl) =
  ⊥-elim (value-not-blame vV)

cast-proj-ok-step-inv : ∀ {V G N}
  → Valueᶜ V
  → cast (cast V [ G ! ]) [ G `? ] —→ᶜ N
  → N ≡ V
cast-proj-ok-step-inv vV (ξξ {F = cast□[ _ `? ]} refl refl injV→N) =
  ⊥-elim (value-irreducible (V-cast! vV) injV→N)
cast-proj-ok-step-inv vV (β-proj-inj-ok vV′) = refl
cast-proj-ok-step-inv vV (β-proj-inj-bad vV′ G≢G) = ⊥-elim (G≢G refl)
cast-proj-ok-step-inv vV (ξξ-blame {F = cast□[ _ `? ]} ())

cast-proj-bad-step-inv : ∀ {V G H N}
  → Valueᶜ V
  → (G ≡ H → ⊥)
  → cast (cast V [ G ! ]) [ H `? ] —→ᶜ N
  → N ≡ blame
cast-proj-bad-step-inv vV G≢H (ξξ {F = cast□[ _ `? ]} refl refl injV→N) =
  ⊥-elim (value-irreducible (V-cast! vV) injV→N)
cast-proj-bad-step-inv vV G≢H (β-proj-inj-ok vV′) = ⊥-elim (G≢H refl)
cast-proj-bad-step-inv vV G≢H (β-proj-inj-bad vV′ G≢H′) = refl
cast-proj-bad-step-inv vV G≢H (ξξ-blame {F = cast□[ _ `? ]} ())

--------------------------------------------------------------------------------
-- Backward Simulation
--------------------------------------------------------------------------------

sim-back : ∀ {M M′ N A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M —→ᶜ N
  → ∃[ N′ ] ((M′ —↠ᶜ N′) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))

-- Case ξξ

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (ξξ {F = F} refl refl M→N)
    with sim-back M⊑M′ (ξξ {F = F} refl refl M→N)
... | N′ , M′—↠N′ , N⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR N⊑N′ c′⦂ id≤c′

sim-back (⊑castL {M = M} {M′ = M′} {c = c} M⊑M′ c⦂ c≤id)
         (ξξ {F = cast□[ .c ]} refl refl M→N)
    with sim-back M⊑M′ M→N
... | N′ , M′—↠N′ , N⊑N′ =
  N′
  , M′—↠N′
  , ⊑castL N⊑N′ c⦂ c≤id

sim-back (⊑· {L = L} {L′ = L′} {M = M} {M′ = M′} L⊑L′ M⊑M′)
         (ξξ {F = □· .M} refl refl L→N)
    with sim-back L⊑L′ L→N
... | N′ , L′—↠N′ , N⊑N′ =
  N′ · M′
  , ξ* (□· M′) L′—↠N′
  , ⊑· N⊑N′ M⊑M′

sim-back (⊑· {L = V} {L′ = L′} {M = M} {M′ = M′} V⊑L′ M⊑M′)
         (ξξ {F = .V ·□ vV} refl refl M→N)
    with value-right-catchup vV V⊑L′ | sim-back M⊑M′ M→N
... | W′ , L′—↠W′ , inj₁ (vW′ , V⊑W′) | N′ , M′—↠N′ , N⊑N′ =
  W′ · N′
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠W′ ⟩
     W′ · M′
       —↠ᶜ⟨ ξ* (W′ ·□ vW′) M′—↠N′ ⟩
     W′ · N′
     ∎ᶜ)
  , ⊑· V⊑W′ N⊑N′
... | W′ , L′—↠W′ , inj₂ refl | N′ , M′—↠N′ , N⊑N′
    with ⊑ᶜᵀ-type-precision V⊑L′
... | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠W′ ⟩
     blame · M′
       —→ᶜ⟨ ξ-blame (□· M′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (⊢· (⊑ᶜᵀ-left-typed V⊑L′) (⊑ᶜᵀ-left-typed N⊑N′))
      B⊑B′

sim-back (⊑cast {M = M} {M′ = M′} {c = c} {c′ = c′} M⊑M′ c≤c′ c⦂ c′⦂)
         (ξξ {F = cast□[ .c ]} refl refl M→N)
    with sim-back M⊑M′ M→N
... | N′ , M′—↠N′ , N⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑cast N⊑N′ c≤c′ c⦂ c′⦂

-- Case ξξ-blame

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (ξξ-blame {F = F} refl)
    with sim-back M⊑M′ (ξξ-blame {F = F} refl)
... | N′ , M′—↠N′ , blame⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR blame⊑N′ c′⦂ id≤c′

sim-back (⊑castL {M = blame} {M′ = M′} {c = c} blame⊑M′ c⦂ c≤id)
         (ξξ-blame {F = cast□[ .c ]} refl)
    with blame-right-catchup blame⊑M′
... | M′—↠blame =
  blame
  , M′—↠blame
  , ⊑blameR ⊢blame (⊑ᶜᵀ-type-precision (⊑castL blame⊑M′ c⦂ c≤id))

sim-back (⊑· {L = blame} {L′ = L′} {M = M} {M′ = M′} blame⊑L′ M⊑M′)
         (ξξ-blame {F = □· .M} refl)
    with blame-right-catchup blame⊑L′
... | L′—↠blame
    with ⊑ᶜᵀ-type-precision blame⊑L′
... | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠blame ⟩
     blame · M′
       —→ᶜ⟨ ξ-blame (□· M′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR ⊢blame B⊑B′

sim-back (⊑· {L = V} {L′ = L′} {M = blame} {M′ = M′} V⊑L′ blame⊑M′)
         (ξξ-blame {F = .V ·□ vV} refl)
    with value-right-catchup vV V⊑L′ | ⊑ᶜᵀ-type-precision V⊑L′
... | W′ , L′—↠W′ , inj₂ refl | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠W′ ⟩
     blame · M′
       —→ᶜ⟨ ξ-blame (□· M′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR ⊢blame B⊑B′
... | W′ , L′—↠W′ , inj₁ (vW′ , V⊑W′) | ⊑-⇒ A⊑A′ B⊑B′
    with blame-right-catchup blame⊑M′
... | M′—↠blame =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠W′ ⟩
     W′ · M′
       —↠ᶜ⟨ ξ* (W′ ·□ vW′) M′—↠blame ⟩
     W′ · blame
       —→ᶜ⟨ ξ-blame (W′ ·□ vW′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR ⊢blame B⊑B′

sim-back (⊑cast {M = blame} {M′ = M′} {c = c} {c′ = c′} blame⊑M′ c≤c′ c⦂ c′⦂)
         (ξξ-blame {F = cast□[ .c ]} refl)
    with blame-right-catchup blame⊑M′
... | M′—↠blame =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠blame ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR ⊢blame (⊑ᶜᵀ-type-precision (⊑cast blame⊑M′ c≤c′ c⦂ c′⦂))

sim-back (⊑blameR M⦂A A⊑A′) (ξξ-blame x) =
  blame
  , (blame ∎ᶜ)
  , ⊑blameR ⊢blame A⊑A′

sim-back (⊑` x ()) (ξξ-blame x₁)
sim-back ⊑$ (ξξ-blame x) = ⊥-elim (value-irreducible V-$ (ξξ-blame x))
sim-back (⊑ƛ A⊑A′ N⊑M) (ξξ-blame x) = ⊥-elim (value-irreducible V-ƛ (ξξ-blame x))

-- Case β-ƛ

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (β-ƛ vV)
    with sim-back M⊑M′ (β-ƛ vV)
... | N′ , M′—↠N′ , N[V]⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR N[V]⊑N′ c′⦂ id≤c′

sim-back (⊑· {L′ = L′} {M′ = M′} L⊑L′ V⊑M′) (β-ƛ vV)
    with value-right-catchup V-ƛ L⊑L′
       | ⊑ᶜᵀ-type-precision L⊑L′
... | F′ , L′—↠F′ , inj₂ refl | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠F′ ⟩
     blame · M′
       —→ᶜ⟨ ξ-blame (□· M′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ (⊢· (⊑ᶜᵀ-left-typed L⊑L′) (⊑ᶜᵀ-left-typed V⊑M′)) (β-ƛ vV))
      B⊑B′
... | F′ , L′—↠F′ , inj₁ (vF′ , λN⊑F′) | _
    with sim-back-beta λN⊑F′ vF′ V⊑M′ vV
... | N′ , F′M′—↠N′ , N[V]⊑N′ =
  N′
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠F′ ⟩
     F′ · M′
       —↠ᶜ⟨ F′M′—↠N′ ⟩
     N′
     ∎ᶜ)
  , N[V]⊑N′

-- Case β-id

sim-back (⊑cast {M = V} {M′ = M′} {c = c} {c′ = c′} V⊑M′ c≤c′ ⊢idᶜ c′⦂)
         (β-id vV)
    with value-right-catchup vV V⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , sim*-value-right
      vV
      (⊑castR V⊑M′ c′⦂ c≤c′)
      (cast M′ [ c′ ]
         —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
       cast blame [ c′ ]
         —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
       blame
       ∎ᶜ)
... | W′ , M′—↠W′ , inj₁ (vW′ , V⊑W′)
    with cast-value-catchup vW′ (⊑ᶜᵀ-right-typed V⊑W′) c′⦂
... | N′ , castW′-c′—↠N′ , N′vb =
  N′
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N′ ⟩
     N′
     ∎ᶜ)
  , sim*-value-right vV (⊑castR V⊑W′ c′⦂ c≤c′) castW′-c′—↠N′

sim-back (⊑castL {M = V} {M′ = M′} {c = c} V⊑M′ ⊢idᶜ c≤id)
         (β-id vV)
    with value-right-catchup vV V⊑M′
... | N′ , M′—↠N′ , N′vb =
  N′
  , M′—↠N′
  , sim*-value-right vV V⊑M′ M′—↠N′

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (β-id vV)
    with sim-back M⊑M′ (β-id vV)
... | N′ , M′—↠N′ , V⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR V⊑N′ c′⦂ id≤c′

-- Case β-seq

sim-back (⊑castL {M = V} {M′ = M′} {c = c ⨟ d} V⊑M′ (⊢⨟ c⦂ d⦂) (⊑idR⨟ c≤id d≤id))
         (β-seq {V = V} {c = c} {d = d} vV) =
  M′
  , (M′ ∎ᶜ)
  , ⊑castL (⊑castL V⊑M′ c⦂ c≤id) d⦂ d≤id

sim-back (⊑castL {M = V} {M′ = M′} {c = (★ ⇒ ★) `? ⨟ d} V⊑M′ (⊢⨟ (⊢? G-⇒) d⦂) (⊑drop? d≤id))
         (β-seq {V = V} {c = (★ ⇒ ★) `?} {d = d} vV)
    with ⊑ᶜ→⊑ ⊢idᶜ d⦂ d≤id
... | ⊑-⇒ aa aa₁ , bb =
  M′
  , (M′ ∎ᶜ)
  , ⊑castL
      (⊑castL V⊑M′ (⊢? G-⇒) (⊑idR atom-? (⊢? G-⇒) ⊑-★ (⊑-⇒ aa aa₁)))
      d⦂
      d≤id

sim-back (⊑castL {M = V} {M′ = M′} {c = c ⨟ (★ ⇒ ★) !} V⊑M′ (⊢⨟ c⦂ (⊢! G-⇒)) (⊑drop! c≤id))
         (β-seq {V = V} {c = c} {d = (★ ⇒ ★) !} vV)
    with ⊑ᶜ→⊑ ⊢idᶜ c⦂ c≤id
... | aa , ⊑-⇒ bb bb₁ =
  M′
  , (M′ ∎ᶜ)
  , ⊑castL
      (⊑castL V⊑M′ c⦂ c≤id)
      (⊢! G-⇒)
      (⊑idR atom-! (⊢! G-⇒) (⊑-⇒ bb bb₁) ⊑-★)

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (β-seq vV)
    with sim-back M⊑M′ (β-seq vV)
... | N′ , M′—↠N′ , VV-cd⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR VV-cd⊑N′ c′⦂ id≤c′

sim-back
  (⊑cast {M = V} {M′ = M′} {c = c ⨟ d} {c′ = c′} V⊑M′ c≤c′ (⊢⨟ c⦂ d⦂) c′⦂)
  (β-seq vV)
    with value-right-catchup vV V⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ
        (⊢cast (⊑ᶜᵀ-left-typed V⊑M′) (⊢⨟ c⦂ d⦂))
        (β-seq vV))
      (⊑ᶜᵀ-type-precision (⊑cast V⊑M′ c≤c′ (⊢⨟ c⦂ d⦂) c′⦂))
... | W′ , M′—↠W′ , inj₁ (vW′ , V⊑W′)
    with c≤c′ | c⦂ | d⦂ | c′⦂
... | ⊑⨟ c≤c′₁ d≤d′₁ | cwt | dwt | ⊢⨟ c′₁⦂ d′₁⦂ =
  cast cast W′ [ _ ] [ _ ]
  , (cast M′ [ _ ⨟ _ ]
       —↠ᶜ⟨ ξ* (cast□[ _ ⨟ _ ]) M′—↠W′ ⟩
     cast W′ [ _ ⨟ _ ]
       —→ᶜ⟨ β-seq vW′ ⟩
     cast (cast W′ [ _ ]) [ _ ]
     ∎ᶜ)
  , ⊑cast
      (⊑cast V⊑W′ c≤c′₁ cwt c′₁⦂)
      d≤d′₁
      dwt
      d′₁⦂
... | ⊑idR⨟ c≤id d≤id | cwt | dwt | ⊢idᶜ =
  W′
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —→ᶜ⟨ β-id vW′ ⟩
     W′
     ∎ᶜ)
  , ⊑castL (⊑castL V⊑W′ cwt c≤id) dwt d≤id
... | ⊑drop? {c′ = c′₁} d≤c′ | ⊢? G-⇒ | dwt | c′wt =
  let dom-d⊑dom-c′ = proj₁ (⊑ᶜ→⊑ c′wt dwt d≤c′) in
  cast W′ [ c′ ]
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
     ∎ᶜ)
  , ⊑cast
      (⊑castL
        V⊑W′
        (⊢? G-⇒)
        (⊑idR atom-? (⊢? G-⇒) ⊑-★ dom-d⊑dom-c′))
      d≤c′
      dwt
      c′wt
... | ⊑drop! {c′ = c′₁} d≤c′ | cwt | ⊢! G-⇒ | c′wt =
  let cod-d⊑cod-c′ = proj₂ (⊑ᶜ→⊑ c′wt cwt d≤c′) in
  let cod-c⊑cod-c′ = proj₂ (⊑ᶜ→⊑ c′wt (⊢⨟ cwt (⊢! G-⇒)) (⊑drop! d≤c′)) in
  cast W′ [ c′ ]
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
     ∎ᶜ)
  , ⊑castL
      (⊑cast V⊑W′ d≤c′ cwt c′wt)
      (⊢! G-⇒)
      (⊑idR atom-! (⊢! G-⇒) cod-d⊑cod-c′ cod-c⊑cod-c′)

-- Case β-↦

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (β-↦ vV vW)
    with sim-back M⊑M′ (β-↦ vV vW)
... | N′ , M′—↠N′ , V↦W⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR V↦W⊑N′ c′⦂ id≤c′

sim-back (⊑· {L′ = L′} {M′ = M′} L⊑L′ M⊑M′) (β-↦ vV vW)
    with value-right-catchup (V-cast↦ vV) L⊑L′
       | value-right-catchup vW M⊑M′
       | ⊑ᶜᵀ-type-precision L⊑L′
... | F′ , L′—↠F′ , inj₂ refl | _ , _ , _ | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠F′ ⟩
     blame · M′
       —→ᶜ⟨ ξ-blame (□· M′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ (⊢· (⊑ᶜᵀ-left-typed L⊑L′) (⊑ᶜᵀ-left-typed M⊑M′)) (β-↦ vV vW))
      B⊑B′
... | F′ , L′—↠F′ , inj₁ (vF′ , castV⊑F′) | W′ , M′—↠W′ , inj₂ refl | ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠F′ ⟩
     F′ · M′
       —↠ᶜ⟨ ξ* (F′ ·□ vF′) M′—↠W′ ⟩
     F′ · blame
       —→ᶜ⟨ ξ-blame (F′ ·□ vF′) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (preserveᶜ (⊢· (⊑ᶜᵀ-left-typed L⊑L′) (⊑ᶜᵀ-left-typed M⊑M′)) (β-↦ vV vW))
      B⊑B′
... | F′ , L′—↠F′ , inj₁ (vF′ , castV⊑F′) | W′ , M′—↠W′ , inj₁ (vW′ , W⊑W′) | _
    with sim-back-beta-cast castV⊑F′ vF′ W⊑W′ vV vW
... | N′ , F′W′—↠N′ , VW⊑N′ =
  N′
  , (L′ · M′
       —↠ᶜ⟨ ξ* (□· M′) L′—↠F′ ⟩
     F′ · M′
       —↠ᶜ⟨ ξ* (F′ ·□ vF′) M′—↠W′ ⟩
     F′ · W′
       —↠ᶜ⟨ F′W′—↠N′ ⟩
     N′
     ∎ᶜ)
  , VW⊑N′

-- Case β-proj-inj-ok

sim-back (⊑castL {M = cast V [ ℕ ! ]} {M′ = M′} {c = ℕ `?} injV⊑M′ (⊢? G-ℕ) c≤id)
         (β-proj-inj-ok {V = V} {G = ℕ} vV)
    with value-right-catchup (V-cast! vV) injV⊑M′ | ⊑ᶜ→⊑ ⊢idᶜ (⊢? G-ℕ) c≤id
... | N′ , M′—↠N′ , inj₂ refl | ★⊑A′ , ⊑-ℕ =
  blame
  , M′—↠N′
  , ⊑blameR (inj-left-typed injV⊑M′) ⊑-ℕ
... | N′ , M′—↠N′ , inj₁ (vN′ , injV⊑N′) | ★⊑A′ , ⊑-ℕ
    with inj-⊑-not-★ (λ ()) vN′ injV⊑N′
... | g′ , V⊑N′ =
  N′
  , M′—↠N′
  , V⊑N′

sim-back
  (⊑castL {M = cast V [ (★ ⇒ ★) ! ]} {M′ = M′} {c = (★ ⇒ ★) `?} injV⊑M′ (⊢? G-⇒) c≤id)
  (β-proj-inj-ok {V = V} {G = ★ ⇒ ★} vV)
    with value-right-catchup (V-cast! vV) injV⊑M′ | ⊑ᶜ→⊑ ⊢idᶜ (⊢? G-⇒) c≤id
... | N′ , M′—↠N′ , inj₂ refl | ★⊑A′ , ⊑-⇒ A⊑A′ B⊑B′ =
  blame
  , M′—↠N′
  , ⊑blameR (inj-left-typed injV⊑M′) (⊑-⇒ A⊑A′ B⊑B′)
... | N′ , M′—↠N′ , inj₁ (vN′ , injV⊑N′) | ★⊑A′ , ⊑-⇒ A⊑A′ B⊑B′
    with inj-⊑-not-★ (λ ()) vN′ injV⊑N′
... | g′ , V⊑N′ =
  N′
  , M′—↠N′
  , V⊑N′

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (β-proj-inj-ok vV)
    with sim-back M⊑M′ (β-proj-inj-ok vV)
... | N′ , M′—↠N′ , V⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR V⊑N′ c′⦂ id≤c′

sim-back
  (⊑cast {M = cast V [ G ! ]} {M′ = M′} {c = G `?} {c′ = c′}
    injV⊑M′ c≤c′ (⊢? g) c′⦂)
  (β-proj-inj-ok {V = V} {G = G} vV)
    with value-right-catchup (V-cast! vV) injV⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (inj-left-typed injV⊑M′)
      (⊑ᶜᵀ-type-precision (⊑cast injV⊑M′ c≤c′ (⊢? g) c′⦂))
... | W′ , M′—↠W′ , inj₁ (vW′ , injV⊑W′)
    with cast-value-catchup vW′ (⊑ᶜᵀ-right-typed injV⊑W′) c′⦂
... | N′ , castW′-c′—↠N′ , (inj₂ refl , N′⦂) =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N′ ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      (inj-left-typed injV⊑W′)
      (⊑ᶜᵀ-type-precision (⊑cast injV⊑W′ c≤c′ (⊢? g) c′⦂))
... | N′ , castW′-c′—↠N′ , (inj₁ vN′ , N′⦂)
    with sim* (⊑cast injV⊑W′ c≤c′ (⊢? g) c′⦂) castW′-c′—↠N′
... | N₁ , castInj—↠N₁ , N₁⊑N′
    with catchup vN′ N₁⊑N′
... | V₂ , vV₂ , N₁—↠V₂ , V₂⊑N′
    with castInj—↠N₁ ++ᶜ N₁—↠V₂
... | cast (cast V [ G ! ]) [ G `? ] ∎ᶜ = ⊥-elim (cast-proj-not-value vV₂)
... | cast (cast V [ G ! ]) [ G `? ] —→ᶜ⟨ castInj→N₂ ⟩ N₂—↠V₂
    rewrite cast-proj-ok-step-inv vV castInj→N₂
    with value-—↠ᶜ-refl vV N₂—↠V₂
... | refl =
  N′
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N′ ⟩
     N′
     ∎ᶜ)
  , V₂⊑N′

-- Case β-proj-inj-bad

sim-back (⊑castL {M = cast V [ G ! ]} {M′ = M′} {c = ℕ `?} injV⊑M′ (⊢? G-ℕ) c≤id)
         (β-proj-inj-bad {V = V} {G = G} {H = ℕ} vV G≢ℕ)
    with value-right-catchup (V-cast! vV) injV⊑M′ | ⊑ᶜ→⊑ ⊢idᶜ (⊢? G-ℕ) c≤id
... | N′ , M′—↠N′ , inj₂ refl | ★⊑A′ , ℕ⊑A′ =
  blame
  , M′—↠N′
  , ⊑blameR ⊢blame ℕ⊑A′
... | N′ , M′—↠N′ , inj₁ (vN′ , injV⊑N′) | ★⊑A′ , ℕ⊑A′
    rewrite ℕ-⊑-inv ℕ⊑A′
    with inj-⊑-not-★ (λ ()) vN′ injV⊑N′
... | g′ , V⊑N′
    with ground-upper-unique g′ G-ℕ (⊑ᶜᵀ-type-precision V⊑N′) ⊑-ℕ
... | refl = ⊥-elim (G≢ℕ refl)

sim-back
  (⊑castL {M = cast V [ G ! ]} {M′ = M′} {c = (★ ⇒ ★) `?} injV⊑M′ (⊢? G-⇒) c≤id)
  (β-proj-inj-bad {V = V} {G = G} {H = ★ ⇒ ★} vV G≢⇒)
    with value-right-catchup (V-cast! vV) injV⊑M′ | ⊑ᶜ→⊑ ⊢idᶜ (⊢? G-⇒) c≤id
... | N′ , M′—↠N′ , inj₂ refl | ★⊑A′ , ⇒⊑A′ =
  blame
  , M′—↠N′
  , ⊑blameR ⊢blame ⇒⊑A′
... | N′ , M′—↠N′ , inj₁ (vN′ , injV⊑N′) | ★⊑A′ , ⊑-⇒ A⊑A′ B⊑B′
    with inj-⊑-not-★ (λ ()) vN′ injV⊑N′
... | g′ , V⊑N′
    with ground-upper-unique g′ G-⇒ (⊑ᶜᵀ-type-precision V⊑N′) (⊑-⇒ A⊑A′ B⊑B′)
... | refl = ⊥-elim (G≢⇒ refl)

sim-back (⊑castR {M = M} {M′ = M′} {c′ = c′} M⊑M′ c′⦂ id≤c′)
         (β-proj-inj-bad vV G≢H)
    with sim-back M⊑M′ (β-proj-inj-bad vV G≢H)
... | N′ , M′—↠N′ , blame⊑N′ =
  cast N′ [ c′ ]
  , ξ* (cast□[ c′ ]) M′—↠N′
  , ⊑castR blame⊑N′ c′⦂ id≤c′

sim-back
  (⊑cast {M = cast V [ G ! ]} {M′ = M′} {c = H `?} {c′ = c′}
    injV⊑M′ c≤c′ (⊢? gH) c′⦂)
  (β-proj-inj-bad {V = V} {G = G} {H = H} vV G≢H)
    with value-right-catchup (V-cast! vV) injV⊑M′
... | W′ , M′—↠W′ , inj₂ refl =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast blame [ c′ ]
       —→ᶜ⟨ ξ-blame (cast□[ c′ ]) ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      ⊢blame
      (⊑ᶜᵀ-type-precision (⊑cast injV⊑M′ c≤c′ (⊢? gH) c′⦂))
... | W′ , M′—↠W′ , inj₁ (vW′ , injV⊑W′)
    with cast-value-catchup vW′ (⊑ᶜᵀ-right-typed injV⊑W′) c′⦂
... | N′ , castW′-c′—↠N′ , (inj₂ refl , N′⦂) =
  blame
  , (cast M′ [ c′ ]
       —↠ᶜ⟨ ξ* (cast□[ c′ ]) M′—↠W′ ⟩
     cast W′ [ c′ ]
       —↠ᶜ⟨ castW′-c′—↠N′ ⟩
     blame
     ∎ᶜ)
  , ⊑blameR
      ⊢blame
      (⊑ᶜᵀ-type-precision (⊑cast injV⊑W′ c≤c′ (⊢? gH) c′⦂))
... | N′ , castW′-c′—↠N′ , (inj₁ vN′ , N′⦂)
    with sim* (⊑cast injV⊑W′ c≤c′ (⊢? gH) c′⦂) castW′-c′—↠N′
... | N₁ , castInj—↠N₁ , N₁⊑N′
    with catchup vN′ N₁⊑N′
... | V₂ , vV₂ , N₁—↠V₂ , V₂⊑N′
    with castInj—↠N₁ ++ᶜ N₁—↠V₂
... | cast (cast V [ G ! ]) [ H `? ] ∎ᶜ = ⊥-elim (cast-proj-not-value vV₂)
... | cast (cast V [ G ! ]) [ H `? ] —→ᶜ⟨ castInj→N₂ ⟩ N₂—↠V₂
    rewrite cast-proj-bad-step-inv vV G≢H castInj→N₂ =
      ⊥-elim (blame-—↠ᶜ-value-impossible vV₂ N₂—↠V₂)

-- Case ⊑blameR

sim-back (⊑blameR M⦂A A⊑A′) M→N =
  blame
  , (blame ∎ᶜ)
  , ⊑blameR (preserveᶜ M⦂A M→N) A⊑A′

-- Impossible cases

sim-back (⊑` x x₁) N→N = ⊥-elim (var-irreducible N→N)
sim-back ⊑$ N→N = ⊥-elim (value-irreducible V-$ N→N)
sim-back (⊑ƛ A⊑A′ N⊑M) N→N = ⊥-elim (value-irreducible V-ƛ N→N)

--------------------------------------------------------------------------------
-- Multi-step Backward Simulation
--------------------------------------------------------------------------------

sim-back* : ∀ {M M′ N A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M —↠ᶜ N
  → ∃[ N′ ] ∃[ N₂ ] ((M′ —↠ᶜ N′) × (N —↠ᶜ N₂)
        × ([]⊑[] ⊢ N₂ ⦂ A ⊑ᶜᵀ N′ ⦂ A′))
sim-back* {M = M} {M′ = M′} M⊑M′ (M ∎ᶜ) =
  M′
  , M
  , ((M′ ∎ᶜ)
    , (M ∎ᶜ)
    , M⊑M′)
sim-back* {M = L} L⊑L′ (L —→ᶜ⟨ L→M ⟩ M—↠N)
    with sim-back L⊑L′ L→M
... | M′ , L′—↠M′ , M⊑M′
    with sim-back* M⊑M′ M—↠N
... | N′ , N₂ , M′—↠N′ , N—↠N₂ , N₂⊑N′ =
  N′
  , N₂
  , ((L′—↠M′ ++ᶜ M′—↠N′)
    , N—↠N₂
    , N₂⊑N′)

sim-back-converges : ∀ {M M′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → Convergesᶜ M
  → Convergesᶜ M′
sim-back-converges M⊑M′ (W , M—↠W , inj₁ vW)
    with sim-back* M⊑M′ M—↠W
... | N′ , N₂ , M′—↠N′ , W—↠N₂ , N₂⊑N′
    with value-—↠ᶜ-refl vW W—↠N₂
... | refl
    with value-right-catchup vW N₂⊑N′
... | W′ , N′—↠W′ , inj₁ (vW′ , W⊑W′) =
  W′
  , (M′—↠N′ ++ᶜ N′—↠W′)
  , inj₁ vW′
... | W′ , N′—↠W′ , inj₂ refl =
  blame
  , (M′—↠N′ ++ᶜ N′—↠W′)
  , inj₂ refl
sim-back-converges M⊑M′ (W , M—↠W , inj₂ W≡blame)
    rewrite W≡blame
    with sim-back* M⊑M′ M—↠W
... | N′ , N₂ , M′—↠N′ , blame—↠N₂ , N₂⊑N′
    rewrite blame-—↠ᶜ-refl blame—↠N₂
    with blame-right-catchup N₂⊑N′
... | N′—↠blame =
  blame
  , (M′—↠N′ ++ᶜ N′—↠blame)
  , inj₂ refl


gg-diverge-cp
  : ∀ {M M′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → ¬ Convergesᶜ M′
  → ¬ Convergesᶜ M
gg-diverge-cp M⊑M′ ¬M′⇓ M⇓ = ¬M′⇓ (sim-back-converges M⊑M′ M⇓)

gg-diverge
  : ∀ {M M′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → Divergesᶜ M′
  → Divergesᶜ M
gg-diverge M⊑M′ M′⇑ = gg-diverge-cp M⊑M′ M′⇑

_⇓_ : Term → Termᶜ → Set
M ⇓ V = ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (compile wt —↠ᶜ V × Result V))

Diverges : Term → Set
Diverges M = ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (Divergesᶜ (compile wt)))

DivergeOrBlameᶜ : Termᶜ → Set
DivergeOrBlameᶜ M′ = (∀ N′ → M′ —↠ᶜ N′ → N′ ≡ blame ⊎ ∃[ N″ ] N′ —→ᶜ N″)

DivergeOrBlame : Term → Set
DivergeOrBlame M = ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (DivergeOrBlameᶜ (compile wt)))

sum→result : ∀ {V} → Valueᶜ V ⊎ (V ≡ blame) → Result V
sum→result (inj₁ vV) = r-val _ vV
sum→result (inj₂ refl) = r-blame

right-prec-equiv
  : ∀ {V V′ A B C}
  → B ≡ C
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ B
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ C
right-prec-equiv {V = V} {V′ = V′} {A = A} B≡C V⊑V′ =
  subst (λ T → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ T) B≡C V⊑V′

left-prec-equiv
  : ∀ {V V′ A B C}
  → A ≡ B
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ C
  → []⊑[] ⊢ V ⦂ B ⊑ᶜᵀ V′ ⦂ C
left-prec-equiv {V = V} {V′ = V′} {C = C} A≡B V⊑V′ =
  subst (λ T → []⊑[] ⊢ V ⦂ T ⊑ᶜᵀ V′ ⦂ C) A≡B V⊑V′

--------------------------------------------------------------------------------
-- Theorem: Dynamic Gradual Guarantee
--------------------------------------------------------------------------------

dynamic-gradual-guarantee : ∀{M M′}{A A′}
  → M ⊑ᵀ M′
  → [] ⊢ M ⦂ A
  → [] ⊢ M′ ⦂ A′
  → (∀ V′ → Valueᶜ V′ → M′ ⇓ V′ → ∃[ V ] Valueᶜ V × M ⇓ V × []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′)
    × (Diverges M′ → Diverges M)
    × (∀ V → Valueᶜ V → M ⇓ V → (∃[ V′ ] Valueᶜ V′ × M′ ⇓ V′ × []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′) ⊎ (M′ ⇓ blame))
    × (Diverges M → DivergeOrBlame M′)
dynamic-gradual-guarantee {M = M} {M′ = M′} {A = A} {A′ = A′} M≤M′ M⦂A M′⦂A′ =
  (forward , (diverge , (backward , diverge-or-blame)))
  where
  forward : ∀ V′ → Valueᶜ V′ → M′ ⇓ V′
    → ∃[ V ] Valueᶜ V × M ⇓ V × []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  forward V′ vV′ (A″ , M′⦂A″ , M′—↠V′ , r-val .V′ vV′′)
      with gg (compile-precision M≤M′ M⦂A M′⦂A″) M′—↠V′ vV′′
  ... | V , vV , M—↠V , V⊑V′ =
      V , vV , (A , M⦂A , M—↠V , r-val _ vV) , right-prec-equiv (typing-unique M′⦂A″ M′⦂A′) V⊑V′
  forward .blame () (A″ , M′⦂A″ , M′—↠V′ , r-blame)

  diverge : Diverges M′ → Diverges M
  diverge (A″ , M′⦂A″ , M′⇑) =
      A , M⦂A , gg-diverge (compile-precision M≤M′ M⦂A M′⦂A″) M′⇑

  backward : ∀ V → Valueᶜ V → M ⇓ V
    → (∃[ V′ ] Valueᶜ V′ × M′ ⇓ V′ × []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′) ⊎ (M′ ⇓ blame)
  backward V vV (A″ , M⦂A″ , M—↠V , r-val .V vV′)
      with sim-back* (compile-precision M≤M′ M⦂A″ M′⦂A′) M—↠V
  ... | N′ , N₂ , M′—↠N′ , V—↠N₂ , N₂⊑N′
      with value-—↠ᶜ-refl vV V—↠N₂
  ... | refl
      with value-right-catchup vV N₂⊑N′
  ... | W′ , N′—↠W′ , inj₁ (vW′ , V⊑W′) =
      inj₁ (W′ , vW′ , (A′ , M′⦂A′ , (M′—↠N′ ++ᶜ N′—↠W′), r-val _ vW′)
            , left-prec-equiv (typing-unique M⦂A″ M⦂A) V⊑W′)
  ... | W′ , N′—↠W′ , inj₂ refl =
      inj₂ (A′ , M′⦂A′ , (M′—↠N′ ++ᶜ N′—↠W′), r-blame)
  backward .blame () (A″ , M⦂A″ , M—↠V , r-blame)

  diverge-or-blame : Diverges M → DivergeOrBlame M′
  diverge-or-blame (A₀ , wt₀ , divMᶜ) = A′ , M′⦂A′ , dob
    where
    dob : DivergeOrBlameᶜ (compile M′⦂A′)
    dob N′ M′—↠N′
        with progressᶜ (preserveᶜ* (compile-preserves M′⦂A′) M′—↠N′)
    ... | crash N′≡blame = inj₁ N′≡blame
    ... | step {N = N2} N′→N2 = inj₂ (N2 , N′→N2)
    ... | done vN′
        with sim* (compile-precision M≤M′ wt₀ M′⦂A′) M′—↠N′
    ... | N , M—↠N , N⊑N′
        with catchup vN′ N⊑N′
    ... | V , vV , N—↠V , V⊑N′ =
        ⊥-elim (divMᶜ (V , (M—↠N ++ᶜ N—↠V) , inj₁ vV))

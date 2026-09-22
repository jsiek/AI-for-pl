module strong-rep-store.Reduction where

-- File Charter:
--   * §1 `_⊢_-→_∣_`, the fourteen rules — TyBeta, Beta, Peel,
--     TyPeelR-Λ, TyPeelR-⟪⟫, CancelR, Drop$, Drop-true, Drop-false,
--     IdPush and the congruences ξ-·-l, ξ-·-r, ξ-·[], ξ-⟪⟫ (NO ξ-Λ) —
--     with `TyBeta-ℕ`, the multi-step `_⊢_-→*_` and `runCtx`.
--     §2 `value-¬step`.  §3 `det`.
--   * THE STORE CHANGE.  A step returns the change `δ : Alloc` it made
--     to the store, so the contractum lives at `apply δ Δ` and each
--     congruence shifts the redex's siblings by `↑ᴹ[ δ ]`/`↑ᴮ[ δ ]`.
--   * THE CROSSING-SPELLING LAW.  When a rule MOVES a subterm between
--     two name maps, the moved spelling is CARRIED as a named premise
--     and PINNED by `SameConv` or `_⊢_≈_⊣_`, never computed by a fixed
--     renaming.  Five spellings are carried today.
-- Commentary: Commentary.md § Reduction.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ;
         _[_]ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst

------------------------------------------------------------------------
-- 1.  The rules
------------------------------------------------------------------------

-- the small-step relation, indexed by the store change it made
-- Commentary.md § Reduction.agda / `_⊢_-→_∣_` — the store change
infix 2 _⊢_-→_∣_
data _⊢_-→_∣_ : Ctxᵗ → Term → Term → Alloc → Set where

  -- a boundary is BORN: the ∀-elimination mints THE BINDER of the event
  -- Commentary.md § Reduction.agda / TyBeta
  TyBeta : ∀ {Δ B A R N} → Value N
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ (Λ N) ·[ B , A ] -→ N ⟪ inst []
                                      , reveal 0 B ⟫ ∣ new R

  -- beta, FRAME-EXACT: the substitution carries the ƛ's annotation A
  -- Commentary.md § Reduction.agda / Beta
  Beta : ∀ {Δ A N W} → Value W
    → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ∶ A ]ᵐ ∣ none

  -- THE CROSSING: the application is pushed in one layer and the
  -- argument acquires the DUAL, whose spelling `s′` the rule carries.
  -- Commentary.md § Reduction.agda / Peel
  Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ
    → SameConv Δᵈ s′ Δᶜ s
    → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
        -→ (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ∣ none

  -- TYPEEL — the ∀-conversion analogue of Peel, SPLIT IN TWO on the
  -- crossed boundary's interior: `TyPeelR-Λ` instantiates at once,
  -- `TyPeelR-⟪⟫` pushes the type application inward one layer.
  -- Together they are total over canonical `∀`-values.
  -- Commentary.md § Reduction.agda / TyPeelR — why it is two clauses
  --
  -- the interior is `Λ N`: instantiate on the spot.  The frame is
  -- `inst Θ` and the conversion is instantiated at the new name.
  -- Commentary.md § Reduction.agda / TyPeelR-Λ
  TyPeelR-Λ : ∀ {Δ Δᶜ N Θ s B A R Bᵢ Bₑ} → Value N
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ N ⟪ inst Θ , instReveal 0 s ⟫ ∣ new R

  -- the interior is a boundary: push the type application inward one
  -- layer, masking the new ordinary name in the MOVED boundary's own
  -- change list (the snoc `++ (lock 0 0 ∷ [])`).  `s″` and `Bᵢ′` are
  -- the two carried re-spellings.
  -- Commentary.md § Reduction.agda / TyPeelR-⟪⟫
  TyPeelR-⟪⟫ : ∀ {Δ Δᵢ Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ W Θ′ s′ s″ Θ s B A R
                    Bᵢ Bᵢ′ Bₑ} → Value W
    → Δ ⊢ⁱ Θ ⇒ Δᵢ
    → Δ ⊢ᶜ Θ ⇒ Δᶜ
    → Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
    → allocate R Δ ⊢ⁱ inst Θ ⇒ Δᵢ⁺
    → Δᵢ⁺ ⊢ᶜ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])) ⇒ Δ″ᶜ
    → SameConv (underΛ Δ″ᶜ) s″ (underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)) s′
    → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
    → underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ
    → Δ ⊢ᶜ A ~ R
    → Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ]
        -→ ((renᴹᴿ suc W ⟪ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])) , `∀ s″ ⟫)
              ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
             ⟪ inst Θ , instReveal 0 s ⟫ ∣ new R

  -- CANCEL — a conceal directly under the binder it names.  Both
  -- frames are kept (`Θ₁ ++ Θ₂` inside, `rewind Θ₂` outside) and both
  -- conversions are neutralised; `A′` is the carried re-spelling.
  -- Commentary.md § Reduction.agda / CancelR
  CancelR : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y A A′ Aᵢ}
    → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ₁ᶜ ∋ X := Aᵢ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
    → Δᶜ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ++ Θ₂ , mkId A′ ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫ ∣ none

  -- an identity boundary at a base type, over a literal
  Drop$ : ∀ {Δ n Θ A} → Base A
    → Δ ⊢ ($ n) ⟪ Θ , id A ⟫ -→ $ n ∣ none

  Drop-true : ∀ {Δ Θ}
    → Δ ⊢ `true ⟪ Θ , id `𝔹 ⟫ -→ `true ∣ none

  Drop-false : ∀ {Δ Θ}
    → Δ ⊢ `false ⟪ Θ , id `𝔹 ⟫ -→ `false ∣ none

  -- IDPUSH — the transparent-layer rule: the two conversions are
  -- SWAPPED, both frames untouched.  `X′` is the carried re-spelling.
  -- Commentary.md § Reduction.agda / IdPush
  IdPush : ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X X′ Y A} → Value V
    → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
    → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
    → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ
    → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
    → Δᶜ ∋ Y := A
    → Δ ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫
        -→ (V ⟪ Θ₁ ++ Θ₂ , unseal X′ ⟫)
             ⟪ rewind Θ₂ , mkId A ⟫ ∣ none

  -- THE CONGRUENCES pass the store change up and shift the SIBLINGS
  -- by it.  Commentary.md § Reduction.agda / The congruences
  ξ-·-l : ∀ {Δ L L′ M δ} → Δ ⊢ L -→ L′ ∣ δ
    → Δ ⊢ L · M -→ L′ · ↑ᴹ[ δ ] M ∣ δ
  ξ-·-r : ∀ {Δ V M M′ δ} → Value V → Δ ⊢ M -→ M′ ∣ δ
    → Δ ⊢ V · M -→ ↑ᴹ[ δ ] V · M′ ∣ δ
  ξ-·[] : ∀ {Δ L L′ B A δ} → Δ ⊢ L -→ L′ ∣ δ
    → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ] ∣ δ
  -- (NO ξ-Λ: nothing reduces under a type binder — see `⊢Λ`.)
  ξ-⟪⟫  : ∀ {Δ Δᵢ M M′ Θ c δ} → Δ ⊢ⁱ Θ ⇒ Δᵢ
        → Δᵢ ⊢ M -→ M′ ∣ δ
        → Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ ∣ δ

-- Concrete instantiation check: the ordinary argument `ℕ` translates to
-- representation payload `ℕ`, and `inst` produces TyBetaBoundary.
TyBeta-ℕ : empty ⊢ (Λ ($ 7)) ·[ `ℕ , `ℕ ]
  -→ ($ 7) ⟪ TyBetaBoundary , id `ℕ ⟫ ∣ new `ℕ
TyBeta-ℕ = TyBeta V-$ same-ℕ

-- A run needs no store index: each step's change is applied to the
-- context the tail runs at.
infix 2 _⊢_-→*_
data _⊢_-→*_ : Ctxᵗ → Term → Term → Set where
  done   : ∀ {Δ M} → Δ ⊢ M -→* M
  _then_ : ∀ {Δ L M N δ} → Δ ⊢ L -→ M ∣ δ → apply δ Δ ⊢ M -→* N
    → Δ ⊢ L -→* N

infixr 2 _then_

-- The context a run ENDS at: every step's change applied in order.
runCtx : ∀ {Δ M N} → Δ ⊢ M -→* N → Ctxᵗ
runCtx {Δ = Δ} done = Δ
runCtx (_then_ {δ = δ} st sts) = runCtx sts

------------------------------------------------------------------------
-- 2.  VALUES DON'T STEP
------------------------------------------------------------------------

-- the `V-Λ` case is absurd outright: there is no ξ-Λ
value-¬step : ∀ {Δ M M′ δ} → Value M → Δ ⊢ M -→ M′ ∣ δ → ⊥
value-¬step (V-⟪⟫ v I-idv) (Drop$ ())
value-¬step (V-⟪⟫ v ic)    (ξ-⟪⟫ rel st) = value-¬step v st
value-¬step (V-Λ v)        ()

------------------------------------------------------------------------
-- 3.  DETERMINISM
------------------------------------------------------------------------

det : ∀ {Δ Γ M M₁ M₂ A δ₁ δ₂}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
  → M₁ ≡ M₂ × δ₁ ≡ δ₂

-- TyBeta
det _ (TyBeta v same) (TyBeta v′ same′)
  with same-rep-unique same same′
det _ (TyBeta v same) (TyBeta v′ same′) | refl = refl , refl
det _ (TyBeta v same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-Λ v) st)
det _ (ξ-·[] st) (TyBeta v same) =
  ⊥-elim (value-¬step (V-Λ v) st)

-- Beta
det _ (Beta w)     (Beta w′)    = refl , refl
det _ (Beta w)     (ξ-·-l st)   = ⊥-elim (value-¬step V-ƛ st)
det _ (Beta w)     (ξ-·-r v st) = ⊥-elim (value-¬step w st)
det _ (ξ-·-l st)   (Beta w)     = ⊥-elim (value-¬step V-ƛ st)
det _ (ξ-·-r v st) (Beta w)     = ⊥-elim (value-¬step w st)

-- Peel
-- the dual's spelling is pinned by `sameConv-src-unique`
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  with conversion-functional rc rc′ | interior-functional ri ri′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl with conversion-functional rd rd′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl
  with sameConv-src-unique
         (dual-unique (name-fn (bw-exterior mwΘ)) ri rd) sc sc′
det (⊢· (env mwΘ _ _ _ _ _) _)
    (Peel v w rc ri rd sc) (Peel v′ w′ rc′ ri′ rd′ sc′)
  | refl | refl | refl | refl = refl , refl
det _ (Peel v w rc ri rd sc) (ξ-·-l st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (Peel v w rc ri rd sc) (ξ-·-r u′ st) =
  ⊥-elim (value-¬step w st)
det _ (ξ-·-l st) (Peel v w rc ri rd sc) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-fun) st)
det _ (ξ-·-r u′ st) (Peel v w rc ri rd sc) =
  ⊥-elim (value-¬step w st)

-- TyPeelR — the two clauses' patterns are DISJOINT, and the Λ clause is
-- determined by the redex outright.
det _ (TyPeelR-Λ v rel ⊢s same)
    (TyPeelR-Λ v′ rel′ ⊢s′ same′)
  with same-rep-unique same same′
det _ (TyPeelR-Λ v rel ⊢s same)
    (TyPeelR-Λ v′ rel′ ⊢s′ same′) | refl = refl , refl
det _ (TyPeelR-Λ v rel ⊢s same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)
det _ (ξ-·[] st) (TyPeelR-Λ v rel ⊢s same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-Λ v) I-all) st)

-- the wrapper clause: all five carried readings are identified first
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
  with interior-functional ri ri′ | conversion-functional rc rc′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl
  with interior-functional ri (bw-interior mwΘ)
     | conversion-functional rc (bw-conversion mwΘ)
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl
  with conversion-functional r′ r′′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl
  with conv-src-unique
         (unique-underΛ {Γ = Δᶜ} (name-fn (bw-conversion-wf mwΘ))) ⊢s ⊢s′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (unique-underΛ {Γ = Δᵢ} (name-fn (bw-interior-wf mwΘ))) sm sm′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl
  with same-rep-unique same same′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
      v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl
  with interior-functional ri⁺ ri⁺′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δ″ᶜ = Δ″ᶜ} v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with conversion-functional r″ r″′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ {Δ″ᶜ = Δ″ᶜ} v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with sameConv-src-unique
         (unique-underΛ {Γ = Δ″ᶜ}
           (conversion-unique
             (interior-unique (unique-shift (name-fn (bw-exterior mwΘ)))
                              ri⁺) r″))
         sc sc′
det (⊢·[] (env mwΘ _ _ _ _ _) _)
    (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same)
    (TyPeelR-⟪⟫ v′ ri′ rc′ r′′ ri⁺′ r″′ sc′ ⊢s′ sm′ same′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl
    | refl = refl , refl
det _ (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same) (ξ-·[] st) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)
det _ (ξ-·[] st) (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm same) =
  ⊥-elim (value-¬step (V-⟪⟫ (V-⟪⟫ v I-all) I-all) st)

-- CancelR — both looked-up types and the re-spelling are functional
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
  with interior-functional ri ri′ | conversion-functional r₂ r₂′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl
  with interior-functional ri (bw-interior mwΘ₂)
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl
  with conversion-functional r₁ (bw-conversion mwΘ₁)
     | conversion-functional r₂ (bw-conversion mwΘ₂)
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl
  with ∋:=-det (name-fn (bw-conversion-wf mwΘ₁)) d₁ d₁′
     | ∋:=-det (name-fn (bw-conversion-wf mwΘ₂)) d₂ d₂′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sm sm′
det (env mwΘ₂ (env mwΘ₁ _ _ _ _ _) _ _ _ _)
    (CancelR {Θ₂ = Θ₂} v ri r₁ d₁ r⋉ sm r₂ d₂)
    (CancelR v′ ri′ r₁′ d₁′ r⋉′ sm′ r₂′ d₂′)
    | refl | refl | refl | refl | refl | refl | refl | refl | refl | refl =
  refl , refl
det _ (CancelR v ri r₁ d₁ r⋉ sm r₂ d₂) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)
det _ (ξ-⟪⟫ frame st) (CancelR v ri r₁ d₁ r⋉ sm r₂ d₂) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-seal) st)

-- Drop$
det _ (Drop$ b)    (Drop$ b′)   = refl , refl
det _ (Drop$ b) (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-$ st)
det _ (ξ-⟪⟫ frame st) (Drop$ b) = ⊥-elim (value-¬step V-$ st)

-- Drop-true / Drop-false
det _ Drop-true Drop-true = refl , refl
det _ Drop-true (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-true st)
det _ (ξ-⟪⟫ frame st) Drop-true = ⊥-elim (value-¬step V-true st)
det _ Drop-false Drop-false = refl , refl
det _ Drop-false (ξ-⟪⟫ frame st) = ⊥-elim (value-¬step V-false st)
det _ (ξ-⟪⟫ frame st) Drop-false = ⊥-elim (value-¬step V-false st)

-- IdPush — likewise determined by the lookup.
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
  with interior-functional ri ri′ | conversion-functional rel rel′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′) | refl | refl
  with conversion-functional r₁ r₁′ | conversion-functional r⋉ r⋉′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl
  with conversion-functional rel (bw-conversion mwΘ₂)
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl | refl
  with sameTy-src-unique
         (conversion-unique (name-fn (bw-exterior mwΘ₂)) r⋉) sm sm′
     | ∋:=-det (name-fn (bw-conversion-wf mwΘ₂)) d d′
det (env mwΘ₂ _ _ _ _ _)
    (IdPush {Θ₂ = Θ₂} v ri r₁ r⋉ sm rel d)
    (IdPush v′ ri′ r₁′ r⋉′ sm′ rel′ d′)
    | refl | refl | refl | refl | refl | refl | refl = refl , refl
det _ (IdPush v ri r₁ r⋉ sm rel d) (ξ-⟪⟫ frame st) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)
det _ (ξ-⟪⟫ frame st) (IdPush v ri r₁ r⋉ sm rel d) =
  ⊥-elim (value-¬step (V-⟪⟫ v I-idv) st)

-- the congruences: the sibling shift is a function of the store change
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) with det ⊢L st st′
det (⊢· ⊢L ⊢M) (ξ-·-l st) (ξ-·-l st′) | refl , refl = refl , refl
det _ (ξ-·-l st) (ξ-·-r v st′) = ⊥-elim (value-¬step v st)
det _ (ξ-·-r v st) (ξ-·-l st′) = ⊥-elim (value-¬step v st′)
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) with det ⊢M st st′
det (⊢· ⊢L ⊢M) (ξ-·-r v st) (ξ-·-r u st′) | refl , refl = refl , refl
det (⊢·[] ⊢L ⊢A) (ξ-·[] st) (ξ-·[] st′) with det ⊢L st st′
det (⊢·[] ⊢L ⊢A) (ξ-·[] st) (ξ-·[] st′) | refl , refl = refl , refl
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  with interior-functional rel rel′
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl with interior-functional rel (bw-interior mwΘ)
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl with det ⊢M st st′
det (env mwΘ ⊢M ⊢c smi sme wf) (ξ-⟪⟫ rel st) (ξ-⟪⟫ rel′ st′)
  | refl | refl | refl , refl = refl , refl

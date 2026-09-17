module strong.notes.RepresentationReductionExamples where

-- Executable reduction checks for the representation-variable experiment.
-- Every displayed state has an explicit typing derivation; every edge is a
-- derivation of strong.Reduction._⊢_-→_.
--
--   polymorphic identity       6 steps   value 7     : ℕ
--   polymorphic Boolean use    9 steps   value true  : 𝔹
--   polymorphic constant 3    11 steps   value 3     : ℕ
--   later-bound identity       5 steps   value at ∀Y. Y ⇒ Y

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- Shared ℕ-instantiation frames
------------------------------------------------------------------------

Δℕ Δℕ-lock : Ctxᵗ
Δℕ = TyBetaCtx
Δℕ-lock = (bindR `ℕ ∷ []) ∣ []

wf-Δℕ-lock : WfCtx Δℕ-lock
wf-Δℕ-lock = wf-ctx (wf-bindR wfᴿ-ℕ wf-reps[]) (λ ()) unique[]

Θℕ-dual Θℕ-cancel Θℕ-rewind : CtxMorph
Θℕ-dual = dualMorph TyBetaMorph
Θℕ-cancel = Θℕ-dual ⋉ TyBetaMorph
Θℕ-rewind = rewind TyBetaMorph

Θℕ-dual-mw : MorphWf Δℕ Θℕ-dual Δℕ-lock Δℕ
Θℕ-dual-mw =
  mw TyBetaCtx-wf binds[]
     (interior
       (changes∷ changes[]
         (step-lock (_ , here) del-here fresh[])))
     (conversion (conv-lock (_ , here) conv[]))
     wf-Δℕ-lock TyBetaCtx-wf

Θℕ-cancel-mw : MorphWf Δℕ-lock Θℕ-cancel Δℕ-lock Δℕ
Θℕ-cancel-mw =
  mw wf-Δℕ-lock binds[]
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , here) fresh[] ins-here))
         (step-lock (_ , here) del-here fresh[])))
     (conversion
       (conv-lock (_ , here)
         (conv-unlock (_ , here) conv[] fresh[] ins-here)))
     wf-Δℕ-lock TyBetaCtx-wf

Θℕ-rewind-mw : MorphWf empty Θℕ-rewind Δℕ-lock Δℕ
Θℕ-rewind-mw =
  mw wf-empty (binds∷ wfᴿ-ℕ binds[])
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , here) fresh[] ins-here))
         (step-lock (_ , here) del-here fresh[])))
     (conversion
       (conv-lock (_ , here)
         (conv-unlock (_ , here) conv[] fresh[] ins-here)))
     wf-Δℕ-lock TyBetaCtx-wf

same-ℕℕ : ∀ {Γ Γ′} → SameTy Γ `ℕ Γ′ `ℕ
same-ℕℕ = `ℕ , same-ℕ , same-ℕ

same-ℕ⇒ℕ : ∀ {Γ Γ′}
  → SameTy Γ (`ℕ ⇒ `ℕ) Γ′ (`ℕ ⇒ `ℕ)
same-ℕ⇒ℕ = `ℕ ⇒ `ℕ , same-⇒ same-ℕ same-ℕ
                         , same-⇒ same-ℕ same-ℕ

sameExt-ℕ₀ : ∀ {Γ Γ′} → SameTyExt 0 Γ `ℕ Γ′ `ℕ
sameExt-ℕ₀ = `ℕ , same-ℕ , same-ℕ

sameExt-ℕ₁ : ∀ {Γ Γ′} → SameTyExt 1 Γ `ℕ Γ′ `ℕ
sameExt-ℕ₁ = `ℕ , same-ℕ , same-ℕ

sameExt-ℕ⇒ℕ₁ : ∀ {Γ Γ′}
  → SameTyExt 1 Γ (`ℕ ⇒ `ℕ) Γ′ (`ℕ ⇒ `ℕ)
sameExt-ℕ⇒ℕ₁ = `ℕ ⇒ `ℕ , same-⇒ same-ℕ same-ℕ
                            , same-⇒ same-ℕ same-ℕ

same-Xℕ : SameTy Δℕ (` 0) Δℕ (` 0)
same-Xℕ = ` 0 , same-var here , same-var here

------------------------------------------------------------------------
-- 1. (ΛX. λx:X. x) [ℕ] · 7
------------------------------------------------------------------------

P₁₀ P₁₁ P₁₂ P₁₃ P₁₄ P₁₅ P₁₆ : Term
P₁₀ = (Λ (ƛ ` 0 ∙ ` 0)) ·[ ` 0 ⇒ ` 0 , `ℕ ] · $ 7
P₁₁ = ((ƛ ` 0 ∙ ` 0)
        ⟪ TyBetaMorph , seal 0 ↦ unseal 0 ⟫) · $ 7
P₁₂ = ((ƛ ` 0 ∙ ` 0) · (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
        ⟪ TyBetaMorph , unseal 0 ⟫
P₁₃ = (($ 7) ⟪ Θℕ-dual , seal 0 ⟫)
        ⟪ TyBetaMorph , unseal 0 ⟫
P₁₄ = (($ 7) ⟪ Θℕ-cancel , id `ℕ ⟫)
        ⟪ Θℕ-rewind , id `ℕ ⟫
P₁₅ = ($ 7) ⟪ Θℕ-rewind , id `ℕ ⟫
P₁₆ = $ 7

P₁₀-⊢ : empty ∣ [] ⊢ P₁₀ ⦂ `ℕ
P₁₀-⊢ =
  ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var (_ , here)) (⊢` here))) wf-ℕ) ⊢$

P₁₁-⊢ : empty ∣ [] ⊢ P₁₁ ⦂ `ℕ
P₁₁-⊢ = ⊢· wrapped-id ⊢$
  where
  wrapped-id : empty ∣ [] ⊢
    (ƛ ` 0 ∙ ` 0) ⟪ TyBetaMorph , seal 0 ↦ unseal 0 ⟫
      ⦂ (`ℕ ⇒ `ℕ)
  wrapped-id =
    env TyBeta-mw
        (⊢ƛ (wf-var (_ , here)) (⊢` here))
        (conv-fun (conv-seal β-lookup) (conv-unseal β-lookup))
        (` 0 ⇒ ` 0 , same-⇒ (same-var here) (same-var here)
                    , same-⇒ (same-var here) (same-var here))
        (sameExt-ℕ⇒ℕ₁ {Γ = empty} {Γ′ = Δℕ})
        (wf-⇒ wf-ℕ wf-ℕ)

sealed-seven-⊢ : ∀ {Γ}
  → Δℕ ∣ Γ ⊢ ($ 7) ⟪ Θℕ-dual , seal 0 ⟫ ⦂ ` 0
sealed-seven-⊢ =
  env Θℕ-dual-mw ⊢$ (conv-seal β-lookup)
      (same-ℕℕ {Γ = Δℕ-lock} {Γ′ = Δℕ})
      (` 0 , same-var here , same-var here)
      (wf-var (_ , here))

P₁₂-⊢ : empty ∣ [] ⊢ P₁₂ ⦂ `ℕ
P₁₂-⊢ =
  env TyBeta-mw
      (⊢· (⊢ƛ (wf-var (_ , here)) (⊢` here)) sealed-seven-⊢)
      (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

P₁₃-⊢ : empty ∣ [] ⊢ P₁₃ ⦂ `ℕ
P₁₃-⊢ =
  env TyBeta-mw sealed-seven-⊢ (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

cancel-seven-⊢ : Δℕ-lock ∣ []
  ⊢ ($ 7) ⟪ Θℕ-cancel , id `ℕ ⟫ ⦂ `ℕ
cancel-seven-⊢ =
  env Θℕ-cancel-mw ⊢$ (conv-id base-ℕ)
      (same-ℕℕ {Γ = Δℕ-lock} {Γ′ = Δℕ})
      (sameExt-ℕ₀ {Γ = Δℕ-lock} {Γ′ = Δℕ}) wf-ℕ

P₁₄-⊢ : empty ∣ [] ⊢ P₁₄ ⦂ `ℕ
P₁₄-⊢ =
  env Θℕ-rewind-mw cancel-seven-⊢ (conv-id base-ℕ)
      (same-ℕℕ {Γ = Δℕ-lock} {Γ′ = Δℕ})
      (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

P₁₅-⊢ : empty ∣ [] ⊢ P₁₅ ⦂ `ℕ
P₁₅-⊢ =
  env Θℕ-rewind-mw ⊢$ (conv-id base-ℕ)
      (same-ℕℕ {Γ = Δℕ-lock} {Γ′ = Δℕ})
      (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

P₁₆-⊢ : empty ∣ [] ⊢ P₁₆ ⦂ `ℕ
P₁₆-⊢ = ⊢$

P₁-step₀ : empty ⊢ P₁₀ -→ P₁₁
P₁-step₀ = ξ-·-l (TyBeta V-ƛ same-ℕ)

P₁-step₁ : empty ⊢ P₁₁ -→ P₁₂
P₁-step₁ = Peel V-ƛ V-$

P₁-step₂ : empty ⊢ P₁₂ -→ P₁₃
P₁-step₂ =
  ξ-⟪⟫ TyBeta-interior (Beta (V-⟪⟫ V-$ I-seal))

P₁-step₃ : empty ⊢ P₁₃ -→ P₁₄
P₁-step₃ =
  CancelR V-$ TyBeta-conversion (name-fn TyBetaCtx-wf) β-lookup

P₁-step₄ : empty ⊢ P₁₄ -→ P₁₅
P₁-step₄ = ξ-⟪⟫ (mw-interior Θℕ-rewind-mw) (Drop$ base-ℕ)

P₁-step₅ : empty ⊢ P₁₅ -→ P₁₆
P₁-step₅ = Drop$ base-ℕ

P₁-value : Value P₁₆
P₁-value = V-$

P₁-run : empty ⊢ P₁₀ -→* P₁₆
P₁-run =
  P₁-step₀ then
  P₁-step₁ then
  P₁-step₂ then
  P₁-step₃ then
  P₁-step₄ then
  P₁-step₅ then
  done

------------------------------------------------------------------------
-- Shared polymorphic constant used by examples 2 and 3
------------------------------------------------------------------------

const3 : Term
const3 = Λ (ƛ ` 0 ∙ $ 3)

const3Ty : Ty
const3Ty = `∀ (` 0 ⇒ `ℕ)

const3-⊢ : ∀ {Γ} → Δℕ-lock ∣ Γ ⊢ const3 ⦂ const3Ty
const3-⊢ = ⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢$)

lookup-X-underΛℕ : underΛ Δℕ ∋ 1 := `ℕ
lookup-X-underΛℕ =
  1 , `ℕ , there here , r-there-abst r-here , same-ℕ

stℕ : Conv
stℕ = id (` 0) ↦ seal 1

stℕ-⊢ : underΛ Δℕ ⊢ stℕ ∶ (` 0 ⇒ `ℕ) ⇝ (` 0 ⇒ ` 1)
stℕ-⊢ =
  conv-fun (conv-idv (_ , here)) (conv-seal lookup-X-underΛℕ)

unique-underΛΔℕ : Unique (names (underΛ Δℕ))
unique-underΛΔℕ =
  unique-underΛ {Γ = Δℕ} (name-fn TyBetaCtx-wf)

JT : Ty
JT = `∀ (` 0 ⇒ ` 1)

JT-wf : Δℕ ⊢ᵗ JT
JT-wf =
  wf-∀ (wf-⇒ (wf-var (_ , here)) (wf-var (_ , there here)))

const3-cross-⊢ : ∀ {Γ}
  → Δℕ ∣ Γ ⊢ const3 ⟪ Θℕ-dual , `∀ stℕ ⟫ ⦂ JT
const3-cross-⊢ =
  env Θℕ-dual-mw const3-⊢ (conv-all stℕ-⊢)
      (`∀ (` 0 ⇒ `ℕ)
        , same-∀ (same-⇒ (same-var here) same-ℕ)
        , same-∀ (same-⇒ (same-var here) same-ℕ))
      (`∀ (` 0 ⇒ ` 1)
        , same-∀ (same-⇒ (same-var here) (same-var (there here)))
        , same-∀ (same-⇒ (same-var here) (same-var (there here))))
      JT-wf

------------------------------------------------------------------------
-- 3. ((ΛX. λx:X. λf:(∀Y. Y⇒X). f[X]·x) [ℕ]) · 7 · const3
------------------------------------------------------------------------

JB : Ty
JB = ` 0 ⇒ (JT ⇒ ` 0)

Jbody Jfun : Term
Jbody = ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · ` 1)
Jfun = Λ (ƛ ` 0 ∙ Jbody)

Jfun-⊢ : empty ∣ [] ⊢ Jfun ⦂ `∀ JB
Jfun-⊢ =
  ⊢Λ
    (⊢ƛ (wf-var (_ , here))
      (⊢ƛ
        (wf-∀
          (wf-⇒ (wf-var (_ , here))
                (wf-var (_ , there here))))
        (⊢· (⊢·[] (⊢` here) (wf-var (_ , here)))
            (⊢` (there here)))))

J₀ : Term
J₀ = ((Jfun ·[ JB , `ℕ ]) · $ 7) · const3

J₀-⊢ : empty ∣ [] ⊢ J₀ ⦂ `ℕ
J₀-⊢ =
  ⊢· (⊢· (⊢·[] Jfun-⊢ wf-ℕ) ⊢$)
      (⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢$))

Jmint : Conv
Jmint = seal 0 ↦ ((`∀ stℕ) ↦ unseal 0)

J₁ J₂ J₃ J₄ J₅ J₆head J₆ : Term
J₁ = (((ƛ ` 0 ∙ Jbody) ⟪ TyBetaMorph , Jmint ⟫) · $ 7) · const3
J₂ = (((ƛ ` 0 ∙ Jbody) ·
        (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
        ⟪ TyBetaMorph , (`∀ stℕ) ↦ unseal 0 ⟫) · const3
J₃ = ((ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) ·
                  (($ 7) ⟪ Θℕ-dual , seal 0 ⟫)))
        ⟪ TyBetaMorph , (`∀ stℕ) ↦ unseal 0 ⟫) · const3
J₄ = ((ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) ·
                  (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))) ·
        (const3 ⟪ Θℕ-dual , `∀ stℕ ⟫))
        ⟪ TyBetaMorph , unseal 0 ⟫
J₅ = (((const3 ⟪ Θℕ-dual , `∀ stℕ ⟫)
          ·[ ` 0 ⇒ ` 1 , ` 0 ]) ·
        (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
        ⟪ TyBetaMorph , unseal 0 ⟫
J₆head = (ƛ ` 0 ∙ $ 3)
  ⟪ instantiate (` 0) Θℕ-dual , instReveal 0 stℕ ⟫
J₆ = (J₆head · (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
       ⟪ TyBetaMorph , unseal 0 ⟫

J-step₀ : empty ⊢ J₀ -→ J₁
J-step₀ = ξ-·-l (ξ-·-l (TyBeta V-ƛ same-ℕ))

J-step₁ : empty ⊢ J₁ -→ J₂
J-step₁ = ξ-·-l (Peel V-ƛ V-$)

J-step₂ : empty ⊢ J₂ -→ J₃
J-step₂ =
  ξ-·-l
    (ξ-⟪⟫ TyBeta-interior (Beta (V-⟪⟫ V-$ I-seal)))

J-step₃ : empty ⊢ J₃ -→ J₄
J-step₃ = Peel V-ƛ (V-Λ V-ƛ)

J-step₄ : empty ⊢ J₄ -→ J₅
J-step₄ =
  ξ-⟪⟫ TyBeta-interior
    (Beta (V-⟪⟫ (V-Λ V-ƛ) I-all))

J-step₅ : empty ⊢ J₅ -→ J₆
J-step₅ =
  ξ-⟪⟫ TyBeta-interior
    (ξ-·-l
      (TyPeelR-Λ V-ƛ
        (mw-conversion Θℕ-dual-mw)
        unique-underΛΔℕ
        stℕ-⊢
        (same-var here)))

JTarget : Ty
JTarget = `ℕ ⇒ (const3Ty ⇒ `ℕ)

Jmint-⊢ : Δℕ ⊢ Jmint ∶ JB ⇝ JTarget
Jmint-⊢ =
  conv-fun (conv-seal β-lookup)
    (conv-fun (conv-all stℕ-⊢) (conv-unseal β-lookup))

Jbody-Δℕ-⊢ : Δℕ ∣ (` 0 ∷ []) ⊢ Jbody ⦂ (JT ⇒ ` 0)
Jbody-Δℕ-⊢ =
  ⊢ƛ JT-wf
    (⊢· (⊢·[] (⊢` here) (wf-var (_ , here)))
        (⊢` (there here)))

same-JT : SameTy Δℕ JT Δℕ JT
same-JT =
  `∀ (` 0 ⇒ ` 1)
    , same-∀ (same-⇒ (same-var here) (same-var (there here)))
    , same-∀ (same-⇒ (same-var here) (same-var (there here)))

same-JB : SameTy Δℕ JB Δℕ JB
same-JB =
  ` 0 ⇒ ((`∀ (` 0 ⇒ ` 1)) ⇒ ` 0)
    , same-⇒ (same-var here)
        (same-⇒
          (same-∀ (same-⇒ (same-var here) (same-var (there here))))
          (same-var here))
    , same-⇒ (same-var here)
        (same-⇒
          (same-∀ (same-⇒ (same-var here) (same-var (there here))))
          (same-var here))

sameExt-JTarget : SameTyExt 1 empty JTarget Δℕ JTarget
sameExt-JTarget =
  JTarget
    , same-⇒ same-ℕ
        (same-⇒
          (same-∀ (same-⇒ (same-var here) same-ℕ))
          same-ℕ)
    , same-⇒ same-ℕ
        (same-⇒
          (same-∀ (same-⇒ (same-var here) same-ℕ))
          same-ℕ)

J₁-⊢ : empty ∣ [] ⊢ J₁ ⦂ `ℕ
J₁-⊢ = ⊢· (⊢· wrapped ⊢$) (⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢$))
  where
  wrapped : empty ∣ []
    ⊢ (ƛ ` 0 ∙ Jbody) ⟪ TyBetaMorph , Jmint ⟫ ⦂ JTarget
  wrapped =
    env TyBeta-mw (⊢ƛ (wf-var (_ , here)) Jbody-Δℕ-⊢)
        Jmint-⊢ same-JB sameExt-JTarget
        (wf-⇒ wf-ℕ
          (wf-⇒ (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-ℕ)) wf-ℕ))

same-JT⇒X : SameTy Δℕ (JT ⇒ ` 0) Δℕ (JT ⇒ ` 0)
same-JT⇒X =
  (`∀ (` 0 ⇒ ` 1)) ⇒ ` 0
    , same-⇒
        (same-∀ (same-⇒ (same-var here) (same-var (there here))))
        (same-var here)
    , same-⇒
        (same-∀ (same-⇒ (same-var here) (same-var (there here))))
        (same-var here)

sameExt-const3⇒ℕ : SameTyExt 1 empty (const3Ty ⇒ `ℕ)
  Δℕ (const3Ty ⇒ `ℕ)
sameExt-const3⇒ℕ =
  const3Ty ⇒ `ℕ
    , same-⇒ (same-∀ (same-⇒ (same-var here) same-ℕ)) same-ℕ
    , same-⇒ (same-∀ (same-⇒ (same-var here) same-ℕ)) same-ℕ

J₂-⊢ : empty ∣ [] ⊢ J₂ ⦂ `ℕ
J₂-⊢ = ⊢· wrapped (⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢$))
  where
  wrapped : empty ∣ [] ⊢
    ((ƛ ` 0 ∙ Jbody) · (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
      ⟪ TyBetaMorph , (`∀ stℕ) ↦ unseal 0 ⟫
      ⦂ (const3Ty ⇒ `ℕ)
  wrapped =
    env TyBeta-mw
        (⊢· (⊢ƛ (wf-var (_ , here)) Jbody-Δℕ-⊢)
            sealed-seven-⊢)
        (conv-fun (conv-all stℕ-⊢) (conv-unseal β-lookup))
        same-JT⇒X sameExt-const3⇒ℕ
        (wf-⇒ (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-ℕ)) wf-ℕ)

J₃-inner-⊢ : Δℕ ∣ [] ⊢
  ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) ·
            (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
    ⦂ (JT ⇒ ` 0)
J₃-inner-⊢ =
  ⊢ƛ JT-wf
    (⊢· (⊢·[] (⊢` here) (wf-var (_ , here))) sealed-seven-⊢)

J₃-⊢ : empty ∣ [] ⊢ J₃ ⦂ `ℕ
J₃-⊢ = ⊢· wrapped (⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢$))
  where
  wrapped : empty ∣ [] ⊢
    (ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) ·
               (($ 7) ⟪ Θℕ-dual , seal 0 ⟫)))
      ⟪ TyBetaMorph , (`∀ stℕ) ↦ unseal 0 ⟫
      ⦂ (const3Ty ⇒ `ℕ)
  wrapped =
    env TyBeta-mw J₃-inner-⊢
        (conv-fun (conv-all stℕ-⊢) (conv-unseal β-lookup))
        same-JT⇒X sameExt-const3⇒ℕ
        (wf-⇒ (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-ℕ)) wf-ℕ)

J₄-⊢ : empty ∣ [] ⊢ J₄ ⦂ `ℕ
J₄-⊢ =
  env TyBeta-mw (⊢· J₃-inner-⊢ const3-cross-⊢)
      (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

J₅-⊢ : empty ∣ [] ⊢ J₅ ⦂ `ℕ
J₅-⊢ =
  env TyBeta-mw
      (⊢· (⊢·[] const3-cross-⊢ (wf-var (_ , here)))
          sealed-seven-⊢)
      (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

ΔJ-int ΔJ-conv : Ctxᵗ
ΔJ-int = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ [])
ΔJ-conv = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

wf-J-reps : WfRepCtx (bindR (` 0) ∷ bindR `ℕ ∷ [])
wf-J-reps =
  wf-bindR (wfᴿ-var (free-ref here))
    (wf-bindR wfᴿ-ℕ wf-reps[])

wf-ΔJ-int : WfCtx ΔJ-int
wf-ΔJ-int =
  wf-ctx wf-J-reps
    (λ { here → _ , here })
    (unique∷ fresh[] unique[])

wf-ΔJ-conv : WfCtx ΔJ-conv
wf-ΔJ-conv =
  wf-ctx wf-J-reps
    (λ { here → _ , here
       ; (there here) → _ , there here })
    (unique∷ (fresh∷ (λ ()) fresh[])
      (unique∷ fresh[] unique[]))

ΘJ-mw : MorphWf Δℕ (instantiate (` 0) Θℕ-dual) ΔJ-int ΔJ-conv
ΘJ-mw =
  mw TyBetaCtx-wf
     (binds∷ (wfᴿ-var (free-ref here)) binds[])
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , here) (fresh∷ (λ ()) fresh[])
             ins-here))
         (step-lock (_ , there here) (del-there del-here)
           (fresh∷ (λ ()) fresh[]))))
     (conversion
       (conv-lock (_ , there here)
         (conv-unlock (_ , here) conv[]
           (fresh∷ (λ ()) fresh[]) ins-here)))
     wf-ΔJ-int wf-ΔJ-conv

lookup-J0 : ΔJ-conv ∋ 0 := ` 1
lookup-J0 = 0 , ` 1 , here , r-here , same-var (there here)

lookup-J1 : ΔJ-conv ∋ 1 := `ℕ
lookup-J1 = 1 , `ℕ , there here , r-there r-here , same-ℕ

J₆head-⊢ : Δℕ ∣ [] ⊢ J₆head ⦂ (` 0 ⇒ ` 0)
J₆head-⊢ =
  env ΘJ-mw
      (⊢ƛ (wf-var (_ , here)) ⊢$)
      (conv-fun (conv-seal lookup-J0) (conv-seal lookup-J1))
      (` 0 ⇒ `ℕ
        , same-⇒ (same-var here) same-ℕ
        , same-⇒ (same-var here) same-ℕ)
      (` 0 ⇒ ` 0
        , same-⇒ (same-var here) (same-var here)
        , same-⇒ (same-var (there here)) (same-var (there here)))
      (wf-⇒ (wf-var (_ , here)) (wf-var (_ , here)))

J₆-⊢ : empty ∣ [] ⊢ J₆ ⦂ `ℕ
J₆-⊢ =
  env TyBeta-mw (⊢· J₆head-⊢ sealed-seven-⊢)
      (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

ΘJ ΘJ-dual ΘJ-cancel : CtxMorph
ΘJ = morph (` 0 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
ΘJ-dual = morph [] (lock 0 0 ∷ unlock 1 1 ∷ [])
ΘJ-cancel =
  morph (` 0 ∷ [])
    (lock 1 1 ∷ unlock 0 0 ∷ unlock 0 1 ∷ [])

Jshift Jarg J₇ J₈ J₉ J₁₀ : Term
Jshift = renᴹ² (ren² idᵗ (wkN (numBinds ΘJ)))
           (($ 7) ⟪ Θℕ-dual , seal 0 ⟫)
Jarg = Jshift ⟪ ΘJ-dual , seal 0 ⟫
J₇ = (((ƛ ` 0 ∙ $ 3) · Jarg) ⟪ ΘJ , seal 1 ⟫)
       ⟪ TyBetaMorph , unseal 0 ⟫
J₈ = (($ 3) ⟪ ΘJ , seal 1 ⟫)
       ⟪ TyBetaMorph , unseal 0 ⟫
J₉ = (($ 3) ⟪ ΘJ-cancel , id `ℕ ⟫)
       ⟪ Θℕ-rewind , id `ℕ ⟫
J₁₀ = ($ 3) ⟪ Θℕ-rewind , id `ℕ ⟫

J-step₆ : empty ⊢ J₆ -→ J₇
J-step₆ =
  ξ-⟪⟫ TyBeta-interior
    (Peel V-ƛ (V-⟪⟫ V-$ I-seal))

Jarg-value : Value Jarg
Jarg-value = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal

J-step₇ : empty ⊢ J₇ -→ J₈
J-step₇ =
  ξ-⟪⟫ TyBeta-interior
    (ξ-⟪⟫ (mw-interior ΘJ-mw) (Beta Jarg-value))

J-step₈ : empty ⊢ J₈ -→ J₉
J-step₈ =
  CancelR V-$ TyBeta-conversion (name-fn TyBetaCtx-wf) β-lookup

J-step₉ : empty ⊢ J₉ -→ J₁₀
J-step₉ = ξ-⟪⟫ (mw-interior Θℕ-rewind-mw) (Drop$ base-ℕ)

J-step₁₀ : empty ⊢ J₁₀ -→ $ 3
J-step₁₀ = Drop$ base-ℕ

ΔJ-arg-int ΔJ-none : Ctxᵗ
ΔJ-arg-int = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (1 ∷ [])
ΔJ-none = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ []

wf-ΔJ-arg-int : WfCtx ΔJ-arg-int
wf-ΔJ-arg-int =
  wf-ctx wf-J-reps
    (λ { here → _ , there here })
    (unique∷ fresh[] unique[])

wf-ΔJ-none : WfCtx ΔJ-none
wf-ΔJ-none = wf-ctx wf-J-reps (λ ()) unique[]

ΘJ-shift-mw : MorphWf ΔJ-arg-int
  (morph [] (lock 0 1 ∷ [])) ΔJ-none ΔJ-arg-int
ΘJ-shift-mw =
  mw wf-ΔJ-arg-int binds[]
     (interior
       (changes∷ changes[]
         (step-lock (_ , there here) del-here fresh[])))
     (conversion (conv-lock (_ , there here) conv[]))
     wf-ΔJ-none wf-ΔJ-arg-int

lookup-shift-X : ΔJ-arg-int ∋ 0 := `ℕ
lookup-shift-X = 1 , `ℕ , here , r-there r-here , same-ℕ

Jshift-⊢ : ΔJ-arg-int ∣ [] ⊢ Jshift ⦂ ` 0
Jshift-⊢ =
  env ΘJ-shift-mw ⊢$ (conv-seal lookup-shift-X)
      (`ℕ , same-ℕ , same-ℕ)
      (` 1 , same-var here , same-var here)
      (wf-var (_ , here))

ΘJ-dual-mw : MorphWf ΔJ-int
  (morph [] (lock 0 0 ∷ unlock 1 1 ∷ []))
  ΔJ-arg-int ΔJ-conv
ΘJ-dual-mw =
  mw wf-ΔJ-int binds[]
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , there here)
             (fresh∷ (λ ()) fresh[])
             (ins-there ins-here)))
         (step-lock (_ , here) del-here
           (fresh∷ (λ ()) fresh[]))))
     (conversion
       (conv-lock (_ , here)
         (conv-unlock (_ , there here) conv[]
           (fresh∷ (λ ()) fresh[])
           (ins-there ins-here))))
     wf-ΔJ-arg-int wf-ΔJ-conv

Jarg-⊢ : ΔJ-int ∣ [] ⊢ Jarg ⦂ ` 0
Jarg-⊢ =
  env ΘJ-dual-mw Jshift-⊢ (conv-seal lookup-J0)
      (` 1 , same-var here , same-var (there here))
      (` 0 , same-var here , same-var here)
      (wf-var (_ , here))

J₇-inner-⊢ : Δℕ ∣ []
  ⊢ ((ƛ ` 0 ∙ $ 3) · Jarg) ⟪ ΘJ , seal 1 ⟫ ⦂ ` 0
J₇-inner-⊢ =
  env ΘJ-mw (⊢· (⊢ƛ (wf-var (_ , here)) ⊢$) Jarg-⊢)
      (conv-seal lookup-J1)
      (`ℕ , same-ℕ , same-ℕ)
      (` 0 , same-var here , same-var (there here))
      (wf-var (_ , here))

J₇-⊢ : empty ∣ [] ⊢ J₇ ⦂ `ℕ
J₇-⊢ =
  env TyBeta-mw J₇-inner-⊢ (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

J₈-inner-⊢ : Δℕ ∣ [] ⊢ ($ 3) ⟪ ΘJ , seal 1 ⟫ ⦂ ` 0
J₈-inner-⊢ =
  env ΘJ-mw ⊢$ (conv-seal lookup-J1)
      (`ℕ , same-ℕ , same-ℕ)
      (` 0 , same-var here , same-var (there here))
      (wf-var (_ , here))

J₈-⊢ : empty ∣ [] ⊢ J₈ ⦂ `ℕ
J₈-⊢ =
  env TyBeta-mw J₈-inner-⊢ (conv-unseal β-lookup)
      same-Xℕ (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

ΘJ-cancel-mw : MorphWf Δℕ-lock ΘJ-cancel ΔJ-int ΔJ-conv
ΘJ-cancel-mw =
  mw wf-Δℕ-lock
     (binds∷ (wfᴿ-var (free-ref here)) binds[])
     (interior
       (changes∷
         (changes∷
           (changes∷ changes[]
             (step-unlock (_ , there here) fresh[] ins-here))
           (step-unlock (_ , here)
             (fresh∷ (λ ()) fresh[]) ins-here))
         (step-lock (_ , there here) (del-there del-here)
           (fresh∷ (λ ()) fresh[]))))
     (conversion
       (conv-lock (_ , there here)
         (conv-unlock (_ , here)
           (conv-unlock (_ , there here) conv[] fresh[] ins-here)
           (fresh∷ (λ ()) fresh[]) ins-here)))
     wf-ΔJ-int wf-ΔJ-conv

J₉-inner-⊢ : Δℕ-lock ∣ []
  ⊢ ($ 3) ⟪ ΘJ-cancel , id `ℕ ⟫ ⦂ `ℕ
J₉-inner-⊢ =
  env ΘJ-cancel-mw ⊢$ (conv-id base-ℕ)
      (`ℕ , same-ℕ , same-ℕ)
      (sameExt-ℕ₁ {Γ = Δℕ-lock} {Γ′ = ΔJ-conv}) wf-ℕ

J₉-⊢ : empty ∣ [] ⊢ J₉ ⦂ `ℕ
J₉-⊢ =
  env Θℕ-rewind-mw J₉-inner-⊢ (conv-id base-ℕ)
      (same-ℕℕ {Γ = Δℕ-lock} {Γ′ = Δℕ})
      (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

J₁₀-⊢ : empty ∣ [] ⊢ J₁₀ ⦂ `ℕ
J₁₀-⊢ =
  env Θℕ-rewind-mw ⊢$ (conv-id base-ℕ)
      (same-ℕℕ {Γ = Δℕ-lock} {Γ′ = Δℕ})
      (sameExt-ℕ₁ {Γ = empty} {Γ′ = Δℕ}) wf-ℕ

J-final-⊢ : empty ∣ [] ⊢ $ 3 ⦂ `ℕ
J-final-⊢ = ⊢$

J-final-value : Value ($ 3)
J-final-value = V-$

J-run : empty ⊢ J₀ -→* $ 3
J-run =
  J-step₀ then
  J-step₁ then
  J-step₂ then
  J-step₃ then
  J-step₄ then
  J-step₅ then
  J-step₆ then
  J-step₇ then
  J-step₈ then
  J-step₉ then
  J-step₁₀ then
  done

------------------------------------------------------------------------
-- 2. (ΛX. λf:(∀Y.Y⇒𝔹). f[X]) [𝔹] · (ΛZ.λz:Z.true) · false
------------------------------------------------------------------------

Δ𝔹 Δ𝔹-lock : Ctxᵗ
Δ𝔹 = (bindR `𝔹 ∷ []) ∣ (0 ∷ [])
Δ𝔹-lock = (bindR `𝔹 ∷ []) ∣ []

wf-Δ𝔹 : WfCtx Δ𝔹
wf-Δ𝔹 =
  wf-ctx (wf-bindR wfᴿ-𝔹 wf-reps[])
    (λ { here → _ , here })
    (unique∷ fresh[] unique[])

wf-Δ𝔹-lock : WfCtx Δ𝔹-lock
wf-Δ𝔹-lock =
  wf-ctx (wf-bindR wfᴿ-𝔹 wf-reps[]) (λ ()) unique[]

Θ𝔹 Θ𝔹-dual Θ𝔹-rewind : CtxMorph
Θ𝔹 = morph (`𝔹 ∷ []) (unlock 0 0 ∷ [])
Θ𝔹-dual = morph [] (lock 0 0 ∷ [])
Θ𝔹-rewind =
  morph (`𝔹 ∷ []) (lock 0 0 ∷ unlock 0 0 ∷ [])

Θ𝔹-mw : MorphWf empty Θ𝔹 Δ𝔹 Δ𝔹
Θ𝔹-mw =
  mw wf-empty (binds∷ wfᴿ-𝔹 binds[])
     (interior
       (changes∷ changes[]
         (step-unlock (_ , here) fresh[] ins-here)))
     (conversion
       (conv-unlock (_ , here) conv[] fresh[] ins-here))
     wf-Δ𝔹 wf-Δ𝔹

Θ𝔹-dual-mw : MorphWf Δ𝔹 Θ𝔹-dual Δ𝔹-lock Δ𝔹
Θ𝔹-dual-mw =
  mw wf-Δ𝔹 binds[]
     (interior
       (changes∷ changes[]
         (step-lock (_ , here) del-here fresh[])))
     (conversion (conv-lock (_ , here) conv[]))
     wf-Δ𝔹-lock wf-Δ𝔹

Θ𝔹-rewind-mw : MorphWf empty Θ𝔹-rewind Δ𝔹-lock Δ𝔹
Θ𝔹-rewind-mw =
  mw wf-empty (binds∷ wfᴿ-𝔹 binds[])
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , here) fresh[] ins-here))
         (step-lock (_ , here) del-here fresh[])))
     (conversion
       (conv-lock (_ , here)
         (conv-unlock (_ , here) conv[] fresh[] ins-here)))
     wf-Δ𝔹-lock wf-Δ𝔹

lookup-𝔹 : Δ𝔹 ∋ 0 := `𝔹
lookup-𝔹 = 0 , `𝔹 , here , r-here , same-𝔹

GT : Ty
GT = `∀ (` 0 ⇒ `𝔹)

truePoly : Term
truePoly = Λ (ƛ ` 0 ∙ `true)

truePoly-⊢ : ∀ {Γ} → Δ𝔹-lock ∣ Γ ⊢ truePoly ⦂ GT
truePoly-⊢ = ⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢true)

lookup-X-underΛ𝔹 : underΛ Δ𝔹 ∋ 1 := `𝔹
lookup-X-underΛ𝔹 =
  1 , `𝔹 , there here , r-there-abst r-here , same-𝔹

st𝔹 : Conv
st𝔹 = id (` 0) ↦ id `𝔹

st𝔹-⊢ : underΛ Δ𝔹 ⊢ st𝔹 ∶ (` 0 ⇒ `𝔹) ⇝ (` 0 ⇒ `𝔹)
st𝔹-⊢ = conv-fun (conv-idv (_ , here)) (conv-id base-𝔹)

truePoly-cross-⊢ : ∀ {Γ}
  → Δ𝔹 ∣ Γ ⊢ truePoly ⟪ Θ𝔹-dual , `∀ st𝔹 ⟫ ⦂ GT
truePoly-cross-⊢ =
  env Θ𝔹-dual-mw truePoly-⊢ (conv-all st𝔹-⊢)
      (`∀ (` 0 ⇒ `𝔹)
        , same-∀ (same-⇒ (same-var here) same-𝔹)
        , same-∀ (same-⇒ (same-var here) same-𝔹))
      (`∀ (` 0 ⇒ `𝔹)
        , same-∀ (same-⇒ (same-var here) same-𝔹)
        , same-∀ (same-⇒ (same-var here) same-𝔹))
      (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-𝔹))

FB : Ty
FB = GT ⇒ (` 0 ⇒ `𝔹)

Fbody Ffun : Term
Fbody = ƛ GT ∙ ((` 0) ·[ ` 0 ⇒ `𝔹 , ` 0 ])
Ffun = Λ Fbody

Ffun-⊢ : empty ∣ [] ⊢ Ffun ⦂ `∀ FB
Ffun-⊢ =
  ⊢Λ
    (⊢ƛ
      (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-𝔹))
      (⊢·[] (⊢` here) (wf-var (_ , here))))

K₀ : Term
K₀ = ((Ffun ·[ FB , `𝔹 ]) · truePoly) · `false

K₀-⊢ : empty ∣ [] ⊢ K₀ ⦂ `𝔹
K₀-⊢ =
  ⊢· (⊢· (⊢·[] Ffun-⊢ wf-𝔹)
          (⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢true)))
      ⊢false

Kmint : Conv
Kmint = (`∀ st𝔹) ↦ (seal 0 ↦ id `𝔹)

ΘK ΘK-dual : CtxMorph
ΘK = morph (` 0 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
ΘK-dual = morph [] (lock 0 0 ∷ unlock 1 1 ∷ [])

K₁ K₂ K₃ Khead K₄ Kfalse Karg K₅ K₆ K₇ K₈ : Term
K₁ = ((Fbody ⟪ Θ𝔹 , Kmint ⟫) · truePoly) · `false
K₂ = ((Fbody · (truePoly ⟪ Θ𝔹-dual , `∀ st𝔹 ⟫))
        ⟪ Θ𝔹 , seal 0 ↦ id `𝔹 ⟫) · `false
K₃ = (((truePoly ⟪ Θ𝔹-dual , `∀ st𝔹 ⟫)
          ·[ ` 0 ⇒ `𝔹 , ` 0 ])
        ⟪ Θ𝔹 , seal 0 ↦ id `𝔹 ⟫) · `false
Khead = (ƛ ` 0 ∙ `true)
  ⟪ ΘK , seal 0 ↦ id `𝔹 ⟫
K₄ = (Khead ⟪ Θ𝔹 , seal 0 ↦ id `𝔹 ⟫) · `false
Kfalse = `false ⟪ Θ𝔹-dual , seal 0 ⟫
K₅ = (Khead · Kfalse) ⟪ Θ𝔹 , id `𝔹 ⟫
Karg =
  renᴹ² (ren² idᵗ (wkN (numBinds ΘK))) Kfalse
    ⟪ ΘK-dual , seal 0 ⟫
K₆ = (((ƛ ` 0 ∙ `true) · Karg) ⟪ ΘK , id `𝔹 ⟫)
       ⟪ Θ𝔹 , id `𝔹 ⟫
K₇ = (`true ⟪ ΘK , id `𝔹 ⟫) ⟪ Θ𝔹 , id `𝔹 ⟫
K₈ = `true ⟪ Θ𝔹 , id `𝔹 ⟫

ΔK-int ΔK-conv : Ctxᵗ
ΔK-int = (bindR (` 0) ∷ bindR `𝔹 ∷ []) ∣ (0 ∷ [])
ΔK-conv = (bindR (` 0) ∷ bindR `𝔹 ∷ []) ∣ (0 ∷ 1 ∷ [])

wf-K-reps : WfRepCtx (bindR (` 0) ∷ bindR `𝔹 ∷ [])
wf-K-reps =
  wf-bindR (wfᴿ-var (free-ref here))
    (wf-bindR wfᴿ-𝔹 wf-reps[])

wf-ΔK-int : WfCtx ΔK-int
wf-ΔK-int =
  wf-ctx wf-K-reps
    (λ { here → _ , here })
    (unique∷ fresh[] unique[])

wf-ΔK-conv : WfCtx ΔK-conv
wf-ΔK-conv =
  wf-ctx wf-K-reps
    (λ { here → _ , here
       ; (there here) → _ , there here })
    (unique∷ (fresh∷ (λ ()) fresh[])
      (unique∷ fresh[] unique[]))

ΘK-mw : MorphWf Δ𝔹 ΘK ΔK-int ΔK-conv
ΘK-mw =
  mw wf-Δ𝔹
     (binds∷ (wfᴿ-var (free-ref here)) binds[])
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , here) (fresh∷ (λ ()) fresh[])
             ins-here))
         (step-lock (_ , there here) (del-there del-here)
           (fresh∷ (λ ()) fresh[]))))
     (conversion
       (conv-lock (_ , there here)
         (conv-unlock (_ , here) conv[]
           (fresh∷ (λ ()) fresh[]) ins-here)))
     wf-ΔK-int wf-ΔK-conv

lookup-K0 : ΔK-conv ∋ 0 := ` 1
lookup-K0 = 0 , ` 1 , here , r-here , same-var (there here)

lookup-K1 : ΔK-conv ∋ 1 := `𝔹
lookup-K1 = 1 , `𝔹 , there here , r-there r-here , same-𝔹

K-step₀ : empty ⊢ K₀ -→ K₁
K-step₀ = ξ-·-l (ξ-·-l (TyBeta V-ƛ same-𝔹))

K-step₁ : empty ⊢ K₁ -→ K₂
K-step₁ = ξ-·-l (Peel V-ƛ (V-Λ V-ƛ))

K-step₂ : empty ⊢ K₂ -→ K₃
K-step₂ =
  ξ-·-l
    (ξ-⟪⟫ (mw-interior Θ𝔹-mw)
      (Beta (V-⟪⟫ (V-Λ V-ƛ) I-all)))

unique-underΛΔ𝔹 : Unique (names (underΛ Δ𝔹))
unique-underΛΔ𝔹 = unique-underΛ {Γ = Δ𝔹} (name-fn wf-Δ𝔹)

K-step₃ : empty ⊢ K₃ -→ K₄
K-step₃ =
  ξ-·-l
    (ξ-⟪⟫ (mw-interior Θ𝔹-mw)
      (TyPeelR-Λ V-ƛ
        (mw-conversion Θ𝔹-dual-mw)
        unique-underΛΔ𝔹 st𝔹-⊢ (same-var here)))

K-step₄ : empty ⊢ K₄ -→ K₅
K-step₄ = Peel (V-⟪⟫ V-ƛ I-fun) V-false

K-step₅ : empty ⊢ K₅ -→ K₆
K-step₅ =
  ξ-⟪⟫ (mw-interior Θ𝔹-mw)
    (Peel V-ƛ (V-⟪⟫ V-false I-seal))

Karg-value : Value Karg
Karg-value = V-⟪⟫ (V-⟪⟫ V-false I-seal) I-seal

K-step₆ : empty ⊢ K₆ -→ K₇
K-step₆ =
  ξ-⟪⟫ (mw-interior Θ𝔹-mw)
    (ξ-⟪⟫ (mw-interior ΘK-mw) (Beta Karg-value))

K-step₇ : empty ⊢ K₇ -→ K₈
K-step₇ =
  ξ-⟪⟫ (mw-interior Θ𝔹-mw) Drop-true

K-step₈ : empty ⊢ K₈ -→ `true
K-step₈ = Drop-true

KTarget : Ty
KTarget = GT ⇒ (`𝔹 ⇒ `𝔹)

Kmint-⊢ : Δ𝔹 ⊢ Kmint ∶ FB ⇝ KTarget
Kmint-⊢ =
  conv-fun (conv-all st𝔹-⊢)
    (conv-fun (conv-seal lookup-𝔹) (conv-id base-𝔹))

Fbody-Δ𝔹-⊢ : Δ𝔹 ∣ [] ⊢ Fbody ⦂ (GT ⇒ (` 0 ⇒ `𝔹))
Fbody-Δ𝔹-⊢ =
  ⊢ƛ (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-𝔹))
    (⊢·[] (⊢` here) (wf-var (_ , here)))

same-FB : SameTy Δ𝔹 FB Δ𝔹 FB
same-FB =
  (`∀ (` 0 ⇒ `𝔹)) ⇒ (` 0 ⇒ `𝔹)
    , same-⇒
        (same-∀ (same-⇒ (same-var here) same-𝔹))
        (same-⇒ (same-var here) same-𝔹)
    , same-⇒
        (same-∀ (same-⇒ (same-var here) same-𝔹))
        (same-⇒ (same-var here) same-𝔹)

sameExt-KTarget : SameTyExt 1 empty KTarget Δ𝔹 KTarget
sameExt-KTarget =
  KTarget
    , same-⇒
        (same-∀ (same-⇒ (same-var here) same-𝔹))
        (same-⇒ same-𝔹 same-𝔹)
    , same-⇒
        (same-∀ (same-⇒ (same-var here) same-𝔹))
        (same-⇒ same-𝔹 same-𝔹)

K₁-⊢ : empty ∣ [] ⊢ K₁ ⦂ `𝔹
K₁-⊢ =
  ⊢· (⊢· wrapped (⊢Λ (⊢ƛ (wf-var (_ , here)) ⊢true))) ⊢false
  where
  wrapped : empty ∣ [] ⊢ Fbody ⟪ Θ𝔹 , Kmint ⟫ ⦂ KTarget
  wrapped =
    env Θ𝔹-mw Fbody-Δ𝔹-⊢ Kmint-⊢ same-FB sameExt-KTarget
        (wf-⇒ (wf-∀ (wf-⇒ (wf-var (_ , here)) wf-𝔹))
          (wf-⇒ wf-𝔹 wf-𝔹))

same-GT⇒X𝔹 : SameTy Δ𝔹 (GT ⇒ (` 0 ⇒ `𝔹))
  Δ𝔹 (GT ⇒ (` 0 ⇒ `𝔹))
same-GT⇒X𝔹 =
  (`∀ (` 0 ⇒ `𝔹)) ⇒ (` 0 ⇒ `𝔹)
    , same-⇒
        (same-∀ (same-⇒ (same-var here) same-𝔹))
        (same-⇒ (same-var here) same-𝔹)
    , same-⇒
        (same-∀ (same-⇒ (same-var here) same-𝔹))
        (same-⇒ (same-var here) same-𝔹)

sameExt-𝔹⇒𝔹 :
  SameTyExt 1 empty (`𝔹 ⇒ `𝔹) Δ𝔹 (`𝔹 ⇒ `𝔹)
sameExt-𝔹⇒𝔹 =
  `𝔹 ⇒ `𝔹 , same-⇒ same-𝔹 same-𝔹
             , same-⇒ same-𝔹 same-𝔹

K₂-⊢ : empty ∣ [] ⊢ K₂ ⦂ `𝔹
K₂-⊢ = ⊢· wrapped ⊢false
  where
  wrapped : empty ∣ [] ⊢
    (Fbody · (truePoly ⟪ Θ𝔹-dual , `∀ st𝔹 ⟫))
      ⟪ Θ𝔹 , seal 0 ↦ id `𝔹 ⟫ ⦂ (`𝔹 ⇒ `𝔹)
  wrapped =
    env Θ𝔹-mw (⊢· Fbody-Δ𝔹-⊢ truePoly-cross-⊢)
        (conv-fun (conv-seal lookup-𝔹) (conv-id base-𝔹))
        (` 0 ⇒ `𝔹
          , same-⇒ (same-var here) same-𝔹
          , same-⇒ (same-var here) same-𝔹)
        sameExt-𝔹⇒𝔹 (wf-⇒ wf-𝔹 wf-𝔹)

K₃-⊢ : empty ∣ [] ⊢ K₃ ⦂ `𝔹
K₃-⊢ = ⊢· wrapped ⊢false
  where
  wrapped : empty ∣ [] ⊢
    ((truePoly ⟪ Θ𝔹-dual , `∀ st𝔹 ⟫)
       ·[ ` 0 ⇒ `𝔹 , ` 0 ])
      ⟪ Θ𝔹 , seal 0 ↦ id `𝔹 ⟫ ⦂ (`𝔹 ⇒ `𝔹)
  wrapped =
    env Θ𝔹-mw
        (⊢·[] truePoly-cross-⊢ (wf-var (_ , here)))
        (conv-fun (conv-seal lookup-𝔹) (conv-id base-𝔹))
        (` 0 ⇒ `𝔹
          , same-⇒ (same-var here) same-𝔹
          , same-⇒ (same-var here) same-𝔹)
        sameExt-𝔹⇒𝔹 (wf-⇒ wf-𝔹 wf-𝔹)

Khead-⊢ : Δ𝔹 ∣ [] ⊢ Khead ⦂ (` 0 ⇒ `𝔹)
Khead-⊢ =
  env ΘK-mw (⊢ƛ (wf-var (_ , here)) ⊢true)
      (conv-fun (conv-seal lookup-K0) (conv-id base-𝔹))
      (` 0 ⇒ `𝔹
        , same-⇒ (same-var here) same-𝔹
        , same-⇒ (same-var here) same-𝔹)
      (` 0 ⇒ `𝔹
        , same-⇒ (same-var here) same-𝔹
        , same-⇒ (same-var (there here)) same-𝔹)
      (wf-⇒ (wf-var (_ , here)) wf-𝔹)

K₄-⊢ : empty ∣ [] ⊢ K₄ ⦂ `𝔹
K₄-⊢ = ⊢· wrapped ⊢false
  where
  wrapped : empty ∣ []
    ⊢ Khead ⟪ Θ𝔹 , seal 0 ↦ id `𝔹 ⟫ ⦂ (`𝔹 ⇒ `𝔹)
  wrapped =
    env Θ𝔹-mw Khead-⊢
        (conv-fun (conv-seal lookup-𝔹) (conv-id base-𝔹))
        (` 0 ⇒ `𝔹
          , same-⇒ (same-var here) same-𝔹
          , same-⇒ (same-var here) same-𝔹)
        sameExt-𝔹⇒𝔹 (wf-⇒ wf-𝔹 wf-𝔹)

Kfalse-⊢ : ∀ {Γ} → Δ𝔹 ∣ Γ ⊢ Kfalse ⦂ ` 0
Kfalse-⊢ =
  env Θ𝔹-dual-mw ⊢false (conv-seal lookup-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (` 0 , same-var here , same-var here)
      (wf-var (_ , here))

K₅-⊢ : empty ∣ [] ⊢ K₅ ⦂ `𝔹
K₅-⊢ =
  env Θ𝔹-mw (⊢· Khead-⊢ Kfalse-⊢) (conv-id base-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹) wf-𝔹

ΔK-arg-int ΔK-none : Ctxᵗ
ΔK-arg-int = (bindR (` 0) ∷ bindR `𝔹 ∷ []) ∣ (1 ∷ [])
ΔK-none = (bindR (` 0) ∷ bindR `𝔹 ∷ []) ∣ []

wf-ΔK-arg-int : WfCtx ΔK-arg-int
wf-ΔK-arg-int =
  wf-ctx wf-K-reps
    (λ { here → _ , there here })
    (unique∷ fresh[] unique[])

wf-ΔK-none : WfCtx ΔK-none
wf-ΔK-none = wf-ctx wf-K-reps (λ ()) unique[]

ΘK-shift-mw : MorphWf ΔK-arg-int
  (morph [] (lock 0 1 ∷ [])) ΔK-none ΔK-arg-int
ΘK-shift-mw =
  mw wf-ΔK-arg-int binds[]
     (interior
       (changes∷ changes[]
         (step-lock (_ , there here) del-here fresh[])))
     (conversion (conv-lock (_ , there here) conv[]))
     wf-ΔK-none wf-ΔK-arg-int

lookup-shift-𝔹 : ΔK-arg-int ∋ 0 := `𝔹
lookup-shift-𝔹 = 1 , `𝔹 , here , r-there r-here , same-𝔹

Kshift-⊢ : ΔK-arg-int ∣ []
  ⊢ renᴹ² (ren² idᵗ (wkN (numBinds ΘK))) Kfalse ⦂ ` 0
Kshift-⊢ =
  env ΘK-shift-mw ⊢false (conv-seal lookup-shift-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (` 1 , same-var here , same-var here)
      (wf-var (_ , here))

ΘK-dual-mw : MorphWf ΔK-int
  (morph [] (lock 0 0 ∷ unlock 1 1 ∷ []))
  ΔK-arg-int ΔK-conv
ΘK-dual-mw =
  mw wf-ΔK-int binds[]
     (interior
       (changes∷
         (changes∷ changes[]
           (step-unlock (_ , there here)
             (fresh∷ (λ ()) fresh[])
             (ins-there ins-here)))
         (step-lock (_ , here) del-here
           (fresh∷ (λ ()) fresh[]))))
     (conversion
       (conv-lock (_ , here)
         (conv-unlock (_ , there here) conv[]
           (fresh∷ (λ ()) fresh[])
           (ins-there ins-here))))
     wf-ΔK-arg-int wf-ΔK-conv

Karg-⊢ : ΔK-int ∣ [] ⊢ Karg ⦂ ` 0
Karg-⊢ =
  env ΘK-dual-mw Kshift-⊢ (conv-seal lookup-K0)
      (` 1 , same-var here , same-var (there here))
      (` 0 , same-var here , same-var here)
      (wf-var (_ , here))

K₆-inner-⊢ : Δ𝔹 ∣ []
  ⊢ ((ƛ ` 0 ∙ `true) · Karg) ⟪ ΘK , id `𝔹 ⟫ ⦂ `𝔹
K₆-inner-⊢ =
  env ΘK-mw (⊢· (⊢ƛ (wf-var (_ , here)) ⊢true) Karg-⊢)
      (conv-id base-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹) wf-𝔹

K₆-⊢ : empty ∣ [] ⊢ K₆ ⦂ `𝔹
K₆-⊢ =
  env Θ𝔹-mw K₆-inner-⊢ (conv-id base-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹) wf-𝔹

K₇-inner-⊢ : Δ𝔹 ∣ [] ⊢ `true ⟪ ΘK , id `𝔹 ⟫ ⦂ `𝔹
K₇-inner-⊢ =
  env ΘK-mw ⊢true (conv-id base-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹) wf-𝔹

K₇-⊢ : empty ∣ [] ⊢ K₇ ⦂ `𝔹
K₇-⊢ =
  env Θ𝔹-mw K₇-inner-⊢ (conv-id base-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹) wf-𝔹

K₈-⊢ : empty ∣ [] ⊢ K₈ ⦂ `𝔹
K₈-⊢ =
  env Θ𝔹-mw ⊢true (conv-id base-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹)
      (`𝔹 , same-𝔹 , same-𝔹) wf-𝔹

K-final-⊢ : empty ∣ [] ⊢ `true ⦂ `𝔹
K-final-⊢ = ⊢true

K-final-value : Value `true
K-final-value = V-true

K-run : empty ⊢ K₀ -→* `true
K-run =
  K-step₀ then
  K-step₁ then
  K-step₂ then
  K-step₃ then
  K-step₄ then
  K-step₅ then
  K-step₆ then
  K-step₇ then
  K-step₈ then
  done

------------------------------------------------------------------------
-- 4. A polymorphic identity passed beneath a later type binder
------------------------------------------------------------------------

EID EBod : Ty
EID = `∀ (` 0 ⇒ ` 0)
EBod = EID ⇒ EID

Earg Ebody Efun E₀ : Term
Earg = Λ (ƛ ` 0 ∙ ` 0)
Ebody = Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ])
Efun = Λ (ƛ EID ∙ Ebody)
E₀ = (Efun ·[ EBod , `ℕ ]) · Earg

Eid∀ : Conv
Eid∀ = `∀ (id (` 0) ↦ id (` 0))

ΘE-X ΘE-Y ΘE-moved ΘE-Y-inst ΘE-Z-inst : CtxMorph
ΘE-X = morph [] (lock 0 1 ∷ [])
ΘE-Y = morph [] (lock 0 0 ∷ [])
ΘE-moved = morph [] (lock 0 2 ∷ lock 0 0 ∷ [])
ΘE-Y-inst = morph (` 0 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
ΘE-Z-inst =
  morph (` 0 ∷ []) (lock 1 3 ∷ lock 1 1 ∷ unlock 0 0 ∷ [])

EW EW-cross : Term
EW = Earg ⟪ Θℕ-dual , Eid∀ ⟫
EW-cross = Earg ⟪ ΘE-X , Eid∀ ⟫ ⟪ ΘE-Y , Eid∀ ⟫

E₁ E₂ E₃ E₄ E₅-head E₅ : Term
E₁ = ((ƛ EID ∙ Ebody)
        ⟪ TyBetaMorph , Eid∀ ↦ Eid∀ ⟫) · Earg
E₂ = ((ƛ EID ∙ Ebody) · EW) ⟪ TyBetaMorph , Eid∀ ⟫
E₃ = (Λ (EW-cross ·[ ` 0 ⇒ ` 0 , ` 0 ]))
       ⟪ TyBetaMorph , Eid∀ ⟫
E₄ =
  (Λ (((Earg ⟪ ΘE-moved , Eid∀ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ])
       ⟪ ΘE-Y-inst , seal 0 ↦ unseal 0 ⟫))
    ⟪ TyBetaMorph , Eid∀ ⟫
E₅-head = (ƛ ` 0 ∙ ` 0)
  ⟪ ΘE-Z-inst , seal 0 ↦ unseal 0 ⟫
E₅ =
  (Λ (E₅-head ⟪ ΘE-Y-inst , seal 0 ↦ unseal 0 ⟫))
    ⟪ TyBetaMorph , Eid∀ ⟫

ΔE ΔE-Y-int ΔE-none ΔE-YI-int ΔE-YI-conv ΔE-moved-int : Ctxᵗ
ΔE = (abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])
ΔE-Y-int = (abstR ∷ bindR `ℕ ∷ []) ∣ (1 ∷ [])
ΔE-none = (abstR ∷ bindR `ℕ ∷ []) ∣ []
ΔE-YI-int =
  (bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 2 ∷ [])
ΔE-YI-conv =
  (bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ 2 ∷ [])
ΔE-moved-int =
  (bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ []) ∣ []

ΔE-Z-int ΔE-Z-conv : Ctxᵗ
ΔE-Z-int =
  (bindR (` 0) ∷ bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ [])
    ∣ (0 ∷ [])
ΔE-Z-conv =
  (bindR (` 0) ∷ bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ [])
    ∣ (0 ∷ 1 ∷ 3 ∷ [])

wf-E-reps : WfRepCtx (abstR ∷ bindR `ℕ ∷ [])
wf-E-reps = wf-abstR (wf-bindR wfᴿ-ℕ wf-reps[])

wf-ΔE : WfCtx ΔE
wf-ΔE =
  wf-ctx wf-E-reps
    (λ { here → _ , here ; (there here) → _ , there here })
    (unique∷ (fresh∷ (λ ()) fresh[]) (unique∷ fresh[] unique[]))

wf-ΔE-Y-int : WfCtx ΔE-Y-int
wf-ΔE-Y-int =
  wf-ctx wf-E-reps (λ { here → _ , there here })
    (unique∷ fresh[] unique[])

wf-ΔE-none : WfCtx ΔE-none
wf-ΔE-none = wf-ctx wf-E-reps (λ ()) unique[]

wf-EYI-reps :
  WfRepCtx (bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ [])
wf-EYI-reps =
  wf-bindR (wfᴿ-var (free-ref here)) wf-E-reps

wf-ΔE-YI-int : WfCtx ΔE-YI-int
wf-ΔE-YI-int =
  wf-ctx wf-EYI-reps
    (λ { here → _ , here ; (there here) → _ , there (there here) })
    (unique∷ (fresh∷ (λ ()) fresh[])
      (unique∷ fresh[] unique[]))

wf-ΔE-YI-conv : WfCtx ΔE-YI-conv
wf-ΔE-YI-conv =
  wf-ctx wf-EYI-reps
    (λ { here → _ , here
       ; (there here) → _ , there here
       ; (there (there here)) → _ , there (there here) })
    (unique∷ (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[]))
      (unique∷ (fresh∷ (λ ()) fresh[])
        (unique∷ fresh[] unique[])))

wf-ΔE-moved-int : WfCtx ΔE-moved-int
wf-ΔE-moved-int = wf-ctx wf-EYI-reps (λ ()) unique[]

wf-EZ-reps : WfRepCtx
  (bindR (` 0) ∷ bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ [])
wf-EZ-reps =
  wf-bindR (wfᴿ-var (free-ref here)) wf-EYI-reps

wf-ΔE-Z-int : WfCtx ΔE-Z-int
wf-ΔE-Z-int =
  wf-ctx wf-EZ-reps (λ { here → _ , here })
    (unique∷ fresh[] unique[])

wf-ΔE-Z-conv : WfCtx ΔE-Z-conv
wf-ΔE-Z-conv =
  wf-ctx wf-EZ-reps
    (λ { here → _ , here
       ; (there here) → _ , there here
       ; (there (there here)) → _ , there (there (there here)) })
    (unique∷ (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[]))
      (unique∷ (fresh∷ (λ ()) fresh[])
        (unique∷ fresh[] unique[])))

ΘE-Y-mw : MorphWf ΔE ΘE-Y ΔE-Y-int ΔE
ΘE-Y-mw =
  mw wf-ΔE binds[]
    (interior
      (changes∷ changes[]
        (step-lock (_ , here) del-here
          (fresh∷ (λ ()) fresh[]))))
    (conversion (conv-lock (_ , here) conv[]))
    wf-ΔE-Y-int wf-ΔE

ΘE-X-mw : MorphWf ΔE-Y-int ΘE-X ΔE-none ΔE-Y-int
ΘE-X-mw =
  mw wf-ΔE-Y-int binds[]
    (interior
      (changes∷ changes[]
        (step-lock (_ , there here) del-here fresh[])))
    (conversion (conv-lock (_ , there here) conv[]))
    wf-ΔE-none wf-ΔE-Y-int

ΘE-Y-inst-mw : MorphWf ΔE ΘE-Y-inst ΔE-YI-int ΔE-YI-conv
ΘE-Y-inst-mw =
  mw wf-ΔE (binds∷ (wfᴿ-var (free-ref here)) binds[])
    (interior
      (changes∷
        (changes∷ changes[]
          (step-unlock (_ , here)
            (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[])) ins-here))
        (step-lock (_ , there here) (del-there del-here)
          (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[])))))
    (conversion
      (conv-lock (_ , there here)
        (conv-unlock (_ , here) conv[]
          (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[])) ins-here)))
    wf-ΔE-YI-int wf-ΔE-YI-conv

ΘE-Y-inst-interior : ΔE ⊢ⁱ ΘE-Y-inst ⇒ ΔE-YI-int
ΘE-Y-inst-interior = mw-interior ΘE-Y-inst-mw

ΘE-moved-mw : MorphWf ΔE-YI-int ΘE-moved
  ΔE-moved-int ΔE-YI-int
ΘE-moved-mw =
  mw wf-ΔE-YI-int binds[]
    (interior
      (changes∷
        (changes∷ changes[]
          (step-lock (_ , here) del-here
            (fresh∷ (λ ()) fresh[])))
        (step-lock (_ , there (there here)) del-here fresh[])))
    (conversion
      (conv-lock (_ , there (there here))
        (conv-lock (_ , here) conv[])))
    wf-ΔE-moved-int wf-ΔE-YI-int

ΘE-Z-inst-mw : MorphWf ΔE-YI-int ΘE-Z-inst
  ΔE-Z-int ΔE-Z-conv
ΘE-Z-inst-mw =
  mw wf-ΔE-YI-int (binds∷ (wfᴿ-var (free-ref here)) binds[])
    (interior
      (changes∷
        (changes∷
          (changes∷ changes[]
            (step-unlock (_ , here)
              (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[])) ins-here))
          (step-lock (_ , there here) (del-there del-here)
            (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[]))))
        (step-lock (_ , there (there (there here)))
          (del-there del-here) (fresh∷ (λ ()) fresh[]))))
    (conversion
      (conv-lock (_ , there (there (there here)))
        (conv-lock (_ , there here)
          (conv-unlock (_ , here) conv[]
            (fresh∷ (λ ()) (fresh∷ (λ ()) fresh[])) ins-here))))
    wf-ΔE-Z-int wf-ΔE-Z-conv

Eid↦Eid-⊢ : ∀ {Γ} → underΛ Γ ⊢ id (` 0) ↦ id (` 0)
  ∶ (` 0 ⇒ ` 0) ⇝ (` 0 ⇒ ` 0)
Eid↦Eid-⊢ =
  conv-fun (conv-idv (_ , here)) (conv-idv (_ , here))

unique-underΛΔE : Unique (names (underΛ ΔE))
unique-underΛΔE = unique-underΛ { Γ = ΔE } (name-fn wf-ΔE)

unique-underΛΔE-moved : Unique (names (underΛ ΔE-YI-int))
unique-underΛΔE-moved =
  unique-underΛ { Γ = ΔE-YI-int } (name-fn wf-ΔE-YI-int)

wf-EID : ∀ {Γ} → Γ ⊢ᵗ EID
wf-EID = wf-∀ (wf-⇒ (wf-var (_ , here)) (wf-var (_ , here)))

same-EID : ∀ {Γ Γ′} → SameTy Γ EID Γ′ EID
same-EID =
  EID , same-∀ (same-⇒ (same-var here) (same-var here))
      , same-∀ (same-⇒ (same-var here) (same-var here))

shiftRep-EID : ∀ n → shiftRep n EID ≡ EID
shiftRep-EID zero = refl
shiftRep-EID (suc n) rewrite shiftRep-EID n = refl

sameExt-EID₁ : ∀ {Γ Γ′} → SameTyExt 1 Γ EID Γ′ EID
sameExt-EID₁ =
  EID , same-∀ (same-⇒ (same-var here) (same-var here))
      , same-∀ (same-⇒ (same-var here) (same-var here))

Eid∀-⊢ : ∀ {Γ} → Γ ⊢ Eid∀ ∶ EID ⇝ EID
Eid∀-⊢ = conv-all Eid↦Eid-⊢

Earg-⊢ : ∀ {Γ Δ} → Γ ∣ Δ ⊢ Earg ⦂ EID
Earg-⊢ = ⊢Λ (⊢ƛ (wf-var (_ , here)) (⊢` here))

Efun-⊢ : empty ∣ [] ⊢ Efun ⦂ `∀ EBod
Efun-⊢ =
  ⊢Λ (⊢ƛ wf-EID
    (⊢Λ (⊢·[] (⊢` here) (wf-var (_ , here)))))

E₀-⊢ : empty ∣ [] ⊢ E₀ ⦂ EID
E₀-⊢ = ⊢· (⊢·[] Efun-⊢ wf-ℕ) Earg-⊢

E₁-⊢ : empty ∣ [] ⊢ E₁ ⦂ EID
E₁-⊢ = ⊢· wrapped Earg-⊢
  where
  wrapped : empty ∣ [] ⊢
    (ƛ EID ∙ Ebody) ⟪ TyBetaMorph , Eid∀ ↦ Eid∀ ⟫ ⦂ EBod
  wrapped =
    env TyBeta-mw
      (⊢ƛ wf-EID
        (⊢Λ (⊢·[] (⊢` here) (wf-var (_ , here)))))
      (conv-fun Eid∀-⊢ Eid∀-⊢)
      (EBod
        , same-⇒
            (same-∀ (same-⇒ (same-var here) (same-var here)))
            (same-∀ (same-⇒ (same-var here) (same-var here)))
        , same-⇒
            (same-∀ (same-⇒ (same-var here) (same-var here)))
            (same-∀ (same-⇒ (same-var here) (same-var here))))
      (EBod
        , same-⇒
            (same-∀ (same-⇒ (same-var here) (same-var here)))
            (same-∀ (same-⇒ (same-var here) (same-var here)))
        , same-⇒
            (same-∀ (same-⇒ (same-var here) (same-var here)))
            (same-∀ (same-⇒ (same-var here) (same-var here))))
      (wf-⇒ wf-EID wf-EID)

EW-⊢ : ∀ {Γ} → Δℕ ∣ Γ ⊢ EW ⦂ EID
EW-⊢ =
  env Θℕ-dual-mw Earg-⊢ (Eid∀-⊢ { Γ = Δℕ })
    (same-EID { Γ = Δℕ-lock } { Γ′ = Δℕ })
    (same-EID { Γ = Δℕ } { Γ′ = Δℕ }) wf-EID

E₂-⊢ : empty ∣ [] ⊢ E₂ ⦂ EID
E₂-⊢ =
  env TyBeta-mw
    (⊢·
      (⊢ƛ wf-EID
        (⊢Λ (⊢·[] (⊢` here) (wf-var (_ , here)))))
      EW-⊢)
    (Eid∀-⊢ { Γ = Δℕ })
    (same-EID { Γ = Δℕ } { Γ′ = Δℕ })
    (sameExt-EID₁ { Γ = empty } { Γ′ = Δℕ }) wf-EID

EW-cross-⊢ : ∀ {Γ} → ΔE ∣ Γ ⊢ EW-cross ⦂ EID
EW-cross-⊢ =
  env ΘE-Y-mw
    (env ΘE-X-mw Earg-⊢ (Eid∀-⊢ { Γ = ΔE-Y-int })
      (same-EID { Γ = ΔE-none } { Γ′ = ΔE-Y-int })
      (same-EID { Γ = ΔE-Y-int } { Γ′ = ΔE-Y-int }) wf-EID)
    (Eid∀-⊢ { Γ = ΔE })
    (same-EID { Γ = ΔE-Y-int } { Γ′ = ΔE })
    (same-EID { Γ = ΔE } { Γ′ = ΔE }) wf-EID

E₃-⊢ : empty ∣ [] ⊢ E₃ ⦂ EID
E₃-⊢ =
  env TyBeta-mw
    (⊢Λ (⊢·[] EW-cross-⊢ (wf-var (_ , here))))
    (Eid∀-⊢ { Γ = Δℕ })
    (same-EID { Γ = Δℕ } { Γ′ = Δℕ })
    (sameExt-EID₁ { Γ = empty } { Γ′ = Δℕ }) wf-EID

lookup-EYI0 : ΔE-YI-conv ∋ 0 := ` 1
lookup-EYI0 = 0 , ` 1 , here , r-here , same-var (there here)

lookup-EZ0 : ΔE-Z-conv ∋ 0 := ` 1
lookup-EZ0 = 0 , ` 1 , here , r-here , same-var (there here)

Emoved-⊢ : ΔE-YI-int ∣ [] ⊢ Earg ⟪ ΘE-moved , Eid∀ ⟫ ⦂ EID
Emoved-⊢ =
  env ΘE-moved-mw Earg-⊢ (Eid∀-⊢ { Γ = ΔE-YI-int })
    (same-EID { Γ = ΔE-moved-int } { Γ′ = ΔE-YI-int })
    (same-EID { Γ = ΔE-YI-int } { Γ′ = ΔE-YI-int }) wf-EID

same-E00 : SameTy ΔE-YI-int (` 0 ⇒ ` 0)
  ΔE-YI-conv (` 0 ⇒ ` 0)
same-E00 =
  ` 0 ⇒ ` 0 , same-⇒ (same-var here) (same-var here)
                  , same-⇒ (same-var here) (same-var here)

sameExt-E01 : SameTyExt 1 ΔE (` 0 ⇒ ` 0)
  ΔE-YI-conv (` 1 ⇒ ` 1)
sameExt-E01 =
  ` 0 ⇒ ` 0 , same-⇒ (same-var here) (same-var here)
                  , same-⇒ (same-var (there here))
                                (same-var (there here))

E₄-inner-⊢ : ΔE ∣ [] ⊢
  ((Earg ⟪ ΘE-moved , Eid∀ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ])
    ⟪ ΘE-Y-inst , seal 0 ↦ unseal 0 ⟫ ⦂ (` 0 ⇒ ` 0)
E₄-inner-⊢ =
  env ΘE-Y-inst-mw
    (⊢·[] Emoved-⊢ (wf-var (_ , here)))
    (conv-fun (conv-seal lookup-EYI0) (conv-unseal lookup-EYI0))
    same-E00 sameExt-E01
    (wf-⇒ (wf-var (_ , here)) (wf-var (_ , here)))

E₄-⊢ : empty ∣ [] ⊢ E₄ ⦂ EID
E₄-⊢ =
  env TyBeta-mw (⊢Λ E₄-inner-⊢)
    (Eid∀-⊢ { Γ = Δℕ })
    (same-EID { Γ = Δℕ } { Γ′ = Δℕ })
    (sameExt-EID₁ { Γ = empty } { Γ′ = Δℕ }) wf-EID

same-EZ00 : SameTy ΔE-Z-int (` 0 ⇒ ` 0)
  ΔE-Z-conv (` 0 ⇒ ` 0)
same-EZ00 =
  ` 0 ⇒ ` 0 , same-⇒ (same-var here) (same-var here)
                  , same-⇒ (same-var here) (same-var here)

sameExt-EZ01 : SameTyExt 1 ΔE-YI-int (` 0 ⇒ ` 0)
  ΔE-Z-conv (` 1 ⇒ ` 1)
sameExt-EZ01 =
  ` 0 ⇒ ` 0 , same-⇒ (same-var here) (same-var here)
                  , same-⇒ (same-var (there here))
                                (same-var (there here))

E₅-head-⊢ : ΔE-YI-int ∣ [] ⊢
  (ƛ ` 0 ∙ ` 0) ⟪ ΘE-Z-inst , seal 0 ↦ unseal 0 ⟫
    ⦂ (` 0 ⇒ ` 0)
E₅-head-⊢ =
  env ΘE-Z-inst-mw
    (⊢ƛ (wf-var (_ , here)) (⊢` here))
    (conv-fun (conv-seal lookup-EZ0) (conv-unseal lookup-EZ0))
    same-EZ00 sameExt-EZ01
    (wf-⇒ (wf-var (_ , here)) (wf-var (_ , here)))

E₅-inner-⊢ : ΔE ∣ [] ⊢
  E₅-head ⟪ ΘE-Y-inst , seal 0 ↦ unseal 0 ⟫ ⦂ (` 0 ⇒ ` 0)
E₅-inner-⊢ =
  env ΘE-Y-inst-mw E₅-head-⊢
    (conv-fun (conv-seal lookup-EYI0) (conv-unseal lookup-EYI0))
    same-E00 sameExt-E01
    (wf-⇒ (wf-var (_ , here)) (wf-var (_ , here)))

E₅-⊢ : empty ∣ [] ⊢ E₅ ⦂ EID
E₅-⊢ =
  env TyBeta-mw (⊢Λ E₅-inner-⊢)
    (Eid∀-⊢ { Γ = Δℕ })
    (same-EID { Γ = Δℕ } { Γ′ = Δℕ })
    (sameExt-EID₁ { Γ = empty } { Γ′ = Δℕ }) wf-EID

E-step₀ : empty ⊢ E₀ -→ E₁
E-step₀ = ξ-·-l (TyBeta V-ƛ same-ℕ)

E-step₁ : empty ⊢ E₁ -→ E₂
E-step₁ = Peel V-ƛ (V-Λ V-ƛ)

E-step₂ : empty ⊢ E₂ -→ E₃
E-step₂ =
  ξ-⟪⟫ TyBeta-interior
    (Beta (V-⟪⟫ (V-Λ V-ƛ) I-all))

E-step₃ : empty ⊢ E₃ -→ E₄
E-step₃ =
  ξ-⟪⟫ TyBeta-interior
    (ξ-Λ
      (TyPeelR-⟪⟫ (V-Λ V-ƛ)
        (mw-conversion ΘE-Y-mw)
        unique-underΛΔE Eid↦Eid-⊢ (same-var here)))

E-step₄ : empty ⊢ E₄ -→ E₅
E-step₄ =
  ξ-⟪⟫ TyBeta-interior
    (ξ-Λ
      (ξ-⟪⟫ (ΘE-Y-inst-interior)
        (TyPeelR-Λ V-ƛ
          (mw-conversion ΘE-moved-mw)
          unique-underΛΔE-moved Eid↦Eid-⊢
          (same-var here))))

E₀ᴮ E₁ᴮ E₂ᴮ E₃ᴮ E₄ᴮ E₅ᴮ : Term
E₀ᴮ = (E₀ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₁ᴮ = (E₁ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₂ᴮ = (E₂ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₃ᴮ = (E₃ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₄ᴮ = (E₄ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₅ᴮ = (E₅ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true

E₀ᴮ-⊢ : empty ∣ [] ⊢ E₀ᴮ ⦂ `𝔹
E₀ᴮ-⊢ = ⊢· (⊢·[] E₀-⊢ wf-𝔹) ⊢true

E₁ᴮ-⊢ : empty ∣ [] ⊢ E₁ᴮ ⦂ `𝔹
E₁ᴮ-⊢ = ⊢· (⊢·[] E₁-⊢ wf-𝔹) ⊢true

E₂ᴮ-⊢ : empty ∣ [] ⊢ E₂ᴮ ⦂ `𝔹
E₂ᴮ-⊢ = ⊢· (⊢·[] E₂-⊢ wf-𝔹) ⊢true

E₃ᴮ-⊢ : empty ∣ [] ⊢ E₃ᴮ ⦂ `𝔹
E₃ᴮ-⊢ = ⊢· (⊢·[] E₃-⊢ wf-𝔹) ⊢true

E₄ᴮ-⊢ : empty ∣ [] ⊢ E₄ᴮ ⦂ `𝔹
E₄ᴮ-⊢ = ⊢· (⊢·[] E₄-⊢ wf-𝔹) ⊢true

E₅ᴮ-⊢ : empty ∣ [] ⊢ E₅ᴮ ⦂ `𝔹
E₅ᴮ-⊢ = ⊢· (⊢·[] E₅-⊢ wf-𝔹) ⊢true

Eᴮ-step₀ : empty ⊢ E₀ᴮ -→ E₁ᴮ
Eᴮ-step₀ = ξ-·-l (ξ-·[] E-step₀)

Eᴮ-step₁ : empty ⊢ E₁ᴮ -→ E₂ᴮ
Eᴮ-step₁ = ξ-·-l (ξ-·[] E-step₁)

Eᴮ-step₂ : empty ⊢ E₂ᴮ -→ E₃ᴮ
Eᴮ-step₂ = ξ-·-l (ξ-·[] E-step₂)

Eᴮ-step₃ : empty ⊢ E₃ᴮ -→ E₄ᴮ
Eᴮ-step₃ = ξ-·-l (ξ-·[] E-step₃)

Eᴮ-step₄ : empty ⊢ E₄ᴮ -→ E₅ᴮ
Eᴮ-step₄ = ξ-·-l (ξ-·[] E-step₄)

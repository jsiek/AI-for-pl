module strong.notes.RepresentationReductionExamples where

-- Executable reduction checks for the representation-variable experiment.
-- Every displayed state has a typing derivation and every edge is a
-- derivation of strong.Reduction._⊢_-→_.
--
-- The typing derivations are the ORDINARY ones, built by the checker in
-- strong.TypeCheck: `tc` is `env`/`⊢·`/`⊢Λ`/… applied to the premises the
-- checker found, and it typechecks only against the type written beside
-- it.  What a state's derivation DOCUMENTS is therefore its type, which is
-- what a reader wants; what it used to document as well was every
-- `SameTy` reading and every change of every frame, which the terms below
-- already fix.  The reduction steps stay written out, because the rule and
-- the value premises at each edge are the content of the test.
--
--   polymorphic identity       6 steps   value 7     : ℕ
--   polymorphic Boolean use    9 steps   value true  : 𝔹
--   polymorphic constant 3    11 steps   value 3     : ℕ
--   later-bound identity      25 steps   value true  : 𝔹
--
-- The fourth run is the one that pins the design down.  Its argument is a
-- polymorphic identity handed to a function that instantiates it BENEATH A
-- LATER `Λ`, so the value that finally reaches `true` has crossed three
-- boundaries and carries three seals, and unwinding them drives `CancelR`
-- and `IdPush` through frames that are COMPOSITES (`_⋉_`, `rewind`).
-- Finishing it found a defect in the conversion context of exactly those
-- composites and forced the re-unlock clause of `_∣_⊢χᶜ_⇒_`
-- (strong.CtxMorph §3); the wall and its repair are recorded at the end of
-- §4 below.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.TypeCheck
open import strong.Eval using (eval; evalTerms; traceEnd; eval-⦂)

------------------------------------------------------------------------
-- Shared ℕ-instantiation frames
------------------------------------------------------------------------

Δℕ Δℕ-lock : Ctxᵗ
Δℕ = TyBetaCtx
Δℕ-lock = (bindR `ℕ ∷ []) ∣ []

Θℕ-dual Θℕ-cancel Θℕ-rewind : CtxMorph
Θℕ-dual = dualMorph TyBetaMorph
Θℕ-cancel = Θℕ-dual ⋉ TyBetaMorph
Θℕ-rewind = rewind TyBetaMorph

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
P₁₀-⊢ = tc

P₁₁-⊢ : empty ∣ [] ⊢ P₁₁ ⦂ `ℕ
P₁₁-⊢ = tc

P₁₂-⊢ : empty ∣ [] ⊢ P₁₂ ⦂ `ℕ
P₁₂-⊢ = tc

P₁₃-⊢ : empty ∣ [] ⊢ P₁₃ ⦂ `ℕ
P₁₃-⊢ = tc

cancel-seven-⊢ : Δℕ-lock ∣ []
  ⊢ ($ 7) ⟪ Θℕ-cancel , id `ℕ ⟫ ⦂ `ℕ
cancel-seven-⊢ = tc

P₁₄-⊢ : empty ∣ [] ⊢ P₁₄ ⦂ `ℕ
P₁₄-⊢ = tc

P₁₅-⊢ : empty ∣ [] ⊢ P₁₅ ⦂ `ℕ
P₁₅-⊢ = tc

P₁₆-⊢ : empty ∣ [] ⊢ P₁₆ ⦂ `ℕ
P₁₆-⊢ = tc

P₁-step₀ : empty ⊢ P₁₀ -→ P₁₁
P₁-step₀ = ξ-·-l (TyBeta V-ƛ same-ℕ)

P₁-step₁ : empty ⊢ P₁₁ -→ P₁₂
P₁-step₁ = Peel V-ƛ V-$

P₁-step₂ : empty ⊢ P₁₂ -→ P₁₃
P₁-step₂ =
  ξ-⟪⟫ TyBeta-interior (Beta (V-⟪⟫ V-$ I-seal))

P₁-step₃ : empty ⊢ P₁₃ -→ P₁₄
P₁-step₃ =
  CancelR V-$ TyBeta-conversion tu (proj₂ (sq! Δℕ 0))

P₁-step₄ : empty ⊢ P₁₄ -→ P₁₅
P₁-step₄ = ξ-⟪⟫ (proj₂ (int! empty Θℕ-rewind)) (Drop$ base-ℕ)

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

stℕ : Conv
stℕ = id (` 0) ↦ seal 1

stℕ-⊢ : underΛ Δℕ ⊢ stℕ ∶ (` 0 ⇒ `ℕ) ⇝ (` 0 ⇒ ` 1)
stℕ-⊢ = tk

JT : Ty
JT = `∀ (` 0 ⇒ ` 1)

------------------------------------------------------------------------
-- 3. ((ΛX. λx:X. λf:(∀Y. Y⇒X). f[X]·x) [ℕ]) · 7 · const3
------------------------------------------------------------------------

JB : Ty
JB = ` 0 ⇒ (JT ⇒ ` 0)

Jbody Jfun : Term
Jbody = ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) · ` 1)
Jfun = Λ (ƛ ` 0 ∙ Jbody)

J₀ : Term
J₀ = ((Jfun ·[ JB , `ℕ ]) · $ 7) · const3

J₀-⊢ : empty ∣ [] ⊢ J₀ ⦂ `ℕ
J₀-⊢ = tc

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
        (proj₂ (conv! Δℕ Θℕ-dual))
        tu
        stℕ-⊢
        (same-var here)))

JTarget : Ty
JTarget = `ℕ ⇒ (const3Ty ⇒ `ℕ)

Jmint-⊢ : Δℕ ⊢ Jmint ∶ JB ⇝ JTarget
Jmint-⊢ = tk

Jbody-Δℕ-⊢ : Δℕ ∣ (` 0 ∷ []) ⊢ Jbody ⦂ (JT ⇒ ` 0)
Jbody-Δℕ-⊢ = tc

J₁-⊢ : empty ∣ [] ⊢ J₁ ⦂ `ℕ
J₁-⊢ = tc

J₂-⊢ : empty ∣ [] ⊢ J₂ ⦂ `ℕ
J₂-⊢ = tc

J₃-inner-⊢ : Δℕ ∣ [] ⊢
  ƛ JT ∙ (((` 0) ·[ ` 0 ⇒ ` 1 , ` 0 ]) ·
            (($ 7) ⟪ Θℕ-dual , seal 0 ⟫))
    ⦂ (JT ⇒ ` 0)
J₃-inner-⊢ = tc

J₃-⊢ : empty ∣ [] ⊢ J₃ ⦂ `ℕ
J₃-⊢ = tc

J₄-⊢ : empty ∣ [] ⊢ J₄ ⦂ `ℕ
J₄-⊢ = tc

J₅-⊢ : empty ∣ [] ⊢ J₅ ⦂ `ℕ
J₅-⊢ = tc

ΔJ-int ΔJ-conv : Ctxᵗ
ΔJ-int = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ [])
ΔJ-conv = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

J₆head-⊢ : Δℕ ∣ [] ⊢ J₆head ⦂ (` 0 ⇒ ` 0)
J₆head-⊢ = tc

J₆-⊢ : empty ∣ [] ⊢ J₆ ⦂ `ℕ
J₆-⊢ = tc

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
    (ξ-⟪⟫ (proj₂ (int! Δℕ (instantiate (` 0) Θℕ-dual))) (Beta Jarg-value))

J-step₈ : empty ⊢ J₈ -→ J₉
J-step₈ =
  CancelR V-$ TyBeta-conversion tu (proj₂ (sq! Δℕ 0))

J-step₉ : empty ⊢ J₉ -→ J₁₀
J-step₉ = ξ-⟪⟫ (proj₂ (int! empty Θℕ-rewind)) (Drop$ base-ℕ)

J-step₁₀ : empty ⊢ J₁₀ -→ $ 3
J-step₁₀ = Drop$ base-ℕ

ΔJ-arg-int ΔJ-none : Ctxᵗ
ΔJ-arg-int = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ (1 ∷ [])
ΔJ-none = (bindR (` 0) ∷ bindR `ℕ ∷ []) ∣ []

Jshift-⊢ : ΔJ-arg-int ∣ [] ⊢ Jshift ⦂ ` 0
Jshift-⊢ = tc

Jarg-⊢ : ΔJ-int ∣ [] ⊢ Jarg ⦂ ` 0
Jarg-⊢ = tc

J₇-inner-⊢ : Δℕ ∣ []
  ⊢ ((ƛ ` 0 ∙ $ 3) · Jarg) ⟪ ΘJ , seal 1 ⟫ ⦂ ` 0
J₇-inner-⊢ = tc

J₇-⊢ : empty ∣ [] ⊢ J₇ ⦂ `ℕ
J₇-⊢ = tc

J₈-inner-⊢ : Δℕ ∣ [] ⊢ ($ 3) ⟪ ΘJ , seal 1 ⟫ ⦂ ` 0
J₈-inner-⊢ = tc

J₈-⊢ : empty ∣ [] ⊢ J₈ ⦂ `ℕ
J₈-⊢ = tc

J₉-inner-⊢ : Δℕ-lock ∣ []
  ⊢ ($ 3) ⟪ ΘJ-cancel , id `ℕ ⟫ ⦂ `ℕ
J₉-inner-⊢ = tc

J₉-⊢ : empty ∣ [] ⊢ J₉ ⦂ `ℕ
J₉-⊢ = tc

J₁₀-⊢ : empty ∣ [] ⊢ J₁₀ ⦂ `ℕ
J₁₀-⊢ = tc

J-final-⊢ : empty ∣ [] ⊢ $ 3 ⦂ `ℕ
J-final-⊢ = tc

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

Θ𝔹 Θ𝔹-dual Θ𝔹-rewind : CtxMorph
Θ𝔹 = morph (`𝔹 ∷ []) (unlock 0 0 ∷ [])
Θ𝔹-dual = morph [] (lock 0 0 ∷ [])
Θ𝔹-rewind =
  morph (`𝔹 ∷ []) (lock 0 0 ∷ unlock 0 0 ∷ [])

GT : Ty
GT = `∀ (` 0 ⇒ `𝔹)

truePoly : Term
truePoly = Λ (ƛ ` 0 ∙ `true)

st𝔹 : Conv
st𝔹 = id (` 0) ↦ id `𝔹

st𝔹-⊢ : underΛ Δ𝔹 ⊢ st𝔹 ∶ (` 0 ⇒ `𝔹) ⇝ (` 0 ⇒ `𝔹)
st𝔹-⊢ = tk

FB : Ty
FB = GT ⇒ (` 0 ⇒ `𝔹)

Fbody Ffun : Term
Fbody = ƛ GT ∙ ((` 0) ·[ ` 0 ⇒ `𝔹 , ` 0 ])
Ffun = Λ Fbody

K₀ : Term
K₀ = ((Ffun ·[ FB , `𝔹 ]) · truePoly) · `false

K₀-⊢ : empty ∣ [] ⊢ K₀ ⦂ `𝔹
K₀-⊢ = tc

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

K-step₀ : empty ⊢ K₀ -→ K₁
K-step₀ = ξ-·-l (ξ-·-l (TyBeta V-ƛ same-𝔹))

K-step₁ : empty ⊢ K₁ -→ K₂
K-step₁ = ξ-·-l (Peel V-ƛ (V-Λ V-ƛ))

K-step₂ : empty ⊢ K₂ -→ K₃
K-step₂ =
  ξ-·-l
    (ξ-⟪⟫ (proj₂ (int! empty Θ𝔹))
      (Beta (V-⟪⟫ (V-Λ V-ƛ) I-all)))

K-step₃ : empty ⊢ K₃ -→ K₄
K-step₃ =
  ξ-·-l
    (ξ-⟪⟫ (proj₂ (int! empty Θ𝔹))
      (TyPeelR-Λ V-ƛ
        (proj₂ (conv! Δ𝔹 Θ𝔹-dual))
        tu st𝔹-⊢ (same-var here)))

K-step₄ : empty ⊢ K₄ -→ K₅
K-step₄ = Peel (V-⟪⟫ V-ƛ I-fun) V-false

K-step₅ : empty ⊢ K₅ -→ K₆
K-step₅ =
  ξ-⟪⟫ (proj₂ (int! empty Θ𝔹))
    (Peel V-ƛ (V-⟪⟫ V-false I-seal))

Karg-value : Value Karg
Karg-value = V-⟪⟫ (V-⟪⟫ V-false I-seal) I-seal

K-step₆ : empty ⊢ K₆ -→ K₇
K-step₆ =
  ξ-⟪⟫ (proj₂ (int! empty Θ𝔹))
    (ξ-⟪⟫ (proj₂ (int! Δ𝔹 ΘK)) (Beta Karg-value))

K-step₇ : empty ⊢ K₇ -→ K₈
K-step₇ =
  ξ-⟪⟫ (proj₂ (int! empty Θ𝔹)) Drop-true

K-step₈ : empty ⊢ K₈ -→ `true
K-step₈ = Drop-true

KTarget : Ty
KTarget = GT ⇒ (`𝔹 ⇒ `𝔹)

Kmint-⊢ : Δ𝔹 ⊢ Kmint ∶ FB ⇝ KTarget
Kmint-⊢ = tk

Fbody-Δ𝔹-⊢ : Δ𝔹 ∣ [] ⊢ Fbody ⦂ (GT ⇒ (` 0 ⇒ `𝔹))
Fbody-Δ𝔹-⊢ = tc

K₁-⊢ : empty ∣ [] ⊢ K₁ ⦂ `𝔹
K₁-⊢ = tc

K₂-⊢ : empty ∣ [] ⊢ K₂ ⦂ `𝔹
K₂-⊢ = tc

K₃-⊢ : empty ∣ [] ⊢ K₃ ⦂ `𝔹
K₃-⊢ = tc

Khead-⊢ : Δ𝔹 ∣ [] ⊢ Khead ⦂ (` 0 ⇒ `𝔹)
Khead-⊢ = tc

K₄-⊢ : empty ∣ [] ⊢ K₄ ⦂ `𝔹
K₄-⊢ = tc

K₅-⊢ : empty ∣ [] ⊢ K₅ ⦂ `𝔹
K₅-⊢ = tc

ΔK-arg-int ΔK-none : Ctxᵗ
ΔK-arg-int = (bindR (` 0) ∷ bindR `𝔹 ∷ []) ∣ (1 ∷ [])
ΔK-none = (bindR (` 0) ∷ bindR `𝔹 ∷ []) ∣ []

Kshift-⊢ : ΔK-arg-int ∣ []
  ⊢ renᴹ² (ren² idᵗ (wkN (numBinds ΘK))) Kfalse ⦂ ` 0
Kshift-⊢ = tc

Karg-⊢ : ΔK-int ∣ [] ⊢ Karg ⦂ ` 0
Karg-⊢ = tc

K₆-inner-⊢ : Δ𝔹 ∣ []
  ⊢ ((ƛ ` 0 ∙ `true) · Karg) ⟪ ΘK , id `𝔹 ⟫ ⦂ `𝔹
K₆-inner-⊢ = tc

K₆-⊢ : empty ∣ [] ⊢ K₆ ⦂ `𝔹
K₆-⊢ = tc

K₇-inner-⊢ : Δ𝔹 ∣ [] ⊢ `true ⟪ ΘK , id `𝔹 ⟫ ⦂ `𝔹
K₇-inner-⊢ = tc

K₇-⊢ : empty ∣ [] ⊢ K₇ ⦂ `𝔹
K₇-⊢ = tc

K₈-⊢ : empty ∣ [] ⊢ K₈ ⦂ `𝔹
K₈-⊢ = tc

K-final-⊢ : empty ∣ [] ⊢ `true ⦂ `𝔹
K-final-⊢ = tc

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

ΘE-Y-inst-interior : ΔE ⊢ⁱ ΘE-Y-inst ⇒ ΔE-YI-int
ΘE-Y-inst-interior = proj₂ (int! ΔE ΘE-Y-inst)

Eid↦Eid-⊢ : ∀ {Γ} → underΛ Γ ⊢ id (` 0) ↦ id (` 0)
  ∶ (` 0 ⇒ ` 0) ⇝ (` 0 ⇒ ` 0)
Eid↦Eid-⊢ =
  conv-fun (conv-idv (_ , here)) (conv-idv (_ , here))

E₀-⊢ : empty ∣ [] ⊢ E₀ ⦂ EID
E₀-⊢ = tc

E₁-⊢ : empty ∣ [] ⊢ E₁ ⦂ EID
E₁-⊢ = tc

E₂-⊢ : empty ∣ [] ⊢ E₂ ⦂ EID
E₂-⊢ = tc

E₃-⊢ : empty ∣ [] ⊢ E₃ ⦂ EID
E₃-⊢ = tc

E₄-⊢ : empty ∣ [] ⊢ E₄ ⦂ EID
E₄-⊢ = tc

E₅-head-⊢ : ΔE-YI-int ∣ [] ⊢
  (ƛ ` 0 ∙ ` 0) ⟪ ΘE-Z-inst , seal 0 ↦ unseal 0 ⟫
    ⦂ (` 0 ⇒ ` 0)
E₅-head-⊢ = tc

E₅-inner-⊢ : ΔE ∣ [] ⊢
  E₅-head ⟪ ΘE-Y-inst , seal 0 ↦ unseal 0 ⟫ ⦂ (` 0 ⇒ ` 0)
E₅-inner-⊢ = tc

E₅-⊢ : empty ∣ [] ⊢ E₅ ⦂ EID
E₅-⊢ = tc

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
        (proj₂ (conv! ΔE ΘE-Y))
        tu Eid↦Eid-⊢ (same-var here)))

E-step₄ : empty ⊢ E₄ -→ E₅
E-step₄ =
  ξ-⟪⟫ TyBeta-interior
    (ξ-Λ
      (ξ-⟪⟫ (ΘE-Y-inst-interior)
        (TyPeelR-Λ V-ƛ
          (proj₂ (conv! ΔE-YI-int ΘE-moved))
          tu Eid↦Eid-⊢
          (same-var here))))

E₀ᴮ E₁ᴮ E₂ᴮ E₃ᴮ E₄ᴮ E₅ᴮ : Term
E₀ᴮ = (E₀ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₁ᴮ = (E₁ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₂ᴮ = (E₂ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₃ᴮ = (E₃ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₄ᴮ = (E₄ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true
E₅ᴮ = (E₅ ·[ ` 0 ⇒ ` 0 , `𝔹 ]) · `true

E₀ᴮ-⊢ : empty ∣ [] ⊢ E₀ᴮ ⦂ `𝔹
E₀ᴮ-⊢ = tc

E₁ᴮ-⊢ : empty ∣ [] ⊢ E₁ᴮ ⦂ `𝔹
E₁ᴮ-⊢ = tc

E₂ᴮ-⊢ : empty ∣ [] ⊢ E₂ᴮ ⦂ `𝔹
E₂ᴮ-⊢ = tc

E₃ᴮ-⊢ : empty ∣ [] ⊢ E₃ᴮ ⦂ `𝔹
E₃ᴮ-⊢ = tc

E₄ᴮ-⊢ : empty ∣ [] ⊢ E₄ᴮ ⦂ `𝔹
E₄ᴮ-⊢ = tc

E₅ᴮ-⊢ : empty ∣ [] ⊢ E₅ᴮ ⦂ `𝔹
E₅ᴮ-⊢ = tc

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

------------------------------------------------------------------------
-- 4 (continued). The later-bound identity, instantiated and run to `true`
--
-- The frames below are COMPOSITES: `CancelR` and `IdPush` replace their
-- two frames by `Θ₁ ⋉ Θ₂` and `rewind Θ₂`, whose change lists are the
-- concatenations of their arguments', so the last ones in this run carry
-- tens of changes each.  That is what made the checker necessary — and
-- what broke the conversion context, which the end of this section
-- records.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- the three live frames and the contexts they induce
------------------------------------------------------------------------

Θa Θb Θc : CtxMorph
Θa = instantiate `𝔹 TyBetaMorph
Θb = ΘE-Y-inst
Θc = ΘE-Z-inst

Θa-explicit : Θa ≡ morph (`𝔹 ∷ `ℕ ∷ []) (unlock 1 1 ∷ unlock 0 0 ∷ [])
Θa-explicit = refl

repsA repsB repsC : RepCtx
repsA = bindR `𝔹 ∷ bindR `ℕ ∷ []
repsB = bindR (` 0) ∷ repsA
repsC = bindR (` 0) ∷ repsB

Δa Δa-none : Ctxᵗ
Δa = repsA ∣ (0 ∷ 1 ∷ [])
Δa-none = repsA ∣ []

Δb-int Δb-conv Δb-arg Δb-none : Ctxᵗ
Δb-int = repsB ∣ (0 ∷ 2 ∷ [])
Δb-conv = repsB ∣ (0 ∷ 1 ∷ 2 ∷ [])
Δb-arg = repsB ∣ (1 ∷ 2 ∷ [])
Δb-none = repsB ∣ []

Δc-int Δc-conv Δc-arg Δc-mid Δc-in Δc-none Δc-full : Ctxᵗ
Δc-int = repsC ∣ (0 ∷ [])
Δc-conv = repsC ∣ (0 ∷ 1 ∷ 3 ∷ [])
Δc-arg = repsC ∣ (1 ∷ 3 ∷ [])
Δc-mid = repsC ∣ (1 ∷ 2 ∷ 3 ∷ [])
Δc-in = repsC ∣ (2 ∷ 3 ∷ [])
Δc-none = repsC ∣ []
Δc-full = repsC ∣ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])

------------------------------------------------------------------------
-- E₅ᴮ instantiates: TyPeelR-Λ
------------------------------------------------------------------------

sc : Conv
sc = seal 0 ↦ unseal 0

U H G E₆ E₆ᴮ : Term
U = ƛ ` 0 ∙ ` 0
H = U ⟪ Θc , sc ⟫
G = H ⟪ Θb , sc ⟫
E₆ = G ⟪ Θa , sc ⟫
E₆ᴮ = E₆ · `true

Eᴮ-step₅ : empty ⊢ E₅ᴮ -→ E₆ᴮ
Eᴮ-step₅ =
  ξ-·-l
    (TyPeelR-Λ (V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun)
      TyBeta-conversion tu
      (Eid↦Eid-⊢ { Γ = Δℕ }) same-𝔹)

U-⊢ : Δc-int ∣ [] ⊢ U ⦂ (` 0 ⇒ ` 0)
U-⊢ = tc

H-⊢ : Δb-int ∣ [] ⊢ H ⦂ (` 0 ⇒ ` 0)
H-⊢ = tc

G-⊢ : Δa ∣ [] ⊢ G ⦂ (` 0 ⇒ ` 0)
G-⊢ = tc

E₆-⊢ : empty ∣ [] ⊢ E₆ ⦂ (`𝔹 ⇒ `𝔹)
E₆-⊢ = tc

E₆ᴮ-⊢ : empty ∣ [] ⊢ E₆ᴮ ⦂ `𝔹
E₆ᴮ-⊢ = tc

------------------------------------------------------------------------
-- the three Peels and the Beta
------------------------------------------------------------------------

A₁ A₂ A₃ : Term
A₁ = renᴹ² (ren² idᵗ (wkN (numBinds Θa))) `true ⟪ dualMorph Θa , seal 0 ⟫
A₂ = renᴹ² (ren² idᵗ (wkN (numBinds Θb))) A₁ ⟪ dualMorph Θb , seal 0 ⟫
A₃ = renᴹ² (ren² idᵗ (wkN (numBinds Θc))) A₂ ⟪ dualMorph Θc , seal 0 ⟫

A₁-explicit : A₁ ≡ `true ⟪ morph [] (lock 0 0 ∷ lock 1 1 ∷ []) , seal 0 ⟫
A₁-explicit = refl

A₂-explicit : A₂ ≡
  (`true ⟪ morph [] (lock 0 1 ∷ lock 1 2 ∷ []) , seal 0 ⟫)
    ⟪ morph [] (lock 0 0 ∷ unlock 1 1 ∷ []) , seal 0 ⟫
A₂-explicit = refl

A₃-explicit : A₃ ≡
  ((`true ⟪ morph [] (lock 0 2 ∷ lock 1 3 ∷ []) , seal 0 ⟫)
     ⟪ morph [] (lock 0 1 ∷ unlock 1 2 ∷ []) , seal 0 ⟫)
    ⟪ morph [] (lock 0 0 ∷ unlock 1 1 ∷ unlock 1 3 ∷ []) , seal 0 ⟫
A₃-explicit = refl

Σi Σo : CtxMorph
Σi = morph [] (lock 0 2 ∷ lock 1 3 ∷ [])
Σo = morph [] (lock 0 1 ∷ unlock 1 2 ∷ [])

A₂in A₂shift : Term
A₂in = `true ⟪ Σi , seal 0 ⟫
A₂shift = A₂in ⟪ Σo , seal 0 ⟫

A₂shift-explicit :
  renᴹ² (ren² idᵗ (wkN (numBinds Θc))) A₂ ≡ A₂shift
A₂shift-explicit = refl

E₇ E₈ E₉ E₁₀ : Term
E₇ = (G · A₁) ⟪ Θa , unseal 0 ⟫
E₈ = ((H · A₂) ⟪ Θb , unseal 0 ⟫) ⟪ Θa , unseal 0 ⟫
E₉ = (((U · A₃) ⟪ Θc , unseal 0 ⟫) ⟪ Θb , unseal 0 ⟫)
       ⟪ Θa , unseal 0 ⟫
E₁₀ = ((A₃ ⟪ Θc , unseal 0 ⟫) ⟪ Θb , unseal 0 ⟫) ⟪ Θa , unseal 0 ⟫

Eᴮ-step₆ : empty ⊢ E₆ᴮ -→ E₇
Eᴮ-step₆ = Peel (V-⟪⟫ (V-⟪⟫ V-ƛ I-fun) I-fun) V-true

Eᴮ-step₇ : empty ⊢ E₇ -→ E₈
Eᴮ-step₇ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (Peel (V-⟪⟫ V-ƛ I-fun) (V-⟪⟫ V-true I-seal))

Eᴮ-step₈ : empty ⊢ E₈ -→ E₉
Eᴮ-step₈ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (ξ-⟪⟫ (proj₂ (int! Δa Θb))
      (Peel V-ƛ (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-seal)))

Eᴮ-step₉ : empty ⊢ E₉ -→ E₁₀
Eᴮ-step₉ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (ξ-⟪⟫ (proj₂ (int! Δa Θb))
      (ξ-⟪⟫ (proj₂ (int! Δb-int Θc))
        (Beta (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-seal) I-seal))))

A₁-⊢ : Δa ∣ [] ⊢ A₁ ⦂ ` 0
A₁-⊢ = tc

A₁shift-⊢ : Δb-arg ∣ []
  ⊢ renᴹ² (ren² idᵗ (wkN (numBinds Θb))) A₁ ⦂ ` 0
A₁shift-⊢ = tc

A₂-⊢ : Δb-int ∣ [] ⊢ A₂ ⦂ ` 0
A₂-⊢ = tc

A₂in-⊢ : Δc-in ∣ [] ⊢ A₂in ⦂ ` 0
A₂in-⊢ = tc

A₂shift-⊢ : Δc-arg ∣ []
  ⊢ renᴹ² (ren² idᵗ (wkN (numBinds Θc))) A₂ ⦂ ` 0
A₂shift-⊢ = tc

A₃-⊢ : Δc-int ∣ [] ⊢ A₃ ⦂ ` 0
A₃-⊢ = tc

E₇-⊢ : empty ∣ [] ⊢ E₇ ⦂ `𝔹
E₇-⊢ = tc

E₈-⊢ : empty ∣ [] ⊢ E₈ ⦂ `𝔹
E₈-⊢ = tc

E₉-⊢ : empty ∣ [] ⊢ E₉ ⦂ `𝔹
E₉-⊢ = tc

E₁₀-⊢ : empty ∣ [] ⊢ E₁₀ ⦂ `𝔹
E₁₀-⊢ = tc

------------------------------------------------------------------------
-- the cancellation tower
------------------------------------------------------------------------

Dc Ψc Rc : CtxMorph
Dc = dualMorph Θc
Ψc = Dc ⋉ Θc
Rc = rewind Θc

Rc-explicit : Rc ≡
  morph (` 0 ∷ [])
    (lock 0 0 ∷ unlock 1 1 ∷ unlock 1 3
       ∷ lock 1 3 ∷ lock 1 1 ∷ unlock 0 0 ∷ [])
Rc-explicit = refl

E₁₁ : Term
E₁₁ =
  (((A₂shift ⟪ Ψc , id (` 1) ⟫) ⟪ Rc , id (` 1) ⟫) ⟪ Θb , unseal 0 ⟫)
    ⟪ Θa , unseal 0 ⟫

Eᴮ-step₁₀ : empty ⊢ E₁₀ -→ E₁₁
Eᴮ-step₁₀ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (ξ-⟪⟫ (proj₂ (int! Δa Θb))
      (CancelR (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-seal)
        (proj₂ (conv! Δb-int Θc)) tu
        (proj₂ (sq! Δc-conv 0))))

I₁-⊢ : Δc-arg ∣ [] ⊢ A₂shift ⟪ Ψc , id (` 1) ⟫ ⦂ ` 0
I₁-⊢ = tc

E₁₁-⊢ : empty ∣ [] ⊢ E₁₁ ⦂ `𝔹
E₁₁-⊢ = tc

------------------------------------------------------------------------
-- IdPush chain, round one
------------------------------------------------------------------------

RbΘa Θ₄ : CtxMorph
Θ₄ = Rc ⋉ Θb
RbΘa = rewind Θb

I₁ : Term
I₁ = A₂shift ⟪ Ψc , id (` 1) ⟫

I₁-value : Value I₁
I₁-value = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-seal) I-idv

E₁₂ : Term
E₁₂ =
  ((I₁ ⟪ Θ₄ , unseal 1 ⟫) ⟪ RbΘa , id (` 1) ⟫) ⟪ Θa , unseal 0 ⟫

Eᴮ-step₁₁ : empty ⊢ E₁₁ -→ E₁₂
Eᴮ-step₁₁ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (IdPush I₁-value (proj₂ (conv! Δa Θb)) tu
      (proj₂ (sq! Δb-conv 0)))

E₁₂-⊢ : empty ∣ [] ⊢ E₁₂ ⦂ `𝔹
E₁₂-⊢ = tc

Ω R₄ : CtxMorph
Ω = Ψc ⋉ Θ₄
R₄ = rewind Θ₄

E₁₃ : Term
E₁₃ =
  (((A₂shift ⟪ Ω , unseal 1 ⟫) ⟪ R₄ , id (` 2) ⟫)
     ⟪ RbΘa , id (` 1) ⟫)
    ⟪ Θa , unseal 0 ⟫

Eᴮ-step₁₂ : empty ⊢ E₁₂ -→ E₁₃
Eᴮ-step₁₂ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (ξ-⟪⟫ (proj₂ (int! Δa RbΘa))
      (IdPush (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-seal)
        (proj₂ (conv! Δb-arg Θ₄)) tu
        (proj₂ (sq! Δc-full 1))))

E₁₃-⊢ : empty ∣ [] ⊢ E₁₃ ⦂ `𝔹
E₁₃-⊢ = tc

------------------------------------------------------------------------
-- the second cancellation
------------------------------------------------------------------------

ΣΩ RΩ : CtxMorph
ΣΩ = Σo ⋉ Ω
RΩ = rewind Ω

E₁₄ : Term
E₁₄ =
  ((((A₂in ⟪ ΣΩ , id (` 2) ⟫) ⟪ RΩ , id (` 2) ⟫) ⟪ R₄ , id (` 2) ⟫)
     ⟪ RbΘa , id (` 1) ⟫)
    ⟪ Θa , unseal 0 ⟫

Eᴮ-step₁₃ : empty ⊢ E₁₃ -→ E₁₄
Eᴮ-step₁₃ =
  ξ-⟪⟫ (proj₂ (int! empty Θa))
    (ξ-⟪⟫ (proj₂ (int! Δa RbΘa))
      (ξ-⟪⟫ (proj₂ (int! Δb-arg R₄))
        (CancelR (V-⟪⟫ V-true I-seal)
          (proj₂ (conv! Δc-in Ω)) tu
          (proj₂ (sq! Δc-full 1)))))

E₁₄-⊢ : empty ∣ [] ⊢ E₁₄ ⦂ `𝔹
E₁₄-⊢ = tc

------------------------------------------------------------------------
-- the outward IdPush chain and the last cancellation
------------------------------------------------------------------------

Ra P₅ Q₅ P₄ Q₄ P₃ Q₃ P₂ Q₂ P₁ : CtxMorph
Ra = rewind Θa
P₅ = RbΘa ⋉ Θa
Q₅ = rewind P₅
P₄ = R₄ ⋉ P₅
Q₄ = rewind P₄
P₃ = RΩ ⋉ P₄
Q₃ = rewind P₃
P₂ = ΣΩ ⋉ P₃
Q₂ = rewind P₂
P₁ = Σi ⋉ P₂

L₄ : Term
L₄ = (A₂in ⟪ ΣΩ , id (` 2) ⟫) ⟪ RΩ , id (` 2) ⟫

L₄-value : Value L₄
L₄-value = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-idv) I-idv

E₁₅ E₁₆ E₁₇ E₁₈ E₁₉ : Term
E₁₅ = ((L₄ ⟪ R₄ , id (` 2) ⟫) ⟪ P₅ , unseal 1 ⟫) ⟪ Ra , id `𝔹 ⟫
E₁₆ = ((L₄ ⟪ P₄ , unseal 2 ⟫) ⟪ Q₅ , id `𝔹 ⟫) ⟪ Ra , id `𝔹 ⟫
E₁₇ =
  ((((A₂in ⟪ ΣΩ , id (` 2) ⟫) ⟪ P₃ , unseal 2 ⟫) ⟪ Q₄ , id `𝔹 ⟫)
     ⟪ Q₅ , id `𝔹 ⟫)
    ⟪ Ra , id `𝔹 ⟫
E₁₈ =
  (((((A₂in ⟪ P₂ , unseal 2 ⟫) ⟪ Q₃ , id `𝔹 ⟫) ⟪ Q₄ , id `𝔹 ⟫)
      ⟪ Q₅ , id `𝔹 ⟫)
     ⟪ Ra , id `𝔹 ⟫)
E₁₉ =
  ((((((`true ⟪ P₁ , id `𝔹 ⟫) ⟪ Q₂ , id `𝔹 ⟫) ⟪ Q₃ , id `𝔹 ⟫)
       ⟪ Q₄ , id `𝔹 ⟫)
      ⟪ Q₅ , id `𝔹 ⟫)
     ⟪ Ra , id `𝔹 ⟫)

Eᴮ-step₁₄ : empty ⊢ E₁₄ -→ E₁₅
Eᴮ-step₁₄ =
  IdPush (V-⟪⟫ L₄-value I-idv) (proj₂ (conv! empty Θa))
    tu (proj₂ (sq! Δa 0))

Eᴮ-step₁₅ : empty ⊢ E₁₅ -→ E₁₆
Eᴮ-step₁₅ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (IdPush L₄-value (proj₂ (conv! Δa-none P₅)) tu
      (proj₂ (sq! Δb-conv 1)))

Eᴮ-step₁₆ : empty ⊢ E₁₆ -→ E₁₇
Eᴮ-step₁₆ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅))
      (IdPush (V-⟪⟫ (V-⟪⟫ V-true I-seal) I-idv)
        (proj₂ (conv! Δb-none P₄)) tu
        (proj₂ (sq! Δc-full 2))))

Eᴮ-step₁₇ : empty ⊢ E₁₇ -→ E₁₈
Eᴮ-step₁₇ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅))
      (ξ-⟪⟫ (proj₂ (int! Δb-none Q₄))
        (IdPush (V-⟪⟫ V-true I-seal)
          (proj₂ (conv! Δc-none P₃)) tu
          (proj₂ (sq! Δc-full 2)))))

Eᴮ-step₁₈ : empty ⊢ E₁₈ -→ E₁₉
Eᴮ-step₁₈ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅))
      (ξ-⟪⟫ (proj₂ (int! Δb-none Q₄))
        (ξ-⟪⟫ (proj₂ (int! Δc-none Q₃))
          (CancelR V-true (proj₂ (conv! Δc-none P₂))
            tu (proj₂ (sq! Δc-full 2))))))

E₂₀ E₂₁ E₂₂ E₂₃ E₂₄ : Term
E₂₀ =
  (((((`true ⟪ Q₂ , id `𝔹 ⟫) ⟪ Q₃ , id `𝔹 ⟫) ⟪ Q₄ , id `𝔹 ⟫)
      ⟪ Q₅ , id `𝔹 ⟫)
     ⟪ Ra , id `𝔹 ⟫)
E₂₁ =
  ((((`true ⟪ Q₃ , id `𝔹 ⟫) ⟪ Q₄ , id `𝔹 ⟫) ⟪ Q₅ , id `𝔹 ⟫)
     ⟪ Ra , id `𝔹 ⟫)
E₂₂ = (((`true ⟪ Q₄ , id `𝔹 ⟫) ⟪ Q₅ , id `𝔹 ⟫) ⟪ Ra , id `𝔹 ⟫)
E₂₃ = ((`true ⟪ Q₅ , id `𝔹 ⟫) ⟪ Ra , id `𝔹 ⟫)
E₂₄ = (`true ⟪ Ra , id `𝔹 ⟫)

Eᴮ-step₁₉ : empty ⊢ E₁₉ -→ E₂₀
Eᴮ-step₁₉ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅))
      (ξ-⟪⟫ (proj₂ (int! Δb-none Q₄))
        (ξ-⟪⟫ (proj₂ (int! Δc-none Q₃))
          (ξ-⟪⟫ (proj₂ (int! Δc-none Q₂)) Drop-true))))

Eᴮ-step₂₀ : empty ⊢ E₂₀ -→ E₂₁
Eᴮ-step₂₀ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅))
      (ξ-⟪⟫ (proj₂ (int! Δb-none Q₄))
        (ξ-⟪⟫ (proj₂ (int! Δc-none Q₃)) Drop-true)))

Eᴮ-step₂₁ : empty ⊢ E₂₁ -→ E₂₂
Eᴮ-step₂₁ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅))
      (ξ-⟪⟫ (proj₂ (int! Δb-none Q₄)) Drop-true))

Eᴮ-step₂₂ : empty ⊢ E₂₂ -→ E₂₃
Eᴮ-step₂₂ =
  ξ-⟪⟫ (proj₂ (int! empty Ra))
    (ξ-⟪⟫ (proj₂ (int! Δa-none Q₅)) Drop-true)

Eᴮ-step₂₃ : empty ⊢ E₂₃ -→ E₂₄
Eᴮ-step₂₃ = ξ-⟪⟫ (proj₂ (int! empty Ra)) Drop-true

Eᴮ-step₂₄ : empty ⊢ E₂₄ -→ `true
Eᴮ-step₂₄ = Drop-true

Eᴮ-run : empty ⊢ E₀ᴮ -→* `true
Eᴮ-run =
  Eᴮ-step₀ then Eᴮ-step₁ then Eᴮ-step₂ then Eᴮ-step₃ then
  Eᴮ-step₄ then Eᴮ-step₅ then Eᴮ-step₆ then Eᴮ-step₇ then
  Eᴮ-step₈ then Eᴮ-step₉ then Eᴮ-step₁₀ then Eᴮ-step₁₁ then
  Eᴮ-step₁₂ then Eᴮ-step₁₃ then Eᴮ-step₁₄ then Eᴮ-step₁₅ then
  Eᴮ-step₁₆ then Eᴮ-step₁₇ then Eᴮ-step₁₈ then Eᴮ-step₁₉ then
  Eᴮ-step₂₀ then Eᴮ-step₂₁ then Eᴮ-step₂₂ then Eᴮ-step₂₃ then
  Eᴮ-step₂₄ then done

------------------------------------------------------------------------
-- typing derivations for the outward chain
------------------------------------------------------------------------

M₂-⊢ : Δc-in ∣ [] ⊢ A₂in ⟪ ΣΩ , id (` 2) ⟫ ⦂ ` 0
M₂-⊢ = tc

L₄-⊢ : Δc-in ∣ [] ⊢ L₄ ⦂ ` 0
L₄-⊢ = tc

L₄R₄-⊢ : Δb-arg ∣ [] ⊢ L₄ ⟪ R₄ , id (` 2) ⟫ ⦂ ` 0
L₄R₄-⊢ = tc

E₁₅-⊢ : empty ∣ [] ⊢ E₁₅ ⦂ `𝔹
E₁₅-⊢ = tc

E₁₆-⊢ : empty ∣ [] ⊢ E₁₆ ⦂ `𝔹
E₁₆-⊢ = tc

E₁₇-⊢ : empty ∣ [] ⊢ E₁₇ ⦂ `𝔹
E₁₇-⊢ = tc

E₁₈-⊢ : empty ∣ [] ⊢ E₁₈ ⦂ `𝔹
E₁₈-⊢ = tc

E₁₉-⊢ : empty ∣ [] ⊢ E₁₉ ⦂ `𝔹
E₁₉-⊢ = tc

E₂₀-⊢ : empty ∣ [] ⊢ E₂₀ ⦂ `𝔹
E₂₀-⊢ = tc

E₂₁-⊢ : empty ∣ [] ⊢ E₂₁ ⦂ `𝔹
E₂₁-⊢ = tc

E₂₂-⊢ : empty ∣ [] ⊢ E₂₂ ⦂ `𝔹
E₂₂-⊢ = tc

E₂₃-⊢ : empty ∣ [] ⊢ E₂₃ ⦂ `𝔹
E₂₃-⊢ = tc

E₂₄-⊢ : empty ∣ [] ⊢ E₂₄ ⦂ `𝔹
E₂₄-⊢ = tc

E-final-⊢ : empty ∣ [] ⊢ `true ⦂ `𝔹
E-final-⊢ = tc

E-final-value : Value `true
E-final-value = V-true

------------------------------------------------------------------------
-- THE WALL THE RUN WALKED INTO, AND WHY THE RE-UNLOCK CLAUSE IS FORCED
------------------------------------------------------------------------

-- `Eᴮ-step₁₀` is `CancelR`, whose contractum wraps the cancelled value in
-- `rewind Θc`.  Θc LOCKS (it is `TyPeelR-Λ`'s `instantiate` over a frame
-- that already crossed two `Λ`s), and a rewind appends the dual of every
-- change, so its change list re-`unlock`s two representation variables
-- whose `lock`s the conversion context SKIPPED.  Under the conversion
-- judgement as it stood — `conv[]`, `conv-lock`, `conv-unlock`, repeated
-- here — that is a freshness violation, so `rewind Θc` has NO conversion
-- context and `env` cannot type `E₁₁` at all.
infix 4 _∣_⊢χᶜ°_⇒_
data _∣_⊢χᶜ°_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  conv°[] : ∀ {Δ} → Ξ ∣ Δ ⊢χᶜ° [] ⇒ Δ
  conv°-lock : ∀ {Δ₁ Δ₂ χ X α} → ValidRVar Ξ α
    → Ξ ∣ Δ₁ ⊢χᶜ° χ ⇒ Δ₂
    → Ξ ∣ Δ₁ ⊢χᶜ° lock X α ∷ χ ⇒ Δ₂
  conv°-unlock : ∀ {Δ₁ Δ₂ Δ₃ χ X α} → ValidRVar Ξ α
    → Ξ ∣ Δ₁ ⊢χᶜ° χ ⇒ Δ₂
    → Fresh α Δ₂
    → α ⊢+ Δ₂ at X ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χᶜ° unlock X α ∷ χ ⇒ Δ₃

-- The wall itself.  `1 ∷ 3 ∷ []` is `names (extendReps (binds Rc) Δb-int)`,
-- the name map the conversion run starts from.
no-old-rewind-conv : ∀ {Δᶜ}
  → repsC ∣ (1 ∷ 3 ∷ []) ⊢χᶜ° changes Rc ⇒ Δᶜ → ⊥
no-old-rewind-conv
  (conv°-lock _
    (conv°-unlock _
      (conv°-unlock _
        (conv°-lock _
          (conv°-lock _ (conv°-unlock _ conv°[] _ ins-here)))
        (fresh∷ _ (fresh∷ _ (fresh∷ ne _))) _)
      _ _)) = ne refl

-- With the re-unlock clause the run goes through, and the conversion
-- context is the one Θc's own conversion produced — which is exactly what
-- `CancelR`'s minted `mkId A` is checked against.
rewind-conv-repaired : Δb-int ⊢ᶜ Rc ⇒ Δc-conv
rewind-conv-repaired = proj₂ (conv! Δb-int Rc)

-- The same wall stands in front of `CancelR`'s OTHER frame, `Θ₁ ⋉ Θ₂`,
-- whenever the crossing argument acquired Θ₂'s dual at a `Peel`.
cancel-inner-conv-repaired : Δc-arg ⊢ᶜ Ψc ⇒ Δc-conv
cancel-inner-conv-repaired = proj₂ (conv! Δc-arg Ψc)

------------------------------------------------------------------------
-- The evaluator reproduces every recorded run, and keeps the type
--
-- `eval` (strong.Eval) iterates `step` and calls the type checker on each
-- contractum, at the type the run started with.  Each example below is
-- checked twice: the states it visits are the ones written out above, and
-- no step lost the type — `Checked` is the unit record exactly when
-- nothing broke, so the `_` is a proof only because every state checked.
--
-- That is subject reduction FOR THESE RUNS, checked rather than proved,
-- and it is the check that would have caught the `rewind` defect on its
-- own: E₁₁ is the first state the type checker would have rejected
-- (notes/DECISIONS.md, 2026-09-17).
------------------------------------------------------------------------

-- 1. the polymorphic identity
eval-P₁ : evalTerms 6 P₁₀-⊢ ≡ P₁₀ ∷ P₁₁ ∷ P₁₂ ∷ P₁₃ ∷ P₁₄ ∷ P₁₅ ∷ P₁₆ ∷ []
eval-P₁ = refl

eval-P₁-⦂ : empty ∣ [] ⊢ traceEnd (eval 6 P₁₀ P₁₀-⊢) ⦂ `ℕ
eval-P₁-⦂ = eval-⦂ 6 P₁₀-⊢ _

-- 3. the polymorphic constant
eval-J : evalTerms 11 J₀-⊢ ≡ J₀ ∷ J₁ ∷ J₂ ∷ J₃ ∷ J₄ ∷ J₅ ∷ J₆ ∷ J₇ ∷ J₈ ∷
  J₉ ∷ J₁₀ ∷ $ 3 ∷ []
eval-J = refl

eval-J-⦂ : empty ∣ [] ⊢ traceEnd (eval 11 J₀ J₀-⊢) ⦂ `ℕ
eval-J-⦂ = eval-⦂ 11 J₀-⊢ _

-- 2. the polymorphic Boolean use
eval-K : evalTerms 9 K₀-⊢ ≡ K₀ ∷ K₁ ∷ K₂ ∷ K₃ ∷ K₄ ∷ K₅ ∷ K₆ ∷ K₇ ∷ K₈ ∷
  `true ∷ []
eval-K = refl

eval-K-⦂ : empty ∣ [] ⊢ traceEnd (eval 9 K₀ K₀-⊢) ⦂ `𝔹
eval-K-⦂ = eval-⦂ 9 K₀-⊢ _

-- 4. the later-bound identity
eval-Eᴮ : evalTerms 25 E₀ᴮ-⊢ ≡ E₀ᴮ ∷ E₁ᴮ ∷ E₂ᴮ ∷ E₃ᴮ ∷ E₄ᴮ ∷ E₅ᴮ ∷ E₆ᴮ ∷
  E₇ ∷ E₈ ∷ E₉ ∷ E₁₀ ∷ E₁₁ ∷ E₁₂ ∷ E₁₃ ∷ E₁₄ ∷ E₁₅ ∷ E₁₆ ∷ E₁₇ ∷ E₁₈ ∷ E₁₉ ∷
  E₂₀ ∷ E₂₁ ∷ E₂₂ ∷ E₂₃ ∷ E₂₄ ∷ `true ∷ []
eval-Eᴮ = refl

eval-Eᴮ-⦂ : empty ∣ [] ⊢ traceEnd (eval 25 E₀ᴮ E₀ᴮ-⊢) ⦂ `𝔹
eval-Eᴮ-⦂ = eval-⦂ 25 E₀ᴮ-⊢ _

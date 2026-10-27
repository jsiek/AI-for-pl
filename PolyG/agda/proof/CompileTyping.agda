module proof.CompileTyping where

-- File Charter:
--   * Elaboration of PolyGν into PolyCν (Compile.agda) preserves typing:
--     if WfTyEnv Δ, WfCtx (tsize Δ) Γ and d : Δ ∣ Γ ⊢ᴳ M ⦂ A, then
--     Σ ∣ Δ ∣ Γ ⊢ elab d ⦂ A for every store Σ.
--   * Supporting facts: surface-typed terms have well-formed types, and
--     the relation Heads G A A↓ describing the type A↓ produced by the
--     elimination helper ⇓ G (shared with proof/CompilePrecision.agda).
--   * Exported through CompileMeta.agda.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_×_; _,_)

open import Types
open import Terms
open import Typing
open import GradualTerms
open import Compile
open import CompileInvariants
open import proof.PrecisionProps

------------------------------------------------------------------------
-- Lookups in well-formed contexts
------------------------------------------------------------------------

≅-< : ∀ {Δ X A} → Δ ∋ X ≅ A → X < tsize Δ
≅-< Z≅ = s≤s z≤n
≅-< (S≅ X≅A) = s≤s (≅-< X≅A)

≅-wf : ∀ {Δ X A} → WfTyEnv Δ → Δ ∋ X ≅ A → WfTy (tsize Δ) A
≅-wf (wf-known wfA wfΔ) Z≅ = ⇑ᵗ-wf wfA
≅-wf (wf-abs wfΔ) (S≅ X≅A) = ⇑ᵗ-wf (≅-wf wfΔ X≅A)
≅-wf (wf-known wfB wfΔ) (S≅ X≅A) = ⇑ᵗ-wf (≅-wf wfΔ X≅A)

∋-wf : ∀ {n Γ x A} → WfCtx n Γ → Γ ∋ x ⦂ A → WfTy n A
∋-wf (wfc∷ wfA wfΓ) Z = wfA
∋-wf (wfc∷ wfB wfΓ) (S x∈) = ∋-wf wfΓ x∈

⤊-wf : ∀ {n Γ} → WfCtx n Γ → WfCtx (suc n) (⤊ Γ)
⤊-wf wfc[] = wfc[]
⤊-wf (wfc∷ wfA wfΓ) = wfc∷ (⇑ᵗ-wf wfA) (⤊-wf wfΓ)

------------------------------------------------------------------------
-- Shapes of eliminated types
------------------------------------------------------------------------

asFun-wf : ∀ {n A A₁ A₂} → AsFun A A₁ A₂ → WfTy n A
  → WfTy n A₁ × WfTy n A₂
asFun-wf as-fun (wf⇒ wfA₁ wfA₂) = wfA₁ , wfA₂
asFun-wf as-fun★ wf★ = wf★ , wf★

asForall-wf : ∀ {n A A₀} → AsForall A A₀ → WfTy n A → WfTy (suc n) A₀
asForall-wf as-∀ (wf∀ wfA₀) = wfA₀
asForall-wf as-∀★ wf★ = wf★

-- Heads G A A↓: a term of type A, eliminated at ground G, has type A↓
-- after ⇓ G
data Heads : Ground → Ty → Ty → Set where
  hd★ : ∀ {G} → Heads G ★ (groundTy G)
  hd‵ : ∀ {α} → Heads (G‵ α) (‵ α) (‵ α)
  hd𝔹 : Heads G𝔹 𝔹 𝔹
  hd⇒ : ∀ {A B} → Heads G⇒ (A ⇒ B) (A ⇒ B)
  hd∀ : ∀ {A} → Heads G∀ (∀ν A) (∀ν A)

∼‵-heads : ∀ {A X} → A ∼ ‵ tvar X → Heads (G‵ (tvar X)) A (‵ tvar X)
∼‵-heads ∼★L = hd★
∼‵-heads ∼‵ = hd‵

∼𝔹-heads : ∀ {A} → A ∼ 𝔹 → Heads G𝔹 A 𝔹
∼𝔹-heads ∼★L = hd★
∼𝔹-heads ∼𝔹 = hd𝔹

asFun-heads : ∀ {A A₁ A₂} → AsFun A A₁ A₂ → Heads G⇒ A (A₁ ⇒ A₂)
asFun-heads as-fun = hd⇒
asFun-heads as-fun★ = hd★

asForall-heads : ∀ {A A₀} → AsForall A A₀ → Heads G∀ A (∀ν A₀)
asForall-heads as-∀ = hd∀
asForall-heads as-∀★ = hd★

⇓-⊢ : ∀ {Σ Δ Γ G A A↓ M}
  → Heads G A A↓
  → WfGround (tsize Δ) G
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ ∣ Δ ∣ Γ ⊢ ⇓ G A M ⦂ A↓
⇓-⊢ hd★ wfG ⊢M = ⊢down (⊑tag wfG (idᵖ-⊢ (groundTy-wf wfG))) ⊢M
⇓-⊢ hd‵ wfG ⊢M = ⊢M
⇓-⊢ hd𝔹 wfG ⊢M = ⊢M
⇓-⊢ hd⇒ wfG ⊢M = ⊢M
⇓-⊢ hd∀ wfG ⊢M = ⊢M

ascribe-⊢ : ∀ {Σ Δ Γ A B M}
  → WfTy (tsize Δ) A
  → WfTy (tsize Δ) B
  → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
  → Σ ∣ Δ ∣ Γ ⊢ ascribe A B M ⦂ B
ascribe-⊢ wfA wfB ⊢M = ⊢down (dynᵖ-⊢ wfB) (⊢up (dynᵖ-⊢ wfA) ⊢M)

------------------------------------------------------------------------
-- Surface-typed terms have well-formed types
------------------------------------------------------------------------

⊢ᴳ-wf : ∀ {Δ Γ M A} → WfTyEnv Δ → WfCtx (tsize Δ) Γ
  → Δ ∣ Γ ⊢ᴳ M ⦂ A → WfTy (tsize Δ) A
⊢ᴳ-wf wfΔ wfΓ (⊢` x∈) = ∋-wf wfΓ x∈
⊢ᴳ-wf wfΔ wfΓ (⊢⦂⦂ ⊢M A∼B wfB) = wfB
⊢ᴳ-wf wfΔ wfΓ (⊢seal X≅A ⊢M B∼A) = wf‵ (≅-< X≅A)
⊢ᴳ-wf wfΔ wfΓ (⊢unseal X≅A ⊢M B∼X) = ≅-wf wfΔ X≅A
⊢ᴳ-wf wfΔ wfΓ (⊢is wfG ⊢M) = wf𝔹
⊢ᴳ-wf wfΔ wfΓ ⊢true = wf𝔹
⊢ᴳ-wf wfΔ wfΓ ⊢false = wf𝔹
⊢ᴳ-wf wfΔ wfΓ (⊢if ⊢L A∼𝔹 ⊢M ⊢N m) =
  meet-wf m (⊢ᴳ-wf wfΔ wfΓ ⊢M) (⊢ᴳ-wf wfΔ wfΓ ⊢N)
⊢ᴳ-wf wfΔ wfΓ (⊢ƛ wfA ⊢M) = wf⇒ wfA (⊢ᴳ-wf wfΔ (wfc∷ wfA wfΓ) ⊢M)
⊢ᴳ-wf wfΔ wfΓ (⊢· ⊢L shp ⊢M B∼A₁)
  with asFun-wf shp (⊢ᴳ-wf wfΔ wfΓ ⊢L)
⊢ᴳ-wf wfΔ wfΓ (⊢· ⊢L shp ⊢M B∼A₁) | wfA₁ , wfA₂ = wfA₂
⊢ᴳ-wf wfΔ wfΓ (⊢letv ⊢M ⊢N) =
  ⊢ᴳ-wf wfΔ (wfc∷ (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfΓ) ⊢N
⊢ᴳ-wf wfΔ wfΓ (⊢Λν ⊢M) = wf∀ (⊢ᴳ-wf (wf-abs wfΔ) (⤊-wf wfΓ) ⊢M)
⊢ᴳ-wf wfΔ wfΓ (⊢inst ⊢M shp wfB ⊢N wfC) = wfC

------------------------------------------------------------------------
-- Elaboration preserves typing
------------------------------------------------------------------------

elab-⊢ : ∀ {Σ Δ Γ M A} → WfTyEnv Δ → WfCtx (tsize Δ) Γ
  → (d : Δ ∣ Γ ⊢ᴳ M ⦂ A) → Σ ∣ Δ ∣ Γ ⊢ elab d ⦂ A
elab-⊢ wfΔ wfΓ (⊢` x∈) = ⊢` x∈
elab-⊢ wfΔ wfΓ (⊢⦂⦂ ⊢M A∼B wfB) =
  ascribe-⊢ (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfB (elab-⊢ wfΔ wfΓ ⊢M)
elab-⊢ wfΔ wfΓ (⊢seal X≅A ⊢M B∼A) =
  ⊢seal (nt-var X≅A)
    (ascribe-⊢ (⊢ᴳ-wf wfΔ wfΓ ⊢M) (≅-wf wfΔ X≅A) (elab-⊢ wfΔ wfΓ ⊢M))
elab-⊢ wfΔ wfΓ (⊢unseal X≅A ⊢M B∼X) =
  ⊢unseal (nt-var X≅A)
    (⇓-⊢ (∼‵-heads B∼X) (wfG‵ (≅-< X≅A)) (elab-⊢ wfΔ wfΓ ⊢M))
elab-⊢ wfΔ wfΓ (⊢is wfG ⊢M) =
  ⊢is wfG (⊢up (dynᵖ-⊢ (⊢ᴳ-wf wfΔ wfΓ ⊢M)) (elab-⊢ wfΔ wfΓ ⊢M))
elab-⊢ wfΔ wfΓ ⊢true = ⊢true
elab-⊢ wfΔ wfΓ ⊢false = ⊢false
elab-⊢ wfΔ wfΓ (⊢if ⊢L A∼𝔹 ⊢M ⊢N m) =
  ⊢if (⇓-⊢ (∼𝔹-heads A∼𝔹) wfG𝔹 (elab-⊢ wfΔ wfΓ ⊢L))
      (⊢down (meetL-⊢ m wfBt wfBf) (elab-⊢ wfΔ wfΓ ⊢M))
      (⊢down (meetR-⊢ m wfBt wfBf) (elab-⊢ wfΔ wfΓ ⊢N))
  where
  wfBt = ⊢ᴳ-wf wfΔ wfΓ ⊢M
  wfBf = ⊢ᴳ-wf wfΔ wfΓ ⊢N
elab-⊢ wfΔ wfΓ (⊢ƛ wfA ⊢M) = ⊢ƛ (elab-⊢ wfΔ (wfc∷ wfA wfΓ) ⊢M)
elab-⊢ wfΔ wfΓ (⊢· ⊢L shp ⊢M B∼A₁)
  with asFun-wf shp (⊢ᴳ-wf wfΔ wfΓ ⊢L)
elab-⊢ wfΔ wfΓ (⊢· ⊢L shp ⊢M B∼A₁) | wfA₁ , wfA₂ =
  ⊢· (⇓-⊢ (asFun-heads shp) wfG⇒ (elab-⊢ wfΔ wfΓ ⊢L))
     (ascribe-⊢ (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfA₁ (elab-⊢ wfΔ wfΓ ⊢M))
elab-⊢ wfΔ wfΓ (⊢letv ⊢M ⊢N) =
  ⊢letv (elab-⊢ wfΔ wfΓ ⊢M)
        (elab-⊢ wfΔ (wfc∷ (⊢ᴳ-wf wfΔ wfΓ ⊢M) wfΓ) ⊢N)
elab-⊢ wfΔ wfΓ (⊢Λν ⊢M) = ⊢Λν (elab-⊢ (wf-abs wfΔ) (⤊-wf wfΓ) ⊢M)
elab-⊢ wfΔ wfΓ (⊢inst ⊢M shp wfB ⊢N wfC) =
  ⊢inst (⇓-⊢ (asForall-heads shp) wfG∀ (elab-⊢ wfΔ wfΓ ⊢M)) wfB
        (elab-⊢ (wf-known wfB wfΔ) (wfc∷ wfA₀ (⤊-wf wfΓ)) ⊢N)
  where
  wfA₀ = asForall-wf shp (⊢ᴳ-wf wfΔ wfΓ ⊢M)

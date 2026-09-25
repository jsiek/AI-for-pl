module strong-rep-nu.proof.ErasureSubst where

-- File Charter:
--   * ERASURE COMMUTES WITH FRAME-EXACT SUBSTITUTION: `erase-beta`, the
--     `Beta` case of the simulation.  An image crossing a `Λ` is wrapped
--     (`crossΛᴹ`) and erases to the TYPE-shifted source image
--     (`erase-cross`); an image crossing a `λ` is not shifted at run time
--     but is at the source, which is harmless because a value image is
--     closed (`closed-ren`).  A boundary is not entered by `substᵐ`, and
--     its erasure is closed (`closed-subst`).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.Source using (STerm; _∣_⊢ˢ_⦂_; ⊢ˢ`; ⊢ˢ$;
  ⊢ˢtrue; ⊢ˢfalse; ⊢ˢƛ; ⊢ˢ·; ⊢ˢΛ; ⊢ˢ[])
import strong-rep-nu.Source as S
open import strong-rep-nu.SourceReduction
open import strong-rep-nu.Erasure
open import strong-rep-nu.proof.TermSubst using (∋-map⁻)
open import strong-rep-nu.proof.Preserve using (wf-underΛ; wf-ren; WfRen-wk)
open import strong-rep-nu.proof.RepWeaken using (cross-Λ-⊢)
open import strong-rep-nu.proof.ErasureTypes
open import strong-rep-nu.proof.ErasureTyping using (erasure-typing)
open import strong-rep-nu.proof.ErasureRen using (erase-cross)

------------------------------------------------------------------------
-- 1. Closed source terms
------------------------------------------------------------------------

closed-ren : ∀ {n Γ M A} {ρ : Var → Var}
  → (∀ {x B} → Γ ∋ x ⦂ B → ρ x ≡ x)
  → n ∣ Γ ⊢ˢ M ⦂ A → renameˢ ρ M ≡ M
closed-ren h (⊢ˢ` d) = cong S.`_ (h d)
closed-ren h ⊢ˢ$ = refl
closed-ren h ⊢ˢtrue = refl
closed-ren h ⊢ˢfalse = refl
closed-ren {ρ = ρ} h (⊢ˢƛ {A = A} w d) = cong (S.ƛ A ∙_) (closed-ren h′ d)
  where
  h′ : ∀ {x B} → (A ∷ _) ∋ x ⦂ B → extˢ ρ x ≡ x
  h′ here      = refl
  h′ (there e) = cong suc (h e)
closed-ren h (⊢ˢ· d e) = cong₂ S._·_ (closed-ren h d) (closed-ren h e)
closed-ren h (⊢ˢΛ v d) = cong S.Λ_ (closed-ren h′ d)
  where
  h′ : ∀ {x B} → ⤊ _ ∋ x ⦂ B → _ ≡ x
  h′ e with ∋-map⁻ {f = ⇑ᵗ} e
  h′ e | A , eq , q = h q
closed-ren h (⊢ˢ[] {A = A} d w) = cong (S._[ A ]) (closed-ren h d)

closed-subst : ∀ {n Γ M A} {σ : Var → STerm}
  → (∀ {x B} → Γ ∋ x ⦂ B → σ x ≡ S.` x)
  → n ∣ Γ ⊢ˢ M ⦂ A → substˢ σ M ≡ M
closed-subst h (⊢ˢ` d) = h d
closed-subst h ⊢ˢ$ = refl
closed-subst h ⊢ˢtrue = refl
closed-subst h ⊢ˢfalse = refl
closed-subst {σ = σ} h (⊢ˢƛ {A = A} w d) =
  cong (S.ƛ A ∙_) (closed-subst h′ d)
  where
  h′ : ∀ {x B} → (A ∷ _) ∋ x ⦂ B → extsˢ σ x ≡ S.` x
  h′ here      = refl
  h′ (there e) = cong (renameˢ suc) (h e)
closed-subst {σ = σ} h (⊢ˢ· d e) =
  cong₂ S._·_ (closed-subst h d) (closed-subst h e)
closed-subst {σ = σ} h (⊢ˢΛ v d) = cong S.Λ_ (closed-subst h′ d)
  where
  h′ : ∀ {x B} → ⤊ _ ∋ x ⦂ B → renameˢᵗ suc (σ x) ≡ S.` x
  h′ e with ∋-map⁻ {f = ⇑ᵗ} e
  h′ e | A , eq , q = cong (renameˢᵗ suc) (h q)
closed-subst h (⊢ˢ[] {A = A} d w) = cong (S._[ A ]) (closed-subst h d)

-- the erasure of a closed run-time term is closed
erase-closed-subst : ∀ {Δ M A} (σ : Var → STerm) → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A → substˢ σ (erase Δ M) ≡ erase Δ M
erase-closed-subst σ w ⊢M = closed-subst (λ ()) (erasure-typing w ⊢M)

erase-closed-ren : ∀ {Δ M A} (ρ : Var → Var) → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A → renameˢ ρ (erase Δ M) ≡ erase Δ M
erase-closed-ren ρ w ⊢M = closed-ren (λ ()) (erasure-typing w ⊢M)

------------------------------------------------------------------------
-- 2. Images and their erasures
------------------------------------------------------------------------

data ImgE (Δ : Ctxᵗ) : Img → STerm → Set where
  ie-var : ∀ {x s} → s ≡ S.` x → ImgE Δ (ivar x) s
  ie-val : ∀ {W A s} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A → s ≡ erase Δ W
    → ImgE Δ (ival W A) s

img-erase : ∀ {Δ i s} → ImgE Δ i s → erase Δ (imgTm i) ≡ s
img-erase (ie-var e)     = sym e
img-erase (ie-val w ⊢W e) = sym e

shift-ie : ∀ {Δ i s} → WfCtx Δ → ImgE Δ i s
  → ImgE Δ (shiftᴵ i) (renameˢ suc s)
shift-ie w (ie-var e) = ie-var (cong (renameˢ suc) e)
shift-ie w (ie-val wA ⊢W e) =
  ie-val wA ⊢W (trans (cong (renameˢ suc) e) (erase-closed-ren suc w ⊢W))

cross-ie : ∀ {Δ i s} → WfCtx Δ → ImgE Δ i s
  → ImgE (underΛ Δ) (⇑ᴵ i) (renameˢᵗ suc s)
cross-ie w (ie-var e) = ie-var (cong (renameˢᵗ suc) e)
cross-ie {Δ = Δ} w (ie-val wA ⊢W e) =
  ie-val (wf-ren (WfRen-wk {Δ = Δ}) wA) (cross-Λ-⊢ w wA ⊢W)
         (trans (cong (renameˢᵗ suc) e) (sym (erase-cross ⊢W)))

------------------------------------------------------------------------
-- 3. The commutation
------------------------------------------------------------------------

erase-substᵐ : ∀ {Δ Γ N B} {σ : Var → Img} {σˢ : Var → STerm}
  → WfCtx Δ
  → (∀ x → ImgE Δ (σ x) (σˢ x))
  → Δ ∣ Γ ⊢ N ⦂ B
  → erase Δ (substᵐ σ N) ≡ substˢ σˢ (erase Δ N)
erase-substᵐ w h (⊢` {x = x} d) = img-erase (h x)
erase-substᵐ w h ⊢$ = refl
erase-substᵐ w h ⊢true = refl
erase-substᵐ w h ⊢false = refl
erase-substᵐ {Δ} {σ = σ} {σˢ} w h (⊢ƛ {A = A} wA ⊢N) =
  cong (S.ƛ eraseTy Δ A ∙_) (erase-substᵐ w h′ ⊢N)
  where
  h′ : ∀ x → ImgE Δ (extᴵ σ x) (extsˢ σˢ x)
  h′ zero    = ie-var refl
  h′ (suc x) = shift-ie w (h x)
erase-substᵐ w h (⊢· ⊢L ⊢M) =
  cong₂ S._·_ (erase-substᵐ w h ⊢L) (erase-substᵐ w h ⊢M)
erase-substᵐ {Δ} {σ = σ} {σˢ} w h (⊢Λ vN ⊢N) =
  cong S.Λ_ (erase-substᵐ (wf-underΛ w) h′ ⊢N)
  where
  h′ : ∀ x → ImgE (underΛ Δ) (⇑ᴵ (σ x)) (renameˢᵗ suc (σˢ x))
  h′ x = cross-ie w (h x)
erase-substᵐ {Δ} w h (⊢ν {A = A} wA rA ⊢L mw ⊢c same wB) =
  cong (S._[ eraseTy Δ A ]) (erase-substᵐ w h ⊢L)
erase-substᵐ {Δ} {σˢ = σˢ} w h
    (boundary {Θ = Θ} {M = M} mw ⊢M ⊢c sᵢ sₑ wE) =
  sym (trans (cong (λ D → substˢ σˢ (erase D M))
                   (inside-sound (bw-interior mw)))
        (trans (erase-closed-subst σˢ (bw-interior-wf mw) ⊢M)
               (cong (λ D → erase D M)
                     (sym (inside-sound (bw-interior mw))))))

erase-beta : ∀ {Δ A N W B}
  → WfCtx Δ
  → Δ ⊢ᵗ A
  → Δ ∣ A ∷ [] ⊢ N ⦂ B
  → Δ ∣ [] ⊢ W ⦂ A
  → erase Δ (N [ W ∶ A ]ᵐ) ≡ (erase Δ N) [ erase Δ W ]ᵛ
erase-beta {Δ} {A} {W = W} w wA ⊢N ⊢W = erase-substᵐ w h ⊢N
  where
  h : ∀ x → ImgE Δ (betaEnv W A x) (singleˢ (erase Δ W) x)
  h zero    = ie-val wA ⊢W refl
  h (suc x) = ie-var refl

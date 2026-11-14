module proof.LR.Elaboration where

-- File Charter:
--   * Elaboration preserves precision (notes/denotational-dgg.md,
--     Section 7a): source term precision (`GradualTermImprecision`,
--     unchanged) is taken to cast-calculus precision
--     (`LR.CastPrecision`) by eager elaboration (`LR.Elaborate`).
--   * Both sides are elaborated relationally (`ElabE`), so the theorem
--     holds whichever typing derivations the two programs come from.
--   * The right program lives in a smaller context `Δ′`: the source
--     right term is `Grenameᵐ (embedᶜ Φ) M″` for a term `M″` of `Δ′`, as
--     in `proof.DGG.CompilePreservesImprecision2`.  Under a left-only
--     `Λ` the source shifts the right term (`⇑ᵗᴳ N′`); here that is the
--     same `M″` under a `skip`.
--   * Type precision is read in two contexts by `back`
--     (`proof.LR.Precision`); the source environment `μ` only has to
--     agree pointwise with `impEnvᶜ Φ`.
--   * Types are aligned by uniqueness of source typing
--     (`proof.DGG.Elab.typing-uniqueᴳ`); derivation indices that differ
--     only in an equation proof are identified by uniqueness of identity
--     proofs.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Types
open import TyStore using (TyStore; store-empty; store-lift)
open import TermCtx using (TermCtx; ⇑ᶜ)
import TermCtx as T
open import Consistency using (_↪ᵗ_; keep; skip; toRenameᵗ; Env∼; _⊢_∼_)
import Imprecision as I
open import GradualTerms using (GTerm; _∣_⊢_⦂_)
import GradualTerms as G
import GradualTermImprecision as GTI
open GTI
  using (CtxImp; ctx-imp; srcCtxⁱ; tgtCtxⁱ; _∋ⁱ_⦂_; Zⁱ; Sⁱ;
         LiftCtxⁱ; lift-[]; lift-∷; _∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import Primitives
  using (Const; Prim; addℕ; and𝔹; κℕ; κ𝔹; constTy; primArgTy;
         primResultTy)
import CastTerms as C
open import proof.DGG.Elab
  using (elab-gradual-typing; typing-uniqueᴳ; lookup-uniqueᴳ;
         rename-elab; Grenameᵐ)
open import proof.DGG.CompilePreservesImprecision2 using (Grenameᵐ-skip)
open import LR.EagerCast using (Eager)
open import LR.Precision
open import LR.CastPrecision
open import LR.Elaborate
open import proof.LR.Precision

------------------------------------------------------------------------
-- Typing of elaborations
------------------------------------------------------------------------

canonStore : (Δ : TyCtx) → TyStore Δ
canonStore zeroℕ = store-empty
canonStore (sucℕ Δ) = store-lift (canonStore Δ)

elabE-typing : ∀ {Δ} {Γ : TermCtx Δ} {M N A}
  → ElabE Γ M N A → Δ ∣ Γ ⊢ M ⦂ A
elabE-typing {Δ} E = elab-gradual-typing (toElab {Σ = canonStore Δ} E)

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

rightCtx : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} → PrecCtx Φ → TermCtx Δ′
rightCtx = map rightTy

data CtxRel {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
    (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) : CtxImp μ → PrecCtx Φ → Set where
  rel-[] : CtxRel eqμ [] []
  rel-∷ : ∀ {γᴳ γ A B p}
    → (B″ : Ty Δ′)
    → (e : B ≡ renameᵗ (embed Φ) B″)
    → CtxRel eqμ γᴳ γ
    → CtxRel eqμ (ctx-imp A B p ∷ γᴳ) (⟪ A , B″ , back eqμ p B″ e ⟫ ∷ γ)

rel-tgt : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
    {eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X} {γᴳ} {γ : PrecCtx Φ}
  → CtxRel eqμ γᴳ γ
  → tgtCtxⁱ γᴳ ≡ T.renameCtx (embed Φ) (rightCtx γ)
rel-tgt rel-[] = refl
rel-tgt (rel-∷ B″ e r) = cong₂ _∷_ e (rel-tgt r)

rel-lookup : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
    {eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X} {γᴳ} {γ : PrecCtx Φ} {x A B p}
  → CtxRel eqμ γᴳ γ
  → γᴳ ∋ⁱ x ⦂ ctx-imp A B p
  → Σ[ B″ ∈ Ty Δ′ ] Σ[ e ∈ B ≡ renameᵗ (embed Φ) B″ ]
      (γ ∋ᵖ x ⦂ ⟪ A , B″ , back eqμ p B″ e ⟫ × rightCtx γ T.∋ x ⦂ B″)
rel-lookup (rel-∷ B″ e r) Zⁱ = B″ , e , Zᵖ , T.Z
rel-lookup (rel-∷ B₀″ e₀ r) (Sⁱ x∈) with rel-lookup r x∈
rel-lookup (rel-∷ B₀″ e₀ r) (Sⁱ x∈) | B″ , e , x∈ᵖ , y∈ =
  B″ , e , Sᵖ x∈ᵖ , T.S y∈

shift-embed-pair : ∀ {Δ Δ′} (Φ : Corr Δ Δ′) (B″ : Ty Δ′)
  → ⇑ᵗ (renameᵗ (embed Φ) B″) ≡ renameᵗ (embed (pair Φ)) (⇑ᵗ B″)
shift-embed-pair Φ B″ =
  trans (renameᵗ-comp (embed Φ) suc B″)
    (sym (trans (renameᵗ-comp suc (embed (pair Φ)) B″)
      (renameᵗ-cong B″ (λ X → refl))))

rel-lift-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
    {eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X} {γᴳ γᴳ′} {γ : PrecCtx Φ}
  → CtxRel eqμ γᴳ γ
  → LiftCtxⁱ (I.extᵐ μ) γᴳ γᴳ′
  → Σ[ γ′ ∈ PrecCtx (pair Φ) ]
      (LiftPair γ γ′ × CtxRel (env-pair eqμ) γᴳ′ γ′)
rel-lift-pair rel-[] lift-[] = [] , lp-[] , rel-[]
rel-lift-pair {Φ = Φ} {eqμ = eqμ} (rel-∷ B″ e r) (lift-∷ {p′ = p′} l)
    with rel-lift-pair r l
rel-lift-pair {Φ = Φ} {eqμ = eqμ} (rel-∷ B″ e r) (lift-∷ {p′ = p′} l)
    | γ′ , lp , r′ =
  _ , lp-∷ lp , rel-∷ (⇑ᵗ B″) e′ r′
  where
  e′ = trans (cong ⇑ᵗ e) (shift-embed-pair Φ B″)

rel-lift-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
    {eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X} {γᴳ γᴳ′} {γ : PrecCtx Φ}
  → CtxRel eqμ γᴳ γ
  → LiftCtxⁱ (I.instᵐ μ) γᴳ γᴳ′
  → Σ[ γ′ ∈ PrecCtx (only Φ) ]
      (LiftOnly γ γ′ × CtxRel (env-only eqμ) γᴳ′ γ′)
rel-lift-only rel-[] lift-[] = [] , lo-[] , rel-[]
rel-lift-only {Φ = Φ} (rel-∷ B″ e r) (lift-∷ l) with rel-lift-only r l
rel-lift-only {Φ = Φ} (rel-∷ B″ e r) (lift-∷ l) | γ′ , lo , r′ =
  _ , lo-∷ lo , rel-∷ B″ (embed-under-only Φ B″ e) r′

lift-right-pair : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {γ : PrecCtx Φ}
    {γ′ : PrecCtx (pair Φ)}
  → LiftPair γ γ′ → rightCtx γ′ ≡ ⇑ᶜ (rightCtx γ)
lift-right-pair lp-[] = refl
lift-right-pair (lp-∷ lp) = cong (_ ∷_) (lift-right-pair lp)

lift-right-only : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {γ : PrecCtx Φ}
    {γ′ : PrecCtx (only Φ)}
  → LiftOnly γ γ′ → rightCtx γ′ ≡ rightCtx γ
lift-right-only lo-[] = refl
lift-right-only (lo-∷ lo) = cong (_ ∷_) (lift-right-only lo)

------------------------------------------------------------------------
-- Derivation indices
------------------------------------------------------------------------

≡-irrel : ∀ {a} {A : Set a} {x y : A} (e e′ : x ≡ y) → e ≡ e′
≡-irrel refl refl = refl

back-irrel : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X)
  → (p : μ I.⊢ A ⊑ B) (B″ : Ty Δ′)
  → (e e′ : B ≡ renameᵗ (embed Φ) B″)
  → back eqμ p B″ e ≡ back eqμ p B″ e′
back-irrel eqμ p B″ e e′ = cong (back eqμ p B″) (≡-irrel e e′)

reindex : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {γ : PrecCtx Φ} {N N″ A B}
    {q q′ : Φ ⊢ A ⊑ B}
  → q ≡ q′
  → Φ ∣ γ ⊢ N ⊑ N″ ⦂ A ⊑ B ∶ q
  → Φ ∣ γ ⊢ N ⊑ N″ ⦂ A ⊑ B ∶ q′
reindex refl N⊑ = N⊑

back-const : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
  → (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) (κ : Const)
  → (e : constTy κ ≡ renameᵗ (embed Φ) (constTy κ))
  → back eqμ (GTI.constTy-⊑ μ κ) (constTy κ) e ≡ constTy-⊑ κ
back-const eqμ (κℕ n) refl = refl
back-const eqμ (κ𝔹 b) refl = refl

back-prim : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
  → (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) (op : Prim)
  → (e : primResultTy op ≡ renameᵗ (embed Φ) (primResultTy op))
  → back eqμ (GTI.primResultTy-⊑ μ op) (primResultTy op) e
    ≡ primResultTy-⊑ op
back-prim eqμ addℕ refl = refl
back-prim eqμ and𝔹 refl = refl

------------------------------------------------------------------------
-- Inverting the right elaboration of an embedded term
------------------------------------------------------------------------

-- Each view inverts `ElabE Γ M″ N″ B″` when the embedding of `M″` has a
-- known head; matching the view fixes `N″` and `B″`.

data View-` {Δ′} (Γ : TermCtx Δ′) (x : ℕ) : C.Term Δ′ → Ty Δ′ → Set where
  v-` : ∀ {B″} → Γ T.∋ x ⦂ B″ → View-` Γ x (C.` x) B″

view-` : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {x M″ N″ B″}
  → ElabE Γ M″ N″ B″ → G.` x ≡ Grenameᵐ η M″ → View-` Γ x N″ B″
view-` (Eᴱ-` y∈) refl = v-` y∈
view-` (Eᴱ-ƛ _) ()
view-` (Eᴱ-· _ _ _ _ _) ()
view-` (Eᴱ-·★ _ _ _ _ _ _ _) ()
view-` (Eᴱ-Λ _ _ _ _) ()
view-` (Eᴱ-[] _ _) ()
view-` (Eᴱ-$ _) ()
view-` (Eᴱ-⊕ _ _ _ _ _ _ _ _ _) ()

data View-ƛ {Δ Δ′} (η : Δ′ ↪ᵗ Δ) (Γ : TermCtx Δ′) (A′ : Ty Δ)
    (N′ : GTerm Δ) : C.Term Δ′ → Ty Δ′ → Set where
  v-ƛ : ∀ {A″ M₀″ N₀″ B₀″}
    → A′ ≡ renameᵗ (toRenameᵗ η) A″
    → N′ ≡ Grenameᵐ η M₀″
    → ElabE (A″ ∷ Γ) M₀″ N₀″ B₀″
    → View-ƛ η Γ A′ N′ (C.ƛ N₀″) (A″ ⇒ B₀″)

view-ƛ : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {A′ N′ M″ N″ B″}
  → ElabE Γ M″ N″ B″ → G.ƛ A′ ⇒ N′ ≡ Grenameᵐ η M″
  → View-ƛ η Γ A′ N′ N″ B″
view-ƛ (Eᴱ-ƛ Nᴱ) refl = v-ƛ refl refl Nᴱ
view-ƛ (Eᴱ-` _) ()
view-ƛ (Eᴱ-· _ _ _ _ _) ()
view-ƛ (Eᴱ-·★ _ _ _ _ _ _ _) ()
view-ƛ (Eᴱ-Λ _ _ _ _) ()
view-ƛ (Eᴱ-[] _ _) ()
view-ƛ (Eᴱ-$ _) ()
view-ƛ (Eᴱ-⊕ _ _ _ _ _ _ _ _ _) ()

data View-app {Δ Δ′} (η : Δ′ ↪ᵗ Δ) (Γ : TermCtx Δ′)
    (L′ M′ : GTerm Δ) : C.Term Δ′ → Ty Δ′ → Set where
  v-· : ∀ {L″ M₀″ Lᶜ Mᶜ A″ B″ D″} {ν : Env∼ Δ′}
    → L′ ≡ Grenameᵐ η L″
    → M′ ≡ Grenameᵐ η M₀″
    → ElabE Γ L″ Lᶜ (A″ ⇒ B″)
    → ElabE Γ M₀″ Mᶜ D″
    → (c : ν ⊢ D″ ∼ A″) → Eager c
    → View-app η Γ L′ M′ (Lᶜ C.· (Mᶜ C.⟨ c ⟩)) B″
  v-·★ : ∀ {L″ M₀″ Lᶜ Mᶜ A″} {ν ν′ : Env∼ Δ′}
    → L′ ≡ Grenameᵐ η L″
    → M′ ≡ Grenameᵐ η M₀″
    → ElabE Γ L″ Lᶜ ★
    → ElabE Γ M₀″ Mᶜ A″
    → (c : ν ⊢ ★ ∼ (★ ⇒ ★)) → Eager c
    → (d : ν′ ⊢ A″ ∼ ★) → Eager d
    → View-app η Γ L′ M′ ((Lᶜ C.⟨ c ⟩) C.· (Mᶜ C.⟨ d ⟩)) ★

view-app : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {L′ M′ ℓ M″ N″ B″}
  → ElabE Γ M″ N″ B″ → L′ G.·[ ℓ ] M′ ≡ Grenameᵐ η M″
  → View-app η Γ L′ M′ N″ B″
view-app (Eᴱ-· Lᴱ Mᴱ _ c Ec) refl = v-· refl refl Lᴱ Mᴱ c Ec
view-app (Eᴱ-·★ Lᴱ Mᴱ _ c Ec d Ed) refl = v-·★ refl refl Lᴱ Mᴱ c Ec d Ed
view-app (Eᴱ-` _) ()
view-app (Eᴱ-ƛ _) ()
view-app (Eᴱ-Λ _ _ _ _) ()
view-app (Eᴱ-[] _ _) ()
view-app (Eᴱ-$ _) ()
view-app (Eᴱ-⊕ _ _ _ _ _ _ _ _ _) ()

data View-Λ {Δ Δ′} (η : Δ′ ↪ᵗ Δ) (Γ : TermCtx Δ′) (V′ : GTerm (sucℕ Δ))
    : C.Term Δ′ → Ty Δ′ → Set where
  v-Λ : ∀ {V″ N₀″ A″}
    → V′ ≡ Grenameᵐ (keep η) V″
    → C.Value N₀″
    → ElabE (⇑ᶜ Γ) V″ N₀″ A″
    → View-Λ η Γ V′ (C.Λ N₀″) (`∀ A″)

view-Λ : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {V′ M″ N″ B″}
  → ElabE Γ M″ N″ B″ → G.Λ V′ ≡ Grenameᵐ η M″ → View-Λ η Γ V′ N″ B″
view-Λ (Eᴱ-Λ z vM vN Vᴱ) refl = v-Λ refl vN Vᴱ
view-Λ (Eᴱ-` _) ()
view-Λ (Eᴱ-ƛ _) ()
view-Λ (Eᴱ-· _ _ _ _ _) ()
view-Λ (Eᴱ-·★ _ _ _ _ _ _ _) ()
view-Λ (Eᴱ-[] _ _) ()
view-Λ (Eᴱ-$ _) ()
view-Λ (Eᴱ-⊕ _ _ _ _ _ _ _ _ _) ()

data View-[] {Δ Δ′} (η : Δ′ ↪ᵗ Δ) (Γ : TermCtx Δ′) (M′ : GTerm Δ)
    (T′ : Ty Δ) : C.Term Δ′ → Ty Δ′ → Set where
  v-[] : ∀ {M₀″ N₀″ B₀″ T″}
    → M′ ≡ Grenameᵐ η M₀″
    → T′ ≡ renameᵗ (toRenameᵗ η) T″
    → ElabE Γ M₀″ N₀″ (`∀ B₀″)
    → View-[] η Γ M′ T′ (N₀″ C.⦂∀ B₀″ [ T″ ]) (B₀″ [ T″ ]ᵗ)

view-[] : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {M′ T′ M″ N″ B″}
  → ElabE Γ M″ N″ B″ → M′ G.`[ T′ ] ≡ Grenameᵐ η M″
  → View-[] η Γ M′ T′ N″ B″
view-[] (Eᴱ-[] Mᴱ refl) refl = v-[] refl refl Mᴱ
view-[] (Eᴱ-` _) ()
view-[] (Eᴱ-ƛ _) ()
view-[] (Eᴱ-· _ _ _ _ _) ()
view-[] (Eᴱ-·★ _ _ _ _ _ _ _) ()
view-[] (Eᴱ-Λ _ _ _ _) ()
view-[] (Eᴱ-$ _) ()
view-[] (Eᴱ-⊕ _ _ _ _ _ _ _ _ _) ()

data View-$ {Δ′} (κ : Const) : C.Term Δ′ → Ty Δ′ → Set where
  v-$ : View-$ κ (C.$ κ) (constTy κ)

view-$ : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {κ M″ N″ B″}
  → ElabE Γ M″ N″ B″ → G.$ κ ≡ Grenameᵐ η M″ → View-$ κ N″ B″
view-$ (Eᴱ-$ κ) refl = v-$
view-$ (Eᴱ-` _) ()
view-$ (Eᴱ-ƛ _) ()
view-$ (Eᴱ-· _ _ _ _ _) ()
view-$ (Eᴱ-·★ _ _ _ _ _ _ _) ()
view-$ (Eᴱ-Λ _ _ _ _) ()
view-$ (Eᴱ-[] _ _) ()
view-$ (Eᴱ-⊕ _ _ _ _ _ _ _ _ _) ()

data View-⊕ {Δ Δ′} (η : Δ′ ↪ᵗ Δ) (Γ : TermCtx Δ′) (op : Prim)
    (L′ M′ : GTerm Δ) : C.Term Δ′ → Ty Δ′ → Set where
  v-⊕ : ∀ {L″ M₀″ Lᶜ Mᶜ A″ B″} {ν ν′ : Env∼ Δ′}
    → L′ ≡ Grenameᵐ η L″
    → M′ ≡ Grenameᵐ η M₀″
    → ElabE Γ L″ Lᶜ A″
    → (c : ν ⊢ A″ ∼ primArgTy op) → Eager c
    → ElabE Γ M₀″ Mᶜ B″
    → (d : ν′ ⊢ B″ ∼ primArgTy op) → Eager d
    → View-⊕ η Γ op L′ M′
        ((Lᶜ C.⟨ c ⟩) C.⊕[ op ] (Mᶜ C.⟨ d ⟩)) (primResultTy op)

view-⊕ : ∀ {Δ Δ′} {η : Δ′ ↪ᵗ Δ} {Γ : TermCtx Δ′} {op L′ M′ ℓ M″ N″ B″}
  → ElabE Γ M″ N″ B″ → L′ G.⊕[ op at ℓ ] M′ ≡ Grenameᵐ η M″
  → View-⊕ η Γ op L′ M′ N″ B″
view-⊕ (Eᴱ-⊕ op Lᴱ _ c Ec Mᴱ _ d Ed) refl =
  v-⊕ refl refl Lᴱ c Ec Mᴱ d Ed
view-⊕ (Eᴱ-` _) ()
view-⊕ (Eᴱ-ƛ _) ()
view-⊕ (Eᴱ-· _ _ _ _ _) ()
view-⊕ (Eᴱ-·★ _ _ _ _ _ _ _) ()
view-⊕ (Eᴱ-Λ _ _ _ _) ()
view-⊕ (Eᴱ-[] _ _) ()
view-⊕ (Eᴱ-$ _) ()

------------------------------------------------------------------------
-- Aligning the types of the two elaborations with the source relation
------------------------------------------------------------------------

left-align : ∀ {Δ} {μ : I.ImpEnv Δ} {γᴳ : CtxImp μ} {M M′ N A A₁ B p}
  → ElabE (srcCtxⁱ γᴳ) M N A₁
  → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
  → A₁ ≡ A
left-align Mᴱ M⊑ =
  typing-uniqueᴳ (elabE-typing Mᴱ)
    (GTI.gradual-term-imprecision-source-typing M⊑)

right-align : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
    {eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X} {γᴳ} {γ : PrecCtx Φ}
    {M M′ A B p M″ N″ B″}
  → CtxRel eqμ γᴳ γ
  → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
  → M′ ≡ Grenameᵐ (embedᶜ Φ) M″
  → ElabE (rightCtx γ) M″ N″ B″
  → B ≡ renameᵗ (embed Φ) B″
right-align {Δ = Δ} {Δ′ = Δ′} {Φ = Φ} {B = B} r M⊑ eM Mᴱ =
  typing-uniqueᴳ
    (subst₂ (λ Γ M → Δ ∣ Γ ⊢ M ⦂ B) (rel-tgt r) eM
      (GTI.gradual-term-imprecision-target-typing M⊑))
    (elab-gradual-typing
      (rename-elab {Σ = canonStore Δ′} {Σ′ = canonStore Δ} (embedᶜ Φ)
        (toElab Mᴱ)))

★≢⇒ : ∀ {Δ} {A B : Ty Δ} → ★ ≡ A ⇒ B → ⊥
★≢⇒ ()

⇒≢★ : ∀ {Δ} {A B : Ty Δ} → A ⇒ B ≡ ★ → ⊥
⇒≢★ ()

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

mutual
  elab-prec : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {M M′ A B p}
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p
    → ∀ {M″ B″ N N″}
    → M′ ≡ Grenameᵐ (embedᶜ Φ) M″
    → (eB : B ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) M N A
    → ElabE (rightCtx γ) M″ N″ B″
    → Φ ∣ γ ⊢ N ⊑ N″ ⦂ A ⊑ B″ ∶ back eqμ p B″ eB
  elab-prec eqμ r (GTI.x⊑xᴳ x∈) eM eB (Eᴱ-` _) R =
    case-var eqμ r x∈ eB (view-` R eM)
  elab-prec eqμ r (GTI.ƛ⊑ƛᴳ N⊑) eM eB (Eᴱ-ƛ Nᴱ) R =
    case-ƛ eqμ r N⊑ eB Nᴱ (view-ƛ R eM)
  elab-prec eqμ r (GTI.·⊑·ᴳ L⊑ M⊑ _ _) eM eB (Eᴱ-· Lᴱ Mᴱ _ c Ec) R =
    case-· eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec (view-app R eM)
  elab-prec eqμ r (GTI.·⊑·ᴳ L⊑ M⊑ _ _) eM eB
      (Eᴱ-·★ Lᴱ Mᴱ _ c Ec d Ed) R =
    ⊥-elim (★≢⇒ (left-align Lᴱ L⊑))
  elab-prec eqμ r (GTI.·⊑·★ᴳ L⊑ M⊑ _ _) eM eB (Eᴱ-· Lᴱ Mᴱ _ c Ec) R =
    case-·★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec (view-app R eM)
  elab-prec eqμ r (GTI.·⊑·★ᴳ L⊑ M⊑ _ _) eM eB
      (Eᴱ-·★ Lᴱ Mᴱ _ c Ec d Ed) R =
    ⊥-elim (★≢⇒ (left-align Lᴱ L⊑))
  elab-prec eqμ r (GTI.·★⊑·★ᴳ L⊑ M⊑ _ _) eM eB
      (Eᴱ-·★ Lᴱ Mᴱ _ c Ec d Ed) R =
    case-★★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec d Ed (view-app R eM)
  elab-prec eqμ r (GTI.·★⊑·★ᴳ L⊑ M⊑ _ _) eM eB (Eᴱ-· Lᴱ Mᴱ _ c Ec) R =
    ⊥-elim (⇒≢★ (left-align Lᴱ L⊑))
  elab-prec eqμ r (GTI.Λ⊑Λᴳ liftγ vV vV′ zA zB V⊑) eM eB
      (Eᴱ-Λ z vM vN Vᴱ) R =
    case-ΛΛ eqμ r liftγ V⊑ eB vN Vᴱ (view-Λ R eM)
  elab-prec eqμ r (GTI.Λ⊑ᴳ Anv zA liftγ vV N′⊢ V⊑) eM eB
      (Eᴱ-Λ z vM vN Vᴱ) R =
    case-Λ eqμ r Anv zA liftγ V⊑ eM eB vN Vᴱ R
  elab-prec eqμ r (GTI.[]⊑[]ᴳ M⊑ q r′) eM eB (Eᴱ-[] Mᴱ eqT) R =
    case-[][] eqμ r M⊑ q r′ eB Mᴱ (view-[] R eM)
  elab-prec eqμ r (GTI.[]⊑ᴳ M⊑ q r′) eM eB (Eᴱ-[] Mᴱ eqT) R =
    case-[] eqμ r M⊑ q r′ eM eB Mᴱ R
  elab-prec eqμ r (GTI.κ⊑κᴳ κ) eM eB (Eᴱ-$ _) R =
    case-κ eqμ κ eB (view-$ R eM)
  elab-prec eqμ r (GTI.⊕⊑⊕ᴳ op L⊑ _ _ M⊑ _ _) eM eB
      (Eᴱ-⊕ _ Lᴱ _ c Ec Mᴱ _ d Ed) R =
    case-⊕ eqμ r op L⊑ M⊑ eB Lᴱ c Ec Mᴱ d Ed (view-⊕ R eM)

  case-var : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {x A B p B″ N″}
    → γᴳ ∋ⁱ x ⦂ ctx-imp A B p
    → (eB : B ≡ renameᵗ (embed Φ) B″)
    → View-` (rightCtx γ) x N″ B″
    → Φ ∣ γ ⊢ C.` x ⊑ N″ ⦂ A ⊑ B″ ∶ back eqμ p B″ eB
  case-var eqμ r x∈ eB (v-` y∈) with rel-lookup r x∈
  case-var eqμ r x∈ eB (v-` y∈) | B₀″ , e₀ , x∈ᵖ , y∈′
      with lookup-uniqueᴳ y∈′ y∈
  case-var eqμ r x∈ eB (v-` y∈) | B₀″ , e₀ , x∈ᵖ , y∈′ | refl =
    reindex (back-irrel eqμ _ _ e₀ eB) (x⊑x x∈ᵖ)

  case-ƛ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {N N′ A A′ B B′ pA pB B″ Nᶜ N″}
    → μ ∣ ctx-imp A A′ pA ∷ γᴳ ⊢ᴳ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
    → (eB : A′ ⇒ B′ ≡ renameᵗ (embed Φ) B″)
    → ElabE (A ∷ srcCtxⁱ γᴳ) N Nᶜ B
    → View-ƛ (embedᶜ Φ) (rightCtx γ) A′ N′ N″ B″
    → Φ ∣ γ ⊢ C.ƛ Nᶜ ⊑ N″ ⦂ A ⇒ B ⊑ B″ ∶ back eqμ (I.⇒⊑⇒ pA pB) B″ eB
  case-ƛ eqμ r N⊑ eB Nᴱ (v-ƛ {A″ = A″} eA eN Nᴱ″) =
    ƛ⊑ƛ (elab-prec eqμ (rel-∷ A″ (⇒-inj₁ eB) r) N⊑ eN (⇒-inj₂ eB) Nᴱ Nᴱ″)

  case-· : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {L L′ M M′ A A′ B B′ C C′ pA pB pC}
    → μ ∣ γᴳ ⊢ᴳ L ⊑ L′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ I.⇒⊑⇒ pA pB
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → ∀ {B″ Lᶜ Mᶜ A₁ D N″} {ν : Env∼ Δ}
    → (eB : B′ ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) L Lᶜ (A₁ ⇒ B)
    → ElabE (srcCtxⁱ γᴳ) M Mᶜ D
    → (c : ν ⊢ D ∼ A₁) → Eager c
    → View-app (embedᶜ Φ) (rightCtx γ) L′ M′ N″ B″
    → Φ ∣ γ ⊢ Lᶜ C.· (Mᶜ C.⟨ c ⟩) ⊑ N″ ⦂ B ⊑ B″ ∶ back eqμ pB B″ eB
  case-· eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec V
      with left-align Lᴱ L⊑ | left-align Mᴱ M⊑
  case-· eqμ r {pA = pA} {pB = pB} L⊑ M⊑ {B″ = B″} eB Lᴱ Mᴱ c Ec
      (v-· {A″ = A″} eL eM₀ Lᴱ″ Mᴱ″ c″ Ec″) | refl | refl =
    reindex (back-irrel eqμ pB B″ (⇒-inj₂ eBL) eB)
      (·⊑· (elab-prec eqμ r L⊑ eL eBL Lᴱ Lᴱ″)
        (⟨⟩⊑⟨⟩ (elab-prec eqμ r M⊑ eM₀ (right-align r M⊑ eM₀ Mᴱ″) Mᴱ Mᴱ″)
          c c″ Ec Ec″ (back eqμ pA A″ (⇒-inj₁ eBL))))
    where
    eBL = right-align r L⊑ eL Lᴱ″
  case-· eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec
      (v-·★ eL eM₀ Lᴱ″ Mᴱ″ c″ Ec″ d″ Ed″) | refl | refl =
    ⊥-elim (⇒≢★ (right-align r L⊑ eL Lᴱ″))

  case-·★ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {L L′ M M′ A B C C′ pA pB pC}
    → μ ∣ γᴳ ⊢ᴳ L ⊑ L′ ⦂ A ⇒ B ⊑ ★ ∶ I.⇒⊑★ pA pB
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → ∀ {B″ Lᶜ Mᶜ A₁ D N″} {ν : Env∼ Δ}
    → (eB : ★ ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) L Lᶜ (A₁ ⇒ B)
    → ElabE (srcCtxⁱ γᴳ) M Mᶜ D
    → (c : ν ⊢ D ∼ A₁) → Eager c
    → View-app (embedᶜ Φ) (rightCtx γ) L′ M′ N″ B″
    → Φ ∣ γ ⊢ Lᶜ C.· (Mᶜ C.⟨ c ⟩) ⊑ N″ ⦂ B ⊑ B″ ∶ back eqμ pB B″ eB
  case-·★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec V
      with left-align Lᴱ L⊑ | left-align Mᴱ M⊑
  case-·★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec
      (v-· eL eM₀ Lᴱ″ Mᴱ″ c″ Ec″) | refl | refl =
    ⊥-elim (★≢⇒ (right-align r L⊑ eL Lᴱ″))
  case-·★ eqμ r {pA = pA} {pB = pB} L⊑ M⊑ eB Lᴱ Mᴱ c Ec
      (v-·★ eL eM₀ Lᴱ″ Mᴱ″ c″ Ec″ d″ Ed″) | refl | refl =
    reindex (back-irrel eqμ pB ★ refl eB)
      (·⊑· (⊑⟨⟩ (elab-prec eqμ r L⊑ eL refl Lᴱ Lᴱ″) c″ Ec″
              (⇒⊑⇒ (back eqμ pA ★ refl) (back eqμ pB ★ refl)))
        (⟨⟩⊑⟨⟩ (elab-prec eqμ r M⊑ eM₀ (right-align r M⊑ eM₀ Mᴱ″) Mᴱ Mᴱ″)
          c d″ Ec Ed″ (back eqμ pA ★ refl)))

  case-★★ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {L L′ M M′ C C′ pC}
    → μ ∣ γᴳ ⊢ᴳ L ⊑ L′ ⦂ ★ ⊑ ★ ∶ I.★⊑★
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC
    → ∀ {B″ Lᶜ Mᶜ A₀ N″} {ν ν′ : Env∼ Δ}
    → (eB : ★ ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) L Lᶜ ★
    → ElabE (srcCtxⁱ γᴳ) M Mᶜ A₀
    → (c : ν ⊢ ★ ∼ (★ ⇒ ★)) → Eager c
    → (d : ν′ ⊢ A₀ ∼ ★) → Eager d
    → View-app (embedᶜ Φ) (rightCtx γ) L′ M′ N″ B″
    → Φ ∣ γ ⊢ (Lᶜ C.⟨ c ⟩) C.· (Mᶜ C.⟨ d ⟩) ⊑ N″ ⦂ ★ ⊑ B″
        ∶ back eqμ I.★⊑★ B″ eB
  case-★★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec d Ed V with left-align Mᴱ M⊑
  case-★★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec d Ed
      (v-· eL eM₀ Lᴱ″ Mᴱ″ c″ Ec″) | refl =
    ⊥-elim (★≢⇒ (right-align r L⊑ eL Lᴱ″))
  case-★★ eqμ r L⊑ M⊑ eB Lᴱ Mᴱ c Ec d Ed
      (v-·★ eL eM₀ Lᴱ″ Mᴱ″ c″ Ec″ d″ Ed″) | refl =
    ·⊑· (⟨⟩⊑⟨⟩ (elab-prec eqμ r L⊑ eL refl Lᴱ Lᴱ″) c c″ Ec Ec″
          (⇒⊑⇒ ★⊑★ ★⊑★))
      (⟨⟩⊑⟨⟩ (elab-prec eqμ r M⊑ eM₀ (right-align r M⊑ eM₀ Mᴱ″) Mᴱ Mᴱ″)
        d d″ Ed Ed″ ★⊑★)

  case-ΛΛ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γᴳ′ : CtxImp (I.extᵐ μ)} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → LiftCtxⁱ (I.extᵐ μ) γᴳ γᴳ′
    → ∀ {V V′ A B p B″ N N″}
    → I.extᵐ μ ∣ γᴳ′ ⊢ᴳ V ⊑ V′ ⦂ A ⊑ B ∶ p
    → (eB : `∀ B ≡ renameᵗ (embed Φ) B″)
    → C.Value N
    → ElabE (⇑ᶜ (srcCtxⁱ γᴳ)) V N A
    → View-Λ (embedᶜ Φ) (rightCtx γ) V′ N″ B″
    → Φ ∣ γ ⊢ C.Λ N ⊑ N″ ⦂ `∀ A ⊑ B″ ∶ back eqμ (I.∀⊑∀ p) B″ eB
  case-ΛΛ eqμ r liftγ V⊑ eB vN Vᴱ (v-Λ eV vN″ Vᴱ″)
      with rel-lift-pair r liftγ
  case-ΛΛ {Φ = Φ} eqμ r liftγ V⊑ eB vN Vᴱ
      (v-Λ {A″ = A″} eV vN″ Vᴱ″) | γ′ , lp , r′ =
    Λ⊑Λ lp vN vN″
      (elab-prec (env-pair eqμ) r′ V⊑ eV (embed-under-pair Φ A″ eB)
        (subst (λ Γ → ElabE Γ _ _ _) (sym (GTI.srcCtxⁱ-lift liftγ)) Vᴱ)
        (subst (λ Γ → ElabE Γ _ _ _) (sym (lift-right-pair lp)) Vᴱ″))

  case-Λ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γᴳ′ : CtxImp (I.instᵐ μ)} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {V N′ A B p}
    → (Anv : NonVar A) (zA : zero ∈ᵗ A)
    → LiftCtxⁱ (I.instᵐ μ) γᴳ γᴳ′
    → I.instᵐ μ ∣ γᴳ′ ⊢ᴳ V ⊑ G.⇑ᵗᴳ N′ ⦂ A ⊑ ⇑ᵗ B ∶ p
    → ∀ {M″ B″ N N″}
    → N′ ≡ Grenameᵐ (embedᶜ Φ) M″
    → (eB : B ≡ renameᵗ (embed Φ) B″)
    → C.Value N
    → ElabE (⇑ᶜ (srcCtxⁱ γᴳ)) V N A
    → ElabE (rightCtx γ) M″ N″ B″
    → Φ ∣ γ ⊢ C.Λ N ⊑ N″ ⦂ `∀ A ⊑ B″ ∶ back eqμ (I.∀⊑ Anv zA p) B″ eB
  case-Λ eqμ r Anv zA liftγ V⊑ eM eB vN Vᴱ R with rel-lift-only r liftγ
  case-Λ {Φ = Φ} eqμ r Anv zA liftγ V⊑ {M″ = M″} {B″ = B″} eM eB vN Vᴱ R
      | γ′ , lo , r′ =
    Λ⊑ Anv zA lo vN
      (elab-prec (env-only eqμ) r′ V⊑
        (trans (cong G.⇑ᵗᴳ eM) (Grenameᵐ-skip (embedᶜ Φ) M″))
        (embed-under-only Φ B″ eB)
        (subst (λ Γ → ElabE Γ _ _ _) (sym (GTI.srcCtxⁱ-lift liftγ)) Vᴱ)
        (subst (λ Γ → ElabE Γ _ _ _) (sym (lift-right-only lo)) R))

  case-[][] : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {M M′ T T′ A A₁ B p}
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ `∀ A ⊑ `∀ B ∶ I.∀⊑∀ p
    → (q : μ I.⊢ T ⊑ T′)
    → (r′ : μ I.⊢ A [ T ]ᵗ ⊑ B [ T′ ]ᵗ)
    → ∀ {B″ N N″}
    → (eB : B [ T′ ]ᵗ ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) M N (`∀ A₁)
    → View-[] (embedᶜ Φ) (rightCtx γ) M′ T′ N″ B″
    → Φ ∣ γ ⊢ N C.⦂∀ A₁ [ T ] ⊑ N″ ⦂ A [ T ]ᵗ ⊑ B″ ∶ back eqμ r′ B″ eB
  case-[][] eqμ r M⊑ q r′ eB Mᴱ V with left-align Mᴱ M⊑
  case-[][] eqμ r M⊑ q r′ eB Mᴱ
      (v-[] {B₀″ = B₀″} {T″ = T″} eM₀ eT Mᴱ″) | refl =
    •⊑• (elab-prec eqμ r M⊑ eM₀ (right-align r M⊑ eM₀ Mᴱ″) Mᴱ Mᴱ″)
      (back eqμ q T″ eT) (back eqμ r′ (B₀″ [ T″ ]ᵗ) eB)

  case-[] : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → ∀ {M M′ T A A₁ B p Anv zA}
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ `∀ A ⊑ B ∶ I.∀⊑ Anv zA p
    → (q : μ I.⊢ T ⊑ ★)
    → (r′ : μ I.⊢ A [ T ]ᵗ ⊑ B)
    → ∀ {M″ B″ N N″}
    → M′ ≡ Grenameᵐ (embedᶜ Φ) M″
    → (eB : B ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) M N (`∀ A₁)
    → ElabE (rightCtx γ) M″ N″ B″
    → Φ ∣ γ ⊢ N C.⦂∀ A₁ [ T ] ⊑ N″ ⦂ A [ T ]ᵗ ⊑ B″ ∶ back eqμ r′ B″ eB
  case-[] eqμ r M⊑ q r′ eM eB Mᴱ R with left-align Mᴱ M⊑
  case-[] eqμ r M⊑ q r′ {B″ = B″} eM eB Mᴱ R | refl =
    •⊑ (elab-prec eqμ r M⊑ eM eB Mᴱ R) (back eqμ q ★ refl)
      (back eqμ r′ B″ eB)

  case-κ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γ : PrecCtx Φ}
    → (κ : Const) → ∀ {B″ N″}
    → (eB : constTy κ ≡ renameᵗ (embed Φ) B″)
    → View-$ κ N″ B″
    → Φ ∣ γ ⊢ C.$ κ ⊑ N″ ⦂ constTy κ ⊑ B″
        ∶ back eqμ (GTI.constTy-⊑ μ κ) B″ eB
  case-κ eqμ κ eB v-$ = reindex (sym (back-const eqμ κ eB)) (κ⊑κ κ)

  case-⊕ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {μ : I.ImpEnv Δ}
      (eqμ : ∀ X → μ X ≡ impEnvᶜ Φ X) {γᴳ : CtxImp μ} {γ : PrecCtx Φ}
    → CtxRel eqμ γᴳ γ
    → (op : Prim)
    → ∀ {L L′ M M′ A A′ B B′ pA pB}
    → μ ∣ γᴳ ⊢ᴳ L ⊑ L′ ⦂ A ⊑ A′ ∶ pA
    → μ ∣ γᴳ ⊢ᴳ M ⊑ M′ ⦂ B ⊑ B′ ∶ pB
    → ∀ {B″ Lᶜ Mᶜ A₁ B₁ N″} {ν ν′ : Env∼ Δ}
    → (eB : primResultTy op ≡ renameᵗ (embed Φ) B″)
    → ElabE (srcCtxⁱ γᴳ) L Lᶜ A₁
    → (c : ν ⊢ A₁ ∼ primArgTy op) → Eager c
    → ElabE (srcCtxⁱ γᴳ) M Mᶜ B₁
    → (d : ν′ ⊢ B₁ ∼ primArgTy op) → Eager d
    → View-⊕ (embedᶜ Φ) (rightCtx γ) op L′ M′ N″ B″
    → Φ ∣ γ ⊢ (Lᶜ C.⟨ c ⟩) C.⊕[ op ] (Mᶜ C.⟨ d ⟩) ⊑ N″
        ⦂ primResultTy op ⊑ B″ ∶ back eqμ (GTI.primResultTy-⊑ μ op) B″ eB
  case-⊕ eqμ r op L⊑ M⊑ eB Lᴱ c Ec Mᴱ d Ed V
      with left-align Lᴱ L⊑ | left-align Mᴱ M⊑
  case-⊕ eqμ r op L⊑ M⊑ eB Lᴱ c Ec Mᴱ d Ed
      (v-⊕ eL eM₀ Lᴱ″ c″ Ec″ Mᴱ″ d″ Ed″) | refl | refl =
    reindex (sym (back-prim eqμ op eB))
      (⊕⊑⊕ op
        (⟨⟩⊑⟨⟩ (elab-prec eqμ r L⊑ eL (right-align r L⊑ eL Lᴱ″) Lᴱ Lᴱ″)
          c c″ Ec Ec″ (primArgTy-⊑ op))
        (⟨⟩⊑⟨⟩ (elab-prec eqμ r M⊑ eM₀ (right-align r M⊑ eM₀ Mᴱ″) Mᴱ Mᴱ″)
          d d″ Ed Ed″ (primArgTy-⊑ op)))

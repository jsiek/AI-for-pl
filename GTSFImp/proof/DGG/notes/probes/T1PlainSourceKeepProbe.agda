module proof.DGG.notes.probes.T1PlainSourceKeepProbe where

-- File Charter:
--   * Calibration probe for T1 direct target-frame keep certificates.
--   * Proves the narrow plain-source target reveal/conceal keep theorems
--     by inverting the current CastTermImprecision2 relation.
--   * Confirms that the T10 paired counterexample source shape is not a
--     bare value because an `unseal` reveal wrapper is not a value wrapper.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; [])
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; nonvar-base; nonvar-star; nonvar-fun;
   nonvar-all; renameNonVar; ＇_; `∀)
open import TyStore using (TyStore)
open import TermCtx using (TermCtx)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Primitives using (Const; constTy; κℕ; κ𝔹)
import Conversion as Conv
open import Conversion using
  (Conv↑; Conv↓; id↑; id↓; unseal; seal; ⊢↑-id; ⊢↓-id)
import CastTerms as CT
open import CastTerms using
  (Term; Value; Ctx; ⟨_,_,_⟩; _⊢_⦂_; ƛ_; Λ_; $; _↑_; _↓_;
   _⟨_⟩; ⊢reveal; ⊢conceal)
import Reduction as R
open import Reduction using
  (_—→[_]_; keep; pure-step; id-reveal; id-conceal; conceal-reveal;
   blame-reveal; blame-conceal; ξ-reveal; ξ-conceal)

import proof.Imprecision as PI
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; CtxImp; SameCtx; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof using
  (value-no-step)


data BareValue {Δ : TyCtx} : Term Δ → Set where
  bare-ƛ : (N : Term Δ) → BareValue (ƛ N)
  bare-Λ : ∀ {V : Term (suc Δ)} → Value V → BareValue (Λ V)
  bare-$ : (κ : Const) → BareValue ($ κ)


data NonΛBareValue {Δ : TyCtx} : Term Δ → Set where
  bare-nonΛ-ƛ : (N : Term Δ) → NonΛBareValue (ƛ N)
  bare-nonΛ-$ : (κ : Const) → NonΛBareValue ($ κ)


bare-value : ∀ {Δ} {P : Term Δ} → BareValue P → Value P
bare-value (bare-ƛ N) = ƛ N
bare-value (bare-Λ vV) = Λ vV
bare-value (bare-$ κ) = $ κ


nonΛ-bare-value : ∀ {Δ} {P : Term Δ} → NonΛBareValue P → Value P
nonΛ-bare-value (bare-nonΛ-ƛ N) = ƛ N
nonΛ-bare-value (bare-nonΛ-$ κ) = $ κ


nonΛ-bare->bare : ∀ {Δ} {P : Term Δ} → NonΛBareValue P → BareValue P
nonΛ-bare->bare (bare-nonΛ-ƛ N) = bare-ƛ N
nonΛ-bare->bare (bare-nonΛ-$ κ) = bare-$ κ


unseal-reveal-not-bare-value : ∀ {Δ} {V : Term Δ} {X : TyVar Δ}
    {R : Ty Δ}
  → BareValue (V ↑ unseal X R)
  → ⊥
unseal-reveal-not-bare-value ()


unseal-reveal-not-value : ∀ {Δ} {V : Term Δ} {X : TyVar Δ}
    {R : Ty Δ}
  → Value (V ↑ unseal X R)
  → ⊥
unseal-reveal-not-value (vV CT.↑ ())


imprecision-nonvar-to-var : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A : Ty Δ} {X : TyVar Δ}
  → NonVar A
  → I._⊢_⊑_ μ A (＇ X)
  → ⊥
imprecision-nonvar-to-var nonvar-base ()
imprecision-nonvar-to-var nonvar-star ()
imprecision-nonvar-to-var nonvar-fun ()
imprecision-nonvar-to-var nonvar-all
    (I.∀⊑ Anv zero∈A A⊑X) =
  imprecision-nonvar-to-var Anv A⊑X


ctx-imp-eq : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p p′ : A ⊑ᵂ⟨ W ⟩ B}
  → CTI2.ctx-imp A B p ≡ CTI2.ctx-imp A B p′
ctx-imp-eq {W = W} {A = A} {B = B} {p = p} {p′ = p′} =
  cong (λ r → CTI2.ctx-imp {W = W} A B r) (PI.⊑-unique p p′)


sameCtx-eq : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ γ′ : CtxImp W}
  → SameCtx γ γ′
  → γ ≡ γ′
sameCtx-eq CTI2.same-[] = refl
sameCtx-eq (CTI2.same-∷ sc) =
  cong₂ _∷_ ctx-imp-eq (sameCtx-eq sc)


sameCtx-transport : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ γ′ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → SameCtx γ γ′
  → W ∣ γ′ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ p
sameCtx-transport {W = W} {γ = γ} {M = M} {N = N} {p = p} sc rel =
  subst≡ (λ γ₀ → W ∣ γ₀ ⊢² M ⊑ N ∶ p)
    (sym (sameCtx-eq sc)) rel


⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} rel =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r)
    (PI.⊑-unique p q) rel


target-typing-id-reveal-strip : ∀ {Δ} {Σ : TyStore Δ}
    {Γ : TermCtx Δ} {N : Term Δ} {B : Ty Δ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N ↑ id↑ B ⦂ B
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N ⦂ B
target-typing-id-reveal-strip (⊢reveal ⊢↑-id N⊢) = N⊢


target-typing-id-conceal-strip : ∀ {Δ} {Σ : TyStore Δ}
    {Γ : TermCtx Δ} {N : Term Δ} {B : Ty Δ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N ↓ id↓ B ⦂ B
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N ⦂ B
target-typing-id-conceal-strip (⊢conceal ⊢↓-id N⊢) = N⊢


plain-source-nonvarᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → BareValue P
  → W ∣ γ ⊢² P ⊑ N ∶ p
  → NonVar A
plain-source-nonvarᴸ () (CTI2.x⊑x² x∈)
plain-source-nonvarᴸ (bare-ƛ M) (CTI2.ƛ⊑ƛ² rel) = nonvar-fun
plain-source-nonvarᴸ () (CTI2.·⊑·² rel₁ rel₂)
plain-source-nonvarᴸ (bare-Λ vV)
    (CTI2.Λ⊑Λ² liftγ vL vR rel q) =
  nonvar-all
plain-source-nonvarᴸ (bare-Λ vV)
    (CTI2.Λ⊑² Anv zero∈A liftγ vL target⊢ rel q) =
  nonvar-all
plain-source-nonvarᴸ (bare-Λ vV)
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vL target⊢ rel q) =
  nonvar-all
plain-source-nonvarᴸ () (CTI2.•⊑•² p∀ rel q r)
plain-source-nonvarᴸ () (CTI2.•⊑² p∀ rel q r)
plain-source-nonvarᴸ (bare-$ (κℕ n)) (CTI2.κ⊑κ² .(κℕ n) p) =
  nonvar-base
plain-source-nonvarᴸ (bare-$ (κ𝔹 b)) (CTI2.κ⊑κ² .(κ𝔹 b) p) =
  nonvar-base
plain-source-nonvarᴸ () (CTI2.cast⊑cast² c c′ rel q)
plain-source-nonvarᴸ bare (CTI2.⊑cast² c′ rel q) =
  plain-source-nonvarᴸ bare rel
plain-source-nonvarᴸ bare (CTI2.⊑reveal² mono rb sc c′⊢ rel q) =
  plain-source-nonvarᴸ bare rel
plain-source-nonvarᴸ bare (CTI2.⊑conceal² mono rb sc c′⊢ rel q) =
  plain-source-nonvarᴸ bare rel
plain-source-nonvarᴸ () (CTI2.cast⊑² c rel q)
plain-source-nonvarᴸ () (CTI2.reveal⊑² mono rb sc c⊢ rel q)
plain-source-nonvarᴸ () (CTI2.conceal⊑² partner mono rb sc c⊢ rel q)
plain-source-nonvarᴸ ()
    (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ rel q)
plain-source-nonvarᴸ ()
    (CTI2.conceal⊑conceal² partner mono rb sc c⊢ c′⊢ rel q)
plain-source-nonvarᴸ ()
    (CTI2.packaged-seal-star² partner mono rb sc c⊢ c′⊢ rel seal-rel q)
plain-source-nonvarᴸ () (CTI2.blame⊑² target⊢ p)
plain-source-nonvarᴸ () (CTI2.⊕⊑⊕² op rel₁ rel₂ r)


plain-source-to-target-var-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {X : TyVar Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ ＇ X}
  → BareValue P
  → W ∣ γ ⊢² P ⊑ N ∶ p
  → ⊥
plain-source-to-target-var-empty {W = W} {p = p} bare rel =
  imprecision-nonvar-to-var
    (renameNonVar (toRenameᵗ (CTI2.ηᴸʷ W))
      (plain-source-nonvarᴸ bare rel))
    p


target-reveal-id-strip : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → NonΛBareValue P
  → W ∣ γ ⊢² P ⊑ N ↑ id↑ B ∶ q
  → W ∣ γ ⊢² P ⊑ N ∶ q
target-reveal-id-strip bare
    (CTI2.⊑reveal² {p = p} mono CTI2.rebase-idᴿ sc
      CTI2.⊢↑-idˣ rel q) =
  ⊢²-retarget (sameCtx-transport sc rel)
target-reveal-id-strip ()
    (CTI2.Λ⊑² Anv zero∈A liftγ vL target⊢ rel q)
target-reveal-id-strip ()
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vL target⊢ rel q)
target-reveal-id-strip ()
    (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ rel q)
target-reveal-id-strip () (CTI2.blame⊑² target⊢ p)


target-conceal-id-strip : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → NonΛBareValue P
  → W ∣ γ ⊢² P ⊑ N ↓ id↓ B ∶ q
  → W ∣ γ ⊢² P ⊑ N ∶ q
target-conceal-id-strip bare
    (CTI2.⊑conceal² {p = p} mono CTI2.rebase-idᴿ sc
      CTI2.⊢↓-idˣ rel q) =
  ⊢²-retarget (sameCtx-transport sc rel)
target-conceal-id-strip ()
    (CTI2.Λ⊑² Anv zero∈A liftγ vL target⊢ rel q)
target-conceal-id-strip ()
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vL target⊢ rel q)
target-conceal-id-strip ()
    (CTI2.conceal⊑conceal² partner mono rb sc c⊢ c′⊢ rel q)
target-conceal-id-strip () (CTI2.blame⊑² target⊢ p)


target-unseal-reveal-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {R : Ty Δᴿ} {X : TyVar Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ R}
  → NonΛBareValue P
  → W ∣ γ ⊢² P ⊑ (V ↓ seal X R) ↑ unseal X R ∶ q
  → ⊥
target-unseal-reveal-empty bare
    (CTI2.⊑reveal² mono (CTI2.rebase-varᴿ rb) sc
      (CTI2.⊢↑-unsealˣ X∈) rel q) =
  plain-source-to-target-var-empty (nonΛ-bare->bare bare) rel
target-unseal-reveal-empty ()
    (CTI2.Λ⊑² Anv zero∈A liftγ vL target⊢ rel q)
target-unseal-reveal-empty ()
    (CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vL target⊢ rel q)
target-unseal-reveal-empty ()
    (CTI2.reveal⊑reveal² mono rb sc c⊢ c′⊢ rel q)
target-unseal-reveal-empty () (CTI2.blame⊑² target⊢ p)


PlainSourceTargetRevealKeepᵀ : Set
PlainSourceTargetRevealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → BareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


PlainSourceTargetConcealKeepᵀ : Set
PlainSourceTargetConcealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → BareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


NonΛSourceTargetRevealKeepᵀ : Set
NonΛSourceTargetRevealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → NonΛBareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


NonΛSourceTargetConcealKeepᵀ : Set
NonΛSourceTargetConcealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → NonΛBareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


nonΛ-source-target-reveal-keep : NonΛSourceTargetRevealKeepᵀ
nonΛ-source-target-reveal-keep bare vN rel
    (pure-step (id-reveal vN′)) finalV =
  target-reveal-id-strip bare rel
nonΛ-source-target-reveal-keep bare vN rel
    (pure-step (conceal-reveal vV)) finalV =
  ⊥-elim (target-unseal-reveal-empty bare rel)
nonΛ-source-target-reveal-keep bare () rel
    (pure-step blame-reveal) finalV
nonΛ-source-target-reveal-keep bare vN rel
    (ξ-reveal step refl) finalV =
  ⊥-elim (value-no-step vN step)


nonΛ-source-target-conceal-keep : NonΛSourceTargetConcealKeepᵀ
nonΛ-source-target-conceal-keep bare vN rel
    (pure-step (id-conceal vN′)) finalV =
  target-conceal-id-strip bare rel
nonΛ-source-target-conceal-keep bare () rel
    (pure-step blame-conceal) finalV
nonΛ-source-target-conceal-keep bare vN rel
    (ξ-conceal step refl) finalV =
  ⊥-elim (value-no-step vN step)

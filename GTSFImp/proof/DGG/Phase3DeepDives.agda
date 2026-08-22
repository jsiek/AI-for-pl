module proof.DGG.Phase3DeepDives where

-- File Charter:
--   * Records Phase-3 single-step deep-dive checkpoints for selected
--     source-derived reachability catalog entries.
--   * Starts each source-derived pair from compile-preserves-imprecision².
--   * Makes the allocation-world pattern explicit at the checked steps:
--     fresh pivots are parked by identity/both-side or right-only extension,
--     not by re-parking an existing pivot.
--   * Depends on ReachabilityCatalog, CompilePreservesImprecision2, Eval, and
--     the version-2 DGG relation.

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.List using ([])
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-bind; Z∋)
import Imprecision as I
import GradualTerms as G
import GradualTermImprecision as GTI
open import Consistency using
  (_⊢_∼_; id; renameᵐᶜ; symᶜ; toRenameᵗ; wk↪ᵗ; ？_)
open import Compile using (compile)
open import Primitives using (κℕ)
import CastTerms as C
open import Conversion using (〖_,_↑_〗)
open import Reduction using (StoreChange; bind; keep)
open import Eval using (step?)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.ExampleTerms as Ex
import proof.DGG.OneStep as Step
import proof.DGG.Examples2 as Ex2
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS

open Step using (Δ′; change; next; reduction)

------------------------------------------------------------------------
-- Shared initial theorem surface
------------------------------------------------------------------------

entry-initial² : (e : RC.SourceEntry)
  → CPI2.initialWorld I.idᵐ store-empty
      ∣ CPI2.initialCtx {Σ = store-empty} []
      ⊢² proj₁ (compile {Σ = store-empty}
        (GTI.gradual-term-imprecision-source-typing
          (RC.SourceEntry.initial⊑ᴳ e)))
      ⊑ proj₁ (compile {Σ = store-empty}
        (GTI.gradual-term-imprecision-target-typing
          (RC.SourceEntry.initial⊑ᴳ e)))
      ∶ CPI2.initial-⊑ {Σ = store-empty}
        (RC.SourceEntry.type⊑ᴳ e)
entry-initial² e =
  CPI2.compile-preserves-imprecision² (RC.SourceEntry.initial⊑ᴳ e)

bothBind-freshᴸ-parked : ∀ {Δᴸ Δᴿ Δ v A B}
    {W : CTX.World Δᴸ Δᴿ Δ}
  → toRenameᵗ (CTX.ηᴸʷ (CTX.bothBindWorld v W A B)) Fin.zero
      ≡ Fin.zero
bothBind-freshᴸ-parked = refl

bothBind-freshᴿ-parked : ∀ {Δᴸ Δᴿ Δ v A B}
    {W : CTX.World Δᴸ Δᴿ Δ}
  → toRenameᵗ (CTX.ηᴿʷ (CTX.bothBindWorld v W A B)) Fin.zero
      ≡ Fin.zero
bothBind-freshᴿ-parked = refl

rightOnly-freshᴿ-parked : ∀ {Δᴸ Δᴿ Δ B}
    {W : CTX.World Δᴸ Δᴿ Δ}
  → toRenameᵗ (CTX.ηᴿʷ (CTX.rightOnlyWorld W B)) Fin.zero
      ≡ Fin.zero
rightOnly-freshᴿ-parked = refl

------------------------------------------------------------------------
-- D2. adversarial-source-chain, first parked allocation checkpoint
------------------------------------------------------------------------

adversarial-source-chain-initial² :
  CPI2.initialWorld I.idᵐ store-empty
    ∣ CPI2.initialCtx {Σ = store-empty} []
    ⊢² proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing
        (RC.SourceEntry.initial⊑ᴳ RC.adversarial-source-chain)))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing
        (RC.SourceEntry.initial⊑ᴳ RC.adversarial-source-chain)))
    ∶ CPI2.initial-⊑ {Σ = store-empty}
      (RC.SourceEntry.type⊑ᴳ RC.adversarial-source-chain)
adversarial-source-chain-initial² =
  entry-initial² RC.adversarial-source-chain

adversarial-source-chain₀ : C.Term 0
adversarial-source-chain₀ =
  proj₁ (compile {Σ = store-empty}
    (RC.typingᴸ RC.adversarial-source-chain))

adversarial-source-chain-step₀ :
  Step.OneStep store-empty adversarial-source-chain₀
adversarial-source-chain-step₀ =
  Step.from-just-step (step? store-empty adversarial-source-chain₀) refl

adversarial-source-chain-change₀ :
  change adversarial-source-chain-step₀ ≡ bind RC.ℕ₀
adversarial-source-chain-change₀ = refl

adversarial-source-chain-world₁ : CTX.World 1 1 1
adversarial-source-chain-world₁ =
  CTX.bothBindWorld I.X⊑X
    (CPI2.initialWorld I.idᵐ store-empty) RC.ℕ₀ RC.ℕ₀

adversarial-source-chain-X-rep₁ :
  CTX.StoreRepImp adversarial-source-chain-world₁ Fin.zero Fin.zero
adversarial-source-chain-X-rep₁ =
  CTX.store-rep-imp (Ex2.ℕ⊑ℕ² {W = adversarial-source-chain-world₁})

adversarial-source-chain-rebase₁ :
  CTX.RebaseAt adversarial-source-chain-world₁
    adversarial-source-chain-world₁ Fin.zero Fin.zero
adversarial-source-chain-rebase₁ =
  CTX.sameWorldRebaseAt refl adversarial-source-chain-X-rep₁

adversarial-source-chain-reveal₁-⊢ˣ :
  CTX.sourceStoreʷ adversarial-source-chain-world₁
    Conv.⊢↑[ just Fin.zero ]
      〖 Fin.zero , ⇑ᵗ RC.ℕ₀ ↑ RC.X₀⇒X₀ 〗
adversarial-source-chain-reveal₁-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both
    (Conv.⊢↓-sealˣ (Z∋ refl))
    (Conv.⊢↑-unsealˣ (Z∋ refl))

adversarial-source-chain-lambda₁ :
  adversarial-source-chain-world₁ ∣ [] ⊢²
    proj₁ (compile {Σ = store-bind store-empty RC.ℕ₀}
      (G.⊢ƛ (RC.idAtX³⊢ {Γ = []})))
    ⊑ proj₁ (compile {Σ = store-bind store-empty RC.ℕ₀}
      (G.⊢ƛ (RC.idAtX³⊢ {Γ = []})))
    ∶ CPI2.initial-⊑ {Σ = store-bind store-empty RC.ℕ₀}
      (RC.refl⊑ᵗ (CTX.impEnvʷ adversarial-source-chain-world₁)
        RC.X₀⇒X₀)
adversarial-source-chain-lambda₁ =
  CPI2.compile-preserves-imprecision²
    (RC.reflᴳ (CTX.impEnvʷ adversarial-source-chain-world₁)
      (G.⊢ƛ (RC.idAtX³⊢ {Γ = []})))

adversarial-source-chain-function₁ :
  adversarial-source-chain-world₁ ∣ [] ⊢²
    proj₁ (compile {Σ = store-bind store-empty RC.ℕ₀}
      (G.⊢ƛ (RC.idAtX³⊢ {Γ = []})))
      C.↑ 〖 Fin.zero , ⇑ᵗ RC.ℕ₀ ↑ RC.X₀⇒X₀ 〗
    ⊑ proj₁ (compile {Σ = store-bind store-empty RC.ℕ₀}
      (G.⊢ƛ (RC.idAtX³⊢ {Γ = []})))
      C.↑ 〖 Fin.zero , ⇑ᵗ RC.ℕ₀ ↑ RC.X₀⇒X₀ 〗
    ∶ Ex2.ℕ⇒ℕ⊑ℕ⇒ℕ² {W = adversarial-source-chain-world₁}
adversarial-source-chain-function₁ =
  CTI2.reveal⊑reveal² (λ _ eq → eq)
    adversarial-source-chain-rebase₁ CTX.same-[]
    adversarial-source-chain-reveal₁-⊢ˣ
    adversarial-source-chain-reveal₁-⊢ˣ
    adversarial-source-chain-lambda₁
    (Ex2.ℕ⇒ℕ⊑ℕ⇒ℕ² {W = adversarial-source-chain-world₁})

adversarial-source-chain-arg-cast₁ :
  _ ⊢ ⇑ᵗ RC.ℕ₀ ∼ ⇑ᵗ RC.ℕ₀
adversarial-source-chain-arg-cast₁ =
  renameᵐᶜ wk↪ᵗ (symᶜ (id (‵ `ℕ)))

adversarial-source-chain-argument₁ :
  adversarial-source-chain-world₁ ∣ [] ⊢²
    C.$ (κℕ 7) C.⟨ adversarial-source-chain-arg-cast₁ ⟩
    ⊑ C.$ (κℕ 7) C.⟨ adversarial-source-chain-arg-cast₁ ⟩
    ∶ Ex2.ℕ⊑ℕ² {W = adversarial-source-chain-world₁}
adversarial-source-chain-argument₁ =
  CTI2.cast⊑cast² adversarial-source-chain-arg-cast₁
    adversarial-source-chain-arg-cast₁
    (CTI2.κ⊑κ² (κℕ 7)
      (Ex2.ℕ⊑ℕ² {W = adversarial-source-chain-world₁}))
    (Ex2.ℕ⊑ℕ² {W = adversarial-source-chain-world₁})

adversarial-source-chain-checkpoint₁ :
  adversarial-source-chain-world₁ ∣ [] ⊢²
    next adversarial-source-chain-step₀
    ⊑ next adversarial-source-chain-step₀
    ∶ Ex2.ℕ⊑ℕ² {W = adversarial-source-chain-world₁}
adversarial-source-chain-checkpoint₁ =
  CTI2.·⊑·² adversarial-source-chain-function₁
    adversarial-source-chain-argument₁

adversarial-source-chain-screen₀ : C.Term 0
adversarial-source-chain-screen₀ =
  RS.Entry.more-precise (RC.compiled RC.adversarial-source-chain)

adversarial-source-chain-screen-step₀ :
  Step.OneStep store-empty adversarial-source-chain-screen₀
adversarial-source-chain-screen-step₀ =
  Step.from-just-step
    (step? store-empty adversarial-source-chain-screen₀) refl

adversarial-source-chain-screen-change₀ :
  change adversarial-source-chain-screen-step₀ ≡ bind RC.ℕ₀
adversarial-source-chain-screen-change₀ = refl

adversarial-source-chain-screen₁ :
  C.Term (Δ′ adversarial-source-chain-screen-step₀)
adversarial-source-chain-screen₁ =
  next adversarial-source-chain-screen-step₀

adversarial-source-chain-screen-store₁ :
  TyStore (Δ′ adversarial-source-chain-screen-step₀)
adversarial-source-chain-screen-store₁ =
  Step.store-after adversarial-source-chain-screen-step₀

adversarial-source-chain-screen-step₁ :
  Step.OneStep
    adversarial-source-chain-screen-store₁
    adversarial-source-chain-screen₁
adversarial-source-chain-screen-step₁ =
  Step.from-just-step
    (step? adversarial-source-chain-screen-store₁
      adversarial-source-chain-screen₁)
    refl

adversarial-source-chain-screen-change₁ :
  change adversarial-source-chain-screen-step₁ ≡ keep
adversarial-source-chain-screen-change₁ = refl

adversarial-source-chain-screen₂ :
  C.Term (Δ′ adversarial-source-chain-screen-step₁)
adversarial-source-chain-screen₂ =
  next adversarial-source-chain-screen-step₁

adversarial-source-chain-screen-store₂ :
  TyStore (Δ′ adversarial-source-chain-screen-step₁)
adversarial-source-chain-screen-store₂ =
  Step.store-after adversarial-source-chain-screen-step₁

adversarial-source-chain-screen-step₂ :
  Step.OneStep
    adversarial-source-chain-screen-store₂
    adversarial-source-chain-screen₂
adversarial-source-chain-screen-step₂ =
  Step.from-just-step
    (step? adversarial-source-chain-screen-store₂
      adversarial-source-chain-screen₂)
    refl

adversarial-source-chain-screen-change₂ :
  change adversarial-source-chain-screen-step₂ ≡ keep
adversarial-source-chain-screen-change₂ = refl

adversarial-source-chain-screen₃ :
  C.Term (Δ′ adversarial-source-chain-screen-step₂)
adversarial-source-chain-screen₃ =
  next adversarial-source-chain-screen-step₂

adversarial-source-chain-screen-store₃ :
  TyStore (Δ′ adversarial-source-chain-screen-step₂)
adversarial-source-chain-screen-store₃ =
  Step.store-after adversarial-source-chain-screen-step₂

adversarial-source-chain-screen-step₃ :
  Step.OneStep
    adversarial-source-chain-screen-store₃
    adversarial-source-chain-screen₃
adversarial-source-chain-screen-step₃ =
  Step.from-just-step
    (step? adversarial-source-chain-screen-store₃
      adversarial-source-chain-screen₃)
    refl

adversarial-source-chain-screen-change₃ :
  change adversarial-source-chain-screen-step₃ ≡ keep
adversarial-source-chain-screen-change₃ = refl

adversarial-source-chain-screen₄ :
  C.Term (Δ′ adversarial-source-chain-screen-step₃)
adversarial-source-chain-screen₄ =
  next adversarial-source-chain-screen-step₃

adversarial-source-chain-screen-store₄ :
  TyStore (Δ′ adversarial-source-chain-screen-step₃)
adversarial-source-chain-screen-store₄ =
  Step.store-after adversarial-source-chain-screen-step₃

adversarial-source-chain-screen-step₄ :
  Step.OneStep
    adversarial-source-chain-screen-store₄
    adversarial-source-chain-screen₄
adversarial-source-chain-screen-step₄ =
  Step.from-just-step
    (step? adversarial-source-chain-screen-store₄
      adversarial-source-chain-screen₄)
    refl

adversarial-source-chain-screen-change₄ :
  change adversarial-source-chain-screen-step₄ ≡ bind (＇ Fin.zero)
adversarial-source-chain-screen-change₄ = refl

adversarial-source-chain-screen₅ :
  C.Term (Δ′ adversarial-source-chain-screen-step₄)
adversarial-source-chain-screen₅ =
  next adversarial-source-chain-screen-step₄

adversarial-source-chain-screen-store₅ :
  TyStore (Δ′ adversarial-source-chain-screen-step₄)
adversarial-source-chain-screen-store₅ =
  Step.store-after adversarial-source-chain-screen-step₄

adversarial-source-chain-screen-step₅ :
  Step.OneStep
    adversarial-source-chain-screen-store₅
    adversarial-source-chain-screen₅
adversarial-source-chain-screen-step₅ =
  Step.from-just-step
    (step? adversarial-source-chain-screen-store₅
      adversarial-source-chain-screen₅)
    refl

adversarial-source-chain-screen-change₅ :
  change adversarial-source-chain-screen-step₅
    ≡ bind (＇ (Fin.suc Fin.zero))
adversarial-source-chain-screen-change₅ = refl

adversarial-source-chain-screen₆ :
  C.Term (Δ′ adversarial-source-chain-screen-step₅)
adversarial-source-chain-screen₆ =
  next adversarial-source-chain-screen-step₅

adversarial-source-chain-screen-store₆ :
  TyStore (Δ′ adversarial-source-chain-screen-step₅)
adversarial-source-chain-screen-store₆ =
  Step.store-after adversarial-source-chain-screen-step₅

adversarial-source-chain-screen-step₆ :
  Step.OneStep
    adversarial-source-chain-screen-store₆
    adversarial-source-chain-screen₆
adversarial-source-chain-screen-step₆ =
  Step.from-just-step
    (step? adversarial-source-chain-screen-store₆
      adversarial-source-chain-screen₆)
    refl

adversarial-source-chain-screen-change₆ :
  change adversarial-source-chain-screen-step₆
    ≡ bind (＇ (Fin.suc (Fin.suc Fin.zero)))
adversarial-source-chain-screen-change₆ = refl

adversarial-source-chain-screen-store₇ :
  TyStore (Δ′ adversarial-source-chain-screen-step₆)
adversarial-source-chain-screen-store₇ =
  Step.store-after adversarial-source-chain-screen-step₆

adversarial-source-chain-world₂ : CTX.World 2 2 2
adversarial-source-chain-world₂ =
  CTX.bothBindWorld I.X⊑X adversarial-source-chain-world₁
    (＇ Fin.zero) (＇ Fin.zero)

adversarial-source-chain-world₃ : CTX.World 3 3 3
adversarial-source-chain-world₃ =
  CTX.bothBindWorld I.X⊑X adversarial-source-chain-world₂
    (＇ (Fin.suc Fin.zero)) (＇ (Fin.suc Fin.zero))

adversarial-source-chain-world₄ : CTX.World 4 4 4
adversarial-source-chain-world₄ =
  CTX.bothBindWorld I.X⊑X adversarial-source-chain-world₃
    (＇ (Fin.suc (Fin.suc Fin.zero)))
    (＇ (Fin.suc (Fin.suc Fin.zero)))

adversarial-source-chain-store₇-parkedᴸ :
  adversarial-source-chain-screen-store₇
    ≡ CTX.sourceStoreʷ adversarial-source-chain-world₄
adversarial-source-chain-store₇-parkedᴸ = refl

adversarial-source-chain-store₇-parkedᴿ :
  adversarial-source-chain-screen-store₇
    ≡ CTX.targetStoreʷ adversarial-source-chain-world₄
adversarial-source-chain-store₇-parkedᴿ = refl

adversarial-source-chain-fresh-pivotᴸ-parked :
  toRenameᵗ (CTX.ηᴸʷ adversarial-source-chain-world₄) Fin.zero
    ≡ Fin.zero
adversarial-source-chain-fresh-pivotᴸ-parked = refl

adversarial-source-chain-fresh-pivotᴿ-parked :
  toRenameᵗ (CTX.ηᴿʷ adversarial-source-chain-world₄) Fin.zero
    ≡ Fin.zero
adversarial-source-chain-fresh-pivotᴿ-parked = refl

adversarial-source-chain-original-pivotᴸ-parked :
  toRenameᵗ (CTX.ηᴸʷ adversarial-source-chain-world₄)
    (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
adversarial-source-chain-original-pivotᴸ-parked = refl

adversarial-source-chain-original-pivotᴿ-parked :
  toRenameᵗ (CTX.ηᴿʷ adversarial-source-chain-world₄)
    (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
adversarial-source-chain-original-pivotᴿ-parked = refl

------------------------------------------------------------------------
-- D3. skew-star-inst / tag-boundary-star-inst, ★ allocation checkpoint
------------------------------------------------------------------------

skew-star-inst-initial² :
  CPI2.initialWorld I.idᵐ store-empty
    ∣ CPI2.initialCtx {Σ = store-empty} []
    ⊢² proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing
        (RC.SourceEntry.initial⊑ᴳ RC.skew-star-inst)))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing
        (RC.SourceEntry.initial⊑ᴳ RC.skew-star-inst)))
    ∶ CPI2.initial-⊑ {Σ = store-empty}
      (RC.SourceEntry.type⊑ᴳ RC.skew-star-inst)
skew-star-inst-initial² = entry-initial² RC.skew-star-inst

tag-boundary-star-inst-initial² :
  CPI2.initialWorld I.idᵐ store-empty
    ∣ CPI2.initialCtx {Σ = store-empty} []
    ⊢² proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing
        (RC.SourceEntry.initial⊑ᴳ RC.tag-boundary-star-inst)))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing
        (RC.SourceEntry.initial⊑ᴳ RC.tag-boundary-star-inst)))
    ∶ CPI2.initial-⊑ {Σ = store-empty}
      (RC.SourceEntry.type⊑ᴳ RC.tag-boundary-star-inst)
tag-boundary-star-inst-initial² =
  entry-initial² RC.tag-boundary-star-inst

star-inst₀ : C.Term 0
star-inst₀ =
  proj₁ (compile {Σ = store-empty} (RC.typingᴸ RC.skew-star-inst))

tag-boundary-star-inst-same-compiled :
  proj₁ (compile {Σ = store-empty}
    (RC.typingᴸ RC.tag-boundary-star-inst))
    ≡ star-inst₀
tag-boundary-star-inst-same-compiled = refl

star-inst-step₀ : Step.OneStep store-empty star-inst₀
star-inst-step₀ =
  Step.from-just-step (step? store-empty star-inst₀) refl

star-inst-change₀ : change star-inst-step₀ ≡ bind ★
star-inst-change₀ = refl

star-inst-world₁ : CTX.World 1 1 1
star-inst-world₁ =
  CTX.bothBindWorld I.X⊑X
    (CPI2.initialWorld I.idᵐ store-empty) ★ ★

star-inst-X-rep₁ :
  CTX.StoreRepImp star-inst-world₁ Fin.zero Fin.zero
star-inst-X-rep₁ = CTX.store-rep-imp I.★⊑★

star-inst-rebase₁ :
  CTX.RebaseAt star-inst-world₁ star-inst-world₁
    Fin.zero Fin.zero
star-inst-rebase₁ =
  CTX.sameWorldRebaseAt refl star-inst-X-rep₁

star-inst-reveal₁-⊢ˣ :
  CTX.sourceStoreʷ star-inst-world₁ Conv.⊢↑[ just Fin.zero ]
    〖 Fin.zero , ★ ↑ RC.X₀⇒★ 〗
star-inst-reveal₁-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-left
    (Conv.⊢↓-sealˣ (Z∋ refl))
    Conv.⊢↑-idˣ

star-inst-lambda₁ :
  star-inst-world₁ ∣ [] ⊢²
    proj₁ (compile {Σ = store-bind store-empty ★}
      (G.⊢ƛ (RC.starBody⊢ {Γ = []})))
    ⊑ proj₁ (compile {Σ = store-bind store-empty ★}
      (G.⊢ƛ (RC.starBody⊢ {Γ = []})))
    ∶ CPI2.initial-⊑ {Σ = store-bind store-empty ★}
      (RC.refl⊑ᵗ (CTX.impEnvʷ star-inst-world₁) RC.X₀⇒★)
star-inst-lambda₁ =
  CPI2.compile-preserves-imprecision²
    (RC.reflᴳ (CTX.impEnvʷ star-inst-world₁)
      (G.⊢ƛ (RC.starBody⊢ {Γ = []})))

star-inst-function₁ :
  star-inst-world₁ ∣ [] ⊢²
    proj₁ (compile {Σ = store-bind store-empty ★}
      (G.⊢ƛ (RC.starBody⊢ {Γ = []})))
      C.↑ 〖 Fin.zero , ★ ↑ RC.X₀⇒★ 〗
    ⊑ proj₁ (compile {Σ = store-bind store-empty ★}
      (G.⊢ƛ (RC.starBody⊢ {Γ = []})))
      C.↑ 〖 Fin.zero , ★ ↑ RC.X₀⇒★ 〗
    ∶ Ex2.★⇒★⊑★⇒★² {W = star-inst-world₁}
star-inst-function₁ =
  CTI2.reveal⊑reveal² (λ _ eq → eq)
    star-inst-rebase₁ CTX.same-[]
    star-inst-reveal₁-⊢ˣ star-inst-reveal₁-⊢ˣ
    star-inst-lambda₁
    (Ex2.★⇒★⊑★⇒★² {W = star-inst-world₁})

star-inst-arg-cast₁ :
  _ ⊢ ⇑ᵗ RC.ℕ₀ ∼ ★
star-inst-arg-cast₁ =
  renameᵐᶜ wk↪ᵗ (symᶜ (？ (id (‵ `ℕ))))

star-inst-argument₁ :
  star-inst-world₁ ∣ [] ⊢²
    C.$ (κℕ 7) C.⟨ star-inst-arg-cast₁ ⟩
    ⊑ C.$ (κℕ 7) C.⟨ star-inst-arg-cast₁ ⟩
    ∶ I.★⊑★
star-inst-argument₁ =
  CTI2.cast⊑cast² star-inst-arg-cast₁ star-inst-arg-cast₁
    (CTI2.κ⊑κ² (κℕ 7)
      (Ex2.ℕ⊑ℕ² {W = star-inst-world₁}))
    I.★⊑★

star-inst-checkpoint₁ :
  star-inst-world₁ ∣ [] ⊢²
    next star-inst-step₀
    ⊑ next star-inst-step₀
    ∶ I.★⊑★
star-inst-checkpoint₁ =
  CTI2.·⊑·² star-inst-function₁ star-inst-argument₁

------------------------------------------------------------------------
-- D4. higher-order-shared-arg trace locators
------------------------------------------------------------------------

higher-order-shared-arg-initial² :
  CPI2.initialWorld I.idᵐ store-empty
    ∣ CPI2.initialCtx {Σ = store-empty} []
    ⊢² proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing
        (RC.SourceEntry.initial⊑ᴳ RC.higher-order-shared-arg)))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing
        (RC.SourceEntry.initial⊑ᴳ RC.higher-order-shared-arg)))
    ∶ CPI2.initial-⊑ {Σ = store-empty}
      (RC.SourceEntry.type⊑ᴳ RC.higher-order-shared-arg)
higher-order-shared-arg-initial² =
  entry-initial² RC.higher-order-shared-arg

higher-order-shared-arg₀ : C.Term 0
higher-order-shared-arg₀ =
  RS.Entry.more-precise (RC.compiled RC.higher-order-shared-arg)

higher-order-shared-arg-step₀ :
  Step.OneStep store-empty higher-order-shared-arg₀
higher-order-shared-arg-step₀ =
  Step.from-just-step (step? store-empty higher-order-shared-arg₀) refl

higher-order-shared-arg-change₀ :
  change higher-order-shared-arg-step₀ ≡ bind RC.∀X⇒X₀
higher-order-shared-arg-change₀ = refl

higher-order-shared-arg₁ : C.Term (Δ′ higher-order-shared-arg-step₀)
higher-order-shared-arg₁ = next higher-order-shared-arg-step₀

higher-order-shared-arg-store₁ :
  TyStore (Δ′ higher-order-shared-arg-step₀)
higher-order-shared-arg-store₁ =
  Step.store-after higher-order-shared-arg-step₀

higher-order-shared-arg-step₁ :
  Step.OneStep higher-order-shared-arg-store₁ higher-order-shared-arg₁
higher-order-shared-arg-step₁ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₁ higher-order-shared-arg₁) refl

higher-order-shared-arg-change₁ :
  change higher-order-shared-arg-step₁ ≡ keep
higher-order-shared-arg-change₁ = refl

higher-order-shared-arg₂ : C.Term (Δ′ higher-order-shared-arg-step₁)
higher-order-shared-arg₂ = next higher-order-shared-arg-step₁

higher-order-shared-arg-store₂ :
  TyStore (Δ′ higher-order-shared-arg-step₁)
higher-order-shared-arg-store₂ =
  Step.store-after higher-order-shared-arg-step₁

higher-order-shared-arg-step₂ :
  Step.OneStep higher-order-shared-arg-store₂ higher-order-shared-arg₂
higher-order-shared-arg-step₂ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₂ higher-order-shared-arg₂) refl

higher-order-shared-arg-change₂ :
  change higher-order-shared-arg-step₂ ≡ keep
higher-order-shared-arg-change₂ = refl

higher-order-shared-arg₃ : C.Term (Δ′ higher-order-shared-arg-step₂)
higher-order-shared-arg₃ = next higher-order-shared-arg-step₂

higher-order-shared-arg-store₃ :
  TyStore (Δ′ higher-order-shared-arg-step₂)
higher-order-shared-arg-store₃ =
  Step.store-after higher-order-shared-arg-step₂

higher-order-shared-arg-step₃ :
  Step.OneStep higher-order-shared-arg-store₃ higher-order-shared-arg₃
higher-order-shared-arg-step₃ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₃ higher-order-shared-arg₃) refl

higher-order-shared-arg-change₃ :
  change higher-order-shared-arg-step₃ ≡ keep
higher-order-shared-arg-change₃ = refl

higher-order-shared-arg₄ : C.Term (Δ′ higher-order-shared-arg-step₃)
higher-order-shared-arg₄ = next higher-order-shared-arg-step₃

higher-order-shared-arg-store₄ :
  TyStore (Δ′ higher-order-shared-arg-step₃)
higher-order-shared-arg-store₄ =
  Step.store-after higher-order-shared-arg-step₃

higher-order-shared-arg-step₄ :
  Step.OneStep higher-order-shared-arg-store₄ higher-order-shared-arg₄
higher-order-shared-arg-step₄ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₄ higher-order-shared-arg₄) refl

higher-order-shared-arg-change₄ :
  change higher-order-shared-arg-step₄ ≡ keep
higher-order-shared-arg-change₄ = refl

higher-order-shared-arg₅ : C.Term (Δ′ higher-order-shared-arg-step₄)
higher-order-shared-arg₅ = next higher-order-shared-arg-step₄

higher-order-shared-arg-store₅ :
  TyStore (Δ′ higher-order-shared-arg-step₄)
higher-order-shared-arg-store₅ =
  Step.store-after higher-order-shared-arg-step₄

higher-order-shared-arg-step₅ :
  Step.OneStep higher-order-shared-arg-store₅ higher-order-shared-arg₅
higher-order-shared-arg-step₅ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₅ higher-order-shared-arg₅) refl

higher-order-shared-arg-change₅ :
  change higher-order-shared-arg-step₅ ≡ keep
higher-order-shared-arg-change₅ = refl

higher-order-shared-arg₆ : C.Term (Δ′ higher-order-shared-arg-step₅)
higher-order-shared-arg₆ = next higher-order-shared-arg-step₅

higher-order-shared-arg-store₆ :
  TyStore (Δ′ higher-order-shared-arg-step₅)
higher-order-shared-arg-store₆ =
  Step.store-after higher-order-shared-arg-step₅

higher-order-shared-arg-step₆ :
  Step.OneStep higher-order-shared-arg-store₆ higher-order-shared-arg₆
higher-order-shared-arg-step₆ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₆ higher-order-shared-arg₆) refl

higher-order-shared-arg-change₆ :
  change higher-order-shared-arg-step₆ ≡ keep
higher-order-shared-arg-change₆ = refl

higher-order-shared-arg₇ : C.Term (Δ′ higher-order-shared-arg-step₆)
higher-order-shared-arg₇ = next higher-order-shared-arg-step₆

higher-order-shared-arg-store₇ :
  TyStore (Δ′ higher-order-shared-arg-step₆)
higher-order-shared-arg-store₇ =
  Step.store-after higher-order-shared-arg-step₆

higher-order-shared-arg-step₇ :
  Step.OneStep higher-order-shared-arg-store₇ higher-order-shared-arg₇
higher-order-shared-arg-step₇ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₇ higher-order-shared-arg₇) refl

higher-order-shared-arg-change₇ :
  change higher-order-shared-arg-step₇ ≡ bind (RC.ℕᵗ {Δ = 1})
higher-order-shared-arg-change₇ = refl

higher-order-shared-arg₈ : C.Term (Δ′ higher-order-shared-arg-step₇)
higher-order-shared-arg₈ = next higher-order-shared-arg-step₇

higher-order-shared-arg-store₈ :
  TyStore (Δ′ higher-order-shared-arg-step₇)
higher-order-shared-arg-store₈ =
  Step.store-after higher-order-shared-arg-step₇

higher-order-shared-arg-step₈ :
  Step.OneStep higher-order-shared-arg-store₈ higher-order-shared-arg₈
higher-order-shared-arg-step₈ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₈ higher-order-shared-arg₈) refl

higher-order-shared-arg-change₈ :
  change higher-order-shared-arg-step₈ ≡ keep
higher-order-shared-arg-change₈ = refl

higher-order-shared-arg₉ : C.Term (Δ′ higher-order-shared-arg-step₈)
higher-order-shared-arg₉ = next higher-order-shared-arg-step₈

higher-order-shared-arg-store₉ :
  TyStore (Δ′ higher-order-shared-arg-step₈)
higher-order-shared-arg-store₉ =
  Step.store-after higher-order-shared-arg-step₈

higher-order-shared-arg-step₉ :
  Step.OneStep higher-order-shared-arg-store₉ higher-order-shared-arg₉
higher-order-shared-arg-step₉ =
  Step.from-just-step
    (step? higher-order-shared-arg-store₉ higher-order-shared-arg₉) refl

higher-order-shared-arg-change₉ :
  change higher-order-shared-arg-step₉ ≡ keep
higher-order-shared-arg-change₉ = refl

------------------------------------------------------------------------
-- D4. parked-world shape at the located allocation
------------------------------------------------------------------------

higher-order-shared-arg-world₀ : CTX.World 0 0 0
higher-order-shared-arg-world₀ =
  CPI2.initialWorld I.idᵐ store-empty

higher-order-shared-arg-world₁ : CTX.World 1 1 1
higher-order-shared-arg-world₁ =
  CTX.bothBindWorld I.X⊑X higher-order-shared-arg-world₀
    RC.∀X⇒X₀ RC.∀X⇒X₀

higher-order-shared-arg-store₁-parkedᴸ :
  higher-order-shared-arg-store₁
    ≡ CTX.sourceStoreʷ higher-order-shared-arg-world₁
higher-order-shared-arg-store₁-parkedᴸ = refl

higher-order-shared-arg-store₁-parkedᴿ :
  higher-order-shared-arg-store₁
    ≡ CTX.targetStoreʷ higher-order-shared-arg-world₁
higher-order-shared-arg-store₁-parkedᴿ = refl

higher-order-shared-arg-world₂ : CTX.World 2 2 2
higher-order-shared-arg-world₂ =
  CTX.bothBindWorld I.X⊑X higher-order-shared-arg-world₁
    (RC.ℕᵗ {Δ = 1}) (RC.ℕᵗ {Δ = 1})

higher-order-shared-arg-store₈-parkedᴸ :
  higher-order-shared-arg-store₈
    ≡ CTX.sourceStoreʷ higher-order-shared-arg-world₂
higher-order-shared-arg-store₈-parkedᴸ = refl

higher-order-shared-arg-store₈-parkedᴿ :
  higher-order-shared-arg-store₈
    ≡ CTX.targetStoreʷ higher-order-shared-arg-world₂
higher-order-shared-arg-store₈-parkedᴿ = refl

higher-order-shared-arg-callee-pivotᴸ-parked :
  toRenameᵗ (CTX.ηᴸʷ higher-order-shared-arg-world₂) Fin.zero
    ≡ Fin.zero
higher-order-shared-arg-callee-pivotᴸ-parked = refl

higher-order-shared-arg-callee-pivotᴿ-parked :
  toRenameᵗ (CTX.ηᴿʷ higher-order-shared-arg-world₂) Fin.zero
    ≡ Fin.zero
higher-order-shared-arg-callee-pivotᴿ-parked = refl

higher-order-shared-arg-shared-pivotᴸ-parked :
  toRenameᵗ (CTX.ηᴸʷ higher-order-shared-arg-world₂)
    (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
higher-order-shared-arg-shared-pivotᴸ-parked = refl

higher-order-shared-arg-shared-pivotᴿ-parked :
  toRenameᵗ (CTX.ηᴿʷ higher-order-shared-arg-world₂)
    (Fin.suc Fin.zero)
    ≡ Fin.suc Fin.zero
higher-order-shared-arg-shared-pivotᴿ-parked = refl

module D19PairedRevealReparseProbe where

-- File Charter:
--   * Tests D19's sync-first hypothesis without changing any live definition.
--   * Rebuilds the Examples2 YZ worlds with the aligned Z center marked X⊑X.
--   * Re-parses aligned Z reveals with CTI2.reveal⊑reveal² and retains the
--     existing paired Z conceal in the checkpoint-9 argument.
--   * Classifies each YZ Z-site as PAIRED-OK or ASYNC-FORCED, and records the
--     independent live X-side obstruction to the stale checkpoint 4--9 code.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
import Consistency as C
open C using (_⊢_∼_; id; renameEnv∼; wk↪ᵗ; idᶜ)
import Conversion as Conv
open import Conversion using (Conv↑; Conv↓; seal; unseal)
open import Imprecision using
  (ImpEnv; X⊑X; X⊑★; ★⊑★; ⇒⊑⇒)
import Imprecision as I
open import CastTerms
open import Primitives using (κℕ)
open import Reduction using (bind; applyEnv)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2

open CTX using (World; _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


------------------------------------------------------------------------
-- Precise-Z variants of the two YZ worlds
------------------------------------------------------------------------

yz-precise-Z-env : ImpEnv 3
yz-precise-Z-env Fin.zero = X⊑★
yz-precise-Z-env (Fin.suc Fin.zero) = X⊑★
yz-precise-Z-env (Fin.suc (Fin.suc Fin.zero)) = X⊑X

left-path-world₃-precise-Z : World 3 2 3
left-path-world₃-precise-Z =
  CTX.world Ex2.id↪ᵗ Ex2.left-path-target-ηᴿ-YZ yz-precise-Z-env
    Ex.right-store₃ Ex2.left-path-target-store₃

left-path-world₄-precise-Z : World 3 2 3
left-path-world₄-precise-Z =
  CTX.world Ex2.id↪ᵗ Ex2.left-path-target-ηᴿ-YZ yz-precise-Z-env
    Ex.right-store₄ Ex2.left-path-target-store₄


------------------------------------------------------------------------
-- Shared indices and rebases
------------------------------------------------------------------------

left-path-ℕ⊑★₃-precise-Z :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩ ★
left-path-ℕ⊑★₃-precise-Z =
  Ex2.ℕ⊑★² {W = left-path-world₃-precise-Z}

left-path-ℕ⊑★₄-precise-Z :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ ★
left-path-ℕ⊑★₄-precise-Z =
  Ex2.ℕ⊑★² {W = left-path-world₄-precise-Z}

left-path-Y-var⊑YZ₃-precise-Z :
  ＇ (Fin.suc Fin.zero) ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩ ＇ Fin.zero
left-path-Y-var⊑YZ₃-precise-Z = I.X⊑X

left-path-Z-var⊑YZ₃-precise-Z :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩ ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑YZ₃-precise-Z = I.X⊑X

left-path-Y⇒Y⊑Y⇒Y-YZ₃-precise-Z :
  (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩ (＇ Fin.zero ⇒ ＇ Fin.zero)
left-path-Y⇒Y⊑Y⇒Y-YZ₃-precise-Z =
  ⇒⊑⇒ left-path-Y-var⊑YZ₃-precise-Z left-path-Y-var⊑YZ₃-precise-Z

left-path-Z⇒Z⊑Z⇒Z-YZ₃-precise-Z :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-YZ₃-precise-Z =
  ⇒⊑⇒ left-path-Z-var⊑YZ₃-precise-Z left-path-Z-var⊑YZ₃-precise-Z

left-path-X-var⊑★-YZ₃-precise-Z :
  ＇ Fin.zero ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩ ★
left-path-X-var⊑★-YZ₃-precise-Z = I.X⊑★ refl

left-path-X⇒X⊑★⇒★-YZ₃-precise-Z :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ left-path-world₃-precise-Z ⟩ (★ ⇒ ★)
left-path-X⇒X⊑★⇒★-YZ₃-precise-Z =
  ⇒⊑⇒ left-path-X-var⊑★-YZ₃-precise-Z
    left-path-X-var⊑★-YZ₃-precise-Z

left-path-Y-rep₃-precise-Z :
  CTX.StoreRepImp left-path-world₃-precise-Z
    (Fin.suc Fin.zero) Fin.zero
left-path-Y-rep₃-precise-Z = CTX.store-rep-imp ★⊑★

left-path-Z-rep₃-precise-Z :
  CTX.StoreRepImp left-path-world₃-precise-Z
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-Z-rep₃-precise-Z = CTX.store-rep-imp ★⊑★

left-path-rebase-Y-YZ₃-precise-Z :
  CTX.RebaseAt left-path-world₃-precise-Z left-path-world₃-precise-Z
    (Fin.suc Fin.zero) Fin.zero
left-path-rebase-Y-YZ₃-precise-Z =
  CTX.sameWorldRebaseAt refl left-path-Y-rep₃-precise-Z

left-path-rebase-Z-YZ₃-precise-Z :
  CTX.RebaseAt left-path-world₃-precise-Z left-path-world₃-precise-Z
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-Z-YZ₃-precise-Z =
  CTX.sameWorldRebaseAt refl left-path-Z-rep₃-precise-Z

left-path-rebase-X-YZ₃-precise-Zᴸ :
  CTX.RebaseAtᴸ left-path-world₃-precise-Z left-path-world₃-precise-Z
    (just Fin.zero)
left-path-rebase-X-YZ₃-precise-Zᴸ =
  CTX.rebase-onlyᴸ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    left-path-ℕ⊑★₃-precise-Z


------------------------------------------------------------------------
-- Checkpoint 3: PAIRED-OK
------------------------------------------------------------------------

left-path-lambda₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢²
    ƛ (` 0) ⊑ Ex2.left-path-target-lambda₃ ∶
      left-path-Y⇒Y⊑Y⇒Y-YZ₃-precise-Z
left-path-lambda₃-precise-Z =
  CTI2.ƛ⊑ƛ²
    {A = ＇ (Fin.suc Fin.zero)} {A′ = ＇ Fin.zero}
    {B = ＇ (Fin.suc Fin.zero)} {B′ = ＇ Fin.zero}
    {pA = left-path-Y-var⊑YZ₃-precise-Z}
    {pB = left-path-Y-var⊑YZ₃-precise-Z}
    (CTI2.x⊑x² {p = left-path-Y-var⊑YZ₃-precise-Z} CTX.Zʷ)

left-path-Y-revealed₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal
    ⊑ Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂ ∶
      left-path-Z⇒Z⊑Z⇒Z-YZ₃-precise-Z
left-path-Y-revealed₃-precise-Z =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl
    left-path-rebase-Y-YZ₃-precise-Z CTX.same-[]
    Ex2.left-path-source-Y-reveal₃-⊢ˣ
    Ex2.left-path-target-Y-reveal₃-⊢ˣ
    left-path-lambda₃-precise-Z left-path-Z⇒Z⊑Z⇒Z-YZ₃-precise-Z

-- Paired-Z derivation head (checkpoint 3):
--   CTI2.reveal⊑reveal² CTX.impEnvMono-refl
--     left-path-rebase-Z-YZ₃-precise-Z CTX.same-[]
left-path-both-Z-revealed₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = left-path-world₃-precise-Z}
left-path-both-Z-revealed₃-precise-Z =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl
    left-path-rebase-Z-YZ₃-precise-Z CTX.same-[]
    Ex2.left-path-source-Z-reveal₃-⊢ˣ
    Ex2.left-path-target-Z-reveal₃-⊢ˣ
    left-path-Y-revealed₃-precise-Z
    (Ex2.★⇒★⊑★⇒★² {W = left-path-world₃-precise-Z})

left-path-source-id₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢²
    (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = left-path-world₃-precise-Z}
left-path-source-id₃-precise-Z =
  CTI2.cast⊑² Ex2.example12-target-id★↦id★
    left-path-both-Z-revealed₃-precise-Z
    (Ex2.★⇒★⊑★⇒★² {W = left-path-world₃-precise-Z})

left-path-source-X?₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      ⟨ Ex2.example12-target-X?↦X? ⟩
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      left-path-X⇒X⊑★⇒★-YZ₃-precise-Z
left-path-source-X?₃-precise-Z =
  CTI2.cast⊑² Ex2.example12-target-X?↦X?
    left-path-source-id₃-precise-Z left-path-X⇒X⊑★⇒★-YZ₃-precise-Z

left-path-function₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      ⟨ Ex2.example12-target-X?↦X? ⟩)
      ↑ Ex2.example12-target-X-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.ℕ⇒ℕ⊑★⇒★² {W = left-path-world₃-precise-Z}
left-path-function₃-precise-Z =
  CTI2.reveal⊑² CTX.impEnvMono-refl
    left-path-rebase-X-YZ₃-precise-Zᴸ CTX.same-[]
    Ex2.left-path-source-X-reveal₃-⊢ˣ left-path-source-X?₃-precise-Z
    (Ex2.ℕ⇒ℕ⊑★⇒★² {W = left-path-world₃-precise-Z})

left-path-argument₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢² $ (κℕ 7)
    ⊑ ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ C.sym∼ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-ℕ⊑★₃-precise-Z
left-path-argument₃-precise-Z =
  CTI2.⊑cast² (C.sym∼ Ex2.left-path-target-result-id★₃)
    (CTI2.⊑cast² Ex2.left-path-ℕ!₂
      (CTI2.κ⊑κ² (κℕ 7)
        (Ex2.ℕ⊑ℕ² {W = left-path-world₃-precise-Z}))
      left-path-ℕ⊑★₃-precise-Z)
    left-path-ℕ⊑★₃-precise-Z

left-path-checkpoint₃-precise-Z :
  left-path-world₃-precise-Z ∣ [] ⊢² Ex.right₃
    ⊑ Ex2.left-path-target₃ ∶ left-path-ℕ⊑★₃-precise-Z
left-path-checkpoint₃-precise-Z =
  CTI2.⊑cast² Ex2.left-path-target-result-id★₃
    (CTI2.·⊑·² left-path-function₃-precise-Z
      left-path-argument₃-precise-Z)
    left-path-ℕ⊑★₃-precise-Z


------------------------------------------------------------------------
-- Checked failure of the old asynchronous Z index
------------------------------------------------------------------------

left-path-Z-to-star-precise-empty :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ ★
  → ⊥
left-path-Z-to-star-precise-empty (I.X⊑★ ())


------------------------------------------------------------------------
-- Stage-4 shared paired function stack
------------------------------------------------------------------------

left-path-Y-var⊑YZ₄-precise-Z :
  ＇ (Fin.suc Fin.zero) ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ ＇ Fin.zero
left-path-Y-var⊑YZ₄-precise-Z = I.X⊑X

left-path-Z-var⊑YZ₄-precise-Z :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑YZ₄-precise-Z = I.X⊑X

left-path-X-var⊑★-YZ₄-precise-Z :
  ＇ Fin.zero ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ ★
left-path-X-var⊑★-YZ₄-precise-Z = I.X⊑★ refl

left-path-Y⇒Y⊑Y⇒Y-YZ₄-precise-Z :
  (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ (＇ Fin.zero ⇒ ＇ Fin.zero)
left-path-Y⇒Y⊑Y⇒Y-YZ₄-precise-Z =
  ⇒⊑⇒ left-path-Y-var⊑YZ₄-precise-Z left-path-Y-var⊑YZ₄-precise-Z

left-path-Z⇒Z⊑Z⇒Z-YZ₄-precise-Z :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-YZ₄-precise-Z =
  ⇒⊑⇒ left-path-Z-var⊑YZ₄-precise-Z left-path-Z-var⊑YZ₄-precise-Z

left-path-X⇒X⊑★⇒★-YZ₄-precise-Z :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ (★ ⇒ ★)
left-path-X⇒X⊑★⇒★-YZ₄-precise-Z =
  ⇒⊑⇒ left-path-X-var⊑★-YZ₄-precise-Z
    left-path-X-var⊑★-YZ₄-precise-Z

left-path-Y-rep₄-precise-Z :
  CTX.StoreRepImp left-path-world₄-precise-Z
    (Fin.suc Fin.zero) Fin.zero
left-path-Y-rep₄-precise-Z = CTX.store-rep-imp ★⊑★

left-path-Z-rep₄-precise-Z :
  CTX.StoreRepImp left-path-world₄-precise-Z
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-Z-rep₄-precise-Z = CTX.store-rep-imp ★⊑★

left-path-rebase-Y-YZ₄-precise-Z :
  CTX.RebaseAt left-path-world₄-precise-Z left-path-world₄-precise-Z
    (Fin.suc Fin.zero) Fin.zero
left-path-rebase-Y-YZ₄-precise-Z =
  CTX.sameWorldRebaseAt refl left-path-Y-rep₄-precise-Z

left-path-rebase-Z-YZ₄-precise-Z :
  CTX.RebaseAt left-path-world₄-precise-Z left-path-world₄-precise-Z
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-Z-YZ₄-precise-Z =
  CTX.sameWorldRebaseAt refl left-path-Z-rep₄-precise-Z

left-path-rebase-X-YZ₄-precise-Zᴸ :
  CTX.RebaseAtᴸ left-path-world₄-precise-Z left-path-world₄-precise-Z
    (just Fin.zero)
left-path-rebase-X-YZ₄-precise-Zᴸ =
  CTX.rebase-onlyᴸ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    left-path-ℕ⊑★₄-precise-Z

left-path-lambda₄-precise-Z :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ƛ (` 0) ⊑ Ex2.left-path-target-lambda₃ ∶
      left-path-Y⇒Y⊑Y⇒Y-YZ₄-precise-Z
left-path-lambda₄-precise-Z =
  CTI2.ƛ⊑ƛ²
    {A = ＇ (Fin.suc Fin.zero)} {A′ = ＇ Fin.zero}
    {B = ＇ (Fin.suc Fin.zero)} {B′ = ＇ Fin.zero}
    {pA = left-path-Y-var⊑YZ₄-precise-Z}
    {pB = left-path-Y-var⊑YZ₄-precise-Z}
    (CTI2.x⊑x² {p = left-path-Y-var⊑YZ₄-precise-Z} CTX.Zʷ)

left-path-Y-revealed₄-precise-Z :
  left-path-world₄-precise-Z ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal
    ⊑ Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂ ∶
      left-path-Z⇒Z⊑Z⇒Z-YZ₄-precise-Z
left-path-Y-revealed₄-precise-Z =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl
    left-path-rebase-Y-YZ₄-precise-Z CTX.same-[]
    Ex2.left-path-source-Y-reveal₃-⊢ˣ
    Ex2.left-path-target-Y-reveal₃-⊢ˣ
    left-path-lambda₄-precise-Z left-path-Z⇒Z⊑Z⇒Z-YZ₄-precise-Z

-- Paired-Z derivation head (checkpoints 5--7):
--   CTI2.reveal⊑reveal² CTX.impEnvMono-refl
--     left-path-rebase-Z-YZ₄-precise-Z CTX.same-[]
left-path-both-Z-revealed₄-precise-Z :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = left-path-world₄-precise-Z}
left-path-both-Z-revealed₄-precise-Z =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl
    left-path-rebase-Z-YZ₄-precise-Z CTX.same-[]
    Ex2.left-path-source-Z-reveal₃-⊢ˣ
    Ex2.left-path-target-Z-reveal₃-⊢ˣ
    left-path-Y-revealed₄-precise-Z
    (Ex2.★⇒★⊑★⇒★² {W = left-path-world₄-precise-Z})


------------------------------------------------------------------------
-- Checkpoints 5--8: paired Z, but a pre-existing X-side block
------------------------------------------------------------------------

left-path-argument₄-precise-Z :
  left-path-world₄-precise-Z ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      left-path-ℕ⊑★₄-precise-Z
left-path-argument₄-precise-Z =
  CTI2.⊑cast² Ex2.left-path-ℕ!₂
    (CTI2.κ⊑κ² (κℕ 7)
      (Ex2.ℕ⊑ℕ² {W = left-path-world₄-precise-Z}))
    left-path-ℕ⊑★₄-precise-Z

-- Every attempted whole-program reconstruction of checkpoints 5--8 reaches
-- the same source-only `seal X ℕ` comparison before its paired Z node.  The
-- live side condition rejects the intended target, independently of Z's mark.

left-path-X-seal-source-ok-empty-precise-Z :
  ∀ {W : World 3 2 3} {P Xᴿ?}
  → CTX.SourceConcealOK W P Ex2.example12-target-X-seal Xᴿ?
      ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
  → ⊥
left-path-X-seal-source-ok-empty-precise-Z
    (CTX.seal-nonstar-plain-ok _ ())

left-path-X-to-ℕ-precise-empty : ∀ {W : World 3 2 3}
  → ＇ Fin.zero ⊑ᵂ⟨ W ⟩ ‵ `ℕ
  → ⊥
left-path-X-to-ℕ-precise-empty ()

left-path-star-to-ℕ-precise-empty : ∀ {W : World 3 2 3}
  → ★ ⊑ᵂ⟨ W ⟩ ‵ `ℕ
  → ⊥
left-path-star-to-ℕ-precise-empty ()

left-path-X-sealed-vs-tagged-empty :
  ∀ {p : ＇ Fin.zero ⊑ᵂ⟨ left-path-world₄-precise-Z ⟩ ★}
  → left-path-world₄-precise-Z ∣ [] ⊢²
    ($ (κℕ 7)) ↓ Ex2.example12-target-X-seal
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      p
  → ⊥
left-path-X-sealed-vs-tagged-empty
    (CTI2.⊑cast² {p = p} c′ D q) =
  left-path-X-to-ℕ-precise-empty
    {W = left-path-world₄-precise-Z} p
left-path-X-sealed-vs-tagged-empty
    (CTI2.conceal⊑² {W′ = W′}
      ok mono rb sc c⊢ D q) =
  left-path-X-seal-source-ok-empty-precise-Z {W = W′} ok

left-path-X-core-empty :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → ⊥
left-path-X-core-empty
    (CTI2.cast⊑cast² {p = p} c c′ D q) =
  left-path-X-to-ℕ-precise-empty
    {W = left-path-world₄-precise-Z} p
left-path-X-core-empty
    (CTI2.⊑cast² {p = p} c′ D q) =
  left-path-star-to-ℕ-precise-empty
    {W = left-path-world₄-precise-Z} p
left-path-X-core-empty
    (CTI2.cast⊑² {p = p} c D q) =
  left-path-X-sealed-vs-tagged-empty {p = p} D

left-path-source-arg-id★₆ :
  C.flipᵐ
    (renameEnv∼ (C.skip Ex2.id↪ᵗ)
      (applyEnv (bind (＇ Fin.zero))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))))
    ⊢ ★ ∼ ★
left-path-source-arg-id★₆ = id ★

left-path-source-result-id★₆ :
  renameEnv∼ (C.skip Ex2.id↪ᵗ)
    (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))
    ⊢ ★ ∼ ★
left-path-source-result-id★₆ = id ★

-- The following three implications check every Z step and every outer wrapper
-- of checkpoints 5--7.  Their sole hypothesis is exactly the unavailable
-- post-X-seal argument judgment isolated above.

left-path-checkpoint₄-from-X-seal-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ($ (κℕ 7)) ↓ Ex2.example12-target-X-seal
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      left-path-X-var⊑★-YZ₄-precise-Z
  → left-path-world₄-precise-Z ∣ [] ⊢² Ex.right₄
      ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-precise-Z
left-path-checkpoint₄-from-X-seal-core D =
  CTI2.reveal⊑² CTX.impEnvMono-refl
    left-path-rebase-X-YZ₄-precise-Zᴸ CTX.same-[]
    Ex2.left-path-source-X-unseal₄-⊢ˣ
    (CTI2.⊑cast² Ex2.left-path-target-result-id★₃
      (CTI2.·⊑·²
        (CTI2.cast⊑² Ex2.example12-target-X?↦X?
          (CTI2.cast⊑² Ex2.example12-target-id★↦id★
            left-path-both-Z-revealed₄-precise-Z
            (Ex2.★⇒★⊑★⇒★² {W = left-path-world₄-precise-Z}))
          left-path-X⇒X⊑★⇒★-YZ₄-precise-Z)
        D)
      left-path-X-var⊑★-YZ₄-precise-Z)
    left-path-ℕ⊑★₄-precise-Z

left-path-checkpoint₅-from-X-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → left-path-world₄-precise-Z ∣ [] ⊢² Ex.right₅
      ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-precise-Z
left-path-checkpoint₅-from-X-core D =
  CTI2.reveal⊑² CTX.impEnvMono-refl
    left-path-rebase-X-YZ₄-precise-Zᴸ CTX.same-[]
    Ex2.left-path-source-X-unseal₄-⊢ˣ
    (CTI2.cast⊑² Ex2.example12-target-★?X
      (CTI2.⊑cast² Ex2.left-path-target-result-id★₃
        (CTI2.·⊑·²
          (CTI2.cast⊑² Ex2.example12-target-id★↦id★
            left-path-both-Z-revealed₄-precise-Z
            (Ex2.★⇒★⊑★⇒★² {W = left-path-world₄-precise-Z}))
          D)
        ★⊑★)
      left-path-X-var⊑★-YZ₄-precise-Z)
    left-path-ℕ⊑★₄-precise-Z

left-path-checkpoint₆-from-X-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → left-path-world₄-precise-Z ∣ [] ⊢² Ex.right₆
      ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-precise-Z
left-path-checkpoint₆-from-X-core D =
  CTI2.reveal⊑² CTX.impEnvMono-refl
    left-path-rebase-X-YZ₄-precise-Zᴸ CTX.same-[]
    Ex2.left-path-source-X-unseal₄-⊢ˣ
    (CTI2.cast⊑² Ex2.example12-target-★?X
      (CTI2.cast⊑cast² left-path-source-result-id★₆
        Ex2.left-path-target-result-id★₃
        (CTI2.·⊑·² left-path-both-Z-revealed₄-precise-Z
          (CTI2.cast⊑² left-path-source-arg-id★₆ D ★⊑★))
        ★⊑★)
      left-path-X-var⊑★-YZ₄-precise-Z)
    left-path-ℕ⊑★₄-precise-Z

left-path-checkpoint₇-from-X-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → left-path-world₄-precise-Z ∣ [] ⊢² Ex.right₇
      ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-precise-Z
left-path-checkpoint₇-from-X-core D =
  CTI2.reveal⊑² CTX.impEnvMono-refl
    left-path-rebase-X-YZ₄-precise-Zᴸ CTX.same-[]
    Ex2.left-path-source-X-unseal₄-⊢ˣ
    (CTI2.cast⊑² Ex2.example12-target-★?X
      (CTI2.cast⊑cast² left-path-source-result-id★₆
        Ex2.left-path-target-result-id★₃
        (CTI2.·⊑·² left-path-both-Z-revealed₄-precise-Z D)
        ★⊑★)
      left-path-X-var⊑★-YZ₄-precise-Z)
    left-path-ℕ⊑★₄-precise-Z


------------------------------------------------------------------------
-- Checkpoint 8's paired result reveal and checkpoint 9's paired argument
------------------------------------------------------------------------

left-path-target-Z-seal₂ : Conv↓ 2 ★ (＇ (Fin.suc Fin.zero))
left-path-target-Z-seal₂ = seal (Fin.suc Fin.zero) ★

left-path-target-Z-unseal₂ : Conv↑ 2 (＇ (Fin.suc Fin.zero)) ★
left-path-target-Z-unseal₂ = unseal (Fin.suc Fin.zero) ★

left-path-target-Y-seal₂ :
  Conv↓ 2 (＇ (Fin.suc Fin.zero)) (＇ Fin.zero)
left-path-target-Y-seal₂ = seal Fin.zero (＇ (Fin.suc Fin.zero))

left-path-source-Z-seal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↓[ just (Fin.suc (Fin.suc Fin.zero)) ]
    Ex2.example12-target-Z-seal
left-path-source-Z-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ Ex2.left-path-source-Z∋₃

left-path-target-Z-seal₄-⊢ˣ :
  Ex2.left-path-target-store₄ Conv.⊢↓[ just (Fin.suc Fin.zero) ]
    left-path-target-Z-seal₂
left-path-target-Z-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ Ex2.left-path-target-Z∋₃

left-path-source-Z-unseal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↑[ just (Fin.suc (Fin.suc Fin.zero)) ]
    Ex2.example12-target-Z-unseal
left-path-source-Z-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ Ex2.left-path-source-Z∋₃

left-path-target-Z-unseal₄-⊢ˣ :
  Ex2.left-path-target-store₄ Conv.⊢↑[ just (Fin.suc Fin.zero) ]
    left-path-target-Z-unseal₂
left-path-target-Z-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ Ex2.left-path-target-Z∋₃

left-path-source-Y-seal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↓[ just (Fin.suc Fin.zero) ]
    Ex2.example12-target-Y-seal
left-path-source-Y-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ Ex2.left-path-source-Y∋₃

left-path-target-Y-seal₄-⊢ˣ :
  Ex2.left-path-target-store₄ Conv.⊢↓[ just Fin.zero ]
    left-path-target-Y-seal₂
left-path-target-Y-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ Ex2.left-path-target-Y∋₃

left-path-argument-Z₈-from-X-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → left-path-world₄-precise-Z ∣ [] ⊢²
      ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal
      ⊑ ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂ ∶
        left-path-Z-var⊑YZ₄-precise-Z
left-path-argument-Z₈-from-X-core D =
  CTI2.conceal⊑conceal²
    (CTX.matched-seal-star-partner
      (CTX.rep★-nonvar-tag nonvar-base))
    CTX.impEnvMono-refl left-path-rebase-Z-YZ₄-precise-Z CTX.same-[]
    left-path-source-Z-seal₄-⊢ˣ left-path-target-Z-seal₄-⊢ˣ D
    left-path-Z-var⊑YZ₄-precise-Z

-- Paired-Z derivation head (checkpoint 8 result unseals):
--   CTI2.reveal⊑reveal² CTX.impEnvMono-refl
--     left-path-rebase-Z-YZ₄-precise-Z CTX.same-[]
left-path-checkpoint₈-from-X-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → left-path-world₄-precise-Z ∣ [] ⊢² Ex.right₈
      ⊑ Ex2.left-path-target₅ ∶ left-path-ℕ⊑★₄-precise-Z
left-path-checkpoint₈-from-X-core D =
  CTI2.reveal⊑² CTX.impEnvMono-refl
    left-path-rebase-X-YZ₄-precise-Zᴸ CTX.same-[]
    Ex2.left-path-source-X-unseal₄-⊢ˣ
    (CTI2.cast⊑² Ex2.example12-target-★?X
      (CTI2.cast⊑cast² left-path-source-result-id★₆
        Ex2.left-path-target-result-id★₃
        (CTI2.reveal⊑reveal² CTX.impEnvMono-refl
          left-path-rebase-Z-YZ₄-precise-Z CTX.same-[]
          left-path-source-Z-unseal₄-⊢ˣ
          left-path-target-Z-unseal₄-⊢ˣ
          (CTI2.·⊑·² left-path-Y-revealed₄-precise-Z
            (left-path-argument-Z₈-from-X-core D))
          ★⊑★)
        ★⊑★)
      left-path-X-var⊑★-YZ₄-precise-Z)
    left-path-ℕ⊑★₄-precise-Z

left-path-argument-Y₉-from-X-core :
  left-path-world₄-precise-Z ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶ ★⊑★
  → left-path-world₄-precise-Z ∣ [] ⊢²
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal)
      ⊑ ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂)
          ↓ left-path-target-Y-seal₂) ∶
        left-path-Y-var⊑YZ₄-precise-Z
left-path-argument-Y₉-from-X-core D =
  CTI2.conceal⊑conceal²
    (CTX.matched-seal-nonstar nonstar-X)
    CTX.impEnvMono-refl left-path-rebase-Y-YZ₄-precise-Z CTX.same-[]
    left-path-source-Y-seal₄-⊢ˣ left-path-target-Y-seal₄-⊢ˣ
    (left-path-argument-Z₈-from-X-core D)
    left-path-Y-var⊑YZ₄-precise-Z


------------------------------------------------------------------------
-- D19 classification
------------------------------------------------------------------------

data Classification : Set where
  PAIRED-OK ASYNC-FORCED : Classification

-- Checkpoint 3                  -> PAIRED-OK (whole judgment checked).
-- Checkpoint 4                  -> PAIRED-OK at Z; whole blocked earlier at X.
-- Checkpoints 5, 6, 7          -> PAIRED-OK at Z; whole blocked earlier at X.
-- Checkpoint 8                  -> PAIRED-OK at Z; whole blocked earlier at X.
-- Checkpoint 9 argument         -> PAIRED-OK at Z; blocked earlier at X.
-- ASYNC-FORCED                  -> no checkpoint in the swept set.
--
-- Consequently, the requested two-way classification is total for the Z
-- sites, but not for the whole stale checkpoint-5--9 fixtures: their X-side
-- premise is already rejected by the current live relation.  Calling those
-- whole judgments ASYNC-FORCED would falsely attribute the failure to Z.

checkpoint₃-Z-classification : Classification
checkpoint₃-Z-classification = PAIRED-OK

checkpoint₄-Z-classification : Classification
checkpoint₄-Z-classification = PAIRED-OK

checkpoint₅-Z-classification : Classification
checkpoint₅-Z-classification = PAIRED-OK

checkpoint₆-Z-classification : Classification
checkpoint₆-Z-classification = PAIRED-OK

checkpoint₇-Z-classification : Classification
checkpoint₇-Z-classification = PAIRED-OK

checkpoint₈-Z-classification : Classification
checkpoint₈-Z-classification = PAIRED-OK

checkpoint₉-argument-Z-classification : Classification
checkpoint₉-argument-Z-classification = PAIRED-OK

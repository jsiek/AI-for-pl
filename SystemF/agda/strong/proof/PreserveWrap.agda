module strong.proof.PreserveWrap where

-- Strong System F v7 — preservation for `Wrap`.
--
--   νΘ,χ[ƛA₁∙N | c] · W  -→  νΘ,χ[ (ƛA₁∙N) · ν∅,-χ[W′|c₁] | c₂ ]
--
-- with arr A₁ c = (c₁ , c₂) and W′ the argument weakened under the store.
-- The three pieces this was blocked on, in order of their repair:
--
--   * `χ-invert` (the merged-entry context): the dual scope leads from the
--     interior back to ΔΘ EXACTLY, which is where c₁ and W′ live.
--   * the reflexive terminator: `conv-fun` states its components at the
--     interior and the seam, and `tail-id` makes the seam the exterior.
--   * `arr` takes the interior domain FROM THE λ, so the bare-`id` case's
--     contravariant component is `id A₁`, which retypes by symmetry.
--
-- After those, the case is assembling `⊢ν` twice.

open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.proof.ScopeDual using (χ-invert)
open import strong.proof.AnchorWeaken using (wk-⊢; wk-base; store-block)
open import strong.proof.ArrTyping using (arr-typing)

preserve-Wrap : ∀ {Δ Θ χ A N c W c₁ c₂ B}
  → Δ ok
  → Value (ν Θ , χ [ ƛ A ∙ N ∣ c ])
  → Value W
  → arr A c ≡ just (c₁ , c₂)
  → Δ ∣ [] ⊢ (ν Θ , χ [ ƛ A ∙ N ∣ c ]) · W ⦂ B
  → Δ ∣ [] ⊢ ν Θ , χ
       [ (ƛ A ∙ N) · (ν [] , dual χ
         [ renAnchᴹ (shiftAnchor (length Θ)) W ∣ c₁ ])
       ∣ c₂ ] ⦂ B
preserve-Wrap ctx-ok bval wval arr-eq
  (⊢· (⊢ν store scope nf (⊢ƛ wfA ⊢N) conv) ⊢W)
  with arr-typing conv nf arr-eq
preserve-Wrap ctx-ok bval wval arr-eq
  (⊢· (⊢ν store scope nf (⊢ƛ wfA ⊢N) conv) ⊢W)
  | c₁-ty , c₂-ty , nf₁ , nf₂ =
  ⊢ν store scope nf₂
    (⊢· (⊢ƛ wfA ⊢N)
        (⊢ν store[] (χ-invert scope) nf₁
            (wk-⊢ (wk-base (store-block store)) ⊢W)
            c₁-ty))
    c₂-ty

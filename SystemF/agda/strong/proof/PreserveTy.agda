module strong.proof.PreserveTy where

-- Strong System F v8 — two of the three obligations
-- `proof.Preservation` is parameterized on, discharged.
--
-- What makes them discharge is the repair of 2026-09-15.  With
-- `conv-hide`/`conv-show` scoping their address, `proof.Scoped` carries
-- "every assignment names an address in scope" along the interior
-- walk, and the side facts the two developments had to take as
-- premises become derived:
--
--   `Σ ∣ Δ ⊢ᴿ R` from `Σ ∣ Δ ⊢⌊ A ⌋ R`   `quote-wfᴿ`
--   `FreshStk`, `FreshM`                  `scoped-freshStk`,
--                                         `typing-fresh`
--   `Δ ⊢ᵗ ∀B`                             `typing-wf`
--
-- `TyWrapOk` is the one still open; it is `allView-typing` composed
-- with `revTy`'s typing and `substAnn-typing`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst

open import strong.proof.Flat using (Flat; Flatn; fu-nobinds)
open Flatn
open import strong.proof.Scoped using
  (Scoped; quote-wfᴿ; scoped-freshStk; typing-fresh; flat-bindsBelow)
open import strong.proof.TypeWf using (typing-wf; ctxOk-[])
open import strong.proof.PreserveAlloc using
  (preserve-Alloc; alloc-storeOk)
open import strong.proof.BuilderTyping using (preserve-TyBeta)
open import strong.proof.PreserveTyDef

------------------------------------------------------------------------
-- Alloc
------------------------------------------------------------------------
-- The `ν`'s representation is well formed at a FLAT context, hence
-- base-closed, hence storable; and the two freshness facts are the
-- scoping invariant read at the store's next level.

allocOk : AllocOk
allocOk {Sg} {Δ = Ss ∥ Bs} sok fl scp (⊢ν wf ⊢M) =
    alloc-storeOk sok fl wf
  , preserve-Alloc sok fl (scoped-freshStk scp)
      (typing-fresh ⊢M) (⊢ν wf ⊢M)

------------------------------------------------------------------------
-- TyBeta
------------------------------------------------------------------------
-- The reduction rule hands over `⌊ A ⌋ R`; `quote-wfᴿ` turns it into
-- the `⊢ᴿ R` the `ν` it builds needs, and `typing-wf` supplies the
-- builder's source well-formedness.

tyBetaOk : TyBetaOk
tyBetaOk {Δ = Ss ∥ Bs} sok fl nf scp q (⊢•[] ⊢Λ' wfA) =
  preserve-TyBeta sok fl (quote-wfᴿ scp (flat-bindsBelow (fu-nobinds (flat-stk fl))) q) q
    (typing-wf ctxOk-[] ⊢Λ') (⊢•[] ⊢Λ' wfA)

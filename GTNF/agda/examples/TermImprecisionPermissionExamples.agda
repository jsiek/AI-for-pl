module examples.TermImprecisionPermissionExamples where

-- File Charter:
--   * PERMISSIONS, R1′ AND R2 (design.md D28, D31) on concrete programs,
--     with the real relation (TermImprecision): example P4 derives with
--     its permissions chosen at JOINING boundaries, and the
--     counterexamples C1-C5, C4g and the hunt's gen-valued C4 are NOT
--     derivable.  Checked first as proof/DGG/notes/D28pD30.agda
--     (CorpusB, CorpusD, C1ᴰ-C5ᴰ, Hunt); no notes module is imported.
--       P4.p4-B1 … p4-B6   P4 (= cambridge Cf from its second block),
--                          every block; the matched TyBeta boundary
--                          `+X ∥ +X` permits αᴿ for its interior (B2,
--                          B3, B4; K = [0], `jr₀`), paying with its
--                          interior index at X⊑X, so inside it the
--                          shared X is X⊑★ (`W₄²¹`) and the gen wrapper
--                          `X! → X?` (B2) and the check `X?` (B3, B4)
--                          are plain ⊑casts
--       CgB1.cg-b1,        Cg B1 and C18b B7 (two type variables; the
--       C18bB7.c18b-b7     matched boundary permits only X's rep. var)
--       P4c.p4-R7 … p4-R10 the right's Merge, IdDyn, Merge, TagUntag
--                          against B4's left (reduction closure)
--       C1.c1-unrelated    C1 (`L₆ ⊑ R₇`, all three routes of
--                          HiddenNames §2): not derivable at κʷ ≡ []
--       C3.c3-unrelated    C3 (`LE₁ ⊑ RE₁`): not derivable at κʷ ≡ []
--       C2.c2-unrelated    C2 (`LE₃ ⊑ RE₅`, the late pair): not
--                          derivable at κʷ ≡ []
--       C4.c4-unrelated,   C4 and C4g (the left's initial program
--       C4g.c4g-unrelated  against the right's state 2; sources
--                          unrelated, `C4.source-unrelated`): not
--                          derivable at κʷ ≡ [], with claim-rep
--                          (design.md D29), openings, skips and
--                          permissions (D31)
--       Hunt.c4gen-unrelated  a gen-VALUED left against C4's right:
--                          every new freedom of D31 at once; not
--                          derivable at κʷ ≡ []
--       C5.r1-rejects-c5,  C5 (Permissions.md §5; L state 3, R state 5):
--       C5Dead.c5-unrelated  R1′ rejects the payload view (the seal's
--                          exterior type is X, so R1′ is R1), and the
--                          pair is unrelated in EVERY world at ANY κ;
--                          so is its failing redex against the left
--                          value (M26's shape, `c5-redex-unrelated`)
--                          and its hidden variant (`hidden-unrelated`,
--                          which needs R1′ after the right hide or R2
--                          at the matched hides)
--   * THE NEGATIVE PROOFS quantify over every slot list O and read the
--     PAYMENT of each boundary: a permission enters only at a boundary
--     that joins a type variable, and that boundary pays with its
--     interior index read without the permission (`K-pay`, `pay-RBd`);
--     a top-level world has no permission (`κʷ ≡ []`).  C5 needs no
--     hypothesis at all.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.List using (List; []; _∷_; map; length; head; drop; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product
  using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision
open import proof.ImprecisionWorld
open import proof.TypeSafety.CoercionTyping using (coercion-trg)
open import proof.DGG.ImprecisionTyping using (imprecision-typing)
import examples.TermImprecisionExamples as TIE
import examples.TermImprecisionRebaseExamples as Rebase

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Example P4 (= cambridge Cf from its second block), every block.
-- The shared X is X⊑X (`W₄²`) unless the matched TyBeta boundary
-- `+X ∥ +X` permits αᴿ for its interior (design.md D31; B2, B3, B4).
-- With the permission X is X⊑★ (`W₄²¹`); inside the right's own `−X`
-- it is left-only (`W₄ᴸ`), and the right's `+X` rejoins it at αᴿ, which
-- is still permitted (κ passes through every inner boundary)
------------------------------------------------------------------------

module P4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.ImprecisionExamples using (L4; R4; L4-⊢; R4-⊢)

  nth : List Term → ℕ → Term
  nth []       _       = $ 0
  nth (x ∷ xs) zero    = x
  nth (x ∷ xs) (suc n) = nth xs n

  Ls Rs : List Term
  Ls = evalTerms 11 L4-⊢
  Rs = evalTerms 17 R4-⊢
  open TIE using (idX; revX; Θ₀; L1′; ΔL; ΔLᵢ; bL-ty; revX⊑revX; νL-ty;
                  Wν; Wν-conv)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ; Wc-bindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; ℕ⇒ℕ; ∀id⊑★; ∀id⊑∀id; I★⁻; I★gen; Bg; tagX↦;
           id★→; jr₀)
  open import examples.CambridgeExamples using (I★)

  νbody : Term
  νbody = ν `ℕ · ` 0 ⟨ revX ⟩

  νbody-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νbody-ty = proj₂ (proj₂ (ν-inv {Γ = TIE.∀X⇒X ∷ []}
    (tc {Δ = empty} {Γ = TIE.∀X⇒X ∷ []} {M = νbody})))

  genArg : Term
  genArg = (ƛ ★ ∙ ` 0) ⟨ [] ∣ genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)) ⟩

  genArg-ty : CastTy empty [] (genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0)))
    (★ ⇒ ★) TIE.∀X⇒X
  genArg-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = genArg})))

  ---------------------------------------------------------------------
  -- The worlds.  Both sides allocate αᴸ:=ℕ, αᴿ:=ℕ (rep. var 0); the
  -- matched TyBetas pair them globally.  The boundary type variable X is
  -- both-sided, X⊑X without permission (`W₄²`) and X⊑★ where the matched
  -- TyBeta boundary permits αᴿ (`W₄²¹`, design.md D31), left-only after
  -- a right `−X` (`W₄ᴸ`), and rejoined at the right's `+X` with αᴿ
  -- still permitted.

  Ξ₄ : RepCtx
  Ξ₄ = bindR `ℕ ∷ []

  ϱ₄ : RepRel
  ϱ₄ = (0 , 0) ∷ []

  W₄ : World ΔL ΔL
  W₄ = Wc⁰ {Ξ₄} {ϱ₄}

  -- X both-sided, NOT permitted: X⊑X
  W₄² : World ΔLᵢ ΔLᵢ
  W₄² = Wc² {Ξ₄} {ϱ₄} [] 0

  -- X both-sided, αᴿ PERMITTED (inside the permitting boundary): X⊑★
  W₄²¹ : World ΔLᵢ ΔLᵢ
  W₄²¹ = Wc² {Ξ₄} {ϱ₄} (0 ∷ []) 0

  -- X left-only (inside the right's −X), αᴿ permitted
  W₄ᴸ : World ΔLᵢ ΔL
  W₄ᴸ = Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ [])

  -- no name, permissions κ
  W₄⁰ : List RVar → World ΔL ΔL
  W₄⁰ κ = world 0 []↪ []↪ ϱ₄ [] κ

  -- without a permission the shared X is X⊑X: B3's premise index is
  -- empty
  no-X⊑★-W₄² : ¬ (marksʷ W₄² ∋ˡ 0 := X⊑★)
  no-X⊑★-W₄² ()

  module Wf₄ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World (Ξ₄ ∣ nsL) (Ξ₄ ∣ nsR)
    W = world n η η′ ϱ₄ [] κ

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  p0 : All (Ξ₄ ∋ʳ_) (0 ∷ [])
  p0 = (_ , here) ∷ []

  W₄⁰-wf : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → WfWorld (W₄⁰ κ)
  W₄⁰-wf {κ} ps = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[])
    (namedᴿ-≤1 W ≤1-[]) ps
    where open Wf₄ 0 []↪ []↪ κ

  W₄-wf : WfWorld W₄
  W₄-wf = W₄⁰-wf []

  W₄²κ-wf : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → WfWorld (Wc² {Ξ₄} {ϱ₄} κ 0)
  W₄²κ-wf {κ} ps = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) ps
    where open Wf₄ 1 (keep []↪) (keep []↪) κ

  W₄²-wf : WfWorld W₄²
  W₄²-wf = W₄²κ-wf []

  W₄²¹-wf : WfWorld W₄²¹
  W₄²¹-wf = W₄²κ-wf p0

  W₄ᴸ-wf : WfWorld W₄ᴸ
  W₄ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) p0
    where open Wf₄ 1 (keep []↪) (skip []↪) (0 ∷ [])

  v₀ : Ξ₄ ∋ʳ 0
  v₀ = _ , here

  ---------------------------------------------------------------------
  -- Shared pieces: the sealed argument S = [−X^α] 5 ⟨−X⟩ on both sides

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  S : Term
  S = $ 5 ⟪ unb₀ , tail (seal 0) ⟫

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  unb-int : ∀ {κ} → Interior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ unb₀ (W₄⁰ κ)
  unb-int = record
    { int-left   = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; int-right  = interior (changes∷ changes[]
                     (step-unbind (_ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  unb-conv : ∀ {κ} → ConversionInterior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ unb₀
    (Wc² {Ξ₄} {ϱ₄} κ 0)
  unb-conv = record
    { conv-left       = conversion (conv-unbind (_ , here) conv[])
    ; conv-right      = conversion (conv-unbind (_ , here) conv[])
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  bS : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S}))))

  -- the sealed literals, at any permissions
  S⊑Sκ : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → Wc² {Ξ₄} {ϱ₄} κ 0 ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑Sκ ps = ⟪⟫⊑⟪⟫₀ unb-int (W₄⁰-wf ps) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (_ , unb-conv , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  S⊑S : W₄²¹ ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S = S⊑Sκ p0

  -- the left's λx:X. x against the right's λx:★. x (X left-only)
  idX⊑I★ : W₄ᴸ ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξ₄ ϱ₄ (0 ∷ [])
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  bI★⁻ : BdyTy ΔLᵢ unb₀ ΔL (★ ⇒ ★) id★→ (★ ⇒ ★)
  bI★⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★⁻}))))

  -- idX ⊑ [−X^α] (λx:★. x) ⟨id(★) → id(★)⟩ at X→X ⊑ ★→★ (X both-sided
  -- and PERMITTED: this index needs the permission)
  idX⊑I★⁻ : W₄²¹ ∣ [] ⊢ idX ⊑ I★⁻ ∶ c⊑★² Ξ₄ ϱ₄ (0 ∷ []) 0 refl
  idX⊑I★⁻ = ⊑⟪⟫₀ (Wc-unbindᴿ v₀) W₄ᴸ-wf idX⊑I★ bI★⁻
    (c⊑★² Ξ₄ ϱ₄ (0 ∷ []) 0 refl)

  tagᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) tagX↦ (★ ⇒ ★) (` 0 ⇒ ` 0)
  tagᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★gen})))

  ---------------------------------------------------------------------
  -- B1 (0, 0): the initial pair

  p4-B1 : ∅ʷ ∣ [] ⊢ L4 ⊑ R4 ∶ ι⊑ι base-ℕ
  p4-B1 =
    ·⊑·
      (ƛ⊑ƛ {pA = ∀id⊑∀id ∅ʷ} tf tf
        (·⊑·
          (ν⊑ν (x⊑x Zʷ) (ι⊑ι base-ℕ) νbody-ty νbody-ty
            (Wν , Wν-conv , revX⊑revX refl)
            (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
          (κ⊑κ lit-$ (ι⊑ι base-ℕ))))
      (⊑cast
        (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
          (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
        genArg-ty (∀id⊑∀id ∅ʷ))

  ---------------------------------------------------------------------
  -- (1, 1): after both Betas (cambridge Cf B0)

  νR₁ : Term
  νR₁ = ν `ℕ · genArg ⟨ revX ⟩

  νR₁-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νR₁-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = νR₁})))

  p4-B1′ : ∅ʷ ∣ [] ⊢ nth Ls 1 ⊑ nth Rs 1 ∶ ι⊑ι base-ℕ
  p4-B1′ =
    ·⊑·
      (ν⊑ν
        (⊑cast
          (Λ⊑ b-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
          genArg-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty νR₁-ty
        (Wν , Wν-conv , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B2 (2, 2): after both TyBetas, BEFORE CastFun.  The matched TyBeta
  -- boundary `+X ∥ +X` JOINS its fresh pair and PERMITS αᴿ for its
  -- interior (K = [0], `jr₀`, design.md D31), paying with X→X ⊑ X→X at
  -- X⊑X; inside, the right's gen wrapper `X! → X?` at `^[X:★∼X]` (ONE
  -- arrow coercion) is peeled by a plain ⊑cast at X→X ⊑ ★→★

  bBg : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bBg = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = Bg}))))

  p4-B2 : W₄ ∣ [] ⊢ nth Ls 2 ⊑ nth Rs 2 ∶ ι⊑ι base-ℕ
  p4-B2 =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf (c⊑c² Ξ₄ ϱ₄ [] 0)
        (⊑cast idX⊑I★⁻ tagᵍ-ty (c⊑c² Ξ₄ ϱ₄ (0 ∷ []) 0))
        bL-ty bBg (W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B3 (3, 4): after the left's Wrap and the right's Wrap, CastFun.
  -- The right's X? at `^[X:★∼X]` and its argument's X! at `^[X:X∼★]`
  -- (CastFun flipped the environment).  The matched `+X ∥ +X` permits
  -- αᴿ (pays X ⊑ X); the check is a plain ⊑cast, and the tag below it
  -- reads X ⊑ ★ at the permitted X

  tagX : Coercion
  tagX = (` 0) !

  chkX : Coercion
  chkX = (` 0) ？ 0

  tagˣ-ty : CastTy ΔLᵢ (X∼★ ∷ []) tagX (` 0) ★
  tagˣ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = S ⟨ X∼★ ∷ [] ∣ tagX ⟩})))

  chkᵍ-ty : CastTy ΔLᵢ (★∼X ∷ []) chkX ★ (` 0)
  chkᵍ-ty = proj₂ (proj₂ (cast-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩})))

  -- the left's and the right's +X boundaries (conversion `unseal 0`)
  bUnsealL : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealL = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 4}))))

  bUnsealR : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealR = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 6}))))

  bUnsealL₃ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealL₃ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 3}))))

  bUnsealR₄ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bUnsealR₄ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 4}))))

  S⊑S! : W₄²¹ ∣ [] ⊢ S ⊑ S ⟨ X∼★ ∷ [] ∣ tagX ⟩ ∶ X⊑★ here
  S⊑S! = ⊑cast S⊑S tagˣ-ty (X⊑★ here)

  p4-B3 : W₄ ∣ [] ⊢ nth Ls 3 ⊑ nth Rs 4 ∶ ι⊑ι base-ℕ
  p4-B3 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf X⊑X
      (⊑cast {p = X⊑★ here} (·⊑· idX⊑I★⁻ S⊑S!) chkᵍ-ty X⊑X)
      bUnsealL₃ bUnsealR₄
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B4 (4, 6): after the left's Beta and the right's Wrap, Beta.  THE
  -- "J" PAIR (SidedMarks.md §4) is the premise `S ⊑ J`: X left-only
  -- after the right's −X, rejoined at the right's +X; αᴿ is still
  -- permitted (the matched boundary above permits it; κ passes both
  -- inner boundaries, and the rejoin pays nothing)

  J : Term
  J = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ₀ , id★ᶜ ⟫

  bJ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bJ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = J}))))

  bJ⁻ : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bJ⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = J ⟪ unb₀ , id★ᶜ ⟫}))))

  -- the J pair (index X ⊑ ★, X left-only)
  S⊑J : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here
  S⊑J = ⊑⟪⟫₀ (Wc-bindᴿ v₀ here⇔) W₄²¹-wf S⊑S! bJ (X⊑★ here)

  p4-B4 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ nth Rs 6 ∶ ι⊑ι base-ℕ
  p4-B4 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf X⊑X
      (⊑cast {p = X⊑★ here}
        (⊑⟪⟫₀ (Wc-unbindᴿ v₀) W₄ᴸ-wf S⊑J bJ⁻ (X⊑★ here))
        chkᵍ-ty X⊑X)
      bUnsealL bUnsealR
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B5 (5, 11): after the Merges; the interiors have no name, the two
  -- conversions are id(ℕ)

  b5L : BdyTy ΔL (unbind 0 0 ∷ bind 0 0 ∷ []) ΔL `ℕ ⌞ id `ℕ ⌟ `ℕ
  b5L = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Ls 5}))))

  b5R : BdyTy ΔL (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ [])
    ΔL `ℕ ⌞ id `ℕ ⌟ `ℕ
  b5R = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = nth Rs 11}))))

  bdy-wf : ∀ {Δ Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ
    → Σ[ Δᶜ ∈ Ctxᵗ ] BoundaryWf Δ Θ Δᵢ Δᶜ
  bdy-wf (bdy-ty mw _ _ _ _) = _ , mw

  int5 : Interior W₄ (unbind 0 0 ∷ bind 0 0 ∷ [])
    (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ []) W₄
  int5 = record
    { int-left   = bw-interior (proj₂ (bdy-wf b5L))
    ; int-right  = bw-interior (proj₂ (bdy-wf b5R))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  p4-B5 : W₄ ∣ [] ⊢ nth Ls 5 ⊑ nth Rs 11 ∶ ι⊑ι base-ℕ
  p4-B5 = ⟪⟫⊑⟪⟫₀ int5 W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b5L b5R
    (W₄² , conv5 , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))
    (ι⊑ι base-ℕ)
    where
    conv5 : ConversionInterior W₄ (unbind 0 0 ∷ bind 0 0 ∷ [])
      (unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ bind 0 0 ∷ []) W₄²
    conv5 = record
      { conv-left       = bw-conversion (proj₂ (bdy-wf b5L))
      ; conv-right      = bw-conversion (proj₂ (bdy-wf b5R))
      ; conv-same-ϱᵍ    = refl
      ; conv-same-ϱˡ    = refl
      ; conv-same-κ     = refl
      ; conv-join-cont  = λ { _ _ () _ }
      ; conv-join-fresh = λ
          { here here _ → (λ _ → inj₁ here⇔) , (λ _ → refl)
          ; here (there ()) _
          ; (there ()) _ _
          }
      }

  -- B6 (6, 12): 5 ⊑ 5
  p4-B6 : W₄ ∣ [] ⊢ nth Ls 6 ⊑ nth Rs 12 ∶ ι⊑ι base-ℕ
  p4-B6 = κ⊑κ lit-$ (ι⊑ι base-ℕ)


------------------------------------------------------------------------
-- 1a. Cg B1 (cambridge Ex 1/20 after the left's catch-up TyBeta):
-- matched `+X` boundaries (αᴸ:=ℕ against the right's Inst αᴿ:=★, paired
-- globally), X both-sided; the matched boundary PERMITS αᴿ (design.md
-- D31), paying with X→X ⊑ X→X; inside it the right's gen wrapper
-- `X! → X?` is a plain ⊑cast; inside its own `−X` X is left-only, where
-- λx:X.x ⊑ λx:★.x reads X ⊑ ★
------------------------------------------------------------------------

module CgB1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (Cg-L; Cg-L-⊢; I★)
  open TIE using (idX; revX; L1′; ΔL; ΔR; ΔLᵢ; bL-ty; revX⊑revX; five⊑)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; Cg-R₂; Cg-R₂-state; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty;
           id★↦ᴿ-ty; ℕ⇒ℕ⊑★⇒★; p0; jr₀)

  Ξg : RepCtx
  Ξg = bindR ★ ∷ []

  ϱg : RepRel
  ϱg = (0 , 0) ∷ []

  Cg-L₁-state : head (drop 1 (evalTerms 10 Cg-L-⊢)) ≡ just L1′
  Cg-L₁-state = refl

  module Wfg {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξg ∣ nsR)
    W = world n η η′ ϱg [] κ

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wg²-wf : WfWorld (Wc² {Ξg} {ϱg} [] 0)
  Wg²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) []
    where open Wfg 1 (keep []↪) (keep []↪) []

  Wgᴴ-wf : WfWorld (Wcᴸ {Ξg} {ϱg} (0 ∷ []))
  Wgᴴ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) p0
    where open Wfg 1 (keep []↪) (skip []↪) (0 ∷ [])

  idX⊑I★ : Wcᴸ {Ξg} {ϱg} (0 ∷ []) ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξg ϱg (0 ∷ [])
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  cg-b1 : Wc⁰ {Ξg} {ϱg} ∣ [] ⊢ L1′ ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
  cg-b1 =
    ·⊑·
      (⊑cast
        (⟪⟫⊑⟪⟫ (Wc-bind² (_ , here) here⇔) (jr₀ ∷ [])
          (wf+κ Wg²-wf ((_ , here) ∷ [])) (c⊑c² Ξg ϱg [] 0)
          (⊑cast {A = ` 0 ⇒ ` 0}
            (⊑⟪⟫₀ (Wc-unbindᴿ (_ , here)) Wgᴴ-wf idX⊑I★ I★⁻ᴿ-ty
              (c⊑★² Ξg ϱg (0 ∷ []) 0 refl))
            tagᴿ-ty (c⊑c² Ξg ϱg (0 ∷ []) 0))
          bL-ty Bg-ty
          (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
      five⊑

------------------------------------------------------------------------
-- 1b. C18b B7 (cambridge Ex 18b, block (7,12)): TWO names at once.
-- Matched outer `(+Y,+X)`, both both-sided; it PERMITS X's rep. var 1
-- only (K = [1], design.md D31), paying with X ⊑ X; the right's `X?` is
-- a plain ⊑cast; the right's `(−Y,−X)` makes both left-only; its
-- `(+X,+Y)` rejoins both, X still permitted (κ = [1] passes both
-- boundaries); the right's `X!` reads X ⊑ ★.  Center 0 is Y (rep. var
-- 0 = β), center 1 is X (rep. var 1 = α).
------------------------------------------------------------------------

module C18bB7 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.Examples using (ℓ)
  open import examples.CambridgeExamples using (C18b-L-⊢; C18b-R-⊢)
  open P4 using (nth)

  Δ₀ Δ₂ : Ctxᵗ
  Δ₀ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ []
  Δ₂ = (bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ (0 ∷ 1 ∷ [])

  Θo Θh Θj ΘS : Boundary
  Θo = bind 1 1 ∷ bind 0 0 ∷ []
  Θh = unbind 0 1 ∷ unbind 0 0 ∷ []
  Θj = bind 0 0 ∷ bind 0 1 ∷ []
  ΘS = unbind 0 0 ∷ unbind 1 1 ∷ []

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S2 J2 RH L7 R12 : Term
  S2  = $ 42 ⟪ ΘS , tail (seal 1) ⟫
  J2  = (S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩) ⟪ Θj , id★ᶜ ⟫
  RH  = J2 ⟪ Θh , id★ᶜ ⟫
  L7  = S2 ⟪ Θo , unseal 1 ⟫
  R12 = (RH ⟨ ★∼X ∷ ★∼X ∷ [] ∣ (` 1) ？ ℓ ⟩) ⟪ Θo , unseal 1 ⟫

  L7-state : nth (evalTerms 30 C18b-L-⊢) 7 ≡ L7
  L7-state = refl

  R12-state : nth (evalTerms 30 C18b-R-⊢) 12 ≡ R12
  R12-state = refl

  ϱ : RepRel
  ϱ = (0 , 0) ∷ (1 , 1) ∷ []

  W₀ : List RVar → World Δ₀ Δ₀
  W₀ κ = world 0 []↪ []↪ ϱ [] κ

  -- both both-sided, X⊑★
  Wb : List RVar → World Δ₂ Δ₂
  Wb κ = world 2 (keep (keep []↪)) (keep (keep []↪)) ϱ [] κ

  -- both left-only (inside the right's (−Y,−X))
  Wh : List RVar → World Δ₂ Δ₀
  Wh κ = world 2 (keep (keep []↪)) (skip (skip []↪)) ϱ [] κ

  module Wf {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsL)
              ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsR)
    W = world n η η′ ϱ [] κ

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ here⇔)) =
      rep-rep (r-there r-here) (r-there r-here) (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ (there⇔ ())))
    agree (inj₂ ())

    diag : ∀ {α β} → Paired W α β → α ≡ β
    diag (inj₁ here⇔) = refl
    diag (inj₁ (there⇔ here⇔)) = refl
    diag (inj₁ (there⇔ (there⇔ ())))
    diag (inj₂ ())

    uniqᴸ : NamedUniqueᴸ W
    uniqᴸ _ _ _ p p′ = trans (diag p) (sym (diag p′))

    uniqᴿ : NamedUniqueᴿ W
    uniqᴿ _ _ _ p p′ = trans (sym (diag p)) (diag p′)

  Rs₂ : RepCtx
  Rs₂ = bindR `ℕ ∷ bindR `ℕ ∷ []

  p1 : All (Rs₂ ∋ʳ_) (1 ∷ [])
  p1 = (_ , there here) ∷ []

  W₀-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (W₀ κ)
  W₀-wf {κ} ps = wf-world joint[] agree uniqᴸ uniqᴿ ps
    where open Wf 0 []↪ []↪ κ

  Wb-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (Wb κ)
  Wb-wf {κ} ps =
    wf-world (both (inj₁ here⇔) (both (inj₁ (there⇔ here⇔)) joint[]))
      agree uniqᴸ uniqᴿ ps
    where open Wf 2 (keep (keep []↪)) (keep (keep []↪)) κ

  Wh-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (Wh κ)
  Wh-wf {κ} ps =
    wf-world (left-only (left-only joint[])) agree uniqᴸ uniqᴿ ps
    where open Wf 2 (keep (keep []↪)) (skip (skip []↪)) κ

  -- the boundaries' interior contexts
  int-o : Δ₀ ⊢ⁱ Θo ⇒ Δ₂
  int-o = interior (changes∷ (changes∷ changes[]
    (step-bind (_ , here) fresh[] ins-here))
    (step-bind (_ , there here) (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))

  int-h : Δ₂ ⊢ⁱ Θh ⇒ Δ₀
  int-h = interior (changes∷ (changes∷ changes[]
    (step-unbind (_ , here) del-here (fresh∷ (λ ()) fresh[])))
    (step-unbind (_ , there here) del-here fresh[]))

  int-j : Δ₀ ⊢ⁱ Θj ⇒ Δ₂
  int-j = interior (changes∷ (changes∷ changes[]
    (step-bind (_ , there here) fresh[] ins-here))
    (step-bind (_ , here) (fresh∷ (λ ()) fresh[]) ins-here))

  int-S : Δ₂ ⊢ⁱ ΘS ⇒ Δ₀
  int-S = interior (changes∷ (changes∷ changes[]
    (step-unbind (_ , there here) (del-there del-here) (fresh∷ (λ ()) fresh[])))
    (step-unbind (_ , here) del-here fresh[]))

  -- the joins of the two fresh pairs: name i on each side, rep. var i
  pairs : ∀ {κ κ′ X X′ α β} → Δ₂ ∋ᵗ X := α → Δ₂ ∋ᵗ X′ := β
    → (Joins (Wb κ) X X′ → Paired (W₀ κ′) α β)
      × (Paired (W₀ κ′) α β → Joins (Wb κ) X X′)
  pairs here here = (λ _ → inj₁ here⇔) , (λ _ → refl)
  pairs here (there here) =
    (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
  pairs (there here) here =
    (λ ()) , (λ { (inj₁ (there⇔ (there⇔ ()))) ; (inj₂ ()) })
  pairs (there here) (there here) = (λ _ → inj₁ (there⇔ here⇔)) , (λ _ → refl)

  -- the matched outer (+Y,+X): both fresh, both joined
  IntO : Interior (W₀ []) Θo Θo (Wb [])
  IntO = record
    { int-left   = int-o
    ; int-right  = int-o
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , here) _ () _ ; (_ , there here) _ () _ }
    ; join-fresh = λ a b _ → pairs {[]} {[]} a b
    }

  -- the right's (−Y,−X): both continuing left names become left-only
  IntH : ∀ {κ} → Interior (Wb κ) [] Θh (Wh κ)
  IntH = record
    { int-left   = interior changes[]
    ; int-right  = int-h
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , ()) _ _ }
    ; join-fresh = λ { _ () _ }
    }

  -- the right's (+X,+Y): both names REJOIN; κ is unchanged
  IntJ : ∀ {κ} → Interior (Wh κ) [] Θj (Wb κ)
  IntJ {κ} = record
    { int-left   = interior changes[]
    ; int-right  = int-j
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there here) _ () }
    ; join-fresh = λ a b _ → pairs {κ} {κ} a b
    }

  -- the matched (−X,−Y) of the sealed literal: no names inside
  IntS : ∀ {κ} → Interior (Wb κ) ΘS ΘS (W₀ κ)
  IntS = record
    { int-left   = int-S
    ; int-right  = int-S
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  conv-o : Δ₀ ⊢ᶜ Θo ⇒ Δ₂
  conv-o = conversion (conv-bind (_ , there here)
    (conv-bind (_ , here) conv[] fresh[] ins-here)
    (fresh∷ (λ ()) fresh[]) (ins-there ins-here))

  conv-S : Δ₂ ⊢ᶜ ΘS ⇒ Δ₂
  conv-S = conversion (conv-unbind (_ , here)
    (conv-unbind (_ , there here) conv[]))

  ConvO : ConversionInterior (W₀ []) Θo Θo (Wb [])
  ConvO = record
    { conv-left       = conv-o
    ; conv-right      = conv-o
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ { _ _ () _ }
    ; conv-join-fresh = λ a b _ → pairs {[]} {[]} a b
    }

  named₂ : ∀ {X α} → Δ₂ ∋ᵗ X := α → names Δ₂ ∌ʳ α → ⊥
  named₂ here         (fresh∷ n _)          = n refl
  named₂ (there here) (fresh∷ _ (fresh∷ n _)) = n refl

  ConvS : ∀ {κ} → ConversionInterior (Wb κ) ΘS ΘS (Wb κ)
  ConvS = record
    { conv-left       = conv-S
    ; conv-right      = conv-S
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here (there here) here (there here) → (λ j → j) , (λ j → j)
        ; (there here) here (there here) here → (λ j → j) , (λ j → j)
        ; (there here) (there here) (there here) (there here) →
            (λ j → j) , (λ j → j)
        ; (there (there ())) _ _ _
        ; _ (there (there ())) _ _
        ; _ _ (there (there ())) _
        ; _ _ _ (there (there ()))
        }
    ; conv-join-fresh = λ
        { a _ (inj₁ f) → ⊥-elim (named₂ a f)
        ; _ b (inj₂ f) → ⊥-elim (named₂ b f)
        }
    }

  bS : BdyTy Δ₂ ΘS Δ₀ `ℕ (tail (seal 1)) (` 1)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₂} {M = S2}))))

  bJ2 : BdyTy Δ₀ Θj Δ₂ ★ id★ᶜ ★
  bJ2 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = J2}))))

  bRH : BdyTy Δ₂ Θh Δ₀ ★ id★ᶜ ★
  bRH = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₂} {M = RH}))))

  bL7 : BdyTy Δ₀ Θo Δ₂ (` 1) (unseal 1) `ℕ
  bL7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = L7}))))

  bR12 : BdyTy Δ₀ Θo Δ₂ (` 1) (unseal 1) `ℕ
  bR12 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = Δ₀} {M = R12}))))

  tag-ty : CastTy Δ₂ (flipᵐ ★∼X ∷ X∼★ ∷ []) ((` 1) !) (` 1) ★
  tag-ty = cast-ty (⊢tag-var (_ , there here) (there here) tag-dyn) refl

  chk-ty : CastTy Δ₂ (★∼X ∷ ★∼X ∷ []) ((` 1) ？ ℓ) ★ (` 1)
  chk-ty = cast-ty (⊢check-var (_ , there here) (there here) check-dyn) refl

  -- X (center 1) at X⊑★ under X's permission (Y stays X⊑X)
  X★ : marksʷ (Wb (1 ∷ [])) ∋ˡ 1 := X⊑★
  X★ = there here

  S2⊑S2 : Wb (1 ∷ []) ∣ [] ⊢ S2 ⊑ S2 ∶ X⊑X
  S2⊑S2 = ⟪⟫⊑⟪⟫₀ IntS (W₀-wf p1) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (Wb (1 ∷ []) , ConvS , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- inside the rejoin: the right's X! at the rejoined, permitted X
  inner : Wb (1 ∷ []) ∣ [] ⊢ S2 ⊑ S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩
    ∶ X⊑★ X★
  inner = ⊑cast S2⊑S2 tag-ty (X⊑★ X★)

  -- the matched outer boundary joins X (its fresh pair through ϱ)
  jr₁ : JoinRep (Wb []) Θo Θo [] 1
  jr₁ = jr-join (_ , there here) (there here) (inj₁ refl) refl

  c18b-b7 : W₀ [] ∣ [] ⊢ L7 ⊑ R12 ∶ ι⊑ι base-ℕ
  c18b-b7 =
    ⟪⟫⊑⟪⟫ IntO (jr₁ ∷ []) (Wb-wf p1) X⊑X
      (⊑cast {p = X⊑★ X★}
        (⊑⟪⟫₀ IntH (Wh-wf p1)
          (⊑⟪⟫₀ IntJ (Wb-wf p1) inner bJ2 (X⊑★ (there here)))
          bRH (X⊑★ X★))
        chk-ty X⊑X)
      bL7 bR12 (Wb [] , ConvO , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- 2. Reduction closure on P4's run (SimBack evidence): the left at B4
-- (`[+X^α] S ⟨+X⟩`) is related to EVERY right state its Merge, IdDyn,
-- Merge, TagUntag steps produce (right states 7-10).  The merged
-- `[−X, +X]` is an unbind then a bind of X in ONE boundary: `toExt`
-- makes X continuing on both sides, so X stays joined, and αᴿ stays
-- permitted (the matched boundary above permits it, design.md D31);
-- after IdDyn the tag `X!` is outside, still under the check.  (State
-- 11, the final Merge, needs the left's own Merge: B5.)
------------------------------------------------------------------------

module P4c where
  open import examples.TypeCheck using (tc; tf)
  open P4 using (nth; Ls; Rs; S; unb₀; id★ᶜ; tagX; chkX; tagˣ-ty; chkᵍ-ty;
                 bUnsealL; W₄; W₄²; W₄-wf; W₄²-wf; v₀; S⊑S; bS; bdy-wf;
                 Ξ₄; ϱ₄; W₄²¹; W₄²¹-wf; W₄⁰; W₄⁰-wf; p0)
  open Rebase using (Wc²; jr₀)
  open TIE using (ΔL; ΔLᵢ; Θ₀)
  open Rebase using (Θ⁻⁺; Θ⁻⁺-int; Wc-bind²; Wc-bind²-conv; unbind₀-int;
                     unbind₀-conv)

  Θ³ : Boundary
  Θ³ = unbind 0 0 ∷ bind 0 0 ∷ unbind 0 0 ∷ []

  Bm7 Bi8 S3 R7 R8 R9 R10 : Term
  Bm7 = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ⁻⁺ , id★ᶜ ⟫
  Bi8 = S ⟪ Θ⁻⁺ , ⌞ id (` 0) ⌟ ⟫
  S3  = $ 5 ⟪ Θ³ , tail (seal 0) ⟫
  R7  = (Bm7 ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R8  = ((Bi8 ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R9  = ((S3 ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟨ ★∼X ∷ [] ∣ chkX ⟩) ⟪ Θ₀ , unseal 0 ⟫
  R10 = S3 ⟪ Θ₀ , unseal 0 ⟫

  R7-state : nth Rs 7 ≡ R7
  R7-state = refl

  R8-state : nth Rs 8 ≡ R8
  R8-state = refl

  R9-state : nth Rs 9 ≡ R9
  R9-state = refl

  R10-state : nth Rs 10 ≡ R10
  R10-state = refl

  -- the right's [−X, +X] alone: X continuing on both sides, joined
  IntRR : Interior W₄²¹ [] Θ⁻⁺ W₄²¹
  IntRR = record
    { int-left   = interior changes[]
    ; int-right  = Θ⁻⁺-int
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ
        { (_ , here) (_ , here) refl refl → (λ j → j) , (λ j → j)
        ; (_ , here) (_ , there ()) _ _
        ; (_ , there ()) _ _ _
        }
    ; join-fresh = λ
        { here here (inj₁ ()) ; here here (inj₂ ())
        ; here (there ()) _ ; (there ()) _ _ }
    }

  bBm7 : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ ★ id★ᶜ ★
  bBm7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Bm7}))))

  bBi8 : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0) ⌞ id (` 0) ⌟ (` 0)
  bBi8 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Bi8}))))

  bS3 : BdyTy ΔLᵢ Θ³ ΔL `ℕ (tail (seal 0)) (` 0)
  bS3 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S3}))))

  bR7 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR7 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R7}))))

  bR8 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR8 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R8}))))

  bR9 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR9 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R9}))))

  bR10 : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bR10 = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = R10}))))

  -- the left's sealed 5 against the right's merged [−X, +X, −X] 5 ⟨−X⟩
  Int3 : ∀ {κ} → Interior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ Θ³ (W₄⁰ κ)
  Int3 = record
    { int-left   = unbind₀-int
    ; int-right  = bw-interior (proj₂ (bdy-wf bS3))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  Conv3 : ∀ {κ} → ConversionInterior (Wc² {Ξ₄} {ϱ₄} κ 0) unb₀ Θ³
    (Wc² {Ξ₄} {ϱ₄} κ 0)
  Conv3 = record
    { conv-left       = unbind₀-conv
    ; conv-right      = bw-conversion (proj₂ (bdy-wf bS3))
    ; conv-same-ϱᵍ    = refl
    ; conv-same-ϱˡ    = refl
    ; conv-same-κ     = refl
    ; conv-join-cont  = λ
        { here here here here → (λ j → j) , (λ j → j)
        ; here here here (there ())
        ; here here (there ()) _
        ; here (there ()) _ _
        ; (there ()) _ _ _
        }
    ; conv-join-fresh = λ
        { here here (inj₁ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here here (inj₂ (fresh∷ n _)) → ⊥-elim (n refl)
        ; here (there ()) _
        ; (there ()) _ _
        }
    }

  S⊑S3 : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ
    → Wc² {Ξ₄} {ϱ₄} κ 0 ∣ [] ⊢ S ⊑ S3 ∶ X⊑X
  S⊑S3 ps = ⟪⟫⊑⟪⟫₀ Int3 (W₄⁰-wf ps) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS3
    (_ , Conv3 , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- the left's B4 boundary against the right's matched `+X`: it permits
  -- αᴿ (K = [0], design.md D31; paying X ⊑ X) while the right's check
  -- is still there (states 7-9), and permits nothing after TagUntag
  -- (state 10)
  outer : ∀ {M′} → (b′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ)
    → BdyConversionImp W₄ bUnsealL b′
    → W₄²¹ ∣ [] ⊢ S ⊑ M′ ∶ X⊑X
    → W₄ ∣ [] ⊢ nth Ls 4 ⊑ M′ ⟪ Θ₀ , unseal 0 ⟫ ∶ ι⊑ι base-ℕ
  outer b′ bc d =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf X⊑X d bUnsealL b′ bc
      (ι⊑ι base-ℕ)

  outer₀ : ∀ {M′} → (b′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ)
    → BdyConversionImp W₄ bUnsealL b′
    → W₄² ∣ [] ⊢ S ⊑ M′ ∶ X⊑X
    → W₄ ∣ [] ⊢ nth Ls 4 ⊑ M′ ⟪ Θ₀ , unseal 0 ⟫ ∶ ι⊑ι base-ℕ
  outer₀ b′ bc d =
    ⟪⟫⊑⟪⟫₀ (Wc-bind² v₀ here⇔) W₄²-wf d bUnsealL b′ bc (ι⊑ι base-ℕ)

  p4-R7 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R7 ∶ ι⊑ι base-ℕ
  p4-R7 = outer bR7
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast {p = X⊑★ here}
      (⊑⟪⟫₀ IntRR W₄²¹-wf (⊑cast S⊑S tagˣ-ty (X⊑★ here)) bBm7
        (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R8 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R8 ∶ ι⊑ι base-ℕ
  p4-R8 = outer bR8
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast {p = X⊑★ here}
      (⊑cast {p = X⊑X} (⊑⟪⟫₀ IntRR W₄²¹-wf S⊑S bBi8 X⊑X)
        tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R9 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R9 ∶ ι⊑ι base-ℕ
  p4-R9 = outer bR9
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast {p = X⊑★ here}
      (⊑cast {p = X⊑X} (S⊑S3 p0) tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R10 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R10 ∶ ι⊑ι base-ℕ
  p4-R10 = outer₀ bR10
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl) (S⊑S3 [])


------------------------------------------------------------------------
-- 3. Facts for the non-derivability proofs (design.md D31).  A
-- top-level world has no permission (κʷ ≡ []); a permission enters
-- only at a boundary that JOINS a type variable (`JoinRep`), and that
-- boundary pays with its interior index read without it.  Under κʷ ≡ []
-- a center type variable the right sees is X⊑X (`no★-right`), so a
-- right tag `X!` can face no untagged left value (`no-tag★`), and a
-- boundary whose payment puts the joined type variable against ★ can
-- permit nothing (`K-pay`).  The proofs quantify over every slot list.
------------------------------------------------------------------------

lookup-unique : ∀ {A : Set} {xs : List A} {k a b}
  → xs ∋ˡ k := a → xs ∋ˡ k := b → a ≡ b
lookup-unique here      here       = refl
lookup-unique (there h) (there h′) = lookup-unique h h′

-- the derived mark of a right type variable is its permission
dmarks-emb : ∀ {ns n X β} (ι : ns ↪ n) (κ : List RVar) → ns ∋ˡ X := β
  → dmarks ι κ ∋ˡ emb ι X := permit β κ
dmarks-emb (keep ι) κ here      = here
dmarks-emb (keep ι) κ (there h) = there (dmarks-emb ι κ h)
dmarks-emb (skip ι) κ h         = there (dmarks-emb ι κ h)

-- NO PERMISSION, NO X⊑★ AT A TYPE VARIABLE THE RIGHT SEES
no★-right : ∀ {V : World Δ Δ′} {X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ¬ (marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := X⊑★)
no★-right {V = V} {β = β} eκ rh h
  with trans (lookup-unique h (dmarks-emb (ηᴿʷ V) (κʷ V) rh))
             (cong (permit β) eκ)
... | ()

-- ... so a left type variable joined to a right one is not X⊑★
no-tag★ : ∀ {V : World Δ Δ′} {X X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → Joins V X X′ → ¬ (marksʷ V ∋ˡ emb (ηᴸʷ V) X := X⊑★)
no-tag★ {V = V} eκ rh j h =
  no★-right {V = V} eκ rh (subst (λ c → marksʷ V ∋ˡ c := X⊑★) j h)

-- the index of a non-∀ left type has no slot
data NonForall : Ty → Set where
  nf-var : ∀ {X} → NonForall (` X)
  nf-ℕ   : NonForall `ℕ
  nf-𝔹   : NonForall `𝔹
  nf-★   : NonForall ★
  nf-⇒   : ∀ {A B} → NonForall (A ⇒ B)

nfO : ∀ {μ e O ρ A B} → NonForall A → OpenO μ e O ρ A B → O ≡ []
nfO {O = []}        _      _  = refl
nfO {O = opn _ ∷ _} nf-var ()
nfO {O = opn _ ∷ _} nf-ℕ   ()
nfO {O = opn _ ∷ _} nf-𝔹   ()
nfO {O = opn _ ∷ _} nf-★   ()
nfO {O = opn _ ∷ _} nf-⇒   ()
nfO {O = skp ∷ _}   nf-var ()
nfO {O = skp ∷ _}   nf-ℕ   ()
nfO {O = skp ∷ _}   nf-𝔹   ()
nfO {O = skp ∷ _}   nf-★   ()
nfO {O = skp ∷ _}   nf-⇒   ()

plain-idx : ∀ {V : World Δ Δ′} {O A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩[ O ] A′
  → marksʷ V ⊢ embᴸ V A ⊑ embᴿ V A′
plain-idx {V = V} {O} {A} {A′} nf q =
  subst (λ O → A ⊑ᵂ⟨ V ⟩[ O ] A′) (nfO {μ = marksʷ V} {e = emb (ηᴿʷ V)}
    {O = O} {ρ = emb (ηᴸʷ V)} {A = A} {B = embᴿ V A′} nf q) q

var⊑var : ∀ {μ a b} → μ ⊢ ` a ⊑ ` b → a ≡ b
var⊑var X⊑X = refl

var⊑★ : ∀ {μ a} → μ ⊢ ` a ⊑ ★ → μ ∋ˡ a := X⊑★
var⊑★ (X⊑★ h) = h

no-plain-ℕ⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ `ℕ ⊑ ` a)
no-plain-ℕ⊑var ()

no-plain-★⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ ★ ⊑ ` a)
no-plain-★⊑var ()

-- the two typings of a derivation (proof/DGG/ImprecisionTyping)
ltyD : ∀ {V : World Δ Δ′} {γ M M′ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → V ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q → Δ ∣ lhs γ ⊢ M ⦂ A
ltyD d = proj₁ (imprecision-typing d)

rtyD : ∀ {V : World Δ Δ′} {γ M M′ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → V ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
rtyD d = proj₂ (imprecision-typing d)

-- typing inversions
ty-cast : ∀ {Γ M μ p A} → Δ ∣ Γ ⊢ M ⟨ μ ∣ p ⟩ ⦂ A → A ≡ trgᵖ p
ty-cast (⊢cast _ ⊢p _) = sym (coercion-trg ⊢p)

ty-ƛ : ∀ {Γ A₀ N A} → Δ ∣ Γ ⊢ ƛ A₀ ∙ N ⦂ A
  → Σ[ B ∈ Ty ] (A ≡ A₀ ⇒ B) × (Δ ∣ A₀ ∷ Γ ⊢ N ⦂ B)
ty-ƛ (⊢ƛ _ ⊢N) = _ , refl , ⊢N

ty-$ : ∀ {Γ n A} → Δ ∣ Γ ⊢ $ n ⦂ A → A ≡ `ℕ
ty-$ ⊢$ = refl

-- the left types of λx:X. x
idX′ : Term
idX′ = ƛ (` 0) ∙ ` 0

-- coercion typings of the casts that occur
ct-id★ : ∀ {μ B A} → CastTy Δ μ (idᵖ ★) B A → (B ≡ ★) × (A ≡ ★)
ct-id★ (cast-ty (⊢id _ _) _) = refl , refl

ct-ℕ! : ∀ {μ B A} → CastTy Δ μ (`ℕ !) B A → (B ≡ `ℕ) × (A ≡ ★)
ct-ℕ! (cast-ty (⊢tag g-ℕ) _) = refl , refl

ct-ℕ? : ∀ {μ ℓ B A} → CastTy Δ μ (`ℕ ？ ℓ) B A → (B ≡ ★) × (A ≡ `ℕ)
ct-ℕ? (cast-ty (⊢check g-ℕ) _) = refl , refl

ct-X! : ∀ {μ X B A} → CastTy Δ μ ((` X) !) B A
  → (Δ ∋tv X) × (B ≡ ` X) × (A ≡ ★)
ct-X! (cast-ty (⊢tag ()) _)
ct-X! (cast-ty (⊢tag-var tv _ _) _) = tv , refl , refl

-- the bind entry `+X^0` from a context with no type variable
Θ₀ : Boundary
Θ₀ = bind 0 0 ∷ []

-- a new opening makes the interior's slots nonempty
fill-∋ᵒ : ∀ {O′ N Oᵢ k} → Fill O′ N Oᵢ → N ∋ᵒ k → Oᵢ ≢ []
fill-∋ᵒ f-end      oh ()
fill-∋ᵒ f-end      (ot _) ()
fill-∋ᵒ (f-keep _) _ ()
fill-∋ᵒ (f-fill _) _ ()

push-∋ᵒ : ∀ {Θ′ M O N Oᵢ k} → Push Θ′ M O N Oᵢ → N ∋ᵒ k → Oᵢ ≢ []
push-∋ᵒ (push _ f _ _) n = fill-∋ᵒ f n

-- no permission can be added
K-none : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ N K}
  → (∀ {β} → ¬ JoinRep Wᵢ Θ Θ′ N β) → All (JoinRep Wᵢ Θ Θ′ N) K → K ≡ []
K-none no []      = refl
K-none no (j ∷ _) = ⊥-elim (no j)

κ-keep : ∀ {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ K}
  → Interior W Θ Θ′ Wᵢ → K ≡ [] → κʷ W ≡ [] → κʷ (Wᵢ +κ K) ≡ []
κ-keep I refl eκ = trans (same-κ I) eκ

-- the left variable 0, facing ★ at a world without permissions, joins
-- no right variable (THE PAYMENT'S CONSEQUENCE)
no-join★ : ∀ {V : World Δ Δ′} → κʷ V ≡ [] → (` 0) ⊑ᵂ⟨ V ⟩ ★
  → ∀ {X′ β} → Δ′ ∋ᵗ X′ := β → ¬ Joins V 0 X′
no-join★ {V = V} eκ q rh j = no-tag★ {V = V} eκ rh j (var⊑★ q)

-- the left context has the one type variable 0
OnlyZero : Ctxᵗ → Set
OnlyZero Δ = ∀ {X} → Δ ∋tv X → X ≡ 0

-- ... so a boundary whose payment puts it against ★ joins nothing
K-pay : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ K}
  → OnlyZero Δᵢ → κʷ Wᵢ ≡ [] → (` 0) ⊑ᵂ⟨ Wᵢ ⟩ ★
  → All (JoinRep Wᵢ Θ Θ′ []) K → K ≡ []
K-pay {Wᵢ = Wᵢ} {Θ} {Θ′} oz eκ q = K-none no
  where
  no : ∀ {β} → ¬ JoinRep Wᵢ Θ Θ′ [] β
  no (jr-join tv rh _ j) with oz tv
  ... | refl = no-join★ {V = Wᵢ} eκ q rh j
  no (jr-open () _)

-- the exterior and interior types of an `id(★)` boundary
bdy-id★ : ∀ {Δ₀ Θ Δᵢ Aᵢ A} → BdyTy Δ₀ Θ Δᵢ Aᵢ ⌞ id ★ ⌟ A
  → (Aᵢ ≡ ★) × (A ≡ ★)
bdy-id★ (bdy-ty _ (conv-tail (conv-mid (conv-id ()))) _ _ _)
bdy-id★ (bdy-ty _ (conv-tail (conv-mid conv-id★)) (_ , same-★ , same-★)
  (_ , same-★ , same-★) _) = refl , refl

-- runs (HiddenNames.Runs, copied): every reachable state is a state of
-- the evalTerms run (determinism)
module Runs where
  open import examples.Eval
    using (eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed;
           no-redex; out-of-fuel; evalTerms; traceTerms; step; StepResult)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
  open import proof.TypeSafety.Determinism using (det)
  open import proof.TypeSafety.Irreducible using (irreducible)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  import Data.List.Relation.Unary.All as All

  justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
    → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
  justStep {r = r} _ = proj₂ (proj₂ r)

  EndsVB : ∀ {Δ A M} → Trace Δ A M → Set
  EndsVB (stop (value _))   = ⊤
  EndsVB (stop (blamed _))  = ⊤
  EndsVB (stop no-redex)    = ⊥
  EndsVB (stop out-of-fuel) = ⊥
  EndsVB (illtyped _)       = ⊥
  EndsVB (_ ◅⟨ _ ⟩ tr)      = EndsVB tr

  in-trace : ∀ {Δ A M N} (tr : Trace Δ A M) → Δ ∣ [] ⊢ M ⦂ A
    → EndsVB tr → Δ ⊢ M -→* N → N ∈ traceTerms tr
  in-trace (stop f) ⊢M e done = here refl
  in-trace (illtyped _) ⊢M e done = here refl
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e done = here refl
  in-trace (stop (value v)) ⊢M e (st then r) =
    ⊥-elim (proj₁ irreducible v st)
  in-trace (stop (blamed refl)) ⊢M e (st then r) =
    ⊥-elim (proj₂ irreducible st)
  in-trace (stop no-redex) ⊢M () (st then r)
  in-trace (stop out-of-fuel) ⊢M () (st then r)
  in-trace (illtyped _) ⊢M () (st then r)
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) with det ⊢M st st′
  in-trace (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) | refl , refl =
    there (in-trace tr ⊢M′ e r)

  all-reach : ∀ {Δ A M N} {P : Term → Set} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
    → EndsVB (eval k M ⊢M) → All P (evalTerms k ⊢M)
    → Δ ⊢ M -→* N → P N
  all-reach k ⊢M e a r = All.lookup a (in-trace (eval k _ ⊢M) ⊢M e r)

  NotBlame : Term → Set
  NotBlame N = ∀ {ℓ} → N ≡ blame ℓ → ⊥

  last : List Term → Term
  last []           = $ 0
  last (x ∷ [])     = x
  last (x ∷ y ∷ xs) = last (y ∷ xs)

data G : Ty → Set where
  gℕ : G `ℕ
  g★ : G ★

no-G⊑varᵖ : ∀ {μ : ImpEnv} {ρ A a} → G A → ¬ (μ ⊢ renameᵗ ρ A ⊑ ` a)
no-G⊑varᵖ gℕ = no-plain-ℕ⊑var
no-G⊑varᵖ g★ = no-plain-★⊑var

data GCast : Coercion → Set where
  gc-ℕ!  : GCast (`ℕ !)
  gc-ℕ?  : GCast (`ℕ ？ 0)
  gc-id★ : GCast (idᵖ ★)

gsrc : ∀ {c μ B A} → GCast c → CastTy Δ μ c B A → G B
gsrc gc-ℕ!  ct with ct-ℕ! ct
... | refl , _ = gℕ
gsrc gc-ℕ?  ct with ct-ℕ? ct
... | refl , _ = g★
gsrc gc-id★ ct with ct-id★ ct
... | refl , _ = g★

gtrg : ∀ {c μ B A} → GCast c → CastTy Δ μ c B A → G A
gtrg gc-ℕ!  ct with ct-ℕ! ct
... | _ , refl = g★
gtrg gc-ℕ?  ct with ct-ℕ? ct
... | _ , refl = gℕ
gtrg gc-id★ ct with ct-id★ ct
... | _ , refl = g★

sealed : Term → Term
sealed m = m ⟪ unbind 0 0 ∷ [] , tail (seal 0) ⟫

G-nf : ∀ {A} → G A → NonForall A
G-nf gℕ = nf-ℕ
G-nf g★ = nf-★

------------------------------------------------------------------------
-- 4. The spine argument for C1 and C2.  A right spine of ground casts
-- and `id(★)` boundaries reaching a tag `X!` (`Reach`); a left term
-- outside its own `[+X^α] (sealed m) ⟨+X⟩` under ground casts (`LO`).
-- Every boundary on the way is entered with no permission: outside the
-- left boundary nothing left is bound to a type variable (no join); at
-- the left boundary and inside it, the payment reads the left's X
-- against ★ (`K-pay`), so X joins no right type variable and no
-- permission is added; the decisive ⊑cast of the tag then needs
-- X ⊑ X′ and X ⊑ ★ at κ = [] (`no-tag★`).
------------------------------------------------------------------------

data Reach : Term → Set where
  r-tag  : ∀ {U μ k} → Reach (U ⟨ μ ∣ (` k) ! ⟩)
  r-cast : ∀ {R μ c} → GCast c → Reach R → Reach (R ⟨ μ ∣ c ⟩)
  r-⟪⟫   : ∀ {R Θ} → Reach R → Reach (R ⟪ Θ , ⌞ id ★ ⌟ ⟫)

gc-trg : ∀ {c} → GCast c → G (trgᵖ c)
gc-trg gc-ℕ! = g★
gc-trg gc-ℕ? = gℕ
gc-trg gc-id★ = g★

reach-G : ∀ {Γ R A′} → Reach R → Δ′ ∣ Γ ⊢ R ⦂ A′ → G A′
reach-G r-tag ⊢R with ty-cast ⊢R
... | refl = g★
reach-G (r-cast gc _) ⊢R with ty-cast ⊢R
... | refl = gc-trg gc
reach-G (r-⟪⟫ _) ⊢R with ⟪⟫-inv ⊢R
... | _ , _ , _ , b = G-from (proj₂ (bdy-id★ b))
  where
  G-from : ∀ {A} → A ≡ ★ → G A
  G-from refl = g★

-- left literals against a spine (by types alone)
no-$ : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ n R O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⊑ R ∶⟨ A , A′ ⟩[ O ] q)
no-$ {V = V} {O = O} r-tag (⊑cast {A = A} {B′ = B′} {p = p} d ct _)
  with ct-X! ct | ty-$ (ltyD d)
... | _ , refl , refl | refl
  with plain-idx {V = V} {O = O} {A = A} {A′ = B′} nf-ℕ p
... | ()
no-$ (r-cast _ r) (⊑cast d _ _) = no-$ r d
no-$ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ _ _ _ _ d _ _) = no-$ r d

no-n★ : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ n μ R O A A′}
    {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⟨ μ ∣ `ℕ ! ⟩ ⊑ R ∶⟨ A , A′ ⟩[ O ] q)
no-n★ {V = V} {O = O} r-tag (⊑cast {A = A} {B′ = B′} {p = p} d ct _)
  with ct-X! ct | ty-cast (ltyD d)
... | _ , refl , refl | refl
  with plain-idx {V = V} {O = O} {A = A} {A′ = B′} nf-★ p
... | ()
no-n★ r-tag (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ! ct | ct-X! ct′
... | refl , refl | _ , refl , refl with p
... | ()
no-n★ (r-cast _ r) (cast⊑cast d _ _ _) = no-$ r d
no-n★ (r-cast _ r) (⊑cast d _ _) = no-n★ r d
no-n★ r (cast⊑ co-plain d _ _) = no-$ r d
no-n★ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ _ _ _ _ d _ _) = no-n★ r d

-- the type variables of the left boundary's interior: just X
oz₀ : ∀ {R} → OnlyZero ((bindR R ∷ []) ∣ (0 ∷ []))
oz₀ (_ , here) = refl
oz₀ (_ , there ())

module Spine (m : Term)
  (no-leaf : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R O A A′}
     {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
     → Reach R → ¬ (V ∣ γ ⊢ m ⊑ R ∶⟨ A , A′ ⟩[ O ] q))
  (Δ₀ : Ctxᵗ)
  (no-tvs : ∀ {X} → ¬ (Δ₀ ∋tv X))
  (bdy : ∀ {Δᵢ Aᵢ A} → BdyTy Δ₀ Θ₀ Δᵢ Aᵢ (unseal 0) A
     → (Aᵢ ≡ ` 0) × G A × OnlyZero Δᵢ)
  where

  -- INSIDE the left boundary: the sealed leaf (type X) against the spine
  no-S : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → OnlyZero Δ₁ → κʷ V ≡ [] → A ≡ ` 0 → Reach R
    → ¬ (V ∣ γ ⊢ sealed m ⊑ R ∶⟨ A , A′ ⟩[ O ] q)
  no-S {V = V} {O = O} oz eκ refl r-tag (⊑cast {B′ = B′} {p = p} d ct q)
    with ct-X! ct
  ... | (_ , rh) , refl , refl =
    no-tag★ {V = V} eκ rh
      (var⊑var (plain-idx {V = V} {O = O} {A′ = B′} nf-var p))
      (var⊑★ (plain-idx {V = V} {O = O} {A′ = ★} nf-var q))
  no-S oz eκ eA (r-cast _ r) (⊑cast d _ _) = no-S oz eκ eA r d
  no-S {Δ₁} {V = V} oz eκ refl (r-⟪⟫ r)
    (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} I pu _ _ ks _ pay d b _)
    with bdy-id★ b
  ... | refl , _ with nfO {O = Oᵢ} nf-var pay
  ... | refl =
    no-S oz (κ-keep I (K-none no ks) eκ) refl r d
    where
    eκᵢ : κʷ Vi ≡ []
    eκᵢ = trans (same-κ I) eκ
    no : ∀ {β} → ¬ JoinRep Vi [] _ _ β
    no (jr-join tv rh _ j) with oz tv
    ... | refl = no-join★ {V = Vi} eκᵢ pay rh j
    no (jr-open n _) = push-∋ᵒ pu n refl
  no-S oz eκ eA r (⟪⟫⊑⟪⟫ _ _ _ _ d _ _ _ _) = no-leaf (r-inner r) d
    where
    r-inner : ∀ {R′ Θ′ c′} → Reach (R′ ⟪ Θ′ , c′ ⟫) → Reach R′
    r-inner (r-⟪⟫ r′) = r′
  no-S oz eκ eA r (⟪⟫⊑ _ _ _ _ _ _ d _ _) = no-leaf r d

  B : Term
  B = sealed m ⟪ Θ₀ , unseal 0 ⟫

  data LO : Term → Set where
    lo-B : LO B
    lo-c : ∀ {M c} → GCast c → LO M → LO (M ⟨ [] ∣ c ⟩)

  lo-ty : ∀ {Γ M A} → LO M → Δ₀ ∣ Γ ⊢ M ⦂ A → G A
  lo-ty lo-B ⊢M with ⟪⟫-inv ⊢M
  ... | _ , _ , _ , b = proj₁ (proj₂ (bdy b))
  lo-ty (lo-c gc _) ⊢M with ty-cast ⊢M
  ... | refl = gc-trg gc

  -- OUTSIDE: the left under its ground casts
  no-LO : ∀ {Δ₂} {V : World Δ₀ Δ₂} {γ M R O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → LO M → Reach R
    → ¬ (V ∣ γ ⊢ M ⊑ R ∶⟨ A , A′ ⟩[ O ] q)
  no-LO {V = V} {O = O} eκ lo r-tag
    (⊑cast {A = A} {B′ = B′} {p = p} d ct _) with ct-X! ct
  ... | _ , refl , refl with lo-ty lo (ltyD d)
  ... | g = no-G⊑varᵖ g (plain-idx {V = V} {O = O} {A = A} {A′ = B′}
                           (G-nf g) p)
  no-LO eκ lo (r-cast _ r) (⊑cast d _ _) = no-LO eκ lo r d
  no-LO eκ (lo-c gc lo) r-tag (cast⊑cast {p = p} d ct ct′ _)
    with ct-X! ct′
  ... | _ , refl , refl = no-G⊑varᵖ (gsrc gc ct) p
  no-LO eκ (lo-c gc lo) (r-cast _ r) (cast⊑cast d _ _ _) = no-LO eκ lo r d
  no-LO eκ (lo-c gc lo) r (cast⊑ co-plain d _ _) = no-LO eκ lo r d
  no-LO {V = V} eκ lo (r-⟪⟫ r)
    (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A = A} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} I pu _ _ ks _ pay
      d b _) =
    no-LO (κ-keep I (K-none no ks) eκ) lo r d
    where
    no : ∀ {β} → ¬ JoinRep Vi [] _ _ β
    no (jr-join tv _ _ _) = no-tvs tv
    no (jr-open n _) = push-∋ᵒ pu n
      (nfO {O = Oᵢ} (G-nf (lo-ty lo (ltyD d))) pay)
  no-LO {V = V} eκ lo-B r
    (⟪⟫⊑ {Wᵢ = Vi} {K = K} {A′ = A′} {O = O} I _ _ ks _ pay d b _)
    with bdy b | reach-G r (rtyD d)
  ... | refl , _ , oz | g with nfO {O = O} nf-var pay
  ... | refl with g
  ...   | gℕ with pay
  ...     | ()
  no-LO {V = V} eκ lo-B r
    (⟪⟫⊑ {Wᵢ = Vi} {K = K} {A′ = A′} {O = O} I _ _ ks _ pay d b _)
    | refl , _ , oz | g | refl | g★ =
    no-S oz (κ-keep I (K-pay oz (trans (same-κ I) eκ) pay ks) eκ) refl r d
  no-LO {V = V} eκ lo-B (r-⟪⟫ r)
    (⟪⟫⊑⟪⟫ {Wᵢ = Vi} {K = K} I ks _ pay d b b′ _ _)
    with bdy b | bdy-id★ b′
  ... | refl , _ , oz | refl , _ =
    no-S oz (κ-keep I (K-pay oz (trans (same-κ I) eκ) pay ks) eκ) refl r d

------------------------------------------------------------------------
-- 5. C1 = the SimBackBlame counterexample L₆ ⊑ R₇ (PendingOpenings
-- §5d): NOT DERIVABLE in any world over its contexts with no
-- permission, at any slots.  All three routes of HiddenNames §2
-- (matched, left-first, right-first) end at the right's tag against
-- the left's sealed value: every boundary that could join the left's X
-- pays with `X ⊑ ★` at κ = [], so X stays left-only (`K-pay`), and the
-- right's tag `X!` then needs `X ⊑ X′` (`no-tag★`).  On the right-first
-- route the right's `+X` joins nothing (the left has no type variable
-- there), so it cannot permit (design.md D31: "joins, not introduces").
------------------------------------------------------------------------

module C1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)
  open Runs
  open P4 using (nth)

  5★ : Term
  5★ = $ 5 ⟨ [] ∣ `ℕ ! ⟩

  ℕ? : Coercion
  ℕ? = `ℕ ？ 0

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  S : Term
  S = 5★ ⟪ unb₀ , tail (seal 0) ⟫

  LB Lid L₆ RX RB R₇ : Term
  LB  = S ⟪ Θ₀ , unseal 0 ⟫
  Lid = LB ⟨ [] ∣ idᵖ ★ ⟩
  L₆  = Lid ⟨ [] ∣ ℕ? ⟩
  RX  = S ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩
  RB  = RX ⟪ Θ₀ , ⌞ id ★ ⌟ ⟫
  R₇  = RB ⟨ [] ∣ ℕ? ⟩

  --   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  --   R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
  L₀ R₀ : Term
  L₀ = ((Λ (ƛ (` 0) ∙ ` 0) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !)) ⟩)
          · 5★) ⟨ [] ∣ ℕ? ⟩
  R₀ = ((Λ (ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩))
          ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
  L₀-⊢ = tc

  R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ `ℕ
  R₀-⊢ = tc

  L₆-state : nth (evalTerms 30 L₀-⊢) 6 ≡ L₆
  L₆-state = refl

  R₇-state : nth (evalTerms 30 R₀-⊢) 7 ≡ R₇
  R₇-state = refl

  ΔR ΔRᵢ : Ctxᵗ
  ΔR  = allocate ★ empty
  ΔRᵢ = (bindR ★ ∷ []) ∣ (0 ∷ [])

  L₆-⊢ : ΔR ∣ [] ⊢ L₆ ⦂ `ℕ
  L₆-⊢ = tc

  R₇-⊢ : ΔR ∣ [] ⊢ R₇ ⦂ `ℕ
  R₇-⊢ = tc

  R₇-blames : ΔR ⊢ R₇ -→ blame 0 ∣ none
  R₇-blames = justStep refl

  L₆-never-blames : ∀ {ℓ} → ¬ (ΔR ⊢ L₆ -→* blame ℓ)
  L₆-never-blames r = all-reach {P = NotBlame} 20 L₆-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bdy-LB : ∀ {Δᵢ Aᵢ A} → BdyTy ΔR Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Aᵢ ≡ ` 0) × G A × OnlyZero Δᵢ
  bdy-LB (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-★))
                 (_ , same-var here , same-var here)
                 (_ , same-★ , same-★) _) | refl | refl =
    refl , g★ , oz₀ {★}

  open Spine 5★ no-n★ ΔR (λ { (_ , ()) }) bdy-LB

  -- C1 IS UNRELATED: every world over (ΔR, ΔR) with no permission, any
  -- slots; all routes (matched, left first, right first)
  c1-unrelated : ∀ {W : World ΔR ΔR} {γ A A′ O} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₆ ⊑ R₇ ∶⟨ A , A′ ⟩[ O ] q)
  c1-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-id★ lo-B)) (r-cast gc-ℕ? (r-⟪⟫ r-tag))

------------------------------------------------------------------------
-- 6. C3 = ModeCondition's `Esc.esc-cex-early` (both after TyBeta):
-- NOT DERIVABLE.  Matched boundaries compare `−X → +X` with
-- `−X → id(★)`: the seal joins X, so the ★ clause `+X ⊑ id(★)` needs X
-- permitted in the EXTERIOR conversion world (R2, unchanged by D31);
-- each one-sided order meets `X ⊑ ℕ` or `ℕ ⊑ X`.
------------------------------------------------------------------------

module C3 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open TIE using (idX; revX; ΔL)
  open Rebase using (I★⁻)

  genE genE-body : Coercion
  genE-body = ((` 0) !) ↦ᵖ idᵖ ★
  genE      = genᵖ genE-body

  cE : Conv
  cE = tail (mid (tail (seal 0) ↦ ⌞ id ★ ⌟))

  --  LE = ((ν X:=ℕ. ((ΛY. λx:Y. x) X) ⟨−X → +X⟩) 5)⟨ℕ!⟩⟨ℕ?ℓ0⟩
  --  RE = ((ν X:=ℕ. ((λx:★. x)⟨gen Y. (Y! → id(★))⟩ X) ⟨−X → id(★)⟩) 5)⟨ℕ?ℓ0⟩
  LE RE : Term
  LE = (((ν `ℕ · Λ idX ⟨ revX ⟩) · $ 5) ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE = ((ν `ℕ · (I★ ⟨ [] ∣ genE ⟩) ⟨ cE ⟩) · $ 5) ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE-⊢ : empty ∣ [] ⊢ LE ⦂ `ℕ
  LE-⊢ = tc

  RE-⊢ : empty ∣ [] ⊢ RE ⦂ `ℕ
  RE-⊢ = tc

  LB₁ RB₁ LA RA LE₁ RE₁ : Term
  LB₁ = idX ⟪ Θ₀ , revX ⟫
  RB₁ = (I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩) ⟪ Θ₀ , cE ⟫
  LA  = LB₁ · $ 5
  RA  = RB₁ · $ 5
  LE₁ = (LA ⟨ [] ∣ `ℕ ! ⟩) ⟨ [] ∣ `ℕ ？ 0 ⟩
  RE₁ = RA ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₁-state : nth (evalTerms 20 LE-⊢) 1 ≡ LE₁
  LE₁-state = refl

  RE₁-state : nth (evalTerms 30 RE-⊢) 1 ≡ RE₁
  RE₁-state = refl

  LE₁-⊢ : ΔL ∣ [] ⊢ LE₁ ⦂ `ℕ
  LE₁-⊢ = tc

  RE₁-⊢ : ΔL ∣ [] ⊢ RE₁ ⦂ `ℕ
  RE₁-⊢ = tc

  RE₁-blames : last (evalTerms 20 RE₁-⊢) ≡ blame 0
  RE₁-blames = refl

  LE₁-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₁ -→* blame ℓ)
  LE₁-never-blames r = all-reach {P = NotBlame} 20 LE₁-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  -- the matched conversions `−X → +X` ⊑ `−X → id(★)`: the seal joins X;
  -- with no permission a joined X is X⊑X, so `+X ⊑ id(★)` fails
  matched-conv : ∀ {Δ₁ Δ₂} {W : World Δ₁ Δ₂} {Δᵢ Δ′ᵢ Aᵢ A′ᵢ A A′ Θ Θ′}
    → κʷ W ≡ []
    → (b : BdyTy Δ₁ Θ Δᵢ Aᵢ revX A) (b′ : BdyTy Δ₂ Θ′ Δ′ᵢ A′ᵢ cE A′)
    → ¬ BdyConversionImp W b b′
  matched-conv eκ (bdy-ty _ _ _ _ _)
    (bdy-ty _ (conv-tail (conv-mid (conv-fun
       (conv-tail (conv-seal (_ , _ , l , _))) _))) _ _ _)
    (Wᶜ , ci , conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
       (conv-tail⊑tail (conv-seal⊑seal j)) (conv-unseal⊑id★ h _)))) =
    no-tag★ {V = Wᶜ} (trans (conv-same-κ ci) eκ) l j h

  ct-genE-body : ∀ {Δ₀ μ B A} → CastTy Δ₀ μ genE-body B A → A ≡ ` 0 ⇒ ★
  ct-genE-body (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-genE-body (cast-ty (⊢fun (⊢tag-var _ _ _) (⊢id _ _)) _) = refl

  no-fun : ∀ {V : World ΔL ΔL} {γ A A′ B B′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → A ≡ `ℕ ⇒ B → A′ ≡ `ℕ ⇒ B′
    → ¬ (V ∣ γ ⊢ LB₁ ⊑ RB₁ ∶⟨ A , A′ ⟩ q)
  no-fun eκ _ _ (⟪⟫⊑⟪⟫ _ _ _ _ _ b b′ bc _) = matched-conv eκ b b′ bc
  no-fun eκ eA refl
    (⟪⟫⊑ {Wᵢ = Vi} {K = K} {Aᵢ = Aᵢ} {A′ = A′} {O = O} {r = r}
      _ _ _ _ _ _ d _ _)
    with ty-ƛ (ltyD d)
  ... | _ , refl , _
    with plain-idx {V = Vi +κ K} {O = O} {A = Aᵢ} {A′ = A′} nf-⇒ r
  ... | ⇒⊑⇒ () _
  no-fun eκ refl _
    (⊑⟪⟫ {Wᵢ = Vi} {K = K} {A = A} {A′ᵢ = A′ᵢ} {Oᵢ = Oᵢ} {r = r}
      _ _ _ _ _ _ _ d _ _)
    with ty-cast (rtyD d)
  ... | refl with plain-idx {V = Vi +κ K} {O = Oᵢ} {A = A} {A′ = A′ᵢ} nf-⇒ r
  ... | ⇒⊑⇒ () _

  no-app : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-app eκ (·⊑· f (κ⊑κ lit-$ _)) = no-fun eκ refl refl f

  no-LAℕ!-RA : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-LAℕ!-RA eκ (cast⊑ co-plain d _ _) = no-app eκ d

  no-LE₁-RA : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LE₁ ⊑ RA ∶⟨ A , A′ ⟩[ O ] q)
  no-LE₁-RA eκ (cast⊑ co-plain d _ _) = no-LAℕ!-RA eκ d

  no-LA-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  no-LA-RE₁ eκ (⊑cast d _ _) = no-app eκ d

  no-LAℕ!-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  no-LAℕ!-RE₁ eκ (cast⊑cast d _ _ _) = no-app eκ d
  no-LAℕ!-RE₁ eκ (⊑cast d _ _) = no-LAℕ!-RA eκ d
  no-LAℕ!-RE₁ eκ (cast⊑ co-plain d _ _) = no-LA-RE₁ eκ d

  -- C3 IS UNRELATED: every world over (ΔL, ΔL) with no permission, any
  -- slots
  c3-unrelated : ∀ {W : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₁ ⊑ RE₁ ∶⟨ A , A′ ⟩[ O ] q)
  c3-unrelated eκ (cast⊑cast d _ _ _) = no-LAℕ!-RA eκ d
  c3-unrelated eκ (⊑cast d _ _) = no-LE₁-RA eκ d
  c3-unrelated eκ (cast⊑ co-plain d _ _) = no-LAℕ!-RE₁ eκ d

------------------------------------------------------------------------
-- 6a. C2 = ModeCondition's `Esc.esc-cex` (the late pair, P4 B4's own
-- inner pair `S ⊑ J`): NOT DERIVABLE.  Its right spine reaches the tag
-- `X!` through `ℕ?`, `id(★)` and three `id(★)` boundaries, so every
-- payment reads `X ⊑ ★` (the spine argument, §4).  Its sources are
-- C3's (`C3.LE`, `C3.RE`, unrelated: ∀Y.Y→Y ⋢ ∀Y.Y→★).
------------------------------------------------------------------------

module C2 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open TIE using (ΔL; ΔLᵢ)
  open C3 using (LE; RE; LE-⊢; RE-⊢)

  unb₀ : Boundary
  unb₀ = unbind 0 0 ∷ []

  id★ᶜ : Conv
  id★ᶜ = ⌞ id ★ ⌟

  S₄ LB₄ Lℕ LE₃ RX J RU RI RB₅ RE₅ : Term
  S₄  = sealed ($ 5)
  LB₄ = S₄ ⟪ Θ₀ , unseal 0 ⟫
  Lℕ  = LB₄ ⟨ [] ∣ `ℕ ! ⟩
  LE₃ = Lℕ ⟨ [] ∣ `ℕ ？ 0 ⟩
  RX  = S₄ ⟨ X∼★ ∷ [] ∣ (` 0) ! ⟩
  J   = RX ⟪ Θ₀ , id★ᶜ ⟫
  RU  = J ⟪ unb₀ , id★ᶜ ⟫
  RI  = RU ⟨ ★∼X ∷ [] ∣ idᵖ ★ ⟩
  RB₅ = RI ⟪ Θ₀ , id★ᶜ ⟫
  RE₅ = RB₅ ⟨ [] ∣ `ℕ ？ 0 ⟩

  LE₃-state : nth (evalTerms 20 LE-⊢) 3 ≡ LE₃
  LE₃-state = refl

  RE₅-state : nth (evalTerms 30 RE-⊢) 5 ≡ RE₅
  RE₅-state = refl

  -- J is P4 B4's J verbatim
  J-is-P4 : J ≡ P4.J
  J-is-P4 = refl

  LE₃-⊢ : ΔL ∣ [] ⊢ LE₃ ⦂ `ℕ
  LE₃-⊢ = tc

  RE₅-⊢ : ΔL ∣ [] ⊢ RE₅ ⦂ `ℕ
  RE₅-⊢ = tc

  RE₅-blames : last (evalTerms 20 RE₅-⊢) ≡ blame 0
  RE₅-blames = refl

  LE₃-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ LE₃ -→* blame ℓ)
  LE₃-never-blames r = all-reach {P = NotBlame} 20 LE₃-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bdy-LB₄ : ∀ {Δᵢ Aᵢ A} → BdyTy ΔL Θ₀ Δᵢ Aᵢ (unseal 0) A
    → (Aᵢ ≡ ` 0) × G A × OnlyZero Δᵢ
  bdy-LB₄ (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB₄ (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-ℕ))
                  (_ , same-var here , same-var here)
                  (_ , same-ℕ , same-ℕ) _) | refl | refl =
    refl , gℕ , oz₀ {`ℕ}

  open Spine ($ 5) no-$ ΔL (λ { (_ , ()) }) bdy-LB₄

  -- C2 IS UNRELATED: every world over (ΔL, ΔL) with no permission, any
  -- slots
  c2-unrelated : ∀ {W : World ΔL ΔL} {γ A A′ O} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₃ ⊑ RE₅ ∶⟨ A , A′ ⟩[ O ] q)
  c2-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-ℕ! lo-B))
      (r-cast gc-ℕ? (r-⟪⟫ (r-cast gc-id★ (r-⟪⟫ (r-⟪⟫ r-tag)))))

------------------------------------------------------------------------
-- 6b. THE WALK for C4, C4g and the hunt's gen-valued C4 (design.md D31).
-- The left has not instantiated; the right's Inst boundary
-- `[+X^α] Bd ⟨−X → id(★)⟩` holds a body of type X → ★.  Whatever the
-- left offers it (λx:X.x, ΛX.λx:X.x, the inst cast, or the gen value
-- λx:★.x⟨gen X.(X! → X?)⟩), possibly OPENED at X and PERMITTING α, or
-- skipped, the boundary's payment reads that left type against X → ★ at
-- κ = [] (`pay-RBd`): the codomain needs X ⊑ ★ at a type variable the
-- right sees (or the domain fails).  Claim-rep and joins keep κ.
------------------------------------------------------------------------

instL : Coercion
instL = instᵖ (((` 0) ？ 0) ↦ᵖ ((` 0) !))

genL : Coercion
genL = genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0))

data LeftT : Term → Set where
  l-id  : LeftT idX′
  l-Λ   : LeftT (Λ idX′)
  l-F   : LeftT (Λ idX′ ⟨ [] ∣ instL ⟩)
  -- the gen-valued left (the hunt): ((λx:★.x : ∀X.X→X) : ★→★)
  l-I★  : LeftT (ƛ ★ ∙ ` 0)
  l-g   : LeftT ((ƛ ★ ∙ ` 0) ⟨ [] ∣ genL ⟩)
  l-gF  : LeftT (((ƛ ★ ∙ ` 0) ⟨ [] ∣ genL ⟩) ⟨ [] ∣ instL ⟩)

-- ∀X.X→X against X′→★, opened, skipped or not, at κ = []
pay-∀ : ∀ {Δᵢ Δ′ᵢ} {Vᵢ : World Δᵢ Δ′ᵢ} {Oᵢ k β}
  → κʷ Vᵢ ≡ [] → All (SlotOK Vᵢ) Oᵢ → Δ′ᵢ ∋ᵗ k := β
  → ¬ (`∀ (` 0 ⇒ ` 0) ⊑ᵂ⟨ Vᵢ ⟩[ Oᵢ ] (` k ⇒ ★))
pay-∀ {Oᵢ = []} eκ so rh (∀⊑ _ _ (⇒⊑⇒ p₁ _)) with var⊑var p₁
... | ()
pay-∀ {Vᵢ = Vᵢ} {Oᵢ = opn j ∷ []} eκ ((β , rj , _) ∷ []) rh (⇒⊑⇒ _ p₂) =
  no★-right {V = Vᵢ} eκ rj (var⊑★ p₂)
pay-∀ {Oᵢ = skp ∷ []} eκ so rh (_ , _ , ⇒⊑⇒ p₁ _) with var⊑var p₁
... | ()
pay-∀ {Oᵢ = opn _ ∷ opn _ ∷ _} eκ so rh ()
pay-∀ {Oᵢ = opn _ ∷ skp ∷ _} eκ so rh ()
pay-∀ {Oᵢ = skp ∷ opn _ ∷ _} eκ so rh (_ , _ , ())
pay-∀ {Oᵢ = skp ∷ skp ∷ _} eκ so rh (_ , _ , ())

-- ★→★ against X′→★: ★ ⊑ X′
pay-★ : ∀ {Δᵢ Δ′ᵢ} {Vᵢ : World Δᵢ Δ′ᵢ} {Oᵢ k}
  → ¬ ((★ ⇒ ★) ⊑ᵂ⟨ Vᵢ ⟩[ Oᵢ ] (` k ⇒ ★))
pay-★ {Vᵢ = Vᵢ} {Oᵢ} {k} pay
  with plain-idx {V = Vᵢ} {O = Oᵢ} {A = ★ ⇒ ★} {A′ = ` k ⇒ ★} nf-⇒ pay
... | ⇒⊑⇒ () _

-- the payment at the right's Inst boundary is impossible
pay-RBd : ∀ {Δᵢ Δ′ᵢ} {Vᵢ : World Δᵢ Δ′ᵢ} {Oᵢ M A k β}
  → κʷ Vᵢ ≡ [] → All (SlotOK Vᵢ) Oᵢ → LeftT M → Δᵢ ∣ [] ⊢ M ⦂ A
  → Δ′ᵢ ∋ᵗ k := β → ¬ (A ⊑ᵂ⟨ Vᵢ ⟩[ Oᵢ ] (` k ⇒ ★))
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} eκ so l-id (⊢ƛ _ (⊢` here)) rh pay
  with plain-idx {V = Vᵢ} {O = Oᵢ} {A = ` 0 ⇒ ` 0} nf-⇒ pay
... | ⇒⊑⇒ p₁ p₂ = no-tag★ {V = Vᵢ} eκ rh (var⊑var p₁) (var⊑★ p₂)
pay-RBd eκ so l-Λ (⊢Λ _ (⊢ƛ _ (⊢` here))) rh pay = pay-∀ eκ so rh pay
pay-RBd eκ so l-g ⊢g rh pay with ty-cast ⊢g
... | refl = pay-∀ eκ so rh pay
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} {k = k} eκ so l-F ⊢F rh pay with ty-cast ⊢F
... | refl = pay-★ {Vᵢ = Vᵢ} {Oᵢ = Oᵢ} {k = k} pay
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} {k = k} eκ so l-gF ⊢F rh pay with ty-cast ⊢F
... | refl = pay-★ {Vᵢ = Vᵢ} {Oᵢ = Oᵢ} {k = k} pay
pay-RBd {Vᵢ = Vᵢ} {Oᵢ} {k = k} eκ so l-I★ (⊢ƛ _ (⊢` here)) rh pay =
  pay-★ {Vᵢ = Vᵢ} {Oᵢ = Oᵢ} {k = k} pay

bind-κ : ∀ {W : World Δ Δ′} {W₁ O O₁} → Bind W O W₁ O₁ → κʷ W₁ ≡ κʷ W
bind-κ b-fresh                = refl
bind-κ (b-join (join1 _ _ _)) = refl
bind-κ (b-rep _ _ _)          = refl

-- the left function: ΛX.λx:X.x (C4, C4g) or the gen value (the hunt)
data LeftF : Term → Term → Set where
  lf-Λ : LeftF (Λ idX′) (Λ idX′ ⟨ [] ∣ instL ⟩)
  lf-g : LeftF ((ƛ ★ ∙ ` 0) ⟨ [] ∣ genL ⟩)
               (((ƛ ★ ∙ ` 0) ⟨ [] ∣ genL ⟩) ⟨ [] ∣ instL ⟩)

lf-v : ∀ {Lv F} → LeftF Lv F → LeftT Lv
lf-v lf-Λ = l-Λ
lf-v lf-g = l-g

lf-F : ∀ {Lv F} → LeftF Lv F → LeftT F
lf-F lf-Λ = l-F
lf-F lf-g = l-gF

module PopWalk (Bd : Term)
  (bd-ty : ∀ {Δ′ Γ A′} → Δ′ ∣ Γ ⊢ Bd ⦂ A′
     → Σ[ k ∈ ℕ ] (A′ ≡ ` k ⇒ ★) × (Δ′ ∋tv k))
  where

  RBd GR : Term
  RBd = Bd ⟪ Θ₀ , C3.cE ⟫
  GR  = RBd ⟨ [] ∣ Rebase.id★↦ ⟩

  w-RB : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ M O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → LeftT M → ¬ (V ∣ γ ⊢ M ⊑ RBd ∶⟨ A , A′ ⟩[ O ] q)
  w-RB {V = V} eκ l (⊑⟪⟫ I _ so _ _ _ pay d _ _)
    with bd-ty (rtyD d)
  ... | k , refl , (β , rh) =
    pay-RBd (trans (same-κ I) eκ) so l (ltyD d) rh pay
  w-RB eκ l-Λ (Λ⊑ bd _ _ _ _ d _) = w-RB (trans (bind-κ bd) eκ) l-id d
  w-RB eκ l-F (cast⊑ co-plain d _ _) = w-RB eκ l-Λ d
  w-RB eκ l-gF (cast⊑ co-plain d _ _) = w-RB eκ l-g d
  w-RB eκ l-g (cast⊑ co-plain d _ _) = w-RB eκ l-I★ d
  w-RB eκ l-g (cast⊑ (co-gen _ co-plain) d _ _) = w-RB eκ l-I★ d

  w-GR : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ M O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → LeftT M → ¬ (V ∣ γ ⊢ M ⊑ GR ∶⟨ A , A′ ⟩[ O ] q)
  w-GR eκ l (⊑cast d _ _) = w-RB eκ l d
  w-GR eκ l-Λ (Λ⊑ bd _ _ _ _ d _) = w-GR (trans (bind-κ bd) eκ) l-id d
  w-GR eκ l-F (cast⊑ co-plain d _ _) = w-GR eκ l-Λ d
  w-GR eκ l-F (cast⊑cast d _ _ _) = w-RB eκ l-Λ d
  w-GR eκ l-gF (cast⊑ co-plain d _ _) = w-GR eκ l-g d
  w-GR eκ l-gF (cast⊑cast d _ _ _) = w-RB eκ l-g d
  w-GR eκ l-g (cast⊑ co-plain d _ _) = w-GR eκ l-I★ d
  w-GR eκ l-g (cast⊑ (co-gen _ co-plain) d _ _) = w-GR eκ l-I★ d
  w-GR eκ l-g (cast⊑cast d _ _ _) = w-RB eκ l-I★ d

  module _ {Lv F : Term} (lf : LeftF Lv F) where
    w-app : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ F · C1.5★ ⊑ GR · C1.5★ ∶⟨ A , A′ ⟩[ O ] q)
    w-app eκ (·⊑· f _) = w-GR eκ (lf-F lf) f

    w-L-app : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′}
        {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ (F · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩ ⊑ GR · C1.5★
             ∶⟨ A , A′ ⟩[ O ] q)
    w-L-app eκ (cast⊑ co-plain d _ _) = w-app eκ d

    w-app-R : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′}
        {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ F · C1.5★ ⊑ (GR · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩
             ∶⟨ A , A′ ⟩[ O ] q)
    w-app-R eκ (⊑cast d _ _) = w-app eκ d

    -- THE WALK: the initial-shaped pair is unrelated with no permission
    walk : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
      → κʷ V ≡ []
      → ¬ (V ∣ γ ⊢ (F · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩
             ⊑ (GR · C1.5★) ⟨ [] ∣ C1.ℕ? ⟩ ∶⟨ A , A′ ⟩[ O ] q)
    walk eκ (cast⊑cast d _ _ _) = w-app eκ d
    walk eκ (⊑cast d _ _) = w-L-app eκ d
    walk eκ (cast⊑ co-plain d _ _) = w-app-R eκ d

------------------------------------------------------------------------
-- 6c. C4 (HiddenNames §5; PushTypePremise §3): NOT DERIVABLE, also with
-- claim-rep (design.md D29), D31's openings and its permissions.  At
-- the right's Inst boundary (body type `X→★`) the payment reads the
-- left's `X→X`, `∀X.X→X` (opened, skipped or not) or `★→★` against
-- `X→★` at κ = [].
--
-- Source programs (UNRELATED: ∀X.X→X ⋢ ∀X.X→★, `source-unrelated`):
--   L:  ((ΛX. λx:X. x)         : ★→★) 5 : ℕ
--   R:  ((ΛX. λx:X. (x : ★))   : ★→★) 5 : ℕ
-- Initial cast terms (C1.L₀, C1.R₀, rendered):
--   L₀  ((ΛX. λx:X. x)⟨inst Y.(Y?ℓ0 → Y!)⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
--   R₀  ((ΛX. λx:X. x⟨X!⟩)⟨inst Y.(Y?ℓ0 → id(★))⟩ 5⟨ℕ!⟩)⟨ℕ?ℓ0⟩
-- The pair is (L₀, R₂), R₂ the right's state 2 (after Inst, TyBeta);
-- the right blames, the left reaches 5.
------------------------------------------------------------------------

module C4 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open C1 using (5★; ℕ?; L₀; R₀; L₀-⊢; R₀-⊢; ΔR; ΔRᵢ)
  open Rebase using (id★↦)

  source-unrelated : ∀ {μ} → ¬ (μ ⊢ `∀ (` 0 ⇒ ` 0) ⊑ `∀ (` 0 ⇒ ★))
  source-unrelated (∀⊑∀ (⇒⊑⇒ _ (X⊑★ ())))
  source-unrelated (∀⊑ _ _ ())

  bodyR : Term
  bodyR = ƛ (` 0) ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ! ⟩)

  RBp R₂ : Term
  RBp = bodyR ⟪ Θ₀ , C3.cE ⟫
  R₂  = ((RBp ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  R₂-state : nth (evalTerms 30 R₀-⊢) 2 ≡ R₂
  R₂-state = refl

  R₂-⊢ : ΔR ∣ [] ⊢ R₂ ⦂ `ℕ
  R₂-⊢ = tc

  R₂-blames : last (evalTerms 20 R₂-⊢) ≡ blame 0
  R₂-blames = refl

  L₀-never-blames : ∀ {ℓ} → ¬ (empty ⊢ L₀ -→* blame ℓ)
  L₀-never-blames r = all-reach {P = NotBlame} 30 L₀-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  bd-ty : ∀ {Δ′ Γ A′} → Δ′ ∣ Γ ⊢ bodyR ⦂ A′
    → Σ[ k ∈ ℕ ] (A′ ≡ ` k ⇒ ★) × (Δ′ ∋tv k)
  bd-ty (⊢ƛ (wf-var tv) ⊢b) with ty-cast ⊢b
  ... | refl = 0 , refl , tv

  open PopWalk bodyR bd-ty

  -- C4 IS UNRELATED: every world over (empty, ΔR) with no permission,
  -- any slots
  c4-unrelated : ∀ {W : World empty ΔR} {γ A A′ O} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₀ ⊑ R₂ ∶⟨ A , A′ ⟩[ O ] q)
  c4-unrelated = walk lf-Λ

------------------------------------------------------------------------
-- 6d. C4g (HiddenNames §19, C4 with a gen-mode tag): NOT DERIVABLE,
-- also with claim-rep and D31.  The right's body is the gen wrapper
-- `(…)⟨X! → id(★)⟩^[X:★∼X]`, of type X → ★; the walk applies.
--
-- Source programs (UNRELATED, again ∀X.X→X ⋢ ∀X.X→★):
--   L:  ((ΛX. λx:X. x)                              : ★→★) 5 : ℕ
--   R:  (((λx:★. x) : ∀X.X→★  by gen X.(X! → id★)) : ★→★) 5 : ℕ
-- The pair is (C1.L₀, R2g), R2g the right's state 2.
------------------------------------------------------------------------

module C4g where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (I★)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth)
  open C1 using (5★; ℕ?; L₀; L₀-⊢; ΔR)
  open C3 using (genE; genE-body; cE; RB₁)
  open C4 using (L₀-never-blames; source-unrelated)
  open Rebase using (id★↦; I★⁻)

  R0g R2g Bdg : Term
  R0g = (((I★ ⟨ [] ∣ genE ⟩) ⟨ [] ∣ instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★) ⟩)
          · 5★) ⟨ [] ∣ ℕ? ⟩
  R2g = ((RB₁ ⟨ [] ∣ id★↦ ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩
  Bdg = I★⁻ ⟨ ★∼X ∷ [] ∣ genE-body ⟩

  R0g-⊢ : empty ∣ [] ⊢ R0g ⦂ `ℕ
  R0g-⊢ = tc

  R2g-state : nth (evalTerms 30 R0g-⊢) 2 ≡ R2g
  R2g-state = refl

  R2g-⊢ : ΔR ∣ [] ⊢ R2g ⦂ `ℕ
  R2g-⊢ = tc

  R2g-blames : last (evalTerms 30 R2g-⊢) ≡ blame 0
  R2g-blames = refl

  ct-genE′ : ∀ {Δ₀ μ B A} → CastTy Δ₀ μ genE-body B A
    → (Δ₀ ∋tv 0) × (A ≡ ` 0 ⇒ ★)
  ct-genE′ (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-genE′ (cast-ty (⊢fun (⊢tag-var tv _ _) (⊢id _ _)) _) = tv , refl

  bd-ty : ∀ {Δ′ Γ A′} → Δ′ ∣ Γ ⊢ Bdg ⦂ A′
    → Σ[ k ∈ ℕ ] (A′ ≡ ` k ⇒ ★) × (Δ′ ∋tv k)
  bd-ty (⊢cast _ ⊢p len) with ct-genE′ (cast-ty ⊢p len)
  ... | tv , refl = 0 , refl , tv

  open PopWalk Bdg bd-ty

  -- C4g IS UNRELATED: every world over (empty, ΔR) with no permission,
  -- any slots
  c4g-unrelated : ∀ {W : World empty ΔR} {γ A A′ O}
      {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₀ ⊑ R2g ∶⟨ A , A′ ⟩[ O ] q)
  c4g-unrelated = walk lf-Λ

------------------------------------------------------------------------
-- 6e. THE HUNT (D28pD30.md §6).  A gen-VALUED left against C4's right
-- exercises every new freedom of design.md D31 at once: ⊑⟪⟫ may OPEN the
-- left's ∀ at the right's Inst type variable X and PERMIT α, the left's
-- gen layer may CONSUME the opening (cast⊑, no world change), and the
-- left may SKIP (it is a gen-cast value).  Sources UNRELATED
-- (∀X.X→X ⋢ ∀X.X→★, `C4.source-unrelated`):
--   L:  ((λx:★. x : ∀X.X→X) : ★→★) 5 : ℕ          (gen, then inst)
--   R:  ((ΛX. λx:X. (x : ★))  : ★→★) 5 : ℕ        (C4's right)
-- The left answers 5; the right blames (`C4.R₂-blames`).  The left's
-- initial term against the right's state 2 is NOT related (`walk lf-g`).
------------------------------------------------------------------------

module Hunt where
  open import examples.TypeCheck using (tc)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs using (all-reach; NotBlame; last)
  open C4 using (bodyR; R₂; R₂-blames; source-unrelated; bd-ty)
  open C1 using (5★; ℕ?; ΔR)

  Lg₀ : Term
  Lg₀ = ((((ƛ ★ ∙ ` 0) ⟨ [] ∣ genL ⟩) ⟨ [] ∣ instL ⟩) · 5★) ⟨ [] ∣ ℕ? ⟩

  Lg₀-⊢ : empty ∣ [] ⊢ Lg₀ ⦂ `ℕ
  Lg₀-⊢ = tc

  -- the left answers 5 and never blames
  Lg₀-answers : last (evalTerms 30 Lg₀-⊢) ≡ $ 5
  Lg₀-answers = refl

  Lg₀-never-blames : ∀ {ℓ} → ¬ (empty ⊢ Lg₀ -→* blame ℓ)
  Lg₀-never-blames r = all-reach {P = NotBlame} 30 Lg₀-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷
     (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  open PopWalk bodyR bd-ty

  -- NOT DERIVABLE: every world over (empty, ΔR) with no permission, any
  -- slots
  c4gen-unrelated : ∀ {W : World empty ΔR} {γ A A′ O}
      {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ Lg₀ ⊑ R₂ ∶⟨ A , A′ ⟩[ O ] q)
  c4gen-unrelated = walk lf-g

------------------------------------------------------------------------
-- 7. C5 (Permissions.md §5), its programs and runs.  In Permissions'
-- relation the pair (L state 3, R state 5) is related through the
-- left's payload view `⟪⟫⊑` under a permission of the right's X
-- (`Permissions.C5.c5`).  HERE R1′ rejects that step (`r1-rejects-c5`:
-- the seal's exterior type is X, so R1′ is R1) and §7a proves the pair
-- unrelated in every world.
--
-- Source programs (unrelated: ∀Y.Y→Y ⋢ ∀Y.★→Y, the shared Y is X⊑X):
--   L  (ΛY. λx:Y. x) [ℕ] 5
--   R  (ΛY. λx:★. (x : Y)) [ℕ] (5 : ★)
------------------------------------------------------------------------

module C5 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open P4 using (nth; W₄; W₄²; W₄²-wf; W₄²¹; v₀; S; unb₀; bS; bUnsealL;
                 Ξ₄; ϱ₄; p0; module Wf₄)
  open TIE using (ΔL; ΔLᵢ)
  open Rebase using (Wc-bind²; Wc-bind²-conv; unbind₀-int)
  open C1 using (5★)

  -- the initial programs (cast terms); the left is P1's left
  L5 R5 : Term
  L5 = (ν `ℕ · Λ (ƛ (` 0) ∙ ` 0) ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5
  R5 = (ν `ℕ · Λ (ƛ ★ ∙ (` 0 ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩))
          ⟨ reveal 0 (★ ⇒ ` 0) ⟩) · 5★

  L5-⊢ : empty ∣ [] ⊢ L5 ⦂ `ℕ
  L5-⊢ = tc

  R5-⊢ : empty ∣ [] ⊢ R5 ⦂ `ℕ
  R5-⊢ = tc

  -- the related pair: left state 3, right state 5
  5★ˣ C5L C5R : Term
  5★ˣ = $ 5 ⟨ X∼X ∷ [] ∣ `ℕ ! ⟩
  C5L = S ⟪ Θ₀ , unseal 0 ⟫
  C5R = (5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩) ⟪ Θ₀ , unseal 0 ⟫

  C5L-state : nth (evalTerms 10 L5-⊢) 3 ≡ C5L
  C5L-state = refl

  C5R-state : nth (evalTerms 20 R5-⊢) 5 ≡ C5R
  C5R-state = refl

  C5L-⊢ : ΔL ∣ [] ⊢ C5L ⦂ `ℕ
  C5L-⊢ = tc

  C5R-⊢ : ΔL ∣ [] ⊢ C5R ⦂ `ℕ
  C5R-⊢ = tc

  C5R-blames : last (evalTerms 10 C5R-⊢) ≡ blame 0
  C5R-blames = refl

  C5L-never-blames : ∀ {ℓ} → ¬ (ΔL ⊢ C5L -→* blame ℓ)
  C5L-never-blames r = all-reach {P = NotBlame} 10 C5L-⊢ tt
    ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) r refl

  ℕ!ˣ-ty : CastTy ΔLᵢ (X∼X ∷ []) (`ℕ !) `ℕ ★
  ℕ!ˣ-ty = cast-ty (⊢tag g-ℕ) refl

  chk-ty : CastTy ΔLᵢ (★∼X∼★ ∷ []) ((` 0) ？ 0) ★ (` 0)
  chk-ty = cast-ty (⊢check-var (_ , here) here check-cross) refl

  bC5R : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ
  bC5R = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = C5R}))))

  -- the earlier pairs of the same runs are unrelated: before the Beta,
  -- λx:X. x faces λx:★. x⟨X?⟩ at X→X ⊑ ★→X, whose domain needs X⊑★ at
  -- the joined, unpermitted X (no check is around the λ)
  no-early-idx : ¬ ((` 0 ⇒ ` 0) ⊑ᵂ⟨ W₄² ⟩ (★ ⇒ ` 0))
  no-early-idx (⇒⊑⇒ (X⊑★ ()) _)


  -- R1′ REJECTS the step Permissions.C5.c5 used: the left's `−X^0`, of
  -- exterior type X, inside the matched boundary that permits αᴿ = 0,
  -- which is paired with αᴸ = 0
  r1-rejects-c5 : ¬ All (UnbindOK W₄²¹ (` 0)) unb₀
  r1-rejects-c5 (ok-hidden f ∷ []) with f here
  ... | ()
  r1-rejects-c5 (ok-unbind u ∷ []) with u (inj₁ here⇔)
  ... | ()

------------------------------------------------------------------------
-- 7a. C5 IS DEAD under R1′/R2: not derivable in ANY world over its
-- contexts, at any κ, at any slots.  Also its hidden variant (the
-- left's payload view inside the right's own hide
-- `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`), which needs R1′ after the right hide or R2
-- at the matched hides.
--
-- The argument: below the right's check `X?` the left's X is joined
-- and `X⊑★` in ONE world (no cast rule changes the world, design.md
-- D31), so its rep. var has a permitted partner (`hasPP-chk`).  The
-- left's seal `[−X^α] 5 ⟨−X⟩` has exterior type X, so R1′ is R1
-- (`r1′-fails`); the matched hides fail R2.  The routes that avoid the
-- check meet `ℕ ⊑ X` or `X ⊑ ℕ`.
------------------------------------------------------------------------

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

-- a joined pair of names has paired rep. vars (`wf-joint`)
joint-pair : ∀ {P : RVar → RVar → Set} {ns ns′ n} {ι : ns ↪ n}
    {ι′ : ns′ ↪ n} {X X′ α β}
  → Joint P ι ι′ → ns ∋ˡ X := α → ns′ ∋ˡ X′ := β
  → emb ι X ≡ emb ι′ X′ → P α β
joint-pair joint[]         ()       _          _
joint-pair (both p j)      here     here       e  = p
joint-pair (both p j)      here     (there h′) ()
joint-pair (both p j)      (there h) here      ()
joint-pair (both p j)      (there h) (there h′) e =
  joint-pair j h h′ (suc-inj e)
joint-pair (left-only j)   here     h′         ()
joint-pair (left-only j)   (there h) h′        e  =
  joint-pair j h h′ (suc-inj e)
joint-pair (right-only j)  h        here       ()
joint-pair (right-only j)  h        (there h′) e  =
  joint-pair j h h′ (suc-inj e)

-- the name and rep. var of a one-entry unbind, read off its interior or
-- its conversion context
del-lookup : ∀ {α Δ₀ X Δ₁} → α ⊢- Δ₀ at X ⇒ Δ₁ → Δ₀ ∋ˡ X := α
del-lookup del-here      = here
del-lookup (del-there d) = there (del-lookup d)

unb1-lookup : ∀ {Γ Γᵢ X α} → Γ ⊢ⁱ (unbind X α ∷ []) ⇒ Γᵢ → Γ ∋ᵗ X := α
unb1-lookup (interior (changes∷ changes[] (step-unbind _ d _))) =
  del-lookup d

unb1-conv : ∀ {Γ Γᶜ Y X α β} → Γ ⊢ᶜ (unbind X α ∷ []) ⇒ Γᶜ
  → Γ ∋ᵗ Y := β → Γᶜ ∋ᵗ Y := β
unb1-conv (conversion (conv-unbind _ conv[])) h = h

ct-X? : ∀ {μ X ℓ B A} → CastTy Δ μ ((` X) ？ ℓ) B A
  → (Δ ∋tv X) × (B ≡ ★) × (A ≡ ` X)
ct-X? (cast-ty (⊢check ()) _)
ct-X? (cast-ty (⊢check-var tv _ _) _) = tv , refl , refl

-- the outer +X boundary of C5's two sides (and of the hidden variant)
bdy-C5 : ∀ {Δᵢ Aᵢ A} → BdyTy TIE.ΔL Θ₀ Δᵢ Aᵢ (unseal 0) A
  → (Aᵢ ≡ ` 0) × (A ≡ `ℕ)
bdy-C5 (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
  with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
bdy-C5 (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-ℕ))
               (_ , same-var here , same-var here)
               (_ , same-ℕ , same-ℕ) _) | refl | refl =
  refl , refl

module C5Dead where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import Reduction using (_⊢_-→*_)
  open Runs
  open TIE using (ΔL; ΔLᵢ)
  open P4 using (S; unb₀; id★ᶜ)
  open C5 using (5★ˣ; C5L; C5R; C5L-⊢; C5L-never-blames)
  open C1 using (5★)

  HP0 : World Δ Δ′ → Set
  HP0 {Δ = Δ} U = ∀ {α} → Δ ∋ᵗ 0 := α → HasPermittedPartner U α

  -- THE CHECK FACT, in one world: `a ⊑ X′` and `a ⊑ ★`
  hasPP-chk : ∀ {V : World Δ Δ′} {a X′ α β}
    → WfWorld V → Δ ∋ᵗ a := α → Δ′ ∋ᵗ X′ := β
    → marksʷ V ⊢ embᴸ V (` a) ⊑ embᴿ V (` X′)
    → marksʷ V ⊢ embᴸ V (` a) ⊑ ★
    → HasPermittedPartner V α
  hasPP-chk {V = V} {a} {X′} {β = β} wf lh rh q p =
    β , joint-pair (wf-joint wf) lh rh j , sym (lookup-unique h′ hβ)
    where
    j : Joins V a X′
    j = var⊑var q
    h′ : marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := X⊑★
    h′ = subst (λ c → marksʷ V ∋ˡ c := X⊑★) j (var⊑★ p)
    hβ : marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := permit β (κʷ V)
    hβ = dmarks-emb (ηᴿʷ V) (κʷ V) rh

  no-$-chk : ∀ {V : World Δ Δ′} {γ n M′ μ′ X ℓ O A A′}
      {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ $ n ⊑ M′ ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  no-$-chk {V = V} {O = O} (⊑cast {A = A} {A′ = A′} d ct q)
    with ct-X? ct | ty-$ (ltyD d)
  ... | _ , refl , refl | refl
    with plain-idx {V = V} {O = O} {A = `ℕ} {A′ = A′} nf-ℕ q
  ... | ()

  -- the right cores under the check: C5's `5⟨ℕ!⟩` and the hidden
  -- variant's `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`
  data Core : Term → Set where
    c-5   : ∀ {n μ} → Core ($ n ⟨ μ ∣ `ℕ ! ⟩)
    c-hid : Core (5★ ⟪ unb₀ , id★ᶜ ⟫)

  -- R1′ at the left's seal: α occurs in its exterior type X
  r1′-fails : ∀ {U : World Δ Δ′} {α} → HasPermittedPartner U α
    → Δ ∋ᵗ 0 := α → ¬ UnbindOK U (` 0) (unbind 0 α)
  r1′-fails hp lh (ok-hidden f) with f lh
  ... | ()
  r1′-fails {U = U} hp lh (ok-unbind u) = r1-fails {W = U} hp u

  no-S-5 : ∀ {U : World Δ Δ′} {γ n μ O A A′} {q : A ⊑ᵂ⟨ U ⟩[ O ] A′}
    → A ≡ ` 0 → HP0 U
    → ¬ (U ∣ γ ⊢ S ⊑ $ n ⟨ μ ∣ `ℕ ! ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  no-S-5 {U = U} {O = O} refl hp (⊑cast {B′ = B′} {p = p} d ct _)
    with ct-ℕ! ct
  ... | refl , refl
    with plain-idx {V = U} {O = O} {A = ` 0} {A′ = `ℕ} nf-var p
  ... | ()
  no-S-5 refl hp (⟪⟫⊑ I (ok ∷ []) _ _ _ _ _ _ _) =
    r1′-fails (hp lh) lh ok
    where lh = unb1-lookup (int-left I)

  no-S-core : ∀ {U : World Δ Δ′} {γ Q O A A′} {q : A ⊑ᵂ⟨ U ⟩[ O ] A′}
    → Core Q → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ Q ∶⟨ A , A′ ⟩[ O ] q)
  no-S-core c-5 eA hp d = no-S-5 eA hp d
  no-S-core c-hid eA hp (⊑⟪⟫ {Wᵢ = Ui} {K = K} I _ _ _ _ _ _ d _ _) =
    no-S-5 eA (λ lh → hasPP-+κ {W = Ui} {K = K} (hasPP-int I (hp lh))) d
  no-S-core c-hid refl hp (⟪⟫⊑ I (ok ∷ []) _ _ _ _ _ _ _) =
    r1′-fails (hp lh) lh ok
    where lh = unb1-lookup (int-left I)
  no-S-core c-hid eA hp
    (⟪⟫⊑⟪⟫ I _ _ _ _ (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _)
      (Wᶜ , ci , conv-tail⊑tail (conv-seal⊑id★ _ lu)) _) =
    r1-fails {W = Wᶜ} (hasPP-conv ci (hp lh))
      (lu (unb1-conv (conv-left ci) lh))
    where lh = unb1-lookup (int-left I)

  -- S against a core under the right check `X?`
  no-S-chk : ∀ {V : World Δ Δ′} {γ Q μ′ X ℓ O A A′}
      {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → Core Q → WfWorld V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ Q ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  no-S-chk {V = V} {O = O} core wf refl
    (⊑cast {B′ = B′} {A′ = A′} {p = p} d ct q) with ct-X? ct
  ... | (_ , rh) , refl , refl =
    no-S-core core refl
      (λ lh → hasPP-chk {V = V} wf lh rh
        (plain-idx {V = V} {O = O} {A = ` 0} {A′ = A′} nf-var q)
        (plain-idx {V = V} {O = O} {A = ` 0} {A′ = ★} nf-var p))
      d
  no-S-chk core wf eA (⟪⟫⊑ _ _ _ _ _ _ d _ _) = no-$-chk d

  module Outer (Q : Term) (core : Core Q) where
    RinQ RQ : Term
    RinQ = Q ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩
    RQ   = RinQ ⟪ Θ₀ , unseal 0 ⟫

    no-S-RQ : ∀ {Δ₁} {V : World Δ₁ ΔL} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
      → A ≡ ` 0 → ¬ (V ∣ γ ⊢ S ⊑ RQ ∶⟨ A , A′ ⟩[ O ] q)
    no-S-RQ eA (⊑⟪⟫ _ _ _ _ _ wf _ d _ _) = no-S-chk core wf eA d
    no-S-RQ {V = V} {O = O} refl (⟪⟫⊑ {A′ = A′} _ _ _ _ _ _ d _ q)
      with ty-$ (ltyD d) | proj₂ (bdy-C5 (proj₂ (proj₂ (proj₂
             (⟪⟫-inv (rtyD d))))))
    ... | refl | refl
      with plain-idx {V = V} {O = O} {A = ` 0} {A′ = `ℕ} nf-var q
    ... | ()
    no-S-RQ eA (⟪⟫⊑⟪⟫ _ _ _ _ d _ _ _ _) = no-$-chk d

    no-L-RinQ : ∀ {Δ₂} {V : World ΔL Δ₂} {γ O A A′}
        {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
      → ¬ (V ∣ γ ⊢ C5L ⊑ RinQ ∶⟨ A , A′ ⟩[ O ] q)
    no-L-RinQ {V = V} {O = O} (⊑cast {A = A} d ct q) with ct-X? ct
      | ⟪⟫-inv (ltyD d)
    ... | _ , refl , refl | _ , _ , _ , b with bdy-C5 b
    ... | _ , refl
      with plain-idx {V = V} {O = O} {A = `ℕ} {A′ = ` 0} nf-ℕ q
    ... | ()
    no-L-RinQ (⟪⟫⊑ _ _ _ _ wf _ d b _) =
      no-S-chk core wf (proj₁ (bdy-C5 b)) d

    -- THE TOP: every world over (ΔL, ΔL), ANY κ, any slots
    no-top : ∀ {W : World ΔL ΔL} {γ O A A′} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
      → ¬ (W ∣ γ ⊢ C5L ⊑ RQ ∶⟨ A , A′ ⟩[ O ] q)
    no-top (⟪⟫⊑⟪⟫ _ _ wf _ d b _ _ _) =
      no-S-chk core wf (proj₁ (bdy-C5 b)) d
    no-top (⟪⟫⊑ _ _ _ _ _ _ d b _)    = no-S-RQ (proj₁ (bdy-C5 b)) d
    no-top (⊑⟪⟫ _ _ _ _ _ _ _ d _ _)  = no-L-RinQ d

  -- C5 IS UNRELATED (L state 3, R state 5), in every world, at any κ
  C5R-is : C5R ≡ Outer.RQ (5★ˣ) c-5
  C5R-is = refl

  c5-unrelated : ∀ {W : World ΔL ΔL} {γ O A A′} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ C5R ∶⟨ A , A′ ⟩[ O ] q)
  c5-unrelated = Outer.no-top 5★ˣ c-5

  -- the failing redex `5⟨ℕ!⟩⟨X?⟩` against the left VALUE S (M26's shape)
  -- is unrelated in every well-formed world, at any κ
  c5-redex-unrelated : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ O A A′}
      {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → WfWorld V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ 5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩ ∶⟨ A , A′ ⟩[ O ] q)
  c5-redex-unrelated = no-S-chk c-5

  -- THE HIDDEN VARIANT: right `[+X^α] (([−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩)⟨X?ℓ0⟩) ⟨+X⟩`
  -- against C5L = `[+X^α] ([−X^α] 5 ⟨−X⟩) ⟨+X⟩`
  Hid RH : Term
  Hid = 5★ ⟪ unb₀ , id★ᶜ ⟫
  RH  = Outer.RQ Hid c-hid

  RH-⊢ : ΔL ∣ [] ⊢ RH ⦂ `ℕ
  RH-⊢ = tc

  RH-blames : last (evalTerms 10 RH-⊢) ≡ blame 0
  RH-blames = refl

  hidden-unrelated : ∀ {W : World ΔL ΔL} {γ O A A′} {q : A ⊑ᵂ⟨ W ⟩[ O ] A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ RH ∶⟨ A , A′ ⟩[ O ] q)
  hidden-unrelated = Outer.no-top Hid c-hid

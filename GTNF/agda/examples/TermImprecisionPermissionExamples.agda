module examples.TermImprecisionPermissionExamples where

-- File Charter:
--   * PERMISSIONS AND R1/R2 (design.md D28) on concrete programs, with
--     the real relation (TermImprecision): example P4 derives under the
--     grants of right checks, and the counterexamples C1, C3 and C5 are
--     NOT derivable.  Copied from the checked local copy
--     proof/DGG/notes/PermissionsR.agda (§10-§14, §19, §19a; here
--     §1-§7a); no notes module is imported.
--       P4.p4-B1 … p4-B6   P4 (= cambridge Cf from its second block),
--                          every block; the gen wrapper `X! → X?` (B2)
--                          and the check `X?` (B3, B4) grant αᴿ, under
--                          which the shared X is X⊑★ (`W₄²¹`)
--       CgB1.cg-b1,        Cg B1 and C18b B7 (two names; only X's rep.
--       C18bB7.c18b-b7     var is granted)
--       P4c.p4-R7 … p4-R10 the right's Merge, IdDyn, Merge, TagUntag
--                          against B4's left (reduction closure)
--       C1.c1-unrelated    C1 (`L₆ ⊑ R₇`, all three routes of
--                          HiddenNames §2): not derivable at κʷ ≡ []
--       C3.c3-unrelated    C3 (`LE₁ ⊑ RE₁`): not derivable at κʷ ≡ []
--       C5.r1-rejects-c5,  C5 (Permissions.md §5; L state 3, R state 5):
--       C5Dead.c5-unrelated  R1 rejects the payload view under the grant,
--                          and the pair is unrelated in EVERY world at
--                          ANY κ; so is its failing redex against the
--                          left value (M26's shape,
--                          `c5-redex-unrelated`) and its hidden variant
--                          (`hidden-unrelated`, which needs R1 after the
--                          right hide or R2 at the matched hides)
--   * THE INVARIANT of the negative proofs is `κʷ ≡ []` (§3): a
--     top-level world has no permission; a permission enters only at a
--     granting right cast, and a boundary passes κ unchanged.  C5 needs
--     no hypothesis at all.
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
import examples.TermImprecisionExamples as TIE
import examples.TermImprecisionRebaseExamples as Rebase

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Example P4 (= cambridge Cf from its second block), every block.
-- The shared X is X⊑X (`W₄²`) until a right coercion grants αᴿ: the gen
-- wrapper `X! → X?` before CastFun (B2), the check `X?` after it (B3,
-- B4).  Under the grant X is X⊑★ (`W₄²¹`); inside the right's own `−X`
-- it is left-only (`W₄ᴸ`), and the right's `+X` rejoins it at αᴿ, which
-- is still permitted (κ passes through every boundary)
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
           id★→; tagX↦-grants)
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
  -- matched TyBetas pair them globally.  The boundary name X is
  -- both-sided, X⊑X without permission (`W₄²`) and X⊑★ under the grant
  -- of αᴿ (`W₄²¹`), left-only after a right `−X` (`W₄ᴸ`), and rejoined
  -- at the right's `+X` with αᴿ still permitted.

  Ξ₄ : RepCtx
  Ξ₄ = bindR `ℕ ∷ []

  ϱ₄ : RepRel
  ϱ₄ = (0 , 0) ∷ []

  W₄ : World ΔL ΔL
  W₄ = Wc⁰ {Ξ₄} {ϱ₄}

  -- X both-sided, NOT permitted: X⊑X
  W₄² : World ΔLᵢ ΔLᵢ
  W₄² = Wc² {Ξ₄} {ϱ₄} [] 0

  -- X both-sided, αᴿ PERMITTED (under a grant): X⊑★
  W₄²¹ : World ΔLᵢ ΔLᵢ
  W₄²¹ = Wc² {Ξ₄} {ϱ₄} (0 ∷ []) 0

  -- X left-only (inside the right's −X), αᴿ permitted
  W₄ᴸ : World ΔLᵢ ΔL
  W₄ᴸ = Wcᴸ {Ξ₄} {ϱ₄} (0 ∷ [])

  -- no name, permissions κ
  W₄⁰ : List RVar → World ΔL ΔL
  W₄⁰ κ = world 0 []↪ []↪ ϱ₄ [] κ []

  -- without a grant the shared X is X⊑X: B3's premise index is empty
  no-X⊑★-W₄² : ¬ (marksʷ W₄² ∋ˡ 0 := X⊑★)
  no-X⊑★-W₄² ()

  module Wf₄ {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World (Ξ₄ ∣ nsL) (Ξ₄ ∣ nsR)
    W = world n η η′ ϱ₄ [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑ι base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  p0 : All (Ξ₄ ∋ʳ_) (0 ∷ [])
  p0 = (_ , here) ∷ []

  W₄⁰-wf : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → WfWorld (W₄⁰ κ)
  W₄⁰-wf {κ} ps = wf-world joint[] agree (namedᴸ-≤1 W ≤1-[])
    (namedᴿ-≤1 W ≤1-[]) [] [] ps
    where open Wf₄ 0 []↪ []↪ κ

  W₄-wf : WfWorld W₄
  W₄-wf = W₄⁰-wf []

  W₄²κ-wf : ∀ {κ} → All (Ξ₄ ∋ʳ_) κ → WfWorld (Wc² {Ξ₄} {ϱ₄} κ 0)
  W₄²κ-wf {κ} ps = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] ps
    where open Wf₄ 1 (keep []↪) (keep []↪) κ

  W₄²-wf : WfWorld W₄²
  W₄²-wf = W₄²κ-wf []

  W₄²¹-wf : WfWorld W₄²¹
  W₄²¹-wf = W₄²κ-wf p0

  W₄ᴸ-wf : WfWorld W₄ᴸ
  W₄ᴸ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] p0
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
  S⊑Sκ ps = ⟪⟫⊑⟪⟫ unb-int (W₄⁰-wf ps) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (_ , unb-conv , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  S⊑S : W₄²¹ ∣ [] ⊢ S ⊑ S ∶ X⊑X
  S⊑S = S⊑Sκ p0

  -- the left's λx:X. x against the right's λx:★. x (X left-only)
  idX⊑I★ : W₄ᴸ ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξ₄ ϱ₄ (0 ∷ [])
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  bI★⁻ : BdyTy ΔLᵢ unb₀ ΔL (★ ⇒ ★) id★→ (★ ⇒ ★)
  bI★⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = I★⁻}))))

  -- idX ⊑ [−X^α] (λx:★. x) ⟨id(★) → id(★)⟩ at X→X ⊑ ★→★ (X both-sided
  -- and PERMITTED: this index needs the grant)
  idX⊑I★⁻ : W₄²¹ ∣ [] ⊢ idX ⊑ I★⁻ ∶ c⊑★² Ξ₄ ϱ₄ (0 ∷ []) 0 refl
  idX⊑I★⁻ = ⊑⟪⟫ (Wc-unbindᴿ v₀) push-none W₄ᴸ-wf idX⊑I★ bI★⁻
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
      (⊑cast₀
        (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
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
        (⊑cast₀
          (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
            (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (x⊑x Zʷ)) (∀id⊑★ ∅ʷ))
          genArg-ty (∀id⊑∀id ∅ʷ))
        (ι⊑ι base-ℕ) νL-ty νR₁-ty
        (Wν , Wν-conv , revX⊑revX refl)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B2 (2, 2): after both TyBetas, BEFORE CastFun.  The right's gen
  -- wrapper `X! → X?` at `^[X:★∼X]` is ONE arrow coercion; its
  -- covariant `X?` GRANTS αᴿ (`tagX↦-grants`), so its premise reads
  -- X→X ⊑ ★→★ at X⊑★

  bBg : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  bBg = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = Bg}))))

  p4-B2 : W₄ ∣ [] ⊢ nth Ls 2 ⊑ nth Rs 2 ∶ ι⊑ι base-ℕ
  p4-B2 =
    ·⊑·
      (⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
        (⊑cast! tagX↦-grants idX⊑I★⁻ tagᵍ-ty (c⊑c² Ξ₄ ϱ₄ [] 0))
        bL-ty bBg (W₄² , Wc-bind²-conv v₀ here⇔ , revX⊑revX refl)
        (ℕ⇒ℕ W₄))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- B3 (3, 4): after the left's Wrap and the right's Wrap, CastFun.
  -- The right's X? at `^[X:★∼X]` and its argument's X! at `^[X:X∼★]`
  -- (CastFun flipped the environment).  The check GRANTS αᴿ (`gr-?`);
  -- the tag below it reads X ⊑ ★ at the permitted X

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
  S⊑S! = ⊑cast₀ S⊑S tagˣ-ty (X⊑★ here)

  p4-B3 : W₄ ∣ [] ⊢ nth Ls 3 ⊑ nth Rs 4 ∶ ι⊑ι base-ℕ
  p4-B3 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast! {p = X⊑★ here} (gr-? here) (·⊑· idX⊑I★⁻ S⊑S!) chkᵍ-ty X⊑X)
      bUnsealL₃ bUnsealR₄
      (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
      (ι⊑ι base-ℕ)

  ---------------------------------------------------------------------
  -- B4 (4, 6): after the left's Beta and the right's Wrap, Beta.  THE
  -- "J" PAIR (SidedMarks.md §4) is the premise `S ⊑ J`: X left-only
  -- after the right's −X, rejoined at the right's +X; αᴿ is still
  -- permitted (the check above granted it; κ passes both boundaries)

  J : Term
  J = (S ⟨ X∼★ ∷ [] ∣ tagX ⟩) ⟪ Θ₀ , id★ᶜ ⟫

  bJ : BdyTy ΔL Θ₀ ΔLᵢ ★ id★ᶜ ★
  bJ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = J}))))

  bJ⁻ : BdyTy ΔLᵢ unb₀ ΔL ★ id★ᶜ ★
  bJ⁻ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔLᵢ} {M = J ⟪ unb₀ , id★ᶜ ⟫}))))

  -- the J pair (index X ⊑ ★, X left-only)
  S⊑J : W₄ᴸ ∣ [] ⊢ S ⊑ J ∶ X⊑★ here
  S⊑J = ⊑⟪⟫ (Wc-bindᴿ v₀ here⇔) push-none W₄²¹-wf S⊑S! bJ (X⊑★ here)

  p4-B4 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ nth Rs 6 ∶ ι⊑ι base-ℕ
  p4-B4 =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf
      (⊑cast! {p = X⊑★ here} (gr-? here)
        (⊑⟪⟫ (Wc-unbindᴿ v₀) push-none W₄ᴸ-wf S⊑J bJ⁻ (X⊑★ here))
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
  p4-B5 = ⟪⟫⊑⟪⟫ int5 W₄-wf (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b5L b5R
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
-- globally), X both-sided at X⊑X; the right's gen wrapper `X! → X?`
-- GRANTS αᴿ; inside its own `−X` X is left-only, where λx:X.x ⊑ λx:★.x
-- reads X ⊑ ★
------------------------------------------------------------------------

module CgB1 where
  open import examples.TypeCheck using (tc; tf)
  open import examples.Eval using (evalTerms)
  open import examples.CambridgeExamples using (Cg-L; Cg-L-⊢; I★)
  open TIE using (idX; revX; L1′; ΔL; ΔR; ΔLᵢ; bL-ty; revX⊑revX; five⊑)
  open Rebase
    using (Wc⁰; Wc²; Wcᴸ; Wc-bind²; Wc-bind²-conv; Wc-unbindᴿ;
           c⊑★ᴸ; c⊑★²; c⊑c²; Cg-R₂; Cg-R₂-state; Bg-ty; I★⁻ᴿ-ty; tagᴿ-ty;
           id★↦ᴿ-ty; ℕ⇒ℕ⊑★⇒★; tagX↦-grants; p0)

  Ξg : RepCtx
  Ξg = bindR ★ ∷ []

  ϱg : RepRel
  ϱg = (0 , 0) ∷ []

  Cg-L₁-state : head (drop 1 (evalTerms 10 Cg-L-⊢)) ≡ just L1′
  Cg-L₁-state = refl

  module Wfg {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξg ∣ nsR)
    W = world n η η′ ϱg [] κ []

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wg²-wf : WfWorld (Wc² {Ξg} {ϱg} [] 0)
  Wg²-wf = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] []
    where open Wfg 1 (keep []↪) (keep []↪) []

  Wgᴴ-wf : WfWorld (Wcᴸ {Ξg} {ϱg} (0 ∷ []))
  Wgᴴ-wf = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) [] [] p0
    where open Wfg 1 (keep []↪) (skip []↪) (0 ∷ [])

  idX⊑I★ : Wcᴸ {Ξg} {ϱg} (0 ∷ []) ∣ [] ⊢ idX ⊑ I★ ∶ c⊑★ᴸ Ξg ϱg (0 ∷ [])
  idX⊑I★ = ƛ⊑ƛ {pA = X⊑★ here} {pB = X⊑★ here} tf tf (x⊑x Zʷ)

  cg-b1 : Wc⁰ {Ξg} {ϱg} ∣ [] ⊢ L1′ ⊑ Cg-R₂ ∶ ι⊑★ base-ℕ
  cg-b1 =
    ·⊑·
      (⊑cast₀
        (⟪⟫⊑⟪⟫ (Wc-bind² (_ , here) here⇔) Wg²-wf
          (⊑cast! {A = ` 0 ⇒ ` 0} tagX↦-grants
            (⊑⟪⟫ (Wc-unbindᴿ (_ , here)) push-none Wgᴴ-wf idX⊑I★ I★⁻ᴿ-ty
              (c⊑★² Ξg ϱg (0 ∷ []) 0 refl))
            tagᴿ-ty (c⊑c² Ξg ϱg [] 0))
          bL-ty Bg-ty
          (Wc² [] 0 , Wc-bind²-conv (_ , here) here⇔ , revX⊑revX refl)
          (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
        id★↦ᴿ-ty (ℕ⇒ℕ⊑★⇒★ (Wc⁰ {Ξg} {ϱg})))
      five⊑

------------------------------------------------------------------------
-- 1b. C18b B7 (cambridge Ex 18b, block (7,12)): TWO names at once.
-- Matched outer `(+Y,+X)`, both both-sided at X⊑X; the right's `X?`
-- GRANTS X's rep. var 1; the right's `(−Y,−X)` makes both left-only;
-- its `(+X,+Y)` rejoins both, X still permitted (κ = [1] passes both
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
  W₀ κ = world 0 []↪ []↪ ϱ [] κ []

  -- both both-sided, X⊑★
  Wb : List RVar → World Δ₂ Δ₂
  Wb κ = world 2 (keep (keep []↪)) (keep (keep []↪)) ϱ [] κ []

  -- both left-only (inside the right's (−Y,−X))
  Wh : List RVar → World Δ₂ Δ₀
  Wh κ = world 2 (keep (keep []↪)) (skip (skip []↪)) ϱ [] κ []

  module Wf {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where

    W : World ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsL)
              ((bindR `ℕ ∷ bindR `ℕ ∷ []) ∣ nsR)
    W = world n η η′ ϱ [] κ []

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
  W₀-wf {κ} ps = wf-world joint[] agree uniqᴸ uniqᴿ [] [] ps
    where open Wf 0 []↪ []↪ κ

  Wb-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (Wb κ)
  Wb-wf {κ} ps =
    wf-world (both (inj₁ here⇔) (both (inj₁ (there⇔ here⇔)) joint[]))
      agree uniqᴸ uniqᴿ [] [] ps
    where open Wf 2 (keep (keep []↪)) (keep (keep []↪)) κ

  Wh-wf : ∀ {κ} → All (Rs₂ ∋ʳ_) κ → WfWorld (Wh κ)
  Wh-wf {κ} ps =
    wf-world (left-only (left-only joint[])) agree uniqᴸ uniqᴿ [] [] ps
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
  S2⊑S2 = ⟪⟫⊑⟪⟫ IntS (W₀-wf p1) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS
    (Wb (1 ∷ []) , ConvS , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  -- inside the rejoin: the right's X! at the rejoined, permitted X
  inner : Wb (1 ∷ []) ∣ [] ⊢ S2 ⊑ S2 ⟨ flipᵐ ★∼X ∷ X∼★ ∷ [] ∣ (` 1) ! ⟩
    ∶ X⊑★ X★
  inner = ⊑cast₀ S2⊑S2 tag-ty (X⊑★ X★)

  c18b-b7 : W₀ [] ∣ [] ⊢ L7 ⊑ R12 ∶ ι⊑ι base-ℕ
  c18b-b7 =
    ⟪⟫⊑⟪⟫ IntO (Wb-wf [])
      (⊑cast! {p = X⊑★ X★} (gr-? (there here))
        (⊑⟪⟫ IntH push-none (Wh-wf p1)
          (⊑⟪⟫ IntJ push-none (Wb-wf p1) inner bJ2 (X⊑★ (there here)))
          bRH (X⊑★ X★))
        chk-ty X⊑X)
      bL7 bR12 (Wb [] , ConvO , conv-unseal⊑unseal refl) (ι⊑ι base-ℕ)

------------------------------------------------------------------------
-- 2. Reduction closure on P4's run (SimBack evidence): the left at B4
-- (`[+X^α] S ⟨+X⟩`) is related to EVERY right state its Merge, IdDyn,
-- Merge, TagUntag steps produce (right states 7-10).  The merged
-- `[−X, +X]` is an unbind then a bind of X in ONE boundary: `toExt`
-- makes X continuing on both sides, so X stays joined, and αᴿ stays
-- permitted (the check above it); after IdDyn the tag `X!` is outside,
-- still under the check.  (State 11, the final Merge, needs the left's own Merge:
-- B5.)
------------------------------------------------------------------------

module P4c where
  open import examples.TypeCheck using (tc; tf)
  open P4 using (nth; Ls; Rs; S; unb₀; id★ᶜ; tagX; chkX; tagˣ-ty; chkᵍ-ty;
                 bUnsealL; W₄; W₄²; W₄-wf; W₄²-wf; v₀; S⊑S; bS; bdy-wf;
                 Ξ₄; ϱ₄; W₄²¹; W₄²¹-wf; W₄⁰; W₄⁰-wf; p0)
  open Rebase using (Wc²)
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
  S⊑S3 ps = ⟪⟫⊑⟪⟫ Int3 (W₄⁰-wf ps) (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bS bS3
    (_ , Conv3 , conv-tail⊑tail (conv-seal⊑seal refl)) X⊑X

  outer : ∀ {M′} → (b′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0) (unseal 0) `ℕ)
    → BdyConversionImp W₄ bUnsealL b′
    → W₄² ∣ [] ⊢ S ⊑ M′ ∶ X⊑X
    → W₄ ∣ [] ⊢ nth Ls 4 ⊑ M′ ⟪ Θ₀ , unseal 0 ⟫ ∶ ι⊑ι base-ℕ
  outer b′ bc d =
    ⟪⟫⊑⟪⟫ (Wc-bind² v₀ here⇔) W₄²-wf d bUnsealL b′ bc (ι⊑ι base-ℕ)


  p4-R7 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R7 ∶ ι⊑ι base-ℕ
  p4-R7 = outer bR7
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast! {p = X⊑★ here} (gr-? here)
      (⊑⟪⟫ IntRR push-none W₄²¹-wf (⊑cast₀ S⊑S tagˣ-ty (X⊑★ here)) bBm7
        (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R8 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R8 ∶ ι⊑ι base-ℕ
  p4-R8 = outer bR8
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast! {p = X⊑★ here} (gr-? here)
      (⊑cast₀ {p = X⊑X} (⊑⟪⟫ IntRR push-none W₄²¹-wf S⊑S bBi8 X⊑X)
        tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R9 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R9 ∶ ι⊑ι base-ℕ
  p4-R9 = outer bR9
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl)
    (⊑cast! {p = X⊑★ here} (gr-? here)
      (⊑cast₀ {p = X⊑X} (S⊑S3 p0) tagˣ-ty (X⊑★ here))
      chkᵍ-ty X⊑X)

  p4-R10 : W₄ ∣ [] ⊢ nth Ls 4 ⊑ R10 ∶ ι⊑ι base-ℕ
  p4-R10 = outer bR10
    (W₄² , Wc-bind²-conv v₀ here⇔ , conv-unseal⊑unseal refl) (S⊑S3 [])


------------------------------------------------------------------------
-- 3. Facts for the non-derivability proofs.  THE INVARIANT IS κʷ ≡ []:
-- a top-level world has no permission (like `πʷ ≡ []`); a permission
-- enters only at a granting right cast; a boundary passes κ unchanged.
-- Under κʷ ≡ [] a center name the right sees is X⊑X (`no★-right`), so a
-- right tag `X!` can face no untagged left value (`no-tag★`).
------------------------------------------------------------------------

lookup-unique : ∀ {A : Set} {xs : List A} {k a b}
  → xs ∋ˡ k := a → xs ∋ˡ k := b → a ≡ b
lookup-unique here      here       = refl
lookup-unique (there h) (there h′) = lookup-unique h h′

-- the derived mark of a right name is its permission
dmarks-emb : ∀ {ns n X β} (ι : ns ↪ n) (κ : List RVar) → ns ∋ˡ X := β
  → dmarks ι κ ∋ˡ emb ι X := permit β κ
dmarks-emb (keep ι) κ here      = here
dmarks-emb (keep ι) κ (there h) = there (dmarks-emb ι κ h)
dmarks-emb (skip ι) κ h         = there (dmarks-emb ι κ h)

-- NO PERMISSION, NO X⊑★ AT A NAME THE RIGHT SEES
no★-right : ∀ {V : World Δ Δ′} {X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ¬ (marksʷ V ∋ˡ emb (ηᴿʷ V) X′ := X⊑★)
no★-right {V = V} {β = β} eκ rh h
  with trans (lookup-unique h (dmarks-emb (ηᴿʷ V) (κʷ V) rh))
             (cong (permit β) eκ)
... | ()

-- ... so a left name joined to a right name is not X⊑★
no-tag★ : ∀ {V : World Δ Δ′} {X X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → Joins V X X′ → ¬ (marksʷ V ∋ˡ emb (ηᴸʷ V) X := X⊑★)
no-tag★ {V = V} eκ rh j h =
  no★-right {V = V} eκ rh (subst (λ c → marksʷ V ∋ˡ c := X⊑★) j h)

-- the index of a non-∀ left type has no pending name
data NonForall : Ty → Set where
  nf-var : ∀ {X} → NonForall (` X)
  nf-ℕ   : NonForall `ℕ
  nf-𝔹   : NonForall `𝔹
  nf-★   : NonForall ★
  nf-⇒   : ∀ {A B} → NonForall (A ⇒ B)

openImp-[] : ∀ {μ cs ρ A B} → NonForall A → OpenImp μ cs ρ A B → cs ≡ []
openImp-[] {cs = []}    _      _  = refl
openImp-[] {cs = c ∷ cs} nf-var ()
openImp-[] {cs = c ∷ cs} nf-ℕ   ()
openImp-[] {cs = c ∷ cs} nf-𝔹   ()
openImp-[] {cs = c ∷ cs} nf-★   ()
openImp-[] {cs = c ∷ cs} nf-⇒   ()

map-[] : ∀ {A B : Set} {f : A → B} (xs : List A) → map f xs ≡ [] → xs ≡ []
map-[] []       _  = refl
map-[] (x ∷ xs) ()

π[] : ∀ {V : World Δ Δ′} {A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩ A′ → πʷ V ≡ []
π[] {V = V} {A} {A′} nf q =
  map-[] (πʷ V)
    (openImp-[] {μ = marksʷ V} {ρ = emb (ηᴸʷ V)} {A = A} {B = embᴿ V A′} nf q)

plain-idx : ∀ {V : World Δ Δ′} {A A′} → NonForall A → A ⊑ᵂ⟨ V ⟩ A′
  → marksʷ V ⊢ embᴸ V A ⊑ embᴿ V A′
plain-idx {V = V} {A} {A′} nf q =
  subst (λ π → OpenImp (marksʷ V) (map (emb (ηᴿʷ V)) π) (emb (ηᴸʷ V)) A
                 (embᴿ V A′))
        (π[] {V = V} {A′ = A′} nf q) q

var⊑var : ∀ {μ a b} → μ ⊢ ` a ⊑ ` b → a ≡ b
var⊑var X⊑X = refl

var⊑★ : ∀ {μ a} → μ ⊢ ` a ⊑ ★ → μ ∋ˡ a := X⊑★
var⊑★ (X⊑★ h) = h

no-ℕ⊑var : ∀ {V : World Δ Δ′} {X} → ¬ (`ℕ ⊑ᵂ⟨ V ⟩ ` X)
no-ℕ⊑var {V = V} {X} q with plain-idx {V = V} {A′ = ` X} nf-ℕ q
... | ()

no-★⊑var : ∀ {V : World Δ Δ′} {X} → ¬ (★ ⊑ᵂ⟨ V ⟩ ` X)
no-★⊑var {V = V} {X} q with plain-idx {V = V} {A′ = ` X} nf-★ q
... | ()

no-var⊑ℕ : ∀ {V : World Δ Δ′} {X} → ¬ (` X ⊑ᵂ⟨ V ⟩ `ℕ)
no-var⊑ℕ {V = V} {X} q with plain-idx {V = V} {A′ = `ℕ} nf-var q
... | ()

no-plain-ℕ⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ `ℕ ⊑ ` a)
no-plain-ℕ⊑var ()

no-plain-★⊑var : ∀ {μ : ImpEnv} {a} → ¬ (μ ⊢ ★ ⊑ ` a)
no-plain-★⊑var ()

-- THE DECISIVE INDEX: a left name against a right name in one world,
-- against ★ in another with the same embeddings and no permission
no-tag-at : ∀ {V : World Δ Δ′} {κₚ a X′ β} → κʷ V ≡ [] → Δ′ ∋ᵗ X′ := β
  → ` a ⊑ᵂ⟨ record V { κʷ = κₚ } ⟩ ` X′ → ` a ⊑ᵂ⟨ V ⟩ ★ → ⊥
no-tag-at {V = V} {κₚ} {X′ = X′} eκ rh p q =
  no-tag★ {V = V} eκ rh
    (var⊑var (plain-idx {V = record V { κʷ = κₚ }} {A′ = ` X′} nf-var p))
    (var⊑★ (plain-idx {V = V} {A′ = ★} nf-var q))

-- the left type of a cast, a boundary, a literal (right rules keep it)
lty-cast : ∀ {V : World Δ Δ′} {γ M M′ μ c A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ M′ ∶ q → Σ[ B ∈ Ty ] CastTy Δ μ c B A
lty-cast (cast⊑cast _ ct _ _) = _ , ct
lty-cast (cast⊑ _ _ ct _)     = _ , ct
lty-cast (⊑cast _ _ d _ _)    = lty-cast d
lty-cast (⊑⟪⟫ _ _ _ d _ _)    = lty-cast d

lty-bdy : ∀ {V : World Δ Δ′} {γ M M′ Θ c A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ q
  → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Aᵢ ∈ Ty ] BdyTy Δ Θ Δᵢ Aᵢ c A
lty-bdy (⟪⟫⊑⟪⟫ _ _ _ b _ _ _) = _ , _ , b
lty-bdy (⟪⟫⊑ _ _ _ _ _ b _)   = _ , _ , b
lty-bdy (⊑cast _ _ d _ _)     = lty-bdy d
lty-bdy (⊑⟪⟫ _ _ _ d _ _)     = lty-bdy d

lty-$ : ∀ {V : World Δ Δ′} {γ n M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ $ n ⊑ M′ ∶ q → A ≡ `ℕ
lty-$ (κ⊑κ lit-$ _)       = refl
lty-$ (⊑cast _ _ d _ _)   = lty-$ d
lty-$ (⊑⟪⟫ _ _ _ d _ _)   = lty-$ d

-- a variable at the empty term context is related to nothing
no-var-[] : ∀ {V : World Δ Δ′} {x M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → ¬ (V ∣ [] ⊢ ` x ⊑ M′ ∶ q)
no-var-[] (x⊑x ())
no-var-[] (⊑cast _ raise-[] d _ _) = no-var-[] d
no-var-[] (⊑⟪⟫ _ _ _ d _ _) = no-var-[] d

-- the left type of the variable 0 is its entry's
lty-x : ∀ {V : World Δ Δ′} {A₀ A₀′ p₀ γ M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ ctx-imp A₀ A₀′ p₀ ∷ γ ⊢ ` 0 ⊑ M′ ∶ q → A ≡ A₀
lty-x (x⊑x Zʷ) = refl
lty-x (⊑cast _ (raise-∷ _) d _ _) = lty-x d
lty-x (⊑⟪⟫ _ _ _ d _ _) = ⊥-elim (no-var-[] d)

-- the left types of λx:X. x and of ΛX. λx:X. x
idX′ : Term
idX′ = ƛ (` 0) ∙ ` 0

lty-idX : ∀ {V : World Δ Δ′} {γ M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ idX′ ⊑ M′ ∶ q → A ≡ ` 0 ⇒ ` 0
lty-idX (ƛ⊑ƛ _ _ d) rewrite lty-x d = refl
lty-idX (⊑cast _ _ d _ _) = lty-idX d
lty-idX (⊑⟪⟫ _ _ _ d _ _) = lty-idX d

lty-ΛidX : ∀ {V : World Δ Δ′} {γ M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → V ∣ γ ⊢ Λ idX′ ⊑ M′ ∶ q → A ≡ `∀ (` 0 ⇒ ` 0)
lty-ΛidX (Λ⊑Λ _ _ _ d _) rewrite lty-idX d = refl
lty-ΛidX (Λ⊑ _ _ _ _ _ d _) rewrite lty-idX d = refl
lty-ΛidX (⊑cast _ _ d _ _) = lty-ΛidX d
lty-ΛidX (⊑⟪⟫ _ _ _ d _ _) = lty-ΛidX d

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

-- coercions that grant nothing
NoGrant : Coercion → Set
NoGrant c = ∀ {Δ′ β} → ¬ Grants Δ′ β c

ng-ℕ? : ∀ {ℓ} → NoGrant (`ℕ ？ ℓ)
ng-ℕ? ()

ng-id : ∀ {A} → NoGrant (idᵖ A)
ng-id ()

ng-id★↦ : NoGrant (idᵖ ★ ↦ᵖ idᵖ ★)
ng-id★↦ (gr-↦ _ ())

ng-tag↦id★ : ∀ {X} → NoGrant (((` X) !) ↦ᵖ idᵖ ★)
ng-tag↦id★ (gr-↦ _ ())

cg-none : ∀ {Δ′ c κ κₚ} → NoGrant c → CastGrant Δ′ c κ κₚ → κₚ ≡ κ
cg-none ng no-grant  = refl
cg-none ng (grant g) = ⊥-elim (ng g)

-- the bind entry `+X^0` from a context with no name
Θ₀ : Boundary
Θ₀ = bind 0 0 ∷ []

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

------------------------------------------------------------------------
-- 4. The spine argument for C1 and C2.  A RIGHT spine (casts,
-- boundaries) that reaches a name tag `X!` through casts that grant
-- nothing (`Reach`); a LEFT term outside its own `[+X^α] (sealed m)
-- ⟨+X⟩` boundary under ground casts (`LO`).  Under κʷ ≡ [] they are
-- never related: inside the left boundary the decisive step `⊑cast` of
-- the tag needs X⊑★ at a name the right sees (`no-tag-at`).
------------------------------------------------------------------------

data Reach : Term → Set where
  r-tag  : ∀ {U μ k} → Reach (U ⟨ μ ∣ (` k) ! ⟩)
  r-cast : ∀ {R μ c} → NoGrant c → Reach R → Reach (R ⟨ μ ∣ c ⟩)
  r-⟪⟫   : ∀ {R Θ d} → Reach R → Reach (R ⟪ Θ , d ⟫)

-- left literals against a Reach spine (by types alone)
no-$ : ∀ {V : World Δ Δ′} {γ n R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⊑ R ∶ q)
no-$ {V = V} r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
  with ct-X! ct | lty-$ d
... | _ , refl , refl | refl = no-ℕ⊑var {V = record V { κʷ = κₚ }} p
no-$ (r-cast _ r) (⊑cast _ _ d _ _) = no-$ r d
no-$ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ d _ _) = no-$ r d

no-n★ : ∀ {V : World Δ Δ′} {γ n μ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
  → Reach R → ¬ (V ∣ γ ⊢ $ n ⟨ μ ∣ `ℕ ! ⟩ ⊑ R ∶ q)
no-n★ {V = V} r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
  with ct-X! ct | lty-cast d
... | _ , refl , refl | _ , ct₀ with ct-ℕ! ct₀
... | refl , refl = no-★⊑var {V = record V { κʷ = κₚ }} p
no-n★ r-tag (cast⊑cast {p = p} d ct ct′ _) with ct-ℕ! ct | ct-X! ct′
... | refl , refl | _ , refl , refl = no-plain-ℕ⊑var p
no-n★ (r-cast _ r) (cast⊑cast d _ _ _) = no-$ r d
no-n★ (r-cast _ r) (⊑cast _ _ d _ _) = no-n★ r d
no-n★ r (cast⊑ _ d _ _) = no-$ r d
no-n★ (r-⟪⟫ r) (⊑⟪⟫ _ _ _ d _ _) = no-n★ r d

data G : Ty → Set where
  gℕ : G `ℕ
  g★ : G ★

no-G⊑var : ∀ {V : World Δ Δ′} {A X} → G A → ¬ (A ⊑ᵂ⟨ V ⟩ ` X)
no-G⊑var {V = V} gℕ = no-ℕ⊑var {V = V}
no-G⊑var {V = V} g★ = no-★⊑var {V = V}

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

module Spine (m : Term)
  (no-leaf : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Reach R → ¬ (V ∣ γ ⊢ m ⊑ R ∶ q))
  (Δ₀ : Ctxᵗ)
  (bdy : ∀ {Δᵢ Aᵢ A} → BdyTy Δ₀ Θ₀ Δᵢ Aᵢ (unseal 0) A → (Aᵢ ≡ ` 0) × G A)
  where

  -- THE INSIDE LEMMA: the left's sealed leaf (type X) against a spine
  -- reaching a tag, with no permission
  no-S : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → A ≡ ` 0 → Reach R → ¬ (V ∣ γ ⊢ sealed m ⊑ R ∶ q)
  no-S {V = V} eκ refl r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct q)
    with ct-X! ct
  ... | (_ , rh) , refl , refl = no-tag-at {V = V} {κₚ = κₚ} eκ rh p q
  no-S eκ eA (r-cast ng r) (⊑cast g _ d _ _) =
    no-S (trans (cg-none ng g) eκ) eA r d
  no-S eκ eA (r-⟪⟫ r) (⊑⟪⟫ I _ _ d _ _) = no-S (trans (same-κ I) eκ) eA r d
  no-S eκ eA (r-⟪⟫ r) (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-leaf r d
  no-S eκ eA r (⟪⟫⊑ _ _ _ _ d _ _) = no-leaf r d

  B : Term
  B = sealed m ⟪ Θ₀ , unseal 0 ⟫

  data LO : Term → Set where
    lo-B : LO B
    lo-c : ∀ {M c} → GCast c → LO M → LO (M ⟨ [] ∣ c ⟩)

  lo-ty : ∀ {Δ₂} {V : World Δ₀ Δ₂} {γ M R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → LO M → V ∣ γ ⊢ M ⊑ R ∶ q → G A
  lo-ty lo-B d with lty-bdy d
  ... | _ , _ , b = proj₂ (bdy b)
  lo-ty (lo-c gc _) d with lty-cast d
  ... | _ , ct = gtrg gc ct

  -- THE OUTSIDE LEMMA: the left outside its boundary
  no-LO : ∀ {Δ₂} {V : World Δ₀ Δ₂} {γ M R A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → LO M → Reach R → ¬ (V ∣ γ ⊢ M ⊑ R ∶ q)
  no-LO {V = V} eκ lo r-tag (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
    with ct-X! ct
  ... | _ , refl , refl = no-G⊑var {V = record V { κʷ = κₚ }} (lo-ty lo d) p
  no-LO eκ lo (r-cast ng r) (⊑cast g _ d _ _) =
    no-LO (trans (cg-none ng g) eκ) lo r d
  no-LO eκ (lo-c gc lo) r-tag (cast⊑cast {p = p} d ct ct′ _)
    with ct-X! ct′
  ... | _ , refl , refl = no-G⊑varᵖ (gsrc gc ct) p
  no-LO eκ (lo-c gc lo) (r-cast _ r) (cast⊑cast d _ _ _) = no-LO eκ lo r d
  no-LO eκ (lo-c gc lo) r (cast⊑ _ d _ _) = no-LO eκ lo r d
  no-LO eκ lo (r-⟪⟫ r) (⊑⟪⟫ I _ _ d _ _) = no-LO (trans (same-κ I) eκ) lo r d
  no-LO eκ lo-B r (⟪⟫⊑ I _ _ _ d b _) =
    no-S (trans (same-κ I) eκ) (proj₁ (bdy b)) r d
  no-LO eκ lo-B (r-⟪⟫ r) (⟪⟫⊑⟪⟫ I _ d b _ _ _) =
    no-S (trans (same-κ I) eκ) (proj₁ (bdy b)) r d

------------------------------------------------------------------------
-- 5. C1 = the SimBackBlame counterexample L₆ ⊑ R₇ (PendingOpenings
-- §5d): NOT DERIVABLE in any world over its contexts with no
-- permission, at any index.  All three routes of HiddenNames §2
-- (matched, left-first, right-first) end at the right's tag against
-- the left's sealed value with no right check above it: `no-tag-at`.
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
    → (Aᵢ ≡ ` 0) × G A
  bdy-LB (bdy-ty (bw _ i c) ⊢c eqᵢ eqₑ _)
    with interior-functional i TIE.int₀ | conversion-functional c TIE.conv₀
  bdy-LB (bdy-ty _ (conv-unseal (_ , _ , here , r-here , same-★))
                 (_ , same-var here , same-var here)
                 (_ , same-★ , same-★) _) | refl | refl =
    refl , g★

  open Spine 5★ no-n★ ΔR bdy-LB

  -- C1 IS UNRELATED: every world over (ΔR, ΔR) with no permission
  c1-unrelated : ∀ {W : World ΔR ΔR} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₆ ⊑ R₇ ∶ q)
  c1-unrelated eκ =
    no-LO eκ (lo-c gc-ℕ? (lo-c gc-id★ lo-B)) (r-cast ng-ℕ? (r-⟪⟫ r-tag))

------------------------------------------------------------------------
-- 6. C3 = ModeCondition's `Esc.esc-cex-early` (both after TyBeta):
-- NOT DERIVABLE.  Matched boundaries compare `−X → +X` with
-- `−X → id(★)`: the seal joins X, so the ★ clause `+X ⊑ id(★)` needs X
-- permitted; each one-sided order meets `X ⊑ ℕ` or `ℕ ⊑ X`.
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

  lty-ƛ : ∀ {V : World Δ Δ′} {γ A₀ N M′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → V ∣ γ ⊢ ƛ A₀ ∙ N ⊑ M′ ∶ q → Σ[ B ∈ Ty ] A ≡ A₀ ⇒ B
  lty-ƛ (ƛ⊑ƛ _ _ _)       = _ , refl
  lty-ƛ (⊑cast _ _ d _ _) = lty-ƛ d
  lty-ƛ (⊑⟪⟫ _ _ _ d _ _) = lty-ƛ d

  rty-cast : ∀ {V : World Δ Δ′} {γ M M′ μ′ c′ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → V ∣ γ ⊢ M ⊑ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q → Σ[ B′ ∈ Ty ] CastTy Δ′ μ′ c′ B′ A′
  rty-cast (cast⊑cast _ _ ct′ _) = _ , ct′
  rty-cast (⊑cast _ _ _ ct _)    = _ , ct
  rty-cast (cast⊑ _ d _ _)       = rty-cast d
  rty-cast (⟪⟫⊑ _ _ _ _ d _ _)   = rty-cast d
  rty-cast (Λ⊑ _ _ _ _ _ d _)    = rty-cast d
  rty-cast (ν⊑ d _ _ _)          = rty-cast d
  rty-cast (blame⊑ _ ⊢M′ _) with cast-inv ⊢M′
  ... | _ , _ , ct = _ , ct

  no-var⇒⊑ℕ⇒ : ∀ {V : World Δ Δ′} {X B B′} → ¬ ((` X ⇒ B) ⊑ᵂ⟨ V ⟩ (`ℕ ⇒ B′))
  no-var⇒⊑ℕ⇒ {V = V} {X} {B} {B′} q
    with plain-idx {V = V} {A′ = `ℕ ⇒ B′} (nf-⇒ {A = ` X} {B = B}) q
  ... | ⇒⊑⇒ () _

  no-ℕ⇒⊑var⇒ : ∀ {V : World Δ Δ′} {X B B′} → ¬ ((`ℕ ⇒ B) ⊑ᵂ⟨ V ⟩ (` X ⇒ B′))
  no-ℕ⇒⊑var⇒ {V = V} {X} {B} {B′} q
    with plain-idx {V = V} {A′ = ` X ⇒ B′} (nf-⇒ {A = `ℕ} {B = B}) q
  ... | ⇒⊑⇒ () _

  idx : ∀ {Δ₁ Δ₂} {V′ : World Δ₁ Δ₂} {γ M M′ A₁ A₂} {r : A₁ ⊑ᵂ⟨ V′ ⟩ A₂}
    → V′ ∣ γ ⊢ M ⊑ M′ ∶ r → A₁ ⊑ᵂ⟨ V′ ⟩ A₂
  idx {r = r} _ = r

  no-fun : ∀ {V : World ΔL ΔL} {γ A A′ B B′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → A ≡ `ℕ ⇒ B → A′ ≡ `ℕ ⇒ B′ → ¬ (V ∣ γ ⊢ LB₁ ⊑ RB₁ ∶ q)
  no-fun eκ _ _ (⟪⟫⊑⟪⟫ _ _ _ b b′ bc _) = matched-conv eκ b b′ bc
  no-fun eκ eA refl (⟪⟫⊑ {Wᵢ = Vi} _ _ _ _ d _ _) with lty-ƛ d
  ... | _ , refl = no-var⇒⊑ℕ⇒ {V = Vi} (idx d)
  no-fun eκ refl _ (⊑⟪⟫ {Wᵢ = Vi} _ _ _ d _ _) with rty-cast d
  ... | _ , ct with ct-genE-body ct
  ... | refl = no-ℕ⇒⊑var⇒ {V = Vi} (idx d)

  no-app : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ RA ∶ q)
  no-app eκ (·⊑· f (κ⊑κ lit-$ _)) = no-fun eκ refl refl f

  no-LAℕ!-RA : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RA ∶ q)
  no-LAℕ!-RA eκ (cast⊑ _ d _ _) = no-app eκ d

  no-LE₁-RA : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LE₁ ⊑ RA ∶ q)
  no-LE₁-RA eκ (cast⊑ _ d _ _) = no-LAℕ!-RA eκ d

  no-LA-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⊑ RE₁ ∶ q)
  no-LA-RE₁ eκ (⊑cast g _ d _ _) = no-app (trans (cg-none ng-ℕ? g) eκ) d

  no-LAℕ!-RE₁ : ∀ {V : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ LA ⟨ [] ∣ `ℕ ! ⟩ ⊑ RE₁ ∶ q)
  no-LAℕ!-RE₁ eκ (cast⊑cast d _ _ _) = no-app eκ d
  no-LAℕ!-RE₁ eκ (⊑cast g _ d _ _) =
    no-LAℕ!-RA (trans (cg-none ng-ℕ? g) eκ) d
  no-LAℕ!-RE₁ eκ (cast⊑ _ d _ _) = no-LA-RE₁ eκ d

  -- C3 IS UNRELATED: every world over (ΔL, ΔL) with no permission
  c3-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LE₁ ⊑ RE₁ ∶ q)
  c3-unrelated eκ (cast⊑cast d _ _ _) = no-LAℕ!-RA eκ d
  c3-unrelated eκ (⊑cast g _ d _ _) = no-LE₁-RA (trans (cg-none ng-ℕ? g) eκ) d
  c3-unrelated eκ (cast⊑ _ d _ _) = no-LAℕ!-RE₁ eκ d

------------------------------------------------------------------------
-- 7. C5 (Permissions.md §5), its programs and runs.  In Permissions'
-- relation the pair (L state 3, R state 5) is related through the
-- left's payload view `⟪⟫⊑` under the grant of the right's `X?`
-- (`Permissions.C5.c5`).  HERE R1 rejects that step (`r1-rejects-c5`)
-- and §7a proves the pair unrelated in every world.
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

  -- the left's `−X` alone, under the grant: X right-only, αᴿ permitted
  WU : World ΔL ΔLᵢ
  WU = world 1 (skip []↪) (keep []↪) ϱ₄ [] (0 ∷ []) []

  IntU : Interior W₄²¹ unb₀ [] WU
  IntU = record
    { int-left   = unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  WU-wf : WfWorld WU
  WU-wf = wf-world (right-only joint[]) agree
    (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-∷[]) [] [] p0
    where open Wf₄ 1 (skip []↪) (keep []↪) (0 ∷ [])

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


  -- R1 REJECTS the step Permissions.C5.c5 used: the left's `−X^0` under
  -- the grant of αᴿ = 0, which is paired with αᴸ = 0
  r1-rejects-c5 : ¬ All (UnbindOK W₄²¹) unb₀
  r1-rejects-c5 (ok-unbind u ∷ []) with u (inj₁ here⇔)
  ... | ()

------------------------------------------------------------------------
-- 7a. C5 IS DEAD under R1/R2: not derivable in ANY world over its
-- contexts, at any κ (no `κʷ ≡ []`, no WfWorld hypothesis at the top).
-- Also its hidden variant (the left's payload view inside the right's own
-- hide `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`), which needs R1 after the right hide or
-- R2 at the matched hides.
--
-- The argument: the only way to put the left's sealed `S : X` against a
-- right ★ value that is not X-tagged is the payload view (`⟪⟫⊑` with
-- the left's `−X^0`) or the ★ clause `−X ⊑ id(★)`.  Both sit below the
-- right check `X?`, whose conclusion index `X ⊑ X` joins the left X to
-- the right X (so, by `wf-joint`, rep. var 0 is paired with the right X's
-- rep. var β) and whose premise index `X ⊑ ★` reads X⊑★ at that joined
-- name (so β is permitted).  `HasPermittedPartner _ 0` then refutes R1
-- or R2.  The routes that avoid the check meet `ℕ ⊑ X` or `X ⊑ ℕ`.
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

-- THE CHECK FACT: under a right check of X′ (rep. var β), a left name a
-- (rep. var α) whose conclusion index is `a ⊑ X′` and whose premise
-- index is `a ⊑ ★` has α paired with β, and β permitted in the premise
HasPP-chk : ∀ {V : World Δ Δ′} {κₚ a X′ α β}
  → WfWorld V → Δ ∋ᵗ a := α → Δ′ ∋ᵗ X′ := β
  → ` a ⊑ᵂ⟨ V ⟩ ` X′ → ` a ⊑ᵂ⟨ record V { κʷ = κₚ } ⟩ ★
  → HasPermittedPartner (record V { κʷ = κₚ }) α
HasPP-chk {V = V} {κₚ} {a} {X′} {β = β} wf lh rh q p =
  β , joint-pair (wf-joint wf) lh rh j , sym (lookup-unique h′ hβ)
  where
  j : Joins V a X′
  j = var⊑var (plain-idx {V = V} {A′ = ` X′} nf-var q)
  h : marksʷ (record V { κʷ = κₚ }) ∋ˡ emb (ηᴸʷ V) a := X⊑★
  h = var⊑★ (plain-idx {V = record V { κʷ = κₚ }} {A′ = ★} nf-var p)
  h′ : dmarks (ηᴿʷ V) κₚ ∋ˡ emb (ηᴿʷ V) X′ := X⊑★
  h′ = subst (λ c → dmarks (ηᴿʷ V) κₚ ∋ˡ c := X⊑★) j h
  hβ : dmarks (ηᴿʷ V) κₚ ∋ˡ emb (ηᴿʷ V) X′ := permit β κₚ
  hβ = dmarks-emb (ηᴿʷ V) κₚ rh

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

  -- a literal against a right check of a name: `ℕ ⊑ X`
  no-$-chk : ∀ {V : World Δ Δ′} {γ n M′ μ′ X ℓ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → ¬ (V ∣ γ ⊢ $ n ⊑ M′ ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶ q)
  no-$-chk {V = V} (⊑cast _ _ d ct q) with ct-X? ct | lty-$ d
  ... | _ , refl , refl | refl = no-ℕ⊑var {V = V} q

  -- the right cores under the check: C5's `5⟨ℕ!⟩` and the hidden
  -- variant's `[−X^α] 5⟨ℕ!⟩ ⟨id(★)⟩`
  data Core : Term → Set where
    c-5   : ∀ {n μ} → Core ($ n ⟨ μ ∣ `ℕ ! ⟩)
    c-hid : Core (5★ ⟪ unb₀ , id★ᶜ ⟫)

  -- "the left name 0's rep. var has a permitted partner"
  HP0 : World Δ Δ′ → Set
  HP0 {Δ = Δ} U = ∀ {α} → Δ ∋ᵗ 0 := α → HasPermittedPartner U α

  hp0-int : ∀ {U : World Δ Δ′} {Uᵢ : World Δ Δ′ᵢ} {Θ′}
    → Interior U [] Θ′ Uᵢ → HP0 U → HP0 Uᵢ
  hp0-int I hp lh = hasPP-int I (hp lh)

  -- S against an ℕ-tagged literal: X ⊑ ℕ, or the payload view (R1)
  no-S-5 : ∀ {U : World Δ Δ′} {γ n μ A A′} {q : A ⊑ᵂ⟨ U ⟩ A′}
    → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ $ n ⟨ μ ∣ `ℕ ! ⟩ ∶ q)
  no-S-5 {U = U} refl hp (⊑cast {κₚ = κₚ} _ _ d ct _) with ct-ℕ! ct
  ... | refl , refl = no-var⊑ℕ {V = record U { κʷ = κₚ }} (C3.idx d)
  no-S-5 {U = U} eA hp (⟪⟫⊑ I (ok-unbind u ∷ []) _ _ _ _ _) =
    r1-fails {W = U} (hp (unb1-lookup (int-left I))) u

  -- S against the hidden core: the right hide keeps HP0 (then no-S-5),
  -- the payload view fails R1, the matched hides fail R2
  no-S-core : ∀ {U : World Δ Δ′} {γ Q A A′} {q : A ⊑ᵂ⟨ U ⟩ A′}
    → Core Q → A ≡ ` 0 → HP0 U → ¬ (U ∣ γ ⊢ S ⊑ Q ∶ q)
  no-S-core c-5 eA hp d = no-S-5 eA hp d
  no-S-core c-hid eA hp (⊑⟪⟫ I _ _ d _ _) = no-S-5 eA (hp0-int I hp) d
  no-S-core {U = U} c-hid eA hp (⟪⟫⊑ I (ok-unbind u ∷ []) _ _ _ _ _) =
    r1-fails {W = U} (hp (unb1-lookup (int-left I))) u
  no-S-core c-hid eA hp
    (⟪⟫⊑⟪⟫ I _ _ (bdy-ty _ _ _ _ _) (bdy-ty _ _ _ _ _)
      (Wᶜ , ci , conv-tail⊑tail (conv-seal⊑id★ _ lu)) _) =
    r1-fails {W = Wᶜ} (hasPP-conv ci (hp lh)) (lu (unb1-conv (conv-left ci) lh))
    where lh = unb1-lookup (int-left I)

  -- S against a core under the right check `X?`: THE CHECK FACT gives
  -- HP0 in the premise world
  no-S-chk : ∀ {V : World Δ Δ′} {γ Q μ′ X ℓ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → Core Q → WfWorld V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ Q ⟨ μ′ ∣ (` X) ？ ℓ ⟩ ∶ q)
  no-S-chk {V = V} core wf refl (⊑cast {κₚ = κₚ} {p = p} _ _ d ct q)
    with ct-X? ct
  ... | (_ , rh) , refl , refl =
    no-S-core core refl
      (λ lh → HasPP-chk {V = V} {κₚ = κₚ} wf lh rh q p) d
  no-S-chk core wf eA (⟪⟫⊑ _ _ _ _ d _ _) = no-$-chk d

  module Outer (Q : Term) (core : Core Q) where
    RinQ RQ : Term
    RinQ = Q ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩
    RQ   = RinQ ⟪ Θ₀ , unseal 0 ⟫

    -- a literal against RQ: its right type is ℕ
    rty-$RQ : ∀ {Δ₁} {V : World Δ₁ ΔL} {γ n A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
      → V ∣ γ ⊢ $ n ⊑ RQ ∶ q → A′ ≡ `ℕ
    rty-$RQ (⊑⟪⟫ _ _ _ _ b _) = proj₂ (bdy-C5 b)

    no-S-RQ : ∀ {Δ₁} {V : World Δ₁ ΔL} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
      → A ≡ ` 0 → ¬ (V ∣ γ ⊢ S ⊑ RQ ∶ q)
    no-S-RQ eA (⊑⟪⟫ _ _ wf d _ _) = no-S-chk core wf eA d
    no-S-RQ {V = V} refl (⟪⟫⊑ _ _ _ _ d _ q) with rty-$RQ d
    ... | refl = no-var⊑ℕ {V = V} q
    no-S-RQ eA (⟪⟫⊑⟪⟫ _ _ d _ _ _ _) = no-$-chk d

    no-L-RinQ : ∀ {Δ₂} {V : World ΔL Δ₂} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
      → ¬ (V ∣ γ ⊢ C5L ⊑ RinQ ∶ q)
    no-L-RinQ {V = V} (⊑cast _ _ d ct q) with ct-X? ct | lty-bdy d
    ... | _ , refl , refl | _ , _ , b with bdy-C5 b
    ...   | _ , refl = no-ℕ⊑var {V = V} q
    no-L-RinQ (⟪⟫⊑ _ _ _ wf d b _) = no-S-chk core wf (proj₁ (bdy-C5 b)) d

    -- THE TOP: every world over (ΔL, ΔL), any κ
    no-top : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ C5L ⊑ RQ ∶ q)
    no-top (⟪⟫⊑⟪⟫ _ wf d b _ _ _) = no-S-chk core wf (proj₁ (bdy-C5 b)) d
    no-top (⟪⟫⊑ _ _ _ _ d b _)    = no-S-RQ (proj₁ (bdy-C5 b)) d
    no-top (⊑⟪⟫ _ _ _ d _ _)      = no-L-RinQ d

  -- C5 IS UNRELATED (L state 3, R state 5), in every world, at any κ
  C5R-is : C5R ≡ Outer.RQ (5★ˣ) c-5
  C5R-is = refl

  c5-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ C5R ∶ q)
  c5-unrelated = Outer.no-top 5★ˣ c-5

  -- the failing redex `5⟨ℕ!⟩⟨X?⟩` against the left VALUE S (M26's shape)
  -- is unrelated in every well-formed world, at any κ
  c5-redex-unrelated : ∀ {Δ₁ Δ₂} {V : World Δ₁ Δ₂} {γ A A′}
      {q : A ⊑ᵂ⟨ V ⟩ A′}
    → WfWorld V → A ≡ ` 0
    → ¬ (V ∣ γ ⊢ S ⊑ 5★ˣ ⟨ ★∼X∼★ ∷ [] ∣ (` 0) ？ 0 ⟩ ∶ q)
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

  hidden-unrelated : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5L ⊑ RH ∶ q)
  hidden-unrelated = Outer.no-top Hid c-hid

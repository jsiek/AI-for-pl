module examples.TermImprecisionD32Examples where

-- File Charter:
--   * EXAMPLES FOR design.md D32 (adopted 2026-10-09; Jeremy approved
--     "updating Wrap and Merge"): a boundary that REBINDS a type
--     variable may permit it (`jr-rebind`), and a boundary that UNJOINS
--     a type variable may revoke its permission for its interior, paying
--     with its exterior index read without it (`Revoke`, `rv-drop`).
--     Each example is given from its source programs, with the real
--     relation (TermImprecision).
--       RB2.*     the Merge of a hide over a rejoin (both sides): the
--                 rejoins permit αᴿ; after the Merge the merged
--                 `[−X, +X]` boundaries make X CONTINUING, and every
--                 derivation of the merged pair at the TyBeta interior
--                 world (no permission) permits by a rebind
--                 (`post-uses-rebind`)
--       KW.*      κ-weakening: false in general (`kw-left-only`); at a
--                 joined type variable it needs a revocation
--                 (`kw-joined-uses-drop`); the right's Wrap moves a
--                 value whose seal sits under a λ into a rejoin that
--                 permits, and the moved pair is related only because
--                 the Wrap dual revokes (`post-uses-drop`)
--   * `UsesRebind d` / `UsesDrop d`: some boundary of the derivation d
--     permits by `jr-rebind` / revokes a permission (`rv-drop` with a
--     dropped rep. var).
--   * Every state that is not a source program is pinned to its
--     `evalTerms` state by `refl`.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; drop)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
import Data.List.Relation.Unary.AllPairs as AP
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

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
open import Reduction using (_⊢_-→*_; _⊢_-→_∣_)
open import proof.ImprecisionWorld
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms; stepTo)
open import Data.Maybe using (just)
open import examples.Examples using (ℓ; μX)
import examples.TermImprecisionExamples as TIE
import examples.TermImprecisionRebaseExamples as Rbs
import examples.TermImprecisionPermissionExamples as PE

------------------------------------------------------------------------
-- 0. Tools
------------------------------------------------------------------------

nth : List Term → ℕ → Term
nth []       _       = $ 0
nth (x ∷ xs) zero    = x
nth (x ∷ xs) (suc n) = nth xs n

-- some permission of the list is a rebind
AnyRebind : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ N K}
  → All (JoinRep Wᵢ Θ Θ′ N) K → Set
AnyRebind []                       = ⊥
AnyRebind (jr-join _ _ _ _ ∷ js)   = AnyRebind js
AnyRebind (jr-rebind _ _ _ _ ∷ js) = ⊤
AnyRebind (jr-open _ _ ∷ js)       = AnyRebind js

-- the revocation drops some rep. var
Drops : ∀ {P : RVar → Set} {κ κ₁} → Dropped P κ κ₁ → Set
Drops dr-[]        = ⊥
Drops (dr-keep d)  = Drops d
Drops (dr-drop _ d) = ⊤

DropsRv : ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {O A A′ κ₁}
  → Revoke W Wᵢ O A A′ κ₁ → Set
DropsRv rv-none       = ⊥
DropsRv (rv-drop d _) = Drops d

-- `UsesRebind d`, `UsesDrop d`: some boundary of d permits by a rebind
-- / revokes
UsesRebind UsesDrop : ∀ {Δ Δ′} {W : World Δ Δ′} {γ M M′ O A A′}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p → Set
UsesRebind (x⊑x _)                       = ⊥
UsesRebind (κ⊑κ _ _)                     = ⊥
UsesRebind (ƛ⊑ƛ _ _ d)                   = UsesRebind d
UsesRebind (·⊑· d e)                     = UsesRebind d ⊎ UsesRebind e
UsesRebind (blame⊑ _ _ _)                = ⊥
UsesRebind (cast⊑cast d _ _ _)           = UsesRebind d
UsesRebind (cast⊑ _ d _ _)               = UsesRebind d
UsesRebind (⊑cast d _ _)                 = UsesRebind d
UsesRebind (Λ⊑Λ _ _ _ d _)               = UsesRebind d
UsesRebind (Λ⊑ _ _ _ _ _ d _)            = UsesRebind d
UsesRebind (ν⊑ν d _ _ _ _ _)             = UsesRebind d
UsesRebind (ν⊑ d _ _ _)                  = UsesRebind d
UsesRebind (⟪⟫⊑⟪⟫ _ _ ks _ _ d _ _ _ _)  = AnyRebind ks ⊎ UsesRebind d
UsesRebind (⟪⟫⊑ _ _ _ _ ks _ _ d _ _)    = AnyRebind ks ⊎ UsesRebind d
UsesRebind (⊑⟪⟫ _ _ _ _ _ ks _ _ d _ _)  = AnyRebind ks ⊎ UsesRebind d

UsesDrop (x⊑x _)                         = ⊥
UsesDrop (κ⊑κ _ _)                       = ⊥
UsesDrop (ƛ⊑ƛ _ _ d)                     = UsesDrop d
UsesDrop (·⊑· d e)                       = UsesDrop d ⊎ UsesDrop e
UsesDrop (blame⊑ _ _ _)                  = ⊥
UsesDrop (cast⊑cast d _ _ _)             = UsesDrop d
UsesDrop (cast⊑ _ d _ _)                 = UsesDrop d
UsesDrop (⊑cast d _ _)                   = UsesDrop d
UsesDrop (Λ⊑Λ _ _ _ d _)                 = UsesDrop d
UsesDrop (Λ⊑ _ _ _ _ _ d _)              = UsesDrop d
UsesDrop (ν⊑ν d _ _ _ _ _)               = UsesDrop d
UsesDrop (ν⊑ d _ _ _)                    = UsesDrop d
UsesDrop (⟪⟫⊑⟪⟫ rv _ _ _ _ d _ _ _ _)    = DropsRv rv ⊎ UsesDrop d
UsesDrop (⟪⟫⊑ rv _ _ _ _ _ _ d _ _)      = DropsRv rv ⊎ UsesDrop d
UsesDrop (⊑⟪⟫ rv _ _ _ _ _ _ _ d _ _)    = DropsRv rv ⊎ UsesDrop d

------------------------------------------------------------------------
-- 1. RB2: a Merge turns a rejoin into a continuation under a permission
-- (design.md D32, jr-rebind).
--
-- Source programs (UNRELATED: under the matched ΛX the left's λy:X
-- faces the right's λy:★, and X ⋢ ★ at a type variable both sides
-- bind; the pair is related from the TyBeta on, `top5`):
--   L  (ΛX. λk:(X→ℕ)→X→ℕ. k (λy:X. 5))[ℕ] (λq:ℕ→ℕ. q) 7
--   R  (ΛX. λk:(X→ℕ)→X→ℕ. k ((λy:★. 5) : X→ℕ))[ℕ] (λq:ℕ→ℕ. q) 7
-- Both runs: TyBeta Wrap Beta Wrap Beta Merge Merge Wrap … (lockstep to
-- state 7).  State 5 has, inside the TyBeta boundary, the hide of k's
-- Wrap over the rejoin of its argument's Wrap dual; state 6 merges them
-- into `[−X^α, +X^α]`, where X CONTINUES.
------------------------------------------------------------------------

module RB2 where
  open PE.P4 using (Ξ₄; ϱ₄; W₄; W₄²; W₄²¹; W₄⁰; W₄⁰-wf; W₄²-wf; W₄²¹-wf;
                    v₀; unb₀; unb-int; unb-conv)
  open Rbs using (Wc-bind²; Wc-bind²-conv; jr₀; Θ⁻⁺; Θ⁻⁺-int; Θ⁻⁺-conv)
  open TIE using (ΔL; ΔLᵢ; Θ₀)

  Fk : Ty
  Fk = ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)) ⇒ (` 0 ⇒ `ℕ)

  tagX↦ : Coercion
  tagX↦ = ((` 0) !) ↦ᵖ idᵖ `ℕ

  FL FR K L R : Term
  FL = Λ (ƛ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)) ∙ (` 0 · (ƛ (` 0) ∙ $ 5)))
  FR = Λ (ƛ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)) ∙
         (` 0 · ((ƛ ★ ∙ $ 5) ⟨ μX ∣ tagX↦ ⟩)))
  K  = ƛ (`ℕ ⇒ `ℕ) ∙ ` 0
  L  = ((ν `ℕ · FL ⟨ reveal 0 Fk ⟩) · K) · $ 7
  R  = ((ν `ℕ · FR ⟨ reveal 0 Fk ⟩) · K) · $ 7

  L-⊢ : empty ∣ [] ⊢ L ⦂ `ℕ
  L-⊢ = tc

  R-⊢ : empty ∣ [] ⊢ R ⦂ `ℕ
  R-⊢ = tc

  -- the conversions `−X → id(ℕ)`, `+X → id(ℕ)`, `id(X) → id(ℕ)`
  cS cU cI : Conv
  cS = tail (mid (tail (seal 0) ↦ tail (mid (id `ℕ))))
  cU = tail (mid (unseal 0 ↦ tail (mid (id `ℕ))))
  cI = tail (mid (tail (mid (id (` 0))) ↦ tail (mid (id `ℕ))))

  -- the argument functions: λy:X. 5 and (λy:★. 5)⟨X! → id(ℕ)⟩
  Lv Rv : Term
  Lv = ƛ (` 0) ∙ $ 5
  Rv = (ƛ ★ ∙ $ 5) ⟨ μX ∣ tagX↦ ⟩

  -- inside the TyBeta boundary: before the Merge (hide over rejoin) and
  -- after it (the merged `[−X, +X]`, Θ⁻⁺)
  pre post : Term → Term
  pre  v = (v ⟪ Θ₀ , cS ⟫) ⟪ unb₀ , cU ⟫
  post v = v ⟪ Θ⁻⁺ , cI ⟫

  top : Term → Term
  top m = (m ⟪ Θ₀ , cS ⟫) · $ 7

  L5 : nth (evalTerms 20 L-⊢) 5 ≡ top (pre Lv)
  L5 = refl

  R5 : nth (evalTerms 20 R-⊢) 5 ≡ top (pre Rv)
  R5 = refl

  L6 : nth (evalTerms 20 L-⊢) 6 ≡ top (post Lv)
  L6 = refl

  R6 : nth (evalTerms 20 R-⊢) 6 ≡ top (post Rv)
  R6 = refl

  ---------------------------------------------------------------------
  -- typings read off `tc`

  bdy : ∀ {Δ M Θ c B} → Δ ∣ [] ⊢ M ⟪ Θ , c ⟫ ⦂ B
    → Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Bᵢ ∈ Ty ] BdyTy Δ Θ Δᵢ Bᵢ c B
  bdy ⊢M with ⟪⟫-inv {Γ = []} ⊢M
  ... | Δᵢ , Bᵢ , _ , b = Δᵢ , Bᵢ , b

  bJL : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bJL = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = Lv ⟪ Θ₀ , cS ⟫})))

  bJR : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bJR = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = Rv ⟪ Θ₀ , cS ⟫})))

  bHL : BdyTy ΔLᵢ unb₀ ΔL (`ℕ ⇒ `ℕ) cU (` 0 ⇒ `ℕ)
  bHL = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = pre Lv})))

  bHR : BdyTy ΔLᵢ unb₀ ΔL (`ℕ ⇒ `ℕ) cU (` 0 ⇒ `ℕ)
  bHR = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = pre Rv})))

  bML : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0 ⇒ `ℕ) cI (` 0 ⇒ `ℕ)
  bML = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = post Lv})))

  bMR : BdyTy ΔLᵢ Θ⁻⁺ ΔLᵢ (` 0 ⇒ `ℕ) cI (` 0 ⇒ `ℕ)
  bMR = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = post Rv})))

  bTL : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bTL = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = pre Lv ⟪ Θ₀ , cS ⟫})))

  bTR : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bTR = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = pre Rv ⟪ Θ₀ , cS ⟫})))

  tag-ty : CastTy ΔLᵢ μX tagX↦ (★ ⇒ `ℕ) (` 0 ⇒ `ℕ)
  tag-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Rv})))

  ---------------------------------------------------------------------
  -- the argument functions, at the permitted joined X (W₄²¹)

  ℕ⊑ℕ : ∀ {Δ Δ′} {W : World Δ Δ′} → `ℕ ⊑ᵂ⟨ W ⟩ `ℕ
  ℕ⊑ℕ = ι⊑ι base-ℕ

  X→ℕ : ∀ κ → (` 0 ⇒ `ℕ) ⊑ᵂ⟨ Rbs.Wc² {Ξ₄} {ϱ₄} κ 0 ⟩ (` 0 ⇒ `ℕ)
  X→ℕ κ = ⇒⊑⇒ (X⊑X {X = 0}) (ι⊑ι base-ℕ)

  Lv⊑Rv : W₄²¹ ∣ [] ⊢ Lv ⊑ Rv ∶ X→ℕ (0 ∷ [])
  Lv⊑Rv = ⊑cast (ƛ⊑ƛ {pA = X⊑★ here} {pB = ι⊑ι base-ℕ} tf tf
                   (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
            tag-ty (X→ℕ (0 ∷ []))

  -- the conversions agree (`−X ⊑ −X`, `+X ⊑ +X`, `id(X) ⊑ id(X)`)
  cS⊑ : ∀ {κ} → ConvImp (Rbs.Wc² {Ξ₄} {ϱ₄} κ 0) cS cS
  cS⊑ = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
          (conv-tail⊑tail (conv-seal⊑seal refl))
          (conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))))

  cU⊑ : ∀ {κ} → ConvImp (Rbs.Wc² {Ξ₄} {ϱ₄} κ 0) cU cU
  cU⊑ = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
          (conv-unseal⊑unseal refl)
          (conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))))

  cI⊑ : ∀ {κ} → ConvImp (Rbs.Wc² {Ξ₄} {ϱ₄} κ 0) cI cI
  cI⊑ = conv-tail⊑tail (conv-mid⊑mid (conv-↦⊑↦
          (conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (X⊑X {X = 0}))))
          (conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))))

  ---------------------------------------------------------------------
  -- BEFORE the Merge, at the TyBeta interior with NO permission (W₄²):
  -- the matched hides, then the matched REJOINS, which join their fresh
  -- pair through ϱ and permit αᴿ (K = [0], `jr₀`, paying X→ℕ ⊑ X→ℕ)

  pre⊑ : W₄² ∣ [] ⊢ pre Lv ⊑ pre Rv ∶ X→ℕ []
  pre⊑ =
    ⟪⟫⊑⟪⟫ rv-none unb-int [] (W₄⁰-wf []) (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ))
      (⟪⟫⊑⟪⟫ rv-none (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf (X→ℕ [])
        Lv⊑Rv bJL bJR (W₄² , Wc-bind²-conv v₀ here⇔ , cS⊑)
        (⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)))
      bHL bHR (W₄² , unb-conv , cU⊑) (X→ℕ [])

  ---------------------------------------------------------------------
  -- AFTER the Merge: `[−X, +X]` on both sides, X continuing and joined
  -- (`IntM`); the merged boundaries REBIND X (Θ⁻⁺ unbinds and binds rep.
  -- var 0), so they may permit αᴿ (`jr-rebind`, design.md D32), paying
  -- X→ℕ ⊑ X→ℕ at W₄²

  IntM : Interior W₄² Θ⁻⁺ Θ⁻⁺ W₄²
  IntM = record
    { int-left   = Θ⁻⁺-int
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

  ConvM : ConversionInterior W₄² Θ⁻⁺ Θ⁻⁺ W₄²
  ConvM = record
    { conv-left       = Θ⁻⁺-conv
    ; conv-right      = Θ⁻⁺-conv
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

  -- the rebind permission
  jrM : JoinRep W₄² Θ⁻⁺ Θ⁻⁺ [] 0
  jrM = jr-rebind (_ , here) here (inj₂ (iu-there iu-here , ib-here)) refl

  post⊑ : W₄² ∣ [] ⊢ post Lv ⊑ post Rv ∶ X→ℕ []
  post⊑ =
    ⟪⟫⊑⟪⟫ rv-none IntM (jrM ∷ []) W₄²¹-wf (X→ℕ []) Lv⊑Rv bML bMR
      (W₄² , ConvM , cI⊑) (X→ℕ [])

  ---------------------------------------------------------------------
  -- The whole states 5 and 6, at the top-level world W₄ (both TyBetas
  -- done, no permission): the TyBeta boundaries permit nothing (K = []),
  -- the permission is the rejoins' (state 5) or the rebinds' (state 6)

  ℕ→ℕ : ∀ {Δ Δ′} {W : World Δ Δ′} → (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ `ℕ)
  ℕ→ℕ = ⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)

  top⊑ : ∀ {m m′} → W₄² ∣ [] ⊢ m ⊑ m′ ∶ X→ℕ []
    → (b : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ))
    → (b′ : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ))
    → BdyConversionImp W₄ b b′
    → W₄ ∣ [] ⊢ top m ⊑ top m′ ∶ ι⊑ι base-ℕ
  top⊑ d b b′ bc =
    ·⊑· (⟪⟫⊑⟪⟫ rv-none (Wc-bind² v₀ here⇔) [] W₄²-wf (X→ℕ []) d b b′ bc
          (ℕ→ℕ {W = W₄}))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  top5 : W₄ ∣ [] ⊢ top (pre Lv) ⊑ top (pre Rv) ∶ ι⊑ι base-ℕ
  top5 = top⊑ pre⊑ bTL bTR (W₄² , Wc-bind²-conv v₀ here⇔ , cS⊑)

  bTL6 : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bTL6 = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = post Lv ⟪ Θ₀ , cS ⟫})))

  bTR6 : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bTR6 = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = post Rv ⟪ Θ₀ , cS ⟫})))

  top6 : W₄ ∣ [] ⊢ top (post Lv) ⊑ top (post Rv) ∶ ι⊑ι base-ℕ
  top6 = top⊑ post⊑ bTL6 bTR6 (W₄² , Wc-bind²-conv v₀ here⇔ , cS⊑)

  ---------------------------------------------------------------------
  -- WITHOUT A REBIND THE MERGED PAIR IS UNRELATED at the TyBeta
  -- interior with no permission: every derivation of
  -- `post Lv ⊑ post Rv` at any world in which X is joined and nothing
  -- is permitted (e.g. W₄²) permits by a rebind.  The merged boundaries
  -- continue X on both sides, so `jr-join` (a FRESH type variable) and
  -- `jr-open` (a new opening) do not apply; with K = [] the inner
  -- `λy:X. 5 ⊑ (λy:★. 5)⟨X! → id(ℕ)⟩` needs X ⊑ ★ at the joined,
  -- unpermitted X.

  data LeftT : Term → Set where
    l-v : LeftT Lv
    l-m : LeftT (post Lv)

  data RightT : Term → Set where
    r-v : RightT Rv
    r-m : RightT (post Rv)

  -- the right's cast `X! → id(ℕ)`: its source is ★→ℕ
  ct-tag↦ : ∀ {Δ μ B A} → CastTy Δ μ tagX↦ B A → B ≡ ★ ⇒ `ℕ
  ct-tag↦ (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-tag↦ (cast-ty (⊢fun (⊢tag-var _ _ _) (⊢id _ _)) _) = refl

  -- X→ℕ ⊑ ★→ℕ at a joined, unpermitted X
  dead-idx : ∀ {V : World ΔLᵢ ΔLᵢ} {O}
    → κʷ V ≡ [] → Joins V 0 0
    → ¬ ((` 0 ⇒ `ℕ) ⊑ᵂ⟨ V ⟩[ O ] (★ ⇒ `ℕ))
  dead-idx {V = V} {O} eκ j p
    with PE.plain-idx {V = V} {O = O} {A = ` 0 ⇒ `ℕ} {A′ = ★ ⇒ `ℕ}
           PE.nf-⇒ p
  ... | ⇒⊑⇒ p₁ _ = PE.no-tag★ {V = V} eκ here j (PE.var⊑★ p₁)

  no-fresh : ∀ {X} → ΔLᵢ ∋tv X → ¬ (Fresh Θ⁻⁺ X)
  no-fresh (_ , here) ()
  no-fresh (_ , there ())

  no-fresh[] : ∀ {X} → ¬ (Fresh [] X)
  no-fresh[] ()

  ∋ᵒ-fresh : ∀ {Θ′ M N k} → N ∋ᵒ k → All (NewSlot Θ′ M) N → Fresh Θ′ k
  ∋ᵒ-fresh oh     (ns-opn f ∷ _) = f
  ∋ᵒ-fresh (ot n) (_ ∷ ns)       = ∋ᵒ-fresh n ns

  nfR : ∀ {X X′ β} → ΔLᵢ ∋tv X → ΔLᵢ ∋ᵗ X′ := β
    → ¬ (Fresh [] X ⊎ Fresh Θ⁻⁺ X′)
  nfR _ here (inj₁ ())
  nfR _ here (inj₂ ())
  nfR _ (there ()) _

  nfL : ∀ {X X′ β} → ΔLᵢ ∋tv X → ΔLᵢ ∋ᵗ X′ := β
    → ¬ (Fresh Θ⁻⁺ X ⊎ Fresh [] X′)
  nfL (_ , here) _ (inj₁ ())
  nfL (_ , here) _ (inj₂ ())
  nfL (_ , there ()) _ _

  nf² : ∀ {X X′ β} → ΔLᵢ ∋tv X → ΔLᵢ ∋ᵗ X′ := β
    → ¬ (Fresh Θ⁻⁺ X ⊎ Fresh Θ⁻⁺ X′)
  nf² (_ , here) _ (inj₁ ())
  nf² _ here (inj₂ ())
  nf² (_ , there ()) _ _

  noN : ∀ {M N k β} → All (NewSlot Θ⁻⁺ M) N → N ∋ᵒ k → ΔLᵢ ∋ᵗ k := β → ⊥
  noN ns n here = no-fresh (_ , here) (∋ᵒ-fresh n ns)
  noN ns n (there ())

  push-new : ∀ {Θ′ M O N Oᵢ} → Push Θ′ M O N Oᵢ → All (NewSlot Θ′ M) N
  push-new (push _ _ ns _) = ns

  -- with no fresh type variable and no new opening, a permission is a
  -- rebind
  rb-or-empty : ∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ N K}
    → (∀ {X X′ β} → Δᵢ ∋tv X → Δ′ᵢ ∋ᵗ X′ := β → ¬ (Fresh Θ X ⊎ Fresh Θ′ X′))
    → (∀ {k β} → N ∋ᵒ k → Δ′ᵢ ∋ᵗ k := β → ⊥)
    → (ks : All (JoinRep Wᵢ Θ Θ′ N) K) → AnyRebind ks ⊎ K ≡ []
  rb-or-empty nf no []                         = inj₂ refl
  rb-or-empty nf no (jr-join tv rh fr _ ∷ _)   = ⊥-elim (nf tv rh fr)
  rb-or-empty nf no (jr-rebind _ _ _ _ ∷ _)    = inj₁ tt
  rb-or-empty nf no (jr-open n rh ∷ _)         = ⊥-elim (no n rh)

  -- the left's type
  ty-Lv : ∀ {Δ Γ A} → Δ ∣ Γ ⊢ Lv ⦂ A → A ≡ ` 0 ⇒ `ℕ
  ty-Lv (⊢ƛ _ ⊢$) = refl

  needs : ∀ {V : World ΔLᵢ ΔLᵢ} {γ M M′ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → κʷ V ≡ [] → Joins V 0 0 → LeftT M → RightT M′ → A ≡ ` 0 ⇒ `ℕ
    → (d : V ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q) → UsesRebind d
  needs {V = V} {O = O} eκ j l-v r-v refl (⊑cast {p = p} _ ct _)
    with ct-tag↦ ct
  ... | refl = ⊥-elim (dead-idx {V = V} {O = O} eκ j p)
  needs {V = V} {O = O} eκ j l-m r-v refl (⊑cast {p = p} _ ct _)
    with ct-tag↦ ct
  ... | refl = ⊥-elim (dead-idx {V = V} {O = O} eκ j p)
  needs {V = V} eκ j l-v r-m eA
    (⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Vi} {κ₁ = κ₁} rv I pu so sn ks wi pay d b′ q)
    with interior-functional (int-right I) Θ⁻⁺-int
  ... | refl
    with rb-or-empty nfR (noN (push-new pu)) ks
  ... | inj₁ a = inj₁ a
  ... | inj₂ refl =
    inj₂ (needs (revoke-[] rv (trans (same-κ I) eκ))
            (proj₂ (join-cont I (_ , here) (_ , here) refl refl) j)
            l-v r-v eA d)
  needs {V = V} eκ j l-m r-v refl
    (⟪⟫⊑ {Δᵢ = Δᵢ} {Wᵢ = Vi} rv I ok bo ks wi pay d b q)
    with interior-functional (int-left I) Θ⁻⁺-int
  ... | refl
    with rb-or-empty nfL (λ ()) ks
  ... | inj₁ a = inj₁ a
  ... | inj₂ refl =
    inj₂ (needs (revoke-[] rv (trans (same-κ I) eκ))
            (proj₂ (join-cont I (_ , here) (_ , here) refl refl) j)
            l-v r-v (ty-Lv (PE.ltyD d)) d)
  needs {V = V} eκ j l-m r-m eA
    (⟪⟫⊑⟪⟫ {Δᵢ = Δᵢ} {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Vi} rv I ks wi pay d b b′ bc q)
    with interior-functional (int-left I) Θ⁻⁺-int
       | interior-functional (int-right I) Θ⁻⁺-int
  ... | refl | refl
    with rb-or-empty nf² (λ ()) ks
  ... | inj₁ a = inj₁ a
  ... | inj₂ refl =
    inj₂ (needs (revoke-[] rv (trans (same-κ I) eκ))
            (proj₂ (join-cont I (_ , here) (_ , here) refl refl) j)
            l-v r-v (ty-Lv (PE.ltyD d)) d)
  needs eκ j l-m r-m eA (⟪⟫⊑ {Δᵢ = Δᵢ} rv I ok bo ks wi pay d b q)
    with interior-functional (int-left I) Θ⁻⁺-int
  ... | refl
    with rb-or-empty nfL (λ ()) ks
  ... | inj₁ a = inj₁ a
  ... | inj₂ refl =
    inj₂ (needs (revoke-[] rv (trans (same-κ I) eκ))
            (proj₂ (join-cont I (_ , here) (_ , here) refl refl) j)
            l-v r-m (ty-Lv (PE.ltyD d)) d)
  needs eκ j l-m r-m eA
    (⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Vi} rv I pu so sn ks wi pay d b′ q)
    with interior-functional (int-right I) Θ⁻⁺-int
  ... | refl
    with rb-or-empty nfR (noN (push-new pu)) ks
  ... | inj₁ a = inj₁ a
  ... | inj₂ refl =
    inj₂ (needs (revoke-[] rv (trans (same-κ I) eκ))
            (proj₂ (join-cont I (_ , here) (_ , here) refl refl) j)
            l-m r-v eA d)

  -- THE CLAIM: at W₄² (X joined, no permission) every derivation of the
  -- merged pair permits by a rebind (design.md D32)
  post-uses-rebind : ∀ {γ O} {q : (` 0 ⇒ `ℕ) ⊑ᵂ⟨ W₄² ⟩[ O ] (` 0 ⇒ `ℕ)}
    → (d : W₄² ∣ γ ⊢ post Lv ⊑ post Rv ∶⟨ ` 0 ⇒ `ℕ , ` 0 ⇒ `ℕ ⟩[ O ] q)
    → UsesRebind d
  post-uses-rebind = needs {V = W₄²} refl refl l-m r-m refl

------------------------------------------------------------------------
-- 2. KW: κ-weakening and the Wrap dual (design.md D32, revocation).
-- No source program reaches these worlds as far as we know; they are
-- related pairs of cast terms at worlds Sim and SimBack are stated for
-- (well formed, κʷ ≡ []).
--
-- The left allocated α:=ℕ, the right αᴿ:=★ (rep. var 0 on each side),
-- paired globally (CgB1's ϱ).  `Wcᴸ κ`: the left's X (bound to α) is in
-- scope and LEFT-ONLY (the right hid it); `Wc² κ 0`: X is joined to the
-- right's X (bound to αᴿ).  κ is the permitted right rep. vars.
------------------------------------------------------------------------

module KW where
  open PE.CgB1 using (Ξg; ϱg; Wg²-wf; Wgᴴ-wf)
  open PE.P4 using (S; unb₀)
  open PE.C5Dead using (no-S-5)
  open Rbs using (Wc²; Wcᴸ; Wc-bindᴿ; Wc-unbindᴿ; jrR; p0)
  open TIE using (ΔL; ΔLᵢ; Θ₀)

  ΔR ΔRᵢ : Ctxᵗ
  ΔR  = Ξg ∣ []
  ΔRᵢ = Ξg ∣ (0 ∷ [])

  -- X left-only / joined, at permissions κ
  Wh : List RVar → World ΔLᵢ ΔR
  Wh κ = Wcᴸ {Ξg} {ϱg} κ

  Wj : List RVar → World ΔLᵢ ΔRᵢ
  Wj κ = Wc² {Ξg} {ϱg} κ 0

  module Wf {nsL nsR : TyCtx} (n : ℕ)
      (η : nsL ↪ n) (η′ : nsR ↪ n) (κ : List RVar) where
    W : World ((bindR `ℕ ∷ []) ∣ nsL) (Ξg ∣ nsR)
    W = world n η η′ ϱg [] κ

    agree : ∀ {α β} → Paired W α β → Agree W α β
    agree (inj₁ here⇔) = rep-rep r-here r-here (ι⊑★ base-ℕ)
    agree (inj₁ (there⇔ ()))
    agree (inj₂ ())

  Wh-wf : ∀ {κ} → All (Ξg ∋ʳ_) κ → WfWorld (Wh κ)
  Wh-wf {κ} ps = wf-world (left-only joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-[]) ps
    where open Wf 1 (keep []↪) (skip []↪) κ

  Wj-wf : ∀ {κ} → All (Ξg ∋ʳ_) κ → WfWorld (Wj κ)
  Wj-wf {κ} ps = wf-world (both (inj₁ here⇔) joint[]) agree
    (namedᴸ-≤1 W ≤1-∷[]) (namedᴿ-≤1 W ≤1-∷[]) ps
    where open Wf 1 (keep []↪) (keep []↪) κ

  W⁰-wf : ∀ {κ} → All (Ξg ∋ʳ_) κ
    → WfWorld (world⁰ {Δ = ΔL} {Δ′ = ΔR} 0 []↪ []↪ ϱg [] ⇂κ κ)
  W⁰-wf {κ} ps = wf-world joint[] agree
    (namedᴸ-≤1 W ≤1-[]) (namedᴿ-≤1 W ≤1-[]) ps
    where open Wf 0 []↪ []↪ κ

  v₀ : Ξg ∋ʳ 0
  v₀ = _ , here

  ---------------------------------------------------------------------
  -- the terms

  n★ Wv Wv′ Hd V V′ F′ : Term
  n★  = $ 5 ⟨ [] ∣ `ℕ ! ⟩
  Wv  = ƛ `ℕ ∙ S                     -- λy:ℕ. [−X^α] 5 ⟨−X⟩
  Wv′ = ƛ `ℕ ∙ n★                    -- λy:ℕ. 5⟨ℕ!⟩
  V   = ƛ (`ℕ ⇒ ` 0) ∙ $ 7            -- λf:ℕ→X. 7

  -- `id(ℕ) → −X` and `(id(ℕ) → −X) → id(ℕ)`
  cH cF : Conv
  cH = tail (mid (tail (mid (id `ℕ)) ↦ tail (seal 0)))
  cF = tail (mid (cH ↦ tail (mid (id `ℕ))))

  tagF : Coercion
  tagF = (idᵖ `ℕ ↦ᵖ ((` 0) !)) ↦ᵖ idᵖ `ℕ

  Hd = Wv′ ⟪ unb₀ , cH ⟫              -- [−X^αᴿ] (λy:ℕ. 5⟨ℕ!⟩) ⟨id(ℕ) → −X⟩
  V′ = (ƛ (`ℕ ⇒ ★) ∙ $ 7) ⟨ μX ∣ tagF ⟩ -- (λf:ℕ→★. 7)⟨(id(ℕ) → X!) → id(ℕ)⟩
  F′ = V′ ⟪ Θ₀ , cF ⟫                 -- [+X^αᴿ] V′ ⟨(id(ℕ) → −X) → id(ℕ)⟩

  -- the right's Wrap: its argument goes inside the rejoin, under the
  -- dual `[−X^αᴿ]`, which is Hd
  wrap-step : stepTo ΔR (F′ · Wv′) ≡ just ((V′ · Hd) ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫)
  wrap-step = refl

  ---------------------------------------------------------------------
  -- typings read off `tc`

  bS : BdyTy ΔLᵢ unb₀ ΔL `ℕ (tail (seal 0)) (` 0)
  bS = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = S}))))

  bHd : BdyTy ΔRᵢ unb₀ ΔR (`ℕ ⇒ ★) cH (`ℕ ⇒ ` 0)
  bHd = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = Hd}))))

  bF′ : BdyTy ΔR Θ₀ ΔRᵢ ((`ℕ ⇒ ` 0) ⇒ `ℕ) cF ((`ℕ ⇒ ★) ⇒ `ℕ)
  bF′ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = F′}))))

  bPost : BdyTy ΔR Θ₀ ΔRᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bPost = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔR} {M = (V′ · Hd) ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫}))))

  ctℕ! : CastTy ΔR [] (`ℕ !) `ℕ ★
  ctℕ! = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = n★})))

  ctF : CastTy ΔRᵢ μX tagF ((`ℕ ⇒ ★) ⇒ `ℕ) ((`ℕ ⇒ ` 0) ⇒ `ℕ)
  ctF = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = V′})))

  ---------------------------------------------------------------------
  -- the seal against 5⟨ℕ!⟩ where X is left-only and α's partner αᴿ is
  -- NOT permitted: a one-sided left unbind (R1′, `ok-unbind`)

  IntS : ∀ {κ} → Interior (Wh κ) unb₀ []
    (world⁰ {Δ = ΔL} {Δ′ = ΔR} 0 []↪ []↪ ϱg [] ⇂κ κ)
  IntS = record
    { int-left   = Rbs.unbind₀-int
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  S⊑n★ : ∀ {γ} → Wh [] ∣ γ ⊢ S ⊑ n★ ∶ X⊑★ here
  S⊑n★ =
    ⟪⟫⊑₀ IntS (ok-unbind (λ _ → refl) ∷ []) (W⁰-wf [])
      (⊑cast (κ⊑κ lit-$ (ι⊑ι base-ℕ)) ctℕ! (ι⊑★ base-ℕ)) bS (X⊑★ here)

  -- (a) UNRESTRICTED κ-WEAKENING IS FALSE: the pair is related at Wh []
  -- and unrelated at Wh [0] = Wh [] +κ [αᴿ] (R1′ rejects the seal, and
  -- `ℕ ⊑ X` the ⊑cast route: C5's argument, `no-S-5`)
  hp-h : ∀ {α} → ΔLᵢ ∋ᵗ 0 := α → HasPermittedPartner (Wh (0 ∷ [])) α
  hp-h here = 0 , inj₁ here⇔ , refl

  kw-left-only : ∀ {γ O A′} {q : ` 0 ⊑ᵂ⟨ Wh (0 ∷ []) ⟩[ O ] A′}
    → ¬ (Wh (0 ∷ []) ∣ γ ⊢ S ⊑ n★ ∶⟨ ` 0 , A′ ⟩[ O ] q)
  kw-left-only = no-S-5 refl hp-h

  ---------------------------------------------------------------------
  -- (b) AT A JOINED X the weakening needs a REVOCATION: the right hides
  -- X around a λ whose body is the right's half of (a).  At Wj [] the
  -- hide revokes nothing; at Wj [0] (αᴿ permitted) it revokes αᴿ and
  -- pays with its exterior index ℕ→X ⊑ ℕ→X read at Wj [] (D32)

  ℕ→X : ∀ κ → (`ℕ ⇒ ` 0) ⊑ᵂ⟨ Wj κ ⟩ (`ℕ ⇒ ` 0)
  ℕ→X κ = ⇒⊑⇒ (ι⊑ι base-ℕ) (X⊑X {X = 0})

  Wv⊑Wv′ : Wh [] ∣ [] ⊢ Wv ⊑ Wv′ ∶ ⇒⊑⇒ (ι⊑ι base-ℕ) (X⊑★ here)
  Wv⊑Wv′ = ƛ⊑ƛ tf tf S⊑n★

  Wv⊑Hd⁰ : Wj [] ∣ [] ⊢ Wv ⊑ Hd ∶ ℕ→X []
  Wv⊑Hd⁰ = ⊑⟪⟫₀ (Wc-unbindᴿ v₀) (Wh-wf []) Wv⊑Wv′ bHd (ℕ→X [])

  -- the right hide unjoins X (αᴿ is no longer bound inside)
  unj : Unjoins (Wj (0 ∷ [])) (Wh (0 ∷ [])) 0
  unj = unjoin here here refl (inj₂ (λ { (_ , ()) }))

  Wv⊑Hd¹ : Wj (0 ∷ []) ∣ [] ⊢ Wv ⊑ Hd ∶ ℕ→X (0 ∷ [])
  Wv⊑Hd¹ =
    ⊑⟪⟫ (rv-drop (dr-drop unj dr-[]) (ℕ→X [])) (Wc-unbindᴿ v₀) push-none
      [] AP.[] [] (Wh-wf []) (⇒⊑⇒ (ι⊑ι base-ℕ) (X⊑★ here)) Wv⊑Wv′ bHd
      (ℕ→X (0 ∷ []))

  -- ... and WITHOUT the revocation it is unrelated: at any world where X
  -- is joined to the right's X and αᴿ is permitted, every derivation
  -- revokes (inside the hide the seal would face 5⟨ℕ!⟩ with α's partner
  -- permitted: R1′, C5's argument)
  drops-or-same : ∀ {P : RVar → Set} {κ κ₁} (d : Dropped P κ κ₁)
    → Drops d ⊎ κ₁ ≡ κ
  drops-or-same dr-[]        = inj₂ refl
  drops-or-same (dr-drop _ _) = inj₁ tt
  drops-or-same {κ = β ∷ _} (dr-keep d) with drops-or-same d
  ... | inj₁ x = inj₁ x
  ... | inj₂ refl = inj₂ refl

  rv-same : ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {O A A′ κ₁}
    → (rv : Revoke W Wᵢ O A A′ κ₁) → DropsRv rv ⊎ κ₁ ≡ κʷ Wᵢ
  rv-same rv-none       = inj₂ refl
  rv-same (rv-drop d _) = drops-or-same d

  unb-intR : ΔRᵢ ⊢ⁱ unb₀ ⇒ ΔR
  unb-intR = interior (changes∷ changes[] (step-unbind v₀ del-here fresh[]))

  -- the hide's interior has no right type variable: it permits nothing
  K-hide : ∀ {Wᵢ : World ΔLᵢ ΔR} {N K} → All (JoinRep Wᵢ [] unb₀ N) K
    → K ≡ []
  K-hide []                          = refl
  K-hide (jr-join _ () _ _ ∷ _)
  K-hide (jr-rebind _ () _ _ ∷ _)
  K-hide (jr-open _ () ∷ _)

  joined-uses-drop : ∀ {U : World ΔLᵢ ΔRᵢ} {γ O A′}
      {q : (`ℕ ⇒ ` 0) ⊑ᵂ⟨ U ⟩[ O ] A′}
    → Paired U 0 0 → permit 0 (κʷ U) ≡ X⊑★
    → (d : U ∣ γ ⊢ Wv ⊑ Hd ∶⟨ `ℕ ⇒ ` 0 , A′ ⟩[ O ] q) → UsesDrop d
  joined-uses-drop {U = U} pr pm
    (⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Ui} {κ₁ = κ₁} rv I pu so sn ks wi pay d b′ q)
    with interior-functional (int-right I) unb-intR
  ... | refl with K-hide ks
  ... | refl with rv-same rv
  ... | inj₁ x = inj₁ x
  ... | inj₂ eq = ⊥-elim (inner d)
    where
    pm′ : permit 0 κ₁ ≡ X⊑★
    pm′ = subst (λ κ → permit 0 κ ≡ X⊑★) (sym (trans eq (same-κ I))) pm
    hp : ∀ {α} → ΔLᵢ ∋ᵗ 0 := α
      → HasPermittedPartner (Ui ⇂κ κ₁ +κ []) α
    hp here = 0 , Paired-int I pr , pm′
    inner : ∀ {γ′ O′ A″} {r : (`ℕ ⇒ ` 0) ⊑ᵂ⟨ Ui ⇂κ κ₁ +κ [] ⟩[ O′ ] A″}
      → ¬ (Ui ⇂κ κ₁ +κ [] ∣ γ′ ⊢ Wv ⊑ Wv′ ∶⟨ `ℕ ⇒ ` 0 , A″ ⟩[ O′ ] r)
    inner (ƛ⊑ƛ _ _ body) = no-S-5 refl hp body

  -- (b) at Wj [0]
  kw-joined-uses-drop : ∀ {γ O A′} {q : (`ℕ ⇒ ` 0) ⊑ᵂ⟨ Wj (0 ∷ []) ⟩[ O ] A′}
    → (d : Wj (0 ∷ []) ∣ γ ⊢ Wv ⊑ Hd ∶⟨ `ℕ ⇒ ` 0 , A′ ⟩[ O ] q)
    → UsesDrop d
  kw-joined-uses-drop = joined-uses-drop (inj₁ here⇔) refl

  ---------------------------------------------------------------------
  -- (c) THE WRAP.  At Wh [] (X left-only, nothing permitted) the left
  -- applies λf:ℕ→X. 7 to Wv; the right applies its rejoin F′ to Wv′.
  -- The rejoin joins X and permits αᴿ (paying (ℕ→X)→ℕ ⊑ (ℕ→X)→ℕ), so
  -- inside it V′'s `X!` is peeled at X ⊑ ★.  The right's Wrap moves Wv′
  -- inside the rejoin, under the dual `[−X^αᴿ]` (= Hd): the moved pair
  -- is (b)'s, and it is related only because the dual revokes αᴿ.

  ℕ→X⊑ℕ→★ : ∀ κ → ((`ℕ ⇒ ` 0) ⇒ `ℕ) ⊑ᵂ⟨ Wh κ ⟩ ((`ℕ ⇒ ★) ⇒ `ℕ)
  ℕ→X⊑ℕ→★ κ = ⇒⊑⇒ (⇒⊑⇒ (ι⊑ι base-ℕ) (X⊑★ here)) (ι⊑ι base-ℕ)

  F⊑F : ∀ κ → ((`ℕ ⇒ ` 0) ⇒ `ℕ) ⊑ᵂ⟨ Wj κ ⟩ ((`ℕ ⇒ ` 0) ⇒ `ℕ)
  F⊑F κ = ⇒⊑⇒ (ℕ→X κ) (ι⊑ι base-ℕ)

  V⊑V′ : Wj (0 ∷ []) ∣ [] ⊢ V ⊑ V′ ∶ F⊑F (0 ∷ [])
  V⊑V′ = ⊑cast (ƛ⊑ƛ {pA = ⇒⊑⇒ (ι⊑ι base-ℕ) (X⊑★ here)} {pB = ι⊑ι base-ℕ}
                  tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
           ctF (F⊑F (0 ∷ []))

  V⊑F′ : Wh [] ∣ [] ⊢ V ⊑ F′ ∶ ℕ→X⊑ℕ→★ []
  V⊑F′ = ⊑⟪⟫ rv-none (Wc-bindᴿ v₀ here⇔) push-none [] AP.[] (jrR ∷ [])
    (Wj-wf p0) (F⊑F []) V⊑V′ bF′ (ℕ→X⊑ℕ→★ [])

  pre⊑ : Wh [] ∣ [] ⊢ V · Wv ⊑ F′ · Wv′ ∶ ι⊑ι base-ℕ
  pre⊑ = ·⊑· V⊑F′ Wv⊑Wv′

  post⊑ : Wh [] ∣ [] ⊢ V · Wv ⊑ (V′ · Hd) ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫ ∶ ι⊑ι base-ℕ
  post⊑ = ⊑⟪⟫ rv-none (Wc-bindᴿ v₀ here⇔) push-none [] AP.[] (jrR ∷ [])
    (Wj-wf p0) (ι⊑ι base-ℕ) (·⊑· V⊑V′ Wv⊑Hd¹) bPost (ι⊑ι base-ℕ)

  -- every derivation of the pair after the Wrap revokes: the rejoin must
  -- permit αᴿ (else V ⊑ V′ needs X ⊑ ★ at the joined, unpermitted X),
  -- and then the moved argument is (b)'s pair at a permitted αᴿ
  bind-intR : ΔR ⊢ⁱ Θ₀ ⇒ ΔRᵢ
  bind-intR = interior (changes∷ changes[] (step-bind v₀ fresh[] ins-here))

  -- the rejoin's permissions are copies of αᴿ
  data Zeros : List RVar → Set where
    z[] : Zeros []
    z∷  : ∀ {K} → Zeros K → Zeros (0 ∷ K)

  K-rejoin : ∀ {Wᵢ : World ΔLᵢ ΔRᵢ} {M O N Oᵢ K}
    → Push Θ₀ M O N Oᵢ → ¬ Value M → All (JoinRep Wᵢ [] Θ₀ N) K
    → Zeros K
  K-rejoin pu nv []                            = z[]
  K-rejoin pu nv (jr-join _ here _ _ ∷ ks)      = z∷ (K-rejoin pu nv ks)
  K-rejoin pu nv (jr-join _ (there ()) _ _ ∷ ks)
  K-rejoin pu nv (jr-rebind _ _ (inj₁ (_ , _ , () , _)) _ ∷ ks)
  K-rejoin pu nv (jr-rebind _ _ (inj₂ (iu-there () , _)) _ ∷ ks)
  K-rejoin (push _ _ _ (inj₁ refl)) nv (jr-open () _ ∷ ks)
  K-rejoin (push _ _ _ (inj₂ v)) nv (jr-open _ _ ∷ ks) = ⊥-elim (nv v)

  ¬v-app : ∀ {L M} → ¬ Value (L · M)
  ¬v-app (V-simple ())

  ty-V : ∀ {Δ Γ B} → Δ ∣ Γ ⊢ V ⦂ B → B ≡ (`ℕ ⇒ ` 0) ⇒ `ℕ
  ty-V (⊢ƛ _ ⊢$) = refl

  ty-Vf : ∀ {Δ Γ B C} → Δ ∣ Γ ⊢ V ⦂ B ⇒ C → B ≡ `ℕ ⇒ ` 0
  ty-Vf (⊢ƛ _ _) = refl

  ct-F : ∀ {Δ μ B A} → CastTy Δ μ tagF B A → B ≡ (`ℕ ⇒ ★) ⇒ `ℕ
  ct-F (cast-ty (⊢fun (⊢fun _ (⊢tag ())) _) _)
  ct-F (cast-ty (⊢fun (⊢fun (⊢id _ _) (⊢tag-var _ _ _)) (⊢id _ _)) _) = refl

  -- V ⊑ V′ needs X ⊑ ★ at the joined X
  dead-V : ∀ {U : World ΔLᵢ ΔRᵢ} {γ O A A′} {q : A ⊑ᵂ⟨ U ⟩[ O ] A′}
    → κʷ U ≡ [] → Joins U 0 0 → ¬ (U ∣ γ ⊢ V ⊑ V′ ∶⟨ A , A′ ⟩[ O ] q)
  dead-V {U = U} {O = O} eκ j (⊑cast {A = A} {p = p} d ct _)
    with ty-V (PE.ltyD d) | ct-F ct
  ... | refl | refl
    with PE.plain-idx {V = U} {O = O} {A = (`ℕ ⇒ ` 0) ⇒ `ℕ}
           {A′ = (`ℕ ⇒ ★) ⇒ `ℕ} PE.nf-⇒ p
  ... | ⇒⊑⇒ (⇒⊑⇒ _ p₁) _ = PE.no-tag★ {V = U} eκ here j (PE.var⊑★ p₁)

  post-uses-drop : ∀ {γ O A′}
      {q : `ℕ ⊑ᵂ⟨ Wh [] ⟩[ O ] A′}
    → (d : Wh [] ∣ γ ⊢ V · Wv ⊑ (V′ · Hd) ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫
             ∶⟨ `ℕ , A′ ⟩[ O ] q)
    → UsesDrop d
  post-uses-drop
    (⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Ui} {κ₁ = κ₁} rv I pu so sn ks wi pay d b′ q)
    with interior-functional (int-right I) bind-intR
  ... | refl with revoke-[] rv (same-κ I) | K-rejoin pu ¬v-app ks
  ... | refl | z[] with d
  ...   | ·⊑· dV _ =
    ⊥-elim (dead-V refl (proj₂ (join-fresh I here here (inj₂ refl))
                               (inj₁ here⇔)) dV)
  post-uses-drop
    (⊑⟪⟫ {Δ′ᵢ = Δ′ᵢ} {Wᵢ = Ui} {κ₁ = κ₁} rv I pu so sn ks wi pay d b′ q)
    | refl | refl | z∷ zs with d
  ...   | ·⊑· dV dW with ty-Vf (PE.ltyD dV)
  ...     | refl =
    inj₂ (inj₂ (joined-uses-drop (Paired-int I (inj₁ here⇔)) refl dW))

------------------------------------------------------------------------
-- 3. MG: a Merge on ONE side can lose a JOIN, not only a permission
-- (open; design.md §C9.2).  A rejoin over a hide `[+X^α] ([−X^α] V)`
-- merges into `[+X^α, −X^α] V`, which binds X and unbinds it again: X is
-- in scope neither outside nor inside.  When the other side still has
-- its rejoin, with casts at X between the rejoin and its hide, the
-- merged left has no X for the right's casts to face, and no right
-- state relates to it until the right has consumed its casts: SIM FAILS
-- at the left's Merge (`sim-fails`).  jr-rebind and revocations do not
-- help (the obstruction is ℕ ⊑ X, not a permission).
--
-- Source programs (UNRELATED, as RB2: the right ascribes the ∀-bound
-- g : X→ℕ to ★→ℕ and back; the pair is related from the TyBeta on,
-- `mg6`):
--   L  (ΛX. λk:(X→ℕ)→X→ℕ. λg:X→ℕ. k g)[ℕ] (λq:ℕ→ℕ. q) (λz:ℕ. z) 5
--   R  (ΛX. λk:(X→ℕ)→X→ℕ. λg:X→ℕ. k ((g : ★→ℕ) : X→ℕ))[ℕ]
--        (λq:ℕ→ℕ. q) (λz:ℕ. z) 5
-- Both runs: TyBeta Wrap Beta Wrap Beta Wrap (lockstep to state 6);
-- then the left Merges its argument's `[+X]([−X] G ⟨+X→id⟩)⟨−X→id⟩`
-- (state 7) while the right's argument is `[+X] (Gs⟨X?→id⟩⟨X!→id⟩)
-- ⟨−X→id⟩`, which does not step until it is applied.
------------------------------------------------------------------------

module MG where
  open PE.P4 using (Ξ₄; ϱ₄; W₄; W₄²; W₄²¹; W₄⁰; W₄⁰-wf; W₄²-wf; W₄²¹-wf;
                    v₀; unb₀; unb-int; unb-conv; p0)
  open Rbs using (Wc-bind²; Wc-bind²-conv; jr₀)
  open TIE using (ΔL; ΔLᵢ; Θ₀)
  open RB2 using (cS; cU; cS⊑; cU⊑; X→ℕ; ℕ→ℕ; bdy)
  open PE.Runs using (all-reach; EndsVB)

  Ck : Ty
  Ck = ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)) ⇒ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ))

  chk↦ tag↦ : Coercion
  chk↦ = ((` 0) ？ ℓ) ↦ᵖ idᵖ `ℕ
  tag↦ = ((` 0) !) ↦ᵖ idᵖ `ℕ

  FL FR K G L R : Term
  FL = Λ (ƛ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)) ∙ ƛ (` 0 ⇒ `ℕ) ∙ (` 1 · ` 0))
  FR = Λ (ƛ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)) ∙ ƛ (` 0 ⇒ `ℕ) ∙
         (` 1 · ((` 0 ⟨ μX ∣ chk↦ ⟩) ⟨ μX ∣ tag↦ ⟩)))
  K  = ƛ (`ℕ ⇒ `ℕ) ∙ ` 0
  G  = ƛ `ℕ ∙ ` 0
  L  = (((ν `ℕ · FL ⟨ reveal 0 Ck ⟩) · K) · G) · $ 5
  R  = (((ν `ℕ · FR ⟨ reveal 0 Ck ⟩) · K) · G) · $ 5

  L-⊢ : empty ∣ [] ⊢ L ⦂ `ℕ
  L-⊢ = tc

  R-⊢ : empty ∣ [] ⊢ R ⦂ `ℕ
  R-⊢ = tc

  -- the sealed g, its casts, and the arguments of k
  Gs Gc Lj Rj Lm : Term
  Gs = G ⟪ unb₀ , cU ⟫
  Gc = (Gs ⟨ μX ∣ chk↦ ⟩) ⟨ μX ∣ tag↦ ⟩
  Lj = Gs ⟪ Θ₀ , cS ⟫
  Rj = Gc ⟪ Θ₀ , cS ⟫
  -- the left's Merge of `[+X] ([−X] G)`: X bound then unbound
  Lm = G ⟪ unbind 0 0 ∷ bind 0 0 ∷ [] ,
           tail (mid (tail (mid (id `ℕ)) ↦ tail (mid (id `ℕ)))) ⟫

  st : Term → Term
  st a = ((((ƛ (`ℕ ⇒ `ℕ) ∙ ` 0) · a) ⟪ unb₀ , cU ⟫) ⟪ Θ₀ , cS ⟫) · $ 5

  L6 : nth (evalTerms 20 L-⊢) 6 ≡ st Lj
  L6 = refl

  R6 : nth (evalTerms 30 R-⊢) 6 ≡ st Rj
  R6 = refl

  L7 : nth (evalTerms 20 L-⊢) 7 ≡ st Lm
  L7 = refl

  ---------------------------------------------------------------------
  -- state 6 is related (the TyBeta boundaries permit nothing; the
  -- matched rejoins of g permit αᴿ, paying X→ℕ ⊑ X→ℕ)

  ctG : CastTy ΔLᵢ μX chk↦ (` 0 ⇒ `ℕ) (★ ⇒ `ℕ)
  ctG = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Gs ⟨ μX ∣ chk↦ ⟩})))

  ctT : CastTy ΔLᵢ μX tag↦ (★ ⇒ `ℕ) (` 0 ⇒ `ℕ)
  ctT = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔLᵢ} {M = Gc})))

  bGs : BdyTy ΔLᵢ unb₀ ΔL (`ℕ ⇒ `ℕ) cU (` 0 ⇒ `ℕ)
  bGs = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = Gs})))

  bLj : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bLj = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = Lj})))

  bRj : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bRj = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = Rj})))

  hid : Term → Term
  hid a = ((ƛ (`ℕ ⇒ `ℕ) ∙ ` 0) · a) ⟪ unb₀ , cU ⟫

  bHL : BdyTy ΔLᵢ unb₀ ΔL (`ℕ ⇒ `ℕ) cU (` 0 ⇒ `ℕ)
  bHL = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = hid Lj})))

  bHR : BdyTy ΔLᵢ unb₀ ΔL (`ℕ ⇒ `ℕ) cU (` 0 ⇒ `ℕ)
  bHR = proj₂ (proj₂ (bdy (tc {Δ = ΔLᵢ} {M = hid Rj})))

  bTL : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bTL = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = hid Lj ⟪ Θ₀ , cS ⟫})))

  bTR : BdyTy ΔL Θ₀ ΔLᵢ (` 0 ⇒ `ℕ) cS (`ℕ ⇒ `ℕ)
  bTR = proj₂ (proj₂ (bdy (tc {Δ = ΔL} {M = hid Rj ⟪ Θ₀ , cS ⟫})))

  Gs⊑Gs : W₄²¹ ∣ [] ⊢ Gs ⊑ Gs ∶ X→ℕ (0 ∷ [])
  Gs⊑Gs =
    ⟪⟫⊑⟪⟫ rv-none unb-int [] (W₄⁰-wf p0) (ℕ→ℕ {W = W₄⁰ (0 ∷ [])})
      (ƛ⊑ƛ {pA = ι⊑ι base-ℕ} {pB = ι⊑ι base-ℕ} tf tf (x⊑x Zʷ))
      bGs bGs (W₄²¹ , unb-conv , cU⊑) (X→ℕ (0 ∷ []))

  Gs⊑Gc : W₄²¹ ∣ [] ⊢ Gs ⊑ Gc ∶ X→ℕ (0 ∷ [])
  Gs⊑Gc = ⊑cast (⊑cast Gs⊑Gs ctG (⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ)))
            ctT (X→ℕ (0 ∷ []))

  Lj⊑Rj : W₄⁰ [] ∣ [] ⊢ Lj ⊑ Rj ∶ ℕ→ℕ {W = W₄⁰ []}
  Lj⊑Rj = ⟪⟫⊑⟪⟫ rv-none (Wc-bind² v₀ here⇔) (jr₀ ∷ []) W₄²¹-wf (X→ℕ [])
    Gs⊑Gc bLj bRj (W₄² , Wc-bind²-conv v₀ here⇔ , cS⊑) (ℕ→ℕ {W = W₄⁰ []})

  mg6 : W₄ ∣ [] ⊢ st Lj ⊑ st Rj ∶ ι⊑ι base-ℕ
  mg6 =
    ·⊑·
      (⟪⟫⊑⟪⟫ rv-none (Wc-bind² v₀ here⇔) [] W₄²-wf (X→ℕ [])
        (⟪⟫⊑⟪⟫ rv-none unb-int [] (W₄⁰-wf []) (ℕ→ℕ {W = W₄⁰ []})
          (·⊑· (ƛ⊑ƛ {pA = ℕ→ℕ {W = W₄⁰ []}} {pB = ℕ→ℕ {W = W₄⁰ []}} tf tf
                  (x⊑x Zʷ))
               Lj⊑Rj)
          bHL bHR (W₄² , unb-conv , cU⊑) (X→ℕ []))
        bTL bTR (W₄² , Wc-bind²-conv v₀ here⇔ , cS⊑) (ℕ→ℕ {W = W₄}))
      (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  ---------------------------------------------------------------------
  -- state 7 (the left's Merge) is related to NO right state reachable
  -- from state 6, in any world

  val-cast : ∀ {M μ p} → Value (M ⟨ μ ∣ p ⟩) → Value M
  val-cast (V-simple (S-cast v _)) = v

  val-bdy : ∀ {M Θ c} → Value (M ⟪ Θ , c ⟫) → Value M
  val-bdy (V-⟪⟫ u _)   = V-simple u
  val-bdy (V-fresh v _) = V-simple (S-cast v I-tag)

  -- a left term with an application at its head, under boundaries and
  -- casts
  data AppIn : Term → Set where
    ai-app  : ∀ {L M} → AppIn (L · M)
    ai-cast : ∀ {M μ p} → AppIn M → AppIn (M ⟨ μ ∣ p ⟩)
    ai-bdy  : ∀ {M Θ c} → AppIn M → AppIn (M ⟪ Θ , c ⟫)

  -- (A) such a term is related to no right value
  no-val : ∀ {Δ Δ′} {V : World Δ Δ′} {γ M M′ O A A′}
      {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → AppIn M → Value M′ → ¬ (V ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q)
  no-val ai-app (V-simple ()) (·⊑· _ _)
  no-val ai-app v (⊑cast d _ _) = no-val ai-app (val-cast v) d
  no-val ai-app v (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = no-val ai-app (val-bdy v) d
  no-val (ai-cast a) v (cast⊑cast d _ _ _) = no-val a (val-cast v) d
  no-val (ai-cast a) v (cast⊑ _ d _ _) = no-val a v d
  no-val (ai-cast a) v (⊑cast d _ _) = no-val (ai-cast a) (val-cast v) d
  no-val (ai-cast a) v (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) =
    no-val (ai-cast a) (val-bdy v) d
  no-val (ai-bdy a) v (⟪⟫⊑⟪⟫ _ _ _ _ _ d _ _ _ _) = no-val a (val-bdy v) d
  no-val (ai-bdy a) v (⟪⟫⊑ _ _ _ _ _ _ _ d _ _) = no-val a v d
  no-val (ai-bdy a) v (⊑cast d _ _) = no-val (ai-bdy a) (val-cast v) d
  no-val (ai-bdy a) v (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) =
    no-val (ai-bdy a) (val-bdy v) d

  -- a right term that reaches a value under casts and boundaries
  data Peel : Term → Set where
    pv-val  : ∀ {M} → Value M → Peel M
    pv-cast : ∀ {M μ p} → Peel M → Peel (M ⟨ μ ∣ p ⟩)
    pv-bdy  : ∀ {M Θ c} → Peel M → Peel (M ⟪ Θ , c ⟫)

  -- (A′) ... nor to such a term
  no-peel : ∀ {Δ Δ′} {V : World Δ Δ′} {γ M M′ O A A′}
      {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → AppIn M → Peel M′ → ¬ (V ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q)
  no-peel a (pv-val v) d = no-val a v d
  no-peel ai-app (pv-cast p) (⊑cast d _ _) = no-peel ai-app p d
  no-peel ai-app (pv-bdy p) (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = no-peel ai-app p d
  no-peel (ai-cast a) (pv-cast p) (cast⊑cast d _ _ _) = no-peel a p d
  no-peel (ai-cast a) p (cast⊑ _ d _ _) = no-peel a p d
  no-peel (ai-cast a) (pv-cast p) (⊑cast d _ _) = no-peel (ai-cast a) p d
  no-peel (ai-cast a) (pv-bdy p) (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) =
    no-peel (ai-cast a) p d
  no-peel (ai-bdy a) (pv-bdy p) (⟪⟫⊑⟪⟫ _ _ _ _ _ d _ _ _ _) = no-peel a p d
  no-peel (ai-bdy a) p (⟪⟫⊑ _ _ _ _ _ _ _ d _ _) = no-peel a p d
  no-peel (ai-bdy a) (pv-cast p) (⊑cast d _ _) = no-peel (ai-bdy a) p d
  no-peel (ai-bdy a) (pv-bdy p) (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) =
    no-peel (ai-bdy a) p d

  -- the right's spine: under casts and boundaries, a peelable term or an
  -- application of one
  data Spine : Term → Set where
    sp-peel : ∀ {M} → Peel M → Spine M
    sp-app  : ∀ {L M} → Peel L → Spine (L · M)
    sp-cast : ∀ {M μ p} → Spine M → Spine (M ⟨ μ ∣ p ⟩)
    sp-bdy  : ∀ {M Θ c} → Spine M → Spine (M ⟪ Θ , c ⟫)

  -- (B) an application whose function has an application at its head is
  -- related to no right spine
  no-spine : ∀ {Δ Δ′} {V : World Δ Δ′} {γ L N M′ O A A′}
      {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → AppIn L → Spine M′ → ¬ (V ∣ γ ⊢ L · N ⊑ M′ ∶⟨ A , A′ ⟩[ O ] q)
  no-spine a (sp-peel p) d = no-peel ai-app p d
  no-spine a (sp-app p) (·⊑· d _) = no-peel a p d
  no-spine a (sp-cast s) (⊑cast d _ _) = no-spine a s d
  no-spine a (sp-bdy s) (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = no-spine a s d

  open import examples.TypeCheck using (value?)
  open import Data.Maybe using (Maybe; nothing; is-just)
  open import Data.Bool using (T)

  peel? : (M : Term) → Maybe (Peel M)
  peel? M with value? M
  peel? M | just v = just (pv-val v)
  peel? (M ⟨ μ ∣ p ⟩) | nothing with peel? M
  peel? (M ⟨ μ ∣ p ⟩) | nothing | just q  = just (pv-cast q)
  peel? (M ⟨ μ ∣ p ⟩) | nothing | nothing = nothing
  peel? (M ⟪ Θ , c ⟫) | nothing with peel? M
  peel? (M ⟪ Θ , c ⟫) | nothing | just q  = just (pv-bdy q)
  peel? (M ⟪ Θ , c ⟫) | nothing | nothing = nothing
  peel? _ | nothing = nothing

  spine? : (M : Term) → Maybe (Spine M)
  spine? M with peel? M
  spine? M | just q = just (sp-peel q)
  spine? (L · N) | nothing with peel? L
  spine? (L · N) | nothing | just q  = just (sp-app q)
  spine? (L · N) | nothing | nothing = nothing
  spine? (M ⟨ μ ∣ p ⟩) | nothing with spine? M
  spine? (M ⟨ μ ∣ p ⟩) | nothing | just s  = just (sp-cast s)
  spine? (M ⟨ μ ∣ p ⟩) | nothing | nothing = nothing
  spine? (M ⟪ Θ , c ⟫) | nothing with spine? M
  spine? (M ⟪ Θ , c ⟫) | nothing | just s  = just (sp-bdy s)
  spine? (M ⟪ Θ , c ⟫) | nothing | nothing = nothing
  spine? _ | nothing = nothing

  -- (C) state 6's right against state 7's left: ℕ ⊑ X.  The left's
  -- merged argument Lm has interior and exterior type ℕ→ℕ; every route
  -- reaches the right's Gc, of type X→ℕ, with the left's ℕ→ℕ
  ty-G : ∀ {Δ Γ A} → Δ ∣ Γ ⊢ G ⦂ A → A ≡ `ℕ ⇒ `ℕ
  ty-G (⊢ƛ _ (⊢` here)) = refl

  ty-Gc : ∀ {Δ Γ A} → Δ ∣ Γ ⊢ Gc ⦂ A → A ≡ ` 0 ⇒ `ℕ
  ty-Gc ⊢Gc with PE.ty-cast ⊢Gc
  ... | refl = refl

  no-Gc : ∀ {Δ Δ′} {V : World Δ Δ′} {γ M O A′}
      {q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ M ⊑ Gc ∶⟨ `ℕ ⇒ `ℕ , A′ ⟩[ O ] q)
  no-Gc {V = V} {O = O} {q = q} d with ty-Gc (PE.rtyD d)
  ... | refl with PE.plain-idx {V = V} {O = O} {A = `ℕ ⇒ `ℕ}
                    {A′ = ` 0 ⇒ `ℕ} PE.nf-⇒ q
  ... | ⇒⊑⇒ () _

  no-G-Rj : ∀ {Δ Δ′} {V : World Δ Δ′} {γ O A′}
      {q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ G ⊑ Rj ∶⟨ `ℕ ⇒ `ℕ , A′ ⟩[ O ] q)
  no-G-Rj (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = no-Gc d

  no-Lm-Rj : ∀ {Δ Δ′} {V : World Δ Δ′} {γ O A′}
      {q : (`ℕ ⇒ `ℕ) ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ Lm ⊑ Rj ∶⟨ `ℕ ⇒ `ℕ , A′ ⟩[ O ] q)
  no-Lm-Rj (⟪⟫⊑⟪⟫ _ _ _ _ _ d _ _ _ _) with ty-G (PE.ltyD d)
  ... | refl = no-Gc d
  no-Lm-Rj (⟪⟫⊑ _ _ _ _ _ _ _ d _ _) with ty-G (PE.ltyD d)
  ... | refl = no-G-Rj d
  no-Lm-Rj (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = no-Gc d

  app₁ app₂ : Term
  app₁ = (ƛ (`ℕ ⇒ `ℕ) ∙ ` 0) · Lm
  app₂ = (ƛ (`ℕ ⇒ `ℕ) ∙ ` 0) · Rj

  no-app : ∀ {Δ Δ′} {V : World Δ Δ′} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ app₁ ⊑ app₂ ∶⟨ A , A′ ⟩[ O ] q)
  no-app (·⊑· f a) with PE.ltyD f
  ... | ⊢ƛ _ _ = no-Lm-Rj a

  data Wr (M₀ : Term) : Term → Set where
    wr-0   : Wr M₀ M₀
    wr-⟪⟫  : ∀ {M Θ c} → Wr M₀ M → Wr M₀ (M ⟪ Θ , c ⟫)

  peel : ∀ {Δ Δ′} {V : World Δ Δ′} {γ L R O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → Wr app₁ L → Wr app₂ R → ¬ (V ∣ γ ⊢ L ⊑ R ∶⟨ A , A′ ⟩[ O ] q)
  peel wr-0 wr-0 d = no-app d
  peel wr-0 (wr-⟪⟫ r) (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = peel wr-0 r d
  peel (wr-⟪⟫ l) wr-0 (⟪⟫⊑ _ _ _ _ _ _ _ d _ _) = peel l wr-0 d
  peel (wr-⟪⟫ l) (wr-⟪⟫ r) (⟪⟫⊑⟪⟫ _ _ _ _ _ d _ _ _ _) = peel l r d
  peel (wr-⟪⟫ l) (wr-⟪⟫ r) (⟪⟫⊑ _ _ _ _ _ _ _ d _ _) = peel l (wr-⟪⟫ r) d
  peel (wr-⟪⟫ l) (wr-⟪⟫ r) (⊑⟪⟫ _ _ _ _ _ _ _ _ d _ _) = peel (wr-⟪⟫ l) r d

  no-6 : ∀ {Δ Δ′} {V : World Δ Δ′} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ st Lm ⊑ st Rj ∶⟨ A , A′ ⟩[ O ] q)
  no-6 (·⊑· f _) = peel (wr-⟪⟫ (wr-⟪⟫ wr-0)) (wr-⟪⟫ (wr-⟪⟫ wr-0)) f

  -- THE CLAIM: the left's step 6 → 7 (Merge) has no simulating right
  -- run.  State 6 is related (`mg6`); state 7 is related to no right
  -- state reachable from state 6, in any world, at any slots.
  P7 : Term → Set
  P7 N′ = ∀ {Δ′} {V : World ΔL Δ′} {γ O A A′} {q : A ⊑ᵂ⟨ V ⟩[ O ] A′}
    → ¬ (V ∣ γ ⊢ st Lm ⊑ N′ ∶⟨ A , A′ ⟩[ O ] q)

  sp7 : ∀ {N′} → Spine N′ → P7 N′
  sp7 s = no-spine (ai-bdy (ai-bdy ai-app)) s

  R6-⊢ : ΔL ∣ [] ⊢ st Rj ⦂ `ℕ
  R6-⊢ = tc

  spines : (xs : List Term) → Maybe (All Spine xs)
  spines []       = just []
  spines (x ∷ xs) with spine? x | spines xs
  ... | just s  | just ss = just (s ∷ ss)
  ... | just _  | nothing = nothing
  ... | nothing | _       = nothing

  spines! : (xs : List Term) → {T (is-just (spines xs))} → All Spine xs
  spines! xs {ok} with spines xs
  spines! xs {ok} | just ss = ss

  -- every right state from state 6 on: state 6 itself (C), then spines
  -- every right state from state 6 on: state 6 itself (C), then spines
  allP7 : All P7 (evalTerms 20 R6-⊢)
  allP7 = no-6 ∷ All.map sp7 (spines! (drop 1 (evalTerms 20 R6-⊢)))

  sim-fails : ∀ {N′} → ΔL ⊢ st Rj -→* N′ → P7 N′
  sim-fails r = all-reach {P = P7} 20 R6-⊢ tt allP7 r

  -- ... so SIM, as stated (proof/DGG/SimDef), is FALSE for the relation
  -- (the left's Merge at state 6 of related cast terms, at the
  -- well-formed top-level world W₄ with no permission)
  open import proof.DGG.SimDef using (Sim)
  open import examples.Eval using (step; stepDeriv)

  wfΔL : WfCtx ΔL
  wfΔL = wf-ctx (wf-bindR wfᴿ-ℕ wf-reps[]) (λ ()) unique[]

  fromJust! : ∀ {X : Set} (m : Maybe X) → {T (is-just m)} → X
  fromJust! (just x) = x

  step67 : ΔL ⊢ st Lj -→ st Lm ∣ none
  step67 = stepDeriv (fromJust! (step ΔL (st Lj)))

  not-sim : ¬ Sim
  not-sim sim with sim wfΔL wfΔL PE.P4.W₄-wf refl mg6 step67
  ... | N′ , r′ , W′ , ev , wf′ , q , d = sim-fails r′ d

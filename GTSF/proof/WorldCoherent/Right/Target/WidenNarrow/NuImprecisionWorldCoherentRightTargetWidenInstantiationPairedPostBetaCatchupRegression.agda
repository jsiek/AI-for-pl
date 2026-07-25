module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedPostBetaCatchupRegression
  where

-- File Charter:
--   * Gives the smallest closed positive regression for the strict
--     post-`β-inst` QTI constructor.
--   * Checks the repaired final relation both for the bare target
--     instantiation trace and for the compiler-reachable gradual program.
--   * Packages the two final relations with the exact terminal worlds
--     required by the backward clauses of `ClosedNuDGG` and `GradualDGG`.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, or termination bypass.

import Coercions as C
import GradualTerms as G
import Imprecision as Imp
import NarrowWiden as NW
import NuTerms

open import Agda.Builtin.Equality using (_≡_; refl)
open import CastImprecisionShape using
  (shape-all; shape-fun; shape-id-var; shape-inst; shape-seal; shape-unseal)
open import Compile using
  ( CastPlan
  ; cast
  ; consistency-cast-plan
  ; down⊒
  ; up⊑
  )
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; zero; z<s)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax; ∃-syntax)
open import DynamicGradualGuarantee using
  (compiled-left; compiled-right)
open import GradualTermImprecision using
  ( lift-[]
  ; x⊑xᴳ
  ; ƛ⊑ƛᴳ
  ; ·⊑·ᴳ
  ; Λ⊑Λᴳ
  ; _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
  )
open import GradualTerms using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; Λ_ to Λᴳ_
    ; _·[_]_ to _·ᴳ[_]_
    )
open import Imprecision using
  (nonvar-fun; _ˣ⊑★; _ˣ⊑ˣ_)
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  ; idˣ
  ; tagˣ
  ; ∀ⁱ_
  ; ν
  )
open import ImprecisionComposition using
  (comp-idˣ-idˣ; comp-idˣ-tagˣ; comp-↦-↦; comp-∀-ν)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_; _∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; β
  ; β-inst
  ; β-Λ•
  ; β-∀•
  ; ξ-⟨⟩
  ; ν-step
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( StoreImp
  ; lift-ctx-[]
  ; lift-right-store-[]
  ; lift-store-[]
  ; seal★-tag-or-id
  ; store-right
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-`
  ; no•-ƛ
  ; no•-⟨⟩
  ; no•-Λ
  ; `_
  ; ƛ_
  ; Λ_
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; nu-term-imprecision-source-typing
  ; Λ⊑instβᵀ
  ; ⊑cast⊑idᵀ
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; Λ⊑Λᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import TermTyping using
  ( cast-inst
  ; cast-tag-or-id
  ; forget
  ; _∣_∣_⊢_⦂_
  ; ⊢`
  ; ⊢ƛ
  ; ⊢⟨⟩⊑
  )
open import Types using
  ( Ty
  ; wf★
  ; wf⇒
  ; wf∀
  ; ★
  ; Z
  ; ＇_
  ; _⇒_
  ; `∀
  )
open import proof.Core.Properties.ReductionProperties using
  (·₂-↠; ↠-trans)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-id; typing-closedᵐ)
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-id)
open import proof.Core.Properties.TypePreservation using (seal★-inst)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameAlgebra
  using (rel-assm²-id∈ᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)


private
  X : Ty
  X = ＇ zero

  F : Ty
  F = X ⇒ X

  H : Ty
  H = ★ ⇒ ★

  I : Term
  I = ƛ (` zero)

  vI : Value I
  vI = ƛ (` zero)

  noI : No• I
  noI = no•-ƛ no•-`

  pX :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ X ⊑ X ⊣ suc zero
  pX = idˣ (here refl) z<s z<s

  pF :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ⊢ F ⊑ F ⊣ suc zero
  pF = pX ↦ pX

  qX :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ X ⊑ ★ ⊣ zero
  qX = tagˣ (here refl) z<s

  qF :
    ((zero ˣ⊑★) ∷ [])
      ∣ suc zero ⊢ F ⊑ H ⊣ zero
  qF = qX ↦ qX

  q∀F-H :
    [] ∣ zero ⊢ `∀ F ⊑ H ⊣ zero
  q∀F-H = ν nonvar-fun refl qF

  final-q∀F-H :
    [] ∣ zero ⊢ `∀ F ⊑ H ⊣ suc zero
  final-q∀F-H = ⊑-target-lift-rightᵢ q∀F-H

  wfF : Types.WfTy (suc zero) F
  wfF = wf⇒ (Types.wfVar z<s) (Types.wfVar z<s)

  wf∀F : Types.WfTy zero (`∀ F)
  wf∀F = wf∀ wfF

  wfH : Types.WfTy zero H
  wfH = wf⇒ wf★ wf★

  raw-pX :
    ((zero ˣ⊑ˣ zero) ∷ []) Imp.⊢ X ⊑ X
  raw-pX = Imp.idˣ (here refl)

  raw-pF :
    ((zero ˣ⊑ˣ zero) ∷ []) Imp.⊢ F ⊑ F
  raw-pF = raw-pX Imp.↦ raw-pX

  raw-p∀F :
    [] Imp.⊢ `∀ F ⊑ `∀ F
  raw-p∀F = Imp.∀ⁱ raw-pF

  raw-qX :
    ((zero ˣ⊑★) ∷ []) Imp.⊢ X ⊑ ★
  raw-qX = Imp.tagˣ (here refl)

  raw-qF :
    ((zero ˣ⊑★) ∷ []) Imp.⊢ F ⊑ H
  raw-qF = raw-qX Imp.↦ raw-qX

  raw-q∀F-H :
    [] Imp.⊢ `∀ F ⊑ H
  raw-q∀F-H = Imp.ν nonvar-fun refl raw-qF

  source-argument-consistency :
    zero Imp.⊢ `∀ F ~ `∀ F
  source-argument-consistency =
    `∀ F , raw-p∀F , raw-p∀F

  target-argument-consistency :
    zero Imp.⊢ H ~ `∀ F
  target-argument-consistency =
    `∀ F , raw-q∀F-H , raw-p∀F

  Iᴳ : GTerm
  Iᴳ = ƛᴳ X ⇒ `ᴳ zero

  polyᴳ : GTerm
  polyᴳ = Λᴳ Iᴳ

  source-idᴳ : GTerm
  source-idᴳ = ƛᴳ (`∀ F) ⇒ `ᴳ zero

  target-idᴳ : GTerm
  target-idᴳ = ƛᴳ H ⇒ `ᴳ zero

  source-programᴳ : GTerm
  source-programᴳ = source-idᴳ ·ᴳ[ zero ] polyᴳ

  target-programᴳ : GTerm
  target-programᴳ = target-idᴳ ·ᴳ[ zero ] polyᴳ

  gradual-I-relation :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ []
      ⊢ᴳ Iᴳ ⊑ Iᴳ ⦂ F ⊑ F ∶ pF
  gradual-I-relation =
    ƛ⊑ƛᴳ (Types.wfVar z<s) (Types.wfVar z<s) (x⊑xᴳ Z)

  gradual-poly-relation :
    [] ∣ zero ∣ zero ∣ []
      ⊢ᴳ polyᴳ ⊑ polyᴳ
      ⦂ `∀ F ⊑ `∀ F ∶ ∀ⁱ pF
  gradual-poly-relation =
    Λ⊑Λᴳ lift-[] (G.ƛ X ⇒ G.` zero) (G.ƛ X ⇒ G.` zero)
      refl refl gradual-I-relation

  gradual-function-relation :
    [] ∣ zero ∣ zero ∣ []
      ⊢ᴳ source-idᴳ ⊑ target-idᴳ
      ⦂ (`∀ F ⇒ `∀ F) ⊑ (H ⇒ H) ∶ q∀F-H ↦ q∀F-H
  gradual-function-relation =
    ƛ⊑ƛᴳ wf∀F wfH (x⊑xᴳ Z)

  public-target-instantiation-relation :
    [] ∣ zero ∣ zero ∣ []
      ⊢ᴳ source-programᴳ ⊑ target-programᴳ
      ⦂ `∀ F ⊑ H ∶ q∀F-H
  public-target-instantiation-relation =
    ·⊑·ᴳ gradual-function-relation gradual-poly-relation
      source-argument-consistency target-argument-consistency

  body-cast : C.Coercion
  body-cast =
    C.seal ★ zero C.↦ C.unseal zero ★

  forall-id-cast : C.Coercion
  forall-id-cast =
    C.`∀ (C.id X C.↦ C.id X)

  function-id-cast : C.Coercion
  function-id-cast =
    C.id X C.↦ C.id X

  source-plan : CastPlan zero [] (`∀ F) (`∀ F)
  source-plan =
    consistency-cast-plan zero source-argument-consistency

  target-compile-consistency :
    zero Imp.⊢ `∀ F ~ H
  target-compile-consistency =
    `∀ F , raw-p∀F , raw-q∀F-H

  target-plan : CastPlan zero [] (`∀ F) H
  target-plan =
    consistency-cast-plan zero target-compile-consistency

  source-down-shape :
    Compile.down source-plan ≡ forall-id-cast
  source-down-shape = refl

  source-up-shape :
    Compile.up source-plan ≡ forall-id-cast
  source-up-shape = refl

  target-down-shape :
    Compile.down target-plan ≡ forall-id-cast
  target-down-shape = refl

  target-up-shape :
    Compile.up target-plan ≡ C.inst H body-cast
  target-up-shape = refl

  compiled-source-shape :
    compiled-left public-target-instantiation-relation
      ≡ (ƛ (` zero)) · cast source-plan (Λ I)
  compiled-source-shape = refl

  compiled-target-shape :
    compiled-right public-target-instantiation-relation
      ≡ (ƛ (` zero)) · cast target-plan (Λ I)
  compiled-target-shape = refl

  source-public-final : Term
  source-public-final =
    (Λ I) ⟨ forall-id-cast ⟩ ⟨ forall-id-cast ⟩

  source-public-final-value : Value source-public-final
  source-public-final-value =
    (Λ vI) ⟨ C.`∀ (C.id X C.↦ C.id X) ⟩
      ⟨ C.`∀ (C.id X C.↦ C.id X) ⟩

  target-inst-input : Term
  target-inst-input =
    (Λ I) ⟨ forall-id-cast ⟩

  target-inst-input-value : Value target-inst-input
  target-inst-input-value =
    (Λ vI) ⟨ C.`∀ (C.id X C.↦ C.id X) ⟩

  target-inst-input-no-bullet : No• target-inst-input
  target-inst-input-no-bullet =
    no•-⟨⟩ (no•-Λ noI)

  target-public-final : Term
  target-public-final =
    I ⟨ function-id-cast ⟩ ⟨ body-cast ⟩

  target-public-final-value : Value target-public-final
  target-public-final-value =
    vI ⟨ C.id X C.↦ C.id X ⟩
      ⟨ C.seal ★ zero C.↦ C.unseal zero ★ ⟩

  source-program-trace :
    (ƛ (` zero)) · cast source-plan (Λ I)
      —↠[ keep ∷ [] ] source-public-final
  source-program-trace
      rewrite source-down-shape | source-up-shape =
    ↠-step (pure-step (β source-public-final-value)) ↠-refl

  public-source-program-trace :
    compiled-left public-target-instantiation-relation
      —↠[ keep ∷ [] ] source-public-final
  public-source-program-trace =
    subst
      (λ M → M —↠[ keep ∷ [] ] source-public-final)
      (sym compiled-source-shape)
      source-program-trace

  target-argument-trace :
    cast target-plan (Λ I)
      —↠[ keep ∷ bind ★ ∷ keep ∷ keep ∷ [] ]
        target-public-final
  target-argument-trace
      rewrite target-down-shape | target-up-shape =
    ↠-step (pure-step (β-inst target-inst-input-value))
      (↠-step
        (ν-step target-inst-input-value target-inst-input-no-bullet)
        (↠-step
          (ξ-⟨⟩ (pure-step (β-∀• (Λ vI))))
          (↠-step
            (ξ-⟨⟩ (ξ-⟨⟩ (pure-step (β-Λ• vI))))
            ↠-refl)))

  target-program-trace :
    (ƛ (` zero)) · cast target-plan (Λ I)
      —↠[ keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ [] ]
        target-public-final
  target-program-trace =
    ↠-trans
      (·₂-↠ (ƛ (` zero)) noI target-argument-trace)
      (↠-step (pure-step (β target-public-final-value)) ↠-refl)

  public-target-program-trace :
    compiled-right public-target-instantiation-relation
      —↠[ keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ [] ]
        target-public-final
  public-target-program-trace =
    subst
      (λ M →
        M —↠[ keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ [] ]
          target-public-final)
      (sym compiled-target-shape)
      target-program-trace

  body-cast-typing :
    C.instᵈ C.tag-or-idᵈ
      ∣ suc zero ∣ ((zero , ★) ∷ [])
      ⊢ body-cast ∶ F ⊑ H
  body-cast-typing =
    C.cast-fun
      (C.cast-seal wf★ (here refl) refl)
      (C.cast-unseal wf★ (here refl) refl) ,
    NW.instSafe→widening
      (NW.safe-fun
        (NW.sealⁿ ★ zero)
        (NW.unsealʷ zero ★))

  outer-cast-typing :
    C.tag-or-idᵈ ∣ zero ∣ []
      ⊢ C.inst H body-cast ∶ `∀ F ⊑ H
  outer-cast-typing =
    C.cast-inst (Types.wf⇒ wf★ wf★) refl
      (proj₁ body-cast-typing) ,
    NW.inst
      (NW.safe-fun
        (NW.sealⁿ ★ zero)
        (NW.unsealʷ zero ★))

  function-id-cast-typing-empty :
    C.id-onlyᵈ ∣ suc zero ∣ []
      ⊢ function-id-cast ∶ F ⊑ F
  function-id-cast-typing-empty =
    C.cast-fun
      (C.cast-id (Types.wfVar z<s) refl)
      (C.cast-id (Types.wfVar z<s) refl) ,
    NW.cross
      (NW.cross (NW.id-＇ zero) NW.↦
       NW.cross (NW.id-＇ zero))

  function-id-cast-typing-allocated :
    C.id-onlyᵈ ∣ suc zero ∣ ((zero , ★) ∷ [])
      ⊢ function-id-cast ∶ F ⊑ F
  function-id-cast-typing-allocated =
    C.cast-fun
      (C.cast-id (Types.wfVar z<s) refl)
      (C.cast-id (Types.wfVar z<s) refl) ,
    NW.cross
      (NW.cross (NW.id-＇ zero) NW.↦
       NW.cross (NW.id-＇ zero))

  paired-body-relation :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴺ I ⊑ I ⦂ F ⊑ F ∶ pF
  paired-body-relation =
    ƛ⊑ƛᵀ (Types.wfVar z<s) (Types.wfVar z<s)
      (x⊑xᵀ Types.Z)

  paired-body-id-relation :
    ((zero ˣ⊑ˣ zero) ∷ [])
      ∣ suc zero ∣ suc zero ∣ [] ∣ []
      ⊢ᴺ I ⊑ I ⟨ function-id-cast ⟩
      ⦂ F ⊑ F ∶ pF
  paired-body-id-relation =
    ⊑cast⊑idᵀ (λ α ()) function-id-cast-typing-empty
      paired-body-relation pF
      (shape-fun shape-id-var shape-id-var)
      (comp-↦-↦ comp-idˣ-idˣ comp-idˣ-idˣ)

  paired-universal-relation :
    [] ∣ zero ∣ zero ∣ [] ∣ []
      ⊢ᴺ Λ I ⊑ Λ I
      ⦂ `∀ F ⊑ `∀ F ∶ ∀ⁱ pF
  paired-universal-relation =
    Λ⊑Λᵀ lift-store-[] lift-ctx-[]
      vI vI paired-body-relation

  source-final-typing :
    zero ∣ [] ∣ [] ⊢ Λ I ⦂ `∀ F
  source-final-typing =
    nu-term-imprecision-source-typing paired-universal-relation

  allocated-I-typing :
    suc zero ∣ ((zero , ★) ∷ []) ∣ [] ⊢ I ⦂ F
  allocated-I-typing =
    ⊢ƛ (Types.wfVar z<s) (⊢` Types.Z)

  bare-target-final-typing :
    suc zero ∣ ((zero , ★) ∷ []) ∣ []
      ⊢ I ⟨ body-cast ⟩ ⦂ H
  bare-target-final-typing =
    ⊢⟨⟩⊑ (cast-inst cast-tag-or-id)
      (seal★-inst seal★-tag-or-id)
      body-cast-typing allocated-I-typing

  public-target-inner-typing :
    suc zero ∣ ((zero , ★) ∷ []) ∣ []
      ⊢ I ⟨ function-id-cast ⟩ ⦂ F
  public-target-inner-typing =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ
        function-id-cast-typing-allocated)
      allocated-I-typing

  public-target-final-typing :
    suc zero ∣ ((zero , ★) ∷ []) ∣ []
      ⊢ target-public-final ⦂ H
  public-target-final-typing =
    ⊢⟨⟩⊑ (cast-inst cast-tag-or-id)
      (seal★-inst seal★-tag-or-id)
      body-cast-typing public-target-inner-typing

  bare-final-relation :
    [] ∣ zero ∣ suc zero
      ∣ store-right zero ★ wf★ ∷ [] ∣ []
      ⊢ᴺ Λ I ⊑ I ⟨ body-cast ⟩
      ⦂ `∀ F ⊑ H ∶ final-q∀F-H
  bare-final-relation =
    Λ⊑instβᵀ
      {τ = λ X → X} {σ = λ X → X}
      prefix-reflⁱ cast-tag-or-id
      seal★-tag-or-id outer-cast-typing
      lift-store-[] lift-right-store-[]
      vI noI vI noI
      (C.seal ★ zero C.↦ C.unseal zero ★)
      paired-body-relation q∀F-H
      (shape-inst (shape-fun shape-seal shape-unseal))
      (comp-∀-ν
        (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))
      rel-assm²-id∈ᵢ
      (λ X< → X<) (λ X< → X<)
      rel-store-embedding-reflⁱ
      (renameᵗᵐ-id (Λ I))
      (renameᵗᵐ-id (I ⟨ body-cast ⟩))
      (renameᵗ-id (`∀ F)) (renameᵗ-id H)
      final-q∀F-H
      (Λ vI) (no•-Λ noI)
      (typing-closedᵐ (forget source-final-typing))
      (vI ⟨ C.seal ★ zero C.↦ C.unseal zero ★ ⟩)
      (no•-⟨⟩ noI)
      (typing-closedᵐ (forget bare-target-final-typing))
      source-final-typing bare-target-final-typing

  target-inner-value : Value (I ⟨ function-id-cast ⟩)
  target-inner-value =
    vI ⟨ C.id X C.↦ C.id X ⟩

  target-inner-no-bullet : No• (I ⟨ function-id-cast ⟩)
  target-inner-no-bullet =
    no•-⟨⟩ noI

  public-base-final-relation :
    [] ∣ zero ∣ suc zero
      ∣ store-right zero ★ wf★ ∷ [] ∣ []
      ⊢ᴺ Λ I ⊑ target-public-final
      ⦂ `∀ F ⊑ H ∶ final-q∀F-H
  public-base-final-relation =
    Λ⊑instβᵀ
      {τ = λ X → X} {σ = λ X → X}
      prefix-reflⁱ cast-tag-or-id
      seal★-tag-or-id outer-cast-typing
      lift-store-[] lift-right-store-[]
      vI noI target-inner-value target-inner-no-bullet
      (C.seal ★ zero C.↦ C.unseal zero ★)
      paired-body-id-relation q∀F-H
      (shape-inst (shape-fun shape-seal shape-unseal))
      (comp-∀-ν
        (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))
      rel-assm²-id∈ᵢ
      (λ X< → X<) (λ X< → X<)
      rel-store-embedding-reflⁱ
      (renameᵗᵐ-id (Λ I))
      (renameᵗᵐ-id target-public-final)
      (renameᵗ-id (`∀ F)) (renameᵗ-id H)
      final-q∀F-H
      (Λ vI) (no•-Λ noI)
      (typing-closedᵐ (forget source-final-typing))
      target-public-final-value
      (no•-⟨⟩ target-inner-no-bullet)
      (typing-closedᵐ (forget public-target-final-typing))
      source-final-typing public-target-final-typing

  public-one-source-cast-relation :
    [] ∣ zero ∣ suc zero
      ∣ store-right zero ★ wf★ ∷ [] ∣ []
      ⊢ᴺ (Λ I) ⟨ forall-id-cast ⟩
        ⊑ target-public-final
      ⦂ `∀ F ⊑ H ∶ final-q∀F-H
  public-one-source-cast-relation =
    cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ
        (down⊒ source-plan))
      public-base-final-relation final-q∀F-H
      (shape-all (shape-fun shape-id-var shape-id-var))
      (comp-∀-ν
        (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))

  public-final-relation :
    [] ∣ zero ∣ suc zero
      ∣ store-right zero ★ wf★ ∷ [] ∣ []
      ⊢ᴺ source-public-final ⊑ target-public-final
      ⦂ `∀ F ⊑ H ∶ final-q∀F-H
  public-final-relation =
    cast⊑⊑ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.widen-mode-relax C.id-only≤tag-or-idᵈ
        (up⊑ source-plan))
      public-one-source-cast-relation final-q∀F-H
      (shape-all (shape-fun shape-id-var shape-id-var))
      (comp-∀-ν
        (comp-↦-↦ comp-idˣ-tagˣ comp-idˣ-tagˣ))

  full-target-value-trace :
    (Λ I) ⟨ C.inst H body-cast ⟩
      —↠[ keep ∷ bind ★ ∷ keep ∷ [] ] I ⟨ body-cast ⟩
  full-target-value-trace =
    ↠-step (pure-step (β-inst (Λ vI)))
      (↠-step (ν-step (Λ vI) (no•-Λ noI))
        (↠-step (ξ-⟨⟩ (pure-step (β-Λ• vI))) ↠-refl))


paired-post-beta-catchup-regression :
  [] ∣ zero ∣ suc zero
    ∣ store-right zero ★ wf★ ∷ [] ∣ []
    ⊢ᴺ Λ I ⊑ I ⟨ body-cast ⟩
    ⦂ `∀ F ⊑ H ∶ final-q∀F-H
paired-post-beta-catchup-regression =
  bare-final-relation


paired-target-instantiation-closed-nu-dgg-regression :
  ∃[ V ] (Σ[ χs ∈ StoreChanges ]
  (∃[ Φ ] (Σ[ ρ ∈
      StoreImp Φ
        (applyTyCtxs χs zero)
        (applyTyCtxs (keep ∷ bind ★ ∷ keep ∷ []) zero) ]
  (Σ[ q ∈
      (Φ ∣ applyTyCtxs χs zero
        ⊢ applyTys χs (`∀ F)
          ⊑ applyTys (keep ∷ bind ★ ∷ keep ∷ []) H
        ⊣ applyTyCtxs (keep ∷ bind ★ ∷ keep ∷ []) zero) ]
    (((Λ I) —↠[ χs ] V) ×
     Value V ×
     (NuTermImprecision.leftStoreⁱ ρ ≡ applyStores χs []) ×
     (NuTermImprecision.rightStoreⁱ ρ
       ≡ applyStores (keep ∷ bind ★ ∷ keep ∷ []) []) ×
     Φ ∣ applyTyCtxs χs zero
       ∣ applyTyCtxs (keep ∷ bind ★ ∷ keep ∷ []) zero
       ∣ ρ ∣ []
       ⊢ᴺ V ⊑ I ⟨ body-cast ⟩
       ⦂ applyTys χs (`∀ F)
         ⊑ applyTys (keep ∷ bind ★ ∷ keep ∷ []) H
       ∶ q)))))
paired-target-instantiation-closed-nu-dgg-regression =
  Λ I , [] , [] , store-right zero ★ wf★ ∷ [] ,
  final-q∀F-H , ↠-refl , Λ vI , refl , refl ,
  bare-final-relation


paired-target-instantiation-gradual-dgg-regression :
  ∃[ V ] (Σ[ χs ∈ StoreChanges ]
  (∃[ Φ ] (Σ[ ρ ∈
      StoreImp Φ
        (applyTyCtxs χs zero)
        (applyTyCtxs
          (keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ []) zero) ]
  (Σ[ q ∈
      (Φ ∣ applyTyCtxs χs zero
        ⊢ applyTys χs (`∀ F)
          ⊑ applyTys
            (keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ []) H
        ⊣ applyTyCtxs
          (keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ []) zero) ]
    ((compiled-left public-target-instantiation-relation
        —↠[ χs ] V) ×
     Value V ×
     (NuTermImprecision.leftStoreⁱ ρ ≡ applyStores χs []) ×
     (NuTermImprecision.rightStoreⁱ ρ
       ≡ applyStores
         (keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ []) []) ×
     Φ ∣ applyTyCtxs χs zero
       ∣ applyTyCtxs
         (keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ []) zero
       ∣ ρ ∣ []
       ⊢ᴺ V ⊑ target-public-final
       ⦂ applyTys χs (`∀ F)
         ⊑ applyTys
           (keep ∷ bind ★ ∷ keep ∷ keep ∷ keep ∷ []) H
       ∶ q)))))
paired-target-instantiation-gradual-dgg-regression =
  source-public-final , keep ∷ [] , [] ,
  store-right zero ★ wf★ ∷ [] ,
  final-q∀F-H , public-source-program-trace ,
  source-public-final-value , refl , refl ,
  public-final-relation

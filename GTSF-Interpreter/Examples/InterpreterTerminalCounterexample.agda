module Examples.InterpreterTerminalCounterexample where

-- File Charter:
--   * Separates an obsolete hand-written source-return/target-blame cast plan
--     from the cast plans produced by the current compiler.
--   * Checks directly that the old plan still disagrees, while both endpoints
--     selected by the strengthened compiler blame.
--   * Uses no reduction, catch-up, observation, or existing DGG theorem.
--   * Guards the compiler-facing scope of the Milestone 5 statement.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; z<s)
open import Data.Product using (_,_; proj₁)

import Coercions as C
open import Compile using (compileᵀ)
open import Narrowing.CompileInterpreterNarrowing using
  (compile-preserves-interpreter-narrowing)
open import Ctx using (ctxWf-[])
open import GradualTermImprecision as GTI using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
import GradualTerms as G
import Imprecision as Imp
open import ImprecisionWf using
  ( id★
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _ˣ⊑★
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import Interpreter
open import Narrowing.InterpreterTermNarrowing using
  (OpenInterpreterTermNarrowing)
import NuTerms as N
import Primitives as P
import Types as T
open import proof.ImprecisionProperties using
  (⊑-refl-idᵢ; ~-sym)
open import proof.MaximalLowerBoundsWf using (⊑-forgetᵢ)


HNat : T.Ty
HNat = T.‵ T.`ℕ

G : T.Ty
G = T.★ T.⇒ T.★

X : T.Ty
X = T.＇ zero

A : T.Ty
A = T.`∀ (X T.⇒ X)

body-cast : C.Coercion
body-cast =
  (G C.？) C.︔ ((X C.!) C.↦ (X C.？))

source-gen : C.Coercion
source-gen = C.gen T.★ body-cast

source-up : C.Coercion
source-up = C.`∀ ((C.id X) C.↦ (C.id X))

target-up : C.Coercion
target-up = (C.id T.★) C.↦ (C.id T.★)

label : T.Label
label = zero

gradual-identity : T.Ty → G.GTerm
gradual-identity B = G.ƛ B ⇒ G.` zero

gradual-nat-producer : G.GTerm
gradual-nat-producer =
  gradual-identity T.★ G.·[ label ] G.$ (P.κℕ zero)

gradual-source : G.GTerm
gradual-source =
  gradual-identity A G.·[ label ] gradual-nat-producer

gradual-target : G.GTerm
gradual-target =
  gradual-identity G G.·[ label ] gradual-nat-producer

wfA : T.WfTy zero A
wfA = T.wf∀ (T.wf⇒ (T.wfVar z<s) (T.wfVar z<s))

wfG : T.WfTy zero G
wfG = T.wf⇒ T.wf★ T.wf★

G⊑★ : [] ∣ zero ⊢ G ⊑ T.★ ⊣ zero
G⊑★ = ImprecisionWf.tag id★ ⇛ id★

x★ :
  ((zero ˣ⊑★) ∷ []) ∣ 1
    ⊢ X ⊑ T.★ ⊣ zero
x★ = tagˣ (here refl) z<s

star~nat : zero Imp.⊢ T.★ ~ HNat
star~nat =
  HNat , (Imp.tag T.`ℕ) , Imp.idι

A~star : zero Imp.⊢ A ~ T.★
A~star =
  A , ⊑-refl-idᵢ wfA , ⊑-forgetᵢ p
  where
  p : [] ∣ zero ⊢ A ⊑ T.★ ⊣ zero
  p = ν ImprecisionWf.nonvar-fun refl (tag x★ ⇛ x★)

G~star : zero Imp.⊢ G ~ T.★
G~star =
  G , ⊑-refl-idᵢ wfG , ⊑-forgetᵢ G⊑★

q : [] ∣ zero ⊢ A ⊑ G ⊣ zero
q = ν ImprecisionWf.nonvar-fun refl (x★ ↦ x★)

identity-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ gradual-identity T.★ ⊑ gradual-identity T.★
      ⦂ G ⊑ G ∶ id★ ↦ id★
identity-relation =
  GTI.ƛ⊑ƛᴳ T.wf★ T.wf★ (GTI.x⊑xᴳ T.Z)

nat-producer-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ gradual-nat-producer ⊑ gradual-nat-producer
      ⦂ T.★ ⊑ T.★ ∶ id★
nat-producer-relation =
  GTI.·⊑·ᴳ identity-relation GTI.κ⊑κᴳ
    star~nat star~nat

outer-function-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ gradual-identity A ⊑ gradual-identity G
      ⦂ A T.⇒ A ⊑ G T.⇒ G ∶ q ↦ q
outer-function-relation =
  GTI.ƛ⊑ƛᴳ wfA wfG (GTI.x⊑xᴳ T.Z)

public-mismatch-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ gradual-source ⊑ gradual-target
      ⦂ A ⊑ G ∶ q
public-mismatch-relation =
  GTI.·⊑·ᴳ outer-function-relation nat-producer-relation
    A~star G~star

compiled-left : N.Term
compiled-left =
  proj₁
    (compileᵀ ctxWf-[]
      (GTI.gradual-term-imprecision-source-typing
        public-mismatch-relation))

compiled-right : N.Term
compiled-right =
  proj₁
    (compileᵀ ctxWf-[]
      (GTI.gradual-term-imprecision-target-typing
        public-mismatch-relation))

identity : N.Term
identity = N.ƛ (N.` zero)

tagged-nat : N.Term
tagged-nat = N.$ (P.κℕ zero) N.⟨ HNat C.! ⟩

compiled-nat-producer : N.Term
compiled-nat-producer = identity N.· tagged-nat

compiled-source : N.Term
compiled-source =
  identity N.·
    ((compiled-nat-producer N.⟨ source-gen ⟩)
      N.⟨ source-up ⟩)

compiled-target : N.Term
compiled-target =
  identity N.·
    ((compiled-nat-producer N.⟨ G C.？ ⟩)
      N.⟨ target-up ⟩)

compiled-relation :
  OpenInterpreterTermNarrowing
    Narrowing.InterpreterTermNarrowing.RelatedWorlds.empty-world⊑
    [] zero zero [] []
    compiled-left compiled-right A G q
compiled-relation =
  compile-preserves-interpreter-narrowing
    ctxWf-[] ctxWf-[] public-mismatch-relation

source-result : Value
source-result =
  forall-proxy ((C.id X) C.↦ (C.id X)) []
    (generalized T.★ body-cast []
      (tagged (T.‵ T.`ℕ) []
        (constant (P.κℕ zero))))

direct-source-returns :
  run compiled-source 20 ≡ returned emptyWorld source-result
direct-source-returns = refl

direct-target-blames :
  run compiled-target 20 ≡ blamed emptyWorld
direct-target-blames = refl

is-returned : Outcome → Bool
is-returned (timed W) = false
is-returned (blamed W) = false
is-returned (failed W e) = false
is-returned (returned W V) = true

is-blamed : Outcome → Bool
is-blamed (timed W) = false
is-blamed (blamed W) = true
is-blamed (failed W e) = false
is-blamed (returned W V) = false

is-failed : Outcome → Bool
is-failed (timed W) = false
is-failed (blamed W) = false
is-failed (failed W e) = true
is-failed (returned W V) = false

compiled-source-blames :
  is-blamed (run compiled-left 100) ≡ true
compiled-source-blames = refl

compiled-target-blames :
  is-blamed (run compiled-right 100) ≡ true
compiled-target-blames = refl

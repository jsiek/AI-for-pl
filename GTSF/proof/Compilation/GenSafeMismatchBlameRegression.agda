module proof.Compilation.GenSafeMismatchBlameRegression where

-- File Charter:
--   * Preserves the source-level gen/untag mismatch example after the
--     `GenSafe` grammar repair.
--   * Proves that both gradual programs are well typed and related.
--   * Gives the intended eager source and target coercions and proves that
--     both reject the shared dynamically tagged Nat value with blame.
--   * Proves that coercion compilation synthesizes both intended coercions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_,_; proj₁)

import Coercions as C
import Imprecision as Imp
import NarrowWiden as NW
import Primitives as P
import Types as T

open import Coercions using (_∣_∣_⊢_∶_=⇒_)
open import GradualTermImprecision using
  ( gradual-term-imprecision-source-typing
  ; gradual-term-imprecision-target-typing
  ; _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
  ; x⊑xᴳ
  ; ƛ⊑ƛᴳ
  ; ·⊑·ᴳ
  ; κ⊑κᴳ
  )
open import GradualTerms using
  ( GTerm
  ; _∣_⊢_⦂_
  )
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; $ to $ᴳ
    )
open import ImprecisionWf using
  ( id★
  ; tag_⇛_
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( blame-⟨⟩
  ; keep
  ; pure-step
  ; tag-untag-bad
  ; β-seq
  ; ξ-⟨⟩
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-$
  ; no•-⟨⟩
  ; ok-no
  ; $
  ; _⟨_⟩
  )
open import Relation.Binary.PropositionalEquality using (_≢_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import Types using
  ( Ty
  ; ★
  ; wf★
  ; wfVar
  ; wf⇒
  ; wf∀
  ; ＇_
  ; _⇒_
  ; `∀
  ; Z
  )
open import proof.Core.Properties.ImprecisionProperties using (⊑-refl-idᵢ; ~-sym)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-forgetᵢ)
open import proof.Compilation.CompileCoercions using
  ( coerce-downⁿᵐ
  ; realizes-idᵢᴺᵂ
  )


G : Ty
G = ★ ⇒ ★

X : Ty
X = ＇ zero

A : Ty
A = `∀ (X ⇒ X)

HNat : Ty
HNat = T.‵ T.`ℕ

label : T.Label
label = zero

idᴳ : Ty → GTerm
idᴳ B = ƛᴳ B ⇒ `ᴳ zero

nat-producerᴳ : GTerm
nat-producerᴳ = idᴳ ★ ·ᴳ[ label ] $ᴳ (P.κℕ zero)

source-programᴳ : GTerm
source-programᴳ = idᴳ A ·ᴳ[ label ] nat-producerᴳ

target-programᴳ : GTerm
target-programᴳ = idᴳ G ·ᴳ[ label ] nat-producerᴳ

wfA : T.WfTy zero A
wfA = wf∀ (wf⇒ (wfVar z<s) (wfVar z<s))

wfG : T.WfTy zero G
wfG = wf⇒ wf★ wf★

x★ : ((zero Imp.ˣ⊑★) ∷ []) ∣ suc zero ⊢ X ⊑ ★ ⊣ zero
x★ = ImprecisionWf.tagˣ (here refl) z<s

p : [] ∣ zero ⊢ A ⊑ ★ ⊣ zero
p = ImprecisionWf.ν refl (tag x★ ⇛ x★)

q : [] ∣ zero ⊢ A ⊑ G ⊣ zero
q = ImprecisionWf.ν refl (x★ ↦ x★)

star~nat : zero Imp.⊢ ★ ~ HNat
star~nat = HNat , (Imp.tag T.`ℕ) , Imp.idι

A~star : zero Imp.⊢ A ~ ★
A~star = A , ⊑-refl-idᵢ wfA , ⊑-forgetᵢ p

G⊑★ : [] ∣ zero ⊢ G ⊑ ★ ⊣ zero
G⊑★ = tag id★ ⇛ id★

G~star : zero Imp.⊢ G ~ ★
G~star = G , ⊑-refl-idᵢ wfG , ⊑-forgetᵢ G⊑★

id-star-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ idᴳ ★ ⊑ idᴳ ★ ⦂ G ⊑ G ∶ id★ ↦ id★
id-star-relation = ƛ⊑ƛᴳ wf★ wf★ (x⊑xᴳ Z)

nat-producer-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ nat-producerᴳ ⊑ nat-producerᴳ ⦂ ★ ⊑ ★ ∶ id★
nat-producer-relation =
  ·⊑·ᴳ id-star-relation κ⊑κᴳ star~nat star~nat

outer-function-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ idᴳ A ⊑ idᴳ G ⦂ A ⇒ A ⊑ G ⇒ G ∶ q ↦ q
outer-function-relation = ƛ⊑ƛᴳ wfA wfG (x⊑xᴳ Z)

public-mismatch-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ source-programᴳ ⊑ target-programᴳ ⦂ A ⊑ G ∶ q
public-mismatch-relation =
  ·⊑·ᴳ outer-function-relation nat-producer-relation
    A~star G~star

source-program-typing : zero ∣ [] ⊢ source-programᴳ ⦂ A
source-program-typing =
  gradual-term-imprecision-source-typing public-mismatch-relation

target-program-typing : zero ∣ [] ⊢ target-programᴳ ⦂ G
target-program-typing =
  gradual-term-imprecision-target-typing public-mismatch-relation

gG : T.Ground G
gG = T.★⇒★

gNat : T.Ground HNat
gNat = T.‵ T.`ℕ

body : C.Coercion
body = (X C.!) C.↦ (X C.？)

body-typing :
  C.genᵈ C.tag-or-idᵈ ∣ suc zero ∣ []
    ⊢ body ∶ G =⇒ (X ⇒ X)
body-typing =
  C.cast-fun
    (C.cast-tag (wfVar z<s) (T.＇ zero) refl)
    (C.cast-untag (wfVar z<s) (T.＇ zero) refl)

body-safe : NW.GenSafe body
body-safe = NW.safe-fun (NW.tag (T.＇ zero)) (NW.untag (T.＇ zero))

source-down : C.Coercion
source-down = (G C.？) C.︔ C.gen G body

source-down-typing :
  C.tag-or-idᵈ ∣ zero ∣ [] ⊢ source-down ∶ ★ =⇒ A
source-down-typing =
  C.cast-seq
    (C.cast-untag wfG gG refl)
    (C.cast-gen wfG refl body-typing)

source-down-narrowing :
  C.tag-or-idᵈ ∣ zero ∣ [] ⊢ source-down ∶ ★ ⊒ A
source-down-narrowing =
  source-down-typing , NW.fun-untag-gen body-safe

source-down-compiler-agreement :
  proj₁
    (coerce-downⁿᵐ label wfA wf★
      (realizes-idᵢᴺᵂ zero) (⊑-forgetᵢ p))
    ≡ source-down
source-down-compiler-agreement = refl

target-down : C.Coercion
target-down = G C.？

target-down-compiler-agreement :
  proj₁
    (coerce-downⁿᵐ label wfG wf★
      (realizes-idᵢᴺᵂ zero) (⊑-forgetᵢ G⊑★))
    ≡ target-down
target-down-compiler-agreement = refl

WNat : Term
WNat = $ (P.κℕ zero)

taggedNat : Term
taggedNat = WNat ⟨ HNat C.! ⟩

source-redex : Term
source-redex = taggedNat ⟨ source-down ⟩

target-redex : Term
target-redex = taggedNat ⟨ target-down ⟩

vWNat : Value WNat
vWNat = $ (P.κℕ zero)

noWNat : No• WNat
noWNat = no•-$

vTaggedNat : Value taggedNat
vTaggedNat = vWNat ⟨ HNat C.! ⟩

noTaggedNat : No• taggedNat
noTaggedNat = no•-⟨⟩ noWNat

source-runtime : RuntimeOK source-redex
source-runtime = ok-no (no•-⟨⟩ noTaggedNat)

target-runtime : RuntimeOK target-redex
target-runtime = ok-no (no•-⟨⟩ noTaggedNat)

nat-not-function-ground : HNat ≢ G
nat-not-function-ground ()

source-blame-trace :
  source-redex —↠[ keep ∷ keep ∷ keep ∷ [] ] blame
source-blame-trace =
  ↠-step (pure-step (β-seq vTaggedNat))
    (↠-step
      (ξ-⟨⟩ (pure-step
        (tag-untag-bad vWNat nat-not-function-ground)))
      (↠-step (pure-step blame-⟨⟩) ↠-refl))

target-blame-trace :
  target-redex —↠[ keep ∷ [] ] blame
target-blame-trace =
  ↠-step
    (pure-step (tag-untag-bad vWNat nat-not-function-ground))
    ↠-refl

module proof.NuImprecisionGenUntagCounterexampleCore where

-- File Charter:
--   * Defines the shared concrete source-`gen`/target-`untag` counterexample.
--   * Provides its syntax, typing, QTI, runtime, and reduction witnesses.
--   * Proves that no final QTI relation can relate its source and target
--     values, even after an arbitrary allocation prefix.
--   * Introduces no record, result, view, theorem alias, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_,_; proj₁; proj₂)

import Coercions as C
open import ImprecisionWf using
  ( ImpCtx
  ; id★
  ; _↦_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; _ˣ⊑★
  ; _∣_⊢_⊑_⊣_
  )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( keep
  ; pure-step
  ; tag-untag-ok
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuTermImprecision using
  ( StoreImp
  ; seal★-tag-or-id
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-`
  ; no•-ƛ
  ; no•-⟨⟩
  ; ok-no
  ; `_
  ; ƛ_
  ; _⟨_⟩
  )
open import PairedWideningCompatibility using
  (compatible-source-inert)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; paired-widening
  ; x⊑xᵀ
  ; ƛ⊑ƛᵀ
  ; ⊑cast⊒ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (cast-tag-or-id)
import Types
open import Types using
  ( Ty
  ; TyCtx
  ; ★
  ; wf★
  ; wfVar
  ; wf⇒
  ; ＇_
  ; _⇒_
  ; `∀
  )
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)


Φ₀ : ImpCtx
Φ₀ = []

Δ₀ : TyCtx
Δ₀ = zero

ρ₀ : StoreImp Φ₀ Δ₀ Δ₀
ρ₀ = []

G : Ty
G = ★ ⇒ ★

X : Ty
X = ＇ zero

A : Ty
A = `∀ (X ⇒ X)

W : Term
W = ƛ (` zero)

tagged : Term
tagged = W ⟨ G C.! ⟩

body-cast : C.Coercion
body-cast = (G C.？) C.︔ ((X C.!) C.↦ (X C.？))

source-gen : C.Coercion
source-gen = C.gen ★ body-cast

V : Term
V = tagged ⟨ source-gen ⟩

target-redex : Term
target-redex = tagged ⟨ G C.？ ⟩

gG : Types.Ground G
gG = Types.★⇒★

tag-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ G C.! ∶ G ⊑ ★
tag-typing =
  C.cast-tag (wf⇒ wf★ wf★) gG refl , NW.tag gG

untag-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ G C.？ ∶ ★ ⊒ G
untag-typing =
  C.cast-untag (wf⇒ wf★ wf★) gG refl , NW.untag gG

body-cast-typing :
  C.genᵈ C.tag-or-idᵈ ∣ suc Δ₀ ∣ []
    ⊢ body-cast ∶ ★ ⊒ (X ⇒ X)
body-cast-typing =
  C.cast-seq
    (C.cast-untag (wf⇒ wf★ wf★) gG refl)
    (C.cast-fun
      (C.cast-tag (wfVar z<s) (Types.＇ zero) refl)
      (C.cast-untag (wfVar z<s) (Types.＇ zero) refl)) ,
  gG NW.？︔
    NW.cn-funˡ
      (NW.strict-tag (Types.＇ zero))
      (NW.untag (Types.＇ zero))

source-gen-typing :
  C.tag-or-idᵈ ∣ Δ₀ ∣ [] ⊢ source-gen ∶ ★ ⊒ A
source-gen-typing =
  C.cast-gen wf★ refl (proj₁ body-cast-typing) ,
  NW.gen (proj₂ body-cast-typing)

x★ :
  ((zero ˣ⊑★) ∷ []) ∣ suc Δ₀ ⊢ X ⊑ ★ ⊣ Δ₀
x★ = tagˣ (here refl) z<s

p : Φ₀ ∣ Δ₀ ⊢ A ⊑ ★ ⊣ Δ₀
p = ν refl (tag x★ ⇛ x★)

q : Φ₀ ∣ Δ₀ ⊢ A ⊑ G ⊣ Δ₀
q = ν refl (x★ ↦ x★)

vW : Value W
vW = ƛ (` zero)

noW : No• W
noW = no•-ƛ no•-`

v-tagged : Value tagged
v-tagged = vW ⟨ G C.! ⟩

no-tagged : No• tagged
no-tagged = no•-⟨⟩ noW

vV : Value V
vV = v-tagged ⟨ C.gen ★ body-cast ⟩

noV : No• V
noV = no•-⟨⟩ no-tagged

W-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ W ⦂ G ⊑ G ∶ id★ ↦ id★
W-relation = ƛ⊑ƛᵀ wf★ wf★ (x⊑xᵀ Types.Z)

tagged-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ tagged ⊑ tagged ⦂ ★ ⊑ ★ ∶ id★
tagged-relation =
  conv⊑convᵀ
    (paired-widening
      cast-tag-or-id seal★-tag-or-id tag-typing
      cast-tag-or-id seal★-tag-or-id tag-typing
      (compatible-source-inert (G C.!)))
    W-relation

V-tagged-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ tagged ⦂ A ⊑ ★ ∶ p
V-tagged-relation =
  cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
    source-gen-typing tagged-relation p

initial-relation :
  Φ₀ ∣ Δ₀ ∣ Δ₀ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ target-redex ⦂ A ⊑ G ∶ q
initial-relation =
  ⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
    untag-typing V-tagged-relation q

exclusive₀ : SourceNameExclusive Φ₀
exclusive₀ () match∈

unique₀ : AssumptionMembershipUnique Φ₀
unique₀ () j

source-runtime : RuntimeOK V
source-runtime = ok-no noV

target-runtime : RuntimeOK target-redex
target-runtime = ok-no (no•-⟨⟩ no-tagged)

target-trace : target-redex —↠[ keep ∷ [] ] W
target-trace =
  ↠-step (pure-step (tag-untag-ok vW)) ↠-refl

no-star-function-index :
  ∀ {Φ : ImpCtx} →
  Φ ∣ Δ₀ ⊢ ★ ⊑ G ⊣ Δ₀ →
  ⊥
no-star-function-index ()

no-star-function-relation :
  ∀ {Φ : ImpCtx} {ρ : StoreImp Φ Δ₀ Δ₀}
    {M N : Term} {r : Φ ∣ Δ₀ ⊢ ★ ⊑ G ⊣ Δ₀} →
  Φ ∣ Δ₀ ∣ Δ₀ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ ★ ⊑ G ∶ r →
  ⊥
no-star-function-relation {r = r} relation =
  no-star-function-index r

final-relation-impossible :
  ∀ {Φ : ImpCtx} {ρ : StoreImp Φ Δ₀ Δ₀}
    {r : Φ ∣ Δ₀ ⊢ A ⊑ G ⊣ Δ₀} →
  Φ ∣ Δ₀ ∣ Δ₀ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ A ⊑ G ∶ r →
  ⊥
final-relation-impossible
    (cast⊒⊑ᵀ mode seal★
      (C.cast-gen h★ occ c⊢ , NW.gen cⁿ) inner oldq) =
  no-star-function-relation inner
final-relation-impossible
    (cast⊑⊑ᵀ mode seal★ (c⊢ , NW.cross ()) inner oldq)
final-relation-impossible
    (conv↑⊑ᵀ () inner oldq)
final-relation-impossible
    (conv↓⊑ᵀ () inner oldq)
final-relation-impossible
    (allocation-prefixᵀ prefix inner V⊢ W⊢) =
  final-relation-impossible inner

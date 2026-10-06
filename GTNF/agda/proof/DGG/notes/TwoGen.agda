module proof.DGG.notes.TwoGen where

-- File Charter:
--   * THE GEN ANALOGUE OF H1 (TwoGen.md).  A LEFT ∀-value built by a
--     `gen` cast, against a RIGHT that instantiates it at ★ (twice, for
--     two binders), from RELATED source programs.  The real relation
--     (TermImprecision at 810b540e: D27 pushes, D28 permissions, D29
--     claim-rep) is imported; nothing outside this directory is edited.
--     LEFT is the more precise side.  No holes, no postulates.
--   * THE PAIRS (left value; right: one inst cast `…m`, or two casts):
--       G0          (λx:★.5 : ∀X.X→ℕ)                  one gen, one Inst
--       G2m, G2     (λx:★.λy:★.x : ∀X.∀Y.X→Y→X)        two gen layers
--       HRm, HR     (ΛX.λx:X.λy:★.x : ∀X.∀Y.X→Y→X)     a gen under a ∀
--       N2.Merged,  ((λx:★.λy:★.x : ∀Y.★→Y→★)           nested gen casts
--       N2.TwoCast    : ∀X.∀Y.X→Y→X)
--     Each: the initial cast terms related at ∅ʷ (`init`), the right's
--     run pinned to `evalTerms`/`eval` (`…-end`, `…-state`).
--   * REAL RELATION: EVERY FINAL PAIR IS UNRELATED, in every world with
--     no permission (G0, G2, HR, HRm, N2: any context; G2m: the final
--     context; N2.Merged: any permission), and so DGG PART 1 FAILS:
--     `G0.not-dgg`, `G2m.not-dgg`, `G2.not-dgg`, `HRm.not-dgg`,
--     `HR.not-dgg`, `N2.not-dgg`, `N2.not-dgg-m`, each `¬ DGG`.  Also
--     G2's intermediate states 2 and 4 (`G2st.g2-st2-unrelated`,
--     `g2-st4-unrelated`).  Two obstructions:
--     (O1) `cc-gen` pops into a premise at the gen's SOURCE type
--          (★ where the binder was), so the right's cast over the gen
--          body must be peeled first by ⊑cast, which needs the popped
--          name X⊑★, i.e. a GRANT; a gen body with no covariant check
--          of its variable (`X! → id(ℕ)`, `Y! → …`) grants nothing.
--          G0 has ONE gen layer.  And `cc-gen` pops exactly one name.
--     (O2) H1's order problem, back for gen binders: with two casts the
--          right's boundaries nest `[+Y^β]` OUTSIDE `[+X^α]`; inside
--          `+Y^β` the index must open the left's INNER ∀ at Y while the
--          outer one waits (`no-K2-★`).  claim-rep cannot help: a gen
--          binder scopes over no left term, so nothing is peeled.
--   * THE FIX (`module V`; V1 = (i)+(ii), V2 = (i)+(ii)+(iii)):
--     (i) cast⊑cast at any world with a claim on the left coercion (a
--     gen pops against the right's cast; no grant needed); (ii) a gen
--     layer pops one name and the claim continues below; (iii) for a
--     left gen-cast value only: the index may SKIP a leading left ∀
--     (left-only, X⊑★) before opening the next at a pending name, and
--     ⊑⟪⟫ may push new names before the carried ones.
--     - V (both): G0, G2m, HRm, N2.Merged derive (`Pos.g0-final`,
--       `g2m-final`, `hrm-final`, `N2.InV2.nrm-final`).
--     - V1: G2 and HR stay unrelated (`InV1.G2ns.g2-unrelated`,
--       `InV1.HRns.hr-unrelated`): (iii) is needed.
--     - V2: G2, HR, N2.TwoCast derive (`Pos2.g2-final`, `hr-final`,
--       `N2.InV2.nr-final`), and G2's states 2, 4
--       (`G2st.InV2.g2-st2`, `g2-st4`); DGG part 1 holds on all of
--       them (`DGG1.*`, `N2.DGG1ᴺ.*`).
--     - The real relation is a sub-relation (`V.fromReal`), so the
--       corpus derives (`Corpus.*`: H1, K, P3 = Ch X0, Cg X0, C2 X0,
--       G1, C12, L3c, L3d, P4).
--     - C1-C5, C4g stay dead in V1 and V2 (`Dead1.*`, `Dead2.*`): their
--       left terms are gen-free, and on a gen-free left V adds no
--       derivation (`V.Back.back`).
--   * Not a Def module; All.agda does not import it.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; head; drop; length; map; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms)
open import examples.CambridgeExamples using (K★; genK; instK)
open import examples.Examples using (ℓ)
open import examples.TermImprecisionH1Examples
  using (K2; instX∀; instY; ci; cf; cX; cY; ΘX; ΘY; ΔT2; ΔXY; ΔY; q-top;
         q-src1; src-1; src-2; instX∀-ty; instY-ty₀)
open import Imprecision
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.ImprecisionTyping using (imprecision-typing)
open import proof.TypeSafety.CoercionTyping using (coercion-src; coercion-trg)
open import examples.TermImprecisionPermissionExamples
  using (no★-right; NoGrant; cg-none; NonForall; nf-⇒; plain-idx;
         dmarks-emb; lookup-unique; var⊑var;
         module Runs)
open Runs using (all-reach)
open import Reduction
  using (_⊢_-→_∣_; _⊢_-→*_; done; _then_; runCtx; value-¬step)
open import proof.TypeSafety.Determinism using (det)
open import examples.Eval
  using (eval; Trace; stop; illtyped; _◅⟨_⟩_; value; blamed; no-redex;
         out-of-fuel; traceEnd; traceCtx)
open import Data.Unit using (⊤)
open import DynamicGradualGuarantee using (DGG)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- Tools: types read off the typings of a derivation
------------------------------------------------------------------------

ltyT : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ q → Δ ∣ lhs γ ⊢ M ⦂ A
ltyT d = proj₁ (imprecision-typing d)

rtyT : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ q → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
rtyT d = proj₂ (imprecision-typing d)

ty-cast : ∀ {Γ M μ p A} → Δ ∣ Γ ⊢ M ⟨ μ ∣ p ⟩ ⦂ A → A ≡ trgᵖ p
ty-cast (⊢cast _ ⊢p _) = sym (coercion-trg ⊢p)

ct-src : ∀ {μ p B A} → CastTy Δ μ p B A → B ≡ srcᵖ p
ct-src (cast-ty ⊢p _) = sym (coercion-src ⊢p)

ct-trg : ∀ {μ p B A} → CastTy Δ μ p B A → A ≡ trgᵖ p
ct-trg (cast-ty ⊢p _) = sym (coercion-trg ⊢p)

ty-ƛ : ∀ {Γ A₀ N A} → Δ ∣ Γ ⊢ ƛ A₀ ∙ N ⦂ A
  → Σ[ B ∈ Ty ] (A ≡ A₀ ⇒ B) × (Δ ∣ A₀ ∷ Γ ⊢ N ⦂ B)
ty-ƛ (⊢ƛ _ ⊢N) = _ , refl , ⊢N

-- the index at a world with exactly one pending name
idx1 : ∀ {W : World Δ Δ′} {A A′ k} → πʷ W ≡ k ∷ [] → A ⊑ᵂ⟨ W ⟩ A′
  → OpenImp (marksʷ W) (emb (ηᴿʷ W) k ∷ []) (emb (ηᴸʷ W)) A (embᴿ W A′)
idx1 {W = W} {A} {A′} e q =
  subst (λ π → OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) π) (emb (ηᴸʷ W)) A
                 (embᴿ W A′)) e q

-- ... and with none
idx0 : ∀ {W : World Δ Δ′} {A A′} → πʷ W ≡ [] → A ⊑ᵂ⟨ W ⟩ A′
  → marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′
idx0 {W = W} {A} {A′} e q =
  subst (λ π → OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) π) (emb (ηᴸʷ W)) A
                 (embᴿ W A′)) e q

-- a pending name is a right name
pend-name : ∀ {W : World Δ Δ′} {k} → WfWorld W → πʷ W ≡ k ∷ []
  → Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β)
pend-name {W = W} wf e with subst (All (PendingOK W)) e (wf-pending wf)
... | (β , rh , _) ∷ [] = β , rh

------------------------------------------------------------------------
-- The programs
------------------------------------------------------------------------

-- two gen layers:  (λx:★.λy:★.x : ∀X.∀Y.X→Y→X)
GL : Term
GL = K★ ⟨ [] ∣ genK ⟩

GL-⊢ : empty ∣ [] ⊢ GL ⦂ K2
GL-⊢ = tc

-- ... against two casts:  ((GL-source : ∀Y.★→Y→★) : ★→★→★)
GR : Term
GR = (GL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩
GR-⊢ : empty ∣ [] ⊢ GR ⦂ ★ ⇒ (★ ⇒ ★)
GR-⊢ = tc

-- ... and against one cast:  (GL-source : ★→★→★)
GRm : Term
GRm = GL ⟨ [] ∣ instK ⟩
GRm-⊢ : empty ∣ [] ⊢ GRm ⦂ ★ ⇒ (★ ⇒ ★)
GRm-⊢ = tc

-- gen over Λ: (ΛX.λx:X.λy:★.x : ∀X.∀Y.X→Y→X)
NΛ KΛ : Term
NΛ = ƛ (` 0) ∙ (ƛ ★ ∙ ` 1)
KΛ = Λ NΛ
pH : Coercion
pH = idᵖ (` 1) ↦ᵖ (((` 0) !) ↦ᵖ idᵖ (` 1))
∀gen : Coercion
∀gen = ∀ᵖ (genᵖ pH)
HL : Term
HL = KΛ ⟨ [] ∣ ∀gen ⟩
HL-⊢ : empty ∣ [] ⊢ HL ⦂ K2
HL-⊢ = tc
HR HRm : Term
HR = (HL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩
HR-⊢ : empty ∣ [] ⊢ HR ⦂ ★ ⇒ (★ ⇒ ★)
HR-⊢ = tc
HRm = HL ⟨ [] ∣ instK ⟩
HRm-⊢ : empty ∣ [] ⊢ HRm ⦂ ★ ⇒ (★ ⇒ ★)
HRm-⊢ = tc

-- one gen, no covariant check of its variable:  (λx:★. 5 : ∀X. X→ℕ)
I5 : Term
I5 = ƛ ★ ∙ $ 5
genX5 instX5 : Coercion
genX5 = genᵖ (((` 0) !) ↦ᵖ idᵖ `ℕ)
instX5 = instᵖ (((` 0) ？ 0) ↦ᵖ idᵖ `ℕ)
FL FR : Term
FL = I5 ⟨ [] ∣ genX5 ⟩
FL-⊢ : empty ∣ [] ⊢ FL ⦂ `∀ (` 0 ⇒ `ℕ)
FL-⊢ = tc
FR = FL ⟨ [] ∣ instX5 ⟩
FR-⊢ : empty ∣ [] ⊢ FR ⦂ ★ ⇒ `ℕ
FR-⊢ = tc

-- Λ over gen (a cast-calculus term; no source under ⊢Λ's value
-- restriction, since an ascription is not a source value)
ΛG : Term
ΛG = Λ (NΛ ⟨ X∼X ∷ [] ∣ genᵖ pH ⟩)
ΛG-⊢ : empty ∣ [] ⊢ ΛG ⦂ K2
ΛG-⊢ = tc


-- the index at a world with known pending names
idxπ : ∀ {W : World Δ Δ′} {A A′ π} → πʷ W ≡ π → A ⊑ᵂ⟨ W ⟩ A′
  → OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) π) (emb (ηᴸʷ W)) A (embᴿ W A′)
idxπ {W = W} {A} {A′} e q =
  subst (λ π → OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) π) (emb (ηᴸʷ W)) A
                 (embᴿ W A′)) e q

-- the pending names are right names
pend-all : ∀ {W : World Δ Δ′} {π} → WfWorld W → πʷ W ≡ π
  → All (λ k → Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β)) π
pend-all {Δ′ = Δ′} {W = W} wf e =
  go (subst (All (PendingOK W)) e (wf-pending wf))
  where
  go : ∀ {π} → All (PendingOK W) π → All (λ k → Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β)) π
  go [] = []
  go ((β , rh , _) ∷ ps) = (β , rh) ∷ go ps

ty-Λ : ∀ {Γ N A} → Δ ∣ Γ ⊢ Λ N ⦂ A
  → Σ[ C ∈ Ty ] (A ≡ `∀ C) × (underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C)
ty-Λ (⊢Λ _ ⊢N) = _ , refl , ⊢N

-- the left types of K★ and of λx:X.λy:★.x: ★ in the middle
ty-K★ : ∀ {Γ A} → Δ ∣ Γ ⊢ K★ ⦂ A → Σ[ B ∈ Ty ] A ≡ ★ ⇒ (★ ⇒ B)
ty-K★ ⊢M with ty-ƛ ⊢M
... | _ , refl , ⊢N with ty-ƛ ⊢N
... | _ , refl , _ = _ , refl

ty-NΛ : ∀ {Γ A} → Δ ∣ Γ ⊢ NΛ ⦂ A → Σ[ B ∈ Ty ] A ≡ ` 0 ⇒ (★ ⇒ B)
ty-NΛ ⊢M with ty-ƛ ⊢M
... | _ , refl , ⊢N with ty-ƛ ⊢N
... | _ , refl , _ = _ , refl

ty-KΛ : ∀ {Γ A} → Δ ∣ Γ ⊢ KΛ ⦂ A → Σ[ B ∈ Ty ] A ≡ `∀ (` 0 ⇒ (★ ⇒ B))
ty-KΛ ⊢M with ty-Λ ⊢M
... | _ , refl , ⊢N with ty-NΛ ⊢N
... | _ , refl = _ , refl

-- a run to a value ends at the trace's end, in the trace's context
EndsV : ∀ {Δ A M} → Trace Δ A M → Set
EndsV (stop (value _))   = ⊤
EndsV (stop (blamed _))  = ⊥
EndsV (stop no-redex)    = ⊥
EndsV (stop out-of-fuel) = ⊥
EndsV (illtyped _)       = ⊥
EndsV (_ ◅⟨ _ ⟩ tr)      = EndsV tr

final-of : ∀ {Δ A M N} (tr : Trace Δ A M) → Δ ∣ [] ⊢ M ⦂ A → EndsV tr
  → (r : Δ ⊢ M -→* N) → Value N → (N ≡ traceEnd tr) × (runCtx r ≡ traceCtx tr)
final-of (stop (value v)) ⊢M e done vN = refl , refl
final-of (stop (value v)) ⊢M e (st then r) vN = ⊥-elim (value-¬step v st)
final-of (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e done vN = ⊥-elim (value-¬step vN st)
final-of (st ◅⟨ ⊢M′ ⟩ tr) ⊢M e (st′ then r) vN with det ⊢M st st′
... | refl , refl = final-of tr ⊢M′ e r vN

------------------------------------------------------------------------
-- G0
------------------------------------------------------------------------

module G0 where
  pF : Coercion
  pF = ((` 0) !) ↦ᵖ idᵖ `ℕ

  cU0 cB0 : Conv
  cU0 = tail (mid (tail (mid (id ★)) ↦ tail (mid (id `ℕ))))
  cB0 = tail (mid (tail (seal 0) ↦ tail (mid (id `ℕ))))

  UF IF BF FR₁ FR₂ : Term
  UF  = I5 ⟪ unbind 0 0 ∷ [] , cU0 ⟫
  IF  = UF ⟨ ★∼X ∷ [] ∣ pF ⟩
  BF  = IF ⟪ bind 0 0 ∷ [] , cB0 ⟫
  FR₁ = (ν ★ · FL ⟨ cB0 ⟩) ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ `ℕ ⟩
  FR₂ = BF ⟨ [] ∣ idᵖ ★ ↦ᵖ idᵖ `ℕ ⟩

  FR-states : evalTerms 20 FR-⊢ ≡ FR ∷ FR₁ ∷ FR₂ ∷ []
  FR-states = refl

  ng-pF : NoGrant pF
  ng-pF (gr-↦ _ ())

  ng-id★ℕ : NoGrant (idᵖ ★ ↦ᵖ idᵖ `ℕ)
  ng-id★ℕ (gr-↦ _ ())

  -- the left's λ against the right's tag cast `X! → id(ℕ)`: ★ ⊑ X
  noA′ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ I5 ⊑ IF ∶ q)
  noA′ {W = W} {q = q} d with ty-ƛ (ltyT d) | ty-cast (rtyT d)
  ... | _ , refl , _ | refl with plain-idx {V = W} nf-⇒ q
  ... | ⇒⊑⇒ () _

  noA : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ I5 ⊑ BF ∶ q)
  noA (⊑⟪⟫ _ _ _ d _ _) = noA′ d

  noB : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ I5 ⊑ FR₂ ∶ q)
  noB (⊑cast _ _ d _ _) = noA d

  -- the left gen value against the tag cast, inside +X^α
  noD : ∀ {Δ′} {W : World empty Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ FL ⊑ IF ∶ q)
  noD {W = W} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = go (πʷ W) refl d
    where
    go : ∀ π → πʷ W ≡ π → ¬ (W ∣ _ ⊢ FL ⊑ IF ∶ q)
    go [] e _ with idx0 {W = W} e q
    ... | ∀⊑ _ _ (⇒⊑⇒ () _)
    go (k ∷ _ ∷ _) e _ = subst (λ π → OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) π)
      (emb (ηᴸʷ W)) (`∀ (` 0 ⇒ `ℕ)) (embᴿ W (` 0 ⇒ `ℕ))) e q
    go (k ∷ []) () (cast⊑cast _ _ _ _)
    go (k ∷ []) e (cast⊑ {πₚ = πₚ} {p = p} _ _ ct _) with ct-src ct
    ... | refl with plain-idx {V = record W { πʷ = πₚ }} nf-⇒ p
    ... | ⇒⊑⇒ () _
    go (k ∷ []) e (⊑cast {κₚ = κₚ} {p = p} g _ _ ct _) with ct-src ct
    ... | refl with idx1 {W = record W { κʷ = κₚ }} e p | pend-name wf e
    ... | ⇒⊑⇒ (X⊑★ h) _ | β , rh =
      no★-right {V = record W { κʷ = κₚ }} (trans (cg-none ng-pF g) eκ) rh h

  noC : ∀ {Δ′} {W : World empty Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ FL ⊑ BF ∶ q)
  noC eκ (cast⊑ _ d _ _) = noA d
  noC eκ (⊑⟪⟫ I _ wf d _ _) = noD (trans (same-κ I) eκ) wf d

  -- G0's final pair is related in NO world with no permission
  g0-unrelated : ∀ {Δ′} {W : World empty Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ FL ⊑ FR₂ ∶ q)
  g0-unrelated eκ (cast⊑cast d _ _ _) = noA d
  g0-unrelated eκ (cast⊑ _ d _ _) = noB d
  g0-unrelated eκ (⊑cast g _ d _ _) = noC (trans (cg-none ng-id★ℕ g) eκ) d

  -- sources: (λx:★. 5 : ∀X. X→ℕ) and ((λx:★. 5 : ∀X. X→ℕ) : ★→ℕ)
  src : [] ⊢ `∀ (` 0 ⇒ `ℕ) ⊑ (★ ⇒ `ℕ)
  src = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ))

  genX5-ty : CastTy empty [] genX5 (★ ⇒ `ℕ) (`∀ (` 0 ⇒ `ℕ))
  genX5-ty = proj₂ (proj₂ (cast-inv {Γ = []} FL-⊢))

  instX5-ty : CastTy empty [] instX5 (`∀ (` 0 ⇒ `ℕ)) (★ ⇒ `ℕ)
  instX5-ty = proj₂ (proj₂ (cast-inv {Γ = []} FR-⊢))

  q0 : ∀ {μ} → μ ⊢ `∀ (` 0 ⇒ `ℕ) ⊑ (★ ⇒ `ℕ)
  q0 = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ))

  -- the initial cast terms are related
  init : ∅ʷ ∣ [] ⊢ FL ⊑ FR ∶ q0
  init =
    ⊑cast₀
      (cast⊑cast (ƛ⊑ƛ {pA = ★⊑★} tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ)))
        genX5-ty genX5-ty (∀⊑∀ (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ))))
      instX5-ty q0

  vFL : Value FL
  vFL = V-simple (S-cast (V-simple S-ƛ) I-gen)

  FR-nv : ¬ Value FR
  FR-nv (V-simple (S-cast _ ()))

  FR₁-nv : ¬ Value FR₁
  FR₁-nv (V-simple (S-cast (V-simple ()) _))

  -- every value the right reaches is FR₂
  only-FR₂ : ∀ {N} → empty ⊢ FR -→* N → Value N → N ≡ FR₂
  only-FR₂ r = all-reach {P = λ N → Value N → N ≡ FR₂} 20 FR-⊢ tt
    ((λ v → ⊥-elim (FR-nv v)) ∷ (λ v → ⊥-elim (FR₁-nv v)) ∷ (λ _ → refl)
      ∷ []) r

  -- THE DGG FAILS: part 1 on (FL, FR), whose left is a value
  not-dgg : ¬ DGG
  not-dgg dgg with proj₁ (dgg init) done vFL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d with only-FR₂ r′ vV′
  ... | refl = g0-unrelated eκ d

------------------------------------------------------------------------
-- Shared: the right pieces and the index lemmas
------------------------------------------------------------------------

cU cXY cUH : Conv
cU  = tail (mid (tail (mid (id ★))
        ↦ tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))))
cXY = tail (mid (tail (seal 1) ↦ tail (mid (tail (seal 0) ↦ unseal 1))))
cUH = tail (mid (tail (mid (id (` 1)))
        ↦ tail (mid (tail (mid (id ★)) ↦ tail (mid (id (` 1)))))))

pK : Coercion
pK = ((` 1) !) ↦ᵖ (((` 0) !) ↦ᵖ ((` 1) ？ ℓ))

U2 ΘXY : Boundary
U2  = unbind 0 1 ∷ unbind 0 0 ∷ []
ΘXY = bind 1 1 ∷ bind 0 0 ∷ []

-- the gen bodies after the right's two TyBetas: `[−Y^β, −X^α] K★ ⟨…⟩`
-- under `X! → Y! → X?`, and `[−Y^β] (λx:X.λy:★.x) ⟨…⟩` under
-- `id(X) → Y! → id(X)`
UK CK UH CH : Term
UK = K★ ⟪ U2 , cU ⟫
CK = UK ⟨ ★∼X ∷ ★∼X ∷ [] ∣ pK ⟩
UH = NΛ ⟪ unbind 0 0 ∷ [] , cUH ⟫
CH = UH ⟨ ★∼X ∷ X∼X ∷ [] ∣ pH ⟩

ng-cf : NoGrant cf
ng-cf (gr-↦ _ (gr-↦ _ ()))

ng-pH : NoGrant pH
ng-pH (gr-↦ _ (gr-↦ _ ()))

no-cc2 : ∀ {M c k k′ πₚ} → ¬ CastClaim M (genᵖ c) (k ∷ k′ ∷ []) πₚ
no-cc2 ()

-- projections of an arrow imprecision
dom⇒ : ∀ {μ A B A′ B′} → μ ⊢ A ⇒ B ⊑ A′ ⇒ B′ → μ ⊢ A ⊑ A′
dom⇒ (⇒⊑⇒ p _) = p
dom⇒ (ι⊑ι ())

cod⇒ : ∀ {μ A B A′ B′} → μ ⊢ A ⇒ B ⊑ A′ ⇒ B′ → μ ⊢ B ⊑ B′
cod⇒ (⇒⊑⇒ _ p) = p
cod⇒ (ι⊑ι ())

-- ★ in the left's middle against a right name: never
no-mid : ∀ {W : World Δ Δ′} {A₁ B R₁ R₃ y}
  → ¬ ((A₁ ⇒ (★ ⇒ B)) ⊑ᵂ⟨ W ⟩ (R₁ ⇒ (` y ⇒ R₃)))
no-mid {W = W} q with plain-idx {V = W} nf-⇒ q
... | ⇒⊑⇒ _ (⇒⊑⇒ () _)

-- ... nor under one ∀, opened or not
no-∀mid : ∀ {W : World Δ Δ′} {A₁ B R₁ R₃ y}
  → ¬ (`∀ (A₁ ⇒ (★ ⇒ B)) ⊑ᵂ⟨ W ⟩ (R₁ ⇒ (` y ⇒ R₃)))
no-∀mid {W = W} {A₁} {B} {R₁} {R₃} {y} q = go (πʷ W) refl
  where
  go : ∀ π → πʷ W ≡ π → ⊥
  go [] e with idxπ {W = W} e q
  ... | ∀⊑ _ _ (⇒⊑⇒ _ (⇒⊑⇒ () _))
  go (_ ∷ []) e with idxπ {W = W} e q
  ... | ⇒⊑⇒ _ (⇒⊑⇒ () _)
  go (_ ∷ _ ∷ _) e = idxπ {W = W} e q

-- K2 = ∀X.∀Y.X→Y→X against a right type with a NAME in the middle,
-- with at most one name opened
K2-01 : ∀ {W : World Δ Δ′} {R₁ R₃ y π} → πʷ W ≡ π → length π ≢ 2
  → ¬ (K2 ⊑ᵂ⟨ W ⟩ (R₁ ⇒ (` y ⇒ R₃)))
K2-01 {W = W} {π = []} e _ q with idxπ {W = W} e q
... | ∀⊑ _ _ (∀⊑ _ _ (⇒⊑⇒ _ (⇒⊑⇒ () _)))
K2-01 {W = W} {π = _ ∷ []} e _ q with idxπ {W = W} e q
... | ∀⊑ _ _ (⇒⊑⇒ _ (⇒⊑⇒ () _))
K2-01 {π = _ ∷ _ ∷ []} e n q = n refl
K2-01 {W = W} {π = _ ∷ _ ∷ _ ∷ _} e _ q = idxπ {W = W} e q

-- ... and against ★ → Y → ★ (the outer Inst boundary of a two-cast
-- right): with two names opened the left's X faces ★ at a name the
-- right sees, which needs a permission
no-K2-★ : ∀ {W : World Δ Δ′} {R₃ y} → κʷ W ≡ [] → WfWorld W
  → ¬ (K2 ⊑ᵂ⟨ W ⟩ (★ ⇒ (` y ⇒ R₃)))
no-K2-★ {W = W} eκ wf q = go (πʷ W) refl
  where
  go : ∀ π → πʷ W ≡ π → ⊥
  go (k ∷ k′ ∷ []) e with idxπ {W = W} e q | pend-all wf e
  ... | ⇒⊑⇒ (X⊑★ h) _ | (β , rh) ∷ _ = no★-right {V = W} eκ rh h
  go [] e = K2-01 {W = W} {R₁ = ★} e (λ ()) q
  go (_ ∷ []) e = K2-01 {W = W} {R₁ = ★} e (λ ()) q
  go (_ ∷ _ ∷ _ ∷ _) e = K2-01 {W = W} {R₁ = ★} e (λ ()) q

-- the left types: K★, λx:X.λy:★.x, ΛX.λx:X.λy:★.x
data LeftMid : Term → Set where
  lm-K★ : LeftMid K★
  lm-NΛ : LeftMid NΛ

lm-ty : ∀ {M Γ A} → LeftMid M → Δ ∣ Γ ⊢ M ⦂ A
  → Σ[ A₁ ∈ Ty ] Σ[ B ∈ Ty ] A ≡ A₁ ⇒ (★ ⇒ B)
lm-ty lm-K★ ⊢M with ty-K★ ⊢M
... | _ , refl = _ , _ , refl
lm-ty lm-NΛ ⊢M with ty-NΛ ⊢M
... | _ , refl = _ , _ , refl

-- a left term with ★ in its middle against a right cast whose target
-- has a name in its middle
no-lm-cast : ∀ {W : World Δ Δ′} {γ M U μ p A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → LeftMid M → (∀ {R} → trgᵖ p ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ]
                                Σ[ R₃ ∈ Ty ] R ≡ R₁ ⇒ (` y ⇒ R₃))
  → ¬ (W ∣ γ ⊢ M ⊑ U ⟨ μ ∣ p ⟩ ∶ q)
no-lm-cast {W = W} {q = q} lm tp d with lm-ty lm (ltyT d) | ty-cast (rtyT d)
... | _ , _ , refl | e with tp (sym e)
... | _ , _ , _ , refl = no-mid {W = W} q

no-KΛ-cast : ∀ {W : World Δ Δ′} {γ U μ p A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → (∀ {R} → trgᵖ p ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ]
                            Σ[ R₃ ∈ Ty ] R ≡ R₁ ⇒ (` y ⇒ R₃))
  → ¬ (W ∣ γ ⊢ KΛ ⊑ U ⟨ μ ∣ p ⟩ ∶ q)
no-KΛ-cast {W = W} {q = q} tp d with ty-KΛ (ltyT d) | ty-cast (rtyT d)
... | _ , refl | e with tp (sym e)
... | _ , _ , _ , refl = no-∀mid {W = W} q

-- the targets of the right casts ci (★ → Y → ★), pK and pH (X → Y → X)
tp-ci : ∀ {R} → trgᵖ ci ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ] Σ[ R₃ ∈ Ty ]
  R ≡ R₁ ⇒ (` y ⇒ R₃)
tp-ci refl = _ , _ , _ , refl

tp-pK : ∀ {R} → trgᵖ pK ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ] Σ[ R₃ ∈ Ty ]
  R ≡ R₁ ⇒ (` y ⇒ R₃)
tp-pK refl = _ , _ , _ , refl

tp-pH : ∀ {R} → trgᵖ pH ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ] Σ[ R₃ ∈ Ty ]
  R ≡ R₁ ⇒ (` y ⇒ R₃)
tp-pH refl = _ , _ , _ , refl

-- the left values and the shared positive pieces
vGL : Value GL
vGL = V-simple (S-cast (V-simple S-ƛ) I-gen)

vNΛ : Value NΛ
vNΛ = V-simple S-ƛ

vHL : Value HL
vHL = V-simple (S-cast (V-simple (S-Λ vNΛ)) I-∀ᵖ)

genK-ty : CastTy empty [] genK (★ ⇒ (★ ⇒ ★)) K2
genK-ty = proj₂ (proj₂ (cast-inv {Γ = []} GL-⊢))

∀gen-ty : CastTy empty [] ∀gen (`∀ (` 0 ⇒ (★ ⇒ ` 0))) K2
∀gen-ty = proj₂ (proj₂ (cast-inv {Γ = []} HL-⊢))

instK-ty : CastTy empty [] instK K2 (★ ⇒ (★ ⇒ ★))
instK-ty = proj₂ (proj₂ (cast-inv {Γ = []} GRm-⊢))

idK2 : ∀ {μ} → μ ⊢ K2 ⊑ K2
idK2 = ∀⊑∀ (∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)))

-- K★ ⊑ K★ and KΛ ⊑ KΛ at the closed world
K★⊑K★ : ∅ʷ ∣ [] ⊢ K★ ⊑ K★ ∶ ⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)
K★⊑K★ = ƛ⊑ƛ tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} tf tf (x⊑x (Sʷ Zʷ)))

KΛ⊑KΛ : ∅ʷ ∣ [] ⊢ KΛ ⊑ KΛ ∶ ∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X))
KΛ⊑KΛ =
  Λ⊑Λ lift-[] vNΛ vNΛ
    (ƛ⊑ƛ {pA = X⊑X} tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
    (∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)))

GL⊑GL : ∅ʷ ∣ [] ⊢ GL ⊑ GL ∶ idK2
GL⊑GL = cast⊑cast K★⊑K★ genK-ty genK-ty idK2

HL⊑HL : ∅ʷ ∣ [] ⊢ HL ⊑ HL ∶ idK2
HL⊑HL = cast⊑cast KΛ⊑KΛ ∀gen-ty ∀gen-ty idK2

-- the sources' ascriptions: the left's ∀X.∀Y.X→Y→X against the
-- right's ∀Y.★→Y→★ then ★→★→★ (`src-1`, `src-2` of H1), or against
-- ★→★→★ directly
src-m : [] ⊢ K2 ⊑ (★ ⇒ (★ ⇒ ★))
src-m = q-top

------------------------------------------------------------------------
-- G2m: two gens, one inst cast (the right Merges)
------------------------------------------------------------------------

module G2m where
  BXYm GmF : Term
  BXYm = CK ⟪ ΘXY , cXY ⟫
  GmF  = BXYm ⟨ [] ∣ cf ⟩

  GmF-end : traceEnd (eval 40 GRm GRm-⊢) ≡ GmF
  GmF-end = refl

  GmF-ctx : traceCtx (eval 40 GRm GRm-⊢) ≡ ΔT2
  GmF-ctx = refl

  init : ∅ʷ ∣ [] ⊢ GL ⊑ GRm ∶ q-top
  init = ⊑cast₀ GL⊑GL instK-ty q-top

  -- the merged boundary's interior is ΔXY
  intXYm : ΔT2 ⊢ⁱ ΘXY ⇒ ΔXY
  intXYm = interior (changes∷
    (changes∷ changes[] (step-bind (bindR ★ , here) fresh[] ins-here))
    (step-bind (bindR ★ , there here) (fresh∷ (λ ()) fresh[])
      (ins-there ins-here)))

  kB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ K★ ⊑ BXYm ∶ q)
  kB (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-K★ tp-pK d

  kF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ K★ ⊑ GmF ∶ q)
  kF (⊑cast _ _ d _ _) = kB d

  -- inside the merged boundary: the left's two gens against `X! → Y! →
  -- X?`.  The index needs both names opened (X then Y); then no rule
  -- applies: cast⊑cast needs no pending name, `cc-gen` pops one, and
  -- the right's check grants only X's rep. var, so Y ⊑ ★ fails
  gC : ∀ {W : World empty ΔXY} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ GL ⊑ CK ∶ q)
  gC {W = W} {γ} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = go (πʷ W) refl d
    where
    go : ∀ π → πʷ W ≡ π → ¬ (W ∣ γ ⊢ GL ⊑ CK ∶ q)
    go (k ∷ k′ ∷ []) () (cast⊑cast _ _ _ _)
    go (k ∷ k′ ∷ []) e (cast⊑ cc _ _ _) =
      no-cc2 (subst (λ π → CastClaim _ _ π _) e cc)
    go (k ∷ k′ ∷ []) e (⊑cast {κₚ = κₚ} {p = p} g _ _ ct _)
      with ct-src ct
    ... | refl
      with dom⇒ (cod⇒ (idxπ {W = W} e q))
         | dom⇒ (cod⇒ (idxπ {W = record W { κʷ = κₚ }} e p))
    ... | y⊑ | X⊑★ h =
      noY g (subst (λ c → marksʷ (record W { κʷ = κₚ }) ∋ˡ c := X⊑★)
                   (var⊑var y⊑) h)
      where
      -- Y (name 0, rep. var 0) is X⊑★ only if granted; pK grants rep.
      -- var 1 (X) alone
      noY : CastGrant ΔXY pK (κʷ W) κₚ
        → ¬ (dmarks (ηᴿʷ W) κₚ ∋ˡ emb (ηᴿʷ W) 0 := X⊑★)
      noY no-grant h′
        with trans (lookup-unique h′ (dmarks-emb (ηᴿʷ W) κₚ here))
                   (cong (permit 0) eκ)
      ... | ()
      noY (grant (gr-↦ _ (gr-↦ _ (gr-? (there here))))) h′
        with trans (lookup-unique h′ (dmarks-emb (ηᴿʷ W) κₚ here))
                   (cong (permit 0) eκ)
      ... | ()
    go [] e _ = K2-01 {W = W} e (λ ()) q
    go (_ ∷ []) e _ = K2-01 {W = W} e (λ ()) q
    go (_ ∷ _ ∷ _ ∷ _) e _ = K2-01 {W = W} e (λ ()) q

  gB : ∀ {W : World empty ΔT2} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ BXYm ∶ q)
  gB eκ (cast⊑ _ d _ _) = kB d
  gB eκ (⊑⟪⟫ I _ wf d _ _) with interior-functional (int-right I) intXYm
  ... | refl = gC (trans (same-κ I) eκ) wf d

  -- G2m's FINAL PAIR is related in no world with no permission
  g2m-unrelated : ∀ {W : World empty ΔT2} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ GmF ∶ q)
  g2m-unrelated eκ (cast⊑cast d _ _ _) = kB d
  g2m-unrelated eκ (cast⊑ _ d _ _) = kF d
  g2m-unrelated eκ (⊑cast g _ d _ _) = gB (trans (cg-none ng-cf g) eκ) d

  at : ∀ {Δ′} → Δ′ ≡ ΔT2 → ∀ {W : World empty Δ′} {γ A A′}
    {q : A ⊑ᵂ⟨ W ⟩ A′} → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ GmF ∶ q)
  at refl = g2m-unrelated

  not-dgg : ¬ DGG
  not-dgg dgg with proj₁ (dgg init) done vGL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d
    with final-of (eval 40 GRm GRm-⊢) GRm-⊢ tt r′ vV′
  ... | refl , ec = at ec eκ d

------------------------------------------------------------------------
-- G2: two gens, two inst casts (nested right boundaries, no Merge)
------------------------------------------------------------------------

module G2 where
  BXg CIg BYg GF : Term
  BXg = CK ⟪ ΘX , cX ⟫
  CIg = BXg ⟨ X∼X ∷ [] ∣ ci ⟩
  BYg = CIg ⟪ ΘY , cY ⟫
  GF  = BYg ⟨ [] ∣ cf ⟩

  GF-end : traceEnd (eval 40 GR GR-⊢) ≡ GF
  GF-end = refl

  GF-ctx : traceCtx (eval 40 GR GR-⊢) ≡ ΔT2
  GF-ctx = refl

  init : ∅ʷ ∣ [] ⊢ GL ⊑ GR ∶ q-top
  init = ⊑cast₀ (⊑cast₀ GL⊑GL instX∀-ty q-src1) instY-ty₀ q-top

  kB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ K★ ⊑ BYg ∶ q)
  kB (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-K★ tp-ci d

  kF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ K★ ⊑ GF ∶ q)
  kF (⊑cast _ _ d _ _) = kB d

  -- inside the OUTER boundary +Y^β: the right has one name, Y, and the
  -- left's index K2 opens its OUTER binder first; whatever is pending,
  -- the left's second binder meets Y bound, or its first meets ★ at a
  -- name the right sees
  gY : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ GL ⊑ CIg ∶ q)
  gY {W = W} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = no-K2-★ {W = W} eκ wf q

  gB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ BYg ∶ q)
  gB eκ (cast⊑ _ d _ _) = kB d
  gB eκ (⊑⟪⟫ I _ wf d _ _) = gY (trans (same-κ I) eκ) wf d

  -- G2's FINAL PAIR is related in no world with no permission
  g2-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ GF ∶ q)
  g2-unrelated eκ (cast⊑cast d _ _ _) = kB d
  g2-unrelated eκ (cast⊑ _ d _ _) = kF d
  g2-unrelated eκ (⊑cast g _ d _ _) = gB (trans (cg-none ng-cf g) eκ) d

  not-dgg : ¬ DGG
  not-dgg dgg with proj₁ (dgg init) done vGL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d
    with final-of (eval 40 GR GR-⊢) GR-⊢ tt r′ vV′
  ... | refl , _ = g2-unrelated eκ d

------------------------------------------------------------------------
-- HRm: gen over Λ, one inst cast (Merge)
------------------------------------------------------------------------

module HRm where
  BXYh HmF : Term
  BXYh = CH ⟪ ΘXY , cXY ⟫
  HmF  = BXYh ⟨ [] ∣ cf ⟩

  HmF-end : traceEnd (eval 40 HRm HRm-⊢) ≡ HmF
  HmF-end = refl

  init : ∅ʷ ∣ [] ⊢ HL ⊑ HRm ∶ q-top
  init = ⊑cast₀ HL⊑HL instK-ty q-top

  ΛC : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ KΛ ⊑ CH ∶ q)
  ΛC = no-KΛ-cast tp-pH

  nB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ NΛ ⊑ BXYh ∶ q)
  nB (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-NΛ tp-pH d

  ΛB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ KΛ ⊑ BXYh ∶ q)
  ΛB (⊑⟪⟫ _ _ _ d _ _) = ΛC d
  ΛB (Λ⊑ _ _ _ _ _ d _) = nB d

  nF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ NΛ ⊑ HmF ∶ q)
  nF (⊑cast _ _ d _ _) = nB d

  ΛF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ KΛ ⊑ HmF ∶ q)
  ΛF (⊑cast _ _ d _ _) = ΛB d
  ΛF (Λ⊑ _ _ _ _ _ d _) = nF d

  -- inside the merged boundary: both names must be opened (X then Y);
  -- the gen pops Y only into a premise at ∀X.X→★→X, against X→Y→X; and
  -- the right's `id(X) → Y! → id(X)` grants nothing, so Y ⊑ ★ fails
  hC : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ HL ⊑ CH ∶ q)
  hC {W = W} {γ = γ} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = go (πʷ W) refl d
    where
    go : ∀ π → πʷ W ≡ π → ¬ (W ∣ γ ⊢ HL ⊑ CH ∶ q)
    go (k ∷ k′ ∷ []) () (cast⊑cast _ _ _ _)
    go (k ∷ k′ ∷ []) e (cast⊑ {πₚ = πₚ} {p = p} _ _ ct _) with ct-src ct
    ... | refl = no-∀mid {W = record W { πʷ = πₚ }} p
    go (k ∷ k′ ∷ []) e (⊑cast {κₚ = κₚ} {p = p} g _ _ ct _) with ct-src ct
    ... | refl with dom⇒ (cod⇒ (idxπ {W = record W { κʷ = κₚ }} e p))
                  | pend-all wf e
    ... | X⊑★ h | _ ∷ (β , rh) ∷ [] =
      no★-right {V = record W { κʷ = κₚ }} (trans (cg-none ng-pH g) eκ) rh h
    go [] e _ = K2-01 {W = W} e (λ ()) q
    go (_ ∷ []) e _ = K2-01 {W = W} e (λ ()) q
    go (_ ∷ _ ∷ _ ∷ _) e _ = K2-01 {W = W} e (λ ()) q

  hB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ HL ⊑ BXYh ∶ q)
  hB eκ (cast⊑ _ d _ _) = ΛB d
  hB eκ (⊑⟪⟫ I _ wf d _ _) = hC (trans (same-κ I) eκ) wf d

  hrm-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ HL ⊑ HmF ∶ q)
  hrm-unrelated eκ (cast⊑cast d _ _ _) = ΛB d
  hrm-unrelated eκ (cast⊑ _ d _ _) = ΛF d
  hrm-unrelated eκ (⊑cast g _ d _ _) = hB (trans (cg-none ng-cf g) eκ) d

  not-dgg : ¬ DGG
  not-dgg dgg with proj₁ (dgg init) done vHL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d
    with final-of (eval 40 HRm HRm-⊢) HRm-⊢ tt r′ vV′
  ... | refl , _ = hrm-unrelated eκ d

------------------------------------------------------------------------
-- HR: gen over Λ, two inst casts
------------------------------------------------------------------------

module HR where
  BXh CIh BYh HF : Term
  BXh = CH ⟪ ΘX , cX ⟫
  CIh = BXh ⟨ X∼X ∷ [] ∣ ci ⟩
  BYh = CIh ⟪ ΘY , cY ⟫
  HF  = BYh ⟨ [] ∣ cf ⟩

  HF-end : traceEnd (eval 40 HR HR-⊢) ≡ HF
  HF-end = refl

  init : ∅ʷ ∣ [] ⊢ HL ⊑ HR ∶ q-top
  init = ⊑cast₀ (⊑cast₀ HL⊑HL instX∀-ty q-src1) instY-ty₀ q-top

  nB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ NΛ ⊑ BYh ∶ q)
  nB (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-NΛ tp-ci d

  ΛB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ KΛ ⊑ BYh ∶ q)
  ΛB (⊑⟪⟫ _ _ _ d _ _) = no-KΛ-cast tp-ci d
  ΛB (Λ⊑ _ _ _ _ _ d _) = nB d

  nF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ NΛ ⊑ HF ∶ q)
  nF (⊑cast _ _ d _ _) = nB d

  ΛF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ KΛ ⊑ HF ∶ q)
  ΛF (⊑cast _ _ d _ _) = ΛB d
  ΛF (Λ⊑ _ _ _ _ _ d _) = nF d

  hY : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ HL ⊑ CIh ∶ q)
  hY {W = W} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = no-K2-★ {W = W} eκ wf q

  hB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ HL ⊑ BYh ∶ q)
  hB eκ (cast⊑ _ d _ _) = ΛB d
  hB eκ (⊑⟪⟫ I _ wf d _ _) = hY (trans (same-κ I) eκ) wf d

  hr-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ HL ⊑ HF ∶ q)
  hr-unrelated eκ (cast⊑cast d _ _ _) = ΛB d
  hr-unrelated eκ (cast⊑ _ d _ _) = ΛF d
  hr-unrelated eκ (⊑cast g _ d _ _) = hB (trans (cg-none ng-cf g) eκ) d

  not-dgg : ¬ DGG
  not-dgg dgg with proj₁ (dgg init) done vHL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d
    with final-of (eval 40 HR HR-⊢) HR-⊢ tt r′ vV′
  ... | refl , _ = hr-unrelated eκ d

------------------------------------------------------------------------
-- THE FIX, as a local variant of the relation.  `V SkipOK` is the real
-- relation with
--   (i)   cast⊑cast at ANY world, with a `CastClaimG` on its LEFT
--         coercion: a left gen layer POPS its pending name against a
--         right cast (the right cast's own types then carry the index;
--         no grant is needed);
--   (ii)  `cg-gen` pops one name per gen layer and the claim CONTINUES
--         into the layer below (`gen X. gen Y. p` pops X then Y;
--         `gen X. ∀Y. p` pops X and passes Y on), in cast⊑ and
--         cast⊑cast;
--   (iii) for a left GEN-CAST VALUE only (`SkipOK M`): the index may
--         open a leading left ∀ LEFT-ONLY (`∀⊑`'s X⊑★) before it opens
--         the next one at a pending name (a "skip": the gen analogue of
--         claim-rep, the outer gen binder waits, left-only, for the
--         inner right boundary that names its instantiation), and
--         ⊑⟪⟫ may push the new names BEFORE the carried ones.
-- `V1 = V (λ _ → ⊥)` has (i) and (ii) only; `V2 = V GenCastValue` has
-- all three.  The index is `_⊑ˢ⟨_⟩_` (`OpenImpS`); at a world with no
-- pending name it is the plain index, definitionally.  A rule whose
-- world may have pending names takes `OkIx M q`: its index has no skip,
-- or its left term is allowed to skip.
------------------------------------------------------------------------

OpenImpS : ImpEnv → List ℕ → Renameᵗ → Ty → Ty → Set
OpenImpS μ []       ρ A        B = μ ⊢ renameᵗ ρ A ⊑ B
OpenImpS μ (c ∷ cs) ρ (`∀ A)   B =
  OpenImpS μ cs (c ⊳ ρ) A B
  ⊎ (NonVar A × 0 ∈ᵗ A
     × OpenImpS (instᵐ μ) (map suc (c ∷ cs)) (extᵗ ρ) A (⇑ᵗ B))
OpenImpS μ (c ∷ cs) ρ (` X)    B = ⊥
OpenImpS μ (c ∷ cs) ρ `ℕ       B = ⊥
OpenImpS μ (c ∷ cs) ρ `𝔹       B = ⊥
OpenImpS μ (c ∷ cs) ρ ★        B = ⊥
OpenImpS μ (c ∷ cs) ρ (A ⇒ A′) B = ⊥

infix 4 _⊑ˢ⟨_⟩_
_⊑ˢ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ˢ⟨ W ⟩ A′ =
  OpenImpS (marksʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

SkipFree : ∀ {μ cs ρ A B} → OpenImpS μ cs ρ A B → Set
SkipFree {cs = []}                    _        = ⊤
SkipFree {cs = c ∷ cs} {A = `∀ A}     (inj₁ x) = SkipFree x
SkipFree {cs = c ∷ cs} {A = `∀ A}     (inj₂ _) = ⊥
SkipFree {cs = c ∷ cs} {A = ` X}      _        = ⊤
SkipFree {cs = c ∷ cs} {A = `ℕ}       _        = ⊤
SkipFree {cs = c ∷ cs} {A = `𝔹}       _        = ⊤
SkipFree {cs = c ∷ cs} {A = ★}        _        = ⊤
SkipFree {cs = c ∷ cs} {A = _ ⇒ _}    _        = ⊤

toOI : ∀ {μ cs ρ A B} (x : OpenImpS μ cs ρ A B) → SkipFree x
  → OpenImp μ cs ρ A B
toOI {cs = []}                x        _  = x
toOI {cs = c ∷ cs} {A = `∀ A} (inj₁ x) sf = toOI x sf
toOI {cs = c ∷ cs} {A = `∀ A} (inj₂ _) ()

fromOI : ∀ μ cs ρ A B → OpenImp μ cs ρ A B → OpenImpS μ cs ρ A B
fromOI μ []       ρ A      B x = x
fromOI μ (c ∷ cs) ρ (`∀ A) B x = inj₁ (fromOI μ cs (c ⊳ ρ) A B x)

sf-fromOI : ∀ μ cs ρ A B (x : OpenImp μ cs ρ A B)
  → SkipFree (fromOI μ cs ρ A B x)
sf-fromOI μ []       ρ A      B x = tt
sf-fromOI μ (c ∷ cs) ρ (`∀ A) B x = sf-fromOI μ cs (c ⊳ ρ) A B x

-- at a world
fromOIʷ : ∀ {W : World Δ Δ′} {A A′} → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ˢ⟨ W ⟩ A′
fromOIʷ {W = W} {A} {A′} =
  fromOI (marksʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

sfʷ : ∀ {W : World Δ Δ′} {A A′} (q : A ⊑ᵂ⟨ W ⟩ A′)
  → SkipFree {μ = marksʷ W} {cs = map (emb (ηᴿʷ W)) (πʷ W)}
      {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} (fromOIʷ {W = W} q)
sfʷ {W = W} {A} {A′} =
  sf-fromOI (marksʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

toOIʷ : ∀ {W : World Δ Δ′} {A A′} (q : A ⊑ˢ⟨ W ⟩ A′)
  → SkipFree {μ = marksʷ W} {cs = map (emb (ηᴿʷ W)) (πʷ W)}
      {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} q
  → A ⊑ᵂ⟨ W ⟩ A′
toOIʷ {W = W} {A} {A′} q sf =
  toOI {μ = marksʷ W} {cs = map (emb (ηᴿʷ W)) (πʷ W)}
    {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} q sf

-- (ii) a gen layer pops its pending name and the claim CONTINUES into
-- the layer below (as a ∀ layer passes its name on): one name per gen
-- layer, so `gen X. gen Y. p` pops X then Y, and `gen X. ∀Y. p` pops X
-- and passes Y to the cast value (nested gen casts)
data CastClaimG (M : Term) : Coercion → List ℕ → List ℕ → Set where
  cg-plain : ∀ {c} → CastClaimG M c [] []
  cg-∀     : ∀ {c k π πₚ} → Value M → CastClaimG M c π πₚ
    → CastClaimG M (∀ᵖ c) (k ∷ π) (k ∷ πₚ)
  cg-gen   : ∀ {c k π πₚ} → Value M → CastClaimG M c π πₚ
    → CastClaimG M (genᵖ c) (k ∷ π) πₚ

ccG : ∀ {M c π πₚ} → CastClaim M c π πₚ → CastClaimG M c π πₚ
ccG cc-plain      = cg-plain
ccG (cc-∀ v cc)   = cg-∀ v (ccG cc)
ccG (cc-gen v)    = cg-gen v cg-plain

-- a left gen-cast value: gen layers under ∀ layers
data GenLayer : Coercion → Set where
  gl-gen : ∀ {c} → GenLayer (genᵖ c)
  gl-∀   : ∀ {c} → GenLayer c → GenLayer (∀ᵖ c)

data GenCastValue : Term → Set where
  gcv : ∀ {V μ c} → Value V → GenLayer c → GenCastValue (V ⟨ μ ∣ c ⟩)

-- a left term with no ∀- or gen-cast layer anywhere (the left terms of
-- C1-C5 and C4g): the variant's new derivations need one
NoGA : Coercion → Set
NoGA (∀ᵖ _)   = ⊥
NoGA (genᵖ _) = ⊥
NoGA _        = ⊤

GenFree : Term → Set
GenFree (` _)          = ⊤
GenFree ($ _)          = ⊤
GenFree `true          = ⊤
GenFree `false         = ⊤
GenFree (ƛ _ ∙ N)      = GenFree N
GenFree (L · M)        = GenFree L × GenFree M
GenFree (Λ N)          = GenFree N
GenFree (ν _ · L ⟨ _ ⟩) = GenFree L
GenFree (M ⟪ _ , _ ⟫)  = GenFree M
GenFree (M ⟨ _ ∣ p ⟩)  = NoGA p × GenFree M
GenFree (blame _)      = ⊤

gf-no-gcv : ∀ {M} → GenFree M → ¬ GenCastValue M
gf-no-gcv (() , _) (gcv _ gl-gen)
gf-no-gcv (() , _) (gcv _ (gl-∀ _))

-- a gen-free cast claims nothing
cg-free : ∀ {M c π πₚ} → NoGA c → CastClaimG M c π πₚ
  → (π ≡ []) × (πₚ ≡ [])
cg-free _  cg-plain       = refl , refl
cg-free () (cg-∀ _ _)
cg-free () (cg-gen _ _)

module V (SkipOK : Term → Set) where

  OkIx : ∀ {W : World Δ Δ′} {A A′} → Term → A ⊑ˢ⟨ W ⟩ A′ → Set
  OkIx {W = W} {A} {A′} M q =
    SkipFree {μ = marksʷ W} {cs = map (emb (ηᴿʷ W)) (πʷ W)}
      {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} q ⊎ SkipOK M

  -- (iii) the push may put the new names first, for a skipping left
  data PushV (Θ′ : Boundary) (M : Term) (π : List ℕ) : List ℕ → Set where
    pv-real : ∀ {πᵢ} → Push Θ′ M π πᵢ → PushV Θ′ M π πᵢ
    pv-new  : ∀ {π′ new} → SkipOK M → Carried Θ′ π π′
      → All (Fresh Θ′) new → Value M → PushV Θ′ M π (new ++ π′)

  infix 3 _∣_⊢_⊑ᵛ_∶_

  data _∣_⊢_⊑ᵛ_∶_ {Δ Δ′ : Ctxᵗ}
      : (W : World Δ Δ′) → CtxImp W → Term → Term
      → {A A′ : Ty} → A ⊑ˢ⟨ W ⟩ A′ → Set where

    x⊑x : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ x A A′} {p : A ⊑ᵂ⟨ W ⟩ A′}
      → γ ∋ʷ x ⦂ ctx-imp A A′ p
      → W ∣ γ ⊢ ` x ⊑ᵛ ` x ∶ p

    κ⊑κ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ k ι}
      → Lit k ι
      → (p : ι ⊑ᵂ⟨ W ⟩ ι)
      → W ∣ γ ⊢ k ⊑ᵛ k ∶ p

    ƛ⊑ƛ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ N N′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → Δ ⊢ᵗ A
      → Δ′ ⊢ᵗ A′
      → W ∣ ctx-imp A A′ pA ∷ γ ⊢ N ⊑ᵛ N′ ∶ pB
      → W ∣ γ ⊢ ƛ A ∙ N ⊑ᵛ ƛ A′ ∙ N′ ∶ ⇒⊑⇒ pA pB

    ·⊑· : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ L L′ M M′ A A′ B B′} {pA : A ⊑ᵂ⟨ W ⟩ A′} {pB : B ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ᵛ L′ ∶ ⇒⊑⇒ pA pB
      → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ pA
      → W ∣ γ ⊢ L · M ⊑ᵛ L′ · M′ ∶ pB

    blame⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ ℓ M′ A A′}
      → Δ ⊢ᵗ A
      → Δ′ ∣ rhs γ ⊢ M′ ⦂ A′
      → (p : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ blame ℓ ⊑ᵛ M′ ∶ p

    -- CHANGED (i), (ii): any world; the left coercion claims
    cast⊑cast : ∀ {W : World Δ Δ′} {πₚ γ M M′ μ μ′ c c′ B B′ A A′}
        {p : B ⊑ˢ⟨ record W { πʷ = πₚ } ⟩ B′}
      → CastClaimG M c (πʷ W) πₚ
      → record W { πʷ = πₚ } ∣ γ ⊢ M ⊑ᵛ M′ ∶ p
      → CastTy Δ μ c B A
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ˢ⟨ W ⟩ A′)
      → OkIx {W = W} {A} {A′} (M ⟨ μ ∣ c ⟩) q
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ᵛ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    -- CHANGED (ii)
    cast⊑ : ∀ {W : World Δ Δ′} {πₚ γ M M′ μ c B A A′}
        {p : B ⊑ˢ⟨ record W { πʷ = πₚ } ⟩ A′}
      → CastClaimG M c (πʷ W) πₚ
      → record W { πʷ = πₚ } ∣ γ ⊢ M ⊑ᵛ M′ ∶ p
      → CastTy Δ μ c B A
      → (q : A ⊑ˢ⟨ W ⟩ A′)
      → OkIx {W = W} {A} {A′} (M ⟨ μ ∣ c ⟩) q
      → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ᵛ M′ ∶ q

    ⊑cast : ∀ {W : World Δ Δ′} {κₚ γ γ′ M M′ μ′ c′ A B′ A′}
        {p : A ⊑ˢ⟨ record W { κʷ = κₚ } ⟩ B′}
      → CastGrant Δ′ c′ (κʷ W) κₚ
      → RaiseCtx γ γ′
      → record W { κʷ = κₚ } ∣ γ′ ⊢ M ⊑ᵛ M′ ∶ p
      → CastTy Δ′ μ′ c′ B′ A′
      → (q : A ⊑ˢ⟨ W ⟩ A′)
      → OkIx {W = W} {A} {A′} M q
      → W ∣ γ ⊢ M ⊑ᵛ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q

    Λ⊑Λ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ γ′ V V′ A A′} {r : A ⊑ᵂ⟨ W ⊕² ⟩ A′}
      → LiftCtx γ γ′
      → Value V
      → Value V′
      → W ⊕² ∣ γ′ ⊢ V ⊑ᵛ V′ ∶ r
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ `∀ A′)
      → W ∣ γ ⊢ Λ V ⊑ᵛ Λ V′ ∶ q

    Λ⊑ : ∀ {W : World Δ Δ′} {W₁ : World (underΛ Δ) Δ′}
        {γ γ′ V M′ A B′} {r : A ⊑ˢ⟨ W₁ ⟩ B′}
      → Claim W W₁
      → NonVar A
      → 0 ∈ᵗ A
      → LiftCtxᴸ γ γ′
      → Value V
      → W₁ ∣ γ′ ⊢ V ⊑ᵛ M′ ∶ r
      → (q : `∀ A ⊑ˢ⟨ W ⟩ B′)
      → OkIx {W = W} {`∀ A} {B′} (Λ V) q
      → W ∣ γ ⊢ Λ V ⊑ᵛ M′ ∶ q

    ν⊑ν : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ L L′ A A′ C C′ c c′ B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
      → W ∣ γ ⊢ L ⊑ᵛ L′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ A′
      → (n : NuTy Δ A C c B)
      → (n′ : NuTy Δ′ A′ C′ c′ B′)
      → NuConversionImp W n n′
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ᵛ ν A′ · L′ ⟨ c′ ⟩ ∶ q

    ν⊑ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {γ L M′ A C c B B′} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
      → W ∣ γ ⊢ L ⊑ᵛ M′ ∶ r
      → A ⊑ᵂ⟨ W ⟩ ★
      → NuTy Δ A C c B
      → (q : B ⊑ᵂ⟨ W ⟩ B′)
      → W ∣ γ ⊢ ν A · L ⟨ c ⟩ ⊑ᵛ M′ ∶ q

    ⟪⟫⊑⟪⟫ : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ} → let W = world Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
        ∀ {Δᵢ Δ′ᵢ Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ}
      → let Wᵢ = world {Δᵢ} {Δ′ᵢ} Ωᵢ ηᴸᵢ ηᴿᵢ ϱᵍᵢ ϱˡᵢ κᵢ [] in
        ∀ {γ M M′ Θ Θ′ c c′ Aᵢ A′ᵢ A A′} {r : Aᵢ ⊑ᵂ⟨ Wᵢ ⟩ A′ᵢ}
      → Interior W Θ Θ′ Wᵢ
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ᵛ M′ ∶ r
      → (b : BdyTy Δ Θ Δᵢ Aᵢ c A)
      → (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
      → BdyConversionImp W b b′
      → (q : A ⊑ᵂ⟨ W ⟩ A′)
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ᵛ M′ ⟪ Θ′ , c′ ⟫ ∶ q

    ⟪⟫⊑ : ∀ {W : World Δ Δ′} {Δᵢ} {Wᵢ : World Δᵢ Δ′}
        {γ M M′ Θ c Aᵢ A A′} {r : Aᵢ ⊑ˢ⟨ Wᵢ ⟩ A′}
      → Interior W Θ [] Wᵢ
      → All (UnbindOK W) Θ
      → BdyClaim M c (πʷ W) (πʷ Wᵢ)
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ᵛ M′ ∶ r
      → BdyTy Δ Θ Δᵢ Aᵢ c A
      → (q : A ⊑ˢ⟨ W ⟩ A′)
      → OkIx {W = W} {A} {A′} (M ⟪ Θ , c ⟫) q
      → W ∣ γ ⊢ M ⟪ Θ , c ⟫ ⊑ᵛ M′ ∶ q

    -- CHANGED (iii): PushV
    ⊑⟪⟫ : ∀ {W : World Δ Δ′} {Δ′ᵢ} {Wᵢ : World Δ Δ′ᵢ}
        {γ M M′ Θ′ c′ A A′ᵢ A′} {r : A ⊑ˢ⟨ Wᵢ ⟩ A′ᵢ}
      → Interior W [] Θ′ Wᵢ
      → PushV Θ′ M (πʷ W) (πʷ Wᵢ)
      → WfWorld Wᵢ
      → Wᵢ ∣ [] ⊢ M ⊑ᵛ M′ ∶ r
      → BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′
      → (q : A ⊑ˢ⟨ W ⟩ A′)
      → OkIx {W = W} {A} {A′} M q
      → W ∣ γ ⊢ M ⊑ᵛ M′ ⟪ Θ′ , c′ ⟫ ∶ q

  ⊑cast₀ᵛ : ∀ {W : World Δ Δ′} {γ M M′ μ′ c′ A B′ A′}
      {p : A ⊑ˢ⟨ W ⟩ B′}
    → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ p
    → CastTy Δ′ μ′ c′ B′ A′
    → (q : A ⊑ˢ⟨ W ⟩ A′)
    → OkIx {W = W} {A} {A′} M q
    → W ∣ γ ⊢ M ⊑ᵛ M′ ⟨ μ′ ∣ c′ ⟩ ∶ q
  ⊑cast₀ᵛ {γ = γ} d ct q ok = ⊑cast no-grant (raise-refl γ) d ct q ok

  -- THE REAL RELATION IS A SUB-RELATION: every real derivation (so the
  -- whole corpus) is one here
  fromReal : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ M′ ∶ q → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ fromOIʷ {W = W} q
  fromReal (x⊑x h) = x⊑x h
  fromReal (κ⊑κ l p) = κ⊑κ l p
  fromReal (ƛ⊑ƛ wA wA′ d) = ƛ⊑ƛ wA wA′ (fromReal d)
  fromReal (·⊑· d e) = ·⊑· (fromReal d) (fromReal e)
  fromReal (blame⊑ w ⊢M′ p) = blame⊑ w ⊢M′ p
  fromReal (cast⊑cast d ct ct′ q) =
    cast⊑cast cg-plain (fromReal d) ct ct′ q (inj₁ tt)
  fromReal {W = W} (cast⊑ cc d ct q) =
    cast⊑ (ccG cc) (fromReal d) ct (fromOIʷ {W = W} q) (inj₁ (sfʷ {W = W} q))
  fromReal {W = W} (⊑cast g r d ct q) =
    ⊑cast g r (fromReal d) ct (fromOIʷ {W = W} q) (inj₁ (sfʷ {W = W} q))
  fromReal (Λ⊑Λ l v v′ d q) = Λ⊑Λ l v v′ (fromReal d) q
  fromReal {W = W} (Λ⊑ cl nv occ l v d q) =
    Λ⊑ cl nv occ l v (fromReal d) (fromOIʷ {W = W} q) (inj₁ (sfʷ {W = W} q))
  fromReal (ν⊑ν d a n n′ nc q) = ν⊑ν (fromReal d) a n n′ nc q
  fromReal (ν⊑ d a n q) = ν⊑ (fromReal d) a n q
  fromReal (⟪⟫⊑⟪⟫ I wf d b b′ bc q) = ⟪⟫⊑⟪⟫ I wf (fromReal d) b b′ bc q
  fromReal {W = W} (⟪⟫⊑ I ok bc wf d b q) =
    ⟪⟫⊑ I ok bc wf (fromReal d) b (fromOIʷ {W = W} q) (inj₁ (sfʷ {W = W} q))
  fromReal {W = W} (⊑⟪⟫ I pu wf d b q) =
    ⊑⟪⟫ I (pv-real pu) wf (fromReal d) b (fromOIʷ {W = W} q)
      (inj₁ (sfʷ {W = W} q))

  -- BACK TO THE REAL RELATION, for a gen-free left term (when gen-free
  -- terms may not skip): the variant adds no derivation for it
  module Back (noSkip : ∀ {M} → GenFree M → ¬ SkipOK M) where

    sfOf : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → GenFree M → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ q
      → SkipFree {μ = marksʷ W} {cs = map (emb (ηᴿʷ W)) (πʷ W)}
          {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} q
    sfOf g (x⊑x _) = tt
    sfOf g (κ⊑κ _ _) = tt
    sfOf g (ƛ⊑ƛ _ _ _) = tt
    sfOf g (·⊑· _ _) = tt
    sfOf g (blame⊑ _ _ _) = tt
    sfOf g (cast⊑cast _ _ _ _ _ (inj₁ sf)) = sf
    sfOf g (cast⊑cast _ _ _ _ _ (inj₂ s)) = ⊥-elim (noSkip g s)
    sfOf g (cast⊑ _ _ _ _ (inj₁ sf)) = sf
    sfOf g (cast⊑ _ _ _ _ (inj₂ s)) = ⊥-elim (noSkip g s)
    sfOf g (⊑cast _ _ _ _ _ (inj₁ sf)) = sf
    sfOf g (⊑cast _ _ _ _ _ (inj₂ s)) = ⊥-elim (noSkip g s)
    sfOf g (Λ⊑Λ _ _ _ _ _) = tt
    sfOf g (Λ⊑ _ _ _ _ _ _ _ (inj₁ sf)) = sf
    sfOf g (Λ⊑ _ _ _ _ _ _ _ (inj₂ s)) = ⊥-elim (noSkip g s)
    sfOf g (ν⊑ν _ _ _ _ _ _) = tt
    sfOf g (ν⊑ _ _ _ _) = tt
    sfOf g (⟪⟫⊑⟪⟫ _ _ _ _ _ _ _) = tt
    sfOf g (⟪⟫⊑ _ _ _ _ _ _ _ (inj₁ sf)) = sf
    sfOf g (⟪⟫⊑ _ _ _ _ _ _ _ (inj₂ s)) = ⊥-elim (noSkip g s)
    sfOf g (⊑⟪⟫ _ _ _ _ _ _ (inj₁ sf)) = sf
    sfOf g (⊑⟪⟫ _ _ _ _ _ _ (inj₂ s)) = ⊥-elim (noSkip g s)

    back : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → (g : GenFree M) → (d : W ∣ γ ⊢ M ⊑ᵛ M′ ∶ q)
      → W ∣ γ ⊢ M ⊑ M′ ∶ toOIʷ {W = W} q (sfOf g d)
    back g (x⊑x h) = x⊑x h
    back g (κ⊑κ l p) = κ⊑κ l p
    back g (ƛ⊑ƛ wA wA′ d) = ƛ⊑ƛ wA wA′ (back g d)
    back (gL , gM) (·⊑· d e) = ·⊑· (back gL d) (back gM e)
    back g (blame⊑ w ⊢M′ p) = blame⊑ w ⊢M′ p
    back {W = world _ _ _ _ _ _ _} (n , g) (cast⊑cast cc d ct ct′ q ok)
      with cg-free n cc
    back {W = world _ _ _ _ _ _ _} (n , g)
      (cast⊑cast cg-plain d ct ct′ q (inj₁ _)) | refl , refl =
      cast⊑cast (back g d) ct ct′ q
    back {W = world _ _ _ _ _ _ _} (n , g)
      (cast⊑cast cg-plain d ct ct′ q (inj₂ s)) | refl , refl =
      ⊥-elim (noSkip (n , g) s)
    back {W = world _ _ _ _ _ _ _} (n , g) (cast⊑ cc d ct q ok)
      with cg-free n cc
    back {W = world _ _ _ _ _ _ _} (n , g)
      (cast⊑ cg-plain d ct q (inj₁ _)) | refl , refl =
      cast⊑ cc-plain (back g d) ct q
    back {W = world _ _ _ _ _ _ _} (n , g)
      (cast⊑ cg-plain d ct q (inj₂ s)) | refl , refl =
      ⊥-elim (noSkip (n , g) s)
    back {W = W} g (⊑cast gr r d ct q (inj₁ sf)) =
      ⊑cast gr r (back g d) ct (toOIʷ {W = W} q sf)
    back g (⊑cast gr r d ct q (inj₂ s)) = ⊥-elim (noSkip g s)
    back g (Λ⊑Λ l v v′ d q) = Λ⊑Λ l v v′ (back g d) q
    back {W = W} g (Λ⊑ cl nv occ l v d q (inj₁ sf)) =
      Λ⊑ cl nv occ l v (back g d) (toOIʷ {W = W} q sf)
    back g (Λ⊑ cl nv occ l v d q (inj₂ s)) = ⊥-elim (noSkip g s)
    back g (ν⊑ν d a n n′ nc q) = ν⊑ν (back g d) a n n′ nc q
    back g (ν⊑ d a n q) = ν⊑ (back g d) a n q
    back g (⟪⟫⊑⟪⟫ I wf d b b′ bc q) = ⟪⟫⊑⟪⟫ I wf (back g d) b b′ bc q
    back {W = W} g (⟪⟫⊑ I ok bc wf d b q (inj₁ sf)) =
      ⟪⟫⊑ I ok bc wf (back g d) b (toOIʷ {W = W} q sf)
    back g (⟪⟫⊑ I ok bc wf d b q (inj₂ s)) = ⊥-elim (noSkip g s)
    back {W = W} g (⊑⟪⟫ I (pv-real pu) wf d b q (inj₁ sf)) =
      ⊑⟪⟫ I pu wf (back g d) b (toOIʷ {W = W} q sf)
    back g (⊑⟪⟫ I (pv-new s _ _ _) wf d b q _) = ⊥-elim (noSkip g s)
    back g (⊑⟪⟫ I (pv-real _) wf d b q (inj₂ s)) = ⊥-elim (noSkip g s)

------------------------------------------------------------------------
-- The variant's derivations of the failing final pairs.  `Pos SkipOK`
-- holds for every SkipOK (so in V1 and in V2): G0, G2m and HRm need
-- only (i) and (ii).  G2 and HR (module `Pos2`) need (iii).
------------------------------------------------------------------------

open import examples.TermImprecisionExamples
  using (W₃; int-ro₃; Wi₃-wf; ΔR; ΔRᵢ)
open import examples.TermImprecisionRebaseExamples using (IntN; W₃-wf)
open import examples.TermImprecisionH1Examples
  using (W₄; W₄-wf; cf-ty; ci-ty; bX; bY)
open import proof.ImprecisionWorld using (namedᴸ-≤1; namedᴿ-≤1; ≤1-[]; ≤1-∷[])
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)

-- the typing side premises, read off `tc`
module Tys where
  open G0 using (pF; cU0; cB0; UF; IF; BF)

  pF-ty : CastTy ΔRᵢ (★∼X ∷ []) pF (★ ⇒ `ℕ) (` 0 ⇒ `ℕ)
  pF-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = IF})))

  UF-ty : BdyTy ΔRᵢ (unbind 0 0 ∷ []) ΔR (★ ⇒ `ℕ) cU0 (★ ⇒ `ℕ)
  UF-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = UF}))))

  BF-ty : BdyTy ΔR (bind 0 0 ∷ []) ΔRᵢ (` 0 ⇒ `ℕ) cB0 (★ ⇒ `ℕ)
  BF-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = BF}))))

  cF-ty : CastTy ΔR [] (idᵖ ★ ↦ᵖ idᵖ `ℕ) (★ ⇒ `ℕ) (★ ⇒ `ℕ)
  cF-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔR} {M = G0.FR₂})))

  pK-ty : CastTy ΔXY (★∼X ∷ ★∼X ∷ []) pK (★ ⇒ (★ ⇒ ★)) (` 1 ⇒ (` 0 ⇒ ` 1))
  pK-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = CK})))

  UK-ty : BdyTy ΔXY U2 ΔT2 (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  UK-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔXY} {M = UK}))))

  BXY-ty : BdyTy ΔT2 ΘXY ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cXY (★ ⇒ (★ ⇒ ★))
  BXY-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔT2} {M = G2m.BXYm}))))

  pH-ty : CastTy ΔXY (★∼X ∷ X∼X ∷ []) pH (` 1 ⇒ (★ ⇒ ` 1)) (` 1 ⇒ (` 0 ⇒ ` 1))
  pH-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = CH})))

  ΔX1 : Ctxᵗ
  ΔX1 = (bindR ★ ∷ bindR ★ ∷ []) ∣ (1 ∷ [])

  UH-ty : BdyTy ΔXY (unbind 0 0 ∷ []) ΔX1 (` 0 ⇒ (★ ⇒ ` 0)) cUH
    (` 1 ⇒ (★ ⇒ ` 1))
  UH-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔXY} {M = UH}))))

  BXYh-ty : BdyTy ΔT2 ΘXY ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cXY (★ ⇒ (★ ⇒ ★))
  BXYh-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔT2} {M = HRm.BXYh}))))

-- the worlds
Wm : World empty ΔXY      -- inside +Y^β, +X^α: X (name 1) then Y pending
Wm = world⁰ 2 (skip (skip []↪)) (keep (keep []↪)) [] [] (1 ∷ 0 ∷ [])

intXYW : Interior W₄ [] ΘXY Wm
intXYW = record
  { int-left   = interior changes[]
  ; int-right  = G2m.intXYm
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

wfm : WfWorld Wm
wfm = wf-world (right-only (right-only joint[])) (λ { (inj₁ ()) ; (inj₂ ()) })
  (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
  ((1 , there here , r-there r-here , (λ { (_ , ()) }) , (λ { (_ , ()) }))
   ∷ (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ [])
  (((λ ()) ∷ []) ∷ [] ∷ []) []

-- the gen bodies' right unbinds `[−Y^β, −X^α]`: both pending names
-- were popped by the gen chain, so they simply go
intU2 : Interior (record Wm { πʷ = [] }) [] U2 W₄
intU2 = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷
      (changes∷ changes[]
        (step-unbind (bindR ★ , here) del-here (fresh∷ (λ ()) fresh[])))
      (step-unbind (bindR ★ , there here) del-here fresh[]))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

-- gen over Λ: the ∀ layer passes X to the Λ, which pops it (Open1)
W₁h : World (underΛ empty) ΔXY
W₁h = world 2 (skip (keep []↪)) (keep (keep []↪)) [] ((0 , 1) ∷ []) [] []

open1h : Open1 (record Wm { πʷ = 1 ∷ [] }) W₁h
open1h = open1 (join-there join-here) (there here) (r-there r-here)

Wq : World (underΛ empty) Tys.ΔX1
Wq = world 1 (keep []↪) (keep []↪) [] ((0 , 1) ∷ []) [] []

intUH : Interior W₁h [] (unbind 0 0 ∷ []) Wq
intUH = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
      (step-unbind (bindR ★ , here) del-here (fresh∷ (λ ()) fresh[])))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , here) (_ , here) refl refl →
                       (λ _ → refl) , (λ _ → refl)
                   ; (_ , there ()) _ _ _
                   ; (_ , here) (_ , there ()) _ _ }
  ; join-fresh = λ { here here (inj₁ ()) ; here here (inj₂ ())
                   ; (there ()) _ _ ; here (there ()) _ }
  }

wfq : WfWorld Wq
wfq = wf-world (both (inj₂ here⇔) joint[])
  (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here (r-there r-here)
     ; (inj₂ (there⇔ ())) })
  (namedᴸ-≤1 Wq ≤1-∷[]) (namedᴿ-≤1 Wq ≤1-∷[]) [] [] []

-- the outer Inst boundary of a two-cast right: Y pending
WYg : World empty ΔY
WYg = world⁰ 1 (skip []↪) (keep []↪) [] [] (0 ∷ [])

intYg : Interior W₄ [] ΘY WYg
intYg = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , here) fresh[] ins-here))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

wfYg : WfWorld WYg
wfYg = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
  (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
  ((0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ [])
  ([] ∷ []) []

-- the inner Inst boundary +X^α: Y carried, X new
intXg : Interior WYg [] ΘX Wm
intXg = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , there here)
                      (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

vK★ : Value K★
vK★ = V-simple S-ƛ

vKΛ : Value KΛ
vKΛ = V-simple (S-Λ vNΛ)

-- the indices
qm : K2 ⊑ˢ⟨ Wm ⟩ (` 1 ⇒ (` 0 ⇒ ` 1))
qm = inj₁ (inj₁ (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)))

qH : `∀ (` 0 ⇒ (★ ⇒ ` 0)) ⊑ˢ⟨ record Wm { πʷ = 1 ∷ [] } ⟩
  (` 1 ⇒ (★ ⇒ ` 1))
qH = inj₁ (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X))

-- THE SKIP: K2 at +Y^β, its outer ∀ left-only (X⊑★ against ★), its
-- inner ∀ opened at the pending Y
qY : K2 ⊑ˢ⟨ WYg ⟩ (★ ⇒ (` 0 ⇒ ★))
qY = inj₂ (nv-∀ , ∈-∀ (∈-⇒ˡ ∈-var) ,
           inj₁ (⇒⊑⇒ (X⊑★ here) (⇒⊑⇒ X⊑X (X⊑★ here))))

module Pos (SkipOK : Term → Set) where
  open V SkipOK

  K★⊑K★ᵛ : W₄ ∣ [] ⊢ K★ ⊑ᵛ K★ ∶ ⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)
  K★⊑K★ᵛ = ƛ⊑ƛ tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} tf tf (x⊑x (Sʷ Zʷ)))

  -- G2m's gen body: the chain pops X then Y against `X! → Y! → X?`
  bodyK : Wm ∣ [] ⊢ GL ⊑ᵛ CK ∶ qm
  bodyK =
    cast⊑cast (cg-gen vK★ (cg-gen vK★ cg-plain))
      (⊑⟪⟫ intU2 (pv-real push-none) W₄-wf K★⊑K★ᵛ Tys.UK-ty
        (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)) (inj₁ tt))
      genK-ty Tys.pK-ty qm (inj₁ tt)

  g2m-final : W₄ ∣ [] ⊢ GL ⊑ᵛ G2m.GmF ∶ q-top
  g2m-final =
    ⊑cast₀ᵛ
      (⊑⟪⟫ intXYW (pv-real (push ca-[] (refl ∷ refl ∷ []) (inj₂ vGL))) wfm
        bodyK Tys.BXY-ty q-top (inj₁ tt))
      cf-ty q-top (inj₁ tt)

  NΛ⊑NΛᵛ : Wq ∣ [] ⊢ NΛ ⊑ᵛ NΛ ∶ ⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)
  NΛ⊑NΛᵛ =
    ƛ⊑ƛ {pA = X⊑X} tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ)))

  -- HRm's body: the ∀ layer passes X, the gen pops Y; the Λ pops X
  bodyH : Wm ∣ [] ⊢ HL ⊑ᵛ CH ∶ qm
  bodyH =
    cast⊑cast (cg-∀ vKΛ (cg-gen vKΛ cg-plain))
      (Λ⊑ (claim-pop open1h) nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] vNΛ
        (⊑⟪⟫ intUH (pv-real push-none) wfq NΛ⊑NΛᵛ Tys.UH-ty
          (⇒⊑⇒ X⊑X (⇒⊑⇒ ★⊑★ X⊑X)) (inj₁ tt))
        qH (inj₁ tt))
      ∀gen-ty Tys.pH-ty qm (inj₁ tt)

  hrm-final : W₄ ∣ [] ⊢ HL ⊑ᵛ HRm.HmF ∶ q-top
  hrm-final =
    ⊑cast₀ᵛ
      (⊑⟪⟫ intXYW (pv-real (push ca-[] (refl ∷ refl ∷ []) (inj₂ vHL))) wfm
        bodyH Tys.BXYh-ty q-top (inj₁ tt))
      cf-ty q-top (inj₁ tt)

  -- G0: push X, then the gen pops it against `X! → id(ℕ)` (no grant)
  g0-final : W₃ ∣ [] ⊢ FL ⊑ᵛ G0.FR₂ ∶ G0.q0
  g0-final =
    ⊑cast₀ᵛ
      (⊑⟪⟫ int-ro₃ (pv-real (push ca-[] (refl ∷ []) (inj₂ G0.vFL))) Wi₃-wf
        (cast⊑cast (cg-gen (V-simple S-ƛ) cg-plain)
          (⊑⟪⟫ IntN (pv-real push-none) (W₃-wf [])
            (ƛ⊑ƛ {pA = ★⊑★} tf tf (κ⊑κ lit-$ (ι⊑ι base-ℕ))) Tys.UF-ty
            (⇒⊑⇒ ★⊑★ (ι⊑ι base-ℕ)) (inj₁ tt))
          G0.genX5-ty Tys.pF-ty (inj₁ (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ))) (inj₁ tt))
        Tys.BF-ty G0.q0 (inj₁ tt))
      Tys.cF-ty G0.q0 (inj₁ tt)

------------------------------------------------------------------------
-- V2 = V GenCastValue: the two-cast pairs G2 and HR need the skip and
-- the new-first push
------------------------------------------------------------------------

module V2 = V GenCastValue
module V1 = V (λ _ → ⊥)

gcvGL : GenCastValue GL
gcvGL = gcv vK★ gl-gen

gcvHL : GenCastValue HL
gcvHL = gcv vKΛ (gl-∀ gl-gen)

module Pos2 where
  open V2
  open Pos GenCastValue

  -- +Y^β pushes Y; the index SKIPS the left's outer ∀ (qY); +X^α
  -- pushes X BEFORE the carried Y; then G2m's gen body
  g2-final : W₄ ∣ [] ⊢ GL ⊑ᵛ G2.GF ∶ q-top
  g2-final =
    ⊑cast₀ᵛ
      (⊑⟪⟫ intYg (pv-real (push ca-[] (refl ∷ []) (inj₂ vGL))) wfYg
        (⊑cast₀ᵛ
          (⊑⟪⟫ intXg (pv-new gcvGL (ca-∷ refl ca-[]) (refl ∷ []) vGL) wfm
            bodyK bX qY (inj₂ gcvGL))
          ci-ty qY (inj₂ gcvGL))
        bY q-top (inj₁ tt))
      cf-ty q-top (inj₁ tt)

  hr-final : W₄ ∣ [] ⊢ HL ⊑ᵛ HR.HF ∶ q-top
  hr-final =
    ⊑cast₀ᵛ
      (⊑⟪⟫ intYg (pv-real (push ca-[] (refl ∷ []) (inj₂ vHL))) wfYg
        (⊑cast₀ᵛ
          (⊑⟪⟫ intXg (pv-new gcvHL (ca-∷ refl ca-[]) (refl ∷ []) vHL) wfm
            bodyH bX qY (inj₂ gcvHL))
          ci-ty qY (inj₂ gcvHL))
        bY q-top (inj₁ tt))
      cf-ty q-top (inj₁ tt)

------------------------------------------------------------------------
-- The counterexamples stay dead in V2 (and so in V1): their left terms
-- are gen-free, and on a gen-free left term V2 adds no derivation
-- (`Back.back`), so the real non-derivability results carry over
------------------------------------------------------------------------

import examples.TermImprecisionPermissionExamples as PE
open import examples.TermImprecisionExamples using (ΔL)
open PE using (module C1; module C2; module C3; module C4; module C4g;
               module C5; module C5Dead)

module DeadAt (SkipOK : Term → Set)
    (noSkip : ∀ {M} → GenFree M → ¬ SkipOK M) where
  open V SkipOK
  open Back noSkip

  c1 : ∀ {W : World C1.ΔR C1.ΔR} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C1.L₆ ⊑ᵛ C1.R₇ ∶ q)
  c1 eκ d = C1.c1-unrelated eκ (back _ d)

  c2 : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C2.LE₃ ⊑ᵛ C2.RE₅ ∶ q)
  c2 eκ d = C2.c2-unrelated eκ (back _ d)

  c3 : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C3.LE₁ ⊑ᵛ C3.RE₁ ∶ q)
  c3 eκ d = C3.c3-unrelated eκ (back _ d)

  c4 : ∀ {W : World empty C1.ΔR} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C1.L₀ ⊑ᵛ C4.R₂ ∶ q)
  c4 eκ d = C4.c4-unrelated eκ (back _ d)

  c4g : ∀ {W : World empty C1.ΔR} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ C1.L₀ ⊑ᵛ C4g.R2g ∶ q)
  c4g eκ d = C4g.c4g-unrelated eκ (back _ d)

  c5 : ∀ {W : World ΔL ΔL} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ C5.C5L ⊑ᵛ C5.C5R ∶ q)
  c5 d = C5Dead.c5-unrelated (back _ d)

module Dead2 = DeadAt GenCastValue gf-no-gcv
module Dead1 = DeadAt (λ _ → ⊥) (λ _ ())

------------------------------------------------------------------------
-- The corpus derives in V2 (the real relation is a sub-relation):
-- H1, K, P3 = Ch X0, Cg X0, C2 X0, G1, C12, L3c, L3d, P4
------------------------------------------------------------------------

module Corpus where
  open V2
  import examples.TermImprecisionH1Examples as H1
  import examples.TermImprecisionRegressionExamples as RG
  import examples.TermImprecisionExamples as TIE
  import examples.TermImprecisionRebaseExamples as RB
  import proof.DGG.notes.NoPush as NP

  h1-final        : _
  h1-final        = fromReal H1.final
  h1-final-np     : _
  h1-final-np     = fromReal H1.final-no-push
  k-VL⊑RF         : _
  k-VL⊑RF         = fromReal RG.VL⊑RF
  k-lk₁⊑rk₄       : _
  k-lk₁⊑rk₄       = fromReal RG.lk₁⊑rk₄
  k-lk₁⊑rk₃       : _
  k-lk₁⊑rk₃       = fromReal RG.lk₁⊑rk₃
  p3              : _
  p3              = fromReal TIE.p3-inst
  ch-x0           : _
  ch-x0           = fromReal RB.ch-x0
  cg-x0           : _
  cg-x0           = fromReal RB.cg-x0
  c2-x0           : _
  c2-x0           = fromReal RB.c2-x0
  g1              : _
  g1              = fromReal NP.C2X0.g1-final-real
  c12-x0          : _
  c12-x0          = fromReal RB.c12-x0
  c12-b1          : _
  c12-b1          = fromReal RB.c12-b1
  l3c-pre         : _
  l3c-pre         = fromReal (NP.toReal NP.Corpus.l3c-pre)
  l3c-post        : _
  l3c-post        = fromReal (NP.toReal NP.Corpus.l3c-post)
  l3d-before      : _
  l3d-before      = fromReal (NP.toReal NP.Corpus.l3d-before)
  p4-B1           : _
  p4-B1           = fromReal PE.P4.p4-B1
  p4-B2           : _
  p4-B2           = fromReal PE.P4.p4-B2
  p4-B3           : _
  p4-B3           = fromReal PE.P4.p4-B3
  p4-B4           : _
  p4-B4           = fromReal PE.P4.p4-B4
  p4-B5           : _
  p4-B5           = fromReal PE.P4.p4-B5
  p4-B6           : _
  p4-B6           = fromReal PE.P4.p4-B6

------------------------------------------------------------------------
-- (iii) IS NEEDED: in V1 (gen chains and cast⊑cast pops, no skip, no
-- new-first push) the two-cast pairs G2 and HR are still unrelated in
-- every world with no permission.  The obstruction is the index at
-- the OUTER Inst boundary +Y^β, which only (iii)'s skip removes: the
-- order problem of PushOrder §2 comes back for gen binders.
------------------------------------------------------------------------

module NoSkipWalk (SkipOK : Term → Set) (none : ∀ {M} → ¬ SkipOK M) where
  open V SkipOK

  sfOf₀ : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ q
    → SkipFree {μ = marksʷ W} {cs = map (emb (ηᴿʷ W)) (πʷ W)}
        {ρ = emb (ηᴸʷ W)} {A = A} {B = embᴿ W A′} q
  sfOf₀ (x⊑x _) = tt
  sfOf₀ (κ⊑κ _ _) = tt
  sfOf₀ (ƛ⊑ƛ _ _ _) = tt
  sfOf₀ (·⊑· _ _) = tt
  sfOf₀ (blame⊑ _ _ _) = tt
  sfOf₀ (cast⊑cast _ _ _ _ _ (inj₁ sf)) = sf
  sfOf₀ (cast⊑cast _ _ _ _ _ (inj₂ s)) = ⊥-elim (none s)
  sfOf₀ (cast⊑ _ _ _ _ (inj₁ sf)) = sf
  sfOf₀ (cast⊑ _ _ _ _ (inj₂ s)) = ⊥-elim (none s)
  sfOf₀ (⊑cast _ _ _ _ _ (inj₁ sf)) = sf
  sfOf₀ (⊑cast _ _ _ _ _ (inj₂ s)) = ⊥-elim (none s)
  sfOf₀ (Λ⊑Λ _ _ _ _ _) = tt
  sfOf₀ (Λ⊑ _ _ _ _ _ _ _ (inj₁ sf)) = sf
  sfOf₀ (Λ⊑ _ _ _ _ _ _ _ (inj₂ s)) = ⊥-elim (none s)
  sfOf₀ (ν⊑ν _ _ _ _ _ _) = tt
  sfOf₀ (ν⊑ _ _ _ _) = tt
  sfOf₀ (⟪⟫⊑⟪⟫ _ _ _ _ _ _ _) = tt
  sfOf₀ (⟪⟫⊑ _ _ _ _ _ _ _ (inj₁ sf)) = sf
  sfOf₀ (⟪⟫⊑ _ _ _ _ _ _ _ (inj₂ s)) = ⊥-elim (none s)
  sfOf₀ (⊑⟪⟫ _ _ _ _ _ _ (inj₁ sf)) = sf
  sfOf₀ (⊑⟪⟫ _ _ _ _ _ _ (inj₂ s)) = ⊥-elim (none s)

  -- with no skip, the index is the real one
  idxV : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ q → A ⊑ᵂ⟨ W ⟩ A′
  idxV {W = W} {q = q} d = toOIʷ {W = W} q (sfOf₀ d)

  -- the two types, read off the derivation
  rty-cast : ∀ {W : World Δ Δ′} {γ M U μ p A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⊑ᵛ U ⟨ μ ∣ p ⟩ ∶ q → A′ ≡ trgᵖ p
  rty-cast (blame⊑ _ ⊢M′ _) = ty-cast ⊢M′
  rty-cast (cast⊑cast _ _ _ ct′ _ _) = ct-trg ct′
  rty-cast (cast⊑ _ d _ _ _) = rty-cast d
  rty-cast (⊑cast _ _ _ ct _ _) = ct-trg ct
  rty-cast (Λ⊑ _ _ _ _ _ d _ _) = rty-cast d
  rty-cast (ν⊑ d _ _ _) = rty-cast d
  rty-cast (⟪⟫⊑ _ _ _ _ d _ _ _) = rty-cast d

  lty-cast : ∀ {W : World Δ Δ′} {γ M μ c M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → W ∣ γ ⊢ M ⟨ μ ∣ c ⟩ ⊑ᵛ M′ ∶ q → A ≡ trgᵖ c
  lty-cast (cast⊑cast _ _ ct _ _ _) = ct-trg ct
  lty-cast (cast⊑ _ _ ct _ _) = ct-trg ct
  lty-cast (⊑cast _ _ d _ _ _) = lty-cast d
  lty-cast (⊑⟪⟫ _ _ _ d _ _ _) = lty-cast d

  lty-ƛ★ : ∀ {W : World Δ Δ′} {γ N M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → W ∣ γ ⊢ ƛ ★ ∙ N ⊑ᵛ M′ ∶ q → Σ[ B ∈ Ty ] A ≡ ★ ⇒ B
  lty-ƛ★ (ƛ⊑ƛ _ _ _) = _ , refl
  lty-ƛ★ (⊑cast _ _ d _ _ _) = lty-ƛ★ d
  lty-ƛ★ (⊑⟪⟫ _ _ _ d _ _ _) = lty-ƛ★ d

  lty-lm : ∀ {W : World Δ Δ′} {γ M M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → LeftMid M → W ∣ γ ⊢ M ⊑ᵛ M′ ∶ q
    → Σ[ A₁ ∈ Ty ] Σ[ B ∈ Ty ] A ≡ A₁ ⇒ (★ ⇒ B)
  lty-lm lm-K★ (ƛ⊑ƛ _ _ d) with lty-ƛ★ d
  ... | _ , refl = _ , _ , refl
  lty-lm lm-NΛ (ƛ⊑ƛ _ _ d) with lty-ƛ★ d
  ... | _ , refl = _ , _ , refl
  lty-lm lm (⊑cast _ _ d _ _ _) = lty-lm lm d
  lty-lm lm (⊑⟪⟫ _ _ _ d _ _ _) = lty-lm lm d

  lty-KΛ : ∀ {W : World Δ Δ′} {γ M′ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → W ∣ γ ⊢ KΛ ⊑ᵛ M′ ∶ q
    → Σ[ A₁ ∈ Ty ] Σ[ B ∈ Ty ] A ≡ `∀ (A₁ ⇒ (★ ⇒ B))
  lty-KΛ (Λ⊑Λ _ _ _ d _) with lty-lm lm-NΛ d
  ... | _ , _ , refl = _ , _ , refl
  lty-KΛ (Λ⊑ _ _ _ _ _ d _ _) with lty-lm lm-NΛ d
  ... | _ , _ , refl = _ , _ , refl
  lty-KΛ (⊑cast _ _ d _ _ _) = lty-KΛ d
  lty-KΛ (⊑⟪⟫ _ _ _ d _ _ _) = lty-KΛ d

  -- the left's ★ (or left-only binder) in the middle against a right
  -- cast whose target has a name in the middle
  nlm : ∀ {W : World Δ Δ′} {γ M U μ p A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → LeftMid M → (∀ {R} → trgᵖ p ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ]
                                 Σ[ R₃ ∈ Ty ] R ≡ R₁ ⇒ (` y ⇒ R₃))
    → ¬ (W ∣ γ ⊢ M ⊑ᵛ U ⟨ μ ∣ p ⟩ ∶ q)
  nlm {W = W} lm tp d with lty-lm lm d | rty-cast d
  ... | _ , _ , refl | e with tp (sym e)
  ... | _ , _ , _ , refl = no-mid {W = W} (idxV d)

  nKΛ : ∀ {W : World Δ Δ′} {γ U μ p A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
    → (∀ {R} → trgᵖ p ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ]
                             Σ[ R₃ ∈ Ty ] R ≡ R₁ ⇒ (` y ⇒ R₃))
    → ¬ (W ∣ γ ⊢ KΛ ⊑ᵛ U ⟨ μ ∣ p ⟩ ∶ q)
  nKΛ {W = W} tp d with lty-KΛ d | rty-cast d
  ... | _ , _ , refl | e with tp (sym e)
  ... | _ , _ , _ , refl = no-∀mid {W = W} (idxV d)

  -- G2 (two gens, two casts)
  module G2ns where
    open G2 using (CIg; BYg; GF)

    kB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ K★ ⊑ᵛ BYg ∶ q)
    kB (⊑⟪⟫ _ _ _ d _ _ _) = nlm lm-K★ tp-ci d

    kF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ K★ ⊑ᵛ GF ∶ q)
    kF (⊑cast _ _ d _ _ _) = kB d

    gY : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ GL ⊑ᵛ CIg ∶ q)
    gY {W = W} eκ wf d with lty-cast d | rty-cast d
    ... | refl | refl = no-K2-★ {W = W} eκ wf (idxV d)

    gB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ᵛ BYg ∶ q)
    gB eκ (cast⊑ _ d _ _ _) = kB d
    gB eκ (⊑⟪⟫ I _ wf d _ _ _) = gY (trans (same-κ I) eκ) wf d

    g2-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ᵛ GF ∶ q)
    g2-unrelated eκ (cast⊑cast _ d _ _ _ _) = kB d
    g2-unrelated eκ (cast⊑ _ d _ _ _) = kF d
    g2-unrelated eκ (⊑cast g _ d _ _ _) =
      gB (trans (cg-none ng-cf g) eκ) d

  -- HR (gen over Λ, two casts)
  module HRns where
    open HR using (CIh; BYh; HF)

    nB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NΛ ⊑ᵛ BYh ∶ q)
    nB (⊑⟪⟫ _ _ _ d _ _ _) = nlm lm-NΛ tp-ci d

    ΛB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ KΛ ⊑ᵛ BYh ∶ q)
    ΛB (⊑⟪⟫ _ _ _ d _ _ _) = nKΛ tp-ci d
    ΛB (Λ⊑ _ _ _ _ _ d _ _) = nB d

    nF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NΛ ⊑ᵛ HF ∶ q)
    nF (⊑cast _ _ d _ _ _) = nB d

    ΛF : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ KΛ ⊑ᵛ HF ∶ q)
    ΛF (⊑cast _ _ d _ _ _) = ΛB d
    ΛF (Λ⊑ _ _ _ _ _ d _ _) = nF d

    hY : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ HL ⊑ᵛ CIh ∶ q)
    hY {W = W} eκ wf d with lty-cast d | rty-cast d
    ... | refl | refl = no-K2-★ {W = W} eκ wf (idxV d)

    hB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ HL ⊑ᵛ BYh ∶ q)
    hB eκ (cast⊑ _ d _ _ _) = ΛB d
    hB eκ (⊑⟪⟫ I _ wf d _ _ _) = hY (trans (same-κ I) eκ) wf d

    hr-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ˢ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ HL ⊑ᵛ HF ∶ q)
    hr-unrelated eκ (cast⊑cast _ d _ _ _ _) = ΛB d
    hr-unrelated eκ (cast⊑ _ d _ _ _) = ΛF d
    hr-unrelated eκ (⊑cast g _ d _ _ _) =
      hB (trans (cg-none ng-cf g) eκ) d

module InV1 = NoSkipWalk (λ _ → ⊥) (λ ())

------------------------------------------------------------------------
-- G2's intermediate states (Sim/SimBack need them): the right's
-- states 2 (after Inst, TyBeta) and 4 (after the second Inst, TyBeta,
-- before the Merge of its two unbinds).  States 1 and 3 are ν-terms
-- that no rule relates to a left non-ν (as in P3, K, H1).
------------------------------------------------------------------------

open import examples.TermImprecisionH1Examples
  using (KY; cA; ΘA; ∀ci-ty; instY-ty₂)

module G2st where
  U1 G2a B2 GR₂ UK₄ CK₄ : Term
  U1  = K★ ⟪ unbind 0 0 ∷ [] , cU ⟫
  G2a = U1 ⟨ ★∼X ∷ [] ∣ genᵖ pK ⟩
  B2  = G2a ⟪ ΘA , cA ⟫
  GR₂ = (B2 ⟨ [] ∣ ∀ᵖ ci ⟩) ⟨ [] ∣ instY ⟩
  UK₄ = (K★ ⟪ unbind 0 1 ∷ [] , cU ⟫) ⟪ unbind 0 0 ∷ [] , cU ⟫
  CK₄ = UK₄ ⟨ ★∼X ∷ ★∼X ∷ [] ∣ pK ⟩

  GR₄ : Term
  GR₄ = ((((CK₄ ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩) ⟪ ΘY , cY ⟫) ⟨ [] ∣ cf ⟩)

  GR₂-state : head (drop 2 (evalTerms 40 GR-⊢)) ≡ just GR₂
  GR₂-state = refl

  GR₄-state : head (drop 4 (evalTerms 40 GR-⊢)) ≡ just GR₄
  GR₄-state = refl

  -- REAL RELATION: state 2 is unrelated too.  Inside +X^α the left's
  -- index opens X; the right's `gen Y. (X! → Y! → X?)` cast grants
  -- nothing, so the left's X faces ★ unpermitted, and `cc-gen`'s
  -- premise puts ★→★→★ against ∀Y.X→Y→X
  no-⇒⊑∀ : ∀ {μ A B C} → ¬ (μ ⊢ A ⇒ B ⊑ `∀ C)
  no-⇒⊑∀ ()

  K★-vs-∀ : ∀ {W : World Δ Δ′} {γ M′ A′ C} {q : A′ ⊑ᵂ⟨ W ⟩ `∀ C}
    → ¬ (W ∣ γ ⊢ K★ ⊑ M′ ∶ q)
  K★-vs-∀ {W = W} {q = q} d with ty-K★ (ltyT d)
  ... | _ , refl = no-⇒⊑∀ (plain-idx {V = W} nf-⇒ q)

  -- K2 against ∀Y.X→Y→X (X a right name) with no name or two names
  -- opened: never
  K2-vs-∀ : ∀ {W : World Δ Δ′} {x π} → πʷ W ≡ π → length π ≢ 1
    → ¬ (K2 ⊑ᵂ⟨ W ⟩ `∀ (` (suc x) ⇒ (` 0 ⇒ ` (suc x))))
  K2-vs-∀ {W = W} {π = []} e _ q with idxπ {W = W} e q
  ... | ∀⊑ _ _ (∀⊑ _ _ ())
  ... | ∀⊑ _ _ (∀⊑∀ (⇒⊑⇒ () _))
  ... | ∀⊑∀ (∀⊑ _ _ (⇒⊑⇒ () _))
  K2-vs-∀ {π = _ ∷ []} e n q = n refl
  K2-vs-∀ {W = W} {π = _ ∷ _ ∷ []} e _ q = no-⇒⊑∀ (idxπ {W = W} e q)
  K2-vs-∀ {W = W} {π = _ ∷ _ ∷ _ ∷ _} e _ q = idxπ {W = W} e q

  ng-genpK : NoGrant (genᵖ pK)
  ng-genpK ()

  ng-∀ci : NoGrant (∀ᵖ ci)
  ng-∀ci ()

  ng-instY : NoGrant instY
  ng-instY ()

  g2a : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ GL ⊑ G2a ∶ q)
  g2a {W = W} {γ} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = go (πʷ W) refl d
    where
    go : ∀ π → πʷ W ≡ π → ¬ (W ∣ γ ⊢ GL ⊑ G2a ∶ q)
    go (k ∷ []) () (cast⊑cast _ _ _ _)
    go (k ∷ []) e (cast⊑ _ d′ _ _) = K★-vs-∀ d′
    go (k ∷ []) e (⊑cast {κₚ = κₚ} {p = p} g _ _ ct _) with ct-src ct
    ... | refl with idxπ {W = record W { κʷ = κₚ }} e p | pend-all wf e
    ... | ∀⊑ _ _ (⇒⊑⇒ (X⊑★ (there h)) _) | (β , rh) ∷ [] =
      no★-right {V = record W { κʷ = κₚ }} (trans (cg-none ng-genpK g) eκ)
        rh h
    go [] e _ = K2-vs-∀ {W = W} e (λ ()) q
    go (_ ∷ _ ∷ _) e _ = K2-vs-∀ {W = W} e (λ ()) q

  g2b : ∀ {W : World Δ Δ′} {γ A C} {q : A ⊑ᵂ⟨ W ⟩ `∀ C}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ B2 ∶ q)
  g2b eκ (cast⊑ _ d _ _) = K★-vs-∀ d
  g2b eκ (⊑⟪⟫ I _ wf d _ _) = g2a (trans (same-κ I) eκ) wf d

  -- K★ against a right term of type ∀Y.★→Y→★ (the ∀-cast's)
  K★-vs-KY : ∀ {W : World Δ Δ′} {γ M′} {q : (★ ⇒ (★ ⇒ ★)) ⊑ᵂ⟨ W ⟩ KY}
    → ¬ (W ∣ γ ⊢ K★ ⊑ M′ ∶ q)
  K★-vs-KY = K★-vs-∀

  g2c : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ B2 ⟨ [] ∣ ∀ᵖ ci ⟩ ∶ q)
  g2c eκ (cast⊑cast d _ ct′ _) with ct-src ct′
  ... | refl = K★-vs-∀ d
  g2c eκ (cast⊑ _ d _ _) with ty-cast (rtyT d)
  ... | refl = K★-vs-∀ d
  g2c eκ (⊑cast g _ d ct _) with ct-src ct
  ... | refl = g2b (trans (cg-none ng-∀ci g) eκ) d

  g2-st2-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ GR₂ ∶ q)
  g2-st2-unrelated eκ (cast⊑cast d _ ct′ _) with ct-src ct′
  ... | refl = K★-vs-∀ d
  g2-st2-unrelated eκ (cast⊑ _ d _ _) = k d
    where
    k : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ K★ ⊑ GR₂ ∶ q)
    k (⊑cast _ _ d _ ct) = k′ d
      where
      k′ : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
        → ¬ (W ∣ γ ⊢ K★ ⊑ B2 ⟨ [] ∣ ∀ᵖ ci ⟩ ∶ q)
      k′ d with ty-cast (rtyT d)
      ... | refl = K★-vs-∀ d
  g2-st2-unrelated eκ (⊑cast g _ d _ _) =
    g2c (trans (cg-none ng-instY g) eκ) d

  -- REAL RELATION: the G2 walk never looks inside +X^α, so it refutes
  -- state 4 as well (any inner term Z)
  module G2W (Z : Term) where
    CIz BYz Fz : Term
    CIz = (Z ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩
    BYz = CIz ⟪ ΘY , cY ⟫
    Fz  = BYz ⟨ [] ∣ cf ⟩

    kB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ K★ ⊑ BYz ∶ q)
    kB (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-K★ tp-ci d

    gY : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ GL ⊑ CIz ∶ q)
    gY {W = W} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
    ... | refl | refl = no-K2-★ {W = W} eκ wf q

    unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ Fz ∶ q)
    unrelated eκ (cast⊑cast d _ _ _) = kB d
    unrelated eκ (cast⊑ _ d _ _) = k d
      where
      k : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
        → ¬ (W ∣ γ ⊢ K★ ⊑ Fz ∶ q)
      k (⊑cast _ _ d _ _) = kB d
    unrelated eκ (⊑cast g _ d _ _) = gB (trans (cg-none ng-cf g) eκ) d
      where
      gB : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
        → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ BYz ∶ q)
      gB eκ (cast⊑ _ d _ _) = kB d
      gB eκ (⊑⟪⟫ I _ wf d _ _) = gY (trans (same-κ I) eκ) wf d

  g2-st4-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ GL ⊑ GR₄ ∶ q)
  g2-st4-unrelated = G2W.unrelated CK₄

  ----------------------------------------------------------------------
  -- V2 relates both intermediate states
  ----------------------------------------------------------------------

  ΔX0 : Ctxᵗ
  ΔX0 = (bindR ★ ∷ bindR ★ ∷ []) ∣ (1 ∷ [])

  genpK-ty : CastTy ΔRᵢ (★∼X ∷ []) (genᵖ pK) (★ ⇒ (★ ⇒ ★))
    (`∀ (` 1 ⇒ (` 0 ⇒ ` 1)))
  genpK-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = G2a})))

  U1-ty : BdyTy ΔRᵢ (unbind 0 0 ∷ []) ΔR (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  U1-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔRᵢ} {M = U1}))))

  B2-ty : BdyTy ΔR ΘA ΔRᵢ (`∀ (` 1 ⇒ (` 0 ⇒ ` 1))) cA KY
  B2-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔR} {M = B2}))))

  U0-ty : BdyTy ΔXY (unbind 0 0 ∷ []) ΔX0 (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  U0-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔXY} {M = UK₄}))))

  U1′-ty : BdyTy ΔX0 (unbind 0 1 ∷ []) ΔT2 (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  U1′-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔX0} {M = K★ ⟪ unbind 0 1 ∷ [] , cU ⟫}))))

  pK4-ty : CastTy ΔXY (★∼X ∷ ★∼X ∷ []) pK (★ ⇒ (★ ⇒ ★)) (` 1 ⇒ (` 0 ⇒ ` 1))
  pK4-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = CK₄})))

  -- the right's −Y^β then −X^α (state 4 has them unmerged)
  Wu0 : World empty ΔX0
  Wu0 = world⁰ 1 (skip []↪) (keep []↪) [] [] []

  intU0 : Interior (record Wm { πʷ = [] }) [] (unbind 0 0 ∷ []) Wu0
  intU0 = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , here) del-here (fresh∷ (λ ()) fresh[])))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  wfU0 : WfWorld Wu0
  wfU0 = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
    (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
    [] [] []

  intU1 : Interior Wu0 [] (unbind 0 1 ∷ []) W₄
  intU1 = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , there here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  q2 : K2 ⊑ˢ⟨ record (W₃ ⊕ʳ^ 0) { πʷ = 0 ∷ [] } ⟩ `∀ (` 1 ⇒ (` 0 ⇒ ` 1))
  q2 = inj₁ (∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)))

  module InV2 where
    open V2
    open Pos GenCastValue

    K★⊑K★₃ : W₃ ⊕ʳ^ 0 ∣ [] ⊢ K★ ⊑ᵛ U1 ∶ ⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)
    K★⊑K★₃ =
      ⊑⟪⟫ IntN (pv-real push-none) (W₃-wf [])
        (ƛ⊑ƛ tf tf (ƛ⊑ƛ {pA = ★⊑★} {pB = ★⊑★} tf tf (x⊑x (Sʷ Zʷ)))) U1-ty
        (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)) (inj₁ tt)

    -- state 2: +X^α pushes X; the left's chain pops X against the
    -- right's remaining `gen Y. …` (its inner gen layer matched by type)
    g2-st2 : W₃ ∣ [] ⊢ GL ⊑ᵛ GR₂ ∶ q-top
    g2-st2 =
      ⊑cast₀ᵛ
        (⊑cast₀ᵛ
          (⊑⟪⟫ int-ro₃ (pv-real (push ca-[] (refl ∷ []) (inj₂ vGL))) Wi₃-wf
            (cast⊑cast (cg-gen vK★ cg-plain) K★⊑K★₃ genK-ty genpK-ty q2
              (inj₁ tt))
            B2-ty q-src1 (inj₁ tt))
          ∀ci-ty q-src1 (inj₁ tt))
        instY-ty₂ q-top (inj₁ tt)

    bodyK₄ : Wm ∣ [] ⊢ GL ⊑ᵛ CK₄ ∶ qm
    bodyK₄ =
      cast⊑cast (cg-gen vK★ (cg-gen vK★ cg-plain))
        (⊑⟪⟫ intU0 (pv-real push-none) wfU0
          (⊑⟪⟫ intU1 (pv-real push-none) W₄-wf K★⊑K★ᵛ U1′-ty
            (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)) (inj₁ tt))
          U0-ty (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)) (inj₁ tt))
        genK-ty pK4-ty qm (inj₁ tt)

    -- state 4: as the final pair, before the Merge
    g2-st4 : W₄ ∣ [] ⊢ GL ⊑ᵛ GR₄ ∶ q-top
    g2-st4 =
      ⊑cast₀ᵛ
        (⊑⟪⟫ intYg (pv-real (push ca-[] (refl ∷ []) (inj₂ vGL))) wfYg
          (⊑cast₀ᵛ
            (⊑⟪⟫ intXg (pv-new gcvGL (ca-∷ refl ca-[]) (refl ∷ []) vGL) wfm
              bodyK₄ bX qY (inj₂ gcvGL))
            ci-ty qY (inj₂ gcvGL))
          bY q-top (inj₁ tt))
        cf-ty q-top (inj₁ tt)

------------------------------------------------------------------------
-- DGG PART 1 HOLDS IN V2 for all five pairs (the left is a value; the
-- right's run reaches its value; V2 relates them at a well-formed world
-- with no pending name and no permission); the initial pairs are
-- related (the real derivations, `fromReal`)
------------------------------------------------------------------------

runOf : ∀ {Δ A M} (tr : Trace Δ A M) → EndsV tr → Δ ⊢ M -→* traceEnd tr
runOf (stop (value v)) e = done
runOf (st ◅⟨ ⊢M′ ⟩ tr) e = st then runOf tr e

vEnd : ∀ {Δ A M} (tr : Trace Δ A M) → EndsV tr → Value (traceEnd tr)
vEnd (stop (value v)) e = v
vEnd (st ◅⟨ ⊢M′ ⟩ tr) e = vEnd tr e

module DGG1 where
  open V2
  open Pos GenCastValue
  open Pos2

  Part1 : Term → Term → Ty → Ty → Set
  Part1 M M′ A A′ =
    ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ] Value V′
      × Σ[ W ∈ World empty (runCtx r′) ] WfWorld W × πʷ W ≡ [] × κʷ W ≡ []
        × Σ[ q ∈ A ⊑ˢ⟨ W ⟩ A′ ] (W ∣ [] ⊢ M ⊑ᵛ V′ ∶ q)

  g0 : Part1 FL FR (`∀ (` 0 ⇒ `ℕ)) (★ ⇒ `ℕ)
  g0 = _ , runOf (eval 40 FR FR-⊢) tt , vEnd (eval 40 FR FR-⊢) tt ,
       W₃ , W₃-wf [] , refl , refl , G0.q0 , g0-final

  g2m : Part1 GL GRm K2 (★ ⇒ (★ ⇒ ★))
  g2m = _ , runOf (eval 40 GRm GRm-⊢) tt , vEnd (eval 40 GRm GRm-⊢) tt ,
        W₄ , W₄-wf , refl , refl , q-top , g2m-final

  g2 : Part1 GL GR K2 (★ ⇒ (★ ⇒ ★))
  g2 = _ , runOf (eval 40 GR GR-⊢) tt , vEnd (eval 40 GR GR-⊢) tt ,
       W₄ , W₄-wf , refl , refl , q-top , g2-final

  hrm : Part1 HL HRm K2 (★ ⇒ (★ ⇒ ★))
  hrm = _ , runOf (eval 40 HRm HRm-⊢) tt , vEnd (eval 40 HRm HRm-⊢) tt ,
        W₄ , W₄-wf , refl , refl , q-top , hrm-final

  hr : Part1 HL HR K2 (★ ⇒ (★ ⇒ ★))
  hr = _ , runOf (eval 40 HR HR-⊢) tt , vEnd (eval 40 HR HR-⊢) tt ,
       W₄ , W₄-wf , refl , refl , q-top , hr-final

  -- the initial pairs
  init-g0  = fromReal G0.init
  init-g2m = fromReal G2m.init
  init-g2  = fromReal G2.init
  init-hrm = fromReal HRm.init
  init-hr  = fromReal HR.init

-- nested gens: ((λx:★.λy:★.x : ∀Y.★→Y→★) : ∀X.∀Y.X→Y→X)
genY genX∀ : Coercion
genY  = genᵖ (idᵖ ★ ↦ᵖ (((` 0) !) ↦ᵖ idᵖ ★))
genX∀ = genᵖ (∀ᵖ (((` 1) !) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) ？ 0))))
NL NR NRm : Term
NL = (K★ ⟨ [] ∣ genY ⟩) ⟨ [] ∣ genX∀ ⟩
NL-⊢ : empty ∣ [] ⊢ NL ⦂ K2
NL-⊢ = tc
NR = (NL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩
NR-⊢ : empty ∣ [] ⊢ NR ⦂ ★ ⇒ (★ ⇒ ★)
NR-⊢ = tc
NRm = NL ⟨ [] ∣ instK ⟩
NRm-⊢ : empty ∣ [] ⊢ NRm ⦂ ★ ⇒ (★ ⇒ ★)
NRm-⊢ = tc

module N2 where
  pY pX : Coercion
  pY = idᵖ ★ ↦ᵖ (((` 0) !) ↦ᵖ idᵖ ★)
  pX = ((` 1) !) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) ？ 0))

  cUX : Conv
  cUX = tail (mid (tail (mid (id ★))
          ↦ tail (mid (tail (mid (id (` 0))) ↦ tail (mid (id ★))))))

  NUY NCY NUX NCX NF NmF NL₁ : Term
  NL₁ = K★ ⟨ [] ∣ genY ⟩
  NUY = K★ ⟪ unbind 0 0 ∷ [] , cU ⟫
  NCY = NUY ⟨ ★∼X ∷ [] ∣ pY ⟩
  NUX = NCY ⟪ unbind 1 1 ∷ [] , cUX ⟫
  NCX = NUX ⟨ X∼X ∷ ★∼X ∷ [] ∣ pX ⟩
  NF  = (((NCX ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩) ⟪ ΘY , cY ⟫) ⟨ [] ∣ cf ⟩
  NmF = (NCX ⟪ ΘXY , cXY ⟫) ⟨ [] ∣ cf ⟩

  NF-end : traceEnd (eval 40 NR NR-⊢) ≡ NF
  NF-end = refl

  NmF-end : traceEnd (eval 40 NRm NRm-⊢) ≡ NmF
  NmF-end = refl

  vNL₁ : Value NL₁
  vNL₁ = V-simple (S-cast vK★ I-gen)

  vNL : Value NL
  vNL = V-simple (S-cast vNL₁ I-gen)

  gcvNL : GenCastValue NL
  gcvNL = gcv vNL₁ gl-gen

  genY-ty : CastTy empty [] genY (★ ⇒ (★ ⇒ ★)) KY
  genY-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = NL₁})))

  genX∀-ty : CastTy empty [] genX∀ KY K2
  genX∀-ty = proj₂ (proj₂ (cast-inv {Γ = []} NL-⊢))

  pY-ty : CastTy ΔY (★∼X ∷ []) pY (★ ⇒ (★ ⇒ ★)) (★ ⇒ (` 0 ⇒ ★))
  pY-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔY} {M = NCY})))

  pX-ty : CastTy ΔXY (X∼X ∷ ★∼X ∷ []) pX (★ ⇒ (` 0 ⇒ ★)) (` 1 ⇒ (` 0 ⇒ ` 1))
  pX-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = ΔXY} {M = NCX})))

  UY-ty : BdyTy ΔY (unbind 0 0 ∷ []) ΔT2 (★ ⇒ (★ ⇒ ★)) cU (★ ⇒ (★ ⇒ ★))
  UY-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔY} {M = NUY}))))

  UX-ty : BdyTy ΔXY (unbind 1 1 ∷ []) ΔY (★ ⇒ (` 0 ⇒ ★)) cUX (★ ⇒ (` 0 ⇒ ★))
  UX-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔXY} {M = NUX}))))

  BXYn-ty : BdyTy ΔT2 ΘXY ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cXY (★ ⇒ (★ ⇒ ★))
  BXYn-ty = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
    (tc {Δ = ΔT2} {M = NCX ⟪ ΘXY , cXY ⟫}))))

  -- the right's −X^α (X was popped by the outer gen; Y continues)
  intUX : Interior (record Wm { πʷ = 0 ∷ [] }) [] (unbind 1 1 ∷ []) WYg
  intUX = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , there here) (del-there del-here)
          (fresh∷ (λ ()) fresh[])))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  -- the right's −Y^β (Y was popped by the inner gen)
  intUY : Interior (record WYg { πʷ = [] }) [] (unbind 0 0 ∷ []) W₄
  intUY = record
    { int-left   = interior changes[]
    ; int-right  = interior (changes∷ changes[]
        (step-unbind (bindR ★ , here) del-here fresh[]))
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  qYY : KY ⊑ˢ⟨ WYg ⟩ (★ ⇒ (` 0 ⇒ ★))
  qYY = inj₁ (⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★))

  qXY : KY ⊑ˢ⟨ record Wm { πʷ = 0 ∷ [] } ⟩ (★ ⇒ (` 0 ⇒ ★))
  qXY = inj₁ (⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★))

  module InV2 where
    open V2
    open Pos GenCastValue

    -- the outer gen cast pops X and passes Y to the inner gen cast,
    -- which pops Y
    bodyN : Wm ∣ [] ⊢ NL ⊑ᵛ NCX ∶ qm
    bodyN =
      cast⊑cast (cg-gen vNL₁ (cg-∀ vNL₁ cg-plain))
        (⊑⟪⟫ intUX (pv-real (push (ca-∷ refl ca-[]) [] (inj₁ refl))) wfYg
          (cast⊑cast (cg-gen vK★ cg-plain)
            (⊑⟪⟫ intUY (pv-real push-none) W₄-wf K★⊑K★ᵛ UY-ty
              (⇒⊑⇒ ★⊑★ (⇒⊑⇒ ★⊑★ ★⊑★)) (inj₁ tt))
            genY-ty pY-ty qYY (inj₁ tt))
          UX-ty qXY (inj₁ tt))
        genX∀-ty pX-ty qm (inj₁ tt)

    nrm-final : W₄ ∣ [] ⊢ NL ⊑ᵛ NmF ∶ q-top
    nrm-final =
      ⊑cast₀ᵛ
        (⊑⟪⟫ intXYW (pv-real (push ca-[] (refl ∷ refl ∷ []) (inj₂ vNL))) wfm
          bodyN BXYn-ty q-top (inj₁ tt))
        cf-ty q-top (inj₁ tt)

    nr-final : W₄ ∣ [] ⊢ NL ⊑ᵛ NF ∶ q-top
    nr-final =
      ⊑cast₀ᵛ
        (⊑⟪⟫ intYg (pv-real (push ca-[] (refl ∷ []) (inj₂ vNL))) wfYg
          (⊑cast₀ᵛ
            (⊑⟪⟫ intXg (pv-new gcvNL (ca-∷ refl ca-[]) (refl ∷ []) vNL) wfm
              bodyN bX qY (inj₂ gcvNL))
            ci-ty qY (inj₂ gcvNL))
          bY q-top (inj₁ tt))
        cf-ty q-top (inj₁ tt)

  ----------------------------------------------------------------------
  -- REAL RELATION: both nested-gen final pairs are unrelated
  ----------------------------------------------------------------------

  tp-pX : ∀ {R} → trgᵖ pX ≡ R → Σ[ R₁ ∈ Ty ] Σ[ y ∈ ℕ ] Σ[ R₃ ∈ Ty ]
    R ≡ R₁ ⇒ (` y ⇒ R₃)
  tp-pX refl = _ , _ , _ , refl

  -- ∀Y.★→Y→★ against a right type with a NAME first: never
  no-KY-var : ∀ {W : World Δ Δ′} {x R} → ¬ (KY ⊑ᵂ⟨ W ⟩ (` x ⇒ R))
  no-KY-var {W = W} q = go (πʷ W) refl
    where
    go : ∀ π → πʷ W ≡ π → ⊥
    go [] e with idxπ {W = W} e q
    ... | ∀⊑ _ _ (⇒⊑⇒ () _)
    go (_ ∷ []) e with idxπ {W = W} e q
    ... | ⇒⊑⇒ () _
    go (_ ∷ _ ∷ _) e = idxπ {W = W} e q

  n1C : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ NL₁ ⊑ NCX ∶ q)
  n1C {W = W} {q = q} d with ty-cast (ltyT d) | ty-cast (rtyT d)
  ... | refl | refl = no-KY-var {W = W} q

  kX : ∀ {W : World Δ Δ′} {γ Θ c A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ K★ ⊑ NCX ⟪ Θ , c ⟫ ∶ q)
  kX (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-K★ tp-pX d

  n1X : ∀ {W : World Δ Δ′} {γ Θ c A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ NL₁ ⊑ NCX ⟪ Θ , c ⟫ ∶ q)
  n1X (cast⊑ _ d _ _) = kX d
  n1X (⊑⟪⟫ _ _ _ d _ _) = n1C d

  -- NR: two casts
  module TwoCast where
    CIn BYn : Term
    CIn = (NCX ⟪ ΘX , cX ⟫) ⟨ X∼X ∷ [] ∣ ci ⟩
    BYn = CIn ⟪ ΘY , cY ⟫

    kB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ K★ ⊑ BYn ∶ q)
    kB (⊑⟪⟫ _ _ _ d _ _) = no-lm-cast lm-K★ tp-ci d

    -- the peeled left ∀Y.★→Y→★ may open Y at +Y^β, but then faces
    -- X → Y → X inside +X^α with ★ first
    n1Y : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NL₁ ⊑ CIn ∶ q)
    n1Y (cast⊑cast d _ _ _) = kX d
    n1Y (cast⊑ _ d _ _) = no-lm-cast lm-K★ tp-ci d
    n1Y (⊑cast _ _ d _ _) = n1X d

    n1B : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NL₁ ⊑ BYn ∶ q)
    n1B (cast⊑ _ d _ _) = kB d
    n1B (⊑⟪⟫ _ _ _ d _ _) = n1Y d

    nY : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → κʷ W ≡ [] → WfWorld W → ¬ (W ∣ γ ⊢ NL ⊑ CIn ∶ q)
    nY {W = W} {q = q} eκ wf d with ty-cast (ltyT d) | ty-cast (rtyT d)
    ... | refl | refl = no-K2-★ {W = W} eκ wf q

    nB : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ NL ⊑ BYn ∶ q)
    nB eκ (cast⊑ _ d _ _) = n1B d
    nB eκ (⊑⟪⟫ I _ wf d _ _) = nY (trans (same-κ I) eκ) wf d

    nr-unrelated : ∀ {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ NL ⊑ NF ∶ q)
    nr-unrelated eκ (cast⊑cast d _ _ _) = n1B d
    nr-unrelated eκ (cast⊑ _ d _ _) = n1F d
      where
      n1F : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
        → ¬ (W ∣ γ ⊢ NL₁ ⊑ NF ∶ q)
      n1F (cast⊑cast d _ _ _) = kB d
      n1F (cast⊑ _ d _ _) = kF d
        where
        kF : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
          → ¬ (W ∣ γ ⊢ K★ ⊑ NF ∶ q)
        kF (⊑cast _ _ d _ _) = kB d
      n1F (⊑cast _ _ d _ _) = n1B d
    nr-unrelated eκ (⊑cast g _ d _ _) = nB (trans (cg-none ng-cf g) eκ) d

  -- NRm: one cast (Merge); contexts pinned (ΔT2 outside, ΔXY inside)
  module Merged where
    BXYn : Term
    BXYn = NCX ⟪ ΘXY , cXY ⟫

    two-carried : ∀ {Θ′ M k k′ πᵢ} → Push Θ′ M (k ∷ k′ ∷ []) πᵢ
      → Σ[ a ∈ ℕ ] Σ[ b ∈ ℕ ] Σ[ r ∈ List ℕ ] πᵢ ≡ a ∷ b ∷ r
    two-carried (push (ca-∷ _ (ca-∷ _ ca-[])) _ _) = _ , _ , _ , refl

    -- inside the right's −X^α only Y is named, but both pending names
    -- would have to continue: two distinct pending names in a context
    -- with one name
    nU : ∀ {W : World empty ΔXY} {γ A A′ k k′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → πʷ W ≡ k ∷ k′ ∷ [] → ¬ (W ∣ γ ⊢ NL ⊑ NUX ∶ q)
    nU e (cast⊑ cc _ _ _) = no-cc2 (subst (λ π → CastClaim _ _ π _) e cc)
    nU {W = W} e (⊑⟪⟫ {Wᵢ = Wᵢ} I pu wf d _ _)
      with interior-functional (int-right I) (int-right intUX)
    ... | refl with two-carried (subst (λ π → Push _ _ π _) e pu)
    ... | a , b , r , eᵢ
      with pend-all wf eᵢ | subst (AllPairs _≢_) eᵢ (wf-distinct wf)
    ... | (_ , here) ∷ (_ , here) ∷ _ | (a≢b ∷ _) ∷ _ = a≢b refl

    nC : ∀ {W : World empty ΔXY} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NL ⊑ NCX ∶ q)
    nC {W = W} {γ} {q = q} d with ty-cast (ltyT d) | ty-cast (rtyT d)
    ... | refl | refl = go (πʷ W) refl d
      where
      go : ∀ π → πʷ W ≡ π → ¬ (W ∣ γ ⊢ NL ⊑ NCX ∶ q)
      go (k ∷ k′ ∷ []) () (cast⊑cast _ _ _ _)
      go (k ∷ k′ ∷ []) e (cast⊑ cc _ _ _) =
        no-cc2 (subst (λ π → CastClaim _ _ π _) e cc)
      go (k ∷ k′ ∷ []) e (⊑cast _ _ d′ _ _) = nU e d′
      go [] e _ = K2-01 {W = W} e (λ ()) q
      go (_ ∷ []) e _ = K2-01 {W = W} e (λ ()) q
      go (_ ∷ _ ∷ _ ∷ _) e _ = K2-01 {W = W} e (λ ()) q

    nB : ∀ {W : World empty ΔT2} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NL ⊑ BXYn ∶ q)
    nB (cast⊑ _ d _ _) = n1X d
    nB (⊑⟪⟫ I _ _ d _ _) with interior-functional (int-right I) G2m.intXYm
    ... | refl = nC d

    nrm-unrelated : ∀ {W : World empty ΔT2} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
      → ¬ (W ∣ γ ⊢ NL ⊑ NmF ∶ q)
    nrm-unrelated (cast⊑cast d _ _ _) = n1X d
    nrm-unrelated (cast⊑ _ d _ _) = n1F d
      where
      n1F : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
        → ¬ (W ∣ γ ⊢ NL₁ ⊑ NmF ∶ q)
      n1F (cast⊑cast d _ _ _) = kX d
      n1F (cast⊑ _ d _ _) = kF d
        where
        kF : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
          → ¬ (W ∣ γ ⊢ K★ ⊑ NmF ∶ q)
        kF (⊑cast _ _ d _ _) = kX d
      n1F (⊑cast _ _ d _ _) = n1X d
    nrm-unrelated (⊑cast _ _ d _ _) = nB d

  -- the initial pairs are related; DGG part 1 fails for both
  idKY : ∀ {μ} → μ ⊢ KY ⊑ KY
  idKY = ∀⊑∀ (⇒⊑⇒ ★⊑★ (⇒⊑⇒ X⊑X ★⊑★))

  NL⊑NL : ∅ʷ ∣ [] ⊢ NL ⊑ NL ∶ idK2
  NL⊑NL = cast⊑cast (cast⊑cast K★⊑K★ genY-ty genY-ty idKY)
            genX∀-ty genX∀-ty idK2

  init : ∅ʷ ∣ [] ⊢ NL ⊑ NR ∶ q-top
  init = ⊑cast₀ (⊑cast₀ NL⊑NL instX∀-ty q-src1) instY-ty₀ q-top

  init-m : ∅ʷ ∣ [] ⊢ NL ⊑ NRm ∶ q-top
  init-m = ⊑cast₀ NL⊑NL instK-ty q-top


  not-dgg : ¬ DGG
  not-dgg dgg with proj₁ (dgg init) done vNL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d
    with final-of (eval 40 NR NR-⊢) NR-⊢ tt r′ vV′
  ... | refl , _ = TwoCast.nr-unrelated eκ d

  at : ∀ {Δ′} → Δ′ ≡ ΔT2 → ∀ {W : World empty Δ′} {γ A A′}
    {q : A ⊑ᵂ⟨ W ⟩ A′} → ¬ (W ∣ γ ⊢ NL ⊑ NmF ∶ q)
  at refl = Merged.nrm-unrelated

  not-dgg-m : ¬ DGG
  not-dgg-m dgg with proj₁ (dgg init-m) done vNL
  ... | V′ , r′ , vV′ , W , _ , _ , eκ , q , d
    with final-of (eval 40 NRm NRm-⊢) NRm-⊢ tt r′ vV′
  ... | refl , ec = at ec d

  -- V2: DGG part 1 holds
  module DGG1ᴺ where
    open V2
    open InV2
    open DGG1 using (Part1)

    nr : Part1 NL NR K2 (★ ⇒ (★ ⇒ ★))
    nr = _ , runOf (eval 40 NR NR-⊢) tt , vEnd (eval 40 NR NR-⊢) tt ,
         W₄ , W₄-wf , refl , refl , q-top , nr-final

    nrm : Part1 NL NRm K2 (★ ⇒ (★ ⇒ ★))
    nrm = _ , runOf (eval 40 NRm NRm-⊢) tt , vEnd (eval 40 NRm NRm-⊢) tt ,
          W₄ , W₄-wf , refl , refl , q-top , nrm-final

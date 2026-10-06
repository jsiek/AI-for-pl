module proof.DGG.notes.ReductionAudit where

-- File Charter:
--   * MECHANIZED FACTS FOR ReductionAudit.md (this directory): what the
--     relation of TermImprecision (D27 pushes, D28 permissions with
--     R1/R2, D29 claim-rep) checks at a redex and at its contractum.
--     LEFT is the more precise side.  No holes, no postulates, no
--     pragmas; nothing outside this directory is edited; All.agda does
--     not import it.  From GTNF/agda:
--       agda --safe -v0 proof/DGG/notes/ReductionAudit.agda
--   * P4k (`module P4k`): P4 with the constant body, i.e. the left
--     argument ΛY.λx:Y.5 against the right (λx:★.5 : ∀X.X→ℕ), whose gen
--     wrapper `X! → id(ℕ)` GRANTS NOTHING (D28).  RELATED initial cast
--     terms (`init`); the ν pair after both Betas is related (`pre`);
--     after both TyBetas the pair is related in no world without
--     permissions (`post-unrelated`), nor is any later right state
--     (`right-states`); so SIM IS FALSE (`not-sim : ¬ Sim`).  What
--     TyBeta dropped: the left binder was LEFT-ONLY (X⊑★) against the
--     gen's ★ source; after TyBeta it is a joined name at X⊑X.
--   * P4h (`module P4h`): P4 whose left Λ captures a free variable, so
--     the left's Beta puts it under the Λ's crossΛ hide
--     [−Y^β] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩.  RELATED initial cast terms
--     (`init`) and ν pair (`pre`, where the hide passes R1: the Λ's rep.
--     var is unpaired); after both TyBetas the hide's rep. var is
--     paired with the right's, which the gen wrapper's `X?` grants, and
--     R1 rejects the hide although its conversion seals nothing
--     (`noBody`, `post-unrelated`); SIM IS FALSE (`not-sim : ¬ Sim`).
--   * INTERFACES (`module Interfaces`, design.md §12.2.1): the two ∀
--     bodies with the bound name at X⊑X.  They fail for C1-C4g
--     (`iface-C1`) and C5 (`iface-C5`), hold for P4, K, P4h, P4k, G0,
--     G2; the trivial interface (X, X), which fits C5's late boundaries,
--     is well formed (`iface-fake`); and ν⊑ν's index need not be ∀⊑∀
--     (`ν-index-∀⊑`), unlike the source rule []⊑[]ᴳ.
--   * A LEFT-ONLY TyBeta drops ∀⊑'s side condition `X ∈ C` (`module
--     LeftOnly`): ν X:=ℕ.((ΛX.5) X)⟨id(ℕ)⟩ against 5 is related in no
--     world (`redex-unrelated`); its contractum is (`contractum`).
--     Harmless: both sides answer 5.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; head; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.AllPairs as AP
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Imprecision
open import ImprecisionWorld
open import TermImprecision
open import ConversionImprecision
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms)
open import proof.DGG.ImprecisionTyping using (imprecision-typing)
open import proof.TypeSafety.CoercionTyping using (coercion-src; coercion-trg)
open import examples.TermImprecisionPermissionExamples
  using (no★-right; NoGrant; cg-none; nf-⇒; nf-ℕ; plain-idx; var⊑var)
open import examples.TermImprecisionExamples
  using (Θ₀; ΔL; ΔLᵢ; Wν; Wν-conv; revX; revX⊑revX; int₀)
open import Data.Bool using (true)
open import Data.Nat using (_≡ᵇ_)
open import examples.TermImprecisionPermissionExamples using (module Runs)
open import proof.Ctx using (wf-empty)
open import proof.DGG.SimDef using (Sim)
open import proof.DGG.EvolveLemmas using (⟿-κʷ)
open import Data.Unit using (tt)
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_)

private
  variable
    Δ Δ′ : Ctxᵗ

------------------------------------------------------------------------
-- Tools: types read off the typings of a derivation (TwoGen's)
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

ty-$ : ∀ {Γ n A} → Δ ∣ Γ ⊢ $ n ⦂ A → A ≡ `ℕ
ty-$ ⊢$ = refl

ty-Λ : ∀ {Γ N A} → Δ ∣ Γ ⊢ Λ N ⦂ A
  → Σ[ C ∈ Ty ] (A ≡ `∀ C) × (underΛ Δ ∣ ⤊ Γ ⊢ N ⦂ C)
ty-Λ (⊢Λ _ ⊢N) = _ , refl , ⊢N

-- a boundary's interior reading, off its typing bundle
bdy-int : ∀ {Θ Δᵢ Bᵢ c Bₑ} → BdyTy Δ Θ Δᵢ Bᵢ c Bₑ → Δ ⊢ⁱ Θ ⇒ Δᵢ
bdy-int (bdy-ty (bw _ i _) _ _ _ _) = i

-- the domain of an arrow imprecision
dom⊑ : ∀ {μ A B A′ B′} → μ ⊢ A ⇒ B ⊑ A′ ⇒ B′ → μ ⊢ A ⊑ A′
dom⊑ (⇒⊑⇒ a _) = a
dom⊑ (ι⊑ι ())

-- the joined names of a well-formed world name paired rep. vars
-- (PermissionsR's `joint-pair`)
suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

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

------------------------------------------------------------------------
-- P4k: the programs
------------------------------------------------------------------------

∀Xℕ : Ty
∀Xℕ = `∀ (` 0 ⇒ `ℕ)

cK : Conv
cK = reveal 0 (` 0 ⇒ `ℕ)

-- the shared function  λf:∀X.X→ℕ. f [ℕ] 5
F : Term
F = ƛ ∀Xℕ ∙ ((ν `ℕ · ` 0 ⟨ cK ⟩) · $ 5)

-- the left argument  ΛY. λx:Y. 5
KL : Term
KL = Λ (ƛ (` 0) ∙ $ 5)

-- the right argument  (λx:★. 5 : ∀X. X→ℕ)
genK5 : Coercion
genK5 = genᵖ (((` 0) !) ↦ᵖ idᵖ `ℕ)

KR : Term
KR = (ƛ ★ ∙ $ 5) ⟨ [] ∣ genK5 ⟩

LK RK : Term
LK = F · KL
RK = F · KR

LK-⊢ : empty ∣ [] ⊢ LK ⦂ `ℕ
LK-⊢ = tc

RK-⊢ : empty ∣ [] ⊢ RK ⦂ `ℕ
RK-⊢ = tc

------------------------------------------------------------------------
-- P4h: the programs (P4 whose Λ captures a free variable, so the
-- left's Beta wraps it in the Λ's crossΛ hide)
------------------------------------------------------------------------

∀X⇒X : Ty
∀X⇒X = `∀ (` 0 ⇒ ` 0)

-- P4's function  λh:∀X.X→X. h [ℕ] 5
F4 : Term
F4 = ƛ ∀X⇒X ∙ ((ν `ℕ · ` 0 ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5)

-- the body  (λy:ℕ. x) (f 1)  under x (0) and f (1)
bodyH : Term
bodyH = (ƛ `ℕ ∙ ` 1) · (` 1 · $ 1)

genI : Coercion
genI = genᵖ (((` 0) !) ↦ᵖ ((` 0) ？ 0))

-- left argument  (λf:ℕ→ℕ. ΛX. λx:X. (λy:ℕ. x) (f 1)) (λz:ℕ. z)
-- right argument (λf:ℕ→ℕ. (λx:★. (λy:ℕ. x) (f 1) : ∀X. X→X)) (λz:ℕ. z)
HL HR : Term
HL = (ƛ (`ℕ ⇒ `ℕ) ∙ Λ (ƛ (` 0) ∙ bodyH)) · (ƛ `ℕ ∙ ` 0)
HR = (ƛ (`ℕ ⇒ `ℕ) ∙ ((ƛ ★ ∙ bodyH) ⟨ [] ∣ genI ⟩)) · (ƛ `ℕ ∙ ` 0)

LH RH : Term
LH = F4 · HL
RH = F4 · HR

LH-⊢ : empty ∣ [] ⊢ LH ⦂ `ℕ
LH-⊢ = tc

RH-⊢ : empty ∣ [] ⊢ RH ⦂ `ℕ
RH-⊢ = tc

------------------------------------------------------------------------
-- P4k: the initial pair, the ν pair, the TyBeta pair, ¬ Sim
------------------------------------------------------------------------

module P4k where
  nth : List Term → ℕ → Term
  nth []       _       = $ 0
  nth (x ∷ xs) zero    = x
  nth (x ∷ xs) (suc n) = nth xs n

  q∀ : ∀ {μ} → μ ⊢ ∀Xℕ ⊑ ∀Xℕ
  q∀ = ∀⊑∀ (⇒⊑⇒ X⊑X (ι⊑ι base-ℕ))

  q★ : ∀ {μ} → μ ⊢ ∀Xℕ ⊑ ★ ⇒ `ℕ
  q★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (ι⊑ι base-ℕ))

  ℕ⇒ℕ : ∀ {μ} → μ ⊢ `ℕ ⇒ `ℕ ⊑ `ℕ ⇒ `ℕ
  ℕ⇒ℕ = ⇒⊑⇒ (ι⊑ι base-ℕ) (ι⊑ι base-ℕ)

  genK5-ty : CastTy empty [] genK5 (★ ⇒ `ℕ) ∀Xℕ
  genK5-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = KR})))

  νF : Term
  νF = ν `ℕ · ` 0 ⟨ cK ⟩

  νF-ty : NuTy empty `ℕ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  νF-ty = proj₂ (proj₂ (ν-inv {Γ = ∀Xℕ ∷ []}
    (tc {Δ = empty} {Γ = ∀Xℕ ∷ []} {M = νF})))

  cK⊑cK : ∀ {Δ Δ′} {W : World Δ Δ′} → Joins W 0 0 → ConvImp W cK cK
  cK⊑cK j =
    conv-tail⊑tail
      (conv-mid⊑mid
        (conv-↦⊑↦ (conv-tail⊑tail (conv-seal⊑seal j))
                   (conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))))

  -- the left Λ against the right gen value: the Λ's binder is a fresh
  -- LEFT-ONLY name (X⊑★), facing the gen's source ★→ℕ
  KL⊑KR : ∀ {Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ}
    → let W = world {empty} {empty} Ω ηᴸ ηᴿ ϱᵍ ϱˡ κ [] in
      (q : ∀Xℕ ⊑ᵂ⟨ W ⟩ ∀Xℕ) → (q′ : ∀Xℕ ⊑ᵂ⟨ W ⟩ (★ ⇒ `ℕ))
    → W ∣ [] ⊢ KL ⊑ KR ∶ q
  KL⊑KR q q′ =
    ⊑cast₀
      (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★ (κ⊑κ lit-$ (ι⊑ι base-ℕ))) q′)
      genK5-ty q

  -- the initial cast terms are RELATED (the sources are: the arguments
  -- by Λ⊑ with ∀X.X→ℕ ⊑ ★→ℕ, the functions by reflexivity)
  init : ∅ʷ ∣ [] ⊢ LK ⊑ RK ∶ ι⊑ι base-ℕ
  init =
    ·⊑·
      (ƛ⊑ƛ {pA = q∀} tf tf
        (·⊑· (ν⊑ν (x⊑x Zʷ) (ι⊑ι base-ℕ) νF-ty νF-ty
                (Wν , Wν-conv , cK⊑cK refl) ℕ⇒ℕ)
             (κ⊑κ lit-$ (ι⊑ι base-ℕ))))
      (KL⊑KR q∀ q★)

  -- state 1 on both sides (after both Betas): the ν redexes
  L₁ R₁ : Term
  L₁ = (ν `ℕ · KL ⟨ cK ⟩) · $ 5
  R₁ = (ν `ℕ · KR ⟨ cK ⟩) · $ 5

  L₁-state : nth (evalTerms 10 LK-⊢) 1 ≡ L₁
  L₁-state = refl

  R₁-state : nth (evalTerms 20 RK-⊢) 1 ≡ R₁
  R₁-state = refl

  νL-ty : NuTy empty `ℕ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = ν `ℕ · KL ⟨ cK ⟩})))

  νR-ty : NuTy empty `ℕ (` 0 ⇒ `ℕ) cK (`ℕ ⇒ `ℕ)
  νR-ty = proj₂ (proj₂ (ν-inv {Γ = []} (tc {Δ = empty} {M = ν `ℕ · KR ⟨ cK ⟩})))

  -- the ν pair is RELATED: ν⊑ν over KL ⊑ KR
  pre : ∅ʷ ∣ [] ⊢ L₁ ⊑ R₁ ∶ ι⊑ι base-ℕ
  pre =
    ·⊑· (ν⊑ν (KL⊑KR q∀ q★) (ι⊑ι base-ℕ) νL-ty νR-ty
           (Wν , Wν-conv , cK⊑cK refl) ℕ⇒ℕ)
        (κ⊑κ lit-$ (ι⊑ι base-ℕ))

  -- state 2 on both sides (after both TyBetas, α:=ℕ on each)
  I5 UF IF LB RB L₂ R₂ : Term
  I5 = ƛ ★ ∙ $ 5
  UF = I5 ⟪ unbind 0 0 ∷ []
          , tail (mid (tail (mid (id ★)) ↦ tail (mid (id `ℕ)))) ⟫
  IF = UF ⟨ ★∼X ∷ [] ∣ ((` 0) !) ↦ᵖ idᵖ `ℕ ⟩
  LB = (ƛ (` 0) ∙ $ 5) ⟪ Θ₀ , cK ⟫
  RB = IF ⟪ Θ₀ , cK ⟫
  L₂ = LB · $ 5
  R₂ = RB · $ 5

  L₂-state : nth (evalTerms 10 LK-⊢) 2 ≡ L₂
  L₂-state = refl

  R₂-state : nth (evalTerms 20 RK-⊢) 2 ≡ R₂
  R₂-state = refl

  ng-pF : NoGrant (((` 0) !) ↦ᵖ idᵖ `ℕ)
  ng-pF (gr-↦ _ ())

  -- inside the boundaries: the left's λx:X. 5 against the right's gen
  -- wrapper `X! → id(ℕ)`, which grants nothing.  Its premise needs
  -- X ⊑ ★ and its conclusion X ⊑ X (X joined): impossible at κ = [].
  pF : Coercion
  pF = ((` 0) !) ↦ᵖ idᵖ `ℕ

  -- the right's tag names a right name
  ct-pF : ∀ {Δ′ μ B A} → CastTy Δ′ μ pF B A → Δ′ ∋tv 0
  ct-pF (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-pF (cast-ty (⊢fun (⊢tag-var tv _ _) _) _) = tv

  noI : ∀ {Δᵢ Δ′ᵢ} {V : World Δᵢ Δ′ᵢ} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → κʷ V ≡ [] → ¬ (V ∣ γ ⊢ ƛ (` 0) ∙ $ 5 ⊑ IF ∶ q)
  noI {V = V} {q = q} eκ (⊑cast {κₚ = κₚ} {p = p} g _ d ct _)
    with ty-ƛ (ltyT d) | ct-src ct | ct-trg ct | ct-pF ct
  ... | B , refl , ⊢b | refl | refl | β , rh with ty-$ ⊢b
  ... | refl with plain-idx {V = record V { κʷ = κₚ }} nf-⇒ p
                | plain-idx {V = V} nf-⇒ q
  ... | p₀ | q₀ with dom⊑ p₀ | dom⊑ q₀
  ... | X⊑★ h | e =
    no★-right {V = record V { κʷ = κₚ }} (trans (cg-none ng-pF g) eκ) rh
      (subst (λ c → marksʷ (record V { κʷ = κₚ }) ∋ˡ c := X⊑★) (var⊑var e) h)

  -- a type variable is below no base type, and no base type below one
  no-var⊑ℕ : ∀ {μ X} → ¬ (μ ⊢ ` X ⊑ `ℕ)
  no-var⊑ℕ ()

  no-ℕ⊑var : ∀ {μ X} → ¬ (μ ⊢ `ℕ ⊑ ` X)
  no-ℕ⊑var ()

  -- the left's contractum against a right term N, in every world with
  -- no permission (the right side's context is arbitrary)
  NoRel : Term → Set
  NoRel N = ∀ {Δ′} {W : World ΔL Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₂ ⊑ N ∶ q)

  -- THE PAIR AFTER BOTH TyBetas IS RELATED IN NO WORLD WITHOUT
  -- PERMISSIONS (every top-level world): the matched route meets `noI`;
  -- the left-first route meets X ⊑ ℕ; the right-first route ℕ ⊑ X
  post-unrelated : NoRel R₂
  post-unrelated eκ (·⊑· dF d5) with ty-$ (ltyT d5) | ty-$ (rtyT d5)
  ... | refl | refl = noF eκ dF
    where
    noF : ∀ {Δ′} {W : World ΔL Δ′} {γ B B′}
        {q : (`ℕ ⇒ B) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ B′)}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LB ⊑ RB ∶ q)
    -- matched: the gen wrapper grants nothing
    noF eκ (⟪⟫⊑⟪⟫ I _ d _ _ _ _) = noI (trans (same-κ I) eκ) d
    -- left first: X ⊑ ℕ
    noF eκ (⟪⟫⊑ {Wᵢ = Wᵢ} {r = r} _ _ _ _ d _ _)
      with ty-ƛ (ltyT d)
    ... | _ , refl , _ = no-var⊑ℕ (dom⊑ (plain-idx {V = Wᵢ} nf-⇒ r))
    -- right first: ℕ ⊑ X
    noF eκ (⊑⟪⟫ {Wᵢ = Wᵢ} {r = r} _ _ _ d _ _)
      with ty-cast (rtyT d)
    ... | refl = no-ℕ⊑var (dom⊑ (plain-idx {V = Wᵢ} nf-⇒ r))

  -- the right's ν redex (0 catch-up steps): X ⊑ ℕ again
  pre-unrelated : NoRel R₁
  pre-unrelated eκ (·⊑· dF d5) with ty-$ (ltyT d5) | ty-$ (rtyT d5)
  ... | refl | refl = noF eκ dF
    where
    noF : ∀ {Δ′} {W : World ΔL Δ′} {γ B B′}
        {q : (`ℕ ⇒ B) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ B′)}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LB ⊑ ν `ℕ · KR ⟨ cK ⟩ ∶ q)
    noF eκ (⟪⟫⊑ {Wᵢ = Wᵢ} {r = r} _ _ _ _ d _ _)
      with ty-ƛ (ltyT d)
    ... | _ , refl , _ = no-var⊑ℕ (dom⊑ (plain-idx {V = Wᵢ} nf-⇒ r))

  -- peeling a right boundary, and a right cast that grants nothing
  peel⟪⟫ : ∀ {N Θ c} → NoRel N → NoRel (N ⟪ Θ , c ⟫)
  peel⟪⟫ h eκ (⊑⟪⟫ I _ _ d _ _) = h (trans (same-κ I) eκ) d

  peelCast : ∀ {N μ p} → NoGrant p → NoRel N → NoRel (N ⟨ μ ∣ p ⟩)
  peelCast ng h eκ (⊑cast g _ d _ _) = h (trans (cg-none ng g) eκ) d

  ng-idℕ : NoGrant (idᵖ `ℕ)
  ng-idℕ ()

  -- an application is related to no literal
  noApp5 : NoRel ($ 5)
  noApp5 _ ()

  -- the literal 5 against an X-tagged right value: ℕ ⊑ X
  no5tag : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′} {N μ}
    → ¬ (W ∣ γ ⊢ $ 5 ⊑ N ⟨ μ ∣ (` 0) ! ⟩ ∶ q)
  no5tag {W = W} (⊑cast {κₚ = κₚ} {p = p} _ _ d ct _)
    with ct-src ct | ty-$ (ltyT d)
  ... | refl | refl = no-ℕ⊑var (plain-idx {V = record W { κʷ = κₚ }} nf-ℕ p)

  -- ... also behind a right boundary (the Wrap dual [+X^α] … ⟨id(★)⟩)
  no5J : ∀ {Δ Δ′} {W : World Δ Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′} {N μ Θ c}
    → ¬ (W ∣ γ ⊢ $ 5 ⊑ (N ⟨ μ ∣ (` 0) ! ⟩) ⟪ Θ , c ⟫ ∶ q)
  no5J (⊑⟪⟫ _ _ _ d _ _) = no5tag d

  -- the function against a gen-wrapper application: ℕ ⊑ X at the domain
  noAppIF : ∀ {M} → NoRel (IF · M)
  noAppIF {W = W} eκ (·⊑· {pA = pA} dF d5)
    with ty-$ (ltyT d5) | ty-cast (rtyT dF)
  ... | refl | refl = no-ℕ⊑var (plain-idx {V = W} nf-ℕ pA)

  -- an argument that the literal 5 cannot face
  noAppArg : ∀ {L′ M′}
    → (∀ {Δ′} {W : World ΔL Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
         → ¬ (W ∣ γ ⊢ $ 5 ⊑ M′ ∶ q))
    → NoRel (L′ · M′)
  noAppArg h eκ (·⊑· _ d5) = h d5

  -- the right's states from its ν redex: R₁, R₂, … , 5
  R₁-⊢ : empty ∣ [] ⊢ R₁ ⦂ `ℕ
  R₁-⊢ = tc

  right-states : All NoRel (evalTerms 20 R₁-⊢)
  right-states =
    pre-unrelated
    ∷ post-unrelated
    ∷ peel⟪⟫ noAppIF
    ∷ peel⟪⟫ (peelCast ng-idℕ (noAppArg no5tag))
    ∷ peel⟪⟫ (peelCast ng-idℕ (peel⟪⟫ (noAppArg no5J)))
    ∷ peel⟪⟫ (peelCast ng-idℕ (peel⟪⟫ noApp5))
    ∷ peel⟪⟫ (peelCast ng-idℕ noApp5)
    ∷ peel⟪⟫ noApp5
    ∷ noApp5
    ∷ []

  -- the initial world is well formed (DynamicGradualGuaranteeProof's)
  no-pair : ∀ {α β} → Paired ∅ʷ α β → ∀ {X : Set} → X
  no-pair (inj₁ ())
  no-pair (inj₂ ())

  wf-∅ʷ : WfWorld ∅ʷ
  wf-∅ʷ = wf-world joint[] (λ π → no-pair π) (λ _ _ _ π _ → no-pair π)
    (λ _ _ _ π _ → no-pair π) [] AP.[] []

  -- the left's TyBeta from the related ν pair `pre`
  stepL : empty ⊢ L₁ -→ L₂ ∣ new `ℕ
  stepL = Runs.justStep refl

  -- SIM FAILS on P4k: the left's TyBeta from the related pair `pre` has
  -- no right catch-up (none of the right's states is related to L₂)
  not-sim : ¬ Sim
  not-sim sim with sim wf-empty wf-empty wf-∅ʷ refl refl pre stepL
  ... | N′ , r′ , W′ , ev , wf , q , d =
    Runs.all-reach {P = NoRel} 20 R₁-⊢ tt right-states r′ (⟿-κʷ ev refl) d

------------------------------------------------------------------------
-- P4h: the ν pair, the TyBeta pair (R1 rejects the left's crossΛ hide
-- under the gen wrapper's grant), ¬ Sim
------------------------------------------------------------------------

module P4h where
  open P4k using (nth; ℕ⇒ℕ; ng-idℕ; no-var⊑ℕ; no-ℕ⊑var; noApp5;
                  no5tag; no5J; wf-∅ʷ)

  ι : ∀ {μ} → μ ⊢ `ℕ ⊑ `ℕ
  ι = ι⊑ι base-ℕ

  q∀ : ∀ {μ} → μ ⊢ ∀X⇒X ⊑ ∀X⇒X
  q∀ = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

  q★ : ∀ {μ} → μ ⊢ ∀X⇒X ⊑ ★ ⇒ ★
  q★ = ∀⊑ nv-⇒ (∈-⇒ˡ ∈-var) (⇒⊑⇒ (X⊑★ here) (X⊑★ here))

  idℕ⇒ℕ : Conv
  idℕ⇒ℕ = tail (mid (tail (mid (id `ℕ)) ↦ tail (mid (id `ℕ))))

  -- the left's Λ after the argument's Beta: f became the crossΛ hide
  -- [−Y^β] (λy:ℕ. y) ⟨id(ℕ) → id(ℕ)⟩ (β the Λ's abstract rep. var)
  idℕ H₀ bodyL bodyR HLv HRv : Term
  idℕ   = ƛ `ℕ ∙ ` 0
  H₀    = idℕ ⟪ unbind 0 0 ∷ [] , idℕ⇒ℕ ⟫
  bodyL = (ƛ `ℕ ∙ ` 1) · (H₀ · $ 1)
  bodyR = (ƛ `ℕ ∙ ` 1) · (idℕ · $ 1)
  HLv   = Λ (ƛ (` 0) ∙ bodyL)
  HRv   = (ƛ ★ ∙ bodyR) ⟨ [] ∣ genI ⟩

  -- state 2 on both sides: the ν redexes
  L₂ R₂ : Term
  L₂ = (ν `ℕ · HLv ⟨ revX ⟩) · $ 5
  R₂ = (ν `ℕ · HRv ⟨ revX ⟩) · $ 5

  L₂-state : nth (evalTerms 20 LH-⊢) 2 ≡ L₂
  L₂-state = refl

  R₂-state : nth (evalTerms 30 RH-⊢) 2 ≡ R₂
  R₂-state = refl

  genI-ty : CastTy empty [] genI (★ ⇒ ★) ∀X⇒X
  genI-ty = proj₂ (proj₂ (cast-inv {Γ = []} (tc {Δ = empty} {M = HRv})))

  νL-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νL-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = ν `ℕ · HLv ⟨ revX ⟩})))

  νR-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νR-ty = proj₂ (proj₂ (ν-inv {Γ = []}
    (tc {Δ = empty} {M = ν `ℕ · HRv ⟨ revX ⟩})))

  -- the left's hide under the left-only Λ binder (W₀ ⊕ᴸ, no pair)
  ΔΛ ΔΛᵢ : Ctxᵗ
  ΔΛ  = underΛ empty
  ΔΛᵢ = (abstR ∷ []) ∣ []

  WΛ : World ΔΛ empty
  WΛ = ∅ʷ ⊕ᴸ

  WΛᵢ : World ΔΛᵢ empty
  WΛᵢ = world 0 []↪ []↪ [] [] [] []

  bH₀ : BdyTy ΔΛ (unbind 0 0 ∷ []) ΔΛᵢ (`ℕ ⇒ `ℕ) idℕ⇒ℕ (`ℕ ⇒ `ℕ)
  bH₀ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔΛ} {M = H₀}))))

  intH₀ : Interior WΛ (unbind 0 0 ∷ []) [] WΛᵢ
  intH₀ = record
    { int-left   = bdy-int bH₀
    ; int-right  = interior changes[]
    ; same-ϱᵍ    = refl
    ; same-ϱˡ    = refl
    ; same-κ     = refl
    ; join-cont  = λ { (_ , ()) _ _ _ }
    ; join-fresh = λ { () _ _ }
    }

  no-pairΛ : ∀ {α β} → Paired WΛᵢ α β → ∀ {X : Set} → X
  no-pairΛ (inj₁ ())
  no-pairΛ (inj₂ ())

  wf-WΛᵢ : WfWorld WΛᵢ
  wf-WΛᵢ = wf-world joint[] (λ π → no-pairΛ π) (λ _ _ _ π _ → no-pairΛ π)
    (λ _ _ _ π _ → no-pairΛ π) [] AP.[] []

  -- the left's hide against the right's λz:ℕ. z, one-sided: R1 holds,
  -- because the Λ's rep. var has no partner (a fresh left-only binder)
  H₀⊑ : ∀ {γ} → WΛ ∣ γ ⊢ H₀ ⊑ idℕ ∶ ⇒⊑⇒ ι ι
  H₀⊑ = ⟪⟫⊑ intH₀ (ok-unbind (λ { (inj₁ ()) ; (inj₂ ()) }) ∷ []) bc-plain
    wf-WΛᵢ (ƛ⊑ƛ {pA = ι} {pB = ι} tf tf (x⊑x Zʷ)) bH₀ (⇒⊑⇒ ι ι)

  bodyΛ⊑ : WΛ ∣ [] ⊢ ƛ (` 0) ∙ bodyL ⊑ ƛ ★ ∙ bodyR
    ∶ ⇒⊑⇒ (X⊑★ here) (X⊑★ here)
  bodyΛ⊑ =
    ƛ⊑ƛ {pA = X⊑★ here} tf wf-★
      (·⊑· {pA = ι}
        (ƛ⊑ƛ {pA = ι} {pB = X⊑★ here} tf tf (x⊑x (Sʷ Zʷ)))
        (·⊑· {pA = ι} H₀⊑ (κ⊑κ lit-$ ι)))

  HLv⊑HRv : ∅ʷ ∣ [] ⊢ HLv ⊑ HRv ∶ q∀
  HLv⊑HRv =
    ⊑cast₀ (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) liftᴸ-[] (V-simple S-ƛ)
              bodyΛ⊑ q★)
           genI-ty q∀

  -- the ν pair is RELATED
  pre : ∅ʷ ∣ [] ⊢ L₂ ⊑ R₂ ∶ ι⊑ι base-ℕ
  pre =
    ·⊑· (ν⊑ν HLv⊑HRv ι νL-ty νR-ty (Wν , Wν-conv , revX⊑revX refl)
           (⇒⊑⇒ ι ι))
        (κ⊑κ lit-$ ι)

  -- state 3 on both sides: after both TyBetas
  pI : Coercion
  pI = ((` 0) !) ↦ᵖ ((` 0) ？ 0)

  id★⇒★ : Conv
  id★⇒★ = tail (mid (tail (mid (id ★)) ↦ tail (mid (id ★))))

  UF IF LB RB L₃ R₃ : Term
  UF = (ƛ ★ ∙ bodyR) ⟪ unbind 0 0 ∷ [] , id★⇒★ ⟫
  IF = UF ⟨ ★∼X ∷ [] ∣ pI ⟩
  LB = (ƛ (` 0) ∙ bodyL) ⟪ Θ₀ , revX ⟫
  RB = IF ⟪ Θ₀ , revX ⟫
  L₃ = LB · $ 5
  R₃ = RB · $ 5

  L₃-state : nth (evalTerms 20 LH-⊢) 3 ≡ L₃
  L₃-state = refl

  R₃-state : nth (evalTerms 30 RH-⊢) 3 ≡ R₃
  R₃-state = refl

  -- a boundary keeps ϱ and κ
  paired-int : ∀ {Δᵢ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′ α β}
    → Interior W Θ Θ′ Wᵢ → Paired W α β → Paired Wᵢ α β
  paired-int I (inj₁ x) = inj₁ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (same-ϱᵍ I)) x)
  paired-int I (inj₂ x) = inj₂ (subst (λ ϱ → ϱ ∋ᵨ _ ⇔ _) (sym (same-ϱˡ I)) x)

  ≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  permit-self : ∀ β κ → permit β (β ∷ κ) ≡ X⊑★
  permit-self β κ rewrite ≡ᵇ-refl β = refl

  X⊑★≢X⊑X : _≡_ {A = VarImp} X⊑★ X⊑X → ∀ {A : Set} → A
  X⊑★≢X⊑X ()

  -- the right's gen wrapper tags and checks a right name
  ct-pI : ∀ {Δ′ μ B A} → CastTy Δ′ μ pI B A → Δ′ ∋tv 0
  ct-pI (cast-ty (⊢fun (⊢tag ()) _) _)
  ct-pI (cast-ty (⊢fun (⊢tag-var tv _ _) _) _) = tv

  -- BELOW THE GRANT: the left's crossΛ hide H₀ meets the right's λz:ℕ. z
  -- one-sided, and R1 needs its rep. var 0 to have no permitted
  -- partner; but 0 is paired with the granted β
  noBody : ∀ {Δ₁ Δ₁′} {V : World Δ₁ Δ₁′} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′} {β}
    → Paired V 0 β → permit β (κʷ V) ≡ X⊑★
    → ¬ (V ∣ γ ⊢ bodyL ⊑ bodyR ∶ q)
  noBody pr pm (·⊑· _ (·⊑· (⟪⟫⊑ _ (ok-unbind u ∷ []) _ _ _ _ _) _)) =
    X⊑★≢X⊑X (trans (sym pm) (u pr))

  noHide : ∀ {Δ₁ Δ₁′} {V : World Δ₁ Δ₁′} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′} {β}
    → Paired V 0 β → permit β (κʷ V) ≡ X⊑★
    → ¬ (V ∣ γ ⊢ ƛ (` 0) ∙ bodyL ⊑ UF ∶ q)
  noHide pr pm (⊑⟪⟫ I _ _ (ƛ⊑ƛ _ _ d) _ _) =
    noBody (paired-int I pr) (trans (cong (permit _) (same-κ I)) pm) d

  -- INSIDE THE MATCHED +X: without a grant X ⊑ ★ fails at the joined X;
  -- with the grant (the wrapper's X?), R1 fails at the hide
  noI : ∀ {Δᵢ Δ′ᵢ} {V : World Δᵢ Δ′ᵢ} {γ A A′} {q : A ⊑ᵂ⟨ V ⟩ A′}
    → WfWorld V → names Δᵢ ∋ˡ 0 := 0 → κʷ V ≡ []
    → ¬ (V ∣ γ ⊢ ƛ (` 0) ∙ bodyL ⊑ IF ∶ q)
  noI {V = V} {q = q} wf lh eκ (⊑cast {κₚ = κₚ} {p = p} g _ d ct _)
    with ty-ƛ (ltyT d) | ct-src ct | ct-trg ct | ct-pI ct
  ... | B , refl , _ | refl | refl | β₀ , rh
    with dom⊑ (plain-idx {V = V} nf-⇒ q)
  ... | e with g
  ...   | no-grant with dom⊑ (plain-idx {V = V} nf-⇒ p)
  ...     | X⊑★ h = no★-right {V = V} eκ rh
      (subst (λ c → marksʷ V ∋ˡ c := X⊑★) (var⊑var e) h)
  noI {V = V} wf lh eκ (⊑cast {κₚ = _} g _ d ct _)
      | B , refl , _ | refl | refl | β₀ , rh | e
      | grant {β = β} (gr-↦ _ (gr-? h)) =
    noHide {V = record V { κʷ = β ∷ κʷ V }}
      (joint-pair (wf-joint wf) lh h (var⊑var e)) (permit-self β (κʷ V)) d

  NoRel : Term → Set
  NoRel N = ∀ {Δ′} {W : World ΔL Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ L₃ ⊑ N ∶ q)

  NoRelAny : Term → Set
  NoRelAny N = ∀ {Δ′} {W : World ΔL Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ L₃ ⊑ N ∶ q)

  any→ : ∀ {N} → NoRelAny N → NoRel N
  any→ h _ = h

  -- THE PAIR AFTER BOTH TyBetas IS RELATED IN NO WORLD WITHOUT
  -- PERMISSIONS: matched, the wrapper either grants nothing (X ⊑ ★
  -- fails at the joined X) or grants αᴿ (then R1 rejects the left's
  -- crossΛ hide [−X^α] (λy:ℕ. y) ⟨…⟩, whose α is paired with αᴿ);
  -- left first X ⊑ ℕ; right first ℕ ⊑ X
  post-unrelated : NoRel R₃
  post-unrelated eκ (·⊑· dF d5) with ty-$ (ltyT d5) | ty-$ (rtyT d5)
  ... | refl | refl = noF eκ dF
    where
    noF : ∀ {Δ′} {W : World ΔL Δ′} {γ B B′}
        {q : (`ℕ ⇒ B) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ B′)}
      → κʷ W ≡ [] → ¬ (W ∣ γ ⊢ LB ⊑ RB ∶ q)
    noF eκ (⟪⟫⊑⟪⟫ I wf d b _ _ _)
      with interior-functional (int-left I) int₀
    ... | refl = noI wf here (trans (same-κ I) eκ) d
    noF eκ (⟪⟫⊑ {Wᵢ = Wᵢ} {r = r} _ _ _ _ d _ _)
      with ty-ƛ (ltyT d)
    ... | _ , refl , _ = no-var⊑ℕ (dom⊑ (plain-idx {V = Wᵢ} nf-⇒ r))
    noF eκ (⊑⟪⟫ {Wᵢ = Wᵢ} {r = r} _ _ _ d _ _)
      with ty-cast (rtyT d)
    ... | refl = no-ℕ⊑var (dom⊑ (plain-idx {V = Wᵢ} nf-⇒ r))

  -- the right's ν redex (0 catch-up steps): X ⊑ ℕ
  pre-unrelated : NoRelAny R₂
  pre-unrelated (·⊑· dF d5) with ty-$ (ltyT d5) | ty-$ (rtyT d5)
  ... | refl | refl = noF dF
    where
    noF : ∀ {Δ′} {W : World ΔL Δ′} {γ B B′}
        {q : (`ℕ ⇒ B) ⊑ᵂ⟨ W ⟩ (`ℕ ⇒ B′)}
      → ¬ (W ∣ γ ⊢ LB ⊑ ν `ℕ · HRv ⟨ revX ⟩ ∶ q)
    noF (⟪⟫⊑ {Wᵢ = Wᵢ} {r = r} _ _ _ _ d _ _)
      with ty-ƛ (ltyT d)
    ... | _ , refl , _ = no-var⊑ℕ (dom⊑ (plain-idx {V = Wᵢ} nf-⇒ r))

  -- peeling right boundaries and right casts (at any permissions)
  peel⟪⟫ : ∀ {N Θ c} → NoRelAny N → NoRelAny (N ⟪ Θ , c ⟫)
  peel⟪⟫ h (⊑⟪⟫ _ _ _ d _ _) = h d

  peelCast : ∀ {N μ p} → NoRelAny N → NoRelAny (N ⟨ μ ∣ p ⟩)
  peelCast h (⊑cast _ _ d _ _) = h d

  noApp5′ : NoRelAny ($ 5)
  noApp5′ ()

  noAppArg : ∀ {L′ M′}
    → (∀ {Δ′} {W : World ΔL Δ′} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
         → ¬ (W ∣ γ ⊢ $ 5 ⊑ M′ ∶ q))
    → NoRelAny (L′ · M′)
  noAppArg h (·⊑· _ d5) = h d5

  -- the function against the gen wrapper: ℕ ⊑ X at the domain
  noAppIF : ∀ {M} → NoRelAny (IF · M)
  noAppIF {W = W} (·⊑· {pA = pA} dF d5)
    with ty-$ (ltyT d5) | ty-cast (rtyT dF)
  ... | refl | refl = no-ℕ⊑var (plain-idx {V = W} nf-ℕ pA)

  R₂-⊢ : empty ∣ [] ⊢ R₂ ⦂ `ℕ
  R₂-⊢ = tc

  right-states : All NoRel (evalTerms 30 R₂-⊢)
  right-states =
    any→ pre-unrelated
    ∷ post-unrelated
    ∷ any→ (peel⟪⟫ noAppIF)
    ∷ any→ (peel⟪⟫ (peelCast (noAppArg no5tag)))
    ∷ any→ (peel⟪⟫ (peelCast (peel⟪⟫ (noAppArg no5J))))
    ∷ any→ (peel⟪⟫ (peelCast (peel⟪⟫ (noAppArg (λ ())))))
    ∷ any→ (peel⟪⟫ (peelCast (peel⟪⟫ (noAppArg (λ ())))))
    ∷ any→ (peel⟪⟫ (peelCast (peel⟪⟫ (peel⟪⟫ (peelCast (peel⟪⟫ noApp5′))))))
    ∷ any→ (peel⟪⟫ (peelCast (peel⟪⟫ (peelCast (peel⟪⟫ noApp5′)))))
    ∷ any→ (peel⟪⟫ (peelCast (peelCast (peel⟪⟫ (peel⟪⟫ noApp5′)))))
    ∷ any→ (peel⟪⟫ (peelCast (peelCast (peel⟪⟫ noApp5′))))
    ∷ any→ (peel⟪⟫ (peel⟪⟫ noApp5′))
    ∷ any→ (peel⟪⟫ noApp5′)
    ∷ any→ noApp5′
    ∷ []

  stepL : empty ⊢ L₂ -→ L₃ ∣ new `ℕ
  stepL = Runs.justStep refl

  -- SIM FAILS on P4h, from RELATED sources: the left's TyBeta from the
  -- related pair `pre` has no right catch-up
  not-sim : ¬ Sim
  not-sim sim with sim wf-empty wf-empty wf-∅ʷ refl refl pre stepL
  ... | N′ , r′ , W′ , ev , wf , q , d =
    Runs.all-reach {P = NoRel} 30 R₂-⊢ tt right-states r′ (⟿-κʷ ev refl) d

  -- the initial cast terms are RELATED (sources: the arguments by Λ⊑,
  -- ∀X.X→X ⊑ ★→★, under λf; the functions by reflexivity)
  νb-ty : NuTy empty `ℕ (` 0 ⇒ ` 0) revX (`ℕ ⇒ `ℕ)
  νb-ty = proj₂ (proj₂ (ν-inv {Γ = ∀X⇒X ∷ []}
    (tc {Δ = empty} {Γ = ∀X⇒X ∷ []} {M = ν `ℕ · ` 0 ⟨ revX ⟩})))

  bodyf : ∅ʷ ∣ ctx-imp (`ℕ ⇒ `ℕ) (`ℕ ⇒ `ℕ) (⇒⊑⇒ ι ι) ∷ []
    ⊢ Λ (ƛ (` 0) ∙ bodyH) ⊑ (ƛ ★ ∙ bodyH) ⟨ [] ∣ genI ⟩ ∶ q∀
  bodyf =
    ⊑cast₀
      (Λ⊑ claim-fresh nv-⇒ (∈-⇒ˡ ∈-var) (liftᴸ-∷ {p′ = ⇒⊑⇒ ι ι} liftᴸ-[])
        (V-simple S-ƛ)
        (ƛ⊑ƛ {pA = X⊑★ here} tf wf-★
          (·⊑· {pA = ι}
            (ƛ⊑ƛ {pA = ι} {pB = X⊑★ here} tf tf (x⊑x (Sʷ Zʷ)))
            (·⊑· {pA = ι} (x⊑x (Sʷ Zʷ)) (κ⊑κ lit-$ ι))))
        q★)
      genI-ty q∀

  argH : ∅ʷ ∣ [] ⊢ HL ⊑ HR ∶ q∀
  argH = ·⊑· (ƛ⊑ƛ {pA = ⇒⊑⇒ ι ι} tf tf bodyf)
             (ƛ⊑ƛ {pA = ι} {pB = ι} tf tf (x⊑x Zʷ))

  init : ∅ʷ ∣ [] ⊢ LH ⊑ RH ∶ ι⊑ι base-ℕ
  init =
    ·⊑·
      (ƛ⊑ƛ {pA = q∀} tf tf
        (·⊑· (ν⊑ν (x⊑x Zʷ) ι νb-ty νb-ty (Wν , Wν-conv , revX⊑revX refl)
                (⇒⊑⇒ ι ι))
             (κ⊑κ lit-$ ι)))
      argH

------------------------------------------------------------------------
-- Interfaces (design.md §12.2.1): the two ∀ bodies with the bound
-- name at X⊑X (the `∀⊑∀` that matched ν's need)
------------------------------------------------------------------------

module Interfaces where
  -- C1, C2, C3, C4, C4g: ∀X.X→X against ∀X.X→★
  iface-C1 : ∀ {μ} → ¬ (X⊑X ∷ μ ⊢ ` 0 ⇒ ` 0 ⊑ ` 0 ⇒ ★)
  iface-C1 (⇒⊑⇒ _ (X⊑★ ()))
  iface-C1 (⇒⊑⇒ _ (ι⊑★ ()))

  -- C5: ∀Y.Y→Y against ∀Y.★→Y
  iface-C5 : ∀ {μ} → ¬ (X⊑X ∷ μ ⊢ ` 0 ⇒ ` 0 ⊑ ★ ⇒ ` 0)
  iface-C5 (⇒⊑⇒ (X⊑★ ()) _)
  iface-C5 (⇒⊑⇒ (ι⊑★ ()) _)

  -- P4, K, P4h (∀X.X→X), P4k and G0 (∀X.X→ℕ): the interface holds
  iface-P4 : ∀ {μ} → X⊑X ∷ μ ⊢ ` 0 ⇒ ` 0 ⊑ ` 0 ⇒ ` 0
  iface-P4 = ⇒⊑⇒ X⊑X X⊑X

  iface-P4k : ∀ {μ} → X⊑X ∷ μ ⊢ ` 0 ⇒ `ℕ ⊑ ` 0 ⇒ `ℕ
  iface-P4k = ⇒⊑⇒ X⊑X (ι⊑ι base-ℕ)

  -- G2 (two names, both matched): ∀X.∀Y.X→Y→X
  iface-G2 : ∀ {μ} → X⊑X ∷ X⊑X ∷ μ ⊢ ` 1 ⇒ (` 0 ⇒ ` 1) ⊑ ` 1 ⇒ (` 0 ⇒ ` 1)
  iface-G2 = ⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)

  -- C5's late states (L state 3, R state 5) have the outer boundaries
  -- [+X^α] … ⟨+X⟩ on both sides, interior type X: the interface (X, X)
  -- fits them and is well formed, although C5's ν pair had (Y→Y, ★→Y)
  iface-fake : ∀ {μ} → X⊑X ∷ μ ⊢ ` 0 ⊑ ` 0
  iface-fake = X⊑X

  -- the index of ν⊑ν need not be ∀⊑∀ (the source rule []⊑[]ᴳ requires
  -- it): ∀X.∀Y.X→Y→X ⊑ ∀Y.★→Y→★ by ∀⊑ (H1's first ascription)
  ν-index-∀⊑ : [] ⊢ `∀ (`∀ (` 1 ⇒ (` 0 ⇒ ` 1))) ⊑ `∀ (★ ⇒ (` 0 ⇒ ★))
  ν-index-∀⊑ =
    ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
      (∀⊑∀ (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))

------------------------------------------------------------------------
-- A LEFT-ONLY TyBeta drops ∀⊑'s side condition `X ∈ C`.
-- Left  ν X:=ℕ. ((ΛX. 5) X) ⟨id(ℕ)⟩    (source: (ΛX. 5) [ℕ])
-- Right 5                              (source: 5)
-- The sources are unrelated (Λ⊑ needs X ∈ ℕ), and so is the redex pair
-- (`∀ℕ ⊑ ℕ` is empty).  One left TyBeta later the pair is related.
------------------------------------------------------------------------

module LeftOnly where
  open import examples.TermImprecisionExamples
    using (W₂; Wᵢ₂; Wᵢ₂-int; Wᵢ₂-wf)

  L₀ L₁ : Term
  L₀ = ν `ℕ · Λ ($ 5) ⟨ ⌞ id `ℕ ⌟ ⟩
  L₁ = $ 5 ⟪ Θ₀ , ⌞ id `ℕ ⌟ ⟫

  L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ `ℕ
  L₀-⊢ = tc

  step : empty ⊢ L₀ -→ L₁ ∣ new `ℕ
  step = Runs.justStep refl

  no∀ℕ : ∀ {μ} → ¬ (μ ⊢ `∀ `ℕ ⊑ `ℕ)
  no∀ℕ (∀⊑ _ () _)

  redex-unrelated : ∀ {W : World empty empty} {γ A A′} {q : A ⊑ᵂ⟨ W ⟩ A′}
    → ¬ (W ∣ γ ⊢ L₀ ⊑ $ 5 ∶ q)
  redex-unrelated (ν⊑ {r = r} d _ _ _) with ty-Λ (ltyT d) | ty-$ (rtyT d)
  ... | _ , refl , ⊢5 | refl with ty-$ ⊢5
  ... | refl = no∀ℕ r

  bL₁ : BdyTy ΔL Θ₀ ΔLᵢ `ℕ ⌞ id `ℕ ⌟ `ℕ
  bL₁ = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} (tc {Δ = ΔL} {M = L₁}))))

  contractum : W₂ ∣ [] ⊢ L₁ ⊑ $ 5 ∶ ι⊑ι base-ℕ
  contractum = ⟪⟫⊑ Wᵢ₂-int (ok-bind ∷ []) bc-plain Wᵢ₂-wf
    (κ⊑κ lit-$ (ι⊑ι base-ℕ)) bL₁ (ι⊑ι base-ℕ)

module examples.TermImprecisionH1Examples where

-- File Charter:
--   * REGRESSION EXAMPLE for design.md D29 (claim-rep): the DGG part 1
--     counterexample H1 of proof/DGG/notes/PushOrder.md (there H1′).
--     The left keeps ΛX.ΛY.λx:X.λy:Y.x polymorphic; the right
--     instantiates it at ★ TWICE, through two casts
--     `∀X.∀Y.X→Y→X ⇒ ∀Y.★→Y→★ ⇒ ★→★→★`.  The second Inst runs InstX
--     through the first Inst boundary, so the right's final value nests
--     `[+Y^β]` OUTSIDE `[+X^α]`, with a cast between them (no Merge).
--     The left's binders are peeled X first; the right's boundaries
--     are entered Y first.  With openings alone (D27's pending names;
--     D31's slots without a skip) the pair is unrelated in every world
--     (PushOrder `NoD27.unrelated`); with claim-rep the left's ΛX claims
--     α at the top, and `+X^α` rejoins it inside `+Y^β`.
--       src-1, src-2      the source ascriptions are related
--       init              the initial pair, at ∅ʷ (no claim)
--       st2               the right's state 2: P3's opening and join
--       final             THE FINAL PAIR: ΛX claims α (claim-rep), +Y^β
--                         opens the left's next ∀ at Y, +X^α rejoins X
--                         and carries the slot, ΛY joins Y (design.md
--                         D31)
--       final-no-push     the same pair with no opening at all: both left
--                         binders claim (X ↦ α, Y ↦ β), both right
--                         boundaries rejoin
--       dgg1-H1           DGG part 1 on the initial pair: the right's
--                         run reaches its value R₄, related to the left
--                         value
--     The right's run is pinned to `evalTerms` by `refl`.
--   * PERMISSIONS (design.md D28, D31): no world has a permission.  The
--     claimed X is left-only (X⊑★) until `+X^α` rejoins it; from there
--     it is α's permission, X⊑X, and the bodies need only X ⊑ X, Y ⊑ Y.
--   * Ported from proof/DGG/notes/PushOrder.agda §3-§5 (`Ex`, `Pos`,
--     `FinalR`) to the real relation; no notes module is imported.
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; head; drop; length)
open import Data.Maybe using (just)
open import Data.Product
  using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; done; _then_)
open import Imprecision
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.Evolve using (applyˢ; allocs)
open import examples.TypeCheck using (tc; tf)
open import examples.Eval using (evalTerms; step; StepResult)

------------------------------------------------------------------------
-- 1. Sources, initial cast terms, runs
------------------------------------------------------------------------
-- Sources (cast insertion is the compilation; an ascription at the
-- term's own type inserts no cast):
--   L:  (ΛX.ΛY.λx:X.λy:Y.x  : ∀X.∀Y.X→Y→X)
--   R:  ((ΛX.ΛY.λx:X.λy:Y.x : ∀Y.★→Y→★) : ★→★→★)
-- The sources are RELATED: the same term, and the ascriptions are
-- related, ∀X.∀Y.X→Y→X ⊑ ∀Y.★→Y→★ ⊑ ★→★→★ (`src-1`, `src-2`).

K2 KY : Ty
K2 = `∀ (`∀ (` 1 ⇒ (` 0 ⇒ ` 1)))   -- ∀X.∀Y.X→Y→X
KY = `∀ (★ ⇒ (` 0 ⇒ ★))              -- ∀Y.★→Y→★

src-1 : [] ⊢ K2 ⊑ KY
src-1 = ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
          (∀⊑∀ (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))

src-2 : [] ⊢ KY ⊑ (★ ⇒ (★ ⇒ ★))
src-2 = ∀⊑ nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var))
          (⇒⊑⇒ ★⊑★ (⇒⊑⇒ (X⊑★ here) ★⊑★))

NL L1 KL : Term
NL = ƛ (` 1) ∙ (ƛ (` 0) ∙ ` 1)        -- λx:X.λy:Y.x
L1 = Λ NL
KL = Λ L1

vNL : Value NL
vNL = V-simple S-ƛ

vL1 : Value L1
vL1 = V-simple (S-Λ vNL)

vKL : Value KL
vKL = V-simple (S-Λ vL1)

-- the two casts: ∀X.∀Y.X→Y→X ⇒ ∀Y.★→Y→★ ⇒ ★→★→★
instX∀ instY ci cf : Coercion
instX∀ = instᵖ (∀ᵖ (((` 1) ？ 0) ↦ᵖ (idᵖ (` 0) ↦ᵖ ((` 1) !))))
instY  = instᵖ (idᵖ ★ ↦ᵖ (((` 0) ？ 0) ↦ᵖ idᵖ ★))
ci     = idᵖ ★ ↦ᵖ (idᵖ (` 0) ↦ᵖ idᵖ ★)
cf     = idᵖ ★ ↦ᵖ (idᵖ ★ ↦ᵖ idᵖ ★)

-- the initial cast terms (rendered):
--   L₀ = (ΛX. (ΛY. (λx:X. (λy:Y. x))))
--   R₀ = (ΛX. (ΛY. (λx:X. (λy:Y. x))))
--          ⟨inst Z. (∀X′. (Z?ℓ0 → (id(X′) → Z!)))⟩^[]
--          ⟨inst Y′. (id(★) → (Y′?ℓ0 → id(★)))⟩^[]
L₀ R₀ : Term
L₀ = KL
R₀ = (KL ⟨ [] ∣ instX∀ ⟩) ⟨ [] ∣ instY ⟩

L₀-⊢ : empty ∣ [] ⊢ L₀ ⦂ K2
L₀-⊢ = tc

R₀-⊢ : empty ∣ [] ⊢ R₀ ⦂ ★ ⇒ (★ ⇒ ★)
R₀-⊢ = tc

-- the right's states 2 and 4 (state 4 is its final value):
--   R₂ = ([+X^α] (ΛY. λx:X. λy:Y. x) ⟨∀Y. (−X → (id(Y) → +X))⟩)
--          ⟨∀Z. (id(★) → (id(Z) → id(★)))⟩^[]
--          ⟨inst X′. (id(★) → (X′?ℓ0 → id(★)))⟩^[]
--   R₄ = ([+Y^β] ([+X^α] (λx:X. λy:Y. x) ⟨−X → (id(Y) → +X)⟩)
--                 ⟨id(★) → (id(Y) → id(★))⟩^[Y:X∼X]
--               ⟨id(★) → (−Y → id(★))⟩)
--          ⟨id(★) → (id(★) → id(★))⟩^[]
ΘA ΘY ΘX : Boundary
ΘA = bind 0 0 ∷ []      -- the first Inst boundary +X^α
ΘY = bind 0 0 ∷ []      -- the second Inst boundary +Y^β (outer)
ΘX = bind 1 1 ∷ []      -- +X^α after InstX moved it inside

cA cX cY : Conv
cA = tail (mid (`∀ (tail (mid (tail (seal 1)
       ↦ tail (mid (tail (mid (id (` 0))) ↦ unseal 1)))))))
cX = tail (mid (tail (seal 1)
       ↦ tail (mid (tail (mid (id (` 0))) ↦ unseal 1))))
cY = tail (mid (tail (mid (id ★))
       ↦ tail (mid (tail (seal 0) ↦ tail (mid (id ★))))))

BA R₂ BX CI BY R₄ : Term
BA = L1 ⟪ ΘA , cA ⟫
R₂ = (BA ⟨ [] ∣ ∀ᵖ ci ⟩) ⟨ [] ∣ instY ⟩
BX = NL ⟪ ΘX , cX ⟫
CI = BX ⟨ X∼X ∷ [] ∣ ci ⟩
BY = CI ⟪ ΘY , cY ⟫
R₄ = BY ⟨ [] ∣ cf ⟩

R₂-state : head (drop 2 (evalTerms 30 R₀-⊢)) ≡ just R₂
R₂-state = refl

R₄-state : head (drop 4 (evalTerms 30 R₀-⊢)) ≡ just R₄
R₄-state = refl

-- the run stops at R₄: it is a value, the right's final value
R₄-final : length (evalTerms 30 R₀-⊢) ≡ 5
R₄-final = refl

-- the earlier states are no values (an `inst` cast is not inert;
-- states 1 and 3 are ν-terms, and `Value` has no ν case)
R₀-nv : ¬ Value R₀
R₀-nv (V-simple (S-cast _ ()))

R₂-nv : ¬ Value R₂
R₂-nv (V-simple (S-cast _ ()))

vR₄ : Value R₄
vR₄ = V-simple (S-cast (V-⟪⟫ (S-cast (V-⟪⟫ S-ƛ I-fun) I-↦) I-fun) I-↦)

-- the typing bundles, read off `tc` derivations
ΔT1 ΔT2 ΔA ΔY ΔXY Δ1 Δ2 : Ctxᵗ
ΔT1 = allocate ★ empty                          -- after the 1st TyBeta
ΔT2 = allocate ★ ΔT1                            -- after the 2nd TyBeta
ΔA  = (bindR ★ ∷ []) ∣ (0 ∷ [])                -- inside +X^α (state 2)
ΔY  = (bindR ★ ∷ bindR ★ ∷ []) ∣ (0 ∷ [])      -- inside +Y^β
ΔXY = (bindR ★ ∷ bindR ★ ∷ []) ∣ (0 ∷ 1 ∷ [])  -- inside +Y^β, +X^α
Δ1  = underΛ empty                              -- left, under ΛX
Δ2  = underΛ Δ1                                 -- left, under ΛX.ΛY

R₂-⊢ : ΔT1 ∣ [] ⊢ R₂ ⦂ ★ ⇒ (★ ⇒ ★)
R₂-⊢ = tc

R₄-⊢ : ΔT2 ∣ [] ⊢ R₄ ⦂ ★ ⇒ (★ ⇒ ★)
R₄-⊢ = tc

instX∀-ty : CastTy empty [] instX∀ K2 KY
instX∀-ty = proj₂ (proj₂ (cast-inv {Γ = []}
  (proj₁ (proj₂ (cast-inv {Γ = []} R₀-⊢)))))

instY-ty₀ : CastTy empty [] instY KY (★ ⇒ (★ ⇒ ★))
instY-ty₀ = proj₂ (proj₂ (cast-inv {Γ = []} R₀-⊢))

instY-ty₂ : CastTy ΔT1 [] instY KY (★ ⇒ (★ ⇒ ★))
instY-ty₂ = proj₂ (proj₂ (cast-inv {Γ = []} R₂-⊢))

∀ci-ty : CastTy ΔT1 [] (∀ᵖ ci) KY KY
∀ci-ty = proj₂ (proj₂ (cast-inv {Γ = []}
  (proj₁ (proj₂ (cast-inv {Γ = []} R₂-⊢)))))

bA : BdyTy ΔT1 ΘA ΔA (`∀ (` 1 ⇒ (` 0 ⇒ ` 1))) cA KY
bA = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
  (proj₁ (proj₂ (cast-inv {Γ = []}
    (proj₁ (proj₂ (cast-inv {Γ = []} R₂-⊢)))))))))

⊢BY : ΔT2 ∣ [] ⊢ BY ⦂ ★ ⇒ (★ ⇒ ★)
⊢BY = proj₁ (proj₂ (cast-inv {Γ = []} R₄-⊢))

cf-ty : CastTy ΔT2 [] cf (★ ⇒ (★ ⇒ ★)) (★ ⇒ (★ ⇒ ★))
cf-ty = proj₂ (proj₂ (cast-inv {Γ = []} R₄-⊢))

bY : BdyTy ΔT2 ΘY ΔY (★ ⇒ (` 0 ⇒ ★)) cY (★ ⇒ (★ ⇒ ★))
bY = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} ⊢BY)))

⊢CI : ΔY ∣ [] ⊢ CI ⦂ ★ ⇒ (` 0 ⇒ ★)
⊢CI = proj₁ (proj₂ (proj₂ (⟪⟫-inv {Γ = []} ⊢BY)))

ci-ty : CastTy ΔY (X∼X ∷ []) ci (★ ⇒ (` 0 ⇒ ★)) (★ ⇒ (` 0 ⇒ ★))
ci-ty = proj₂ (proj₂ (cast-inv {Γ = []} ⊢CI))

bX : BdyTy ΔY ΘX ΔXY (` 1 ⇒ (` 0 ⇒ ` 1)) cX (★ ⇒ (` 0 ⇒ ★))
bX = proj₂ (proj₂ (proj₂ (⟪⟫-inv {Γ = []}
  (proj₁ (proj₂ (cast-inv {Γ = []} ⊢CI))))))

-- indices
q-top : ∀ {μ} → μ ⊢ K2 ⊑ (★ ⇒ (★ ⇒ ★))
q-top = ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
  (∀⊑ nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var))
    (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here)))))

q-src1 : ∀ {μ} → μ ⊢ K2 ⊑ KY
q-src1 = ∀⊑ nv-∀ (∈-∀ (∈-⇒ˡ ∈-var))
          (∀⊑∀ (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))))

idK : ∀ {μ} → μ ⊢ `∀ (` 1 ⇒ (` 0 ⇒ ` 1)) ⊑ `∀ (` 1 ⇒ (` 0 ⇒ ` 1))
idK = ∀⊑∀ (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X))

------------------------------------------------------------------------
-- 2. The initial pair and state 2 (no claim-rep needed)
------------------------------------------------------------------------

-- the initial pair, at ∅ʷ: ⊑cast twice, then KL ⊑ KL by Λ⊑Λ twice
init : ∅ʷ ∣ [] ⊢ L₀ ⊑ R₀ ∶ q-top
init =
  ⊑cast
    (⊑cast
      (Λ⊑Λ lift-[] vL1 vL1
        (Λ⊑Λ lift-[] vNL vNL
          (ƛ⊑ƛ {pA = X⊑X} tf tf
            (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
          idK)
        (∀⊑∀ idK))
      instX∀-ty q-src1)
    instY-ty₀ q-top

-- state 2: the opening and join of P3 (the right's first Inst boundary
-- +X^α opens the left's ∀ at X, the left's ΛX joins it), then Λ⊑Λ for
-- Y
W₂ : World empty ΔT1
W₂ = world⁰ 0 []↪ []↪ [] []

WA : World empty ΔA
WA = world⁰ 1 (skip []↪) (keep []↪) [] []

intA : Interior W₂ [] ΘA WA
intA = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , here) fresh[] ins-here))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , ()) _ _ _ }
  ; join-fresh = λ { () _ _ }
  }

wfA : WfWorld WA
wfA = wf-world (right-only joint[]) (λ { (inj₁ ()) ; (inj₂ ()) })
  (λ { (_ , ()) _ _ _ _ }) (λ { _ _ _ (inj₁ ()) _ ; _ _ _ (inj₂ ()) _ })
  []

-- X's opening is well formed (design.md D31)
okA : All (SlotOK WA) (opn 0 ∷ [])
okA = (0 , here , r-here , (λ { (_ , ()) }) , (λ { (_ , ()) })) ∷ []

st2 : W₂ ∣ [] ⊢ L₀ ⊑ R₂ ∶ q-top
st2 =
  ⊑cast
    (⊑cast
      (⊑⟪⟫ intA (push ca-[] f-end (ns-opn refl ∷ []) (inj₂ vKL)) okA
        ([] ∷ []) [] wfA idK
        (Λ⊑ (b-join (join1 join-here here r-here))
          nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
          (Λ⊑Λ lift-[] vNL vNL
            (ƛ⊑ƛ {pA = X⊑X} tf tf
              (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
            idK)
          idK)
        bA q-src1)
      ∀ci-ty q-src1)
    instY-ty₂ q-top

------------------------------------------------------------------------
-- 3. THE FINAL PAIR (L₀, R₄), related by claim-rep (design.md D29).
-- The left's ΛX claims α (rep. var 1 of ΔT2, no right name yet) at the
-- top; +Y^β opens the left's next ∀ at Y (design.md D31); the inner
-- +X^α binds X to α, so its fresh X REJOINS the left X
-- (Interior.join-fresh, D25) and carries the slot; the left's ΛY joins
-- Y; then the bodies at X ⊑ X, Y ⊑ Y.
------------------------------------------------------------------------

W₄ : World empty ΔT2
W₄ = world⁰ 0 []↪ []↪ [] []

-- after the claim: left X at center 0 (left-only, X⊑★), paired with α
W₄₁ : World Δ1 ΔT2
W₄₁ = W₄ ⊕ᴸ⇔ 1

-- inside +Y^β: Y at center 0, opened; left X at center 1
WY : World Δ1 ΔY
WY = world⁰ 2 (skip (keep []↪)) (keep (skip []↪)) [] ((0 , 1) ∷ [])

-- inside +X^α: X rejoins the left X at center 1; Y still opened
WX : World Δ1 ΔXY
WX = world⁰ 2 (skip (keep []↪)) (keep (keep []↪)) [] ((0 , 1) ∷ [])

claimX : Bind W₄ [] W₄₁ []
claimX = b-rep (r-there r-here) (λ { (_ , ()) }) (λ { (_ , ()) })

intY : Interior W₄₁ [] ΘY WY
intY = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , here) fresh[] ins-here))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
  ; join-fresh = λ { here here _ → (λ ()) , (λ { (inj₁ ())
                                             ; (inj₂ (there⇔ ())) })
                   ; here (there ()) _ ; (there ()) _ _ }
  }

intX : Interior WY [] ΘX WX
intX = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , there here)
                      (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { (_ , here) (_ , here) refl refl →
                       (λ ()) , (λ ())
                   ; (_ , here) (_ , there here) _ ()
                   ; (_ , here) (_ , there (there ())) _ _
                   ; (_ , there ()) _ _ _ }
  ; join-fresh = λ { here (there here) _ →
                       (λ _ → inj₂ here⇔) , (λ _ → refl)
                   ; here here (inj₁ ()) ; here here (inj₂ ())
                   ; here (there (there ())) _
                   ; (there ()) _ _ }
  }

wfY : WfWorld WY
wfY = wf-world (right-only (left-only joint[]))
  (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here (r-there r-here)
     ; (inj₂ (there⇔ ())) })
  (λ { (_ , here) (_ , here) _ _ _ → refl
     ; (_ , there ()) _ _ _ _ ; _ (_ , there ()) _ _ _ })
  (λ { _ (_ , here) (_ , here) _ _ → refl
     ; _ (_ , there ()) _ _ _ ; _ _ (_ , there ()) _ _ })
  []

-- Y's opening is well formed inside +Y^β and, carried, inside +X^α
okY : All (SlotOK WY) (opn 0 ∷ [])
okY = (0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) }) ,
        (λ { _ (inj₁ ()) ; _ (inj₂ (there⇔ ())) })) ∷ []

okX : All (SlotOK WX) (opn 0 ∷ [])
okX = (0 , here , r-here , (λ { (_ , here) () ; (_ , there ()) }) ,
        (λ { _ (inj₁ ()) ; _ (inj₂ (there⇔ ())) })) ∷ []

wfX : WfWorld WX
wfX = wf-world (right-only (both (inj₂ here⇔) joint[]))
  (λ { (inj₁ ()) ; (inj₂ here⇔) → abst-★ r-here (r-there r-here)
     ; (inj₂ (there⇔ ())) })
  (λ { (_ , here) (_ , here) _ _ _ → refl
     ; (_ , there ()) _ _ _ _ ; _ (_ , there ()) _ _ _ })
  (λ { _ _ _ (inj₂ here⇔) (inj₂ here⇔) → refl
     ; _ _ _ (inj₁ ()) _ ; _ _ _ _ (inj₁ ())
     ; _ _ _ (inj₂ (there⇔ ())) _ ; _ _ _ _ (inj₂ (there⇔ ())) })
  []

rK★ : ∀ {μ} → (X⊑★ ∷ μ) ⊢ `∀ (` 1 ⇒ (` 0 ⇒ ` 1)) ⊑ (★ ⇒ (★ ⇒ ★))
rK★ = ∀⊑ nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var))
  (⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here))))

qXY : ∀ {μ} → (X⊑X ∷ X⊑★ ∷ μ) ⊢ ` 1 ⇒ (` 0 ⇒ ` 1) ⊑ ★ ⇒ (` 0 ⇒ ★)
qXY = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ X⊑X (X⊑★ (there here)))

-- THE FINAL PAIR, related (claim-rep for X, opening and join for Y)
final : W₄ ∣ [] ⊢ L₀ ⊑ R₄ ∶ q-top
final =
  Λ⊑ claimX nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
    (⊑cast
      (⊑⟪⟫ intY (push ca-[] f-end (ns-opn refl ∷ []) (inj₂ vL1)) okY
        ([] ∷ []) [] wfY qXY
        (⊑cast
          (⊑⟪⟫ intX (push (ca-opn refl ca-[]) (f-keep f-end) [] (inj₁ refl))
            okX ([] ∷ []) [] wfX (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X))
            (Λ⊑ (b-join (join1 join-here here r-here))
              nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var)) liftᴸ-[] vNL
              (ƛ⊑ƛ {pA = X⊑X} tf tf
                (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
              (⇒⊑⇒ X⊑X (⇒⊑⇒ X⊑X X⊑X)))
            bX qXY)
          ci-ty qXY)
        bY rK★)
      cf-ty rK★)
    q-top

-- claim-rep needs NO opening here: both left binders claim their rep.
-- vars at the top (X ↦ α, Y ↦ β), and both right boundaries rejoin
W₄₂ : World Δ2 ΔT2      -- Y_L at center 0 ↦ β, X_L at center 1 ↦ α
W₄₂ = W₄₁ ⊕ᴸ⇔ 0

WY2 : World Δ2 ΔY
WY2 = world⁰ 2 (keep (keep []↪)) (keep (skip []↪))
        [] ((0 , 0) ∷ (1 , 1) ∷ [])

WX2 : World Δ2 ΔXY
WX2 = world⁰ 2 (keep (keep []↪)) (keep (keep []↪))
        [] ((0 , 0) ∷ (1 , 1) ∷ [])

claimY : Bind W₄₁ [] W₄₂ []
claimY = b-rep r-here (λ { (_ , ()) })
  (λ { _ (inj₁ ()) ; _ (inj₂ (there⇔ ())) })

intY2 : Interior W₄₂ [] ΘY WY2
intY2 = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , here) fresh[] ins-here))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ { _ (_ , here) _ () ; _ (_ , there ()) _ _ }
  ; join-fresh = λ
      { here here _ → (λ _ → inj₂ here⇔) , (λ _ → refl)
      ; (there here) here _ →
          (λ ()) , (λ { (inj₁ ()) ; (inj₂ (there⇔ (there⇔ ()))) })
      ; _ (there ()) _ ; (there (there ())) _ _ }
  }

intX2 : Interior WY2 [] ΘX WX2
intX2 = record
  { int-left   = interior changes[]
  ; int-right  = interior (changes∷ changes[]
                   (step-bind (_ , there here)
                      (fresh∷ (λ ()) fresh[]) (ins-there ins-here)))
  ; same-ϱᵍ    = refl
  ; same-ϱˡ    = refl
  ; same-κ     = refl
  ; join-cont  = λ
      { (_ , here) (_ , here) refl refl → (λ _ → refl) , (λ _ → refl)
      ; (_ , there here) (_ , here) refl refl → (λ ()) , (λ ())
      ; _ (_ , there here) _ ()
      ; _ (_ , there (there ())) _ _
      ; (_ , there (there ())) _ _ _ }
  ; join-fresh = λ
      { (there here) (there here) _ →
          (λ _ → inj₂ (there⇔ here⇔)) , (λ _ → refl)
      ; here (there here) _ →
          (λ ()) , (λ { (inj₁ ()) ; (inj₂ (there⇔ (there⇔ ()))) })
      ; _ here (inj₁ ()) ; _ here (inj₂ ())
      ; _ (there (there ())) _ ; (there (there ())) _ _ }
  }

agree2 : ∀ {Δ′} {W : World Δ2 Δ′} {α β}
  → Δ′ ∋rep 0 := ★ → Δ′ ∋rep 1 := ★
  → (ϱᵍʷ W ≡ []) → (ϱˡʷ W ≡ (0 , 0) ∷ (1 , 1) ∷ [])
  → Paired W α β → Agree W α β
agree2 h0 h1 eg el (inj₁ p) rewrite eg with p
... | ()
agree2 h0 h1 eg el (inj₂ p) rewrite el with p
... | here⇔            = abst-★ r-here h0
... | there⇔ here⇔     = abst-★ (r-there-abst r-here) h1
... | there⇔ (there⇔ ())

uniq2 : ∀ {Δ′} {W : World Δ2 Δ′} → (ϱᵍʷ W ≡ [])
  → (ϱˡʷ W ≡ (0 , 0) ∷ (1 , 1) ∷ [])
  → ∀ {α α′ β β′} → Paired W α β → Paired W α′ β′
  → (α ≡ α′ → β ≡ β′) × (β ≡ β′ → α ≡ α′)
uniq2 eg el (inj₁ p) _ rewrite eg with p
... | ()
uniq2 eg el _ (inj₁ p) rewrite eg with p
... | ()
uniq2 eg el (inj₂ p) (inj₂ p′) rewrite el with p | p′
... | here⇔ | here⇔ = (λ _ → refl) , (λ _ → refl)
... | here⇔ | there⇔ here⇔ = (λ ()) , (λ ())
... | there⇔ here⇔ | here⇔ = (λ ()) , (λ ())
... | there⇔ here⇔ | there⇔ here⇔ = (λ _ → refl) , (λ _ → refl)
... | there⇔ (there⇔ ()) | _
... | _ | there⇔ (there⇔ ())

wfY2 : WfWorld WY2
wfY2 = wf-world (both (inj₂ here⇔) (left-only joint[]))
  (agree2 r-here (r-there r-here) refl refl)
  (λ _ _ _ p p′ → proj₂ (uniq2 {W = WY2} refl refl p p′) refl)
  (λ _ _ _ p p′ → proj₁ (uniq2 {W = WY2} refl refl p p′) refl)
  []

wfX2 : WfWorld WX2
wfX2 = wf-world (both (inj₂ here⇔) (both (inj₂ (there⇔ here⇔)) joint[]))
  (agree2 r-here (r-there r-here) refl refl)
  (λ _ _ _ p p′ → proj₂ (uniq2 {W = WX2} refl refl p p′) refl)
  (λ _ _ _ p p′ → proj₁ (uniq2 {W = WX2} refl refl p p′) refl)
  []

qF : (X⊑★ ∷ X⊑★ ∷ []) ⊢ ` 1 ⇒ (` 0 ⇒ ` 1) ⊑ ★ ⇒ (★ ⇒ ★)
qF = ⇒⊑⇒ (X⊑★ (there here)) (⇒⊑⇒ (X⊑★ here) (X⊑★ (there here)))

qC : (X⊑X ∷ X⊑★ ∷ []) ⊢ ` 1 ⇒ (` 0 ⇒ ` 1) ⊑ ★ ⇒ (` 0 ⇒ ★)
qC = qXY

final-no-push : W₄ ∣ [] ⊢ L₀ ⊑ R₄ ∶ q-top
final-no-push =
  Λ⊑ claimX nv-∀ (∈-∀ (∈-⇒ˡ ∈-var)) liftᴸ-[] vL1
    (Λ⊑ claimY nv-⇒ (∈-⇒ʳ refl (∈-⇒ˡ ∈-var)) liftᴸ-[] vNL
      (⊑cast
        (⊑⟪⟫₀ intY2 wfY2
          (⊑cast
            (⊑⟪⟫₀ intX2 wfX2
              (ƛ⊑ƛ {pA = X⊑X} tf tf
                (ƛ⊑ƛ {pA = X⊑X} {pB = X⊑X} tf tf (x⊑x (Sʷ Zʷ))))
              bX qC)
            ci-ty qC)
          bY qF)
        cf-ty qF)
      rK★)
    q-top

-- the DGG's `RelatedValues` side conditions hold at W₄
W₄-wf : WfWorld W₄
W₄-wf = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
  (λ { (_ , ()) _ _ _ _ }) (λ { _ (_ , ()) _ _ _ }) []

------------------------------------------------------------------------
-- 4. DGG part 1 on the initial pair (design.md D29's obligation): the
-- left is a value; the right's run reaches its value R₄, related to it
------------------------------------------------------------------------

-- states 1 and 3 (ν-terms), pinned
R₁ R₃ : Term
R₁ = ((ν ★ · KL ⟨ cA ⟩) ⟨ [] ∣ ∀ᵖ ci ⟩) ⟨ [] ∣ instY ⟩
R₃ = (ν ★ · (BA ⟨ [] ∣ ∀ᵖ ci ⟩) ⟨ cY ⟩) ⟨ [] ∣ cf ⟩

R₀-states : evalTerms 30 R₀-⊢ ≡ R₀ ∷ R₁ ∷ R₂ ∷ R₃ ∷ R₄ ∷ []
R₀-states = refl

justStep : ∀ {Δ M} {r : StepResult Δ M} → step Δ M ≡ just r
  → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
justStep {r = r} _ = proj₂ (proj₂ r)

st₀ : empty ⊢ R₀ -→ R₁ ∣ none
st₀ = justStep refl

st₁ : empty ⊢ R₁ -→ R₂ ∣ new ★
st₁ = justStep refl

st₂ : ΔT1 ⊢ R₂ -→ R₃ ∣ none
st₂ = justStep refl

st₃ : ΔT1 ⊢ R₃ -→ R₄ ∣ new ★
st₃ = justStep refl

dgg1-H1 :
  ∃[ V′ ] Σ[ r′ ∈ empty ⊢ R₀ -→* V′ ] Value V′
    × Σ[ W′ ∈ World empty (applyˢ (allocs r′) empty) ]
        WfWorld W′ × (κʷ W′ ≡ [])
        × Σ[ q ∈ K2 ⊑ᵂ⟨ W′ ⟩ (★ ⇒ (★ ⇒ ★)) ] (W′ ∣ [] ⊢ L₀ ⊑ V′ ∶ q)
dgg1-H1 =
  R₄ , (st₀ then st₁ then st₂ then st₃ then done) , vR₄ ,
  W₄ , W₄-wf , refl , q-top , final

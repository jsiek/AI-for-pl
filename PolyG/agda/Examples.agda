module Examples where

-- File Charter:
--   * Closed example programs, run by the evaluator of Eval.agda:
--       - in the surface language PolyGν, each with a typing derivation
--         `name-⊢ : [] ∣ [] ⊢ᴳ name ⦂ A`, run after elaboration
--         (Compile.elab); the PolyCν typing of the elaborated term is
--         `elab-preserves-typing-closed name-⊢`;
--       - directly in the cast calculus PolyCν, each with a typing
--         derivation `name-⊢ : Σ ∣ [] ∣ [] ⊢ name ⦂ A`.
--   * Each run `name-↠ : Σ ▷ M —↠ Σ′ ▷ N` ends at true, false or ℧ and
--     is the trace computed by `eval`, so the endpoint is checked by
--     computation.  Two short runs are also written out by hand.
--   * Most surface programs are the examples of thesis §10.2.1: the
--     polymorphic identity at 𝔹 with seal/unseal, its variant with a ?
--     input, the variant without the seal (a tag error), and `const`.
--   * Two instances of the graduality theorem (MetaTheory.agda) on pairs
--     of programs related by precision.
--   * ExamplesCoverage.agda checks that these runs exercise every
--     reduction rule.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; z<s)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Terms
open import Reduction
open import Typing
open import GradualTerms
open import Compile using (elab)
open import CompileMeta using (elab-preserves-typing-closed)
open import TermPrecision using (Z≅ᵖ; Zᵖ)
open import GradualTermPrecision
open import GradualityDefinitions
open import MetaTheory using (graduality)
open import Eval

------------------------------------------------------------------------
-- Notation
------------------------------------------------------------------------

-- the innermost type variable, X
TX : Ty
TX = ‵ tvar zero

-- the fuel used for every run
gas : ℕ
gas = 200

------------------------------------------------------------------------
-- Polymorphic library terms of PolyGν
------------------------------------------------------------------------

-- Λν X. λ x : X. x :: X
idX : GTerm
idX = Λν (ƛ TX (` 0 ⦂⦂ TX))

idX-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ idX ⦂ ∀ν (TX ⇒ TX)
idX-⊢ = ⊢Λν (⊢ƛ (wf‵ z<s) (⊢⦂⦂ (⊢` Z) ∼‵ (wf‵ z<s)))

-- Λν X. λ x : ?. x :: X
idD : GTerm
idD = Λν (ƛ ★ (` 0 ⦂⦂ TX))

idD-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ idD ⦂ ∀ν (★ ⇒ TX)
idD-⊢ = ⊢Λν (⊢ƛ wf★ (⊢⦂⦂ (⊢` Z) ∼★L (wf‵ z<s)))

-- const = (Λν X. λ x : X. true) :: ∀ν X. ? → 𝔹
constD : GTerm
constD = Λν (ƛ TX true) ⦂⦂ ∀ν (★ ⇒ 𝔹)

constD-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ constD ⦂ ∀ν (★ ⇒ 𝔹)
constD-⊢ = ⊢⦂⦂ (⊢Λν (⊢ƛ (wf‵ z<s) ⊢true)) (∼∀ (∼⇒ ∼★R ∼𝔹))
                (wf∀ (wf⇒ wf★ wf𝔹))

-- Λν X. λ x : X. λ y : 𝔹. x
firstX : GTerm
firstX = Λν (ƛ TX (ƛ 𝔹 (` 1)))

firstX-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ firstX ⦂ ∀ν (TX ⇒ 𝔹 ⇒ TX)
firstX-⊢ = ⊢Λν (⊢ƛ (wf‵ z<s) (⊢ƛ wf𝔹 (⊢` (S Z))))

-- Λν X. λ x : X. λ y : 𝔹. y
secondX : GTerm
secondX = Λν (ƛ TX (ƛ 𝔹 (` 0)))

secondX-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ secondX ⦂ ∀ν (TX ⇒ 𝔹 ⇒ 𝔹)
secondX-⊢ = ⊢Λν (⊢ƛ (wf‵ z<s) (⊢ƛ wf𝔹 (⊢` Z)))

-- Λν X. λ x : ?. is(X)? x
isX : GTerm
isX = Λν (ƛ ★ (is (G‵ (tvar 0)) (` 0)))

isX-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ isX ⦂ ∀ν (★ ⇒ 𝔹)
isX-⊢ = ⊢Λν (⊢ƛ wf★ (⊢is (wfG‵ z<s) (⊢` Z)))

-- λ x : 𝔹. x
id𝔹 : GTerm
id𝔹 = ƛ 𝔹 (` 0)

id𝔹-⊢ : ∀ {Δ Γ} → Δ ∣ Γ ⊢ᴳ id𝔹 ⦂ 𝔹 ⇒ 𝔹
id𝔹-⊢ = ⊢ƛ wf𝔹 (⊢` Z)

------------------------------------------------------------------------
-- The polymorphic identity at 𝔹 (thesis §10.2.1)
------------------------------------------------------------------------

-- let f = (Λν X. λ x : X. x :: X) {X ≅ 𝔹}; unseal X (f (seal X true))
id-seal : GTerm
id-seal = inst idX 𝔹 (unseal 0 (` 0 · seal 0 true))

id-seal-⊢ : [] ∣ [] ⊢ᴳ id-seal ⦂ 𝔹
id-seal-⊢ = ⊢inst idX-⊢ as-∀ wf𝔹
  (⊢unseal Z≅ (⊢· (⊢` Z) as-fun (⊢seal Z≅ ⊢true ∼𝔹) ∼‵) ∼‵) wf𝔹

-- the elaborated program, written out
id-seal-elab : elab id-seal-⊢ ≡
  inst (Λν [] (ƛ TX (cast down (tag (G‵ (tvar 0)) (‵⊑ (tvar 0)))
                      (cast up (tag (G‵ (tvar 0)) (‵⊑ (tvar 0))) (` 0)))))
       𝔹
       (unseal (tvar 0)
         (` 0 · cast down (tag (G‵ (tvar 0)) (‵⊑ (tvar 0)))
                  (cast up (tag (G‵ (tvar 0)) (‵⊑ (tvar 0)))
                    (seal (tvar 0)
                      (cast down (tag G𝔹 𝔹⊑) (cast up (tag G𝔹 𝔹⊑) true))))))
id-seal-elab = refl

id-seal-↠ : [] ▷ elab id-seal-⊢ —↠ 𝔹 ∷ [] ▷ true
id-seal-↠ = trace (eval gas [] (elab id-seal-⊢))

-- the input type changed from X to ?; the seal stays:
-- let f = (Λν X. λ x : ?. x :: X) {X ≅ 𝔹}; unseal X (f (seal X true))
id-dyn-seal : GTerm
id-dyn-seal = inst idD 𝔹 (unseal 0 (` 0 · seal 0 true))

id-dyn-seal-⊢ : [] ∣ [] ⊢ᴳ id-dyn-seal ⦂ 𝔹
id-dyn-seal-⊢ = ⊢inst idD-⊢ as-∀ wf𝔹
  (⊢unseal Z≅ (⊢· (⊢` Z) as-fun (⊢seal Z≅ ⊢true ∼𝔹) ∼★R) ∼‵) wf𝔹

id-dyn-seal-↠ : [] ▷ elab id-dyn-seal-⊢ —↠ 𝔹 ∷ [] ▷ true
id-dyn-seal-↠ = trace (eval gas [] (elab id-dyn-seal-⊢))

-- without the seal the input is tagged 𝔹, not X, and the cast to X
-- fails: let f = (Λν X. λ x : ?. x :: X) {X ≅ 𝔹}; unseal X (f true)
id-dyn-noseal : GTerm
id-dyn-noseal = inst idD 𝔹 (unseal 0 (` 0 · true))

id-dyn-noseal-⊢ : [] ∣ [] ⊢ᴳ id-dyn-noseal ⦂ 𝔹
id-dyn-noseal-⊢ = ⊢inst idD-⊢ as-∀ wf𝔹
  (⊢unseal Z≅ (⊢· (⊢` Z) as-fun ⊢true ∼★R) ∼‵) wf𝔹

id-dyn-noseal-↠ : [] ▷ elab id-dyn-noseal-⊢ —↠ 𝔹 ∷ [] ▷ ℧
id-dyn-noseal-↠ = trace (eval gas [] (elab id-dyn-noseal-⊢))

------------------------------------------------------------------------
-- A Λν through ? and back
------------------------------------------------------------------------

-- the identity ascribed to ?, then instantiated:
-- let f = (idX :: ?) {X ≅ 𝔹}; unseal X (f (seal X true))
id-via-dyn : GTerm
id-via-dyn = inst (idX ⦂⦂ ★) 𝔹 (unseal 0 (` 0 · seal 0 true))

id-via-dyn-⊢ : [] ∣ [] ⊢ᴳ id-via-dyn ⦂ 𝔹
id-via-dyn-⊢ = ⊢inst (⊢⦂⦂ idX-⊢ ∼★R wf★) as-∀★ wf𝔹
  (⊢unseal Z≅ (⊢· (⊢` Z) as-fun★ (⊢seal Z≅ ⊢true ∼𝔹) ∼★R) ∼★L) wf𝔹

id-via-dyn-↠ : [] ▷ elab id-via-dyn-⊢ —↠ 𝔹 ∷ [] ▷ true
id-via-dyn-↠ = trace (eval gas [] (elab id-via-dyn-⊢))

-- the same without the seal: the proxy's cast to X fails
-- let f = (idX :: ?) {X ≅ 𝔹}; unseal X (f true)
id-via-dyn-noseal : GTerm
id-via-dyn-noseal = inst (idX ⦂⦂ ★) 𝔹 (unseal 0 (` 0 · true))

id-via-dyn-noseal-⊢ : [] ∣ [] ⊢ᴳ id-via-dyn-noseal ⦂ 𝔹
id-via-dyn-noseal-⊢ = ⊢inst (⊢⦂⦂ idX-⊢ ∼★R wf★) as-∀★ wf𝔹
  (⊢unseal Z≅ (⊢· (⊢` Z) as-fun★ ⊢true ∼★R) ∼★L) wf𝔹

id-via-dyn-noseal-↠ : [] ▷ elab id-via-dyn-noseal-⊢ —↠ 𝔹 ∷ [] ▷ ℧
id-via-dyn-noseal-↠ = trace (eval gas [] (elab id-via-dyn-noseal-⊢))

------------------------------------------------------------------------
-- const (thesis §10.2.1)
------------------------------------------------------------------------

-- let f = const {X ≅ 𝔹}; f (seal X true)
const-seal : GTerm
const-seal = inst constD 𝔹 (` 0 · seal 0 true)

const-seal-⊢ : [] ∣ [] ⊢ᴳ const-seal ⦂ 𝔹
const-seal-⊢ = ⊢inst constD-⊢ as-∀ wf𝔹
  (⊢· (⊢` Z) as-fun (⊢seal Z≅ ⊢true ∼𝔹) ∼★R) wf𝔹

const-seal-↠ : [] ▷ elab const-seal-⊢ —↠ 𝔹 ∷ [] ▷ true
const-seal-↠ = trace (eval gas [] (elab const-seal-⊢))

-- let f = const {X ≅ 𝔹}; f true
-- (the input is tagged 𝔹, not X: a tag error, not a parametricity
-- violation)
const-noseal : GTerm
const-noseal = inst constD 𝔹 (` 0 · true)

const-noseal-⊢ : [] ∣ [] ⊢ᴳ const-noseal ⦂ 𝔹
const-noseal-⊢ = ⊢inst constD-⊢ as-∀ wf𝔹
  (⊢· (⊢` Z) as-fun ⊢true ∼★R) wf𝔹

const-noseal-↠ : [] ▷ elab const-noseal-⊢ —↠ 𝔹 ∷ [] ▷ ℧
const-noseal-↠ = trace (eval gas [] (elab const-noseal-⊢))

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

-- let f = firstX {X ≅ 𝔹}; unseal X (f (seal X true) false)
first-ex : GTerm
first-ex = inst firstX 𝔹 (unseal 0 (` 0 · seal 0 true · false))

first-ex-⊢ : [] ∣ [] ⊢ᴳ first-ex ⦂ 𝔹
first-ex-⊢ = ⊢inst firstX-⊢ as-∀ wf𝔹
  (⊢unseal Z≅
    (⊢· (⊢· (⊢` Z) as-fun (⊢seal Z≅ ⊢true ∼𝔹) ∼‵) as-fun ⊢false ∼𝔹)
    ∼‵)
  wf𝔹

first-ex-↠ : [] ▷ elab first-ex-⊢ —↠ 𝔹 ∷ [] ▷ true
first-ex-↠ = trace (eval gas [] (elab first-ex-⊢))

-- let f = secondX {X ≅ 𝔹}; f (seal X true) false
second-ex : GTerm
second-ex = inst secondX 𝔹 (` 0 · seal 0 true · false)

second-ex-⊢ : [] ∣ [] ⊢ᴳ second-ex ⦂ 𝔹
second-ex-⊢ = ⊢inst secondX-⊢ as-∀ wf𝔹
  (⊢· (⊢· (⊢` Z) as-fun (⊢seal Z≅ ⊢true ∼𝔹) ∼‵) as-fun ⊢false ∼𝔹)
  wf𝔹

second-ex-↠ : [] ▷ elab second-ex-⊢ —↠ 𝔹 ∷ [] ▷ false
second-ex-↠ = trace (eval gas [] (elab second-ex-⊢))

------------------------------------------------------------------------
-- Nested instantiation: two fresh seals
------------------------------------------------------------------------

-- let f = idX {X ≅ 𝔹};
-- let g = idX {Y ≅ X};
-- unseal X (f (unseal Y (g (seal Y (seal X true)))))
-- (in the inner body Y is variable 0 and X is variable 1)
nested : GTerm
nested =
  inst idX 𝔹
    (inst idX TX
      (unseal 1 (` 1 · unseal 0 (` 0 · seal 0 (seal 1 true)))))

nested-⊢ : [] ∣ [] ⊢ᴳ nested ⦂ 𝔹
nested-⊢ = ⊢inst idX-⊢ as-∀ wf𝔹
  (⊢inst idX-⊢ as-∀ (wf‵ z<s)
    (⊢unseal (S≅ Z≅)
      (⊢· (⊢` (S Z)) as-fun
        (⊢unseal Z≅
          (⊢· (⊢` Z) as-fun (⊢seal Z≅ (⊢seal (S≅ Z≅) ⊢true ∼𝔹) ∼‵) ∼‵)
          ∼‵)
        ∼‵)
      ∼‵)
    wf𝔹)
  wf𝔹

-- the two seals: seal 0 ≅ 𝔹 and seal 1 ≅ seal 0
nested-↠ : [] ▷ elab nested-⊢ —↠ 𝔹 ∷ ‵ tseal 0 ∷ [] ▷ true
nested-↠ = trace (eval gas [] (elab nested-⊢))

------------------------------------------------------------------------
-- Tag tests
------------------------------------------------------------------------

-- is(𝔹)? true
is-bool : GTerm
is-bool = is G𝔹 true

is-bool-⊢ : [] ∣ [] ⊢ᴳ is-bool ⦂ 𝔹
is-bool-⊢ = ⊢is wfG𝔹 ⊢true

is-bool-↠ : [] ▷ elab is-bool-⊢ —↠ [] ▷ true
is-bool-↠ = trace (eval gas [] (elab is-bool-⊢))

-- is(? → ?)? true
is-fun : GTerm
is-fun = is G⇒ true

is-fun-⊢ : [] ∣ [] ⊢ᴳ is-fun ⦂ 𝔹
is-fun-⊢ = ⊢is wfG⇒ ⊢true

is-fun-↠ : [] ▷ elab is-fun-⊢ —↠ [] ▷ false
is-fun-↠ = trace (eval gas [] (elab is-fun-⊢))

-- let f = (Λν X. λ x : ?. is(X)? x) {X ≅ 𝔹}; f (seal X true)
is-seal-yes : GTerm
is-seal-yes = inst isX 𝔹 (` 0 · seal 0 true)

is-seal-yes-⊢ : [] ∣ [] ⊢ᴳ is-seal-yes ⦂ 𝔹
is-seal-yes-⊢ = ⊢inst isX-⊢ as-∀ wf𝔹
  (⊢· (⊢` Z) as-fun (⊢seal Z≅ ⊢true ∼𝔹) ∼★R) wf𝔹

is-seal-yes-↠ : [] ▷ elab is-seal-yes-⊢ —↠ 𝔹 ∷ [] ▷ true
is-seal-yes-↠ = trace (eval gas [] (elab is-seal-yes-⊢))

-- let f = (Λν X. λ x : ?. is(X)? x) {X ≅ 𝔹}; f true
is-seal-no : GTerm
is-seal-no = inst isX 𝔹 (` 0 · true)

is-seal-no-⊢ : [] ∣ [] ⊢ᴳ is-seal-no ⦂ 𝔹
is-seal-no-⊢ = ⊢inst isX-⊢ as-∀ wf𝔹 (⊢· (⊢` Z) as-fun ⊢true ∼★R) wf𝔹

is-seal-no-↠ : [] ▷ elab is-seal-no-⊢ —↠ 𝔹 ∷ [] ▷ false
is-seal-no-↠ = trace (eval gas [] (elab is-seal-no-⊢))

------------------------------------------------------------------------
-- Casts at ? and at function types
------------------------------------------------------------------------

-- a function used as a boolean: if (λ x : 𝔹. x) :: ? then true else
-- false
tag-mismatch : GTerm
tag-mismatch = if (id𝔹 ⦂⦂ ★) true false

tag-mismatch-⊢ : [] ∣ [] ⊢ᴳ tag-mismatch ⦂ 𝔹
tag-mismatch-⊢ = ⊢if (⊢⦂⦂ id𝔹-⊢ ∼★R wf★) ∼★L ⊢true ⊢false m𝔹

tag-mismatch-↠ : [] ▷ elab tag-mismatch-⊢ —↠ [] ▷ ℧
tag-mismatch-↠ = trace (eval gas [] (elab tag-mismatch-⊢))

-- ((λ x : 𝔹. x) :: ? → ?) true :: 𝔹
-- (a function proxy: the call casts the argument down and the result
-- up, then the inner proxy the other way)
fun-cast : GTerm
fun-cast = (id𝔹 ⦂⦂ (★ ⇒ ★)) · true ⦂⦂ 𝔹

fun-cast-⊢ : [] ∣ [] ⊢ᴳ fun-cast ⦂ 𝔹
fun-cast-⊢ =
  ⊢⦂⦂ (⊢· (⊢⦂⦂ id𝔹-⊢ (∼⇒ ∼★R ∼★R) (wf⇒ wf★ wf★)) as-fun ⊢true ∼★R)
      ∼★L wf𝔹

fun-cast-↠ : [] ▷ elab fun-cast-⊢ —↠ [] ▷ true
fun-cast-↠ = trace (eval gas [] (elab fun-cast-⊢))

-- ((λ x : 𝔹. x) :: ?) true :: 𝔹: an application at type ?
dyn-app : GTerm
dyn-app = (id𝔹 ⦂⦂ ★) · true ⦂⦂ 𝔹

dyn-app-⊢ : [] ∣ [] ⊢ᴳ dyn-app ⦂ 𝔹
dyn-app-⊢ = ⊢⦂⦂ (⊢· (⊢⦂⦂ id𝔹-⊢ ∼★R wf★) as-fun★ ⊢true ∼★R) ∼★L wf𝔹

dyn-app-↠ : [] ▷ elab dyn-app-⊢ —↠ [] ▷ true
dyn-app-↠ = trace (eval gas [] (elab dyn-app-⊢))

-- ((λ x : 𝔹. x) :: ?) (λ x : 𝔹. x) :: 𝔹: the argument fails the
-- function's cast to 𝔹
dyn-app-bad : GTerm
dyn-app-bad = (id𝔹 ⦂⦂ ★) · id𝔹 ⦂⦂ 𝔹

dyn-app-bad-⊢ : [] ∣ [] ⊢ᴳ dyn-app-bad ⦂ 𝔹
dyn-app-bad-⊢ = ⊢⦂⦂ (⊢· (⊢⦂⦂ id𝔹-⊢ ∼★R wf★) as-fun★ id𝔹-⊢ ∼★R) ∼★L wf𝔹

dyn-app-bad-↠ : [] ▷ elab dyn-app-bad-⊢ —↠ [] ▷ ℧
dyn-app-bad-↠ = trace (eval gas [] (elab dyn-app-bad-⊢))

------------------------------------------------------------------------
-- let and if
------------------------------------------------------------------------

-- let x = true; if x then (false :: ?) else true
-- (the branches have types ? and 𝔹, with meet 𝔹)
let-if : GTerm
let-if = letv true (if (` 0) (false ⦂⦂ ★) true)

let-if-⊢ : [] ∣ [] ⊢ᴳ let-if ⦂ 𝔹
let-if-⊢ = ⊢letv ⊢true (⊢if (⊢` Z) ∼𝔹 (⊢⦂⦂ ⊢false ∼★R wf★) ⊢true m★L)

let-if-↠ : [] ▷ elab let-if-⊢ —↠ [] ▷ false
let-if-↠ = trace (eval gas [] (elab let-if-⊢))

-- let x = false :: ?; if x then false else true
let-if-dyn : GTerm
let-if-dyn = letv (false ⦂⦂ ★) (if (` 0) false true)

let-if-dyn-⊢ : [] ∣ [] ⊢ᴳ let-if-dyn ⦂ 𝔹
let-if-dyn-⊢ = ⊢letv (⊢⦂⦂ ⊢false ∼★R wf★) (⊢if (⊢` Z) ∼★L ⊢false ⊢true m𝔹)

let-if-dyn-↠ : [] ▷ elab let-if-dyn-⊢ —↠ [] ▷ true
let-if-dyn-↠ = trace (eval gas [] (elab let-if-dyn-⊢))

------------------------------------------------------------------------
-- Programs of the cast calculus PolyCν
------------------------------------------------------------------------

-- let f = (⟨∀ν X. X → X?⟩↑ (Λν X. λ x : X. x)) {X ≅ 𝔹};
-- is(X)? (f (seal X true))
-- (a ∀ν cast on a proxy, then an upcast of the result to ?)
c-proxy : Term
c-proxy =
  inst (cast up (∀⊑ (‵⊑ (tvar 0) ⇒⊑ tag (G‵ (tvar 0)) (‵⊑ (tvar 0))))
          (Λν [] (ƛ TX (` 0))))
       𝔹
       (is (G‵ (tvar 0)) (` 0 · seal (tvar 0) true))

c-proxy-⊢ : [] ∣ [] ∣ [] ⊢ c-proxy ⦂ 𝔹
c-proxy-⊢ =
  ⊢inst (⊢up (⊑∀ (⊑⇒ (⊑‵ z<s) (⊑tag (wfG‵ z<s) (⊑‵ z<s))))
             (⊢Λν (⊢ƛ (⊢` Z))))
        wf𝔹
        (⊢is (wfG‵ z<s) (⊢· (⊢` Z) (⊢seal (nt-var Z≅) ⊢true)))

c-proxy-↠ : [] ▷ c-proxy —↠ 𝔹 ∷ [] ▷ true
c-proxy-↠ = trace (eval gas [] c-proxy)

-- if ⟨𝔹?⟩↓ (inj_{?→?} (λ x : ?. x)) then true else false
c-mismatch : Term
c-mismatch = if (cast down (tag G𝔹 𝔹⊑) (inj G⇒ (ƛ ★ (` 0)))) true false

c-mismatch-⊢ : [] ∣ [] ∣ [] ⊢ c-mismatch ⦂ 𝔹
c-mismatch-⊢ =
  ⊢if (⊢down (⊑tag wfG𝔹 ⊑𝔹) (⊢inj wfG⇒ (⊢ƛ (⊢` Z)))) ⊢true ⊢false

c-mismatch-↠ : [] ▷ c-mismatch —↠ [] ▷ ℧
c-mismatch-↠ = trace (eval gas [] c-mismatch)

-- (λ x : 𝔹. x) ℧: ℧ in argument position
c-℧-arg : Term
c-℧-arg = ƛ 𝔹 (` 0) · ℧

c-℧-arg-⊢ : [] ∣ [] ∣ [] ⊢ c-℧-arg ⦂ 𝔹
c-℧-arg-⊢ = ⊢· (⊢ƛ (⊢` Z)) ⊢℧

c-℧-arg-↠ : [] ▷ c-℧-arg —↠ [] ▷ ℧
c-℧-arg-↠ =
    ƛ 𝔹 (` 0) · ℧
  —→⟨ ξ-℧ (app□ (ƛ 𝔹 (` 0)) V-ƛ) ⟩
    ℧
  ∎

c-℧-arg-eval : trace (eval gas [] c-℧-arg) ≡ c-℧-arg-↠
c-℧-arg-eval = refl

-- let x = true; if x then false else true, written out by hand
c-let-if : Term
c-let-if = letv true (if (` 0) false true)

c-let-if-⊢ : [] ∣ [] ∣ [] ⊢ c-let-if ⦂ 𝔹
c-let-if-⊢ = ⊢letv ⊢true (⊢if (⊢` Z) ⊢false ⊢true)

c-let-if-↠ : [] ▷ c-let-if —↠ [] ▷ false
c-let-if-↠ =
    letv true (if (` 0) false true)
  —→⟨ β-letv V-true ⟩
    if true false true
  —→⟨ β-if-true ⟩
    false
  ∎

c-let-if-eval : trace (eval gas [] c-let-if) ≡ c-let-if-↠
c-let-if-eval = refl

-- runs from a nonempty store, with the seal 0 ≅ 𝔹 already created:
-- unseal_0 (seal_0 true)
c-unseal : Term
c-unseal = unseal (tseal 0) (seal (tseal 0) true)

c-unseal-⊢ : 𝔹 ∷ [] ∣ [] ∣ [] ⊢ c-unseal ⦂ 𝔹
c-unseal-⊢ = ⊢unseal (nt-seal Zˢ) (⊢seal (nt-seal Zˢ) ⊢true)

c-unseal-↠ : 𝔹 ∷ [] ▷ c-unseal —↠ 𝔹 ∷ [] ▷ true
c-unseal-↠ = trace (eval gas (𝔹 ∷ []) c-unseal)

-- is(seal 0)? (inj_𝔹 true): a seal tag against the 𝔹 tag
c-is-seal-no : Term
c-is-seal-no = is (G‵ (tseal 0)) (inj G𝔹 true)

c-is-seal-no-⊢ : 𝔹 ∷ [] ∣ [] ∣ [] ⊢ c-is-seal-no ⦂ 𝔹
c-is-seal-no-⊢ = ⊢is (wfG‵ _) (⊢inj wfG𝔹 ⊢true)

c-is-seal-no-↠ : 𝔹 ∷ [] ▷ c-is-seal-no —↠ 𝔹 ∷ [] ▷ false
c-is-seal-no-↠ = trace (eval gas (𝔹 ∷ []) c-is-seal-no)

------------------------------------------------------------------------
-- Graduality in action (MetaTheory.graduality)
------------------------------------------------------------------------

-- id-seal ⊑ id-dyn-seal: the input type X made less precise (?).
-- Both programs return true.
id-seal⊑id-dyn-seal : [] ∣ [] ⊢ id-seal-⊢ ⊑ᴳ id-dyn-seal-⊢ ⦂ 𝔹⊑
id-seal⊑id-dyn-seal =
  ⊑inst (⊑Λν (⊑ƛ X⊑★ (⊑⦂⦂ (⊑` Zᵖ) (⊑‵ z<s))))
        ⊑𝔹
        (⊑⇒ X⊑★ (⊑‵ z<s))
        (⊑unseal Z≅ᵖ (⊑· (⊑` Zᵖ) (⊑seal Z≅ᵖ ⊑true) (⊑‵ z<s)))
        ⊑𝔹
  where
  X⊑★ : 1 ⊢ tag (G‵ (tvar 0)) (‵⊑ (tvar 0)) ⦂ TX ⊑ ★
  X⊑★ = ⊑tag (wfG‵ z<s) (⊑‵ z<s)

-- graduality (a), applied to the run of the more precise program:
-- the less precise one also returns true
id-dyn-seal-⇓ : ∃[ V′ ] Σ[ R⇓ ∈ elab id-dyn-seal-⊢ ⇓ V′ ]
  (bool-obs Data.Bool.true ≡ observe (proj₂ (proj₂ R⇓)))
id-dyn-seal-⇓ =
  proj₁ (graduality id-seal⊑id-dyn-seal) (𝔹 ∷ [] , id-seal-↠ , V-true)

-- is(𝔹)? ((λ x : 𝔹. x) :: ? :: 𝔹) fails, while the less precise
-- is(𝔹)? ((λ x : 𝔹. x) :: ? :: ?) returns false
is-asc-𝔹 : GTerm
is-asc-𝔹 = is G𝔹 (id𝔹 ⦂⦂ ★ ⦂⦂ 𝔹)

is-asc-𝔹-⊢ : [] ∣ [] ⊢ᴳ is-asc-𝔹 ⦂ 𝔹
is-asc-𝔹-⊢ = ⊢is wfG𝔹 (⊢⦂⦂ (⊢⦂⦂ id𝔹-⊢ ∼★R wf★) ∼★L wf𝔹)

is-asc-𝔹-↠ : [] ▷ elab is-asc-𝔹-⊢ —↠ [] ▷ ℧
is-asc-𝔹-↠ = trace (eval gas [] (elab is-asc-𝔹-⊢))

is-asc-★ : GTerm
is-asc-★ = is G𝔹 (id𝔹 ⦂⦂ ★ ⦂⦂ ★)

is-asc-★-⊢ : [] ∣ [] ⊢ᴳ is-asc-★ ⦂ 𝔹
is-asc-★-⊢ = ⊢is wfG𝔹 (⊢⦂⦂ (⊢⦂⦂ id𝔹-⊢ ∼★R wf★) ∼★L wf★)

is-asc-★-↠ : [] ▷ elab is-asc-★-⊢ —↠ [] ▷ false
is-asc-★-↠ = trace (eval gas [] (elab is-asc-★-⊢))

is-asc-𝔹⊑is-asc-★ : [] ∣ [] ⊢ is-asc-𝔹-⊢ ⊑ᴳ is-asc-★-⊢ ⦂ 𝔹⊑
is-asc-𝔹⊑is-asc-★ =
  ⊑is (⊑⦂⦂ (⊑⦂⦂ (⊑ƛ ⊑𝔹 (⊑` Zᵖ)) ⊑★) (⊑tag wfG𝔹 ⊑𝔹))

-- graduality (b), applied to the run of the less precise program: the
-- more precise one returns false or fails (here it fails)
is-asc-𝔹-⇓-or-fails :
  (∃[ V ] Σ[ L⇓ ∈ elab is-asc-𝔹-⊢ ⇓ V ]
     (observe (proj₂ (proj₂ L⇓)) ≡ bool-obs Data.Bool.false))
  ⊎ Fails (elab is-asc-𝔹-⊢)
is-asc-𝔹-⇓-or-fails =
  proj₁ (proj₂ (graduality is-asc-𝔹⊑is-asc-★)) ([] , is-asc-★-↠ , V-false)

-- graduality (c) does not apply (the less precise program does not
-- fail), but the more precise one does
is-asc-𝔹-fails : Fails (elab is-asc-𝔹-⊢)
is-asc-𝔹-fails = [] , is-asc-𝔹-↠

module strong-rep-nu.SourceExamples where

-- File Charter:
--   * THE EXAMPLE PROGRAMS AS SOURCE: every plain-System-F run of
--     strong-rep-nu.Examples, written in strong-rep-nu.Source with the
--     standard `L [ A ]`, and a `refl` proof that `compile` of its
--     (checker-built) derivation IS the run-time term Examples runs.
--     Same names as Examples; the types are Examples' own.

open import Data.List using ([])
open import Data.Maybe using (from-just)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-nu.Types
open import strong-rep-nu.Source
open import strong-rep-nu.Compile using (compile)
import strong-rep-nu.Terms as T
import strong-rep-nu.Examples as E
open E using (EBod; EID; FB; GT; HB; JB; JT; VBod)

------------------------------------------------------------------------
-- The programs
------------------------------------------------------------------------

P₀ : STerm
P₀ = (Λ (ƛ ` 0 ∙ ` 0)) [ `ℕ ] · $ 7

truePoly Fbody Ffun K₀ : STerm
truePoly = Λ (ƛ ` 0 ∙ `true)
Fbody = ƛ GT ∙ (` 0 [ ` 0 ])
Ffun = Λ Fbody
K₀ = Ffun [ `𝔹 ] · truePoly · `false

const3 Jbody Jfun J₀ : STerm
const3 = Λ (ƛ ` 0 ∙ $ 3)
Jbody = ƛ JT ∙ (` 0 [ ` 0 ] · ` 1)
Jfun = Λ (ƛ ` 0 ∙ Jbody)
J₀ = Jfun [ `ℕ ] · $ 7 · const3

F₀ : STerm
F₀ = (Λ (ƛ ` 0 ∙ ` 0)) [ `𝔹 ] · `false

U₀ : STerm
U₀ = (ƛ (`ℕ ⇒ `ℕ) ∙ (` 0 · $ 5)) · ((Λ (ƛ ` 0 ∙ ` 0)) [ `ℕ ])

Qvac Qbody Qfun Q₀ : STerm
Qvac  = Λ (ƛ `ℕ ∙ ` 1)
Qbody = Qvac [ `ℕ ] · $ 0
Qfun  = Λ (ƛ ` 0 ∙ Qbody)
Q₀    = Qfun [ `ℕ ] · $ 7

Dinner Dbody Dfun D₀ : STerm
Dinner = Λ (ƛ `ℕ ∙ ((Λ (ƛ `ℕ ∙ ` 2)) [ `ℕ ] · $ 0))
Dbody  = Dinner [ `ℕ ] · $ 0
Dfun   = Λ (ƛ ` 0 ∙ Dbody)
D₀     = Dfun [ `ℕ ] · $ 7

Lbody Lfun L₀ : STerm
Lbody = Qvac [ ` 0 ] · $ 0
Lfun  = Λ (ƛ ` 0 ∙ Lbody)
L₀    = Lfun [ `ℕ ] · $ 7

Rbody Rfun R₀ : STerm
Rbody = Qfun [ ` 0 ] · ` 0
Rfun  = Λ (ƛ ` 0 ∙ Rbody)
R₀    = Rfun [ `ℕ ] · $ 7

Gpoly Gbody Gfun G₀ : STerm
Gpoly = Λ (Λ (ƛ `ℕ ∙ ` 1))
Gbody = Gpoly [ `ℕ ] [ `ℕ ] · $ 0
Gfun  = Λ (ƛ ` 0 ∙ Gbody)
G₀    = Gfun [ `ℕ ] · $ 7

Hfun H₀ : STerm
Hfun = Λ (ƛ ` 0 ∙ (Λ (ƛ ` 0 ∙ ` 1)))
H₀   = Hfun [ `ℕ ] · $ 7 [ `ℕ ] · $ 5

Earg Ebody Efun E₀ E₀ᴮ : STerm
Earg = Λ (ƛ ` 0 ∙ ` 0)
Ebody = Λ (ƛ `ℕ ∙ (` 1 [ ` 0 ]))
Efun = Λ (ƛ EID ∙ Ebody)
E₀ = Efun [ `ℕ ] · Earg
E₀ᴮ = E₀ [ `𝔹 ] · $ 0 · `true

Vbody Vfun V₀ : STerm
Vbody = Λ (Λ (ƛ `ℕ ∙ (` 1 [ ` 0 ])))
Vfun = Λ (ƛ EID ∙ Vbody)
V₀ = Vfun [ `ℕ ] · Earg [ `𝔹 ] [ `𝔹 ] · $ 0 · `true

I₀ : STerm
I₀ = (Λ (ƛ ` 0 ∙ ` 0)) [ EID ] · Earg [ `𝔹 ] · `true

N₀ : STerm
N₀ = (Λ (ƛ ` 0 ∙
        ((Λ (ƛ ` 0 ∙ ` 0)) [ `∀ (` 0 ⇒ ` 1) ] · (Λ (ƛ ` 0 ∙ ` 1)))))
       [ `ℕ ] · $ 7 [ `𝔹 ] · `true

A₀ : STerm
A₀ = (Λ (ƛ ` 0 ∙ ` 0)) [ `ℕ ⇒ `ℕ ] · (ƛ `ℕ ∙ ` 0) · $ 7

idℕℕ B₀ : STerm
idℕℕ = (Λ (ƛ ` 0 ∙ ` 0)) [ `ℕ ⇒ `ℕ ]
B₀ = idℕℕ · (idℕℕ · (ƛ `ℕ ∙ ` 0)) · $ 7

C₀ : STerm
C₀ = E₀ [ `ℕ ⇒ `ℕ ] · $ 0 · (ƛ `ℕ ∙ ` 0) · $ 7

S₀ : STerm
S₀ = (Λ (ƛ ` 0 ∙
        ((Λ (ƛ `∀ (` 0 ⇒ ` 1) ∙ (` 0 [ `ℕ ] · $ 7))) [ ` 0 ]
          · (Λ (ƛ ` 0 ∙ ` 1)))))
       [ `ℕ ] · $ 7

------------------------------------------------------------------------
-- compile (inferˢ …) is exactly the term Examples runs
------------------------------------------------------------------------

P-compiles : compile (proj₂ (from-just (inferˢ 0 [] P₀))) ≡ E.P₀
P-compiles = refl

K-compiles : compile (proj₂ (from-just (inferˢ 0 [] K₀))) ≡ E.K₀
K-compiles = refl

J-compiles : compile (proj₂ (from-just (inferˢ 0 [] J₀))) ≡ E.J₀
J-compiles = refl

F-compiles : compile (proj₂ (from-just (inferˢ 0 [] F₀))) ≡ E.F₀
F-compiles = refl

U-compiles : compile (proj₂ (from-just (inferˢ 0 [] U₀))) ≡ E.U₀
U-compiles = refl

Q-compiles : compile (proj₂ (from-just (inferˢ 0 [] Q₀))) ≡ E.Q₀
Q-compiles = refl

D-compiles : compile (proj₂ (from-just (inferˢ 0 [] D₀))) ≡ E.D₀
D-compiles = refl

L-compiles : compile (proj₂ (from-just (inferˢ 0 [] L₀))) ≡ E.L₀
L-compiles = refl

R-compiles : compile (proj₂ (from-just (inferˢ 0 [] R₀))) ≡ E.R₀
R-compiles = refl

G-compiles : compile (proj₂ (from-just (inferˢ 0 [] G₀))) ≡ E.G₀
G-compiles = refl

H-compiles : compile (proj₂ (from-just (inferˢ 0 [] H₀))) ≡ E.H₀
H-compiles = refl

E-compiles : compile (proj₂ (from-just (inferˢ 0 [] E₀))) ≡ E.E₀
E-compiles = refl

Eᴮ-compiles : compile (proj₂ (from-just (inferˢ 0 [] E₀ᴮ))) ≡ E.E₀ᴮ
Eᴮ-compiles = refl

V-compiles : compile (proj₂ (from-just (inferˢ 0 [] V₀))) ≡ E.V₀
V-compiles = refl

I-compiles : compile (proj₂ (from-just (inferˢ 0 [] I₀))) ≡ E.I₀
I-compiles = refl

N-compiles : compile (proj₂ (from-just (inferˢ 0 [] N₀))) ≡ E.N₀
N-compiles = refl

A-compiles : compile (proj₂ (from-just (inferˢ 0 [] A₀))) ≡ E.A₀
A-compiles = refl

B-compiles : compile (proj₂ (from-just (inferˢ 0 [] B₀))) ≡ E.B₀
B-compiles = refl

C-compiles : compile (proj₂ (from-just (inferˢ 0 [] C₀))) ≡ E.C₀
C-compiles = refl

S-compiles : compile (proj₂ (from-just (inferˢ 0 [] S₀))) ≡ E.S₀
S-compiles = refl


module strong.notes.probes.V7ArrViewProbe where

-- PROBE (2026-09-13): `preserve-Wrap` is FALSE as the rule stands.
--
--   νΘ,χ[V|c] · W  -→  νΘ,χ[ V · ν∅,-χ[W|c₁] | c₂ ]      arr c = (c₁,c₂)
--
-- The contractum's boundary carries `c₂`, so by `⊢ν` its type is
-- `target c₂`.  The redex's type is the CODOMAIN of `c`'s target.  The rule
-- preserves types only if those agree — and `arr` cannot make them agree,
-- because it reads the syntax alone.
--
-- A conversion is a list of heads terminated by `id T`, and `conv-id`
-- BRIDGES: its source and target are related by `SameTy`, not equal,
-- because a source variable's index counts the REVEALED entries and a
-- boundary's interior reveals one more than its exterior.  When that
-- bridging sits in the TERMINATOR, `arr` throws it away: it returns the
-- head's two components, whose types are stated at the seam, and the
-- re-indexing the terminator performed is lost.
--
-- Below, `c` is well typed AND in normal form, and `arr c`'s covariant
-- component has target `` ` 1 `` where the boundary's exterior type says
-- `` ` 0 ``.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph

-- Two abstract anchors.  The exterior conceals the newer one; the
-- boundary's scope change reveals it.
ΔΘ : Ctxᵗ
ΔΘ = anch concealed abstA ∷ anch revealed abstA ∷ []

Δᵢ : Ctxᵗ
Δᵢ = anch revealed abstA ∷ anch revealed abstA ∷ []

enter : ΔΘ ⊢χ reveal zero ∷ [] ⇒ Δᵢ
enter = scope∷ rev-here scope[]

-- The variable naming anchor 1 is index 1 inside and index 0 outside:
-- that is the re-indexing a reveal performs, and it is what `conv-id`
-- exists to bridge.
inside : Δᵢ ∋n 1 := 1
inside = n-revealed n-here

outside : ΔΘ ∋n zero := 1
outside = n-concealed n-here

bridge : SameTy zero Δᵢ (` 1) ΔΘ (` zero)
bridge = same-free inside outside
           (same-anchor (a-there a-here) (a-there a-here) refl)

-- A reflexive component, stated at the seam (here, the interior).
refl-at-Δᵢ : Δᵢ ⊢ id (` 1) ∶ ` 1 ⇝ ` 1 ⊣ Δᵢ
refl-at-Δᵢ = conv-id (same-free inside inside
                       (same-anchor (a-there a-here) (a-there a-here) refl))
                     refl

-- … and the bridging is done by the TERMINATOR.
conv : Δᵢ ⊢ (id (` 1) ↦ id (` 1)) ∷ᶜ id (` zero ⇒ ` zero)
         ∶ (` 1 ⇒ ` 1) ⇝ (` zero ⇒ ` zero) ⊣ ΔΘ
conv = conv-cons (conv-fun refl-at-Δᵢ refl-at-Δᵢ)
                 (conv-id (same-⇒ bridge bridge) refl)

normal : NF ((id (` 1) ↦ id (` 1)) ∷ᶜ id (` zero ⇒ ` zero))
normal = nf-cons (nf-fun nf-id nf-id) nf-id irr-id

------------------------------------------------------------------------
-- What `arr` returns, and why it is the wrong thing
------------------------------------------------------------------------

split : arr ((id (` 1) ↦ id (` 1)) ∷ᶜ id (` zero ⇒ ` zero))
      ≡ just (id (` 1) , id (` 1))
split = refl

-- The boundary's exterior type is `` ` 0 ⇒ ` 0 ``, so the application
-- `νΘ,χ[V|c] · W` has type `` ` 0 ``.  But the contractum's boundary
-- carries `c₂ = id (` 1)`, whose target — hence, by `⊢ν`, whose type — is
-- `` ` 1 ``.
codomain-of-target : ℕ
codomain-of-target = zero

target-of-c₂ : target (id (` 1)) ≡ ` 1
target-of-c₂ = refl

mismatch : ¬ (target (id (` 1)) ≡ ` zero)
mismatch ()

-- The contravariant side fails for the same reason and in a sharper form:
-- `arr (id (A ⇒ B)) = (id A , id B)` takes both halves from the TARGET,
-- while `c₁` must end at the SOURCE's domain — a type `arr` never sees.

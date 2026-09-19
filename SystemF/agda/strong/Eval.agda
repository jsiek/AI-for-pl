module strong.Eval where

-- Strong System F — THE STEP FUNCTION.
--
-- `step Δ M` searches for a redex in M and returns the contractum
-- TOGETHER WITH its `Δ ⊢ M -→ M′` derivation, or `nothing`.  It takes no
-- typing derivation and does not depend on progress or preservation, so it
-- runs on this branch while the metatheory is still being ported.
--
-- WHY THIS IS NOT A SECOND RULE TABLE.  v2's evaluator WAS progress
-- (`step = progress`), on the argument that a `Maybe`-returning step
-- function is a type-blind transcription of the rules that then needs a
-- `step-sound` theorem tying it back to the relation.  That argument does
-- not apply here: `step` returns the derivation, not the term, so
-- soundness is the type and there is nothing to transcribe and nothing to
-- prove.  What `step` does NOT give is the other half — that a well-typed
-- term is a value or steps.  That is progress, it is still owed, and this
-- module deliberately does not pretend to it: a `nothing` here means only
-- that this function found no redex.
--
-- On a well-typed term, determinism (`det`, strong.Reduction) is what makes
-- "no soundness theorem" enough in practice.  Any redex `step` finds is THE
-- redex, so a run it produces is THE run, and an example has only to say
-- where that run ends (`Reaches`, §10).
--
-- WHERE THE PREMISES COME FROM.  The boundary rules carry side conditions
-- not read off the redex — induced contexts, conversion typing, lookup
-- squares, re-spellings and the representation reading of a type argument.
-- Those are decided by strong.TypeCheck, which returns the ordinary
-- derivations, so this module assumes nothing either.  Name uniqueness is
-- no longer a reduction premise and is not decided here.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.TypeCheck
  using (interior?; conversion?; ∋:=?; read?; convTy?;
         rebase?; respell?; check⊢)

------------------------------------------------------------------------
-- 1. Deciding the classifications the rules guard on
------------------------------------------------------------------------

base? : (A : Ty) → Maybe (Base A)
base? (` X)   = nothing
base? `ℕ      = just base-ℕ
base? `𝔹      = just base-𝔹
base? (A ⇒ B) = nothing
base? (`∀ A)  = nothing

inert? : (c : Conv) → Maybe (Inert c)
inert? (id (` X))   = just I-idv
inert? (id `ℕ)      = nothing
inert? (id `𝔹)      = nothing
inert? (id (A ⇒ B)) = nothing
inert? (id (`∀ A))  = nothing
inert? (seal X)     = just I-seal
inert? (unseal X)   = nothing
inert? (s ↦ t)      = just I-fun
inert? (`∀ s)       = just I-all

-- `V-Λ` carries `Value N` and `V-⟪⟫` carries `Inert c`, so this is a
-- recursion, not a shape test.
value? : (M : Term) → Maybe (Value M)
value? (` x)          = nothing
value? ($ n)          = just V-$
value? `true          = just V-true
value? `false         = just V-false
value? (ƛ A ∙ N)      = just V-ƛ
value? (L · M)        = nothing
value? (L ·[ B , A ]) = nothing
value? (Λ N) with value? N
value? (Λ N) | just v  = just (V-Λ v)
value? (Λ N) | nothing = nothing
value? (M ⟪ Θ , c ⟫) with value? M
value? (M ⟪ Θ , c ⟫) | nothing = nothing
value? (M ⟪ Θ , c ⟫) | just v with inert? c
value? (M ⟪ Θ , c ⟫) | just v | just ic = just (V-⟪⟫ v ic)
value? (M ⟪ Θ , c ⟫) | just v | nothing = nothing

------------------------------------------------------------------------
-- 2. The side conditions the boundary rules carry
------------------------------------------------------------------------

-- `TyPeelR-Λ` asks for three things of the crossed frame and the type
-- argument; `TyPeelR-⟪⟫` asks for those and, since 2026-09-18, for the
-- interior spelling of the annotation it pushes in.
PeelPremises : Ctxᵗ → CtxMorph → Conv → Ty → Set
PeelPremises Δ Θ s A =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Bᵢ ∈ Ty ] Σ[ Bₑ ∈ Ty ] Σ[ R ∈ Ty ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ)
      × (Δ ⊢ᶜ A ~ R))

peelPremises? : (Δ : Ctxᵗ) (Θ : CtxMorph) (s : Conv) (A : Ty)
  → Maybe (PeelPremises Δ Θ s A)
peelPremises? Δ Θ s A with conversion? Δ Θ
peelPremises? Δ Θ s A | nothing = nothing
peelPremises? Δ Θ s A | just (Δᶜ , rel) with convTy? (underΛ Δᶜ) s
peelPremises? Δ Θ s A | just (Δᶜ , rel) | nothing = nothing
peelPremises? Δ Θ s A | just (Δᶜ , rel) | just (Bᵢ , Bₑ , ⊢s)
  with read? (names Δ) A
peelPremises? Δ Θ s A | just (Δᶜ , rel) | just (Bᵢ , Bₑ , ⊢s)
  | nothing = nothing
peelPremises? Δ Θ s A | just (Δᶜ , rel) | just (Bᵢ , Bₑ , ⊢s)
  | just (R , same) = just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same)

-- The wrapper clause's extra two: the interior context and the crossing
-- itself.
BdyPremises : Ctxᵗ → CtxMorph → Ty → Ctxᵗ → Set
BdyPremises Δ Θ Bᵢ Δᶜ =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Bᵢ′ ∈ Ty ]
    ((Δ ⊢ⁱ Θ ⇒ Δᵢ) × SameTy (underΛ Δᵢ) Bᵢ′ (underΛ Δᶜ) Bᵢ)

bdyPremises? : (Δ : Ctxᵗ) (Θ : CtxMorph) (Bᵢ : Ty) (Δᶜ : Ctxᵗ)
  → Maybe (BdyPremises Δ Θ Bᵢ Δᶜ)
bdyPremises? Δ Θ Bᵢ Δᶜ with interior? Δ Θ
bdyPremises? Δ Θ Bᵢ Δᶜ | nothing = nothing
bdyPremises? Δ Θ Bᵢ Δᶜ | just (Δᵢ , ri)
  with rebase? (names (underΛ Δᶜ)) (names (underΛ Δᵢ)) Bᵢ
bdyPremises? Δ Θ Bᵢ Δᶜ | just (Δᵢ , ri) | nothing = nothing
bdyPremises? Δ Θ Bᵢ Δᶜ | just (Δᵢ , ri) | just (Bᵢ′ , sm) =
  just (Δᵢ , Bᵢ′ , ri , sm)

-- `IdPush` re-bases the name it pushes into the merged frame, the same
-- way `TyPeelR-⟪⟫` re-bases its annotation.
PushPremises : Ctxᵗ → CtxMorph → CtxMorph → ℕ → Set
PushPremises Δ Θ₁ Θ₂ X =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ Δ⋉ᶜ ∈ Ctxᵗ ] Σ[ X′ ∈ ℕ ]
    ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
      × (extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
      × SameTy Δ⋉ᶜ (` X′) Δ₁ᶜ (` X))

pushPremises? : (Δ : Ctxᵗ) (Θ₁ Θ₂ : CtxMorph) (X : ℕ)
  → Maybe (PushPremises Δ Θ₁ Θ₂ X)
pushPremises? Δ Θ₁ Θ₂ X with interior? Δ Θ₂
pushPremises? Δ Θ₁ Θ₂ X | nothing = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) with conversion? Δᵢ Θ₁
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | nothing = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  with conversion? (extendReps (binds Θ₂) Δ) (Θ₁ ⋉ Θ₂)
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | nothing = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉)
  with rebase? (names Δ₁ᶜ) (names Δ⋉ᶜ) (` X)
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉) | nothing = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉) | just (` X′ , sm) =
  just (Δᵢ , Δ₁ᶜ , Δ⋉ᶜ , X′ , ri , r₁ , r⋉ , sm)
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉) | just (`ℕ , sm) = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉) | just (`𝔹 , sm) = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉) | just (C ⇒ D , sm) = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ⋉ᶜ , r⋉) | just (`∀ C , sm) = nothing

-- `CancelR`'s inner layer is checked at the MERGED frame's conversion
-- context, so its `mkId` needs the looked-up type spelled there.
MergedPremises : Ctxᵗ → CtxMorph → CtxMorph → Ctxᵗ → Ty → Set
MergedPremises Δ Θ₁ Θ₂ Δᶜ A =
  Σ[ Δ⋉ᶜ ∈ Ctxᵗ ] Σ[ A′ ∈ Ty ]
    ((extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
      × SameTy Δ⋉ᶜ A′ Δᶜ A)

mergedPremises? : (Δ : Ctxᵗ) (Θ₁ Θ₂ : CtxMorph) (Δᶜ : Ctxᵗ) (A : Ty)
  → Maybe (MergedPremises Δ Θ₁ Θ₂ Δᶜ A)
mergedPremises? Δ Θ₁ Θ₂ Δᶜ A
  with conversion? (extendReps (binds Θ₂) Δ) (Θ₁ ⋉ Θ₂)
mergedPremises? Δ Θ₁ Θ₂ Δᶜ A | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ Δᶜ A | just (Δ⋉ᶜ , r⋉)
  with rebase? (names Δᶜ) (names Δ⋉ᶜ) A
mergedPremises? Δ Θ₁ Θ₂ Δᶜ A | just (Δ⋉ᶜ , r⋉) | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ Δᶜ A | just (Δ⋉ᶜ , r⋉) | just (A′ , sm) =
  just (Δ⋉ᶜ , A′ , r⋉ , sm)

-- `Peel`'s crossing premises (2026-09-18).  The morphism's two readings,
-- the DUAL's conversion context — which typing the redex does not supply,
-- so it is built here — and the dual's spelling of the domain half.  The
-- redex fixes only Δ, Θ and `s`.
CrossPremises : Ctxᵗ → CtxMorph → Conv → Set
CrossPremises Δ Θ s =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᵈ ∈ Ctxᵗ ] Σ[ s′ ∈ Conv ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (Δ ⊢ⁱ Θ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ dualMorph Θ ⇒ Δᵈ)
      × SameConv Δᵈ s′ Δᶜ s)

crossPremises? : (Δ : Ctxᵗ) (Θ : CtxMorph) (s : Conv)
  → Maybe (CrossPremises Δ Θ s)
crossPremises? Δ Θ s with conversion? Δ Θ
crossPremises? Δ Θ s | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) with interior? Δ Θ
crossPremises? Δ Θ s | just (Δᶜ , rc) | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri)
  with conversion? Δᵢ (dualMorph Θ)
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri)
  | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri) | just (Δᵈ , rd)
  with respell? (names Δᶜ) (names Δᵈ) s
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri) | just (Δᵈ , rd)
  | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri) | just (Δᵈ , rd)
  | just (s′ , sc) = just (Δᶜ , Δᵢ , Δᵈ , s′ , rc , ri , rd , sc)

-- The looked-up type is an output: the contracta mention it only under
-- `mkId`, which the unifier cannot invert.
CancelPremises : Ctxᵗ → CtxMorph → ℕ → Set
CancelPremises Δ Θ Y =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ A ∈ Ty ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (Δᶜ ∋ Y := A))

cancelPremises? : (Δ : Ctxᵗ) (Θ : CtxMorph) (Y : ℕ)
  → Maybe (CancelPremises Δ Θ Y)
cancelPremises? Δ Θ Y with conversion? Δ Θ
cancelPremises? Δ Θ Y | nothing = nothing
cancelPremises? Δ Θ Y | just (Δᶜ , rel) with ∋:=? Δᶜ Y
cancelPremises? Δ Θ Y | just (Δᶜ , rel) | nothing = nothing
cancelPremises? Δ Θ Y | just (Δᶜ , rel) | just (A , d) =
  just (Δᶜ , A , rel , d)

------------------------------------------------------------------------
-- 3. The redexes, by the shape of the head
------------------------------------------------------------------------

-- An application whose two sides are values.  Matching on the head's
-- VALUE derivation is what refines its shape — and, at a boundary, its
-- conversion, since `Peel` fires only under a `_↦_`.
appRedex : (Δ : Ctxᵗ) {L M : Term} → Value L → Value M
  → Maybe (∃[ N ] (Δ ⊢ L · M -→ N))
appRedex Δ V-ƛ             vM = just (_ , Beta vM)
appRedex Δ (V-⟪⟫ {Θ = Θ} v (I-fun {s = s})) vM
  with crossPremises? Δ Θ s
appRedex Δ (V-⟪⟫ {Θ = Θ} v (I-fun {s = s})) vM
  | just (Δᶜ , Δᵢ , Δᵈ , s′ , rc , ri , rd , sc) =
  just (_ , Peel v vM rc ri rd sc)
appRedex Δ (V-⟪⟫ {Θ = Θ} v (I-fun {s = s})) vM | nothing = nothing
appRedex Δ (V-⟪⟫ v I-idv)  vM = nothing
appRedex Δ (V-⟪⟫ v I-seal) vM = nothing
appRedex Δ (V-⟪⟫ v I-all)  vM = nothing
appRedex Δ (V-Λ v)         vM = nothing
appRedex Δ V-$             vM = nothing
appRedex Δ V-true          vM = nothing
appRedex Δ V-false         vM = nothing

-- A type application whose head is a value.  `canon-∀` says the head is a
-- `Λ`, a `Λ` under one `∀`-conversion boundary, or a tower of them; the
-- three clauses below are `TyBeta`, `TyPeelR-Λ` and `TyPeelR-⟪⟫` in that
-- order.
tyAppRedex : (Δ : Ctxᵗ) {L : Term} (B A : Ty) → Value L
  → Maybe (∃[ N ] (Δ ⊢ L ·[ B , A ] -→ N))
tyAppRedex Δ B A (V-Λ vN) with read? (names Δ) A
tyAppRedex Δ B A (V-Λ vN) | just (R , same) = just (_ , TyBeta vN same)
tyAppRedex Δ B A (V-Λ vN) | nothing = nothing
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-Λ vN) (I-all {s}))
  with peelPremises? Δ Θ s A
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-Λ vN) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same) =
  just (_ , TyPeelR-Λ vN rel ⊢s same)
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-Λ vN) (I-all {s})) | nothing = nothing
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-⟪⟫ vW I-all) (I-all {s}))
  with peelPremises? Δ Θ s A
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-⟪⟫ vW I-all) (I-all {s}))
  | nothing = nothing
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-⟪⟫ vW I-all) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same)
  with bdyPremises? Δ Θ Bᵢ Δᶜ
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-⟪⟫ vW I-all) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same)
  | just (Δᵢ , Bᵢ′ , ri , sm) =
  just (_ , TyPeelR-⟪⟫ vW ri rel ⊢s sm same)
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-⟪⟫ vW I-all) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same) | nothing = nothing
tyAppRedex Δ B A _ = nothing

-- A boundary.  `Drop` fires at a literal under an identity at a base
-- type; `CancelR` and `IdPush` fire at a REVEALING boundary over an inert
-- one, and are told apart by the inner conversion.  Everything else is
-- either a congruence or stuck, which is the caller's business.
bdyRedex : (Δ : Ctxᵗ) (M : Term) (Θ : CtxMorph) (c : Conv)
  → Maybe (∃[ N ] (Δ ⊢ M ⟪ Θ , c ⟫ -→ N))
bdyRedex Δ ($ n) Θ (id A) with base? A
bdyRedex Δ ($ n) Θ (id A) | just b  = just (_ , Drop$ b)
bdyRedex Δ ($ n) Θ (id A) | nothing = nothing
bdyRedex Δ `true  Θ (id `𝔹) = just (_ , Drop-true)
bdyRedex Δ `false Θ (id `𝔹) = just (_ , Drop-false)
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) with value? V
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | nothing = nothing
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  with cancelPremises? Δ Θ Y
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v | nothing = nothing
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) with mergedPremises? Δ Θ₁ Θ Δᶜ A
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) | just (Δ⋉ᶜ , A′ , r⋉ , sm) =
  just (_ , CancelR v r⋉ sm rel d)
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) | nothing = nothing
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) with value? V
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | nothing = nothing
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | just v
  with cancelPremises? Δ Θ Y
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | just v | nothing =
  nothing
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) with pushPremises? Δ Θ₁ Θ X
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d)
  | just (Δᵢ , Δ₁ᶜ , Δ⋉ᶜ , X′ , ri , r₁ , r⋉ , sm) =
  just (_ , IdPush v ri r₁ r⋉ sm rel d)
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) | nothing = nothing
bdyRedex Δ M Θ c = nothing

------------------------------------------------------------------------
-- 4. The step function
------------------------------------------------------------------------

StepResult : Ctxᵗ → Term → Set
StepResult Δ M = ∃[ M′ ] (Δ ⊢ M -→ M′)

-- Leftmost-outermost, with the rules' own `Value` premises deciding where
-- a congruence stops: at each node the head is tried first, and a redex is
-- reported only once every subterm the rule demands to be a value is one.
-- Values do not step (`value-¬step`), so the two never both apply.
step : (Δ : Ctxᵗ) (M : Term) → Maybe (StepResult Δ M)
step Δ (` x)     = nothing
step Δ ($ n)     = nothing
step Δ `true     = nothing
step Δ `false    = nothing
step Δ (ƛ A ∙ N) = nothing
step Δ (Λ N) with step (underΛ Δ) N
step Δ (Λ N) | just (N′ , st) = just (Λ N′ , ξ-Λ st)
step Δ (Λ N) | nothing        = nothing
step Δ (L · M) with step Δ L
step Δ (L · M) | just (L′ , st) = just (L′ · M , ξ-·-l st)
step Δ (L · M) | nothing with value? L
step Δ (L · M) | nothing | nothing = nothing
step Δ (L · M) | nothing | just vL with step Δ M
step Δ (L · M) | nothing | just vL | just (M′ , st) =
  just (L · M′ , ξ-·-r vL st)
step Δ (L · M) | nothing | just vL | nothing with value? M
step Δ (L · M) | nothing | just vL | nothing | nothing = nothing
step Δ (L · M) | nothing | just vL | nothing | just vM =
  appRedex Δ vL vM
step Δ (L ·[ B , A ]) with step Δ L
step Δ (L ·[ B , A ]) | just (L′ , st) =
  just (L′ ·[ B , A ] , ξ-·[] st)
step Δ (L ·[ B , A ]) | nothing with value? L
step Δ (L ·[ B , A ]) | nothing | nothing   = nothing
step Δ (L ·[ B , A ]) | nothing | just vL = tyAppRedex Δ B A vL
step Δ (M ⟪ Θ , c ⟫) with bdyRedex Δ M Θ c
step Δ (M ⟪ Θ , c ⟫) | just r = just r
step Δ (M ⟪ Θ , c ⟫) | nothing with interior? Δ Θ
step Δ (M ⟪ Θ , c ⟫) | nothing | nothing = nothing
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel) with step Δᵢ M
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel) | just (M′ , st) =
  just (M′ ⟪ Θ , c ⟫ , ξ-⟪⟫ rel st)
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel) | nothing = nothing

------------------------------------------------------------------------
-- 5. Reading a step off
------------------------------------------------------------------------

-- The contractum alone, for stating what a recorded trace expects.  The
-- derivation is still what `step` returns; this only forgets it.
stepTo : (Δ : Ctxᵗ) (M : Term) → Maybe Term
stepTo Δ M = map proj₁ (step Δ M)

-- `Steps Δ M N` is what a regression check asserts, and `refl` proves it.
Steps : Ctxᵗ → Term → Term → Set
Steps Δ M N = stepTo Δ M ≡ just N

-- The derivation behind such a check, when a caller wants it rather than
-- the equation.
stepDeriv : ∀ {Δ M} (r : StepResult Δ M) → Δ ⊢ M -→ proj₁ r
stepDeriv r = proj₂ r

------------------------------------------------------------------------
-- 6. Traces
------------------------------------------------------------------------

-- Why the run stopped, said of the state it stopped at.  `no-redex` is
-- the honest one: it is where progress would say something and cannot
-- yet, so the evaluator reports "this search found nothing" rather than
-- claiming the term is stuck.
data Final (M : Term) : Set where
  value       : Value M → Final M
  no-redex    : Final M
  out-of-fuel : Final M

-- A run from M that is supposed to keep the type A.  Each step stores its
-- own derivation AND a typing derivation for the contractum, because
-- `eval` re-checks after every step; `illtyped` records a step whose
-- contractum the checker REJECTED, and is the only way the type can be
-- lost along a trace.
infixr 5 _◅⟨_⟩_
data Trace (Δ : Ctxᵗ) (A : Ty) : Term → Set where
  stop   : ∀ {M} → Final M → Trace Δ A M
  illtyped  : ∀ {M M′} → Δ ⊢ M -→ M′ → Trace Δ A M
  _◅⟨_⟩_ : ∀ {M M′} → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A
    → Trace Δ A M′ → Trace Δ A M

------------------------------------------------------------------------
-- 7. The evaluator
------------------------------------------------------------------------

-- `step ⨟ check⊢`, iterated with fuel.  The type checker is what closes
-- the loop: preservation is not available to retype the contractum, so
-- the contractum is CHECKED instead, at the type the run started with.
--
-- That is not preservation and does not pretend to be — it says nothing
-- about runs it was not pointed at.  What it is, is the executable form
-- of subject reduction, and it is the check that would have caught the
-- `rewind` defect by itself: the eleventh state of the fourth example was
-- the first one `check⊢` would have rejected (notes/DECISIONS.md,
-- 2026-09-17).
eval : ∀ {Δ A} (k : ℕ) (M : Term) → Δ ∣ [] ⊢ M ⦂ A → Trace Δ A M
eval {Δ} {A} zero M ⊢M with value? M
eval {Δ} {A} zero M ⊢M | just v  = stop (value v)
eval {Δ} {A} zero M ⊢M | nothing = stop out-of-fuel
eval {Δ} {A} (suc k) M ⊢M with step Δ M
eval {Δ} {A} (suc k) M ⊢M | nothing with value? M
eval {Δ} {A} (suc k) M ⊢M | nothing | just v  = stop (value v)
eval {Δ} {A} (suc k) M ⊢M | nothing | nothing = stop no-redex
eval {Δ} {A} (suc k) M ⊢M | just (M′ , r) with check⊢ Δ [] M′ A
eval {Δ} {A} (suc k) M ⊢M | just (M′ , r) | just ⊢M′ =
  r ◅⟨ ⊢M′ ⟩ eval k M′ ⊢M′
eval {Δ} {A} (suc k) M ⊢M | just (M′ , r) | nothing = illtyped r

------------------------------------------------------------------------
-- 8. Reading a trace
------------------------------------------------------------------------

traceEnd : ∀ {Δ A M} → Trace Δ A M → Term
traceEnd {M = M} (stop f)            = M
traceEnd         (illtyped {M′ = M′} r) = M′
traceEnd         (r ◅⟨ ⊢M′ ⟩ tr)     = traceEnd tr

-- the states, the first one included
traceTerms : ∀ {Δ A M} → Trace Δ A M → List Term
traceTerms {M = M} (stop f)            = M ∷ []
traceTerms {M = M} (illtyped {M′ = M′} r) = M ∷ M′ ∷ []
traceTerms {M = M} (r ◅⟨ ⊢M′ ⟩ tr)     = M ∷ traceTerms tr

traceLen : ∀ {Δ A M} → Trace Δ A M → ℕ
traceLen (stop f)        = zero
traceLen (illtyped r)       = suc zero
traceLen (r ◅⟨ ⊢M′ ⟩ tr) = suc (traceLen tr)

evalTerms : ∀ {Δ A M} (k : ℕ) → Δ ∣ [] ⊢ M ⦂ A → List Term
evalTerms k ⊢M = traceTerms (eval k _ ⊢M)

------------------------------------------------------------------------
-- 9. What a trace proves
------------------------------------------------------------------------

-- The states really are a run: the `_⊢_-→_` derivations are stored, so
-- this only reassembles them.
trace-sound : ∀ {Δ A M} (tr : Trace Δ A M) → Δ ⊢ M -→* traceEnd tr
trace-sound (stop f)        = done
trace-sound (illtyped r)       = r then done
trace-sound (r ◅⟨ ⊢M′ ⟩ tr) = r then trace-sound tr

eval-sound : ∀ {Δ A M} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → Δ ⊢ M -→* traceEnd (eval k M ⊢M)
eval-sound k ⊢M = trace-sound (eval k _ ⊢M)

-- `Checked tr` is the unit RECORD exactly when no step along `tr` lost the
-- type, so Agda discharges it by eta at a concrete run and an `illtyped`
-- anywhere leaves an unsolvable `⊥`.
Checked : ∀ {Δ A M} → Trace Δ A M → Set
Checked (stop f)        = ⊤
Checked (illtyped r)       = ⊥
Checked (r ◅⟨ ⊢M′ ⟩ tr) = Checked tr

-- SUBJECT REDUCTION, FOR THIS RUN.  Not proved — checked, state by
-- state, by the derivations the trace stores.
trace-⦂ : ∀ {Δ A M} → Δ ∣ [] ⊢ M ⦂ A → (tr : Trace Δ A M)
  → Checked tr → Δ ∣ [] ⊢ traceEnd tr ⦂ A
trace-⦂ ⊢M (stop f)        c = ⊢M
trace-⦂ ⊢M (illtyped r)       ()
trace-⦂ ⊢M (r ◅⟨ ⊢M′ ⟩ tr) c = trace-⦂ ⊢M′ tr c

eval-⦂ : ∀ {Δ A M} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → Checked (eval k M ⊢M) → Δ ∣ [] ⊢ traceEnd (eval k M ⊢M) ⦂ A
eval-⦂ k ⊢M c = trace-⦂ ⊢M (eval k _ ⊢M) c

-- and `Checked` really bites: an `illtyped` trace has no such proof, so
-- the `_` a caller writes for it is a proof only because every state the
-- run passed through was checked.
illtyped-unchecked : ∀ {Δ A M M′} (r : Δ ⊢ M -→ M′)
  → Checked {Δ} {A} (illtyped r) → ⊥
illtyped-unchecked r c = c

------------------------------------------------------------------------
-- 10. What a recorded example asserts
------------------------------------------------------------------------

-- ONE PASS OVER THE RUN.  Agda shares nothing between the occurrences of
-- a term, so a statement that mentions `eval k M ⊢M` three times RUNS THE
-- PROGRAM THREE TIMES — measured, on the 25-step example, at about 0.12s
-- an occurrence.  `report` therefore walks the trace once and returns
-- everything an example asserts about it: where the run ended, how many
-- steps it took, and whether every state kept its type.  `Reaches` then
-- mentions the run ONCE.
--
-- `bump` matches on the triple rather than projecting out of it, which is
-- what keeps that one pass one pass: projections would put three copies
-- of the recursive call back in.  The price is that `report` is stuck on
-- a variable trace, so the two lemmas below have to `with` their way past
-- it; that is paid once, here, and not per example.
-- A DATA type, not a triple: a triple has eta, so comparing one against
-- a literal splits into three independent projections and walks the run
-- three times anyway (measured).  Forcing a datatype to weak head normal
-- form walks it once and leaves the three components computed.
data Report : Set where
  reported : Term → ℕ → Bool → Report

repEnd : Report → Term
repEnd (reported V n b) = V

repKept : Report → Bool
repKept (reported V n b) = b

bump : Report → Report
bump (reported V n b) = reported V (suc n) b

report : ∀ {Δ A M} → Trace Δ A M → Report
report {M = M} (stop f)            = reported M zero true
report         (illtyped {M′ = M′} r) = reported M′ (suc zero) false
report         (r ◅⟨ ⊢M′ ⟩ tr)     = bump (report tr)

report-end : ∀ {Δ A M} (tr : Trace Δ A M)
  → repEnd (report tr) ≡ traceEnd tr
report-end (stop f)  = refl
report-end (illtyped r) = refl
report-end (r ◅⟨ ⊢M′ ⟩ tr) with report tr | report-end tr
report-end (r ◅⟨ ⊢M′ ⟩ tr) | reported V n b | eq = eq

report-kept : ∀ {Δ A M} (tr : Trace Δ A M)
  → repKept (report tr) ≡ true → Checked tr
report-kept (stop f)  eq = tt
report-kept (illtyped r) ()
report-kept (r ◅⟨ ⊢M′ ⟩ tr) eq with report tr | report-kept tr
report-kept (r ◅⟨ ⊢M′ ⟩ tr) eq | reported V n b | h = h eq

-- One statement per example: with fuel `k` the evaluator reaches `V` in
-- exactly `n` steps, no state along the way lost the type, and `V` is a
-- value.  Only the first component mentions the run.
--
-- The intermediate states are deliberately not part of this.  They are
-- what `eval` type-checked on the way — the `true` is the record of that
-- — and `evalTerms` hands them back whenever a reader wants to see one.
-- A RECORD, not a product, so that `k`, `n` and `⊢M` are recoverable
-- from the type: the accessors below are applied to an example's
-- `Reaches` and have to read them off it.
record Reaches {Δ A M} (k n : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A) (V : Term)
  : Set where
  constructor reaches
  field
    ran      : report (eval k M ⊢M) ≡ reported V n true
    endValue : Value V
open Reaches public

-- What an example's `Reaches` yields.  None of these re-runs the program:
-- they are equational, so the trace stays unevaluated.
reaches-end : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → traceEnd (eval k M ⊢M) ≡ V
reaches-end {k = k} {⊢M = ⊢M} r =
  trans (sym (report-end (eval k _ ⊢M))) (cong repEnd (ran r))

reaches-checked : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → Checked (eval k M ⊢M)
reaches-checked {k = k} {⊢M = ⊢M} r =
  report-kept (eval k _ ⊢M) (cong repKept (ran r))

-- The multi-step run, with the endpoint NAMED.  `eval-sound` already
-- gives `Δ ⊢ M -→* traceEnd …`; this is that, with the endpoint read off
-- an equation.
eval-run : ∀ {Δ A M V} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → traceEnd (eval k M ⊢M) ≡ V → Δ ⊢ M -→* V
eval-run k ⊢M refl = eval-sound k ⊢M

-- the run, in the object language's own relation
reaches-run : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → Δ ⊢ M -→* V
reaches-run {k = k} {⊢M = ⊢M} r = eval-run k ⊢M (reaches-end r)

-- and the endpoint's typing: SUBJECT REDUCTION for this run, checked
reaches-⦂ : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → Δ ∣ [] ⊢ V ⦂ A
reaches-⦂ {A = A} {k = k} {⊢M = ⊢M} r =
  subst (λ W → _ ∣ [] ⊢ W ⦂ A) (reaches-end r)
    (eval-⦂ k ⊢M (reaches-checked r))

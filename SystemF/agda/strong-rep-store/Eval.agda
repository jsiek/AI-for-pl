module strong-rep-store.Eval where

-- File Charter:
--   * THE STEP FUNCTION AND THE EVALUATOR BUILT ON IT.  §1 decides the
--     classifications the rules guard on; §2 assembles each boundary
--     rule's side conditions; §3 is the redex search by head shape;
--     §4 `step`, leftmost-outermost, returning the contractum, the
--     allocation and the step derivation; §5 `stepTo`/`Steps`;
--     §6–§7 `Trace` and `eval`; §8–§9 reading a trace; §10 `Report`
--     and `Reaches`.
--   * NO METATHEORY IS NEEDED AND NONE IS CLAIMED.  `step` RETURNS THE
--     DERIVATION, so soundness is its type; a `nothing` means only
--     that this search found no redex — that other half is `progress`.
--   * WHAT A RUN ASSERTS.  `eval` is `step ⨟ check⊢` iterated with
--     fuel: the contractum is CHECKED, not retyped by preservation.
--     `illtyped` is the ONLY way a type is lost along a `Trace`, and
--     `Checked tr` is the unit record exactly when none occurs — so a
--     concrete run's subject reduction is checked, not proved.
-- Commentary: Commentary.md § Eval.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.TypeCheck
  using (interior?; conversion?; ∋:=?; read?; convTy?;
         rebase?; respell?; check⊢; inert?; value?)

------------------------------------------------------------------------
-- 1. Deciding the classifications the rules guard on
------------------------------------------------------------------------

base? : (A : Ty) → Maybe (Base A)
base? (` X)   = nothing
base? `ℕ      = just base-ℕ
base? `𝔹      = just base-𝔹
base? (A ⇒ B) = nothing
base? (`∀ A)  = nothing

-- `inert?` and `value?` live in strong-rep-store.TypeCheck now and are
-- re-exported here through its `open import`.

------------------------------------------------------------------------
-- 2. The side conditions the boundary rules carry
------------------------------------------------------------------------

-- Commentary.md § Eval.agda / §1–§2
PeelPremises : Ctxᵗ → Boundary → Conv → Ty → Set
PeelPremises Δ Θ s A =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Bᵢ ∈ Ty ] Σ[ Bₑ ∈ Ty ] Σ[ R ∈ Ty ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ)
      × (Δ ⊢ᶜ A ~ R))

peelPremises? : (Δ : Ctxᵗ) (Θ : Boundary) (s : Conv) (A : Ty)
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

-- The wrapper clause's remaining premises.  No arithmetic renaming is
-- used for the carried conversion.
BdyPremises : Ctxᵗ → Boundary → Boundary → Conv → Ty → Ty → Ctxᵗ → Set
BdyPremises Δ Θ Θ′ s′ R Bᵢ Δᶜ =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Bᵢ′ ∈ Ty ] Σ[ Δ′ᶜ ∈ Ctxᵗ ] Σ[ Δᵢ⁺ ∈ Ctxᵗ ]
    Σ[ Δ″ᶜ ∈ Ctxᵗ ] Σ[ s″ ∈ Conv ]
      ((Δ ⊢ⁱ Θ ⇒ Δᵢ)
        × (underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ)
        × (Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ)
        × (allocate R Δ ⊢ⁱ inst Θ ⇒ Δᵢ⁺)
        × (Δᵢ⁺ ⊢ᶜ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])) ⇒ Δ″ᶜ)
        × SameConv (underΛ Δ″ᶜ) s″
            (underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)) s′)

bdyPremises? : (Δ : Ctxᵗ) (Θ Θ′ : Boundary) (s′ : Conv)
  (R Bᵢ : Ty) (Δᶜ : Ctxᵗ) → Maybe (BdyPremises Δ Θ Θ′ s′ R Bᵢ Δᶜ)
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ with interior? Δ Θ
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | nothing = nothing
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  with rebase? (names (underΛ Δᶜ)) (names (underΛ Δᵢ)) Bᵢ
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri) | nothing = nothing
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) with conversion? Δᵢ Θ′
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | nothing = nothing
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′)
  with interior? (allocate R Δ) (inst Θ)
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′) | nothing = nothing
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′) | just (Δᵢ⁺ , ri⁺)
  with conversion? Δᵢ⁺ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ []))
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′) | just (Δᵢ⁺ , ri⁺)
  | nothing = nothing
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′) | just (Δᵢ⁺ , ri⁺)
  | just (Δ″ᶜ , r″)
  with respell?
         (names (underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)))
         (names (underΛ Δ″ᶜ)) s′
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′) | just (Δᵢ⁺ , ri⁺)
  | just (Δ″ᶜ , r″) | nothing = nothing
bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ | just (Δᵢ , ri)
  | just (Bᵢ′ , sm) | just (Δ′ᶜ , r′) | just (Δᵢ⁺ , ri⁺)
  | just (Δ″ᶜ , r″) | just (s″ , sc) =
  just (Δᵢ , Bᵢ′ , Δ′ᶜ , Δᵢ⁺ , Δ″ᶜ , s″
       , ri , sm , r′ , ri⁺ , r″ , sc)

-- `IdPush` re-bases the name it pushes into the merged frame, the same
-- way `TyPeelR-⟪⟫` re-bases its annotation.
PushPremises : Ctxᵗ → Boundary → Boundary → ℕ → Set
PushPremises Δ Θ₁ Θ₂ X =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ Δ⋉ᶜ ∈ Ctxᵗ ] Σ[ X′ ∈ ℕ ]
    ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
      × (Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ)
      × (Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ))

pushPremises? : (Δ : Ctxᵗ) (Θ₁ Θ₂ : Boundary) (X : ℕ)
  → Maybe (PushPremises Δ Θ₁ Θ₂ X)
pushPremises? Δ Θ₁ Θ₂ X with interior? Δ Θ₂
pushPremises? Δ Θ₁ Θ₂ X | nothing = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) with conversion? Δᵢ Θ₁
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | nothing = nothing
pushPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  with conversion? Δ (Θ₁ ++ Θ₂)
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
-- context.  Repaired 2026-09-19: the re-spelled type is the cancelled
-- `seal X`'s OWN source, read at Θ₁'s conversion context.
MergedPremises : Ctxᵗ → Boundary → Boundary → ℕ → Set
MergedPremises Δ Θ₁ Θ₂ X =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ Aᵢ ∈ Ty ]
    Σ[ Δ⋉ᶜ ∈ Ctxᵗ ] Σ[ A′ ∈ Ty ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
        × (Δ₁ᶜ ∋ X := Aᵢ)
        × (Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ)
        × (Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ))

mergedPremises? : (Δ : Ctxᵗ) (Θ₁ Θ₂ : Boundary) (X : ℕ)
  → Maybe (MergedPremises Δ Θ₁ Θ₂ X)
mergedPremises? Δ Θ₁ Θ₂ X with interior? Δ Θ₂
mergedPremises? Δ Θ₁ Θ₂ X | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri)
  with conversion? Δᵢ Θ₁
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  with ∋:=? Δ₁ᶜ X
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Aᵢ , d₁)
  with conversion? Δ (Θ₁ ++ Θ₂)
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Aᵢ , d₁) | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Aᵢ , d₁) | just (Δ⋉ᶜ , r⋉)
  with rebase? (names Δ₁ᶜ) (names Δ⋉ᶜ) Aᵢ
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Aᵢ , d₁) | just (Δ⋉ᶜ , r⋉) | nothing = nothing
mergedPremises? Δ Θ₁ Θ₂ X | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Aᵢ , d₁) | just (Δ⋉ᶜ , r⋉) | just (A′ , sm) =
  just (Δᵢ , Δ₁ᶜ , Aᵢ , Δ⋉ᶜ , A′
       , ri , r₁ , d₁ , r⋉ , sm)

-- `Peel`'s crossing premises (2026-09-18).  The redex fixes only Δ, Θ
-- and `s`; the dual's conversion context is built here.
CrossPremises : Ctxᵗ → Boundary → Conv → Set
CrossPremises Δ Θ s =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᵈ ∈ Ctxᵗ ] Σ[ s′ ∈ Conv ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (Δ ⊢ⁱ Θ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ)
      × SameConv Δᵈ s′ Δᶜ s)

crossPremises? : (Δ : Ctxᵗ) (Θ : Boundary) (s : Conv)
  → Maybe (CrossPremises Δ Θ s)
crossPremises? Δ Θ s with conversion? Δ Θ
crossPremises? Δ Θ s | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) with interior? Δ Θ
crossPremises? Δ Θ s | just (Δᶜ , rc) | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri)
  with conversion? Δᵢ (dual Θ)
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
CancelPremises : Ctxᵗ → Boundary → ℕ → Set
CancelPremises Δ Θ Y =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ A ∈ Ty ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (Δᶜ ∋ Y := A))

cancelPremises? : (Δ : Ctxᵗ) (Θ : Boundary) (Y : ℕ)
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
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ L · M -→ N ∣ δ))
appRedex Δ V-ƛ             vM = just (_ , none , Beta vM)
appRedex Δ (V-⟪⟫ {Θ = Θ} v (I-fun {s = s})) vM
  with crossPremises? Δ Θ s
appRedex Δ (V-⟪⟫ {Θ = Θ} v (I-fun {s = s})) vM
  | just (Δᶜ , Δᵢ , Δᵈ , s′ , rc , ri , rd , sc) =
  just (_ , none , Peel v vM rc ri rd sc)
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
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ L ·[ B , A ] -→ N ∣ δ))
tyAppRedex Δ B A (V-Λ vN) with read? (names Δ) A
tyAppRedex Δ B A (V-Λ vN) | just (R , same) =
  just (_ , new R , TyBeta vN same)
tyAppRedex Δ B A (V-Λ vN) | nothing = nothing
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-Λ vN) (I-all {s}))
  with peelPremises? Δ Θ s A
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-Λ vN) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same) =
  just (_ , new R , TyPeelR-Λ vN rel ⊢s same)
tyAppRedex Δ B A (V-⟪⟫ {Θ = Θ} (V-Λ vN) (I-all {s})) | nothing = nothing
tyAppRedex Δ B A
  (V-⟪⟫ {Θ = Θ} (V-⟪⟫ {Θ = Θ′} vW (I-all {s = s′})) (I-all {s}))
  with peelPremises? Δ Θ s A
tyAppRedex Δ B A
  (V-⟪⟫ {Θ = Θ} (V-⟪⟫ {Θ = Θ′} vW (I-all {s = s′})) (I-all {s}))
  | nothing = nothing
tyAppRedex Δ B A
  (V-⟪⟫ {Θ = Θ} (V-⟪⟫ {Θ = Θ′} vW (I-all {s = s′})) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same)
  with bdyPremises? Δ Θ Θ′ s′ R Bᵢ Δᶜ
tyAppRedex Δ B A
  (V-⟪⟫ {Θ = Θ} (V-⟪⟫ {Θ = Θ′} vW (I-all {s = s′})) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same)
  | just (Δᵢ , Bᵢ′ , Δ′ᶜ , Δᵢ⁺ , Δ″ᶜ , s″
         , ri , sm , r′ , ri⁺ , r″ , sc) =
  just (_ , new R , TyPeelR-⟪⟫ vW ri rel r′ ri⁺ r″ sc ⊢s sm same)
tyAppRedex Δ B A
  (V-⟪⟫ {Θ = Θ} (V-⟪⟫ {Θ = Θ′} vW (I-all {s = s′})) (I-all {s}))
  | just (Δᶜ , Bᵢ , Bₑ , R , rel , ⊢s , same) | nothing = nothing
tyAppRedex Δ B A _ = nothing

-- A boundary.  `Drop` fires at a literal under an identity at a base
-- type; `CancelR` and `IdPush` fire at a REVEALING boundary over an inert
-- one, and are told apart by the inner conversion.  Everything else is
-- either a congruence or stuck, which is the caller's business.
bdyRedex : (Δ : Ctxᵗ) (M : Term) (Θ : Boundary) (c : Conv)
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ M ⟪ Θ , c ⟫ -→ N ∣ δ))
bdyRedex Δ ($ n) Θ (id A) with base? A
bdyRedex Δ ($ n) Θ (id A) | just b  = just (_ , none , Drop$ b)
bdyRedex Δ ($ n) Θ (id A) | nothing = nothing
bdyRedex Δ `true  Θ (id `𝔹) = just (_ , none , Drop-true)
bdyRedex Δ `false Θ (id `𝔹) = just (_ , none , Drop-false)
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) with value? V
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | nothing = nothing
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  with cancelPremises? Δ Θ Y
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v | nothing = nothing
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) with mergedPremises? Δ Θ₁ Θ X
bdyRedex Δ (V ⟪ Θ₁ , seal X ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d)
  | just (Δᵢ , Δ₁ᶜ , Aᵢ , Δ⋉ᶜ , A′
         , ri , r₁ , d₁ , r⋉ , sm) =
  just (_ , none , CancelR v ri r₁ d₁ r⋉ sm rel d)
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
  just (_ , none , IdPush v ri r₁ r⋉ sm rel d)
bdyRedex Δ (V ⟪ Θ₁ , id (` X) ⟫) Θ (unseal Y) | just v
  | just (Δᶜ , A , rel , d) | nothing = nothing
bdyRedex Δ M Θ c = nothing

------------------------------------------------------------------------
-- 4. The step function
------------------------------------------------------------------------

StepResult : Ctxᵗ → Term → Set
StepResult Δ M = ∃[ M′ ] ∃[ δ ] (Δ ⊢ M -→ M′ ∣ δ)

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
step Δ (Λ N)     = nothing        -- no ξ-Λ: a type abstraction is a value
step Δ (L · M) with step Δ L
step Δ (L · M) | just (L′ , δ , st) =
  just (L′ · ↑ᴹ[ δ ] M , δ , ξ-·-l st)
step Δ (L · M) | nothing with value? L
step Δ (L · M) | nothing | nothing = nothing
step Δ (L · M) | nothing | just vL with step Δ M
step Δ (L · M) | nothing | just vL | just (M′ , δ , st) =
  just (↑ᴹ[ δ ] L · M′ , δ , ξ-·-r vL st)
step Δ (L · M) | nothing | just vL | nothing with value? M
step Δ (L · M) | nothing | just vL | nothing | nothing = nothing
step Δ (L · M) | nothing | just vL | nothing | just vM =
  appRedex Δ vL vM
step Δ (L ·[ B , A ]) with step Δ L
step Δ (L ·[ B , A ]) | just (L′ , δ , st) =
  just (L′ ·[ B , A ] , δ , ξ-·[] st)
step Δ (L ·[ B , A ]) | nothing with value? L
step Δ (L ·[ B , A ]) | nothing | nothing   = nothing
step Δ (L ·[ B , A ]) | nothing | just vL = tyAppRedex Δ B A vL
step Δ (M ⟪ Θ , c ⟫) with bdyRedex Δ M Θ c
step Δ (M ⟪ Θ , c ⟫) | just r = just r
step Δ (M ⟪ Θ , c ⟫) | nothing with interior? Δ Θ
step Δ (M ⟪ Θ , c ⟫) | nothing | nothing = nothing
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel) with step Δᵢ M
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel)
  | just (M′ , δ , st) =
  just (M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ , δ , ξ-⟪⟫ rel st)
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
stepDeriv : ∀ {Δ M} (r : StepResult Δ M)
  → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
stepDeriv r = proj₂ (proj₂ r)

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
  illtyped  : ∀ {M M′ δ} → Δ ⊢ M -→ M′ ∣ δ → Trace Δ A M
  _◅⟨_⟩_ : ∀ {M M′ δ} → Δ ⊢ M -→ M′ ∣ δ
    → apply δ Δ ∣ [] ⊢ M′ ⦂ A
    → Trace (apply δ Δ) A M′
    → Trace Δ A M

------------------------------------------------------------------------
-- 7. The evaluator
------------------------------------------------------------------------

-- `step ⨟ check⊢`, iterated with fuel.  The contractum is CHECKED, not
-- retyped by preservation — the executable form of subject reduction.
-- Commentary.md § Eval.agda / What a run asserts
eval : ∀ {Δ A} (k : ℕ) (M : Term) → Δ ∣ [] ⊢ M ⦂ A → Trace Δ A M
eval {Δ} {A} zero M ⊢M with value? M
eval {Δ} {A} zero M ⊢M | just v  = stop (value v)
eval {Δ} {A} zero M ⊢M | nothing = stop out-of-fuel
eval {Δ} {A} (suc k) M ⊢M with step Δ M
eval {Δ} {A} (suc k) M ⊢M | nothing with value? M
eval {Δ} {A} (suc k) M ⊢M | nothing | just v  = stop (value v)
eval {Δ} {A} (suc k) M ⊢M | nothing | nothing = stop no-redex
eval {Δ} {A} (suc k) M ⊢M | just (M′ , δ , r)
  with check⊢ (apply δ Δ) [] M′ A
eval {Δ} {A} (suc k) M ⊢M | just (M′ , δ , r) | just ⊢M′ =
  r ◅⟨ ⊢M′ ⟩ eval k M′ ⊢M′
eval {Δ} {A} (suc k) M ⊢M | just (M′ , δ , r) | nothing = illtyped r

------------------------------------------------------------------------
-- 8. Reading a trace
------------------------------------------------------------------------

traceEnd : ∀ {Δ A M} → Trace Δ A M → Term
traceEnd {M = M} (stop f)            = M
traceEnd         (illtyped {M′ = M′} r) = M′
traceEnd         (r ◅⟨ ⊢M′ ⟩ tr)     = traceEnd tr

-- The context in which the final state lives.  Allocating steps change this
-- index even though the trace itself remains a run from its initial context.
traceCtx : ∀ {Δ A M} → Trace Δ A M → Ctxᵗ
traceCtx {Δ = Δ} (stop f) = Δ
traceCtx {Δ = Δ} (illtyped {δ = δ} r) = apply δ Δ
traceCtx (r ◅⟨ ⊢M′ ⟩ tr) = traceCtx tr

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
  → Checked tr → traceCtx tr ∣ [] ⊢ traceEnd tr ⦂ A
trace-⦂ ⊢M (stop f)        c = ⊢M
trace-⦂ ⊢M (illtyped r)       ()
trace-⦂ ⊢M (r ◅⟨ ⊢M′ ⟩ tr) c = trace-⦂ ⊢M′ tr c

eval-⦂ : ∀ {Δ A M} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → Checked (eval k M ⊢M)
  → traceCtx (eval k M ⊢M) ∣ [] ⊢ traceEnd (eval k M ⊢M) ⦂ A
eval-⦂ k ⊢M c = trace-⦂ ⊢M (eval k _ ⊢M) c

-- and `Checked` really bites: an `illtyped` trace has no such proof, so
-- the `_` a caller writes for it is a proof only because every state the
-- run passed through was checked.
illtyped-unchecked : ∀ {Δ A M M′ δ} (r : Δ ⊢ M -→ M′ ∣ δ)
  → Checked {Δ} {A} (illtyped r) → ⊥
illtyped-unchecked r c = c

------------------------------------------------------------------------
-- 10. What a recorded example asserts
------------------------------------------------------------------------

-- ONE PASS OVER THE RUN: Agda shares nothing between occurrences of a
-- term, so `report` walks the trace once and `Reaches` mentions the run
-- ONCE.  `bump` matches on the triple rather than projecting out of it,
-- and `Report` is a DATA type rather than a triple, for the same reason.
-- Commentary.md § Eval.agda / §10
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
-- exactly `n` steps, no state lost the type, and `V` is a value.  A
-- RECORD, so that `k`, `n` and `⊢M` are recoverable from the type.
-- Commentary.md § Eval.agda / §10
record Reaches {Δ A M} (k n : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A) (V : Term)
  : Set where
  constructor reaches
  field
    ran      : report (eval k M ⊢M) ≡ reported V n true
    endValue : Value V
open Reaches public

-- What an example's `Reaches` yields.  None of these re-runs the term.
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
  → Reaches k n ⊢M V
  → traceCtx (eval k M ⊢M) ∣ [] ⊢ V ⦂ A
reaches-⦂ {A = A} {k = k} {⊢M = ⊢M} r =
  subst (λ W → _ ∣ [] ⊢ W ⦂ A) (reaches-end r)
    (eval-⦂ k ⊢M (reaches-checked r))

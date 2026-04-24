{-# OPTIONS --allow-unsolved-metas #-}

module Parametricity where

-- File Charter:
--   * Decomposes the fundamental theorem into compatibility lemmas,
--   * following the style used in `SystemF/agda/extrinsic/Parametricity.agda`.
--   * Provides a recursive proof skeleton of `fundamental` by induction on
--   * term precision derivations.
--   * Keeps hard compatibility cases postulated for now, while exposing the
--   * final theorem with the intended interface.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; length)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Level using (lift)
open import Types
open import Imprecision
open import UpDown
open import Terms
open import Data.Product using (_,_; proj₁; proj₂)
open import TermPrecision
open import TermProperties using (substˣ-term)
open import ReductionFresh using (Value; _∣_—↠_∣_; _∎) renaming ($ to v$)
open import LogicalRelation

postulate
  𝒢-lookup :
    ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
    Γ ∋ₚ x ⦂ (A , B , p) →
    𝒢 Γ (suc n) dir w ρ γ →
    𝒱 (substᴿ-⊑ ρ p) n dir w (leftˣ γ x) (rightˣ γ x)

  𝒢-lookup-substᵗ :
    ∀ {Γ x A B} {p : A ⊑ B} {n dir w} {ρ : RelSub 0} {γ} →
    Γ ∋ₚ x ⦂ (A , B , p) →
    𝒢 Γ (suc n) dir w ρ γ →
    𝒱 (substᴿ-⊑ ρ p) n dir w
      (substᵗᵐ (leftᵗ ρ) (leftˣ γ x))
      (substᵗᵐ (rightᵗ ρ) (rightˣ γ x))
  
  const-𝒱 :
    ∀ {n dir w m} →
    𝒱 (⊑-‵ `ℕ) n dir w ($ (κℕ m)) ($ (κℕ m))

  compat-var :
    ∀ {Γ dir x A B} {p : A ⊑ B} →
    Γ ∋ₚ x ⦂ (A , B , p) →
    Γ ∣ dir ⊨ (` x) ⊑ (` x) ⦂ p

  compat-$ :
    ∀ {E dir n} →
    TPEnv.Γ E ∣ dir ⊨ ($ (κℕ n)) ⊑ ($ (κℕ n)) ⦂ (⊑-‵ `ℕ)

postulate
  compat-ƛ :
    ∀ {E dir A A′ B B′ M M′} {pA : A ⊑ A′} {pB : B ⊑ B′} →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) A′ →
    TPEnv.Γ (extendᴾ E (A , A′ , pA)) ∣ dir ⊨ M ⊑ M′ ⦂ pB →
    TPEnv.Γ E ∣ dir ⊨ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′) ⦂ (⊑-⇒ A A′ B B′ pA pB)

  compat-· :
    ∀ {E dir A A′ B B′ L L′ M M′} {pA : A ⊑ A′} {pB : B ⊑ B′} →
    TPEnv.Γ E ∣ dir ⊨ L ⊑ L′ ⦂ (⊑-⇒ A A′ B B′ pA pB) →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.Γ E ∣ dir ⊨ (L · M) ⊑ (L′ · M′) ⦂ pB

  compat-Λ :
    ∀ {E dir A B M M′} {p : A ⊑ B} →
    TPEnv.Γ (⇑ᵗᴱ E) ∣ dir ⊨ M ⊑ M′ ⦂ p →
    TPEnv.Γ E ∣ dir ⊨ (Λ M) ⊑ (Λ M′) ⦂ (⊑-∀ A B p)

  compat-⦂∀ :
    ∀ {E dir A B M M′ T} {p : A ⊑ B} →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-∀ A B p) →
    WfTy (TPEnv.Δ E) (TPEnv.Ψ E) T →
    TPEnv.Γ E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ (M′ ⦂∀ B [ T ]) ⦂ substᵗ-⊑ (singleTyEnv T) p

  compat-⦂∀-ν :
    ∀ (A B : Ty) {E dir M M′ T} (p : ((⇑ˢ A) [ α₀ ]ᵗ ⊑ ⇑ˢ B)) →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-ν A B p) →
    (hT : WfTy 0 (TPEnv.Ψ E) T) →
    TPEnv.Γ E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ ν-inst-⊑ A B T hT p

  compat-⊕ :
    ∀ {E dir L L′ M M′} {op : Prim} →
    TPEnv.Γ E ∣ dir ⊨ L ⊑ L′ ⦂ (⊑-‵ `ℕ) →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑-‵ `ℕ) →
    TPEnv.Γ E ∣ dir ⊨ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′) ⦂ (⊑-‵ `ℕ)

  compat-up :
    ∀ {E dir M M′ A A′ B B′} {pA : A ⊑ A′} {pB : B ⊑ B′} {u : Up} {u′ : Up} →
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.store E ∣ Φ ⊢ u ⦂ A ⊑ B →
    TPEnv.store E ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    TPEnv.Γ E ∣ dir ⊨ (M up u) ⊑ (M′ up u′) ⦂ pB

  compat-upL :
    ∀ {E dir M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {u : Up} →
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.store E ∣ Φ ⊢ u ⦂ A ⊑ B →
    TPEnv.Γ E ∣ dir ⊨ (M up u) ⊑ M′ ⦂ pB

  compat-upR :
    ∀ {E dir M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {u′ : Up} →
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.store E ∣ Φ ⊢ u′ ⦂ A′ ⊑ B′ →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ (M′ up u′) ⦂ pB

  compat-down :
    ∀ {E dir M M′ A A′ B B′} {pA : A ⊑ A′} {pB : B ⊑ B′} {d : Down} {d′ : Down} →
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.store E ∣ Φ ⊢ d ⦂ A ⊒ B →
    TPEnv.store E ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    TPEnv.Γ E ∣ dir ⊨ (M down d) ⊑ (M′ down d′) ⦂ pB

  compat-downL :
    ∀ {E dir M M′ A A′ B} {pA : A ⊑ A′} {pB : B ⊑ A′} {d : Down} →
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.store E ∣ Φ ⊢ d ⦂ A ⊒ B →
    TPEnv.Γ E ∣ dir ⊨ (M down d) ⊑ M′ ⦂ pB

  compat-downR :
    ∀ {E dir M M′ A A′ B′} {pA : A ⊑ A′} {pB : A ⊑ B′} {d′ : Down} →
    (Φ : List CastPerm) →
    length Φ ≡ TPEnv.Ψ E →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ pA →
    TPEnv.store E ∣ Φ ⊢ d′ ⦂ A′ ⊒ B′ →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ (M′ down d′) ⦂ pB

  compat-blameR :
    ∀ {E dir M A B ℓ} {p : A ⊑ B} →
    TPEnv.Δ E ∣ TPEnv.Ψ E ∣ TPEnv.store E ∣ leftCtx (TPEnv.Γ E) ⊢ M ⦂ A →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ (blame ℓ) ⦂ p

fundamental :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ p
fundamental {E = E} {p = p} dir (⊑` {x = x} x∈) =
  compat-var {Γ = TPEnv.Γ E} {dir = dir} {x = x} {p = p} x∈
fundamental {E = E} dir
  (⊑ƛ {A = A} {A′ = A′} {B = B} {B′ = B′} {M = M} {M′ = M′}
      {pA = pA} {pB = pB} hA hA′ rel) =
  compat-ƛ {E = E} {dir = dir} {A = A} {A′ = A′} {B = B} {B′ = B′}
    {M = M} {M′ = M′} {pA = pA} {pB = pB} hA hA′
    (fundamental {E = extendᴾ E (A , A′ , pA)} {M = M} {M′ = M′} {p = pB} dir rel)
fundamental {E = E} dir
  (⊑· {A = A} {A′ = A′} {B = B} {B′ = B′}
      {L = L} {L′ = L′} {M = M} {M′ = M′} {pA = pA} {pB = pB}
      relL relM) =
  compat-· {E = E} {dir = dir} {A = A} {A′ = A′} {B = B} {B′ = B′}
    {L = L} {L′ = L′} {M = M} {M′ = M′} {pA = pA} {pB = pB}
    (fundamental {E = E} {M = L} {M′ = L′} {p = ⊑-⇒ A A′ B B′ pA pB} dir relL)
    (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir relM)
fundamental {E = E} dir (⊑Λ {A = A} {B = B} {M = M} {M′ = M′} {p = p} rel) =
  compat-Λ {E = E} {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {p = p}
    (fundamental {E = ⇑ᵗᴱ E} {M = M} {M′ = M′} {p = p} dir rel)
fundamental {E = E} dir (⊑⦂∀ {A = A} {B = B} {M = M} {M′ = M′} {T = T} {p = p} rel hT) =
  compat-⦂∀ {E = E} {dir = dir} {A = A} {B = B} {M = M} {M′ = M′} {T = T} {p = p}
    (fundamental {E = E} {M = M} {M′ = M′} {p = ⊑-∀ A B p} dir rel) hT
fundamental {E = E} dir (⊑⦂∀-ν A B {M = M} {M′ = M′} {T = T} p rel hT) =
  compat-⦂∀-ν A B {E = E} {dir = dir} {M = M} {M′ = M′} {T = T} p
    (fundamental {E = E} {M = M} {M′ = M′} {p = ⊑-ν A B p} dir rel)
    hT
fundamental {E = E} dir (⊑$ {n}) = compat-$ {E = E} {dir = dir} {n = n}
fundamental {E = E} dir (⊑⊕ {L = L} {L′ = L′} {M = M} {M′ = M′} {op = op} relL relM) =
  compat-⊕ {E = E} {dir = dir} {L = L} {L′ = L′} {M = M} {M′ = M′} {op = op}
    (fundamental {E = E} {M = L} {M′ = L′} {p = ⊑-‵ `ℕ} dir relL)
    (fundamental {E = E} {M = M} {M′ = M′} {p = ⊑-‵ `ℕ} dir relM)
fundamental {E = E} dir
  (⊑up {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
      {pA = pA} {pB = pB} {u = u} {u′ = u′} Φ lenΦ rel hu hu′) =
  compat-up {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {pA = pA} {pB = pB} {u = u} {u′ = u′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hu hu′
fundamental {E = E} dir
  (⊑upL {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B}
      {pA = pA} {pB = pB} {u = u} Φ lenΦ rel hu) =
  compat-upL {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {pA = pA} {pB = pB} {u = u}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hu
fundamental {E = E} dir
  (⊑upR {M = M} {M′ = M′} {A = A} {A′ = A′} {B′ = B′}
      {pA = pA} {pB = pB} {u′ = u′} Φ lenΦ rel hu′) =
  compat-upR {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B′ = B′} {pA = pA} {pB = pB} {u′ = u′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hu′
fundamental {E = E} dir
  (⊑down {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B} {B′ = B′}
      {pA = pA} {pB = pB} {d = d} {d′ = d′} Φ lenΦ rel hd hd′) =
  compat-down {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {B′ = B′} {pA = pA} {pB = pB} {d = d} {d′ = d′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hd hd′
fundamental {E = E} dir
  (⊑downL {M = M} {M′ = M′} {A = A} {A′ = A′} {B = B}
      {pA = pA} {pB = pB} {d = d} Φ lenΦ rel hd) =
  compat-downL {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B = B} {pA = pA} {pB = pB} {d = d}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hd
fundamental {E = E} dir
  (⊑downR {M = M} {M′ = M′} {A = A} {A′ = A′} {B′ = B′}
      {pA = pA} {pB = pB} {d′ = d′} Φ lenΦ rel hd′) =
  compat-downR {E = E} {dir = dir} {M = M} {M′ = M′} {A = A} {A′ = A′}
    {B′ = B′} {pA = pA} {pB = pB} {d′ = d′}
    Φ lenΦ (fundamental {E = E} {M = M} {M′ = M′} {p = pA} dir rel) hd′
fundamental {E = E} {M = M} {A = A} {B = B} {p = p} dir (⊑blameR {ℓ = ℓ} hM) =
  compat-blameR {E = E} {dir = dir} {M = M} {A = A} {B = B} {ℓ = ℓ} {p = p} hM

fundamental-⊨ :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Γ E ⊨ M ⊑ M′ ⦂ p
fundamental-⊨ rel = (fundamental ≼ rel) , (fundamental ≽ rel)

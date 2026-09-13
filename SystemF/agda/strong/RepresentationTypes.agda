module strong.RepresentationTypes where

-- Strong System F v7 — representation types.
--
-- Anchor variables inhabit their own de Bruijn universe.  In particular,
-- `α n` is never a source type variable ` n` from strong.Types.

open import Data.Nat using (ℕ; zero; suc)

Anchor : Set
Anchor = ℕ

infixr 7 _⇒ᴿ_
infix 6 `∀ᴿ

data RepTy : Set where
  `α   : Anchor → RepTy
  `ℕᴿ  : RepTy
  `𝔹ᴿ  : RepTy
  _⇒ᴿ_ : RepTy → RepTy → RepTy
  `∀ᴿ  : RepTy → RepTy

Renameᴿ : Set
Renameᴿ = Anchor → Anchor

Substᴿ : Set
Substᴿ = Anchor → RepTy

renᴿ : Renameᴿ → Substᴿ
renᴿ ρ α = `α (ρ α)

extᴿ : Renameᴿ → Renameᴿ
extᴿ ρ zero    = zero
extᴿ ρ (suc α) = suc (ρ α)

renameᴿ : Renameᴿ → RepTy → RepTy
renameᴿ ρ (`α α)   = `α (ρ α)
renameᴿ ρ `ℕᴿ      = `ℕᴿ
renameᴿ ρ `𝔹ᴿ      = `𝔹ᴿ
renameᴿ ρ (R ⇒ᴿ S) = renameᴿ ρ R ⇒ᴿ renameᴿ ρ S
renameᴿ ρ (`∀ᴿ R)  = `∀ᴿ (renameᴿ (extᴿ ρ) R)

⇑ᴿ : RepTy → RepTy
⇑ᴿ = renameᴿ suc

extsᴿ : Substᴿ → Substᴿ
extsᴿ σ zero    = `α zero
extsᴿ σ (suc α) = ⇑ᴿ (σ α)

substᴿ : Substᴿ → RepTy → RepTy
substᴿ σ (`α α)   = σ α
substᴿ σ `ℕᴿ      = `ℕᴿ
substᴿ σ `𝔹ᴿ      = `𝔹ᴿ
substᴿ σ (R ⇒ᴿ S) = substᴿ σ R ⇒ᴿ substᴿ σ S
substᴿ σ (`∀ᴿ R)  = `∀ᴿ (substᴿ (extsᴿ σ) R)

shiftByᴿ : ℕ → RepTy → RepTy
shiftByᴿ zero    R = R
shiftByᴿ (suc n) R = shiftByᴿ n (⇑ᴿ R)

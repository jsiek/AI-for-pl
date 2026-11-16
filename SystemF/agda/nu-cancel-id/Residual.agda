module nu-cancel-id.Residual where

-- File Charter:
--   * ONE-HOLE TERM CONTEXTS, THE SCOPE MAP AT A HOLE, AND RESIDUALS:
--     the layer nu-cancel-id.ColorPreservation is stated in, after
--     strong-rep-nu.Residual.
--   * §1 `TermCtx`/`plug`.  §2 the flags at a hole (`holeFlags`) and
--     the scope map they give (`names`): under the naming condition a
--     hole's scope map is determined by WHICH cells are named there, so
--     the map is the list of named cells, newest first.  §3 renaming a
--     context (`renCtx`/`holeᴿ`) and the sibling shift
--     (`↑ᶜ`/`↑ᴴ`/`↑ʳ`).  §4 Beta's substitution through a context, and
--     the copies of the argument (`cross`).  §5 TyBeta's instantiation
--     on contexts.  §6 `Residual`, one step.  §7 `Residuals`, a run.
--   * WHAT A RESIDUAL RECORDS.  A position is a pair `(C , M)`.  A
--     residual of a step moves the node `M` in hole `C` to hole `D` as
--     `N`, and `ρ` is the representation renaming that reaches the hole:
--     the identity, except in a sibling of an allocation and in a copy
--     that `crossΛ` moved under a `Λ`.
--   * THE REDEX'S OWN NODES ARE CONSUMED (Id's constant with its
--     layer); a substituted variable's position becomes the copy's.
--   * proof/Residual.agda shows that every residual is a position of
--     the contractum (`residual-sound`).  This module proves nothing.

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction

private
  variable
    Γ : Ctx
    s : Sign
    α β j k : ℕ
    A P : Ty
    c d : Conv
    ρ ρ′ : Renameᵗ
    a : Alloc
    L N O W : Term

------------------------------------------------------------------------
-- 1. One-hole contexts
------------------------------------------------------------------------

infixl 7 _·L_ _·R_
infix  5 ƛC_∙_ ΛC_

data TermCtx : Set where
  □           : TermCtx
  ƛC_∙_       : Ty → TermCtx → TermCtx
  _·L_        : TermCtx → Term → TermCtx
  _·R_        : Term → TermCtx → TermCtx
  ΛC_         : TermCtx → TermCtx
  νC_·_⟨_⟩    : Ty → TermCtx → Conv → TermCtx
  [_,_]C_⟨_⟩  : Sign → ℕ → TermCtx → Conv → TermCtx

plug : TermCtx → Term → Term
plug □                  M = M
plug (ƛC A ∙ C)         M = ƛ A ∙ plug C M
plug (C ·L N)           M = plug C M · N
plug (L ·R C)           M = L · plug C M
plug (ΛC C)             M = Λ plug C M
plug (νC A · C ⟨ c ⟩)   M = ν A · plug C M ⟨ c ⟩
plug ([ s , α ]C C ⟨ c ⟩) M = [ s , α ] plug C M ⟨ c ⟩

------------------------------------------------------------------------
-- 2. The flags at a hole, and the scope map they give
------------------------------------------------------------------------

-- a `Λ` names its new cell; a boundary sets its cell's flag
holeFlags : Flags → TermCtx → Flags
holeFlags Φ □                    = Φ
holeFlags Φ (ƛC A ∙ C)           = holeFlags Φ C
holeFlags Φ (C ·L N)             = holeFlags Φ C
holeFlags Φ (L ·R C)             = holeFlags Φ C
holeFlags Φ (ΛC C)               = holeFlags (true ∷ Φ) C
holeFlags Φ (νC A · C ⟨ c ⟩)     = holeFlags Φ C
holeFlags Φ ([ s , α ]C C ⟨ c ⟩) = holeFlags (setFlag α (inside s) Φ) C

-- the named cells, newest first: name X denotes the X-th of them
names : Flags → List ℕ
names []          = []
names (true ∷ Φ)  = zero ∷ map suc (names Φ)
names (false ∷ Φ) = map suc (names Φ)

------------------------------------------------------------------------
-- 3. Renaming a context, clause for clause with `renameʳ`, the renaming
--    that reaches its hole, and the sibling shift
------------------------------------------------------------------------

idʳ : Renameᵗ
idʳ x = x

renCtx : Renameᵗ → TermCtx → TermCtx
renCtx ρ □                    = □
renCtx ρ (ƛC A ∙ C)           = ƛC A ∙ renCtx ρ C
renCtx ρ (C ·L N)             = renCtx ρ C ·L renameʳ ρ N
renCtx ρ (L ·R C)             = renameʳ ρ L ·R renCtx ρ C
renCtx ρ (ΛC C)               = ΛC renCtx (extᵗ ρ) C
renCtx ρ (νC A · C ⟨ c ⟩)     = νC A · renCtx ρ C ⟨ c ⟩
renCtx ρ ([ s , α ]C C ⟨ c ⟩) = [ s , ρ α ]C renCtx ρ C ⟨ c ⟩

holeᴿ : Renameᵗ → TermCtx → Renameᵗ
holeᴿ ρ □                    = ρ
holeᴿ ρ (ƛC A ∙ C)           = holeᴿ ρ C
holeᴿ ρ (C ·L N)             = holeᴿ ρ C
holeᴿ ρ (L ·R C)             = holeᴿ ρ C
holeᴿ ρ (ΛC C)               = holeᴿ (extᵗ ρ) C
holeᴿ ρ (νC A · C ⟨ c ⟩)     = holeᴿ ρ C
holeᴿ ρ ([ s , α ]C C ⟨ c ⟩) = holeᴿ ρ C

-- a sibling of a step moves by the step's allocation: its context, its
-- node, and the renaming that reaches its hole
↑ᶜ : Alloc → TermCtx → TermCtx
↑ᶜ keep    C = C
↑ᶜ (new P) C = renCtx suc C

↑ᴴ : Alloc → TermCtx → Term → Term
↑ᴴ keep    C M = M
↑ᴴ (new P) C M = renameʳ (holeᴿ suc C) M

↑ʳ : Alloc → TermCtx → Renameᵗ
↑ʳ keep    C = idʳ
↑ʳ (new P) C = holeᴿ suc C

------------------------------------------------------------------------
-- 4. Beta's substitution through a context, clause for clause with
--    `substᵐ`.  A boundary is term-closed, so substitution stops there.
------------------------------------------------------------------------

substCtx : ℕ → Term → TermCtx → TermCtx
substCtx j V □                    = □
substCtx j V (ƛC A ∙ C)           = ƛC A ∙ substCtx (suc j) V C
substCtx j V (C ·L N)             = substCtx j V C ·L substᵐ j V N
substCtx j V (L ·R C)             = substᵐ j V L ·R substCtx j V C
substCtx j V (ΛC C)               = ΛC substCtx j (crossΛ V) C
substCtx j V (νC A · C ⟨ c ⟩)     = νC A · substCtx j V C ⟨ c ⟩
substCtx j V ([ s , α ]C C ⟨ c ⟩) = [ s , α ]C C ⟨ c ⟩

-- the node in the hole, after the substitution
holeSubst : ℕ → Term → TermCtx → Term → Term
holeSubst j V □                    M = substᵐ j V M
holeSubst j V (ƛC A ∙ C)           M = holeSubst (suc j) V C M
holeSubst j V (C ·L N)             M = holeSubst j V C M
holeSubst j V (L ·R C)             M = holeSubst j V C M
holeSubst j V (ΛC C)               M = holeSubst j (crossΛ V) C M
holeSubst j V (νC A · C ⟨ c ⟩)     M = holeSubst j V C M
holeSubst j V ([ s , α ]C C ⟨ c ⟩) M = M

-- the node in the hole is the substituted variable itself
data Hits : ℕ → TermCtx → Term → Set where
  hits-□  : ∀ {x} → hitVar x j ≡ hit → Hits j □ (` x)
  hits-ƛ  : ∀ {C M} → Hits (suc j) C M → Hits j (ƛC A ∙ C) M
  hits-·L : ∀ {C M} → Hits j C M → Hits j (C ·L N) M
  hits-·R : ∀ {C M} → Hits j C M → Hits j (L ·R C) M
  hits-Λ  : ∀ {C M} → Hits j C M → Hits j (ΛC C) M
  hits-ν  : ∀ {C M} → Hits j C M → Hits j (νC A · C ⟨ c ⟩) M

-- the copy of a value under k `Λ`s: k `crossΛ` layers
cross : ℕ → Term → Term
cross zero    V = V
cross (suc k) V = crossΛ (cross k V)

-- A position (C , M) of the argument `plug C M`, in its copy under k
-- `Λ`s.  Each `crossΛ` wraps the copy in a hide of the `Λ`'s cell and
-- shifts it past that cell.
data ImageResidual : ℕ → TermCtx → Term → Renameᵗ → TermCtx → Term
                   → Set where
  image-here : ∀ {C M} → ImageResidual zero C M idʳ C M
  image-Λ    : ∀ {C M D N}
    → ImageResidual k C M ρ D N
    → ImageResidual (suc k) C M (λ x → holeᴿ suc D (ρ x))
        ([ ⁻ , zero ]C renCtx suc D ⟨ idᶜ ⟩) (renameʳ (holeᴿ suc D) N)

-- The same position, followed through the body `P` (substituted for
-- variable j, under k `Λ`s) to an occurrence that receives a copy.
data CopyResidual (k j : ℕ) : Term → TermCtx → Term → Renameᵗ → TermCtx
                            → Term → Set where
  copy-var : ∀ {x C M D N}
    → hitVar x j ≡ hit
    → ImageResidual k C M ρ D N
    → CopyResidual k j (` x) C M ρ D N
  copy-ƛ   : ∀ {P C M D N}
    → CopyResidual k (suc j) P C M ρ D N
    → CopyResidual k j (ƛ A ∙ P) C M ρ (ƛC A ∙ D) N
  copy-·L  : ∀ {P C M D N}
    → CopyResidual k j L C M ρ D N
    → CopyResidual k j (L · P) C M ρ
        (D ·L substᵐ j (cross k (plug C M)) P) N
  copy-·R  : ∀ {P C M D N}
    → CopyResidual k j P C M ρ D N
    → CopyResidual k j (L · P) C M ρ
        (substᵐ j (cross k (plug C M)) L ·R D) N
  copy-Λ   : ∀ {P C M D N}
    → CopyResidual (suc k) j P C M ρ D N
    → CopyResidual k j (Λ P) C M ρ (ΛC D) N
  copy-ν   : ∀ {C M D N}
    → CopyResidual k j L C M ρ D N
    → CopyResidual k j (ν A · L ⟨ c ⟩) C M ρ (νC A · D ⟨ c ⟩) N

------------------------------------------------------------------------
-- 5. TyBeta's instantiation on contexts: the hole is in the body of
--    the `Λ` at the bottom of the tower, and stays there.
------------------------------------------------------------------------

infix 4 _•ᶜ⟶_
data _•ᶜ⟶_ : TermCtx → TermCtx → Set where
  instᶜ-Λ  : ∀ {C} → ΛC C •ᶜ⟶ C
  instᶜ-∀  : ∀ {C D} → C •ᶜ⟶ D
    → [ s , α ]C C ⟨ ∀ᶜ c ⟩ •ᶜ⟶ [ s , suc α ]C D ⟨ c ⟩
  instᶜ-id : ∀ {C D} → C •ᶜ⟶ D
    → [ s , α ]C C ⟨ idᶜ ⟩ •ᶜ⟶ [ s , suc α ]C D ⟨ idᶜ ⟩

------------------------------------------------------------------------
-- 6. Residuals of one step: the step `r` moves the node `M` in hole `C`
--    to hole `D` as `N`, with renaming `ρ` reaching the hole.
------------------------------------------------------------------------

data Residual : ∀ {Γ L L′ a} → Γ ⊢ L ⟶ L′ ∣ a
              → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where

  -- Beta, the body: a node the substitution does not replace
  residual-β-body : ∀ {C M}
    (w : Value W)
    → ¬ Hits zero C M
    → Residual (β-ƛ {Γ = Γ} {A = A} {N = plug C M} w)
        ((ƛC A ∙ C) ·L W) M idʳ
        (substCtx zero W C) (holeSubst zero W C M)

  -- Beta, the argument: one residual per occurrence that receives it
  residual-β-arg : ∀ {Q C M D N}
    (w : Value (plug C M))
    → CopyResidual zero zero Q C M ρ D N
    → Residual (β-ƛ {Γ = Γ} {A = A} {N = Q} w)
        ((ƛ A ∙ Q) ·R C) M ρ D N

  -- Wrap: the function keeps its layer; the argument crosses into the
  -- inverse entry
  residual-wrap-fun : ∀ {C M}
    (v : Value (plug C M)) (w : Value W)
    → Residual (wrap {Γ = Γ} {s = s} {α = α} {c = c} {d = d} v w)
        ([ s , α ]C C ⟨ c ↦ d ⟩ ·L W) M idʳ
        ([ s , α ]C (C ·L [ flip s , α ] W ⟨ c ⟩) ⟨ d ⟩) M
  residual-wrap-arg : ∀ {V C M}
    (v : Value V) (w : Value (plug C M))
    → Residual (wrap {Γ = Γ} {s = s} {α = α} {c = c} {d = d} v w)
        ([ s , α ] V ⟨ c ↦ d ⟩ ·R C) M idʳ
        ([ s , α ]C (V ·R [ flip s , α ]C C ⟨ c ⟩) ⟨ d ⟩) M
  residual-wrap-id-fun : ∀ {C M}
    (u : Value ([ s , α ] plug C M ⟨ idᶜ ⟩)) (w : Value W)
    → Residual (wrap-id {Γ = Γ} u w)
        ([ s , α ]C C ⟨ idᶜ ⟩ ·L W) M idʳ
        ([ s , α ]C (C ·L [ flip s , α ] W ⟨ idᶜ ⟩) ⟨ idᶜ ⟩) M
  residual-wrap-id-arg : ∀ {V C M}
    (u : Value ([ s , α ] V ⟨ idᶜ ⟩)) (w : Value (plug C M))
    → Residual (wrap-id {Γ = Γ} u w)
        ([ s , α ] V ⟨ idᶜ ⟩ ·R C) M idʳ
        ([ s , α ]C (V ·R [ flip s , α ]C C ⟨ idᶜ ⟩) ⟨ idᶜ ⟩) M

  -- TyBeta: the `Λ`'s cell becomes the allocated cell, so the body
  -- stays where it is
  residual-tyβ : ∀ {C D M}
    (sp : flags Γ ⊢ A ⇝ P) (v : Value (plug C M))
    (i : plug C M •⟶ plug D M)
    → C •ᶜ⟶ D
    → Residual (tyβ {Γ = Γ} {d = d} sp v i)
        (νC A · C ⟨ d ⟩) M idʳ ([ ⁺ , zero ]C D ⟨ d ⟩) M

  -- the boundary rules: the body below the redex's two layers
  residual-cancel-□ : ∀ {C M}
    (w : Value (plug C M))
    → Residual (cancel-□ {Γ = Γ} {α = α} w)
        ([ ⁺ , α ]C [ ⁻ , α ]C C ⟨ seal ⟩ ⟨ unseal ⟩) M idʳ C M
  residual-cancel-id : ∀ {C M}
    (u : Value ([ ⁺ , α ] plug C M ⟨ idᶜ ⟩))
    → Residual (cancel-id {Γ = Γ} u)
        ([ ⁻ , α ]C [ ⁺ , α ]C C ⟨ idᶜ ⟩ ⟨ idᶜ ⟩) M idʳ C M
  residual-sink : ∀ {C M}
    (α≢β : α ≢ β) (v : Value (plug C M))
    → Residual (sink {Γ = Γ} α≢β v)
        ([ ⁻ , α ]C [ ⁻ , β ]C C ⟨ seal ⟩ ⟨ idᶜ ⟩) M idʳ
        ([ ⁻ , β ]C [ ⁻ , α ]C C ⟨ idᶜ ⟩ ⟨ seal ⟩) M
  residual-swap : ∀ {C M}
    (α≢β : α ≢ β) (v : Sealed (plug C M))
    → Residual (swap {Γ = Γ} α≢β v)
        ([ ⁻ , α ]C [ ⁺ , β ]C C ⟨ idᶜ ⟩ ⟨ idᶜ ⟩) M idʳ
        ([ ⁺ , β ]C [ ⁻ , α ]C C ⟨ idᶜ ⟩ ⟨ idᶜ ⟩) M
  residual-push : ∀ {C M}
    (v : Sealed (plug C M))
    → Residual (push {Γ = Γ} {α = α} {β = β} v)
        ([ ⁺ , α ]C [ ⁺ , β ]C C ⟨ idᶜ ⟩ ⟨ unseal ⟩) M idʳ
        ([ ⁺ , β ]C [ ⁺ , α ]C C ⟨ unseal ⟩ ⟨ idᶜ ⟩) M

  -- (Id: no residual; the constant is consumed with its layer.)

  -- the ξ rules: the position is inside the stepping subterm, or in a
  -- sibling, which moves by the step's allocation
  residual-ξ-·₁ : ∀ {L′ C M D N} {r : Γ ⊢ L ⟶ L′ ∣ a}
    → Residual r C M ρ D N
    → Residual (ξ-·₁ {M = O} r) (C ·L O) M ρ (D ·L ↑ᵃ a O) N
  residual-ξ-·₁-sib : ∀ {L′ C M} (r : Γ ⊢ L ⟶ L′ ∣ a)
    → Residual (ξ-·₁ {M = plug C M} r) (L ·R C) M (↑ʳ a C)
        (L′ ·R ↑ᶜ a C) (↑ᴴ a C M)
  residual-ξ-·₂ : ∀ {V O′ C M D N} {r : Γ ⊢ O ⟶ O′ ∣ a}
    (v : Value V)
    → Residual r C M ρ D N
    → Residual (ξ-·₂ v r) (V ·R C) M ρ (↑ᵃ a V ·R D) N
  residual-ξ-·₂-sib : ∀ {O′ C M} (v : Value (plug C M))
    (r : Γ ⊢ O ⟶ O′ ∣ a)
    → Residual (ξ-·₂ v r) (C ·L O) M (↑ʳ a C) (↑ᶜ a C ·L O′) (↑ᴴ a C M)
  residual-ξ-ν : ∀ {L′ C M D N} {r : Γ ⊢ L ⟶ L′ ∣ a}
    → Residual r C M ρ D N
    → Residual (ξ-ν {A = A} {c = c} r) (νC A · C ⟨ c ⟩) M ρ
        (νC A · D ⟨ c ⟩) N
  residual-ξ-[] : ∀ {O′ C M D N} {r : interior s α Γ ⊢ O ⟶ O′ ∣ a}
    → Residual r C M ρ D N
    → Residual (ξ-[] {c = c} r) ([ s , α ]C C ⟨ c ⟩) M ρ
        ([ s , ↑ᵛ a α ]C D ⟨ c ⟩) N

------------------------------------------------------------------------
-- 7. Residuals through a run: the renamings compose
------------------------------------------------------------------------

data Residuals : ∀ {Γ L L′ Γ′} → Γ ⊢ L —↠ L′ ⊣ Γ′
               → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where
  residuals-done : ∀ {C M}
    → Residuals (_∎ {Γ = Γ} (plug C M)) C M idʳ C M
  residuals-step : ∀ {L′ L″ Γ′ C M D N E O}
    {r : Γ ⊢ L ⟶ L′ ∣ a} {rs : a ⨾ Γ ⊢ L′ —↠ L″ ⊣ Γ′}
    → Residual r C M ρ D N
    → Residuals rs D N ρ′ E O
    → Residuals (L —→⟨ r ⟩ rs) C M (λ x → ρ′ (ρ x)) E O

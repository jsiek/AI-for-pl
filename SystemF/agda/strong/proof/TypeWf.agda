module strong.proof.TypeWf where

-- Strong System F v7 — a typed term's type is well formed.
--
-- `revTy-typing` asks for `Δᵢ ⊢ᵗ B`, the SOURCE type of the conversion
-- `TyBeta` mints, and neither `⊢Λ` nor `⊢•[]` carries it.  `typing-wf`
-- recovers it from the derivation.  Three things are needed on the way:
-- anchor-only entries are invisible to source type variables (so a store
-- can be dropped), a type application's result type is well formed, and a
-- conversion's two endpoint types are well formed at their own contexts.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.proof.SameTyProperties using (sameTy-sym)
open import strong.proof.CloseTy using (closeAt-single)
open import strong.proof.RevealTyping using
  (tv-of-name; read-wf; wf-Λ; Reveals; rev-here; closeAt-wf)
open import strong.proof.TermSubstitution using (unmap-lookup)

private
  variable
    Δ Δ₁ Δ₂ ΔΘ : Ctxᵗ
    Γ : Ctx
    A B : Ty
    R S : RepTy
    k X : ℕ
    α : Anchor
    Θ : Store
    c : Conv
    h : Head
    M : Term

------------------------------------------------------------------------
-- Anchor entries are invisible to source type variables
------------------------------------------------------------------------

data AnchorEnt : Ent → Set where
  ae-abst : AnchorEnt abst
  ae-bind : AnchorEnt (bind R)

ins-tv : ∀ {e} → AnchorEnt e → ∀ P {Δ X}
  → (P ++ Δ) ∋tv X → (P ++ e ∷ Δ) ∋tv X
ins-tv ae-abst [] t = tv-over-abst t
ins-tv ae-bind [] t = tv-over-bind t
ins-tv ae (abst ∷ P) (tv-over-abst t) = tv-over-abst (ins-tv ae P t)
ins-tv ae (bind R ∷ P) (tv-over-bind t) = tv-over-bind (ins-tv ae P t)
ins-tv ae (name α ∷ P) tv-here = tv-here
ins-tv ae (name α ∷ P) (tv-over-name t) = tv-over-name (ins-tv ae P t)

del-tv : ∀ {e} → AnchorEnt e → ∀ P {Δ X}
  → (P ++ e ∷ Δ) ∋tv X → (P ++ Δ) ∋tv X
del-tv ae-abst [] (tv-over-abst t) = t
del-tv ae-bind [] (tv-over-bind t) = t
del-tv ae (abst ∷ P) (tv-over-abst t) = tv-over-abst (del-tv ae P t)
del-tv ae (bind R ∷ P) (tv-over-bind t) = tv-over-bind (del-tv ae P t)
del-tv ae (name α ∷ P) tv-here = tv-here
del-tv ae (name α ∷ P) (tv-over-name t) = tv-over-name (del-tv ae P t)

ins-wf : ∀ {e} → AnchorEnt e → ∀ P {Δ A}
  → (P ++ Δ) ⊢ᵗ A → (P ++ e ∷ Δ) ⊢ᵗ A
ins-wf ae P (wf-var x) = wf-var (ins-tv ae P x)
ins-wf ae P wf-ℕ = wf-ℕ
ins-wf ae P wf-𝔹 = wf-𝔹
ins-wf ae P (wf-⇒ a b) = wf-⇒ (ins-wf ae P a) (ins-wf ae P b)
ins-wf ae P (wf-∀ a) = wf-∀ (ins-wf ae (name zero ∷ abst ∷ P) a)

del-wf : ∀ {e} → AnchorEnt e → ∀ P {Δ A}
  → (P ++ e ∷ Δ) ⊢ᵗ A → (P ++ Δ) ⊢ᵗ A
del-wf ae P (wf-var x) = wf-var (del-tv ae P x)
del-wf ae P wf-ℕ = wf-ℕ
del-wf ae P wf-𝔹 = wf-𝔹
del-wf ae P (wf-⇒ a b) = wf-⇒ (del-wf ae P a) (del-wf ae P b)
del-wf ae P (wf-∀ a) = wf-∀ (del-wf ae (name zero ∷ abst ∷ P) a)

abst-weaken-wf : Δ ⊢ᵗ A → (abst ∷ Δ) ⊢ᵗ A
abst-weaken-wf = ins-wf ae-abst []

-- A store adds only anchor entries, so it changes no source index.
store-drop-wf : Δ ⊢ˢ Θ ⇒ ΔΘ → ΔΘ ⊢ᵗ A → Δ ⊢ᵗ A
store-drop-wf store[] wf = wf
store-drop-wf (store-abst s) wf =
  del-wf ae-abst [] (store-drop-wf s wf)
store-drop-wf (store-bind wfR s) wf =
  del-wf ae-bind [] (store-drop-wf s wf)

------------------------------------------------------------------------
-- A type application's result
------------------------------------------------------------------------

tyapp-wf : (name zero ∷ abst ∷ Δ) ⊢ᵗ B → Δ ⊢ᵗ A → Δ ⊢ᵗ B [ A ]ᵗ
tyapp-wf {Δ = Δ} {B = B} {A = A} wfB wfA =
  subst (Δ ⊢ᵗ_) (closeAt-single A B)
    (del-wf ae-abst [] (closeAt-wf rev-here (abst-weaken-wf wfA) wfB))

------------------------------------------------------------------------
-- Conversion endpoints
------------------------------------------------------------------------

-- The k source variables `Paired` tracks are the binders `same-∀` pushed,
-- so a context reached by k of those steps has them all in scope.
data KPrefix : ℕ → Ctxᵗ → Set where
  kp-zero : KPrefix zero Δ
  kp-suc  : KPrefix k Δ → KPrefix (suc k) (name zero ∷ abst ∷ Δ)

paired-tv : Paired k X → KPrefix k Δ → Δ ∋tv X
paired-tv paired-zero (kp-suc kp) = tv-here
paired-tv (paired-suc p) (kp-suc kp) =
  tv-over-name (tv-over-abst (paired-tv p kp))

sameTy-wf-right : SameTy k Δ₁ A Δ₂ B → KPrefix k Δ₂ → Δ₂ ⊢ᵗ B
sameTy-wf-right (same-bound p) kp = wf-var (paired-tv p kp)
sameTy-wf-right (same-free n₁ n₂ sa) kp = wf-var (tv-of-name n₂)
sameTy-wf-right same-ℕ kp = wf-ℕ
sameTy-wf-right same-𝔹 kp = wf-𝔹
sameTy-wf-right (same-⇒ a b) kp =
  wf-⇒ (sameTy-wf-right a kp) (sameTy-wf-right b kp)
sameTy-wf-right (same-∀ a) kp = wf-∀ (sameTy-wf-right a (kp-suc kp))

sameTy-wf-left : SameTy k Δ₁ A Δ₂ B → KPrefix k Δ₁ → Δ₁ ⊢ᵗ A
sameTy-wf-left same kp = sameTy-wf-right (sameTy-sym same) kp

mutual
  head-wf-source : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₁ ⊢ᵗ A
  head-wf-source (conv-seal x r rd) = read-wf rd
  head-wf-source (conv-unseal x r rd) = wf-var (tv-of-name x)
  head-wf-source (conv-fun s t) =
    wf-⇒ (conv-wf-target s) (conv-wf-source t)
  head-wf-source (conv-all s) = wf-∀ (conv-wf-source s)

  head-wf-target : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊢ᵗ B
  head-wf-target (conv-seal x r rd) = wf-var (tv-of-name x)
  head-wf-target (conv-unseal x r rd) = read-wf rd
  head-wf-target (conv-fun s t) =
    wf-⇒ (conv-wf-source s) (conv-wf-target t)
  head-wf-target (conv-all s) = wf-∀ (conv-wf-target s)

  conv-wf-source : Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁ ⊢ᵗ A
  conv-wf-source (conv-id same) = sameTy-wf-left same kp-zero
  conv-wf-source (conv-cons hd tl) = head-wf-source hd

  conv-wf-target : Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊢ᵗ B
  conv-wf-target (conv-id same) = sameTy-wf-right same kp-zero
  conv-wf-target (conv-cons hd tl) = conv-wf-target tl

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

WfCtx : Ctxᵗ → Ctx → Set
WfCtx Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ⊢ᵗ A

wfCtx-[] : WfCtx Δ []
wfCtx-[] ()

wfCtx-∷ : Δ ⊢ᵗ A → WfCtx Δ Γ → WfCtx Δ (A ∷ Γ)
wfCtx-∷ wf wfΓ here = wf
wfCtx-∷ wf wfΓ (there x) = wfΓ x

wfCtx-Λ : WfCtx Δ Γ → WfCtx (name zero ∷ abst ∷ Δ) (⤊ Γ)
wfCtx-Λ wfΓ x with unmap-lookup x
wfCtx-Λ wfΓ x | A , refl , y = wf-Λ (wfΓ y)

typing-wf : WfCtx Δ Γ → Δ ∣ Γ ⊢ M ⦂ A → Δ ⊢ᵗ A
typing-wf wfΓ (⊢` x) = wfΓ x
typing-wf wfΓ ⊢$ = wf-ℕ
typing-wf wfΓ ⊢# = wf-𝔹
typing-wf wfΓ (⊢⊕ l r) = wf-ℕ
typing-wf wfΓ (⊢ƛ wf body) =
  wf-⇒ wf (typing-wf (wfCtx-∷ wf wfΓ) body)
typing-wf wfΓ (⊢· l r) with typing-wf wfΓ l
typing-wf wfΓ (⊢· l r) | wf-⇒ a b = b
typing-wf wfΓ (⊢Λ body) = wf-∀ (typing-wf (wfCtx-Λ wfΓ) body)
typing-wf wfΓ (⊢•[] l wfA) with typing-wf wfΓ l
typing-wf wfΓ (⊢•[] l wfA) | wf-∀ b = tyapp-wf b wfA
typing-wf wfΓ (⊢ν store scope nf body conv) =
  store-drop-wf store (conv-wf-target conv)

typing-wf-closed : Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ᵗ A
typing-wf-closed = typing-wf wfCtx-[]

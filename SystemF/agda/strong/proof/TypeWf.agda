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
open import strong.proof.CtxProperties using (tv-of-name)
open import strong.proof.RevealTyping using
  (read-wf; wf-Λ; Reveals; rev-at; closeAt-wf)
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

-- A CONCEALED entry is invisible to source type variables, whatever it
-- binds — that is the whole content of the two universes being separate.
ins-tv : ∀ {b} P {Δ X}
  → (P ++ Δ) ∋tv X → (P ++ anch concealed b ∷ Δ) ∋tv X
ins-tv [] t = tv-concealed t
ins-tv (anch revealed b′ ∷ P) tv-here = tv-here
ins-tv (anch revealed b′ ∷ P) (tv-revealed t) = tv-revealed (ins-tv P t)
ins-tv (anch concealed b′ ∷ P) (tv-concealed t) = tv-concealed (ins-tv P t)

del-tv : ∀ {b} P {Δ X}
  → (P ++ anch concealed b ∷ Δ) ∋tv X → (P ++ Δ) ∋tv X
del-tv [] (tv-concealed t) = t
del-tv (anch revealed b′ ∷ P) tv-here = tv-here
del-tv (anch revealed b′ ∷ P) (tv-revealed t) = tv-revealed (del-tv P t)
del-tv (anch concealed b′ ∷ P) (tv-concealed t) = tv-concealed (del-tv P t)

ins-wf : ∀ {b} P {Δ A}
  → (P ++ Δ) ⊢ᵗ A → (P ++ anch concealed b ∷ Δ) ⊢ᵗ A
ins-wf P (wf-var x) = wf-var (ins-tv P x)
ins-wf P wf-ℕ = wf-ℕ
ins-wf P wf-𝔹 = wf-𝔹
ins-wf P (wf-⇒ a b) = wf-⇒ (ins-wf P a) (ins-wf P b)
ins-wf P (wf-∀ a) = wf-∀ (ins-wf (anch revealed abstA ∷ P) a)

del-wf : ∀ {b} P {Δ A}
  → (P ++ anch concealed b ∷ Δ) ⊢ᵗ A → (P ++ Δ) ⊢ᵗ A
del-wf P (wf-var x) = wf-var (del-tv P x)
del-wf P wf-ℕ = wf-ℕ
del-wf P wf-𝔹 = wf-𝔹
del-wf P (wf-⇒ a b) = wf-⇒ (del-wf P a) (del-wf P b)
del-wf P (wf-∀ a) = wf-∀ (del-wf (anch revealed abstA ∷ P) a)

abst-weaken-wf : ∀ {b} → Δ ⊢ᵗ A → (anch concealed b ∷ Δ) ⊢ᵗ A
abst-weaken-wf = ins-wf []

-- A store introduces anchors CONCEALED, so it changes no source index.
store-drop-wf : Δ ⊢ˢ Θ ⇒ ΔΘ → ΔΘ ⊢ᵗ A → Δ ⊢ᵗ A
store-drop-wf store[] wf = wf
store-drop-wf (store-abst s) wf = del-wf [] (store-drop-wf s wf)
store-drop-wf (store-bind wfR s) wf = del-wf [] (store-drop-wf s wf)

------------------------------------------------------------------------
-- A type application's result
------------------------------------------------------------------------

tyapp-wf : (anch revealed abstA ∷ Δ) ⊢ᵗ B → Δ ⊢ᵗ A → Δ ⊢ᵗ B [ A ]ᵗ
tyapp-wf {Δ = Δ} {B = B} {A = A} wfB wfA =
  subst (Δ ⊢ᵗ_) (closeAt-single A B)
    (del-wf [] (closeAt-wf rev-at (abst-weaken-wf wfA) wfB))

------------------------------------------------------------------------
-- Conversion endpoints
------------------------------------------------------------------------

-- The k source variables `Paired` tracks are the binders `same-∀` pushed,
-- so a context reached by k of those steps has them all in scope.
data KPrefix : ℕ → Ctxᵗ → Set where
  kp-zero : KPrefix zero Δ
  kp-suc  : KPrefix k Δ → KPrefix (suc k) (anch revealed abstA ∷ Δ)

paired-tv : Paired k X → KPrefix k Δ → Δ ∋tv X
paired-tv paired-zero (kp-suc kp) = tv-here
paired-tv (paired-suc p) (kp-suc kp) = tv-revealed (paired-tv p kp)

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
  head-wf-source (conv-seal x r rd _) = read-wf rd
  head-wf-source (conv-unseal x r rd _) = wf-var (tv-of-name x)
  head-wf-source (conv-fun s t) =
    wf-⇒ (conv-wf-target s) (conv-wf-source t)
  head-wf-source (conv-all s) = wf-∀ (conv-wf-source s)

  head-wf-target : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊢ᵗ B
  head-wf-target (conv-seal x r rd _) = wf-var (tv-of-name x)
  head-wf-target (conv-unseal x r rd _) = read-wf rd
  head-wf-target (conv-fun s t) =
    wf-⇒ (conv-wf-source s) (conv-wf-target t)
  head-wf-target (conv-all s) = wf-∀ (conv-wf-target s)

  conv-wf-source : Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₁ ⊢ᵗ A
  conv-wf-source (conv-id same _) = sameTy-wf-left same kp-zero
  conv-wf-source (conv-cons hd tl) = head-wf-source hd

  conv-wf-target : Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊢ᵗ B
  conv-wf-target (conv-id same _) = sameTy-wf-right same kp-zero
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

wfCtx-Λ : WfCtx Δ Γ → WfCtx (anch revealed abstA ∷ Δ) (⤊ Γ)
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

module strong.notes.EmptyStackClosed where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.RepresentationTypes using (Addr)
open import strong.Ctx
open Ctxᵗ
open import strong.proof.SubstAnnTyping using (NoFreeᵗ; nf-var; nf-ℕ; nf-𝔹; nf-⇒; nf-∀; Closedᵗ)

-- A type well-formed at a context whose STACK IS EMPTY has no free
-- variables at all: `wf-var`'s only evidence is `stk Γ ∋ᵗ X`, and `∋ᵗ`
-- has no rule at `[]`.
wf-nofree-len : ∀ {Ss Bs A n} → (∀ {X} → Ss ∋ᵗ X → X < n)
  → (Ss ∥ Bs) ⊢ᵗ A → NoFreeᵗ n A
wf-nofree-len h (wf-var n) = nf-var (h n)
wf-nofree-len h wf-ℕ = nf-ℕ
wf-nofree-len h wf-𝔹 = nf-𝔹
wf-nofree-len h (wf-⇒ a b) = nf-⇒ (wf-nofree-len h a) (wf-nofree-len h b)
wf-nofree-len h (wf-∀ a) = nf-∀ (wf-nofree-len h′ a)
  where
  h′ : ∀ {X} → _ ∋ᵗ X → X < suc _
  h′ t-here = s≤s z≤n
  h′ (t-there p) = s≤s (h p)

-- so at an EMPTY stack, well-formed IS closed
wf-empty-closed : ∀ {Bs A} → ([] ∥ Bs) ⊢ᵗ A → Closedᵗ A
wf-empty-closed = wf-nofree-len (λ ())

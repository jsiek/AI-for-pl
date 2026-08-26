module proof.DGG.notes.probes.McpPilotProbe where

-- File Charter:
--   * Serves as a small MCP-server pilot probe for Agda interactions.
--   * Checks that real GTSFImp imports expose the structural `castSize`
--     measure and tag-cast constructor as expected.
--   * Proves a tiny strict-growth fact used by DGG fuel-bound reasoning.

open import Data.Nat using (_<_)
open import Data.Nat.Properties using (n<1+n)

open import Types using (Ty; Ground; NonStar)
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; _!; ？_)
open import proof.Consistency using (castSize)


mcp-castSize-tag-grows : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ Ans : NonStar A ⦄
  → (c : μ ⊢ A ∼ G)
  → castSize c < castSize (_! c)
mcp-castSize-tag-grows c = n<1+n (castSize c)

mcp-castSize-project-grows : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : μ ⊢ G ∼ B)
  → castSize c < castSize (？ c)
mcp-castSize-project-grows c = n<1+n (castSize c)

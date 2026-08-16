module proof.DGG.SimProof where

-- File Charter:
--   * Gives the direct term-imprecision/reduction case skeleton for Simᵀ.
--   * Recurses only on immediate term-imprecision premises; any other case
--     analysis or induction belongs in separately compiled helper lemmas.
--   * Is currently a partial proof: square-shaped cases are left as holes
--     until their helper interfaces and transports are fixed.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import CastTerms
open import Reduction
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (evolve-refl; evolve-keepᴸ)
open import proof.DGG.SimDef using (Simᵀ)
open import proof.DGG.SimBetaDef using (SimBetaᵀ)
open import proof.DGG.SimBetaCastDef using (SimBetaCastᵀ)
open import proof.DGG.TransportTermImprecisionDef
  using (TransportTermImprecisionᴾᵀ)
open import proof.DGG.SimSourceRevealDef using (SimSourceRevealᵀ)
open import proof.DGG.SimTargetRevealDef using (SimTargetRevealᵀ)
open import proof.DGG.SimSourceConcealDef using (SimSourceConcealᵀ)
open import proof.DGG.SimTargetConcealDef using (SimTargetConcealᵀ)
open import proof.DGG.CatchupToMorePreciseDef
  using
    ( CatchupToMorePrecise
    ; boundary-refl
    ; boundary-source-reveal
    ; boundary-source-conceal
    ; toTagRebaseAtᴸ
    )

------------------------------------------------------------------------
-- Direct simulation skeleton
------------------------------------------------------------------------

sim : SimBetaᵀ
  → SimBetaCastᵀ
  → TransportTermImprecisionᴾᵀ
  → SimSourceRevealᵀ
  → SimTargetRevealᵀ
  → SimSourceConcealᵀ
  → SimTargetConcealᵀ
  → CatchupToMorePrecise
  → Simᵀ

------------------------------------------------------------------------
-- Irreducible source forms
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (x⊑x² x) (pure-step ())
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (ƛ⊑ƛ² rel) (pure-step ())
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (Λ⊑Λ² lift vV vV′ rel q) (pure-step ())
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (Λ⊑² Anv z∈A lift vV M′⊢ rel q) (pure-step ())
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (Λ⊑²-smart-comma Anv z∈A smart lift vV M′⊢ rel q)
    (pure-step ())
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (κ⊑κ² κ p) (pure-step ())
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (blame⊑² M′⊢ p) (pure-step ())

------------------------------------------------------------------------
-- Application squares
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ V⊑M′) (pure-step (β vV)) =
  sim-beta parked L⊑L′ V⊑M′ vV

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (pure-step (β-⇒ vV vM)) =
  sim-beta-cast parked L⊑L′ M⊑M′ vV vM

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (pure-step (β-reveal-⇒ vV vM)) =
  {!!}

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (pure-step (β-conceal-⇒ vV vM)) =
  {!!}

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} {p = p} parked
    rel@(·⊑·² L⊑L′ M⊑M′) (pure-step blame-·₁) =
  Δᴿ , [] , _ , _ , W , p ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) p

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} {p = p} parked
    rel@(·⊑·² L⊑L′ M⊑M′) (pure-step (blame-·₂ vL)) =
  Δᴿ , [] , _ , _ , W , p ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) p

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (ξ-·₁ L→N refl)
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked L⊑L′ L→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (ξ-·₁ L→N refl)
    | result =
  {!!}

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (ξ-·₂ vL M→N refl)
    with catchup parked boundary-refl L⊑L′ vL
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (·⊑·² L⊑L′ M⊑M′) (ξ-·₂ vL M→N refl)
    | caught-up =
  {!!}

------------------------------------------------------------------------
-- Type-application squares
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (pure-step (β-∀ vM eq)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(•⊑•² p∀ M⊑M′ q r) (pure-step blame-•) =
  Δᴿ , [] , _ , _ , W , r ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) r
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (β-Λ vM) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (β-gen vM A≠★ safe) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (β-reveal-∀ vM) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (β-conceal-∀ vM) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (ξ-• M→N refl refl)
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked M⊑M′ M→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑•² p∀ M⊑M′ q r) (ξ-• M→N refl refl)
    | result =
  {!!}

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (pure-step (β-∀ vM eq)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(•⊑² p∀ M⊑M′ q r) (pure-step blame-•) =
  Δᴿ , [] , _ , _ , W , r ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) r
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (β-Λ vM) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (β-gen vM A≠★ safe) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (β-reveal-∀ vM) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (β-conceal-∀ vM) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (ξ-• M→N refl refl)
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked M⊑M′ M→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (•⊑² p∀ M⊑M′ q r) (ξ-• M→N refl refl)
    | result =
  {!!}

------------------------------------------------------------------------
-- Cast squares
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (pure-step (β-id vM)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (pure-step (ground vM A≠G)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (pure-step (expand vM G≠B)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (pure-step (tag-untag vM)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(cast⊑cast² c c′ M⊑M′ q)
    (pure-step (tag-untag-bad vM G≠H)) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(cast⊑cast² c c′ M⊑M′ q) (pure-step (blame-bot-intro vM)) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(cast⊑cast² c c′ M⊑M′ q) (pure-step blame-⟨⟩) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (β-inst vM B≠★) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (ξ-⟨⟩ M→N refl)
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked M⊑M′ M→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑cast² c c′ M⊑M′ q) (ξ-⟨⟩ M→N refl)
    | result =
  {!!}

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (pure-step (β-id vM)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (pure-step (ground vM A≠G)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (pure-step (expand vM G≠B)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (pure-step (tag-untag vM)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(cast⊑² c M⊑M′ q) (pure-step (tag-untag-bad vM G≠H)) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(cast⊑² c M⊑M′ q) (pure-step (blame-bot-intro vM)) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(cast⊑² c M⊑M′ q) (pure-step blame-⟨⟩) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (β-inst vM B≠★) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (ξ-⟨⟩ M→N refl)
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked M⊑M′ M→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (cast⊑² c M⊑M′ q) (ξ-⟨⟩ M→N refl)
    | result =
  {!!}

------------------------------------------------------------------------
-- Target-only wrappers: recurse on the source step
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊑cast² c′ M⊑M′ q) M→N
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked M⊑M′ M→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊑cast² c′ M⊑M′ q) M→N
    | result =
  {!!}

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(⊑reveal² mono rebase same c′⊢ M⊑M′ q) M→N =
  tgt↑ parked rel M→N

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(⊑conceal² mono rebase same c′⊢ M⊑M′ q) M→N =
  tgt↓ parked rel M→N

------------------------------------------------------------------------
-- Reveal and conceal squares
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑² mono rebase same-[] c⊢ M⊑M′ q)
    (pure-step (id-reveal vM))
    with catchup parked
      (boundary-source-reveal mono (toTagRebaseAtᴸ rebase)) M⊑M′ vM
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑² mono rebase same-[] c⊢ M⊑M′ q)
    (pure-step (id-reveal vM))
    | Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , Wᵖ′ , Xᴿ′? ,
      boundary-source-reveal mono′ rebase′ , q′ , pivot-map ,
      M′↠V′ , vV′ , evol , plan , V⊑V′
      rewrite pivot-map =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑² mono rebase same-[] c⊢ M⊑M′ q)
    (pure-step (conceal-reveal vM))
    with catchup parked
      (boundary-source-reveal mono (toTagRebaseAtᴸ rebase)) M⊑M′
      (vM ↓ ConcealValue.seal)
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑² mono rebase same-[] c⊢ M⊑M′ q)
    (pure-step (conceal-reveal vM))
    | Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , Wᵖ′ , Xᴿ′? ,
      boundary-source-reveal mono′ rebase′ , q′ , pivot-map ,
      M′↠V′ , vV′ , evol , plan , V⊑V′
      rewrite pivot-map =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(reveal⊑² mono rebase same c⊢ M⊑M′ q)
    (pure-step blame-reveal) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑² mono rebase same c⊢ M⊑M′ q)
    step@(ξ-reveal M→N refl) =
  src↑ parked rel step

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(conceal⊑² partner mono rebase same-[] c⊢ M⊑M′ q)
    (pure-step (id-conceal vM))
    with catchup parked (boundary-source-conceal mono rebase) M⊑M′ vM
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(conceal⊑² partner mono rebase same-[] c⊢ M⊑M′ q)
    (pure-step (id-conceal vM))
    | Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , Wᵖ′ , Xᴿ′? ,
      boundary-source-conceal mono′ rebase′ , q′ , pivot-map ,
      M′↠V′ , vV′ , evol , plan , V⊑V′
      rewrite pivot-map =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(conceal⊑² partner mono rebase same c⊢ M⊑M′ q)
    (pure-step blame-conceal) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(conceal⊑² partner mono rebase same c⊢ M⊑M′ q)
    step@(ξ-conceal M→N refl) =
  src↓ parked rel step

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ M⊑M′ q)
    (pure-step (id-reveal vM))
    with catchup parked
      (boundary-source-reveal mono
        (toTagRebaseAtᴸ (rebase-varᴸ rebase))) M⊑M′ vM
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ M⊑M′ q)
    (pure-step (id-reveal vM))
    | Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , Wᵖ′ , Xᴿ′? ,
      boundary-source-reveal mono′ rebase′ , q′ , pivot-map ,
      M′↠V′ , vV′ , evol , plan , V⊑V′
      rewrite pivot-map =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ M⊑M′ q)
    (pure-step (conceal-reveal vM))
    with catchup parked
      (boundary-source-reveal mono
        (toTagRebaseAtᴸ (rebase-varᴸ rebase))) M⊑M′
      (vM ↓ ConcealValue.seal)
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑reveal² mono rebase same-[] c⊢ c′⊢ M⊑M′ q)
    (pure-step (conceal-reveal vM))
    | Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , Wᵖ′ , Xᴿ′? ,
      boundary-source-reveal mono′ rebase′ , q′ , pivot-map ,
      M′↠V′ , vV′ , evol , plan , V⊑V′
      rewrite pivot-map =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
    (pure-step blame-reveal) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(reveal⊑reveal² mono rebase same c⊢ c′⊢ M⊑M′ q)
    step@(ξ-reveal M→N refl) =
  src↑ parked rel step

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(conceal⊑conceal² partner mono rebase same-[] c⊢ c′⊢
      M⊑M′ q) (pure-step (id-conceal vM))
    with catchup parked
      (boundary-source-conceal mono (tag-rebase-varᴸ rebase))
      M⊑M′ vM
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(conceal⊑conceal² partner mono rebase same-[] c⊢ c′⊢
      M⊑M′ q) (pure-step (id-conceal vM))
    | Δᴿ′ , χsᴿ , V′ , Δ′ , W′ , Wᵖ′ , Xᴿ′? ,
      boundary-source-conceal mono′ rebase′ , q′ , pivot-map ,
      M′↠V′ , vV′ , evol , plan , V⊑V′
      rewrite pivot-map =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢ M⊑M′ q)
    (pure-step blame-conceal) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(conceal⊑conceal² partner mono rebase same c⊢ c′⊢
      M⊑M′ q) step@(ξ-conceal M→N refl) =
  src↓ parked rel step

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
      M⊑M′ sealed q)
    (pure-step blame-conceal) =
  Δᴿ , [] , _ , _ , W , q ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) q
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    rel@(packaged-seal-star² partner mono rebase same c⊢ c′⊢
      M⊑M′ sealed q) step@(ξ-conceal M→N refl) =
  src↓ parked rel step

------------------------------------------------------------------------
-- Primitive-operation squares
------------------------------------------------------------------------

sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊕⊑⊕² op L⊑L′ M⊑M′ r) (pure-step (δ-⊕ δ)) =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r) (pure-step blame-⊕₁) =
  Δᴿ , [] , _ , _ , W , r ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) r
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
    {Δᴿ = Δᴿ} {W = W} parked
    rel@(⊕⊑⊕² op L⊑L′ M⊑M′ r) (pure-step (blame-⊕₂ vL)) =
  Δᴿ , [] , _ , _ , W , r ,
  (_ ∎[]) ,
  evolve-keepᴸ evolve-refl ,
  blame⊑² (CTI2T.target-typing² rel) r
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₁ L→N refl)
    with sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup
      parked L⊑L′ L→N
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₁ L→N refl)
    | result =
  {!!}
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₂ vL M→N refl)
    with catchup parked boundary-refl L⊑L′ vL
sim sim-beta sim-beta-cast tr src↑ tgt↑ src↓ tgt↓ catchup parked
    (⊕⊑⊕² op L⊑L′ M⊑M′ r) (ξ-⊕₂ vL M→N refl)
    | caught-up =
  {!!}

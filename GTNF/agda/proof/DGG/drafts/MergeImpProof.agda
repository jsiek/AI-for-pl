module proof.DGG.drafts.MergeImpProof where

-- File Charter:
--   * DRAFT SKELETON (2026-10-03) of `MergeImp2` (drafts/MergeImpDef),
--     by induction following the recursion of `⨟` (Conversion §4b):
--     `merge` (Conv), `mergeᵀ` (Tail then Conv), `mergeᵀᵀ` (Tail then
--     Tail), `mergeᵐ` (Mid then Mid), mutually, on the two `ConvImp`
--     derivations.  Every place `⨟` recurses is an IH call.
--   * No module parameters (MergeImp uses no other DGG lemma).
--   * IH FIT.  Every recursion of `⨟` has its IH, including the
--     cancellation of a left-only seal against a left-only unseal.
--     Glue that is not the IH:
--     - the smart constructors `unseal_⨾ˢ_`, `_⨾sealˢ_` (they test
--       `IsId`, and a ★ clause relates an identity to a non-identity,
--       e.g. `seal X ⊑ id ★`: the two sides may normalize differently);
--     - `seal X ⨟ unseal X = mkId (repOf Δ X)`: Agree of the joined
--       names' rep. vars (WfWorld), or the end types against `id ★`;
--     - MIXED derivations: a ★ clause on one conversion and a matched
--       clause on the other for the same name (or `conv-∀⊑∀` against
--       `conv-∀⊑`): the IH's composite differs from the goal's.
--   * Orientation: the LEFT term is the more precise one.

open import Types using (Ty)
open import Ctx using (Ctxᵗ; underΛ)
open import Conversion
open import Imprecision using (X⊑X; X⊑★)
open import Ctx using (_∋ˡ_:=_)
open import ImprecisionWorld
open import ConversionImprecision
open import proof.DGG.drafts.MergeImpDef

-- WfWorld under the binders of conv-∀⊑∀ / conv-∀⊑ (glue)
wf-⊕ : ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → WfWorld (W ⊕ X⊑X)
wf-⊕ wf = {!!}

wf-⊕ᴸ : ∀ {Δ Δ′} {W : World Δ Δ′} → WfWorld W → WfWorld (W ⊕ᴸ)
wf-⊕ᴸ wf = {!!}

-- the smart constructors (glue; they test IsId, see the charter)
unseal⨾ˢ⊑ : ∀ {Δ Δ′} {W : World Δ Δ′} {X X′ c c′}
  → Joins W X X′ → ConvImp W c c′
  → ConvImp W (unseal X ⨾ˢ c) (unseal X′ ⨾ˢ c′)
unseal⨾ˢ⊑ j c⊑ = {!!}

unseal⨾ˢ⊑ᴸ : ∀ {Δ Δ′} {W : World Δ Δ′} {X c c′}
  → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★ → ConvImp W c c′
  → ConvImp W (unseal X ⨾ˢ c) c′
unseal⨾ˢ⊑ᴸ mk c⊑ = {!!}

⨾sealˢ⊑ : ∀ {Δ Δ′} {W : World Δ Δ′} {X X′ t t′}
  → TailImp W t t′ → Joins W X X′
  → TailImp W (t ⨾sealˢ X) (t′ ⨾sealˢ X′)
⨾sealˢ⊑ t⊑ j = {!!}

⨾sealˢ⊑ᴸ : ∀ {Δ Δ′} {W : World Δ Δ′} {X t t′}
  → TailImp W t t′ → μʷ W ∋ˡ emb (ηᴸʷ W) X := X⊑★
  → TailImp W (t ⨾sealˢ X) t′
⨾sealˢ⊑ᴸ t⊑ mk = {!!}

mutual
  merge : ∀ {Δ Δ′} {W : World Δ Δ′} {c₁ c₂ c₁′ c₂′ A B C A′ B′ C′}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
    → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′)
  merge wf (conv-tail ⊢t) ⊢2 (conv-tail ⊢t′) ⊢2′ a z
      (conv-tail⊑tail t⊑) d₂ =
    mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z t⊑ d₂
  merge wf ⊢1 ⊢2 ⊢1′ ⊢2′ a z (conv-unseal⊑unseal j) d₂ =
    {!SMART unseal X ⨾ˢ c₂ ⊑ unseal X′ ⨾ˢ c₂′ (j, d₂)!}
  merge wf (conv-unseal-seq x ⊢c ni nc) ⊢2
      (conv-unseal-seq x′ ⊢c′ ni′ nc′) ⊢2′ a z
      (conv-unseal⨾⊑unseal⨾ j c⊑) d₂ =
    unseal⨾ˢ⊑ j
      (merge wf ⊢c ⊢2 ⊢c′ ⊢2′ {!source rel. of reps (Agree)!} z c⊑ d₂)
  merge wf ⊢1 ⊢2 ⊢1′ ⊢2′ a z (conv-unseal⊑id★ mk) d₂ =
    {!SMART unseal X ⨾ˢ c₂ ⊑ id★ ⨟ c₂′ (mk, d₂)!}
  merge wf (conv-unseal-seq x ⊢c ni nc) ⊢2 ⊢1′ ⊢2′ a z
      (conv-unseal⨾⊑ mk c⊑) d₂ =
    unseal⨾ˢ⊑ᴸ mk
      (merge wf ⊢c ⊢2 ⊢1′ ⊢2′ {!source rel.!} z c⊑ d₂)

  mergeᵀ : ∀ {Δ Δ′} {W : World Δ Δ′} {t c₂ t′ c₂′ A B C A′ B′ C′}
    → WfWorld W
    → Δ ⊢ᵀ t ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
    → Δ′ ⊢ᵀ t′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → TailImp W t t′ → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ t ⨟ᵀ c₂) (Δ′ ⊢ t′ ⨟ᵀ c₂′)
  -- c₂ a tail on both sides
  mergeᵀ wf ⊢t (conv-tail ⊢t₂) ⊢t′ (conv-tail ⊢t₂′) a z t⊑
      (conv-tail⊑tail t₂⊑) =
    conv-tail⊑tail (mergeᵀᵀ wf ⊢t ⊢t₂ ⊢t′ ⊢t₂′ a z t⊑ t₂⊑)
  -- c₂ = unseal Y ⊑ unseal Y′
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-mid⊑mid g⊑)
      (conv-unseal⊑unseal j) = conv-unseal⊑unseal j
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑seal j₁)
      (conv-unseal⊑unseal j) =
    {!mkId (repOf Δ X) ⊑ mkId (repOf Δ′ X′): Agree of the joined names (wf)!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑⨾seal t₀⊑ j₁)
      (conv-unseal⊑unseal j) = conv-tail⊑tail t₀⊑
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑id★ mk)
      (conv-unseal⊑unseal j) = {!absurd by typing (★ against ` Y′)!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑ t₀⊑ mk)
      (conv-unseal⊑unseal j) =
    {!MIXED: left-only seal X, matched unseal Y = X!}
  -- c₂ = unseal Y ⨾ c ⊑ unseal Y′ ⨾ c′
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-mid⊑mid g⊑)
      (conv-unseal⨾⊑unseal⨾ j c⊑) = conv-unseal⨾⊑unseal⨾ j c⊑
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑seal j₁)
      (conv-unseal⨾⊑unseal⨾ j c⊑) = c⊑
  mergeᵀ wf (conv-seal-seq ⊢t₀ x ni) (conv-unseal-seq y ⊢c ni₂ nc)
      (conv-seal-seq ⊢t₀′ x′ ni′) (conv-unseal-seq y′ ⊢c′ ni₂′ nc′) a z
      (conv-⨾seal⊑⨾seal t₀⊑ j₁) (conv-unseal⨾⊑unseal⨾ j c⊑) =
    mergeᵀ wf ⊢t₀ {!⊢c at the rep. of X = Y!} ⊢t₀′ {!⊢c′!} a z t₀⊑ c⊑
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑id★ mk)
      (conv-unseal⨾⊑unseal⨾ j c⊑) = {!absurd by typing!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑ t₀⊑ mk)
      (conv-unseal⨾⊑unseal⨾ j c⊑) =
    {!MIXED: left-only seal X, matched unseal Y = X!}
  -- c₂ = unseal Y ⊑ id ★ (left only)
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-mid⊑mid g⊑) (conv-unseal⊑id★ mk) =
    {!id(` Y) ⊑ g′ forces g′ = id ★ (typing); then conv-unseal⊑id★!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑seal j₁) (conv-unseal⊑id★ mk) =
    {!absurd by typing (` X′ against ★)!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑⨾seal t₀⊑ j₁)
      (conv-unseal⊑id★ mk) = {!absurd by typing!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑id★ mk₁) (conv-unseal⊑id★ mk) =
    {!mkId A ⊑ id ★ from a : A ⊑ ★ (the end-type premise)!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑ t₀⊑ mk₁)
      (conv-unseal⊑id★ mk) = {!tail t₀ ⊑ t′ ⨟ᵀ id★ (= t′ up to typing)!}
  -- c₂ = unseal Y ⨾ c ⊑ c₂′ (left only)
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-mid⊑mid g⊑) (conv-unseal⨾⊑ mk c⊑) =
    {!unseal Y ⨾ c ⊑ mid g′ ⨟ᵀ c₂′ (g = id(` Y), g′ = id ★ by typing)!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑seal j₁) (conv-unseal⨾⊑ mk c⊑) =
    {!MIXED: matched seal X, left-only unseal X!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑⨾seal t₀⊑ j₁)
      (conv-unseal⨾⊑ mk c⊑) =
    {!MIXED: matched seal X, left-only unseal X (the IH's right composite is t₀′ ⨟ᵀ c₂′, the goal's (t₀′ ⨾seal X′) ⨟ᵀ c₂′)!}
  mergeᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑id★ mk₁) (conv-unseal⨾⊑ mk c⊑) =
    {!c ⊑ id★ ⨟ c₂′, and id★ ⨟ c₂′ = c₂′ (typing)!}
  mergeᵀ wf (conv-seal-seq ⊢t₀ x ni) (conv-unseal-seq y ⊢c ni₂ nc) ⊢t′ ⊢2′
      a z (conv-⨾seal⊑ t₀⊑ mk₁) (conv-unseal⨾⊑ mk c⊑) =
    -- a left-only seal cancels a left-only unseal: the IH fits
    mergeᵀ wf ⊢t₀ {!⊢c at the rep. of X = Y!} ⊢t′ ⊢2′ a z t₀⊑ c⊑

  mergeᵀᵀ : ∀ {Δ Δ′} {W : World Δ Δ′} {t t₂ t′ t₂′ A B C A′ B′ C′}
    → WfWorld W
    → Δ ⊢ᵀ t ∶ A ⇝ B → Δ ⊢ᵀ t₂ ∶ B ⇝ C
    → Δ′ ⊢ᵀ t′ ∶ A′ ⇝ B′ → Δ′ ⊢ᵀ t₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → TailImp W t t′ → TailImp W t₂ t₂′
    → TailImp W (Δ ⊢ t ⨟ᵀᵀ t₂) (Δ′ ⊢ t′ ⨟ᵀᵀ t₂′)
  mergeᵀᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z t⊑ (conv-seal⊑seal j) =
    {!SMART t ⨾sealˢ Y ⊑ t′ ⨾sealˢ Y′ (t⊑, j)!}
  mergeᵀᵀ wf ⊢t (conv-seal-seq ⊢t₂ y ni) ⊢t′ (conv-seal-seq ⊢t₂′ y′ ni′)
      a z t⊑ (conv-⨾seal⊑⨾seal t₂⊑ j) =
    ⨾sealˢ⊑ (mergeᵀᵀ wf ⊢t ⊢t₂ ⊢t′ ⊢t₂′ a {!target rel. (Agree)!} t⊑ t₂⊑) j
  mergeᵀᵀ wf (conv-mid ⊢g) (conv-mid ⊢g₂) (conv-mid ⊢g′) (conv-mid ⊢g₂′)
      a z (conv-mid⊑mid g⊑) (conv-mid⊑mid g₂⊑) =
    conv-mid⊑mid (mergeᵐ wf ⊢g ⊢g₂ ⊢g′ ⊢g₂′ a z g⊑ g₂⊑)
  mergeᵀᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑seal j) (conv-mid⊑mid g₂⊑) =
    conv-seal⊑seal j
  mergeᵀᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑⨾seal t₀⊑ j)
      (conv-mid⊑mid g₂⊑) = conv-⨾seal⊑⨾seal t₀⊑ j
  mergeᵀᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-seal⊑id★ mk) (conv-mid⊑mid g₂⊑) =
    {!g₂′ = id ★ by typing, then conv-seal⊑id★ mk!}
  mergeᵀᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z (conv-⨾seal⊑ t₀⊑ mk) (conv-mid⊑mid g₂⊑) =
    {!t′ ⨟ᵀᵀ mid (id ★) = t′ (typing), then conv-⨾seal⊑ t₀⊑ mk!}
  mergeᵀᵀ wf ⊢t ⊢2 ⊢t′ ⊢2′ a z t⊑ (conv-seal⊑id★ mk) =
    {!SMART t ⨾sealˢ Y ⊑ t′ ⨟ᵀᵀ mid (id ★)!}
  mergeᵀᵀ wf ⊢t (conv-seal-seq ⊢t₂ y ni) ⊢t′ ⊢2′ a z t⊑
      (conv-⨾seal⊑ t₂⊑ mk) =
    ⨾sealˢ⊑ᴸ (mergeᵀᵀ wf ⊢t ⊢t₂ ⊢t′ ⊢2′ a {!target rel.!} t⊑ t₂⊑) mk

  mergeᵐ : ∀ {Δ Δ′} {W : World Δ Δ′} {g g₂ g′ g₂′ A B C A′ B′ C′}
    → WfWorld W
    → Δ ⊢ᵐ g ∶ A ⇝ B → Δ ⊢ᵐ g₂ ∶ B ⇝ C
    → Δ′ ⊢ᵐ g′ ∶ A′ ⇝ B′ → Δ′ ⊢ᵐ g₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → MidImp W g g′ → MidImp W g₂ g₂′
    → MidImp W (Δ ⊢ g ⨟ᵐ g₂) (Δ′ ⊢ g′ ⨟ᵐ g₂′)
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-id⊑id p) d₂ = d₂
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-↦⊑↦ s⊑ c⊑) (conv-id⊑id p) =
    conv-↦⊑↦ s⊑ c⊑
  mergeᵐ wf (conv-fun ⊢s ⊢c) (conv-fun ⊢s₂ ⊢c₂)
      (conv-fun ⊢s′ ⊢c′) (conv-fun ⊢s₂′ ⊢c₂′) a z
      (conv-↦⊑↦ s⊑ c⊑) (conv-↦⊑↦ s₂⊑ c₂⊑) =
    -- the domain flips
    conv-↦⊑↦ (merge wf ⊢s₂ ⊢s ⊢s₂′ ⊢s′ {!domain of z!} {!domain of a!}
                 s₂⊑ s⊑)
             (merge wf ⊢c ⊢c₂ ⊢c′ ⊢c₂′ {!codomain of a!} {!codomain of z!}
                 c⊑ c₂⊑)
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-↦⊑↦ s⊑ c⊑) (conv-∀⊑∀ s₂⊑) =
    {!absurd by typing (⇒ against ∀)!}
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-↦⊑↦ s⊑ c⊑) (conv-∀⊑ s₂⊑) =
    {!absurd by typing (⇒ against ∀)!}
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-∀⊑∀ s⊑) (conv-id⊑id p) = conv-∀⊑∀ s⊑
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-∀⊑∀ s⊑) (conv-↦⊑↦ s₂⊑ c₂⊑) =
    {!absurd by typing (∀ against ⇒)!}
  mergeᵐ wf (conv-all ⊢s) (conv-all ⊢s₂) (conv-all ⊢s′) (conv-all ⊢s₂′)
      a z (conv-∀⊑∀ s⊑) (conv-∀⊑∀ s₂⊑) =
    conv-∀⊑∀ (merge (wf-⊕ wf) ⊢s ⊢s₂ ⊢s′ ⊢s₂′ {!body of a!} {!body of z!}
                s⊑ s₂⊑)
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-∀⊑∀ s⊑) (conv-∀⊑ s₂⊑) =
    {!MIXED: ∀⊑∀ then ∀⊑ (absurd by ⊑-unique on the middle type?)!}
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-∀⊑ s⊑) (conv-id⊑id p) =
    {!`∀ s ⊑ g′ ⨟ᵐ id B′ (= g′ unless g′ is an identity)!}
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-∀⊑ s⊑) (conv-↦⊑↦ s₂⊑ c₂⊑) =
    {!absurd by typing (∀ against ⇒)!}
  mergeᵐ wf ⊢g ⊢2 ⊢g′ ⊢2′ a z (conv-∀⊑ s⊑) (conv-∀⊑∀ s₂⊑) =
    {!MIXED: ∀⊑ then ∀⊑∀!}
  mergeᵐ wf (conv-all ⊢s) (conv-all ⊢s₂) ⊢g′ ⊢2′ a z
      (conv-∀⊑ s⊑) (conv-∀⊑ s₂⊑) =
    conv-∀⊑ (merge (wf-⊕ᴸ wf) ⊢s ⊢s₂ (conv-tail (conv-mid ⊢g′))
               (conv-tail (conv-mid ⊢2′)) {!body of a!} {!body of z!}
               s⊑ s₂⊑)

merge-imp2 : MergeImp2
merge-imp2 = merge

------------------------------------------------------------------------
-- MergeImpL, Conv level only (PARTIAL: the Tail/Mid levels would mirror
-- mergeᵀ/mergeᵀᵀ/mergeᵐ with a left-only first conversion)
------------------------------------------------------------------------

merge-impL : MergeImpL
merge-impL wf (conv-tail ⊢t) ⊢2 ⊢2′ a b z d₂ =
  {!Tail level (t ⨟ᵀ c₂ ⊑ c₂′): not written!}
merge-impL wf (conv-unseal x) ⊢2 ⊢2′ a b z d₂ =
  {!unseal X ⨾ˢ c₂ ⊑ c₂′: a : ` X ⊑ A′ gives X⊑★ (A′ = ★) or a join (A′ = ` X′, then b : rep ⊑ ` X′ forces rep = a name)!}
merge-impL wf (conv-unseal-seq x ⊢c ni nc) ⊢2 ⊢2′ a b z d₂ =
  unseal⨾ˢ⊑ᴸ {!the mark X⊑★ (from a, as above)!}
    (merge-impL wf ⊢c ⊢2 ⊢2′
       {!NOT DERIVABLE from a: the IH needs rep(X) ⊑ A′!} b z d₂)

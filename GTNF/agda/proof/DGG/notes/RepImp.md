# `RepImp`: comparing paired rep. vars' payloads (design.md D23)

Decision (Jeremy, 2026-10-03): paired rep. vars' payloads are compared
**in the representation universe**, not by reading them as ordinary
types through the names in scope.

## What it replaced

`ImprecisionWorld.Agree` had this case ("deviation 2"):

```agda
  rep-rep   : ∀ {R R′ A A′}
    → Δ ∋rep α := R → Δ′ ∋rep β := R′
    → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′      -- read each payload through names
    → A ⊑ᵂ⟨ W ⟩ A′
    → Agree W α β
```

A payload that mentions a rep. var with no name in scope has no reading.
Interior worlds must now be well formed (D15).  Inside a boundary that
hides a name, a payload that mentions the hidden name's rep. var cannot
satisfy `Agree`, so `EvolveImp` was false
(`drafts/EvolveImpWfInteriorCounterexample.agda`).

## The definition (`ImprecisionWorld.agda` §8)

A payload `Ξ ⊢ᴿ[ n ] R` uses mixed indices.  An index `i < n` is a
local `∀`-bound variable, and the index `n + α` is the free rep. var `α`
(Ctx §4).  `μ` holds one mark per local and is shared by both sides, as
in `_⊢_⊑_`.

```agda
data RepImp (W : World Δ Δ′) : ImpEnv → Ty → Ty → Set
infix 4 RepImp
syntax RepImp W μ R R′ = μ ⊢ R ⊑ᴿ⟨ W ⟩ R′

data RepImp W where
  ★⊑★ : ∀ {μ} → μ ⊢ ★ ⊑ᴿ⟨ W ⟩ ★
  ι⊑ι : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ι
  X⊑X : ∀ {μ X m} → μ ∋ˡ X := m → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ` X
  α⊑β : ∀ {μ α β} → Paired W α β
    → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ` (length μ + β)
  ⇒⊑⇒ : ∀ {μ R R′ S S′}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ S ⊑ᴿ⟨ W ⟩ S′
    → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ R′ ⇒ S′
  ∀⊑∀ : ∀ {μ R R′} → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ `∀ R′
  ⇒⊑★ : ∀ {μ R S}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ S ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ ★
  ι⊑★ : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ★
  X⊑★ : ∀ {μ X} → μ ∋ˡ X := X⊑★ → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ★
  α⊑★ : ∀ {μ α} → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ★
  ∀⊑  : ∀ {μ R R′} → NonVar R → 0 ∈ᵗ R
    → instᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ⇑ᵗ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ R′
  ∀★⊑★ : ∀ {μ} → μ ⊢ `∀ ★ ⊑ᴿ⟨ W ⟩ ★
  ∀⊑★ : ∀ {μ R} → NonStar R → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ★
    → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ ★
  bot-elim : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ `∀ ★
  bot⊑★ : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ ★

data Agree (W : World Δ Δ′) (α β : RVar) : Set where
  abst-abst : reps Δ ∋ʳ α := abstR → reps Δ′ ∋ʳ β := abstR → Agree W α β
  abst-★    : reps Δ ∋ʳ α := abstR → Δ′ ∋rep β := ★      → Agree W α β
  rep-rep   : ∀ {R R′} → Δ ∋rep α := R → Δ′ ∋rep β := R′
    → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′ → Agree W α β
```

## Design choices and reasons

1. **The rules are `_⊢_⊑_`'s rules (Imprecision.agda), one for one.**
   Payloads are types in the representation universe, so their
   imprecision should be the same lattice as for ordinary types.  `∀⊑∀`
   extends `μ` with `X⊑X`, and `∀⊑` / `∀⊑★` use `instᵐ` / `extᵐ`
   exactly as `_⊢_⊑_` does.

2. **`X⊑X` is split into a local case and a free case.**
   - In `_⊢_⊑_`, every variable is a center name, so `X⊑X` needs no
     premise.  Here an index is local exactly when it is
     `< length μ`.  The local `X⊑X` therefore requires `μ ∋ˡ X := m`.
     The local `X⊑★` requires `μ ∋ˡ X := X⊑★`, as before.
   - **Free rep. vars correspond through `Paired W` (ϱᵍ ∪ ϱˡ).**  Rep.
     vars are global (D12).  `ϱ` relates them across the two sides, just
     as the center relates names.  The rule reads no names, so a
     boundary that hides a name does not affect it.
   - The two sides share one local count `length μ`.  `∀⊑` shifts the
     right side with `⇑ᵗ`, and that shift moves the right side's free
     indices consistently: `⇑ᵗ (` (length μ + β))` is, by definition,
     `` ` (length (instᵐ μ) + β) ``.

3. **A free left rep. var against `★` (`α⊑★`) has no side condition.**
   The reasons:
   - A rep. var carries no mark.  Marks belong to names (D11, D12).
     In the old reading, `` ` α ⊑ ★ `` required that α's name have mark
     `X⊑★`.  Requiring a mark here would mean reading through names
     again, which is the reading that failed.
   - It is the free-variable instance of the case `Agree` already had at
     top level: `abst-★` allows an abstract left rep. var against `β:=★`.
   - Semantically, `α` stands for its own payload, and that payload has
     its own `Agree` obligation.  Against `★`, the payload is expected to
     be `⊑ ★`, because `★` is the top of `⊑` for closed and free-rep.-var
     types.  I have not proved this "★ is top" lemma for `RepImp`.
   - **For you to confirm:** this rule is looser than the old relation
     in one case.  Before, a left payload `` ` α `` against `★` was
     rejected when α's name had mark `X⊑X`.  Now it is accepted.

4. **No rule puts a free rep. var on the right without its partner on
   the left.**  This mirrors `_⊢_⊑_`, where a right variable faces only
   the same variable.  A concrete left payload against an abstract right
   rep. var stays unrelated, as before.

5. **`abst-abst` and `abst-★` are kept, not subsumed.**  `RepImp`
   relates payloads, and an abstract rep. var (`abstR`) has no payload.
   They would be subsumed only if an abstract α were read as its own
   payload `` ` α ``.  Then `abst-abst` would become `α⊑β` and `abst-★`
   would become `α⊑★`.  I did not take that simplification, to keep the
   edit minimal.

## Examples re-checked

- `examples/TermImprecisionExamples.agda`: `Wᵢ₁-wf` (`ℕ ⊑ ★`, now
  `ι⊑★ base-ℕ`) and `Wᵢ₆-wf` (`𝔹 ⊑ 𝔹`).
- `examples/TermImprecisionRebaseExamples.agda`: the six `agree`
  functions (ℕ/ℕ and ℕ/★ payloads; `abst-★` and `abst-abst` unchanged).
- `proof/DGG/Evolve.agda`: the premises `ev-2` / `ev-L⇔` are
  `Agree (alloc² R R′ W) zero zero` / `Agree (allocᴸ⇔ R β W) zero β`.
  They are unchanged in form and now mean `RepImp` of the new pair's
  payloads.
- **Regression, `drafts/EvolveImpWfInteriorCounterexample.agda`.**
  - The configuration: X names rep. var 0 := ℕ, and (0, 0) is a global
    pair.  The terms are `$1 ⟪ unbind X , id ℕ ⟫` on both sides.
  - One matched TyBeta happens, with payload `` ` 0 `` on both sides.
  - After allocation, the payloads of pair (0, 0) are `` ` 1 ``.  The
    proof `` ` 1 ⊑ᴿ ` 1 `` is `α⊑β` from the pair (1, 1).
  - The file proves `wf₁ : WfWorld W₁` and `wfᵢ₁ : WfWorld Wᵢ₁`, where
    `Wᵢ₁` is the interior world of the shifted boundary: no names, pairs
    (0, 0) and (1, 1).
  - It also proves `M₁⊑M₁` and `evolved`, which is EvolveImp's
    conclusion at this instance:

    ```agda
    WfWorld W₁ × Σ[ q ∈ `ℕ ⊑ᵂ⟨ W₁ ⟩ `ℕ ]
      (W₁ ∣ [] ⊢ ↑ᴹ*[ new R₀ ∷ [] ] M₀ ⊑ ↑ᴹ*[ new R₀ ∷ [] ] M₀ ∶ q)
    ```

## Open obligations created

`drafts/AllocImpCorollariesProof.agda`'s `wf-alloc*` holes now need a
renaming lemma for `RepImp` under the allocation renumberings
(`shiftᴸ`/`shift²`, which move both payload indices and ϱ).  No hole was
added.

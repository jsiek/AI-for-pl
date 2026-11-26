module proof.LR.CastLemma where

-- File Charter:
--   * The cast lemma (notes/logrel-dgg.md, Section 6.9, item 7): casts
--     at related types, in eager normal form, take related values to
--     related expressions.  It includes the world-change cases, where a
--     side allocates store variables (Section 7, "The cast lemma's
--     world-change cases").
--   * Casts are over the type context Δ (`LR.CastPrecision`); they are
--     read at the world through the interpretation (`CastHyp`):
--       - left: `subst∼` with a `SubstEnv∼` for the cast's modes at δl;
--       - right: `subst∼` with a `SubstEnv∼` at a store substitution σR,
--         since right terms live in the store; σR is tied to δr by
--         `PreB` equations, for the cast's two types only.
--   * The hypothesis is `𝒱ᵀ` (the right value typed); the conclusion is
--     `ℰ` at the target precision.
--   * `CastHyp` also carries what the cases need of δ: its leaves are
--     good and closed under later conversions on either side (the
--     conversion lemmas, used by the `∀` cases), and the cast lemma
--     holds at its variables (`VarI`, the base cases, which only the
--     caller can discharge), in every future of w with the casts
--     renamed into it (`renSE`): a leaf may relate values that exist
--     only in the future.  It also holds at the flipped environments
--     (`varF`), which a function's domain cast reads.  A variable at
--     which `Z!` or `？Z` can occur (mode not `X∼X`) is not read as
--     `★` (`starFree`), so a cast is the identity at its ground after
--     δl only if it is before (`proof.LR.CastCases3`, `collapse!ι`);
--     the same on the right with σR (`starFreeR`, for the row `!`
--     against `!`).
--   * `flipHyp`: the hypotheses at the flipped environments (for a
--     function's domain; `sym∼` is involutive up to `≅ᶜ`,
--     `agree-FF`); `CastHyp-↑`: the hypotheses in a future, the casts
--     renamed into it (`agree-renSE`).  Both move `VarI` by `VarI-≅`
--     (equivalent interpretations, environments that agree).
--   * Moving `VarI` between interpretations: `ℰ-conv`, `CastRel-map`,
--     `CastRel-resp`; `VarI-ext`, `VarI` under one more left-only
--     variable (case 6), from `VarI` before it and agreeing
--     environments (`Agree`).
--   * The statement is `CastLemma`; `CastCase c c′` is its instance at
--     two given casts, the shape of an induction hypothesis.
--   * Cases proved: `id` against `id` at `★` and at base types, and at
--     variables (from `VarI` at the reflexive extension).  The other
--     cases without world change are in `proof.LR.CastCases`, and the
--     induction, with the open cases as its hypotheses, in
--     `proof.LR.CastInduction`.
--   * `ℰ-down`: the expression relation is downward closed in the stage,
--     in both directions (for `inner` below, in `≺`).
--   * Case 6 (left `∀ᶜ`, right `inst`, from `∀⊑∀` to `∀⊑`; module
--     `Case6`) is proved from the induction hypothesis at
--     `c₁` against `c₁′ [ ★/0 ]ᶜ` and the obligations `Case6Ob`:
--       - proved here: the right's allocation and the run to its value
--         (`inst-cast-value`, determinism), the clause of the `∀⊑` value
--         it arrives at, the left's `β-∀` step, the replay
--         (`ℰ-stepReplay`), the bound of the new variable's leaf in `≻`
--         (`lowOnly`), and the bind around the casts (`coreFrom`); the
--         replay's stage s has s + 1 ≤ n (`rstage-<`; in `≻` the
--         right's allocation is counted, `antiR₁⁺`, `AllocB`), so the
--         hypothesis's clause can be used at s + 1;
--       - obligations, at the replay world (`AtReplay.Ob`): the
--         instantiations inside the casts (the hypothesis's clause, the
--         right-only reveal of α′ as `★`, the substitution instance
--         `pairStarˢ`), the typing of the right's instantiation, and the
--         casts read through the extended interpretation (cast
--         substitution composes; `VarI` for the new variable).
--       - `proof.LR.Case6` discharges all of them (`case6R`).

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _≤?_; s≤s; z≤n;
  _<_; _≤′_; ≤′-refl)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤′⇒≤;
  ≰⇒>; n≤1+n; +-monoʳ-≤; m≤n+m; ≤⇒≤′;
  m+[n∸m]≡n; ∸-monoˡ-≤; m+n∸m≡n; m∸n≤m)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; ¬_)

open import Types
open import Consistency
open import Conversion using (〖_,_↑_〗)
open import CastTerms using (Term; Value; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ;
  renameᵗᵐ; _《_》; all)
open import Reduction using (StoreChanges; []; _∷_; bind; applyBody; _—→_;
  _—→[_]_;
  applyStores; β-∀; β-inst; β-id; ↠-refl; ↠-step; StoreChange)
open import LR.Precision
open import proof.LR.PrecisionSubst using (PSub; σl; σr; σ↔; σo; substᵖ)
open import LR.EagerCast using (Eager)
open import LR.Desc
open import LR.World
open import LR.Steps using (_—→^_[_]_; Runs; none; more; steps→↠;
  embedᶜˢ)
open import LR.Relation
open import proof.TypeInTermSubst using (toRename-id-eq;
  renameᵗᵐ-preserves-Value)
open import proof.Reduction.Determinism using (det)
open import proof.TypeSafety.InstValue using (inst-cast-value)
open import proof.LR.WorldProps using (renameTy-id; ⊒-refl; ⊒-trans)
open import proof.LR.InterpProps using (exts-cong; ℰᵍ-≡; ℰᵍ-map; _≈ᴵ_; _≈ˡ_;
  ≈ˡ-sym; ≈ᴵ-sym; ≈ᴵ-refl; ↑ᴵ-refl; ↑ᴵ-trans; transportLeaf-resp;
  leafRel-resp; 𝒱-resp; ℰ-resp)
open import proof.TermRename using (cast-id; renameEnv∼-id; renameEnv∼-∘;
  toRenameᵗ-∘′)
open import proof.DGG.CenterRename using (_∘↪_)
open import proof.LR.CastSubst using (renAfter; Agree; aself; ato; afrom;
  acto; acfrom; _≅ᶜ_; hrefl; ≅ᶜ-⟨⟩; ≅-sym; agree-FL; agree-FF; flip-flip;
  renameEnv-flip; agree-ren; agree-flip; irr)
open import proof.LR.Monotone using (GoodI; GoodI-↑; GoodI-extOnlyI; 𝒱≤-cast;
  onlyLeafS-good; G≤→G; G→G≤; peelSL-map; 𝒱-down)
open import proof.LR.Expression using (stepExt; ℰ-value; ℰ-anti-≺;
  ℰ-anti-≻; ℰ-stepL; ℰ-stepR; ℰ-bind₂ᵀ)
open import LR.Frame using (cast)
open import proof.LR.ConvBase using (ℰ-zero)
open import proof.LR.ConvLemma using (FreshP; FreshO; both; ℰL; PreB;
  pre-typed; ∀-inj; stᴬ; _↑ˢ_; FreshP-↑; FreshO-↑)
open import proof.LR.ConvMain using (allOnly-from; 𝒱-∀⊑⇒; 𝒱-∀⊑∀;
  nv⊑var; ⊑ι-closed)
open import proof.LR.SubstLemma using (to; from; iff; 𝒱-XY; 𝒱-X★;
  ℰᵍ-map⁺; SubI; sl≡; sr≡; sonly; spair; SubI-↑; 𝒱-subst)
open import proof.LR.PrecisionUnique using (⊑-unique; ↔-unique; only-unique)
open import proof.LR.ConvRight using (FreshR; FreshR-↑; worldR; extR;
  tagsR; okBindR)
open import proof.LR.Replay using (replayW; replayPre; release-coh;
  ℰ-replay≻ᵛ; ℰ-replay≺ᵛ)

------------------------------------------------------------------------
-- Casts at variables
------------------------------------------------------------------------

-- the cast into `★` that a substitution gives a variable of mode v
toW : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
  → SubstEnv∼ μ ν σ → ∀ X {v} → μ ‼ X ≡ v → VarTo★ v → ν ⊢ σ X ∼ ★
toW s X eq to★-dynamic = SubstEnv∼.to-★ s X eq
toW s X eq to★-cross = SubstEnv∼.cross-to-★ s X eq

-- the cast out of `★`
fromW : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
  → SubstEnv∼ μ ν σ → ∀ X {v} → μ ‼ X ≡ v → ★ToVar v → ν ⊢ ★ ∼ σ X
fromW s X eq from★-dynamic = SubstEnv∼.from-★ s X eq
fromW s X eq from★-cross = SubstEnv∼.cross-from-★ s X eq

-- the casts at hand take values related at p to expressions related at
-- r, at every stage
CastRel : Dir → ℕ → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
  → Φ ⊢ A ⊑ A′ → Φ ⊢ B ⊑ B′ → (w : World) → Interp Δ Δ′ (ΔL w) (ΔR w)
  → (Term (ΔL w) → Term (ΔL w)) → (Term (storeR w) → Term (storeR w))
  → Set
CastRel d k p r w δ fl fr = ∀ {Vl Vr} → Value Vl → Value Vr
  → 𝒱 d k p w δ Vl Vr → ℰ d k r w δ (fl Vl) (fr Vr)

------------------------------------------------------------------------
-- The hypotheses
------------------------------------------------------------------------

module _ {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (w : World)
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) where

  -- The cast lemma at the variables, at every stage: the casts that
  -- `subst∼` puts at a variable's positions, against the right's cast
  -- there.  These are its base cases, and only the caller knows the
  -- leaves well enough to prove them.
  record VarI {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {νL : Env∼ (ΔL w)}
      {νR : Env∼ (storeR w)} {σR : Δ′ ⇒ˢ storeR w}
      (sL : SubstEnv∼ ν νL (δl δ)) (sR : SubstEnv∼ ν′ νR σR) : Set where
    field
      -- `id` at X ⊑ Y, and at X ⊑ ★ (the right cast is `id ★`)
      selfP : ∀ {Z Y′} (x : Φ ∋ Z ↔ Y′) k
        → CastRel d k (X⊑Y x) (X⊑Y x) w δ
            (λ V → V ⟨ SubstEnv∼.self sL Z ⟩)
            (λ V → V ⟨ SubstEnv∼.self sR Y′ ⟩)
      selfO : ∀ {Z} (o : Φ ∋ Z only) k
        → CastRel d k (X⊑★ o) (X⊑★ o) w δ
            (λ V → V ⟨ SubstEnv∼.self sL Z ⟩) (λ V → V ⟨ id {μ = νR} ★ ⟩)
      -- `Z!` against `Y′!`, and against `id ★`
      toP : ∀ {Z Y′} (x : Φ ∋ Z ↔ Y′) {v v′}
        (eq : ν ‼ Z ≡ v) (t : VarTo★ v) (eq′ : ν′ ‼ Y′ ≡ v′)
        (t′ : VarTo★ v′) k
        → CastRel d k (X⊑Y x) ★⊑★ w δ
            (λ V → V ⟨ toW sL Z eq t ⟩) (λ V → V ⟨ toW sR Y′ eq′ t′ ⟩)
      toO : ∀ {Z} (o : Φ ∋ Z only) {v} (eq : ν ‼ Z ≡ v) (t : VarTo★ v) k
        → CastRel d k (X⊑★ o) ★⊑★ w δ
            (λ V → V ⟨ toW sL Z eq t ⟩) (λ V → V ⟨ id {μ = νR} ★ ⟩)
      -- `？Z` against `？Y′`, and against `id ★`
      fromP : ∀ {Z Y′} (x : Φ ∋ Z ↔ Y′) {v v′}
        (eq : ν ‼ Z ≡ v) (t : ★ToVar v) (eq′ : ν′ ‼ Y′ ≡ v′)
        (t′ : ★ToVar v′) k
        → CastRel d k ★⊑★ (X⊑Y x) w δ
            (λ V → V ⟨ fromW sL Z eq t ⟩) (λ V → V ⟨ fromW sR Y′ eq′ t′ ⟩)
      fromO : ∀ {Z} (o : Φ ∋ Z only) {v} (eq : ν ‼ Z ≡ v) (t : ★ToVar v) k
        → CastRel d k ★⊑★ (X⊑★ o) w δ
            (λ V → V ⟨ fromW sL Z eq t ⟩) (λ V → V ⟨ id {μ = νR} ★ ⟩)

-- an environment renamed along an embedding (into a future world)
renSE : ∀ {Δ Θ Θ′} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ} (ρ : Θ ↪ᵗ Θ′)
  → SubstEnv∼ μ ν σ
  → SubstEnv∼ μ (renameEnv∼ ρ ν) (λ X → renameᵗ (toRenameᵗ ρ) (σ X))
renSE {ν = ν} ρ s =
  renAfter {ν′ = renameEnv∼ ρ ν} (toRenameᵗ ρ) (renameEnv∼-preserves ρ ν) s

module _ {Δ Δ′} (Φ : Corr Δ Δ′) (d : Dir) (w : World)
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) where

  -- how the casts are read at w, and what the cases need of δ
  record CastHyp (ν : Env∼ Δ) (ν′ : Env∼ Δ′) : Set₁ where
    field
      {νL} : Env∼ (ΔL w)
      sL : SubstEnv∼ ν νL (δl δ)
      {νR} : Env∼ (storeR w)
      σR : Δ′ ⇒ˢ storeR w
      sR : SubstEnv∼ ν′ νR σR
      -- the leaves are good, and closed under later conversions: the
      -- left's and both sides' (`FreshP`, `FreshO`), and the right's
      -- alone (`FreshR`)
      good : GoodI δ
      freshP : ∀ {Z Y′} → Φ ∋ Z ↔ Y′
        → FreshP d both w (leaf δ Z) (δl δ Z) (σR Y′)
      freshO : ∀ {Z} → Φ ∋ Z only → FreshO d w (leaf δ Z) (δl δ Z)
      freshR : ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → FreshR d w (leaf δ Z) (σR Y′)
      -- a variable at which `Z!` or `？Z` can occur is not read as `★`
      -- (notes/logrel-dgg.md, "The ★ field of VarI")
      starFree : ∀ Z → ν ‼ Z ≢ X∼X → δl δ Z ≢ ★
      -- the same on the right (notes/logrel-dgg.md, "Right starFree")
      starFreeR : ∀ Y → ν′ ‼ Y ≢ X∼X → σR Y ≢ ★
      -- the lemma at the variables, in every future (the casts renamed
      -- into it): a leaf may relate values that exist only there
      var : ∀ {w″} (e″ : w″ ⊒ w)
        → VarI Φ d w″ (δ ↑ᴵ e″) (renSE (ρL e″) sL) (renSE (ρS e″) sR)
      -- the same at the flipped environments, for a function's domain
      -- (notes/logrel-dgg.md, "The cast lemma: the case table")
      varF : ∀ {w″} (e″ : w″ ⊒ w)
        → VarI Φ d w″ (δ ↑ᴵ e″) (flip-SubstEnv∼ (renSE (ρL e″) sL))
            (flip-SubstEnv∼ (renSE (ρS e″) sR))

  open CastHyp public

------------------------------------------------------------------------
-- Moving the casts at the variables between interpretations
------------------------------------------------------------------------

private
  -- `★⊑★` does not read the interpretation
  ★⊑★-at : ∀ d k {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′}
      {Φ₂ : Corr Δ₂ Δ₂′} w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)} {V V′}
    → 𝒱 d k (★⊑★ {Φ = Φ₁}) w δ₁ V V′ → 𝒱 d k (★⊑★ {Φ = Φ₂}) w δ₂ V V′
  ★⊑★-at ≺ k w r = r
  ★⊑★-at ≻ zero w r = r
  ★⊑★-at ≻ (suc k) w r = r

-- the expression relation along a map of the value relations in the
-- futures
ℰ-conv : ∀ d k {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′} {Φ₂ : Corr Δ₂ Δ₂′}
    {A₁ A₁′ A₂ A₂′} (r₁ : Φ₁ ⊢ A₁ ⊑ A₁′) (r₂ : Φ₂ ⊢ A₂ ⊑ A₂′) w
    {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)} {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
  → (∀ {m} w′ (e : w′ ⊒ w) {V V′} → 𝒱 d m r₁ w′ (δ₁ ↑ᴵ e) V V′
       → 𝒱 d m r₂ w′ (δ₂ ↑ᴵ e) V V′)
  → ∀ {Ml Mr} → ℰ d k r₁ w δ₁ Ml Mr → ℰ d k r₂ w δ₂ Ml Mr
ℰ-conv d k r₁ r₂ w f =
  ℰᵍ-map d k w (λ le w′ e V V′ a →
    𝒱≤-cast d ≤′-refl le r₂ w′ (f w′ e (𝒱≤-cast d le ≤′-refl r₁ w′ a)))

-- the casts at hand, moved to other derivations, interpretations and
-- equal casts
CastRel-map : ∀ d k {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′}
    {Φ₂ : Corr Δ₂ Δ₂′} {A₁ A₁′ B₁ B₁′ A₂ A₂′ B₂ B₂′}
    {p₁ : Φ₁ ⊢ A₁ ⊑ A₁′} {r₁ : Φ₁ ⊢ B₁ ⊑ B₁′} {p₂ : Φ₂ ⊢ A₂ ⊑ A₂′}
    {r₂ : Φ₂ ⊢ B₂ ⊑ B₂′} w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
    {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    {fl₁ fl₂ : Term (ΔL w) → Term (ΔL w)}
    {fr₁ fr₂ : Term (storeR w) → Term (storeR w)}
  → (∀ {V V′} → 𝒱 d k p₂ w δ₂ V V′ → 𝒱 d k p₁ w δ₁ V V′)
  → (∀ {m} w′ (e : w′ ⊒ w) {V V′} → 𝒱 d m r₁ w′ (δ₁ ↑ᴵ e) V V′
       → 𝒱 d m r₂ w′ (δ₂ ↑ᴵ e) V V′)
  → (∀ V → fl₁ V ≡ fl₂ V) → (∀ V → fr₁ V ≡ fr₂ V)
  → CastRel d k p₁ r₁ w δ₁ fl₁ fr₁ → CastRel d k p₂ r₂ w δ₂ fl₂ fr₂
CastRel-map d k {r₁ = r₁} {r₂ = r₂} w fv fe el er c vl vr a =
  ℰᵍ-≡ (el _) (er _) (ℰ-conv d k r₁ r₂ w fe (c vl vr (fv a)))

-- the casts at hand, at an equivalent interpretation
CastRel-resp : ∀ d k {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′}
    (p : Φ ⊢ A ⊑ A′) (r : Φ ⊢ B ⊑ B′) w
    {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {fl fr}
  → δ ≈ᴵ δ′ → CastRel d k p r w δ fl fr → CastRel d k p r w δ′ fl fr
CastRel-resp d k p r w h c vl vr a =
  ℰ-resp d k r w h (c vl vr (𝒱-resp d k p w (≈ᴵ-sym h) a))

-- the casts a substitution gives a variable, in agreeing environments
toW-≅ : ∀ {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν ν′ : Env∼ Θ}
    {ρ : Δ ⇒ʳ Δ′} {σ : Δ ⇒ˢ Θ} {σ′ : Δ′ ⇒ˢ Θ} {s : SubstEnv∼ μ ν σ}
    {s′ : SubstEnv∼ μ′ ν′ σ′} → Agree ρ s s′
  → ∀ X {v} (eq′ : μ′ ‼ ρ X ≡ v) (eq : μ ‼ X ≡ v) (t : VarTo★ v)
  → toW s′ (ρ X) eq′ t ≅ᶜ toW s X eq t
toW-≅ a X eq′ eq to★-dynamic = ato a X eq′ eq
toW-≅ a X eq′ eq to★-cross = acto a X eq′ eq

fromW-≅ : ∀ {Δ Δ′ Θ} {μ : Env∼ Δ} {μ′ : Env∼ Δ′} {ν ν′ : Env∼ Θ}
    {ρ : Δ ⇒ʳ Δ′} {σ : Δ ⇒ˢ Θ} {σ′ : Δ′ ⇒ˢ Θ} {s : SubstEnv∼ μ ν σ}
    {s′ : SubstEnv∼ μ′ ν′ σ′} → Agree ρ s s′
  → ∀ X {v} (eq′ : μ′ ‼ ρ X ≡ v) (eq : μ ‼ X ≡ v) (t : ★ToVar v)
  → fromW s′ (ρ X) eq′ t ≅ᶜ fromW s X eq t
fromW-≅ a X eq′ eq from★-dynamic = afrom a X eq′ eq
fromW-≅ a X eq′ eq from★-cross = acfrom a X eq′ eq

-- VarI under one more left-only variable (case 6): at the old
-- variables it is VarI before the variable, through agreeing
-- environments and equivalent leaves; at the new one it is `new`
module _ {Δ Δ′} {Φ : Corr Δ Δ′} (d : Dir) (w : World)
    {δ₁ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {δ₂ : Interp (suc Δ) Δ′ (ΔL w) (ΔR w)} {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
    {νL₁ νL₂ : Env∼ (ΔL w)} {νR₁ νR₂ : Env∼ (storeR w)}
    {σR₁ σR₂ : Δ′ ⇒ˢ storeR w}
    {sL₁ : SubstEnv∼ ν νL₁ (δl δ₁)} {sR₁ : SubstEnv∼ ν′ νR₁ σR₁}
    {sL₂ : SubstEnv∼ (extᵐ ν) νL₂ (δl δ₂)} {sR₂ : SubstEnv∼ ν′ νR₂ σR₂}
    (lv : ∀ Z → leaf δ₁ Z ≈ˡ leaf δ₂ (suc Z))
    (aL : Agree suc sL₁ sL₂) (aR : Agree (λ Y → Y) sR₁ sR₂)
    (eR : νR₁ ≡ νR₂)
  where

  private
    up : ∀ Z {m} w′ (e : w′ ⊒ w) {V V′}
      → leafRel d m w′ (leaf (δ₁ ↑ᴵ e) Z) V V′
      → leafRel d m w′ (leaf (δ₂ ↑ᴵ e) (suc Z)) V V′
    up Z w′ e =
      leafRel-resp d _ w′ (transportLeaf-resp (ρL e) (ρR e) (lv Z))

    down : ∀ Z {m} {V V′} → leafRel d m w (leaf δ₂ (suc Z)) V V′
      → leafRel d m w (leaf δ₁ Z) V V′
    down Z = leafRel-resp d _ w (≈ˡ-sym (lv Z))

    vP : ∀ {Z Y′} (x : Φ ∋ Z ↔ Y′) {m V V′}
      → 𝒱 d m (X⊑Y (↔-only x)) w δ₂ V V′ → 𝒱 d m (X⊑Y x) w δ₁ V V′
    vP x a = to (𝒱-XY d _ x w) (down _ (from (𝒱-XY d _ (↔-only x) w) a))

    uP : ∀ {Z Y′} (x : Φ ∋ Z ↔ Y′) {m} w′ (e : w′ ⊒ w) {V V′}
      → 𝒱 d m (X⊑Y x) w′ (δ₁ ↑ᴵ e) V V′
      → 𝒱 d m (X⊑Y (↔-only x)) w′ (δ₂ ↑ᴵ e) V V′
    uP x w′ e a =
      to (𝒱-XY d _ (↔-only x) w′) (up _ w′ e (from (𝒱-XY d _ x w′) a))

    vO : ∀ {Z} (o : Φ ∋ Z only) {m V V′}
      → 𝒱 d m (X⊑★ (only-only o)) w δ₂ V V′ → 𝒱 d m (X⊑★ o) w δ₁ V V′
    vO o a = to (𝒱-X★ d _ o w) (down _ (from (𝒱-X★ d _ (only-only o) w) a))

    uO : ∀ {Z} (o : Φ ∋ Z only) {m} w′ (e : w′ ⊒ w) {V V′}
      → 𝒱 d m (X⊑★ o) w′ (δ₁ ↑ᴵ e) V V′
      → 𝒱 d m (X⊑★ (only-only o)) w′ (δ₂ ↑ᴵ e) V V′
    uO o w′ e a =
      to (𝒱-X★ d _ (only-only o) w′) (up _ w′ e (from (𝒱-X★ d _ o w′) a))

    id★ : ∀ V → V ⟨ id {μ = νR₁} ★ ⟩ ≡ V ⟨ id {μ = νR₂} ★ ⟩
    id★ V = cong (λ μ → V ⟨ id {μ = μ} ★ ⟩) eR

  VarI-ext : VarI Φ d w δ₁ sL₁ sR₁
    → (∀ k → CastRel d k (X⊑★ (only-here {Φ = Φ})) (X⊑★ only-here) w δ₂
         (λ V → V ⟨ SubstEnv∼.self sL₂ zero ⟩)
         (λ V → V ⟨ id {μ = νR₂} ★ ⟩))
    → VarI (only Φ) d w δ₂ sL₂ sR₂
  VarI.selfP (VarI-ext v new) (↔-only {X = Z} {Y = Y′} x) k =
    CastRel-map d k w
      (vP x)
      (uP x)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (aself aL Z)))
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (aself aR Y′)))
      (VarI.selfP v x k)
  VarI.selfO (VarI-ext v new) only-here k = new k
  VarI.selfO (VarI-ext v new) (only-only {X = Z} o) k =
    CastRel-map d k w
      (vO o)
      (uO o)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (aself aL Z))) id★
      (VarI.selfO v o k)
  VarI.toP (VarI-ext v new) (↔-only {X = Z} {Y = Y′} x) eq t eq′ t′ k =
    CastRel-map d k w
      (vP x)
      (λ w′ e a → ★⊑★-at d _ w′ a)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (toW-≅ aL Z eq eq t)))
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (toW-≅ aR Y′ eq′ eq′ t′)))
      (VarI.toP v x eq t eq′ t′ k)
  VarI.toO (VarI-ext v new) only-here refl ()
  VarI.toO (VarI-ext v new) (only-only {X = Z} o) eq t k =
    CastRel-map d k w
      (vO o)
      (λ w′ e a → ★⊑★-at d _ w′ a)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (toW-≅ aL Z eq eq t))) id★
      (VarI.toO v o eq t k)
  VarI.fromP (VarI-ext v new) (↔-only {X = Z} {Y = Y′} x) eq t eq′ t′ k =
    CastRel-map d k w
      (λ a → ★⊑★-at d k w a)
      (uP x)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (fromW-≅ aL Z eq eq t)))
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (fromW-≅ aR Y′ eq′ eq′ t′)))
      (VarI.fromP v x eq t eq′ t′ k)
  VarI.fromO (VarI-ext v new) only-here refl ()
  VarI.fromO (VarI-ext v new) (only-only {X = Z} o) eq t k =
    CastRel-map d k w
      (λ a → ★⊑★-at d k w a)
      (uO o)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (fromW-≅ aL Z eq eq t))) id★
      (VarI.fromO v o eq t k)

-- VarI at equivalent interpretations and environments with the same
-- modes and the same casts
module _ {Δ Δ′} {Φ : Corr Δ Δ′} (d : Dir) (w : World)
    {δ₁ δ₂ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ν₁ ν₂ : Env∼ Δ}
    {ν₁′ ν₂′ : Env∼ Δ′} {νL₁ νL₂ : Env∼ (ΔL w)}
    {νR₁ νR₂ : Env∼ (storeR w)} {σR₁ σR₂ : Δ′ ⇒ˢ storeR w}
    {sL₁ : SubstEnv∼ ν₁ νL₁ (δl δ₁)} {sR₁ : SubstEnv∼ ν₁′ νR₁ σR₁}
    {sL₂ : SubstEnv∼ ν₂ νL₂ (δl δ₂)} {sR₂ : SubstEnv∼ ν₂′ νR₂ σR₂}
    (hδ : δ₁ ≈ᴵ δ₂)
    (eL : ∀ Z → ν₂ ‼ Z ≡ ν₁ ‼ Z) (eR : ∀ Y → ν₂′ ‼ Y ≡ ν₁′ ‼ Y)
    (aL : Agree (λ X → X) sL₁ sL₂) (aR : Agree (λ Y → Y) sR₁ sR₂)
    (eνR : νR₁ ≡ νR₂)
  where

  private
    id★ : ∀ V → V ⟨ id {μ = νR₁} ★ ⟩ ≡ V ⟨ id {μ = νR₂} ★ ⟩
    id★ V = cong (λ μ → V ⟨ id {μ = μ} ★ ⟩) eνR

    e₁ : ∀ Z {v} → ν₂ ‼ Z ≡ v → ν₁ ‼ Z ≡ v
    e₁ Z eq = trans (sym (eL Z)) eq

    e₁′ : ∀ Y {v} → ν₂′ ‼ Y ≡ v → ν₁′ ‼ Y ≡ v
    e₁′ Y eq = trans (sym (eR Y)) eq

    mv : ∀ {k} {A A′ B B′} (p : Φ ⊢ A ⊑ A′) (r : Φ ⊢ B ⊑ B′)
        {fl₁ fl₂ : Term (ΔL w) → Term (ΔL w)}
        {fr₁ fr₂ : Term (storeR w) → Term (storeR w)}
      → (∀ V → fl₁ V ≡ fl₂ V) → (∀ V → fr₁ V ≡ fr₂ V)
      → CastRel d k p r w δ₁ fl₁ fr₁ → CastRel d k p r w δ₂ fl₂ fr₂
    mv {k} p r el er c =
      CastRel-resp d k p r w hδ
        (CastRel-map d k w (λ a → a) (λ w′ e a → a) el er c)

  VarI-≅ : VarI Φ d w δ₁ sL₁ sR₁ → VarI Φ d w δ₂ sL₂ sR₂
  VarI.selfP (VarI-≅ v) {Z} {Y′} x k =
    mv (X⊑Y x) (X⊑Y x)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (aself aL Z)))
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (aself aR Y′)))
      (VarI.selfP v x k)
  VarI.selfO (VarI-≅ v) {Z} o k =
    mv (X⊑★ o) (X⊑★ o)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (aself aL Z))) id★
      (VarI.selfO v o k)
  VarI.toP (VarI-≅ v) {Z} {Y′} x eq t eq′ t′ k =
    mv (X⊑Y x) ★⊑★
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (toW-≅ aL Z eq (e₁ Z eq) t)))
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (toW-≅ aR Y′ eq′ (e₁′ Y′ eq′) t′)))
      (VarI.toP v x (e₁ Z eq) t (e₁′ Y′ eq′) t′ k)
  VarI.toO (VarI-≅ v) {Z} o eq t k =
    mv (X⊑★ o) ★⊑★
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (toW-≅ aL Z eq (e₁ Z eq) t))) id★
      (VarI.toO v o (e₁ Z eq) t k)
  VarI.fromP (VarI-≅ v) {Z} {Y′} x eq t eq′ t′ k =
    mv ★⊑★ (X⊑Y x)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (fromW-≅ aL Z eq (e₁ Z eq) t)))
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (fromW-≅ aR Y′ eq′ (e₁′ Y′ eq′) t′)))
      (VarI.fromP v x (e₁ Z eq) t (e₁′ Y′ eq′) t′ k)
  VarI.fromO (VarI-≅ v) {Z} o eq t k =
    mv ★⊑★ (X⊑★ o)
      (λ V → ≅ᶜ-⟨⟩ V (≅-sym (fromW-≅ aL Z eq (e₁ Z eq) t))) id★
      (VarI.fromO v o (e₁ Z eq) t k)

-- an environment agrees with itself
agree-refl : ∀ {Δ Θ} {μ : Env∼ Δ} {ν : Env∼ Θ} {σ : Δ ⇒ˢ Θ}
    (s : SubstEnv∼ μ ν σ) → Agree (λ X → X) s s
aself (agree-refl s) X = hrefl
ato (agree-refl s) X e e′ = irr (SubstEnv∼.to-★ s X) e e′
afrom (agree-refl s) X e e′ = irr (SubstEnv∼.from-★ s X) e e′
acto (agree-refl s) X e e′ = irr (SubstEnv∼.cross-to-★ s X) e e′
acfrom (agree-refl s) X e e′ = irr (SubstEnv∼.cross-from-★ s X) e e′

-- renaming twice is renaming along the composite
agree-renSE : ∀ {Δ Θ₀ Θ₁ Θ₂} {μ : Env∼ Δ} {ν : Env∼ Θ₀} {σ : Δ ⇒ˢ Θ₀}
    (π : Θ₁ ↪ᵗ Θ₂) (η : Θ₀ ↪ᵗ Θ₁) (s : SubstEnv∼ μ ν σ)
  → Agree (λ X → X) (renSE (π ∘↪ η) s) (renSE π (renSE η s))
agree-renSE {ν = ν} π η s =
  agree-ren (toRenameᵗ η) (toRenameᵗ π) (toRenameᵗ (π ∘↪ η))
    (renameEnv∼-preserves η ν)
    (renameEnv∼-preserves π (renameEnv∼ η ν))
    (renameEnv∼-preserves (π ∘↪ η) ν)
    (renameEnv∼-∘ π η ν) (toRenameᵗ-∘′ π η) (agree-refl (renSE η s))

-- a renamed type is `★` only if it was
ren≡★ : ∀ {Θ Θ′} (ρ : Θ ⇒ʳ Θ′) {T : Ty Θ} → renameᵗ ρ T ≡ ★ → T ≡ ★
ren≡★ ρ {★} eq = refl
ren≡★ ρ {＇ X} ()
ren≡★ ρ {‵ ι} ()
ren≡★ ρ {A ⇒ B} ()
ren≡★ ρ {`∀ A} ()

-- the hypotheses at a function's domain: the environments flipped
flipHyp : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {d w} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
  → CastHyp Φ d w δ ν ν′ → CastHyp Φ d w δ (flipᵐ ν) (flipᵐ ν′)
flipHyp {d = d} {ν = ν} {ν′} h = record
  { sL = flip-SubstEnv∼ (sL h)
  ; σR = σR h
  ; sR = flip-SubstEnv∼ (sR h)
  ; good = good h
  ; freshP = freshP h
  ; freshO = freshO h
  ; freshR = freshR h
  ; starFree = λ Z ne → starFree h Z (λ eq →
      ne (trans (flipᵐ-‼ ν Z) (cong flipVar∼ eq)))
  ; starFreeR = λ Y ne → starFreeR h Y (λ eq →
      ne (trans (flipᵐ-‼ ν′ Y) (cong flipVar∼ eq)))
  ; var = λ {w″} e″ → VarI-≅ d w″ ≈ᴵ-refl (λ Z → refl) (λ Y → refl)
      (agree-FL (ρL e″) (sL h)) (agree-FL (ρS e″) (sR h))
      (sym (renameEnv-flip (ρS e″) (νR h))) (varF h e″)
  ; varF = λ {w″} e″ → VarI-≅ d w″ ≈ᴵ-refl
      (λ Z → cong (_‼ Z) (flip-flip ν))
      (λ Y → cong (_‼ Y) (flip-flip ν′))
      (agree-FF (ρL e″) (sL h)) (agree-FF (ρS e″) (sR h))
      (trans (cong (renameEnv∼ (ρS e″)) (sym (flip-flip (νR h))))
        (renameEnv-flip (ρS e″) (flipᵐ (νR h))))
      (var h e″)
  }

-- the hypotheses in a future, the casts renamed into it
CastHyp-↑ : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {d w w′}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
  → CastHyp Φ d w δ ν ν′ → (e : w′ ⊒ w)
  → CastHyp Φ d w′ (δ ↑ᴵ e) ν ν′
CastHyp-↑ {d = d} {δ = δ} h e = record
  { sL = renSE (ρL e) (sL h)
  ; σR = σR h ↑ˢ e
  ; sR = renSE (ρS e) (sR h)
  ; good = GoodI-↑ {δ = δ} (good h) e
  ; freshP = λ {Z} x →
      FreshP-↑ {d = d} e {L = leaf δ Z} {rk = both} (freshP h x)
  ; freshO = λ {Z} o → FreshO-↑ {d = d} e {L = leaf δ Z} (freshO h o)
  ; freshR = λ {Z} x → FreshR-↑ {d = d} e {L = leaf δ Z} (freshR h x)
  ; starFree = λ Z ne eq → starFree h Z ne (ren≡★ (toRenameᵗ (ρL e)) eq)
  ; starFreeR = λ Y ne eq →
      starFreeR h Y ne (ren≡★ (toRenameᵗ (ρS e)) eq)
  ; var = λ {w″} e″ → VarI-≅ d w″ (≈ᴵ-sym (↑ᴵ-trans δ e″ e))
      (λ Z → refl) (λ Y → refl)
      (agree-renSE (ρL e″) (ρL e) (sL h))
      (agree-renSE (ρS e″) (ρS e) (sR h))
      (sym (renameEnv∼-∘ (ρS e″) (ρS e) (νR h)))
      (var h (⊒-trans e″ e))
  ; varF = λ {w″} e″ → VarI-≅ d w″ (≈ᴵ-sym (↑ᴵ-trans δ e″ e))
      (λ Z → refl) (λ Y → refl)
      (agree-flip (agree-renSE (ρL e″) (ρL e) (sL h)))
      (agree-flip (agree-renSE (ρS e″) (ρS e) (sR h)))
      (cong flipᵐ (sym (renameEnv∼-∘ (ρS e″) (ρS e) (νR h))))
      (varF h (⊒-trans e″ e))
  }

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

-- the lemma at two given casts
CastCase : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A : Ty Δ}
    {C′ A′ : Ty Δ′} → ν ⊢ C ∼ A → ν′ ⊢ C′ ∼ A′ → Set₁
CastCase {Δ} {Δ′} {ν} {ν′} {C} {A} {C′} {A′} c c′ =
  ∀ d n {Φ : Corr Δ Δ′} (p : Φ ⊢ C ⊑ C′) (r : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (h : CastHyp Φ d w δ ν ν′)
  → PreB w (δr δ) (σR h) C′ → PreB w (δr δ) (σR h) A′
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱ᵀ d n p w δ Vl Vr
  → ℰ d n r w δ (Vl ⟨ subst∼ (sL h) c ⟩) (Vr ⟨ subst∼ (sR h) c′ ⟩)

CastLemma : Set₁
CastLemma =
  ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C A : Ty Δ} {C′ A′ : Ty Δ′}
    (c : ν ⊢ C ∼ A) (c′ : ν′ ⊢ C′ ∼ A′) → Eager c → Eager c′
  → CastCase c c′

------------------------------------------------------------------------
-- Identity casts at `★` and at base types
------------------------------------------------------------------------

-- both sides take an identity step
ℰ-ids : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr} {μ μ′} {B B′}
    (al : Atom B) (ar : Atom B′)
  → GoodI δ → Value Vl → Value Vr → 𝒱 d n p w δ Vl Vr
  → ℰ d n p w δ (Vl ⟨ id {μ = μ} al ⟩) (Vr ⟨ id {μ = μ′} ar ⟩)
ℰ-ids ≺ zero p w al ar g vl vr r = ℰ-zero ≺ p w
ℰ-ids ≺ (suc m) p w al ar g vl vr r =
  ℰ-stepL ≺ m p w (β-id vl)
    (ℰ-stepR ≺ m p w (β-id vr)
      (ℰ-value ≺ m p w vl vr (𝒱-down ≺ (n≤1+n m) p w g r)))
ℰ-ids ≻ zero p w al ar g vl vr r = ℰ-zero ≻ p w
ℰ-ids ≻ (suc m) p w al ar g vl vr r =
  ℰ-stepR ≻ m p w (β-id vr)
    (ℰ-stepL ≻ m p w (β-id vl)
      (ℰ-value ≻ m p w vl vr (𝒱-down ≻ (n≤1+n m) p w g r)))

-- `id ★` against `id ★`
caseId★ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′}
  → CastCase (id {μ = ν} ★) (id {μ = ν′} ★)
caseId★ d n ★⊑★ ★⊑★ w h pC pA vl vr (t , r) =
  ℰ-ids d n ★⊑★ w ★ ★ (good h) vl vr r

-- `id ι` against `id ι`
caseIdι : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {ι}
  → CastCase (id {μ = ν} (‵ ι)) (id {μ = ν′} (‵ ι))
caseIdι {ι = ι} d n ι⊑ι ι⊑ι w h pC pA vl vr (t , r) =
  ℰ-ids d n ι⊑ι w (‵ ι) (‵ ι) (good h) vl vr r

-- a cast renamed along the identity embedding
ren-refl : ∀ {Θ} {μ : Env∼ Θ} {A B} (c : μ ⊢ A ∼ B) (M : Term Θ)
  → M ⟨ rename∼ {μ = μ} {renameEnv∼ id↪ᵗ μ} (toRenameᵗ id↪ᵗ)
          (renameEnv∼-preserves id↪ᵗ μ) c ⟩
    ≡ M ⟨ c ⟩
ren-refl {μ = μ} c M =
  cast-id (toRenameᵗ id↪ᵗ) (renameEnv∼-preserves id↪ᵗ μ) refl
    (renameEnv∼-id μ) toRename-id-eq c

-- `id Z` against `id Y′` at a paired variable: a base case (`VarI`)
caseVarP : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {Z Y′}
  → CastCase (id {μ = ν} (＇ Z)) (id {μ = ν′} (＇ Y′))
caseVarP d n (X⊑Y x) (X⊑Y x′) w h pC pA vl vr (t , r)
    with ↔-unique x x′
caseVarP d n (X⊑Y {X = Z} {Y = Y′} x) (X⊑Y x′) w {δ} h pC pA vl vr
    (t , r) | refl =
  ℰᵍ-≡ (ren-refl {μ = νL h} (SubstEnv∼.self (sL h) Z) _)
    (ren-refl {μ = νR h} (SubstEnv∼.self (sR h) Y′) _)
    (ℰ-resp d n (X⊑Y x) w (↑ᴵ-refl {w = w} δ)
      (VarI.selfP (var h (⊒-refl w)) x n vl vr
        (𝒱-resp d n (X⊑Y x) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) r)))

-- `id Z` against `id ★` at a left-only variable: a base case
caseVarO : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {Z}
  → CastCase (id {μ = ν} (＇ Z)) (id {μ = ν′} ★)
caseVarO d n (X⊑★ o) (X⊑★ o′) w h pC pA vl vr (t , r)
    with only-unique o o′
caseVarO d n (X⊑★ {X = Z} o) (X⊑★ o′) w {δ} h pC pA {Vr = Vr} vl vr
    (t , r) | refl =
  ℰᵍ-≡ (ren-refl {μ = νL h} (SubstEnv∼.self (sL h) Z) _)
    (cong (λ μ → Vr ⟨ id {μ = μ} ★ ⟩) (renameEnv∼-id (νR h)))
    (ℰ-resp d n (X⊑★ o) w (↑ᴵ-refl {w = w} δ)
      (VarI.selfO (var h (⊒-refl w)) o n vl vr
        (𝒱-resp d n (X⊑★ o) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) r)))

------------------------------------------------------------------------
-- Runs on the right
------------------------------------------------------------------------

-- a run of k steps can take any s ≤ k steps
runs-prefix : ∀ {Δ Δ′ k s} {M : Term Δ} {χs : StoreChanges Δ Δ′} {N}
  → M —→^ k [ χs ] N → s ≤ k → Runs M s
runs-prefix ss z≤n = _ , [] , _ , none
runs-prefix (more st ss) (s≤s le) with runs-prefix ss le
runs-prefix (more st ss) (s≤s le) | Δ″ , χs , N , ss′ =
  Δ″ , _ , N , more st ss′

-- the world a right run from w arrives at, the left unchanged
arrTags : (w : World) {Δ₁ : TyCtx} → ΔR w ↪ᵗ Δ₁ → TyVar (ΔL w)
  → Tag (ΔL w) Δ₁
arrTags w ρ X = renameTag id↪ᵗ ρ (tag w X)

arrOk : ∀ (w : World) {Δ₁} (ρ : ΔR w ↪ᵗ Δ₁) X
  → arrTags w ρ (toRenameᵗ (embedᶜˢ ([] {ΔL w})) X)
    ≡ renameTag (embedᶜˢ ([] {ΔL w})) ρ (tag w X)
arrOk w ρ X = cong (arrTags w ρ) (toRename-id-eq X)

arrW : (w : World) {Θ′ Δ₁ : TyCtx} {χs : StoreChanges (storeR w) Θ′}
    {p₁ : Prefix Θ′ Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
  → Steps (pre w) χs p₁ ρ → World
arrW w {χs = χs} {p₁} {ρ} st =
  mkWorld (ΔL w) _ (arrTags w ρ) _ p₁ (applyStores χs (ΣR w))

arrE : ∀ (w : World) {Θ′ Δ₁} {χs : StoreChanges (storeR w) Θ′}
    {p₁ : Prefix Θ′ Δ₁} {ρ : ΔR w ↪ᵗ Δ₁} (st : Steps (pre w) χs p₁ ρ)
  → arrW w st ⊒ w
arrE w {χs = χs} {ρ = ρ} st =
  stepExt {w = w} [] χs st (arrTags w ρ) (arrOk w ρ)

-- the stages at which a run's arrival is read: any up to s in `≺`; in
-- `≻` the run's k steps are counted first
RunB : Dir → ℕ → ℕ → ℕ → Set
RunB ≺ k m s = m ≤ s
RunB ≻ k m s = k + m ≤ s

-- the left is a value and the right runs to one
ℰ-runR : ∀ d {s} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (q : Φ ⊢ A ⊑ A′)
    (w : World) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml : Term (ΔL w)}
    {Mr : Term (storeR w)} {k Θ′} {χs : StoreChanges (storeR w) Θ′}
    {W : Term Θ′}
  → Value Ml → Mr —→^ k [ χs ] W → Value W
  → (∀ {Δ₁} {p₁ : Prefix Θ′ Δ₁} {ρ} (st : Steps (pre w) χs p₁ ρ) {m}
       → RunB d k m s → 𝒱 d m q (arrW w st) (δ ↑ᴵ arrE w st) Ml W)
  → ℰ d s q w δ Ml Mr
ℰ-runR ≺ {s} q w {χs = χs} vl run vW H with steps (pre w) χs
ℰ-runR ≺ {s} q w {χs = χs} vl run vW H | Δ₁ , p₁ , ρ , st =
  ℰ-anti-≺ q none (steps→↠ run) st (arrTags w ρ) (arrOk w ρ)
    (ℰ-value ≺ s q _ vl vW (H st ≤-refl))
ℰ-runR ≻ {s} q w {k = k} vl run vW H with k ≤? s
ℰ-runR ≻ {s} q w {k = k} vl run vW H | no k≰s =
  inj₁ (runs-prefix run (<⇒≤ (≰⇒> k≰s)))
ℰ-runR ≻ {s} q w {δ = δ} {Ml} {Mr} {k = k} {χs = χs} vl run vW H
    | yes k≤s with steps (pre w) χs
ℰ-runR ≻ {s} q w {δ = δ} {Ml} {Mr} {k = k} {χs = χs} vl run vW H
    | yes k≤s | Δ₁ , p₁ , ρ , st =
  subst (λ m → ℰ ≻ m q w δ Ml Mr) (m+[n∸m]≡n k≤s)
    (ℰ-anti-≻ q ↠-refl run st (arrTags w ρ) (arrOk w ρ)
      (ℰ-value ≻ (s ∸ k) q _ vl vW
        (H st (≤-reflexive (m+[n∸m]≡n k≤s)))))

------------------------------------------------------------------------
-- Replaying the right's run after a left step
------------------------------------------------------------------------


------------------------------------------------------------------------
-- The expression relation is downward closed in the stage
------------------------------------------------------------------------

private
  ∸-arr : ∀ {k m n n′} → k + m ≡ n → n′ ≤ n → n′ ∸ k ≤ m
  ∸-arr {k} {m} refl le =
    ≤-trans (∸-monoˡ-≤ k le) (≤-reflexive (m+n∸m≡n k m))

  ≰→≥ : ∀ {a b} → ¬ (suc a ≤ b) → b ≤ a
  ≰→≥ {a} {b} ¬lt with ≰⇒> ¬lt
  ≰→≥ {a} {b} ¬lt | s≤s le = le

  -- the value at the arrival, one stage lower
  𝒱≤-down : ∀ d {m m′ n n′} (lm : m ≤′ n) (lm′ : m′ ≤′ n′) → m′ ≤ m
    → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′) w
      {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
    → GoodI δ → 𝒱≤ d lm p w δ V V′ → 𝒱≤ d lm′ p w δ V V′
  𝒱≤-down d lm lm′ le p w g r =
    𝒱≤-cast d ≤′-refl lm′ p w
      (𝒱-down d le p w g (𝒱≤-cast d lm ≤′-refl p w r))

ℰ-down : ∀ d {n′ n} → n′ ≤ n → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
    (p : Φ ⊢ A ⊑ A′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Ml Mr}
  → GoodI δ → ℰ d n p w δ Ml Mr → ℰ d n′ p w δ Ml Mr
ℰ-down ≺ le p w g (inj₁ (Δ″ , χs , N , ss)) = inj₁ (runs-prefix ss le)
ℰ-down ≺ {n′} le p w g (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss)))
    with suc k ≤? n′
ℰ-down ≺ {n′} le p w g (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss)))
    | yes lt = inj₂ (inj₁ (k , Δ″ , χs , lt , ss))
ℰ-down ≺ {n′} le p w g (inj₂ (inj₁ (k , Δ″ , χs , k<n , ss)))
    | no ¬lt = inj₁ (runs-prefix ss (≰→≥ ¬lt))
ℰ-down ≺ {n′} le p w {δ} g
    (inj₂ (inj₂ (k , m , lm , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r)))
    with k ≤? n′
ℰ-down ≺ {n′} le p w {δ} g
    (inj₂ (inj₂ (k , m , lm , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r)))
    | yes k≤ =
  inj₂ (inj₂ (k , n′ ∸ k , ≤⇒≤′ (m∸n≤m n′ k) , ΔL′ , χsL , Vl , ΘR′ ,
    χsR , Vr , m+[n∸m]≡n k≤ , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st ,
    tags , ok ,
    𝒱≤-down ≺ lm (≤⇒≤′ (m∸n≤m n′ k)) (∸-arr eq le) p _
      (GoodI-↑ {δ = δ} g (stepExt {w = w} χsL χsR st tags ok)) r))
ℰ-down ≺ {n′} le p w {δ} g
    (inj₂ (inj₂ (k , m , lm , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r)))
    | no k≰ = inj₁ (runs-prefix sl (<⇒≤ (≰⇒> k≰)))
ℰ-down ≻ le p w g (inj₁ (Δ″ , χs , N , ss)) = inj₁ (runs-prefix ss le)
ℰ-down ≻ le p w g (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰ-down ≻ {n′} le p w {δ} g
    (inj₂ (inj₂ (k , m , lm , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r)))
    with k ≤? n′
ℰ-down ≻ {n′} le p w {δ} g
    (inj₂ (inj₂ (k , m , lm , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r)))
    | yes k≤ =
  inj₂ (inj₂ (k , n′ ∸ k , ≤⇒≤′ (m∸n≤m n′ k) , ΔL′ , χsL , Vl , ΘR′ ,
    χsR , Vr , m+[n∸m]≡n k≤ , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st ,
    tags , ok ,
    𝒱≤-down ≻ lm (≤⇒≤′ (m∸n≤m n′ k)) (∸-arr eq le) p _
      (GoodI-↑ {δ = δ} g (stepExt {w = w} χsL χsR st tags ok)) r))
ℰ-down ≻ {n′} le p w {δ} g
    (inj₂ (inj₂ (k , m , lm , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ₁ , p₁ , ρ , st , tags , ok , r)))
    | no k≰ = inj₁ (runs-prefix sr (<⇒≤ (≰⇒> k≰)))

-- the stage s at which a replay is read, for a clause at stage n′: in
-- `≺` the left's type application is counted, in `≻` the right's run
data RStage : Dir → ℕ → ℕ → ℕ → Set where
  r≺ : ∀ {k s} → RStage ≺ k (suc s) s
  r≻ : ∀ {k n′} → RStage ≻ k n′ (k + n′)

-- the stage after the right's allocation at the cast, against the
-- cast's: in `≻` the allocation is counted
AllocB : Dir → ℕ → ℕ → Set
AllocB ≺ s n = n ≤ s
AllocB ≻ s n = s < n

-- the right's allocation step at the cast (as `antiR₁`, keeping the
-- count in `≻`)
antiR₁⁺ : ∀ d {n} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (p : Φ ⊢ A ⊑ A′)
    {w : World} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {ΘR Δ₁} {Ml : Term (ΔL w)}
    {Mr : Term (storeR w)} {Mr′ : Term ΘR} {χR : StoreChange (storeR w) ΘR}
    {p₁ : Prefix ΘR Δ₁} {ρ : ΔR w ↪ᵗ Δ₁}
  → Mr —→[ χR ] Mr′
  → (st : Steps (pre w) (χR ∷ []) p₁ ρ)
  → (tags : TyVar (ΔL w) → Tag (ΔL w) Δ₁)
  → (ok : ∀ X → tags (toRenameᵗ (embedᶜˢ ([] {ΔL w})) X)
            ≡ renameTag (embedᶜˢ ([] {ΔL w})) ρ (tag w X))
  → (∀ {s} → s ≤ n → AllocB d s n
       → ℰ d s p
           (mkWorld (ΔL w) Δ₁ tags ΘR p₁ (applyStores (χR ∷ []) (ΣR w)))
           (δ ↑ᴵ stepExt {w = w} [] (χR ∷ []) st tags ok) Ml Mr′)
  → ℰ d n p w δ Ml Mr
antiR₁⁺ ≺ p sr st tags ok k =
  ℰ-anti-≺ p none (↠-step sr ↠-refl) st tags ok (k ≤-refl ≤-refl)
antiR₁⁺ ≻ {zero} p sr st tags ok k = ℰ-zero ≻ p _
antiR₁⁺ ≻ {suc s} p sr st tags ok k =
  ℰ-anti-≻ p ↠-refl (more sr none) st tags ok (k (n≤1+n s) ≤-refl)

-- the replay's stage is below the hypothesis's: in `≺` the left's
-- type application is counted, in `≻` the right's allocation
rstage-< : ∀ d {k n′ m s₀ N s} → RStage d k n′ s → n′ ≤ m → RunB d k m s₀
  → s₀ ≤ N → AllocB d s₀ N → suc s ≤ N
rstage-< ≺ r≺ le b le₀ up = ≤-trans le (≤-trans b le₀)
rstage-< ≻ {k} r≻ le b le₀ up =
  ≤-trans (s≤s (≤-trans (+-monoʳ-≤ k le) b)) up

-- The right ran Mr₁ to W from w₁'s store, arriving in w₂.  In a future
-- w′ of w₂, the left takes a pure step; the rest is read at the replay
-- world (w′'s left store, scope and tags, over w₁'s store), where the
-- right runs Mr₁ again (`proof.LR.Replay`).
--   The interpretation δᵇ b has a leaf bounded by b.  At the replay the
-- bound is one above the replay's stage s: in `≺` that is the clause's
-- stage n′, in `≻` it is above n′, because the right's counted run
-- passes stages above n′.  So in `≻` the result is read back at the
-- bound n′ (`low`), at the stages up to n′ that remain.
ℰ-stepReplay : ∀ d {n′} {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (q : Φ ⊢ A ⊑ A′)
    {w₁ w₂ w′ : World} (e₂ : w₂ ⊒ w₁) (e : w′ ⊒ w₂)
    (δᵇ : ℕ → Interp Δ Δ′ (ΔL w′) (ΔR w′)) {Ml Ml₁ : Term (ΔL w′)}
    {Mr₁ : Term (storeR w₁)} {k₀} {χs₀ : StoreChanges (storeR w₁) (storeR w₂)}
    {W : Term (storeR w₂)}
  → (∀ b → GoodI (δᵇ b)) → Ml —→ Ml₁ → Mr₁ —→^ k₀ [ χs₀ ] W → Value W
  → StoreRen (ρS e) (applyStores χs₀ (ΣR w₁)) (ΣR w′)
  → (∀ {s} → RStage d k₀ n′ s → ∀ {w″} (e″ : w″ ⊒ w′) {m} → 0 < m
       → m ≤ n′ → ∀ {V V′} → 𝒱 d m q w″ (δᵇ (suc s) ↑ᴵ e″) V V′
       → 𝒱 d m q w″ (δᵇ n′ ↑ᴵ e″) V V′)
  → (∀ {s} → RStage d k₀ n′ s
       → ℰ d s q (replayW w′ (replayPre (⊒-trans e e₂)) (ΣR w₁))
           (δᵇ (suc s)) Ml₁ Mr₁)
  → ℰ d n′ q w′ (δᵇ n′) Ml (renameᵗᵐ (ρS e) W)
ℰ-stepReplay ≺ {zero} q e₂ e δᵇ g sl r v hR low k = ℰ-zero ≺ q _
ℰ-stepReplay ≺ {suc s} q e₂ e δᵇ g sl r v hR low k =
  ℰ-stepL ≺ s q _ sl
    (ℰ-replay≺ᵛ (replayPre (⊒-trans e e₂)) (replayPre e) (ρS e) q
      (release-coh e (replayPre e)) hR (g (suc s)) r v (k r≺))
ℰ-stepReplay ≻ {n′} q {w′ = w′} e₂ e δᵇ {k₀ = k₀} g sl r v hR low k =
  ℰ-stepL ≻ n′ q _ sl
    (ℰᵍ-map⁺ ≻ n′ w′
      (λ le pos w″ e″ V V′ a →
        𝒱≤-cast ≻ ≤′-refl le q w″
          (low r≻ e″ pos (≤′⇒≤ le) {V} {V′}
            (𝒱≤-cast ≻ le ≤′-refl q w″ a)))
      (ℰ-replay≻ᵛ (replayPre (⊒-trans e e₂)) (replayPre e) (ρS e) q
        (release-coh e (replayPre e)) hR (g (suc (k₀ + n′))) r v (k r≻)))

------------------------------------------------------------------------
-- A left-only leaf read back at a lower bound
------------------------------------------------------------------------

-- derivations between equal types relate the same values
𝒱-at : ∀ d n {Δ Δ′} {Ψ : Corr Δ Δ′} {A₁ A₂ B₁ B₂} → A₁ ≡ A₂ → B₁ ≡ B₂
  → (s₁ : Ψ ⊢ A₁ ⊑ B₁) (s₂ : Ψ ⊢ A₂ ⊑ B₂) → ∀ w
  → ∀ {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱 d n s₁ w δ V V′ → 𝒱 d n s₂ w δ V V′
𝒱-at d n refl refl s₁ s₂ w {δ} {V} {V′} r =
  subst (λ s → 𝒱 d n s w δ V V′) (⊑-unique s₁ s₂) r

-- the identity substitution under a left-only binder
idOnlyˢ : ∀ {Δ Δ′} {Ψ : Corr Δ Δ′} → PSub (only Ψ) (only Ψ)
σl idOnlyˢ X = ＇ X
σr idOnlyˢ Y = ＇ Y
σ↔ idOnlyˢ x = X⊑Y x
σo idOnlyˢ x = X⊑★ x

-- the `≻` left-only leaf at two bounds agrees at the stages below both
leafG-lower : ∀ {a a′ b b′} (la : a ≤′ a′) (lb : b ≤′ b′) {ΘL ΘR}
    (c : Desc ΘL ΘR) {k} → k ≤ a → k ≤ b → ∀ w τL τR {V V′}
  → leafG la c k w τL τR V V′ → leafG lb c k w τL τR V V′
leafG-lower {a} {b = b} la lb c {k} ka kb w τL τR r with k ≤? a | k ≤? b
leafG-lower la lb (desc p env envR) ka kb w τL τR r | yes l₁ | yes l₂ =
  G→G≤ (≤′-trans (≤⇒≤′ l₂) lb) p w
    (G≤→G (≤′-trans (≤⇒≤′ l₁) la) p w r)
leafG-lower la lb c ka kb w τL τR r | yes l₁ | no ¬l₂ = ⊥-elim (¬l₂ kb)
leafG-lower la lb c ka kb w τL τR () | no ¬l₁ | yes l₂
leafG-lower la lb c ka kb w τL τR () | no ¬l₁ | no ¬l₂

onlyLeafS-lower : ∀ {a a′ b b′} (la : a ≤′ a′) (lb : b ≤′ b′) {ΘL ΘR}
    (c : SDesc ΘL ΘR) {k} → k ≤ a → k ≤ b → ∀ w τL τR {V V′}
  → onlyLeafS ≻ la c k w τL τR V V′ → onlyLeafS ≻ lb c k w τL τR V V′
onlyLeafS-lower la lb (sdesc Xs Ys c) ka kb w τL τR =
  peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR c)
    (leafG-lower la lb c ka kb w τL τR)

-- the clause's interpretation at a bound a and at a lower bound b
-- agree at the stages up to b
SubI-lower : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {a b} {w : World} (T : Ty (ΔL w))
    (c : SDesc (ΔL w) (ΔR w)) (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) → b ≤ a
  → SubI (idOnlyˢ {Ψ = Φ}) ≻ (suc b) w
      (extOnlyI T (sem (onlyLeafS ≻ (≤′-refl {a}) c)) δ)
      (extOnlyI T (sem (onlyLeafS ≻ (≤′-refl {b}) c)) δ)
sl≡ (SubI-lower T c δ ba) zero = refl
sl≡ (SubI-lower T c δ ba) (suc X) = refl
sr≡ (SubI-lower T c δ ba) Y = refl
sonly (SubI-lower T c δ ba) only-here e {k} pos (s≤s kb) =
  iff (onlyLeafS-lower ≤′-refl ≤′-refl c (≤-trans kb ba) kb _ _ _)
      (onlyLeafS-lower ≤′-refl ≤′-refl c kb (≤-trans kb ba) _ _ _)
sonly (SubI-lower T c δ ba) (only-only x) e {k} pos lt =
  iff (λ r → r) (λ r → r)
spair (SubI-lower T c δ ba) (↔-only x) e {k} lt =
  iff (λ r → r) (λ r → r)

-- in `≻` the replay's bound is above the clause's; in `≺` it is the
-- clause's
lowOnly : ∀ d {k₀ n′ s} → RStage d k₀ n′ s
  → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (q : only Φ ⊢ A ⊑ B) {w : World}
    (T : Ty (ΔL w)) (c : SDesc (ΔL w) (ΔR w))
    (δ : Interp Δ Δ′ (ΔL w) (ΔR w)) {w″} (e″ : w″ ⊒ w) {m}
  → 0 < m → m ≤ n′ → ∀ {V V′}
  → 𝒱 d m q w″
      (extOnlyI T (sem (onlyLeafS d (≤′-refl {suc s}) c)) δ ↑ᴵ e″) V V′
  → 𝒱 d m q w″
      (extOnlyI T (sem (onlyLeafS d (≤′-refl {n′}) c)) δ ↑ᴵ e″) V V′
lowOnly ≺ r≺ q T c δ e″ pos le r = r
lowOnly ≻ {k₀} {n′} r≻ {A = A} {B} q {w} T c δ {w″} e″ {m} pos le r =
  𝒱-at ≻ m (substᵗ-id A) (substᵗ-id B) (substᵖ idOnlyˢ q) q w″
    (to (𝒱-subst ≻ m idOnlyˢ q w″
          (SubI-↑ (SubI-lower {w = w} T c δ
                    (≤-trans (m≤n+m n′ k₀) (n≤1+n _))) e″)
          pos (s≤s le))
      r)

------------------------------------------------------------------------
-- Case 6: left `∀ᶜ`, right `inst`, from `∀⊑∀` to `∀⊑`
------------------------------------------------------------------------

-- the right type of a left-only binder's body, when not `★`, has no
-- instance `★`
only≢★ : ∀ {Δ Δ′ Θ} {Φ : Corr Δ Δ′} {A B} (σ : Δ′ ⇒ˢ Θ)
  → only Φ ⊢ A ⊑ B → NonVar A → B ≢ ★ → substᵗ σ B ≢ ★
only≢★ {B = ★} σ q nv ne eq = ne refl
only≢★ {B = ＇ Y} σ q nv ne eq = nv⊑var q nv
only≢★ {B = ‵ ι} σ q nv ne ()
only≢★ {B = B₁ ⇒ B₂} σ q nv ne ()
only≢★ {B = `∀ B₁} σ q nv ne ()

-- reading X paired at right type `★` as X left-only
pairStarˢ : ∀ {Δ Δ′} {Ψ : Corr Δ Δ′} → PSub (pair Ψ) (only Ψ)
σl pairStarˢ X = ＇ X
σr pairStarˢ = singleSubᵗ ★
σ↔ pairStarˢ ↔-here = X⊑★ only-here
σ↔ pairStarˢ (↔-pair x) = X⊑Y (↔-only x)
σo pairStarˢ (only-pair x) = X⊑★ (only-only x)

pairStarᵖ : ∀ {Δ Δ′} {Ψ : Corr Δ Δ′} {A B}
  → pair Ψ ⊢ A ⊑ B → only Ψ ⊢ A ⊑ B [ ★ ]ᵗ
pairStarᵖ {A = A} p =
  subst (λ C → _ ⊢ C ⊑ _) (substᵗ-id A) (substᵖ pairStarˢ p)

-- the `∀⊑` clause, at a right type that is not `★`
only→𝒱 : ∀ d m {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (Anv : NonVar A)
    (z : zero ∈ᵗ A) (q : only Φ ⊢ A ⊑ B) → B ≢ ★ → ∀ w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → allOnly d m q w δ V V′ → 𝒱 d m (∀⊑ Anv z q) w δ V V′
only→𝒱 d m {B = ★} Anv z q ne w a = ⊥-elim (ne refl)
only→𝒱 d m {B = ＇ Y} Anv z q ne w a = ⊥-elim (nv⊑var q Anv)
only→𝒱 d m {B = ‵ ι} Anv z q ne w a = ⊥-elim (⊑ι-closed q z)
only→𝒱 d m {B = B₁ ⇒ B₂} Anv z q ne w a = to (𝒱-∀⊑⇒ d m Anv z q w) a
only→𝒱 d m {B = `∀ B₁} Anv z q ne w a = to (𝒱-∀⊑∀ d m Anv z q w) a

module Case6 {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {C₁ A₁ : Ty (suc Δ)}
    {C₁′ : Ty (suc Δ′)} {B′ : Ty Δ′}
    (c₁ : extᵐ ν ⊢ C₁ ∼ A₁)
    ⦃ Anv′ : NonVar C₁′ ⦄ ⦃ z′ : zero ∈ᵗ C₁′ ⦄
    (c₁′ : instᵐ ν′ ⊢ C₁′ ∼ ⇑ᵗ B′) (B≢★ : B′ ≢ ★)
    (d : Dir) (n : ℕ) {Φ : Corr Δ Δ′}
    (p₁ : pair Φ ⊢ C₁ ⊑ C₁′) (Anv : NonVar A₁) (z : zero ∈ᵗ A₁)
    (r₁ : only Φ ⊢ A₁ ⊑ B′) (w : World)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (h : CastHyp Φ d w δ ν ν′)
    (preC : PreB w (δr δ) (σR h) (`∀ C₁′))
    {Vl : Term (ΔL w)} {Vr : Term (storeR w)} (vl : Value Vl)
    (vr : Value Vr)
  where

  -- the left's body cast at w, and renamed along ρ
  cl₁ : extᵐ (νL h)
    ⊢ substᵗ (extsᵗ (δl δ)) C₁ ∼ substᵗ (extsᵗ (δl δ)) A₁
  cl₁ = subst∼ (ext-SubstEnv∼ (sL h)) c₁

  clρ : ∀ {Θ} (ρ : ΔL w ↪ᵗ Θ)
    → extᵐ (renameEnv∼ ρ (νL h))
      ⊢ renameᵗ (extᵗ (toRenameᵗ ρ)) (substᵗ (extsᵗ (δl δ)) C₁)
      ∼ renameᵗ (extᵗ (toRenameᵗ ρ)) (substᵗ (extsᵗ (δl δ)) A₁)
  clρ ρ = rename∼ (extᵗ (toRenameᵗ ρ))
    (extᵐ-rename (toRenameᵗ ρ) (renameEnv∼-preserves ρ (νL h))) cl₁

  -- the right's source body, in the store, and its body cast
  A₀ : Ty (suc (storeR w))
  A₀ = substᵗ (extsᵗ (σR h)) C₁′

  cwI : instᵐ (νR h) ⊢ A₀ ∼ ⇑ᵗ (substᵗ (σR h) B′)
  cwI = subst-right-∼ (substᵗ-shift (σR h) B′)
    (subst∼ (inst-SubstEnv∼ (sR h)) c₁′)

  -- the right's term after it allocates α′ := ★
  Mr₁ : Term (suc (storeR w))
  Mr₁ = ⇑ᵗᵐ Vr ⦂∀ (bind ★ ▷ᵇ A₀) [ ＇ 0 ] ↑ 〖 0 , ★ ↑ A₀ 〗
    ⟨ ↑ᶜ (cwI [ ★/0 ]ᶜ) ⟩

  w₁ : World
  w₁ = worldR w ★

  e₁ : w₁ ⊒ w
  e₁ = extR w ★

  -- the left after its type application's step, in a future of the
  -- right's arrival
  Ml₁ : ∀ {Θ} → ΔL w ↪ᵗ Θ → Ty Θ → Term Θ
  Ml₁ ρ T =
    (renameᵗᵐ ρ Vl
       ⦂∀ renameᵗ (extᵗ (toRenameᵗ ρ)) (substᵗ (extsᵗ (δl δ)) C₁) [ T ])
    ⟨ clρ ρ [ T ]ᶜ ⟩

  -- the annotation of the left's type application
  ann≡ : ∀ {Θ} (ρ : ΔL w ↪ᵗ Θ) (τ : Δ ⇒ˢ Θ)
    → (∀ X → τ X ≡ renameᵗ (toRenameᵗ ρ) (δl δ X))
    → substᵗ (extsᵗ τ) A₁
      ≡ renameᵗ (extᵗ (toRenameᵗ ρ)) (substᵗ (extsᵗ (δl δ)) A₁)
  ann≡ ρ τ eq =
    trans (substᵗ-cong A₁ (exts-cong eq))
      (sym (∀-inj (renameᵗ-subst (toRenameᵗ ρ) (δl δ) (`∀ A₁))))

  -- the clause's interpretation in a future w′ of the right's arrival,
  -- with the new variable's leaf bounded by b
  δᵇ : ∀ {Θ₂ Δ₂} {χs₀ : StoreChanges (suc (storeR w)) Θ₂}
      {p₂ : Prefix Θ₂ Δ₂} {ρ₂} (st : Steps (pre w₁) χs₀ p₂ ρ₂)
      {w′} (e : w′ ⊒ arrW w₁ st) (c : SDesc (ΔL w′) (ΔR w′)) → ℕ
    → Interp (suc Δ) Δ′ (ΔL w′) (ΔR w′)
  δᵇ st e c b = extOnlyI (leftTyS c) (sem (onlyLeafS d (≤′-refl {b}) c))
    (((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e)

  -- The core of case 6, at the replay world: the left's instantiation
  -- after its step, against the right's run after its allocation.  It
  -- is an obligation (`Case6Ob`, below).
  Core6R : Set
  Core6R =
    𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr
    → ∀ {Θ₂ k₀} {χs₀ : StoreChanges (suc (storeR w)) Θ₂} {U : Term Θ₂}
    → Mr₁ —→^ k₀ [ χs₀ ] U → Value U
    → ∀ {Δ₂} {p₂ : Prefix Θ₂ Δ₂} {ρ₂} (st : Steps (pre w₁) χs₀ p₂ ρ₂)
    → ∀ {w′} (e : w′ ⊒ arrW w₁ st) {n′ s} → RStage d k₀ n′ s
    → suc s ≤ n → (c : SDesc (ΔL w′) (ΔR w′)) → OnlyS c
    → ℰ d s r₁ (replayW w′ (replayPre (⊒-trans e (arrE w₁ st))) (ΣR w₁))
        (δᵇ st e c (suc s)) (Ml₁ (ρL e) (leftTyS c)) Mr₁

  -- the leaf at the replay's bound read back at the clause's bound, at
  -- the clause's stages (only `≻` raises the bound)
  Low6 : Set
  Low6 =
    ∀ {Θ₂ Δ₂} {χs₀ : StoreChanges (suc (storeR w)) Θ₂}
      {p₂ : Prefix Θ₂ Δ₂} {ρ₂} (st : Steps (pre w₁) χs₀ p₂ ρ₂)
      {w′} (e : w′ ⊒ arrW w₁ st) (c : SDesc (ΔL w′) (ΔR w′))
    → ∀ {k₀ n′ s} → RStage d k₀ n′ s → ∀ {w″} (e″ : w″ ⊒ w′) {m}
    → 0 < m → m ≤ n′
    → ∀ {V V′} → 𝒱 d m r₁ w″ (δᵇ st e c (suc s) ↑ᴵ e″) V V′
    → 𝒱 d m r₁ w″ (δᵇ st e c n′ ↑ᴵ e″) V V′

  low6 : Low6
  low6 st e c rs e″ pos le =
    lowOnly d rs r₁ (leftTyS c) c (((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e) e″ pos le

  module _ (low : Low6) (core : Core6R) (hyp : 𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr)
    where

    -- a clause of the `∀⊑` value the right's run arrives at
    clause : ∀ {Θ₂ k₀} {χs₀ : StoreChanges (suc (storeR w)) Θ₂}
        {U : Term Θ₂}
      → Mr₁ —→^ k₀ [ χs₀ ] U → Value U
      → ∀ {Δ₂} {p₂ : Prefix Θ₂ Δ₂} {ρ₂} (st : Steps (pre w₁) χs₀ p₂ ρ₂)
      → ∀ {m s₀} → RunB d k₀ m s₀ → s₀ ≤ n → AllocB d s₀ n
      → ∀ {w′} (e : w′ ⊒ arrW w₁ st) {n′} → n′ ≤ m
      → (c : SDesc (ΔL w′) (ΔR w′)) → OnlyS c
      → ℰ d n′ r₁ w′
          (extOnlyI (leftTyS c) (sem (onlyLeafS d (≤′-refl {n′}) c))
            (((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e))
          (renameᵗᵐ (ρL e) (Vl ⟨ ∀ᶜ cl₁ ⟩)
             ⦂∀ substᵗ (extsᵗ (δl (((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e))) A₁
             [ leftTyS c ])
          (renameᵗᵐ (ρS e) U)
    clause {U = U} run vU st b s₀≤n up {w′} e {n′} le c oc =
      ℰ-stepReplay d r₁ (arrE w₁ st) e (δᵇ st e c)
        (λ b′ → GoodI-extOnlyI {T = T} {δ = δ₂ ↑ᴵ e}
          (onlyLeafS-good d (≤′-refl {b′}) c)
          (GoodI-↑ {δ = δ₂}
            (GoodI-↑ {δ = δ ↑ᴵ e₁} (GoodI-↑ {δ = δ} (good h) e₁)
              (arrE w₁ st)) e))
        stepL run vU (ΣR⊒ e) (low st e c)
        (λ rs → core hyp run vU st e rs (rstage-< d rs le b s₀≤n up) c oc)
      where
      ρ = ρL e
      T = leftTyS c
      δ₂ = (δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st

      eqδ : ∀ X → δl (((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e) X
        ≡ renameᵗ (toRenameᵗ ρ) (δl δ X)
      eqδ X = cong (renameᵗ (toRenameᵗ ρ))
        (trans (renameTy-id _) (renameTy-id (δl δ X)))

      stepL : renameᵗᵐ ρ (Vl ⟨ ∀ᶜ cl₁ ⟩)
          ⦂∀ substᵗ (extsᵗ (δl (((δ ↑ᴵ e₁) ↑ᴵ arrE w₁ st) ↑ᴵ e))) A₁ [ T ]
        —→ Ml₁ ρ T
      stepL =
        subst (λ B → renameᵗᵐ ρ (Vl ⟨ ∀ᶜ cl₁ ⟩) ⦂∀ B [ T ] —→ Ml₁ ρ T)
          (sym (ann≡ ρ _ eqδ))
          (β-∀ (renameᵗᵐ-preserves-Value ρ vl) refl)

    -- the right's run, after its first step
    afterInst : ∀ {k₀ Θ₂} {χs₀ : StoreChanges (suc (storeR w)) Θ₂}
        {U : Term Θ₂}
      → Mr₁ —→^ k₀ [ χs₀ ] U → Value U
      → ∀ {s} → s ≤ n → AllocB d s n
      → ℰ d s (∀⊑ Anv z r₁) w₁ (δ ↑ᴵ e₁) (Vl ⟨ ∀ᶜ cl₁ ⟩) Mr₁
    afterInst run vU s≤n up =
      ℰ-runR d (∀⊑ Anv z r₁) w₁ (vl 《 all 》) run vU
        (λ st {m} b →
          only→𝒱 d m Anv z r₁ B≢★ _
            (allOnly-from d m r₁ _
              (λ e le c oc → clause run vU st b s≤n up e le c oc)))

    module _ (ne : substᵗ (σR h) B′ ≢ ★) where

      -- the right's world cast
      cw : νR h ⊢ `∀ A₀ ∼ substᵗ (σR h) B′
      cw = (inst_ ⦃ substNonVar (extsᵗ (σR h)) Anv′ ⦄
              ⦃ subst-∈ᵗ z′ var-∈ ⦄ cwI) ne

      stepR : Vr ⟨ cw ⟩ —→[ bind ★ ] Mr₁
      stepR = β-inst ⦃ Anv = substNonVar (extsᵗ (σR h)) Anv′ ⦄
        ⦃ z∈A = subst-∈ᵗ z′ var-∈ ⦄ vr ne

      fromRun : ∀ {K Θ′} {χs : StoreChanges (storeR w) Θ′} {U : Term Θ′}
        → Vr ⟨ cw ⟩ —→^ K [ χs ] U → Value U
        → ℰ d n (∀⊑ Anv z r₁) w δ (Vl ⟨ ∀ᶜ cl₁ ⟩) (Vr ⟨ cw ⟩)
      fromRun none (v 《 () 》)
      fromRun (more s rest) vU with det s stepR
      fromRun (more s rest) vU | refl =
        antiR₁⁺ d (∀⊑ Anv z r₁) stepR (stᴬ w ★) (tagsR w ★)
          (okBindR w ★) (afterInst rest vU)

      atNo : ℰ d n (∀⊑ Anv z r₁) w δ (Vl ⟨ ∀ᶜ cl₁ ⟩) (Vr ⟨ cw ⟩)
      atNo with inst-cast-value ⦃ substNonVar (extsᵗ (σR h)) Anv′ ⦄
          ⦃ subst-∈ᵗ z′ var-∈ ⦄ cwI ne vr (pre-typed preC (proj₁ hyp))
      atNo | K , Θ′ , χs , U , run , vU = fromRun run vU


  ----------------------------------------------------------------------
  -- The core, at the replay world: two binds
  ----------------------------------------------------------------------

  -- Inside the casts, the left's instantiation at T is related to the
  -- right's instantiation at α′ revealed as `★`, at the derivation p₂
  -- that reads X paired at right type `★` as X left-only.  The casts
  -- are then related by the induction hypothesis, at casts read at the
  -- world through the extended interpretation.
  module AtReplay (hyp : 𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr)
      {Θ₂ k₀} {χs₀ : StoreChanges (suc (storeR w)) Θ₂} {U : Term Θ₂}
      (run : Mr₁ —→^ k₀ [ χs₀ ] U) (vU : Value U)
      {Δ₂} {pr₂ : Prefix Θ₂ Δ₂} {ρ₂} (st : Steps (pre w₁) χs₀ pr₂ ρ₂)
      {w′} (e : w′ ⊒ arrW w₁ st) {n′ s} (rs : RStage d k₀ n′ s)
      (s<n : suc s ≤ n) (c : SDesc (ΔL w′) (ΔR w′)) (oc : OnlyS c)
    where

    wR : World
    wR = replayW w′ (replayPre (⊒-trans e (arrE w₁ st))) (ΣR w₁)

    ρ : ΔL w ↪ᵗ ΔL w′
    ρ = ρL e

    T : Ty (ΔL w′)
    T = leftTyS c

    -- the new variable's leaf is bounded one above the replay's stage
    δ₃ : Interp (suc Δ) Δ′ (ΔL w′) (ΔR w′)
    δ₃ = δᵇ st e c (suc s)

    -- the two sides inside their casts
    Il : Term (ΔL w′)
    Il = renameᵗᵐ ρ Vl
      ⦂∀ renameᵗ (extᵗ (toRenameᵗ ρ)) (substᵗ (extsᵗ (δl δ)) C₁) [ T ]

    Ir : Term (suc (storeR w))
    Ir = ⇑ᵗᵐ Vr ⦂∀ (bind ★ ▷ᵇ A₀) [ ＇ 0 ] ↑ 〖 0 , ★ ↑ A₀ 〗

    -- the body's derivation with X left-only and the right's variable
    -- instantiated at `★`
    p₂ : only Φ ⊢ C₁ ⊑ C₁′ [ ★ ]ᵗ
    p₂ = pairStarᵖ p₁

    -- what the core needs (notes/logrel-dgg.md, "Case 6, what remains")
    record Ob : Set₁ where
      field
        -- the instantiations: the hypothesis's clause at the replay
        -- world, the right-only reveal of α′ as `★`, and the
        -- substitution instance from X paired at `★` to X left-only
        inner : ℰ d s p₂ wR δ₃ Il Ir
        -- the right's instantiation is typed (preservation)
        typed : Typedᴿ wR (substᵗ (δr δ₃) (C₁′ [ ★ ]ᵗ)) Ir
        -- the casts, read at the futures of wR through the extended
        -- interpretation (cast substitution composes)
        hyp₂ : ∀ {w″} (e″ : w″ ⊒ wR)
          → CastHyp (only Φ) d w″ (δ₃ ↑ᴵ e″) (extᵐ ν) ν′
        preC₂ : ∀ {w″} (e″ : w″ ⊒ wR)
          → PreB w″ (δr (δ₃ ↑ᴵ e″)) (σR (hyp₂ e″)) (C₁′ [ ★ ]ᵗ)
        preA₂ : ∀ {w″} (e″ : w″ ⊒ wR)
          → PreB w″ (δr (δ₃ ↑ᴵ e″)) (σR (hyp₂ e″)) B′
        castL₂ : ∀ {w″} (e″ : w″ ⊒ wR) (Q : Term (ΔL w″))
          → Q ⟨ subst∼ (sL (hyp₂ e″)) c₁ ⟩
            ≡ Q ⟨ renameᵐᶜ (ρL e″) (clρ ρ [ T ]ᶜ) ⟩
        castR₂ : ∀ {w″} (e″ : w″ ⊒ wR) (Q : Term (storeR w″))
          → Q ⟨ subst∼ (sR (hyp₂ e″)) (c₁′ [ ★/0 ]ᶜ) ⟩
            ≡ Q ⟨ renameᵐᶜ (ρS e″) (↑ᶜ (cwI [ ★/0 ]ᶜ)) ⟩

    -- the core from its obligations and the induction hypothesis
    coreFrom : Ob → CastCase c₁ (c₁′ [ ★/0 ]ᶜ)
      → ℰ d s r₁ wR δ₃ (Ml₁ ρ T) Mr₁
    coreFrom ob ih =
      ℰ-bind₂ᵀ d s p₂ r₁ wR {δ₁ = δ₃} {δ₂ = δ₃}
        (just (cast (clρ ρ [ T ]ᶜ))) (just (cast (↑ᶜ (cwI [ ★/0 ]ᶜ))))
        (Ob.typed ob) (Ob.inner ob)
        (λ e″ {k} k≤ {Ql} {Qr} ql qr q t →
          ℰᵍ-≡ (Ob.castL₂ ob e″ Ql) (Ob.castR₂ ob e″ Qr)
            (ih d k p₂ r₁ _ (Ob.hyp₂ ob e″) (Ob.preC₂ ob e″)
              (Ob.preA₂ ob e″) ql qr (t , q)))

  -- the obligations of case 6, at every replay
  Case6Ob : Set₁
  Case6Ob =
    ∀ hyp {Θ₂ k₀} {χs₀ : StoreChanges (suc (storeR w)) Θ₂} {U : Term Θ₂}
      run vU {Δ₂} {pr₂ : Prefix Θ₂ Δ₂} {ρ₂} st {w′} e {n′ s} rs s<n c oc
    → AtReplay.Ob hyp {Θ₂} {k₀} {χs₀} {U} run vU {Δ₂} {pr₂} {ρ₂} st
        {w′} e {n′} {s} rs s<n c oc

  core6 : Case6Ob → CastCase c₁ (c₁′ [ ★/0 ]ᶜ) → Core6R
  core6 ob ih hyp run vU st e rs s<n c oc =
    AtReplay.coreFrom hyp run vU st e rs s<n c oc
      (ob hyp run vU st e rs s<n c oc) ih

  -- case 6, from its core
  case6 : Low6 → Core6R → 𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr
    → ℰ d n (∀⊑ Anv z r₁) w δ (Vl ⟨ subst∼ (sL h) (∀ᶜ c₁) ⟩)
        (Vr ⟨ subst∼ (sR h) ((inst c₁′) B≢★) ⟩)
  case6 low core hyp with substᵗ (σR h) B′ ≟Ty ★
  case6 low core hyp | yes eq = ⊥-elim (only≢★ (σR h) r₁ Anv B≢★ eq)
  case6 low core hyp | no ne = atNo low core hyp ne

  -- case 6, from its obligations and the induction hypothesis
  case6′ : Case6Ob → CastCase c₁ (c₁′ [ ★/0 ]ᶜ)
    → 𝒱ᵀ d n (∀⊑∀ p₁) w δ Vl Vr
    → ℰ d n (∀⊑ Anv z r₁) w δ (Vl ⟨ subst∼ (sL h) (∀ᶜ c₁) ⟩)
        (Vr ⟨ subst∼ (sR h) ((inst c₁′) B≢★) ⟩)
  case6′ ob ih = case6 low6 (core6 ob ih)

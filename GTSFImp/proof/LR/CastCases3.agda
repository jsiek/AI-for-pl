module proof.LR.CastCases3 where

-- File Charter:
--   * Cases of the cast lemma (`proof.LR.CastLemma`, `CastCase`) of a
--     left injection or projection against a right `id ★`
--     (notes/logrel-dgg.md, "The cast lemma: the case table"):
--       - `case!★`: a left `c !` against `id ★`.  At a ground variable
--         it is the base case `VarI.toO`.  At a closed ground G: if
--         c is the identity at G, the left is a value, an injection
--         (`inj⇒`, `injι`, `inj∀`); otherwise the left takes its
--         `ground` step and the hypothesis at c against `id ★`, at
--         `G ⊑ ★`, is followed by the injection.  If c is not the
--         identity but its source and G are equal after the
--         interpretation, a variable at which c injects or projects is
--         read as `★`, which `CastHyp.starFree` excludes (`collapse!ι`,
--         `collapse!⇒`, `collapse!∀`).
--       - `case？★`: a left `？ c` against `id ★`, the mirror.  At a
--         ground variable it is `VarI.fromO`.  At `ι` and `★⇒★`: the
--         left projects a value related at `★` (`starView`; a mismatched
--         tag blames, `untagBad`), at `G ⊑ ★` (`projι`, `proj⇒`,
--         `proj∀`); if c is not the identity, after its `expand` step
--         and before the hypothesis at c against `id ★` in the
--         projection's future (`expandStep`); the collapse is excluded
--         as for `!` (`collapse？ι`, `collapse？⇒`, `collapse？∀`).
--   * Plumbing: `★⊑★` and functions between `★` and `★` do not read the
--     correspondence or the interpretation (`★-at`, `★≤-at`,
--     `fun★-at`); `⇒⊑★` from the `★⇒★` payload (`funOfStar`).  The
--     `∀★` payload of `★` is `∀★ ⊑ ★` itself (`starAll`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import CastTerms using (Term; Value; _⟨_⟩; _⦂∀_[_]; renameᵗᵐ;
  blame; _《_》; inj; fun; all; genᵥ; ƛ_; Λ_; $; _↑_; _↓_)
open import Reduction using (_—→_; β-id; ground; expand; tag-untag;
  tag-untag-bad)
open import LR.Precision
open import LR.Desc using (leftTyS)
open import LR.World
open import LR.Relation
open import LR.Frame using (Frame; cast; plug; renameFrame)
open import proof.TermRename using (renameEnv∼-id)
open import proof.TypeSafety.Progress using (to-ground; from-ground;
  same; other; no-to-base)
open import proof.LR.InterpProps using (ℰᵍ-map; ℰᵍ-≡; ℰ-resp; 𝒱-resp;
  ↑ᴵ-refl; ≈ᴵ-sym)
open import proof.LR.Monotone using (GoodI-↑; 𝒱-down; funRel-down;
  starAll-down)
open import proof.LR.Expression using (ℰ-value; ℰ-stepL; ℰ-bind₂;
  ℰ-bind₂ᵀ)
open import proof.LR.ConvBase using (ℰ-zero; ℰ-stepR?; step)
open import proof.LR.ConvLemma using (PreB; PreB-↑)
open import proof.LR.IdentityCast using (ℰ-stepL≤)
open import proof.LR.PrecisionUnique using (⊑-unique)
open import proof.LR.WorldProps using (⊒-refl)
open import proof.LR.CastLemma using (CastCase; CastHyp; sL; sR; σR; νL;
  νR; good; var; ren-refl; toW; fromW; VarI; CastHyp-↑; starFree;
  ren≡★)
open import proof.LR.CastCases using (ℰ-blameStep; castVar)
open import proof.LR.CastCases2 using (castRen)

------------------------------------------------------------------------
-- `★` does not read the correspondence or the interpretation
------------------------------------------------------------------------

★-at : ∀ d k {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′} {Φ₂ : Corr Δ₂ Δ₂′} w
    {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)} {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)}
    {V V′}
  → 𝒱 d k (★⊑★ {Φ = Φ₁}) w δ₁ V V′ → 𝒱 d k (★⊑★ {Φ = Φ₂}) w δ₂ V V′
★-at ≺ k w r = r
★-at ≻ zero w r = r
★-at ≻ (suc k) w r = r

★≤-at : ∀ d {m k} (le : m ≤′ k) {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′}
    {Φ₂ : Corr Δ₂ Δ₂′} w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
    {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱≤ d le (★⊑★ {Φ = Φ₁}) w δ₁ V V′
  → 𝒱≤ d le (★⊑★ {Φ = Φ₂}) w δ₂ V V′
★≤-at d ≤′-refl w r = ★-at d _ w r
★≤-at d (≤′-step le) w r = ★≤-at d le w r

module _ {Δ₁ Δ₁′ Δ₂ Δ₂′} {Φ₁ : Corr Δ₁ Δ₁′} {Φ₂ : Corr Δ₂ Δ₂′} where

  -- functions from `★` to `★`
  fun★-at : ∀ d n w {δ₁ : Interp Δ₁ Δ₁′ (ΔL w) (ΔR w)}
      {δ₂ : Interp Δ₂ Δ₂′ (ΔL w) (ΔR w)} {V W}
    → funRel d n (★⊑★ {Φ = Φ₁}) ★⊑★ w δ₁ V W
    → funRel d n (★⊑★ {Φ = Φ₂}) ★⊑★ w δ₂ V W
  fun★-at d n w f e le Wl Wr wl wr a t =
    ℰᵍ-map d _ _ (λ le′ w″ e′ V V′ → ★≤-at d (≤′-trans le′ le) w″)
      (f e le Wl Wr wl wr (★≤-at d le _ a) t)

------------------------------------------------------------------------
-- Injections
------------------------------------------------------------------------

module _ {Δ Δ′} {Φ : Corr Δ Δ′} where

  -- at a base type
  injι : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)} {ι}
      {W Vr}
    → 𝒱 d k (ι⊑★ {Φ = Φ} {ι = ι}) w δ W Vr
    → 𝒱 d k (★⊑★ {Φ = Φ}) w δ
        (W ⟨ _! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (idᵍ {μ = μ} (‵ ι))
               ⦃ Ans = nonstar-ι ⦄ ⟩) Vr
  injι ≺ k w r = r
  injι ≻ zero w r = r
  injι ≻ (suc k) w r = r

  -- at `★ ⇒ ★`
  inj⇒ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)}
      {W Vr}
    → Value Vr → 𝒱 d k (⇒⊑★ (★⊑★ {Φ = Φ}) ★⊑★) w δ W Vr
    → 𝒱 d k (★⊑★ {Φ = Φ}) w δ
        (W ⟨ _! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (idᵍ {μ = μ} ★⇒★)
               ⦃ Ans = nonstar-⇒ ⦄ ⟩) Vr
  inj⇒ ≺ zero w vr r = tt
  inj⇒ ≺ (suc k) w (wr 《 i 》) (ij , f) =
    ij , fun★-at ≺ k w (funRel-down ≺ (n≤1+n k) ★⊑★ ★⊑★ w f)
  inj⇒ ≺ (suc k) w (ƛ N) ()
  inj⇒ ≺ (suc k) w (Λ v) ()
  inj⇒ ≺ (suc k) w ($ κ) ()
  inj⇒ ≺ (suc k) w (v ↑ rv) ()
  inj⇒ ≺ (suc k) w (v ↓ cv) ()
  inj⇒ ≻ zero w vr r = r
  inj⇒ ≻ (suc k) w (wr 《 i 》) (ij , f) = ij , fun★-at ≻ k w f
  inj⇒ ≻ (suc k) w (ƛ N) ()
  inj⇒ ≻ (suc k) w (Λ v) ()
  inj⇒ ≻ (suc k) w ($ κ) ()
  inj⇒ ≻ (suc k) w (v ↑ rv) ()
  inj⇒ ≻ (suc k) w (v ↓ cv) ()

  -- at `∀★`
  inj∀ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)}
      {W Vr}
    → Value Vr → 𝒱 d k (∀★⊑★ {Φ = Φ}) w δ W Vr
    → 𝒱 d k (★⊑★ {Φ = Φ}) w δ
        (W ⟨ _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (idᵍ {μ = μ} ∀★)
               ⦃ Ans = nonstar-∀ ⦄ ⟩) Vr
  inj∀ ≺ zero w vr r = tt
  inj∀ ≺ (suc k) w vr r = starAll-down ≺ (n≤1+n k) w r
  inj∀ ≻ zero w vr r = r
  inj∀ ≻ (suc k) w vr r = r

------------------------------------------------------------------------
-- A cast that is the identity at its ground only after the
-- interpretation does not occur (`CastHyp.starFree`)
------------------------------------------------------------------------

private
  dyn≢ : ∀ {v} → v ≡ X∼★ → v ≢ X∼X
  dyn≢ refl ()

  gen≢ : ∀ {v} → v ≡ ★∼X → v ≢ X∼X
  gen≢ refl ()

  cross≢ : ∀ {v} → v ≡ ★∼X∼★ → v ≢ X∼X
  cross≢ refl ()

  -- a cast from a variable into `★` injects it, at a mode not `X∼X`
  varTo★ : ∀ {Θ} {μ : Env∼ Θ} {X} → μ ⊢ ＇ X ∼ ★ → μ ‼ X ≢ X∼X
  varTo★ (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = X∼★ᵍ m ⦄ c) e with castVar c
  varTo★ (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = X∼★ᵍ m ⦄ c) e | inj₁ refl =
    dyn≢ m e
  varTo★ (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = X∼★ᵍ m ⦄ c) e | inj₂ (() , _)
  varTo★ (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = X∼★ᶜ m ⦄ c) e with castVar c
  varTo★ (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = X∼★ᶜ m ⦄ c) e | inj₁ refl =
    cross≢ m e
  varTo★ (_! ⦃ Gᵍ = ＇ Y ⦄ ⦃ G∼★ = X∼★ᶜ m ⦄ c) e | inj₂ (() , _)
  varTo★ (_! ⦃ Gᵍ = ‵ ι ⦄ c) e = no-to-base c var-∈
  varTo★ (_! ⦃ Gᵍ = ★⇒★ ⦄ c) e =
    var-to-nonstar-nonvar-impossible c nonvar-fun nonstar-⇒
  varTo★ (_! ⦃ Gᵍ = ∀★ ⦄ c) e =
    var-to-nonstar-nonvar-impossible c nonvar-all nonstar-∀

  -- a cast from `★` into a variable projects it, at a mode not `X∼X`
  ★toVar : ∀ {Θ} {μ : Env∼ Θ} {X} → μ ⊢ ★ ∼ ＇ X → μ ‼ X ≢ X∼X
  ★toVar c e with castVar c
  ★toVar c e | inj₁ ()
  ★toVar c e | inj₂ (refl , inj₁ m) = gen≢ m e
  ★toVar c e | inj₂ (refl , inj₂ m) = cross≢ m e

  unflip : ∀ {Θ} (μ : Env∼ Θ) X → flipᵐ μ ‼ X ≢ X∼X → μ ‼ X ≢ X∼X
  unflip μ X ne e = ne (trans (flipᵐ-‼ μ X) (cong flipVar∼ e))

  -- a type sent to `★` is `★` or a variable sent to `★`
  data To★ {Θ Θ′} (σ : Θ ⇒ˢ Θ′) : Ty Θ → Set where
    is★ : To★ σ ★
    isVar : ∀ {Z} → σ Z ≡ ★ → To★ σ (＇ Z)

  to★ : ∀ {Θ Θ′} (σ : Θ ⇒ˢ Θ′) (A : Ty Θ) → substᵗ σ A ≡ ★ → To★ σ A
  to★ σ ★ eq = is★
  to★ σ (＇ Z) eq = isVar eq
  to★ σ (‵ ι) ()
  to★ σ (A ⇒ B) ()
  to★ σ (`∀ A) ()

  unAll : ∀ {Θ} {A B : Ty (suc Θ)} → `∀ A ≡ `∀ B → A ≡ B
  unAll refl = refl

  un⇒ : ∀ {Θ} {A B C D : Ty Θ} → A ⇒ B ≡ C ⇒ D → A ≡ C × B ≡ D
  un⇒ refl = refl , refl

module _ {Θ Θ′} {ν : Env∼ Θ} {σ : Θ ⇒ˢ Θ′}
    (sf : ∀ Z → ν ‼ Z ≢ X∼X → σ Z ≢ ★) where

  private
    -- a source or target sent to `★` by σ is `★`
    ★Src : ∀ {μ : Env∼ Θ} {A} → (∀ Z → μ ‼ Z ≢ X∼X → ν ‼ Z ≢ X∼X)
      → μ ⊢ A ∼ ★ → substᵗ σ A ≡ ★ → A ≡ ★
    ★Src {A = A} m c eq with to★ σ A eq
    ★Src m c eq | is★ = refl
    ★Src {A = ＇ Z} m c eq | isVar e = ⊥-elim (sf Z (m Z (varTo★ c)) e)

    ★Tgt : ∀ {μ : Env∼ Θ} {A} → (∀ Z → μ ‼ Z ≢ X∼X → ν ‼ Z ≢ X∼X)
      → μ ⊢ ★ ∼ A → substᵗ σ A ≡ ★ → A ≡ ★
    ★Tgt {A = A} m c eq with to★ σ A eq
    ★Tgt m c eq | is★ = refl
    ★Tgt {A = ＇ Z} m c eq | isVar e = ⊥-elim (sf Z (m Z (★toVar c)) e)

    -- under a binder: a body sent to `★` whose variable 0 is the
    -- binder's
    ★Body : ∀ (A : Ty (suc Θ)) → substᵗ (extsᵗ σ) A ≡ ★
      → A ≡ ★ ⊎ Σ[ Z ∈ TyVar Θ ] (A ≡ ＇ fsuc Z × σ Z ≡ ★)
    ★Body A eq with to★ (extsᵗ σ) A eq
    ★Body ★ eq | is★ = inj₁ refl
    ★Body (＇ fzero) eq | isVar ()
    ★Body (＇ fsuc Z) eq | isVar e = inj₂ (Z , refl , ren≡★ fsuc e)

  collapse!⇒ : ∀ {A} (c : ν ⊢ A ∼ ★ ⇒ ★) → A ≢ ★ ⇒ ★ → substᵗ σ A ≡ ★ ⇒ ★ → ⊥
  collapse!⇒ (id a) ne eq = ne refl
  collapse!⇒ (c₁ ↦ c₂) ne eq =
    ne (cong₂ _⇒_ (★Tgt (unflip ν) c₁ (proj₁ (un⇒ eq)))
      (★Src (λ Z e → e) c₂ (proj₂ (un⇒ eq))))
  collapse!⇒ (？ c) ne ()
  collapse!⇒ ((inst c) n) ne ()

  collapse!∀ : ∀ {A} (c : ν ⊢ A ∼ `∀ ★) → A ≢ `∀ ★ → substᵗ σ A ≡ `∀ ★ → ⊥
  collapse!∀ (id a) ne eq = ne refl
  collapse!∀ (∀ᶜ_ {A = A₀} c₀) ne eq with ★Body A₀ (unAll eq)
  collapse!∀ (∀ᶜ c₀) ne eq | inj₁ refl = ne refl
  collapse!∀ (∀ᶜ c₀) ne eq | inj₂ (Z , refl , e) =
    sf Z (varTo★ c₀) e
  collapse!∀ (？ c) ne ()
  collapse!∀ (inst_ {A = A₀} ⦃ Anv ⦄ ⦃ z ⦄ c n) ne eq
      with ★Body A₀ (unAll eq)
  collapse!∀ (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c n) ne eq | inj₁ refl
  collapse!∀ (inst_ ⦃ () ⦄ ⦃ z ⦄ c n) ne eq | inj₂ (Z , refl , e)
  collapse!∀ (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c n) ne eq
  collapse!∀ bot-elim ne ()

  collapse!ι : ∀ {A ι} (c : ν ⊢ A ∼ ‵ ι) → A ≢ ‵ ι → substᵗ σ A ≡ ‵ ι → ⊥
  collapse!ι {★} c ne ()
  collapse!ι {＇ Z} c ne eq = no-to-base c var-∈
  collapse!ι {‵ ι′} c ne refl = ne refl
  collapse!ι {A ⇒ B} c ne ()
  collapse!ι {`∀ A} c ne ()

  collapse？⇒ : ∀ {B} (c : ν ⊢ ★ ⇒ ★ ∼ B) → B ≢ ★ ⇒ ★ → ★ ⇒ ★ ≡ substᵗ σ B → ⊥
  collapse？⇒ (id a) ne eq = ne refl
  collapse？⇒ (c₁ ↦ c₂) ne eq =
    ne (cong₂ _⇒_ (★Src (unflip ν) c₁ (sym (proj₁ (un⇒ eq))))
      (★Tgt (λ Z e → e) c₂ (sym (proj₂ (un⇒ eq)))))
  collapse？⇒ (c !) ne ()
  collapse？⇒ ((gen c) n) ne ()

  collapse？∀ : ∀ {B} (c : ν ⊢ `∀ ★ ∼ B) → B ≢ `∀ ★ → `∀ ★ ≡ substᵗ σ B → ⊥
  collapse？∀ (id a) ne eq = ne refl
  collapse？∀ (∀ᶜ_ {B = B₀} c₀) ne eq with ★Body B₀ (sym (unAll eq))
  collapse？∀ (∀ᶜ c₀) ne eq | inj₁ refl = ne refl
  collapse？∀ (∀ᶜ c₀) ne eq | inj₂ (Z , refl , e) =
    sf Z (★toVar c₀) e
  collapse？∀ (c !) ne ()
  collapse？∀ (inst_ ⦃ Anv ⦄ ⦃ () ⦄ c n) ne eq
  collapse？∀ (gen_ {B = B₀} ⦃ Bnv ⦄ ⦃ z ⦄ c n) ne eq
      with ★Body B₀ (sym (unAll eq))
  collapse？∀ (gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c n) ne eq | inj₁ refl
  collapse？∀ (gen_ ⦃ () ⦄ ⦃ z ⦄ c n) ne eq | inj₂ (Z , refl , e)
  collapse？∀ bot-intro ne ()

  collapse？ι : ∀ {B ι} (c : ν ⊢ ‵ ι ∼ B) → B ≢ ‵ ι → ‵ ι ≡ substᵗ σ B → ⊥
  collapse？ι (id a) ne eq = ne refl
  collapse？ι (c !) ne ()
  collapse？ι ((gen c) n) ne ()

------------------------------------------------------------------------
-- A left `!` against `id ★`
------------------------------------------------------------------------

-- the left takes its `ground` step; the cast into the ground is
-- related by `ih`, and its result injected by `K`
groundStep : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {G} (q : Φ ⊢ G ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (F : Frame (ΔL w)) {Ml M Mr}
  → Ml —→ plug F M
  → (∀ {s} → s ≤ n → ℰ d s q w δ M Mr)
  → (∀ {w′} (e : w′ ⊒ w) {k} → k ≤ n → ∀ {Ql Qr} → Value Ql → Value Qr
       → 𝒱 d k q w′ (δ ↑ᴵ e) Ql Qr
       → ℰ d k (★⊑★ {Φ = Φ}) w′ (δ ↑ᴵ e) (plug (renameFrame (ρL e) F) Ql)
           Qr)
  → ℰ d n (★⊑★ {Φ = Φ}) w δ Ml Mr
groundStep d n q w F sl ih K =
  ℰ-stepL≤ d n ★⊑★ w sl (λ {s} s≤ →
    ℰ-bind₂ d s q ★⊑★ w (just F) nothing (ih s≤)
      (λ e k≤ ql qr r → K e (≤-trans k≤ s≤) ql qr r))

case!★ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {A G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄ (c : ν ⊢ A ∼ G)
    ⦃ Ans : NonStar A ⦄
  → CastCase c (id {μ = ν′} ★)
  → CastCase (c !) (id {μ = ν′} ★)
-- a ground variable: the base case
case!★ ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ (id (＇ _)) ih d n (X⊑★ o)
    ★⊑★ w {δ} h pC pA {Vr = Vr} vl vr (t , a) =
  ℰᵍ-≡ (ren-refl {μ = νL h} (toW (sL h) X eq to★-dynamic) _)
    (cong (λ μ → Vr ⟨ id {μ = μ} ★ ⟩) (renameEnv∼-id (νR h)))
    (ℰ-resp d n ★⊑★ w (↑ᴵ-refl {w = w} δ)
      (VarI.toO (var h (⊒-refl w)) o eq to★-dynamic n vl vr
        (𝒱-resp d n (X⊑★ o) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
case!★ ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ (id (＇ _)) ih d n (X⊑★ o)
    ★⊑★ w {δ} h pC pA {Vr = Vr} vl vr (t , a) =
  ℰᵍ-≡ (ren-refl {μ = νL h} (toW (sL h) X eq to★-cross) _)
    (cong (λ μ → Vr ⟨ id {μ = μ} ★ ⟩) (renameEnv∼-id (νR h)))
    (ℰ-resp d n ★⊑★ w (↑ᴵ-refl {w = w} δ)
      (VarI.toO (var h (⊒-refl w)) o eq to★-cross n vl vr
        (𝒱-resp d n (X⊑★ o) w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
case!★ ⦃ Gᵍ = ＇ X ⦄ (？ c) ⦃ Ans = () ⦄ ih
case!★ ⦃ Gᵍ = ＇ X ⦄ c@((inst c₀) B≢★) ⦃ Ans = Ans ⦄ ih =
  ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)
-- a base type
case!★ ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ c ih d n p ★⊑★ w {δ} h pC pA
    vl vr hyp
    with to-ground (‵ ι) c
case!★ ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ .(id (‵ ι)) ih d n p ★⊑★ w {δ}
    h pC pA {Vl} {Vr} vl vr (t , a) | same =
  ℰ-stepR? d n ★⊑★ w (good h) (step (β-id vr)) (vl 《 inj 》) vr
    (injι d n w (subst (λ q → 𝒱 d n q w δ Vl Vr) (⊑-unique p ι⊑★) a))
case!★ {A = A} ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr hyp | other A≢G
    with substᵗ (δl δ) A ≟Ty ‵ ι
case!★ {A = A} ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr hyp | other A≢G | yes eq =
  ⊥-elim (collapse!ι (starFree h) c A≢G eq)
case!★ {A = A} ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr (t , a) | other A≢G | no neq =
  groundStep d n ι⊑★ w
    (cast (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ (id (‵ ι)) ⦃ Ans = nonstar-ι ⦄))
    (ground ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-ι ⦄ vl neq)
    (λ s≤ → ih d _ p ι⊑★ w h pC pA vl vr
      (t , 𝒱-down d s≤ p w (good h) a))
    (λ e k≤ ql qr r → ℰ-value d _ ★⊑★ _ (ql 《 inj 》) qr (injι d _ _ r))
-- `★ ⇒ ★`
case!★ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ c ih d n p ★⊑★ w {δ} h pC pA
    vl vr hyp
    with to-ground ★⇒★ c
case!★ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ .(id ★ ↦ id ★) ih d n p ★⊑★ w
    {δ} h pC pA {Vl} {Vr} vl vr (t , a) | same =
  ℰ-stepR? d n ★⊑★ w (good h) (step (β-id vr)) (vl 《 inj 》) vr
    (inj⇒ d n w vr
      (subst (λ q → 𝒱 d n q w δ Vl Vr) (⊑-unique p (⇒⊑★ ★⊑★ ★⊑★)) a))
case!★ {A = A} ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr hyp | other A≢G
    with substᵗ (δl δ) A ≟Ty ★ ⇒ ★
case!★ {A = A} ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr hyp | other A≢G | yes eq =
  ⊥-elim (collapse!⇒ (starFree h) c A≢G eq)
case!★ {A = A} ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr (t , a) | other A≢G | no neq =
  groundStep d n (⇒⊑★ ★⊑★ ★⊑★) w
    (cast (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ (id ★ ↦ id ★)
      ⦃ Ans = nonstar-⇒ ⦄))
    (ground ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-⇒ ⦄ vl neq)
    (λ s≤ → ih d _ p (⇒⊑★ ★⊑★ ★⊑★) w h pC pA vl vr
      (t , 𝒱-down d s≤ p w (good h) a))
    (λ e k≤ ql qr r → ℰ-value d _ ★⊑★ _ (ql 《 inj 》) qr (inj⇒ d _ _ qr r))
-- `∀★`
case!★ ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ c ih d n p ★⊑★ w {δ} h pC pA
    vl vr hyp
    with to-ground ∀★ c
case!★ ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ .(∀ᶜ (id ★)) ih d n p ★⊑★ w
    {δ} h pC pA {Vl} {Vr} vl vr (t , a) | same =
  ℰ-stepR? d n ★⊑★ w (good h) (step (β-id vr)) (vl 《 inj 》) vr
    (inj∀ d n w vr (subst (λ q → 𝒱 d n q w δ Vl Vr) (⊑-unique p ∀★⊑★) a))
case!★ {A = A} ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr hyp | other A≢G
    with substᵗ (δl δ) A ≟Ty `∀ ★
case!★ {A = A} ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr hyp | other A≢G | yes eq =
  ⊥-elim (collapse!∀ (starFree h) c A≢G eq)
case!★ {A = A} ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ c ih d n p ★⊑★ w {δ} h
    pC pA vl vr (t , a) | other A≢G | no neq =
  groundStep d n ∀★⊑★ w
    (cast (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ (∀ᶜ (id ★)) ⦃ Ans = nonstar-∀ ⦄))
    (ground ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ ⦃ Ans = _ ⦄ ⦃ Gns = nonstar-∀ ⦄ vl neq)
    (λ s≤ → ih d _ p ∀★⊑★ w h pC pA vl vr
      (t , 𝒱-down d s≤ p w (good h) a))
    (λ e k≤ ql qr r → ℰ-value d _ ★⊑★ _ (ql 《 inj 》) qr (inj∀ d _ _ qr r))

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

-- a value related at `★` is an injection
data StarView (d : Dir) (k : ℕ) (w : World)
    : Term (ΔL w) → Term (storeR w) → Set where
  tagged : ∀ {H} {Hᵍ : Ground H} {μ : Env∼ (ΔL w)} {H∼★ : μ ⊢ H ∼★}
      {Hns : NonStar H} {W Vr}
    → Value W → starGround d k w Hᵍ W Vr
    → StarView d k w
        (W ⟨ _! ⦃ Gᵍ = Hᵍ ⦄ ⦃ G∼★ = H∼★ ⦄ (idᵍ Hᵍ) ⦃ Ans = Hns ⦄ ⟩) Vr

starView : ∀ d k w {Vl Vr} → Value Vl → star d k w Vl Vr
  → StarView d k w Vl Vr
starView d k w (wv 《 inj 》) a = tagged wv a
starView d k w (ƛ N) ()
starView d k w (Λ v) ()
starView d k w ($ κ) ()
starView d k w (v 《 fun 》) ()
starView d k w (v 《 all 》) ()
starView d k w (v 《 genᵥ A≢★ gs 》) ()
starView d k w (v ↑ rv) ()
starView d k w (v ↓ cv) ()

-- the `★ ⇒ ★` payload of `★`, at `★⇒★ ⊑ ★`
funOfStar : ∀ d k {Δ Δ′} {Φ : Corr Δ Δ′} w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {W Vr}
  → Value Vr → starFun d k w W Vr
  → funStar d k (★⊑★ {Φ = Φ}) ★⊑★ w δ W Vr
funOfStar ≺ k w (wr 《 i 》) (ij , f) = ij , fun★-at ≺ k w f
funOfStar ≻ k w (wr 《 i 》) (ij , f) = ij , fun★-at ≻ k w f
funOfStar d k w (ƛ N) ()
funOfStar d k w (Λ v) ()
funOfStar d k w ($ κ) ()
funOfStar d k w (v ↑ rv) ()
funOfStar d k w (v ↓ cv) ()

-- a mismatched projection blames, the instances given explicitly
untagBad : ∀ {Θ} {V : Term Θ} {μ ν : Env∼ Θ} {G H : Ty Θ}
    {Gᵍ : Ground G} {Hᵍ : Ground H} {G∼★ : μ ⊢ G ∼★} {★∼H : ν ⊢★∼ H}
    {Gns : NonStar G} {Hns : NonStar H}
  → Value V → G ≢ H
  → V ⟨ _! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ (idᵍ Gᵍ) ⦃ Ans = Gns ⦄ ⟩
      ⟨ ？_ ⦃ Gᵍ = Hᵍ ⦄ ⦃ ★∼G = ★∼H ⦄ (idᵍ Hᵍ) ⦃ Bns = Hns ⦄ ⟩ —→ blame
untagBad {Gᵍ = Gᵍ} {Hᵍ} {G∼★} {★∼H} {Gns} {Hns} v ne =
  tag-untag-bad ⦃ Gᵍ = Gᵍ ⦄ ⦃ Hᵍ = Hᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ ★∼H = ★∼H ⦄
    ⦃ Gns = Gns ⦄ ⦃ Hns = Hns ⦄ v ne

module _ {Δ Δ′} {Φ : Corr Δ Δ′} where

  -- the projection `？ι` of a value related at `★`
  untagι : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)} {ι}
      {Vl Vr}
    → Value Vr → StarView d (suc k) w Vl Vr
    → ℰ d (suc k) (ι⊑★ {Φ = Φ} {ι = ι}) w δ
        (Vl ⟨ ？_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ (idᵍ {μ = μ} (‵ ι))
                ⦃ Bns = nonstar-ι ⦄ ⟩) Vr
  untagι d k w {ι = ι} vr
      (tagged {Hᵍ = ‵ ι′} {H∼★ = ι∼★} {Hns = nonstar-ι} wv a)
      with ι′ ≟Base ι
  untagι ≺ k w {ι = ι} vr
      (tagged {Hᵍ = ‵ .ι} {H∼★ = ι∼★} {Hns = nonstar-ι} wv a)
      | yes refl =
    ℰ-stepL ≺ k ι⊑★ w
      (tag-untag ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ ⦃ ★∼G = ★∼ι ⦄
        ⦃ Gns = nonstar-ι ⦄ wv)
      (ℰ-value ≺ k ι⊑★ w wv vr a)
  untagι ≻ k w {ι = ι} vr
      (tagged {Hᵍ = ‵ .ι} {H∼★ = ι∼★} {Hns = nonstar-ι} wv a)
      | yes refl =
    ℰ-stepL ≻ (suc k) ι⊑★ w
      (tag-untag ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄ ⦃ ★∼G = ★∼ι ⦄
        ⦃ Gns = nonstar-ι ⦄ wv)
      (ℰ-value ≻ (suc k) ι⊑★ w wv vr a)
  untagι d k w {ι = ι} vr
      (tagged {Hᵍ = ‵ ι′} {H∼★ = ι∼★} {Hns = nonstar-ι} wv a)
      | no ne =
    ℰ-blameStep d (suc k) ι⊑★ w (untagBad wv (λ { refl → ne refl }))
  untagι d k w vr (tagged {Hᵍ = ＇ X} wv a) =
    ℰ-blameStep d (suc k) ι⊑★ w (untagBad wv (λ ()))
  untagι d k w vr (tagged {Hᵍ = ★⇒★} wv a) =
    ℰ-blameStep d (suc k) ι⊑★ w (untagBad wv (λ ()))
  untagι d k w vr (tagged {Hᵍ = ∀★} wv a) =
    ℰ-blameStep d (suc k) ι⊑★ w (untagBad wv (λ ()))

  projι : ∀ d n w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)} {ι}
      {Vl Vr}
    → Value Vl → Value Vr → 𝒱 d n (★⊑★ {Φ = Φ}) w δ Vl Vr
    → ℰ d n (ι⊑★ {Φ = Φ} {ι = ι}) w δ
        (Vl ⟨ ？_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ (idᵍ {μ = μ} (‵ ι))
                ⦃ Bns = nonstar-ι ⦄ ⟩) Vr
  projι ≺ zero w vl vr a = ℰ-zero ≺ ι⊑★ w
  projι ≺ (suc k) w vl vr a = untagι ≺ k w vr (starView ≺ (suc k) w vl a)
  projι ≻ zero w vl vr a = ℰ-zero ≻ ι⊑★ w
  projι ≻ (suc k) w vl vr a = untagι ≻ k w vr (starView ≻ (suc k) w vl a)

  -- the projection `？(★⇒★)`
  untag⇒ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)}
      {Vl Vr}
    → Value Vr → StarView d (suc k) w Vl Vr
    → ℰ d (suc k) (⇒⊑★ (★⊑★ {Φ = Φ}) ★⊑★) w δ
        (Vl ⟨ ？_ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ (idᵍ {μ = μ} ★⇒★)
                ⦃ Bns = nonstar-⇒ ⦄ ⟩) Vr
  untag⇒ ≺ k w vr
      (tagged {Hᵍ = ★⇒★} {H∼★ = ⇒∼★} {Hns = nonstar-⇒} wv a) =
    ℰ-stepL ≺ k (⇒⊑★ ★⊑★ ★⊑★) w
      (tag-untag ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄
        ⦃ Gns = nonstar-⇒ ⦄ wv)
      (ℰ-value ≺ k (⇒⊑★ ★⊑★ ★⊑★) w wv vr (funOfStar ≺ k w vr a))
  untag⇒ ≻ k w vr
      (tagged {Hᵍ = ★⇒★} {H∼★ = ⇒∼★} {Hns = nonstar-⇒} wv a) =
    ℰ-stepL ≻ (suc k) (⇒⊑★ ★⊑★ ★⊑★) w
      (tag-untag ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄
        ⦃ Gns = nonstar-⇒ ⦄ wv)
      (ℰ-value ≻ (suc k) (⇒⊑★ ★⊑★ ★⊑★) w wv vr (funOfStar ≻ k w vr a))
  untag⇒ d k w vr (tagged {Hᵍ = ＇ X} wv a) =
    ℰ-blameStep d (suc k) (⇒⊑★ ★⊑★ ★⊑★) w (untagBad wv (λ ()))
  untag⇒ d k w vr (tagged {Hᵍ = ‵ ι} wv a) =
    ℰ-blameStep d (suc k) (⇒⊑★ ★⊑★ ★⊑★) w (untagBad wv (λ ()))
  untag⇒ d k w vr (tagged {Hᵍ = ∀★} wv a) =
    ℰ-blameStep d (suc k) (⇒⊑★ ★⊑★ ★⊑★) w (untagBad wv (λ ()))

  proj⇒ : ∀ d n w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)}
      {Vl Vr}
    → Value Vl → Value Vr → 𝒱 d n (★⊑★ {Φ = Φ}) w δ Vl Vr
    → ℰ d n (⇒⊑★ (★⊑★ {Φ = Φ}) ★⊑★) w δ
        (Vl ⟨ ？_ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ (idᵍ {μ = μ} ★⇒★)
                ⦃ Bns = nonstar-⇒ ⦄ ⟩) Vr
  proj⇒ ≺ zero w vl vr a = ℰ-zero ≺ (⇒⊑★ ★⊑★ ★⊑★) w
  proj⇒ ≺ (suc k) w vl vr a = untag⇒ ≺ k w vr (starView ≺ (suc k) w vl a)
  proj⇒ ≻ zero w vl vr a = ℰ-zero ≻ (⇒⊑★ ★⊑★ ★⊑★) w
  proj⇒ ≻ (suc k) w vl vr a = untag⇒ ≻ k w vr (starView ≻ (suc k) w vl a)

  -- the projection `？∀★`: the payload is the relation at `∀★ ⊑ ★`
  untag∀ : ∀ d k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)}
      {Vl Vr}
    → Value Vr → StarView d (suc k) w Vl Vr
    → ℰ d (suc k) (∀★⊑★ {Φ = Φ}) w δ
        (Vl ⟨ ？_ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ (idᵍ {μ = μ} ∀★)
                ⦃ Bns = nonstar-∀ ⦄ ⟩) Vr
  untag∀ ≺ k w vr
      (tagged {Hᵍ = ∀★} {H∼★ = ∀∼★} {Hns = nonstar-∀} wv a) =
    ℰ-stepL ≺ k ∀★⊑★ w
      (tag-untag ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ ⦃ ★∼G = ★∼∀ ⦄
        ⦃ Gns = nonstar-∀ ⦄ wv)
      (ℰ-value ≺ k ∀★⊑★ w wv vr a)
  untag∀ ≻ k w vr
      (tagged {Hᵍ = ∀★} {H∼★ = ∀∼★} {Hns = nonstar-∀} wv a) =
    ℰ-stepL ≻ (suc k) ∀★⊑★ w
      (tag-untag ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄ ⦃ ★∼G = ★∼∀ ⦄
        ⦃ Gns = nonstar-∀ ⦄ wv)
      (ℰ-value ≻ (suc k) ∀★⊑★ w wv vr a)
  untag∀ d k w vr (tagged {Hᵍ = ＇ X} wv a) =
    ℰ-blameStep d (suc k) ∀★⊑★ w (untagBad wv (λ ()))
  untag∀ d k w vr (tagged {Hᵍ = ‵ ι} wv a) =
    ℰ-blameStep d (suc k) ∀★⊑★ w (untagBad wv (λ ()))
  untag∀ d k w vr (tagged {Hᵍ = ★⇒★} wv a) =
    ℰ-blameStep d (suc k) ∀★⊑★ w (untagBad wv (λ ()))

  proj∀ : ∀ d n w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {μ : Env∼ (ΔL w)}
      {Vl Vr}
    → Value Vl → Value Vr → 𝒱 d n (★⊑★ {Φ = Φ}) w δ Vl Vr
    → ℰ d n (∀★⊑★ {Φ = Φ}) w δ
        (Vl ⟨ ？_ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ (idᵍ {μ = μ} ∀★)
                ⦃ Bns = nonstar-∀ ⦄ ⟩) Vr
  proj∀ ≺ zero w vl vr a = ℰ-zero ≺ ∀★⊑★ w
  proj∀ ≺ (suc k) w vl vr a = untag∀ ≺ k w vr (starView ≺ (suc k) w vl a)
  proj∀ ≻ zero w vl vr a = ℰ-zero ≻ ∀★⊑★ w
  proj∀ ≻ (suc k) w vl vr a = untag∀ ≻ k w vr (starView ≻ (suc k) w vl a)

------------------------------------------------------------------------
-- A left `？` against `id ★`
------------------------------------------------------------------------

-- the left's `expand` step, the projection, then the hypothesis at c
-- against `id ★` in the future of the projection
expandStep : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {G B : Ty Δ}
    (c : ν ⊢ G ∼ B) → CastCase c (id {μ = ν′} ★)
  → ∀ d n {Φ : Corr Δ Δ′} (q : Φ ⊢ G ⊑ ★) (r : Φ ⊢ B ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} (h : CastHyp Φ d w δ ν ν′)
  → PreB w (δr δ) (σR h) ★ → PreB w (δr δ) (σR h) ★
  → ∀ {Ml M Vr} → Typedᴿ w ★ Vr
  → Ml —→ M ⟨ subst∼ (sL h) c ⟩
  → (∀ {s} → s ≤ n → ℰ d s q w δ M Vr)
  → ℰ d n r w δ Ml (Vr ⟨ id {μ = νR h} ★ ⟩)
expandStep c ih d n q r w {δ} h pC pA t sl inner =
  ℰ-stepL≤ d n r w sl (λ {s} s≤ →
    ℰ-bind₂ᵀ d s q r w (just (cast (subst∼ (sL h) c)))
      (just (cast (id {μ = νR h} ★))) t (inner s≤)
      (λ e {k} k≤ {Ql} {Qr} ql qr r′ tq →
        ℰᵍ-≡ (sym (castRen (ρL e) (sL h) c Ql))
          (sym (castRen (ρS e) (sR h) (id ★) Qr))
          (ih d k q r _ (CastHyp-↑ h e) (PreB-↑ pC e) (PreB-↑ pA e) ql qr
            (tq , r′))))

case？★ : ∀ {Δ Δ′} {ν : Env∼ Δ} {ν′ : Env∼ Δ′} {G B : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄ (c : ν ⊢ G ∼ B)
    ⦃ Bns : NonStar B ⦄
  → CastCase c (id {μ = ν′} ★)
  → CastCase (？ c) (id {μ = ν′} ★)
-- a ground variable: the base case
case？★ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᵍ eq ⦄ (id (＇ _)) ih d n ★⊑★
    (X⊑★ o) w {δ} h pC pA {Vr = Vr} vl vr (t , a) =
  ℰᵍ-≡ (ren-refl {μ = νL h} (fromW (sL h) X eq from★-dynamic) _)
    (cong (λ μ → Vr ⟨ id {μ = μ} ★ ⟩) (renameEnv∼-id (νR h)))
    (ℰ-resp d n (X⊑★ o) w (↑ᴵ-refl {w = w} δ)
      (VarI.fromO (var h (⊒-refl w)) o eq from★-dynamic n vl vr
        (𝒱-resp d n ★⊑★ w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
case？★ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼Xᶜ eq ⦄ (id (＇ _)) ih d n ★⊑★
    (X⊑★ o) w {δ} h pC pA {Vr = Vr} vl vr (t , a) =
  ℰᵍ-≡ (ren-refl {μ = νL h} (fromW (sL h) X eq from★-cross) _)
    (cong (λ μ → Vr ⟨ id {μ = μ} ★ ⟩) (renameEnv∼-id (νR h)))
    (ℰ-resp d n (X⊑★ o) w (↑ᴵ-refl {w = w} δ)
      (VarI.fromO (var h (⊒-refl w)) o eq from★-cross n vl vr
        (𝒱-resp d n ★⊑★ w (≈ᴵ-sym (↑ᴵ-refl {w = w} δ)) a)))
case？★ ⦃ Gᵍ = ＇ X ⦄ (_! c) ⦃ Bns = () ⦄ ih
case？★ ⦃ Gᵍ = ＇ X ⦄ c@((gen c₀) A≢★) ⦃ Bns = Bns ⦄ ih =
  ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)
-- a base type
case？★ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ c ih d n ★⊑★ r w {δ} h pC pA
    vl vr hyp
    with from-ground (‵ ι) c
case？★ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ .(id (‵ ι)) ih d n ★⊑★ r w
    {δ} h pC pA vl vr (t , a) | same =
  subst (λ q → ℰ d n q w δ _ _) (⊑-unique ι⊑★ r)
    (ℰ-bind₂ d n ι⊑★ ι⊑★ w nothing (just (cast (id {μ = νR h} ★)))
      (projι d n w vl vr a)
      (λ e k≤ ql qr r′ →
        ℰ-stepR? d _ ι⊑★ _ (GoodI-↑ {δ = δ} (good h) e) (step (β-id qr))
          ql qr r′))
case？★ {B = B} ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr hyp | other B≢G
    with substᵗ (δl δ) B ≟Ty ‵ ι
case？★ {B = B} ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr hyp | other B≢G | yes eq =
  ⊥-elim (collapse？ι (starFree h) c B≢G (sym eq))
case？★ {B = B} ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr (t , a) | other B≢G | no neq =
  expandStep c ih d n ι⊑★ r w h pC pA t
    (expand ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄ ⦃ Bns = _ ⦄ ⦃ Gns = nonstar-ι ⦄ vl
      (λ eq → neq (sym eq)))
    (λ s≤ → projι d _ w vl vr (𝒱-down d s≤ ★⊑★ w (good h) a))
-- `★ ⇒ ★`
case？★ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ c ih d n ★⊑★ r w {δ} h pC pA
    vl vr hyp
    with from-ground ★⇒★ c
case？★ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ .(id ★ ↦ id ★) ih d n ★⊑★ r
    w {δ} h pC pA vl vr (t , a) | same =
  subst (λ q → ℰ d n q w δ _ _) (⊑-unique (⇒⊑★ ★⊑★ ★⊑★) r)
    (ℰ-bind₂ d n (⇒⊑★ ★⊑★ ★⊑★) (⇒⊑★ ★⊑★ ★⊑★) w nothing
      (just (cast (id {μ = νR h} ★)))
      (proj⇒ d n w vl vr a)
      (λ e k≤ ql qr r′ →
        ℰ-stepR? d _ (⇒⊑★ ★⊑★ ★⊑★) _ (GoodI-↑ {δ = δ} (good h) e)
          (step (β-id qr)) ql qr r′))
case？★ {B = B} ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr hyp | other B≢G
    with substᵗ (δl δ) B ≟Ty ★ ⇒ ★
case？★ {B = B} ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr hyp | other B≢G | yes eq =
  ⊥-elim (collapse？⇒ (starFree h) c B≢G (sym eq))
case？★ {B = B} ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr (t , a) | other B≢G | no neq =
  expandStep c ih d n (⇒⊑★ ★⊑★ ★⊑★) r w h pC pA t
    (expand ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄ ⦃ Bns = _ ⦄ ⦃ Gns = nonstar-⇒ ⦄ vl
      (λ eq → neq (sym eq)))
    (λ s≤ → proj⇒ d _ w vl vr (𝒱-down d s≤ ★⊑★ w (good h) a))
-- `∀★`: the payload is the relation at `∀★ ⊑ ★` (the pair clause)
case？★ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ c ih d n ★⊑★ r w {δ} h pC pA
    vl vr hyp
    with from-ground ∀★ c
case？★ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ .(∀ᶜ (id ★)) ih d n ★⊑★ r
    w {δ} h pC pA vl vr (t , a) | same =
  subst (λ q → ℰ d n q w δ _ _) (⊑-unique ∀★⊑★ r)
    (ℰ-bind₂ d n ∀★⊑★ ∀★⊑★ w nothing
      (just (cast (id {μ = νR h} ★)))
      (proj∀ d n w vl vr a)
      (λ e k≤ ql qr r′ →
        ℰ-stepR? d _ ∀★⊑★ _ (GoodI-↑ {δ = δ} (good h) e)
          (step (β-id qr)) ql qr r′))
case？★ {B = B} ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr hyp | other B≢G
    with substᵗ (δl δ) B ≟Ty `∀ ★
case？★ {B = B} ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr hyp | other B≢G | yes eq =
  ⊥-elim (collapse？∀ (starFree h) c B≢G (sym eq))
case？★ {B = B} ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ c ih d n ★⊑★ r w {δ}
    h pC pA vl vr (t , a) | other B≢G | no neq =
  expandStep c ih d n ∀★⊑★ r w h pC pA t
    (expand ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄ ⦃ Bns = _ ⦄ ⦃ Gns = nonstar-∀ ⦄ vl
      (λ eq → neq (sym eq)))
    (λ s≤ → proj∀ d _ w vl vr (𝒱-down d s≤ ★⊑★ w (good h) a))

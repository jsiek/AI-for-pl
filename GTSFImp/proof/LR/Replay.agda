module proof.LR.Replay where

-- File Charter:
--   * Replay worlds (notes/logrel-dgg.md, Section 7, "Design (W)"):
--     a later world's left store, right scope and tags, with an earlier
--     right store, so that the variables the right allocated since are
--     reserved.  Release gives the later world back.
--   * Prefixes are unique (`Prefix Θ Δ` has at most one element), so
--     growing embeddings (`Grows`, `LR.World`) are coherent with each
--     other (`coh-grows`).
--   * `Steps` is functional in the run (`Steps-func`).  Replaying a run
--     from a prefix with room for its allocations takes reserved
--     variables only: the scope is unchanged (`replaySteps`,
--     `replay-arrive`).
--   * The lemmas case 6 of the cast lemma needs: the replay world is a
--     future of the earlier world (`replay-⊒`); the replay's arrival
--     releases into the later world (`release`, `release-coh`); the
--     value relation moves across the release (`𝒱-release`).
--   * The expression relation across a replay (`ℰ-replay≻`,
--     `ℰ-replay≺`): related at the replay world against the right's
--     cast-time term, then related at the later world against the value
--     that term ran to, given that the arrival's values move across the
--     release (`mv`); for `ℰ` at a derivation that is `𝒱-release`
--     (`ℰ-replay≻ᵛ`, `ℰ-replay≺ᵛ`).
--   * Why extensions must grow (`NoGrowth`): a scope embedding that
--     inserts a variable below the newest one makes the replay take
--     that variable.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (zero; suc; _+_; _≤_; s≤s; _≤′_; ≤′-refl)
open import Data.Nat.Properties using (suc-injective)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n;
  m≤n⇒m≤1+n; 1+n≰n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term; Value; renameᵗᵐ)
open import Reduction using (StoreChange; StoreChanges; keep; bind; [];
  _∷_; ↠-refl)
open import LR.Desc using (Tag; renameTag)
open import LR.Steps using (_—→^_[_]_; none; embedᶜˢ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.Reduction.Determinism using (value-run-stops;
  det-value-run; det-value-↠)
open import proof.DGG.CenterRename using (_∘↪_; toRenameᵗ-∘)
open import proof.TermRename using (renameᵗᵐ-id)
open import LR.Precision
open import LR.World
open import LR.Relation
open import proof.LR.WorldProps
open import proof.LR.InterpProps using (𝒱-resp; transportI-id)
open import proof.LR.Monotone using (𝒱-mono; GoodI; GoodI-↑;
  𝒱≤-cast)

------------------------------------------------------------------------
-- Prefixes
------------------------------------------------------------------------

Prefix-≤ : ∀ {Θ Δ} → Prefix Θ Δ → Θ ≤ Δ
Prefix-≤ pid = ≤-refl
Prefix-≤ (pres p) = m≤n⇒m≤1+n (Prefix-≤ p)

Prefix-unique : ∀ {Θ Δ} (p q : Prefix Θ Δ) → p ≡ q
Prefix-unique pid pid = refl
Prefix-unique pid (pres q) = ⊥-elim (1+n≰n (Prefix-≤ q))
Prefix-unique (pres p) pid = ⊥-elim (1+n≰n (Prefix-≤ p))
Prefix-unique (pres p) (pres q) = cong pres (Prefix-unique p q)

-- a store's size only grows
changes-≤ : ∀ {Θ Θ′} → StoreChanges Θ Θ′ → Θ ≤ Θ′
changes-≤ [] = ≤-refl
changes-≤ (keep ∷ χs) = changes-≤ χs
changes-≤ (bind A ∷ χs) = ≤-trans (n≤1+n _) (changes-≤ χs)

-- two growing embeddings of one prefix's store are the same
grows-unique : ∀ {Θ Δ Δ′} (p : Prefix Θ Δ) (p′ : Prefix Θ Δ′)
    {ρ : Δ ↪ᵗ Δ′} → Grows ρ
  → ∀ X → toRenameᵗ ρ (toRenameᵗ (ιᴾ p) X) ≡ toRenameᵗ (ιᴾ p′) X
grows-unique p p′ (q , refl) X =
  trans (sym (toRenameᵗ-∘ (ιᴾ q) (ιᴾ p) X))
    (cong (λ r → toRenameᵗ r X)
      (trans (sym (ιᴾ-++ p q)) (cong ιᴾ (Prefix-unique (p ++ᴾ q) p′))))

-- coherence holds for growing embeddings
coh-grows : ∀ {Θ Θ′ Δ Δ′} {p : Prefix Θ Δ} {p′ : Prefix Θ′ Δ′}
    {ρS : Θ ↪ᵗ Θ′} {ρR : Δ ↪ᵗ Δ′}
  → Grows ρS → Grows ρR → Coh p p′ ρS ρR
coh-grows {p = p} {p′} (qS , refl) gR X =
  trans (grows-unique p (qS ++ᴾ p′) gR X)
    (trans (cong (λ r → toRenameᵗ r X) (ιᴾ-++ qS p′))
      (toRenameᵗ-∘ (ιᴾ p′) (ιᴾ qS) X))

------------------------------------------------------------------------
-- Runs
------------------------------------------------------------------------

-- where a run's steps lead: the scope, the prefix and the embedding
Lands : ∀ {Θ′} → TyCtx → Set
Lands {Θ′} Δ = Σ[ Δ′ ∈ TyCtx ] (Prefix Θ′ Δ′ × (Δ ↪ᵗ Δ′))

Step1-func : ∀ {Θ Θ′ Δ Δ₁ Δ₂} {p : Prefix Θ Δ} {χ : StoreChange Θ Θ′}
    {p₁ : Prefix Θ′ Δ₁} {ρ₁} {p₂ : Prefix Θ′ Δ₂} {ρ₂}
  → Step1 p χ p₁ ρ₁ → Step1 p χ p₂ ρ₂
  → _≡_ {A = Lands Δ} (Δ₁ , p₁ , ρ₁) (Δ₂ , p₂ , ρ₂)
Step1-func fresh fresh = refl
Step1-func stay stay = refl
Step1-func take take = refl

-- a run's steps are determined by the run
Steps-func : ∀ {Θ Θ′ Δ Δ₁ Δ₂} {p : Prefix Θ Δ} {χs : StoreChanges Θ Θ′}
    {p₁ : Prefix Θ′ Δ₁} {ρ₁} {p₂ : Prefix Θ′ Δ₂} {ρ₂}
  → Steps p χs p₁ ρ₁ → Steps p χs p₂ ρ₂
  → _≡_ {A = Lands Δ} (Δ₁ , p₁ , ρ₁) (Δ₂ , p₂ , ρ₂)
Steps-func (done refl) (done refl) = refl
Steps-func (more s ss refl) (more s′ ss′ refl) with Step1-func s s′
Steps-func (more s ss refl) (more s′ ss′ refl) | refl
  with Steps-func ss ss′
Steps-func (more s ss refl) (more s′ ss′ refl) | refl | refl = refl

-- with room for its allocations, a run takes reserved variables only
replaySteps : ∀ {Θ Θ′ Δ} (p : Prefix Θ Δ) (χs : StoreChanges Θ Θ′)
  → Prefix Θ′ Δ → Σ[ p′ ∈ Prefix Θ′ Δ ] Steps p χs p′ id↪ᵗ
replaySteps p [] room = p , done refl
replaySteps p (keep ∷ χs) room with replaySteps p χs room
replaySteps p (keep ∷ χs) room | p′ , ss =
  p′ , more (step1-keep p) ss (sym (∘↪-idʳ id↪ᵗ))
replaySteps pid (bind A ∷ χs) room =
  ⊥-elim (1+n≰n (≤-trans (changes-≤ χs) (Prefix-≤ room)))
replaySteps (pres p) (bind A ∷ χs) room
  with replaySteps (consumeᴾ p) χs room
replaySteps (pres p) (bind A ∷ χs) room | p′ , ss =
  p′ , more take ss (sym (∘↪-idʳ id↪ᵗ))

-- replaying the run lands in the same scope, at its only prefix
replay-arrive : ∀ {Θ Θ′ Δ Δ′} {p : Prefix Θ Δ} {χs : StoreChanges Θ Θ′}
    {p′ : Prefix Θ′ Δ′} {ρ}
  → Steps p χs p′ ρ → (room : Prefix Θ′ Δ)
  → _≡_ {A = Lands Δ} (Δ′ , p′ , ρ) (Δ , room , id↪ᵗ)
replay-arrive {p = p} {χs} st room with replaySteps p χs room
replay-arrive {p = p} {χs} st room | p₀ , st₀
  with Steps-func st st₀
replay-arrive {p = p} {χs} st room | p₀ , st₀ | refl
  rewrite Prefix-unique p₀ room = refl

------------------------------------------------------------------------
-- Replay worlds and release
------------------------------------------------------------------------

-- w's left store, scope and tags, with an earlier right store
replayW : (w : World) {Θ : TyCtx} → Prefix Θ (ΔR w) → World
replayW w {Θ} p = mkWorld (ΔL w) (ΔR w) (tag w) Θ p

-- the prefix of w's store in a future's scope
replayPre : ∀ {w w′ : World} → w′ ⊒ w → Prefix (storeR w) (ΔR w′)
replayPre {w} e = pre w ++ᴾ proj₁ (grows e)

-- the replay world over w's store is a future of w, with the store
-- unchanged and everything allocated since reserved
replay-⊒ : ∀ {w w′ : World} (e : w′ ⊒ w) → replayW w′ (replayPre e) ⊒ w
replay-⊒ {w} e =
  ext (ρL e) (ρR e) id↪ᵗ
    (coh-grows {p = pre w} {p′ = replayPre e} Grows-id (grows e))
    (grows e) (tags≡ e)

-- releasing the reserved variables gives the world back
release : ∀ (w : World) {Θ} (p : Prefix Θ (ΔR w)) (σ : Θ ↪ᵗ storeR w)
  → Coh p (pre w) σ id↪ᵗ → w ⊒ replayW w p
release w p σ c = ext id↪ᵗ id↪ᵗ σ c Grows-id (tags≡ (⊒-refl w))

-- the release's coherence, for the store of a world w₂ with
-- w′ ⊒ w₂: every prefix of w₂'s store in w′'s scope sits where w₂'s
-- store does
release-coh : ∀ {w₂ w′ : World} (e : w′ ⊒ w₂)
  → (p : Prefix (storeR w₂) (ΔR w′)) → Coh p (pre w′) (ρS e) id↪ᵗ
release-coh {w₂} {w′} e p X =
  trans (grows-unique p p Grows-id X)
    (trans (sym (grows-unique (pre w₂) p (grows e) X)) (coh e X))

-- the value relation moves across a release
𝒱-release : ∀ d n {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (q : Φ ⊢ A ⊑ A′)
    (w : World) {Θ} (p : Prefix Θ (ΔR w)) (σ : Θ ↪ᵗ storeR w)
    (c : Coh p (pre w) σ id↪ᵗ)
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → GoodI δ → 𝒱 d n q (replayW w p) δ Vl Vr
  → 𝒱 d n q w δ Vl (renameᵗᵐ σ Vr)
𝒱-release d n q w p σ c {δ} {Vl} g r =
  subst (λ V → 𝒱 d n q w δ V _) (renameᵗᵐ-id Vl)
    (𝒱-resp d n q w (transportI-id δ) (𝒱-mono d n q (release w p σ c) g r))

------------------------------------------------------------------------
-- The expression relation across a replay
------------------------------------------------------------------------

-- Case 6 of the cast lemma: the right ran Mr to W at cast time, from
-- the store Θ₁.  At a later world w′ the clause is used at the replay
-- world over Θ₁, where the right runs Mr again; by determinism it
-- takes the same steps to W, allocating exactly the reserved variables
-- `room` leaves in the scope.  Its arrival releases into w′ (`mv`), at
-- which the right is the value W, embedded by σ.

private
  +-cancelˡ : ∀ m {a b} → m + a ≡ m + b → a ≡ b
  +-cancelˡ zero eq = eq
  +-cancelˡ (suc m) eq = +-cancelˡ m (suc-injective eq)

  +suc≰ : ∀ m {n} → m + suc n ≤ m → ⊥
  +suc≰ zero ()
  +suc≰ (suc m) (s≤s h) = +suc≰ m h

-- the replay's arrival world, and the world it releases into
replayArr : ∀ (w′ : World) {ΔL′ Θ₂} (room : Prefix Θ₂ (ΔR w′))
  → (TyVar ΔL′ → Tag ΔL′ (ΔR w′)) → World
replayArr w′ {ΔL′} {Θ₂} room tags = mkWorld ΔL′ (ΔR w′) tags Θ₂ room

releaseArr : ∀ (w′ : World) {ΔL′} → (TyVar ΔL′ → Tag ΔL′ (ΔR w′))
  → World
releaseArr w′ {ΔL′} tags = mkWorld ΔL′ (ΔR w′) tags (storeR w′) (pre w′)

-- the ok condition of an arrival whose right scope does not change
OkL : ∀ (w′ : World) {ΔL′} (χsL : StoreChanges (ΔL w′) ΔL′)
  → (TyVar ΔL′ → Tag ΔL′ (ΔR w′)) → Set
OkL w′ χsL tags = ∀ X → tags (toRenameᵗ (embedᶜˢ χsL) X)
  ≡ renameTag (embedᶜˢ χsL) id↪ᵗ (tag w′ X)

-- the arrival's extensions: in the replay, and in w′
replayExt : ∀ {w′ : World} {Θ₁ Θ₂ ΔL′} {p₀ : Prefix Θ₁ (ΔR w′)}
    {room : Prefix Θ₂ (ΔR w′)} {χsL : StoreChanges (ΔL w′) ΔL′}
    {χs₀ : StoreChanges Θ₁ Θ₂} (st : Steps p₀ χs₀ room id↪ᵗ)
    {tags} (ok : OkL w′ χsL tags)
  → replayArr w′ room tags ⊒ replayW w′ p₀
replayExt {χsL = χsL} {χs₀} st ok =
  ext (embedᶜˢ χsL) id↪ᵗ (embedᶜˢ χs₀) (coh-steps st) (Steps-grows st) ok

releaseExt : ∀ {w′ : World} {ΔL′} {χsL : StoreChanges (ΔL w′) ΔL′}
    {tags} (ok : OkL w′ χsL tags)
  → releaseArr w′ tags ⊒ w′
releaseExt {w′} {χsL = χsL} ok =
  ext (embedᶜˢ χsL) id↪ᵗ id↪ᵗ (coh-steps (done {p = pre w′} refl))
    Grows-id ok

-- `≻`: the replay counts the right's k₀ steps again
ℰ-replay≻ : ∀ {w′ : World} {Θ₁ Θ₂} (p₀ : Prefix Θ₁ (ΔR w′))
    (room : Prefix Θ₂ (ΔR w′)) {k₀ n} {χs₀ : StoreChanges Θ₁ Θ₂}
    {Mr : Term Θ₁} {W : Term Θ₂} (σ : Θ₂ ↪ᵗ storeR w′)
    {VR : VRel (k₀ + n) (replayW w′ p₀)} {VR′ : VRel n w′}
    {Ml : Term (ΔL w′)}
  → Mr —→^ k₀ [ χs₀ ] W → Value W
  → (∀ {ΔL′} {χsL : StoreChanges (ΔL w′) ΔL′}
       (st : Steps p₀ χs₀ room id↪ᵗ) {tags} (ok : OkL w′ χsL tags)
       (le : n ≤′ k₀ + n) Vl
     → VR le (replayArr w′ room tags)
         (replayExt {w′ = w′} {p₀ = p₀} {room = room}
         {χsL = χsL} {χs₀} st {tags} ok) Vl W
     → VR′ ≤′-refl (releaseArr w′ tags) (releaseExt {w′ = w′} {χsL = χsL}
          {tags = tags} ok) Vl
         (renameᵗᵐ σ W))
  → ℰᵍ ≻ (k₀ + n) (replayW w′ p₀) VR Ml Mr
  → ℰᵍ ≻ n w′ VR′ Ml (renameᵗᵐ σ W)
ℰ-replay≻ p₀ room {n = zero} σ r v mv h =
  inj₁ (_ , [] , _ , none)
ℰ-replay≻ p₀ room {k₀} {suc n} σ r v mv
    (inj₁ (Δ″ , χs , N , ss)) =
  ⊥-elim (+suc≰ k₀ (value-run-stops r v ss))
ℰ-replay≻ p₀ room {n = suc n} σ r v mv (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰ-replay≻ p₀ room {k₀} {suc n} σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  with det-value-run sr vr r v
ℰ-replay≻ p₀ room {k₀} {suc n} σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  | refl , refl with replay-arrive st room
ℰ-replay≻ p₀ room {k₀} {suc n} σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  | refl , refl | refl with +-cancelˡ k₀ eq
ℰ-replay≻ p₀ room {k₀} {suc n} {W = W} σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  | refl , refl | refl | refl =
  inj₂ (inj₂ (zero , suc n , ≤′-refl , ΔL′ , χsL , Vl , _ , [] ,
    renameᵗᵐ σ W , refl , sl , none , vl ,
    renameᵗᵐ-preserves-Value σ v , _ , _ , id↪ᵗ , done refl , tags , ok ,
    mv {χsL = χsL} st ok le Vl rel))

-- `≺`: the stage is the left's, and the replay changes nothing in it
ℰ-replay≺ : ∀ {w′ : World} {Θ₁ Θ₂} (p₀ : Prefix Θ₁ (ΔR w′))
    (room : Prefix Θ₂ (ΔR w′)) {k₀ n} {χs₀ : StoreChanges Θ₁ Θ₂}
    {Mr : Term Θ₁} {W : Term Θ₂} (σ : Θ₂ ↪ᵗ storeR w′)
    {VR : VRel n (replayW w′ p₀)} {VR′ : VRel n w′}
    {Ml : Term (ΔL w′)}
  → Mr —→^ k₀ [ χs₀ ] W → Value W
  → (∀ {ΔL′} {χsL : StoreChanges (ΔL w′) ΔL′}
       (st : Steps p₀ χs₀ room id↪ᵗ) {tags} (ok : OkL w′ χsL tags)
       {n′} (le : n′ ≤′ n) Vl
     → VR le (replayArr w′ room tags)
         (replayExt {w′ = w′} {p₀ = p₀} {room = room}
         {χsL = χsL} {χs₀} st {tags} ok) Vl W
     → VR′ le (releaseArr w′ tags) (releaseExt {w′ = w′} {χsL = χsL}
          {tags = tags} ok) Vl (renameᵗᵐ σ W))
  → ℰᵍ ≺ n (replayW w′ p₀) VR Ml Mr
  → ℰᵍ ≺ n w′ VR′ Ml (renameᵗᵐ σ W)
ℰ-replay≺ p₀ room σ r v mv (inj₁ ru) = inj₁ ru
ℰ-replay≺ p₀ room σ r v mv (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
ℰ-replay≺ p₀ room σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  with det-value-↠ r v sr vr
ℰ-replay≺ p₀ room σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  | refl with replay-arrive st room
ℰ-replay≺ p₀ room {W = W} σ r v mv
    (inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , ΘR′ , χsR , Vr ,
      eq , sl , sr , vl , vr , Δ′ , p′ , ρ , st , tags , ok , rel)))
  | refl | refl =
  inj₂ (inj₂ (k , n′ , le , ΔL′ , χsL , Vl , _ , [] , renameᵗᵐ σ W ,
    eq , sl , ↠-refl , vl , renameᵗᵐ-preserves-Value σ v , _ , _ , id↪ᵗ ,
    done refl , tags , ok , mv {χsL = χsL} st ok le Vl rel))

-- the same for `ℰ` at a derivation: the arrival's values move across
-- the release by `𝒱-release`, given where the replayed store sits
ℰ-replay≻ᵛ : ∀ {w′ : World} {Θ₁ Θ₂} (p₀ : Prefix Θ₁ (ΔR w′))
    (room : Prefix Θ₂ (ΔR w′)) {k₀ n} {χs₀ : StoreChanges Θ₁ Θ₂}
    {Mr : Term Θ₁} {W : Term Θ₂} (σ : Θ₂ ↪ᵗ storeR w′)
    {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (q : Φ ⊢ A ⊑ A′)
    {δ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {Ml : Term (ΔL w′)}
  → Coh room (pre w′) σ id↪ᵗ → GoodI δ
  → Mr —→^ k₀ [ χs₀ ] W → Value W
  → ℰ ≻ (k₀ + n) q (replayW w′ p₀) δ Ml Mr
  → ℰ ≻ n q w′ δ Ml (renameᵗᵐ σ W)
ℰ-replay≻ᵛ {w′} p₀ room {k₀} {n} {χs₀} {W = W} σ q {δ} c g r v =
  ℰ-replay≻ p₀ room σ
    {VR = λ le w e → 𝒱≤ ≻ le q w (δ ↑ᴵ e)}
    {VR′ = λ le w e → 𝒱≤ ≻ le q w (δ ↑ᴵ e)} r v
    (λ {ΔL′} {χsL} → mv {ΔL′} {χsL})
  where
  mv : ∀ {ΔL′} {χsL : StoreChanges (ΔL w′) ΔL′}
       (st : Steps p₀ χs₀ room id↪ᵗ) {tags} (ok : OkL w′ χsL tags)
       (le : n ≤′ k₀ + n) Vl
    → 𝒱≤ ≻ le q (replayArr w′ room tags)
        (δ ↑ᴵ replayExt {w′ = w′} {p₀ = p₀} {room = room} {χsL = χsL}
          {χs₀} st {tags} ok) Vl W
    → 𝒱≤ ≻ ≤′-refl q (releaseArr w′ tags)
        (δ ↑ᴵ releaseExt {w′ = w′} {χsL = χsL}
          {tags = tags} ok) Vl (renameᵗᵐ σ W)
  mv {χsL = χsL} st {tags} ok le Vl rel =
    𝒱-release ≻ _ q (releaseArr w′ tags) room σ c {δ = δ ↑ᴵ e′}
      (GoodI-↑ {δ = δ} g e′)
      (𝒱≤-cast ≻ le ≤′-refl q (replayArr w′ room tags) {δ = δ ↑ᴵ e′} rel)
    where
    e′ = releaseExt {w′ = w′} {χsL = χsL} {tags = tags} ok

ℰ-replay≺ᵛ : ∀ {w′ : World} {Θ₁ Θ₂} (p₀ : Prefix Θ₁ (ΔR w′))
    (room : Prefix Θ₂ (ΔR w′)) {k₀ n} {χs₀ : StoreChanges Θ₁ Θ₂}
    {Mr : Term Θ₁} {W : Term Θ₂} (σ : Θ₂ ↪ᵗ storeR w′)
    {Δ Δ′} {Φ : Corr Δ Δ′} {A A′} (q : Φ ⊢ A ⊑ A′)
    {δ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {Ml : Term (ΔL w′)}
  → Coh room (pre w′) σ id↪ᵗ → GoodI δ
  → Mr —→^ k₀ [ χs₀ ] W → Value W
  → ℰ ≺ n q (replayW w′ p₀) δ Ml Mr
  → ℰ ≺ n q w′ δ Ml (renameᵗᵐ σ W)
ℰ-replay≺ᵛ {w′} p₀ room {k₀} {n} {χs₀} {W = W} σ q {δ} c g r v =
  ℰ-replay≺ p₀ room σ
    {VR = λ le w e → 𝒱≤ ≺ le q w (δ ↑ᴵ e)}
    {VR′ = λ le w e → 𝒱≤ ≺ le q w (δ ↑ᴵ e)} r v
    (λ {ΔL′} {χsL} → mv {ΔL′} {χsL})
  where
  mv : ∀ {ΔL′} {χsL : StoreChanges (ΔL w′) ΔL′}
       (st : Steps p₀ χs₀ room id↪ᵗ) {tags} (ok : OkL w′ χsL tags)
       {n′} (le : n′ ≤′ n) Vl
    → 𝒱≤ ≺ le q (replayArr w′ room tags)
        (δ ↑ᴵ replayExt {w′ = w′} {p₀ = p₀} {room = room} {χsL = χsL}
          {χs₀} st {tags} ok) Vl W
    → 𝒱≤ ≺ le q (releaseArr w′ tags)
        (δ ↑ᴵ releaseExt {w′ = w′} {χsL = χsL}
          {tags = tags} ok) Vl (renameᵗᵐ σ W)
  mv {χsL = χsL} st {tags} ok {n′} le Vl rel =
    𝒱≤-cast ≺ ≤′-refl le q (releaseArr w′ tags) {δ = δ ↑ᴵ e′}
      (𝒱-release ≺ n′ q (releaseArr w′ tags) room σ c {δ = δ ↑ᴵ e′}
        (GoodI-↑ {δ = δ} g e′)
        (𝒱≤-cast ≺ le ≤′-refl q (replayArr w′ room tags)
          {δ = δ ↑ᴵ e′} rel))
    where
    e′ = releaseExt {w′ = w′} {χsL = χsL} {tags = tags} ok

------------------------------------------------------------------------
-- Why extensions grow: a scope embedding that inserts a variable below
-- the newest one (notes/logrel-dgg.md, Gap G1)
------------------------------------------------------------------------

-- Right scope and store [α′ β′] (index 1 is α′, the oldest), the run
-- from the store [α′] having allocated β′.  The embedding `ins` inserts
-- γ between them: [α′ γ β′], β′ ↦ 0, α′ ↦ 2.  It is coherent for
-- ordinary worlds, so before `grows` it was an extension.  Over the
-- store [α′] the reserved variables are γ and β′, and replaying the
-- allocation of β′ takes γ, so the replay's store cannot be released
-- along `ins`.
module NoGrowth where
  ins : 2 ↪ᵗ 3
  ins = keep (skip (keep empty))

  coh-ins : Coh (pid {2}) (pid {3}) ins ins
  coh-ins Fin.zero = refl
  coh-ins (Fin.suc Fin.zero) = refl

  no-growth : Grows ins → ⊥
  no-growth (pres pid , ())

  -- the replay over [α′] allocates γ (index 1), not β′ (index 0)
  replay-takes-γ :
    proj₁ (replaySteps (pres (pres (pid {1}))) (bind ★ ∷ [])
      (pres (pid {2})))
      ≡ pres pid
  replay-takes-γ = refl

  no-release : Coh (pres (pid {2})) (pid {3}) ins id↪ᵗ → ⊥
  no-release c with c Fin.zero
  no-release c | ()

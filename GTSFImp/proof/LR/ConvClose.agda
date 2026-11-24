module proof.LR.ConvClose where

-- File Charter:
--   * The closure oracle (notes/logrel-dgg.md, Section 7): the leaves
--     that the `∀` clauses build from sealed descriptors are closed
--     under conversions at fresh store variables, on both sides
--     (`Oracle`) and on the right alone (`OracleR`), at every bound.
--   * A descriptor's own leaves are entries, whose types are store
--     variables, so the conversion lemmas apply to the descriptor's
--     derivation in mode none, with every hypothesis an identity step.
--     The lemmas need a converted variable, so the derivation is first
--     weakened by a dead one.
--   * A sealed side takes an identity step; the seals are peeled one at
--     a time around the descriptor's relation.
--   * The descriptor's store types (`σᵘ`) are the store preimages of
--     its right variables, or ★ where a variable names a reserved scope
--     variable.  They are preimages wherever the descriptor's right
--     type has one (`unT-subst`), which is all the lemmas read, and
--     only when the right side converts; a left-only leaf's store types
--     are never read (`σ★`).
--   * Induction on the bound: a clause leaf at stage k is closed by the
--     lemmas at bound k, whose oracle covers the stages below k
--     (`oracle-all`, `oracleR-all`).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl; ≤′-step; _≤?_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  ≤-<-trans; <⇒≤; s≤′s; +-suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; lookup)
open import Data.Vec.Properties using (lookup-map)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ; empty; keep; skip)
open import proof.DGG.CenterRename using (_∘↪_)
open import Conversion
open import CastTerms using (Term; _↑_; _↓_; Value)
import CastTerms as CT
open import Reduction using (_—→_; id-reveal; id-conceal)
open import LR.Steps using (more)
open import proof.Reduction.ValueIrreducibleProof using (value-no-step)
open import LR.Frame using (conceal)
open import proof.TypeInTermSubst using (toRename-id-eq)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective;
  renameᵗ-injective)
open import proof.DGG.CenterRename using (toRenameᵗ-∘)
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.PrecisionSubst using (CRen; wk-deadᴿ; renᵖ)
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone
open import proof.LR.Expression
open import proof.LR.SubstLemma using (ℰᵍ-zero; _⇔_; iff; to; from; 𝒱-XY; RenI;
  rl≡; rr≡; rleaf; RenI-↑; 𝒱-ren; 𝒱≤-ren; G-ren; leafBelow-⇔; leafG-⇔; envI-↑;
  allDeadStar-★)
open import proof.LR.ConvSyntax
open import proof.LR.ConvBase
open import proof.LR.ConvLemma
open import proof.LR.ConvMain using (revC; conC; rev★; con★; rev★★;
  con★★; noRF; pre★; pre★⇒; allDeadStar-map; module OnlyV; module DeadV)
open import proof.LR.ConvRight

private
  variable
    Δ Δ′ ΘL ΘR : TyCtx

------------------------------------------------------------------------
-- Every right variable is paired
------------------------------------------------------------------------

partner : ∀ {Δ Δ′} (Φ : Corr Δ Δ′) (Y : TyVar Δ′)
  → Σ[ X ∈ TyVar Δ ] Φ ∋ X ↔ Y
partner (pair Φ) zero = zero , ↔-here
partner (pair Φ) (suc Y) with partner Φ Y
partner (pair Φ) (suc Y) | X , x = suc X , ↔-pair x
partner (only Φ) Y with partner Φ Y
partner (only Φ) Y | X , x = suc X , ↔-only x
partner (dead Φ) Y with partner Φ Y
partner (dead Φ) Y | X , x = suc X , ↔-dead x

------------------------------------------------------------------------
-- A descriptor's entries, fresh for a conversion
------------------------------------------------------------------------

-- the entry's outer left seal is not β
SealNe : TyVar ΘL → Entry ΘL ΘR → Set
SealNe β (seals X Xs Ys c) = X ≢ β

-- a right store type that is a store variable other than β′
RFresh : ∀ {Θ} → TyVar Θ → Ty Θ → Set
RFresh β′ T′ = Σ[ γ′ ∈ _ ] (T′ ≡ ＇ γ′ × γ′ ≢ β′)

-- ... or ★, the store type of a descriptor's right variable whose
-- scope variable is reserved
RFresh★ : ∀ {Θ} → TyVar Θ → Ty Θ → Set
RFresh★ β′ T′ = T′ ≡ ★ ⊎ RFresh β′ T′

-- what the right side's conversion needs of the descriptor's store
-- types σ
data RCOk {Δ′ Θ} (σ : Δ′ ⇒ˢ Θ) : RConv Θ → Set where
  rc-none : RCOk σ nothing
  rc-just : ∀ {β′ R′} → (∀ Y′ → RFresh★ β′ (σ Y′))
    → RCOk σ (just (β′ , R′))

module _ {Δ′ Θ} {σ : Δ′ ⇒ˢ Θ} where

  rkOf : ∀ {rc} → RCOk σ rc → RK
  rkOf rc-none = left
  rkOf (rc-just f) = both

  allowedOf : ∀ {rc} (ok : RCOk σ rc) → Allowed (rkOf ok) rc
  allowedOf rc-none = tt
  allowedOf (rc-just f) = tt

tyL-entry : ∀ {β : TyVar ΘL} R (e : Entry ΘL ΘR) → SealNe β e
  → replaceTy β R (entryTy e) ≡ entryTy e
tyL-entry R (seals X Xs Ys c) ne = replaceTy-other R ne

tyR-fresh : ∀ {Θ} {β′ : TyVar Θ} R′ {T′} → RFresh★ β′ T′
  → replaceTy β′ R′ T′ ≡ T′
tyR-fresh R′ (inj₁ refl) = refl
tyR-fresh R′ (inj₂ (γ′ , refl , ne)) = replaceTy-other R′ ne

-- a store preimage of a scope variable is a store variable
var-pre : ∀ {Θ Δ} (ι : Θ ↪ᵗ Δ) {Y} (T₀ : Ty Θ)
  → ＇ Y ≡ renameᵗ (toRenameᵗ ι) T₀ → Σ[ γ ∈ TyVar Θ ] T₀ ≡ ＇ γ
var-pre ι (＇ γ) eq = γ , refl
var-pre ι (‵ ι′) ()
var-pre ι ★ ()
var-pre ι (A ⇒ B) ()
var-pre ι (`∀ A) ()

rsealed-var : ∀ {en : Entry ΘL ΘR} {T} → RSealed en T
  → Σ[ Y ∈ TyVar ΘR ] T ≡ ＇ Y
rsealed-var (rsealed {Y = Y}) = Y , refl

-- at ★, the right side's conversion is an identity step
rid★ : ∀ {Θ} (rc : RConv Θ) → RId rc ★
rid★ nothing = tt
rid★ (just c) = inj₁ refl

module _ {d : Dir} {w : World} where

  -- an entry's leaf, at the right store type ★
  private
    idR★ : ∀ k {w′ : World} {L : Leaf (ΔL w′) (ΔR w′)} → GoodLeaf L
      → ∀ {Vl Vr} → Value Vl → Value Vr → leafRel d k w′ L Vl Vr
      → ℰL d k w′ L Vl (Vr ↑ id↑ ★)
    idR★ k {w′} {L} gl vl vr r =
      XY→ℰL d k (↔-here {Φ = []}) w′ {δ = extPairI ★ ★ L closedI}
        (ℰ-steps? d k (X⊑Y ↔-here) w′
          (GoodI-extPairI {T = ★} {T′ = ★} {δ = closedI} gl good-closedI)
          stay (step (id-reveal vr)) vl vr (to (𝒱-XY d k ↔-here w′) r))

    idC★ : ∀ k {w′ : World} {L : Leaf (ΔL w′) (ΔR w′)} → GoodLeaf L
      → ∀ {Vl Wr} → Value Vl → Value Wr → leafRel d k w′ L Vl Wr
      → ℰL d k w′ L Vl (Wr ↓ id↓ ★)
    idC★ k {w′} {L} gl vl wr r =
      XY→ℰL d k (↔-here {Φ = []}) w′ {δ = extPairI ★ ★ L closedI}
        (ℰ-steps? d k (X⊑Y ↔-here) w′
          (GoodI-extPairI {T = ★} {T′ = ★} {δ = closedI} gl good-closedI)
          stay (step (id-conceal wr)) vl wr (to (𝒱-XY d k ↔-here w′) r))

  entryConvPN : ∀ {N β} R (e : Entry (ΔL w) (ΔR w)) {T′} → SealNe β e
    → ConvLeafP d N w R nothing β (syn e) (syn e) (entryTy e) T′
  entryConvPN R (seals X Xs Ys c) {T′} ne =
    storeConvPN good-syn {T′ = T′} R ne

  entryConvPJ : ∀ {N β} R (e : Entry (ΔL w) (ΔR w)) {T′ β′ R′}
    → SealNe β e → RFresh★ β′ T′
    → ConvLeafP d N w R (just (β′ , R′)) β (syn e) (syn e) (entryTy e) T′
  entryConvPJ R (seals X Xs Ys c) ne (inj₂ (γ′ , refl , ne′)) e k≤N =
    storeConvP good-syn R (just _) ne ne′ e k≤N
  entryConvPJ R (seals X Xs Ys c) {β′ = β′} {R′} ne (inj₁ refl) {w′} e {k}
      k≤N =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) (syn (seals X Xs Ys c)))
        good-syn (λ eq → ne (toRenameᵗ-injective (ρL e) eq))
        (renRConv (ρS e) (just (β′ , R′)))
        (rid★ (renRConv (ρS e) (just (β′ , R′)))) vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) (syn (seals X Xs Ys c)))
        good-syn (λ eq → ne (toRenameᵗ-injective (ρL e) eq))
        (renRConv (ρS e) (just (β′ , R′)))
        (rid★ (renRConv (ρS e) (just (β′ , R′)))) wl wr r)

  entryConvO : ∀ {N β} R (e : Entry (ΔL w) (ΔR w)) → SealNe β e
    → ConvLeafO d N w R β (syn e) (syn e) (entryTy e)
  entryConvO R (seals X Xs Ys c) ne = storeConvO good-syn R ne

  entryFreshPL : ∀ (e : Entry (ΔL w) (ΔR w)) {T′}
    → FreshP d left w (syn e) (entryTy e) T′
  entryFreshPL (seals X Xs Ys c) = storeFreshPL {N = zero} good-syn

  entryFreshPJ : ∀ (e : Entry (ΔL w) (ΔR w)) {T′ β′} → RFresh★ β′ T′
    → FreshP d both w (syn e) (entryTy e) T′
  entryFreshPJ (seals X Xs Ys c) (inj₂ (γ′ , refl , ne)) e rc ok nb nrc rs =
    storeFreshP {N = zero} good-syn {rk = both} e rc ok nb nrc rs
  entryFreshPJ (seals X Xs Ys c) (inj₁ refl) {w′} e {β} {R} rc ok nb nrc
      rs {k} =
    (λ vl vr r →
      idRevP d k w′ (transportLeaf (ρL e) (ρR e) (syn (seals X Xs Ys c)))
        good-syn (nb X) rc (rid★ rc) vl vr r) ,
    (λ wl wr r →
      idConP d k w′ (transportLeaf (ρL e) (ρR e) (syn (seals X Xs Ys c)))
        good-syn (nb X) rc (rid★ rc) wl wr r)

  entryFreshO : ∀ (e : Entry (ΔL w) (ΔR w))
    → FreshO d w (syn e) (entryTy e)
  entryFreshO (seals X Xs Ys c) = storeFreshO good-syn

  entryConvR : ∀ {N β′} R′ {e : Entry (ΔL w) (ΔR w)} {T′} → RFresh★ β′ T′
    → ConvLeafR d N w β′ R′ (syn e) (syn e) T′
  entryConvR R′ (inj₂ (γ′ , refl , ne)) e′ k≤N =
    storeConvR good-syn R′ ne e′ k≤N
  entryConvR R′ (inj₁ refl) {w′} e′ {k} k≤N =
    (λ vl vr r → idR★ k good-syn vl vr r) ,
    (λ vl wr r → idC★ k good-syn vl wr r)

  entryFreshR : ∀ {e : Entry (ΔL w) (ΔR w)} {T′ β′} → RFresh★ β′ T′
    → FreshR d w (syn e) T′
  entryFreshR (inj₂ (γ′ , refl , ne)) e′ nb bs =
    storeFreshR {N = zero} good-syn e′ nb bs
  entryFreshR (inj₁ refl) {w′} e′ nb bs {k} =
    (λ vl vr r → idR★ k good-syn vl vr r) ,
    (λ vl wr r → idC★ k good-syn vl wr r)

------------------------------------------------------------------------
-- The lemmas at a descriptor's own interpretation
------------------------------------------------------------------------

-- σ: store types for the descriptor's right variables.  The lemmas read
-- them as store preimages only at the descriptor's right type B, and
-- only when the right side converts; a right variable may name a
-- reserved scope variable.
module Core (d : Dir) {w : World} {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : Φ ⊢ A ⊑ B) (env : Vec (Entry (ΔL w) (ΔR w)) Δ)
    (envR : Vec (Ty (ΔR w)) Δ′) where

  δ : Interp Δ Δ′ (ΔL w) (ΔR w)
  δ = envI env envR

  -- weakened by a dead variable, the converted one in mode none
  δ′ : Interp (suc Δ) Δ′ (ΔL w) (ΔR w)
  δ′ = extDeadI ★ δ

  p′ : dead Φ ⊢ renameᵗ suc A ⊑ renameᵗ (λ Y → Y) B
  p′ = renᵖ (wk-deadᴿ {Ψ = Φ}) p

  goodδ′ : GoodI δ′
  goodδ′ = GoodI-extDeadI {T = ★} {δ = δ} (good-envI {env = env} {envR = envR})

  renI : RenI (wk-deadᴿ {Ψ = Φ}) δ δ′
  rl≡ renI X = refl
  rr≡ renI Y = refl
  rleaf renI X = ≈ˡ-refl

  -- back from the weakened derivation
  back : ∀ {k M M′} → ℰ d k p′ w δ′ M M′ → ℰ d k p w δ M M′
  back {k} =
    ℰᵍ-map d k w (λ le′ w″ e″ V V′ r →
      from (𝒱≤-ren d le′ (wk-deadᴿ {Ψ = Φ}) p w″ (RenI-↑ renI e″)) r)

  inW : ∀ {k Vl Vr} → 𝒱 d k p w δ Vl Vr → 𝒱 d k p′ w δ′ Vl Vr
  inW {k} = to (𝒱-ren d k (wk-deadᴿ {Ψ = Φ}) p w renI)

  tyA : substᵗ (δl δ′) (renameᵗ suc A) ≡ substᵗ (δl δ) A
  tyA = substᵗ-rename (δl δ′) suc A

  tyB : ∀ (σ : Δ′ ⇒ˢ storeR w)
    → substᵗ σ (renameᵗ (λ Y → Y) B) ≡ substᵗ σ B
  tyB σ = substᵗ-rename σ (λ Y → Y) B

  -- the right type's store preimage, for the weakened derivation
  preW : ∀ {σ : Δ′ ⇒ˢ storeR w} → PreB w (lookup envR) σ B
    → PreB w (lookup envR) σ (renameᵗ (λ Y → Y) B)
  pre≡ (preW {σ} h) =
    trans (substᵗ-rename (lookup envR) (λ Y → Y) B)
      (trans (pre≡ h) (cong (ιT w) (sym (tyB σ))))

  module _ {σ : Δ′ ⇒ˢ storeR w} where

    -- the hypotheses that depend on the right side's conversion
    tyR-ok : ∀ {rc} (ok : RCOk σ rc) Y′ → replaceRC rc (σ Y′) ≡ σ Y′
    tyR-ok rc-none Y′ = refl
    tyR-ok (rc-just {R′ = R′} f) Y′ = tyR-fresh R′ (f Y′)

    convP-ok : ∀ {N β} R {rc} (ok : RCOk σ rc)
      → (∀ Z → SealNe β (lookup env Z))
      → ∀ {Z Y′} → Φ ∋ Z ↔ Y′
      → ConvLeafP d N w R rc β (syn (lookup env Z)) (syn (lookup env Z))
          (entryTy (lookup env Z)) (σ Y′)
    convP-ok R rc-none nβ {Z} {Y′} z =
      entryConvPN R (lookup env Z) {T′ = σ Y′} (nβ Z)
    convP-ok R (rc-just f) nβ {Z} {Y′} z =
      entryConvPJ R (lookup env Z) (nβ Z) (f Y′)

    genP-ok : ∀ {rc} (ok : RCOk σ rc) {Z Y′} → Φ ∋ Z ↔ Y′
      → FreshP d (rkOf ok) w (syn (lookup env Z)) (entryTy (lookup env Z))
          (σ Y′)
    genP-ok rc-none {Z} z = entryFreshPL (lookup env Z)
    genP-ok (rc-just f) {Z} {Y′} z = entryFreshPJ (lookup env Z) (f Y′)

  -- the main lemma, with no converted variable
  module _ {N} (orc : Oracle d N) {β : TyVar (ΔL w)}
      (nβ : ∀ Z → SealNe β (lookup env Z)) (R : Ty (ΔL w))
      {σ : Δ′ ⇒ˢ storeR w} {rc : RConv (storeR w)} (ok : RCOk σ rc)
      (rs : RCΣ w rc) where

    hyp : ConvI d N (rkOf ok) w (m-none {Φ = dead Φ} {X = zero} R rc) β
      δ′ δ′ σ σ
    goodS hyp = goodδ′
    goodT hyp = goodδ′
    selfI hyp = tt
    rcOK hyp = allowedOf ok
    tyL hyp zero = refl
    tyL hyp (suc Z) = tyL-entry R (lookup env Z) (nβ Z)
    tyR hyp = tyR-ok ok
    rcΣ hyp = rs
    leafO hyp Z tt = ≈ˡ-refl
    convP hyp (↔-dead z) tt = convP-ok R ok nβ z
    convO hyp (only-dead {X = Z} z) tt = entryConvO R (lookup env Z) (nβ Z)
    genP hyp (↔-dead z) = genP-ok ok z
    genO hyp (only-dead {X = Z} z) = entryFreshO (lookup env Z)
    genPS hyp (↔-dead z) = genP-ok ok z
    genOS hyp (only-dead {X = Z} z) = entryFreshO (lookup env Z)
    sealI hyp = tt
    oracle hyp = orc

    -- pre: the right type's store preimage, when the right converts
    preM : (∀ {c} → rc ≡ just c → PreB w (lookup envR) σ B)
      → PreM w rc δ′ δ′ σ σ (renameᵗ (λ Y → Y) B)
    pNo (preM pre) eq = refl
    pJust (preM pre) eq = preW (pre eq) ,ᵖ preW (pre eq)

    coreRev : (∀ {c} → rc ≡ just c → PreB w (lookup envR) σ B)
      → ∀ {k} → k ≤ N → ∀ {Vl Vr} → Value Vl → Value Vr
      → 𝒱 d k p w δ Vl Vr
      → ℰ d k p w δ (Vl ↑ 〖 β , R ↑ substᵗ (δl δ) A 〗)
          (revM rc (substᵗ σ B) Vr)
    coreRev pre le {Vl} {Vr} vl vr r =
      back
        (ℰᵍ-≡ (cong (λ T → Vl ↑ 〖 β , R ↑ T 〗) tyA)
          (cong (λ T → revM rc T Vr) (tyB σ))
          (revC d p′ hyp (preM pre) le vl vr (inW r)))

    coreCon : (∀ {c} → rc ≡ just c → PreB w (lookup envR) σ B)
      → ∀ {k} → k ≤ N → ∀ {Wl Wr} → Value Wl → Value Wr
      → 𝒱 d k p w δ Wl Wr
      → ℰ d k p w δ (Wl ↓ makeConceal β R (substᵗ (δl δ) A))
          (conM rc (substᵗ σ B) Wr)
    coreCon pre le {Wl} {Wr} wl wr r =
      back
        (ℰᵍ-≡ (cong (λ T → Wl ↓ makeConceal β R T) tyA)
          (cong (λ T → conM rc T Wr) (tyB σ))
          (conC d p′ hyp (preM pre) le wl wr (inW r)))

  -- the right-only lemma, with no converted variable
  module _ {N} (orc : OracleR d N) {β′ : TyVar (storeR w)}
      (R′ : Ty (storeR w)) {σ : Δ′ ⇒ˢ storeR w}
      (pre : PreB w (lookup envR) σ B) (f : ∀ Y′ → RFresh★ β′ (σ Y′))
      (bs : RCΣ w (just (β′ , R′))) where

    hypR : RConvI d N w (r-none {Φ = dead Φ} {X = zero} β′ R′) δ′ δ′ σ σ
    goodS hypR = goodδ′
    goodT hypR = goodδ′
    selfR hypR = tt
    tyL hypR Z = refl
    tyR hypR Y′ = tyR-fresh R′ (f Y′)
    rcΣ hypR = bs
    leafO hypR Z tt = ≈ˡ-refl
    convP hypR (↔-dead {Y = Y′} z) tt = entryConvR R′ (f Y′)
    genR hypR (↔-dead {Y = Y′} z) = entryFreshR (f Y′)
    genRS hypR (↔-dead {Y = Y′} z) = entryFreshR (f Y′)
    sealR hypR = tt
    oracleR hypR = orc

    coreRevR : ∀ {k} → k ≤ N → ∀ {Vl Vr} → Value Vl → Value Vr
      → 𝒱 d k p w δ Vl Vr
      → ℰ d k p w δ Vl (Vr ↑ 〖 β′ , R′ ↑ substᵗ σ B 〗)
    coreRevR le {Vl} {Vr} vl vr r =
      back
        (ℰᵍ-≡ refl (cong (λ T → Vr ↑ 〖 β′ , R′ ↑ T 〗) (tyB σ))
          (revR d p′ hypR (preW pre ,ᵖ preW pre) le vl vr (inW r)))

    coreConR : ∀ {k} → k ≤ N → ∀ {Vl Wr} → Value Vl → Value Wr
      → 𝒱 d k p w δ Vl Wr
      → ℰ d k p w δ Vl (Wr ↓ makeConceal β′ R′ (substᵗ σ B))
    coreConR le {Vl} {Wr} vl wr r =
      back
        (ℰᵍ-≡ refl (cong (λ T → Wr ↓ makeConceal β′ R′ T) (tyB σ))
          (conR d p′ hypR (preW pre ,ᵖ preW pre) le vl wr (inW r)))

------------------------------------------------------------------------
-- Closure of a leaf, at the current world
------------------------------------------------------------------------

-- related values, changed on each side, are related expressions
Close : Dir → (w : World) → Leaf (ΔL w) (ΔR w)
  → (Term (ΔL w) → Term (ΔL w)) → (Term (storeR w) → Term (storeR w)) → Set
Close d w L fl fr = ∀ {k Vl Vr} → Value Vl → Value Vr
  → leafRel d k w L Vl Vr → ℰL d k w L (fl Vl) (fr Vr)

-- the one-variable interpretation that reads a leaf
module One {w : World} (L : Leaf (ΔL w) (ΔR w)) where

  δ₁ : Interp 1 1 (ΔL w) (ΔR w)
  δ₁ = extPairI ★ ★ L closedI

  x₁ : pair [] ⊢ ＇ zero ⊑ ＇ zero
  x₁ = X⊑Y ↔-here

  fromL : ∀ d k {M M′} → ℰL d k w L M M′ → ℰ d k x₁ w δ₁ M M′
  fromL d k = ℰL→XY d k ↔-here w

  toL : ∀ d k {M M′} → ℰ d k x₁ w δ₁ M M′ → ℰL d k w L M M′
  toL d k = XY→ℰL d k ↔-here w

ℰL-zero : ∀ d w (L : Leaf (ΔL w) (ΔR w)) {M M′} → ℰL d zero w L M M′
ℰL-zero d w L =
  ℰᵍ-zero d w
    {VR = λ {n′} le w′ e → leafRel d n′ w′ (transportLeaf (ρL e) (ρR e) L)}

-- one step on the left: counted in `≺`
stepL-ℰL : ∀ d {w} (L : Leaf (ΔL w) (ΔR w)) {k Ml Ml′ Mr}
  → Ml —→ Ml′ → (∀ {k′} → k′ ≤ k → ℰL d k′ w L Ml′ Mr)
  → ℰL d k w L Ml Mr
stepL-ℰL ≺ {w} L {zero} s f = ℰL-zero ≺ w L
stepL-ℰL ≺ L {suc k} s f =
  toL ≺ (suc k) (ℰ-stepL ≺ k x₁ _ s (fromL ≺ k (f (n≤1+n k))))
  where open One L
stepL-ℰL ≻ L {k} s f =
  toL ≻ k (ℰ-stepL ≻ k x₁ _ s (fromL ≻ k (f ≤-refl)))
  where open One L

-- one step on the right: counted in `≻`
stepR-ℰL : ∀ d {w} (L : Leaf (ΔL w) (ΔR w)) {k Ml Mr Mr′}
  → Mr —→ Mr′ → (∀ {k′} → k′ ≤ k → ℰL d k′ w L Ml Mr′)
  → ℰL d k w L Ml Mr
stepR-ℰL ≺ L {k} s f =
  toL ≺ k (ℰ-stepR ≺ k x₁ _ s (fromL ≺ k (f ≤-refl)))
  where open One L
stepR-ℰL ≻ {w} L {zero} s f = ℰL-zero ≻ w L
stepR-ℰL ≻ L {suc k} s f =
  toL ≻ (suc k) (ℰ-stepR ≻ k x₁ _ s (fromL ≻ k (f (n≤1+n k))))
  where open One L

-- A side whose type is another store variable takes an identity step.
module _ (d : Dir) {w : World} {L : Leaf (ΔL w) (ΔR w)} (gl : GoodLeaf L)
    where

  idL-rev : ∀ {β γ : TyVar (ΔL w)} R → γ ≢ β → ∀ {fr}
    → Close d w L (λ V → V) fr
    → Close d w L (λ V → V ↑ 〖 β , R ↑ ＇ γ 〗) fr
  idL-rev R ne cl {k} vl vr r =
    ℰL-≡ d k w L (sym (↑-pk (〖〗-other R refl ne))) refl
      (stepL-ℰL d L (id-reveal vl)
        (λ le → cl vl vr (leafRel-down d le w gl r)))

  idL-con : ∀ {β γ : TyVar (ΔL w)} R → γ ≢ β → ∀ {fr}
    → Close d w L (λ V → V) fr
    → Close d w L (λ V → V ↓ makeConceal β R (＇ γ)) fr
  idL-con R ne cl {k} vl vr r =
    ℰL-≡ d k w L (sym (↓-pk (makeConceal-other R refl ne))) refl
      (stepL-ℰL d L (id-conceal vl)
        (λ le → cl vl vr (leafRel-down d le w gl r)))

  idR-rev : ∀ {β′ γ′ : TyVar (storeR w)} R′ → γ′ ≢ β′ → ∀ {fl}
    → Close d w L fl (λ V → V)
    → Close d w L fl (λ V → V ↑ 〖 β′ , R′ ↑ ＇ γ′ 〗)
  idR-rev R′ ne cl {k} vl vr r =
    ℰL-≡ d k w L refl (sym (↑-pk (〖〗-other R′ refl ne)))
      (stepR-ℰL d L (id-reveal vr)
        (λ le → cl vl vr (leafRel-down d le w gl r)))

  idR-con : ∀ {β′ γ′ : TyVar (storeR w)} R′ → γ′ ≢ β′ → ∀ {fl}
    → Close d w L fl (λ V → V)
    → Close d w L fl (λ V → V ↓ makeConceal β′ R′ (＇ γ′))
  idR-con R′ ne cl {k} vl vr r =
    ℰL-≡ d k w L refl (sym (↓-pk (makeConceal-other R′ refl ne)))
      (stepR-ℰL d L (id-conceal vr)
        (λ le → cl vl vr (leafRel-down d le w gl r)))

  -- the trivial closure
  close-id : Close d w L (λ V → V) (λ V → V)
  close-id {k} vl vr r =
    toL d k (ℰ-value d k x₁ _ vl vr (to (𝒱-XY d k ↔-here w {δ = δ₁}) r))
    where open One L

------------------------------------------------------------------------
-- One more seal around a semantic leaf
------------------------------------------------------------------------

sealLΩ : TyVar ΘL → Ty ΘL → RelΩ ΘL ΘR → RelΩ ΘL ΘR
sealLΩ X R P k w τL τR =
  sealedL (toRenameᵗ τL X) (renameᵗ (toRenameᵗ τL) R) (P k w τL τR)

sealRΩ : TyVar ΘR → Ty ΘR → RelΩ ΘL ΘR → RelΩ ΘL ΘR
sealRΩ Y R P k w τL τR =
  sealedRᴿ (ιʷ w) (toRenameᵗ τR Y) (renameᵗ (toRenameᵗ τR) R) (P k w τL τR)

-- a seal at the identity, renamed into a future, is the seal there
seal-coh : ∀ {Θ Θ′} (ρ : Θ ↪ᵗ Θ′) (X : TyVar Θ) (R : Ty Θ)
  → IsSeal (toRenameᵗ (id↪ᵗ ∘↪ ρ) X) (renameᵗ (toRenameᵗ (id↪ᵗ ∘↪ ρ)) R)
      (seal (toRenameᵗ ρ (toRenameᵗ id↪ᵗ X))
        (renameᵗ (toRenameᵗ ρ) (renameᵗ (toRenameᵗ id↪ᵗ) R)))
seal-coh ρ X R =
  trans (cong (toRenameᵗ ρ) (toRename-id-eq X))
    (sym (trans (toRenameᵗ-∘ id↪ᵗ ρ X) (toRename-id-eq (toRenameᵗ ρ X)))) ,
  trans (cong (renameᵗ (toRenameᵗ ρ)) (renameTy-id R))
    (sym (trans (sym (renameTy-∘ id↪ᵗ ρ R)) (renameTy-id _)))

-- a right store seal read through the identity, renamed into a future
sealᴿ-coh : ∀ {w w′ : World} (e : w′ ⊒ w) (Y : TyVar (ΔR w)) (R : Ty (ΔR w))
    {Y₀ R₀}
  → IsSealᴿ (ιʷ w) (toRenameᵗ id↪ᵗ Y) (renameᵗ (toRenameᵗ id↪ᵗ) R)
      (seal Y₀ R₀)
  → IsSealᴿ (ιʷ w′) (toRenameᵗ (id↪ᵗ ∘↪ ρR e) Y)
      (renameᵗ (toRenameᵗ (id↪ᵗ ∘↪ ρR e)) R)
      (seal (toRenameᵗ (ρS e) Y₀) (renameᵗ (toRenameᵗ (ρS e)) R₀))
sealᴿ-coh e Y R {Y₀} {R₀} is =
  subst (λ Z → IsSealᴿ _ Z _ (seal (toRenameᵗ (ρS e) Y₀) _)) (proj₁ sc)
    (IsSealᴿ-rename (coh e) (seal Y₀ R₀) (sym (proj₂ sc)) is)
  where
  sc = seal-coh (ρR e) Y R

value-↓ : ∀ {Θ} {W : Term Θ} {A B} {s : Conv↓ Θ A B}
  → Value (W ↓ s) → Value W
value-↓ (v CT.↓ cv) = v

module _ (d : Dir) {w : World} (P : RelΩ (ΔL w) (ΔR w)) where

  -- the right side's change passes a left seal
  wrapL : ∀ X R {fr} → Close d w (sem P) (λ V → V) fr
    → Close d w (sem (sealLΩ X R P)) (λ V → V) fr
  wrapL X R {fr} cl {k} {Vl} {Vr} vl vr r with sealedL-inv r
  wrapL X R {fr} cl {k} {_} {Vr} vl vr r | W , refl , q =
    I.toL d k
      (ℰ-bind₂ d k O.x₁ I.x₁ w {δ₁ = O.δ₁} {δ₂ = I.δ₁}
        (just (conceal (seal X₀ R₀))) nothing
        (O.fromL d k (cl (value-↓ vl) vr q))
        (λ e₂ {n₂} le₂ {P₁} {P₂} p₁ p₂ q₂ →
          ℰ-value d n₂ I.x₁ _ (p₁ CT.↓ CT.seal) p₂
            (to (𝒱-XY d n₂ ↔-here _ {δ = I.δ₁ ↑ᴵ e₂})
              (seal-coh (ρL e₂) X R ,
               from (𝒱-XY d n₂ ↔-here _ {δ = O.δ₁ ↑ᴵ e₂}) q₂))))
    where
    X₀ = toRenameᵗ id↪ᵗ X
    R₀ = renameᵗ (toRenameᵗ id↪ᵗ) R
    module O = One (sem P)
    module I = One (sem (sealLΩ X R P))

  -- the left side's change passes a right seal
  wrapR : ∀ Y R {fl} → Close d w (sem P) fl (λ V → V)
    → Close d w (sem (sealRΩ Y R P)) fl (λ V → V)
  wrapR Y R {fl} cl {k} {Vl} {Vr} vl vr r with sealedRᴿ-inv r
  wrapR Y R {fl} cl {k} {Vl} {_} vl vr r | W , Y₀ , R₀ , refl , is , q =
    I.toL d k
      (ℰ-bind₂ d k O.x₁ I.x₁ w {δ₁ = O.δ₁} {δ₂ = I.δ₁}
        nothing (just (conceal (seal Y₀ R₀)))
        (O.fromL d k (cl vl (value-↓ vr) q))
        (λ e₂ {n₂} le₂ {P₁} {P₂} p₁ p₂ q₂ →
          ℰ-value d n₂ I.x₁ _ p₁ (p₂ CT.↓ CT.seal)
            (to (𝒱-XY d n₂ ↔-here _ {δ = I.δ₁ ↑ᴵ e₂})
              (sealᴿ-coh e₂ Y R is ,
               from (𝒱-XY d n₂ ↔-here _ {δ = O.δ₁ ↑ᴵ e₂}) q₂))))
    where
    module O = One (sem P)
    module I = One (sem (sealRΩ Y R P))

-- a sealed descriptor's leaf, one seal at a time
module _ (d : Dir) {n′ n} (le : n′ ≤′ n) {ΘL ΘR} (Xs : List (TyVar ΘL))
    (Ys : List (TyVar ΘR)) (c : Desc ΘL ΘR) where

  leafSL≈ : ∀ X → sem (leafBelowS d le (sdesc (X ∷ Xs) Ys c))
    ≈ˡ sem (sealLΩ X (repL Xs c) (leafBelowS d le (sdesc Xs Ys c)))
  leafSL≈ X =
    sem≈
      (λ k w τL τR V V′ r →
        subst (λ T → sealedL (renameVar τL X) T
                       (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′)
          (repL-rename τL τR Xs c)
          (sealSL→ d le Xs Ys c X k w τL τR r))
      (λ k w τL τR V V′ r →
        sealSL← d le Xs Ys c X k w τL τR
          (subst (λ T → sealedL (renameVar τL X) T
                         (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′)
            (sym (repL-rename τL τR Xs c)) r))

  leafSR≈ : ∀ Y → sem (leafBelowS d le (sdesc Xs (Y ∷ Ys) c))
    ≈ˡ sem (sealRΩ Y (repR Ys c) (leafBelowS d le (sdesc Xs Ys c)))
  leafSR≈ Y =
    sem≈
      (λ k w τL τR V V′ r →
        subst (λ T → sealedRᴿ (ιʷ w) (renameVar τR Y) T
                       (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′)
          (repR-rename τL τR Ys c)
          (peelSL-sealedR (ιʷ w) (map (renameVar τL) Xs)
            (renameDesc τL τR c)
            (peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR c)
              peelSR→ r)))
      (λ k w τL τR V V′ r →
        peelSL-map (map (renameVar τL) Xs) (renameDesc τL τR c)
          (peelSR← {ι = ιʷ w})
          (sealedR-peelSL (ιʷ w) (map (renameVar τL) Xs)
            (renameDesc τL τR c)
            (subst (λ T → sealedRᴿ (ιʷ w) (renameVar τR Y) T
                           (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′)
              (sym (repR-rename τL τR Ys c)) r)))

-- closure respects equivalent leaves
Close-resp : ∀ d {w} {L L′ : Leaf (ΔL w) (ΔR w)} {fl fr} → L ≈ˡ L′
  → Close d w L fl fr → Close d w L′ fl fr
Close-resp d {w} h cl {k} vl vr r =
  ℰL-resp d k w h (cl vl vr (leafRel-resp d k w (≈ˡ-sym h) r))

------------------------------------------------------------------------
-- A descriptor's relation, as its clause leaf
------------------------------------------------------------------------

-- σ: the store preimages of the descriptor's right types
module LeafCore (d : Dir) {n′ n} (le : n′ ≤′ n) {w : World} {Δ Δ′}
    {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B)
    (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′) where

  c₀ : Desc (ΔL w) (ΔR w)
  c₀ = desc p env envR

  L : Leaf (ΔL w) (ΔR w)
  L = sem (leafBelow d le c₀)

  δ : Interp Δ Δ′ (ΔL w) (ΔR w)
  δ = envI env envR

  below : ∀ {k w′ τL τR V V′} → leafBelow d le c₀ k w′ τL τR V V′
    → suc k ≤ n′
  below {k} r with suc k ≤? n′
  below {k} r | yes lt = lt
  below {k} () | no ¬lt

  envI-id : envI (renameEntries id↪ᵗ id↪ᵗ env)
      (Vec.map (renameᵗ (toRenameᵗ id↪ᵗ)) envR) ≈ᴵ δ
  envI-id =
    ≈ᴵ-trans (≈ᴵ-sym (envI-transport id↪ᵗ id↪ᵗ env envR)) (transportI-id δ)

  leafIn : ∀ {k Vl Vr} (r : leafRel d k w L Vl Vr) → 𝒱 d k p w δ Vl Vr
  leafIn {k} r =
    𝒱-resp d k p w envI-id
      (to (leafBelow-⇔ d le p env envR (below r) w id↪ᵗ id↪ᵗ) r)

  leafOut : ∀ {w′} (e : w′ ⊒ w) {k} → suc k ≤ n′ → ∀ {V V′}
    → 𝒱 d k p w′ (δ ↑ᴵ e) V V′
    → leafRel d k w′ (transportLeaf (ρL e) (ρR e) L) V V′
  leafOut {w′} e {k} lt r =
    from (leafBelow-⇔ d le p env envR lt w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e))
      (𝒱-resp d k p w′ (≈ᴵ-sym (envI-↑ e {env} {envR} ≈ᴵ-refl)) r)

  toLeaf : ∀ {k M M′} → k < n′ → ℰ d k p w δ M M′ → ℰL d k w L M M′
  toLeaf {k} lt =
    ℰᵍ-map d k w (λ {n₁} le₁ w′ e V V′ r →
      leafOut e (≤-<-trans (≤′⇒≤ le₁) lt) (𝒱≤-cast d le₁ ≤′-refl p w′ r))

  -- σ: store types for the descriptor's right variables
  module _ {σ : Δ′ ⇒ˢ storeR w} where

    -- the store preimage of the descriptor's right type
    rpre≡ : PreB w (lookup envR) σ B → ∀ {T′} → rightTy c₀ ≡ ιT w T′
      → substᵗ σ B ≡ T′
    rpre≡ pre eq =
      renameᵗ-injective (toRenameᵗ-injective (ιʷ w))
        (trans (sym (pre≡ pre)) eq)

    -- the main lemma, at the leaf; pre is the right type's store
    -- preimage, when the right converts
    module _ (orc : ∀ {k} → suc k ≤ n′ → Oracle d k) {β : TyVar (ΔL w)}
        (nβ : ∀ Z → SealNe β (lookup env Z)) (R : Ty (ΔL w))
        {rc : RConv (storeR w)}
        (pre : ∀ {c} → rc ≡ just c → PreB w (lookup envR) σ B)
        (ok : RCOk σ rc) (rs : RCΣ w rc) {T′ : Ty (storeR w)}
        (eq : substᵗ σ B ≡ T′) where

      open Core d {w = w} p env envR using (coreRev; coreCon)

      closeRev : Close d w L (λ V → V ↑ 〖 β , R ↑ leftTy c₀ 〗) (revM rc T′)
      closeRev {Vr = Vr} vl vr r =
        ℰL-≡ d _ w L refl (cong (λ T → revM rc T Vr) eq)
          (toLeaf (below r)
            (coreRev (orc (below r)) nβ R ok rs pre ≤-refl vl vr (leafIn r)))

      closeCon : Close d w L (λ V → V ↓ makeConceal β R (leftTy c₀))
        (conM rc T′)
      closeCon {Vr = Wr} wl wr r =
        ℰL-≡ d _ w L refl (cong (λ T → conM rc T Wr) eq)
          (toLeaf (below r)
            (coreCon (orc (below r)) nβ R ok rs pre ≤-refl wl wr (leafIn r)))

    -- the right-only lemma, at the leaf
    module _ (orc : ∀ {k} → suc k ≤ n′ → OracleR d k)
        {β′ : TyVar (storeR w)} (R′ : Ty (storeR w))
        (pre : PreB w (lookup envR) σ B)
        (f : ∀ Y′ → RFresh★ β′ (σ Y′)) (bs : RCΣ w (just (β′ , R′)))
        {T′ : Ty (storeR w)} (eq : rightTy c₀ ≡ ιT w T′) where

      open Core d {w = w} p env envR using (coreRevR; coreConR)

      closeRevR : Close d w L (λ V → V) (λ V → V ↑ 〖 β′ , R′ ↑ T′ 〗)
      closeRevR {Vr = Vr} vl vr r =
        ℰL-≡ d _ w L refl
          (cong (λ T → Vr ↑ 〖 β′ , R′ ↑ T 〗) (rpre≡ pre eq))
          (toLeaf (below r)
            (coreRevR (orc (below r)) R′ pre f bs ≤-refl vl vr (leafIn r)))

      closeConR : Close d w L (λ V → V)
        (λ V → V ↓ makeConceal β′ R′ T′)
      closeConR {Vr = Wr} vl wr r =
        ℰL-≡ d _ w L refl
          (cong (λ T → Wr ↓ makeConceal β′ R′ T) (rpre≡ pre eq))
          (toLeaf (below r)
            (coreConR (orc (below r)) R′ pre f bs ≤-refl vl wr (leafIn r)))

------------------------------------------------------------------------
-- A sealed descriptor's leaf, at the current world
------------------------------------------------------------------------

-- the outermost seal is not the converted store variable
HeadNe : ∀ {Θ} → TyVar Θ → List (TyVar Θ) → Set
HeadNe β [] = ⊤
HeadNe β (X ∷ Xs) = X ≢ β

-- under a right seal, the right store type is another store variable
HeadNeR : ∀ {Θ ΘR} → RConv Θ → List (TyVar ΘR) → Ty Θ → Set
HeadNeR nothing Ys T′ = ⊤
HeadNeR (just (β′ , R′)) [] T′ = ⊤
HeadNeR (just (β′ , R′)) (Y ∷ Ys) T′ = RFresh β′ T′

module SealedNow (d : Dir) {n′ n} (le : n′ ≤′ n) {w : World} {Δ Δ′}
    {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B)
    (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {σ : Δ′ ⇒ˢ storeR w} where

  open LeafCore d le {w = w} p env envR using (c₀)
  open LeafCore d le {w = w} p env envR
    using (rpre≡; closeRev; closeCon; closeRevR; closeConR)

  LS : List (TyVar (ΔL w)) → List (TyVar (ΔR w)) → Leaf (ΔL w) (ΔR w)
  LS Xs Ys = sem (leafBelowS d le (sdesc Xs Ys c₀))

  gLS : ∀ Xs Ys → GoodLeaf (LS Xs Ys)
  gLS Xs Ys = leafBelowS-good d le (sdesc Xs Ys c₀)

  -- the right side alone converts, past the left seals
  module _ (orc : ∀ {k} → suc k ≤ n′ → OracleR d k)
      {β′ : TyVar (storeR w)} (R′ : Ty (storeR w))
      (pre : PreB w (lookup envR) σ B)
      (f : ∀ Y′ → RFresh★ β′ (σ Y′)) (bs : RCΣ w (just (β′ , R′)))
      {T′ : Ty (storeR w)} (eq : rightTy c₀ ≡ ιT w T′) where

    revRS : ∀ Xs
      → Close d w (LS Xs []) (λ V → V) (λ V → V ↑ 〖 β′ , R′ ↑ T′ 〗)
    revRS [] = closeRevR orc R′ pre f bs eq
    revRS (X ∷ Xs) =
      Close-resp d (≈ˡ-sym (leafSL≈ d le Xs [] c₀ X))
        (wrapL d {w = w} (leafBelowS d le (sdesc Xs [] c₀)) X (repL Xs c₀)
          (revRS Xs))

    conRS : ∀ Xs
      → Close d w (LS Xs []) (λ V → V)
          (λ V → V ↓ makeConceal β′ R′ T′)
    conRS [] = closeConR orc R′ pre f bs eq
    conRS (X ∷ Xs) =
      Close-resp d (≈ˡ-sym (leafSL≈ d le Xs [] c₀ X))
        (wrapL d {w = w} (leafBelowS d le (sdesc Xs [] c₀)) X (repL Xs c₀)
          (conRS Xs))

  -- the left side alone converts, past the right seals
  module _ (orc : ∀ {k} → suc k ≤ n′ → Oracle d k) {β : TyVar (ΔL w)}
      (nβ : ∀ Z → SealNe β (lookup env Z)) (R : Ty (ΔL w)) where

    revLS : ∀ Ys
      → Close d w (LS [] Ys) (λ V → V ↑ 〖 β , R ↑ leftTy c₀ 〗) (λ V → V)
    revLS [] = closeRev {σ = σ} orc nβ R (λ ()) rc-none tt refl
    revLS (Y ∷ Ys) =
      Close-resp d (≈ˡ-sym (leafSR≈ d le [] Ys c₀ Y))
        (wrapR d {w = w} (leafBelowS d le (sdesc [] Ys c₀)) Y (repR Ys c₀)
          (revLS Ys))

    conLS : ∀ Ys
      → Close d w (LS [] Ys) (λ V → V ↓ makeConceal β R (leftTy c₀))
          (λ V → V)
    conLS [] = closeCon {σ = σ} orc nβ R (λ ()) rc-none tt refl
    conLS (Y ∷ Ys) =
      Close-resp d (≈ˡ-sym (leafSR≈ d le [] Ys c₀ Y))
        (wrapR d {w = w} (leafBelowS d le (sdesc [] Ys c₀)) Y (repR Ys c₀)
          (conLS Ys))

  -- at a descriptor without right seals, its right type's store
  -- preimage
  PreIf : List (TyVar (ΔR w)) → Set
  PreIf [] = PreB w (lookup envR) σ B
  PreIf (Y ∷ Ys) = ⊤

  -- fresh for both sides' conversions, at the store type T′
  record FreshFor (β : TyVar (ΔL w)) (rc : RConv (storeR w))
      (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w)))
      (T′ : Ty (storeR w)) : Set where
    field
      headL : HeadNe β Xs
      headR : HeadNeR rc Ys T′
      entL : ∀ Z → SealNe β (lookup env Z)
      entR : RCOk σ rc
      entΣ : RCΣ w rc
      preF : PreIf Ys

  open FreshFor public

  module _ (orc : ∀ {k} → suc k ≤ n′ → Oracle d k)
      (orcR : ∀ {k} → suc k ≤ n′ → OracleR d k) {β : TyVar (ΔL w)}
      (R : Ty (ΔL w)) where

    -- both sides convert; T′ is a store preimage of the right type
    revPS : ∀ {rc} Xs Ys {T′} → repR Ys c₀ ≡ ιT w T′
      → FreshFor β rc Xs Ys T′
      → Close d w (LS Xs Ys)
          (λ V → V ↑ 〖 β , R ↑ repL Xs c₀ 〗) (revM rc T′)
    revPS {nothing} (X ∷ Xs) Ys eq fr =
      idL-rev d (gLS (X ∷ Xs) Ys) R (headL fr) (close-id d (gLS (X ∷ Xs) Ys))
    revPS {just (β′ , R′)} (X ∷ Xs) (Y ∷ Ys) eq fr with headR fr
    revPS {just (β′ , R′)} (X ∷ Xs) (Y ∷ Ys) eq fr | γ′ , refl , ne =
      idL-rev d (gLS (X ∷ Xs) (Y ∷ Ys)) R (headL fr)
        (idR-rev d (gLS (X ∷ Xs) (Y ∷ Ys)) R′ ne
          (close-id d (gLS (X ∷ Xs) (Y ∷ Ys))))
    revPS {just (β′ , R′)} (X ∷ Xs) [] eq fr with entR fr
    revPS {just (β′ , R′)} (X ∷ Xs) [] eq fr | rc-just f =
      idL-rev d (gLS (X ∷ Xs) []) R (headL fr)
        (revRS orcR R′ (preF fr) f (entΣ fr) eq (X ∷ Xs))
    revPS {nothing} [] Ys eq fr = revLS orc (entL fr) R Ys
    revPS {just (β′ , R′)} [] (Y ∷ Ys) eq fr with headR fr
    revPS {just (β′ , R′)} [] (Y ∷ Ys) eq fr | γ′ , refl , ne =
      idR-rev d (gLS [] (Y ∷ Ys)) R′ ne
        (revLS orc (entL fr) R (Y ∷ Ys))
    revPS {just (β′ , R′)} [] [] eq fr =
      closeRev orc (entL fr) R (λ _ → preF fr) (entR fr)
        (entΣ fr)
        (rpre≡ (preF fr) eq)

    conPS : ∀ {rc} Xs Ys {T′} → repR Ys c₀ ≡ ιT w T′
      → FreshFor β rc Xs Ys T′
      → Close d w (LS Xs Ys)
          (λ V → V ↓ makeConceal β R (repL Xs c₀)) (conM rc T′)
    conPS {nothing} (X ∷ Xs) Ys eq fr =
      idL-con d (gLS (X ∷ Xs) Ys) R (headL fr) (close-id d (gLS (X ∷ Xs) Ys))
    conPS {just (β′ , R′)} (X ∷ Xs) (Y ∷ Ys) eq fr with headR fr
    conPS {just (β′ , R′)} (X ∷ Xs) (Y ∷ Ys) eq fr | γ′ , refl , ne =
      idL-con d (gLS (X ∷ Xs) (Y ∷ Ys)) R (headL fr)
        (idR-con d (gLS (X ∷ Xs) (Y ∷ Ys)) R′ ne
          (close-id d (gLS (X ∷ Xs) (Y ∷ Ys))))
    conPS {just (β′ , R′)} (X ∷ Xs) [] eq fr with entR fr
    conPS {just (β′ , R′)} (X ∷ Xs) [] eq fr | rc-just f =
      idL-con d (gLS (X ∷ Xs) []) R (headL fr)
        (conRS orcR R′ (preF fr) f (entΣ fr) eq (X ∷ Xs))
    conPS {nothing} [] Ys eq fr = conLS orc (entL fr) R Ys
    conPS {just (β′ , R′)} [] (Y ∷ Ys) eq fr with headR fr
    conPS {just (β′ , R′)} [] (Y ∷ Ys) eq fr | γ′ , refl , ne =
      idR-con d (gLS [] (Y ∷ Ys)) R′ ne
        (conLS orc (entL fr) R (Y ∷ Ys))
    conPS {just (β′ , R′)} [] [] eq fr =
      closeCon orc (entL fr) R (λ _ → preF fr) (entR fr)
        (entΣ fr)
        (rpre≡ (preF fr) eq)

------------------------------------------------------------------------
-- The left-only leaf in `≻`: the guarded relation
------------------------------------------------------------------------

-- a descriptor's entry: the conversion is an identity step
module _ {w : World} {β : TyVar (ΔL w)} (R : Ty (ΔL w)) where

  entryRevStep : ∀ (e : Entry (ΔL w) (ΔR w)) → SealNe β e → ∀ {V}
    → Value V → (V ↑ 〖 β , R ↑ entryTy e 〗) —→ V
  entryRevStep (seals X Xs Ys c) ne {V} v =
    subst (λ M → M —→ V) (sym (↑-pk (〖〗-other R refl ne))) (id-reveal v)

  entryConStep : ∀ (e : Entry (ΔL w) (ΔR w)) → SealNe β e → ∀ {W}
    → Value W → (W ↓ makeConceal β R (entryTy e)) —→ W
  entryConStep (seals X Xs Ys c) ne {W} v =
    subst (λ M → M —→ W) (sym (↓-pk (makeConceal-other R refl ne)))
      (id-conceal v)

  entryRevO : ∀ {k} (e : Entry (ΔL w) (ΔR w)) → SealNe β e → ∀ {Vl Vr}
    → Value Vl → Value Vr → leafRel ≻ k w (syn e) Vl Vr
    → ℰL ≻ k w (syn e) (Vl ↑ 〖 β , R ↑ entryTy e 〗) Vr
  entryRevO {k} (seals X Xs Ys c) ne vl vr r =
    idRevO ≻ k w (syn _) good-syn ne vl vr r

  entryConO : ∀ {k} (e : Entry (ΔL w) (ΔR w)) → SealNe β e → ∀ {Wl Vr}
    → Value Wl → Value Vr → leafRel ≻ k w (syn e) Wl Vr
    → ℰL ≻ k w (syn e) (Wl ↓ makeConceal β R (entryTy e)) Vr
  entryConO {k} (seals X Xs Ys c) ne wl vr r =
    idConO ≻ k w (syn _) good-syn ne wl vr r

-- At a derivation into `★`, `G` at stage k + 1 reads the clauses at
-- stage k, so the lemma at bound k converts it.
module StarG {w : World} {Δ Δ′} {Φ : Corr Δ Δ′}
    (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
    {N : ℕ} {rk : RK} {β : TyVar (ΔL w)} {R : Ty (ΔL w)}
    (nβ : ∀ Z → SealNe β (lookup env Z)) {σ : Δ′ ⇒ˢ storeR w} where

  δ′ : Interp (suc Δ) Δ′ (ΔL w) (ΔR w)
  δ′ = extDeadI ★ (envI env envR)

  module _ (h : ConvI ≻ N rk w (m-none {Φ = dead Φ} {X = zero} R nothing) β
      δ′ δ′ σ σ) where

    revG★ : ∀ {A₁} (p₁ : dead Φ ⊢ A₁ ⊑ ★) {j} → j ≤ N → ∀ {Vl Vr}
      → Value Vl → Value Vr → G (suc j) p₁ w δ′ Vl Vr
      → ℰ ≻ (suc j) p₁ w δ′ (Vl ↑ 〖 β , R ↑ substᵗ (δl δ′) A₁ 〗) Vr
    revG★ ★⊑★ {j} le vl vr q =
      ℰ-steps? ≻ (suc j) ★⊑★ w (goodT h) (step (id-reveal vl)) stay vl vr q
    revG★ ι⊑★ {j} le vl vr q =
      ℰ-steps? ≻ (suc j) ι⊑★ w (goodT h) (step (id-reveal vl)) stay vl vr q
    revG★ (X⊑★ (only-dead {X = Z} z)) {j} le vl vr q =
      ℰL→X★ ≻ (suc j) (only-dead z) w
        (entryRevO R (lookup env Z) (nβ Z) vl vr q)
    revG★ (⇒⊑★ p q) {j} le vl vr r =
      ℰ-value ≻ (suc j) (⇒⊑★ p q) w (vl CT.↑ CT.fun) vr
        (funStar-map (λ v f → fun-rev h pre★⇒ le vl v f) vr r)
      where
      open FunConv {X = zero} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
        (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
        (λ h′ _ → rev★ ≻ q h′) (λ h′ _ → con★ ≻ q h′)
        (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
    revG★ (∀⊑ Anv z p) {j} le vl vr r =
      ℰ-value ≻ (suc j) (∀⊑ Anv z p) w (vl CT.↑ CT.all) vr
        (OnlyV.revV ≻ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
          (λ σ → refl) (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
          w h pre★ le vl vr r)
    revG★ ∀★⊑★ {j} le vl vr r =
      ℰ-value ≻ (suc j) ∀★⊑★ w (vl CT.↑ CT.all) vr
        (to (allDeadStar-★ ≻ j {Ψ = dead Φ} w {δ = δ′})
          (allDeadStar-map
            (DeadV.revV ≻ N (★⊑★ {Φ = dead (dead Φ)}) (rev★★ ≻) (con★★ ≻)
              w h le vl)
            vr (from (allDeadStar-★ ≻ j {Ψ = dead Φ} w {δ = δ′}) r)))
    revG★ (∀⊑★ ns p) {j} le vl vr r =
      ℰ-value ≻ (suc j) (∀⊑★ ns p) w (vl CT.↑ CT.all) vr
        (allDeadStar-map
          (DeadV.revV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
            w h le vl)
          vr r)
    revG★ bot⊑★ le vl vr ()

    conG★ : ∀ {A₁} (p₁ : dead Φ ⊢ A₁ ⊑ ★) {j} → j ≤ N → ∀ {Wl Vr}
      → Value Wl → Value Vr → G (suc j) p₁ w δ′ Wl Vr
      → ℰ ≻ (suc j) p₁ w δ′ (Wl ↓ makeConceal β R (substᵗ (δl δ′) A₁)) Vr
    conG★ ★⊑★ {j} le wl vr q =
      ℰ-steps? ≻ (suc j) ★⊑★ w (goodS h) (step (id-conceal wl)) stay wl vr q
    conG★ ι⊑★ {j} le wl vr q =
      ℰ-steps? ≻ (suc j) ι⊑★ w (goodS h) (step (id-conceal wl)) stay wl vr q
    conG★ (X⊑★ (only-dead {X = Z} z)) {j} le wl vr q =
      ℰL→X★ ≻ (suc j) (only-dead z) w
        (entryConO R (lookup env Z) (nβ Z) wl vr q)
    conG★ (⇒⊑★ p q) {j} le wl vr r =
      ℰ-value ≻ (suc j) (⇒⊑★ p q) w (wl CT.↓ CT.fun) vr
        (funStar-map (λ v f → fun-con h pre★⇒ le wl v f) vr r)
      where
      open FunConv {X = zero} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
        (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
        (λ h′ _ → rev★ ≻ q h′) (λ h′ _ → con★ ≻ q h′)
        (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
    conG★ (∀⊑ Anv z p) {j} le wl vr r =
      ℰ-value ≻ (suc j) (∀⊑ Anv z p) w (wl CT.↓ CT.all) vr
        (OnlyV.conV ≻ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
          (λ σ → refl) (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
          w h pre★ le wl vr r)
    conG★ ∀★⊑★ {j} le wl vr r =
      ℰ-value ≻ (suc j) ∀★⊑★ w (wl CT.↓ CT.all) vr
        (to (allDeadStar-★ ≻ j {Ψ = dead Φ} w {δ = δ′})
          (allDeadStar-map
            (DeadV.conV ≻ N (★⊑★ {Φ = dead (dead Φ)}) (rev★★ ≻) (con★★ ≻)
              w h le wl)
            vr (from (allDeadStar-★ ≻ j {Ψ = dead Φ} w {δ = δ′}) r)))
    conG★ (∀⊑★ ns p) {j} le wl vr r =
      ℰ-value ≻ (suc j) (∀⊑★ ns p) w (wl CT.↓ CT.all) vr
        (allDeadStar-map
          (DeadV.conV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
            w h le wl)
          vr r)
    conG★ bot⊑★ le wl vr ()

-- the guarded relation as the left-only leaf
module LeafG {n′ n} (le : n′ ≤′ n) {w : World} {Δ Δ′} {Φ : Corr Δ Δ′}
    {A B} (p : Φ ⊢ A ⊑ B) (env : Vec (Entry (ΔL w) (ΔR w)) Δ)
    (envR : Vec (Ty (ΔR w)) Δ′) where

  open LeafCore ≻ le {w = w} p env envR using (c₀; δ; envI-id)

  L : Leaf (ΔL w) (ΔR w)
  L = sem (leafG le c₀)

  gL : GoodLeaf L
  gL = onlyLeafS-good ≻ le (sdesc [] [] c₀)

  belowG : ∀ {k w′ τL τR V V′} → leafG le c₀ k w′ τL τR V V′ → k ≤ n′
  belowG {k} r with k ≤? n′
  belowG {k} r | yes le′ = le′
  belowG {k} () | no ¬le

  leafInG : ∀ {k Vl Vr} (r : leafRel ≻ k w L Vl Vr) → G k p w δ Vl Vr
  leafInG {k} {Vl} {Vr} r =
    G-resp k p w envI-id
      (to (leafG-⇔ le p env envR
            (belowG {k} {w} {id↪ᵗ} {id↪ᵗ} {Vl} {Vr} r) w id↪ᵗ id↪ᵗ) r)

  leafOutG : ∀ {w′} (e : w′ ⊒ w) {k} → k ≤ n′ → ∀ {V V′}
    → G k p w′ (δ ↑ᴵ e) V V′
    → leafRel ≻ k w′ (transportLeaf (ρL e) (ρR e) L) V V′
  leafOutG {w′} e {k} le′ r =
    from (leafG-⇔ le p env envR le′ w′ (id↪ᵗ ∘↪ ρL e) (id↪ᵗ ∘↪ ρR e))
      (G-resp k p w′ (≈ᴵ-sym (envI-↑ e {env} {envR} ≈ᴵ-refl)) r)

  leafBackG : ∀ {k} → k ≤ n′ → ∀ {V V′} → G k p w δ V V′
    → leafRel ≻ k w L V V′
  leafBackG {k} le′ r =
    from (leafG-⇔ le p env envR le′ w id↪ᵗ id↪ᵗ)
      (G-resp k p w (≈ᴵ-sym envI-id) r)

  -- the expression closure of `G`
  ℰG : ℕ → Term (ΔL w) → Term (storeR w) → Set
  ℰG k = ℰᵍ ≻ k w (λ le₁ w′ e → G≤ le₁ p w′ (δ ↑ᴵ e))

  toLeafG : ∀ {k M M′} → k ≤ n′ → ℰG k M M′ → ℰL ≻ k w L M M′
  toLeafG {k} lt =
    ℰᵍ-map ≻ k w {VR = λ le₁ w′ e → G≤ le₁ p w′ (δ ↑ᴵ e)}
      {VR′ = λ {n₁} le₁ w′ e →
        leafRel ≻ n₁ w′ (transportLeaf (ρL e) (ρR e) L)}
      (λ le₁ w′ e V V′ r →
      leafOutG e (≤-trans (≤′⇒≤ le₁) lt) (G≤→G le₁ p w′ r))

  -- at a derivation into `★`, `G` is the value relation
  fromStar : (∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
                → 𝒱 ≻ n₁ p w′ δ₀ V V′ → G n₁ p w′ δ₀ V V′)
    → ∀ {k M M′} → ℰ ≻ k p w δ M M′ → ℰG k M M′
  fromStar f {k} =
    ℰᵍ-map ≻ k w {VR = λ le₁ w′ e → 𝒱≤ ≻ le₁ p w′ (δ ↑ᴵ e)}
      {VR′ = λ le₁ w′ e → G≤ le₁ p w′ (δ ↑ᴵ e)}
      (λ {n₁} le₁ w′ e V V′ r →
      G→G≤ le₁ p w′ (f n₁ (𝒱≤-cast ≻ le₁ ≤′-refl p w′ r)))

  -- elsewhere, `G` reads the value relation one stage down; the right
  -- is a value, so it takes no step
  shiftG : (∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
              → 𝒱 ≻ n₁ p w′ δ₀ V V′ → G (suc n₁) p w′ δ₀ V V′)
    → ∀ {j Ml Mr} → 0 < j → Value Mr → ℰ ≻ j p w δ Ml Mr
    → ℰG (suc j) Ml Mr
  shiftG f {zero} () vr r
  shiftG f {suc j} lt vr (inj₁ (Δ₁ , χs , N , more s ss)) =
    ⊥-elim (value-no-step vr s)
  shiftG f {suc j} lt vr (inj₂ (inj₁ b)) = inj₂ (inj₁ b)
  shiftG f {suc j} lt vr
      (inj₂ (inj₂ (k′ , n₁ , le₁ , ΔL′ , χsL , Vl′ , ΔR′ , χsR , Vr′ ,
        eq , sl , sr , vl′ , vr′ , Δ₂ , p₂ , ρ₂ , st , tags , ok , r))) =
    inj₂ (inj₂ (k′ , suc n₁ , s≤′s le₁ , ΔL′ , χsL , Vl′ , ΔR′ , χsR , Vr′ ,
      trans (+-suc k′ n₁) (cong suc eq) , sl , sr , vl′ , vr′ ,
      Δ₂ , p₂ , ρ₂ , st , tags , ok ,
      G→G≤ (s≤′s le₁) p _ (f n₁ (𝒱≤-cast ≻ le₁ ≤′-refl p _ r))))

  -- related values at a stage up to the bound
  valL : ∀ {k} → k ≤ n′ → ∀ {V V′} → Value V → Value V′ → G k p w δ V V′
    → ℰL ≻ k w L V V′
  valL lt v v′ g = close-id ≻ gL v v′ (leafBackG lt g)

  -- one left step, then related values
  stepValL : ∀ {k} → k ≤ n′ → ∀ {Ml V V′} → Ml —→ V → Value V → Value V′
    → G k p w δ V V′ → ℰL ≻ k w L Ml V′
  stepValL lt s v v′ g =
    stepL-ℰL ≻ L s
      (λ le′ → close-id ≻ gL v v′ (leafRel-down ≻ le′ w gL (leafBackG lt g)))

-- every clause is trivial at stage 0
fun0 : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A A′ B B′} {p : Φ ⊢ A ⊑ A′}
    {q : Φ ⊢ B ⊑ B′} {w} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → funRel d 0 p q w δ V V′
fun0 d e ≤′-refl Wl Wr wl wr a t = ℰᵍ-zero d _

all0 : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A B} {p : pair Φ ⊢ A ⊑ B} {w}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → allPair d 0 p w δ V V′
all0 d e ≤′-refl c wf T₀ eqT B₀ eqB = ℰᵍ-zero d _

only0 : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A B} {p : only Φ ⊢ A ⊑ B} {w}
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → allOnly d 0 p w δ V V′
only0 d e ≤′-refl c = ℰᵍ-zero d _

-- the store types of a left-only leaf's right variables, which the
-- right side never reads
σ★ : ∀ {Δ′ Θ} → Δ′ ⇒ˢ Θ
σ★ Y = ★

module GClose {n′ n} (le : n′ ≤′ n) {w : World}
    (orc : ∀ {k} → suc k ≤ n′ → Oracle ≻ k) {β : TyVar (ΔL w)}
    (R : Ty (ΔL w)) where

  private
    LG = λ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B)
           (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
         → sem (leafG le (desc p env envR))

  module _ {Δ Δ′} {Φ : Corr Δ Δ′} (env : Vec (Entry (ΔL w) (ΔR w)) Δ)
      (envR : Vec (Ty (ΔR w)) Δ′) (nβ : ∀ Z → SealNe β (lookup env Z))
      where

    δ : Interp Δ Δ′ (ΔL w) (ΔR w)
    δ = envI env envR

    -- into `★`: the lemma's clauses at the stage below
    starRev : ∀ {A} (p : Φ ⊢ A ⊑ ★) j → suc j ≤ n′
      → (∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
           → 𝒱 ≻ n₁ p w′ δ₀ V V′ → G n₁ p w′ δ₀ V V′)
      → ∀ {Vl Vr} → Value Vl → Value Vr → G (suc j) p w δ Vl Vr
      → ℰL ≻ (suc j) w (LG p env envR)
          (Vl ↑ 〖 β , R ↑ leftTy (desc p env envR) 〗) Vr
    starRev {A} p j lt f {Vl} vl vr q =
      toLeafG lt
        (fromStar f
          (back
            (ℰ-≡ ≻ (suc j) (renᵖ wk-deadᴿ p) w _
              (cong (λ T → Vl ↑ 〖 β , R ↑ T 〗) tyA) refl
              (revG★ (hyp (orc lt) nβ R {σ = σ★} rc-none tt) (renᵖ wk-deadᴿ p)
                ≤-refl
                vl vr (to (G-ren (suc j) wk-deadᴿ p w renI) q)))))
      where
      open LeafG le {w = w} p env envR using (toLeafG; fromStar)
      open Core ≻ {w = w} p env envR using (back; tyA; hyp; renI)
      open StarG {w = w} env envR nβ using (revG★)

    starCon : ∀ {A} (p : Φ ⊢ A ⊑ ★) j → suc j ≤ n′
      → (∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
           → 𝒱 ≻ n₁ p w′ δ₀ V V′ → G n₁ p w′ δ₀ V V′)
      → ∀ {Wl Vr} → Value Wl → Value Vr → G (suc j) p w δ Wl Vr
      → ℰL ≻ (suc j) w (LG p env envR)
          (Wl ↓ makeConceal β R (leftTy (desc p env envR))) Vr
    starCon {A} p j lt f {Wl} wl vr q =
      toLeafG lt
        (fromStar f
          (back
            (ℰ-≡ ≻ (suc j) (renᵖ wk-deadᴿ p) w _
              (cong (λ T → Wl ↓ makeConceal β R T) tyA) refl
              (conG★ (hyp (orc lt) nβ R {σ = σ★} rc-none tt) (renᵖ wk-deadᴿ p)
                ≤-refl
                wl vr (to (G-ren (suc j) wk-deadᴿ p w renI) q)))))
      where
      open LeafG le {w = w} p env envR using (toLeafG; fromStar)
      open Core ≻ {w = w} p env envR using (back; tyA; hyp; renI)
      open StarG {w = w} env envR nβ using (conG★)

    -- elsewhere, above stage 1: the lemma at the stage below
    shiftRev : ∀ {A B} (p : Φ ⊢ A ⊑ B) j → suc (suc j) ≤ n′
      → (∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
           → 𝒱 ≻ n₁ p w′ δ₀ V V′ → G (suc n₁) p w′ δ₀ V V′)
      → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 ≻ (suc j) p w δ Vl Vr
      → ℰL ≻ (suc (suc j)) w (LG p env envR)
          (Vl ↑ 〖 β , R ↑ leftTy (desc p env envR) 〗) Vr
    shiftRev p j lt f vl vr q =
      toLeafG lt
        (shiftG f (s≤s z≤n) vr
          (coreRev (orc lt) nβ R {σ = σ★} rc-none tt (λ ()) ≤-refl vl vr q))
      where
      open LeafG le {w = w} p env envR using (toLeafG; shiftG)
      open Core ≻ {w = w} p env envR using (coreRev)

    shiftCon : ∀ {A B} (p : Φ ⊢ A ⊑ B) j → suc (suc j) ≤ n′
      → (∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
           → 𝒱 ≻ n₁ p w′ δ₀ V V′ → G (suc n₁) p w′ δ₀ V V′)
      → ∀ {Wl Vr} → Value Wl → Value Vr → 𝒱 ≻ (suc j) p w δ Wl Vr
      → ℰL ≻ (suc (suc j)) w (LG p env envR)
          (Wl ↓ makeConceal β R (leftTy (desc p env envR))) Vr
    shiftCon p j lt f wl vr q =
      toLeafG lt
        (shiftG f (s≤s z≤n) vr
          (coreCon (orc lt) nβ R {σ = σ★} rc-none tt (λ ()) ≤-refl wl vr q))
      where
      open LeafG le {w = w} p env envR using (toLeafG; shiftG)
      open Core ≻ {w = w} p env envR using (coreCon)

    -- the guarded relation at stage k + 1, by the derivation
    revS : ∀ {A B} (p : Φ ⊢ A ⊑ B) j → suc j ≤ n′ → ∀ {Vl Vr}
      → Value Vl → Value Vr → G (suc j) p w δ Vl Vr
      → ℰL ≻ (suc j) w (LG p env envR)
          (Vl ↑ 〖 β , R ↑ leftTy (desc p env envR) 〗) Vr
    revS ★⊑★ j lt = starRev ★⊑★ j lt (λ n₁ r → r)
    revS ι⊑★ j lt = starRev ι⊑★ j lt (λ n₁ r → r)
    revS (X⊑★ x) j lt = starRev (X⊑★ x) j lt fX
      where
      fX : ∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
        → 𝒱 ≻ n₁ (X⊑★ x) w′ δ₀ V V′ → G n₁ (X⊑★ x) w′ δ₀ V V′
      fX zero r = tt
      fX (suc n₁) r = r
    revS (⇒⊑★ p q) j lt = starRev (⇒⊑★ p q) j lt (λ n₁ r → r)
    revS (∀⊑ {B = ★} a z p) j lt = starRev (∀⊑ a z p) j lt (λ n₁ r → r)
    revS ∀★⊑★ j lt = starRev ∀★⊑★ j lt (λ n₁ r → r)
    revS (∀⊑★ ns p) j lt = starRev (∀⊑★ ns p) j lt (λ n₁ r → r)
    revS bot⊑★ j lt vl vr ()
    revS ι⊑ι zero lt vl vr q =
      LeafG.stepValL le {w = w} ι⊑ι env envR lt (id-reveal vl) vl vr q
    revS ι⊑ι (suc j) lt = shiftRev ι⊑ι j lt (λ n₁ r → r)
    revS (X⊑Y {X = Z} x) zero lt vl vr q =
      LeafG.stepValL le {w = w} (X⊑Y x) env envR lt
        (entryRevStep {w = w} R (lookup env Z) (nβ Z) vl) vl vr q
    revS (X⊑Y x) (suc j) lt = shiftRev (X⊑Y x) j lt (λ n₁ r → r)
    revS (⇒⊑⇒ p q) zero lt vl vr g =
      LeafG.valL le {w = w} (⇒⊑⇒ p q) env envR lt (vl CT.↑ CT.fun) vr
        (fun0 ≻)
    revS (⇒⊑⇒ p q) (suc j) lt = shiftRev (⇒⊑⇒ p q) j lt (λ n₁ r → r)
    revS (∀⊑∀ p) zero lt vl vr g =
      LeafG.valL le {w = w} (∀⊑∀ p) env envR lt (vl CT.↑ CT.all) vr (all0 ≻)
    revS (∀⊑∀ p) (suc j) lt = shiftRev (∀⊑∀ p) j lt (λ n₁ r → r)
    revS (∀⊑ {B = ＇ Y} a z p) zero lt vl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (vl CT.↑ CT.all) vr
        (only0 ≻)
    revS (∀⊑ {B = ＇ Y} a z p) (suc j) lt =
      shiftRev (∀⊑ a z p) j lt (λ n₁ r → r)
    revS (∀⊑ {B = ‵ ι} a z p) zero lt vl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (vl CT.↑ CT.all) vr
        (only0 ≻)
    revS (∀⊑ {B = ‵ ι} a z p) (suc j) lt =
      shiftRev (∀⊑ a z p) j lt (λ n₁ r → r)
    revS (∀⊑ {B = B₁ ⇒ B₂} a z p) zero lt vl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (vl CT.↑ CT.all) vr
        (only0 ≻)
    revS (∀⊑ {B = B₁ ⇒ B₂} a z p) (suc j) lt =
      shiftRev (∀⊑ a z p) j lt (λ n₁ r → r)
    revS (∀⊑ {B = `∀ B₁} a z p) zero lt vl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (vl CT.↑ CT.all) vr
        (only0 ≻)
    revS (∀⊑ {B = `∀ B₁} a z p) (suc j) lt =
      shiftRev (∀⊑ a z p) j lt (λ n₁ r → r)
    revS bot-elim j lt vl vr ()

    conS : ∀ {A B} (p : Φ ⊢ A ⊑ B) j → suc j ≤ n′ → ∀ {Wl Vr}
      → Value Wl → Value Vr → G (suc j) p w δ Wl Vr
      → ℰL ≻ (suc j) w (LG p env envR)
          (Wl ↓ makeConceal β R (leftTy (desc p env envR))) Vr
    conS ★⊑★ j lt = starCon ★⊑★ j lt (λ n₁ r → r)
    conS ι⊑★ j lt = starCon ι⊑★ j lt (λ n₁ r → r)
    conS (X⊑★ x) j lt = starCon (X⊑★ x) j lt fX
      where
      fX : ∀ n₁ {w′} {δ₀ : Interp Δ Δ′ (ΔL w′) (ΔR w′)} {V V′}
        → 𝒱 ≻ n₁ (X⊑★ x) w′ δ₀ V V′ → G n₁ (X⊑★ x) w′ δ₀ V V′
      fX zero r = tt
      fX (suc n₁) r = r
    conS (⇒⊑★ p q) j lt = starCon (⇒⊑★ p q) j lt (λ n₁ r → r)
    conS (∀⊑ {B = ★} a z p) j lt = starCon (∀⊑ a z p) j lt (λ n₁ r → r)
    conS ∀★⊑★ j lt = starCon ∀★⊑★ j lt (λ n₁ r → r)
    conS (∀⊑★ ns p) j lt = starCon (∀⊑★ ns p) j lt (λ n₁ r → r)
    conS bot⊑★ j lt wl vr ()
    conS ι⊑ι zero lt wl vr q =
      LeafG.stepValL le {w = w} ι⊑ι env envR lt (id-conceal wl) wl vr q
    conS ι⊑ι (suc j) lt = shiftCon ι⊑ι j lt (λ n₁ r → r)
    conS (X⊑Y {X = Z} x) zero lt wl vr q =
      LeafG.stepValL le {w = w} (X⊑Y x) env envR lt
        (entryConStep {w = w} R (lookup env Z) (nβ Z) wl) wl vr q
    conS (X⊑Y x) (suc j) lt = shiftCon (X⊑Y x) j lt (λ n₁ r → r)
    conS (⇒⊑⇒ p q) zero lt wl vr g =
      LeafG.valL le {w = w} (⇒⊑⇒ p q) env envR lt (wl CT.↓ CT.fun) vr
        (fun0 ≻)
    conS (⇒⊑⇒ p q) (suc j) lt = shiftCon (⇒⊑⇒ p q) j lt (λ n₁ r → r)
    conS (∀⊑∀ p) zero lt wl vr g =
      LeafG.valL le {w = w} (∀⊑∀ p) env envR lt (wl CT.↓ CT.all) vr (all0 ≻)
    conS (∀⊑∀ p) (suc j) lt = shiftCon (∀⊑∀ p) j lt (λ n₁ r → r)
    conS (∀⊑ {B = ＇ Y} a z p) zero lt wl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (wl CT.↓ CT.all) vr
        (only0 ≻)
    conS (∀⊑ {B = ＇ Y} a z p) (suc j) lt =
      shiftCon (∀⊑ a z p) j lt (λ n₁ r → r)
    conS (∀⊑ {B = ‵ ι} a z p) zero lt wl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (wl CT.↓ CT.all) vr
        (only0 ≻)
    conS (∀⊑ {B = ‵ ι} a z p) (suc j) lt =
      shiftCon (∀⊑ a z p) j lt (λ n₁ r → r)
    conS (∀⊑ {B = B₁ ⇒ B₂} a z p) zero lt wl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (wl CT.↓ CT.all) vr
        (only0 ≻)
    conS (∀⊑ {B = B₁ ⇒ B₂} a z p) (suc j) lt =
      shiftCon (∀⊑ a z p) j lt (λ n₁ r → r)
    conS (∀⊑ {B = `∀ B₁} a z p) zero lt wl vr g =
      LeafG.valL le {w = w} (∀⊑ a z p) env envR lt (wl CT.↓ CT.all) vr
        (only0 ≻)
    conS (∀⊑ {B = `∀ B₁} a z p) (suc j) lt =
      shiftCon (∀⊑ a z p) j lt (λ n₁ r → r)
    conS bot-elim j lt wl vr ()

    -- the left-only leaf in `≻`
    gRev : ∀ {A B} (p : Φ ⊢ A ⊑ B)
      → Close ≻ w (LG p env envR)
          (λ V → V ↑ 〖 β , R ↑ leftTy (desc p env envR) 〗) (λ V → V)
    gRev p {zero} vl vr r = ℰL-zero ≻ w (LG p env envR)
    gRev p {suc j} {Vl} {Vr} vl vr r =
      revS p j
        (LeafG.belowG le {w = w} p env envR {suc j} {w} {id↪ᵗ} {id↪ᵗ}
          {Vl} {Vr} r)
        vl vr (LeafG.leafInG le {w = w} p env envR {suc j} r)

    gCon : ∀ {A B} (p : Φ ⊢ A ⊑ B)
      → Close ≻ w (LG p env envR)
          (λ V → V ↓ makeConceal β R (leftTy (desc p env envR))) (λ V → V)
    gCon p {zero} wl vr r = ℰL-zero ≻ w (LG p env envR)
    gCon p {suc j} {Wl} {Vr} wl vr r =
      conS p j
        (LeafG.belowG le {w = w} p env envR {suc j} {w} {id↪ᵗ} {id↪ᵗ}
          {Wl} {Vr} r)
        wl vr (LeafG.leafInG le {w = w} p env envR {suc j} r)

------------------------------------------------------------------------
-- The clauses' leaves, in every future
------------------------------------------------------------------------

-- a transported clause leaf is the clause leaf of the renamed
-- descriptor
module _ (d : Dir) {n′ n} (le : n′ ≤′ n) {ΘL ΘR ΘL′ ΘR′}
    (σL : ΘL ↪ᵗ ΘL′) (σR : ΘR ↪ᵗ ΘR′) (c : SDesc ΘL ΘR) where

  leafS-tr : transportLeaf σL σR (sem (leafBelowS d le c))
    ≈ˡ sem (leafBelowS d le (renameSDesc σL σR c))
  leafS-tr =
    sem≈ (λ k w τL τR V V′ → from (leafBelowS-ren d le σL σR c k w τL τR))
      (λ k w τL τR V V′ → to (leafBelowS-ren d le σL σR c k w τL τR))

  onlyS-tr : transportLeaf σL σR (sem (onlyLeafS d le c))
    ≈ˡ sem (onlyLeafS d le (renameSDesc σL σR c))
  onlyS-tr =
    sem≈ (λ k w τL τR V V′ → from (onlyLeafS-ren d le σL σR c k w τL τR))
      (λ k w τL τR V V′ → to (onlyLeafS-ren d le σL σR c k w τL τR))

------------------------------------------------------------------------
-- A descriptor's store types: its right types' store preimages, or ★
------------------------------------------------------------------------

-- the preimage of a scope variable, or of a scope type, if any
unV : ∀ {Θ Δ} → Θ ↪ᵗ Δ → TyVar Δ → Maybe (TyVar Θ)
unV empty ()
unV (keep ι) zero = just zero
unV (keep ι) (suc Y) = Maybe.map suc (unV ι Y)
unV (skip ι) zero = nothing
unV (skip ι) (suc Y) = unV ι Y

_⇒ᴹ_ : ∀ {Θ} → Maybe (Ty Θ) → Maybe (Ty Θ) → Maybe (Ty Θ)
just A ⇒ᴹ just B = just (A ⇒ B)
just A ⇒ᴹ nothing = nothing
nothing ⇒ᴹ M = nothing

unT : ∀ {Θ Δ} → Θ ↪ᵗ Δ → Ty Δ → Maybe (Ty Θ)
unT ι (＇ Y) = Maybe.map ＇_ (unV ι Y)
unT ι (‵ b) = just (‵ b)
unT ι ★ = just ★
unT ι (A ⇒ B) = unT ι A ⇒ᴹ unT ι B
unT ι (`∀ A) = Maybe.map `∀ (unT (keep ι) A)

orStar : ∀ {Θ} → Maybe (Ty Θ) → Ty Θ
orStar (just T) = T
orStar nothing = ★

unV-ι : ∀ {Θ Δ} (ι : Θ ↪ᵗ Δ) X → unV ι (toRenameᵗ ι X) ≡ just X
unV-ι empty ()
unV-ι (keep ι) zero = refl
unV-ι (keep ι) (suc X) = cong (Maybe.map suc) (unV-ι ι X)
unV-ι (skip ι) X = unV-ι ι X

unT-ι : ∀ {Θ Δ} (ι : Θ ↪ᵗ Δ) T → unT ι (renameᵗ (toRenameᵗ ι) T) ≡ just T
unT-ι ι (＇ X) = cong (Maybe.map ＇_) (unV-ι ι X)
unT-ι ι (‵ b) = refl
unT-ι ι ★ = refl
unT-ι ι (A ⇒ B) rewrite unT-ι ι A | unT-ι ι B = refl
unT-ι ι (`∀ A) =
  cong (Maybe.map `∀)
    (trans (cong (unT (keep ι)) (renameᵗ-cong A ke)) (unT-ι (keep ι) A))
  where
  ke : ∀ X → extᵗ (toRenameᵗ ι) X ≡ toRenameᵗ (keep ι) X
  ke zero = refl
  ke (suc X) = refl

-- the preimage commutes with renamings that commute with the
-- variables' preimages
unT-ren : ∀ {Θ Δ Θ₂ Δ₂} (ι : Θ ↪ᵗ Δ) (ι₂ : Θ₂ ↪ᵗ Δ₂) (θ : Δ ⇒ʳ Δ₂)
    (θ₀ : Θ ⇒ʳ Θ₂)
  → (∀ y → unV ι₂ (θ y) ≡ Maybe.map θ₀ (unV ι y))
  → ∀ U → unT ι₂ (renameᵗ θ U) ≡ Maybe.map (renameᵗ θ₀) (unT ι U)
unT-ren ι ι₂ θ θ₀ H (＇ y) =
  trans (cong (Maybe.map ＇_) (H y)) (mv (unV ι y))
  where
  mv : ∀ m → Maybe.map ＇_ (Maybe.map θ₀ m)
    ≡ Maybe.map (renameᵗ θ₀) (Maybe.map ＇_ m)
  mv (just x) = refl
  mv nothing = refl
unT-ren ι ι₂ θ θ₀ H (‵ b) = refl
unT-ren ι ι₂ θ θ₀ H ★ = refl
unT-ren ι ι₂ θ θ₀ H (A ⇒ B) =
  trans (cong₂ _⇒ᴹ_ (unT-ren ι ι₂ θ θ₀ H A) (unT-ren ι ι₂ θ θ₀ H B))
    (mf (unT ι A) (unT ι B))
  where
  mf : ∀ a b → Maybe.map (renameᵗ θ₀) a ⇒ᴹ Maybe.map (renameᵗ θ₀) b
    ≡ Maybe.map (renameᵗ θ₀) (a ⇒ᴹ b)
  mf (just a) (just b) = refl
  mf (just a) nothing = refl
  mf nothing b = refl
unT-ren ι ι₂ θ θ₀ H (`∀ A) =
  trans
    (cong (Maybe.map `∀)
      (unT-ren (keep ι) (keep ι₂) (extᵗ θ) (extᵗ θ₀) H′ A))
    (ma (unT (keep ι) A))
  where
  ms : ∀ m → Maybe.map suc (Maybe.map θ₀ m)
    ≡ Maybe.map (extᵗ θ₀) (Maybe.map suc m)
  ms (just x) = refl
  ms nothing = refl
  H′ : ∀ y → unV (keep ι₂) (extᵗ θ y) ≡ Maybe.map (extᵗ θ₀) (unV (keep ι) y)
  H′ zero = refl
  H′ (suc y) = trans (cong (Maybe.map suc) (H y)) (ms (unV ι y))
  ma : ∀ m → Maybe.map `∀ (Maybe.map (renameᵗ (extᵗ θ₀)) m)
    ≡ Maybe.map (renameᵗ θ₀) (Maybe.map `∀ m)
  ma (just a) = refl
  ma nothing = refl

orStar-⇑ : ∀ {Θ} (m : Maybe (Ty Θ))
  → ⇑ᵗ (orStar m) ≡ orStar (Maybe.map ⇑ᵗ m)
orStar-⇑ (just T) = refl
orStar-⇑ nothing = refl

just-inj : ∀ {Θ} {T T′ : Ty Θ} → just T ≡ just T′ → T ≡ T′
just-inj refl = refl

-- the store types read off a scope substitution are the preimage of
-- every type whose image has one
unT-subst : ∀ {Θ Δ Δ′} (ι : Θ ↪ᵗ Δ) (δ : Δ′ ⇒ˢ Δ) B {T₀}
  → unT ι (substᵗ δ B) ≡ just T₀
  → substᵗ (λ Y → orStar (unT ι (δ Y))) B ≡ T₀
unT-subst ι δ (＇ Y) eq = cong orStar eq
unT-subst ι δ (‵ b) eq = just-inj eq
unT-subst ι δ ★ eq = just-inj eq
unT-subst ι δ (A ⇒ B) eq
    with unT ι (substᵗ δ A) in eA | unT ι (substᵗ δ B) in eB
unT-subst ι δ (A ⇒ B) eq | just a | just b =
  trans (cong₂ _⇒_ (unT-subst ι δ A eA) (unT-subst ι δ B eB)) (just-inj eq)
unT-subst ι δ (A ⇒ B) () | just a | nothing
unT-subst ι δ (A ⇒ B) () | nothing | mb
unT-subst ι δ (`∀ A) eq with unT (keep ι) (substᵗ (extsᵗ δ) A) in eA
unT-subst ι δ (`∀ A) eq | just a =
  trans
    (cong `∀ (trans (substᵗ-cong A pw) (unT-subst (keep ι) (extsᵗ δ) A eA)))
    (just-inj eq)
  where
  pw : ∀ Z → extsᵗ (λ Y → orStar (unT ι (δ Y))) Z
    ≡ orStar (unT (keep ι) (extsᵗ δ Z))
  pw zero = refl
  pw (suc Y) =
    trans (orStar-⇑ (unT ι (δ Y)))
      (cong orStar (sym (unT-ren ι (keep ι) suc suc (λ y → refl) (δ Y))))
unT-subst ι δ (`∀ A) () | nothing

-- a descriptor's store types, in the world w
σᵘ : (w : World) → ∀ {Δ′} → Vec (Ty (ΔR w)) Δ′ → Δ′ ⇒ˢ storeR w
σᵘ w envR Y = orStar (unT (ιʷ w) (lookup envR Y))

-- the store preimage of a right type, read off the descriptor
preᵘ : ∀ {w Δ′} (envR : Vec (Ty (ΔR w)) Δ′) B {T₀}
  → substᵗ (lookup envR) B ≡ ιT w T₀ → PreB w (lookup envR) (σᵘ w envR) B
pre≡ (preᵘ {w} envR B {T₀} eq) =
  trans eq
    (cong (ιT w)
      (sym (unT-subst (ιʷ w) (lookup envR) B
        (trans (cong (unT (ιʷ w)) eq) (unT-ι (ιʷ w) T₀)))))

-- the store type of a scope variable is ★ or a store variable
var★ : ∀ {Θ Δ} (ι : Θ ↪ᵗ Δ) Y
  → orStar (unT ι (＇ Y)) ≡ ★
    ⊎ Σ[ γ ∈ TyVar Θ ] orStar (unT ι (＇ Y)) ≡ ＇ γ
var★ ι Y with unV ι Y
var★ ι Y | just γ = inj₂ (γ , refl)
var★ ι Y | nothing = inj₁ refl

PreB-map : ∀ {Δ′} {w : World} {ρ ρ′ : Δ′ ⇒ˢ ΔR w} {σ B}
  → (∀ Y → ρ′ Y ≡ ρ Y) → PreB w ρ σ B → PreB w ρ′ σ B
pre≡ (PreB-map {B = B} eqs h) = trans (substᵗ-cong B eqs) (pre≡ h)

-- the renamed descriptor's entries are fresh for new store variables
module _ {w w′ : World} (e : w′ ⊒ w) where

  sealNe-new : ∀ {β} → NewL e β → (en : Entry (ΔL w) (ΔR w))
    → SealNe β (renameEntry (ρL e) (ρR e) en)
  sealNe-new nb (seals X Xs Ys c) = nb X

  -- a store variable, renamed, is fresh for a new store variable
  rfresh-new : ∀ {β′} → (∀ Y → toRenameᵗ (ρS e) Y ≢ β′) → ∀ {T₀}
    → Σ[ γ ∈ TyVar (storeR w) ] T₀ ≡ ＇ γ
    → RFresh β′ (renameᵗ (toRenameᵗ (ρS e)) T₀)
  rfresh-new nb (γ , refl) = toRenameᵗ (ρS e) γ , refl , nb γ

  rfresh★-new : ∀ {β′} → (∀ Y → toRenameᵗ (ρS e) Y ≢ β′) → ∀ {T₀}
    → T₀ ≡ ★ ⊎ Σ[ γ ∈ TyVar (storeR w) ] T₀ ≡ ＇ γ
    → RFresh★ β′ (renameᵗ (toRenameᵗ (ρS e)) T₀)
  rfresh★-new nb (inj₁ refl) = inj₁ refl
  rfresh★-new nb (inj₂ v) = inj₂ (rfresh-new nb v)

  -- a store preimage of the right type, in the future
  rep-new : ∀ (Ys : List (TyVar (ΔR w))) (c : Desc (ΔL w) (ΔR w)) {T₀}
    → repR Ys c ≡ ιT w T₀
    → repR (map (renameVar (ρR e)) Ys) (renameDesc (ρL e) (ρR e) c)
      ≡ ιT w′ (renameᵗ (toRenameᵗ (ρS e)) T₀)
  rep-new Ys c {T₀} eq =
    trans (repR-rename (ρL e) (ρR e) Ys c)
      (trans (cong (renameᵗ (toRenameᵗ (ρR e))) eq) (coh-ty e T₀))

  module _ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B)
      (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′)
      where

    env′ : Vec (Entry (ΔL w′) (ΔR w′)) Δ
    env′ = renameEntries (ρL e) (ρR e) env

    envR′ : Vec (Ty (ΔR w′)) Δ′
    envR′ = Vec.map (renameᵗ (toRenameᵗ (ρR e))) envR

    -- the descriptor's store types, in the future
    σ′ : Δ′ ⇒ˢ storeR w′
    σ′ = σᵘ w envR ↑ˢ e

    entL-new : ∀ {β} → NewL e β → ∀ Z → SealNe β (lookup env′ Z)
    entL-new nb Z =
      subst (SealNe _) (sym (lookup-renameEntries (ρL e) (ρR e) env Z))
        (sealNe-new nb (lookup env Z))

    -- the store preimage of the right type, in the future
    pre-new : ∀ {T₀} → rightTy (desc p env envR) ≡ ιT w T₀
      → PreB w′ (lookup envR′) σ′ B
    pre-new eq =
      PreB-map (λ Y → lookup-map Y (renameᵗ (toRenameᵗ (ρR e))) envR)
        (PreB-↑ (preᵘ envR B eq) e)

    -- the descriptor's store types are ★ or store variables
    σ-var : WFDesc (desc p env envR) → ∀ Y′
      → σᵘ w envR Y′ ≡ ★ ⊎ Σ[ γ ∈ TyVar (storeR w) ] σᵘ w envR Y′ ≡ ＇ γ
    σ-var wf Y′ with partner Φ Y′
    σ-var wf Y′ | Z , z with rsealed-var (wf z)
    σ-var wf Y′ | Z , z | Y , eqY =
      subst (λ T → orStar (unT (ιʷ w) T) ≡ ★
               ⊎ Σ[ γ ∈ TyVar (storeR w) ] orStar (unT (ιʷ w) T) ≡ ＇ γ)
        (sym eqY) (var★ (ιʷ w) Y)

    entR-new : ∀ {β′} → (∀ Y → toRenameᵗ (ρS e) Y ≢ β′)
      → WFDesc (desc p env envR) → ∀ Y′ → RFresh★ β′ (σ′ Y′)
    entR-new nb wf Y′ = rfresh★-new nb (σ-var wf Y′)

    rcOk-new : ∀ (rc : RConv (storeR w′)) → NewRC e rc
      → WFDesc (desc p env envR) → RCOk σ′ rc
    rcOk-new nothing nrc wf = rc-none
    rcOk-new (just (β′ , R′)) nrc wf = rc-just (entR-new nrc wf)

  headL-new : ∀ {β} → NewL e β → (Xs : List (TyVar (ΔL w)))
    → HeadNe β (map (renameVar (ρL e)) Xs)
  headL-new nb [] = tt
  headL-new nb (X ∷ Xs) = nb X

  headR-new : ∀ (rc : RConv (storeR w′)) → NewRC e rc
    → (Ys : List (TyVar (ΔR w))) {c : Desc (ΔL w) (ΔR w)} (T₀ : Ty (storeR w))
    → repR Ys c ≡ ιT w T₀
    → HeadNeR rc (map (renameVar (ρR e)) Ys) (renameᵗ (toRenameᵗ (ρS e)) T₀)
  headR-new nothing nrc Ys T₀ eq = tt
  headR-new (just c) nrc [] T₀ eq = tt
  headR-new (just c) nrc (Y ∷ Ys) T₀ eq =
    rfresh-new nrc (var-pre (ιʷ w) T₀ eq)

module Fresh (d : Dir) {n′ n} (le : n′ ≤′ n)
    (orc : ∀ {k} → suc k ≤ n′ → Oracle d k)
    (orcR : ∀ {k} → suc k ≤ n′ → OracleR d k) where

  -- closure under both sides' conversions, at each store preimage of the
  -- right type
  freshP : ∀ {w} (c : SDesc (ΔL w) (ΔR w)) → WFS c
    → PreTy (ιʷ w) (rightTyS c) λ T₀
    → FreshP d both w (sem (leafBelowS d le c)) (leftTyS c) T₀
  freshP {w} (sdesc Xs Ys (desc p env envR)) wf T₀ eq {w′} e
      {β} {R} rc ok nb nrc rs {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym tr)
        (ℰL-≡ d k w′ (LS Xs′ Ys′)
          (cong (λ T → Vl ↑ 〖 β , R ↑ T 〗) (repL-rename ρL₁ ρR₁ Xs c₀))
          refl
          (revPS orc orcR R Xs′ Ys′ eq′ ff vl vr
            (leafRel-resp d k w′ tr r)))) ,
    (λ {Wl} {Wr} wl wr r →
      ℰL-resp d k w′ (≈ˡ-sym tr)
        (ℰL-≡ d k w′ (LS Xs′ Ys′)
          (cong (λ T → Wl ↓ makeConceal β R T) (repL-rename ρL₁ ρR₁ Xs c₀))
          refl
          (conPS orc orcR R Xs′ Ys′ eq′ ff wl wr
            (leafRel-resp d k w′ tr r))))
    where
    ρL₁ = ρL e
    ρR₁ = ρR e
    c₀ = desc p env envR
    Xs′ = map (renameVar ρL₁) Xs
    Ys′ = map (renameVar ρR₁) Ys
    tr = leafS-tr d le ρL₁ ρR₁ (sdesc Xs Ys c₀)
    eq′ = rep-new e Ys c₀ eq
    open SealedNow d le {w = w′} p (env′ e p env envR) (envR′ e p env envR)
      {σ = σ′ e p env envR}
    pf : ∀ Ys₁ → repR Ys₁ c₀ ≡ ιT w T₀ → PreIf (map (renameVar ρR₁) Ys₁)
    pf [] eq₁ = pre-new e p env envR eq₁
    pf (Y ∷ Ys₁) eq₁ = tt
    ff : FreshFor β rc Xs′ Ys′ (renameᵗ (toRenameᵗ (ρS e)) T₀)
    headL ff = headL-new e nb Xs
    headR ff = headR-new e rc nrc Ys T₀ eq
    entL ff = entL-new e p env envR nb
    entR ff = rcOk-new e p env envR rc nrc wf
    entΣ ff = rs
    preF ff = pf Ys eq

  -- closure under the right side's conversions
  freshR : ∀ {w} (c : SDesc (ΔL w) (ΔR w)) → WFS c
    → PreTy (ιʷ w) (rightTyS c) λ T₀
    → FreshR d w (sem (leafBelowS d le c)) T₀
  freshR {w} (sdesc Xs Ys (desc p env envR)) wf T₀ eq {w′} e
      {β′} {R′} nb bs {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym tr)
        (rev Ys T₀ eq vl vr (leafRel-resp d k w′ tr r))) ,
    (λ {Vl} {Wr} vl wr r →
      ℰL-resp d k w′ (≈ˡ-sym tr)
        (con Ys T₀ eq vl wr (leafRel-resp d k w′ tr r)))
    where
    ρL₁ = ρL e
    ρR₁ = ρR e
    c₀ = desc p env envR
    Xs′ = map (renameVar ρL₁) Xs
    tr = leafS-tr d le ρL₁ ρR₁ (sdesc Xs Ys c₀)
    open SealedNow d le {w = w′} p (env′ e p env envR) (envR′ e p env envR)
      {σ = σ′ e p env envR}
    f = entR-new e p env envR nb wf

    rev : ∀ Ys₁ T₁ → repR Ys₁ c₀ ≡ ιT w T₁
      → Close d w′ (LS Xs′ (map (renameVar ρR₁) Ys₁)) (λ V → V)
          (λ V → V ↑ 〖 β′ , R′ ↑ renameᵗ (toRenameᵗ (ρS e)) T₁ 〗)
    rev [] T₁ eq₁ =
      revRS orcR R′ (pre-new e p env envR eq₁) f bs
        (rep-new e [] c₀ eq₁) Xs′
    rev (Y ∷ Ys₁) T₁ eq₁ with var-pre (ιʷ w) T₁ eq₁
    rev (Y ∷ Ys₁) _ eq₁ | γ , refl =
      idR-rev d (gLS Xs′ (map (renameVar ρR₁) (Y ∷ Ys₁))) R′ (nb γ)
        (close-id d (gLS Xs′ (map (renameVar ρR₁) (Y ∷ Ys₁))))

    con : ∀ Ys₁ T₁ → repR Ys₁ c₀ ≡ ιT w T₁
      → Close d w′ (LS Xs′ (map (renameVar ρR₁) Ys₁)) (λ V → V)
          (λ V → V ↓ makeConceal β′ R′ (renameᵗ (toRenameᵗ (ρS e)) T₁))
    con [] T₁ eq₁ =
      conRS orcR R′ (pre-new e p env envR eq₁) f bs
        (rep-new e [] c₀ eq₁) Xs′
    con (Y ∷ Ys₁) T₁ eq₁ with var-pre (ιʷ w) T₁ eq₁
    con (Y ∷ Ys₁) _ eq₁ | γ , refl =
      idR-con d (gLS Xs′ (map (renameVar ρR₁) (Y ∷ Ys₁))) R′ (nb γ)
        (close-id d (gLS Xs′ (map (renameVar ρR₁) (Y ∷ Ys₁))))

-- closure of the left-only leaf; the right does not move, so its store
-- types are never read
module FreshO′ {n′ n} (le : n′ ≤′ n) where

  freshO : ∀ d → (∀ {k} → suc k ≤ n′ → Oracle d k) → ∀ {w}
    (c : SDesc (ΔL w) (ΔR w))
    → FreshO d w (sem (onlyLeafS d le c)) (leftTyS c)
  freshO d orc {w} (sdesc Xs Ys (desc p env envR)) {w′} e {β} {R} nb {k} =
    (λ {Vl} {Vr} vl vr r →
      ℰL-resp d k w′ (≈ˡ-sym tr)
        (ℰL-≡ d k w′ (OL d Xs)
          (cong (λ T → Vl ↑ 〖 β , R ↑ T 〗) (repL-rename ρL₁ ρR₁ Xs c₀))
          refl
          (rev d orc Xs vl vr (leafRel-resp d k w′ tr r)))) ,
    (λ {Wl} {Vr} wl vr r →
      ℰL-resp d k w′ (≈ˡ-sym tr)
        (ℰL-≡ d k w′ (OL d Xs)
          (cong (λ T → Wl ↓ makeConceal β R T) (repL-rename ρL₁ ρR₁ Xs c₀))
          refl
          (con d orc Xs wl vr (leafRel-resp d k w′ tr r))))
    where
    ρL₁ = ρL e
    ρR₁ = ρR e
    c₀ = desc p env envR
    c₁ = renameDesc ρL₁ ρR₁ c₀
    Ys′ = map (renameVar ρR₁) Ys
    tr = onlyS-tr d le ρL₁ ρR₁ (sdesc Xs Ys c₀)
    nβ = entL-new e p env envR nb
    env₁ = env′ e p env envR
    envR₁ = envR′ e p env envR
    module LC = LeafCore ≺ le {w = w′} p env₁ envR₁

    OL : Dir → List (TyVar (ΔL w)) → Leaf (ΔL w′) (ΔR w′)
    OL d₀ Xs₀ = sem (onlyLeafS d₀ le (sdesc (map (renameVar ρL₁) Xs₀) Ys′ c₁))

    gOL : ∀ d₀ Xs₀ → GoodLeaf (OL d₀ Xs₀)
    gOL d₀ Xs₀ = onlyLeafS-good d₀ le (sdesc (map (renameVar ρL₁) Xs₀) Ys′ c₁)

    rev : ∀ d₀ → (∀ {k} → suc k ≤ n′ → Oracle d₀ k) → ∀ Xs₀
      → Close d₀ w′ (OL d₀ Xs₀)
          (λ V → V ↑ 〖 β , R ↑ repL (map (renameVar ρL₁) Xs₀) c₁ 〗)
          (λ V → V)
    rev d₀ orc₀ (X ∷ Xs₀) =
      idL-rev d₀ (gOL d₀ (X ∷ Xs₀)) R (nb X)
        (close-id d₀ (gOL d₀ (X ∷ Xs₀)))
    rev ≺ orc₀ [] = LC.closeRev {σ = σ★} orc₀ nβ R (λ ()) rc-none tt
      refl
    rev ≻ orc₀ [] = GClose.gRev le {w = w′} orc₀ R env₁ envR₁ nβ p

    con : ∀ d₀ → (∀ {k} → suc k ≤ n′ → Oracle d₀ k) → ∀ Xs₀
      → Close d₀ w′ (OL d₀ Xs₀)
          (λ V → V ↓ makeConceal β R (repL (map (renameVar ρL₁) Xs₀) c₁))
          (λ V → V)
    con d₀ orc₀ (X ∷ Xs₀) =
      idL-con d₀ (gOL d₀ (X ∷ Xs₀)) R (nb X)
        (close-id d₀ (gOL d₀ (X ∷ Xs₀)))
    con ≺ orc₀ [] = LC.closeCon {σ = σ★} orc₀ nβ R (λ ()) rc-none tt
      refl
    con ≻ orc₀ [] = GClose.gCon le {w = w′} orc₀ R env₁ envR₁ nβ p

------------------------------------------------------------------------
-- The oracle, by induction on the bound
------------------------------------------------------------------------

private
  Both : Dir → ℕ → Set
  Both d N = Oracle d N × OracleR d N

  both-down : ∀ {d N N′} → N′ ≤ N → Both d N → Both d N′
  both-down le (o , oR) = Oracle-down le o , OracleR-down le oR

  -- the bound N, from every bound below it
  stepO : ∀ d N → (∀ {k} → k < N → Both d k) → Both d N
  stepO d N ih =
    (  (λ le b c wf → Fresh.freshP d le (orc b) (orcR b) c wf)
     , (λ le b c → FreshO′.freshO le d (orc b) c))
    , (λ le b c wf → Fresh.freshR d le (orc b) (orcR b) c wf)
    where
    orc : ∀ {n′} → n′ ≤ N → ∀ {k} → suc k ≤ n′ → Oracle d k
    orc b lt = proj₁ (ih (≤-trans lt b))
    orcR : ∀ {n′} → n′ ≤ N → ∀ {k} → suc k ≤ n′ → OracleR d k
    orcR b lt = proj₂ (ih (≤-trans lt b))

  below : ∀ d N {k} → k < N → Both d k
  below d (suc N) (s≤s k≤N) = both-down k≤N (stepO d N (below d N))

-- the clauses' leaves are closed at every bound
oracle-all : ∀ d N → Oracle d N
oracle-all d N = proj₁ (stepO d N (below d N))

oracleR-all : ∀ d N → OracleR d N
oracleR-all d N = proj₂ (stepO d N (below d N))

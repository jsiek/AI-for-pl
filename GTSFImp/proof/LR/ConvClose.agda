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
--   * Induction on the bound ties the oracle together: a clause leaf at
--     stage k is closed by the lemmas at bound k, whose oracle covers
--     the stages below k.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl; ≤′-step; _≤?_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  ≤-<-trans; <⇒≤)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; lookup)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import proof.DGG.CenterRename using (_∘↪_)
open import Conversion
open import CastTerms using (Term; _↑_; _↓_; Value)
import CastTerms as CT
open import Reduction using (_—→_; id-reveal; id-conceal)
open import LR.Frame using (conceal)
open import proof.TypeInTermSubst using (toRename-id-eq)
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
  con★★; noRF; allDeadStar-map; module OnlyV; module DeadV)
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

-- a paired entry is sealed on the right, at its right type, not by β′
data RFresh {ΘL ΘR} (β′ : TyVar ΘR) : Entry ΘL ΘR → Ty ΘR → Set where
  rfresh : ∀ {X Xs Y Ys c} → Y ≢ β′
    → RFresh β′ (seals X Xs (Y ∷ Ys) c) (＇ Y)

-- what the right side's conversion needs of the descriptor
data RCOk {Δ Δ′ ΘL ΘR} (Φ : Corr Δ Δ′) (env : Vec (Entry ΘL ΘR) Δ)
    (envR : Vec (Ty ΘR) Δ′) : RConv ΘR → Set where
  rc-none : RCOk Φ env envR nothing
  rc-just : ∀ {β′ R′}
    → (∀ {Z Y′} → Φ ∋ Z ↔ Y′ → RFresh β′ (lookup env Z) (lookup envR Y′))
    → RCOk Φ env envR (just (β′ , R′))

module _ {Δ Δ′ ΘL ΘR} {Φ : Corr Δ Δ′} {env : Vec (Entry ΘL ΘR) Δ}
    {envR : Vec (Ty ΘR) Δ′} where

  rkOf : ∀ {rc} → RCOk Φ env envR rc → RK
  rkOf rc-none = left
  rkOf (rc-just f) = both

  allowedOf : ∀ {rc} (ok : RCOk Φ env envR rc) → Allowed (rkOf ok) rc
  allowedOf rc-none = tt
  allowedOf (rc-just f) = tt

tyL-entry : ∀ {β : TyVar ΘL} R (e : Entry ΘL ΘR) → SealNe β e
  → replaceTy β R (entryTy e) ≡ entryTy e
tyL-entry R (seals X Xs Ys c) ne = replaceTy-other R ne

tyR-entry : ∀ {β′ : TyVar ΘR} R′ {e : Entry ΘL ΘR} {T′} → RFresh β′ e T′
  → replaceTy β′ R′ T′ ≡ T′
tyR-entry R′ (rfresh ne) = replaceTy-other R′ ne

module _ {d : Dir} {w : World} where

  entryConvPN : ∀ {N β} R (e : Entry (ΔL w) (ΔR w)) {T′} → SealNe β e
    → ConvLeafP d N w R nothing β (syn e) (syn e) (entryTy e) T′
  entryConvPN R (seals X Xs Ys c) {T′} ne =
    storeConvPN good-syn {T′ = T′} R ne

  entryConvPJ : ∀ {N β} R {e : Entry (ΔL w) (ΔR w)} {T′ β′ R′}
    → SealNe β e → RFresh β′ e T′
    → ConvLeafP d N w R (just (β′ , R′)) β (syn e) (syn e) (entryTy e) T′
  entryConvPJ R ne (rfresh ne′) = storeConvP good-syn R (just _) ne ne′

  entryConvO : ∀ {N β} R (e : Entry (ΔL w) (ΔR w)) → SealNe β e
    → ConvLeafO d N w R β (syn e) (syn e) (entryTy e)
  entryConvO R (seals X Xs Ys c) ne = storeConvO good-syn R ne

  entryFreshPL : ∀ (e : Entry (ΔL w) (ΔR w)) {T′}
    → FreshP d left w (syn e) (entryTy e) T′
  entryFreshPL (seals X Xs Ys c) = storeFreshPL {N = zero} good-syn

  entryFreshPJ : ∀ {e : Entry (ΔL w) (ΔR w)} {T′ β′} → RFresh β′ e T′
    → FreshP d both w (syn e) (entryTy e) T′
  entryFreshPJ (rfresh ne) = storeFreshP {N = zero} good-syn {rk = both}

  entryFreshO : ∀ (e : Entry (ΔL w) (ΔR w))
    → FreshO d w (syn e) (entryTy e)
  entryFreshO (seals X Xs Ys c) = storeFreshO good-syn

  entryConvR : ∀ {N β′} R′ {e : Entry (ΔL w) (ΔR w)} {T′} → RFresh β′ e T′
    → ConvLeafR d N w β′ R′ (syn e) (syn e) T′
  entryConvR R′ (rfresh ne) = storeConvR good-syn R′ ne

  entryFreshR : ∀ {e : Entry (ΔL w) (ΔR w)} {T′ β′} → RFresh β′ e T′
    → FreshR d w (syn e) T′
  entryFreshR (rfresh ne) = storeFreshR {N = zero} good-syn

------------------------------------------------------------------------
-- The lemmas at a descriptor's own interpretation
------------------------------------------------------------------------

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

  tyB : substᵗ (δr δ′) (renameᵗ (λ Y → Y) B) ≡ substᵗ (δr δ) B
  tyB = substᵗ-rename (δr δ′) (λ Y → Y) B

  -- the hypotheses that depend on the right side's conversion
  tyR-ok : ∀ {rc} (ok : RCOk Φ env envR rc) Y′
    → replaceRC rc (lookup envR Y′) ≡ lookup envR Y′
  tyR-ok rc-none Y′ = refl
  tyR-ok (rc-just {R′ = R′} f) Y′ with partner Φ Y′
  tyR-ok (rc-just {R′ = R′} f) Y′ | Z , z = tyR-entry R′ (f z)

  convP-ok : ∀ {N β} R {rc} (ok : RCOk Φ env envR rc)
    → (∀ Z → SealNe β (lookup env Z))
    → ∀ {Z Y′} → Φ ∋ Z ↔ Y′
    → ConvLeafP d N w R rc β (syn (lookup env Z)) (syn (lookup env Z))
        (entryTy (lookup env Z)) (lookup envR Y′)
  convP-ok R rc-none nβ {Z} {Y′} z =
    entryConvPN R (lookup env Z) {T′ = lookup envR Y′} (nβ Z)
  convP-ok R (rc-just f) nβ {Z} z = entryConvPJ R (nβ Z) (f z)

  genP-ok : ∀ {rc} (ok : RCOk Φ env envR rc) {Z Y′} → Φ ∋ Z ↔ Y′
    → FreshP d (rkOf ok) w (syn (lookup env Z)) (entryTy (lookup env Z))
        (lookup envR Y′)
  genP-ok rc-none {Z} z = entryFreshPL (lookup env Z)
  genP-ok (rc-just f) z = entryFreshPJ (f z)

  -- the main lemma, with no converted variable
  module _ {N} (orc : Oracle d N) {β : TyVar (ΔL w)}
      (nβ : ∀ Z → SealNe β (lookup env Z)) (R : Ty (ΔL w))
      {rc : RConv (ΔR w)} (ok : RCOk Φ env envR rc) where

    hyp : ConvI d N (rkOf ok) w (m-none {Φ = dead Φ} {X = zero} R rc) β
      δ′ δ′
    goodS hyp = goodδ′
    goodT hyp = goodδ′
    selfI hyp = tt
    rcOK hyp = allowedOf ok
    tyL hyp zero = refl
    tyL hyp (suc Z) = tyL-entry R (lookup env Z) (nβ Z)
    tyR hyp = tyR-ok ok
    leafO hyp Z tt = ≈ˡ-refl
    convP hyp (↔-dead z) tt = convP-ok R ok nβ z
    convO hyp (only-dead {X = Z} z) tt = entryConvO R (lookup env Z) (nβ Z)
    genP hyp (↔-dead z) = genP-ok ok z
    genO hyp (only-dead {X = Z} z) = entryFreshO (lookup env Z)
    genPS hyp (↔-dead z) = genP-ok ok z
    genOS hyp (only-dead {X = Z} z) = entryFreshO (lookup env Z)
    sealI hyp = tt
    oracle hyp = orc

    coreRev : ∀ {k} → k ≤ N → ∀ {Vl Vr} → Value Vl → Value Vr
      → 𝒱 d k p w δ Vl Vr
      → ℰ d k p w δ (Vl ↑ 〖 β , R ↑ substᵗ (δl δ) A 〗)
          (revM rc (substᵗ (δr δ) B) Vr)
    coreRev le {Vl} {Vr} vl vr r =
      back
        (ℰᵍ-≡ (cong (λ T → Vl ↑ 〖 β , R ↑ T 〗) tyA)
          (cong (λ T → revM rc T Vr) tyB)
          (revC d p′ hyp le vl vr (inW r)))

    coreCon : ∀ {k} → k ≤ N → ∀ {Wl Wr} → Value Wl → Value Wr
      → 𝒱 d k p w δ Wl Wr
      → ℰ d k p w δ (Wl ↓ makeConceal β R (substᵗ (δl δ) A))
          (conM rc (substᵗ (δr δ) B) Wr)
    coreCon le {Wl} {Wr} wl wr r =
      back
        (ℰᵍ-≡ (cong (λ T → Wl ↓ makeConceal β R T) tyA)
          (cong (λ T → conM rc T Wr) tyB)
          (conC d p′ hyp le wl wr (inW r)))

  -- the right-only lemma, with no converted variable
  module _ {N} (orc : OracleR d N) {β′ : TyVar (ΔR w)} (R′ : Ty (ΔR w))
      (f : ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → RFresh β′ (lookup env Z) (lookup envR Y′))
      where

    hypR : RConvI d N w (r-none {Φ = dead Φ} {X = zero} β′ R′) δ′ δ′
    goodS hypR = goodδ′
    goodT hypR = goodδ′
    selfR hypR = tt
    tyL hypR Z = refl
    tyR hypR Y′ with partner Φ Y′
    tyR hypR Y′ | Z , z = tyR-entry R′ (f z)
    leafO hypR Z tt = ≈ˡ-refl
    convP hypR (↔-dead z) tt = entryConvR R′ (f z)
    genR hypR (↔-dead z) = entryFreshR (f z)
    genRS hypR (↔-dead z) = entryFreshR (f z)
    sealR hypR = tt
    oracleR hypR = orc

    coreRevR : ∀ {k} → k ≤ N → ∀ {Vl Vr} → Value Vl → Value Vr
      → 𝒱 d k p w δ Vl Vr
      → ℰ d k p w δ Vl (Vr ↑ 〖 β′ , R′ ↑ substᵗ (δr δ) B 〗)
    coreRevR le {Vl} {Vr} vl vr r =
      back
        (ℰᵍ-≡ refl (cong (λ T → Vr ↑ 〖 β′ , R′ ↑ T 〗) tyB)
          (revR d p′ hypR le vl vr (inW r)))

    coreConR : ∀ {k} → k ≤ N → ∀ {Vl Wr} → Value Vl → Value Wr
      → 𝒱 d k p w δ Vl Wr
      → ℰ d k p w δ Vl (Wr ↓ makeConceal β′ R′ (substᵗ (δr δ) B))
    coreConR le {Vl} {Wr} vl wr r =
      back
        (ℰᵍ-≡ refl (cong (λ T → Wr ↓ makeConceal β′ R′ T) tyB)
          (conR d p′ hypR le vl wr (inW r)))

------------------------------------------------------------------------
-- Closure of a leaf, at the current world
------------------------------------------------------------------------

-- related values, changed on each side, are related expressions
Close : Dir → (w : World) → Leaf (ΔL w) (ΔR w)
  → (Term (ΔL w) → Term (ΔL w)) → (Term (ΔR w) → Term (ΔR w)) → Set
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

  idR-rev : ∀ {β′ γ′ : TyVar (ΔR w)} R′ → γ′ ≢ β′ → ∀ {fl}
    → Close d w L fl (λ V → V)
    → Close d w L fl (λ V → V ↑ 〖 β′ , R′ ↑ ＇ γ′ 〗)
  idR-rev R′ ne cl {k} vl vr r =
    ℰL-≡ d k w L refl (sym (↑-pk (〖〗-other R′ refl ne)))
      (stepR-ℰL d L (id-reveal vr)
        (λ le → cl vl vr (leafRel-down d le w gl r)))

  idR-con : ∀ {β′ γ′ : TyVar (ΔR w)} R′ → γ′ ≢ β′ → ∀ {fl}
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
  sealedR (toRenameᵗ τR Y) (renameᵗ (toRenameᵗ τR) R) (P k w τL τR)

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
  wrapR Y R {fl} cl {k} {Vl} {Vr} vl vr r with sealedR-inv r
  wrapR Y R {fl} cl {k} {Vl} {_} vl vr r | W , refl , q =
    I.toL d k
      (ℰ-bind₂ d k O.x₁ I.x₁ w {δ₁ = O.δ₁} {δ₂ = I.δ₁}
        nothing (just (conceal (seal Y₀ R₀)))
        (O.fromL d k (cl vl (value-↓ vr) q))
        (λ e₂ {n₂} le₂ {P₁} {P₂} p₁ p₂ q₂ →
          ℰ-value d n₂ I.x₁ _ p₁ (p₂ CT.↓ CT.seal)
            (to (𝒱-XY d n₂ ↔-here _ {δ = I.δ₁ ↑ᴵ e₂})
              (seal-coh (ρR e₂) Y R ,
               from (𝒱-XY d n₂ ↔-here _ {δ = O.δ₁ ↑ᴵ e₂}) q₂))))
    where
    Y₀ = toRenameᵗ id↪ᵗ Y
    R₀ = renameᵗ (toRenameᵗ id↪ᵗ) R
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
        subst (λ T → sealedR (renameVar τR Y) T
                       (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′)
          (repR-rename τL τR Ys c)
          (sealSR→ d le Xs Ys c Y k w τL τR r))
      (λ k w τL τR V V′ r →
        sealSR← d le Xs Ys c Y k w τL τR
          (subst (λ T → sealedR (renameVar τR Y) T
                         (leafBelowS d le (sdesc Xs Ys c) k w τL τR) V V′)
            (sym (repR-rename τL τR Ys c)) r))

-- closure respects equivalent leaves
Close-resp : ∀ d {w} {L L′ : Leaf (ΔL w) (ΔR w)} {fl fr} → L ≈ˡ L′
  → Close d w L fl fr → Close d w L′ fl fr
Close-resp d {w} h cl {k} vl vr r =
  ℰL-resp d k w h (cl vl vr (leafRel-resp d k w (≈ˡ-sym h) r))

------------------------------------------------------------------------
-- A descriptor's relation, as its clause leaf
------------------------------------------------------------------------

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

  -- the main lemma, at the leaf
  module _ (orc : ∀ {k} → suc k ≤ n′ → Oracle d k) {β : TyVar (ΔL w)}
      (nβ : ∀ Z → SealNe β (lookup env Z)) (R : Ty (ΔL w))
      {rc : RConv (ΔR w)} (ok : RCOk Φ env envR rc) where

    open Core d {w = w} p env envR using (coreRev; coreCon)

    closeRev : Close d w L (λ V → V ↑ 〖 β , R ↑ leftTy c₀ 〗)
      (revM rc (rightTy c₀))
    closeRev vl vr r =
      toLeaf (below r)
        (coreRev (orc (below r)) nβ R ok ≤-refl vl vr (leafIn r))

    closeCon : Close d w L (λ V → V ↓ makeConceal β R (leftTy c₀))
      (conM rc (rightTy c₀))
    closeCon vl vr r =
      toLeaf (below r)
        (coreCon (orc (below r)) nβ R ok ≤-refl vl vr (leafIn r))

  -- the right-only lemma, at the leaf
  module _ (orc : ∀ {k} → suc k ≤ n′ → OracleR d k) {β′ : TyVar (ΔR w)}
      (R′ : Ty (ΔR w))
      (f : ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → RFresh β′ (lookup env Z) (lookup envR Y′))
      where

    open Core d {w = w} p env envR using (coreRevR; coreConR)

    closeRevR : Close d w L (λ V → V) (λ V → V ↑ 〖 β′ , R′ ↑ rightTy c₀ 〗)
    closeRevR vl vr r =
      toLeaf (below r)
        (coreRevR (orc (below r)) R′ f ≤-refl vl vr (leafIn r))

    closeConR : Close d w L (λ V → V)
      (λ V → V ↓ makeConceal β′ R′ (rightTy c₀))
    closeConR vl vr r =
      toLeaf (below r)
        (coreConR (orc (below r)) R′ f ≤-refl vl vr (leafIn r))

------------------------------------------------------------------------
-- A sealed descriptor's leaf, at the current world
------------------------------------------------------------------------

-- the outermost seal is not the converted store variable
HeadNe : ∀ {Θ} → TyVar Θ → List (TyVar Θ) → Set
HeadNe β [] = ⊤
HeadNe β (X ∷ Xs) = X ≢ β

HeadNeR : ∀ {Θ} → RConv Θ → List (TyVar Θ) → Set
HeadNeR nothing Ys = ⊤
HeadNeR (just (β′ , R′)) [] = ⊤
HeadNeR (just (β′ , R′)) (Y ∷ Ys) = Y ≢ β′

module SealedNow (d : Dir) {n′ n} (le : n′ ≤′ n) {w : World} {Δ Δ′}
    {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B)
    (env : Vec (Entry (ΔL w) (ΔR w)) Δ) (envR : Vec (Ty (ΔR w)) Δ′) where

  open LeafCore d le {w = w} p env envR
    using (c₀; closeRev; closeCon; closeRevR; closeConR)

  LS : List (TyVar (ΔL w)) → List (TyVar (ΔR w)) → Leaf (ΔL w) (ΔR w)
  LS Xs Ys = sem (leafBelowS d le (sdesc Xs Ys c₀))

  gLS : ∀ Xs Ys → GoodLeaf (LS Xs Ys)
  gLS Xs Ys = leafBelowS-good d le (sdesc Xs Ys c₀)

  -- the right side alone converts, past the left seals
  module _ (orc : ∀ {k} → suc k ≤ n′ → OracleR d k) {β′ : TyVar (ΔR w)}
      (R′ : Ty (ΔR w))
      (f : ∀ {Z Y′} → Φ ∋ Z ↔ Y′ → RFresh β′ (lookup env Z) (lookup envR Y′))
      where

    revRS : ∀ Xs
      → Close d w (LS Xs []) (λ V → V) (λ V → V ↑ 〖 β′ , R′ ↑ rightTy c₀ 〗)
    revRS [] = closeRevR orc R′ f
    revRS (X ∷ Xs) =
      Close-resp d (≈ˡ-sym (leafSL≈ d le Xs [] c₀ X))
        (wrapL d {w = w} (leafBelowS d le (sdesc Xs [] c₀)) X (repL Xs c₀)
          (revRS Xs))

    conRS : ∀ Xs
      → Close d w (LS Xs []) (λ V → V)
          (λ V → V ↓ makeConceal β′ R′ (rightTy c₀))
    conRS [] = closeConR orc R′ f
    conRS (X ∷ Xs) =
      Close-resp d (≈ˡ-sym (leafSL≈ d le Xs [] c₀ X))
        (wrapL d {w = w} (leafBelowS d le (sdesc Xs [] c₀)) X (repL Xs c₀)
          (conRS Xs))

  -- the left side alone converts, past the right seals
  module _ (orc : ∀ {k} → suc k ≤ n′ → Oracle d k) {β : TyVar (ΔL w)}
      (nβ : ∀ Z → SealNe β (lookup env Z)) (R : Ty (ΔL w)) where

    revLS : ∀ Ys
      → Close d w (LS [] Ys) (λ V → V ↑ 〖 β , R ↑ leftTy c₀ 〗) (λ V → V)
    revLS [] = closeRev orc nβ R rc-none
    revLS (Y ∷ Ys) =
      Close-resp d (≈ˡ-sym (leafSR≈ d le [] Ys c₀ Y))
        (wrapR d {w = w} (leafBelowS d le (sdesc [] Ys c₀)) Y (repR Ys c₀)
          (revLS Ys))

    conLS : ∀ Ys
      → Close d w (LS [] Ys) (λ V → V ↓ makeConceal β R (leftTy c₀))
          (λ V → V)
    conLS [] = closeCon orc nβ R rc-none
    conLS (Y ∷ Ys) =
      Close-resp d (≈ˡ-sym (leafSR≈ d le [] Ys c₀ Y))
        (wrapR d {w = w} (leafBelowS d le (sdesc [] Ys c₀)) Y (repR Ys c₀)
          (conLS Ys))

  -- fresh for both sides' conversions
  record FreshFor (β : TyVar (ΔL w)) (rc : RConv (ΔR w))
      (Xs : List (TyVar (ΔL w))) (Ys : List (TyVar (ΔR w))) : Set where
    field
      headL : HeadNe β Xs
      headR : HeadNeR rc Ys
      entL : ∀ Z → SealNe β (lookup env Z)
      entR : RCOk Φ env envR rc

  open FreshFor public

  module _ (orc : ∀ {k} → suc k ≤ n′ → Oracle d k)
      (orcR : ∀ {k} → suc k ≤ n′ → OracleR d k) {β : TyVar (ΔL w)}
      (R : Ty (ΔL w)) where

    -- both sides convert
    revPS : ∀ {rc} Xs Ys → FreshFor β rc Xs Ys
      → Close d w (LS Xs Ys)
          (λ V → V ↑ 〖 β , R ↑ repL Xs c₀ 〗) (revM rc (repR Ys c₀))
    revPS {nothing} (X ∷ Xs) Ys fr =
      idL-rev d (gLS (X ∷ Xs) Ys) R (headL fr) (close-id d (gLS (X ∷ Xs) Ys))
    revPS {just (β′ , R′)} (X ∷ Xs) (Y ∷ Ys) fr =
      idL-rev d (gLS (X ∷ Xs) (Y ∷ Ys)) R (headL fr)
        (idR-rev d (gLS (X ∷ Xs) (Y ∷ Ys)) R′ (headR fr)
          (close-id d (gLS (X ∷ Xs) (Y ∷ Ys))))
    revPS {just (β′ , R′)} (X ∷ Xs) [] fr with entR fr
    revPS {just (β′ , R′)} (X ∷ Xs) [] fr | rc-just f =
      idL-rev d (gLS (X ∷ Xs) []) R (headL fr) (revRS orcR R′ f (X ∷ Xs))
    revPS {nothing} [] Ys fr = revLS orc (entL fr) R Ys
    revPS {just (β′ , R′)} [] (Y ∷ Ys) fr =
      idR-rev d (gLS [] (Y ∷ Ys)) R′ (headR fr)
        (revLS orc (entL fr) R (Y ∷ Ys))
    revPS {just (β′ , R′)} [] [] fr = closeRev orc (entL fr) R (entR fr)

    conPS : ∀ {rc} Xs Ys → FreshFor β rc Xs Ys
      → Close d w (LS Xs Ys)
          (λ V → V ↓ makeConceal β R (repL Xs c₀)) (conM rc (repR Ys c₀))
    conPS {nothing} (X ∷ Xs) Ys fr =
      idL-con d (gLS (X ∷ Xs) Ys) R (headL fr) (close-id d (gLS (X ∷ Xs) Ys))
    conPS {just (β′ , R′)} (X ∷ Xs) (Y ∷ Ys) fr =
      idL-con d (gLS (X ∷ Xs) (Y ∷ Ys)) R (headL fr)
        (idR-con d (gLS (X ∷ Xs) (Y ∷ Ys)) R′ (headR fr)
          (close-id d (gLS (X ∷ Xs) (Y ∷ Ys))))
    conPS {just (β′ , R′)} (X ∷ Xs) [] fr with entR fr
    conPS {just (β′ , R′)} (X ∷ Xs) [] fr | rc-just f =
      idL-con d (gLS (X ∷ Xs) []) R (headL fr) (conRS orcR R′ f (X ∷ Xs))
    conPS {nothing} [] Ys fr = conLS orc (entL fr) R Ys
    conPS {just (β′ , R′)} [] (Y ∷ Ys) fr =
      idR-con d (gLS [] (Y ∷ Ys)) R′ (headR fr)
        (conLS orc (entL fr) R (Y ∷ Ys))
    conPS {just (β′ , R′)} [] [] fr = closeCon orc (entL fr) R (entR fr)

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
    (nβ : ∀ Z → SealNe β (lookup env Z)) where

  δ′ : Interp (suc Δ) Δ′ (ΔL w) (ΔR w)
  δ′ = extDeadI ★ (envI env envR)

  module _ (h : ConvI ≻ N rk w (m-none {Φ = dead Φ} {X = zero} R nothing) β
      δ′ δ′) where

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
        (funStar-map (λ v f → fun-rev h le vl v f) vr r)
      where
      open FunConv {X = zero} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
        (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
        (λ h′ → rev★ ≻ q h′) (λ h′ → con★ ≻ q h′)
    revG★ (∀⊑ Anv z p) {j} le vl vr r =
      ℰ-value ≻ (suc j) (∀⊑ Anv z p) w (vl CT.↑ CT.all) vr
        (OnlyV.revV ≻ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
          (λ σ → refl) (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h le vl vr r)
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
        (funStar-map (λ v f → fun-con h le wl v f) vr r)
      where
      open FunConv {X = zero} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
        (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
        (λ h′ → rev★ ≻ q h′) (λ h′ → con★ ≻ q h′)
    conG★ (∀⊑ Anv z p) {j} le wl vr r =
      ℰ-value ≻ (suc j) (∀⊑ Anv z p) w (wl CT.↓ CT.all) vr
        (OnlyV.conV ≻ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
          (λ σ → refl) (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h le wl vr r)
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

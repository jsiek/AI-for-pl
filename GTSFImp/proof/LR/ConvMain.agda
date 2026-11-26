module proof.LR.ConvMain where

-- File Charter:
--   * The conversion lemma's value-level `∀` cases: the clauses of
--     `allPair`, `allOnly` and `allDead` for converted values, from the
--     per-descriptor cases of `proof.LR.ConvLemma`.
--   * The lemma at `★` (`rev★`, `con★`), where the right is not
--     converted, by induction on the precision derivation.
--   * The main lemma (`revC`, `conC`), where the right converts as the
--     mode says, by induction on the precision derivation; into `★` it
--     is the lemma at `★` followed by the right's identity step.
--   * The guarded clause (`allOnlyG`) is the clause with slack 1 read by
--     `𝒱` (`allOnlyG→Cl`, `Cl→allOnlyG`).  In `≻` at a body into `★`
--     (not a variable) the lemma at stage k + 1 needs the bound k only
--     (`rev★G`, `con★G`): `G` there reads its leaves at stage k.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n; _+_;
  _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans;
  <⇒≤; ≤-pred)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
  renaming (keep to keepᵗ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.TermRename using (renameᵗᵐ-∘)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective;
  renameᵗ-injective)
open import Conversion
open import CastTerms using (Term; _⦂∀_[_]; _⟨_⟩; _↑_; _↓_; Value;
  RevealValue; ConcealValue; renameᵗᵐ)
import CastTerms as CT
open import LR.Precision
open import LR.Desc
open import LR.World
open import LR.Relation
open import proof.LR.WorldProps
open import proof.LR.InterpProps
open import proof.LR.Monotone
open import proof.LR.Expression
open import proof.LR.ConvSyntax
open import proof.LR.ConvBase
open import proof.LR.ConvLemma
open import proof.LR.SubstLemma using (allDeadStar-★; _⇔_; ⇔-id; to;
  from; iff; ℰᵍ-map⁺)
open import Reduction using (id-reveal; id-conceal)

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- The `∀` clauses from their instances at each stage
------------------------------------------------------------------------

allPair-from : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : pair Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → (c : SDesc (ΔL w′) (ΔR w′)) → WFS c
       → PreTy (ιʷ w′) (rightTyS c) λ T₀ →
         PreTy (keepᵗ (ιʷ w′)) (substᵗ (extsᵗ (δr (δ ↑ᴵ e))) B) λ B₀ →
         ℰ d n′ p w′ (extPairI (leftTyS c) (rightTyS c)
             (sem (leafBelowS d (≤′-refl {n′}) c)) (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
             [ leftTyS c ])
           (renameᵗᵐ (ρS e) Vr ⦂∀ B₀ [ T₀ ]))
  → allPair d n p w δ Vl Vr
allPair-from d n p w f e le c wf T₀ eqT B₀ eqB =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le) p w″
        (↑ᴵ-resp (extPairI-resp (leafBelowS-≈ d ≤′-refl le c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d le′ (≤′-trans le′ le) p w″ r))
    (f e (≤′⇒≤ le) c wf T₀ eqT B₀ eqB)

OnlyCl-from : ∀ d g n {Φ : Corr Δ Δ′} {A B} (p : only Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → (c : SDesc (ΔL w′) (ΔR w′))
       → OnlyS c → ℰ d n′ p w′ (extOnlyI (leftTyS c)
             (sem (onlyLeafS d (leafLe g (≤′-refl {n′})) c)) (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
             [ leftTyS c ])
           (renameᵗᵐ (ρS e) Vr))
  → OnlyCl d g n p w δ Vl Vr
OnlyCl-from d g n p w f e le c oc =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le) p w″
        (↑ᴵ-resp (extOnlyI-resp
          (onlyLeafS-≈ d (leafLe g ≤′-refl) (leafLe g le) c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d le′ (≤′-trans le′ le) p w″ r))
    (f e (≤′⇒≤ le) c oc)

allOnly-from : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : only Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → (c : SDesc (ΔL w′) (ΔR w′))
       → OnlyS c → ℰ d n′ p w′ (extOnlyI (leftTyS c)
             (sem (onlyLeafS d (≤′-refl {n′}) c)) (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
             [ leftTyS c ])
           (renameᵗᵐ (ρS e) Vr))
  → allOnly d n p w δ Vl Vr
allOnly-from d n = OnlyCl-from d 0 n

-- the clause with slack, in a future and at a lower stage
OnlyCl-mono : ∀ d g n {Φ : Corr Δ Δ′} {A B} (p : only Φ ⊢ A ⊑ B)
    {w w′} (e : w′ ⊒ w) {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → OnlyCl d g n p w δ Vl Vr
  → OnlyCl d g n p w′ (δ ↑ᴵ e) (renameᵗᵐ (ρL e) Vl) (renameᵗᵐ (ρS e) Vr)
OnlyCl-mono d g n {A = A} p e {δ} {Vl} {Vr} f e′ le c oc =
  ℰᵍ-≡
    (cong₂ (λ M C → M ⦂∀ C [ leftTyS c ])
      (sym (renameᵗᵐ-∘ (ρL e′) (ρL e) Vl))
      (substᵗ-cong A (exts-cong (λ X → sym (δl≡ (↑ᴵ-trans δ e′ e) X)))))
    (sym (renameᵗᵐ-∘ (ρS e′) (ρS e) Vr))
    (ℰᵍ-map d _ _
      (λ le′ w″ e″ V V′ →
        𝒱≤-resp d (≤′-trans le′ le) p w″
          (↑ᴵ-resp (extOnlyI-resp ≈ˡ-refl (≈ᴵ-sym (↑ᴵ-trans δ e′ e))) e″))
      (f (⊒-trans e′ e) le c oc))

OnlyCl-down : ∀ d g {n n′} (le : n′ ≤ n) {Φ : Corr Δ Δ′} {A B}
    (p : only Φ ⊢ A ⊑ B) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → OnlyCl d g n p w δ Vl Vr → OnlyCl d g n′ p w δ Vl Vr
OnlyCl-down d g le p w f e le₁ c oc =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le₁) p w″
        (↑ᴵ-resp (extOnlyI-resp
          (onlyLeafS-≈ d (leafLe g le₂) (leafLe g le₁) c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d (≤′-trans le′ le₂) (≤′-trans le′ le₁) p w″ r))
    (f e le₂ c oc)
  where le₂ = ≤′-trans le₁ (≤⇒≤′ le)

------------------------------------------------------------------------
-- The guarded clause (`allOnlyG`) and the clause with slack 1
------------------------------------------------------------------------

-- at a positive stage, `Gᵇ` is `𝒱` at a body: not a variable, and with
-- a variable occurring in it
Gᵇ⇔𝒱 : ∀ k {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) {X} → X ∈ᵗ A → NonVar A
  → ∀ w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → Gᵇ ≻ (suc k) p w δ Vl Vr ⇔ 𝒱 ≻ (suc k) p w δ Vl Vr
Gᵇ⇔𝒱 k ★⊑★ () nv w
Gᵇ⇔𝒱 k ι⊑★ () nv w
Gᵇ⇔𝒱 k (X⊑★ x) i () w
Gᵇ⇔𝒱 k (⇒⊑★ p q) i nv w = ⇔-id
Gᵇ⇔𝒱 k (∀⊑ a z p) i nv w = ⇔-id
Gᵇ⇔𝒱 k ∀★⊑★ i nv w = ⇔-id
Gᵇ⇔𝒱 k (∀⊑★ ns p) i nv w = ⇔-id
Gᵇ⇔𝒱 k bot⊑★ i nv w = iff (λ ()) (λ ())

module _ {Φ : Corr Δ Δ′} {A} (a : NonVar A) (z : zero ∈ᵗ A)
    (p : only Φ ⊢ A ⊑ ★) where

  private
    toV : ∀ {m n} (le : m ≤′ n) → 0 < m → ∀ w
      {δ : Interp (suc Δ) Δ′ (ΔL w) (ΔR w)} {V V′}
      → Gᵇ≤ ≻ le p w δ V V′ → 𝒱≤ ≻ le p w δ V V′
    toV {suc j} le (s≤s z≤n) w r =
      𝒱≤-cast ≻ ≤′-refl le p w
        (to (Gᵇ⇔𝒱 j p z a w) (Gᵇ≤→Gᵇ ≻ le p w r))

    fromV : ∀ {m n} (le : m ≤′ n) → 0 < m → ∀ w
      {δ : Interp (suc Δ) Δ′ (ΔL w) (ΔR w)} {V V′}
      → 𝒱≤ ≻ le p w δ V V′ → Gᵇ≤ ≻ le p w δ V V′
    fromV {suc j} le (s≤s z≤n) w r =
      Gᵇ→Gᵇ≤ ≻ le p w
        (from (Gᵇ⇔𝒱 j p z a w) (𝒱≤-cast ≻ le ≤′-refl p w r))

  -- the guarded clause is the clause with slack 1, read by `𝒱`
  allOnlyG→Cl : ∀ k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → allOnlyG ≻ (suc k) p w δ Vl Vr → OnlyCl ≻ 1 (suc k) p w δ Vl Vr
  allOnlyG→Cl k w {δ} f e {n′} le c oc =
    ℰᵍ-map⁺ ≻ n′ _
      {VR = λ le′ w″ e′ → Gᵇ≤ ≻ (≤′-trans le′ le) p w″
        (extOnlyI (leftTyS c) (sem (onlyLeafS ≻ (∸1-≤′ le) c)) (δ ↑ᴵ e)
          ↑ᴵ e′)}
      {VR′ = λ le′ w″ e′ → 𝒱≤ ≻ (≤′-trans le′ le) p w″
        (extOnlyI (leftTyS c) (sem (onlyLeafS ≻ (leafLe 1 le) c)) (δ ↑ᴵ e)
          ↑ᴵ e′)}
      (λ le′ pos w″ e′ V V′ r →
        𝒱≤-resp ≻ (≤′-trans le′ le) p w″
          (↑ᴵ-resp (extOnlyI-resp
            (onlyLeafS-≈ ≻ (∸1-≤′ le) (leafLe 1 le) c) ≈ᴵ-refl) e′)
          (toV (≤′-trans le′ le) pos w″ r))
      (f e le c oc)

  Cl→allOnlyG : ∀ k w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
    → OnlyCl ≻ 1 (suc k) p w δ Vl Vr → allOnlyG ≻ (suc k) p w δ Vl Vr
  Cl→allOnlyG k w {δ} f e {n′} le c oc =
    ℰᵍ-map⁺ ≻ n′ _
      {VR = λ le′ w″ e′ → 𝒱≤ ≻ (≤′-trans le′ le) p w″
        (extOnlyI (leftTyS c) (sem (onlyLeafS ≻ (leafLe 1 le) c)) (δ ↑ᴵ e)
          ↑ᴵ e′)}
      {VR′ = λ le′ w″ e′ → Gᵇ≤ ≻ (≤′-trans le′ le) p w″
        (extOnlyI (leftTyS c) (sem (onlyLeafS ≻ (∸1-≤′ le) c)) (δ ↑ᴵ e)
          ↑ᴵ e′)}
      (λ le′ pos w″ e′ V V′ r →
        fromV (≤′-trans le′ le) pos w″
          (𝒱≤-resp ≻ (≤′-trans le′ le) p w″
            (↑ᴵ-resp (extOnlyI-resp
              (onlyLeafS-≈ ≻ (leafLe 1 le) (∸1-≤′ le) c) ≈ᴵ-refl) e′) r))
      (f e le c oc)

allDead-from : ∀ d n {Φ : Corr Δ Δ′} {A} (p : dead Φ ⊢ A ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Wr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n
       → (c : SDesc (ΔL w′) (ΔR w′)) → WFS c
       → PreTy (ιʷ w′) (rightTyS c) λ T₀ →
         ℰ d n′ p w′ (extDeadI (leftTyS c) (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
             [ leftTyS c ])
           (renameᵗᵐ (ρS e) Wr ⦂∀ ★ [ T₀ ]))
  → allDead d n p w δ Vl Wr
allDead-from d n p w f e le c wf T₀ eqT =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ → 𝒱≤-cast d le′ (≤′-trans le′ le) p w″)
    (f e (≤′⇒≤ le) c wf T₀ eqT)

-- equal type-applied terms
inst≡ : ∀ {Θ} {M M′ : Term Θ} {C T} → M ≡ M′ → M ⦂∀ C [ T ] ≡ M′ ⦂∀ C [ T ]
inst≡ refl = refl

------------------------------------------------------------------------
-- The bounds and right conversions in a future
------------------------------------------------------------------------

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} {w w′ : World} (e : w′ ⊒ w)
    (m : CMode Φ X (ΔL w) (storeR w)) (σ : Δ′ ⇒ˢ storeR w) where

  rconv-↑≡ : ∀ {rc} → rconv m σ ≡ rc
    → rconv (CMode-↑ (ρL e) (ρS e) m) (σ ↑ˢ e) ≡ renRConv (ρS e) rc
  rconv-↑≡ eq = trans (rconv-↑ (ρL e) (ρS e) m σ) (cong (renRConv (ρS e)) eq)

-- the store body of a `∀` clause's right annotation
pre∀ : ∀ {Δ′} {w : World} {ρ : Δ′ ⇒ˢ ΔR w} {σ} B {B₀}
  → PreB w ρ σ (`∀ B)
  → substᵗ (extsᵗ ρ) B ≡ renameᵗ (toRenameᵗ (keepᵗ (ιʷ w))) B₀
  → substᵗ (extsᵗ σ) B ≡ B₀
pre∀ {w = w} B h eqB =
  renameᵗ-injective (toRenameᵗ-injective (keepᵗ (ιʷ w)))
    (trans (sym (PreB-body B h)) eqB)

-- the right type ★ is its own store preimage
pre★ : ∀ {Δ Δ′} {w : World} {rc} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt}
  → PreM w rc δs δt σs σt ★
pNo pre★ eq = refl
pJust pre★ eq = preB refl ,ᵖ preB refl

pre★⇒ : ∀ {Δ Δ′} {w : World} {rc} {δs δt : Interp Δ Δ′ (ΔL w) (ΔR w)}
    {σs σt}
  → PreM w rc δs δt σs σt (★ ⇒ ★)
pNo pre★⇒ eq = refl
pJust pre★⇒ eq = preB refl ,ᵖ preB refl


------------------------------------------------------------------------
-- A converted value at a `∀` type, renamed
------------------------------------------------------------------------

revL≡ : ∀ {w w′} (e : w′ ⊒ w) {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    (m : CMode Φ X (ΔL w) (storeR w)) α
    (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    (Vl : Term (ΔL w)) (A : Ty (suc Δ)) {C T}
  → renameᵗᵐ (ρL e) (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗)
      ⦂∀ C [ T ]
    ≡ (renameᵗᵐ (ρL e) Vl
        ↑ `∀↑ 〖 suc (toRenameᵗ (ρL e) α)
               , ⇑ᵗ (repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e)))
               ↑ substᵗ (extsᵗ (δl (δs ↑ᴵ e))) A 〗) ⦂∀ C [ T ]
revL≡ e m α δs δt Vl A =
  inst≡ (sym (revRen e m α δs δt (renameᵗᵐ (ρL e) Vl) (`∀ A)))

conL≡ : ∀ {w w′} (e : w′ ⊒ w) {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    (m : CMode Φ X (ΔL w) (storeR w)) α
    (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    (Wl : Term (ΔL w)) (A : Ty (suc Δ)) {C T}
  → renameᵗᵐ (ρL e)
      (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A)))
      ⦂∀ C [ T ]
    ≡ (renameᵗᵐ (ρL e) Wl
        ↓ `∀↓ makeConceal (suc (toRenameᵗ (ρL e) α))
               (⇑ᵗ (repM (CMode-↑ (ρL e) (ρS e) m) (δl (δt ↑ᴵ e))))
               (substᵗ (extsᵗ (δl (δs ↑ᴵ e))) A)) ⦂∀ C [ T ]
conL≡ e m α δs δt Wl A =
  inst≡ (sym (conRen e m α δs δt (renameᵗᵐ (ρL e) Wl) (`∀ A)))

------------------------------------------------------------------------
-- `∀⊑∀`
------------------------------------------------------------------------

-- the interpretation of a `∀` clause at an equal right type
ℰ-pairI : ∀ {d n} {Φ : Corr Δ Δ′} {A B} {p : pair Φ ⊢ A ⊑ B} {w}
    {Tl Tr Tr′ L} {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {M M′}
  → Tr ≡ Tr′ → ℰ d n p w (extPairI Tl Tr L δ) M M′
  → ℰ d n p w (extPairI Tl Tr′ L δ) M M′
ℰ-pairI refl r = r

module PairV (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m σt) (substᵗ σs B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (rconv m σt) δs δt σs σt B → ∀ {k} → ConM d m (rconv m σt) k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (rconv m σt) (substᵗ σs B) Wr))
    where

  open PairRev d N p rev
  open PairRevL d N p rev
  open PairCon d N p rev con
  open PairConL d N p rev con

  revV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
      {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (rconv m σt) δs δt σs σt (`∀ B) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → allPair d n p w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗)
        (revM (rconv m σt) (substᵗ σs (`∀ B)) Vr)
  revV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {rk} h ps le {Vl} {Vr} vl vr r
      with rconv m σt in eq
  revV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {both} h ps le {Vl} {Vr} vl vr r
      | just (α′ , R′) =
    allPair-from d n p w {δ = δt}
      λ {w′} e {n′} le′ (sdesc Xs Ys c) wf T₀ eqT B₀ eqB →
      ℰ-pairI (sym eqT)
        (ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A))
          (cong₂ (λ M C → M ⦂∀ C [ T₀ ])
            (sym (revM-ren (ρS e) (just (α′ , R′)) σs (`∀ B) Vr))
            (pre∀ B (PreB-↑ (pT (pJust ps refl)) e) eqB))
          (pairRev {n′} _ (ConvI-↑ e h) (PreS-↑ (pJust ps refl) e)
            (≤-trans le′ le)
            (rconv-↑≡ e m σt eq)
            (renameᵗᵐ-preserves-Value (ρL e) vl)
            (renameᵗᵐ-preserves-Value (ρS e) vr)
            (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c wf
            eqT))
  revV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {left} h ps le {Vl} {Vr} vl vr r
      | just (α′ , R′) =
    ⊥-elim (subst (Allowed left) eq (rcOK h))
  revV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {rk} h ps le {Vl} {Vr} vl vr r
      | nothing =
    allPair-from d n p w {δ = δt}
      λ {w′} e {n′} le′ (sdesc Xs Ys c) wf T₀ eqT B₀ eqB →
      ℰ-pairI (sym eqT)
        (ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A))
          refl
          (pairRevL {n′} _ (ConvI-↑ e h)
            (Agree-↑ (toRenameᵗ (ρR e)) (`∀ B) (pNo ps refl)) (≤-trans le′ le)
            (rconv-↑≡ e m σt eq)
            (renameᵗᵐ-preserves-Value (ρL e) vl)
            (renameᵗᵐ-preserves-Value (ρS e) vr)
            (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c wf
            eqT eqB))

  conV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
      {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (rconv m σt) δs δt σs σt (`∀ B) → ConM d m (rconv m σt) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → allPair d n p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A)))
        (conM (rconv m σt) (substᵗ σs (`∀ B)) Wr)
  conV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {rk} h ps cb {Wl} {Wr} wl wr r
      with rconv m σt in eq
  conV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {both} h ps cb {Wl} {Wr} wl wr r
      | just (α′ , R′) =
    allPair-from d n p w {δ = δs}
      λ {w′} e {n′} le′ (sdesc Xs Ys c) wf T₀ eqT B₀ eqB →
      ℰ-pairI (sym eqT)
        (ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A))
          (cong₂ (λ M C → M ⦂∀ C [ T₀ ])
            (sym (conM-ren (ρS e) (just (α′ , R′)) σs (`∀ B) Wr))
            (pre∀ B (PreB-↑ (pS (pJust ps refl)) e) eqB))
          (pairCon {n′} _ (ConvI-↑ e h) (PreS-↑ (pJust ps refl) e)
            (≤-trans le′ (ConMb-≤ d (isNone m) (just (α′ , R′)) cb))
            (rconv-↑≡ e m σt eq)
            (renameᵗᵐ-preserves-Value (ρL e) wl)
            (renameᵗᵐ-preserves-Value (ρS e) wr)
            (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c wf
            eqT))
  conV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {left} h ps cb {Wl} {Wr} wl wr r
      | just (α′ , R′) =
    ⊥-elim (subst (Allowed left) eq (rcOK h))
  conV {n} w {m = m} {α} {δs} {δt} {σs} {σt} {rk} h ps cb {Wl} {Wr} wl wr r
      | nothing =
    allPair-from d n p w {δ = δs}
      λ {w′} e {n′} le′ (sdesc Xs Ys c) wf T₀ eqT B₀ eqB →
      ℰ-pairI (sym eqT)
        (ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A))
          refl
          (pairConL {n′} _ (ConvI-↑ e h)
            (Agree-↑ (toRenameᵗ (ρR e)) (`∀ B) (pNo ps refl))
            (ConM-↑ d (ρL e) (ρS e) m (rconv-↑≡ e m σt eq) le′ cb)
            (rconv-↑≡ e m σt eq)
            (renameᵗᵐ-preserves-Value (ρL e) wl)
            (renameᵗᵐ-preserves-Value (ρS e) wr)
            (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c wf
            eqT eqB))

------------------------------------------------------------------------
-- `∀⊑`
------------------------------------------------------------------------

module OnlyV (d : Dir) (g : ℕ) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : only Φ ⊢ A ⊑ B)
    (RF : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       → CMode Ψ X′ ΘL ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR)
    (RF-↑ : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR ΘL′ ΘR′}
       (ρL : ΘL ↪ᵗ ΘL′) (ρR : ΘR ↪ᵗ ΘR′) (m : CMode Ψ X′ ΘL ΘR) σ
       → RF (CMode-↑ ρL ρR m) (λ Y → renameᵗ (toRenameᵗ ρR) (σ Y))
         ≡ renRConv ρR (RF m σ))
    (RF-only : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       (m : CMode Ψ X′ ΘL ΘR) σ → RF (CMode-only m) σ ≡ RF m σ)
    (RF-left : ∀ {Δ₀} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
       (σ : Δ′ ⇒ˢ ΘR) → RF (m-left {Φ = Ψ} {X = X′} {ΘL = ΘL}) σ ≡ nothing)
    (rev : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B → ∀ {k} → k ≤ g + N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (RF m σt) (substᵗ σs B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt
       → PreM w (RF m σt) δs δt σs σt B → ∀ {k}
       → ConM d m (RF m σt) k (g + N′)
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (RF m σt) (substᵗ σs B) Wr))
    where

  open OnlyRev d g N p RF RF-↑ RF-only RF-left rev
  open OnlyCon d g N p RF RF-↑ RF-only RF-left rev con

  revV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
      {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt B → n ≤ g + N
    → ∀ {Vl Vr} → Value Vl → Value Vr → OnlyCl d g n p w δs Vl Vr
    → OnlyCl d g n p w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗)
        (revM (RF m σt) (substᵗ σs B) Vr)
  revV {n} w {m = m} {α} {δs} {δt} {σs} {σt} h ps le {Vl} {Vr} vl vr r =
    OnlyCl-from d g n p w {δ = δt} λ e {n′} le′ (sdesc Xs Ys c) oc →
      ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A))
        (trans
          (cong (λ c′ → revM c′ (substᵗ (σs ↑ˢ e) B)
                          (renameᵗᵐ (ρS e) Vr))
            (RF-↑ (ρL e) (ρS e) m σt))
          (sym (revM-ren (ρS e) (RF m σt) σs B Vr)))
        (onlyRev {n′} _ (ConvI-↑ e h) (PreM-↑ ps e (RF-↑ (ρL e) (ρS e) m σt))
          (≤-trans le′ le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρS e) vr)
          (OnlyCl-down d g le′ p _ (OnlyCl-mono d g n p e r)) Xs Ys c oc)

  conV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
      {rk} (h : ConvI d N rk w m α δs δt σs σt)
    → PreM w (RF m σt) δs δt σs σt B → ConM d m (RF m σt) n (g + N)
    → ∀ {Wl Wr} → Value Wl → Value Wr → OnlyCl d g n p w δt Wl Wr
    → OnlyCl d g n p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A)))
        (conM (RF m σt) (substᵗ σs B) Wr)
  conV {n} w {m = m} {α} {δs} {δt} {σs} {σt} h ps cb {Wl} {Wr} wl wr r =
    OnlyCl-from d g n p w {δ = δs} λ e {n′} le′ (sdesc Xs Ys c) oc →
      ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A))
        (trans
          (cong (λ c′ → conM c′ (substᵗ (σs ↑ˢ e) B)
                          (renameᵗᵐ (ρS e) Wr))
            (RF-↑ (ρL e) (ρS e) m σt))
          (sym (conM-ren (ρS e) (RF m σt) σs B Wr)))
        (onlyCon {n′} _ (ConvI-↑ e h) (PreM-↑ ps e (RF-↑ (ρL e) (ρS e) m σt))
          (ConM-↑ d (ρL e) (ρS e) m (RF-↑ (ρL e) (ρS e) m σt) le′ cb)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρS e) wr)
          (OnlyCl-down d g le′ p _ (OnlyCl-mono d g n p e r)) Xs Ys c oc)

------------------------------------------------------------------------
-- `∀⊑★`, in the `★` lemma
------------------------------------------------------------------------

module DeadV (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A}
    (p : dead Φ ⊢ A ⊑ ★)
    (rev : ∀ {N′ rk w X′} {m : CMode (dead Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           Vr)
    (con : ∀ {N′ rk w X′} {m : CMode (dead Φ) X′ (ΔL w) (storeR w)}
       {α δs δt σs σt} → ConvI d N′ rk w m α δs δt σs σt → ∀ {k}
       → ConM d m nothing k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A)) Wr)
    where

  open DeadConv d N p rev con

  revV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
      {rk} (h : ConvI d N rk w m α δs δt σs σt) → n ≤ N
    → ∀ {Vl Wr} → Value Vl → allDead d n p w δs Vl Wr
    → allDead d n p w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗) Wr
  revV {n} w {m = m} {α} {δs} {δt} {σs} {σt} h le {Vl} {Wr} vl r =
    allDead-from d n p w {δ = δt}
      λ e {n′} le′ (sdesc Xs Ys c) wf T₀ eqT →
      ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A)) refl
        (deadRev {n′} _ (ConvI-↑ e h) (≤-trans le′ le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (allDead-down d le′ p _ (allDead-mono d n p e r))
          Xs Ys c wf eqT)

  conV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
      {rk} (h : ConvI d N rk w m α δs δt σs σt) → ConM d m nothing n N
    → ∀ {Wl Wr} → Value Wl → allDead d n p w δt Wl Wr
    → allDead d n p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A))) Wr
  conV {n} w {m = m} {α} {δs} {δt} {σs} {σt} h cb {Wl} {Wr} wl r =
    allDead-from d n p w {δ = δs}
      λ e {n′} le′ (sdesc Xs Ys c) wf T₀ eqT →
      ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A)) refl
        (deadCon {n′} _ (ConvI-↑ e h)
          (ConM-↑ d (ρL e) (ρS e) m refl le′ cb)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (allDead-down d le′ p _ (allDead-mono d n p e r))
          Xs Ys c wf eqT)

------------------------------------------------------------------------
-- The lemma at `★`: the right is not converted
------------------------------------------------------------------------

Rev★ : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A} → Φ ⊢ A ⊑ ★ → Set₁
Rev★ d {Φ = Φ} {A} p =
  ∀ {N rk w X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → ∀ {k} → k ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
  → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗) Vr

Con★ : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A} → Φ ⊢ A ⊑ ★ → Set₁
Con★ d {Φ = Φ} {A} p =
  ∀ {N rk w X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → ∀ {k} → ConM d m nothing k N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
  → ℰ d k p w δs
      (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A)) Wr

-- `★` itself: an identity step
rev★★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} → Rev★ d (★⊑★ {Φ = Φ})
rev★★ d h {k} le vl vr r =
  ℰ-steps? d k ★⊑★ _ (goodT h) (step (id-reveal vl)) stay vl vr
    (★★-δ d k r)

con★★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} → Con★ d (★⊑★ {Φ = Φ})
con★★ d h {k} cb wl wr r =
  ℰ-steps? d k ★⊑★ _ (goodS h) (step (id-conceal wl)) stay wl wr
    (★★-δ d k r)

-- a `∀★` value under a map of its dead-variable clause
allDeadStar-map : ∀ {d n} {Φ : Corr Δ Δ′} {A} {p : dead Φ ⊢ A ⊑ ★}
    {w} {δ δ′ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vl′ Vr}
  → (∀ {Wr} → allDead d n p w δ Vl Wr → allDead d n p w δ′ Vl′ Wr)
  → Value Vr → allDeadStar d n p w δ Vl Vr → allDeadStar d n p w δ′ Vl′ Vr
allDeadStar-map f (v CT.《 i 》) (inj , r) = inj , f r
allDeadStar-map f (CT.ƛ N) ()
allDeadStar-map f (CT.Λ v) ()
allDeadStar-map f (CT.$ k) ()
allDeadStar-map f (v CT.↑ rv) ()
allDeadStar-map f (v CT.↓ cv) ()

-- the right side's conversion when the right is not converted
noRF : ∀ {Δ₀ Δ′} {Ψ : Corr Δ₀ Δ′} {X′ : TyVar Δ₀} {ΘL ΘR}
  → CMode Ψ X′ ΘL ΘR → (Δ′ ⇒ˢ ΘR) → RConv ΘR
noRF m σ = nothing

-- a conceal's bound in `≻` with the right not converted, with slack 1
ConMb-slack : ∀ {Θ} b {k N} → ConMb {Θ} ≻ b nothing (suc k) (suc N)
  → ConMb {Θ} ≻ b nothing k N
ConMb-slack true le = ≤-pred le
ConMb-slack false le = ≤-pred le

ConMb-up : ∀ {Θ} b {k N} → ConMb {Θ} ≻ b nothing k N
  → ConMb {Θ} ≻ b nothing k (suc N)
ConMb-up true le = ≤-trans le (n≤1+n _)
ConMb-up false le = ≤-trans le (n≤1+n _)

mutual
  rev★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → Rev★ d p
  rev★ d ★⊑★ = rev★★ d
  rev★ d ι⊑★ h {k} le vl vr r =
    ℰ-steps? d k ι⊑★ _ (goodT h) (step (id-reveal vl)) stay vl vr
      (ι★-δ d k r)
  rev★ d (X⊑★ z) h {k} le vl vr r = rev★-var d k z _ h le vl vr r
  rev★ ≺ (⇒⊑★ p q) {N} {rk} {w} {X} h {k} le vl vr r =
    ℰ-value ≺ k (⇒⊑★ p q) w (vl CT.↑ CT.fun) vr
      (funStar-map (λ v f → fun-rev h pre★⇒ le vl v f) vr r)
    where
    open FunConv {X = X} ≺ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ _ → rev★ ≺ p h′) (λ h′ _ → con★ ≺ p h′)
      (λ h′ _ → rev★ ≺ q h′) (λ h′ _ → con★ ≺ q h′)
      (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
  rev★ ≻ (⇒⊑★ p q) h {zero} le vl vr r = ℰ-zero ≻ (⇒⊑★ p q) _
  rev★ ≻ (⇒⊑★ p q) {N} {rk} {w} {X} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) (⇒⊑★ p q) w (vl CT.↑ CT.fun) vr
      (funStar-map
        (λ v f → fun-rev h pre★⇒ (≤-trans (n≤1+n k) le) vl v f) vr r)
    where
    open FunConv {X = X} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
      (λ h′ _ → rev★ ≻ q h′) (λ h′ _ → con★ ≻ q h′)
      (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
  rev★ ≺ (∀⊑ Anv z p) {N} {rk} {w} h {k} le vl vr (i , r) =
    ℰ-value ≺ k (∀⊑ Anv z p) w (vl CT.↑ CT.all) vr
      (i , OnlyV.revV ≺ 0 N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
        (λ σ → refl) (λ h′ _ → rev★ ≺ p h′) (λ h′ _ → con★ ≺ p h′)
        w h pre★ le vl vr r)
  rev★ ≻ (∀⊑ Anv z p) h le vl vr r =
    rev★G (∀⊑ Anv z p) nonvar-all h (≤-trans le (n≤1+n _)) vl vr r
  rev★ ≺ {Φ = Φ} ∀★⊑★ {N} {rk} {w} {δs = δs} {δt} h {k} le vl vr r =
    ℰ-value ≺ k ∀★⊑★ w (vl CT.↑ CT.all) vr
      (to (allDeadStar-★ ≺ k {Ψ = Φ} w {δ = δt})
        (allDeadStar-map
          (DeadV.revV ≺ N (★⊑★ {Φ = dead Φ}) (rev★★ ≺) (con★★ ≺)
            w h le vl)
          vr (from (allDeadStar-★ ≺ k {Ψ = Φ} w {δ = δs}) r)))
  rev★ ≻ ∀★⊑★ h {zero} le vl vr r = ℰ-zero ≻ ∀★⊑★ _
  rev★ ≻ {Φ = Φ} ∀★⊑★ {N} {rk} {w} {δs = δs} {δt} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) ∀★⊑★ w (vl CT.↑ CT.all) vr
      (to (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δt})
        (allDeadStar-map
          (DeadV.revV ≻ N (★⊑★ {Φ = dead Φ}) (rev★★ ≻) (con★★ ≻)
            w h (≤-trans (n≤1+n k) le) vl)
          vr (from (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δs}) r)))
  rev★ ≺ (∀⊑★ ns p) {N} {rk} {w} h {k} le vl vr r =
    ℰ-value ≺ k (∀⊑★ ns p) w (vl CT.↑ CT.all) vr
      (allDeadStar-map
        (DeadV.revV ≺ N p (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
          w h le vl)
        vr r)
  rev★ ≻ (∀⊑★ ns p) h {zero} le vl vr r = ℰ-zero ≻ (∀⊑★ ns p) _
  rev★ ≻ (∀⊑★ ns p) {N} {rk} {w} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) (∀⊑★ ns p) w (vl CT.↑ CT.all) vr
      (allDeadStar-map
        (DeadV.revV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h (≤-trans (n≤1+n k) le) vl)
        vr r)
  rev★ ≺ bot⊑★ h le vl vr ()
  rev★ ≻ bot⊑★ h {zero} le vl vr r = ℰ-zero ≻ bot⊑★ _
  rev★ ≻ bot⊑★ h {suc k} le vl vr ()

  con★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → Con★ d p
  con★ d ★⊑★ = con★★ d
  con★ d ι⊑★ h {k} cb wl wr r =
    ℰ-steps? d k ι⊑★ _ (goodS h) (step (id-conceal wl)) stay wl wr
      (ι★-δ d k r)
  con★ d (X⊑★ z) {m = m} h {k} cb wl wr r =
    con★-var d k z _ h (ConMb-≤ d (isNone m) nothing cb) cb wl wr r
  con★ ≺ (⇒⊑★ p q) {N} {rk} {w} {X} h {k} cb wl wr r =
    ℰ-value ≺ k (⇒⊑★ p q) w (wl CT.↓ CT.fun) wr
      (funStar-map (λ v f → fun-con h pre★⇒ cb wl v f) wr r)
    where
    open FunConv {X = X} ≺ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ _ → rev★ ≺ p h′) (λ h′ _ → con★ ≺ p h′)
      (λ h′ _ → rev★ ≺ q h′) (λ h′ _ → con★ ≺ q h′)
      (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
  con★ ≻ (⇒⊑★ p q) h {zero} cb wl wr r = ℰ-zero ≻ (⇒⊑★ p q) _
  con★ ≻ (⇒⊑★ p q) {N} {rk} {w} {X} {m} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (⇒⊑★ p q) w (wl CT.↓ CT.fun) wr
      (funStar-map
        (λ v f → fun-con h pre★⇒
          (ConMb-down ≻ (isNone m) nothing (n≤1+n k) cb) wl v f) wr r)
    where
    open FunConv {X = X} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
      (λ h′ _ → rev★ ≻ q h′) (λ h′ _ → con★ ≻ q h′)
      (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
  con★ ≺ (∀⊑ Anv z p) {N} {rk} {w} h {k} cb wl wr (i , r) =
    ℰ-value ≺ k (∀⊑ Anv z p) w (wl CT.↓ CT.all) wr
      (i , OnlyV.conV ≺ 0 N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
        (λ σ → refl) (λ h′ _ → rev★ ≺ p h′) (λ h′ _ → con★ ≺ p h′)
        w h pre★ cb wl wr r)
  con★ ≻ (∀⊑ Anv z p) {m = m} h cb wl wr r =
    con★G (∀⊑ Anv z p) nonvar-all h (ConMb-up (isNone m) cb) wl wr r
  con★ ≺ {Φ = Φ} ∀★⊑★ {N} {rk} {w} {δs = δs} {δt} h {k} cb wl wr r =
    ℰ-value ≺ k ∀★⊑★ w (wl CT.↓ CT.all) wr
      (to (allDeadStar-★ ≺ k {Ψ = Φ} w {δ = δs})
        (allDeadStar-map
          (DeadV.conV ≺ N (★⊑★ {Φ = dead Φ}) (rev★★ ≺) (con★★ ≺)
            w h cb wl)
          wr (from (allDeadStar-★ ≺ k {Ψ = Φ} w {δ = δt}) r)))
  con★ ≻ ∀★⊑★ h {zero} cb wl wr r = ℰ-zero ≻ ∀★⊑★ _
  con★ ≻ {Φ = Φ} ∀★⊑★ {N} {rk} {w} {m = m} {δs = δs} {δt} h {suc k} cb wl wr
      r =
    ℰ-value ≻ (suc k) ∀★⊑★ w (wl CT.↓ CT.all) wr
      (to (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δs})
        (allDeadStar-map
          (DeadV.conV ≻ N (★⊑★ {Φ = dead Φ}) (rev★★ ≻) (con★★ ≻)
            w h (ConMb-down ≻ (isNone m) nothing (n≤1+n k) cb) wl)
          wr (from (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δt}) r)))
  con★ ≺ (∀⊑★ ns p) {N} {rk} {w} h {k} cb wl wr r =
    ℰ-value ≺ k (∀⊑★ ns p) w (wl CT.↓ CT.all) wr
      (allDeadStar-map
        (DeadV.conV ≺ N p (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
          w h cb wl)
        wr r)
  con★ ≻ (∀⊑★ ns p) h {zero} cb wl wr r = ℰ-zero ≻ (∀⊑★ ns p) _
  con★ ≻ (∀⊑★ ns p) {N} {rk} {w} {m = m} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (∀⊑★ ns p) w (wl CT.↓ CT.all) wr
      (allDeadStar-map
        (DeadV.conV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h (ConMb-down ≻ (isNone m) nothing (n≤1+n k) cb) wl)
        wr r)
  con★ ≺ bot⊑★ h cb wl wr ()
  con★ ≻ bot⊑★ h {zero} cb wl wr r = ℰ-zero ≻ bot⊑★ _
  con★ ≻ bot⊑★ h {suc k} cb wl wr ()

  -- `≻` at a body into `★` (not a variable): `G` at stage k + 1 reads
  -- the leaves at stage k only, so the bound k suffices (slack 1,
  -- notes/logrel-dgg.md, F2)
  rev★G : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → NonVar A
    → ∀ {N rk w X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
    → ConvI ≻ N rk w m α δs δt σs σt → ∀ {k} → k ≤ suc N
    → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 ≻ k p w δs Vl Vr
    → ℰ ≻ k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗) Vr
  rev★G p nv h {zero} le vl vr r = ℰ-zero ≻ p _
  rev★G ★⊑★ nv h {suc k} le vl vr r =
    ℰ-steps? ≻ (suc k) ★⊑★ _ (goodT h) (step (id-reveal vl)) stay vl vr
      r
  rev★G ι⊑★ nv h {suc k} le vl vr r =
    ℰ-steps? ≻ (suc k) ι⊑★ _ (goodT h) (step (id-reveal vl)) stay vl vr
      r
  rev★G (X⊑★ x) () h {suc k} le vl vr r
  rev★G (⇒⊑★ p q) nv {N} {rk} {w} {X} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) (⇒⊑★ p q) w (vl CT.↑ CT.fun) vr
      (funStar-map (λ v f → fun-rev h pre★⇒ (≤-pred le) vl v f) vr r)
    where
    open FunConv {X = X} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
      (λ h′ _ → rev★ ≻ q h′) (λ h′ _ → con★ ≻ q h′)
      (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
  rev★G (∀⊑ Anv z p) nv {N} {rk} {w} h {suc k} le vl vr (i , r) =
    ℰ-value ≻ (suc k) (∀⊑ Anv z p) w (vl CT.↑ CT.all) vr
      (i , Cl→allOnlyG Anv z p k w
        (OnlyV.revV ≻ 1 N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
          (λ σ → refl) (λ h′ _ → rev★G p Anv h′)
          (λ h′ _ → con★G p Anv h′)
          w h pre★ le vl vr (allOnlyG→Cl Anv z p k w r)))
  rev★G {Φ = Φ} ∀★⊑★ nv {N} {rk} {w} {δs = δs} {δt} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) ∀★⊑★ w (vl CT.↑ CT.all) vr
      (to (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δt})
        (allDeadStar-map
          (DeadV.revV ≻ N (★⊑★ {Φ = dead Φ}) (rev★★ ≻) (con★★ ≻)
            w h (≤-pred le) vl)
          vr (from (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δs}) r)))
  rev★G (∀⊑★ ns p) nv {N} {rk} {w} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) (∀⊑★ ns p) w (vl CT.↑ CT.all) vr
      (allDeadStar-map
        (DeadV.revV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h (≤-pred le) vl)
        vr r)
  rev★G bot⊑★ nv h {suc k} le vl vr ()

  con★G : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → NonVar A
    → ∀ {N rk w X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
    → ConvI ≻ N rk w m α δs δt σs σt → ∀ {k} → ConM ≻ m nothing k (suc N)
    → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 ≻ k p w δt Wl Wr
    → ℰ ≻ k p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A)) Wr
  con★G p nv h {zero} cb wl wr r = ℰ-zero ≻ p _
  con★G ★⊑★ nv h {suc k} cb wl wr r =
    ℰ-steps? ≻ (suc k) ★⊑★ _ (goodS h) (step (id-conceal wl)) stay wl wr
      r
  con★G ι⊑★ nv h {suc k} cb wl wr r =
    ℰ-steps? ≻ (suc k) ι⊑★ _ (goodS h) (step (id-conceal wl)) stay wl wr
      r
  con★G (X⊑★ x) () h {suc k} cb wl wr r
  con★G (⇒⊑★ p q) nv {N} {rk} {w} {X} {m} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (⇒⊑★ p q) w (wl CT.↓ CT.fun) wr
      (funStar-map
        (λ v f → fun-con h pre★⇒ (ConMb-slack (isNone m) cb) wl v f) wr r)
    where
    open FunConv {X = X} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ _ → rev★ ≻ p h′) (λ h′ _ → con★ ≻ p h′)
      (λ h′ _ → rev★ ≻ q h′) (λ h′ _ → con★ ≻ q h′)
      (λ h′ pm t → noTypedR _ pm t) (λ h′ pm t → noTypedC _ pm t)
  con★G (∀⊑ Anv z p) nv {N} {rk} {w} h {suc k} cb wl wr (i , r) =
    ℰ-value ≻ (suc k) (∀⊑ Anv z p) w (wl CT.↓ CT.all) wr
      (i , Cl→allOnlyG Anv z p k w
        (OnlyV.conV ≻ 1 N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
          (λ σ → refl) (λ h′ _ → rev★G p Anv h′)
          (λ h′ _ → con★G p Anv h′)
          w h pre★ cb wl wr (allOnlyG→Cl Anv z p k w r)))
  con★G {Φ = Φ} ∀★⊑★ nv {N} {rk} {w} {m = m} {δs = δs} {δt} h {suc k} cb wl
      wr r =
    ℰ-value ≻ (suc k) ∀★⊑★ w (wl CT.↓ CT.all) wr
      (to (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δs})
        (allDeadStar-map
          (DeadV.conV ≻ N (★⊑★ {Φ = dead Φ}) (rev★★ ≻) (con★★ ≻)
            w h (ConMb-slack (isNone m) cb) wl)
          wr (from (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δt}) r)))
  con★G (∀⊑★ ns p) nv {N} {rk} {w} {m = m} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (∀⊑★ ns p) w (wl CT.↓ CT.all) wr
      (allDeadStar-map
        (DeadV.conV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h (ConMb-slack (isNone m) cb) wl)
        wr r)
  con★G bot⊑★ nv h {suc k} cb wl wr ()

------------------------------------------------------------------------
-- The main lemma: the right converts as the mode says
------------------------------------------------------------------------

RevC : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} → Φ ⊢ A ⊑ B → Set₁
RevC d {Φ = Φ} {A} {B} p =
  ∀ {N rk w X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → PreM w (rconv m σt) δs δt σs σt B
  → ∀ {k} → k ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
  → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
      (revM (rconv m σt) (substᵗ σs B) Vr)

ConC : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A B} → Φ ⊢ A ⊑ B → Set₁
ConC d {Φ = Φ} {A} {B} p =
  ∀ {N rk w X} {m : CMode Φ X (ΔL w) (storeR w)} {α δs δt σs σt}
  → ConvI d N rk w m α δs δt σs σt → PreM w (rconv m σt) δs δt σs σt B
  → ∀ {k} → ConM d m (rconv m σt) k N
  → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
  → ℰ d k p w δs
      (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
      (conM (rconv m σt) (substᵗ σs B) Wr)

-- the right side's conversion of a value
revM-fun : ∀ {Θ} (rc : RConv Θ) {C D} {V : Term Θ}
  → Value V → Value (revM rc (C ⇒ D) V)
revM-fun nothing v = v
revM-fun (just (α′ , R)) v = v CT.↑ CT.fun

revM-all : ∀ {Θ} (rc : RConv Θ) {C} {V : Term Θ}
  → Value V → Value (revM rc (`∀ C) V)
revM-all nothing v = v
revM-all (just (α′ , R)) v = v CT.↑ CT.all

conM-fun : ∀ {Θ} (rc : RConv Θ) {C D} {V : Term Θ}
  → Value V → Value (conM rc (C ⇒ D) V)
conM-fun nothing v = v
conM-fun (just (α′ , R)) v = v CT.↓ CT.fun

conM-all : ∀ {Θ} (rc : RConv Θ) {C} {V : Term Θ}
  → Value V → Value (conM rc (`∀ C) V)
conM-all nothing v = v
conM-all (just (α′ , R)) v = v CT.↓ CT.all

-- at a base type, the right side's conversion is an identity step
rstepι : ∀ {Θ} (rc : RConv Θ) {ι} {V : Term Θ}
  → Value V → revM rc (‵ ι) V —→? V
rstepι nothing v = stay
rstepι (just (α′ , R)) v = step (id-reveal v)

cstepι : ∀ {Θ} (rc : RConv Θ) {ι} {V : Term Θ}
  → Value V → conM rc (‵ ι) V —→? V
cstepι nothing v = stay
cstepι (just (α′ , R)) v = step (id-conceal v)

-- the clauses at a generic direction
𝒱-⇒ : ∀ d n {Φ : Corr Δ Δ′} {A A′ B B′} (p : Φ ⊢ A ⊑ A′)
    (q : Φ ⊢ B ⊑ B′) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → funRel d n p q w δ V V′ ⇔ 𝒱 d n (⇒⊑⇒ p q) w δ V V′
𝒱-⇒ ≺ n p q w = ⇔-id
𝒱-⇒ ≻ n p q w = ⇔-id

𝒱-∀ : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : pair Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → allPair d n p w δ V V′ ⇔ 𝒱 d n (∀⊑∀ p) w δ V V′
𝒱-∀ ≺ n p w = ⇔-id
𝒱-∀ ≻ n p w = ⇔-id

𝒱-∀⊑⇒ : ∀ d n {Φ : Corr Δ Δ′} {A B₁ B₂} (Anv : NonVar A) (z : zero ∈ᵗ A)
    (p : only Φ ⊢ A ⊑ B₁ ⇒ B₂) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → allOnly d n p w δ V V′ ⇔ 𝒱 d n (∀⊑ Anv z p) w δ V V′
𝒱-∀⊑⇒ ≺ n Anv z p w = ⇔-id
𝒱-∀⊑⇒ ≻ n Anv z p w = ⇔-id

𝒱-∀⊑∀ : ∀ d n {Φ : Corr Δ Δ′} {A B} (Anv : NonVar A) (z : zero ∈ᵗ A)
    (p : only Φ ⊢ A ⊑ `∀ B) w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → allOnly d n p w δ V V′ ⇔ 𝒱 d n (∀⊑ Anv z p) w δ V V′
𝒱-∀⊑∀ ≺ n Anv z p w = ⇔-id
𝒱-∀⊑∀ ≻ n Anv z p w = ⇔-id

𝒱-bot : ∀ d n {Φ : Corr Δ Δ′} w {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {V V′}
  → 𝒱 d n (bot-elim {Φ = Φ}) w δ V V′ → ⊥
𝒱-bot ≺ n w ()
𝒱-bot ≻ n w ()

-- a left-only bound variable's body is not below a variable or a base type
nv⊑var : ∀ {Φ : Corr Δ Δ′} {A Y} → Φ ⊢ A ⊑ ＇ Y → NonVar A → ⊥
nv⊑var (X⊑Y x) ()
nv⊑var (∀⊑ Anv z p) nv = nv⊑var p Anv

⊑ι-closed : ∀ {Φ : Corr Δ Δ′} {A ι} → Φ ⊢ A ⊑ ‵ ι → ∀ {X} → X ∈ᵗ A → ⊥
⊑ι-closed ι⊑ι ()
⊑ι-closed (∀⊑ Anv z p) (∈-all x) = ⊑ι-closed p x

-- into `★`: the lemma at `★`, and the right side's identity step
revC★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → RevC d p
revC★ d p {m = m} {σt = σt} h ps le vl vr r with rconv m σt
revC★ d p {m = m} {σt = σt} h ps le vl vr r | nothing =
  rev★ d p h le vl vr r
revC★ ≺ p {m = m} {σt = σt} h ps {k} le vl vr r | just (α′ , R′) =
  ℰ-stepR ≺ k p _ (id-reveal vr) (rev★ ≺ p h le vl vr r)
revC★ ≻ p {m = m} {σt = σt} h ps {zero} le vl vr r | just (α′ , R′) =
  ℰ-zero ≻ p _
revC★ ≻ p {m = m} {σt = σt} h ps {suc k} le vl vr r | just (α′ , R′) =
  ℰ-stepR ≻ k p _ (id-reveal vr)
    (rev★ ≻ p h (≤-trans (n≤1+n k) le) vl vr
      (𝒱-down ≻ (n≤1+n k) p _ (goodS h) r))

conC★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → ConC d p
conC★ d p {m = m} {σt = σt} h ps cb wl wr r with rconv m σt
conC★ d p {m = m} {σt = σt} h ps cb wl wr r | nothing =
  con★ d p h cb wl wr r
conC★ ≺ p {m = m} {σt = σt} h ps {k} cb wl wr r | just (α′ , R′) =
  ℰ-stepR ≺ k p _ (id-conceal wr)
    (con★ ≺ p h (ConMb-≺ (isNone m) (just (α′ , R′)) nothing cb) wl wr r)
conC★ ≻ p {m = m} {σt = σt} h ps {zero} cb wl wr r | just (α′ , R′) =
  ℰ-zero ≻ p _
conC★ ≻ p {m = m} {σt = σt} h ps {suc k} cb wl wr r | just (α′ , R′) =
  ℰ-stepR ≻ k p _ (id-conceal wr)
    (con★ ≻ p h (ConMb-pred ≻ (isNone m) (just (α′ , R′)) nothing cb) wl wr
      (𝒱-down ≻ (n≤1+n k) p _ (goodT h) r))

mutual
  revC : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B) → RevC d p
  revC d ★⊑★ = revC★ d ★⊑★
  revC d ι⊑ι {m = m} {σt = σt} h ps {k} le vl vr r =
    ℰ-steps? d k ι⊑ι _ (goodT h) (step (id-reveal vl))
      (rstepι (rconv m σt) vr) vl vr (ιι-δ d k r)
  revC d (X⊑Y z) h ps {k} le vl vr r = rev-var d k z _ h le vl vr r
  revC d (⇒⊑⇒ p q) {N} {rk} {w} {X} {m} {σt = σt} h ps {k} le vl vr r =
    ℰ-value d k (⇒⊑⇒ p q) w (vl CT.↑ CT.fun) (revM-fun (rconv m σt) vr)
      (to (𝒱-⇒ d k p q w)
        (fun-rev h ps le vl vr (from (𝒱-⇒ d k p q w) r)))
    where
    open FunConv {X = X} d N rk p q rconv
      (λ ρL ρR m′ σ → rconv-↑ ρL ρR m′ σ)
      (λ h′ → revC d p h′) (λ h′ → conC d p h′)
      (λ h′ → revC d q h′) (λ h′ → conC d q h′)
      (λ h′ pm t → revTyped _ _ (rcΣ h′) (tyR h′) pm t)
      (λ h′ pm t → conTyped _ _ (rcΣ h′) (tyR h′) pm t)
  revC d (∀⊑∀ p) {N} {rk} {w} {m = m} {σt = σt} h ps {k} le vl vr r =
    ℰ-value d k (∀⊑∀ p) w (vl CT.↑ CT.all) (revM-all (rconv m σt) vr)
      (to (𝒱-∀ d k p w)
        (PairV.revV d N p (λ h′ → revC d p h′) (λ h′ → conC d p h′)
          w h ps le vl vr (from (𝒱-∀ d k p w) r)))
  revC d (⇒⊑★ p q) = revC★ d (⇒⊑★ p q)
  revC d ι⊑★ = revC★ d ι⊑★
  revC d (X⊑★ z) = revC★ d (X⊑★ z)
  revC d (∀⊑ {B = ★} Anv z p) = revC★ d (∀⊑ Anv z p)
  revC d (∀⊑ {B = ＇ Y} Anv z p) h ps le vl vr r = ⊥-elim (nv⊑var p Anv)
  revC d (∀⊑ {B = ‵ ι} Anv z p) h ps le vl vr r = ⊥-elim (⊑ι-closed p z)
  revC d (∀⊑ {B = B₁ ⇒ B₂} Anv z p) {N} {rk} {w} {m = m} {σt = σt} h ps {k}
      le vl vr r =
    ℰ-value d k (∀⊑ Anv z p) w (vl CT.↑ CT.all)
      (revM-fun (rconv m σt) vr)
      (to (𝒱-∀⊑⇒ d k Anv z p w)
        (OnlyV.revV d 0 N p (λ m′ σ → rconv m′ σ)
          (λ ρL ρR m′ σ → rconv-↑ ρL ρR m′ σ) (λ m′ σ → rconv-only m′ σ)
          (λ σ → refl) (λ h′ → revC d p h′) (λ h′ → conC d p h′)
          w h ps le vl vr (from (𝒱-∀⊑⇒ d k Anv z p w) r)))
  revC d (∀⊑ {B = `∀ B₁} Anv z p) {N} {rk} {w} {m = m} {σt = σt} h ps {k}
      le vl vr r =
    ℰ-value d k (∀⊑ Anv z p) w (vl CT.↑ CT.all)
      (revM-all (rconv m σt) vr)
      (to (𝒱-∀⊑∀ d k Anv z p w)
        (OnlyV.revV d 0 N p (λ m′ σ → rconv m′ σ)
          (λ ρL ρR m′ σ → rconv-↑ ρL ρR m′ σ) (λ m′ σ → rconv-only m′ σ)
          (λ σ → refl) (λ h′ → revC d p h′) (λ h′ → conC d p h′)
          w h ps le vl vr (from (𝒱-∀⊑∀ d k Anv z p w) r)))
  revC d ∀★⊑★ = revC★ d ∀★⊑★
  revC d (∀⊑★ ns p) = revC★ d (∀⊑★ ns p)
  revC d bot-elim h ps {k} le vl vr r = ⊥-elim (𝒱-bot d k _ r)
  revC d bot⊑★ = revC★ d bot⊑★

  conC : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A B} (p : Φ ⊢ A ⊑ B) → ConC d p
  conC d ★⊑★ = conC★ d ★⊑★
  conC d ι⊑ι {m = m} {σt = σt} h ps {k} cb wl wr r =
    ℰ-steps? d k ι⊑ι _ (goodS h) (step (id-conceal wl))
      (cstepι (rconv m σt) wr) wl wr (ιι-δ d k r)
  conC d (X⊑Y z) {m = m} {σt = σt} h ps {k} cb wl wr r =
    con-var d k z _ h (ConMb-≤ d (isNone m) (rconv m σt) cb) cb wl wr r
  conC d (⇒⊑⇒ p q) {N} {rk} {w} {X} {m} {σt = σt} h ps {k} cb wl wr r =
    ℰ-value d k (⇒⊑⇒ p q) w (wl CT.↓ CT.fun) (conM-fun (rconv m σt) wr)
      (to (𝒱-⇒ d k p q w)
        (fun-con h ps cb wl wr (from (𝒱-⇒ d k p q w) r)))
    where
    open FunConv {X = X} d N rk p q rconv
      (λ ρL ρR m′ σ → rconv-↑ ρL ρR m′ σ)
      (λ h′ → revC d p h′) (λ h′ → conC d p h′)
      (λ h′ → revC d q h′) (λ h′ → conC d q h′)
      (λ h′ pm t → revTyped _ _ (rcΣ h′) (tyR h′) pm t)
      (λ h′ pm t → conTyped _ _ (rcΣ h′) (tyR h′) pm t)
  conC d (∀⊑∀ p) {N} {rk} {w} {m = m} {σt = σt} h ps {k} cb wl wr r =
    ℰ-value d k (∀⊑∀ p) w (wl CT.↓ CT.all) (conM-all (rconv m σt) wr)
      (to (𝒱-∀ d k p w)
        (PairV.conV d N p (λ h′ → revC d p h′) (λ h′ → conC d p h′)
          w h ps cb wl wr (from (𝒱-∀ d k p w) r)))
  conC d (⇒⊑★ p q) = conC★ d (⇒⊑★ p q)
  conC d ι⊑★ = conC★ d ι⊑★
  conC d (X⊑★ z) = conC★ d (X⊑★ z)
  conC d (∀⊑ {B = ★} Anv z p) = conC★ d (∀⊑ Anv z p)
  conC d (∀⊑ {B = ＇ Y} Anv z p) h ps cb wl wr r = ⊥-elim (nv⊑var p Anv)
  conC d (∀⊑ {B = ‵ ι} Anv z p) h ps cb wl wr r = ⊥-elim (⊑ι-closed p z)
  conC d (∀⊑ {B = B₁ ⇒ B₂} Anv z p) {N} {rk} {w} {m = m} {σt = σt} h ps {k}
      cb wl wr r =
    ℰ-value d k (∀⊑ Anv z p) w (wl CT.↓ CT.all)
      (conM-fun (rconv m σt) wr)
      (to (𝒱-∀⊑⇒ d k Anv z p w)
        (OnlyV.conV d 0 N p (λ m′ σ → rconv m′ σ)
          (λ ρL ρR m′ σ → rconv-↑ ρL ρR m′ σ) (λ m′ σ → rconv-only m′ σ)
          (λ σ → refl) (λ h′ → revC d p h′) (λ h′ → conC d p h′)
          w h ps cb wl wr (from (𝒱-∀⊑⇒ d k Anv z p w) r)))
  conC d (∀⊑ {B = `∀ B₁} Anv z p) {N} {rk} {w} {m = m} {σt = σt} h ps {k}
      cb wl wr r =
    ℰ-value d k (∀⊑ Anv z p) w (wl CT.↓ CT.all)
      (conM-all (rconv m σt) wr)
      (to (𝒱-∀⊑∀ d k Anv z p w)
        (OnlyV.conV d 0 N p (λ m′ σ → rconv m′ σ)
          (λ ρL ρR m′ σ → rconv-↑ ρL ρR m′ σ) (λ m′ σ → rconv-only m′ σ)
          (λ σ → refl) (λ h′ → revC d p h′) (λ h′ → conC d p h′)
          w h ps cb wl wr (from (𝒱-∀⊑∀ d k Anv z p w) r)))
  conC d ∀★⊑★ = conC★ d ∀★⊑★
  conC d (∀⊑★ ns p) = conC★ d (∀⊑★ ns p)
  conC d bot-elim h ps {k} cb wl wr r = ⊥-elim (𝒱-bot d k _ r)
  conC d bot⊑★ = conC★ d bot⊑★

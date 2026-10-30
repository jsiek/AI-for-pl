module proof.LR.ConvMain where

-- File Charter:
--   * The conversion lemma's value-level `∀` cases: the clauses of
--     `allPair`, `allOnly` and `allDead` for converted values, from the
--     per-descriptor cases of `proof.LR.ConvLemma`.
--   * The lemma at `★` (`rev★`, `con★`), where the right is not
--     converted, by induction on the precision derivation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _≤_; _<_; s≤s; z≤n;
  _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤⇒≤′; ≤′⇒≤; ≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
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
open import proof.LR.SubstLemma using (allDeadStar-★; to; from)
open import Reduction using (id-reveal; id-conceal)

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- The `∀` clauses from their instances at each stage
------------------------------------------------------------------------

allPair-from : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : pair Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → (c : SDesc (ΔL w′) (ΔR w′))
       → ℰ d n′ p w′ (extPairI (leftTyS c) (rightTyS c)
             (sem (leafBelowS d (≤′-refl {n′}) c)) (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
             [ leftTyS c ])
           (renameᵗᵐ (ρR e) Vr ⦂∀ substᵗ (extsᵗ (δr (δ ↑ᴵ e))) B
             [ rightTyS c ]))
  → allPair d n p w δ Vl Vr
allPair-from d n p w f e le c =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le) p w″
        (↑ᴵ-resp (extPairI-resp (leafBelowS-≈ d ≤′-refl le c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d le′ (≤′-trans le′ le) p w″ r))
    (f e (≤′⇒≤ le) c)

allOnly-from : ∀ d n {Φ : Corr Δ Δ′} {A B} (p : only Φ ⊢ A ⊑ B) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Vr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n → (c : SDesc (ΔL w′) (ΔR w′))
       → ℰ d n′ p w′ (extOnlyI (leftTyS c)
             (sem (onlyLeafS d (≤′-refl {n′}) c)) (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A
             [ leftTyS c ])
           (renameᵗᵐ (ρR e) Vr))
  → allOnly d n p w δ Vl Vr
allOnly-from d n p w f e le c =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ r →
      𝒱≤-resp d (≤′-trans le′ le) p w″
        (↑ᴵ-resp (extOnlyI-resp (onlyLeafS-≈ d ≤′-refl le c) ≈ᴵ-refl) e′)
        (𝒱≤-cast d le′ (≤′-trans le′ le) p w″ r))
    (f e (≤′⇒≤ le) c)

allDead-from : ∀ d n {Φ : Corr Δ Δ′} {A} (p : dead Φ ⊢ A ⊑ ★) w
    {δ : Interp Δ Δ′ (ΔL w) (ΔR w)} {Vl Wr}
  → (∀ {w′} (e : w′ ⊒ w) {n′} → n′ ≤ n
       → (T : Ty (ΔL w′)) (T′ : Ty (ΔR w′))
       → ℰ d n′ p w′ (extDeadI T (δ ↑ᴵ e))
           (renameᵗᵐ (ρL e) Vl ⦂∀ substᵗ (extsᵗ (δl (δ ↑ᴵ e))) A [ T ])
           (renameᵗᵐ (ρR e) Wr ⦂∀ ★ [ T′ ]))
  → allDead d n p w δ Vl Wr
allDead-from d n p w f e le T T′ =
  ℰᵍ-map d _ _
    (λ le′ w″ e′ V V′ → 𝒱≤-cast d le′ (≤′-trans le′ le) p w″)
    (f e (≤′⇒≤ le) T T′)

-- equal type-applied terms
inst≡ : ∀ {Θ} {M M′ : Term Θ} {C T} → M ≡ M′ → M ⦂∀ C [ T ] ≡ M′ ⦂∀ C [ T ]
inst≡ refl = refl

------------------------------------------------------------------------
-- The bounds and right conversions in a future
------------------------------------------------------------------------

module _ {Φ : Corr Δ Δ′} {X : TyVar Δ} {w w′ : World} (e : w′ ⊒ w)
    (m : CMode Φ X (ΔL w) (ΔR w)) (σ : Δ′ ⇒ˢ ΔR w) where

  rconv-↑≡ : ∀ {rc} → rconv m σ ≡ rc
    → rconv (CMode-↑ (ρL e) (ρR e) m)
        (λ Y → renameᵗ (toRenameᵗ (ρR e)) (σ Y))
      ≡ renRConv (ρR e) rc
  rconv-↑≡ eq = trans (rconv-↑ (ρL e) (ρR e) m σ) (cong (renRConv (ρR e)) eq)

  ConB-↑ : ∀ d {n n′ N} → n′ ≤ n → ConB d (rconv m σ) n N
    → ConB d (rconv (CMode-↑ (ρL e) (ρR e) m)
        (λ Y → renameᵗ (toRenameᵗ (ρR e)) (σ Y))) n′ N
  ConB-↑ d le cb =
    subst (λ c → ConB d c _ _) (sym (rconv-↑ (ρL e) (ρR e) m σ))
      (ConB-ren d (ρR e) (rconv m σ) (ConB-down d (rconv m σ) le cb))

------------------------------------------------------------------------
-- A converted value at a `∀` type, renamed
------------------------------------------------------------------------

revL≡ : ∀ {w w′} (e : w′ ⊒ w) {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    (m : CMode Φ X (ΔL w) (ΔR w)) α (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    (Vl : Term (ΔL w)) (A : Ty (suc Δ)) {C T}
  → renameᵗᵐ (ρL e) (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗)
      ⦂∀ C [ T ]
    ≡ (renameᵗᵐ (ρL e) Vl
        ↑ `∀↑ 〖 suc (toRenameᵗ (ρL e) α)
               , ⇑ᵗ (repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e)))
               ↑ substᵗ (extsᵗ (δl (δs ↑ᴵ e))) A 〗) ⦂∀ C [ T ]
revL≡ e m α δs δt Vl A =
  inst≡ (sym (revRen e m α δs δt (renameᵗᵐ (ρL e) Vl) (`∀ A)))

conL≡ : ∀ {w w′} (e : w′ ⊒ w) {Δ Δ′} {Φ : Corr Δ Δ′} {X}
    (m : CMode Φ X (ΔL w) (ΔR w)) α (δs δt : Interp Δ Δ′ (ΔL w) (ΔR w))
    (Wl : Term (ΔL w)) (A : Ty (suc Δ)) {C T}
  → renameᵗᵐ (ρL e)
      (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A)))
      ⦂∀ C [ T ]
    ≡ (renameᵗᵐ (ρL e) Wl
        ↓ `∀↓ makeConceal (suc (toRenameᵗ (ρL e) α))
               (⇑ᵗ (repM (CMode-↑ (ρL e) (ρR e) m) (δl (δt ↑ᴵ e))))
               (substᵗ (extsᵗ (δl (δs ↑ᴵ e))) A)) ⦂∀ C [ T ]
conL≡ e m α δs δt Wl A =
  inst≡ (sym (conRen e m α δs δt (renameᵗᵐ (ρL e) Wl) (`∀ A)))

------------------------------------------------------------------------
-- `∀⊑∀`
------------------------------------------------------------------------

module PairV (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
    (p : pair Φ ⊢ A ⊑ B)
    (rev : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (rconv m (δr δt)) (substᵗ (δr δs) B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (pair Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k}
       → ConB d (rconv m (δr δt)) k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (rconv m (δr δt)) (substᵗ (δr δs) B) Wr))
    where

  open PairRev d N p rev
  open PairRevL d N p rev
  open PairCon d N p rev con
  open PairConL d N p rev con

  revV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → allPair d n p w δs Vl Vr
    → allPair d n p w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗)
        (revM (rconv m (δr δt)) (substᵗ (δr δs) (`∀ B)) Vr)
  revV {n} w {m = m} {α} {δs} {δt} {rk} h le {Vl} {Vr} vl vr r
      with rconv m (δr δt) in eq
  revV {n} w {m = m} {α} {δs} {δt} {both} h le {Vl} {Vr} vl vr r
      | just (α′ , R′) =
    allPair-from d n p w {δ = δt} λ e {n′} le′ (sdesc Xs Ys c) →
      ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A))
        (inst≡
          (sym (revM-ren (ρR e) (just (α′ , R′)) (δr δs) (`∀ B) Vr)))
        (pairRev {n′} _ (ConvI-↑ e h) (≤-trans le′ le)
          (rconv-↑≡ e m (δr δt) eq)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c)
  revV {n} w {m = m} {α} {δs} {δt} {left} h le {Vl} {Vr} vl vr r
      | just (α′ , R′) =
    ⊥-elim (subst (Allowed left) eq (rcOK h))
  revV {n} w {m = m} {α} {δs} {δt} {rk} h le {Vl} {Vr} vl vr r
      | nothing =
    allPair-from d n p w {δ = δt} λ e {n′} le′ (sdesc Xs Ys c) →
      ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A)) refl
        (pairRevL {n′} _ (ConvI-↑ e h) (≤-trans le′ le)
          (rconv-↑≡ e m (δr δt) eq)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c)

  conV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → ConB d (rconv m (δr δt)) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → allPair d n p w δt Wl Wr
    → allPair d n p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A)))
        (conM (rconv m (δr δt)) (substᵗ (δr δs) (`∀ B)) Wr)
  conV {n} w {m = m} {α} {δs} {δt} {rk} h cb {Wl} {Wr} wl wr r
      with rconv m (δr δt) in eq
  conV {n} w {m = m} {α} {δs} {δt} {both} h cb {Wl} {Wr} wl wr r
      | just (α′ , R′) =
    allPair-from d n p w {δ = δs} λ e {n′} le′ (sdesc Xs Ys c) →
      ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A))
        (inst≡
          (sym (conM-ren (ρR e) (just (α′ , R′)) (δr δs) (`∀ B) Wr)))
        (pairCon {n′} _ (ConvI-↑ e h)
          (≤-trans le′ (ConB-≤ d (just (α′ , R′)) cb))
          (rconv-↑≡ e m (δr δt) eq)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c)
  conV {n} w {m = m} {α} {δs} {δt} {left} h cb {Wl} {Wr} wl wr r
      | just (α′ , R′) =
    ⊥-elim (subst (Allowed left) eq (rcOK h))
  conV {n} w {m = m} {α} {δs} {δt} {rk} h cb {Wl} {Wr} wl wr r
      | nothing =
    allPair-from d n p w {δ = δs} λ e {n′} le′ (sdesc Xs Ys c) →
      ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A)) refl
        (pairConL {n′} _ (ConvI-↑ e h)
          (subst (λ c′ → ConB d c′ n′ N)
            (sym (rconv-↑≡ e m (δr δt) eq))
            (ConB-cast d (ConB-down d nothing le′ cb)))
          (rconv-↑≡ e m (δr δt) eq)
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (allPair-down d le′ p _ (allPair-mono d n p e r)) Xs Ys c)

------------------------------------------------------------------------
-- `∀⊑`
------------------------------------------------------------------------

module OnlyV (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A B}
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
    (rev : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           (revM (RF m (δr δt)) (substᵗ (δr δs) B) Vr))
    (con : ∀ {N′ rk w X′} {m : CMode (only Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k}
       → ConB d (RF m (δr δt)) k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A))
           (conM (RF m (δr δt)) (substᵗ (δr δs) B) Wr))
    where

  open OnlyRev d N p RF RF-↑ RF-only RF-left rev
  open OnlyCon d N p RF RF-↑ RF-only RF-left rev con

  revV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → n ≤ N
    → ∀ {Vl Vr} → Value Vl → Value Vr → allOnly d n p w δs Vl Vr
    → allOnly d n p w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗)
        (revM (RF m (δr δt)) (substᵗ (δr δs) B) Vr)
  revV {n} w {m = m} {α} {δs} {δt} h le {Vl} {Vr} vl vr r =
    allOnly-from d n p w {δ = δt} λ e {n′} le′ (sdesc Xs Ys c) →
      ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A))
        (trans
          (cong (λ c′ → revM c′ (substᵗ (δr (δs ↑ᴵ e)) B)
                          (renameᵗᵐ (ρR e) Vr))
            (RF-↑ (ρL e) (ρR e) m (δr δt)))
          (sym (revM-ren (ρR e) (RF m (δr δt)) (δr δs) B Vr)))
        (onlyRev {n′} _ (ConvI-↑ e h) (≤-trans le′ le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (renameᵗᵐ-preserves-Value (ρR e) vr)
          (allOnly-down d le′ p _ (allOnly-mono d n p e r)) Xs Ys c)

  conV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → ConB d (RF m (δr δt)) n N
    → ∀ {Wl Wr} → Value Wl → Value Wr → allOnly d n p w δt Wl Wr
    → allOnly d n p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A)))
        (conM (RF m (δr δt)) (substᵗ (δr δs) B) Wr)
  conV {n} w {m = m} {α} {δs} {δt} h cb {Wl} {Wr} wl wr r =
    allOnly-from d n p w {δ = δs} λ e {n′} le′ (sdesc Xs Ys c) →
      ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A))
        (trans
          (cong (λ c′ → conM c′ (substᵗ (δr (δs ↑ᴵ e)) B)
                          (renameᵗᵐ (ρR e) Wr))
            (RF-↑ (ρL e) (ρR e) m (δr δt)))
          (sym (conM-ren (ρR e) (RF m (δr δt)) (δr δs) B Wr)))
        (onlyCon {n′} _ (ConvI-↑ e h)
          (subst (λ c′ → ConB d c′ n′ N)
            (sym (RF-↑ (ρL e) (ρR e) m (δr δt)))
            (ConB-ren d (ρR e) (RF m (δr δt))
              (ConB-down d (RF m (δr δt)) le′ cb)))
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (renameᵗᵐ-preserves-Value (ρR e) wr)
          (allOnly-down d le′ p _ (allOnly-mono d n p e r)) Xs Ys c)

------------------------------------------------------------------------
-- `∀⊑★`, in the `★` lemma
------------------------------------------------------------------------

module DeadV (d : Dir) (N : ℕ) {Δ Δ′} {Φ : Corr Δ Δ′} {A}
    (p : dead Φ ⊢ A ⊑ ★)
    (rev : ∀ {N′ rk w X′} {m : CMode (dead Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k} → k ≤ N′
       → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
       → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗)
           Vr)
    (con : ∀ {N′ rk w X′} {m : CMode (dead Φ) X′ (ΔL w) (ΔR w)}
       {α δs δt} → ConvI d N′ rk w m α δs δt → ∀ {k}
       → ConB {ΔR w} d nothing k N′
       → ∀ {Wl Wr} → Value Wl → Value Wr → 𝒱 d k p w δt Wl Wr
       → ℰ d k p w δs
           (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) A)) Wr)
    where

  open DeadConv d N p rev con

  revV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → n ≤ N
    → ∀ {Vl Wr} → Value Vl → allDead d n p w δs Vl Wr
    → allDead d n p w δt
        (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) (`∀ A) 〗) Wr
  revV {n} w {m = m} {α} {δs} {δt} h le {Vl} {Wr} vl r =
    allDead-from d n p w {δ = δt} λ e {n′} le′ T T′ →
      ℰᵍ-≡ (sym (revL≡ e m α δs δt Vl A)) refl
        (deadRev {n′} _ (ConvI-↑ e h) (≤-trans le′ le)
          (renameᵗᵐ-preserves-Value (ρL e) vl)
          (allDead-down d le′ p _ (allDead-mono d n p e r)) T T′)

  conV : ∀ {n} w {X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt} {rk}
      (h : ConvI d N rk w m α δs δt) → ConB {ΔR w} d nothing n N
    → ∀ {Wl Wr} → Value Wl → allDead d n p w δt Wl Wr
    → allDead d n p w δs
        (Wl ↓ makeConceal α (repM m (δl δt)) (substᵗ (δl δs) (`∀ A))) Wr
  conV {n} w {m = m} {α} {δs} {δt} h cb {Wl} {Wr} wl r =
    allDead-from d n p w {δ = δs} λ e {n′} le′ T T′ →
      ℰᵍ-≡ (sym (conL≡ e m α δs δt Wl A)) refl
        (deadCon {n′} _ (ConvI-↑ e h)
          (ConB-cast d (ConB-down d nothing le′ cb))
          (renameᵗᵐ-preserves-Value (ρL e) wl)
          (allDead-down d le′ p _ (allDead-mono d n p e r)) T T′)

------------------------------------------------------------------------
-- The lemma at `★`: the right is not converted
------------------------------------------------------------------------

Rev★ : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A} → Φ ⊢ A ⊑ ★ → Set₁
Rev★ d {Φ = Φ} {A} p =
  ∀ {N rk w X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
  → ConvI d N rk w m α δs δt → ∀ {k} → k ≤ N
  → ∀ {Vl Vr} → Value Vl → Value Vr → 𝒱 d k p w δs Vl Vr
  → ℰ d k p w δt (Vl ↑ 〖 α , repM m (δl δt) ↑ substᵗ (δl δs) A 〗) Vr

Con★ : Dir → ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A} → Φ ⊢ A ⊑ ★ → Set₁
Con★ d {Φ = Φ} {A} p =
  ∀ {N rk w X} {m : CMode Φ X (ΔL w) (ΔR w)} {α δs δt}
  → ConvI d N rk w m α δs δt → ∀ {k} → ConB {ΔR w} d nothing k N
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

mutual
  rev★ : ∀ d {Δ Δ′} {Φ : Corr Δ Δ′} {A} (p : Φ ⊢ A ⊑ ★) → Rev★ d p
  rev★ d ★⊑★ = rev★★ d
  rev★ d ι⊑★ h {k} le vl vr r =
    ℰ-steps? d k ι⊑★ _ (goodT h) (step (id-reveal vl)) stay vl vr
      (ι★-δ d k r)
  rev★ d (X⊑★ z) h {k} le vl vr r = rev★-var d k z _ h le vl vr r
  rev★ ≺ (⇒⊑★ p q) {N} {rk} {w} {X} h {k} le vl vr r =
    ℰ-value ≺ k (⇒⊑★ p q) w (vl CT.↑ CT.fun) vr
      (funStar-map (λ v f → fun-rev h le vl v f) vr r)
    where
    open FunConv {X = X} ≺ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
      (λ h′ → rev★ ≺ q h′) (λ h′ → con★ ≺ q h′)
  rev★ ≻ (⇒⊑★ p q) h {zero} le vl vr r = ℰ-zero ≻ (⇒⊑★ p q) _
  rev★ ≻ (⇒⊑★ p q) {N} {rk} {w} {X} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) (⇒⊑★ p q) w (vl CT.↑ CT.fun) vr
      (funStar-map (λ v f → fun-rev h (≤-trans (n≤1+n k) le) vl v f) vr r)
    where
    open FunConv {X = X} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
      (λ h′ → rev★ ≻ q h′) (λ h′ → con★ ≻ q h′)
  rev★ ≺ (∀⊑ Anv z p) {N} {rk} {w} h {k} le vl vr r =
    ℰ-value ≺ k (∀⊑ Anv z p) w (vl CT.↑ CT.all) vr
      (OnlyV.revV ≺ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
        (λ σ → refl) (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
        w h le vl vr r)
  rev★ ≻ (∀⊑ Anv z p) h {zero} le vl vr r = ℰ-zero ≻ (∀⊑ Anv z p) _
  rev★ ≻ (∀⊑ Anv z p) {N} {rk} {w} h {suc k} le vl vr r =
    ℰ-value ≻ (suc k) (∀⊑ Anv z p) w (vl CT.↑ CT.all) vr
      (OnlyV.revV ≻ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
        (λ σ → refl) (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
        w h (≤-trans (n≤1+n k) le) vl vr r)
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
  con★ d (X⊑★ z) h {k} cb wl wr r =
    con★-var d k z _ h (ConB-≤ d nothing cb) cb wl wr r
  con★ ≺ (⇒⊑★ p q) {N} {rk} {w} {X} h {k} cb wl wr r =
    ℰ-value ≺ k (⇒⊑★ p q) w (wl CT.↓ CT.fun) wr
      (funStar-map (λ v f → fun-con h cb wl v f) wr r)
    where
    open FunConv {X = X} ≺ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
      (λ h′ → rev★ ≺ q h′) (λ h′ → con★ ≺ q h′)
  con★ ≻ (⇒⊑★ p q) h {zero} cb wl wr r = ℰ-zero ≻ (⇒⊑★ p q) _
  con★ ≻ (⇒⊑★ p q) {N} {rk} {w} {X} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (⇒⊑★ p q) w (wl CT.↓ CT.fun) wr
      (funStar-map (λ v f → fun-con h (≤-trans (n≤1+n k) cb) wl v f) wr r)
    where
    open FunConv {X = X} ≻ N rk p q noRF (λ ρL ρR m σ → refl)
      (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
      (λ h′ → rev★ ≻ q h′) (λ h′ → con★ ≻ q h′)
  con★ ≺ (∀⊑ Anv z p) {N} {rk} {w} h {k} cb wl wr r =
    ℰ-value ≺ k (∀⊑ Anv z p) w (wl CT.↓ CT.all) wr
      (OnlyV.conV ≺ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
        (λ σ → refl) (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
        w h cb wl wr r)
  con★ ≻ (∀⊑ Anv z p) h {zero} cb wl wr r = ℰ-zero ≻ (∀⊑ Anv z p) _
  con★ ≻ (∀⊑ Anv z p) {N} {rk} {w} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (∀⊑ Anv z p) w (wl CT.↓ CT.all) wr
      (OnlyV.conV ≻ N p noRF (λ ρL ρR m σ → refl) (λ m σ → refl)
        (λ σ → refl) (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
        w h (≤-trans (n≤1+n k) cb) wl wr r)
  con★ ≺ {Φ = Φ} ∀★⊑★ {N} {rk} {w} {δs = δs} {δt} h {k} cb wl wr r =
    ℰ-value ≺ k ∀★⊑★ w (wl CT.↓ CT.all) wr
      (to (allDeadStar-★ ≺ k {Ψ = Φ} w {δ = δs})
        (allDeadStar-map
          (DeadV.conV ≺ N (★⊑★ {Φ = dead Φ}) (rev★★ ≺) (con★★ ≺)
            w h cb wl)
          wr (from (allDeadStar-★ ≺ k {Ψ = Φ} w {δ = δt}) r)))
  con★ ≻ ∀★⊑★ h {zero} cb wl wr r = ℰ-zero ≻ ∀★⊑★ _
  con★ ≻ {Φ = Φ} ∀★⊑★ {N} {rk} {w} {δs = δs} {δt} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) ∀★⊑★ w (wl CT.↓ CT.all) wr
      (to (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δs})
        (allDeadStar-map
          (DeadV.conV ≻ N (★⊑★ {Φ = dead Φ}) (rev★★ ≻) (con★★ ≻)
            w h (≤-trans (n≤1+n k) cb) wl)
          wr (from (allDeadStar-★ ≻ k {Ψ = Φ} w {δ = δt}) r)))
  con★ ≺ (∀⊑★ ns p) {N} {rk} {w} h {k} cb wl wr r =
    ℰ-value ≺ k (∀⊑★ ns p) w (wl CT.↓ CT.all) wr
      (allDeadStar-map
        (DeadV.conV ≺ N p (λ h′ → rev★ ≺ p h′) (λ h′ → con★ ≺ p h′)
          w h cb wl)
        wr r)
  con★ ≻ (∀⊑★ ns p) h {zero} cb wl wr r = ℰ-zero ≻ (∀⊑★ ns p) _
  con★ ≻ (∀⊑★ ns p) {N} {rk} {w} h {suc k} cb wl wr r =
    ℰ-value ≻ (suc k) (∀⊑★ ns p) w (wl CT.↓ CT.all) wr
      (allDeadStar-map
        (DeadV.conV ≻ N p (λ h′ → rev★ ≻ p h′) (λ h′ → con★ ≻ p h′)
          w h (≤-trans (n≤1+n k) cb) wl)
        wr r)
  con★ ≺ bot⊑★ h cb wl wr ()
  con★ ≻ bot⊑★ h {zero} cb wl wr r = ℰ-zero ≻ bot⊑★ _
  con★ ≻ bot⊑★ h {suc k} cb wl wr ()

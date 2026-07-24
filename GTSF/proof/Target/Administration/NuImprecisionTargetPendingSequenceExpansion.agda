module
  proof.Target.Administration.NuImprecisionTargetPendingSequenceExpansion
  where

-- File Charter:
--   * Expands one sequence-headed hereditary target-administration spine into
--     two component pending casts.
--   * Exhaustively decomposes retained narrowing, widening, and identity-only
--     widening evidence and eliminates conversion sequences by constructor.
--   * Contains no recursive worker, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; cast-seq
  ; id-onlyᵈ
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-all
  ; conceal-fun
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; conceal-seal
  ; reveal-all
  ; reveal-fun
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NarrowWiden using
  ( _︔_!
  ; _？︔_
  ; _︔seal_
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★⇒★)
open import proof.Core.Properties.CoercionProperties using
  (coercion-endpoints-unique)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using (TargetAdministrationPlan)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (TargetAdministrationSpine; pending-cons)


private
  reveal-sequence-impossible :
    ∀ {μ Δ Σ α X c B D s t} →
    RevealConversion μ Δ Σ α X c B D →
    c ≡ s ︔ t →
    ⊥
  reveal-sequence-impossible (reveal-id-var hY ok) ()
  reveal-sequence-impossible reveal-id-base ()
  reveal-sequence-impossible reveal-id-★ ()
  reveal-sequence-impossible (reveal-unseal hX α∈Σ ok) ()
  reveal-sequence-impossible (reveal-fun s↓ t↑) ()
  reveal-sequence-impossible (reveal-all s↑) ()

  conceal-sequence-impossible :
    ∀ {μ Δ Σ α X c B D s t} →
    ConcealConversion μ Δ Σ α X c B D →
    c ≡ s ︔ t →
    ⊥
  conceal-sequence-impossible (conceal-id-var hY ok) ()
  conceal-sequence-impossible conceal-id-base ()
  conceal-sequence-impossible conceal-id-★ ()
  conceal-sequence-impossible (conceal-seal hX α∈Σ ok) ()
  conceal-sequence-impossible (conceal-fun s↑ t↓) ()
  conceal-sequence-impossible (conceal-all s↓) ()

  align-narrowing :
    ∀ {μ μ′ Δ Σ c B C B′ C′} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ B =⇒ C →
    μ′ ∣ Δ ∣ Σ ⊢ c ∶ B′ ⊒ C′ →
    μ′ ∣ Δ ∣ Σ ⊢ c ∶ B ⊒ C
  align-narrowing c⊢ c⊒
      with coercion-endpoints-unique (_ , c⊢) (_ , proj₁ c⊒)
  align-narrowing c⊢ c⊒ | refl , refl = c⊒

  align-widening :
    ∀ {μ μ′ Δ Σ c B C B′ C′} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ B =⇒ C →
    μ′ ∣ Δ ∣ Σ ⊢ c ∶ B′ ⊑ C′ →
    μ′ ∣ Δ ∣ Σ ⊢ c ∶ B ⊑ C
  align-widening c⊢ c⊑
      with coercion-endpoints-unique (_ , c⊢) (_ , proj₁ c⊑)
  align-widening c⊢ c⊑ | refl , refl = c⊑


TargetAdministrationSequenceSpineExpansionᵀ : Set
TargetAdministrationSequenceSpineExpansionᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A B C D E : Ty} {μ : ModeEnv}
    {s t : Coercion} {cs : List Coercion}
    {s⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B =⇒ C}
    {t⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C =⇒ D}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ}
    {u : Φ ∣ Δᴸ ⊢ A ⊑ E ⊣ Δᴿ} →
  TargetAdministrationPlan ρ A s⊢ p r →
  TargetAdministrationPlan ρ A t⊢ r q →
  ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ (s ︔ t) B D)
   ⊎
   (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ (s ︔ t) B D)
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ︔ t ∶ B ⊒ D))
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ︔ t ∶ B ⊑ D))
   ⊎
   (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) ×
    (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ s ︔ t ∶ B ⊑ D))) →
  TargetAdministrationSpine ρ A q u cs →
  TargetAdministrationSpine ρ A p u (s ∷ t ∷ cs)


target-administration-sequence-spine-expansionᵀ :
  TargetAdministrationSequenceSpineExpansionᵀ
target-administration-sequence-spine-expansionᵀ
    s-plan t-plan
    (inj₁ (μ′ , β , X′ , reveal)) tail =
  ⊥-elim (reveal-sequence-impossible reveal refl)
target-administration-sequence-spine-expansionᵀ
    s-plan t-plan
    (inj₂ (inj₁ (μ′ , β , X′ , conceal))) tail =
  ⊥-elim (conceal-sequence-impossible conceal refl)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       cast-seq s⊢′ t⊢′ , gG ？︔ gˢ)))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       align-narrowing s⊢ (s⊢′ , NW.untag gG)))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ ,
         align-narrowing t⊢
           (t⊢′ , NW.cross
             (NW.strictCrossⁿ→cross gˢ))))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       cast-seq s⊢′ t⊢′ , NW.fun-untag-gen gˢ)))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       align-narrowing s⊢ (s⊢′ , NW.untag ★⇒★)))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ ,
         align-narrowing t⊢ (t⊢′ , NW.gen gˢ)))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       cast-seq s⊢′ t⊢′ , gˢ ︔seal α)))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       align-narrowing s⊢
         (s⊢′ , NW.strictⁿ→narrow gˢ)))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ ,
         align-narrowing t⊢ (t⊢′ , NW.sealⁿ _ α)))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       cast-seq s⊢′ t⊢′ , gˢ ︔ gG !))))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       align-widening s⊢
         (s⊢′ , NW.cross
           (NW.strictCrossʷ→cross gˢ)))))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ ,
         align-widening t⊢ (t⊢′ , NW.tag gG))))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       cast-seq s⊢′ t⊢′ , NW.inst-fun-tag gˢ))))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       align-widening s⊢ (s⊢′ , NW.inst gˢ))))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ ,
         align-widening t⊢ (t⊢′ , NW.tag ★⇒★))))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       cast-seq s⊢′ t⊢′ , NW.unseal︔_ α gˢ))))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₂ (inj₁
      (μ′ , mode , seal★ ,
       align-widening s⊢ (s⊢′ , NW.unsealʷ α _))))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₂ (inj₁
        (μ′ , mode , seal★ ,
         align-widening t⊢
           (t⊢′ , NW.strictʷ→widen gˢ))))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , cast-seq s⊢′ t⊢′ , gˢ ︔ gG !))))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ ,
       align-widening s⊢
         (s⊢′ , NW.cross
           (NW.strictCrossʷ→cross gˢ)))))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₂ (inj₂
        (seal★ ,
         align-widening t⊢ (t⊢′ , NW.tag gG))))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , cast-seq s⊢′ t⊢′ , NW.inst-fun-tag gˢ))))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ ,
       align-widening s⊢ (s⊢′ , NW.inst gˢ))))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₂ (inj₂
        (seal★ ,
         align-widening t⊢ (t⊢′ , NW.tag ★⇒★))))))
      tail)
target-administration-sequence-spine-expansionᵀ
    {s⊢ = s⊢} {t⊢ = t⊢}
    s-plan t-plan
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ , cast-seq s⊢′ t⊢′ , NW.unseal︔_ α gˢ))))) tail =
  pending-cons s-plan
    (inj₂ (inj₂ (inj₂ (inj₂
      (seal★ ,
       align-widening s⊢ (s⊢′ , NW.unsealʷ α _))))))
    (pending-cons t-plan
      (inj₂ (inj₂ (inj₂ (inj₂
        (seal★ ,
         align-widening t⊢
           (t⊢′ , NW.strictʷ→widen gˢ))))))
      tail)

  finish-star-rep-tagged : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
      {P : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {p : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
      {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → sourceStoreʷ W ∋ X ⦂ ★
    → SourceTagSealCoreBranch W γ P ★ U X Y S cY Wᵖ γᵖ p
    → W ∣ γ ⊢² P ↓ seal X ★ ⊑ U ↓ seal Y S ∶ q
  finish-star-rep-tagged {p = p} source∈
      (core-terminus refl
        (U★ , Y★ , .★ , refl , W★ , γ★ , mono★ , same★ ,
          boundary★ , target∈★ , q★ , premise★ , reemit ,
          final-pair)) =
    final-pair p (reemit premise★)
  finish-star-rep-tagged source∈ (core-terminus-nonstar () _)
  finish-star-rep-tagged {q = q} source∈
      (core-sealed (Wʳ , γʳ , qʳ , monoʳ , sameʳ ,
        CTI2.rebase-varᴸ link , target∈ʳ , premʳ)) =
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.star-rep-target)
      monoʳ (CTI2.tag-rebase-varᴸ link) sameʳ
      (CTI2.⊢↓-sealˣ source∈) premʳ q
  finish-star-rep-tagged {q = q} source∈
      (core-sealed (Wʳ , γʳ , qʳ , monoʳ , sameʳ ,
        CTI2.rebase-onlyᴸ to-star disaligned represented ,
        target∈ʳ , premʳ)) =
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok CTI2.star-rep-target)
      monoʳ (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
      sameʳ (CTI2.⊢↓-sealˣ source∈) premʳ q
  source-spine-strip-star-rep-target : ∀ {Δᴸ Δᴿ Δ}
      {W W′ Wᵖ : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W} {γ′ : CtxImp W′} {γᵖ : CtxImp Wᵖ}
      {V : Term Δᴸ} {U : Term Δᴿ}
      {S : Ty Δᴿ} {Xᴸ X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {Xᴿ? : Maybe (TyVar Δᴿ)}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {pᵖ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    → SpineValue V
    → Value U
    → CTI2.ImpEnvMono W W′
    → RebaseAt W′ W Xᴸ Y
    → CTI2.SameCtx γ γ′
    → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X)
    → targetStoreʷ W ∋ Y ⦂ S
    → CTI2.ImpEnvMono W′ Wᵖ
    → TagRebaseAtᴸ Wᵖ W′ (just X) Xᴿ?
    → CTI2.SameCtx γ′ γᵖ
    → sourceStoreʷ W′ ∋ X ⦂ ★
    → Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᵖ
    → Σ[ Core ∈ Term Δᴸ ]
      Σ[ CoreTy ∈ Ty Δᴸ ]
      Σ[ Xᵒ ∈ TyVar Δᴸ ]
      Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γᵒ ∈ CtxImp Wᵒ ]
      Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
        (SpineValue Core
         × SourceSpineStripBranch W γ (V ↓ seal X ★) (＇ X)
             U Xᴸ Y S cY q Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)
  source-spine-strip-star-rep-target {V = M ⦂∀ C [ A ]} ()
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
  source-spine-strip-star-rep-target (sv-ƛ N) vU mono rb sc source∈
      target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-ƛ N) vU mono rb sc source∈
      target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-Λ sv) vU mono rb sc source∈
      target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-Λ sv) vU mono rb sc source∈
      target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-$ (κℕ n)) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-$ (κℕ n)) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-$ (κ𝔹 b)) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-$ (κ𝔹 b)) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-seal sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-seal sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-reveal-fun sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-reveal-fun sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-conceal-fun sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-conceal-fun sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-reveal-all sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-reveal-all sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-conceal-all sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-conceal-all sv) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-cast sv CastTerms.fun) vU
      mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-cast sv CastTerms.fun) vU
      mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target (sv-cast sv CastTerms.all) vU
      mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target (sv-cast sv CastTerms.all) vU
      mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target
      (sv-cast sv (CastTerms.genᵥ A≢★ safe)) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem
      with CTI2T.source-typing² prem
  source-spine-strip-star-rep-target
      (sv-cast sv (CastTerms.genᵥ A≢★ safe)) vU mono rb sc
      source∈ target∈ monoᵖ rb★ scᵖ X∈ prem | ()
  source-spine-strip-star-rep-target
      (sv-cast {V = M ⦂∀ C [ A ]} () CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² c prem p★)
  source-spine-strip-star-rep-target
      (sv-cast {A = ＇ X₂} (sv-cast sv inert₁) CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² c prem p★)
      with var-value-view (spine-value→Value (sv-cast sv inert₁))
        (CTI2T.source-typing² prem)
  source-spine-strip-star-rep-target
      (sv-cast {A = ＇ X₂} (sv-cast sv inert₁) CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² c prem p★) | varv-seal vW X∈′ ()
  source-spine-strip-star-rep-target
      (sv-cast {A = ‵ ι} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c tagged p★) =
    ⊥-elim
      (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-base nonstar-ι
        tagged)
  source-spine-strip-star-rep-target
      (sv-cast {A = A ⇒ B} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c tagged p★) =
    ⊥-elim
      (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-fun nonstar-⇒
        tagged)
  source-spine-strip-star-rep-target
      (sv-cast {A = `∀ A} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c tagged p★) =
    ⊥-elim
      (tagged-target-nonvar-nonstar-spine-⊥ sv nonvar-all nonstar-∀
        tagged)
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = V} {A = ＇ X₂} {c = c}
        sv inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c (CTI2.⊑cast² .cY prem p) p★)
      with var-value-view (spine-value→Value sv)
        (CTI2T.source-typing² prem)
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = .(V₀ ↓ seal X₂ R₀)}
        {A = ＇ X₂} {c = c}
      (sv-seal {V = V₀} {X = X₂} {R = R₀} sv)
      inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c (CTI2.⊑cast² .cY prem p) p★)
      | varv-seal vW X₂∈ refl =
    self-spine-sealed rb target∈
      (sv-seal (sv-seal (sv-cast (sv-seal sv) inert)))
      (target-source-var-chain
        (sv-seal (sv-cast (sv-seal sv) inert))
        vU mono rb sc source∈ target∈
        (star-rep-cast-final (sv-seal sv) inert vU monoᵖ rb★
          scᵖ X∈ (rebase-target-membership-forward rb target∈)
          prem))
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = .(V₀ ↓ seal X₂ R₀)}
        {A = ＇ X₂} {c = c}
        (sv-seal {V = V₀} {X = X₂} {R = R₀} sv)
        inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c
        (CTI2.conceal⊑² ok mono₁ rb₁ sc₁
        (CTI2.⊢↓-sealˣ X₂∈) prem p) p★)
      with rb★
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = .(V₀ ↓ seal X₂ R₀)}
        {A = ＇ X₂} {c = c}
        (sv-seal {V = V₀} {X = X₂} {R = R₀} sv)
        inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c
        (CTI2.conceal⊑² ok mono₁ rb₁ sc₁
        (CTI2.⊢↓-sealˣ X₂∈) prem p) p★)
      | CTI2.tag-rebase-varᴸ link = ?
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = .(V₀ ↓ seal X₂ R₀)}
        {A = ＇ X₂} {c = c}
        (sv-seal {V = V₀} {X = X₂} {R = R₀} sv)
        inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑² .c
        (CTI2.conceal⊑² ok mono₁ rb₁ sc₁
        (CTI2.⊢↓-sealˣ X₂∈) prem p) p★)
      | CTI2.tag-rebase-onlyᴸ to-star disaligned represented = ?
  source-spine-strip-star-rep-target {Wᵖ = Wᵖ} {Y = Y}
      (sv-cast {A = ‵ ι} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² {p = p} .c cY prem p★)
      with SPT.right-var-obligation-view {W = Wᵖ} {R = ‵ ι}
        {Y = Y} p
  source-spine-strip-star-rep-target {Wᵖ = Wᵖ} {Y = Y}
      (sv-cast {A = ‵ ι} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² {p = p} .c cY prem p★) | ()
  source-spine-strip-star-rep-target {Wᵖ = Wᵖ} {Y = Y}
      (sv-cast {A = A ⇒ B} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² {p = p} .c cY prem p★)
      with SPT.right-var-obligation-view {W = Wᵖ} {R = A ⇒ B}
        {Y = Y} p
  source-spine-strip-star-rep-target {Wᵖ = Wᵖ} {Y = Y}
      (sv-cast {A = A ⇒ B} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² {p = p} .c cY prem p★) | ()
  source-spine-strip-star-rep-target {Wᵖ = Wᵖ} {Y = Y}
      (sv-cast {A = `∀ A} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² {p = p} .c cY prem p★)
      with SPT.right-var-obligation-view {W = Wᵖ} {R = `∀ A}
        {Y = Y} p
  source-spine-strip-star-rep-target {Wᵖ = Wᵖ} {Y = Y}
      (sv-cast {A = `∀ A} {c = c} sv CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² {p = p} .c cY prem p★) | ()
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = V} {A = ＇ X₂} {c = c}
        sv inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² .c .cY prem p★)
      with var-value-view (spine-value→Value sv)
        (CTI2T.source-typing² prem)
  source-spine-strip-star-rep-target {W = W} {W′ = W′}
      {γ = γ} {γ′ = γ′}
      {U = U} {S = S} {Xᴸ = Xᴸ} {X = X} {Y = Y}
      {cY = cY} {q = q}
      (sv-cast {V = .(V₀ ↓ seal X₂ R₀)}
        {A = ＇ X₂} {c = c}
        (sv-seal {V = V₀} {X = X₂} {R = R₀} sv)
        inert@CastTerms.inj)
      vU mono rb sc source∈ target∈ monoᵖ rb★ scᵖ X∈
      (CTI2.cast⊑cast² .c .cY prem p★)
      | varv-seal vW X₂∈ refl =
    self-spine-sealed rb target∈
      (sv-seal (sv-seal (sv-cast (sv-seal sv) inert)))
      (target-source-var-chain
        (sv-seal (sv-cast (sv-seal sv) inert))
        vU mono rb sc source∈ target∈
        (star-rep-cast-final (sv-seal sv) inert vU monoᵖ rb★
          scᵖ X∈ (rebase-target-membership-forward rb target∈)
          prem))

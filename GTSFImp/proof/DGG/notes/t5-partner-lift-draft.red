T5 D4.4(ii) partner-lift draft

Date: 2026-08-17

Status: statement draft and feasibility probe only.  No live relation or proof
module was changed.

Probe:

`proof/DGG/notes/probes/PartnerLiftDraft.agda`

Checked standalone with:

`agda --safe -i . -i proof/DGG/notes/probes proof/DGG/notes/probes/PartnerLiftDraft.agda`


Candidate A verdict
-------------------

Candidate A lifts existing partner evidence through the one-bind target
insertion.  The target term is lifted by `⇑ᵗᵐ`, the optional target pivot is
lifted by `mapPivotChanges (bind B ∷ [])`, and the world is the strict-cell
target-insert world.  `NotTopTag` is stable under `⇑ᵗᵐ`; the
name-protected shape is stable because renaming sends
`(V ↓ seal Y S) ⟨ c ⟩` to the same outer shape with the renamed seal name and
renamed consistency evidence.  The `Rep★PartnerOK` occupancy side also lifts
for existing partner evidence, via `targetInsertNoTargetAtSource`.

The checked target-insert statements are:

```agda
CandidateA-SealTargetBindᵀ : Set₁
CandidateA-SealTargetBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SealPartnerOK W X P R Xᴿ? V
  → CTI2.SealPartnerOK W₁ X P R
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateA-SourceConcealTargetBindᵀ : Set₁
CandidateA-SourceConcealTargetBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? V
  → CTI2.SourceConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateA-MatchedConcealTargetBindᵀ : Set₁
CandidateA-MatchedConcealTargetBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.MatchedConcealPartnerOK W P c Xᴿ? V
  → CTI2.MatchedConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)
```

The checked strict one-bind `StructuralWorldExtendᴿ` versions have the same
conclusions:

```agda
CandidateA-SealStructuralBindᵀ : Set₁
CandidateA-SealStructuralBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → StructuralWorldExtendᴿ (bind B ∷ []) W W₁
  → CTI2.SealPartnerOK W X P R Xᴿ? V
  → CTI2.SealPartnerOK W₁ X P R
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateA-SourceConcealStructuralBindᵀ : Set₁
CandidateA-SourceConcealStructuralBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → StructuralWorldExtendᴿ (bind B ∷ []) W W₁
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? V
  → CTI2.SourceConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateA-MatchedConcealStructuralBindᵀ : Set₁
CandidateA-MatchedConcealStructuralBindᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {B : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → StructuralWorldExtendᴿ (bind B ∷ []) W W₁
  → CTI2.MatchedConcealPartnerOK W P c Xᴿ? V
  → CTI2.MatchedConcealPartnerOK W₁ P c
      (mapPivotChanges (bind B ∷ []) Xᴿ?) (⇑ᵗᵐ V)
```

The checked syntactic side statements are:

```agda
candidateA-notTopTag-lift : ∀ {Δ} {V : Term Δ}
  → CTI2.NotTopTag V
  → CTI2.NotTopTag (⇑ᵗᵐ V)

candidateA-name-protected-shape-target-bind :
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B : Ty Δᴿ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {Y : TyVar Δᴿ} {S : Ty Δᴿ} {V : Term Δᴿ}
    {μ : Env∼ Δᴿ} {c : μ ⊢ (＇ Y) ∼ ★}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SealPartnerOK W₁ X P R
      (mapPivotChanges (bind B ∷ []) (just Y))
      (⇑ᵗᵐ ((V ↓ seal Y S) ⟨ c ⟩))
```

Candidate A does not solve the reveal/conceal strip stop by itself.  Given the
stopped evidence for a visible target wrapper, A can only produce the lifted
visible wrapper:

```agda
candidateA-source-reveal-wrapper-output :
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B₀ : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′} {d : Conv↑ (Nat.suc Δᴿ) C B}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↑ `∀↑ d)
  → CTI2.SourceConcealPartnerOK W₁ P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?)
      (⇑ᵗᵐ (V ↑ `∀↑ d))

candidateA-source-conceal-wrapper-output :
  ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {π : Δ ↪ᵗ Δ₁} {B₀ : Ty Δᴿ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′} {d : Conv↓ (Nat.suc Δᴿ) C B}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W W₁
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↓ `∀↓ d)
  → CTI2.SourceConcealPartnerOK W₁ P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?)
      (⇑ᵗᵐ (V ↓ `∀↓ d))
```

The required strict child target is `⇑ᵗᵐ V`, not either of these lifted
wrappers.  The missing step would have to infer a partner for hidden `V` from
`plain-target not-↑` or `plain-target not-↓`; that evidence records only the
outer wrapper and says nothing about whether `V` is untagged, name-protected,
or a valid `Rep★PartnerOK` case.


Candidate B statement
---------------------

Candidate B is the relation-change surface: the partner relation records that a
target revealed/concealed `∀` wrapper reduced through a right-only allocation,
so the post-allocation child target `⇑ᵗᵐ V` keeps the wrapper partner
provenance.  The constructor types checked in the probe are:

```agda
CandidateB-SealLiftedRevealConstructorᵀ : Set
CandidateB-SealLiftedRevealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↑ (Nat.suc Δᴿ) C B}
  → CTI2.SealPartnerOK W X P R Xᴿ? (V ↑ `∀↑ d)
  → CTI2.SealPartnerOK (CTI2.rightOnlyWorld W B₀) X P R
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateB-SealLiftedConcealConstructorᵀ : Set
CandidateB-SealLiftedConcealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {R : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↓ (Nat.suc Δᴿ) C B}
  → CTI2.SealPartnerOK W X P R Xᴿ? (V ↓ `∀↓ d)
  → CTI2.SealPartnerOK (CTI2.rightOnlyWorld W B₀) X P R
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateB-SourceLiftedRevealConstructorᵀ : Set
CandidateB-SourceLiftedRevealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↑ (Nat.suc Δᴿ) C B}
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↑ `∀↑ d)
  → CTI2.SourceConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateB-SourceLiftedConcealConstructorᵀ : Set
CandidateB-SourceLiftedConcealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↓ (Nat.suc Δᴿ) C B}
  → CTI2.SourceConcealPartnerOK W P cˢ Xᴿ? (V ↓ `∀↓ d)
  → CTI2.SourceConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateB-MatchedLiftedRevealConstructorᵀ : Set
CandidateB-MatchedLiftedRevealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↑ (Nat.suc Δᴿ) C B}
  → CTI2.MatchedConcealPartnerOK W P cˢ Xᴿ? (V ↑ `∀↑ d)
  → CTI2.MatchedConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)

CandidateB-MatchedLiftedConcealConstructorᵀ : Set
CandidateB-MatchedLiftedConcealConstructorᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {P : Term Δᴸ} {A A′ : Ty Δᴸ}
    {B₀ : Ty Δᴿ} {B C : Ty (Nat.suc Δᴿ)}
    {cˢ : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {V : Term Δᴿ}
    {d : Conv↓ (Nat.suc Δᴿ) C B}
  → CTI2.MatchedConcealPartnerOK W P cˢ Xᴿ? (V ↓ `∀↓ d)
  → CTI2.MatchedConcealPartnerOK (CTI2.rightOnlyWorld W B₀) P cˢ
      (mapPivotChanges (bind B₀ ∷ []) Xᴿ?) (⇑ᵗᵐ V)
```

The constructor names bundled in the probe are:

```agda
record CandidateBConstructors : Set where
  field
    seal-lifted-reveal-target :
      CandidateB-SealLiftedRevealConstructorᵀ
    seal-lifted-conceal-target :
      CandidateB-SealLiftedConcealConstructorᵀ
    source-lifted-reveal-target :
      CandidateB-SourceLiftedRevealConstructorᵀ
    source-lifted-conceal-target :
      CandidateB-SourceLiftedConcealConstructorᵀ
    matched-lifted-reveal-target :
      CandidateB-MatchedLiftedRevealConstructorᵀ
    matched-lifted-conceal-target :
      CandidateB-MatchedLiftedConcealConstructorᵀ
```


D4.3 subsumption answer
----------------------

The D4.3 package-finalization need is already the
`StructuralCatchupRightResult.source-conceal-endpoint-partner` invariant:
it transports a `SourceConcealPartnerOK` premise through
`mapPivotChanges χs` to the package final target.  Candidate A subsumes only
the one-bind pure target-lift subcase, where the endpoint target is exactly
`⇑ᵗᵐ V` and the starting partner was already for `V`.  It does not subsume the
full package-finalization invariant, because finalization may reduce the target
to an arbitrary `N′`, not merely rename it.

For the D4.4(ii) reveal/conceal strict cells, Candidate A is insufficient
unless another strip theorem first gives partner evidence for hidden `V`.
Candidate B is the candidate that directly discharges that need, because its
premise is the visible wrapper partner that the stopped case actually has, and
its conclusion is the post-β child partner for `⇑ᵗᵐ V`.

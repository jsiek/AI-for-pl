T1 D14 concrete Lambda-source keep options
============================================

Status: statements checked; no option implemented.

Checked companion:

`proof/DGG/notes/probes/T1D14OptionsProbe.agda`

The companion is a standalone `--safe` module.  It contains only `Set` and
record declarations: no inhabitants, postulates, holes, or pragmas.  The
original checked proofs remain in:

`proof/DGG/notes/probes/T1PlainSourceKeepProbe.agda`


1. The theorem already proved
-----------------------------

These are verbatim from `T1PlainSourceKeepProbe.agda` and are restated
verbatim in the D14 statements probe:

```agda
NonΛSourceTargetRevealKeepᵀ : Set
NonΛSourceTargetRevealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → NonΛBareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


NonΛSourceTargetConcealKeepᵀ : Set
NonΛSourceTargetConcealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → NonΛBareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q
```

The inhabitants proved in that probe have exactly these signatures:

```agda
nonΛ-source-target-reveal-keep : NonΛSourceTargetRevealKeepᵀ
nonΛ-source-target-conceal-keep : NonΛSourceTargetConcealKeepᵀ
```

Thus the checked coverage is precisely a bare term lambda or a constant on
the source.  It does not claim the `Λ V` case and does not claim arbitrary
source `Value` wrappers.


2. The stuck configuration
--------------------------

The two relevant constructors, verbatim from
`proof/DGG/CastTermImprecision2.agda`, are:

```agda
  Λ⊑² : ∀ {γ′ V M A B}
      {p : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → LiftCtxᴸ X⊑★ γ γ′
    → Value V
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → liftWorldLeft X⊑★ W ∣ γ′ ⊢² V ⊑ M ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
      -------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ M ∶ q

  Λ⊑²-smart-comma :
      ∀ {Δᵐ}
      {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
      {γᵐ : CtxImp Wᵐ}
      {V : Term (Nat.suc Δᴸ)} {M : Term Δᴿ}
      {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ Wᵐ ⟩ B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → SmartCommaLiftᴸ W Wᵐ
    → SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
    → Value V
    → ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → Wᵐ ∣ γᵐ ⊢² V ⊑ M ∶ p
    → (q : `∀ A ⊑ᵂ⟨ W ⟩ B)
      -------------------------------------------
    → W ∣ γ ⊢² Λ V ⊑ M ∶ q
```

### Case 1. `Λ⊑²` at a target reveal

Matching the constructor's target `M` with `N ↑ c′` gives these actual
premises:

```agda
Anv : NonVar A
zero∈A : Fin.zero ∈ᵗ A
liftγ : LiftCtxᴸ X⊑★ γ γᴸ
vV : Value V
target⊢ :
  ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
    ⊢ N ↑ c′ ⦂ B′
prem :
  CTI2.liftWorldLeft X⊑★ W ∣ γᴸ
    ⊢² V ⊑ N ↑ c′ ∶ p
q : `∀ A ⊑ᵂ⟨ W ⟩ B′
step : (N ↑ c′) —→[ keep ] N₁
finalV : Value N₁
```

To rebuild the outer constructor after `step`, the recursive proof must
produce exactly:

```agda
body-after :
  CTI2.liftWorldLeft X⊑★ W ∣ γᴸ
    ⊢² V ⊑ N₁ ∶ p
```

The world change itself is explicit and usable: the checked theorem
quantifies over arbitrary worlds.  The evidence mismatch is the source-shape
argument.  The constructor supplies only:

```agda
vV : Value V
```

where the checked theorem requires:

```agda
NonΛBareValue V
```

There is no conversion from the former to the latter.  In particular, `V`
may itself be `Λ U`, an inert-cast value, a reveal value, or a conceal value.
The outer evidence `BareValue (Λ V)` also cannot be passed to the body call,
because it classifies `Λ V`, not `V`.

The checked residual Set is `ΛPlainTargetRevealBodyKeepᵀ` in the companion
probe.  It includes every constructor field above and has `body-after` as its
conclusion.

### Case 2. `Λ⊑²` at a target conceal

The configuration is the same with:

```agda
target⊢ :
  ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
    ⊢ N ↓ c′ ⦂ B′
prem :
  CTI2.liftWorldLeft X⊑★ W ∣ γᴸ
    ⊢² V ⊑ N ↓ c′ ∶ p
step : (N ↓ c′) —→[ keep ] N₁
body-after :
  CTI2.liftWorldLeft X⊑★ W ∣ γᴸ
    ⊢² V ⊑ N₁ ∶ p
```

This is checked as `ΛPlainTargetConcealBodyKeepᵀ`.

If the attempted recursive proof inverts `prem` through a source-conceal
head, it encounters a second, term-indexed mismatch.  For the actual
`id-conceal` keep step, the old evidence has shape:

```agda
partner-before :
  CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? (N ↓ id↓ B)
```

but rebuilding `CTI2.conceal⊑²` after stripping the target wrapper requires:

```agda
partner-after :
  CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? N
```

`partner-before` is indexed by the wrong target term.  The `seal` case of
`SourceConcealPartnerOK` inspects the target's top-tag shape, so this is not a
definitional retargeting and no current theorem transports it.

### Case 3. `Λ⊑²-smart-comma`

The smart constructor leaves the analogous goals, but at its supplied smart
world and context rather than at `liftWorldLeft`:

```agda
liftW : CTI2.SmartCommaLiftᴸ W Wᵐ
liftγ : CTI2.SmartLiftCtxᴸ γ γᵐ
vV : Value V
prem-reveal : Wᵐ ∣ γᵐ ⊢² V ⊑ N ↑ c′ ∶ p
goal-reveal : Wᵐ ∣ γᵐ ⊢² V ⊑ N₁ ∶ p
prem-conceal : Wᵐ ∣ γᵐ ⊢² V ⊑ N ↓ c′ ∶ p
goal-conceal : Wᵐ ∣ γᵐ ⊢² V ⊑ N₁ ∶ p
```

These are checked in full, including the typing, `NonVar`, occurrence, lift,
step, and value premises, as `ΛSmartTargetRevealBodyKeepᵀ` and
`ΛSmartTargetConcealBodyKeepᵀ`.  Again the usable recursive datum is only
`Value V`; it is not `NonΛBareValue V`.


3. Option (a): narrowed Lambda-source certificates
---------------------------------------------------

This option asks for only the two missing outer source shapes.  The exact
checked declarations are:

```agda
record SourceΛTargetRevealKeepCertificateᵀ : Set₁ where
  field
    source-Λ-target-reveal-keep :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
        {Aᵛ : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
        {q : `∀ Aᵛ ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
      → Value V
      → Value N
      → W ∣ γ ⊢² Λ V ⊑ N ↑ c′ ∶ q
      → (N ↑ c′) —→[ keep ] N₁
      → Value N₁
      → W ∣ γ ⊢² Λ V ⊑ N₁ ∶ q


record SourceΛTargetConcealKeepCertificateᵀ : Set₁ where
  field
    source-Λ-target-conceal-keep :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
        {Aᵛ : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
        {q : `∀ Aᵛ ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
      → Value V
      → Value N
      → W ∣ γ ⊢² Λ V ⊑ N ↓ c′ ∶ q
      → (N ↓ c′) —→[ keep ] N₁
      → Value N₁
      → W ∣ γ ⊢² Λ V ⊑ N₁ ∶ q
```

These certificates do not quantify over an arbitrary source `P`.  Their
source is definitionally `Λ V`, and their source result type is definitionally
`` `∀ Aᵛ ``.  The non-`Λ` checked theorem and these two fields cover the three
bare source constructors without resurrecting the rejected arbitrary-source
keep relation.

### Dispatcher diff implied by option (a)

The fields belong in the two outcome surfaces, not directly in
`RestatedDispatcherKeepOutcomesᵀ`.  Before, the complete reveal surface is:

```agda
record TargetRevealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-conceal-reveal :
      PairedConcealRevealPeelᵀ
    source-opened-conceal-reveal :
      SourceOnlyConcealRevealPeelᵀ
```

After:

```agda
record TargetRevealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-conceal-reveal :
      PairedConcealRevealPeelᵀ
    source-opened-conceal-reveal :
      SourceOnlyConcealRevealPeelᵀ
    plain-source-Λ :
      SourceΛTargetRevealKeepCertificateᵀ
```

The companion probe checks this after-shape as
`TargetRevealKeepOutcomeContinuationsD14aᵀ`.

Before, the conceal surface ends with:

```agda
    source-opened-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢² (V₀ ↓ id↓ A) ⊑ V₀′ ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

After, that existing field is unchanged and one field follows it:

```agda
    source-opened-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢² (V₀ ↓ id↓ A) ⊑ V₀′ ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

    plain-source-Λ :
      SourceΛTargetConcealKeepCertificateᵀ
```

The companion checks the complete before-plus-field record as
`TargetConcealKeepOutcomeContinuationsD14aᵀ`.  The outer record remains:

```agda
record RestatedDispatcherKeepOutcomesᵀ : Set₁ where
  field
    target-reveal-outcomes : TargetRevealKeepOutcomeContinuationsᵀ
    target-conceal-outcomes : TargetConcealKeepOutcomeContinuationsᵀ
```

Only the types nested in those two fields become one field wider.


4. Option (b): generalized recursive keep theorem
-------------------------------------------------

The exact generalization is from `NonΛBareValue P` to `Value P`, while
retaining universal quantification over the source context, target context,
center context, local world, and local term context:

```agda
RecursiveSourceValueTargetRevealKeepᵀ : Set
RecursiveSourceValueTargetRevealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → Value P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


RecursiveSourceValueTargetConcealKeepᵀ : Set
RecursiveSourceValueTargetConcealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → Value P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q
```

At a plain `Λ⊑²` head, the recursive call instantiates `W` with
`CTI2.liftWorldLeft X⊑★ W`, `γ` with `γᴸ`, `P` with `V`, and `q` with `p`.
At `Λ⊑²-smart-comma`, it instantiates `W` with the constructor-supplied `Wᵐ`
and `γ` with `γᵐ`.  Thus `vV : Value V` is exactly the required recursive
argument; no bare-value coercion is needed.

The proof would be an induction following the source `Value` and the exposed
`⊢²` head.  The base `ƛ` and constant cases reuse the checked non-`Λ`
inversions.  A `Λ` case recurses at the lifted or smart premise world and
rewraps with the same constructor evidence.  Source inert/reveal/conceal value
wrappers require recursive premise calls and replay of their CTI heads.  The
conceal theorem additionally needs a theorem transporting
`SourceConcealPartnerOK` from the pre-keep target term to the reduct; the exact
`partner-before`/`partner-after` mismatch above is the first concrete missing
lemma.  This option therefore has a simple surface but the broadest proof.


5. Option (c): hereditary routing through `SourceΛReplayStack`
----------------------------------------------------------------

The existing data stack already represents exactly the two Lambda heads.  The
following declaration is verbatim from
`proof/DGG/Catchup/StructuralCatchupRightDef.agda`:

```agda
data SourceΛReplayStack {Δᴸ₀ Δᴿ Δ₀}
    (W₀ : World Δᴸ₀ Δᴿ Δ₀) (γ₀ : CtxImp W₀)
    (M₀ : Term Δᴸ₀) {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    (q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀)
    : ∀ {Δᴸ Δ}
      → (W : World Δᴸ Δᴿ Δ)
      → CtxImp W
      → Term Δᴸ
      → ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → Set₁ where
  source-Λ-stack-id :
    SourceΛReplayStack W₀ γ₀ M₀ q₀ W₀ γ₀ M₀ q₀

  source-Λ-stack-plain :
    ∀ {Δᴸ Δ}
      {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
      {γᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W)}
      {U : Term (suc Δᴸ)}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ B}
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ (Λ U) q
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
    → Value U
    → SourceΛReplayStack W₀ γ₀ M₀ q₀
        (CTI2.liftWorldLeft X⊑★ W) γᴸ U p

  source-Λ-stack-smart :
    ∀ {Δᴸ Δ Δᵐ}
      {W : World Δᴸ Δᴿ Δ}
      {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
      {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
      {U : Term (suc Δᴸ)}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ Wᵐ ⟩ B}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ B}
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ (Λ U) q
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTI2.SmartCommaLiftᴸ W Wᵐ
    → CTI2.SmartLiftCtxᴸ γ γᵐ
    → Value U
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ Wᵐ γᵐ U p
```

At one target context, the existing closing lemma is also already exactly the
needed local-to-root relation map.  Its statement, verbatim, is:

```agda
source-Λ-stack-replay-here : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → ∀ {N : Term Δᴿ}
  → W ∣ γ ⊢² M ⊑ N ∶ q
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀
```

For a catch-up result whose target store has changed, the glue needed at the
keep endpoint is the existing transported version.  This statement is
verbatim from the same file and is restated as the checked Set
`SourceΛReplayTransportedKeepGlueᵀ` in the companion:

```agda
source-Λ-stack-unlift-plan : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    (stack : SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q)
    {Δᴿ′ Δ₀′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀′ : World Δᴸ₀ Δᴿ′ Δ₀′}
    (plan₀ : StructuralWorldExtendᴿ χs W₀ W₀′)
    (transported : SourceΛReplayStackTransport stack plan₀)
  → ∀ {N′ : Term Δᴿ′}
  → SourceΛReplayStackTransport.W′ transported ∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (SourceΛReplayStackTransport.current-plan transported))
        γ
      ⊢² M ⊑ N′ ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (SourceΛReplayStackTransport.current-plan transported))
          q
  → W₀′ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan₀) γ₀
      ⊢² M₀ ⊑ N′ ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan₀) q₀
```

### Exact routed obligation

Instead of asking a Λ-only supplied certificate for the outer relation, the
dispatcher carries a stack and discharges the following root-result
obligations.  Both declarations type-check in the companion:

```agda
SourceΛStackTargetRevealKeepᵀ : Set₁
SourceΛStackTargetRevealKeepᵀ =
  ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
    {N N₁ : Term Δᴿ}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N₁ ∶ q₀


SourceΛStackTargetConcealKeepᵀ : Set₁
SourceΛStackTargetConcealKeepᵀ =
  ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
    {N N₁ : Term Δᴿ}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N₁ ∶ q₀
```

The conclusion is deliberately at `W₀`, `γ₀`, `M₀`, and `q₀`; it is not the
unavailable body conclusion at `W`, `γ`, `M`, and `q`.  At a non-`Λ` bare
leaf, the existing theorem produces the local reduct relation and
`source-Λ-stack-replay-here` closes it to the root.  At a post-store-change
endpoint, `source-Λ-stack-unlift-plan` performs the same closing after
`source-Λ-stack-transport` has mapped the stack.

### Dispatcher diff sketch for option (c)

No field is added to `RestatedDispatcherKeepOutcomesᵀ`.  The private value
dispatcher becomes stack-indexed.  Its root call starts with the existing base
constructor:

```agda
source-Λ-stack-id
```

The two Λ branches change their recursive calls as follows:

```diff
- recurse prem
+ recurse
+   (source-Λ-stack-plain stack Anv zero∈A liftγ vV)
+   prem
```

and:

```diff
- recurse prem
+ recurse
+   (source-Λ-stack-smart stack Anv zero∈A liftW liftγ vV)
+   prem
```

At a target keep leaf, the local post-keep relation is routed back by the
already implemented expression:

```agda
source-Λ-stack-replay-here stack local-rel
```

or, after a target structural plan:

```agda
source-Λ-stack-unlift-plan stack plan₀ transported local-rel
```

Thus option (c) changes control flow and a private worker signature, but asks
for no new logical certificate field and no new replay theorem.


6. Trade-offs
-------------

| Option | Proof mass | Coupling | Existing rulings and checked support |
|---|---|---|---|
| (a) Lambda-only certificates | Smallest dispatcher diff; proof is deferred to the supplier of two fields. | Adds two major supplied fields to the T12 outcome family. | Uses the checked non-`Λ` theorem, D1's caller-supplied keep continuation, and T12's restated outcome records; respects issue #157 by avoiding an arbitrary-source field. |
| (b) Generalized recursive theorem | Largest relation proof: all source `Value` wrappers plus Lambda recursion; conceal needs partner transport. | Couples directly to all relevant `⊢²` source and target wrapper constructors and `SourceConcealPartnerOK`. | Extends the non-`Λ` probe result; excludes T10 Probe 3 because that source is not a `Value`, but still requires a new D14 induction ruling and likely the D15 partner-evidence repair. |
| (c) Hereditary stack routing | Medium-to-large dispatcher work; local logical proof mass is reused at leaves. | Couples the private dispatcher to `SourceΛReplayStack`, `SourceΛReplayStackTransport`, and structural plans. | Uses the LG-3v data-bearing stack ruling, D1 frame relations, T12 synchronized outcomes, and the checked non-`Λ` theorem; adds no broad keep lemma or supplied certificate. |

In short: (a) is the narrowest surface change, (b) is the cleanest standalone
theorem but the riskiest proof, and (c) keeps the logical surface unchanged at
the price of hereditary private-dispatcher plumbing.

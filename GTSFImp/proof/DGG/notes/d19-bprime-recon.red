D19 B-prime reconnaissance
============================

Date: 2026-08-19

Status: RECONNAISSANCE ONLY.  This note and its probe do not change the live
term-imprecision relation, reduction, world, store, or proof definitions.
The checked probe is
`proof/DGG/notes/probes/D19BPrimeReconProbe.agda`.


Decision under survey
---------------------

D19 has selected B-prime:

* a paired beta-instantiation mints its new center variable at `X⊑X`;
* a one-sided beta-instantiation mints its new center variable at `X⊑★`;
* whenever both terms carry the same wrapper, the two-sided relation rule is
  canonical.

“Matched” below means that both embeddings hit the center:

```agda
CenterAligned W X Y =
  toRenameᵗ (ηᴸʷ W) X ≡ toRenameᵗ (ηᴿʷ W) Y
```

A dynamic mark at a matched center is not, by itself, a B-prime violation.
It is valid when a one-sided event minted the center and the other execution
later caught up to it.  The violation is forgetting that provenance and
changing a center minted by a paired event from `X⊑X` to `X⊑★`.

Verdict vocabulary:

* **B′-SAFE**: preserves a paired mint, or writes/requires `X⊑★` only at a
  center whose one-sided provenance is established by the same interface.
* **B′-BREAKS**: the current definition demonstrably permits a paired mint to
  be changed to `X⊑★`.
* **B′-NEEDS-CHANGE**: the surface is too generic to express the distinction,
  or a proof consumer relies on a breaking transformer.


The self-contained YZ fixture and async window
----------------------------------------------

The source store has three variables and the target store has two.  With
newest variables written first, their direct entries are

```text
source: X ↦ ℕ,  Y ↦ ＇Z,  Z ↦ ★
target:          Y ↦ ＇Z,  Z ↦ ★
```

The center context has three variables.  The embeddings and B-prime marks are

```agda
ηᴸ = keep (keep (keep empty))
ηᴿ = skip (keep (keep empty))

μ Fin.zero                         = X⊑★  -- X, source-only
μ (Fin.suc Fin.zero)               = X⊑★  -- Y, one-sided alias history
μ (Fin.suc (Fin.suc Fin.zero))     = X⊑X  -- Z, paired beta-inst mint
```

Thus source/target Y meet at center 1 and source/target Z meet at center 2.
This is exactly the `left-path-world₄-precise-Z` fixture reconstructed in
`D19PairedRevealReparseProbe`; the live `Examples2.left-path-world₄-YZ`
differs only in marking Z `X⊑★`.

For the terms below define the complete wrapper vocabulary:

```text
cYᴸ = seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)
cZᴸ = seal 2 ★     ↦↑ unseal 2 ★
cYᴿ = seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1)
cZᴿ = seal 1 ★     ↦↑ unseal 1 ★
sX  = seal 0 ℕ
uX  = unseal 0 ℕ

Fᴸ = ((ƛ (` 0)) ↑ cYᴸ) ↑ cZᴸ
Fᴿ = (ƛ renameᵗᵐ (keep wk↪ᵗ) (` 0) ↑ cYᴿ) ↑ cZᴿ
aᴸ = (($ (κℕ 7) ↓ sX) ⟨ X! ⟩)
aᴿ = $ (κℕ 7) ⟨ ℕ! ⟩

iₐ = the argument-side `id ★` conversion
iᵣ = the result-side `id ★` conversion
i⇒ = iₐ ↦ iᵣ
iₜ = the target result-side `id ★` conversion
gX = the source result conversion `★ ? X`
```

The two requested out-of-phase source states and the fixed target state are
therefore, without relying on the `Examples2` names,

```text
right₅  = (((Fᴸ ⟨ i⇒ ⟩) · aᴸ) ⟨ gX ⟩) ↑ uX
right₆  = (((Fᴸ · (aᴸ ⟨ iₐ ⟩)) ⟨ iᵣ ⟩) ⟨ gX ⟩) ↑ uX
target₄ = ((Fᴿ · aᴿ) ⟨ iₜ ⟩)
```

The async window keeps the target fixed while the source takes three pure
steps:

```text
(right₄ , target₄)
  -- source beta-function pushes its outer cast
(right₅ , target₄)
  -- source beta-function pushes its second cast
(right₆ , target₄)
  -- source beta-id removes iₐ
(right₇ , target₄)
```

At `right₅`, the commented `Examples2` derivation records these interior
one-sided judgments: the paired-Z function with only source `i⇒`; the X-sealed
argument with only source `X!`; their application; then only target `iₜ`; then
only source `gX`.  At `right₆` it records: the bare paired-Z function; the
X-sealed argument with `X!` and source-only `iₐ`; their application; paired
source `iᵣ`/target `iₜ`; then source-only `gX`.  In formula order:

```text
Fᴸ ⟨i⇒⟩      ⊑ Fᴿ
aᴸ            ⊑ aᴿ
Fᴸ ⟨i⇒⟩ · aᴸ ⊑ Fᴿ · aᴿ
Fᴸ ⟨i⇒⟩ · aᴸ ⊑ (Fᴿ · aᴿ) ⟨iₜ⟩
(Fᴸ ⟨i⇒⟩ · aᴸ) ⟨gX⟩ ⊑ (Fᴿ · aᴿ) ⟨iₜ⟩

Fᴸ                 ⊑ Fᴿ
aᴸ ⟨iₐ⟩            ⊑ aᴿ
Fᴸ · (aᴸ ⟨iₐ⟩)     ⊑ Fᴿ · aᴿ
(Fᴸ · (aᴸ ⟨iₐ⟩)) ⟨iᵣ⟩ ⊑ (Fᴿ · aᴿ) ⟨iₜ⟩
((Fᴸ · (aᴸ ⟨iₐ⟩)) ⟨iᵣ⟩) ⟨gX⟩ ⊑ (Fᴿ · aᴿ) ⟨iₜ⟩
```

These are not alternative Z parses.  The D19 paired-reparse probe checks every
Z site in checkpoints 3--9 at `X⊑X`; the stale whole checkpoints 4--9 fail
earlier at the independent one-sided X conceal.  The window nevertheless
shows why preservation needs atomic peel/keep re-association: canonical
two-sided wrappers cannot describe every intermediate state after only one
program has taken its keep step.


1. Mark-transformer audit
-------------------------

The table covers the live world builders, the relations that constrain marks
between worlds, and the mark-sensitive proof transformers reached by the DGG.
Raw `world` records and hand-authored example fixtures are inputs rather than
transformers, so they are not additional rows.

| Site | File:line | Verdict | One-line reason |
| --- | --- | --- | --- |
| `liftWorldBoth v` | `proof/DGG/CtxImp.agda:78` | **B′-NEEDS-CHANGE** | Both fresh embeddings hit center zero, but the raw API accepts `v = X⊑★`; the canonical `Λ⊑Λ²` caller correctly supplies `X⊑X`. |
| `liftWorldLeft v` | `proof/DGG/CtxImp.agda:92` | **B′-SAFE** | The fresh source center is outside the target image; invariant-facing callers require `v = X⊑★`. |
| `leftOnlyWorld v` | `proof/DGG/CtxImp.agda:102` | **B′-SAFE** | Like `liftWorldLeft`, it creates only a source center; `leftOnlyWorld-invariants` requires `X⊑★`. |
| `rightOnlyWorld` | `proof/DGG/CtxImp.agda:113` | **B′-SAFE** | `instᵐ` writes `X⊑★` at a fresh target-only center and shifts every old mark unchanged. |
| `bothBindWorld v` | `proof/DGG/CtxImp.agda:123` | **B′-NEEDS-CHANGE** | The raw API accepts a dynamic matched head, although all operational paired-bind callers and `bothBindWorld-invariants` use `X⊑X`. |
| `ImpEnvMono` | `proof/DGG/CtxImp.agda:152` | **B′-BREAKS** | It constrains only old dynamic marks; hence a conclusion `X⊑X` may become premise `X⊑★` even when both embeddings still hit the center. |
| `WFWorld` / `WorldInvariants.preciseMarksAligned` | `proof/DGG/CtxImp.agda:163`, `proof/DGG/WorldInvariants.agda:48` | **B′-NEEDS-CHANGE** | They say precise implies matched but do not remember paired-mint provenance; a dynamic matched head still satisfies the live invariant. |
| paired and one-sided invariant builders | `proof/DGG/WorldInvariants.agda:296-764` | **B′-NEEDS-CHANGE** | `liftWorldBoth-invariants` accepts either mark at a matched head, whereas `liftWorldLeft`/`leftOnly` require `X⊑★` and `bothBindWorld` requires `X⊑X`; the paired lift must acquire the same canonical constraint. |
| `SmartFreshBehindGuard` mark fields | `proof/DGG/CtxImp.agda:261` | **B′-SAFE** | `fresh-not-target` proves the required dynamic head is source-only; old/target fields merely preserve already-dynamic marks. |
| `SmartAliasMergeGuard` mark fields | `proof/DGG/CtxImp.agda:293` | **B′-SAFE** | `pending-at-alias` makes the new head matched and `alias-mark-dynamic` requires `X⊑★`, but the enclosing smart-comma premise is a source-only binder event. |
| `RebaseAt` and the paired `RebaseAtᴸ`/`RebaseAtᴿ`/`TagRebaseAtᴸ` cases | `proof/DGG/CtxImp.agda:396-648` | **B′-BREAKS** | Despite the comment that the environment stays fixed, the record has no mark-equality field; it admits the checked precise-to-dynamic matched rebase `generic-rebase-decays-matched`. |
| `sameWorldRebaseAt` and the three id-rebase constructors | `proof/DGG/CtxImp.agda:409-431`, `:615`, `:644` | **B′-SAFE** | Their source and destination world are definitionally the same, so every mark is unchanged. |
| `rebase-onlyᴸ` / `tag-rebase-onlyᴸ` | `proof/DGG/CtxImp.agda:441`, `:623` | **B′-SAFE** | Each requires `X⊑★` only together with an explicit proof that no target embedding hits the source center, so the center cannot be matched. |
| `EnvDecay` / `decay⊑ᵂ` | `proof/DGG/WorldDecay.agda:81` | **B′-BREAKS** | Stores and embeddings are equal while the embedded `ImpEnvMono` may erase any paired precise mark. |
| `blendWorld` | `proof/DGG/WorldDecay.agda:145` | **B′-BREAKS** | At a precise cell in its first world it imports the second world's mark without checking matched-center provenance. |
| `honestEnv` / `honestify` | `proof/DGG/WorldDecay.agda:207` | **B′-SAFE** | It preserves every target-occupied center, hence every matched center, and dynamizes only centers outside the target image. |
| `renameEnv` / `renameWorld` | `proof/DGG/CenterRename.agda:317`, `:348` | **B′-SAFE** | Image marks are copied exactly; `X⊑★` is written only outside the shared renamed image, where neither endpoint can be matched. |
| `dynWorld` | `proof/DGG/SealPeelToolkit.agda:170` | **B′-BREAKS** | It writes `X⊑★` at every center while preserving both embeddings, including paired matched centers. |
| `decay-invariants`, `blendWorld-invariants`, `dynWorld-invariants` | `proof/DGG/WorldInvariants.agda:887-965` | **B′-NEEDS-CHANGE** | These validate the breaking decay family using only the older star-source occupancy side condition, which does not distinguish paired from one-sided provenance. |
| `honestify-invariants`, `renameWorld-invariants`, `targetInsert-invariants` | `proof/DGG/WorldInvariants.agda:784`, `:935`, `:1020` | **B′-SAFE** | Their underlying transformations preserve matched marks; the invariant proofs add no matched-center `X⊑★` requirement. |
| `TargetInsert.impEnv-insert` / `impEnv-off-insert` | `proof/DGG/TargetExtend.agda:76` | **B′-SAFE** | Image marks are equal; off-image marks are dynamic, and `target-source-reflect` prevents a newly matched source/target pair from hiding off the old image. |
| `smartAliasInsertWorld` plus alias `smartStar` | `proof/DGG/TargetExtend.agda:894`, `:1082` | **B′-SAFE** | Rename preserves inherited marks; the `Fin.zero` `smartStar` case uses the source-only alias mint, and the tail uses `old-star` only to preserve an existing dynamic mark. |
| `smartFreshInsertWorld` plus fresh `smartStar` | `proof/DGG/TargetExtend.agda:1243`, `:1482` | **B′-SAFE** | The fresh head is proved outside the target image; `old-star` at line 1514 transports only inherited dynamic marks. |
| `insertRebaseWorld` | `proof/DGG/TargetExtend.agda:1688` | **B′-SAFE** | It renames premise marks exactly; any inserted off-image target center has one-sided target-allocation provenance before a later rebase can meet it. |
| `ΛLiftToBindFreshWorld` / `ΛLiftToBindFreshWorldᴸ` | `proof/DGG/TargetBindLift.agda:75`, `:88` | **B′-NEEDS-CHANGE** | Their middle `v` is a matched slot; live route-one callers use `X⊑★` only after erasing the paired `Λ⊑Λ²` head, while the surrounding `instᵐ` slots are genuinely one-sided. |
| `TargetStoreMove` / `targetStoreAs` | `proof/DGG/TargetBindLift.agda:180`, `:456` | **B′-SAFE** | Both require pointwise mark equality and therefore cannot decay a paired mark. |
| `TargetBindLiftMove.target-pivot-star` | `proof/DGG/TargetBindLift.agda:370` | **B′-NEEDS-CHANGE** | The pivot may be matched, so the unconditional `X⊑★` premise needs one-sided provenance or a separate precise paired branch. |
| `liftTargetBindMove*`, `smartAliasPivotStar`, `smartFreshPivotStar` | `proof/DGG/TargetBindLift.agda:421-583` | **B′-SAFE** | These preserve an existing pivot-star obligation and do not choose a new mark; the alias-β case inherits the source-only smart-alias mint. |
| `liftBothBinderDecay` | `proof/DGG/TermImpDecay.agda:50` | **B′-BREAKS** | This is the explicit witness from `liftWorldBoth X⊑X W` to the identical matched world marked `X⊑★` at its new head. |
| smart-guard decay (`decaySmartFreshBehindGuard`, `decaySmartAliasMergeGuard`) | `proof/DGG/TermImpDecay.agda:155`, `:232` | **B′-BREAKS** | Both replace the complete smart premise by `dynWorld Wᵐ`, erasing every paired mark inherited inside it. |
| `lowerLiftWorldLeft` | `proof/DGG/Inversion/TargetStripProof.agda:309` | **B′-SAFE** | It drops the one-sided head and copies every tail mark exactly; its reconstructed lifted head is again source-only `X⊑★`. |
| `ΛPostMidWorld` | `proof/DGG/Catchup/InstInversionLambdaProof.agda:427` | **B′-NEEDS-CHANGE** | Three `instᵐ`s make its source head match a target center dynamically; the route is currently fed by `liftBothBinderDecay`, not a one-sided mint certificate. |
| `ΛRouteOneFreshWorldAt` / `ΛRouteOneMidWorldAt` | `proof/DGG/Catchup/InstInversionLambdaProof.agda:1031`, `:1056` | **B′-NEEDS-CHANGE** | They preserve route-one allocation marks, but their live input contains `liftWorldBoth X⊑★`; the paired slot must remain precise while genuinely one-sided window slots stay dynamic. |
| the eight `ImpEnvMono` premises in `⊑reveal²`, `⊑conceal²`, `reveal⊑²`, both `conceal⊑²` rules, `reveal⊑reveal²`, `conceal⊑conceal²`, and `packaged-seal-star²` | `proof/DGG/CastTermImprecision.agda:177-296` | **B′-NEEDS-CHANGE** | Every wrapper constructor accepts the breaking generic star-map; B′ needs a provenance-preserving/matched-preserving transformer, with canonical two-sided rules retaining paired heads. |
| `ImpEnvMono` rename/move/insert and strip/walk/catchup consumers | `proof/DGG/CenterRename.agda:760`, `proof/DGG/TargetBindLift.agda:241`, `proof/DGG/TargetExtend.agda:2568`, `proof/DGG/Catchup/StructuralWorldExtendDef.agda:171-290` | **B′-NEEDS-CHANGE** | These are parametric transports of the same generic relation, not independent mark writers; each must transport whatever provenance-preserving replacement the eight rules use. |
| `CompileImageWorld` mint constructors | `proof/DGG/GroundingMint.agda:49` | **B′-SAFE** | The compile image already distinguishes `liftWorldBoth X⊑X` from `liftWorldLeft X⊑★` exactly as B′ requires. |

The probe checks the cheap positive and negative rows directly:
`generic-mono-decays-matched`, `generic-env-decay-decays-matched`,
`blend-decays-matched`, `dyn-world-decays-matched`,
`honestify-keeps-matched`, `dynamic-lift-passes-live-invariants`,
`generic-rebase-decays-matched`, the builder head/occupancy facts,
`paired-binder-decay`, rename preservation, target-store preservation, and the
smart guard geometry.

The operationally decisive break is not merely the permissive raw builder.
`Λ⊑Λ²-route1-entry-p` in
`Catchup/InstInversionLambdaProof.agda:105-127` starts from the paired body
world `liftWorldBoth X⊑X W`, applies a target insertion with `v = X⊑X`, and
then invokes `liftBothBinderDecay` to obtain `liftWorldBoth X⊑★ ...`.  Under
B-prime that exact middle step must disappear or be replaced by an async
re-association that keeps the paired head precise.


2. Smart-alias recheck (F2)
--------------------------------

| Site | Sidedness and matchedness | B′ verdict | Exact consequence |
| --- | --- | --- | --- |
| `Λ⊑²-smart-comma` selects `SmartCommaLiftᴸ` | Source-only: the source has the pending binder while the target term/context is unchanged. | **B′-SAFE** | The event mints `X⊑★`, as required for a one-sided beta-instantiation. |
| `SmartAliasMergeGuard.pending-at-alias` + `alias-mark-dynamic` | The new source `Fin.zero` is matched with existing target `β`, and that center is required to be `X⊑★`. | **B′-SAFE** | Matching happens by catching the source up to a target alias center; it does not retroactively turn the original one-sided mint into a paired mint. |
| Alias `old-star` in `smartAliasGuardInsert` | `TargetExtend.agda:1099` reflects an already-dynamic inserted old center back to `W`; it is not the pending head. | **B′-SAFE** | No mark is minted or decayed; the premise remains `impEnvʷ W Z ≡ X⊑★`. |
| Fresh `old-star` in `smartFreshGuardInsert` | `TargetExtend.agda:1514` is the analogous inherited-tail fact; the fresh head is separately proved unmatched. | **B′-SAFE** | No change under B′. |
| Alias/fresh `smartStar Fin.zero` | Alias uses `alias-mark′`; fresh uses `fresh-mark′`; both establish `＇center ⊑ ★` for transport out of `liftWorldLeft X⊑★ W′`. | **B′-SAFE** for the live one-sided constructor. | Both proofs continue to close unchanged when generic decay is not invoked. |
| Counterfactual paired smart-alias constructor | Both terms would carry the binder wrapper, so the new matched center would be a paired mint. | **B′-NEEDS-CHANGE** | `alias-mark-dynamic` would have to become `impEnvʷ Wᵐ (toRenameᵗ (ηᴿʷ W) β) ≡ X⊑X`; the current `smartStar Fin.zero = X⊑★ alias-mark′` would then fail, so the surrounding proof would need a `liftWorldBoth X⊑X` transport mapping the two fresh variables to each other rather than mapping the source variable to `★`. `name-mark-dynamic` and inherited `old-star` facts need not change. |

The live alias-creation site is therefore one-sided.  No F2 change is needed
for B-prime itself.  The probe lemmas `smart-alias-pending-matched` and
`smart-alias-pending-mark-dynamic` check the apparently paradoxical pair of
facts, and `smart-fresh-pending-unmatched` checks the other smart branch.


3. Async-window lemma inventory
--------------------------------

The B-prime preservation proof needs four narrow continuation statements to
cross one async keep window while retaining canonical two-sided rules.  These
are statements only; this reconnaissance neither proves nor postulates them.

| Statement | Role in one async window | Existing equivalent | Counterexample status |
| --- | --- | --- | --- |
| `PairedConcealRevealPeelᵀ` | When both endpoints still carry matching seal/unseal wrappers, consume both keep steps atomically and return the payload relation at the same `q`. | Exact live statement in `proof/DGG/SimConcealRevealPeel.agda:22`; packaged, but not inhabited, by `Catchup/LeftSourceOperationsDef.agda:211`. `SealPeelToolkit` has no relation-level equivalent. | Not refuted. `T10Probe3TargetKeepSameQ` refutes taking only the target step; its checked `after-both-peel-same-q` is this endpoint shape. |
| `SourceOnlyConcealRevealPeelᵀ` | After the target keep happened first, use explicit evidence of that opening and consume the remaining source keep without reconstructing an impossible sealed target relation. | Exact live statement in `proof/DGG/SimConcealRevealPeel.agda:49`; packaged, but not inhabited, by `Catchup/LeftSourceOperationsDef.agda:211`. No `SealPeelToolkit` equivalent. | Not refuted. `T10Probe2SourceRevealStillSealed` refutes the weaker version with a still-sealed target; `TargetOpenedByConcealReveal` excludes it. |
| `PairedIdConcealPeelᵀ` | When both endpoints carry identity conceal wrappers, consume both `id-conceal` keep steps atomically. | Statement-equivalent field only in `notes/probes/T12TwoSidedPeelRestatementProbe.agda:336`; `Catchup/StructuralFrameOutcomeProof.agda:53` classifies each runtime step but does not peel the relation. No `SealPeelToolkit` equivalent. | No existing counterexample refutes these assumptions. |
| `SourceOpenedIdConcealPeelᵀ` | After the target identity conceal has already stepped, consume the remaining source `id-conceal` wrapper and return the payload relation. | Statement-equivalent field only in `notes/probes/T12TwoSidedPeelRestatementProbe.agda:351`; runtime classification alone exists in `Catchup/StructuralFrameOutcomeProof.agda:53`. No `SealPeelToolkit` equivalent. | No existing counterexample refutes these assumptions. |

Here are the full statements checked against the current live definitions.

### `PairedConcealRevealPeelᵀ`

```agda
PairedConcealRevealPeelᵀ : Set
PairedConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

### `TargetOpenedByConcealReveal`

This is genuine evidence used by the next statement, not an abbreviation for
part of its conclusion.

```agda
record TargetOpenedByConcealReveal {Δᴿ : TyCtx}
    (N : Term Δᴿ) (X : TyVar Δᴿ) (R′ : Ty Δᴿ)
    (V′ : Term Δᴿ) : Set where
  field
    opened-value : Value V′
    opened-step :
      ((N ↓ seal X R′) ↑ unseal X R′) —→[ keep ] V′
```

### `SourceOnlyConcealRevealPeelᵀ`

```agda
SourceOnlyConcealRevealPeelᵀ : Set
SourceOnlyConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {N′ V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → TargetOpenedByConcealReveal N′ Xᴿ R′ V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ V₀′ ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

### `PairedIdConcealPeelᵀ`

```agda
PairedIdConcealPeelᵀ : Set
PairedIdConcealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢² (V₀ ↓ id↓ A) ⊑ (V₀′ ↓ id↓ B) ∶ q
  → (V₀ ↓ id↓ A) —→[ keep ] V₀
  → (V₀′ ↓ id↓ B) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
```

### `SourceOpenedIdConcealPeelᵀ`

```agda
SourceOpenedIdConcealPeelᵀ : Set
SourceOpenedIdConcealPeelᵀ =
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

No statement asks for either counterexample endpoint
`source-revealed ⊑ target-sealed` or
`source-revealed ⊑ target-payload` after only the target step.  That is the
essential narrowing inherited from T12.


Checked artifacts
-----------------

Focused probe command:

```text
PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH \
  agda --safe -v0 -i . -i proof/DGG/notes/probes \
  proof/DGG/notes/probes/D19BPrimeReconProbe.agda
```

Result: exit 0.

Repository-wide final gate:

```text
cd GTSFImp && \
  PATH=/tmp/claude-26597/-home-runner-AI-for-pl/47ee78a9-f010-4f54-9a3a-aed5287dbe12/scratchpad/agda28/bin:$PATH \
  make check
```

Result: exit 0 on 2026-08-19.

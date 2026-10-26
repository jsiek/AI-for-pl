# DGG: the MAJOR statements, consolidated (D31)

Status: 2026-10-09, for review.  The 26 MAJOR statements of the
2026-10-04 consolidation are re-derived for design.md **D31** (adopted
2026-10-09, commit 075c0a81): no `πʷ`; the openings are SLOTS of the
index `A ⊑ᵂ⟨ W ⟩[ O ] A′`; one `cast⊑` with `CastOpen`; `Λ⊑` with
`Bind` (fresh, join, claim-rep); boundary permissions `K ⊆ JoinRep`,
"the join pays"; R1′; no grants.  None of these statements is
approved.  The Agda text is `proof/DGG/drafts/StatementsCore.agda`,
which checks with `agda --safe -v0` (from `GTNF/agda`).  Each block
below is copied from that file.  LEFT is the more precise side.  The
INLINE statements of `drafts/Statements.agda` are NOT updated to D31
(they are text; §6 lists the D31 INLINE helpers).

The Wrap- and Merge-specific statements are PLACEHOLDERS (§5): another
worker is changing the relation for them (JoinRep for rebound type
variables; κ-weakening at Wrap).

## 0. Overview

### 0.1 The table

| # | statement | D31 | why |
|---|---|---|---|
| M1 | `MorSide` | REVISE | (a) at any slots; (e) `Opens` gone; new (e) `Bind`, (f) `JoinRep`, (g) `SlotOK`, (h) R1′ `UnbindOK` |
| M2 | `MorImp` | REVISE | at any slots `O` (its induction goes under slotted premises) |
| M3 | `EvolveMor` | KEEP | text unchanged; `WorldMor` now carries κ exactly (`mor-κ`), no raised marks |
| M4 | `EvolveInterior` | KEEP | `Wᵢ +κ K` evolves as `Wᵢ` (INLINE `+κ-evolve`) |
| M5 | `WfWorld-bind` | REVISE | `W ⊕ m` is gone: `W ⊕²` and the three `Bind` cases |
| M6 | `InteriorMerge` | REVISE | the inner boundary sits in the outer's premise world `Wᵢ +κ K` |
| M7 | `MergeConvWorld` | KEEP | conversions read the exterior world |
| M8 | `PayloadImp` | KEEP | |
| M9 | `RunReplay` | KEEP | |
| M10 | `EvolveReplay` | KEEP | |
| M11 | `SubstImp` | KEEP | substitution stops at (closed) boundaries |
| M12 | `InstXImp2` | REVISE | `W ⊕ m` → `W ⊕²` (no mark to choose) |
| M13 | `InstXImpL` → `InstXBind` | REVISE | at any slots; the outcome is a `Bind` (or a skip used up, `W ⊕ᴸ`); absorbs D27's `PopInstX` |
| M14 | `MergeImp` | KEEP | (R2 in the MIXED cases, D28 note) |
| M15 | `RightMergeOpens` → `RightMergeSlots` | REVISE | `Opens` → `Push`/`SlotOK`/`JoinRep`/pay, as `⊑⟪⟫`'s premises |
| M16 | `SimApp` | KEEP | Wrap needs P1 (κ-weakening) |
| M17 | `SimCast` | KEEP | |
| M18 | `SimBdy` | KEEP | Merge needs P2 |
| M19 | `SimBackApp` | KEEP | `castfun-grant` gone; Wrap needs P1 |
| M20 | `SimBackCast` | KEEP | Inst through PushInstR; TagUntag's drop lemma gone |
| M21 | `SimBackBdy` | KEEP | ⊑⟪⟫ × Merge through RightMergeSlots |
| M22 | `SimBackBlame` | KEEP | C1–C5, C4g dead at κ = [] |
| M23 | `CatchupRightᴳ` | DROP | the left of CatchupRight is always a VALUE now (no `Opens` image); replaced by `CatchupRightO` |
| M24 | `CatchupCast` | REVISE | at any slots and permissions (a frame of CatchupRightO) |
| M25 | `CatchupBdy` | REVISE | at any slots and permissions |
| M26 | `CastRedexNoBlame` | REVISE | at any slots and permissions (Q1) |
| N1 | `CatchupRightO` | NEW | CatchupRight at any slots and permissions; replaces M23 and D27's `CatchupRightπ` |
| N2 | `PushInstR` | NEW | the right's Inst + TyBeta against a left value: a new opening, K ⊆ [0], the join pays |
| G1–G3 | `Simκ`, `SimBackκ`, `CatchupLeftκ` | NEW (Def generalization) | the `…κ` holes are the IH at `Wᵢ +κ K`, K ≠ [] (Q1) |
| P1 | `KappaWeaken` | PLACEHOLDER | the Wrap work (other worker) |
| P2 | `MergePermit` | PLACEHOLDER | the Merge/JoinRep work (other worker) |

**Count.**  26 − 1 (M23) + 2 (N1, N2) = 27 MAJOR, plus three Def
generalizations (G1–G3, pending Q1) and two placeholders (P1, P2).

**Dropped with D31 (beyond M23).**  Everything about `Opens` and
pending type variables: MorSide (e) (`instX-ren`), `PendingMor`, `MorImpπ`,
`CatchupRightπ`, `PopInstX` (now InstXBind's join outcome),
`RightMergePending` (now RightMergeSlots), `WfPop` (the `SlotOK`
premise of `⊑⟪⟫`), `PushCompose` (INLINE in RightMergeSlots), MarkMono
and the raised marks of `WorldMor` (marks are computed from κ; κ moves
exactly), `castfun-grant`/R12 at CastFun, and TagUntag's drop lemma.

### 0.2 What changed in the definitions

- `Pre W` = `WfCtx Δ × WfCtx Δ′ × WfWorld W × κʷ W ≡ []` (no `πʷ`).
  `Preκ W` drops `κʷ W ≡ []`; the catch-up family is stated at `Preκ`
  (Q1).
- `WorldMor ρ ρ′`: the field `mor-μ` (raised marks) is replaced by
  `mor-κ : κʷ W₁ ≡ map ρ′ (κʷ W)`.  Growing κ is not a morphism: R1′
  and R2 are anti-monotone in κ.  It is P1.
- Slots are positions of the RIGHT context's type variables; rep. var
  renamings and allocations move none, so every transport keeps `O`.
- `CatchupRightConclO … O`: CatchupRight's conclusion at slots `O`.

### 0.3 Dependency tree

`→` means "its proof uses"; brackets: approved; parentheses: INLINE;
`↺`: a recursive call on a derivation that is not a subderivation.

```
[DGG] → [Sim*] → [Sim]=Simκ → SimApp, SimCast, SimBdy, [CatchupRight]
                    (SimTyBeta, SimCast-ToBlame, frames)
        [SimBack*] → [SimBack]=SimBackκ → SimBackApp, SimBackCast,
                    SimBackBdy, SimBackBlame, WfWorld-bind,
                    [CatchupLeft]=CatchupLeftκ, [CatchupBlame]
                    (SimBackTyBeta, frames, SimBackValueO → CatchupRightO)

SimApp, SimBackApp → SubstImp, [CatchupRight] / [CatchupLeft], P1 (Wrap)
SimCast → [CatchupRight]
SimBackCast → [CatchupLeft], PushInstR, (TyBetaSync2)
SimBdy, SimBackBdy → InteriorMerge, MergeConvWorld, MergeImp, P2,
                     RightMergeSlots (SimBackBdy)
SimBackBlame → [CatchupBlame], [CatchupLeft], CastRedexNoBlame
(SimTyBeta, SimBackTyBeta) → InstXImp2, InstXBind, MorImp, PayloadImp
(frames) → EvolveMor, MorSide, EvolveInterior, MorImp;
           ·₂ also RunReplay, EvolveReplay

[EvolveImp] → EvolveMor, MorImp
MorImp → MorSide, WfWorld-bind
SubstImp → MorImp, [ImprecisionTyping]
InstXImp2, InstXBind → MorImp, WfWorld-bind
MergeImp → WfWorld-bind          RightMergeSlots → InteriorMerge, P2

[CatchupRight] = CatchupRightO at O = [], κ = []
CatchupRightO → CatchupCast, CatchupBdy, WfWorld-bind, EvolveMor,
                MorSide, MorImp, EvolveInterior   (frames)
CatchupCast → CastRedexNoBlame, ↺CatchupCast, CatchupBdy,
              PushInstR then ↺CatchupRightO
CatchupBdy → MergeImp, InteriorMerge, MergeConvWorld,
             RightMergeSlots, P2, ↺CatchupBdy
```

**The catch-up cycle** is the old one with `CatchupRightᴳ` replaced:

```
CatchupRightO → (cast frames) → CatchupCast →(Inst, PushInstR) CatchupRightO
```

on the slotted premise that PushInstR creates (the InstX image under
the new opening), plus the self-loops `CatchupCast ↺` and
`CatchupBdy ↺`.  The measure is unchanged (§0 of the 2026-10-04
version): `ι` (the `instᵖ` nodes of the right term's coercions), then
the coercion size, then the boundary count, then the derivation.  The
re-entry after Inst is compared with the term before the Inst, where
`ι` has dropped.  Not checked in Agda.

## 1. Fit check

Against the skeletons as they are now (each checks with holes
allowed): SimProof 50 holes, SimBackProof 50, CatchupRightProof 11.
Checked in Agda: `notes/D31StatementsFit.agda` (no holes, no
postulates) derives the approved CatchupRight, Sim, SimBack and
CatchupLeft from G1–G3/N1, closes the argument of the three
`CatchupRightκ` holes and of the `CatchupRightO` hole as calls of
`CatchupRightO` (with the INLINE `slotOK-+κ`: `SlotOK` reads no κ, but
not definitionally), the two `WfWorld (W ⊕ᴸ)` holes and claim-rep's
`WfWorld (W ⊕ᴸ⇔ β)` by `WfWorld-bind`, and builds PushInstR's
evolution `W ⟿[ [] ∣ none ∷ new ★ ∷ [] ] allocᴿ ★ W`.  The rest of
the mapping is by reading (the 2026-10-04 adapters were not re-run).

### SimProof (50)

| holes | n | closed by |
|---|---|---|
| SimBeta-Beta, SimBeta-Wrap, SimCast-CastFun | 3 | SimApp (Wrap into a permitting boundary: P1) |
| SimCast-{CastId, CastSeq, CastSeq?, Inst, TagUntag} × {cast⊑cast, cast⊑} | 10 | SimCast |
| SimBoundary-{Merge, Id, IdDyn, IdDynVar} × {⟪⟫⊑⟪⟫, ⟪⟫⊑} | 8 | SimBdy (Merge of a permitting boundary: P2) |
| SimCast-ToBlame | 14 | INLINE C14 |
| SimFrame-{·₁, ·₂, cast, cast⊑, ⊑cast, ν, ν⊑, ⟪⟫, ⟪⟫⊑, ⊑⟪⟫} | 10 | INLINE frames |
| SimTyBeta (ν⊑ν, ν⊑) | 2 | INLINE: ν⊑ν by InstXImp2, PayloadImp, MorImp, TyBetaSync2 (K ≠ []: P1); ν⊑ by InstXBind, PayloadImp, MorImp |
| **SimFrame-⟪⟫κ, -⟪⟫⊑κ, -⊑⟪⟫κ** | 3 | **uncovered without G1 `Simκ` (Q1)**; with it, the frame plus `+κ-evolve`, MorSide (f) |

### SimBackProof (50)

| holes | n | closed by |
|---|---|---|
| SimBackBeta-Beta, -Wrap, SimBackCast-CastFun | 3 | SimBackApp (Wrap: P1) |
| SimBackCast-{CastId, CastSeq, CastSeq?, Inst, TagUntag} × {cast⊑cast, ⊑cast} | 10 | SimBackCast (Inst: PushInstR, or TyBetaSync2 when the left also Insts) |
| SimBackBoundary-{Merge, Id, IdDyn, IdDynVar} × {⟪⟫⊑⟪⟫, ⊑⟪⟫} | 8 | SimBackBdy (⊑⟪⟫ × Merge: RightMergeSlots; P2) |
| SimBackCast-ToBlame | 11 | SimBackBlame |
| SimBackFrame-{·₁, ·₂, cast, cast⊑, ⊑cast, Λ⊑, ν, ν⊑, ⟪⟫, ⟪⟫⊑, ⊑⟪⟫} | 11 | INLINE frames |
| SimBackFrame-Λ⊑⇔ (claim-rep) | 1 | INLINE: WfWorld-bind (`b-rep`, checked), `unliftᴸ⇔`, EvolveMor |
| SimBackFrame-⊑⟪⟫ with new slots | 1 | INLINE SimBackValueO: the left is a value, so CatchupRightO on the slotted premise, Determinism, EvolveInterior, rebuild `⊑⟪⟫` (MorSide (a), (f), (g)) |
| SimBackTyBeta | 1 | INLINE: CatchupLeft, the left's TyBeta, TyBetaSync2 (K ≠ []: P1) |
| WfWorld (W ⊕ᴸ) | 1 | WfWorld-bind (checked) |
| **SimBackFrame-⟪⟫κ, -⟪⟫⊑κ, -⊑⟪⟫κ** | 3 | **uncovered without G2 `SimBackκ` (Q1)** |

### CatchupRightProof (11)

| holes | n | closed by |
|---|---|---|
| CastTail (cast⊑cast, ⊑cast) | 2 | CatchupCast, after `ξ-cast*`; CastTy and q by EvolveMor, MorSide (a) |
| BdyTail (⟪⟫⊑⟪⟫, ⊑⟪⟫) | 2 | EvolveInterior, MorSide (a)–(c), then CatchupBdy |
| BdyLift (⟪⟫⊑) | 1 | EvolveInterior, MorSide (a), (b), (h) |
| WfWorld (W ⊕ᴸ) | 1 | WfWorld-bind (checked) |
| CatchupRight-claim-rep | 1 | WfWorld-bind (`b-rep`, checked), INLINE `unliftᴸ⇔`, EvolveMor + MorImp |
| CatchupRightκ (×3) | 3 | CatchupRightO as the IH (checked), then BdyTail/BdyLift with `+κ-evolve`, MorSide (f) |
| CatchupRightO (⊑⟪⟫ with new slots) | 1 | CatchupRightO as the IH (checked), EvolveInterior, rebuild `⊑⟪⟫` (Push unchanged, MorSide (a), (f), (g)), then CatchupBdy at slots |

So CatchupRightProof is closed only as the proof of **CatchupRightO**
(Q3): its κ and slot holes are its own IH, and its module parameter
EvolveImp (stated at κ = []) is replaced by EvolveMor and MorImp.

### Gaps

1. **The six `…κ` holes of Sim and SimBack** need the Defs at any κ
   (G1, G2, and G3 for SimBack's ·₂ frame).  That is Q1.
2. **P1** (Wrap into a permitting boundary; a K ≠ [] chosen by the
   matched TyBeta).  PushInstR may avoid it (Q2).
3. **P2** (Merge when a boundary permits; the merged boundary's payment
   needs the inner interior index without the outer K).
4. **INLINE `SlotOK-⟪⟫⊑`**: a slot that `⟪⟫⊑ bo-∀` passes into the
   left boundary's interior must stay `SlotOK` there (needed by
   WfWorld-bind for a join under a pass, in InstXBind and
   CatchupRightO).  Argued, not checked: `RightOnly` and
   `NoNamedPartner` could fail only if the left boundary rejoined the
   opening's β, and then `Join1`'s `skip` contradicts
   `Interior.join-fresh`.
5. **CastRedexNoBlame and SimBackBlame at κ ≠ []**: C1–C4g are proved
   dead at κ = [] only (`notes/D28pD30.md` §5).  CatchupRightO uses
   CastRedexNoBlame at any κ (Q1).

## 2. Transports and worlds

### M1 `MorSide` — REVISE
```agda
MorSide : Set
MorSide = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
  → WorldMor ρ ρ′ W W₁
    -- (a) the index, at any slots
  → (∀ {A A′ O} → A ⊑ᵂ⟨ W ⟩[ O ] A′ → A ⊑ᵂ⟨ W₁ ⟩[ O ] A′)
    -- (b) interior worlds (the boundary rules)
    × (∀ {Δᵢ Δ′ᵢ} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
         → WfWorld W₁
         → Interior W Θ Θ′ Wᵢ
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
             Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁
             × WorldMor ρ ρ′ Wᵢ Wᵢ₁ × AllAgree Wᵢ₁
             × (WfWorld Wᵢ → WfWorld Wᵢ₁))
    -- (c) the conversion premise of ⟪⟫⊑⟪⟫ (R2 reads κ and ϱ: exact)
    × (∀ {Δᵢ Δ′ᵢ Θ Θ′ c c′ Aᵢ A′ᵢ A A′}
         (b : BdyTy Δ Θ Δᵢ Aᵢ c A) (b′ : BdyTy Δ′ Θ′ Δ′ᵢ A′ᵢ c′ A′)
         → BdyConversionImp W b b′
         → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ]
           Σ[ b₁ ∈ BdyTy Δ₁ (renᴮᴿ ρ Θ) Δᵢ₁ Aᵢ c A ]
           Σ[ b₁′ ∈ BdyTy Δ′₁ (renᴮᴿ ρ′ Θ′) Δ′ᵢ₁ A′ᵢ c′ A′ ]
             BdyConversionImp W₁ b₁ b₁′)
    -- (d) the conversion premise of ν⊑ν
    × (∀ {A A′ C C′ c c′ B B′}
         (n : NuTy Δ A C c B) (n′ : NuTy Δ′ A′ C′ c′ B′)
         → NuConversionImp W n n′
         → Σ[ n₁ ∈ NuTy Δ₁ A C c B ] Σ[ n₁′ ∈ NuTy Δ′₁ A′ C′ c′ B′ ]
             NuConversionImp W₁ n₁ n₁′)
    -- (e) Λ⊑'s binder (fresh, join, claim-rep); the left's new rep.
    -- var 0 is renamed by `extᵗ ρ`, claim-rep's β by ρ′
    × (∀ {W⁺ : World (underΛ Δ) Δ′} {O O₁}
         → Bind W O W⁺ O₁
         → Σ[ W₁⁺ ∈ World (underΛ Δ₁) Δ′₁ ]
             Bind W₁ O W₁⁺ O₁ × WorldMor (extᵗ ρ) ρ′ W⁺ W₁⁺)
    -- (f) the permissions a boundary may choose (W read as its
    -- interior world)
    × (∀ {Θ Θ′ N β}
         → JoinRep W Θ Θ′ N β
         → JoinRep W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) N (ρ′ β))
    -- (g) well-formed slots
    × (∀ {s} → SlotOK W s → SlotOK W₁ s)
    -- (h) R1′
    × (∀ {A Θ} → All (UnbindOK W A) Θ → All (UnbindOK W₁ A) (renᴮᴿ ρ Θ))
```
- **Intent.**  The world-level side premises move along any world
  morphism: the index at any slots, the interior world, the two
  conversion premises (R2 reads κ and ϱ, which move exactly), Λ⊑'s
  `Bind`, a boundary's `JoinRep`, `SlotOK`, and R1′'s `UnbindOK`.
- **Consumers.**  MorImp (every rule with a side premise).  Through
  EvolveMor, every frame of Sim, SimBack and CatchupRightO, including
  the rebuilt `⊑⟪⟫` with new slots (f, g) and the `…κ` frames (f).
- **Plan.**  (a) induction on `O` (`OpenO`), at the end
  `renameᵗ-cong` on `mor-ηᴸ`/`mor-ηᴿ` and `permit (ρ′ β) (map ρ′ κ) =
  permit β κ` (ρ′ injective, from `RepWk`).  (b) as before.  (e) by
  cases on `Bind`: `b-join` maps `Join↪` unchanged (positions) and
  `Δ′ ∋ᵗ k := β` to `ρ′ β`; `b-rep` renames β.  (f) `jr-join` by (b)'s
  `Joins`, `jr-open` by positions.  (g) `OpeningOK` field by field.
  (h) `Unpermitted` by `mor-paired` and `mor-κ`.

### M2 `MorImp` — REVISE
```agda
MorImp : Set
MorImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {O : List Slot} {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → WorldMor ρ ρ′ W W₁
  → WfWorld W₁
  → SameTys W W₁ γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩[ O ] A′ ]
      (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶⟨ A , A′ ⟩[ O ] q)
```
- **Intent.**  `⊑` moves along a world morphism, at any slots.  At an
  allocation it is A1 (AllocImp), at `rm-refine` B8 (RefineImp).
- **Consumers.**  EvolveImp (a corollary).  SubstImp (`crossΛᴹ`).
  InstXImp2, InstXBind (refinement into the TyBeta interior).  The
  `·₂` frames.  CatchupRightO's frames (in place of EvolveImp).
- **Plan.**  Induction on `⊑`.  Binders: `Bind` by MorSide (e), `⊕²`
  by `extᵗ`; boundaries: MorSide (b), (f), (h), and `Wᵢ +κ K` ↦
  `Wᵢ₁ +κ map ρ′ K` (INLINE `mor-+κ`); `cast⊑`'s `CastOpen` and
  `⊑⟪⟫`'s `Push` do not mention rep. vars (unchanged); `blame⊑` by
  `⊢renᴿ`/`⊢refine`.

### M3 `EvolveMor` — KEEP
```agda
EvolveMor : Set
EvolveMor = ∀ {Δ Δ′} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
    {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WorldMor (nnew ξs +_) (nnew ξs′ +_) W W′ × (WfWorld W → WfWorld W′)
```
- **Intent.**  An evolution is a world morphism and keeps `WfWorld`.
  κ is renamed by the right's allocations (`map suc`), which is
  `mor-κ`.
- **Consumers.**  EvolveImp, every frame, CatchupRightO.
- **Plan.**  Induction on `⟿`; each step is a morphism; morphisms
  compose.

### M4 `EvolveInterior` — KEEP
```agda
EvolveInterior : Set
EvolveInterior = ∀ {Δ Δ′ Δᵢ Δ′ᵢ} {ξs ξs′ : List Alloc}
    {W : World Δ Δ′} {Wᵢ : World Δᵢ Δ′ᵢ}
    {Wᵢ′ : World (applyˢ ξs Δᵢ) (applyˢ ξs′ Δ′ᵢ)} {Θ Θ′}
  → Interior W Θ Θ′ Wᵢ
  → Wᵢ ⟿[ ξs ∣ ξs′ ] Wᵢ′
  → Σ[ W′ ∈ World (applyˢ ξs Δ) (applyˢ ξs′ Δ′) ]
      (W ⟿[ ξs ∣ ξs′ ] W′) × Interior W′ (↑ᴮ*[ ξs ] Θ) (↑ᴮ*[ ξs′ ] Θ′) Wᵢ′
```
- **Intent.**  The IH's evolution of an interior world lifts to the
  outer world.  For a permitting boundary the IH runs at `Wᵢ +κ K`; its
  evolution is `Wᵢ`'s with `K` renamed (INLINE `+κ-evolve`), so this
  statement applies to `Wᵢ`.
- **Consumers.**  The boundary frames of Sim (3 + 3 κ), SimBack
  (3 + 3 κ + slotted ⊑⟪⟫) and CatchupRightO.
- **Plan.**  Induction on `⟿`, InteriorAlloc at each step.

### M5 `WfWorld-bind` — REVISE
```agda
WfWorld-bind : Set
WfWorld-bind = ∀ {Δ Δ′} {W : World Δ Δ′}
  → WfWorld W
  → WfWorld (W ⊕²)
    × (∀ {W₁ : World (underΛ Δ) Δ′} {O O₁}
         → All (SlotOK W) O → Bind W O W₁ O₁ → WfWorld W₁)
```
- **Intent.**  The premise worlds of `Λ⊑Λ` (`W ⊕²`) and `Λ⊑` (fresh,
  join, claim-rep) are well formed.
- **Consumers.**  The two `WfWorld (W ⊕ᴸ)` holes, claim-rep's holes
  (CatchupRight-claim-rep, SimBackFrame-Λ⊑⇔), MorImp, SubstImp,
  InstXImp2, InstXBind, CatchupRightO (join under a slot).
- **Plan.**  As `wf-⊕⁺`.  `⊕²`: `(0, 0)` agrees by `abst-abst`.  Fresh:
  `left-only`.  Claim-rep: `(0, β)` by `abst-★`, named uniqueness by
  `¬ names Δ′ ∋ᵅ β` and `NoNamedPartner`.  Join: `Join↪` turns the
  right-only `skip`/`keep` into `both`, `(0, β)` by `abst-★`, named
  uniqueness by `OpeningOK`'s `NoNamedPartner`.

### M6 `InteriorMerge` — REVISE
```agda
InteriorMerge : Set
InteriorMerge = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′ K}
  → Interior W Θ₂ Θ₂′ Wᵢ
  → Interior (Wᵢ +κ K) Θ₁ Θ₁′ Wᵢᵢ
  → Interior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) (Wᵢᵢ ⟨κ≔ κʷ W ⟩)
```
- **Intent.**  Interior worlds compose across a Merge.  The inner
  boundary lives in the outer boundary's premise world `Wᵢ +κ K`; the
  merged interior is the inner interior with the exterior κ, and its
  premise world with `K₁ ++ K` is the inner premise world.
- **Consumers.**  SimBdy, SimBackBdy, CatchupBdy, RightMergeSlots.
- **Plan.**  `toExt (Θ₁ ++ Θ₂)` composes; `same-κ` by the record
  update; `join-fresh` as before.

### M7 `MergeConvWorld` — KEEP
```agda
MergeConvWorld : Set
MergeConvWorld = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δ₂ᶜ Δ′₂ᶜ Δ⋉ᶜ Δ′⋉ᶜ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {W₂ᶜ : World Δ₂ᶜ Δ′₂ᶜ} {Θ₁ Θ₂ Θ₁′ Θ₂′}
  → WfWorld W
  → Interior W Θ₂ Θ₂′ Wᵢ
  → ConversionInterior W Θ₂ Θ₂′ W₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ → Δ′ ⊢ᶜ Θ₁′ ++ Θ₂′ ⇒ Δ′⋉ᶜ
  → Σ[ W⋉ᶜ ∈ World Δ⋉ᶜ Δ′⋉ᶜ ]
      ConversionInterior W (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) W⋉ᶜ × WfWorld W⋉ᶜ
      -- the outer pair's conversions
      × (∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₂ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₂ᶜ s′
           → ConvImp W₂ᶜ s s′ → ConvImp W⋉ᶜ r r′)
      -- the inner pair's conversions
      × (∀ {Δ₁ᶜ Δ′₁ᶜ} {W₁ᶜ : World Δ₁ᶜ Δ′₁ᶜ}
           → ConversionInterior Wᵢ Θ₁ Θ₁′ W₁ᶜ
           → ∀ {s s′ r r′}
           → SameConv Δ⋉ᶜ r Δ₁ᶜ s → SameConv Δ′⋉ᶜ r′ Δ′₁ᶜ s′
           → ConvImp W₁ᶜ s s′ → ConvImp W⋉ᶜ r r′)
```
- **Intent, consumers, plan.**  Unchanged: conversions are read in the
  EXTERIOR conversion world, which K does not touch.

### M8 `PayloadImp` — KEEP
```agda
PayloadImp : Set
PayloadImp = ∀ {Δ Δ′} {W : World Δ Δ′} {A A′ R R′}
  → WfWorld W
  → A ⊑ᵂ⟨ W ⟩ A′
  → Δ ⊢ᶜ A ~ R → Δ′ ⊢ᶜ A′ ~ R′
  → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′
```
- Unchanged.  Consumers: the matched TyBeta (`ev-2`) and the left
  TyBeta (`ev-L⇔`).

### M9 `RunReplay` — KEEP
```agda
RunReplay : Set
RunReplay = ∀ {Δ : Ctxᵗ} {M N : Term} (xs : List Alloc)
  → (r : Δ ⊢ M -→* N)
  → Σ[ r₁ ∈ applyˢ xs Δ ⊢ ↑ᴹ*[ xs ] M
              -→* renᴹᴿ (extN (nnew (allocs r)) (nnew xs +_)) N ]
      (allocs r₁ ≡ replayAllocs (nnew xs) zero (allocs r))
```

### M10 `EvolveReplay` — KEEP
```agda
EvolveReplay : Set
EvolveReplay = ∀ {Δ Δ′} {W : World Δ Δ′} {xs xs′ ys ys′ : List Alloc}
    {W₁ : World (applyˢ xs Δ) (applyˢ xs′ Δ′)}
    {W₂ : World (applyˢ ys Δ) (applyˢ ys′ Δ′)}
  → W ⟿[ xs ∣ xs′ ] W₁
  → W ⟿[ ys ∣ ys′ ] W₂
  → Σ[ W₃ ∈ World (applyˢ (replayAllocs (nnew xs) zero ys) (applyˢ xs Δ))
                  (applyˢ (replayAllocs (nnew xs′) zero ys′)
                          (applyˢ xs′ Δ′)) ]
      (W₁ ⟿[ replayAllocs (nnew xs) zero ys
           ∣ replayAllocs (nnew xs′) zero ys′ ] W₃)
      × WorldMor (extN (nnew ys) (nnew xs +_))
                 (extN (nnew ys′) (nnew xs′ +_)) W₂ W₃
```

## 3. Substitution, instantiation, merge

### M11 `SubstImp` — KEEP
```agda
SubstImp : Set
SubstImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ γ₁ : CtxImp W}
    {σ σ′ : Var → Img} {N N′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → (∀ {x e} → γ ∋ʷ x ⦂ e → ImgImp {W = W} γ₁ (σ x) (σ′ x) e)
  → W ∣ γ ⊢ N ⊑ N′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ γ₁ ⊢ substᵐ σ N ⊑ substᵐ σ′ N′ ∶ q)
```
- Unchanged.  Substitution stops at boundaries (their interiors are
  closed), so it never enters a permitting premise world.

### M12 `InstXImp2` — REVISE
```agda
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → WfWorld W
  → C ⊑ᵂ⟨ W ⊕² ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕² ⟩ C′ ] (W ⊕² ∣ [] ⊢ N ⊑ N′ ∶ q)
```
- **Intent.**  Both sides instantiate; the binders correspond.  With
  computed marks there is no mark to choose: the matched binder is
  `X⊑X` in `W ⊕²`.
- **Consumers.**  The matched TyBeta (SimTyBeta, SimBackTyBeta) and
  SimBackCast's Inst when the left also Insts.  If the rebuilt
  `⟪⟫⊑⟪⟫` must choose `K = [αᴿ]` (P4k, P4h), the image is re-read at
  the larger κ: P1.
- **Plan.**  Induction on `⊑`, `InstX` inverted (drafts/InstXImpProof,
  14 holes, Q3 of the 2026-10-04 version).

### M13 `InstXBind` — REVISE (was `InstXImpL`)
```agda
InstXBind : Set
InstXBind = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {O : List Slot} {r : `∀ C ⊑ᵂ⟨ W ⟩[ O ] B′}
  → WfWorld W → All (SlotOK W) O
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶⟨ `∀ C , B′ ⟩[ O ] r
  → Σ[ W₁ ∈ World (underΛ Δ) Δ′ ] Σ[ O₁ ∈ List Slot ]
      (Bind W O W₁ O₁ ⊎ ((O ≡ skp ∷ O₁) × (W₁ ≡ W ⊕ᴸ)))
      × Σ[ q ∈ C ⊑ᵂ⟨ W₁ ⟩[ O₁ ] B′ ] (W₁ ∣ [] ⊢ N ⊑ M′ ∶⟨ C , B′ ⟩[ O₁ ] q)
```
- **Intent.**  The left alone instantiates, at any slots.  Its new type
  variable is bound as `Λ⊑` would bind it: fresh or claim-rep at
  `O = []`, the join of the first slot, or left-only when a gen layer
  uses up a skip.  At `O = []` this is the old InstXImpL, its second
  outcome `W ⊕ᴸ⇔ β` being `b-rep`; the slotted case is D27's
  `PopInstX`.
- **Consumers.**  The left TyBeta (SimTyBeta at `ν⊑`; the left's run in
  SimBackTyBeta).  Its own `⊑⟪⟫`-with-new-slots case.
- **Plan.**  Induction on `⊑` with `InstX` inverted.  `Λ⊑`: the binder
  is the outcome.  `cast⊑ co-∀`: pass; `co-gen`: `inst-gen`'s
  `crossΛᴹ` (a hide, `ok-hidden`), the slot used up.  `⟪⟫⊑ bo-∀`:
  `inst-⟪⟫`, InteriorLift.  `⊑⟪⟫` with new slots: the IH under the
  slots; a join of a new opening inside becomes `b-rep` outside (the
  opening's β is unnamed there), rejoined by `Interior.join-fresh`.
  `⊑cast`: the IH.

### M14 `MergeImp` — KEEP
```agda
MergeImp : Set
MergeImp =
  -- both sides compose
  (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₁ c₂ c₁′ c₂′ : Conv} {A B C A′ B′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C
    → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₁ c₁′ → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) (Δ′ ⊢ c₁′ ⨟ c₂′))
  -- the left alone composes
  × (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₁ c₂ c₂′ : Conv} {A B C A′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₁ ∶ A ⇝ B → Δ ⊢ c₂ ∶ B ⇝ C → Δ′ ⊢ c₂′ ∶ A′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → B ⊑ᵂ⟨ W ⟩ A′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₂ c₂′
    → ConvImp W (Δ ⊢ c₁ ⨟ c₂) c₂′)
  -- the right alone composes
  × (∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′}
      {c₂ c₁′ c₂′ : Conv} {A C A′ B′ C′ : Ty}
    → WfWorld W
    → Δ ⊢ c₂ ∶ A ⇝ C → Δ′ ⊢ c₁′ ∶ A′ ⇝ B′ → Δ′ ⊢ c₂′ ∶ B′ ⇝ C′
    → A ⊑ᵂ⟨ W ⟩ A′ → A ⊑ᵂ⟨ W ⟩ B′ → C ⊑ᵂ⟨ W ⟩ C′
    → ConvImp W c₂ c₂′
    → ConvImp W c₂ (Δ′ ⊢ c₁′ ⨟ c₂′))
```
- Unchanged.  6 `MIXED` cases open (drafts/MergeImpProof); R2 must be
  preserved where a MIXED case creates a ★ clause.

### M15 `RightMergeSlots` — REVISE (was `RightMergeOpens`)
```agda
RightMergeSlots : Set
RightMergeSlots = ∀ {Δ Δ′ Δ′ᵢ} {W : World Δ Δ′} {Wᵢ : World Δ Δ′ᵢ}
    {K : List RVar} {M U′ N′ : Term} {Θ₁′ Θ₂′ : Boundary} {t₁′ : Tail}
    {c₂′ : Conv} {A A′ᵢ A′ : Ty} {O N Oᵢ : List Slot}
    {r : A ⊑ᵂ⟨ Wᵢ +κ K ⟩[ Oᵢ ] A′ᵢ}
  → Preκ W → All (SlotOK W) O
  → Interior W [] Θ₂′ Wᵢ
  → Push Θ₂′ M O N Oᵢ
  → All (SlotOK Wᵢ) Oᵢ → AllPairs SlotNe Oᵢ
  → All (JoinRep Wᵢ [] Θ₂′ N) K → WfWorld (Wᵢ +κ K)
  → A ⊑ᵂ⟨ Wᵢ ⟩[ Oᵢ ] A′ᵢ
  → Wᵢ +κ K ∣ [] ⊢ M ⊑ U′ ⟪ Θ₁′ , tail t₁′ ⟫ ∶⟨ A , A′ᵢ ⟩[ Oᵢ ] r
  → BdyTy Δ′ Θ₂′ Δ′ᵢ A′ᵢ c₂′ A′
  → (q : A ⊑ᵂ⟨ W ⟩[ O ] A′)
  → Δ′ ⊢ (U′ ⟪ Θ₁′ , tail t₁′ ⟫) ⟪ Θ₂′ , c₂′ ⟫ -→ N′ ∣ none
  → W ∣ [] ⊢ M ⊑ N′ ∶⟨ A , A′ ⟩[ O ] q
```
- **Intent.**  A right Merge under a right-only outer boundary, at any
  slots.  The premises are `⊑⟪⟫`'s, exactly as the skeleton holes hold
  them.  The merged boundary carries the slots through `Θ₁′ ++ Θ₂′`.
- **Consumers.**  SimBackBdy (`⊑⟪⟫` × Merge, with or without new
  slots) and CatchupBdy.
- **Plan.**  Inversion of the inner derivation.  Inner `⊑⟪⟫`:
  InteriorMerge, INLINE PushCompose (`Carried`/`Fill` through
  `Θ₁′ ++ Θ₂′`), its K₁ by P2.  Inner `⟪⟫⊑⟪⟫`: becomes `⟪⟫⊑` under the
  merged right boundary (R1′ for its unbinds: the exterior type is the
  same).  Left one-sided rules over the inner boundary: induction.

## 4. Redex lemmas of Sim and SimBack (KEEP)

A redex lemma takes the whole derivation and a head step.  The texts
are unchanged; `Pre W` now reads `κʷ W ≡ []` (if Q1 is accepted, these
take `Preκ`).

### M16 `SimApp` — KEEP
```agda
SimApp : Set
SimApp = ∀ {Δ Δ′} {W : World Δ Δ′} {L M M′ N A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ L · M ⊑ M′ ∶ p
  → Value L → Value M
  → Δ ⊢ L · M -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
- Beta, Wrap, CastFun.  Wrap puts the argument into the dual inside
  the function's boundary, whose interior carries that boundary's K:
  P1.

### M17 `SimCast` — KEEP
```agda
SimCast : Set
SimCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ N μ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ V ⟨ μ ∣ c ⟩ ⊑ M′ ∶ p
  → Value V
  → Δ ⊢ V ⟨ μ ∣ c ⟩ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
- At `O = []`, `cast⊑` is `co-plain` only.  Inst rebuilds `ν⊑ν` or
  `ν⊑` at ★.

### M18 `SimBdy` — KEEP
```agda
SimBdy : Set
SimBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N Θ c A A′ ξ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⟪ Θ , c ⟫ ⊑ M′ ∶ p
  → Value M
  → Δ ⊢ M ⟪ Θ , c ⟫ -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
- Merge: InteriorMerge, MergeConvWorld, MergeImp, and P2 when a
  boundary permits.

### M19 `SimBackApp` — KEEP
```agda
SimBackApp : Set
SimBackApp = ∀ {Δ Δ′} {W : World Δ Δ′} {M L′ M′ N′ A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ L′ · M′ ∶ p
  → Value L′ → Value M′
  → Δ′ ⊢ L′ · M′ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
- No grant moves at CastFun (`castfun-grant` gone).  Wrap: P1.

### M20 `SimBackCast` — KEEP
```agda
SimBackCast : Set
SimBackCast = ∀ {Δ Δ′} {W : World Δ Δ′} {M V′ N′ μ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ V′ ⟨ μ ∣ c ⟩ ∶ p
  → Value V′
  → Δ′ ⊢ V′ ⟨ μ ∣ c ⟩ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
- Inst: CatchupLeft on the premise, then PushInstR (the left a value)
  or TyBetaSync2 (the left Insts too).  TagUntag: no drop lemma.

### M21 `SimBackBdy` — KEEP
```agda
SimBackBdy : Set
SimBackBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ N′ Θ c A A′ ξ′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ⟪ Θ , c ⟫ ∶ p
  → Value M′
  → Δ′ ⊢ M′ ⟪ Θ , c ⟫ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
- `⊑⟪⟫` × Merge: RightMergeSlots.  `⟪⟫⊑⟪⟫`: CatchupLeft, then
  InteriorMerge, MergeConvWorld, MergeImp, P2.

### M22 `SimBackBlame` — KEEP
```agda
SimBackBlame : Set
SimBackBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {M M′ A A′ ℓ}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Pre W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ blame ℓ ∣ none
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)
```
- C1–C5, C4g stay dead at κ = [] (`examples/…`, `notes/D28pD30.md`
  §5).

## 5. CatchupRight, PushInstR, generalizations, placeholders

### N1 `CatchupRightO` — NEW (replaces M23 `CatchupRightᴳ`)
```agda
CatchupRightO : Set
CatchupRightO = ∀ {Δ Δ′} {W : World Δ Δ′} {V M′ A A′ O}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V
  → W ∣ [] ⊢ V ⊑ M′ ∶⟨ A , A′ ⟩[ O ] p
  → CatchupRightConclO W V M′ A A′ O
```
- **Intent.**  CatchupRight at any slots and permissions.  The left is
  a VALUE in every case: D31 keeps the left of a slotted premise a
  value (no InstX image as in D26's `Opens`).
- **Consumers.**  CatchupRightProof's `CatchupRightO` and three
  `CatchupRightκ` holes (checked as calls), CatchupCast's Inst case
  (`↺`), SimBackValueO (SimBack's slotted `⊑⟪⟫`).  CatchupRight is its
  instance (checked).
- **Plan.**  The skeleton's cases, by induction, with the measure of
  §0.3; `Λ⊑ b-join` by WfWorld-bind; `cast⊑ co-∀/co-gen` and `⟪⟫⊑ bo-∀`
  are frames whose slots do not move.

### M24 `CatchupCast` — REVISE
```agda
CatchupCast : Set
CatchupCast = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ O}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶⟨ A , A′ ⟩[ O ] p
  → CatchupRightConclO W V (V′ ⟨ μ′ ∣ c′ ⟩) A A′ O
```
- Inert: `done`.  CastId, CastSeq, CastSeq?, TagUntag: `↺`.  Blame:
  CastRedexNoBlame.  Inst + TyBeta: PushInstR, then `↺`CatchupRightO
  on the slotted interior, CatchupBdy, `↺` on the `closeᵖ` cast.

### M25 `CatchupBdy` — REVISE
```agda
CatchupBdy : Set
CatchupBdy = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ Θ′ c′ A A′ O}
    {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟪ Θ′ , c′ ⟫ ∶⟨ A , A′ ⟩[ O ] p
  → CatchupRightConclO W V (V′ ⟪ Θ′ , c′ ⟫) A A′ O
```
- Merge: MergeImp with InteriorMerge and MergeConvWorld, or
  RightMergeSlots; P2; then `↺`.  Id: the same literal.  IdDyn:
  `exitEnv`.

### M26 `CastRedexNoBlame` — REVISE
```agda
CastRedexNoBlame : Set
CastRedexNoBlame = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ μ′ c′ A A′ O ℓ}
    {ξ′ : Alloc} {p : A ⊑ᵂ⟨ W ⟩[ O ] A′}
  → Preκ W → All (SlotOK W) O
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ c′ ⟩ ∶⟨ A , A′ ⟩[ O ] p
  → ¬ (Δ′ ⊢ V′ ⟨ μ′ ∣ c′ ⟩ -→ blame ℓ ∣ ξ′)
```
- By types, as before.  At κ ≠ [] it inherits Q1's risk.

### N2 `PushInstR` — NEW
```agda
PushInstR : Set
PushInstR = ∀ {Δ Δ′} {W : World Δ Δ′} {V V′ M₁′ N′ μ′ p′ A A′}
    {q : A ⊑ᵂ⟨ W ⟩ A′}
  → Preκ W
  → Value V → Value V′
  → W ∣ [] ⊢ V ⊑ V′ ⟨ μ′ ∣ instᵖ p′ ⟩ ∶ q
  → Δ′ ⊢ V′ ⟨ μ′ ∣ instᵖ p′ ⟩ -→ M₁′ ∣ none
  → Δ′ ⊢ M₁′ -→ N′ ∣ new ★
  → Σ[ q₁ ∈ A ⊑ᵂ⟨ allocᴿ ★ W ⟩ A′ ] (allocᴿ ★ W ∣ [] ⊢ V ⊑ N′ ∶ q₁)
```
- **Intent.**  The right's Inst, then its TyBeta under the cast,
  against a left value.  The result is

  ```
  ⊑cast ⟨closeᵖ 0 p′⟩
    ⊑⟪⟫ [+X^0]: new slot opn X, K ⊆ [0], pays ∀C ⊑^[X] C′ at X⊑X
      (the left value's spine at slot [X]:
       cast⊑ co-∀ passes, cast⊑ co-gen uses up, ⟪⟫⊑ bo-∀ passes,
       Λ⊑ b-join joins)
  ```

  at `allocᴿ ★ W` (checked to be the world of the two right steps).
- **Consumers.**  SimBackCast's two Inst holes, CatchupCast's Inst case.
- **Plan.**  Inversion of the derivation down the left value's spine
  (`⊑cast` below, then the left wrappers), pushing the new `⊑⟪⟫` below
  them; at the `Λ`, MorImp at `rm-ren`/`rm-refine` from the old `⊕²`
  (Λ⊑Λ) to the `Join1` world.  The choice of K: Q2.

### G1–G3 `Simκ`, `SimBackκ`, `CatchupLeftκ` — NEW (Def generalization)
```agda
Simκ : Set
Simκ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N : Term} {A A′ : Ty}
    {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ : Alloc}
  → Preκ W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ N ∣ ξ
  → SimConcl W ξ M′ A A′ N
```
```agda
SimBackκ : Set
SimBackκ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N′ : Term} {A A′ : Ty}
    {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ′ : Alloc}
  → Preκ W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ′ ⊢ M′ -→ N′ ∣ ξ′
  → SimBackConcl W M A A′ ξ′ N′
```
```agda
CatchupLeftκ : Set
CatchupLeftκ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M V′ : Term} {A A′ : Ty}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → Preκ W
  → Value V′
  → W ∣ [] ⊢ M ⊑ V′ ∶ p
  → CatchupLeftConcl W M V′ A A′
```
- **Intent.**  The approved Defs at any permissions.  Each approved
  Def is an instance (checked in `notes/D31StatementsFit.agda`).
- **Consumers.**  The six `…κ` holes of SimProof and SimBackProof (the
  IH at `Wᵢ +κ K`, K ≠ []); CatchupLeftκ for SimBack's `·₂` frame at
  that world.

### P1 `KappaWeaken` — PLACEHOLDER (the Wrap work)
```agda
KappaWeaken : (∀ {Δ Δ′} → World Δ Δ′ → List RVar → Term → Term → Set)
  → Set
KappaWeaken Side = ∀ {Δ Δ′} {W : World Δ Δ′} {K M M′ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfWorld (W +κ K) → Side W K M M′
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W +κ K ⟩ A′ ] (W +κ K ∣ [] ⊢ M ⊑ M′ ∶ q)
```
- False without a side condition (R1′ and R2 are anti-monotone in κ);
  `Side` is the other worker's.  Consumers: SimApp/SimBackApp (Wrap),
  the matched TyBeta choosing K ≠ [] (P4k, P4h), possibly PushInstR
  (Q2).

### P2 `MergePermit` — PLACEHOLDER (the Merge/JoinRep work)
```agda
MergePermit : Set
MergePermit = ∀ {Δ Δ′ Δᵢ Δ′ᵢ Δᵢᵢ Δ′ᵢᵢ} {W : World Δ Δ′}
    {Wᵢ : World Δᵢ Δ′ᵢ} {Wᵢᵢ : World Δᵢᵢ Δ′ᵢᵢ} {Θ₁ Θ₂ Θ₁′ Θ₂′ K₁ K₂}
    {Aᵢᵢ A′ᵢᵢ}
  → WfWorld W
  → Interior W Θ₂ Θ₂′ Wᵢ → All (JoinRep Wᵢ Θ₂ Θ₂′ []) K₂
  → Interior (Wᵢ +κ K₂) Θ₁ Θ₁′ Wᵢᵢ → All (JoinRep Wᵢᵢ Θ₁ Θ₁′ []) K₁
  → Aᵢᵢ ⊑ᵂ⟨ Wᵢᵢ ⟩ A′ᵢᵢ
  → All (JoinRep (Wᵢᵢ ⟨κ≔ κʷ W ⟩) (Θ₁ ++ Θ₂) (Θ₁′ ++ Θ₂′) []) (K₁ ++ K₂)
    × Aᵢᵢ ⊑ᵂ⟨ Wᵢᵢ ⟨κ≔ κʷ W ⟩ ⟩ A′ᵢᵢ
```
- False for the current `JoinRep` at a merged rejoin (`[−X^α]` over
  `[+X^α]`: X continues).  The payment needs the inner interior index
  without the outer K.  Consumers: SimBdy, SimBackBdy, CatchupBdy,
  RightMergeSlots.

## 6. INLINE (D31 additions and changes)

| name | consumer | one-line proof idea |
|---|---|---|
| `slotOK-+κ` (new, checked) | CatchupRightO, SimBackValueO | `SlotOK` reads no κ; by cases on the slot |
| `+κ-evolve` (new) | the `…κ` frames | an evolution of `Wᵢ +κ K` is `Wᵢ`'s with `map (n +_) K`; `map` over `++` |
| `mor-+κ` (new) | MorImp | `WorldMor ρ ρ′ W W₁ → WorldMor ρ ρ′ (W +κ K) (W₁ +κ map ρ′ K)` |
| `SlotOK-⟪⟫⊑` (new) | InstXBind, CatchupRightO | §1 gap 4 |
| `unliftᴸ⇔` (new) | CatchupRight-claim-rep, SimBackFrame-Λ⊑⇔ | as `unliftᴸ`: `allocᴿ R′ (W ⊕ᴸ⇔ β) ≡ allocᴿ R′ W ⊕ᴸ⇔ suc β` |
| `castOpen-value` (new) | the slotted frames | `CastOpen M c (s ∷ O) Oₚ → Value M` |
| SimBackValueO (was D26 SimBackValue) | SimBack (slotted `⊑⟪⟫`) | CatchupRightO, Determinism, Irreducible |
| PushCompose (D27) | RightMergeSlots | `Carried`/`Fill` compose through `Θ₁′ ++ Θ₂′` |
| B11 TyBetaSync2 | SimTyBeta, SimBackTyBeta, SimBackCast | InstXImp2; MorImp (refine); rebuild `⟪⟫⊑⟪⟫` with K = [] (or [αᴿ] by P1); `ev-2` with PayloadImp |
| B12 TyBetaCatchUpᴸ | SimTyBeta | InstXBind; MorImp (refine); rebuild `⟪⟫⊑`; `ev-L` or `ev-L⇔` with PayloadImp |
| B13 InstSyncᴳ, B7, B9, A25 WfOpens, A26 OpensEvolveᴿ | — | DROPPED (PushInstR; slots do not move) |
| frames, C14, D-frames, E-frames | as in the 2026-10-04 version | unchanged, with `cast⊑` at `co-plain` and the boundary rules' `K`/`pay` moved by MorSide (a), (f) |

## 7. Questions for Jeremy

1. **Permissions in the induction.**  Generalize Sim, SimBack,
   CatchupRight and CatchupLeft to any κ (G1–G3, N1)?  Example: P4k
   after both TyBetas (design.md §C9.2), with
   `V′ = [−X^α] (λx:★. 5) ⟨id(★) → id(ℕ)⟩`:

   ```
   R  ([+X^α] V′ ⟨X! → id(ℕ)⟩ ⟨−X → id(ℕ)⟩) 5
   ```

   is related by `⟪⟫⊑⟪⟫` with `K = [αᴿ]`.  The right's Wrap gives

   ```
   R  [+X^α] ((V′ ⟨X! → id(ℕ)⟩) ([−X^α] 5 ⟨…⟩)) ⟨id(ℕ)⟩
   ```

   and its next step, `CastFun` on `⟨X! → id(ℕ)⟩`, is INSIDE that
   boundary: SimBack's IH runs at `Wᵢ +κ [αᴿ]` (`P4kᴰ.wrap`,
   `P4kᴰ.castfun` relate the states around it).  The risk: C1–C4g are
   proved dead only at κ = []; if C1's pair is derivable at a world
   with `κ = [αᴿ]`, SimBackBlame and CastRedexNoBlame at any κ are
   false.  Proposal: first check C1–C4g at a world with one permitted
   rep. var (as `notes/D28pD30.agda`'s dead-pair proofs), then
   generalize.

2. **PushInstR's permission.**  Should PushInstR choose `K = [0]`
   exactly when a gen layer uses the new slot up, and `K = []` when a
   `Λ` joins it?  Example: G0 (`TwoGenᴰ.G0ᴰ.g0-final`) has
   `⊑⟪⟫ +X^α: open at X, K = [α]` because `⟨X! → id(ℕ)⟩` under the
   opening needs `X⊑★`, and the left's `gen` layer (`co-gen`) uses X
   up, so nothing on the left sees α; K's final pair has `Λ⊑ join ΛY
   to Y` with `K = []`, and the old `Λ⊑Λ` read Y at `Y⊑Y`, which is
   what `K = []` gives.  If yes, PushInstR needs no κ-weakening (P1).
3. **CatchupRightO as the proved Def.**  Restate CatchupRightProof
   over CatchupRightO (CatchupRight its corollary, checked), with
   EvolveImp (stated at κ = []) replaced by EvolveMor + MorImp as
   module parameters?  Example: the `⊑⟪⟫` with new slots of K's final
   pair, `⊑⟪⟫ [+Y^β, +X^α], open at Y`, whose interior
   `⟪⟫⊑ [+X^α] … ⟨∀Y. …⟩` is caught up at slots `[Y]`.
4. **InstXBind.**  Accept one statement at any slots whose outcome is a
   `Bind` (fresh, claim-rep, join) or a used-up skip (`W ⊕ᴸ`), in place
   of InstXImpL and D27's PopInstX?  Example: the left's TyBeta on K's
   `ΛY` value under `⊑⟪⟫ [+Y^β, +X^α]` (open at Y): inside, the new
   type variable joins Y (`b-join`); outside, where β is unnamed, it is
   `b-rep β`, and the right boundary rejoins it by `join-fresh`.

## 8. Appendix: fate of the 108 (2026-10-04 consolidation)

| old | fate |
|---|---|
| A1 AllocImp | MAJOR MorImp (`rm-ren`) |
| A2–A5 AllocImpL, R, 2, L⇔ | dropped: EvolveImp is EvolveMor + MorImp (checked); each is MorImp at a one-step EvolveMor if wanted |
| A6 InteriorRen | MorSide (b) |
| A7 OpensRen | MorSide (e) |
| A8 NuConvImpRen | MorSide (d) |
| A9 BdyConvImpRen | MorSide (c) |
| A10 WfWorld-⊕, A11 WfWorld-⊕ᴸ | MAJOR WfWorld-bind |
| A12 WfWorld-evolve | EvolveMor, second conjunct (checked) |
| A13 ⊑ᵂ-evolve | corollary: MorSide (a) ∘ EvolveMor (checked) |
| A14 CastTy-evolve | corollary: `castTy-mor` at EvolveMor's sides (checked) |
| A15 NuTy-evolve | corollary: `nuTy-mor` (checked) |
| A16 BdyTy-evolve | corollary: `bdyTy-mor`, `fusionᴮ`, `interior-functional` |
| A17 BdyConversionImp-evolve | corollary: MorSide (c), `fusionᴮ` |
| A18 NuConversionImp-evolve | corollary: MorSide (d) (checked) |
| A19 WfCtx-evolve | corollary: `wfctx-mor` (checked) |
| A20 InteriorAlloc | INLINE (EvolveInterior) |
| A21 EvolveInterior | MAJOR EvolveInterior |
| A22 InteriorLift | INLINE (InstX module) |
| A23 InteriorMerge | MAJOR InteriorMerge |
| A24 MergeConvWorld | MAJOR MergeConvWorld |
| A25 WfOpens | INLINE (`wf-⊕⁺`) |
| A26 OpensEvolveᴿ | INLINE (E8) |
| A27 MarkMono | MorImp (`mor-μ`) |
| A28 RunReplay | MAJOR RunReplay |
| A29 EvolveReplayᴿ, A30 EvolveReplayᴸ | MAJOR EvolveReplay (two-sided) |
| A31 PayloadAgree2, A32 PayloadAgreeᴸ⇔ | MAJOR PayloadImp |
| B1 SubstImp | MAJOR SubstImp |
| B2 SubstImpBeta | INLINE |
| B3 WeakenClosedImp, B4 ClosedSubstFixed | INLINE (SubstImp) |
| B5 InstXImp2 | MAJOR InstXImp2 |
| B6 InstXImpL | MAJOR InstXImpL |
| B7 InstXImpOpenR | INLINE (InstXImp2) |
| B8 RefineImp | MorImp (`rm-refine`) |
| B9 InstXImp⁺, B10 NuBdyConvImp, B11 TyBetaSync2, B12 TyBetaCatchUpᴸ, B13 InstSyncᴳ | INLINE |
| B14 MergeImp2, B15 MergeImpL, B16 MergeImpR | MAJOR MergeImp |
| B17 RightMergeOpens | MAJOR RightMergeOpens |
| C1 SimBeta-Beta, C2 SimBeta-Wrap, C11 SimCast-CastFun | MAJOR SimApp (checked adapters) |
| C3 SimTyBeta | INLINE |
| C4 SimBoundary-Merge, C5 -Id, C6 -IdDyn, C7 -IdDynVar | MAJOR SimBdy (checked adapters) |
| C8 SimCast-CastId, C9 -CastSeq, C10 -CastSeq?, C12 -Inst, C13 -TagUntag | MAJOR SimCast (checked adapters) |
| C14 SimCast-ToBlame | INLINE |
| C15–C24 SimFrame-* | INLINE |
| D1 SimBackBeta-Beta, D2 SimBackBeta-Wrap, D11 SimBackCast-CastFun | MAJOR SimBackApp (checked adapters) |
| D3 SimBackTyBeta | INLINE |
| D4 SimBackBoundary-Merge, D5 -Id, D6 -IdDyn, D7 -IdDynVar | MAJOR SimBackBdy (checked adapters) |
| D8 SimBackCast-CastId, D9 -CastSeq, D10 -CastSeq?, D12 -Inst, D13 -TagUntag | MAJOR SimBackCast (checked adapters) |
| D14 SimBackCast-ToBlame | MAJOR SimBackBlame |
| D15–D25 SimBackFrame-* | INLINE |
| D26 SimBackValue | INLINE (proved) |
| E1 CatchupRightᴳ | MAJOR CatchupRightᴳ |
| E2, E3, E6, E7, E8 CatchupFrame-* | INLINE |
| E4 CatchupCast | MAJOR CatchupCast |
| E5 CastRedexNoBlame | MAJOR CastRedexNoBlame |
| E9 CatchupBdy | MAJOR CatchupBdy |



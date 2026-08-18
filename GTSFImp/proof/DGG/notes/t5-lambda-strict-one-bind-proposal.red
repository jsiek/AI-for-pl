T5 NS-4 stage 2 proposal: one-bind Lambda strict surface

Date: 2026-08-17

Status: blocked by the standing major-lemma rule.

The fixed stage-2 field is:

```agda
structural-lambda-strict-surface :
  StructuralΛStrictSurfaceᵀ
```

The consumer is the strict `Λ` branch in
`StructuralNameInstantiationProof.agda`:

```agda
with StructuralStrictViewSurfaces.Λ-cell surfaces plan chain-plan
  rel vM vV spine chain typed ins follows child-target
...
child-final =
  structural-value-spine-instantiation-acc surfaces ...
    (StructuralStrictChild.child-relation child) vM child-value
    (lambda-child-spine {B = B} {X = X} spine)
    ...
```

The required lower edge is the one-bind beta-Lambda strip:

```agda
rel :
  W ∣ γ ⊢² M ⊑ Λ V ∶ p

child-relation :
  W₁ ∣ ECR.mapCtxᴿ
        (target-insert-bind-world-extendᴿ ins follows) γ
    ⊢² M ⊑ V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗 ∶
      ECR.transport⊑ᵂ
        (target-insert-bind-world-extendᴿ ins follows) q
```

with the target side reducing vertically and imprecision horizontally:

$$
\begin{array}{ccc}
M & \sqsubseteq & \Lambda V \\
\downarrow^{0} & & \downarrow_{\beta\Lambda} \\
M & \sqsubseteq & V \uparrow
  \langle 0,\mathsf{shift}(X)\uparrow B\rangle
\end{array}
$$

The live `InstInversionLambdaProof.agda` machinery is close but not the
same surface.  Its hereditary worker proves a two-insert residual package:

```agda
Λ-post-prefix-hereditary :
  ...
  → ΛPostPrefixPackageAtBase rel (postExtend plan) c′ B′≢★
```

That conclusion lives at the two-bind post world

```agda
postExtend plan :
  ECR.WorldExtendᴿ (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W (W₂ plan)
```

and its target is `Λ⊑Λ²PostTerm V B`.  The strict surface instead needs the
caller-supplied single target bind by `＇ X` and target
`V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗`.  There is no checked theorem that lowers
the two-insert residual package back to this one-insert child.

Proposed checked statement
--------------------------

The direct statement can be the fixed field itself:

```agda
structural-lambda-strict-surface :
  StructuralΛStrictSurfaceᵀ
```

Equivalently, the underlying major lemma is:

```agda
Λ-strict-one-bind-child : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTI2.∣ γ ⊢² M ⊑ Λ V ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁
      (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
      (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralStrictChild {fuel = fuel} W₁ (ECR.mapCtxᴿ ext₁ γ) M
          (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
          A _ (applyTy (bind (＇ X)) E)
          (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
            mapInstantiationSpine (bind (＇ X)) spine)
          (ECR.transport⊑ᵂ ext₁ q)
```

Why this is major
-----------------

The proof must recurse over the parent `⊢²` derivation:

- `Λ⊑Λ²` uses the route1 geometry for the beta-Lambda body.
- `Λ⊑²` and `Λ⊑²-smart-comma` recurse under the source Lambda premise.
- `cast⊑²`, `reveal⊑²`, and `conceal⊑²` replay the source wrapper around
  the stripped child relation.

That is a new one-bind hereditary worker, parallel to but distinct from the
live two-insert `Λ-post-prefix-hereditary`.  Per the task rule, this proposal
records the statement and does not implement the induction.


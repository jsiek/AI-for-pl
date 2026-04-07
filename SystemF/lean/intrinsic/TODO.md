# Intrinsic System F Lean Port TODO

- [x] Create intrinsic port checklist and implementation plan.
- [x] Port `intrinsic/Types.agda` core syntax (`TyCtx`, `TyVar`, `Ty`) and type renaming/substitution operations.
- [x] Port key `Types` commuting lemmas needed by term/type substitution in terms.
- [x] Port `intrinsic/Ctx.agda` (`Ctx`, variable lookup, `renameCtx`, `substCtx`, lift context).
- [x] Port `intrinsic/Terms.agda` typed syntax (`Δ ; Γ ⊢ A`) for System F terms.
- [x] Port type-substitution action on terms (`renameTT`, `substTT`, `instT` type instantiation for terms). Replaced placeholder axioms with constructive definitions.
- [x] Port term renaming/substitution core (`rename`, `subst`, single substitution) used by beta rules.
- [x] Port `intrinsic/Reduction.agda` values, small-step reduction, and progress. Replaced `progress` axiom with a constructive recursive proof.
- [x] Port multi-step closure and transport lemmas used by metatheory proofs.
- [x] Add `intrinsic` Lean aggregator module(s) in this directory.
- [x] Port `SystemF/agda/extrinsic/Eval.agda` into Lean (intrinsic-style development).
- [x] Port `SystemF/agda/extrinsic/Examples.agda` into Lean (intrinsic-style development). Completed seed/TAPL/Church/list-pair suites with Agda/extrinsic-style quoted aliases (`«..._↠»`) and canonical boolean/nat endpoints, including the cast-sensitive `nilIsNil` endpoint proof to `true`.
- [ ] Create `intrinsic/LogicalRelation.lean` and port the extrinsic Agda logical-relations development to intrinsic Lean formulations. Current status: core definitions (`Rel`, `RelSub`, `VRel`, `ERel`) compile; added renaming/substitution transport scaffolding (`WkRel`, `wk_rho1_var`, `wk_rho2_var`, `wk_substT_rho1`, `wk_substT_rho2`, `wk_substT_ext_rho1`, `wk_substT_ext_rho2`, `wk_rhoR_cast`, `wk_rhoR_uncast`), plus substitution-index transport scaffolding (`SubstRel`, `SubstRel_substT_rho1`, `SubstRel_substT_rho2`, `SubstRel_substT_ext_rho1`, `SubstRel_substT_ext_rho2`) and first lifted variable transport lemmas (`VRel_rename_wk_var`, `VRel_subst_var`, `ERel_subst_var`, `ERel_unsubst_var`), plus cast-coherence groundwork (`uipEq`, `castTy_trans`, `castTy_lam_exists`, `castTy_tlam_exists`, `castValue_lam_heq`, `castValue_tlam_heq`, `castValue_lam_transport`, `castValue_tlam_transport`, `VRel_castTyIndex`, `ERel_castTyIndex`), plus the environment layer (`RelEnv`, `extendRelEnv`, `tailRelEnv`, `GRel`, `LogicalRel`, `GRel_empty`, `extendRelEnv_related`); still pending are the lifted recursive `VRel`/`ERel` transport lemmas under weakening/substitution for arrow/forall types and downstream theorem use in `Parametricity.lean`.
- [ ] Create `intrinsic/Parametricity.lean` and port the extrinsic Agda parametricity theorem/proof structure to intrinsic Lean.
- [ ] Create `intrinsic/FreeTheorems.lean` and port extrinsic Agda free-theorem derivations to intrinsic Lean statements/proofs.
- [ ] Update build wiring to include intrinsic modules. (Blocked by current instruction: edits limited to `SystemF/lean/intrinsic/*`.)

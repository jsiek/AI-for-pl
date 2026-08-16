LG-3 M5 design scratch regression blocker

`M5InstInversionDesignScratch.agda` has been mechanically updated away from
the deleted `CatchupCast⁻` residual witness: its local residual obligation now
uses the live relation-builder shape, and the public package projection uses
`residual-cast-builder`.

The scratch still does not check in ordinary Agda mode because later sections
refer to proof-local names that no longer exist in
`proof.DGG.Catchup.InstInversionProof`, starting with:

```
IIP.ΛPostPrefixPackageAt
```

This is not a live-code blocker.  The live M5 definitions/proofs check through
`make check`; the failing names are historical scratch projections over proof
internals that were reshaped during the LG-3 residual-relation migration.

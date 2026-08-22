# T2 source-cast peel status

Date: 2026-08-18

The review's conditional `source-value-cast-layer-peel-with` surface,
implemented here as `source-value-cast-layer-peel`, and its
`SourceValueCastLayerEndpointEvidence` input have been deleted from the live
canonical surface.  The evidence's base constructors required the endpoint
that the peel returned, so the helper only projected an assumption supplied by
its caller.  No external consumer used the evidence or the helper.

The genuine `source-cast-layer-head-analysis` view remains live and stands on
its own.  The real one-cast inversion needed by the variable-ground rows is
pending the D15 occupancy migration: it needs witness-mark transport across
the rebased world, which is exactly the transport supplied by that migration.
The stopped witness-inversion attempt and the variable-ground obstruction are
recorded in
[t2-d2a-witness-inversion-stopped.red](t2-d2a-witness-inversion-stopped.red).

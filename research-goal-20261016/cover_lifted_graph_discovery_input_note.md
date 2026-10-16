# Minimal fixed-cohort discovery inputs

The 516,598-byte `cover-curvature-parent64.input.json.gz` is the immutable
input shared by the graph8 and graph64 experiments.  Its compressed SHA256
is `f5df55809ffc099520a6cb95f92064436c956faed79a85f6818b9fa1f57e8d77`.
It contains the 64 explicit parent cells and all their necessary ancestor
OBBT/Newton records, root geometry, source hashes, sampling rule and source
checkpoint SHA.  The large original checkpoint is needed only to regenerate
the initial cohort projection; it is not needed to recompute or verify the
frozen graph experiments.  The standalone positive-witness archives do not
need even this full parent64 input.

The original cohort was sampled before any curvature or graph success was
observed: 64 discovery-order spaced branch parents from the last at most
512 depth-24 branches below `r00100000` in the checkpoint at 65,500 checked
nodes.  `cover_curvature_parent_sample.py` records the capture algorithm;
do not rerun it over the live filename, because the live checkpoint has
advanced and this would overwrite the fixed cohort.  The original snapshot
receipt pins the full source checkpoint and the projected input bytes.

The eight pilot paths were the most negative feasible-midpoint Hessian
eigenvalue hints within those same 64.  The small selection JSON records
these exact paths and the diagnostic values.  Their numerical selection
criterion is not a proof assumption; ancestor replay establishes all cells
and the strict certificates are checked independently.

To recompute discovery, retain the pinned positive graph8/64 source packages,
the frozen derivative table, rational ledger and the Python numerical
dependencies used for LP discovery.  Write results to a new output file:

```text
python -B -X utf8 research-goal-20261016/cover_lifted_graph_recompute.py --sample 8 --output graph8-recomputed.json
python -B -X utf8 research-goal-20261016/cover_lifted_graph_recompute.py --sample 64 --output graph64-recomputed.json
```

The driver verifies that each original positive certificate is reproduced
field for field and writes the new timing/receipt separately.  It refuses
to overwrite an existing pinned `cover-lifted-graph*.json` file.  The older
producer default outputs are frozen evidence and should not be overwritten.
This input pin omits the full two-megabyte negative curvature/control bundle.
No global cover or improved zero-proportion theorem is asserted.

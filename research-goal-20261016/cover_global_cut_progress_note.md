Finite global-competitor cuts, verified pilot
==========================================

For every integer shift feasible on the whole cell, let U be a certified
affine upper bound on F(g+delta)-F(g). At an original global minimum U>=0.
Nonnegative combinations of these cuts, the energy sublevel inequality,
and exact difference-constraint flow bounds yield coordinate contraction.
This condition preserves original global minima below the target. It does
not preserve arbitrary KKT points and is not a pointwise cover operation.

The fixed pilot examines the first 50 surviving cells after skipping the
24 previously verified finite-move exclusions and performing the prior
OBBT/Newton/baseline checks. It scans 71 old sample paths. Seventeen paths
contract, with 24 contraction rounds and 149 coordinate bounds; eight
then close by the existing correlated direction checker. The independent
replayer verifies all 149 new bounds, 262 prior OBBT bounds, 65 prior
Newton steps, and all eight final direction certificates. This is a
strict, exact-arithmetic replay, independent of LP optimality.

A paired energy-only OBBT control starts from the identical seventeen
post-Newton cells and uses at most two rounds. Its diagnostic classifies
three cells as closed versus eight for the global-cut run: one is shared,
seven close only with the global cuts, and two only with the control.
The control median volume ratio is 0.283505, versus 0.342235 for the
global-cut subset, so these results do not show uniform volume dominance.
The control stores its bound certificates but not its final leaf witnesses;
its terminal classifications remain diagnostic and are not counted as
independently replayed new exclusions in this archive.

The evidence directory compresses the complete original pilot and control
JSON byte streams losslessly. Its manifest pins compressed and original
hashes and includes the independent proof replay receipt. To rerun the
existing verifier, decompress proof.json.gz to a temporary JSON path and
invoke cover_global_cut_verify.py --input that-path. The verifier also
needs the prior 806-path OBBT proof (SHA256 869122355b263bba85408cf3269ad3172d9f42914bec5077a7e44f28abe01197),
the frozen derivative oracle and parameter files, and their existing
verifier dependencies. This small package is not a standalone geometry
archive; the prior proof can be restored from the already published OBBT
archives. The larger inclusive gamma=0 experiment is excluded here.

All complete-global-cover, actual-analytic-Lean-bridge-complete,
new-zero-proportion-proven and final-submission-ready flags remain false.
This pilot does not establish an unconditional zero-proportion record.

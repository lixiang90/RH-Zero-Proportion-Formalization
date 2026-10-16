# Independent challenge of the two-layer phase proposal

This audit concerns a proposed new relaxation.  It produces no improved
energy lower bound, PSD dual, uniform coefficient certificate, full cover,
or zero-proportion theorem.  All existing proof sources, pinned inputs and
the sole main coverage process were left unchanged.  The bridge's separate
identity audit is `window_phase_hermitian_audit.txt`, SHA256
`db6ac3c30d3bc991eee72475f40f2e16a25755ce61bfbfb0cdd47ff6df6abb90`.

## Algebra and uniform payments

The global smooth decomposition avoids all integer poles:

`k(x) = C_all(x) + A0(x)*sin(pi*x) + B(x)*cos(pi*x)`.

Here `C_all` is the complete normalized perturbation Fourier integral,
not a rational function or constant.  The original MT term supplies
`A0=-sqrt(2)*pi*x*cot(sqrt(2)/2)/(1-2*pi^2*x^2)` and
`B=1/(1-2*pi^2*x^2)`.  Its real poles lie below the original separation.
The derivative identities in the bridge audit and its off-diagonal factor
`H_ij=a_ij*q_ij/2` have the correct signs.  For

`w=c0+c1*cos(pi*x)+s1*sin(pi*x)+c2*cos(2*pi*x)+s2*sin(2*pi*x)`,

the derivative coefficients are

`c0', c1'+pi*s1, s1'-pi*c1, c2'+2*pi*s2, s2'-2*pi*c2`.

All five coefficients vary with the span.  The possible frozen-matrix
bound must retain pressure and subtract rigorously bounded coefficient
variation over the entire cell.  The bridge's triangle-inequality payments
are valid sufficient bounds, but their available margin has not been
established.  A global L1 bound on `C_all` is too coarse to count as a useful
payment.  Local actual Taylor evaluation would be needed.

## An exact two-node obstruction

Take `k(theta)=1+cos(theta)`.  Then

`k(theta)^2 = 3/2 + 2*cos(theta) + (1/2)*cos(2*theta) >= 0`.

Two independent phase layers may choose `u=(1,-1)` and `v=(1,-1)`.
Both rank-one Gram matrices are PSD with unit diagonal, yet the two cosines
are both `-1`, and the relaxed value is exactly `-1`.  The true relation
`v_i=u_i^2` is violated.  Therefore even rank-one layers and within-layer
cycle consistency do not automatically preserve the nonnegativity of the
individual squared kernels.  This is an obstruction to the unlinked
relaxation, not a disproof of a model with the missing relationships.

For an edge let `z=exp(i*delta)` and `t=exp(2*i*delta)`.  The necessary
Toeplitz moment matrix

```text
[ 1       z       t ]
[ conj(z) 1       z ] >= 0
[ conj(t) conj(z) 1 ]
```

has determinant
`(1-|z|^2)^2 - |t-z^2|^2`.  Hence PSD implies
`|t-z^2| <= 1-|z|^2`; when `|z|=1`, it forces `t=z^2`.
The toy choice `z=t=-1` has determinant `-4` and is rejected.  Such a
degree-two moment matrix also preserves the expectation of every frozen
square `(C+A*sin(delta)+B*cos(delta))^2` as nonnegative.  It still does not
recover all cross-edge moments or connect phases to the original cell's
real gap variables.  In the convention `X=u*u*`, the edge phase is
`z=X_ji` and its doubled phase is `t=Y_ji`.

## Minimal fixed-eight numerical challenge

The same eight pre-contraction residual parents used in the earlier
stopped energy/radial pilots were reused.  No new selection or larger search
was performed.  On each cell, a feasible DBM midpoint supplied the amplitude
references.  The exact minimum pressure was accompanied by a feasible
integer gap vector and matching exact flow; the script checks their equality
and every span bound.  BFGS then selected unit-circle phase witnesses for
the frozen amplitudes.  An optimizer's convergence flag or optimality is
not needed for these *primal upper* values: any returned phases are feasible
for the stated weak proxy.  No SDP solver or PSD dual was used.

The value proxy retains the original cell only for pressure.  It drops the
old derivative graph and does **not** connect its phase differences to those
real gaps.  In one version the two layers are independent; the control
version enforces `v=u^2` but still leaves the phases free of the gap geometry.
Coefficient variations and their payments are not yet included.  Any
nonnegative uniform payment would further reduce a certified lower bound
from this frozen-matrix strategy.

The following values are floating diagnostic evaluations, not rigorous
interval or Lean bounds.  Case order is the fixed selection recorded in
`cover-lifted-graph-energy8.json`.

| Case | Old pointwise lower bound | Independent-layer primal upper | Linked-layer primal upper |
|---:|---:|---:|---:|
| 1 | .008074646 | -.001260805 | .007783184 |
| 2 | .008152610 | -.001608842 | .007978680 |
| 3 | .008384845 | -.001209707 | .007602189 |
| 4 | .008465228 | -.001366190 | .007591466 |
| 5 | .007839178 | -.001633244 | .007663335 |
| 6 | .007963320 | -.001508285 | .007701904 |
| 7 | .008000093 | -.001765262 | .007818223 |
| 8 | .007688446 | -.001866573 | .007822116 |

Thus the completely independent-layer proxy loses positivity on all eight.
Even the linked but position-free value proxy has a feasible upper below the
old pointwise lower bound in seven cases.  This rules out expecting a better
bound from that weak frozen value model on those cases, before payments.
The eighth case was not ruled out this way.  Within-layer cycle frustration
is retained by these witnesses; it is not being set to zero by assertion.
The correct conclusion is that missing inter-layer and position links can
erase the hoped-for advantage.  It does **not** establish failure of a phase
model retaining the original graph, geometry and KKT constraints.  Nor does
failure to prove a pointwise floor imply failure of a minimizer-only cover.

## First-cell check retaining the old graph

For the first case, the previous multi-facet graph LP's feasible `g,d`
point was retained, with direct KKT residual about `2.7e-16`.  Its **actual**
position phases were used, with doubled phases exactly linked.  Consequently
all actual phase arcs and edge Toeplitz constraints hold at this trial point.
The frozen five-coefficient formula was compared to each derivative `d_t`.
The script sampled coefficient variations at span endpoints and 1/64 points.
These sampled maxima are lower estimates of the necessary separate uniform
component budgets; they are not uniform upper bounds.

Seven of the 41 derivative terms did not fit the resulting sampled payment
allowance (terms 5, 6, 11, 12, 21, 24 and 27); the largest deficit was about
`9.51e-4`.  Therefore this trial did **not** produce a feasible primal point
for the strengthened graph-plus-phase approximation.  Conversely it is not
an infeasibility certificate: another point or larger rigorous payments
could be feasible.  No PSD-feasibility decision for that stronger model was
made, and no strict new exclusion is claimed.

The complete eight-case diagnostic took 19.74 seconds.  Its JSON includes
all frozen reference coefficients, returned phase angles, pressure witnesses,
the first trial's original graph point and per-term payment comparisons.
The script and data are independently readable research evidence; they do
not contain a rigorous uniform amplitude proof or rational PSD certificate.
The numerical work stops here for this checkpoint.

## Next testable model, not implemented

Retain **all** old `g,d` DBM, multi-facet scalar derivative and original KKT
rows.  Add shared real/imaginary variables for all 45 pair entries of `X,Y`,
their actual phase-arc or sin/cos-span graph outer bounds, the five derivative
coefficient relations with rigorous local payments, and edge Toeplitz links.
HiGHS can optimize an outer approximation.  If a trial `X`, `Y` or edge
Toeplitz matrix is not PSD, a negative eigenvector can be rationalized and
its necessary rank-one inequality `v*Mv >= 0` added as a linear cut.  Each
accepted rational cut has a direct squared-norm interpretation for actual
phases.  A final strict Farkas certificate would be replayable without a
general SDP solver or an assumed numerical PSD conclusion.

No such iteration, rigorous coefficient packet or final Farkas witness was
implemented here.  This is the smallest model worth testing next because it
contains the old relaxation and explicitly retains the links omitted by the
failed weak value proxies.

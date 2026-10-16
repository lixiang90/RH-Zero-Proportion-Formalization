Actual normalized-table feed for three negative-curvature leaves
==============================================================

This audit uses the frozen normalized w Taylor coefficients on the 10^-30
integer grid. All 768 n=1..32 coefficient intervals are matched exactly to
WindowRawCoefficientData.lean. It does not need the much narrower discovery
coefficient intervals as actual analytic premises. The common analytic
remainder is (44/7)^24 times the appropriate radius power and factorial.

The complete audit checks the original 123 scalar rows in the three already
verified curvature leaves. There are 51 rows with nonzero curvature weight
a*(span d)^2. All original m0, m1 and error constants remain valid. Both the
original selected quantized w'' bounds and selected absolute w'''' bounds
remain valid under the normalized table. No scalar or final strict flow
numerator changes are required.

Only necessary grid cells are evaluated: q=2 on 175 cells and q=4 on 304,
with a union of 354 cells; 77 point locations have q=2 and q=3 evaluations.
The independent replayer checks all 633 fixed-integer Horner evaluations,
point remainder payments, interval/affine scalar errors, and all three final
integer flow signs. It imports no discovery evaluator or optimizer and
also checks the scalar budgets using the original fourth-derivative bounds.
This is exact arithmetic evidence, not an ordinary Lean compilation.

The active-only table is 51,615 bytes and needs q=2 on 175 cells, q=4 on 281
cells (331-cell union), and q=2/q=3 at 31 points. Its schemas are:

- grid: {k,n,q2:[mask,L_DS,U_DS],q4:[mask,B_DS]}; an absent q is unnecessary;
- point: {P,n,q2:[mask,L_Q,U_Q],q3:[mask,L_Q,U_Q]}; x=P/(2*32768);
- scalar row: {t,l,u,P,m0,m1,err,kind,e0,e1,B4,first,last}; first..last is inclusive.

Here Q=10^30, DS=10^15. The q2 grid degree is 21, q4 grid degree 19, q2
point degree 21 and q3 point degree 20. Scalar term t uses the existing
41 positive-weight pair order. For an affine row, r=(u-l)/(2*32768) and
err>=e0+e1*r+B4*r^2/2; e0 and e1 are rational errors measured in DS units.
For an interval row m1=0 and only the q2 grid union is needed. Inactive rows
can be removed using span d=0. The original complete table retains them
for independent numerical review.

The compressed complete audit is a lossless copy of
cover-curvature-actual-feed.json. The replayer reads that JSON when present
and otherwise reads cover-curvature-actual-feed.json.gz directly. The
active table and its original uncompressed SHA remain unchanged.

All ordinary-Lean-proven, complete-global-cover and new-zero-proportion
flags remain false for this new feed. It is supplied for the actual q2
scalar consumer and selected-grid formal proof, which are separate work.

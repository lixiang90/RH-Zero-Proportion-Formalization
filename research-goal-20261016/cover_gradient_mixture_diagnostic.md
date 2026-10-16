# Finite actual-gradient mixtures: no origin-in-hull witness found

Only the same first two frozen residual cases were used. For each case,
32 integer objective flows select actual DBM vertices (duplicates are
removed), followed by rational convex combinations of these vertices.
Exactly 128 distinct points are evaluated. All 45 rational span bounds
are checked for every point. Every cell coordinate lies strictly above
the original separation boundary, so zero gradient would be the relevant
first-order necessary condition.

At both 64 and 128 points, the floating gradient-convex-hull equality LP
is infeasible. No positive ten-point simplex is obtained, and no robust
interval origin-in-hull claim is made. A separate LP finds the closest
sample-gradient mixture in L1 norm using those same 128 points; it does
not draw or evaluate additional points.

| Quantity | Case 0 | Case 1 |
| --- | ---: | ---: |
| Minimum sampled F | 0.02274606771 | 0.01684098323 |
| Maximum sampled F | 0.04183651898 | 0.04072001787 |
| Nearest mixture gradient L1 | 0.04092953938 | 0.01193827219 |
| Nearest mixture mean F | 0.03029203901 | 0.02570602789 |
| Weighted Hessian smallest eigenvalue hint | -0.2856350162 | -0.1118818622 |

Every sample and mixture average is above 0.0088. Consequently these
geometric samples do not probe the energy sublevel well. They neither
establish the anticipated first-moment obstruction nor exclude a
zero-gradient mixture made from different actual points in the cells.
The negative averaged-Hessian hints concern mixtures whose average
gradient is nonzero and whose average energy exceeds the target; they
give no valid new exclusion.

One direction per case is selected by the nearest-mixture LP dual and
quantized at scale 1,000,000. The same directions have strictly positive
directional derivatives at all sampled points (floating hints), but the
existing whole-cell derivative enclosures are too broad:

| Whole-cell lower bound for direction dot gradient | Case 0 | Case 1 |
| --- | ---: | ---: |
| Independent scalar intervals | -0.1849174672 | -0.1892458680 |
| Correlated affine terms and exact DBM flow | -0.1562111220 | -0.1221301332 |

The negative lower bounds do not imply that the derivative becomes
negative; they fail to certify strict positivity. Reoptimizing this
linear gradient direction within the old lifted graph/KKT model would
reuse its existing zero-KKT feasible point and is redundant. No such LP
or additional PSD cut rounds were run.

`cover_gradient_mixture_replay.py` runs with `python -S`: it checks all
256 point DBM memberships exactly, recomputes each F and gradient using a
separate stdlib sinc implementation, checks the nearest mixtures and
finite-sample separation numerically, and independently checks both full
cell Taylor/flow bound computations with exact integers and fractions.
Energy/gradient discrepancies are at most 3.2e-17/1.9e-16. The replay
passes, but its floating comparisons do not certify finite-hull
infeasibility or any statement over all points of a cell.

```text
python -S -B -X utf8 research-goal-20261016/cover_gradient_mixture_replay.py
```

This is a stopped negative diagnostic. There is no origin-in-hull theorem,
stationary point, new strict cell exclusion, global cover or new
unconditional zero-proportion record. Full cross-coordinate products of
the KKT equations were not tested here; the earlier radial RLT experiment
was only one summed identity and is a weaker, different model.

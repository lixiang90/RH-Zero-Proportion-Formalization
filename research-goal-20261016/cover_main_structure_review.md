# Structure of the audited c880 search at 117,500 nodes

This is a read-only review of checkpoint SHA
`30920f05d0352808e7dc7404ac5705281ff3a6ae9da73164ffd8807eaa1f58ae`.
The complete JSON, frozen source guards, binary-prefix accounting and all
29 pending DBM closures pass a structural audit. It is not a semantic replay
of the 880,632 OBBT bounds or 119,168 Newton steps.

The old handle stopped responding. After parent authorization, the same
task was resumed from a verified immutable copy of that checkpoint, with
the same script/floor/output and the remaining original node budget.
New handle 1700 reached and atomically saved 118,000 nodes. The parent task's
host-elevated CIM query confirms a single writer PID 46548 and no old PID
36004. Sandbox process enumeration cannot be treated as host authority.
The earlier worker's exit cause is unknown; system event logs were not
accessible. The recovery receipts record these distinctions.

## What is actually complete

At 117,500 processed nodes there are 58,736 accepted leaves, 58,764 branches
and 29 pending cells. The maximal completely explored prefixes are:

```text
r000
r0010000
r001000100000000
r0010001000000010
r00100010000000110
r0010001000000011100000
r00100010000000111000010000000
r001000100000001110000100000010000000
```

In particular `r1`, `r01`, `r0011` and other broad siblings are still pending.
The count 29 is a DFS stack count. It is not an estimate of remaining
geometric volume, work or number of well families. Adaptive span splits
have unequal domain volumes, so no completion percentage is claimed.

The last 5,000 recorded splits all lie in prefix `r001000100000001`.
Only 2,365 split an adjacent gap; 2,635 split nonadjacent spans, including
755 of rank 6 and 440 of rank 9. Thus long-span correlation is an active
source of complexity even after the earlier difficult local subtree.

Accepted leaves are 17,225 value, 40,342 stationary and 1,169 reflection;
Gram, Newton-empty and OBBT-empty counts are zero. The frozen main pipeline
still uses its earlier directional/Taylor checker and does not yet invoke
the newer multi-facet graph or energy/RLT consumers. Small certified
regions from those methods therefore do not imply that this main tree has
already benefited from the new criteria.

## Current residuals are outside the previous 69 basin domains

All 17 pending cells at depth at least 18 have empty intersection with
every one of the 69 registered basin domains, checked by exact integer DBM
closure after intersecting their 41 scalar-span intervals. Their free KKT
coordinate counts range from 3 to 7. These are domain-intersection facts,
not assertions that each cell contains an actual stationary point or a
new low-energy well.

The deepest pending cell has depth 36, integer midpoint pattern
`[1,1,1,1,1,1,2,1,1]`, seven strictly interior coordinates, and span widths
from 1379/32768 to 15077/32768. Its adjacent widths range from about .0421
to .2642. Its total-span lower bound exceeds the sum of the nine separate
adjacent lower bounds by 5889/8192, about .7189. Similar correlated
improvements in neighboring deep cells exceed one gap unit. Refinement
into the existing 69 domains cannot cover these residuals, and shrinking
their constants is not the missing structural step.

## A strictly stronger available RLT cone

The current full cross-moment model multiplies every old affine inequality
`R(g,u)-B <= 0` by the adjacent-gap box factors `1 +/- y_s`. It does not
multiply old rows by nonadjacent DBM slacks. If

```text
ell_ij <= x_ij = sum_{r=i}^{j-1} g_r <= U_ij,
```

then two additional valid inequalities are

```text
(x_ij - ell_ij) * (R-B) <= 0,
(U_ij - x_ij) * (R-B) <= 0.
```

These still use only the existing `g*g` and `g*u` moments. No new variables,
transcendental table or PSD hypothesis is needed. They are redundant when
the chosen span bound is exactly the sum of its adjacent bounds; the
positive correlation deficits measured above identify useful candidates.

The new factors are nonnegative on the DBM cell, although their affine
normalization `A+sum b_s*y_s` may have `A < sum |b_s|`, or even `A<0`, on the
larger independent box. Therefore the existing box-factor validator must
not be reused unchanged: factor nonnegativity must be discharged by the
actual span bound. The polynomial expansion and finite Farkas aggregation
remain the same.

The new rows are not implied by coordinate RLT, KKT, McCormick constraints
or the position moment PSD condition alone. An exact counterexample uses

```text
x=y=1/2, z=t=-1/2;   0<=x,y<=1;   -1<=z,t<=0;   x+y>=1;
KKT: z+t+1=0;
Hxx=Hxy=Hyy=1/4;
Qxz=Qyz=0;   Qxt=Qyt=-1/2.
```

All 11 base inequalities, their 44 coordinate-RLT products and 28
McCormick inequalities hold. The position moment matrix is exactly rank
one PSD. The KKT equation and both coordinate products hold. However the
valid row `z*(x+y-1)<=0` has lifted value +1/2. The accompanying stdlib
script checks every one of these rational assertions. This proves strict
nonredundancy of the cone; it does not yet show gains for the actual window.

The smallest informative experiment is a separation oracle on one already
fixed residual cell with its same midpoint energy row: inspect the current
moment primal, select a small number of violated nonadjacent span-slack
products, and rerun the same LP. Do not allocate all roughly 170k possible
rows or start a global replacement search before a strict exact witness
exists. A generic nonnegative-affine multiplier proof can be shared with
the existing grouped consumer, with DBM factor nonnegativity as the only
additional elementary input.

No new actual cell exclusion, full cover or zero-proportion record is
claimed by this review.

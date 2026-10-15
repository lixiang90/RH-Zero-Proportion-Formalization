# Local-floor and alternating-series refinement of the nine-point bound

The candidate exact proportion is

\[
\kappa=\frac{3338957652820594373879991756052499665323}
{4957023073704306225950000000000000000000}
=0.6735812206590039663684362480701863790258\ldots.
\]

The reference is the accepted
[ajp88 reweighted nine-point record](https://www.riemannzeta.fun/submissions/ajp88-reweighted-nine-point),
archived at site commit `e08fce410ba008ff5c5a03215d9b6bfb3ab91200`.
That record is

\[
\kappa_0=\frac{834739413205148593469931805501689594457}
{1239255769294131601825000000000000000000}.
\]

The exact improvement is

\[
\kappa-\kappa_0=
\frac{115935961467980058372568945908139480510493387458213}
{245720777704487633104131505287559755294350000000000000000000}
>0,
\]

approximately **4.71819935420 × 10⁻⁸ percentage points**. This is a small
improvement in the existing certificate and analytic enclosure. It does
not change the window or establish a new zero-distribution principle.

## Sharper floor from the same proof tree

The accepted certificate used integer floor `859538456469471854` with
denominator \(10^{20}\). Replaying all 48 roots gives 22,664 tree nodes,
10,937 numerical leaves and 419 reflection leaves. There are no Farkas
leaves in this particular tree. Each numerical inequality is linear in the
floor numerator with coefficient `335544320000000000`.

The smallest original integer margin is
`23301675193062482720000000000`, at root 34, bit position 43828. Therefore
raising the floor numerator by `69444403627` leaves margin

\[
23301675193062482720000000000
-69444403627\,(335544320000000000)
=235234080000000000>0.
\]

One further numerator unit makes that fixed leaf inequality negative.
The 108 large-gap, small-gap and root-cover conditions are also checked;
their smallest permitted integer floor is `859704225699355536`, above the
new numerator `859538525913875481`.

The discovery audit compares a compact integer evaluation with a direct
evaluation of the original `mcheckP` expression at every numerical leaf.
It checks exact tree end pointers, reflection conditions, decoding and
pair-bound tightening. Its data and script are supporting evidence. The
published Lean proof retains every ordinary `decide` check and rebuilds
them at the higher floor; Python is not a trusted proof oracle.

This is the largest numerator at this denominator admitted by these fixed
leaf inequalities. It is not a proof that the mathematical local objective
or the method itself is globally optimal.

## Exact rational trigonometric enclosure

Set \(\theta=\sqrt2/2\), so \(\theta^2=1/2\) exactly. The inherited
`Meshuggah.Majorant` alternating-polynomial theorems imply

\[
\cos\theta\le C=
\sum_{j=0}^{16}\frac{(-1)^j}{2^j(2j)!},\qquad
0<S=\sum_{j=0}^{17}\frac{(-1)^j}{2^j(2j+1)!}
\le\operatorname{sinc}\theta.
\]

These are a degree-32 cosine upper bound and a degree-34 sinc lower bound.
Both are evaluated by exact rational arithmetic. In particular,

\[
C=\frac{132424952393242556021461169421128332043}
{174187298275621608010492925706240000000},
\quad
S=\frac{14302403666080084620954960913502913904936237}
{15567659428162813657715716369101619200000000}.
\]

Since \(\sqrt2\sin\theta=\operatorname{sinc}\theta\) and
\(2\sin^2\theta=\operatorname{sinc}^2\theta\), the accepted identity for
the AM window becomes

\[
H_W=\frac32-\frac{\cos\theta}{\operatorname{sinc}\theta}
-\frac{P_{AM}}{\operatorname{sinc}^2\theta}
\ge\frac32-\frac C S-\frac{P_{AM}^{+}}{S^2}.
\]

The same accepted bound
\(\pi<314159265358979323847/10^{20}\) supplies \(P_{AM}^{+}\), with
all twelve window coefficients unchanged. Its nonnegativity and the
positivity of \(S\) justify both denominator comparisons.

The rational expression on the right lies in

\[
\left[\frac{6721684105641188747759983512104999330646}{10^{40}},
\frac{6721684105641188747759983512104999330647}{10^{40}}\right).
\]

Thus the new window floor is
\(h=6721684105641188747759983512104999330646/10^{40}\).
The accepted window floor was
\(6721684105641188747759454444013516755656/10^{40}\).
This replaces an exponential-norm remainder and rational square-root
enclosure by alternating cos/sinc bounds evaluated at the exact squared
argument. No floating-point computation enters the proof.

## Counting and finite certificate

The accepted nine-point proof tree, tangent data, closed cell cover, weights
and gap pressures are retained. The improved local floor and unchanged
total pressure are

\[
c=\frac{859538525913875481}{10^{20}},\qquad
B=\frac{437688000000}{10^{14}}.
\]

The existing counting argument yields \(\kappa=(h-B)/(1-c)\). The
generic counting module preserves reflected off-line pairs, all zero
multiplicities, deleted-strip errors and span errors. It gives the actual
simple critical-line count. Inclusion then gives the distinct critical-line
count, and the inherited dyadic-to-cumulative theorem gives both cumulative
forms. Each conclusion means every \(\kappa-\varepsilon\), for
\(\varepsilon>0\), holds at all sufficiently large heights.

## Source provenance and reproduction

The exact accepted source bytes are preserved in
`formal/upstream/ajp88-reweighted-nine-point.lean`, including the inherited
attribution and full license trailer. Extraction removes the score-specific
wrapper and uses the pinned `Zeta23.FinalMult` import. The new library is
`GramDefect20261015`; historical libraries remain available separately
because inherited declaration names overlap.

Run from the repository root:

```powershell
python -B -X utf8 scripts/extract_record_20261015.py
python -B -X utf8 scripts/finite_margin_20261015.py --output verification/gram-defect-20261015/finite-margin.json
python -B -X utf8 scripts/window_refinement_20261015.py --output output/window-refinement-20261015.json
python -B -X utf8 scripts/final_record_20261015.py
python -B -X utf8 scripts/bundle_record_20261015.py
```

These scripts check exact arithmetic and reproducible assembly. Actual
Lean and independent-kernel verification are separate checks, whose
receipts belong in `verification/gram-defect-20261015`.

Local verification is distinct from website acceptance. The supplied
upload is not an officially accepted record until the site's verifier
accepts it against the then-current record.

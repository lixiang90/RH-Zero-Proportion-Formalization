# Refinement of the nine point Gram defect bound

The exact candidate is

\[
\kappa=\frac{39282451209654051457408555553}
{58319774788300000000000000000}
=0.673570008667708719595754467355\ldots.
\]

It exceeds the [accepted master-of-puppets4 record](https://www.riemannzeta.fun/submissions/master-of-puppets4),
\(667801670564118872522651/991436171500000000000000\), by approximately
\(6.7191492529210\times10^{-11}\) in the proportion, or
\(6.7191492529210\times10^{-9}\) percentage points. This is a numerical
certificate refinement of the existing method.

## The counting identity

The same nine point window, pair weights and gap pressures are used. Its
total pressure is \(B=436674/10^8\). A uniform local certificate with floor
\(c\), together with a proved window bound \(h\le H_W\), gives

\[
\kappa=\frac{h-B}{1-c}.
\]

The counting bridge retains all multiplicities, reflected off-line pairs,
and the deletion and span errors. It first yields the actual simple
critical-line count. Inclusion then gives the distinct critical-line count;
dyadic summation gives both cumulative conclusions. Every lower constant
\(\kappa-\varepsilon\), \(\varepsilon>0\), holds for sufficiently large heights.

## Finer integer certificate

The preceding certificate uses
\(c_0=85638285/10^{10}\). Increasing its numerator by one at that denominator
fails one branch, \(rc38\). Its limiting leaf has integer margin
\(331924437510001200\), while a coarse threshold unit costs
\(335544320000000000\).

Multiplying the objective and Farkas integers and their common denominator
by 1000 leaves the real objective unchanged. Increasing the new numerator
by 989 gives

\[
c=\frac{85638285989}{10^{13}}
=c_0+9.89\times10^{-11}.
\]

The bottleneck margin remains positive:

\[
1000(331924437510001200)-989(335544320000000000)
=71105030001200000>0.
\]

The same 48 root branches, five cut subtrees and eight root-cover conditions
are retained. Discovery used native evaluation; the published module retains
the original soundness proofs and kernel certificate checks. The fixed real
pair weights, pressure and span capacities remain unchanged. The bottleneck
is a feature of this certificate, not a proved global minimum of its objective.

## Sharper window enclosure

Let \(\theta=\sqrt2/2\). The same twenty term exponential Taylor estimate,
cosine monotonicity and identity \(\sin^2\theta+\cos^2\theta=1\) give

\[
\frac{707106781186547524400844362104}{10^{30}}
\le\theta\le
\frac{707106781186547524400844362105}{10^{30}},
\]
\[
\cos\theta\le\frac{760244597075630151253567702555}{10^{30}},\qquad
\sin\theta\ge\frac{649636939080062444129454621098}{10^{30}}.
\]

With the unchanged rational upper bound for \(\pi\), these imply

\[
h=\frac{672168410564118874775945444401}{10^{30}}\le H_W.
\]

The enclosure recovers rounding loss; it does not change the window. The
finite-certificate improvement supplies nearly all of the gain.

## Source and formal environment

The starting proof is R. Arun Chandru's
[accepted Lean source](https://github.com/josusanmartin/riemann/blob/65c71d512f51df92bec4a3d1edb6a795fc1cac63/submissions/master-of-puppets4/proof/Solution.lean),
building on Samuel Lavery's nine point certificate and the attributed AM
window development. The source notices, inherited licenses and modification
notices are retained. New refinements are by Li Xiang.

The proof uses Lean 4.33.0-rc2, Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129` and Zeta23
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. The two historical and current
libraries are separate because their inherited declarations share names;
build or import `GramDefectRecord` for this result.

All five proof modules and the public umbrella compiled with the pinned
ordinary Lean kernel. The six final roots passed a fresh transitive axiom
audit. Independent nanoda replay checked 74,963 declarations with no errors,
permitting only `propext`, `Classical.choice` and `Quot.sound`.

The [verification receipts](../verification/gram-defect-20261014/formal-kernel.json)
bind the exact published source bytes. The
[independent receipt](../verification/gram-defect-20261014/independent-kernel.json)
binds the five public modules, their artifacts, the exported proof graph and
the fixed verifier binaries. The initial directory-wide guard also saw an
unrelated audit artifact created during replay; its failed guard receipt is
retained. No existing source or artifact changed, and all public proof inputs
and the already checked export remained identical.

The site has not received or accepted this candidate. Local modular kernel
verification and the site's whole-file resource checks are separate.

# Regular local phase form: exact identity, existing overlap and one fixed pilot

This is a static mathematical review. It produces no solver run, cover, Lean theorem, new scalar sampling table or zero-proportion claim. The removable-pole identity below is valid, but is an algebraic rewrite of the local decomposition already present in `window_phase_hermitian_audit.txt`, section 3. It is not a new mathematical lower bound or a new breakthrough by itself.

## Actual kernel and conventions

Use the already defined actual kernel `WindowKernel.k 24 WindowKernel.d24` and physical Fourier mode numbers `j=1,...,24`. Write

```text
theta = sqrt(2)/2,
Z = K(0) = sin(theta)/theta = sqrt(2)*sin(theta) > 0,
alpha = theta*cos(theta)/sin(theta),
d_j = NewWindows.nums24(j-1)/10^9,
S(delta) = Real.sinc(pi*delta).
```

The factor `pi` is part of S. This is not `Real.sinc(delta)`. The actual finite-sinc identity and normalization are `WindowKernel.K_eq_sinc`, `K_zero` and `K_zero_pos`. The inherited generic identities `AMW.term_closed` and `AMW.KMT_eq_gamma` give the individual integer mode and the base term. No twelve-mode aggregate identity is substituted for the actual 24-mode kernel.

Fix an integer `1<=n<=24`, put `delta=x-n`, and assume `abs(delta)<=1/4`. Then define

```text
D_n(x) = (-1)^n / (1 - 2*pi^2*x^2),

C_n(x) = d_n*x/[Z*(x+n)]
       + (-1)^n*delta * {
           2*alpha*pi^2*x/(2*pi^2*x^2-1)
           + (1/Z)*sum(j=1..24, j!=n)
                    d_j*(-1)^j*x/(x^2-j^2)
         }.
```

The regular identity is

```text
k(x) = C_n(x)*S(delta) + D_n(x)*cos(pi*delta).       (R)
```

Here C and D are rational **functions of x with fixed actual real constants** `pi`, Z and alpha. Their coefficients are not all rational numbers. Any finite rational enclosure of those constants is an inequality certificate, not an equality replacing them by rational approximations.

## Derivation, including the integer point

The normalized base identity is

```text
KMT(x)/Z = [cos(pi*x)-2*alpha*pi*x*sin(pi*x)]
           /(1-2*pi^2*x^2).
```

Substitute `cos(pi*x)=(-1)^n*cos(pi*delta)` and
`sin(pi*x)=(-1)^n*pi*delta*S(delta)`. Its two contributions become exactly D and the first term inside the braces of C. The disappearance of Z from D is the exact identity `theta*sin(theta)/Z=theta^2=1/2`; it is not a missing normalization factor.

For `j!=n`, the inherited mode formula gives

```text
(d_j/(2*Z))*[sinc(pi*(x-j))+sinc(pi*(x+j))]
 = (d_j/Z)*(-1)^j*x*sin(pi*x)/[pi*(x^2-j^2)]
 = (-1)^(j+n)*(d_j/Z)*x*delta*S(delta)/(x^2-j^2).
```

The active mode must be handled before using that formula. For every x in the stated well, including `x=n`, periodicity and the definition at zero give

```text
sinc(pi*(x-n)) = S(delta),
sinc(pi*(x+n)) = delta*S(delta)/(x+n),
(d_n/(2*Z))*[...+...] = d_n*x*S(delta)/[Z*(x+n)].
```

At `delta=0`, the second sinc is zero and S(0)=1. The last equality therefore retains the exact active-mode value `d_n/(2*Z)`. It does not involve division by delta. In particular,

```text
k(n) = d_n/(2*Z) + (-1)^n/(1-2*pi^2*n^2).          (C)
```

The accompanying symbolic audit checks the rational cross-multiplications after these stated trigonometric substitutions. The periodicity, sinc identity at zero and actual Fourier identification are the mathematical input from the cited definitions/lemmas; the symbolic audit is not a Lean proof of them.

## Why the coefficients stay regular

On this closed well,

```text
x+n >= 2*n-1/4 >= 7/4,
abs(x-j) >= abs(n-j)-1/4 >= 3/4       (j!=n),
x+j >= n+j-1/4,
abs(x^2-j^2) >= (abs(n-j)-1/4)*(n+j-1/4) > 0.
```

Using `pi>3` and `x>=3/4`,

```text
pi^2*x^2 - 1/2 > 73/16 > 0.
```

Thus every nonactive denominator is uniformly separated from zero. Its sign is fixed by whether `j<n` or `j>n`. Interval division must retain that sign. C and D are smooth and bounded on this well; explicit coefficient/derivative enclosures can use the existing proved primitive constant intervals and rational interval arithmetic. No such new uniform C/D certificate is supplied here.

There is no need to multiply by `prod(j=1..24)(x^2-j^2)`. That product is zero at x=n and would turn a kernel equation into a vacuous equality there. Clearing only nonactive denominators would be legitimate because they are nonzero, but introduces unnecessary high degree. Retaining separate reciprocal variables and their signed bounds is another possible algebraic encoding.

For n>24, omit the active term and include all 24 modes in the sum. Negative wells follow from actual kernel evenness with consistent parity. The n=0 quarter-well is not covered: it meets the base poles `+/-theta/pi`, so the base would need its own regularization. This issue is outside positive separated spans `x>=123/128`.

## This identity was already available

The prior Hermitian audit, section 3, writes

```text
k(x) = [d_n*x/(Z*(x+n))]*S(delta)
       + A_n(x)*sin(pi*x) + B(x)*cos(pi*x),
B(x)=1/(1-2*pi^2*x^2).
```

Equation (R) is exactly that formula after absorbing `pi*delta*S(delta)` into the regular coefficient. Section 3a also gives a smooth all-mode sinc sum. The prior 40-point diagnostic includes both resonant integer centres and nearby points. Repeating a pointwise reconstruction check for (R) would repeat that identity diagnostic.

The joint-cycle work already retains actual signed cosine factors and the all-mode correction. Its full-triangle numerical rank can drop at integer phases; a generic numerical inverse must not be used through such a drop. The old phase/KKT work already added two shared Hermitian PSD layers, edge Toeplitz links, phase arcs and thousands of functional phase-versus-span facets. Merely adding those PSD/arc/graph ingredients again is also a duplicate.

One practical distinction of (R) is that its coefficients are regular rational functions, while the only remaining local oscillation is the explicit pair `(S(delta),cos(pi*delta))`. This can reduce an amplitude-freezing loss if those variables are retained jointly. That is a possible implementation advantage, not an established strengthening or positive margin.

## Phase, rank and signs that must be retained

For each edge let

```text
h_e = S(delta_e), c_e = cos(pi*delta_e),
s_e = sin(pi*delta_e) = pi*delta_e*h_e.
```

On `abs(delta_e)<=1/4`, c is positive: `c_e>=sqrt(2)/2`; S is also positive. A simple centre-preserving bound is

```text
1 - pi^2*delta_e^2/6 <= h_e <= 1.                  (S)
```

It follows by integrating `1-u^2/2<=cos(u)<=1` in the standard sinc integral on this small interval. In particular (S) forces `h_e=1` at delta=0. The equation `pi*delta_e*h_e=s_e` alone does **not** do so and would again lose the active-mode information at the centre. Tighter polynomial bounds are possible, but are not computed here.

The circle relation is

```text
c_e^2 + pi^2*delta_e^2*h_e^2 = 1.
```

The actual unshifted cosine/sine are `(-1)^n_e*c_e` and `(-1)^n_e*s_e`. Discarding the parity or allowing an arbitrary sign for c changes the formula for the cross term in

```text
w(x_e) = (C_n(x_e)*h_e + D_n(x_e)*c_e)^2.
```

Do not replace this signed square by independent squares or by cosine magnitudes. In particular D is positive for odd n and negative for even n on the positive domain; C need not have a fixed sign.

For real node positions, `z_i=exp(i*pi*p_i)` and `H_ij=conj(z_i)*z_j` give a Hermitian matrix with diagonal 1, PSD and **rank one**. The second layer must be derived as `z_i^2`, not chosen independently. PSD alone or two independent rank-one layers do not impose that relation. The real cosine Gram matrix has rank at most two, but rank at most two and PSD alone still do not identify the node angles with the real positions. Signed sine orientation, the local arcs and the position/phase relations remain necessary.

For a triangle with all three spans in quarter-wells, real span addition gives

```text
n_ij+n_jk=n_ik,
delta_ij+delta_jk=delta_ik,
s_ik=s_ij*c_jk+c_ij*s_jk,
c_ik=c_ij*c_jk-s_ij*s_jk.
```

The integer equality follows because its difference is an integer of absolute value at most 3/4. Without all those quarter-well assumptions, the labels may have a nonzero carry and the corresponding parity factor must be included. Reverse edges require conjugation: cosine is unchanged and sine changes sign.

These exact nonpolynomial graph/rank relations are not automatically represented by a finite four-degree position-moment vector. Retaining them can therefore define a stronger outer model. Its strength must be demonstrated: if they are immediately replaced by independent fourth-degree scalar envelopes and coefficient hulls, this may only repackage the already tried quartic position model. A convex PSD relaxation still admits mixtures; exact rank-one constraints are nonconvex. No claim of tractable exact rank enforcement or exclusion is made here.

## One fixed, feasible pilot design; no run

Use the actual positive-ledger triangle **vertices (6,7,8)**. It is selected structurally because its two adjacent gaps are precisely those exchanged by swap (6,7), not by a new point scan. All three ledger weights are positive. Freeze all other gaps at 1 and use the coherent band

```text
abs(g6-2)<=1/32, abs(g7-1)<=1/32,
abs(g6+g7-3)<=1/32.
```

Every gap is at least `31/32>123/128`. The one exact anchor is

```text
g6=65/32, g7=31/32, all other gaps=1.
x67=65/32, x78=31/32, x68=3;
n67=2, n78=1, n68=3;
delta67=1/32, delta78=-1/32, delta68=0.
```

Thus this one anchor tests a removable centre and both odd/even raw cosine signs. At the centre edge use (C), with no divided-by-delta expression. The two off-centre local phases are conjugate; their product is the local phase 1 of the centre edge. The raw edge cosines have signs `+,-,-`, exactly as their labels 2,1,3 prescribe.

A future bounded pilot should retain these three actual regular kernel equations, (S), the circle and triangle-addition relations in the **same variables**, then inspect whether a proposed relaxed witness extends to them. No optimization, witness extension or coefficient-interval generation is performed by this note. A successful identity check at the anchor alone would add no new evidence beyond the old audit. A useful result would instead be a rigorous incompatibility or a strictly improved, fully paid inequality for the chosen coherent band. It would remain a local three-edge result, not a full-cell or global energy certificate.

The current full-eight-swap exact 714 point need not supply actual phase variables at all. It cannot be declared invalid for these new relations until a precise extension problem is constructed and rigorously resolved. Likewise, the previously tried phase PSD model cannot be declared superseded just because (R) is regular.

`identity-dependencies.json` records the exact sources and prior audits used. `local-phase-files.json` freezes this new static package. No old file or proof manifest is changed.

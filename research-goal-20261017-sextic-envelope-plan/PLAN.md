# A coherent sextic analytic envelope, conditional next gate

This is a mathematical specification, not a constructed model or a proof of a
new zero proportion. No solver, scalar sampler or Lean job is authorized by
this document. The current target remains `c=11/1250` on the original cell
`r001000001000100110011001`.

## Why the distinction matters

Extending shared moments from degree four to degree six tests the same
polynomials against more squares. If an ordinary nine-variable point satisfies
all those polynomials, its Dirac moments satisfy every order of this same
hierarchy. In that case, increasing moment order alone cannot exclude the
point. This statement is about that fixed polynomial outer approximation; the
point need not be an actual stationary point of the kernel energy.

A different step is to replace the lost analytic information by additional,
more accurate function envelopes. The proposed next gate does this with one
coherent normalized-W jet provider, while retaining old rows when sound. It
does not change the Fourier profile, ledger, target or underlying positions.

## Actual scalar input

Let w be the actual normalized squared 24-mode kernel. For each original
positive ledger edge choose one fixed anchor p inside its complete cell span,
and let R bound the distance to p throughout that span. Use the already
published normalized-W integer Taylor coefficients, with the already proved
global order-24 bound, to obtain actual point intervals

    abs(w^(j)(p)-mu_j) <= eps_j,   j=0,...,6,

where all eps_j are nonnegative rational numbers. Derive one complete-span
bound `abs(w^(7))<=M7` using q=7,d=16 cell enclosures and the same order-24
remainder; `q+d+1=24`. Every selected grid cell and every endpoint interval
must be independently replayed and eventually checked in Lean. Existing
generic APIs do not instantiate these particular finite inputs automatically.
Finite checks must retain `R>=0`, `M7>=0`, and containment of the complete
real segment between the anchor and every permitted span.

No old w-prime literal table or old anchor energy interval is identified with
normalized W by assumption. In particular, absolute w-value jets include j=0,
so this construction can avoid depending on the old F0 packet altogether.

## Lower energy polynomial and gradient envelope

Write d=s-p, where abs(d)<=R. Define

    T6(d) = sum(j=0,...,6) mu_j*d^j/j!,
    A6(d) = eps0+eps1*R
          +(eps2/2+eps3*R/6)*d^2
          +(eps4/24+eps5*R/120)*d^4
          +(eps6/720+M7*R/5040)*d^6.

Taylor's theorem with a complete-segment seventh-derivative bound, the
triangle inequality and `abs(d)^(2k+1)<=R*d^(2k)` give

    T6(d)-A6(d) <= w(s) <= T6(d)+A6(d).

The odd seventh-order energy remainder is bounded by `M7*R*d^6/7!`.
It is not the sixth-order derivative remainder below.

For w-prime define

    U5(d) = sum(j=1,...,6) mu_j*d^(j-1)/(j-1)!,
    E6(d) = eps1+eps2*R
          +(eps3/2+eps4*R/6)*d^2
          +(eps5/24+eps6*R/120)*d^4
          +M7*d^6/720.

Then `abs(w'(s)-U5(d))<=E6(d)`. The last denominator is 6!, because
the order-six remainder of w-prime involves the seventh derivative of w.
These inequalities retain the same nine normalized gap variables in all
edge spans and powers; independent edge moments are not introduced.

For the actual energy `F=pressure+sum_e a_e*w(s_e)` with a_e>=0 set

    L6 = pressure+sum_e a_e*(T6_e-A6_e),
    P5_r = b_r+sum_(e contains r) a_e*U5_e,
    Err6_r = sum_(e contains r) a_e*E6_e.

At an actual free minimum with F<c, necessarily

    L6<c,
    Err6_r+P5_r>=0,  Err6_r-P5_r>=0.

As abs(y_s)<=1, also `Err6_r +/- y_s*P5_r>=0`. All these scalar
polynomials have degree at most six and therefore fit the canonical 5005
monomials through degree six. Do not use the reversed sign `P5_r-Err6_r>=0`.
At this moment order the new degree-six inequalities are scalar constraints
(M0 localizers). Multiplying one by an M1 square basis would produce
degree-eight entries, which are absent from the 5005-monomial layout.
The derivative envelope E6 is proved separately by Taylor's theorem; it
must not be obtained by differentiating the absolute error bound A6.

## Exact comparison before any large solve

There is no automatic ordering between independently built quartic and
sextic rational envelopes: anchor choices, interval widths and remainder
payments all matter. Preserve sound old constraints and add the new ones.
Only an exact violated new inequality at a previously feasible rational
point proves strict strengthening there. Float residuals are hints only.

If the pending fixed rank-one outer-feasibility pilot produces a verified
ordinary point, evaluate the new L6 and all new gradient inequalities at that
exact point first, with no repair. If no new inequality fails, report that
limitation before authorizing any larger solver. If the pilot finds no point,
that is not a proof of nonexistence and the moment extension may still be
useful. Neither outcome is an actual counterexample to the desired floor.

The static construction must first pass a resource gate: factor span powers,
retain the exact old-moment prefix, move only the distinguished old slack
column 714 to 5004, and do not duplicate thousands of full Fraction matrix
entries when a multiplier-times-monomial description suffices. A new scalar
energy condition used for exclusion must be unsoftened; diagnostic slack
cannot make it disappear. Root authorization of a numerical solve is a
separate decision after the mathematical and resource gates.

## What this does not establish

No point intervals, seventh-derivative finite packet, sextic matrix model,
strict exclusion, global cover, new unconditional kappa, independent nanoda
replay or website submission is supplied here. The plan also does not close
the old quartic model's separate analytic-to-Lean literal obligations.

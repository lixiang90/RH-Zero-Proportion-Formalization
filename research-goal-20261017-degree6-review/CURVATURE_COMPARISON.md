# Finite-swap curvature integral: exact equivalence and possible certificate value

This is a theoretical evaluation only. No numerical pilot, new point, solver or Lean is run.

Fix the same swap (6,7). Put `h=g6-g7>0`, `v=-e6+e7`, and `f(t)=F(g+t*h*v)`. Then `g+h*v=swapGap(g,6,7)`. The segment is in the original orthant because its two changing coordinates are convex combinations of g6 and g7. It need not remain in the artificial cell.

For this frozen cell, even the independent adjacent bounds give

`h >= (64179-64062)/32768 = 117/32768 > 0`.

At a genuine relevant minimum all nine coordinates are free, so `grad F(g)·v=0`. Twice applying the fundamental theorem of calculus gives

```text
DeltaF = F(g+h*v)-F(g)
       = h^2 * integral(t=0..1) (1-t)*v^T HessF(g+t*h*v) v dt.   (I)
```

There is **no extra factor 1/2** outside this integral. A constant curvature Q gives integral Q/2. The pressure part is linear and has zero Hessian; its first-order contribution disappears only after using the actual stationary equation. Without stationarity, add `h*grad F(g)·v` to (I).

Because h is strictly positive, the weighted-curvature condition `integral(...)>=0` is exactly equivalent to the actual swap inequality DeltaF>=0 under KKT. Thus it is algebraically implied by the exact swap67 global-competitor condition plus stationarity. It is not a new independent necessary condition in that exact system.

It is not implied by the Hessian at the starting point alone. Abstractly, `f(t)=t^2-2*t^4` has f'(0)=0 and f''(0)=2>0 but f(1)-f(0)=-1. This is an example about the logical implication, not a counterexample involving the actual zeta kernel. Along-path curvature information can still matter even when the starting Hessian is PSD.

The previously used approximate D4 upper bounds and approximate KKT rows need not imply an independently paid upper bound on this curvature integral. Consequently a new integral certificate can be quantitatively stronger, despite giving no new exact condition. It may avoid explicit pressure cancellation and first-derivative error payments. No improvement for the current cell is established without comparing the actual paid bounds.

## Exact quartic integration formula

For an edge write `sigma_e=span_e(v)=sum(r in edge) v_r` in {-1,0,1}, and `x_e(t)=x_e+t*h*sigma_e`. The 33 unchanged positive edges have sigma=0; only the eight changed positive edges enter the directional curvature. Their squared incidence is 1:

```text
v^T HessF(g+t*h*v) v = sum(changed e) a_e*w''(x_e+t*h*sigma_e).
```

Choose a scalar anchor p_e, put d_e=x_e-p_e and q_e=h*sigma_e. Define

```text
J_r(d,q) = integral(t=0..1) (1-t)*(d+t*q)^r dt
         = sum(k=0..r) choose(r,k)*d^(r-k)*q^k/[(k+1)*(k+2)].
```

In particular J0=1/2 and

```text
J1=d/2+q/6,
J2=d^2/2+d*q/3+q^2/12,
J3=d^3/2+d^2*q/2+d*q^2/4+q^3/20,
J4=d^4/2+2*d^3*q/3+d^2*q^2/2+d*q^3/5+q^4/30.
```

Suppose `abs(w^(r+2)(p_e)-mu_r)<=eps_r` for r=0..4 and `abs(w^(7))<=M7` throughout the old-to-image scalar path. Let R bound `abs(d+t*q)` along that whole path. Then an upper bound for the integral of w-double-prime is the quartic

```text
sum(r=0..4) mu_r*J_r/r! + Err,
Err = (eps0+eps1*R)/2
    + (eps2/2+eps3*R/6)*J2
    + (eps4/24+M7*R/120)*J4.
```

The fifth-order remainder is integrated using

`abs(d+t*q)^5 <= R*(d+t*q)^4`.

Thus J4 is retained; it is not replaced by R^4. J2 and J4 are nonnegative because they are integrals of nonnegative even powers with nonnegative weight, even though their expanded mixed coefficients can have either sign. The factors 1/2, 1/24 and 1/120 come from J0 and Taylor factorials, not sampled maxima.

The old and image span bounds determine a path interval by their convex hull. R and M7 must cover that interval; an old-cell-only bound is insufficient when the swap leaves the cell. A single scalar anchor valid on this hull can be used for each changed edge. Summing the eight bounds with their positive ledger weights gives a quartic upper bound on the curvature integral, not directly on DeltaF. Multiplying by h^2 gives a degree-six upper bound on DeltaF.

This fits a degree-six position lift, but its quartic integral row need not be an exact linear combination of the previously paid D4 and P3/E4 rows. Such a relation would have to compare their independent remainder and anchor-error payments; algebraic equality of the actual functions alone does not establish it.

## Actual API and remaining cost

`WindowSecondVariation.directional_hasDerivAt_at` and `curvature_eq_second_deriv`, together with the actual energy's smoothness and `WindowKKTInstance.of_relevant`, supply the derivative interpretation. A new weighted-integral/FTC lemma would connect them to (I); the current pointwise Hessian theorem does not already state (I).

The proposed w-double-prime jets 0..4 are actual w derivative orders **2..6**. Existing normalized W coefficients support their translation using `WindowFixedDerivative.interval`, with q=2..6 and d=23-q. M7 can use `WindowCellDerivative.interval` at **q=7,d=16**, whose order-24 remainder has power **17** and factorial 17. Those are additional finite point/grid checks, not new transcendental samples or a new analytic profile. Their scope and numerical usefulness have not been measured here.

An alternative exact FTC formula uses averaged w-prime along the swap path and avoids high-order jets entirely, but then needs rigorous bounds on that correlated integral. Merely replacing Taylor remainder by interval hulls does not guarantee a tighter result. Neither alternative is run by this review.

The conclusion is therefore conditional and limited: the integral is a potentially better certificate representation of an already valid global competitor, not an additional exact optimality axiom. At h=0 the divided interpretation fails; one would separately use the starting Hessian condition. The present cell's positive h bound avoids that issue.

## The parent's one fixed evaluation, recorded as a limitation

During this static review, the parent separately saved `research-goal-20261017-stationary-swap/stationary-swap-static.json`. It evaluates one fixed normalized-W q7,d16 packet on the latest exact 714 moments, with 391 whole-path grid cells. Its reported expectation of the upper curvature polynomial is **positive**, approximately 0.0815639630321, comprising central value 0.05761163138 and error payment 0.02395233165. It therefore does not separate that point. This review does not re-execute that producer or independently certify its arithmetic; the separate numerical auditor owns that check.

The positive result gives no new cut for this packet and no evidence of strict projection shrink. It does not prove the exact integral condition is redundant in every finite relaxation, or that every alternative payment must fail. No further trial is proposed or run here.

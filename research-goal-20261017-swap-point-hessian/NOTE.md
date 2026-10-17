# One Hessian-localizer test at the new eight-swap point

The fixed test found no negative eigenvalue hint. It stops without another
decomposition, direction, solver or joint model. Minimum/maximum numerical
eigenvalue hints are0.0064287987476066965 and7.422877379724315. Positive
floating eigenvalues are not an exact PSD certificate.

The tested714 coordinates are exactly
`Fraction(str(float(raw_primal_hint[:714])))`, with energy slack fixed0,
and equal the newly frozen `swap-family-exact-primal.json` coordinates.
No coordinate, threshold, scalar bound or old point was adjusted.

All41 edge quadratic upper polynomials are taken unchanged from the frozen
quartic Hessian-localizer package. The90x90 matrix is rebuilt edge by edge
at the new moments, in the same physical gap-direction/affine-basis order.
No normalized radius is incorrectly inserted as a physical-direction factor.
The exact matrix SHA256 is
`103d4e856493e83fb7376d038ecc448011abffb503a78cdc507691345e3b1d16`.
The frozen lower bounds make all nine physical gaps strictly above SEP;
the same actual-Hessian, Taylor and table premises as the old package apply.

The completed eight-swap SCS model did not include this90x90 Hessian
condition. The present test therefore supplies a separate diagnostic on
its one returned point. It does not prove full joint-model feasibility or
infeasibility, actual minimizer existence in the cell, or an exclusion.

There is one durable `eigh-started.json` marker and one saved numerical
`eigh-once-hint.json`. The script refuses another call if either exists.
Because the minimum hint was positive, no integer vector was quantized
and no exact negative quadratic witness was attempted. All source/input
hashes are unchanged. No Lean, new cover or new zero proportion is claimed.

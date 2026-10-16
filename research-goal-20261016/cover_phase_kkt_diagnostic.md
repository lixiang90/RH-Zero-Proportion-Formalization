# Two fixed-cell phase/KKT diagnostic: inconclusive after 20 rounds

The cases, in order, are `r001000001000001101011101` and
`r001000001000001110011100`, using each `before` cell from the frozen
`cover-curvature-parent64.input.json.gz`. The target remains 11/1250.
No running cover, threshold, existing certificate or Lean source was changed.

Both models retain every old gap/derivative multi-facet graph, DBM and KKT
row. They add two shared 10 by 10 Hermitian phase matrices, one 3 by 3
Toeplitz moment matrix per pair, exact phase interval/arc rows, and the
five-harmonic derivative relations with the separate uniform rational
coefficient-error payments. The functional variant additionally retains
8,210/8,362 cos/sin-versus-span graph facets. The uniform packets and phase
graph oracle are supplied separately by `window-phase-uniform-progress-files.json`;
their new analytic interfaces are not Lean theorems.

For at most 20 rounds per model/case, HiGHS selects a primal and negative
eigenvectors select necessary PSD cuts. Every cut vector is first rounded
to Gaussian integers; its exact integer square-norm expansion generates
the LP row. This avoids treating numerical eigenvalues as proof objects.

| Model/case | Rational cuts | Final L1 KKT residual hint | Negative matrices | Smallest eigenvalue hint |
| --- | ---: | ---: | ---: | ---: |
| Interval/arc, case 0 | 867 | 0 | 45 | -0.8270403744 |
| Interval/arc, case 1 | 869 | 0 | 45 | -2.1693446203 |
| Functional graph, case 0 | 703 | 0 | 28 | -1.1234914287 |
| Functional graph, case 1 | 642 | 0 | 25 | -0.9034543686 |

The finite outer LPs gave no positive-residual/infeasibility hint. Their
primal matrices still have substantial negative eigenvalues, so they do
not establish feasible PSD primals either. The result is inconclusive for
the strong shared-phase relaxation. It does not extend the earlier weak
free-phase counterexample into a counterexample for this stronger model.

Replacing only the final functional model's phase entries by the actual
linked rank-one phases at its gap point satisfies the phase graph rows to
floating tolerance, but violates some uniform derivative relation rows:
the largest deficits are about 0.000511908 and 0.024199841. Thus the added
relations are not automatically redundant. This replacement is a diagnostic,
not a feasible primal certificate.

Four lossless gzip archives retain all LP histories, exact cut vectors and
coefficients, final primals, phase intervals and coefficient payments.
`cover_phase_kkt_cut_replay.py` runs with `python -S` and independently
checks all 3,081 cut expansions, 720 phase interval rows and 164 uniform
payment expressions. These arithmetic ingredient checks pass. They do not
prove the uniform packets' analytic connection, certify all primal LP
inequalities as exact, prove PSD feasibility, or supply a strict Farkas
certificate. Decimal interpretations of the final primals even violate
some retained cuts by small amounts (up to about 7.4e-8).

Replay from the repository root, for each `NAME` in `case0`, `case1`,
`graph-case0`, `graph-case1`:

```text
python -S -B -X utf8 research-goal-20261016/cover_phase_kkt_cut_replay.py --input research-goal-20261016/cover-phase-kkt-NAME.json.gz --output replay-NAME.json
```

This experiment is stopped at the fixed budget. There is no new cell
exclusion, global energy floor, unconditional proportion theorem or
submission-ready record. The finite actual-gradient sampling diagnosis is
separately pinned by `cover-gradient-mixture-files.json`.

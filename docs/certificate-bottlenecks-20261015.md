# Fixed-certificate bottlenecks and conditional research ceilings

This supplement analyzes the existing certificate. **It proves no stronger
zero-proportion bound and is not included in the current certified gain.**
The ceilings below constrain fixed numerical witnesses and conditions; they
are not global mathematical upper bounds.

The current result uses \(c=N/10^{20}\), with
\(N=859538525913875481\), and
\(\kappa=(h-B)/(1-c)\). Keep the current window floor \(h\), pressure \(B\)
and weights fixed. If a root has smallest original integer margin \(m\),
its unchanged witnesses permit at most

\[
N_{\max}=859538456469471854+
\left\lfloor\frac{m}{335544320000000000}\right\rfloor.
\]

## The five tightest roots

Gains in the last column are relative to the current certified result.
Every larger score is conditional on strengthening all other conflicting
witnesses; the rows are not independently achieved new lower bounds.

| Root | Limiting bit position | Maximum fixed-root \(N\) | Conditional \(100\kappa\) | Conditional gain, percentage points |
|---|---:|---:|---:|---:|
| 34 | 43828 | 859538525913875481 | 67.3581220659004% | 0 |
| 36 | 36040 | 859538602700661977 | 67.3581221180710% | \(5.21705635\times10^{-8}\) |
| 10 | 46897 | 859538626724399179 | 67.3581221343932% | \(6.84927977\times10^{-8}\) |
| 9 | 13588 | 859538963725758193 | 67.3581223633590% | \(2.97458635\times10^{-7}\) |
| 5 | 12223 | 859539023594025695 | 67.3581224040348% | \(3.38134400\times10^{-7}\) |

Root 34 is the present bottleneck. Improving only its limiting leaf need
not reach root 36's ceiling: another leaf in root 34 may intervene.

Among the 108 root conditions, the tightest is the cover interval
`[28160,28575]` for gap index 1, tied with its reflected index 6 condition.
Its fixed integer limit is \(N\le859704225699355536\). If all conflicting
local roots could be strengthened without changing the other inputs, this
condition would cap the formula at **67.3582346460202%**, approximately
**0.000112580119814 percentage points** above the current result. That
conditional value has not been proved attainable. Changing the cover or
weights also changes this particular ceiling.

## Where further work is most useful

First, revisit the limiting cells with finer partitions, additional valid
tangents or better dual witnesses. The current threshold is maximal only
for the frozen witnesses and denominator, so this is the most direct
remaining certificate question. Second, optimize pair weights and gap
pressures jointly against \((h-B)/(1-c)\), then certify the span capacities
and complete cover again. Neither program has been completed here, and
neither guarantees an improvement.

Further Taylor terms have negligible remaining value in the current
enclosure. At \(\theta^2=1/2\), the next alternating terms are
\(1/(2^{17}34!)\) for cosine and \(1/(2^{18}37!)\) for sinc. Keeping the
accepted \(\pi\) bound and \(P_{AM}^{+}\) fixed, exact rational comparisons
place the resulting window expression below \(h+10^{-40}\). Thus higher
Taylor order alone cannot increase the current window numerator at its
\(10^{40}\) denominator. Even allowing a finer rational denominator, the
conditional remaining gain is less than \(6.04\times10^{-39}\) percentage
points at the current \(c\). Sharpening other analytic inputs would be a
different calculation. No additional Lean theorem is claimed here.

## Reproduction and evidence

Run `python -B -X utf8 scripts/analyze_certificate_potential_20261015.py`.
The [script](../scripts/analyze_certificate_potential_20261015.py) uses exact
`Fraction` arithmetic for every threshold, score and comparison; decimals
are for display. Its [JSON output](../output/fixed-certificate-potential-20261015.json)
binds the input [finite replay receipt](../verification/gram-defect-20261015/finite-margin.json)
and [exact-score receipt](../verification/gram-defect-20261015/exact-score.json)
by SHA256, and records exact conditional fractions alongside the table.

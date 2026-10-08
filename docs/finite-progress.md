# Existing expanded certificate: finite Lean formalization

2026-10-08. New mathematical research is paused. The target remains
`805260/100000000`, yielding `66812491/99194740`.

The site contract accepts only `propext`, `Quot.sound` and `Classical.choice`.
No `native_decide`, custom axiom or placeholder is used in the new file.
`FiniteCertificate.lean` currently contains actual proof terms for complete
real box-dual soundness, positive-scale transport, two safe anchor cuts,
the stronger-frame exterior branch and exact rational target arithmetic.
Compilation awaits the compatible Mathlib environment being prepared by root;
these statements are not yet represented as a compiled full certificate.

The fixed existing JSON contains 62881 positive sparse multipliers. Each is
an integer divided by `10^9`; numerator maximum needs 58 bits and row<360.
There are 15017 distinct numerators. Fixed 72-bit (row+numerator) literals
would occupy 1139055 hexadecimal characters. A dictionary with 14-bit
value indices and 9-bit rows uses 361566 hexadecimal characters in the
stream plus approximately 253466 in the dictionary.
The 241 cell gap/span geometries need 13496 words, at most 67480 hexadecimal
characters at width20. There are 924 extra-point occurrences and 237 points.
Thus a naive append to the old 1675641-byte Solution exceeds the 2MB limit.
Variable-frequency/delta encoding or removing genuinely unused old assembly
declarations is needed; no change to the mathematical certificate is required.

Reusable proved upstream interfaces are `ptl_sound`/individual `PTL_i_ok`,
`tangent_valZ`, generic `mcheckGZ_sound`, and the PCell `CovBy`,
`cov_gmidC`, `cov_rmidC`, `cupd_ok` APIs. The final PC8CL `walk_ok`
hardcodes `Pg 805003`; it cannot directly prove the stronger-or-low-cell
cover. A new generic cover traversal must prove that predicate while
preserving the old bit cursors, closure splits and leaf guards.
The 241 emitted cells alone are not a kernel proof of their completeness.

Remaining finite work: checked compact data decoding; kernel checks of each
rational certificate; physical cut/row soundness from original proofs;
negative-cycle/continuous-closure soundness; complete strong-or-low cover;
then all 2399 domains and the exterior branch assemble the uniform F9 claim.
The file does not yet claim that uniform theorem or site submission validity.

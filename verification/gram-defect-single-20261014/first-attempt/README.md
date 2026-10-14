# First whole-file compilation

The first upload assembly had SHA-256
`87d1beb3103b7ab7a45ad9883bd71d6353325476914eb249d5df33fbfb2a10aa`
and 1,938,602 UTF-8 bytes. Fresh Lean compilation exited 1 after 493.766
seconds. The complete log and original compilation receipt are preserved
here.

The only errors were in the dyadic and cumulative website wrappers: their
`simpa only` lists did not rewrite the separately named trusted `Ncount` and
`N0star` definitions to the structurally identical Zeta23 definitions. The
refined certificate, analytic proof and counting theorems reported no errors.
The repair adds explicit equality lemmas proved by `rfl` and uses them in
both wrappers. It does not change the mathematical bound or counting
definitions. A fresh compilation and independent replay of the repaired
whole file are required; this failed receipt is not verification evidence
for the final upload.

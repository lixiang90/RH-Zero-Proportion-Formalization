Finite global-competitor cut union: 19 closed regions
===================================================

At an original global minimum, every whole-cell feasible finite competitor
has nonnegative energy difference. An affine upper bound U on that difference
therefore gives the necessary cut U>=0. Joint coordinate OBBT combines
nonnegative multiples of these cuts, an energy sublevel minorant and an
exact difference-constraint flow. This operation preserves original global
minima below the target; it does not preserve arbitrary KKT points.

The inclusive cut pilot independently verifies 47 paths, 76 rounds and 700
coordinate bounds, closing 12 regions. The signed-difference hypograph
variant independently verifies 47 paths, 74 rounds and 658 bounds, closing
11 regions. Its scalar spans select separate full-capacity rational upper
mixtures. Different LP witness selections have complementary successes;
neither search output uniformly replaces the other. The earlier cut pilot,
the inclusive pilot and the hypograph pilot together close 15 distinct
regions. Intersecting the two independently valid hulls and applying Newton
to the 32 remaining paths closes four more regions. That entire paired
chain, including 78 additional Newton rounds, has independently replayed.

The compact standalone archive selects one complete witness chain for each
of these 19 mutually nonnested regions. It retains only necessary old tree
ancestors and the 307 old branch records below these regions. All prior
OBBT and Newton witnesses are present. Global-cut affine aggregates,
energy mixtures, cell bounds, flow amounts and costs are reconstructed
losslessly, checked against canonical source-step hashes, and then checked
by the independent arithmetic verifiers. No LP or flow optimizer runs in
the decoder or replayer. Neither the original large OBBT JSON nor the
41,029-node old snapshot is needed to replay this archive.

The 19 regions have no ancestor/descendant overlap with the previously
verified 24 finite-move regions or the separate joint-gradient seven.
Thus the finite-competitor total is 43 topmost regions, covering 558 old
branch records together with the earlier 251. These are local gains from
a fixed partial old snapshot, not a complete minimizer cover. The numerical
pilot targets c=0.00884; the separately running complete-cover search uses
c=0.0088. Their proof obligations must not be conflated.

Only the 19 projected closing chains are included in this small package.
Full-sample receipts pin the original local producer outputs; nonclosing
pilot chains remain reproducible from the producer and earlier OBBT archive
but are not included as large raw JSON files. The paired energy-only control
classifies six inclusive-pilot regions as closed versus twelve with the
cuts; all six are shared. Its terminal classifications are diagnostic
because that control did not retain final leaf witnesses.

Current-frontier negative diagnostics are retained locally: among 11
surviving c=0.0088 cells, adding multiple upper anchors or allowing moves
whose midpoint comparison is positive gave no additional closures. Full
affine reflections T_C(g)=C-g, with whole-cell orthant feasibility and the
correct pressure difference b.C-2b.g, also gave zero strict whole-cell
closures on those 11 cells and a fixed 47-cell sample. They do not count as
new proofs, and these negative experiments were not expanded.

Complete-global-cover, actual-analytic-bridge-complete,
new-zero-proportion-proven and final-submission-ready flags remain false.
This progress does not establish an unconditional zero-proportion record.

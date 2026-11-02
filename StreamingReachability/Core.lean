module

public import StreamingReachability.Core.BatchCorrectness
public import StreamingReachability.Core.ClosureDistances
public import StreamingReachability.Core.RoundingGraph
public import StreamingReachability.Core.Scheduling
public import StreamingReachability.Core.OrdinaryScan
public import StreamingReachability.Core.WordBounds
public import StreamingReachability.Core.Regression
public import StreamingReachability.Core.FusedDriver
public import StreamingReachability.Core.Main
public import StreamingReachability.Core.DriverRegression

/-!
# Deterministic streaming bounded-distance core

`Skeleton.build` is an actual one-pass, target-deduplicating bounded-row
construction. Its update function reads only the current edge, stored rows, and
the public block/known sets. `BlockSearch.actual_gap` derives the manuscript's
gap witness from this construction and actual multi-source Bellman--Ford,
without assuming a search or accuracy certificate. `search_correct_and_cost`
proves doubling termination, exact newly found numerators, the exact next
numerator, and the geometric reservation bound.

`BatchAPI.deterministic_core` closes the actual global driver, its I1--I4
coupling, distinct-insertion charge, shared restricted/reversed batch packing,
and sparse output correctness. Its hypotheses are positive input weights,
positive integer scale, actual block sizes, and `2*x*x ≤ n`; no accuracy,
skeleton, scheduling, or resource certificate is an input.

`Request.workspace` means the block-size bound **x**, not the packing capacity:
packs reserve `|B|*threshold` cells against **n**. The runtime keeps sparse
per-query labels and sparse active block caches. All scheduled block searches
finish before external sources are inserted. Found vertices retain their true
unrounded block numerators. Ordinary scans use frozen old settled sources;
the implementation uses in-memory Bellman--Ford instead of Dijkstra on each
stored skeleton, since local computation time is not measured.

`runGuardedMeasured` checks the original-block weighted record charge before
allocating new records, including found sets in failed doubling phases. Its
`.result` erases to `runGuarded`; `.passes` survives abort. On every execution,
`runGuardedMeasured_pass_bound` gives
`(R+1)*(log₂ x+3) + 32*x*allowance/n`. The raw batch bound has constant 16 and
weighted sparse reply charge in place of allowance. `runGuarded_coupled`
proves that the guard returns the raw result exactly when that raw charge fits.

`runGuarded_every_prefix_space` bounds the concrete live round/task/update,
row/BF, ordinary-candidate, partial-cache, registry, and serialization buffers
by `256*(n+allowance+1) + 4*Live.catalogCells`. The catalog term stores H0,
blocks, distinct search sets and descriptors once; the read-only input stream
is not stored. `runGuardedMeasuredViewed` fuses an endpoint-local option view
into those scans, without allocating its semantic `filterMap` input.

`DriverWordBounds` derives stored numerator bounds `A*R` and actual intermediate
BF-label bounds `A*R+n*W` from the driver, including unfinished searches.
`WordBounds` gives the resulting logarithmic payload-bit bound and bounded
row keys. IDs, clocks, input scan counters and catalog/budget sizes retain
their explicit public-parameter bounds; polynomial-weight/size instantiation
belongs to the caller. The omitted larger-x workspace variant is not asserted.
-/

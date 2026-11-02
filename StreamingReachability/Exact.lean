module

public import StreamingReachability.Exact.Resources
public import StreamingReachability.Exact.QueryProgramBounds
public import StreamingReachability.Exact.Tests

/-!
# Exact SSSP from positive-integer approximate SSSP

This component proves the mathematics of the **current** `exact.tex` reduction.
It does not import an RHM theorem or assume a smooth-distance certificate.
`Exact.exactSSSP_correct` assumes only the local accuracies of the actual
positive-integer approximation queries in `Exact.exactSSSPTrace`. The input is
the actual edge stream, represented semantically by `StoredEdges.graphOfEdges`;
parallel work/depth guarantees are outside this component.

## Explicit integer realization, not a verbatim fractional outer update

The paper leaves the integer discretization in RHM Appendix C.1 unspecified.
Here it is realized by a proved integer-shift variant:

* Outer potentials are nonnegative integers. A residual edge of weight `w` is
  replaced, for smoothing, by `P*w+1`, where `P = 64*(n+1)`.
* There are `t = 32*(2*bits+9)` smoothing rounds. Labels are integers in fixed
  units `C = 100*(t+1)`, and the slope increases by one each round. The additive
  error goes from `2^t` to `1`; denominators therefore never compound.
* Each round constructs the actual two half-width-shifted level graphs.
  `partial_smoothing` proves their envelope sandwich and additive-error
  halving, including the short smoothing-path and shifted-bin arguments.
  The exact envelope occurs only in proofs, never in the algorithm.
* `roundedUpdate` chooses the first safe common shift from `n+1` candidates
  using only stored labels. The finite pigeonhole argument and the safety of
  floor rounding on **zero residual edges** are proved in `Rounding`.
  The update stays feasible and halves each integer residual distance with
  downward rounding. `bits+1` outer iterations therefore give exact distances.
* `positive_oracle` proves the `theta*w+1` wrapper, including recognition of
  zero distances. Rational approximation outputs may first be floored, by
  `floor_preserves_accuracy`.
* Oversized answers are capped before retention. `exact_guarded_raw_correct`
  proves that a successful raw approximation is never invalidated by these
  guards on a successful prefix. Storage and query bounds also cover failed
  executions.

For input weights at most `n^a`, `inputBits n a = (a+4)*(log2 n+1)` is an explicit
bit budget. Preprocessing uses this known upper bound instead of spending a
pass finding the maximum input weight; using the maximum is also covered by
the more general preprocessing lemmas. We prove `n*w+1` path decoding,
sentinel reachability, and a genuine one-edge-at-a-time parent-selection pass.
The selected parents are well-founded and preserve exact original distances,
even for zero-weight cycles and unreachable vertices.

## Streaming interfaces

`BaseDescriptor` and `LevelDescriptor` store only endpoint vectors and scalar
parameters. Their `local` theorems prove exactly which original edge is emitted
and with which weight. `EdgeTransducer.base_graph`, `level_graph`, and
`preprocessing_graph` prove the graph semantics of the real map/filter edge
transducers, including duplicate edges. `oracle_edge_count` gives `m+2n`.
`exactSSSP_local` proves that every generated query has one of these descriptors.
All between-call label and potential updates are explicit vector operations;
no exact-distance computation is hidden in them.

`DescriptorProgram.exact source exponent` is the **computable descriptor-only
free query program** supplied to the streaming compiler. Its constructors are
`Request.base`, `Request.level`, and one final `Request.parents` scan. The
runtime definition takes neither a semantic graph nor an edge list. It builds
the descriptors directly from materialized `Vector` buffers, rather than
extracting witnesses from `HasLocalDescriptor`. Replies are guarded and decoded
before retention; finite shift selection and all vector updates are executable.
The compiler knows the global preprocessing parameters `source` and `n^exponent`
and interprets every base/level descriptor against that preprocessed stream.

`DescriptorProgram.exact_eq` proves unconditional equality with `exactSSSP`
under graph/stream interpretation. `exact_trace_eq` proves equality of the
physical positive-query trace, not just of the final answer.
`exact_protocol_bounds` proves finite distinct clocks and the exact call count
for **every reply handler**, without a semantic graph or an accuracy assumption;
`exact_one_parent_scan` proves there is exactly one final parent-selection scan.
Semantic graphs and the input stream occur only in `interpretReply` and the
interpretation theorems, never as fields of the runtime request/program data.

`OuterState` and `SmoothState` describe actual reachable loop states and prove
unconditional potential/label word bounds. `Workspace` gives the concrete
vector/buffer/parent-register layout and a finite-word encoding. The streaming
compiler can use these invariants with its own metered pass semantics; this
module itself is the deterministic, oracle-generic reduction, not a second
definition of the project's streaming machine.

This generic descriptor program retains no query history. The composed
streaming compiler conservatively accounts for its replay cache and metering
history; their polylogarithmic call count preserves near-linear space.
Every query has a distinct explicit clock, so arbitrary fresh answer sequences
are supported even when two requested graphs happen to be identical.

## Main closed interfaces

* `Exact.exactSSSP_correct`: exact decoded distances, exact parent-tree
  distances, and well-foundedness, conditional only on actual query accuracies.
* `Exact.exactSSSP_call_count`: at most
  `2308*(a+4)^2*(log2 n+1)^2` approximation calls.
* `Exact.exactSSSP_query_bounds`: on every guarded execution, positive integer
  weights at most `(2*n)^(2000*(a+4))` and requested accuracy denominator at most
  `20000000*(a+4)*(log2 n+1)`, on `n` or `n+1` vertices.
* `Exact.exactSSSP_fresh_clocks`: distinct clocks for all actual calls.
* `Exact.DescriptorProgram.exact`: constructive runtime query program;
  `exact_eq`/`exact_trace_eq` are its implementation-refinement theorems.
* `Exact.workspaceBits_bound`: the explicit register layout has a
  `600000*(a+4)*n*(log2 n+1)`-bit capacity.

The probability of all approximation calls succeeding and the compilation of
these edge-local descriptors into metered passes are composed by the surrounding
streaming development, rather than assumed as mathematical facts here.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : ℕ := 0
  for (name, _) in env.constants.toList do
    if (`StreamingReachability.Exact).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless axiomName == `propext || axiomName == `Classical.choice ||
            axiomName == `Quot.sound do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Exact reduction audit: {checked} declarations; only standard Lean foundations."

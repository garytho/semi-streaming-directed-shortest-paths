# Semi-Streaming Reachability and Shortest Paths in $n^{1/3+o(1)}$ Passes

[![Lean build](https://github.com/garytho/semi-streaming-directed-shortest-paths/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/garytho/semi-streaming-directed-shortest-paths/actions/workflows/lean.yml)

Single-source reachability asks which vertices of a directed graph $G=(V,E)$ are reachable from a given source $s$. Likewise, single-source shortest paths asks for a shortest path tree in $G$ rooted at a given source $s$. In the graph streaming model, edges arrive one at a time in an arbitrary order, and the algorithm may make multiple passes over the stream. The semi-streaming model permits $\widetilde O(n)=O(n\log^{O(1)} n)$ space, where $n=|V|$. We obtain improved streaming algorithms for single-source reachability and shortest paths in directed graphs.

**Theorem (Streaming shortest paths).** There is a randomized streaming algorithm that, with high probability, computes exact single-source shortest paths in $n$-vertex directed graphs with nonnegative, polynomially bounded integer edge weights, using

$$
\widetilde O(n)\text{ space}
\qquad\text{and}\qquad
n^{1/3+o(1)}\text{ passes}.
$$

We give a Lean verification of this theorem. The main statement is [`StreamingSSSP.streaming_sssp`](StreamingSSSP/Main.lean):

```lean
namespace StreamingSSSP

theorem streaming_sssp (exponent confidence : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ passConstant : ℝ, 0 < passConstant ∧ ∃ spaceConstant spaceDegree bitConstant threshold : ℕ,
      513 ≤ threshold ∧ ∀ n ≥ threshold, ∀ source : Fin n, ∀ input : List (StoredEdges.Edge n),
        (∀ e ∈ input, e.weight ≤ n ^ exponent) →
        (1 - 1 / (n : ℝ) ^ confidence ≤
          (Exact.Implementation.Measured.evaluate source exponent confidence input).prob
            (fun out => Exact.Implementation.CorrectResult input source out.result.result)) ∧
        Early.Sampling.Holds (Exact.Implementation.Measured.evaluate source exponent confidence input)
          (fun out =>
            (out.passes : ℝ) ≤ passConstant * (n : ℝ) ^ (1 / 3 + epsilon) ∧
            Exact.Implementation.Measured.workingCells exponent confidence out ≤
              spaceConstant * n * Parameters.ell n ^ spaceDegree ∧
            ∃ encoded : List (Fin (2 ^ Exact.Implementation.Measured.wordBits n exponent confidence)),
              encoded.map Fin.val = Exact.Implementation.Measured.traceWords out.result.trace ∧
                encoded.length = (Exact.Implementation.Measured.traceWords out.result.trace).length) ∧
        Exact.Implementation.Measured.wordBits n exponent confidence ≤ bitConstant * Parameters.ell n

end StreamingSSSP
```

The statement uses these definitions:

- **Input graph and distances:** [`StoredEdges.Edge` and `graphOfEdges`](StreamingSSSP/Graph/StoredEdges.lean#L9), and [`Graph.dist`](StreamingSSSP/Graph.lean#L122).
- **Streaming model:** [`Metered` and `readPass`](StreamingSSSP/StreamingModel.lean#L9) define edge-by-edge scans and peak storage; [`fusedPass`](StreamingSSSP/Streaming/FusedPass.lean#L28) scans the original stream through an edge view.
- **Randomized algorithm:** [`Measured.evaluate`](StreamingSSSP/Exact/MeasuredProgram.lean#L143) defines the algorithm whose execution is measured.
- **Correct output:** [`CorrectResult`](StreamingSSSP/Exact/StreamingCorrectness.lean#L14) specifies exact distances and a shortest-path tree using original edges.
- **Probability:** [`Law` and `Law.prob`](StreamingSSSP/Probability.lean#L67), with [`Holds`](StreamingSSSP/Early/Sampling.lean#L18) expressing a property of every sampled outcome.
- **Resource measures:** the [`passes` field](StreamingSSSP/Exact/MeasuredProgram.lean#L19), [`workingCells`](StreamingSSSP/Exact/SpaceComplexity.lean#L38), and [`wordBits`](StreamingSSSP/Exact/WordComplexity.lean#L20).


The proof uses only Lean's standard foundational axioms:

- [`propext`](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#propositional-extensionality): propositional extensionality.
- [`Classical.choice`](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#choice): the axiom of choice.
- [`Quot.sound`](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#quotients): quotient soundness.

[`Audit.lean`](StreamingSSSP/Audit.lean) checks that all imported project declarations use only these axioms.

The [build workflow](.github/workflows/lean.yml) runs `lake build`, including the axiom audit, on every push and pull request. Click the badge above for build logs.

To reproduce with Lean and mathlib **v4.35.0**:

```sh
lake exe cache get
lake build
```

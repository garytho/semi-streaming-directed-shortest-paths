# Semi-Streaming Shortest Paths in $n^{1/3+o(1)}$ Passes

Single-source reachability asks which vertices of a directed graph $G=(V,E)$ are reachable from a given source $s$. In the graph streaming model, edges arrive one at a time in an arbitrary order, and the algorithm may make multiple passes over the stream. The semi-streaming model permits $\widetilde O(n)=O(n\operatorname{polylog}n)$ space, where $n=|V|$.

**Theorem (Streaming shortest paths).** There is a randomized streaming algorithm that, with high probability, computes exact single-source shortest paths in $n$-vertex directed graphs with nonnegative, polynomially bounded integer edge weights, using

$$
\widetilde O(n)\text{ space}
\qquad\text{and}\qquad
n^{1/3+o(1)}\text{ passes}.
$$

We give a Lean verification of this theorem. The main statement is [`StreamingReachability.streaming_sssp`](StreamingReachability/Main.lean):

```lean
namespace StreamingReachability

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

end StreamingReachability
```

Here `exponent` bounds edge weights by $n^{\mathtt{exponent}}$, `confidence` gives success probability at least $1-n^{-\mathtt{confidence}}$, and every $\epsilon>0$ yields an eventual $O(n^{1/3+\epsilon})$ pass bound.

The proof uses only Lean's standard foundational axioms:

- [`propext`](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#propositional-extensionality): propositional extensionality.
- [`Classical.choice`](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#choice): the axiom of choice.
- [`Quot.sound`](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/#quotients): quotient soundness.

[`Audit.lean`](StreamingReachability/Audit.lean) checks that all imported project declarations use only these axioms.

Build with Lean and mathlib **v4.35.0**:

```sh
lake exe cache get
lake build
```

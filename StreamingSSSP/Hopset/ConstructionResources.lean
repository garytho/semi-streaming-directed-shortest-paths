module

public import StreamingSSSP.Hopset.ConstructionResourceCertificate
public import StreamingSSSP.Hopset.InputScaling

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n : ℕ}

def guessScale (n wmin wmax : ℕ) : ℕ := wmin * 2 ^ guessExponent n wmin wmax

def executionCount (n confidence wmin wmax : ℕ) : ℕ :=
  Parameters.ell n * (((confidence + 16) * Parameters.ell n) * (guessExponent n wmin wmax + 1))

def physicalWeight (n accuracy x wmin wmax : ℕ) : ℕ :=
  Parameters.queryUnit n accuracy x * (wmax + 8 * guessScale n wmin wmax)

theorem guesses_scale (n wmin wmax : ℕ) (hwmin : 0 < wmin) :
    ∀ delta ∈ guesses n wmin wmax hwmin, delta.val ≤ guessScale n wmin wmax := by
  intro delta hd
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
  have hJ : j ≤ guessExponent n wmin wmax := by have h := List.mem_range.mp hj; omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hJ)

theorem graph_positive (input : List (StoredEdges.Edge n)) (hp : ∀ e ∈ input, 0 < e.weight) :
    ∀ u v, u ≠ v → (1 : Distance) ≤ StoredEdges.graphOfEdges input u v := by
  intro u v _
  apply (StoredEdges.le_graphOfEdges_iff _ u v _).mpr
  intro e he _ _
  exact WithTop.coe_le_coe.mpr (hp e he)

theorem empty_store_bounds (G : Graph (Fin n)) (accuracy x total weight : ℕ) :
    StoreBounds G accuracy x total weight 0 (emptyRepresentation n) :=
  ⟨emptyRepresentation_valid G x, by simp [emptyRepresentation, volume],
    by simp [emptyRepresentation], by simp [emptyRepresentation], by simp [emptyRepresentation]⟩

theorem construct_certificate (hn : 0 < n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) :
    let count := executionCount n confidence wmin wmax
    let scale := guessScale n wmin wmax
    let weight := physicalWeight n accuracy x wmin wmax
    BuilderCertificate input
      (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count)
        (storeCatalogLimit n accuracy count) scale weight)
      (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
      (construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n)) count
      (StoreBounds (StoredEdges.graphOfEdges input) accuracy x count weight count) := by
  let count := executionCount n confidence wmin wmax
  let scale := guessScale n wmin wmax
  let weight := physicalWeight n accuracy x wmin wmax
  let G := StoredEdges.graphOfEdges input
  change BuilderCertificate input
    (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count)
      (storeCatalogLimit n accuracy count) scale weight)
    (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
    (construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n)) count
    (StoreBounds G accuracy x count weight count)
  have hweight : scale * (8 * Parameters.queryUnit n accuracy x) ≤ weight := by
    dsimp only [scale, weight, physicalWeight]
    nlinarith
  have h := stages_certificate input G hn accuracy x count weight scale ha hp
    (fun u v => Graph.dist_le_edge G u v) (graph_positive input hp) hweight
    (guesses n wmin wmax hwmin) (guesses_scale n wmin wmax hwmin)
    ((confidence + 16) * Parameters.ell n) (Parameters.ell n) (emptyRepresentation n) 0
    (empty_store_bounds G accuracy x count weight) (by
      simp only [guesses_length, Nat.zero_add]
      exact le_refl (executionCount n confidence wmin wmax))
  have he : 0 + Parameters.ell n * (((confidence + 16) * Parameters.ell n) *
      (guesses n wmin wmax hwmin).length) = count := by
    simp only [guesses_length, Nat.zero_add, count, executionCount]
  simpa only [construct, Nat.zero_add, guesses_length, count, executionCount] using h

theorem BuilderFits.passes {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) {x radius records catalogWords scale weight word draws calls count : ℕ}
    {P : Implicit.Representation n → Prop} {out : Report n (Implicit.Representation n)} (hn : 0 < n)
    (h : BuilderFits (QueryBounds x radius records catalogWords scale weight) word draws calls count P out)
    (ha : Actual view input auxiliary out) (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight) :
    out.passes ≤ (count * calls) * passLimit n x radius records := by
  have hsum := List.sum_le_sum (l := out.calls) (f := Call.passes)
    (g := fun _ => passLimit n x radius records) (fun call hm => by
      rw [ha.2 call hm]
      exact (h.calls_valid call hm).passes hn view input auxiliary hp)
  calc
    out.passes = (out.calls.map Call.passes).sum := ha.1
    _ ≤ (out.calls.map (fun _ => passLimit n x radius records)).sum := hsum
    _ = out.calls.length * passLimit n x radius records := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ h.calls_le

end StreamingSSSP.Hopset.Measured

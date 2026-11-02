module

public import StreamingReachability.Core.GlobalCommit

@[expose] public section

namespace StreamingReachability.Core.Global

open StoredEdges

variable {n b : ℕ}

theorem round_invariant (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < p.scale)
    {old : State n b} {r : ℕ} (h : Invariant p input old r) :
    Invariant p input (round hn p input r old) (r + 1) := by
  let results : Vector (BlockResult n) b :=
    Vector.ofFn fun i => searchOne hn p input r i (old.blocks.get i)
  let U := newVertices p input r old results
  have hr : ∀ i, SearchInvariant p input old.settled r i (old.blocks.get i) (results.get i) := by
    intro i
    simpa only [results, Vector.get_ofFn] using
      searchOne_invariant hn p input hA h.1 i (old.blocks.get i) (h.2 i)
  have hU : ∀ v, v ∈ U ↔ target p input v = (r : Distance) :=
    newVertices_exact p input hp hA h.1 h.2 results hr
  change Invariant p input
    { labels := SparseLabels.addNew old.labels U (r : Distance)
      settled := old.settled ∪ U
      blocks := Vector.ofFn fun i => insertExternal p r U i (results.get i).state } (r + 1)
  constructor
  · exact global_commit p input h.1 U hU _
  · intro i
    simpa only [Vector.get_ofFn] using
      insertExternal_invariant p input hA h.1 i (h.2 i) (results.get i) (hr i) U hU

theorem execute_invariant (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < p.scale) (r : ℕ) :
    Invariant p input (execute hn p input r) r := by
  induction r with
  | zero => exact initial_invariant p input
  | succ r ih => exact round_invariant hn p input hp hA ih

def output (hn : 0 < n) (p : Problem n b) (input : List (Edge n)) (R : ℕ)
    (v : Fin n) : Distance :=
  let final := execute hn p input (R + 1)
  if v ∈ final.settled then SparseLabels.get final.labels v else ⊤

theorem core_distance_correct (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < p.scale) (R : ℕ) (v : Fin n) :
    output hn p input R v =
      if (fullQueryGraph input p.blocks.toList p.scale).dist p.source v ≤ (R : Distance)
      then (fullQueryGraph input p.blocks.toList p.scale).dist p.source v else ⊤ := by
  have h := (execute_invariant hn p input hp hA (R + 1)).1
  have hmem : v ∈ (execute hn p input (R + 1)).settled ↔ target p input v ≤ (R : Distance) := by
    rw [h.settled_iff, distance_lt_succ_iff]
  have ht : target p input v = (fullQueryGraph input p.blocks.toList p.scale).dist p.source v :=
    queryGraph_dist_eq_full input p.blocks.toList p.scale p.source v
  unfold output
  by_cases hv : v ∈ (execute hn p input (R + 1)).settled
  · rw [ite_eq_left hv, ite_eq_left (ht ▸ (hmem.mp hv))]
    exact (h.label_exact v (by rw [h.label_support]; exact Finset.mem_union_left _ hv)).trans ht
  · rw [ite_eq_right hv, ite_eq_right (fun hd => hv (hmem.mpr (ht.symm ▸ hd)))]

def membershipRecords (s : State n b) : ℕ :=
  ∑ i : Fin b, (s.blocks.get i).known.length

def searchCount (s : State n b) : ℕ :=
  ∑ i : Fin b, (s.blocks.get i).charge.searches

def reservationCount (s : State n b) : ℕ :=
  ∑ i : Fin b, (s.blocks.get i).reservations

theorem execute_search_charge (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < p.scale) (r : ℕ) :
    searchCount (execute hn p input r) ≤ membershipRecords (execute hn p input r) := by
  apply Finset.sum_le_sum
  intro i _
  have hi := (execute_invariant hn p input hp hA r).2 i
  have hc := ScheduleCharge.searches_le _ hi.charge_valid
  rw [hi.insertion_count, ← SparseLabels.length_eq_card _ hi.known_unique] at hc
  exact hc

theorem execute_reservation_charge (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < p.scale) (x r : ℕ)
    (hx : ∀ i, (p.blocks.get i).card ≤ x) :
    reservationCount (execute hn p input r) ≤
      8 * x * membershipRecords (execute hn p input r) := by
  unfold reservationCount membershipRecords
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := (execute_invariant hn p input hp hA r).2 i
  let bs := (execute hn p input r).blocks.get i
  have hbudget := hi.reservation_bound
  have hc := ScheduleCharge.searches_le _ hi.charge_valid
  have hlen := SparseLabels.length_eq_card bs.known hi.known_unique
  have hcount := hi.insertion_count
  have hmul := Nat.mul_le_mul_right (bs.charge.insertions + bs.charge.searches)
    (Nat.mul_le_mul_left 4 (hx i))
  nlinarith only [hbudget, hc, hcount, hlen, hmul]

end StreamingReachability.Core.Global

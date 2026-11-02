module

public import StreamingSSSP.Exact.Descriptors

@[expose] public section

namespace StreamingSSSP.Exact

open StoredEdges

variable {V : Type*} [Fintype V]

theorem preprocess_weightsBounded (G : Graph V) (s : V) (W : ℕ)
    (hW : WeightsBounded G W) :
    WeightsBounded (preprocess G s W) (sentinel (Fintype.card V) W) := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hA := affine_weightsBounded G W (Fintype.card V) 1 hW
  intro u v w hw
  by_cases ha : affineGraph G (Fintype.card V) 1 u v = ⊤
  · have hs : sentinelGraph s (sentinel (Fintype.card V) W) u v = (w : Distance) := by
      simpa [preprocess, Graph.union, ha] using hw
    unfold sentinelGraph at hs
    split_ifs at hs with he
    · have heq : sentinel (Fintype.card V) W = w := WithTop.coe_eq_coe.mp hs
      omega
    · simp at hs
  · lift affineGraph G (Fintype.card V) 1 u v to ℕ using ha with z hz
    have hwz : w ≤ z := WithTop.coe_le_coe.mp (by
      have hh := min_le_left (affineGraph G (Fintype.card V) 1 u v)
        (sentinelGraph s (sentinel (Fintype.card V) W) u v)
      change preprocess G s W u v ≤ affineGraph G (Fintype.card V) 1 u v at hh
      rw [hw, ← hz] at hh
      exact hh)
    have hzW := hA u v z hz.symm
    unfold sentinel
    nlinarith

theorem edge_list_weightsBounded {n : ℕ} (edges : List (Edge n)) (W : ℕ)
    (hW : ∀ e ∈ edges, e.weight ≤ W) : WeightsBounded (graphOfEdges edges) W := by
  intro u v w hw
  obtain ⟨e, he, _, _, hew⟩ := exists_edge_eq edges (u := u) (v := v) (by simp [hw])
  have hew' : e.weight = w := WithTop.coe_eq_coe.mp (hew.trans hw)
  simpa [hew'] using hW e he

def inputBits (n exponent : ℕ) : ℕ := (exponent + 4) * (n.log2 + 1)

theorem inputBits_bounds (n exponent : ℕ) (hn : 0 < n) :
    n ≤ 2 ^ inputBits n exponent ∧ sentinel n (n ^ exponent) ≤ 2 ^ inputBits n exponent := by
  by_cases hn1 : n = 1
  · subst n
    have hp : 2 ^ 1 ≤ 2 ^ (exponent + 4) := by gcongr; omega
    norm_num [inputBits, sentinel] at hp ⊢
    omega
  · have hn2 : 2 ≤ n := by omega
    have hnbase : n ≤ 2 ^ (n.log2 + 1) :=
      Nat.le_of_lt ((Nat.log2_lt (by omega)).mp (by omega))
    have hp : sentinel n (n ^ exponent) ≤ n ^ (exponent + 3) := by
      have hpow : n * n ^ exponent + 1 ≤ n ^ (exponent + 2) := by
        have hpositive : 0 < n ^ exponent := by positivity
        rw [show exponent + 2 = (exponent + 1) + 1 by omega, pow_succ, pow_succ]
        nlinarith [Nat.mul_le_mul_right (n * n ^ exponent) hn2]
      unfold sentinel
      calc
        n * (n * n ^ exponent + 1) ≤ n * n ^ (exponent + 2) := Nat.mul_le_mul_left n hpow
        _ = n ^ (exponent + 3) := by rw [show exponent + 3 = (exponent + 2) + 1 by omega, pow_succ]; ring
    constructor
    · have he : n.log2 + 1 ≤ inputBits n exponent := by unfold inputBits; nlinarith
      exact hnbase.trans (Nat.pow_le_pow_right (by decide) he)
    · calc
        sentinel n (n ^ exponent) ≤ n ^ (exponent + 3) := hp
        _ ≤ (2 ^ (n.log2 + 1)) ^ (exponent + 3) := by gcongr
        _ = 2 ^ ((n.log2 + 1) * (exponent + 3)) := (pow_mul _ _ _).symm
        _ ≤ 2 ^ inputBits n exponent := Nat.pow_le_pow_right (by decide)
          (by unfold inputBits; nlinarith)

theorem polynomial_weight_bound (n exponent : ℕ) (hn : 0 < n) :
    2 ^ (45 * smallBits (inputBits n exponent)) ≤ (2 * n) ^ (2000 * (exponent + 4)) := by
  have hlog : 2 ^ (n.log2 + 1) ≤ 2 * n := by
    rw [pow_succ]
    nlinarith [Nat.log2_self_le (Nat.ne_of_gt hn)]
  have hbits : 2 ^ inputBits n exponent ≤ (2 * n) ^ (exponent + 4) := by
    unfold inputBits
    rw [Nat.mul_comm, pow_mul]
    gcongr
  have hexp : 45 * smallBits (inputBits n exponent) =
      inputBits n exponent * 360 + 1620 := by unfold smallBits; ring
  rw [hexp, pow_add, pow_mul]
  calc
    (2 ^ inputBits n exponent) ^ 360 * 2 ^ 1620 ≤
        ((2 * n) ^ (exponent + 4)) ^ 360 * (2 * n) ^ 1620 := by gcongr; omega
    _ = (2 * n) ^ ((exponent + 4) * 360 + 1620) := by rw [← pow_mul, ← pow_add]
    _ ≤ (2 * n) ^ (2000 * (exponent + 4)) := by gcongr; omega

variable {n : ℕ}

structure Result (n : ℕ) where
  distances : Fin n → Distance
  parents : ParentPass.State n

noncomputable def transformedEstimates (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) : Fin n → ℕ :=
  let bits := inputBits n exponent
  exactDistances
    (nonnegativeOracle (cappedOracle (replyCap bits) positiveBase))
    (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel))
    (preprocess (graphOfEdges edges) source (n ^ exponent)) source bits

noncomputable def exactSSSP (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) : Result n :=
  let estimates := transformedEstimates positiveBase positiveLevel edges source exponent
  ⟨decode (n ^ exponent) estimates, ParentPass.run source (n ^ exponent) estimates edges⟩

noncomputable def exactSSSPTrace (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) : List (CombinedQuery (Fin n)) :=
  let bits := inputBits n exponent
  outerTrace
    (nonnegativeOracle (cappedOracle (replyCap bits) positiveBase))
    (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel))
    (preprocess (graphOfEdges edges) source (n ^ exponent)) source
    (smoothingRounds bits) (bits + 1) (fun _ => 0)

theorem transformedEstimates_correct (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ)
    (hW : ∀ e ∈ edges, e.weight ≤ n ^ exponent)
    (hs : ∀ q ∈ exactSSSPTrace positiveBase positiveLevel edges source exponent,
      PositiveAccurate positiveBase positiveLevel q) :
    ∀ v, (preprocess (graphOfEdges edges) source (n ^ exponent)).dist source v =
      (transformedEstimates positiveBase positiveLevel edges source exponent v : Distance) := by
  have hn : 0 < n := by have hh := source.isLt; omega
  have hbits := inputBits_bounds n exponent hn
  have hgraph := edge_list_weightsBounded edges (n ^ exponent) hW
  have hpre := preprocess_weightsBounded (graphOfEdges edges) source (n ^ exponent) hgraph
  apply exact_guarded_raw_correct positiveBase positiveLevel
    (preprocess (graphOfEdges edges) source (n ^ exponent)) source (inputBits n exponent)
    (by simpa using hbits.1)
    (weightsBounded_mono _ hpre (by simpa using hbits.2)) _ hs
  intro v
  obtain ⟨d, hd, hdb⟩ := preprocess_reachable (graphOfEdges edges) source (n ^ exponent) v
  exact ⟨d, hd, hdb.trans (by simpa using hbits.2)⟩

/-- The complete deterministic exact-from-approximate result. All hypotheses
about the oracle are accuracies of the actual positive-integer queries.
The RHM reduction, smoothing and tree recovery are conclusions, not hypotheses. -/
theorem exactSSSP_correct (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ)
    (hW : ∀ e ∈ edges, e.weight ≤ n ^ exponent)
    (hs : ∀ q ∈ exactSSSPTrace positiveBase positiveLevel edges source exponent,
      PositiveAccurate positiveBase positiveLevel q) :
    let result := exactSSSP positiveBase positiveLevel edges source exponent
    result.distances = (graphOfEdges edges).dist source ∧
      (ParentPass.graph result.parents).dist source = (graphOfEdges edges).dist source ∧
      WellFounded (fun u v => ∃ e, result.parents v = some e ∧ e.source = u) := by
  have hspec := transformedEstimates_correct positiveBase positiveLevel edges source exponent hW hs
  have hgraph := edge_list_weightsBounded edges (n ^ exponent) hW
  exact ⟨decode_correct (graphOfEdges edges) source (n ^ exponent) hgraph _ hspec,
    ParentPass.tree_distances source (n ^ exponent) _ edges hgraph hspec,
    ParentPass.parent_wellFounded source (n ^ exponent) _ edges⟩

theorem exactSSSP_call_count (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) :
    (exactSSSPTrace positiveBase positiveLevel edges source exponent).length ≤
      2308 * (exponent + 4) ^ 2 * (n.log2 + 1) ^ 2 := by
  rw [exactSSSPTrace, outerTrace_length]
  have hh := oracleCallCount_bound (inputBits n exponent)
  have hpos : 0 < inputBits n exponent := by unfold inputBits; positivity
  change oracleCallCount (inputBits n exponent) ≤ _
  unfold inputBits at *
  nlinarith

theorem exactSSSP_fresh_clocks (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) :
    ((exactSSSPTrace positiveBase positiveLevel edges source exponent).map queryClock).Nodup :=
  outerTrace_clock_nodup _ _ _ _ _ _ _

end StreamingSSSP.Exact

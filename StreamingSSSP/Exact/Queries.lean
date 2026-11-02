module

public import StreamingSSSP.Exact.Tree

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

structure Query (U : Type*) where
  graph : Graph U
  source : U
  denominator : ℕ
  clock : ℕ

def Query.offset {U : Type*} (offset : ℕ) (q : Query U) : Query U :=
  { q with clock := offset + q.clock }

def Query.positive (q : Query V) : Query V :=
  { q with graph := affineGraph q.graph (3 * Fintype.card V * q.denominator) 1
           denominator := 3 * q.denominator }

def Query.Accurate (q : Query V) (call : Oracle V) : Prop :=
  IntegerApprox q.graph q.source q.denominator
    (call q.graph q.source q.denominator q.clock)

def nonnegativeOracle (positiveCall : Oracle V) : Oracle V :=
  fun G source denominator clock =>
    positiveAnswer (Fintype.card V) denominator
      (positiveCall (affineGraph G (3 * Fintype.card V * denominator) 1)
        source (3 * denominator) clock)

theorem nonnegativeOracle_accurate (positiveCall : Oracle V) (q : Query V)
    (hk : 0 < q.denominator) (h : q.positive.Accurate positiveCall) :
    q.Accurate (nonnegativeOracle positiveCall) :=
  positive_oracle q.graph q.source q.denominator hk _ h

theorem nonnegativeOracle_offset (positiveCall : Oracle V) (offset : ℕ) :
    nonnegativeOracle (offsetOracle offset positiveCall) =
      offsetOracle offset (nonnegativeOracle positiveCall) := rfl

abbrev CombinedQuery (V : Type*) := Sum (Query V) (Query (Option V))

def queryClock (q : CombinedQuery V) : ℕ := q.elim Query.clock Query.clock

def offsetQuery (offset : ℕ) (q : CombinedQuery V) : CombinedQuery V :=
  q.map (Query.offset offset) (Query.offset offset)

def PositiveAccurate (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (q : CombinedQuery V) : Prop :=
  q.elim (fun q => q.positive.Accurate baseCall) (fun q => q.positive.Accurate levelCall)

noncomputable def levelTrace (call : Oracle (Option V)) (G : Graph V)
    (M : ℕ) : ℕ → ℕ → (V → ℕ) → List (Query (Option V))
  | 0, _, _ => []
  | rounds + 1, slope, labels =>
      let K := M * (2 * 2 ^ rounds)
      let H₀ := levelGraph G labels (slope + 1) (8 * K) 0
      let H₁ := levelGraph G labels (slope + 1) (8 * K) (4 * K)
      let answer₀ := call H₀ none (100 * M) (2 * rounds + 1)
      let answer₁ := call H₁ none (100 * M) (2 * rounds + 2)
      ⟨H₀, none, 100 * M, 2 * rounds + 1⟩ ::
        ⟨H₁, none, 100 * M, 2 * rounds + 2⟩ ::
        levelTrace call G M rounds (slope + 1) (partialLabels labels K answer₀ answer₁)

noncomputable def smoothingTrace (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) : List (CombinedQuery V) :=
  Sum.inl ⟨G, s, 1, 0⟩ ::
    (levelTrace levelCall G (smoothingScale rounds + rounds) rounds (smoothingScale rounds)
      (fun v => smoothingScale rounds * baseCall G s 1 0 v)).map Sum.inr

noncomputable def outerTrace (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) : ℕ → (V → ℕ) → List (CombinedQuery V)
  | 0, _ => []
  | iterations + 1, potential =>
      let offset := iterations * (1 + 2 * rounds)
      let currentBase := offsetOracle offset baseCall
      let currentLevel := offsetOracle offset levelCall
      (smoothingTrace currentBase currentLevel (positiveResidual G potential) s rounds).map
          (offsetQuery offset) ++
        outerTrace baseCall levelCall G s rounds iterations
          (potentialStep currentBase currentLevel G s rounds potential)

theorem levelTrace_length (call : Oracle (Option V)) (G : Graph V) (M rounds slope : ℕ)
    (labels : V → ℕ) :
    (levelTrace call G M rounds slope labels).length = 2 * rounds := by
  induction rounds generalizing slope labels with
  | zero => rfl
  | succ rounds ih => simp only [levelTrace, List.length_cons, ih]; omega

theorem smoothingTrace_length (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) :
    (smoothingTrace baseCall levelCall G s rounds).length = 1 + 2 * rounds := by
  simp [smoothingTrace, levelTrace_length, Nat.add_comm]

theorem outerTrace_length (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations : ℕ) (potential : V → ℕ) :
    (outerTrace baseCall levelCall G s rounds iterations potential).length =
      iterations * (1 + 2 * rounds) := by
  induction iterations generalizing potential with
  | zero => simp [outerTrace]
  | succ iterations ih =>
      simp only [outerTrace, List.length_append, List.length_map, smoothingTrace_length, ih]
      ring

theorem levelTrace_clocks (call : Oracle (Option V)) (G : Graph V) (M rounds slope : ℕ)
    (labels : V → ℕ) :
    ∀ q ∈ levelTrace call G M rounds slope labels, 1 ≤ q.clock ∧ q.clock ≤ 2 * rounds := by
  induction rounds generalizing slope labels with
  | zero => simp [levelTrace]
  | succ rounds ih =>
      intro q hq
      simp only [levelTrace, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · simp
      · simp; omega
      · have hh := ih _ _ q hq
        omega

theorem levelTrace_clock_nodup (call : Oracle (Option V)) (G : Graph V)
    (M rounds slope : ℕ) (labels : V → ℕ) :
    ((levelTrace call G M rounds slope labels).map Query.clock).Nodup := by
  induction rounds generalizing slope labels with
  | zero => simp [levelTrace]
  | succ rounds ih =>
      simp only [levelTrace, List.map_cons, List.nodup_cons]
      refine ⟨?_, ?_, ih _ _⟩
      · simp only [List.mem_cons, List.mem_map, not_or, not_exists, not_and]
        refine ⟨by omega, ?_⟩
        intro q hq he
        have hh := (levelTrace_clocks call G M rounds _ _ q hq).2
        omega
      · simp only [List.mem_map, not_exists, not_and]
        intro q hq he
        have hh := (levelTrace_clocks call G M rounds _ _ q hq).2
        omega

theorem smoothingTrace_clocks (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) :
    ∀ q ∈ smoothingTrace baseCall levelCall G s rounds, queryClock q < 1 + 2 * rounds := by
  intro q hq
  simp only [smoothingTrace, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨q, hq, rfl⟩
  · simp [queryClock]
  · have hh := (levelTrace_clocks levelCall G _ rounds _ _ q hq).2
    simpa [queryClock] using (show q.clock < 1 + 2 * rounds by omega)

theorem smoothingTrace_clock_nodup (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) :
    ((smoothingTrace baseCall levelCall G s rounds).map queryClock).Nodup := by
  simp only [smoothingTrace, List.map_cons, List.map_map, List.nodup_cons]
  constructor
  · simp only [List.mem_map, not_exists, not_and]
    intro q hq hzero
    have hh := (levelTrace_clocks levelCall G _ rounds _ _ q hq).1
    change q.clock = 0 at hzero
    omega
  · exact levelTrace_clock_nodup levelCall G _ rounds _ _

theorem levelTrace_success (positiveCall : Oracle (Option V)) (G : Graph V)
    (M rounds slope : ℕ) (labels : V → ℕ) (hM : 0 < M)
    (hs : ∀ q ∈ levelTrace (nonnegativeOracle positiveCall) G M rounds slope labels,
      q.positive.Accurate positiveCall) :
    SmoothingSuccess (nonnegativeOracle positiveCall) G M rounds slope labels := by
  induction rounds generalizing slope labels with
  | zero => trivial
  | succ rounds ih =>
      let K := M * (2 * 2 ^ rounds)
      let q₀ : Query (Option V) :=
        ⟨levelGraph G labels (slope + 1) (8 * K) 0, none, 100 * M, 2 * rounds + 1⟩
      let q₁ : Query (Option V) :=
        ⟨levelGraph G labels (slope + 1) (8 * K) (4 * K), none, 100 * M, 2 * rounds + 2⟩
      have h₀ := nonnegativeOracle_accurate positiveCall q₀ (by dsimp [q₀]; positivity)
        (hs q₀ (by simp [levelTrace, q₀, K]))
      have h₁ := nonnegativeOracle_accurate positiveCall q₁ (by dsimp [q₁]; positivity)
        (hs q₁ (by simp [levelTrace, q₁, K]))
      refine ⟨h₀, h₁, ih _ _ ?_⟩
      intro q hq
      exact hs q (by simp only [levelTrace, List.mem_cons]; exact Or.inr (Or.inr hq))

theorem smoothingTrace_success (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ)
    (hs : ∀ q ∈ smoothingTrace (nonnegativeOracle positiveBase)
      (nonnegativeOracle positiveLevel) G s rounds, PositiveAccurate positiveBase positiveLevel q) :
    FullSmoothingSuccess (nonnegativeOracle positiveBase) (nonnegativeOracle positiveLevel)
      G s rounds := by
  constructor
  · have hh := hs (Sum.inl ⟨G, s, 1, 0⟩) (by simp [smoothingTrace])
    exact nonnegativeOracle_accurate positiveBase ⟨G, s, 1, 0⟩ Nat.zero_lt_one hh
  · apply levelTrace_success positiveLevel G _ rounds _ _
    · have hp := smoothingScale_pos rounds
      omega
    · intro q hq
      exact hs (Sum.inr q) (by simp [smoothingTrace, hq])

theorem outerTrace_success (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations : ℕ) (potential : V → ℕ)
    (hs : ∀ q ∈ outerTrace (nonnegativeOracle positiveBase) (nonnegativeOracle positiveLevel)
      G s rounds iterations potential, PositiveAccurate positiveBase positiveLevel q) :
    OuterSuccess (nonnegativeOracle positiveBase) (nonnegativeOracle positiveLevel)
      G s rounds iterations potential := by
  induction iterations generalizing potential with
  | zero => trivial
  | succ iterations ih =>
      let offset := iterations * (1 + 2 * rounds)
      have hcurrent : FullSmoothingSuccess
          (offsetOracle offset (nonnegativeOracle positiveBase))
          (offsetOracle offset (nonnegativeOracle positiveLevel))
          (positiveResidual G potential) s rounds := by
        rw [← nonnegativeOracle_offset, ← nonnegativeOracle_offset]
        apply smoothingTrace_success
        intro q hq
        have hh := hs (offsetQuery offset q) (by
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨q, by simpa [nonnegativeOracle_offset] using hq, rfl⟩)
        cases q <;> exact hh
      refine ⟨hcurrent, ih _ ?_⟩
      intro q hq
      exact hs q (List.mem_append_right _ hq)

theorem affine_positive (G : Graph V) (scale : ℕ) :
    ∀ u v (w : ℕ), affineGraph G scale 1 u v = w → 0 < w := by
  intro u v w hw
  have hfinite : G u v ≠ ⊤ := by
    apply (mapWeights_ne_top G (fun z => scale * z + 1) u v).mp
    change affineGraph G scale 1 u v ≠ ⊤
    simp [hw]
  lift G u v to ℕ using hfinite with z hz
  have he : scale * z + 1 = w :=
    WithTop.coe_eq_coe.mp ((mapWeights_coe G (fun z => scale * z + 1) hz.symm).symm.trans hw)
  omega

theorem exact_positive_oracle (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (bits : ℕ)
    (hcard : Fintype.card V ≤ 2 ^ bits)
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ 2 ^ bits)
    (hs : ∀ q ∈ outerTrace (nonnegativeOracle positiveBase) (nonnegativeOracle positiveLevel)
      G s (smoothingRounds bits) (bits + 1) (fun _ => 0),
      PositiveAccurate positiveBase positiveLevel q) :
    ∀ v, G.dist s v =
      (exactDistances (nonnegativeOracle positiveBase) (nonnegativeOracle positiveLevel) G s bits v :
        Distance) :=
  exactDistances_correct _ _ G s bits hcard hreach (outerTrace_success _ _ _ _ _ _ _ hs)

end StreamingSSSP.Exact

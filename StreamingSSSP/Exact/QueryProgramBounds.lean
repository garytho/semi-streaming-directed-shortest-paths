module

public import StreamingSSSP.Exact.QueryProgramSemantics

@[expose] public section

namespace StreamingSSSP.Exact.DescriptorProgram

variable {n : ℕ}

def Request.approxClocks : Request n → List ℕ
  | .base _ _ _ clock => [clock]
  | .level _ _ clock => [clock]
  | .parents .. => []

def Request.parentScans : Request n → List Unit
  | .parents .. => [()]
  | _ => []

def levelClockList (offset : ℕ) : ℕ → List ℕ
  | 0 => []
  | rounds + 1 => (offset + (2 * rounds + 1)) :: (offset + (2 * rounds + 2)) ::
      levelClockList offset rounds

def outerClockList (rounds : ℕ) : ℕ → List ℕ
  | 0 => []
  | iterations + 1 =>
      let offset := iterations * (1 + 2 * rounds)
      (offset :: levelClockList offset rounds) ++ outerClockList rounds iterations

theorem baseQuery_clocks (reply : (request : Request n) → request.Reply)
    (potential : Labels n) (source : Fin n) (denominator clock cap : ℕ) :
    Program.trace Request.approxClocks reply
      (baseQuery potential source denominator clock cap) = [clock] := rfl

theorem levelQuery_clocks (reply : (request : Request n) → request.Reply)
    (potential labels : Labels n) (slope width shift denominator clock cap : ℕ) :
    Program.trace Request.approxClocks reply
      (levelQuery potential labels slope width shift denominator clock cap) = [clock] := rfl

theorem smoothRounds_clocks (reply : (request : Request n) → request.Reply)
    (potential : Labels n) (M cap offset rounds slope : ℕ) (labels : Labels n) :
    Program.trace Request.approxClocks reply
      (smoothRounds potential M cap offset rounds slope labels) = levelClockList offset rounds := by
  induction rounds generalizing slope labels with
  | zero => rfl
  | succ rounds ih =>
      simp only [smoothRounds, Program.trace_bind, levelQuery_clocks, ih,
        List.singleton_append, levelClockList]

theorem smoothing_clocks (reply : (request : Request n) → request.Reply)
    (source : Fin n) (potential : Labels n) (rounds cap offset : ℕ) :
    Program.trace Request.approxClocks reply (smoothing source potential rounds cap offset) =
      offset :: levelClockList offset rounds := by
  simp only [smoothing, Program.trace_bind, baseQuery_clocks, smoothRounds_clocks,
    List.singleton_append]

theorem outerRounds_clocks (reply : (request : Request n) → request.Reply)
    (source : Fin n) (rounds cap iterations : ℕ) (potential : Labels n) :
    Program.trace Request.approxClocks reply (outerRounds source rounds cap iterations potential) =
      outerClockList rounds iterations := by
  induction iterations generalizing potential with
  | zero => rfl
  | succ iterations ih =>
      simp only [outerRounds, Program.trace_bind, smoothing_clocks, ih, outerClockList]

theorem exact_clocks (reply : (request : Request n) → request.Reply)
    (source : Fin n) (exponent : ℕ) :
    Program.trace Request.approxClocks reply (exact source exponent) =
      outerClockList (smoothingRounds (inputBits n exponent)) (inputBits n exponent + 1) := by
  simp only [exact, Program.trace_bind, estimates, outerRounds_clocks,
    Program.trace, Request.approxClocks, List.append_nil]

theorem levelClockList_length (offset rounds : ℕ) :
    (levelClockList offset rounds).length = 2 * rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simp only [levelClockList, List.length_cons, ih]; omega

theorem outerClockList_length (rounds iterations : ℕ) :
    (outerClockList rounds iterations).length = iterations * (1 + 2 * rounds) := by
  induction iterations with
  | zero => simp [outerClockList]
  | succ iterations ih =>
      simp only [outerClockList, List.length_append, List.length_cons, levelClockList_length, ih]
      ring

theorem levelClockList_bounds (offset rounds : ℕ) :
    ∀ clock ∈ levelClockList offset rounds, offset < clock ∧ clock ≤ offset + 2 * rounds := by
  induction rounds with
  | zero => simp [levelClockList]
  | succ rounds ih =>
      intro clock hclock
      simp only [levelClockList, List.mem_cons] at hclock
      rcases hclock with rfl | rfl | hclock
      · omega
      · omega
      · have hh := ih clock hclock
        omega

theorem levelClockList_nodup (offset rounds : ℕ) : (levelClockList offset rounds).Nodup := by
  induction rounds with
  | zero => simp [levelClockList]
  | succ rounds ih =>
      simp only [levelClockList, List.nodup_cons]
      refine ⟨?_, ?_, ih⟩
      · simp only [List.mem_cons, not_or]
        constructor
        · omega
        · intro hm
          have hh := levelClockList_bounds offset rounds _ hm
          omega
      · intro hm
        have hh := levelClockList_bounds offset rounds _ hm
        omega

theorem outerClockList_bounds (rounds iterations : ℕ) :
    ∀ clock ∈ outerClockList rounds iterations, clock < iterations * (1 + 2 * rounds) := by
  induction iterations with
  | zero => simp [outerClockList]
  | succ iterations ih =>
      intro clock hclock
      simp only [outerClockList, List.mem_append, List.mem_cons] at hclock
      rcases hclock with (rfl | hclock) | hclock
      · nlinarith
      · have hh := levelClockList_bounds _ rounds _ hclock
        nlinarith
      · have hh := ih clock hclock
        nlinarith

theorem outerClockList_nodup (rounds iterations : ℕ) : (outerClockList rounds iterations).Nodup := by
  induction iterations with
  | zero => simp [outerClockList]
  | succ iterations ih =>
      rw [outerClockList, List.nodup_append]
      refine ⟨List.nodup_cons.mpr ⟨?_, levelClockList_nodup _ _⟩, ih, ?_⟩
      · intro hm
        have hh := levelClockList_bounds _ rounds _ hm
        omega
      · intro a ha b hb hab
        have htail := outerClockList_bounds rounds iterations b hb
        rcases List.mem_cons.mp ha with rfl | ha
        · omega
        · have hh := levelClockList_bounds _ rounds a ha
          omega

/-- Clocks and call counts do not depend on any interpretation, graph, stream,
accuracy assumption, or successful execution. -/
theorem exact_protocol_bounds (reply : (request : Request n) → request.Reply)
    (source : Fin n) (exponent : ℕ) :
    let clocks := Program.trace Request.approxClocks reply (exact source exponent)
    clocks.Nodup ∧ clocks.length = oracleCallCount (inputBits n exponent) ∧
      ∀ clock ∈ clocks, clock < oracleCallCount (inputBits n exponent) := by
  rw [exact_clocks]
  exact ⟨outerClockList_nodup _ _, outerClockList_length _ _, outerClockList_bounds _ _⟩

theorem smoothRounds_no_parent (reply : (request : Request n) → request.Reply)
    (potential : Labels n) (M cap offset rounds slope : ℕ) (labels : Labels n) :
    Program.trace Request.parentScans reply
      (smoothRounds potential M cap offset rounds slope labels) = [] := by
  induction rounds generalizing slope labels with
  | zero => rfl
  | succ rounds ih =>
      simp only [smoothRounds, Program.trace_bind, levelQuery, Program.trace,
        Request.parentScans, List.nil_append, ih]

theorem smoothing_no_parent (reply : (request : Request n) → request.Reply)
    (source : Fin n) (potential : Labels n) (rounds cap offset : ℕ) :
    Program.trace Request.parentScans reply (smoothing source potential rounds cap offset) = [] := by
  simp only [smoothing, Program.trace_bind, baseQuery, Program.trace,
    Request.parentScans, List.nil_append, smoothRounds_no_parent]

theorem outerRounds_no_parent (reply : (request : Request n) → request.Reply)
    (source : Fin n) (rounds cap iterations : ℕ) (potential : Labels n) :
    Program.trace Request.parentScans reply (outerRounds source rounds cap iterations potential) = [] := by
  induction iterations generalizing potential with
  | zero => rfl
  | succ iterations ih =>
      simp only [outerRounds, Program.trace_bind, smoothing_no_parent, List.nil_append, ih]

theorem exact_one_parent_scan (reply : (request : Request n) → request.Reply)
    (source : Fin n) (exponent : ℕ) :
    Program.trace Request.parentScans reply (exact source exponent) = [()] := by
  simp only [exact, Program.trace_bind, estimates, outerRounds_no_parent, Program.trace,
    Request.parentScans, List.nil_append, List.append_nil]

theorem baseQuery_guarded (reply : (request : Request n) → request.Reply)
    (potential : Labels n) (source : Fin n) (denominator clock cap : ℕ) (v : Fin n) :
    (Program.run reply (baseQuery potential source denominator clock cap)).get v ≤ cap := by
  simp only [baseQuery, Program.run, Vector.get_ofFn]
  unfold positiveAnswer
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact (Nat.div_le_self _ _).trans (min_le_left _ _)

theorem levelQuery_guarded (reply : (request : Request n) → request.Reply)
    (potential labels : Labels n) (slope width shift denominator clock cap : ℕ)
    (v : Option (Fin n)) :
    (Program.run reply
      (levelQuery potential labels slope width shift denominator clock cap)).at v ≤ cap := by
  simp only [levelQuery, Program.run, LevelAnswer.at_ofFn]
  unfold positiveAnswer
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact (Nat.div_le_self _ _).trans (min_le_left _ _)

theorem smoothRounds_labels_le (reply : (request : Request n) → request.Reply)
    (potential : Labels n) (M cap offset rounds slope : ℕ) (labels : Labels n) (v : Fin n) :
    (Program.run reply (smoothRounds potential M cap offset rounds slope labels)).get v ≤ labels.get v := by
  induction rounds generalizing slope labels with
  | zero => exact le_rfl
  | succ rounds ih =>
      simp only [smoothRounds, Program.run_bind]
      exact (ih _ _).trans (by
        simp only [Vector.get_ofFn]
        exact partialLabels_le _ _ _ _ v)

end StreamingSSSP.Exact.DescriptorProgram

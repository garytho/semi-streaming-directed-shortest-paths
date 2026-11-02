module

public import StreamingReachability.Exact.StreamingFresh

@[expose] public section

namespace StreamingReachability.Exact.DescriptorProgram

open scoped Classical
open StoredEdges
open StreamingReachability.Exact.Implementation

variable {n weight bound : ℕ}

def Request.rawBounds (preprocessed : List (Edge n)) (accuracy weight : ℕ) : Request n → Prop
  | .base descriptor _ denominator _ =>
      denominator ≤ accuracy ∧
        ∀ e ∈ preprocessed.map (EdgeTransducer.mapEdge descriptor.weight), e.weight ≤ weight
  | .level descriptor denominator _ =>
      denominator ≤ accuracy ∧
        ∀ e ∈ (EdgeTransducer.levelEdges descriptor preprocessed).map liftEdge ++
          virtualEdges descriptor.sourceWeight, e.weight ≤ weight
  | .parents .. => True

theorem Request.rawBounds_mono (preprocessed : List (Edge n))
    {accuracy weight accuracy' weight' : ℕ} {request : Request n}
    (h : request.rawBounds preprocessed accuracy weight)
    (ha : accuracy ≤ accuracy') (hw : weight ≤ weight') :
    request.rawBounds preprocessed accuracy' weight' := by
  cases request with
  | base => exact ⟨h.1.trans ha, fun e he => (h.2 e he).trans hw⟩
  | level => exact ⟨h.1.trans ha, fun e he => (h.2 e he).trans hw⟩
  | parents => trivial

end StreamingReachability.Exact.DescriptorProgram

namespace StreamingReachability.Exact.Implementation

open scoped Classical
open DescriptorProgram StoredEdges

variable {n weight bound : ℕ}

theorem preprocessing_raw_weights (input : List (Edge n)) (source : Fin n) (weight : ℕ)
    (hw : ∀ e ∈ input, e.weight ≤ weight) :
    ∀ e ∈ EdgeTransducer.preprocessingEdges input source weight, e.weight ≤ sentinel n weight := by
  have hn := sourcePositive source
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
    change n * raw.weight + 1 ≤ _
    have h := Nat.mul_le_mul_left n (hw raw hr)
    exact (show n * raw.weight + 1 ≤ n * weight + 1 by omega).trans
      (Nat.le_mul_of_pos_left _ hn)
  · exact (EdgeTransducer.sentinelEdges_mem source _ e).mp he |>.2.2.le

theorem base_weight_upper (descriptor : BaseDescriptor (Fin n)) (u v : Fin n)
    (w weight potential : ℕ) (hw : w ≤ weight) (hp : descriptor.potential u ≤ potential) :
    descriptor.weight u v w ≤
      descriptor.positiveScale * (descriptor.inflation * (weight + potential) + 1) + 1 := by
  unfold BaseDescriptor.weight
  gcongr
  exact (Nat.sub_le _ _).trans (Nat.add_le_add hw hp)

theorem level_weight_upper (descriptor : LevelDescriptor (Fin n)) (u v : Fin n)
    (w weight potential : ℕ) (hw : w ≤ weight) (hp : descriptor.potential u ≤ potential) :
    descriptor.weight u v w ≤
      descriptor.positiveScale * (descriptor.slope *
        (descriptor.inflation * (weight + potential) + 1)) + 1 := by
  unfold LevelDescriptor.weight
  gcongr
  exact (Nat.sub_le _ _).trans (Nat.add_le_add hw hp)

theorem level_raw_weights (preprocessed : List (Edge n)) (descriptor : LevelDescriptor (Fin n))
    (weight potential : ℕ) (hw : ∀ e ∈ preprocessed, e.weight ≤ weight)
    (hp : ∀ v, descriptor.potential v ≤ potential) (hwidth : 0 < descriptor.width) :
    ∀ e ∈ (EdgeTransducer.levelEdges descriptor preprocessed).map liftEdge ++
      virtualEdges descriptor.sourceWeight,
      e.weight ≤ descriptor.positiveScale *
        (descriptor.width + descriptor.slope * (descriptor.inflation * (weight + potential) + 1)) + 1 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
    have hmem : original ∈ preprocessed := (List.mem_filter.mp ho).1
    exact (level_weight_upper descriptor original.source original.target original.weight weight potential
      (hw original hmem) (hp original.source)).trans (by
        change _ ≤ _
        gcongr
        exact Nat.le_add_left _ _)
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    change descriptor.sourceWeight v ≤ _
    have hr := (residue_lt hwidth descriptor.shift (descriptor.labels v)).le
    unfold LevelDescriptor.sourceWeight
    gcongr
    exact hr.trans (Nat.le_add_right _ _)

theorem smoothing_reply_bounded (reply : (request : Request n) → request.Reply)
    (source : Fin n) (potential : Labels n) (rounds cap offset : ℕ) (v : Fin n) :
    (Program.run reply (DescriptorProgram.smoothing source potential rounds cap offset)).get v ≤
      smoothingScale rounds * cap := by
  simp only [DescriptorProgram.smoothing, Program.run_bind]
  have h := smoothRounds_labels_le reply potential
    (smoothingScale rounds + rounds) cap offset rounds (smoothingScale rounds)
    (Vector.ofFn (fun v => smoothingScale rounds *
      (Program.run reply (baseQuery potential source 1 offset cap)).get v)) v
  exact h.trans (by
    simp only [Vector.get_ofFn]
    exact Nat.mul_le_mul_left _ (baseQuery_guarded reply potential source 1 offset cap v))

theorem updatePotential_bounded (potential labels : Labels n) (rounds cap : ℕ)
    (hl : ∀ v, labels.get v ≤ smoothingScale rounds * cap) (v : Fin n) :
    (updatePotential potential labels rounds).get v ≤
      potential.get v + incrementBound n rounds cap := by
  have hi := (safeShiftIndex labels.get (smoothingScale rounds) (smoothingScale_pos rounds)).isLt
  simp only [Fintype.card_fin] at hi
  have hs := (shiftCandidate_bounds n (smoothingScale rounds)
    (safeShiftIndex labels.get (smoothingScale rounds) (smoothingScale_pos rounds))
    (smoothingScale_pos rounds) (by omega)).2
  simp only [updatePotential, Vector.get_ofFn, roundedUpdate, Fintype.card_fin]
  apply Nat.add_le_add_left
  exact (Nat.div_le_self _ _).trans (by
    unfold incrementBound
    have h := hl v
    omega)

theorem baseQuery_raw (preprocessed : List (Edge n))
    (hw : ∀ e ∈ preprocessed, e.weight ≤ weight) (source : Fin n) (potential : Labels n)
    (hp : ∀ v, potential.get v ≤ bound) (rounds clock : ℕ) :
    (Request.base (baseDescriptor potential 1) source 3 clock).rawBounds preprocessed
      (300 * (smoothingScale rounds + rounds))
      (smoothingQueryWeightBound n rounds (inflation n * (weight + bound) + 1)) := by
  let M := smoothingScale rounds + rounds
  let B := inflation n * (weight + bound) + 1
  have hM : 0 < M := by dsimp only [M, smoothingScale]; omega
  refine ⟨by dsimp only [M, smoothingScale]; omega, ?_⟩
  intro e he
  obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
  have h := base_weight_upper (baseDescriptor potential 1) raw.source raw.target raw.weight
    weight bound (hw raw hr) (hp raw.source)
  simp only [baseDescriptor, Nat.mul_one] at h
  simp only [EdgeTransducer.mapEdge, baseDescriptor, Nat.mul_one]
  apply h.trans
  change 3 * n * B + 1 ≤ 300 * (n + 1) * M * (B + M * (8 * 2 ^ rounds + B)) + 1
  have hcoeff : 3 * n ≤ 300 * (n + 1) * M := by nlinarith
  gcongr
  exact Nat.le_add_right _ _

theorem levelQuery_raw (preprocessed : List (Edge n))
    (hw : ∀ e ∈ preprocessed, e.weight ≤ weight) (potential labels : Labels n)
    (hp : ∀ v, potential.get v ≤ bound) (total remaining slope shift clock : ℕ)
    (hr : remaining + 1 ≤ total)
    (hs : slope + (remaining + 1) ≤ smoothingScale total + total) :
    (Request.level (levelDescriptor potential labels (slope + 1)
      (8 * ((smoothingScale total + total) * (2 * 2 ^ remaining))) shift
      (100 * (smoothingScale total + total)))
      (3 * (100 * (smoothingScale total + total))) clock).rawBounds preprocessed
      (300 * (smoothingScale total + total))
      (smoothingQueryWeightBound n total (inflation n * (weight + bound) + 1)) := by
  let M := smoothingScale total + total
  let B := inflation n * (weight + bound) + 1
  have hM : 0 < M := by dsimp only [M, smoothingScale]; omega
  have hwidth : 0 < 8 * (M * (2 * 2 ^ remaining)) := by positivity
  refine ⟨by omega, ?_⟩
  have h := level_raw_weights preprocessed
    (levelDescriptor potential labels (slope + 1) (8 * (M * (2 * 2 ^ remaining))) shift (100 * M))
    weight bound hw hp hwidth
  intro e he
  have hpow : 2 * 2 ^ remaining ≤ 2 ^ total := by
    have hp : 2 ^ (remaining + 1) ≤ 2 ^ total := Nat.pow_le_pow_right (by decide) hr
    simpa only [pow_succ, Nat.mul_comm] using hp
  apply (h e he).trans
  change 3 * (n + 1) * (100 * M) * (8 * (M * (2 * 2 ^ remaining)) + (slope + 1) * B) + 1 ≤
    300 * (n + 1) * M * (B + M * (8 * 2 ^ total + B)) + 1
  have hsum : 8 * (M * (2 * 2 ^ remaining)) + (slope + 1) * B ≤
      M * (8 * 2 ^ total + B) := by
    calc
      _ ≤ 8 * (M * 2 ^ total) + M * B := by gcongr <;> omega
      _ = _ := by ring
  have hsum' := hsum.trans (Nat.le_add_left (M * (8 * 2 ^ total + B)) B)
  nlinarith [Nat.mul_le_mul_left (300 * (n + 1) * M) hsum']

def requests {A : Type*} (reply : (request : Request n) → request.Reply) (program : Program n A) :
    List (Request n) := Program.trace (fun request => [request]) reply program

theorem smoothRounds_raw (reply : (request : Request n) → request.Reply)
    (preprocessed : List (Edge n)) (hw : ∀ e ∈ preprocessed, e.weight ≤ weight)
    (potential : Labels n) (hp : ∀ v, potential.get v ≤ bound)
    (total cap offset rounds slope : ℕ) (labels : Labels n) (hr : rounds ≤ total)
    (hs : slope + rounds ≤ smoothingScale total + total) :
    ∀ q ∈ requests reply (smoothRounds potential (smoothingScale total + total) cap offset rounds slope labels),
      q.rawBounds preprocessed (300 * (smoothingScale total + total))
        (smoothingQueryWeightBound n total (inflation n * (weight + bound) + 1)) := by
  induction rounds generalizing slope labels with
  | zero => simp [requests, smoothRounds, Program.trace]
  | succ rounds ih =>
      intro q hq
      simp only [requests, smoothRounds, Program.trace_bind, levelQuery, Program.trace,
        List.singleton_append, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact levelQuery_raw preprocessed hw potential labels hp total rounds slope 0 _ hr hs
      · exact levelQuery_raw preprocessed hw potential labels hp total rounds slope _ _ hr hs
      · exact ih (slope + 1) _ (by omega) (by omega) q hq

theorem smoothing_raw (reply : (request : Request n) → request.Reply)
    (preprocessed : List (Edge n)) (hw : ∀ e ∈ preprocessed, e.weight ≤ weight)
    (source : Fin n) (potential : Labels n) (hp : ∀ v, potential.get v ≤ bound)
    (rounds cap offset : ℕ) :
    ∀ q ∈ requests reply (DescriptorProgram.smoothing source potential rounds cap offset),
      q.rawBounds preprocessed (300 * (smoothingScale rounds + rounds))
        (smoothingQueryWeightBound n rounds (inflation n * (weight + bound) + 1)) := by
  intro q hq
  simp only [requests, DescriptorProgram.smoothing, Program.trace_bind, baseQuery, Program.trace,
    List.singleton_append, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact baseQuery_raw preprocessed hw source potential hp rounds offset
  · exact smoothRounds_raw reply preprocessed hw potential hp rounds cap offset rounds
      (smoothingScale rounds) _ le_rfl le_rfl q hq

theorem outerRounds_raw (reply : (request : Request n) → request.Reply)
    (preprocessed : List (Edge n)) (hw : ∀ e ∈ preprocessed, e.weight ≤ weight)
    (source : Fin n) (rounds cap iterations bound : ℕ) (potential : Labels n)
    (hp : ∀ v, potential.get v ≤ bound) :
    ∀ q ∈ requests reply (outerRounds source rounds cap iterations potential),
      q.rawBounds preprocessed (300 * (smoothingScale rounds + rounds))
        (outerQueryWeightBound n rounds iterations weight cap bound) := by
  induction iterations generalizing potential bound with
  | zero => simp [requests, outerRounds, Program.trace]
  | succ iterations ih =>
      let F := incrementBound n rounds cap
      let current := DescriptorProgram.smoothing source potential rounds cap (iterations * (1 + 2 * rounds))
      let next := updatePotential potential (Program.run reply current) rounds
      have hn : ∀ v, next.get v ≤ bound + F := by
        intro v
        exact (updatePotential_bounded potential (Program.run reply current) rounds cap
          (smoothing_reply_bounded reply source potential rounds cap _) v).trans
            (Nat.add_le_add_right (hp v) F)
      intro q hq
      simp only [requests, outerRounds, Program.trace_bind, List.mem_append] at hq
      rcases hq with hq | hq
      · have h := smoothing_raw (bound := bound + (iterations + 1) * F)
          reply preprocessed hw source potential
          (fun v => (hp v).trans (Nat.le_add_right _ _)) rounds cap _ q hq
        simpa only [outerQueryWeightBound, Nat.add_assoc, F] using h
      · have h := ih (bound + F) next hn q hq
        have he : weight + (bound + F) + iterations * F =
            weight + bound + (iterations + 1) * F := by ring
        change q.rawBounds preprocessed _
          (smoothingQueryWeightBound n rounds (inflation n *
            (weight + (bound + F) + iterations * F) + 1)) at h
        rw [he] at h
        exact h

set_option maxRecDepth 8192 in
/-- The bound applies to every transformed physical edge, including heavier
duplicates. It is not inferred from the minimum-edge semantic graph. -/
theorem exact_raw_query_bounds (reply : (request : Request n) → request.Reply)
    (source : Fin n) (exponent : ℕ) (input : List (Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    ∀ q ∈ requests reply (DescriptorProgram.exact source exponent),
      q.rawBounds (EdgeTransducer.preprocessingEdges input source (n ^ exponent))
        (20000000 * (exponent + 4) * (n.log2 + 1))
        ((2 * n) ^ (2000 * (exponent + 4))) := by
  let bits := inputBits n exponent
  have hn := sourcePositive source
  have hb := inputBits_bounds n exponent hn
  have hpre := preprocessing_raw_weights input source (n ^ exponent) hw
  have hpre' : ∀ e ∈ EdgeTransducer.preprocessingEdges input source (n ^ exponent), e.weight ≤ 2 ^ bits :=
    fun e he => (hpre e he).trans hb.2
  have h := outerRounds_raw reply _ hpre' source (smoothingRounds bits) (replyCap bits)
    (bits + 1) 0 (Vector.ofFn (fun _ => 0)) (by simp)
  have hweight := (scheduled_query_weight_bits bits n (2 ^ bits) hb.1 le_rfl).trans
    (polynomial_weight_bound n exponent hn)
  have hden : 300 * (smoothingScale (smoothingRounds bits) + smoothingRounds bits) ≤
      20000000 * (exponent + 4) * (n.log2 + 1) := by
    dsimp only [bits]
    unfold smoothingScale smoothingRounds inputBits
    nlinarith
  intro q hq
  simp only [requests, DescriptorProgram.exact, Program.trace_bind, estimates,
    Program.trace, List.singleton_append, List.append_nil, List.mem_append,
    List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact Request.rawBounds_mono _ (h q hq) hden hweight
  · trivial

end StreamingReachability.Exact.Implementation

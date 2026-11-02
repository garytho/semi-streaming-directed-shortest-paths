module

public import StreamingReachability.Exact.Locality

@[expose] public section

namespace StreamingReachability.Exact

open StoredEdges

variable {V : Type*} [Fintype V]

/-- Actual outer-loop states, including unsuccessful executions. -/
inductive OuterState (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds total : ℕ) : ℕ → (V → ℕ) → Prop
  | initial : OuterState baseCall levelCall G s rounds total total (fun _ => 0)
  | next {remaining : ℕ} {potential : V → ℕ} :
      OuterState baseCall levelCall G s rounds total (remaining + 1) potential →
      OuterState baseCall levelCall G s rounds total remaining
        (potentialStep (offsetOracle (remaining * (1 + 2 * rounds)) baseCall)
          (offsetOracle (remaining * (1 + 2 * rounds)) levelCall) G s rounds potential)

theorem outerState_bound (cap : ℕ) (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (hbase : OracleBounded cap baseCall) (G : Graph V) (s : V) (rounds total : ℕ)
    {remaining : ℕ} {potential : V → ℕ}
    (hstate : OuterState baseCall levelCall G s rounds total remaining potential) :
    remaining ≤ total ∧ ∀ v, potential v ≤
      (total - remaining) * incrementBound (Fintype.card V) rounds cap := by
  induction hstate with
  | initial => simp
  | @next remaining potential hstate ih =>
      refine ⟨by omega, ?_⟩
      intro v
      have hu := potentialIncrement_bounded cap
        (offsetOracle (remaining * (1 + 2 * rounds)) baseCall)
        (offsetOracle (remaining * (1 + 2 * rounds)) levelCall)
        (offsetOracle_bounded cap (remaining * (1 + 2 * rounds)) baseCall hbase)
        G s rounds potential v
      have hp := ih.2 v
      change potential v + _ ≤ _
      have he : total - remaining = (total - (remaining + 1)) + 1 := by omega
      rw [he, Nat.add_mul]
      simpa using Nat.add_le_add hp hu

/-- Actual partial-smoothing states. The transition is the executable two-answer
minimum, not an assumed numerical invariant. -/
inductive SmoothState (call : Oracle (Option V)) (G : Graph V) (M total initialSlope : ℕ)
    (initial : V → ℕ) : ℕ → ℕ → (V → ℕ) → Prop
  | initial : SmoothState call G M total initialSlope initial total initialSlope initial
  | next {remaining slope : ℕ} {labels : V → ℕ} :
      SmoothState call G M total initialSlope initial (remaining + 1) slope labels →
      SmoothState call G M total initialSlope initial remaining (slope + 1)
        (partialLabels labels (M * (2 * 2 ^ remaining))
          (call (levelGraph G labels (slope + 1) (8 * (M * (2 * 2 ^ remaining))) 0)
            none (100 * M) (2 * remaining + 1))
          (call (levelGraph G labels (slope + 1) (8 * (M * (2 * 2 ^ remaining)))
            (4 * (M * (2 * 2 ^ remaining)))) none (100 * M) (2 * remaining + 2)))

theorem smoothState_bound (call : Oracle (Option V)) (G : Graph V) (M total initialSlope : ℕ)
    (initial : V → ℕ) {remaining slope : ℕ} {labels : V → ℕ}
    (hstate : SmoothState call G M total initialSlope initial remaining slope labels) :
    remaining ≤ total ∧ slope + remaining = initialSlope + total ∧
      ∀ v, labels v ≤ initial v := by
  induction hstate with
  | initial => exact ⟨le_rfl, rfl, fun _ => le_rfl⟩
  | next hstate ih =>
      refine ⟨by omega, by omega, ?_⟩
      intro v
      exact (partialLabels_le _ _ _ _ v).trans (ih.2.2 v)

def wordBits (bits : ℕ) : ℕ := 64 * smallBits bits + 1

theorem word_capacity (bits : ℕ) :
    smallBound bits ^ 64 < 2 ^ wordBits bits := by
  unfold smallBound wordBits
  rw [← pow_mul, Nat.mul_comm (smallBits bits) 64, pow_succ]
  have hp : 0 < 2 ^ (64 * smallBits bits) := by positivity
  omega

theorem scheduled_vector_bounds (bits n : ℕ) (hn : n ≤ 2 ^ bits) :
    let r := smallBound bits
    let rounds := smoothingRounds bits
    let cap := replyCap bits
    smoothingScale rounds * cap ≤ r ^ 33 ∧
      (bits + 1) * incrementBound n rounds cap ≤ r ^ 35 ∧
      8 * (smoothingScale rounds + rounds) * 2 ^ rounds ≤ r ^ 12 := by
  have hs := schedule_small_bounds bits n 0 hn (by omega)
  let r := smallBound bits
  have hC : smoothingScale (smoothingRounds bits) ≤ r := by omega
  have hF := incrementBound_polynomial n (smoothingRounds bits) (replyCap bits) r
    hs.1 hC hs.2.2.2.2.1 le_rfl
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ r * r ^ 32 := Nat.mul_le_mul_right (r ^ 32) hC
      _ = r ^ 33 := by ring
  · calc
      _ ≤ r * r ^ 34 := Nat.mul_le_mul hs.2.2.2.2.2.1 hF
      _ = r ^ 35 := by ring
  · have h8 : 8 ≤ r ^ 3 := by
      calc
        8 = 2 ^ 3 := by decide
        _ ≤ r ^ 3 := Nat.pow_le_pow_left (by have hh := hs.1; omega) 3
    calc
      _ ≤ r ^ 3 * r * r ^ 8 := Nat.mul_le_mul
        (Nat.mul_le_mul h8 hs.2.2.2.1) hs.2.2.2.2.2.2
      _ = r ^ 12 := by ring

theorem outerState_word_bound (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (bits : ℕ) (hn : Fintype.card V ≤ 2 ^ bits)
    {remaining : ℕ} {potential : V → ℕ}
    (hstate : OuterState
      (nonnegativeOracle (cappedOracle (replyCap bits) positiveBase))
      (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel))
      G s (smoothingRounds bits) (bits + 1) remaining potential) :
    ∀ v, potential v < 2 ^ wordBits bits := by
  have hb := outerState_bound (replyCap bits) _ _
    (nonnegativeOracle_bounded _ _ (cappedOracle_bounded _ _))
    G s (smoothingRounds bits) (bits + 1) hstate
  have hp := (scheduled_vector_bounds bits (Fintype.card V) hn).2.1
  intro v
  calc
    potential v ≤ ((bits + 1) - remaining) * incrementBound (Fintype.card V)
        (smoothingRounds bits) (replyCap bits) := hb.2 v
    _ ≤ (bits + 1) * incrementBound (Fintype.card V) (smoothingRounds bits) (replyCap bits) := by gcongr; omega
    _ ≤ smallBound bits ^ 35 := hp
    _ ≤ smallBound bits ^ 64 := Nat.pow_le_pow_right (by unfold smallBound; positivity) (by omega)
    _ < 2 ^ wordBits bits := word_capacity bits

theorem smoothState_word_bound (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (bits : ℕ) (hn : Fintype.card V ≤ 2 ^ bits)
    {remaining slope : ℕ} {labels : V → ℕ}
    (hstate : SmoothState
      (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel)) G
      (smoothingScale (smoothingRounds bits) + smoothingRounds bits)
      (smoothingRounds bits) (smoothingScale (smoothingRounds bits))
      (fun v => smoothingScale (smoothingRounds bits) *
        nonnegativeOracle (cappedOracle (replyCap bits) positiveBase) G s 1 0 v)
      remaining slope labels) : ∀ v, labels v < 2 ^ wordBits bits := by
  have hh := smoothState_bound _ _ _ _ _ _ hstate
  have ha := nonnegativeOracle_bounded _ _ (cappedOracle_bounded (replyCap bits) positiveBase)
  have hC := (scheduled_vector_bounds bits (Fintype.card V) hn).1
  intro v
  calc
    labels v ≤ _ := hh.2.2 v
    _ ≤ smoothingScale (smoothingRounds bits) * replyCap bits :=
      Nat.mul_le_mul_left _ (ha _ _ _ _ _)
    _ ≤ smallBound bits ^ 33 := hC
    _ ≤ smallBound bits ^ 64 := Nat.pow_le_pow_right (by unfold smallBound; positivity) (by omega)
    _ < 2 ^ wordBits bits := word_capacity bits

/-- Current potential/label vectors, two optional-source oracle buffers, the two
synthetic-edge buffers, parent records, and 32 control cells. No edge stream or
query history is a field of this representation. -/
structure Workspace (n : ℕ) where
  potential : Fin n → ℕ
  labels : Fin n → ℕ
  answer₀ : Option (Fin n) → ℕ
  answer₁ : Option (Fin n) → ℕ
  synthetic₀ : Fin n → ℕ
  synthetic₁ : Fin n → ℕ
  parents : ParentPass.State n
  control : Fin 32 → ℕ

def Workspace.words {n : ℕ} (state : Workspace n) : List ℕ :=
  (List.finRange n).map state.potential ++ (List.finRange n).map state.labels ++
  (none :: (List.finRange n).map some).map state.answer₀ ++
  (none :: (List.finRange n).map some).map state.answer₁ ++
  (List.finRange n).map state.synthetic₀ ++ (List.finRange n).map state.synthetic₁ ++
  ((List.finRange n).flatMap fun v =>
    match state.parents v with
    | none => [0, 0, 0, 0]
    | some e => [1, e.source.val, e.target.val, e.weight]) ++
  (List.finRange 32).map state.control

theorem Workspace.word_count {n : ℕ} (state : Workspace n) :
    state.words.length = 10 * n + 34 := by
  have hparent : ((List.finRange n).flatMap fun v =>
      match state.parents v with
      | none => [0, 0, 0, 0]
      | some e => [1, e.source.val, e.target.val, e.weight]).length = 4 * n := by
    rw [List.length_flatMap]
    have hlen : ∀ v : Fin n, (match state.parents v with
      | none => [0, 0, 0, 0]
      | some e => [1, e.source.val, e.target.val, e.weight]).length = 4 := by
      intro v
      cases state.parents v <;> rfl
    simp [hlen, Nat.mul_comm]
  simp [Workspace.words, hparent]
  omega

theorem encode_words (words : List ℕ) (width : ℕ) (h : ∀ w ∈ words, w < 2 ^ width) :
    ∃ encoded : List (Fin (2 ^ width)),
      encoded.map Fin.val = words ∧ encoded.length = words.length := by
  induction words with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons w words ih =>
      obtain ⟨encoded, he, hl⟩ := ih (by intro a ha; exact h a (by simp [ha]))
      exact ⟨⟨w, h w (by simp)⟩ :: encoded, by simp [he], by simp [hl]⟩

theorem Workspace.encodable {n : ℕ} (state : Workspace n) (bits : ℕ)
    (h : ∀ w ∈ state.words, w < 2 ^ wordBits bits) :
    ∃ encoded : List (Fin (2 ^ wordBits bits)),
      encoded.map Fin.val = state.words ∧ encoded.length ≤ 16 * n + 128 := by
  obtain ⟨encoded, he, hl⟩ := encode_words state.words (wordBits bits) h
  exact ⟨encoded, he, by rw [hl, state.word_count]; omega⟩

/-- Physical register writes have a finite capacity on every execution.
`storeWord_exact` proves that in-range mathematical values are unchanged. -/
def storeWord (bits value : ℕ) : Fin (2 ^ wordBits bits) :=
  ⟨min value (2 ^ wordBits bits - 1), by
    have hp : 0 < 2 ^ wordBits bits := by positivity
    exact (min_le_right _ _).trans_lt (Nat.sub_lt hp (by decide))⟩

theorem storeWord_exact (bits value : ℕ) (h : value < 2 ^ wordBits bits) :
    (storeWord bits value).val = value := by
  unfold storeWord
  exact min_eq_left (by omega)

abbrev PackedWorkspace (n bits : ℕ) := Vector (Fin (2 ^ wordBits bits)) (10 * n + 34)

def Workspace.pack {n : ℕ} (state : Workspace n) (bits : ℕ) : PackedWorkspace n bits :=
  Vector.ofFn fun index => storeWord bits
    (state.words.get ⟨index.val, by rw [state.word_count]; exact index.isLt⟩)

theorem Workspace.pack_exact {n : ℕ} (state : Workspace n) (bits : ℕ)
    (h : ∀ w ∈ state.words, w < 2 ^ wordBits bits) (index : Fin (10 * n + 34)) :
    ((state.pack bits).get index).val =
      state.words.get ⟨index.val, by rw [state.word_count]; exact index.isLt⟩ := by
  simp only [Workspace.pack, Vector.get_ofFn]
  apply storeWord_exact
  exact h _ (List.get_mem _ _)

theorem capped_reply_word_bound (bits : ℕ) (call : Oracle V)
    (G : Graph V) (s : V) (denominator clock : ℕ) (v : V) :
    cappedOracle (replyCap bits) call G s denominator clock v < 2 ^ wordBits bits := by
  calc
    _ ≤ replyCap bits := cappedOracle_bounded _ _ _ _ _ _ _
    _ ≤ smallBound bits ^ 64 := Nat.pow_le_pow_right (by unfold smallBound; positivity) (by omega)
    _ < 2 ^ wordBits bits := word_capacity bits

def workspaceBits (n exponent : ℕ) : ℕ :=
  (16 * n + 128) * wordBits (inputBits n exponent)

theorem workspaceBits_bound (n exponent : ℕ) (hn : 0 < n) :
    workspaceBits n exponent ≤ 600000 * (exponent + 4) * n * (n.log2 + 1) := by
  have hc : 16 * n + 128 ≤ 144 * n := by omega
  have hb : wordBits (inputBits n exponent) ≤ 4096 * (exponent + 4) * (n.log2 + 1) := by
    unfold wordBits smallBits inputBits
    nlinarith
  unfold workspaceBits
  exact (Nat.mul_le_mul hc hb).trans (by nlinarith)

/-- The physical layout is bounded without a success or range hypothesis.
The exactness lemmas for writes connect it to the proved loop-state invariants. -/
theorem packed_workspace_bits (n exponent : ℕ) (hn : 0 < n)
    (_state : PackedWorkspace n (inputBits n exponent)) :
    (10 * n + 34) * wordBits (inputBits n exponent) ≤
      600000 * (exponent + 4) * n * (n.log2 + 1) := by
  exact (Nat.mul_le_mul_right _ (show 10 * n + 34 ≤ 16 * n + 128 by omega)).trans
    (workspaceBits_bound n exponent hn)

theorem approx_stronger (G : Graph V) (s : V) (small large : ℕ) (answer : V → ℕ)
    (hlarge : small ≤ large) (hanswer : IntegerApprox G s large answer) :
    IntegerApprox G s small answer := by
  intro v d hd
  have ha := hanswer v d hd
  refine ⟨ha.1, ?_⟩
  have hexcess := Nat.mul_le_mul_right (answer v - d) hlarge
  have he : answer v - d + d = answer v := Nat.sub_add_cancel ha.1
  nlinarith

variable {n : ℕ}

theorem exactSSSP_query_bounds (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ)
    (hW : ∀ e ∈ edges, e.weight ≤ n ^ exponent) :
    ∀ q ∈ exactSSSPTrace positiveBase positiveLevel edges source exponent,
      PositiveQueryBound
        (20000000 * (exponent + 4) * (n.log2 + 1))
        ((2 * n) ^ (2000 * (exponent + 4))) q := by
  have hn : 0 < n := by have hh := source.isLt; omega
  let bits := inputBits n exponent
  have hb := inputBits_bounds n exponent hn
  have hpre := preprocess_weightsBounded (graphOfEdges edges) source (n ^ exponent)
    (edge_list_weightsBounded edges (n ^ exponent) hW)
  have hpre' : WeightsBounded (preprocess (graphOfEdges edges) source (n ^ exponent))
      (2 ^ bits) := weightsBounded_mono _ hpre (by simpa [bits] using hb.2)
  have htrace := outerTrace_positive_bounds (replyCap bits)
    (nonnegativeOracle (cappedOracle (replyCap bits) positiveBase))
    (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel))
    (nonnegativeOracle_bounded _ _ (cappedOracle_bounded _ _))
    (preprocess (graphOfEdges edges) source (n ^ exponent)) source
    (smoothingRounds bits) (bits + 1) (2 ^ bits) 0 (fun _ => 0) hpre' (by simp)
  have hweight := (scheduled_query_weight_bits bits n (2 ^ bits) hb.1 le_rfl).trans
    (polynomial_weight_bound n exponent hn)
  have hden : 300 * (smoothingScale (smoothingRounds bits) + smoothingRounds bits) ≤
      20000000 * (exponent + 4) * (n.log2 + 1) := by
    dsimp [bits]
    unfold smoothingScale smoothingRounds inputBits
    nlinarith
  intro q hq
  have hh := htrace q hq
  simp only [Fintype.card_fin] at hh
  cases q with
  | inl q => exact ⟨hh.1.trans hden, weightsBounded_mono _ hh.2 hweight⟩
  | inr q => exact ⟨hh.1.trans hden, weightsBounded_mono _ hh.2 hweight⟩

theorem exactSSSP_queries_positive (positiveBase : Oracle (Fin n))
    (positiveLevel : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) :
    ∀ q ∈ exactSSSPTrace positiveBase positiveLevel edges source exponent,
      q.elim (fun q => ∀ u v (w : ℕ), q.positive.graph u v = (w : Distance) → 0 < w)
        (fun q => ∀ u v (w : ℕ), q.positive.graph u v = (w : Distance) → 0 < w) := by
  intro q _
  cases q <;> exact affine_positive _ _

end StreamingReachability.Exact

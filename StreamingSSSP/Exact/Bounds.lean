module

public import StreamingSSSP.Exact.Queries

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

/-- Reject oversized outputs coordinatewise before retaining them. Correctness
below concerns these actual retained answers, including on unsuccessful runs. -/
def cappedOracle (cap : ℕ) (call : Oracle V) : Oracle V :=
  fun G source denominator clock v => min cap (call G source denominator clock v)

def OracleBounded (cap : ℕ) (call : Oracle V) : Prop :=
  ∀ G source denominator clock v, call G source denominator clock v ≤ cap

theorem cappedOracle_bounded (cap : ℕ) (call : Oracle V) :
    OracleBounded cap (cappedOracle cap call) := fun _ _ _ _ _ => min_le_left _ _

theorem offsetOracle_bounded (cap offset : ℕ) (call : Oracle V)
    (h : OracleBounded cap call) : OracleBounded cap (offsetOracle offset call) :=
  fun G source denominator clock v => h G source denominator (offset + clock) v

theorem nonnegativeOracle_bounded (cap : ℕ) (call : Oracle V)
    (h : OracleBounded cap call) : OracleBounded cap (nonnegativeOracle call) := by
  intro G source denominator clock v
  dsimp [nonnegativeOracle, positiveAnswer]
  split_ifs
  · exact Nat.zero_le _
  · exact (Nat.div_le_self _ _).trans (h _ _ _ _ _)

theorem cappedOracle_preserves_accuracy (cap : ℕ) (call : Oracle V) (q : Query V)
    (h : q.Accurate call)
    (hcap : ∀ v, call q.graph q.source q.denominator q.clock v ≤ cap) :
    q.Accurate (cappedOracle cap call) := by
  have heq : cappedOracle cap call q.graph q.source q.denominator q.clock =
      call q.graph q.source q.denominator q.clock := by
    funext v
    exact min_eq_right (hcap v)
  simpa only [Query.Accurate, heq] using h

theorem smoothFrom_le (call : Oracle (Option V)) (G : Graph V) (M rounds slope : ℕ)
    (labels : V → ℕ) (v : V) :
    smoothFrom call G M rounds slope labels v ≤ labels v := by
  induction rounds generalizing slope labels with
  | zero => rfl
  | succ rounds ih =>
      exact (ih _ _).trans (partialLabels_le _ _ _ _ _)

theorem smoothing_bounded (cap : ℕ) (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (hbase : OracleBounded cap baseCall) (G : Graph V) (s : V) (rounds : ℕ) (v : V) :
    smoothing baseCall levelCall G s rounds v ≤ smoothingScale rounds * cap := by
  exact (smoothFrom_le _ _ _ _ _ _ v).trans
    (Nat.mul_le_mul_left _ (hbase G s 1 0 v))

def incrementBound (n rounds cap : ℕ) : ℕ :=
  smoothingScale rounds * cap + roundingDenominator n (smoothingScale rounds)

theorem potentialIncrement_bounded (cap : ℕ) (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (hbase : OracleBounded cap baseCall) (G : Graph V) (s : V)
    (rounds : ℕ) (potential : V → ℕ) (v : V) :
    potentialIncrement baseCall levelCall G s rounds potential v ≤
      incrementBound (Fintype.card V) rounds cap := by
  unfold potentialIncrement roundedUpdate
  let labels := smoothing baseCall levelCall (positiveResidual G potential) s rounds
  let C := smoothingScale rounds
  have hlabel := smoothing_bounded cap baseCall levelCall hbase
    (positiveResidual G potential) s rounds v
  have hi := (safeShiftIndex labels C (smoothingScale_pos rounds)).isLt
  have hshift := (shiftCandidate_bounds (Fintype.card V) C
    (safeShiftIndex labels C (smoothingScale_pos rounds)) (smoothingScale_pos rounds)
      (by omega)).2
  dsimp only [labels, C] at hshift
  exact (Nat.div_le_self _ _).trans (by unfold incrementBound; omega)

theorem outerFrom_bounded (cap : ℕ) (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (hbase : OracleBounded cap baseCall) (G : Graph V) (s : V)
    (rounds iterations bound : ℕ) (potential : V → ℕ) (hpotential : ∀ v, potential v ≤ bound) :
    ∀ v, outerFrom baseCall levelCall G s rounds iterations potential v ≤
      bound + iterations * incrementBound (Fintype.card V) rounds cap := by
  induction iterations generalizing potential bound with
  | zero => simpa [outerFrom] using hpotential
  | succ iterations ih =>
      let offset := iterations * (1 + 2 * rounds)
      let next := potentialStep (offsetOracle offset baseCall) (offsetOracle offset levelCall)
        G s rounds potential
      have hnext : ∀ v, next v ≤ bound + incrementBound (Fintype.card V) rounds cap := by
        intro v
        have hu := potentialIncrement_bounded cap (offsetOracle offset baseCall)
          (offsetOracle offset levelCall) (offsetOracle_bounded cap offset baseCall hbase)
          G s rounds potential v
        change potential v + _ ≤ _
        exact Nat.add_le_add (hpotential v) hu
      have hi := ih _ _ hnext
      intro v
      exact (hi v).trans_eq (by ring)

theorem reweight_weightsBounded (G : Graph V) (W bound : ℕ) (potential : V → ℕ)
    (hW : WeightsBounded G W) (hp : ∀ v, potential v ≤ bound) :
    WeightsBounded (reweight G potential) (W + bound) := by
  intro u v w hw
  have hn : G u v ≠ ⊤ := by
    apply (mapWeights_ne_top G (fun z => z + potential u - potential v) u v).mp
    change reweight G potential u v ≠ ⊤
    simp [hw]
  lift G u v to ℕ using hn with z hz
  have he : z + potential u - potential v = w :=
    WithTop.coe_eq_coe.mp ((reweight_coe G potential hz.symm).symm.trans hw)
  have hzW := hW u v z hz.symm
  have hpv := hp u
  omega

theorem affine_weightsBounded (G : Graph V) (W scale offset : ℕ)
    (hW : WeightsBounded G W) :
    WeightsBounded (affineGraph G scale offset) (scale * W + offset) := by
  intro u v w hw
  have hn : G u v ≠ ⊤ := by
    apply (mapWeights_ne_top G (fun z => scale * z + offset) u v).mp
    change affineGraph G scale offset u v ≠ ⊤
    simp [hw]
  lift G u v to ℕ using hn with z hz
  have he : scale * z + offset = w :=
    WithTop.coe_eq_coe.mp ((mapWeights_coe G _ hz.symm).symm.trans hw)
  have hzW := hW u v z hz.symm
  nlinarith [Nat.mul_le_mul_left scale hzW]

theorem weightsBounded_mono (G : Graph V) {a b : ℕ}
    (ha : WeightsBounded G a) (hab : a ≤ b) : WeightsBounded G b :=
  fun u v w hw => (ha u v w hw).trans hab

theorem levelGraph_weightsBounded (G : Graph V) (labels : V → ℕ)
    (W slope width shift : ℕ) (hW : WeightsBounded G W) (hwidth : 0 < width) :
    WeightsBounded (levelGraph G labels slope width shift) (width + slope * W) := by
  intro u v w hw
  cases v with
  | none => simp [levelGraph] at hw
  | some v =>
      cases u with
      | none =>
          have he : residue width shift (labels v) = w := WithTop.coe_eq_coe.mp hw
          have hr := residue_lt hwidth shift (labels v)
          omega
      | some u =>
          by_cases hb : binIndex width shift (labels u) = binIndex width shift (labels v)
          · have hn : G u v ≠ ⊤ := by
              intro hn
              simp [levelGraph, hb, hn] at hw
            lift G u v to ℕ using hn with z hz
            have he : slope * z = w := by
              apply WithTop.coe_eq_coe.mp
              simpa [levelGraph, hb, ← hz] using hw
            have hzW := hW u v z hz.symm
            nlinarith [Nat.mul_le_mul_left slope hzW]
          · simp [levelGraph, hb] at hw

theorem levelTrace_bounds (call : Oracle (Option V)) (G : Graph V)
    (W M rounds slope : ℕ) (labels : V → ℕ)
    (hW : WeightsBounded G W) (hM : 0 < M) (hslope : slope + rounds ≤ M) :
    ∀ q ∈ levelTrace call G M rounds slope labels,
      q.denominator = 100 * M ∧
      WeightsBounded q.graph (8 * M * 2 ^ rounds + M * W) := by
  induction rounds generalizing slope labels with
  | zero => simp [levelTrace]
  | succ rounds ih =>
      intro q hq
      simp only [levelTrace, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · refine ⟨rfl, ?_⟩
        apply weightsBounded_mono _ (levelGraph_weightsBounded G labels W (slope + 1)
          _ _ hW (by positivity))
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_right W (show slope + 1 ≤ M by omega)]
      · refine ⟨rfl, ?_⟩
        apply weightsBounded_mono _ (levelGraph_weightsBounded G labels W (slope + 1)
          _ _ hW (by positivity))
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_right W (show slope + 1 ≤ M by omega)]
      · have hh := ih (slope + 1) _ (by omega) q hq
        refine ⟨hh.1, weightsBounded_mono _ hh.2 ?_⟩
        rw [pow_succ]
        nlinarith [Nat.zero_le (8 * M * 2 ^ rounds)]

def smoothingQueryWeightBound (n rounds W : ℕ) : ℕ :=
  let M := smoothingScale rounds + rounds
  300 * (n + 1) * M * (W + M * (8 * 2 ^ rounds + W)) + 1

theorem smoothingTrace_positive_bounds (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds W : ℕ) (hW : WeightsBounded G W) :
    ∀ q ∈ smoothingTrace baseCall levelCall G s rounds,
      q.elim
        (fun q => q.positive.denominator ≤ 300 * (smoothingScale rounds + rounds) ∧
          WeightsBounded q.positive.graph (smoothingQueryWeightBound (Fintype.card V) rounds W))
        (fun q => q.positive.denominator ≤ 300 * (smoothingScale rounds + rounds) ∧
          WeightsBounded q.positive.graph (smoothingQueryWeightBound (Fintype.card V) rounds W)) := by
  let M := smoothingScale rounds + rounds
  have hM : 0 < M := by have hp := smoothingScale_pos rounds; omega
  intro q hq
  simp only [smoothingTrace, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨q, hq, rfl⟩
  · constructor
    · dsimp [Query.positive]
      omega
    · apply weightsBounded_mono _ (affine_weightsBounded G W _ 1 hW)
      change 3 * Fintype.card V * 1 * W + 1 ≤
        300 * (Fintype.card V + 1) * M * (W + M * (8 * 2 ^ rounds + W)) + 1
      have htheta : 3 * Fintype.card V * 1 ≤ 300 * (Fintype.card V + 1) * M := by
        nlinarith [Nat.mul_le_mul_left (300 * (Fintype.card V + 1)) (show 1 ≤ M by omega)]
      exact Nat.add_le_add_right (Nat.mul_le_mul htheta (Nat.le_add_right W _)) 1
  · have hh := levelTrace_bounds levelCall G W M rounds (smoothingScale rounds) _ hW hM le_rfl q hq
    constructor
    · dsimp [Query.positive]
      rw [hh.1]
      omega
    · apply weightsBounded_mono _ (affine_weightsBounded q.graph _ _ 1 hh.2)
      dsimp [smoothingQueryWeightBound, Query.positive]
      rw [hh.1, Fintype.card_option]
      change 3 * (Fintype.card V + 1) * (100 * M) * (8 * M * 2 ^ rounds + M * W) + 1 ≤
        300 * (Fintype.card V + 1) * M * (W + M * (8 * 2 ^ rounds + W)) + 1
      calc
        _ = 300 * (Fintype.card V + 1) * M * (M * (8 * 2 ^ rounds + W)) + 1 := by ring
        _ ≤ _ := by gcongr; omega

end StreamingSSSP.Exact

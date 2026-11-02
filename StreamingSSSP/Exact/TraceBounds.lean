module

public import StreamingSSSP.Exact.Bounds

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

@[simp] theorem queryClock_offset (offset : ℕ) (q : CombinedQuery V) :
    queryClock (offsetQuery offset q) = offset + queryClock q := by
  cases q <;> rfl

theorem outerTrace_clocks (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations : ℕ) (potential : V → ℕ) :
    ∀ q ∈ outerTrace baseCall levelCall G s rounds iterations potential,
      queryClock q < iterations * (1 + 2 * rounds) := by
  induction iterations generalizing potential with
  | zero => simp [outerTrace]
  | succ iterations ih =>
      intro q hq
      simp only [outerTrace, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q, hq, rfl⟩ | hq
      · have hh := smoothingTrace_clocks _ _ _ _ _ q hq
        rw [queryClock_offset]
        nlinarith
      · have hh := ih _ q hq
        nlinarith

theorem outerTrace_clock_nodup (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations : ℕ) (potential : V → ℕ) :
    ((outerTrace baseCall levelCall G s rounds iterations potential).map queryClock).Nodup := by
  induction iterations generalizing potential with
  | zero => simp [outerTrace]
  | succ iterations ih =>
      let offset := iterations * (1 + 2 * rounds)
      let currentBase := offsetOracle offset baseCall
      let currentLevel := offsetOracle offset levelCall
      let current := smoothingTrace currentBase currentLevel (positiveResidual G potential) s rounds
      let next := potentialStep currentBase currentLevel G s rounds potential
      change ((current.map (offsetQuery offset) ++
        outerTrace baseCall levelCall G s rounds iterations next).map queryClock).Nodup
      rw [List.map_append]
      apply List.nodup_append.mpr
      refine ⟨?_, ih next, ?_⟩
      · have hh := List.Nodup.map (fun a b (he : offset + a = offset + b) =>
          Nat.add_left_cancel he) (smoothingTrace_clock_nodup currentBase currentLevel
            (positiveResidual G potential) s rounds)
        simpa [List.map_map, Function.comp_def] using hh
      · intro a ha b hb hab
        obtain ⟨qa, hqa, rfl⟩ := List.mem_map.mp ha
        obtain ⟨qa, hqa, rfl⟩ := List.mem_map.mp hqa
        obtain ⟨qb, hqb, rfl⟩ := List.mem_map.mp hb
        have hbound := outerTrace_clocks baseCall levelCall G s rounds iterations next qb hqb
        rw [queryClock_offset] at hab
        dsimp [offset] at hab
        omega

def PositiveQueryBound (denominator weight : ℕ) (q : CombinedQuery V) : Prop :=
  q.elim
    (fun q => q.positive.denominator ≤ denominator ∧ WeightsBounded q.positive.graph weight)
    (fun q => q.positive.denominator ≤ denominator ∧ WeightsBounded q.positive.graph weight)

theorem positiveQueryBound_offset (denominator weight offset : ℕ) (q : CombinedQuery V) :
    PositiveQueryBound denominator weight (offsetQuery offset q) ↔
      PositiveQueryBound denominator weight q := by
  cases q <;> rfl

def outerQueryWeightBound (n rounds iterations W cap initialBound : ℕ) : ℕ :=
  smoothingQueryWeightBound n rounds
    (inflation n * (W + initialBound + iterations * incrementBound n rounds cap) + 1)

/-- Every generated positive graph is bounded even when earlier oracle answers
are wrong. Only the unconditional output cap is used here. -/
theorem outerTrace_positive_bounds (cap : ℕ) (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (hbase : OracleBounded cap baseCall) (G : Graph V) (s : V)
    (rounds iterations W bound : ℕ) (potential : V → ℕ)
    (hW : WeightsBounded G W) (hpotential : ∀ v, potential v ≤ bound) :
    ∀ q ∈ outerTrace baseCall levelCall G s rounds iterations potential,
      PositiveQueryBound (300 * (smoothingScale rounds + rounds))
        (outerQueryWeightBound (Fintype.card V) rounds iterations W cap bound) q := by
  induction iterations generalizing potential bound with
  | zero => simp [outerTrace]
  | succ iterations ih =>
      let offset := iterations * (1 + 2 * rounds)
      let currentBase := offsetOracle offset baseCall
      let currentLevel := offsetOracle offset levelCall
      let F := incrementBound (Fintype.card V) rounds cap
      let next := potentialStep currentBase currentLevel G s rounds potential
      have hnext : ∀ v, next v ≤ bound + F := by
        intro v
        exact Nat.add_le_add (hpotential v)
          (potentialIncrement_bounded cap currentBase currentLevel
            (offsetOracle_bounded cap offset baseCall hbase) G s rounds potential v)
      intro q hq
      simp only [outerTrace, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q, hq, rfl⟩ | hq
      · apply (positiveQueryBound_offset _ _ offset q).mpr
        have hR := reweight_weightsBounded G W bound potential hW hpotential
        have hB := affine_weightsBounded (reweight G potential) (W + bound)
          (inflation (Fintype.card V)) 1 hR
        have hB' : WeightsBounded (positiveResidual G potential)
            (inflation (Fintype.card V) *
              (W + bound + (iterations + 1) * F) + 1) := by
          apply weightsBounded_mono _ hB
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _
            (Nat.le_add_right (W + bound) ((iterations + 1) * F))) 1
        exact smoothingTrace_positive_bounds currentBase currentLevel _ s rounds _ hB' q hq
      · have hh := ih (bound + F) next hnext q hq
        have he : W + (bound + F) + iterations * F = W + bound + (iterations + 1) * F := by ring
        change PositiveQueryBound _
          (smoothingQueryWeightBound _ rounds
            (inflation _ * (W + (bound + F) + iterations * F) + 1)) q at hh
        rw [he] at hh
        exact hh

theorem pow_sum_bound (r a b : ℕ) (hr : 2 ≤ r) (hab : a ≤ b) :
    r ^ a + r ^ b ≤ r ^ (b + 1) := by
  have hp : r ^ a ≤ r ^ b := by gcongr
  rw [pow_succ]
  nlinarith [Nat.mul_le_mul_left (r ^ b) hr]

theorem incrementBound_polynomial (n rounds cap r : ℕ) (hr : 1024 ≤ r)
    (hC : smoothingScale rounds ≤ r) (hP : inflation n ≤ r) (hcap : cap ≤ r ^ 32) :
    incrementBound n rounds cap ≤ r ^ 34 := by
  have hQ : roundingDenominator n (smoothingScale rounds) ≤ r ^ 3 := by
    unfold roundingDenominator
    calc
      2 * smoothingScale rounds * inflation n ≤ 2 * r * r := by gcongr
      _ ≤ r ^ 3 := by
        simpa [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left (r * r) (show 2 ≤ r by omega)
  unfold incrementBound
  calc
    smoothingScale rounds * cap + roundingDenominator n (smoothingScale rounds) ≤
        r * r ^ 32 + r ^ 3 := by gcongr
    _ = r ^ 3 + r ^ 33 := by ring
    _ ≤ r ^ 34 := pow_sum_bound r 3 33 (by omega) (by omega)

theorem smoothingQueryWeightBound_polynomial (n rounds W r : ℕ)
    (hr : 1024 ≤ r) (hn : n ≤ r) (hM : smoothingScale rounds + rounds ≤ r)
    (hT : 2 ^ rounds ≤ r ^ 8) (hW : W ≤ r ^ 38) :
    smoothingQueryWeightBound n rounds W ≤ r ^ 45 := by
  let M := smoothingScale rounds + rounds
  have htheta : 300 * (n + 1) * M ≤ r ^ 3 := by
    calc
      300 * (n + 1) * M ≤ 300 * (r + 1) * r := by gcongr
      _ ≤ r ^ 2 * r := Nat.mul_le_mul_right r (by nlinarith)
      _ = r ^ 3 := by ring
  have hsmall : 8 * 2 ^ rounds ≤ r ^ 11 := by
    have h8 : 8 ≤ r ^ 3 := by
      calc
        8 = 2 ^ 3 := by decide
        _ ≤ r ^ 3 := by gcongr; omega
    calc
      8 * 2 ^ rounds ≤ r ^ 3 * r ^ 8 := Nat.mul_le_mul h8 hT
      _ = r ^ 11 := by ring
  have hsum : 8 * 2 ^ rounds + W ≤ r ^ 39 :=
    (Nat.add_le_add hsmall hW).trans (pow_sum_bound r 11 38 (by omega) (by omega))
  have hinner : W + M * (8 * 2 ^ rounds + W) ≤ r ^ 41 := by
    calc
      W + M * (8 * 2 ^ rounds + W) ≤ r ^ 38 + r * r ^ 39 := by gcongr
      _ = r ^ 38 + r ^ 40 := by ring
      _ ≤ r ^ 41 := pow_sum_bound r 38 40 (by omega) (by omega)
  unfold smoothingQueryWeightBound
  calc
    300 * (n + 1) * M * (W + M * (8 * 2 ^ rounds + W)) + 1 ≤
        r ^ 3 * r ^ 41 + 1 := by gcongr
    _ = r ^ 0 + r ^ 44 := by ring
    _ ≤ r ^ 45 := pow_sum_bound r 0 44 (by omega) (by omega)

theorem outerQueryWeightBound_polynomial (n rounds iterations W cap r : ℕ)
    (hr : 1024 ≤ r) (hn : n ≤ r) (hW : W ≤ r)
    (hM : smoothingScale rounds + rounds ≤ r) (hP : inflation n ≤ r)
    (hI : iterations ≤ r) (hT : 2 ^ rounds ≤ r ^ 8) (hcap : cap ≤ r ^ 32) :
    outerQueryWeightBound n rounds iterations W cap 0 ≤ r ^ 45 := by
  have hC : smoothingScale rounds ≤ r := by omega
  have hF := incrementBound_polynomial n rounds cap r hr hC hP hcap
  have hpot : iterations * incrementBound n rounds cap ≤ r ^ 35 := by
    calc
      _ ≤ r * r ^ 34 := Nat.mul_le_mul hI hF
      _ = r ^ 35 := by ring
  have hbase : inflation n * (W + 0 + iterations * incrementBound n rounds cap) + 1 ≤ r ^ 38 := by
    have hsum : W + 0 + iterations * incrementBound n rounds cap ≤ r ^ 36 := by
      calc
        _ ≤ r ^ 1 + r ^ 35 := by simpa using Nat.add_le_add hW hpot
        _ ≤ r ^ 36 := pow_sum_bound r 1 35 (by omega) (by omega)
    calc
      _ ≤ r * r ^ 36 + 1 := by gcongr
      _ = r ^ 0 + r ^ 37 := by ring
      _ ≤ r ^ 38 := pow_sum_bound r 0 37 (by omega) (by omega)
  exact smoothingQueryWeightBound_polynomial n rounds _ r hr hn hM hT hbase

def smallBits (bits : ℕ) : ℕ := 8 * bits + 36

def smallBound (bits : ℕ) : ℕ := 2 ^ smallBits bits

def replyCap (bits : ℕ) : ℕ := smallBound bits ^ 32

theorem schedule_small_bounds (bits n W : ℕ) (hn : n ≤ 2 ^ bits) (hW : W ≤ 2 ^ bits) :
    let r := smallBound bits
    1024 ≤ r ∧ n ≤ r ∧ W ≤ r ∧
      smoothingScale (smoothingRounds bits) + smoothingRounds bits ≤ r ∧
      inflation n ≤ r ∧ bits + 1 ≤ r ∧ 2 ^ smoothingRounds bits ≤ r ^ 8 := by
  let r := smallBound bits
  have hpow (k : ℕ) (hk : k ≤ smallBits bits) : 2 ^ k ≤ r := by
    dsimp [r, smallBound]
    gcongr
  have hbits : bits ≤ smallBits bits := by unfold smallBits; omega
  have hbase : 2 ^ bits ≤ r := hpow bits hbits
  have hM : smoothingScale (smoothingRounds bits) + smoothingRounds bits ≤ 2 ^ (bits + 15) := by
    have hs : smoothingScale (smoothingRounds bits) + smoothingRounds bits ≤
        32768 * (bits + 1) := by unfold smoothingScale smoothingRounds; omega
    have he : 32768 * 2 ^ bits = 2 ^ (bits + 15) := by rw [pow_add]; norm_num; ring
    exact (hs.trans (Nat.mul_le_mul_left _ (succ_le_two_pow bits))).trans_eq he
  have hP : inflation n ≤ 2 ^ (bits + 7) := by
    have hp : 0 < 2 ^ bits := by positivity
    unfold inflation
    rw [pow_add]
    norm_num
    nlinarith
  refine ⟨?_, hn.trans hbase, hW.trans hbase,
    hM.trans (hpow _ (by unfold smallBits; omega)),
    hP.trans (hpow _ (by unfold smallBits; omega)),
    (succ_le_two_pow bits).trans hbase, ?_⟩
  · have hh := hpow 10 (by unfold smallBits; omega)
    norm_num at hh
    exact hh
  · have he : smoothingRounds bits = smallBits bits * 8 := by
      unfold smoothingRounds smallBits
      ring
    dsimp [r, smallBound]
    rw [he, pow_mul]

/-- Explicit linear-in-input-bitlength bounds, hence polynomial integer weights. -/
theorem scheduled_query_weight_bits (bits n W : ℕ) (hn : n ≤ 2 ^ bits) (hW : W ≤ 2 ^ bits) :
    outerQueryWeightBound n (smoothingRounds bits) (bits + 1) W (replyCap bits) 0 ≤
      2 ^ (45 * smallBits bits) := by
  have hs := schedule_small_bounds bits n W hn hW
  have hp := outerQueryWeightBound_polynomial n (smoothingRounds bits) (bits + 1) W
    (replyCap bits) (smallBound bits) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
      hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 le_rfl
  simpa [smallBound, ← pow_mul, Nat.mul_comm] using hp

end StreamingSSSP.Exact

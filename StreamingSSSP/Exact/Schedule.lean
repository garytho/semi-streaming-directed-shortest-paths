module

public import StreamingSSSP.Exact.Algorithm

@[expose] public section

namespace StreamingSSSP.Exact

theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      omega

theorem smoothing_budget (k bound : ℕ) (hb : bound ≤ 2 ^ k) :
    2 * smoothingScale (32 * (k + 1)) * bound ≤ 2 ^ (32 * (k + 1)) := by
  have hscale : 2 * smoothingScale (32 * (k + 1)) ≤ 8192 * 2 ^ k := by
    unfold smoothingScale
    nlinarith [succ_le_two_pow k]
  have hmid : 2 * smoothingScale (32 * (k + 1)) * bound ≤ 8192 * (2 ^ k) ^ 2 := by
    nlinarith [Nat.mul_le_mul hscale hb]
  have hpow : 2 ^ (2 * k + 13) = 8192 * (2 ^ k) ^ 2 := by
    rw [pow_add, show 2 * k = k * 2 by omega, pow_mul]
    norm_num
    ring
  calc
    2 * smoothingScale (32 * (k + 1)) * bound ≤ 2 ^ (2 * k + 13) := by
      rw [hpow]
      exact hmid
    _ ≤ 2 ^ (32 * (k + 1)) := by gcongr <;> omega

def smoothingRounds (bits : ℕ) : ℕ := 32 * (2 * bits + 9)

theorem inflated_bound (bits n bound : ℕ) (hn : n ≤ 2 ^ bits) (hb : bound ≤ 2 ^ bits) :
    inflation n * bound + n ≤ 2 ^ (2 * bits + 8) := by
  have hpow : 2 ^ (2 * bits + 8) = 256 * (2 ^ bits) ^ 2 := by
    rw [pow_add, show 2 * bits = bits * 2 by omega, pow_mul]
    norm_num
    ring
  rw [hpow]
  unfold inflation
  have hprod : 64 * (n + 1) * bound ≤ 64 * (2 ^ bits + 1) * 2 ^ bits := by gcongr
  have hpos : 0 < 2 ^ bits := by positivity
  nlinarith

theorem exact_schedule_budget (bits n bound : ℕ)
    (hn : n ≤ 2 ^ bits) (hb : bound ≤ 2 ^ bits) :
    2 * smoothingScale (smoothingRounds bits) * (inflation n * bound + n) ≤
      2 ^ smoothingRounds bits := by
  exact smoothing_budget (2 * bits + 8) _ (inflated_bound bits n bound hn hb)

def oracleCallCount (bits : ℕ) : ℕ := (bits + 1) * (1 + 2 * smoothingRounds bits)

theorem oracleCallCount_bound (bits : ℕ) :
    oracleCallCount bits ≤ 577 * (bits + 1) ^ 2 := by
  unfold oracleCallCount smoothingRounds
  nlinarith

variable {V : Type*} [Fintype V]

def exactDistances (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (bits : ℕ) : V → ℕ :=
  outerFrom baseCall levelCall G s (smoothingRounds bits) (bits + 1) (fun _ => 0)

theorem exactDistances_correct (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (bits : ℕ)
    (hcard : Fintype.card V ≤ 2 ^ bits)
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ 2 ^ bits)
    (hsuccess : OuterSuccess baseCall levelCall G s (smoothingRounds bits)
      (bits + 1) (fun _ => 0)) :
    ∀ v, G.dist s v = (exactDistances baseCall levelCall G s bits v : Distance) := by
  apply exact_from_approximate baseCall levelCall G s (smoothingRounds bits) (bits + 1)
    (2 ^ bits) hreach (exact_schedule_budget bits _ _ hcard le_rfl) _ hsuccess
  rw [pow_succ]
  have hp : 0 < 2 ^ bits := by positivity
  omega

end StreamingSSSP.Exact

module

public import StreamingReachability.Hopset.Construction
public import StreamingReachability.Hopset.PathRounding

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

theorem guesses_cover_scaled (n wmin wmax U W : ℕ) (hwmin : 0 < wmin) (hU : 0 < U)
    (hlower : wmin * U ≤ W) (hupper : W ≤ 2 * n * wmax * U) :
    ∃ delta ∈ guesses n wmin wmax hwmin, delta.val * U ≤ W ∧ W < 2 * delta.val * U := by
  let J := guessExponent n wmin wmax
  have hlarge := Nat.mul_le_mul_right U (guessExponent_large n wmin wmax hwmin)
  have hlast : W < 2 * (wmin * 2 ^ J) * U := by
    have hp : 0 < (wmin * 2 ^ J) * U := by positivity
    change 2 * n * wmax * U ≤ (wmin * 2 ^ J) * U at hlarge
    nlinarith
  have hex : ∃ j : ℕ, W < 2 * (wmin * 2 ^ j) * U := ⟨J, hlast⟩
  let j := Nat.find hex
  have hright : W < 2 * (wmin * 2 ^ j) * U := Nat.find_spec hex
  have hj : j ≤ J := Nat.find_min' hex hlast
  have hleft : (wmin * 2 ^ j) * U ≤ W := by
    by_cases hz : j = 0
    · simpa only [hz, pow_zero, mul_one] using hlower
    · have hprev : ¬ W < 2 * (wmin * 2 ^ (j - 1)) * U :=
        Nat.find_min hex (show j - 1 < Nat.find hex by change j - 1 < j; omega)
      have heq : (wmin * 2 ^ j) * U = 2 * (wmin * 2 ^ (j - 1)) * U := by
        have hr : j = (j - 1) + 1 := by omega
        conv_lhs => rw [hr, pow_succ]
        ring
      exact heq.le.trans (le_of_not_gt hprev)
  let delta : { d : ℕ // 0 < d } := ⟨wmin * 2 ^ j, by positivity⟩
  refine ⟨delta, ?_, hleft, hright⟩
  apply List.mem_map.mpr
  exact ⟨j, List.mem_range.mpr (by change j < J + 1; omega), rfl⟩

end

end StreamingReachability.Hopset

module

public import StreamingReachability.Hopset.LevelResources
public import StreamingReachability.Hopset.Calibration

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ}

def trialDraws (n : ℕ) (cfg : Config) : ℕ :=
  n * cfg.earlyLevel + 5 * cfg.copyCap * (cfg.maximumLevel + 1)

def trialCalls (cfg : Config) : ℕ := cfg.maximumLevel + 2

def trialHeaders (cfg : Config) : ℕ := 2 * (cfg.maximumLevel + 1) * cfg.copyCap

theorem fixed_guess_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (cfg : Config) (hn : 0 < n)
    (stored : Implicit.Representation n) (hQ : CallsFit cfg stored Q)
    (hw : n ≤ word) (hg : cfg.groups ≤ word) (hs : cfg.shifts ≤ word) :
    Certificate input Q word (fixedGuess cfg hn stored) (trialDraws n cfg) (trialCalls cfg)
      (EndBound cfg 0 (cfg.maximumLevel + 1)) := by
  dsimp only [fixedGuess]
  split
  · rename_i hcopies
    let rates := PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel
    have hrates : ∀ p ∈ rates, p.denominator ≤ word := by
      intro p hp
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
      exact hw
    have hranks := rank_vector_certificate input Q word rates hrates n
    rw [PivotProfile.length_rates] at hranks
    let resume : Vector ℕ n → Code n (Output n) := fun rank =>
      let state : State n := ⟨{}, n, 0⟩
      let sets : Vector (Finset (Fin n)) 1 := Vector.replicate 1 Finset.univ
      (batch cfg 0 stored sets (globalTargets cfg rank) state).bind fun result =>
        levels cfg hn stored rank (cfg.maximumLevel + 1) 0 [Finset.univ] result.2
    have hresume : ∀ rank, True →
        Certificate input Q word (resume rank) (5 * cfg.copyCap * (cfg.maximumLevel + 1)) (trialCalls cfg)
          (EndBound cfg 0 (cfg.maximumLevel + 1)) := by
      intro rank _
      let state : State n := ⟨{}, n, 0⟩
      let sets : Vector (Finset (Fin n)) 1 := Vector.replicate 1 Finset.univ
      have hb : state.Bounded cfg :=
        ⟨by change 0 ≤ cfg.recordCap; omega, by simp [state], by simp [state, volume], by simp [state], hcopies⟩
      have hnSet : 1 ≤ 3 * cfg.copyCap := by omega
      have hv : setVolume sets ≤ cfg.copyCap := by simpa [sets, setVolume, volume] using hcopies
      have ht : (globalTargets cfg rank).length ≤ 2 * cfg.copyCap :=
        (global_targets_count cfg rank).trans (by omega)
      have hbatch := batch_certificate input Q word cfg 0 stored sets (globalTargets cfg rank) state hb hQ hnSet hv ht
      let next : Core.BatchAPI.SparseReply n × State n → Code n (Output n) := fun result =>
        levels cfg hn stored rank (cfg.maximumLevel + 1) 0 [Finset.univ] result.2
      have hnext : ∀ result, result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks →
          Certificate input Q word (next result) (5 * cfg.copyCap * (cfg.maximumLevel + 1)) (cfg.maximumLevel + 1)
            (EndBound cfg 0 (cfg.maximumLevel + 1)) := by
        intro result hresult
        have h := levels_certificate input Q word cfg hn stored rank hQ hw hg hs
          (cfg.maximumLevel + 1) 0 [Finset.univ] result.2
          hresult.1 (by simpa [volume] using hcopies) (by simpa only [List.length_singleton] using hnSet)
        have hheaders : result.2.output.blocks.length = 0 := by rw [hresult.2]; rfl
        simpa only [next, hheaders] using h
      have h := hbatch.bind input Q word _ next 0 1 (5 * cfg.copyCap * (cfg.maximumLevel + 1))
        (cfg.maximumLevel + 1) (fun result => result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks)
        (EndBound cfg 0 (cfg.maximumLevel + 1)) hnext
      have he : 1 + (cfg.maximumLevel + 1) = cfg.maximumLevel + 2 := by omega
      simpa only [resume, state, sets, next, Nat.zero_add, trialCalls, he] using h
    have h := hranks.bind input Q word _ resume (n * cfg.earlyLevel) 0
      (5 * cfg.copyCap * (cfg.maximumLevel + 1)) (trialCalls cfg) (fun _ => True)
      (EndBound cfg 0 (cfg.maximumLevel + 1)) hresume
    simpa only [Code.ranks, rates, resume, trialDraws, Nat.zero_add] using h
  · trivial

theorem calibrated_calls_fit (accuracy x delta : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (scale weight : ℕ)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hw : ∀ e ∈ stored.explicit, e.weight ≤ weight)
    (hb : ∀ B ∈ stored.blocks, B.card ≤ x) (hscale : delta ≤ scale) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    CallsFit cfg stored
      (QueryBounds x cfg.globalRadius cfg.recordCap (catalogLimit stored cfg.copyCap) scale weight) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  change CallsFit cfg stored
    (QueryBounds x cfg.globalRadius cfg.recordCap (catalogLimit stored cfg.copyCap) scale weight)
  intro r m sets targets allowance hsets hvolume htargets hallowance
  apply catalog_query_bounds cfg r stored sets targets allowance scale weight hs hw hb hscale _ hallowance hsets hvolume htargets
  have hr := Parameters.searchRadius_le_queryUnit n accuracy x delta (volume stored.blocks) ha hd r
  exact hr.trans (by change Parameters.queryUnit n accuracy x ≤ 8 * Parameters.queryUnit n accuracy x; omega)

end StreamingReachability.Hopset.Measured

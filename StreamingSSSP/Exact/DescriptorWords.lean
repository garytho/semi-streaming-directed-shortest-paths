module

public import StreamingSSSP.Exact.RawQueryBounds

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingSSSP.Exact.DescriptorProgram

open StoredEdges

variable {n : ℕ}

def Request.dataWords : Request n → List ℕ
  | .base descriptor source denominator _ => descriptor.words ++ [source.val, denominator]
  | .level descriptor denominator _ => descriptor.words ++ [denominator]
  | .parents source weightBound distances => distances.toList ++ [source.val, weightBound]

def Request.DataBound (cap : ℕ) (request : Request n) : Prop :=
  ∀ value ∈ request.dataWords, value ≤ cap

theorem Request.data_count (request : Request n) : request.dataWords.length ≤ 2 * n + 8 := by
  cases request <;> simp [Request.dataWords, BaseDescriptor.words, LevelDescriptor.words] <;> omega

theorem base_data (descriptor : BaseDescriptor (Fin n)) (source : Fin n) (denominator clock cap : ℕ)
    (hp : ∀ v, descriptor.potential v ≤ cap) (hi : descriptor.inflation ≤ cap)
    (hs : descriptor.positiveScale ≤ cap) (hn : n ≤ cap) (hd : denominator ≤ cap) :
    (Request.base descriptor source denominator clock).DataBound cap := by
  intro value hv
  simp only [Request.dataWords, BaseDescriptor.words, List.mem_append, List.mem_map,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with (⟨v, _, rfl⟩ | rfl | rfl) | (rfl | rfl)
  · exact hp v
  · exact hi
  · exact hs
  · exact source.isLt.le.trans hn
  · exact hd

theorem level_data (descriptor : LevelDescriptor (Fin n)) (denominator clock cap : ℕ)
    (hp : ∀ v, descriptor.potential v ≤ cap) (hl : ∀ v, descriptor.labels v ≤ cap)
    (hi : descriptor.inflation ≤ cap) (hs : descriptor.slope ≤ cap) (hw : descriptor.width ≤ cap)
    (hshift : descriptor.shift ≤ cap) (hscale : descriptor.positiveScale ≤ cap) (hd : denominator ≤ cap) :
    (Request.level descriptor denominator clock).DataBound cap := by
  intro value hv
  simp only [Request.dataWords, LevelDescriptor.words, List.mem_append, List.mem_map,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with ((⟨v, _, rfl⟩ | ⟨v, _, rfl⟩) | rfl | rfl | rfl | rfl | rfl) | rfl
  · exact hp v
  · exact hl v
  · exact hi
  · exact hs
  · exact hw
  · exact hshift
  · exact hscale
  · exact hd

end StreamingSSSP.Exact.DescriptorProgram

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open DescriptorProgram

variable {n : ℕ}

theorem smoothing_base_data (bits : ℕ) (hn : n ≤ 2 ^ bits) (potential : Labels n)
    (hp : ∀ v, potential.get v ≤ smallBound bits ^ 35) (source : Fin n) (clock : ℕ) :
    (Request.base (baseDescriptor potential 1) source 3 clock).DataBound (smallBound bits ^ 45) := by
  let r := smallBound bits
  have hs := schedule_small_bounds bits n 0 hn (by omega)
  have hr : 1024 ≤ r := hs.1
  have hpow (a : ℕ) (ha : a ≤ 45) : r ^ a ≤ r ^ 45 := Nat.pow_le_pow_right (by omega) ha
  have h35 := hpow 35 (by omega)
  have h1 : r ≤ r ^ 45 := by simpa only [pow_one] using hpow 1 (by omega)
  have hscale : 3 * n ≤ r ^ 2 := by nlinarith [hs.2.1]
  exact base_data _ _ _ _ _ (fun v => (hp v).trans h35)
    (hs.2.2.2.2.1.trans h1) (by simpa only [baseDescriptor, Nat.mul_one] using hscale.trans (hpow 2 (by omega)))
    (hs.2.1.trans h1) (le_trans (by omega : 3 ≤ r) h1)

theorem smoothing_level_data (bits : ℕ) (hn : n ≤ 2 ^ bits) (potential labels : Labels n)
    (hp : ∀ v, potential.get v ≤ smallBound bits ^ 35)
    (hl : ∀ v, labels.get v ≤ smallBound bits ^ 33) (remaining slope shift clock : ℕ)
    (hr : remaining + 1 ≤ smoothingRounds bits)
    (hslope : slope + (remaining + 1) ≤ smoothingScale (smoothingRounds bits) + smoothingRounds bits)
    (hshift : shift ≤ 8 * ((smoothingScale (smoothingRounds bits) + smoothingRounds bits) * (2 * 2 ^ remaining))) :
    (Request.level (levelDescriptor potential labels (slope + 1)
      (8 * ((smoothingScale (smoothingRounds bits) + smoothingRounds bits) * (2 * 2 ^ remaining)))
      shift (100 * (smoothingScale (smoothingRounds bits) + smoothingRounds bits)))
      (3 * (100 * (smoothingScale (smoothingRounds bits) + smoothingRounds bits))) clock).DataBound
        (smallBound bits ^ 45) := by
  let r := smallBound bits
  let M := smoothingScale (smoothingRounds bits) + smoothingRounds bits
  have hs := schedule_small_bounds bits n 0 hn (by omega)
  have hR : 1024 ≤ r := hs.1
  have hM : M ≤ r := hs.2.2.2.1
  have hpow (a : ℕ) (ha : a ≤ 45) : r ^ a ≤ r ^ 45 := Nat.pow_le_pow_right (by omega) ha
  have h1 : r ≤ r ^ 45 := by simpa only [pow_one] using hpow 1 (by omega)
  have htheta : 300 * (n + 1) * M ≤ r ^ 3 := by
    have hn' : n ≤ r := hs.2.1
    calc
      _ ≤ 300 * (r + 1) * r := by gcongr
      _ ≤ r ^ 2 * r := Nat.mul_le_mul_right r (by nlinarith)
      _ = r ^ 3 := by ring
  have ht : 2 * 2 ^ remaining ≤ 2 ^ smoothingRounds bits := by
    simpa only [pow_succ, Nat.mul_comm] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
  have hw : 8 * (M * (2 * 2 ^ remaining)) ≤ r ^ 12 := by
    have h := (scheduled_vector_bounds bits n hn).2.2
    exact (Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left M ht)).trans (by simpa only [M, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h)
  refine level_data _ _ _ _ (fun v => (hp v).trans (hpow 35 (by omega)))
    (fun v => (hl v).trans (hpow 33 (by omega))) (hs.2.2.2.2.1.trans h1)
    (le_trans (by dsimp only [M] at hM; omega : slope + 1 ≤ r) h1)
    (hw.trans (hpow 12 (by omega))) (hshift.trans (hw.trans (hpow 12 (by omega)))) ?_ ?_
  · change 3 * (n + 1) * (100 * M) ≤ r ^ 45
    exact (by nlinarith : 3 * (n + 1) * (100 * M) ≤ r ^ 3).trans (hpow 3 (by omega))
  · exact (by have h := hs.2.1; nlinarith : 3 * (100 * M) ≤ r ^ 3).trans (hpow 3 (by omega))

theorem smoothRounds_data (reply : (request : Request n) → request.Reply) (bits : ℕ) (hn : n ≤ 2 ^ bits)
    (potential : Labels n) (hp : ∀ v, potential.get v ≤ smallBound bits ^ 35)
    (cap offset rounds slope : ℕ) (labels : Labels n) (hl : ∀ v, labels.get v ≤ smallBound bits ^ 33)
    (hr : rounds ≤ smoothingRounds bits)
    (hs : slope + rounds ≤ smoothingScale (smoothingRounds bits) + smoothingRounds bits) :
    ∀ q ∈ requests reply (smoothRounds potential
      (smoothingScale (smoothingRounds bits) + smoothingRounds bits) cap offset rounds slope labels),
      q.DataBound (smallBound bits ^ 45) := by
  induction rounds generalizing slope labels with
  | zero => simp [requests, smoothRounds, Program.trace]
  | succ rounds ih =>
      intro q hq
      simp only [requests, smoothRounds, Program.trace_bind, levelQuery, Program.trace,
        List.singleton_append, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact smoothing_level_data bits hn potential labels hp hl rounds slope 0 _ hr hs (Nat.zero_le _)
      · exact smoothing_level_data bits hn potential labels hp hl rounds slope _ _ hr hs (by omega)
      · refine ih (slope + 1) _ ?_ (by omega) (by omega) q hq
        intro v
        simp only [Vector.get_ofFn]
        exact (partialLabels_le _ _ _ _ v).trans (hl v)

theorem smoothing_data (reply : (request : Request n) → request.Reply) (bits : ℕ) (hn : n ≤ 2 ^ bits)
    (source : Fin n) (potential : Labels n) (hp : ∀ v, potential.get v ≤ smallBound bits ^ 35) (offset : ℕ) :
    ∀ q ∈ requests reply (DescriptorProgram.smoothing source potential (smoothingRounds bits) (replyCap bits) offset),
      q.DataBound (smallBound bits ^ 45) := by
  intro q hq
  simp only [requests, DescriptorProgram.smoothing, Program.trace_bind, baseQuery, Program.trace,
    List.singleton_append, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact smoothing_base_data bits hn potential hp source offset
  · have hinitial : ∀ v, (Vector.ofFn (fun v => smoothingScale (smoothingRounds bits) *
          (Program.run reply (baseQuery potential source 1 offset (replyCap bits))).get v)).get v ≤ smallBound bits ^ 33 := by
        intro v
        simp only [Vector.get_ofFn]
        exact (Nat.mul_le_mul_left _ (baseQuery_guarded reply potential source 1 offset (replyCap bits) v)).trans
          (scheduled_vector_bounds bits n hn).1
    exact smoothRounds_data reply bits hn potential hp _ offset _ _ _ hinitial le_rfl le_rfl q hq

theorem outerRounds_reply_bound (reply : (request : Request n) → request.Reply) (source : Fin n)
    (rounds cap iterations bound : ℕ) (potential : Labels n) (hp : ∀ v, potential.get v ≤ bound) :
    ∀ v, (Program.run reply (outerRounds source rounds cap iterations potential)).get v ≤
      bound + iterations * incrementBound n rounds cap := by
  induction iterations generalizing potential bound with
  | zero => simpa only [outerRounds, Program.run, zero_mul, add_zero] using hp
  | succ iterations ih =>
      let current := DescriptorProgram.smoothing source potential rounds cap (iterations * (1 + 2 * rounds))
      have hn : ∀ v, (updatePotential potential (Program.run reply current) rounds).get v ≤
          bound + incrementBound n rounds cap := fun v =>
        (updatePotential_bounded _ _ _ _ (smoothing_reply_bounded reply source potential rounds cap _) v).trans
          (Nat.add_le_add_right (hp v) _)
      have h := ih _ _ hn
      simpa only [outerRounds, Program.run_bind, current, Nat.add_mul, one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem outerRounds_data (reply : (request : Request n) → request.Reply) (bits : ℕ) (hn : n ≤ 2 ^ bits)
    (source : Fin n) (iterations bound : ℕ) (potential : Labels n) (hp : ∀ v, potential.get v ≤ bound)
    (hb : bound + iterations * incrementBound n (smoothingRounds bits) (replyCap bits) ≤ smallBound bits ^ 35) :
    ∀ q ∈ requests reply (outerRounds source (smoothingRounds bits) (replyCap bits) iterations potential),
      q.DataBound (smallBound bits ^ 45) := by
  induction iterations generalizing bound potential with
  | zero => simp [requests, outerRounds, Program.trace]
  | succ iterations ih =>
      let current := DescriptorProgram.smoothing source potential (smoothingRounds bits) (replyCap bits)
        (iterations * (1 + 2 * smoothingRounds bits))
      have hnext : ∀ v, (updatePotential potential (Program.run reply current) (smoothingRounds bits)).get v ≤
          bound + incrementBound n (smoothingRounds bits) (replyCap bits) := fun v =>
        (updatePotential_bounded _ _ _ _ (smoothing_reply_bounded reply source potential _ _ _) v).trans
          (Nat.add_le_add_right (hp v) _)
      intro q hq
      simp only [requests, outerRounds, Program.trace_bind, List.mem_append] at hq
      rcases hq with hq | hq
      · exact smoothing_data reply bits hn source potential (fun v => (hp v).trans (by omega)) _ q hq
      · exact ih _ _ hnext (by nlinarith) q hq

theorem exact_data_words (reply : (request : Request n) → request.Reply)
    (source : Fin n) (exponent : ℕ) :
    ∀ q ∈ requests reply (DescriptorProgram.exact source exponent),
      q.DataBound ((2 * n) ^ (2000 * (exponent + 4))) := by
  let bits := inputBits n exponent
  have hn := sourcePositive source
  have hb := inputBits_bounds n exponent hn
  have hprogress := (scheduled_vector_bounds bits n hb.1).2.1
  have hqueries := outerRounds_data reply bits hb.1 source (bits + 1) 0 (Vector.ofFn (fun _ => 0))
    (by simp) (by simpa only [zero_add] using hprogress)
  have hout := outerRounds_reply_bound reply source (smoothingRounds bits) (replyCap bits) (bits + 1) 0
    (Vector.ofFn (fun _ => 0)) (by simp)
  have hweight : smallBound bits ^ 45 ≤ (2 * n) ^ (2000 * (exponent + 4)) := by
    simpa only [smallBound, ← pow_mul, Nat.mul_comm] using polynomial_weight_bound n exponent hn
  intro q hq
  simp only [requests, DescriptorProgram.exact, Program.trace_bind, estimates, Program.trace,
    List.append_nil, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact fun value hv => (hqueries _ hq value hv).trans hweight
  · intro value hv
    simp only [Request.dataWords, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with hv | rfl | rfl
    · rw [← Hopset.Backend.vector_indices] at hv
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
      have hr : 1 ≤ smallBound bits := by change 0 < _; unfold smallBound; positivity
      have hpow : smallBound bits ^ 35 ≤ smallBound bits ^ 45 :=
        Nat.pow_le_pow_right hr (by omega)
      exact ((hout v).trans (by omega)).trans (hpow.trans hweight)
    · exact source.isLt.le.trans (by
        have h := (schedule_small_bounds bits n 0 hb.1 (Nat.zero_le _)).2.1
        have hr : 1 ≤ smallBound bits := by change 0 < _; unfold smallBound; positivity
        have hp : smallBound bits ≤ smallBound bits ^ 45 := by
          simpa only [pow_one] using Nat.pow_le_pow_right hr (by omega : 1 ≤ 45)
        exact h.trans (hp.trans hweight))
    · exact (Nat.pow_le_pow_left (by omega : n ≤ 2 * n) exponent).trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ 2 * n) (by omega : exponent ≤ 2000 * (exponent + 4)))

end StreamingSSSP.Exact.Implementation

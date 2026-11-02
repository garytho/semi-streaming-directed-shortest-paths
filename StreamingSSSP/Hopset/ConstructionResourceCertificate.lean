module

public import StreamingSSSP.Hopset.TrialOutputLimits

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n : ℕ}

theorem execute_guesses_certificate (input : List (StoredEdges.Edge n)) (G : Graph (Fin n))
    (hn : 0 < n) (accuracy x total weight scale : ℕ) (ha : 0 < accuracy)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (hweight : scale * (8 * Parameters.queryUnit n accuracy x) ≤ weight)
    (frozen : Implicit.Representation n) (frozenCount : ℕ)
    (hf : StoreBounds G accuracy x total weight frozenCount frozen) (hfc : frozenCount ≤ total)
    (deltas : List {delta : ℕ // 0 < delta}) (hd : ∀ delta ∈ deltas, delta.val ≤ scale)
    (committed : Implicit.Representation n) (count : ℕ)
    (hc : StoreBounds G accuracy x total weight count committed) (hcount : count + deltas.length ≤ total) :
    BuilderCertificate input
      (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
        (storeCatalogLimit n accuracy total) scale weight)
      (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
      (executeGuesses hn accuracy x ha frozen deltas committed) deltas.length
      (StoreBounds G accuracy x total weight (count + deltas.length)) := by
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
      (storeCatalogLimit n accuracy total) scale weight
  induction deltas generalizing committed count with
  | nil => exact hc
  | cons delta deltas ih =>
      let cfg := Parameters.configuration n accuracy x delta.val (volume frozen.blocks) ha delta.property
      have hd₀ := hd delta (by simp)
      have hdTail : ∀ d ∈ deltas, d.val ≤ scale := fun d hm => hd d (List.mem_cons_of_mem delta hm)
      have hremaining : count + 1 + deltas.length ≤ total := by
        simp only [List.length_cons] at hcount
        omega
      have hindex : count + 1 + deltas.length = count + (delta :: deltas).length := by
        simp only [List.length_cons]
        omega
      have hzero := ih hdTail committed (count + 1) (hc.enlarge (by omega)) hremaining
      rw [hindex] at hzero
      have hout := trial_output_certificate input G hn accuracy x delta.val total weight frozenCount scale
        ha delta.property frozen hf hfc hd₀ hp hinput hG
        ((Nat.mul_le_mul_right _ hd₀).trans hweight)
      change 0 < (delta :: deltas).length ∧ _ ∧ _
      refine ⟨by simp, ?_, ?_⟩
      · simpa only [List.length_cons, Nat.add_sub_cancel] using hzero
      · exact hout.mono input Q (randomLimit n accuracy x) (fixedGuess cfg hn frozen)
          (drawLimit n accuracy x) (callLimit n) (OutputLimits G accuracy x total weight) _
          (fun out ho => by
            have hnext := ih hdTail (commit committed out) (count + 1)
              (hc.commit out ho.sound ho.volume_le ho.headers_le ho.stars_le ho.block_sizes ho.weights) hremaining
            rw [hindex] at hnext
            simpa only [List.length_cons, Nat.add_sub_cancel] using hnext)

theorem repeat_trials_certificate (input : List (StoredEdges.Edge n)) (G : Graph (Fin n))
    (hn : 0 < n) (accuracy x total weight scale : ℕ) (ha : 0 < accuracy)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (hweight : scale * (8 * Parameters.queryUnit n accuracy x) ≤ weight)
    (frozen : Implicit.Representation n) (frozenCount : ℕ)
    (hf : StoreBounds G accuracy x total weight frozenCount frozen) (hfc : frozenCount ≤ total)
    (deltas : List {delta : ℕ // 0 < delta}) (hd : ∀ delta ∈ deltas, delta.val ≤ scale)
    (trials : ℕ) (committed : Implicit.Representation n) (count : ℕ)
    (hc : StoreBounds G accuracy x total weight count committed) (hcount : count + trials * deltas.length ≤ total) :
    BuilderCertificate input
      (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
        (storeCatalogLimit n accuracy total) scale weight)
      (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
      (repeatTrials hn accuracy x ha deltas frozen trials committed) (trials * deltas.length)
      (StoreBounds G accuracy x total weight (count + trials * deltas.length)) := by
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
      (storeCatalogLimit n accuracy total) scale weight
  induction trials generalizing committed count with
  | zero => simpa only [repeatTrials, BuilderCertificate, Nat.zero_mul, Nat.add_zero] using hc
  | succ trials ih =>
      have hhead : count + deltas.length ≤ total := by nlinarith
      have hfirst := execute_guesses_certificate input G hn accuracy x total weight scale ha hp hinput hG hweight
        frozen frozenCount hf hfc deltas hd committed count hc hhead
      have hnext : ∀ stored, StoreBounds G accuracy x total weight (count + deltas.length) stored →
          BuilderCertificate input Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
            (repeatTrials hn accuracy x ha deltas frozen trials stored) (trials * deltas.length)
            (StoreBounds G accuracy x total weight (count + (trials + 1) * deltas.length)) := by
        intro stored hs
        have hrem : count + deltas.length + trials * deltas.length ≤ total := by nlinarith
        have h := ih stored (count + deltas.length) hs hrem
        have he : count + deltas.length + trials * deltas.length = count + (trials + 1) * deltas.length := by ring
        simpa only [he] using h
      have h := hfirst.bind input Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
        _ _ deltas.length (trials * deltas.length) _ _ hnext
      have he : deltas.length + trials * deltas.length = (trials + 1) * deltas.length := by ring
      simpa only [repeatTrials, he] using h

theorem stages_certificate (input : List (StoredEdges.Edge n)) (G : Graph (Fin n))
    (hn : 0 < n) (accuracy x total weight scale : ℕ) (ha : 0 < accuracy)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (hweight : scale * (8 * Parameters.queryUnit n accuracy x) ≤ weight)
    (deltas : List {delta : ℕ // 0 < delta}) (hd : ∀ delta ∈ deltas, delta.val ≤ scale)
    (trials stages : ℕ) (stored : Implicit.Representation n) (count : ℕ)
    (hs : StoreBounds G accuracy x total weight count stored) (hcount : count + stages * (trials * deltas.length) ≤ total) :
    BuilderCertificate input
      (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
        (storeCatalogLimit n accuracy total) scale weight)
      (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
      (Hopset.stages hn accuracy x ha deltas trials stages stored) (stages * (trials * deltas.length))
      (StoreBounds G accuracy x total weight (count + stages * (trials * deltas.length))) := by
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
      (storeCatalogLimit n accuracy total) scale weight
  induction stages generalizing stored count with
  | zero => simpa only [Hopset.stages, BuilderCertificate, Nat.zero_mul, Nat.add_zero] using hs
  | succ stages ih =>
      have hhead : count + trials * deltas.length ≤ total :=
        (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (show 0 < stages + 1 by omega)) count).trans hcount
      have hfirst := repeat_trials_certificate input G hn accuracy x total weight scale ha hp hinput hG hweight
        stored count hs (by omega) deltas hd trials stored count hs hhead
      have hnext : ∀ next, StoreBounds G accuracy x total weight (count + trials * deltas.length) next →
          BuilderCertificate input Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
            (Hopset.stages hn accuracy x ha deltas trials stages next) (stages * (trials * deltas.length))
            (StoreBounds G accuracy x total weight (count + (stages + 1) * (trials * deltas.length))) := by
        intro next hn
        have hrem : count + trials * deltas.length + stages * (trials * deltas.length) ≤ total := by nlinarith
        have h := ih next (count + trials * deltas.length) hn hrem
        have he : count + trials * deltas.length + stages * (trials * deltas.length) =
            count + (stages + 1) * (trials * deltas.length) := by ring
        simpa only [he] using h
      have h := hfirst.bind input Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
        _ _ (trials * deltas.length) (stages * (trials * deltas.length)) _ _ hnext
      have he : trials * deltas.length + stages * (trials * deltas.length) =
          (stages + 1) * (trials * deltas.length) := by ring
      simpa only [Hopset.stages, he] using h

end StreamingSSSP.Hopset.Measured

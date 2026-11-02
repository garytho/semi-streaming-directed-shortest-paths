module

public import StreamingSSSP.Hopset.ResourceCertificate
public import StreamingSSSP.Hopset.ProtocolQueries
public import StreamingSSSP.Hopset.TrialFacts
public import StreamingSSSP.Hopset.ChildCounts

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ}

def setVolume (sets : Vector (Finset (Fin n)) ns) : ℕ := volume sets.toList

theorem members_count (S : Finset (Fin n)) : (members S).length = S.card := by
  simpa only [members_toFinset] using (List.toFinset_card_of_nodup (members_nodup S)).symm

theorem vector_volume (sets : Vector (Finset (Fin n)) ns) :
    (∑ i : Fin ns, (sets.get i).card) = setVolume sets := by
  have he : sets.toList.map Finset.card = List.ofFn (fun i : Fin ns => (sets.get i).card) := by
    rw [← Backend.vector_indices sets, List.map_map, ← List.ofFn_eq_map]
    rfl
  unfold setVolume volume
  rw [he, List.sum_ofFn]

theorem volume_append (first last : List (Finset (Fin n))) :
    volume (first ++ last) = volume first + volume last := by simp [volume]

theorem volume_flatMap {T : Type*} (values : List T) (f : T → List (Finset (Fin n))) :
    volume (values.flatMap f) = (values.map (fun value => volume (f value))).sum := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.flatMap_cons, volume_append, List.map_cons, List.sum_cons, ih]

theorem early_targets_count (cfg : Config) (r : ℕ) (rank : Vector ℕ n)
    (sets : Vector (Finset (Fin n)) ns) :
    (earlyTargets cfg r rank sets).length ≤ 2 * setVolume sets := by
  unfold earlyTargets
  rw [List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  calc
    _ ≤ ∑ i : Fin ns, 2 * (sets.get i).card := by
      apply Finset.sum_le_sum
      intro i _
      have hfirst := List.length_filter_le
        (fun v => advanceWanted cfg r (rank.get v)) (members (sets.get i))
      have hlast := List.length_filter_le
        (fun v => pivotWanted cfg r (rank.get v)) (members (sets.get i))
      simp only [List.length_append, List.length_map, members_count] at *
      omega
    _ = 2 * setVolume sets := by rw [← vector_volume sets, Finset.mul_sum]

theorem global_targets_count (cfg : Config) (rank : Vector ℕ n) : (globalTargets cfg rank).length ≤ n := by
  simp only [globalTargets, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem early_core_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    (earlyCore cfg r sets pivots reply).length ≤ setVolume sets := by
  unfold earlyCore
  rw [List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  apply (Finset.sum_le_sum ?_).trans_eq (vector_volume sets)
  intro i _
  exact (length_le_volume _ (grouped_nonempty (sets.get i) _ _)).trans
    (grouped_card_sum (sets.get i) _ _)

theorem early_core_volume (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    volume (earlyCore cfg r sets pivots reply) ≤ setVolume sets := by
  unfold earlyCore
  rw [volume_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  apply (Finset.sum_le_sum ?_).trans_eq (vector_volume sets)
  intro i _
  exact grouped_card_sum (sets.get i) _ _

theorem early_children_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (hp : pivots.length ≤ 2 * setVolume sets) :
    (earlyFringes cfg r sets pivots reply ++ earlyCore cfg r sets pivots reply).length ≤
      3 * setVolume sets := by
  have hc := early_core_count cfg r sets pivots reply
  simp only [List.length_append, earlyFringes, List.length_map]
  omega

theorem late_core_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    (lateCore cfg r sets pivots reply).length = ns := by simp [lateCore]

theorem late_core_volume (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    volume (lateCore cfg r sets pivots reply) ≤ setVolume sets := by
  unfold lateCore volume
  rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  exact (Finset.sum_le_sum (fun i _ => Finset.card_filter_le _ _)).trans_eq (vector_volume sets)

theorem late_blocks_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    (lateBlocks cfg r sets pivots reply).length = pivots.length := by simp [lateBlocks]

theorem raw_record_radius (hn : 0 < n) (request : Core.BatchAPI.Request n) (input : List (StoredEdges.Edge n))
    (record : Core.BatchAPI.DistanceRecord n) (hr : record ∈ (Core.BatchAPI.run request input).records) :
    record.distance ≤ request.radius := by
  rw [Core.BatchAPI.run, dite_eq_left hn] at hr
  obtain ⟨j, pair, _, _, hb, rfl⟩ := (Core.BatchAPI.serialize_mem _ _ record).mp hr
  have hfinite : pair.2 ≠ ⊤ := ne_top_of_le_ne_top (by simp) hb
  have hdb := WithTop.coe_le_coe.mp ((Core.distance_coe_untop hfinite).le.trans hb)
  exact hdb.trans (Core.BatchAPI.radius_bound request j)

theorem emitted_weights (cfg : Config) (targets : List (Target n ns)) (reply : Core.BatchAPI.SparseReply n)
    (R : ℕ) (hr : ∀ record ∈ reply, record.distance ≤ R) :
    ∀ e ∈ emittedStars cfg targets reply, e.weight ≤ cfg.inputScale * R := by
  intro e he
  obtain ⟨record, hm, hv⟩ := List.mem_filterMap.mp he
  cases ht : targets[record.queryId / 2]? with
  | none => simp only [ht] at hv; cases hv
  | some target =>
      simp only [ht] at hv
      by_cases hk : target.kind = .pivot ∨ record.vertex = target.vertex
      · simp only [hk, ↓reduceIte] at hv; cases hv
      · simp only [hk, ↓reduceIte] at hv
        have heq := Option.some.inj hv
        rw [← heq]
        exact Nat.mul_le_mul_left _ (hr record hm)

end StreamingSSSP.Hopset.Measured

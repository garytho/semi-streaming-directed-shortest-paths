module

public import StreamingSSSP.Hopset.PivotIdentifiers

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ}

def hits (reply : Core.BatchAPI.SparseReply n) (query : ℕ) : Finset (Fin n) :=
  ((reply.filter (fun record => decide (record.queryId = query))).map Core.BatchAPI.DistanceRecord.vertex).toFinset

theorem lookup_record (reply : Core.BatchAPI.SparseReply n) (query : ℕ) (v : Fin n) (R : ℕ)
    (h : Core.BatchAPI.lookup reply query v ≤ (R : Distance)) : v ∈ hits reply query := by
  induction reply with
  | nil => simp [Core.BatchAPI.lookup] at h
  | cons record reply ih =>
      by_cases hm : record.queryId = query ∧ record.vertex = v
      · apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        exact ⟨record, List.mem_filter.mpr ⟨by simp, by simp [hm.1]⟩, hm.2⟩
      · simp only [Core.BatchAPI.lookup, hm, ↓reduceIte] at h
        have hv := ih h
        apply List.mem_toFinset.mpr
        obtain ⟨r, hr, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
        exact List.mem_map.mpr ⟨r, List.mem_filter.mpr
          ⟨List.mem_cons_of_mem record (List.mem_filter.mp hr).1, (List.mem_filter.mp hr).2⟩, he⟩

theorem flag_hits (reply : Core.BatchAPI.SparseReply n) (query numerator denominator : ℕ) (v : Fin n)
    (h : withinFraction (lookup reply query v) numerator denominator = true) : v ∈ hits reply query :=
  lookup_record reply query v _ (of_decide_eq_true h)

theorem both_ball_hits (cfg : Config) (r eta shift : ℕ) (S : Finset (Fin n))
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ) :
    bothBall cfg r eta shift S reply forward backward ⊆ hits reply forward ∪ hits reply backward := by
  intro v hv
  obtain ⟨_, hv⟩ := Finset.mem_filter.mp hv
  have hor : withinFraction (lookup reply forward v) ((eta * cfg.shifts + shift) * cfg.initialNumerator)
        (cfg.shifts * cfg.denominatorAt r) = true ∨
      withinFraction (lookup reply backward v) ((eta * cfg.shifts + shift) * cfg.initialNumerator)
        (cfg.shifts * cfg.denominatorAt r) = true := by
    simpa only [Bool.or_eq_true] using hv
  rcases hor with hv | hv
  · exact Finset.mem_union_left _ (flag_hits reply forward _ _ v hv)
  · exact Finset.mem_union_right _ (flag_hits reply backward _ _ v hv)

theorem hits_count (reply : Core.BatchAPI.SparseReply n) (query : ℕ) :
    (hits reply query).card ≤ (reply.filter (fun record => decide (record.queryId = query))).length := by
  exact (List.toFinset_card_le _).trans_eq (by simp)

theorem distinct_query_counts (reply : Core.BatchAPI.SparseReply n) (queries : List ℕ)
    (h : queries.Nodup) :
    (queries.map (fun query => (reply.filter (fun record => decide (record.queryId = query))).length)).sum ≤ reply.length := by
  rw [← List.sum_toFinset _ h]
  induction reply with
  | nil => simp
  | cons record reply ih =>
      have he (query : ℕ) :
          ((record :: reply).filter (fun r => decide (r.queryId = query))).length =
            (if record.queryId = query then 1 else 0) +
              (reply.filter (fun r => decide (r.queryId = query))).length := by
        by_cases hm : record.queryId = query <;> simp [hm, Nat.add_comm]
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      have hfirst : (∑ query ∈ queries.toFinset, if record.queryId = query then (1 : ℕ) else 0) ≤ 1 := by
        rw [Finset.sum_ite_eq]
        split_ifs <;> norm_num
      simp only [List.length_cons]
      omega

theorem distinct_hits_count (reply : Core.BatchAPI.SparseReply n) (queries : List ℕ)
    (h : queries.Nodup) : (queries.map (fun query => (hits reply query).card)).sum ≤ reply.length :=
  (List.sum_le_sum (l := queries) (fun query _ => hits_count reply query)).trans (distinct_query_counts reply queries h)

theorem balls_record_density (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (h : (pivotIds pivots).Nodup) :
    volume (lateBlocks cfg r sets pivots reply) ≤ reply.length := by
  have hballs (p : Pivot n ns) :
      (bothBall cfg r (p.eta + 1) p.shift (sets.get p.setId) reply p.forward p.backward).card ≤
        (hits reply p.forward).card + (hits reply p.backward).card :=
    (Finset.card_le_card (both_ball_hits cfg r _ _ _ reply p.forward p.backward)).trans (Finset.card_union_le _ _)
  have hsum := List.sum_le_sum (l := pivots) (fun p _ => hballs p)
  have he : (pivots.map (fun p => (hits reply p.forward).card + (hits reply p.backward).card)).sum =
      ((pivotIds pivots).map (fun query => (hits reply query).card)).sum := by
    clear h hsum
    induction pivots with
    | nil => rfl
    | cons p pivots ih =>
        simp only [pivotIds, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih]
  simpa only [volume, lateBlocks, List.map_map, Function.comp_def] using
    hsum.trans (he.le.trans (distinct_hits_count reply _ h))

theorem fringes_record_density (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (h : (pivotIds pivots).Nodup) :
    volume (earlyFringes cfg r sets pivots reply) ≤ reply.length := by
  have hsum := List.sum_le_sum (l := pivots) (fun p _ =>
    Finset.card_le_card (Finset.sdiff_subset :
      fringe cfg r p.eta p.shift (sets.get p.setId) reply p.forward p.backward ⊆
        bothBall cfg r (p.eta + 1) p.shift (sets.get p.setId) reply p.forward p.backward))
  have hb : (pivots.map (fun p =>
      (bothBall cfg r (p.eta + 1) p.shift (sets.get p.setId) reply p.forward p.backward).card)).sum ≤ reply.length := by
    simpa only [volume, lateBlocks, List.map_map, Function.comp_def] using balls_record_density cfg r sets pivots reply h
  simpa only [volume, earlyFringes, List.map_map, Function.comp_def, fringe] using hsum.trans hb

end StreamingSSSP.Hopset.Measured

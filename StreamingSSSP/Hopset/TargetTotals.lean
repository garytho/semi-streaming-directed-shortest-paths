module

public import StreamingSSSP.Hopset.TargetRecords
public import StreamingSSSP.Hopset.LateSampling

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ}

theorem members_sum (P : Finset (Fin n)) (f : Fin n → ℕ) :
    ((members P).map f).sum = ∑ p ∈ P, f p := by
  simpa only [members_toFinset] using (List.sum_toFinset f (members_nodup P)).symm

theorem early_targets_records (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (sets : Vector (Finset (Fin n)) ns) (rank : Vector ℕ n) (hr : r < cfg.earlyLevel)
    (owners : Fin ns → Reference.Owners n cfg) :
    ((earlyTargets cfg r rank sets).map (targetRecords cfg r stored input sets)).sum =
      ∑ i : Fin ns, Reference.nodeRecords cfg stored input (fun v => rank.get v) r (sets.get i)
        ⟨CopyHistory.pivots (sets.get i) r (fun v => rank.get v), owners i⟩ := by
  unfold earlyTargets
  rw [sum_flatMap_map, sum_finRange]
  apply Finset.sum_congr rfl
  intro i _
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    targetRecords, targetRadius]
  have ha :
      ((members (sets.get i)).filter fun v => advanceWanted cfg r (rank.get v)) =
        members (Reference.advancePivots cfg r (sets.get i) (fun v => rank.get v)) :=
    (members_bool_filter _ _).symm
  rw [ha, pivotMembers_eq cfg r rank (sets.get i) hr, members_sum, members_sum]
  simp only [Reference.nodeRecords, hr, ↓reduceIte]
  exact Nat.add_comm _ _

theorem late_targets_records (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (sets : Vector (Finset (Fin n)) ns) (P : Fin ns → Finset (Fin n))
    (ranks : Fin n → ℕ) (hr : ¬ r < cfg.earlyLevel)
    (owners : Fin ns → Reference.Owners n cfg) :
    ((pivotTargets P).map (targetRecords cfg r stored input sets)).sum =
      ∑ i : Fin ns, Reference.nodeRecords cfg stored input ranks r (sets.get i) ⟨P i, owners i⟩ := by
  unfold pivotTargets
  rw [sum_flatMap_map, sum_finRange]
  apply Finset.sum_congr rfl
  intro i _
  simp only [List.map_map, Function.comp_def, targetRecords, targetRadius]
  rw [members_sum]
  simp only [Reference.nodeRecords, hr, ↓reduceIte, add_zero]

theorem global_targets_records (cfg : Config)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ((globalTargets cfg rank).map (targetRecords cfg 0 stored input (Vector.replicate 1 Finset.univ))).sum =
      Reference.globalRecords cfg stored input (fun v => rank.get v) := by
  simp only [globalTargets, List.map_map, Function.comp_def, targetRecords, targetRadius,
    Vector.get_eq_getElem, Vector.getElem_replicate]
  have hm :
      ((List.finRange n).filter fun v => globalWanted cfg (rank.get v)) =
        members (Finset.univ.filter fun v => globalWanted cfg (rank.get v) = true) := by
    rw [members_bool_filter]
    simp [members]
  simp only [Vector.get_eq_getElem] at hm
  rw [hm, members_sum]
  rfl

end

end StreamingSSSP.Hopset

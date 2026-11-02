module

public import StreamingSSSP.Hopset.Trial

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

variable {n ns : ℕ}

def PivotFrom (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (targets : List (Target n ns)) (offset : ℕ)
    (p : Pivot n ns) : Prop :=
  ∃ (index : ℕ) (target : Target n ns) (sigma : Fin cfg.groups) (phi : Fin cfg.shifts),
    targets[index]? = some target ∧ target.kind = .pivot ∧
      p = ⟨target.setId, target.vertex,
        chooseEta cfg r (sets.get target.setId) reply (2 * (offset + index))
          (2 * (offset + index) + 1) sigma phi,
        phi.val, 2 * (offset + index), 2 * (offset + index) + 1⟩

theorem PivotFrom.cons (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (targets : List (Target n ns)) (offset : ℕ)
    (head : Target n ns) (p : Pivot n ns)
    (h : PivotFrom cfg r sets reply targets (offset + 1) p) :
    PivotFrom cfg r sets reply (head :: targets) offset p := by
  obtain ⟨index, target, sigma, phi, hi, hk, hp⟩ := h
  refine ⟨index + 1, target, sigma, phi, ?_, hk, ?_⟩
  · simpa only [List.getElem?_cons_succ] using hi
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem pivotLoop_faithful (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (targets : List (Target n ns)) (offset : ℕ) :
    (pivotLoop cfg r sets reply targets offset).Ensures fun pivots =>
      ∀ p ∈ pivots, PivotFrom cfg r sets reply targets offset p := by
  induction targets generalizing offset with
  | nil => simp [pivotLoop, Code.Ensures]
  | cons target targets ih =>
      dsimp only [pivotLoop]
      split
      next hk =>
        apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
        intro owner _
        apply Code.ensures_map
        apply Code.ensures_mono _ _ _ (ih (offset + 1))
        intro pivots hpivots p hp
        rcases List.mem_cons.mp hp with he | hp
        · subst p
          refine ⟨0, target, owner.1, owner.2, by simp, hk, ?_⟩
          simp only [Nat.add_zero]
        · exact PivotFrom.cons cfg r sets reply targets offset target p (hpivots p hp)
      next hk =>
        apply Code.ensures_mono _ _ _ (ih (offset + 1))
        intro pivots hpivots p hp
        exact PivotFrom.cons cfg r sets reply targets offset target p (hpivots p hp)

theorem subset_from_list (p : Rate) (vertices : List (Fin n)) :
    (Code.subset p vertices).Ensures fun S => ∀ v ∈ S, v ∈ vertices := by
  induction vertices with
  | nil => simp [Code.subset, Code.Ensures]
  | cons v vertices ih =>
      dsimp only [Code.subset]
      apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
      intro hit _
      cases hit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          apply Code.ensures_mono _ _ _ ih
          intro S hS w hw
          exact List.mem_cons_of_mem v (hS w hw)
      | true =>
          simp only [↓reduceIte]
          apply Code.ensures_map
          apply Code.ensures_mono _ _ _ ih
          intro S hS w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · simp
          · exact List.mem_cons_of_mem v (hS w hw)

theorem subset_of_members (p : Rate) (S : Finset (Fin n)) :
    (Code.subset p (members S)).Ensures (fun P => P ⊆ S) := by
  apply Code.ensures_mono _ _ _ (subset_from_list p (members S))
  intro P hP v hv
  exact (mem_members S v).mp (hP v hv)

def ValidTarget (sets : Vector (Finset (Fin n)) ns) (target : Target n ns) : Prop :=
  target.vertex ∈ sets.get target.setId

theorem lateTargetLoop_valid (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (indices : List (Fin ns)) :
    (lateTargetLoop cfg hn r sets indices).Ensures fun targets =>
      ∀ target ∈ targets, ValidTarget sets target := by
  induction indices with
  | nil => simp [lateTargetLoop, Code.Ensures]
  | cons i indices ih =>
      dsimp only [lateTargetLoop]
      have hchosen : (if r < cfg.maximumLevel then
            Code.subset (PivotProfile.rate n hn cfg.k cfg.logarithm r) (members (sets.get i))
          else Code.pure (sets.get i)).Ensures (fun P => P ⊆ sets.get i) := by
        split
        · exact subset_of_members _ _
        · exact Finset.Subset.refl _
      apply Code.ensures_bind _ _ _ _ hchosen
      intro chosen hchosen
      apply Code.ensures_map
      apply Code.ensures_mono _ _ _ ih
      intro targets htargets target ht
      rcases List.mem_append.mp ht with hhead | htail
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hhead
        exact hchosen ((mem_members chosen v).mp hv)
      · exact htargets target htail

end StreamingSSSP.Hopset

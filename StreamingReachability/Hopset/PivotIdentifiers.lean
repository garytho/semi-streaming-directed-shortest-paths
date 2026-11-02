module

public import StreamingReachability.Hopset.TrialResourceBounds

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n ns : ℕ}

def pivotIds (pivots : List (Pivot n ns)) : List ℕ :=
  pivots.flatMap (fun p => [p.forward, p.backward])

theorem pivot_ids_lower (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (targets : List (Target n ns)) (offset : ℕ)
    (pivots : List (Pivot n ns))
    (h : ∀ p ∈ pivots, PivotFrom cfg r sets reply targets offset p) :
    ∀ id ∈ pivotIds pivots, 2 * offset ≤ id := by
  intro id hm
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨index, target, sigma, phi, _, _, rfl⟩ := h p hp
  rcases List.mem_cons.mp hm with rfl | hm
  · change 2 * offset ≤ 2 * (offset + index)
    omega
  · have he := List.mem_singleton.mp hm
    subst id
    change 2 * offset ≤ 2 * (offset + index) + 1
    omega

theorem pivot_loop_identifiers (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (targets : List (Target n ns)) (offset : ℕ) :
    (pivotLoop cfg r sets reply targets offset).Ensures (fun pivots => (pivotIds pivots).Nodup) := by
  induction targets generalizing offset with
  | nil => simp [pivotLoop, Code.Ensures, pivotIds]
  | cons target targets ih =>
      unfold pivotLoop
      split
      · apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
        intro owner _
        apply Code.ensures_map
        apply Code.ensures_mono _ _ _
          (ensures_pair _ _ _ (ih (offset + 1))
            (pivotLoop_faithful cfg r sets reply targets (offset + 1)))
        intro pivots hp
        have hmin := pivot_ids_lower cfg r sets reply targets (offset + 1) pivots hp.2
        change (2 * offset :: (2 * offset + 1) :: pivotIds pivots).Nodup
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hp.1⟩⟩
        · intro hm
          rcases List.mem_cons.mp hm with he | hm
          · omega
          · have hh := hmin _ hm
            omega
        · intro hm
          have hh := hmin _ hm
          omega
      · exact ih (offset + 1)

end StreamingReachability.Hopset.Measured

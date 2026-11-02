module

public import StreamingSSSP.Core.BatchCorrectness
public import StreamingSSSP.Core.ClosureDistances
public import StreamingSSSP.Core.Scheduling
public import StreamingSSSP.Core.OrdinaryScan
public import StreamingSSSP.Core.WordBounds

@[expose] public section

namespace StreamingSSSP.Core.Regression

open StoredEdges

def tiesAndParallel : List (Edge 4) :=
  [⟨0, 1, 7⟩, ⟨0, 3, 2⟩, ⟨0, 1, 1⟩, ⟨0, 2, 2⟩, ⟨1, 2, 1⟩, ⟨0, 1, 9⟩]

theorem parallel_minimum_and_public_tie_break :
    graphOfEdges (Skeleton.build (by decide : 0 < 4) {0, 1, 2, 3} {0} 2 tiesAndParallel) 0 1 = 1 ∧
      graphOfEdges (Skeleton.build (by decide : 0 < 4) {0, 1, 2, 3} {0} 2 tiesAndParallel) 0 2 = 2 ∧
      graphOfEdges (Skeleton.build (by decide : 0 < 4) {0, 1, 2, 3} {0} 2 tiesAndParallel) 0 3 = ⊤ := by
  repeat' (first
    | simp only [List.mergeSort_eq_insertionSort, List.insertionSort_cons, List.insertionSort_nil,
        List.orderedInsert_cons, List.orderedInsert_nil, ite_true, ite_false]
    | fail_if_no_progress norm_num only
    | fail_if_no_progress cbv)
  exact ⟨rfl, rfl, True.intro⟩

def twoMicroEdges : List (Edge 3) := [⟨0, 1, 1⟩, ⟨1, 2, 1⟩]

theorem whole_closure_rounds_once :
    ceilNat 3 (1 + 1) = 1 ∧ ceilNat 3 1 + ceilNat 3 1 = 2 := by decide

theorem block_paths_keep_unrounded_numerators :
    (StoredSearch.run twoMicroEdges (SparseLabels.vector [(0, 0)])).get 1 = 1 ∧
      (StoredSearch.run twoMicroEdges (SparseLabels.vector [(0, 0)])).get 2 = 2 ∧
      roundDistance 3 ((StoredSearch.run twoMicroEdges (SparseLabels.vector [(0, 0)])).get 2) = 1 := by
  decide

theorem reservation_packing_not_actual_edge_count :
    (Packing.pack 4 id [2, 2, 2]).length = 2 ∧
      (Packing.pack 4 id [2, 2, 2]).flatten = [2, 2, 2] := by decide

def nextLabels (v : Fin 3) : Distance :=
  if v = 0 then 0 else if v = 1 then 2 else 5

theorem fractional_next_event :
    roundDistance 3
      (nextDistance Finset.univ ({0} ∪ found Finset.univ {0} nextLabels 3) nextLabels) = 2 := by
  decide

def forwardSearch : OrdinaryScan.Search 3 1 :=
  ⟨0, Finset.univ, 0, false, 2⟩

theorem ordinary_scan_does_not_use_new_sources_in_same_scan :
    (OrdinaryScan.scan 1 1 [forwardSearch] [((0, 0), 0)]
      twoMicroEdges ∅).state = {(0, 1)} := by
  decide

def backwardSearch : OrdinaryScan.Search 3 1 :=
  ⟨0, Finset.univ, 2, true, 2⟩

theorem backward_scan_reverses_stream_edges :
    (OrdinaryScan.scan 1 1 [backwardSearch] [((0, 2), 0)]
      twoMicroEdges ∅).state = {(0, 1)} := by
  decide

end StreamingSSSP.Core.Regression

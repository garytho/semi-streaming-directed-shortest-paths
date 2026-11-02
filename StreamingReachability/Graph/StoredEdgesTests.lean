module

public import StreamingReachability.Graph.StoredEdges

@[expose] public section

namespace StreamingReachability.StoredEdges.Tests

private def mixedEdges : List (Edge 5) :=
  [⟨2, 3, 2⟩, ⟨2, 1, 0⟩, ⟨1, 2, 0⟩, ⟨0, 1, 7⟩, ⟨0, 1, 3⟩]

example : (bellmanFord mixedEdges 0).toArray = #[0, 3, 3, 5, ⊤] := by decide

example : (bellmanFord mixedEdges.reverse 0).toArray = #[0, 3, 3, 5, ⊤] := by decide

example : (labels [⟨0, 1, 2⟩, ⟨1, 2, 0⟩] (0 : Fin 3) 1).get 2 = ⊤ := by decide

example : (bellmanFord [⟨0, 0, 0⟩, ⟨0, 0, 8⟩] (0 : Fin 1)).get 0 = 0 := by decide

end StreamingReachability.StoredEdges.Tests

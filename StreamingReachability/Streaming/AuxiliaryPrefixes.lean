module

public import StreamingReachability.Streaming.Auxiliary

@[expose] public section

namespace StreamingReachability.Streaming

variable {E F S : Type*}

inductive AuxCursor (input : List E) (auxiliary : List F) where
  | original (index : Fin (input.length + 1))
  | auxiliary (index : Fin (auxiliary.length + 1))

def AuxCursor.logicalPrefix (view : E → Option F) {input : List E} {auxiliary : List F} :
    AuxCursor input auxiliary → List F
  | .original index => (input.take index.val).filterMap view
  | .auxiliary index => input.filterMap view ++ auxiliary.take index.val

def AuxCursor.read (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    {input : List E} {auxiliary : List F} (initial : S) :
    AuxCursor input auxiliary → FusedMetered S
  | .original index => fusedPass view step cells (input.take index.val) initial
  | .auxiliary index => fusedAuxPass view step cells input (auxiliary.take index.val) initial

theorem AuxCursor.erase (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    {input : List E} {auxiliary : List F} (initial : S) (cursor : AuxCursor input auxiliary) :
    (cursor.read view step cells initial).erase =
      readPass step cells (cursor.logicalPrefix view) initial := by
  cases cursor with
  | original index => exact fusedPass_erase _ _ _ _ _
  | auxiliary index => exact fusedAuxPass_erase _ _ _ _ _ _

theorem AuxCursor.prefix (view : E → Option F) {input : List E} {auxiliary : List F}
    (cursor : AuxCursor input auxiliary) :
    ∃ suffix, input.filterMap view ++ auxiliary = cursor.logicalPrefix view ++ suffix := by
  cases cursor with
  | original index =>
      refine ⟨(input.drop index.val).filterMap view ++ auxiliary, ?_⟩
      change input.filterMap view ++ auxiliary =
        (input.take index.val).filterMap view ++ ((input.drop index.val).filterMap view ++ auxiliary)
      calc
        _ = (input.take index.val ++ input.drop index.val).filterMap view ++ auxiliary := by
          rw [List.take_append_drop]
        _ = _ := by rw [List.filterMap_append, List.append_assoc]
  | auxiliary index =>
      refine ⟨auxiliary.drop index.val, ?_⟩
      change input.filterMap view ++ auxiliary =
        (input.filterMap view ++ auxiliary.take index.val) ++ auxiliary.drop index.val
      rw [List.append_assoc, List.take_append_drop]

/-- Every physical prefix, including discarded original edges and the
auxiliary tail, is a prefix of the same logical stream used by Core proofs. -/
theorem AuxCursor.logical_position (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    {input : List E} {auxiliary : List F} (initial : S) (cursor : AuxCursor input auxiliary) :
    ∃ count ≤ (input.filterMap view ++ auxiliary).length,
      (cursor.read view step cells initial).erase =
        readPass step cells ((input.filterMap view ++ auxiliary).take count) initial := by
  obtain ⟨suffix, he⟩ := cursor.prefix view
  refine ⟨(cursor.logicalPrefix view).length, ?_, ?_⟩
  · rw [he, List.length_append]
    omega
  · rw [cursor.erase, he]
    simp

theorem AuxCursor.every_prefix_cells (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    {input : List E} {auxiliary : List F} (initial : S) (limit : ℕ)
    (h : ∀ count ≤ (input.filterMap view ++ auxiliary).length,
      (readPass step cells ((input.filterMap view ++ auxiliary).take count) initial).peakCells ≤ limit)
    (cursor : AuxCursor input auxiliary) :
    (cursor.read view step cells initial).peakCells ≤ limit := by
  obtain ⟨count, hc, he⟩ := cursor.logical_position view step cells initial
  exact (congrArg Metered.peakCells he).le.trans (h count hc)

end StreamingReachability.Streaming

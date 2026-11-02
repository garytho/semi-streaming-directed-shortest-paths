module

public import StreamingSSSP.Exact.Main

@[expose] public section

namespace StreamingSSSP.Exact

variable {V : Type*} [Fintype V]

def HasLocalDescriptor (G : Graph V) (q : CombinedQuery V) : Prop :=
  q.elim
    (fun q => ∃ d : BaseDescriptor V, q.positive.graph = d.graph G)
    (fun q => ∃ d : LevelDescriptor V, q.positive.graph = d.graph G)

theorem hasLocalDescriptor_offset (G : Graph V) (offset : ℕ) (q : CombinedQuery V) :
    HasLocalDescriptor G (offsetQuery offset q) ↔ HasLocalDescriptor G q := by
  cases q <;> rfl

theorem levelTrace_local (call : Oracle (Option V)) (G : Graph V) (potential : V → ℕ)
    (M rounds slope : ℕ) (labels : V → ℕ) :
    ∀ q ∈ levelTrace call (positiveResidual G potential) M rounds slope labels,
      ∃ d : LevelDescriptor V, q.positive.graph = d.graph G := by
  induction rounds generalizing slope labels with
  | zero => simp [levelTrace]
  | succ rounds ih =>
      intro q hq
      simp only [levelTrace, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact ⟨⟨potential, labels, inflation (Fintype.card V), slope + 1,
          8 * (M * (2 * 2 ^ rounds)), 0, 3 * Fintype.card (Option V) * (100 * M)⟩, rfl⟩
      · exact ⟨⟨potential, labels, inflation (Fintype.card V), slope + 1,
          8 * (M * (2 * 2 ^ rounds)), 4 * (M * (2 * 2 ^ rounds)),
            3 * Fintype.card (Option V) * (100 * M)⟩, rfl⟩
      · exact ih _ _ q hq

theorem smoothingTrace_local (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (potential : V → ℕ) (rounds : ℕ) :
    ∀ q ∈ smoothingTrace baseCall levelCall (positiveResidual G potential) s rounds,
      HasLocalDescriptor G q := by
  intro q hq
  simp only [smoothingTrace, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨q, hq, rfl⟩
  · exact ⟨⟨potential, inflation (Fintype.card V), 3 * Fintype.card V * 1⟩, rfl⟩
  · exact levelTrace_local levelCall G potential _ rounds _ _ q hq

theorem outerTrace_local (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations : ℕ) (potential : V → ℕ) :
    ∀ q ∈ outerTrace baseCall levelCall G s rounds iterations potential,
      HasLocalDescriptor G q := by
  induction iterations generalizing potential with
  | zero => simp [outerTrace]
  | succ iterations ih =>
      intro q hq
      simp only [outerTrace, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q, hq, rfl⟩ | hq
      · exact (hasLocalDescriptor_offset G _ q).mpr (smoothingTrace_local _ _ G s _ rounds q hq)
      · exact ih _ q hq

def BaseDescriptor.words {n : ℕ} (d : BaseDescriptor (Fin n)) : List ℕ :=
  (List.finRange n).map d.potential ++ [d.inflation, d.positiveScale]

def LevelDescriptor.words {n : ℕ} (d : LevelDescriptor (Fin n)) : List ℕ :=
  (List.finRange n).map d.potential ++ (List.finRange n).map d.labels ++
    [d.inflation, d.slope, d.width, d.shift, d.positiveScale]

theorem BaseDescriptor.word_count {n : ℕ} (d : BaseDescriptor (Fin n)) :
    d.words.length = n + 2 := by simp [words]

theorem LevelDescriptor.word_count {n : ℕ} (d : LevelDescriptor (Fin n)) :
    d.words.length = 2 * n + 5 := by simp [words]; omega

variable {n : ℕ}

theorem exactSSSP_local (positiveBase : Oracle (Fin n)) (positiveLevel : Oracle (Option (Fin n)))
    (edges : List (StoredEdges.Edge n)) (source : Fin n) (exponent : ℕ) :
    ∀ q ∈ exactSSSPTrace positiveBase positiveLevel edges source exponent,
      HasLocalDescriptor (preprocess (StoredEdges.graphOfEdges edges) source (n ^ exponent)) q :=
  outerTrace_local _ _ _ _ _ _ _

end StreamingSSSP.Exact

module

public import StreamingSSSP.Core.GlobalMain

@[expose] public section

namespace StreamingSSSP.Core.Global

open StoredEdges

variable {n b : ℕ}

theorem every_skeleton_found (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hA : 0 < p.scale) {old : State n b} {r : ℕ}
    (hg : GlobalInvariant p input old r)
    (hb : ∀ i, BlockInvariant p input old.settled r i (old.blocks.get i)) (i : Fin b) (τ : ℕ) :
    ∀ v ∈ found (p.blocks.get i) (SparseLabels.support (old.blocks.get i).known)
        (BlockSearch.labels hn (p.blocks.get i) (SparseLabels.support (old.blocks.get i).known) τ
          (SparseLabels.vector (old.blocks.get i).known) input).get (p.scale * r),
      target p input v = (r : Distance) := by
  have hlo : ∀ u, blockDistance p input old.settled i u ≤
      (SparseLabels.vector (old.blocks.get i).known).get u := by
    intro u
    rw [SparseLabels.vector_get]
    by_cases hu : u ∈ SparseLabels.support (old.blocks.get i).known
    · rw [(hb i).known_exact u hu]
    · rw [SparseLabels.get_eq_top_of_not_mem _ hu]
      exact le_top
  have hsub := found_subset (p.blocks.get i) (SparseLabels.support (old.blocks.get i).known)
    (blockDistance p input old.settled i)
    (BlockSearch.labels hn (p.blocks.get i) (SparseLabels.support (old.blocks.get i).known) τ
      (SparseLabels.vector (old.blocks.get i).known) input).get (p.scale * r)
    (fun v _ => BlockSearch.actual_lower hn _ _ τ (blockSeed p input old.settled i) _ input hlo v)
  intro v hv
  have hf := hsub hv
  rw [(hb i).known_support] at hf
  exact found_exact_round p input hA hg i v hf

end StreamingSSSP.Core.Global

module

public import StreamingReachability.Core.CommitSpace

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

structure Cache {p : Boundary hn c stored input budget x} (f : Commit p) where
  query : Fin nq
  block : Fin nb
  active : p.rounds ≤ (c.searches.get query).radius
  count : ℕ

def Cache.fresh {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f) : Finset (Fin n) :=
  GuardedDriver.proposed c p.rounds a.query (p.state.states.get a.query) (f.candidates.get a.query) f.replies

def Cache.base {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f) :=
  (BatchDriver.searchResults c p.rounds a.query (p.state.states.get a.query) f.replies).map fun pair =>
    (pair.1, pair.2.state)

def Cache.partial {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f) (count : ℕ) :=
  RecordMap.foldModify Global.emptyBlock
    (fun i => Global.externalBlock c.scale p.rounds (Shared.block c a.query i) a.fresh)
    (fun i => decide (0 < (a.fresh ∩ Shared.block c a.query i).card)) ((List.finRange nb).take count) a.base

theorem Cache.base_active {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) : SparseDriver.Active a.base := by
  have hf := p.facts hs hp hA hx
  intro pair hm
  simp only [Cache.base, BatchDriver.searchResults, List.map_map, Function.comp_def] at hm
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hm
  have hpos := (hf.shape a.query).active item hi
  dsimp only
  by_cases hn : item.2.next = (p.rounds : Distance)
  · simp only [hn, ↓reduceIte]
    cases he : RecordMap.get none f.replies (a.query, item.1) with
    | none => simpa only [he] using hpos
    | some out =>
        simp only [he, BatchDriver.accept, List.length_append]
        omega
  · simpa only [hn, ↓reduceIte] using hpos

theorem Cache.base_unique {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) : RecordMap.Unique a.base := by
  simpa only [Cache.base, RecordMap.Unique, BatchDriver.searchResults, List.map_map, Function.comp_def] using
    ((p.facts hs hp hA hx).shape a.query).unique

theorem Cache.full_eq {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f) :
    (f.newState.get a.query).cache =
      SparseDriver.commitCache (SparseDriver.ofCatalog c a.query) p.rounds a.fresh a.base := by
  rw [Commit.newState, GuardedDriver.newStates, Vector.get_ofFn, BatchDriver.finishQuery, ite_eq_left a.active]
  simp only [Cache.fresh, GuardedDriver.proposed, a.active, ↓reduceIte]
  rfl

theorem Cache.partial_cells {p : Boundary hn c stored input budget x} {f : Commit p}
    (a : Cache f) (count : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    SparseDriver.cacheCells (a.partial count) ≤ 12 * budget := by
  have hknown := GuardedDriver.raw_known_shapes hn c stored input x (p.rounds + 1) hs hp hA hx a.query
  rw [← f.new_eq] at hknown
  have hcover := GuardedDriver.cover_mono f.afterEdges f.registry f.newState
    (f.after_space hs hp hA hx).2.1 f.mono
  have hfull (i : Fin nb) :
      (RecordMap.get Global.emptyBlock
        (SparseDriver.commitCache (SparseDriver.ofCatalog c a.query) p.rounds a.fresh a.base) i).known.length ≤
      (RecordGuard.verticesAt f.registry.seen a.query ∩ c.blocks.get i).card := by
    rw [← a.full_eq, SparseLabels.length_eq_card _ (hknown i).1]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hl, hb⟩ := Finset.mem_inter.mp ((hknown i).2 hv)
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcover a.query v hl⟩, hb⟩
  apply GuardedDriver.cache_section_bound c budget f.registry (f.valid hs hp hA hx) a.query (a.partial count)
  · exact RecordMap.unique_foldModify _ _ _ _ a.base (a.base_unique hs hp hA hx)
  · exact SparseDriver.partialCache_active (SparseDriver.ofCatalog c a.query) p.rounds a.fresh
      _ a.base (a.base_active hs hp hA hx)
  · intro i
    exact (SparseDriver.partialCache_lengths (SparseDriver.ofCatalog c a.query) p.rounds a.fresh
      ((List.finRange nb).take count) (List.nodup_finRange nb).take a.base i).trans (hfull i)

def Cache.cells {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f) : ℕ :=
  f.cells + SparseDriver.cacheCells a.base + SparseDriver.cacheCells (a.partial a.count) +
    SparseDriver.cacheCells (a.partial (a.count + 1)) +
    4 * (f.newState.get a.query).labels.length + 2 * (f.newState.get a.query).settled.card +
    5 * a.fresh.card + 2 * (Shared.block c a.query a.block).card + 2 * nb + 12

theorem Cache.cells_le {p : Boundary hn c stored input budget x} {f : Commit p} (a : Cache f)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    a.cells ≤ 256 * (n + budget + 1) + 2 * nb := by
  have hbase : SparseDriver.cacheCells a.base ≤ 12 * budget := by
    simpa only [Cache.partial, List.take_zero, RecordMap.foldModify, List.foldl_nil] using
      a.partial_cells 0 hs hp hA hx
  have hcur := a.partial_cells a.count hs hp hA hx
  have hnext := a.partial_cells (a.count + 1) hs hp hA hx
  have hf := f.cells_le hs hp hA hx
  have hshape : SparseDriver.Shape (f.newState.get a.query) := by
    rw [f.new_eq]
    exact BatchDriver.execute_shape hn c stored input x (p.rounds + 1) hx a.query
  have hlabels : (f.newState.get a.query).labels.length ≤ n := by
    rw [SparseLabels.length_eq_card _ hshape.labels_unique]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (SparseLabels.support (f.newState.get a.query).labels)
  have hsettled : (f.newState.get a.query).settled.card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (f.newState.get a.query).settled
  have hU : a.fresh.card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ a.fresh
  have hB : (Shared.block c a.query a.block).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (Shared.block c a.query a.block)
  unfold Cache.cells
  omega

end StreamingReachability.Core.Live

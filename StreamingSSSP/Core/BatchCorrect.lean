module

public import StreamingSSSP.Core.BatchRefinement

@[expose] public section

namespace StreamingSSSP.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

noncomputable def replyMap (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (old : States n nb nq) :=
  answers (jobs c r old)
    (Shared.Engine.run hn c stored input r (Nat.log 2 x + 2) (tasks (jobs c r old))).tasks

theorem searchResults_eq (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (j : Fin nq) (ha : r ≤ (c.searches.get j).radius) :
    searchResults c r j (old.get j) (replyMap hn c stored input x r old) =
      SparseDriver.results hn (SparseDriver.ofCatalog c j) stored input r (old.get j) := by
  unfold searchResults SparseDriver.results
  apply List.map_congr_left
  rintro ⟨i, bs⟩ hmem
  by_cases hs : bs.next = (r : Distance)
  · obtain ⟨out, hsearch, hlookup⟩ := answers_get hn c stored input x r old hu hx j i
      (canonical_mem c r old hu j i bs hmem ha hs)
    have hg := RecordMap.get_mem Global.emptyBlock (old.get j).cache (hu j) hmem
    have hknown : (canonical old j i).sources = bs.known := by simp only [canonical, hg]
    rw [hknown] at hsearch
    change RecordMap.get none (replyMap hn c stored input x r old) (j, i) = some out at hlookup
    rw [ite_eq_left hs, hlookup, SparseDriver.searchBlock, ite_eq_left hs]
    simp only [SparseDriver.ofCatalog]
    rw [hsearch]
    rfl
  · rw [ite_eq_right hs, SparseDriver.searchBlock, ite_eq_right hs]

theorem round_get (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (j : Fin nq) :
    (round hn c stored input x r old).states.get j =
      if r ≤ (c.searches.get j).radius
      then SparseDriver.round hn (SparseDriver.ofCatalog c j) stored input r (old.get j) else old.get j := by
  by_cases ha : r ≤ (c.searches.get j).radius
  · rw [ite_eq_left ha]
    simp only [round, Shared.Engine.runTail_eq, Vector.get_ofFn]
    change finishQuery c r j (old.get j) ((ordinary c r old stored input).state.get j)
      (replyMap hn c stored input x r old) = _
    rw [finishQuery, ite_eq_left ha]
    have ho := ordinary_get c r old stored input j
    rw [ite_eq_left ha] at ho
    rw [show (ordinary c r old stored input).state.get j =
      (stored ++ input).foldl (SparseDriver.edgeStep (SparseDriver.ofCatalog c j) r (old.get j)) ∅ from ho]
    rw [searchResults_eq hn c stored input x r old hu hx j ha, List.foldl_append]
    rfl
  · simp only [round, Shared.Engine.runTail_eq, Vector.get_ofFn, finishQuery, ha, ↓reduceIte]

theorem execute_get (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (j : Fin nq) :
    ((execute hn c stored input x r).states).get j =
      SparseDriver.execute hn (SparseDriver.ofCatalog c j) stored input
        (min r ((c.searches.get j).radius + 1)) := by
  induction r generalizing j with
  | zero => simp [execute, initial, SparseDriver.execute]
  | succ r ih =>
      have hu : ∀ k, RecordMap.Unique ((execute hn c stored input x r).states.get k).cache := by
        intro k
        rw [ih k]
        exact SparseDriver.execute_unique hn _ stored input _
      change (round hn c stored input x r (execute hn c stored input x r).states).states.get j = _
      rw [round_get hn c stored input x r _ hu hx j]
      by_cases ha : r ≤ (c.searches.get j).radius
      · rw [ite_eq_left ha, ih j]
        rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
        rfl
      · rw [ite_eq_right ha, ih j]
        rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

theorem core_distance_correct (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (hR : ∀ j, (c.searches.get j).radius ≤ R) (j : Fin nq) (v : Fin n) :
    output hn c stored input x R j v =
      if (fullQueryGraph ((stored ++ input).filterMap (Shared.view c j))
          (Shared.referenceProblem c j).blocks.toList c.scale).dist (c.searches.get j).source v ≤
            ((c.searches.get j).radius : Distance)
      then (fullQueryGraph ((stored ++ input).filterMap (Shared.view c j))
          (Shared.referenceProblem c j).blocks.toList c.scale).dist (c.searches.get j).source v else ⊤ := by
  have he := execute_get hn c stored input x (R + 1) hx j
  rw [Nat.min_eq_right (Nat.add_le_add_right (hR j) 1)] at he
  unfold output
  dsimp only
  rw [he]
  exact SparseDriver.catalog_core_distance_correct hn c j stored input hs hp hA v

end StreamingSSSP.Core.BatchDriver

module

public import StreamingReachability.Graph.HopDistance

@[expose] public section

namespace StreamingReachability.StoredEdges

structure Edge (n : ℕ) where
  source : Fin n
  target : Fin n
  weight : ℕ
  deriving DecidableEq, Repr

variable {n : ℕ}

def edgeCost (e : Edge n) (u v : Fin n) : Distance :=
  if e.source = u ∧ e.target = v then e.weight else ⊤

def graphOfEdges (edges : List (Edge n)) : Graph (Fin n) :=
  fun u v => edges.foldr (fun e d => min (edgeCost e u v) d) ⊤

@[simp] theorem graphOfEdges_nil (u v : Fin n) :
    graphOfEdges [] u v = ⊤ := rfl

@[simp] theorem graphOfEdges_cons (e : Edge n) (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges (e :: edges) u v = min (edgeCost e u v) (graphOfEdges edges u v) := rfl

theorem le_graphOfEdges_iff (edges : List (Edge n)) (u v : Fin n) (d : Distance) :
    d ≤ graphOfEdges edges u v ↔
      ∀ e ∈ edges, e.source = u → e.target = v → d ≤ (e.weight : Distance) := by
  induction edges with
  | nil => simp
  | cons e edges ih =>
      simp only [graphOfEdges_cons, le_min_iff, ih, List.mem_cons,
        forall_eq_or_imp]
      by_cases hs : e.source = u <;> by_cases ht : e.target = v <;>
        simp [edgeCost, hs, ht]

theorem graphOfEdges_le_edge (edges : List (Edge n)) {e : Edge n} (he : e ∈ edges) :
    graphOfEdges edges e.source e.target ≤ (e.weight : Distance) :=
  (le_graphOfEdges_iff edges e.source e.target _).mp le_rfl e he rfl rfl

theorem exists_edge_eq (edges : List (Edge n)) {u v : Fin n}
    (h : graphOfEdges edges u v ≠ ⊤) :
    ∃ e ∈ edges, e.source = u ∧ e.target = v ∧
      (e.weight : Distance) = graphOfEdges edges u v := by
  induction edges with
  | nil => simp at h
  | cons e edges ih =>
      by_cases hm : e.source = u ∧ e.target = v
      · by_cases hw : (e.weight : Distance) ≤ graphOfEdges edges u v
        · exact ⟨e, by simp, hm.1, hm.2, by simp [edgeCost, hm, min_eq_left hw]⟩
        · have hg : graphOfEdges (e :: edges) u v = graphOfEdges edges u v := by
            simp [edgeCost, hm, min_eq_right (le_of_not_ge hw)]
          obtain ⟨f, hf, hs, ht, hc⟩ := ih (by rwa [← hg])
          exact ⟨f, by simp [hf], hs, ht, hc.trans hg.symm⟩
      · have hg : graphOfEdges (e :: edges) u v = graphOfEdges edges u v := by
          simp [edgeCost, hm]
        obtain ⟨f, hf, hs, ht, hc⟩ := ih (by rwa [← hg])
        exact ⟨f, by simp [hf], hs, ht, hc.trans hg.symm⟩

theorem graphOfEdges_ne_top_iff (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges edges u v ≠ ⊤ ↔ ∃ e ∈ edges, e.source = u ∧ e.target = v := by
  constructor
  · intro h
    obtain ⟨e, he, hs, ht, _⟩ := exists_edge_eq edges h
    exact ⟨e, he, hs, ht⟩
  · rintro ⟨e, he, rfl, rfl⟩ htop
    have h := graphOfEdges_le_edge edges he
    simp [htop] at h

theorem graphOfEdges_append (xs ys : List (Edge n)) :
    graphOfEdges (xs ++ ys) = (graphOfEdges xs).union (graphOfEdges ys) := by
  funext u v
  induction xs with
  | nil => simp [Graph.union]
  | cons e xs ih => simp only [List.cons_append, graphOfEdges_cons, ih,
      Graph.union_apply, min_assoc]

theorem graphOfEdges_antitone {xs ys : List (Edge n)}
    (h : ∀ e ∈ xs, e ∈ ys) (u v : Fin n) :
    graphOfEdges ys u v ≤ graphOfEdges xs u v := by
  apply (le_graphOfEdges_iff xs u v _).mpr
  intro e he hs ht
  simpa only [hs, ht] using graphOfEdges_le_edge ys (h e he)

theorem graphOfEdges_perm {xs ys : List (Edge n)} (h : xs.Perm ys) :
    graphOfEdges xs = graphOfEdges ys := by
  funext u v
  exact le_antisymm
    (graphOfEdges_antitone (fun e he => h.mem_iff.mpr he) u v)
    (graphOfEdges_antitone (fun e he => h.mem_iff.mp he) u v)

abbrev DistanceArray (n : ℕ) := Vector Distance n

def initialDistances (source : Fin n) : DistanceArray n :=
  Vector.ofFn fun v => if v = source then 0 else ⊤

def relaxEdge (old next : DistanceArray n) (e : Edge n) : DistanceArray n :=
  next.set e.target.val (min (next.get e.target) (old.get e.source + e.weight))
    e.target.isLt

def relaxEdges (edges : List (Edge n)) (old next : DistanceArray n) : DistanceArray n :=
  edges.foldl (relaxEdge old) next

def relaxRound (edges : List (Edge n)) (old : DistanceArray n) : DistanceArray n :=
  relaxEdges edges old old

def runRounds (edges : List (Edge n)) : ℕ → DistanceArray n → DistanceArray n
  | 0, d => d
  | k + 1, d => runRounds edges k (relaxRound edges d)

def labels (edges : List (Edge n)) (source : Fin n) (rounds : ℕ) : DistanceArray n :=
  runRounds edges rounds (initialDistances source)

def bellmanFord (edges : List (Edge n)) (source : Fin n) : DistanceArray n :=
  labels edges source (n - 1)

@[simp] theorem initialDistances_get (source v : Fin n) :
    (initialDistances source).get v = if v = source then 0 else ⊤ := by
  simp [initialDistances]

theorem relaxEdge_get (old next : DistanceArray n) (e : Edge n) (v : Fin n) :
    (relaxEdge old next e).get v =
      if v = e.target then min (next.get v) (old.get e.source + e.weight)
      else next.get v := by
  change (next.set e.target.val
    (min next[e.target.val] (old[e.source.val] + (e.weight : Distance))) e.target.isLt)[v.val] =
      if v = e.target then min next[v.val] (old[e.source.val] + (e.weight : Distance))
      else next[v.val]
  rw [Vector.getElem_set]
  by_cases hv : v = e.target
  · subst v
    simp
  · have hval : e.target.val ≠ v.val := by
      intro h
      exact hv (Fin.ext h.symm)
    simp [hv, hval]

theorem relaxEdge_le_self (old next : DistanceArray n) (e : Edge n) (v : Fin n) :
    (relaxEdge old next e).get v ≤ next.get v := by
  rw [relaxEdge_get]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem relaxEdges_le_initial (edges : List (Edge n)) (old next : DistanceArray n)
    (v : Fin n) : (relaxEdges edges old next).get v ≤ next.get v := by
  induction edges generalizing next with
  | nil => exact le_rfl
  | cons e edges ih =>
      exact (ih (relaxEdge old next e)).trans (relaxEdge_le_self old next e v)

theorem relaxEdges_le_edge (edges : List (Edge n)) (old next : DistanceArray n)
    {e : Edge n} (he : e ∈ edges) :
    (relaxEdges edges old next).get e.target ≤ old.get e.source + e.weight := by
  induction edges generalizing next with
  | nil => simp at he
  | cons f edges ih =>
      obtain rfl | he := List.mem_cons.mp he
      · exact (relaxEdges_le_initial edges old (relaxEdge old next e) e.target).trans
          (by rw [relaxEdge_get]; simp only [ite_true]; exact min_le_right _ _)
      · exact ih (relaxEdge old next f) he

theorem relaxEdges_preserves_lower (edges : List (Edge n))
    (old next : DistanceArray n) (d : Fin n → Distance)
    (hn : ∀ v, d v ≤ next.get v)
    (he : ∀ e ∈ edges, d e.target ≤ old.get e.source + e.weight) :
    ∀ v, d v ≤ (relaxEdges edges old next).get v := by
  induction edges generalizing next with
  | nil => exact hn
  | cons e edges ih =>
      apply ih (relaxEdge old next e)
      · intro v
        rw [relaxEdge_get]
        split_ifs with hv
        · subst v
          exact le_min (hn _) (he e (by simp))
        · exact hn v
      · intro f hf
        exact he f (by simp [hf])

theorem relaxRound_le_self (edges : List (Edge n)) (old : DistanceArray n) (v : Fin n) :
    (relaxRound edges old).get v ≤ old.get v :=
  relaxEdges_le_initial edges old old v

theorem relaxRound_le_add_graph (edges : List (Edge n)) (old : DistanceArray n)
    (u v : Fin n) :
    (relaxRound edges old).get v ≤ old.get u + graphOfEdges edges u v := by
  by_cases h : graphOfEdges edges u v = ⊤
  · simp [h]
  obtain ⟨e, he, hs, ht, hc⟩ := exists_edge_eq edges h
  simpa only [relaxRound, hs, ht, hc] using relaxEdges_le_edge edges old old he

theorem runRounds_succ (edges : List (Edge n)) (k : ℕ) (d : DistanceArray n) :
    runRounds edges (k + 1) d = relaxRound edges (runRounds edges k d) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      exact ih (relaxRound edges d)

@[simp] theorem labels_zero (edges : List (Edge n)) (source : Fin n) :
    labels edges source 0 = initialDistances source := rfl

theorem labels_succ (edges : List (Edge n)) (source : Fin n) (k : ℕ) :
    labels edges source (k + 1) = relaxRound edges (labels edges source k) :=
  runRounds_succ edges k _

theorem runRounds_le_initial (edges : List (Edge n)) (k : ℕ)
    (d : DistanceArray n) (v : Fin n) : (runRounds edges k d).get v ≤ d.get v := by
  induction k generalizing d with
  | zero => exact le_rfl
  | succ k ih =>
      exact (ih (relaxRound edges d)).trans (relaxRound_le_self edges d v)

@[simp] theorem labels_source (edges : List (Edge n)) (source : Fin n) (k : ℕ) :
    (labels edges source k).get source = 0 := by
  apply le_antisymm _ bot_le
  simpa [labels] using runRounds_le_initial edges k (initialDistances source) source

theorem labels_le_pathCost (edges : List (Edge n)) (source : Fin n) (k : ℕ)
    {target : Fin n} {xs : List (Fin n)} (he : Graph.Endpoints xs source target)
    (hl : xs.length ≤ k + 1) :
    (labels edges source k).get target ≤ (graphOfEdges edges).pathCost xs := by
  induction k generalizing target xs with
  | zero =>
      obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty he)
      cases tail with
      | nil =>
          have hxs : x = source := by simpa [Graph.Endpoints] using he.1
          have hxt : x = target := by simpa [Graph.Endpoints] using he.2
          subst x
          subst target
          simp
      | cons y ys =>
          simp only [List.length_cons] at hl
          omega
  | succ k ih =>
      obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp he.2
      cases pre with
      | nil =>
          have hts : target = source := by simpa [Graph.Endpoints] using he.1
          subst target
          simp
      | cons x pre =>
          obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp
            (List.getLast?_eq_none_iff.not.mpr (List.cons_ne_nil x pre))
          have hp : Graph.Endpoints (x :: pre) source u := by
            refine ⟨?_, hu⟩
            simpa [Graph.Endpoints] using he.1
          have hpl : (x :: pre).length ≤ k + 1 := by
            simp only [List.length_append, List.length_singleton] at hl
            omega
          rw [labels_succ]
          calc
            (relaxRound edges (labels edges source k)).get target ≤
                (labels edges source k).get u + graphOfEdges edges u target :=
              relaxRound_le_add_graph edges _ u target
            _ ≤ (graphOfEdges edges).pathCost (x :: pre) + graphOfEdges edges u target :=
              add_le_add (ih hp hpl) le_rfl
            _ = (graphOfEdges edges).pathCost ((x :: pre) ++ [target]) := by
              rw [Graph.pathCost_append_of_getLast _ hu]
              simp

theorem labels_le_hopDist (edges : List (Edge n)) (source target : Fin n) (k : ℕ) :
    (labels edges source k).get target ≤ (graphOfEdges edges).hopDist k source target :=
  ((graphOfEdges edges).le_hopDist_iff k source target _).mpr
    (fun _ he hl => labels_le_pathCost edges source k he hl)

theorem hopDist_le_labels (edges : List (Edge n)) (source target : Fin n) (k : ℕ) :
    (graphOfEdges edges).hopDist k source target ≤ (labels edges source k).get target := by
  induction k generalizing target with
  | zero =>
      simp only [labels_zero, initialDistances_get]
      split_ifs with ht
      · subst target
        simp
      · exact le_top
  | succ k ih =>
      rw [labels_succ]
      apply relaxEdges_preserves_lower edges (labels edges source k)
        (labels edges source k) (fun v => (graphOfEdges edges).hopDist (k + 1) source v)
        (fun v => ((graphOfEdges edges).hopDist_antitone source v (Nat.le_succ k)).trans
          (ih v)) ?_ target
      intro e he
      exact ((graphOfEdges edges).hopDist_succ_le_add_edge k source e.source e.target).trans
        (add_le_add (ih e.source) (graphOfEdges_le_edge edges he))

theorem labels_eq_hopDist (edges : List (Edge n)) (source target : Fin n) (k : ℕ) :
    (labels edges source k).get target = (graphOfEdges edges).hopDist k source target :=
  le_antisymm (labels_le_hopDist edges source target k)
    (hopDist_le_labels edges source target k)

theorem bellmanFord_correct (edges : List (Edge n)) (source target : Fin n) :
    (bellmanFord edges source).get target = (graphOfEdges edges).dist source target := by
  rw [bellmanFord, labels_eq_hopDist]
  simpa only [Fintype.card_fin] using
    (graphOfEdges edges).hopDist_card_sub_one source target

theorem bellmanFord_perm {xs ys : List (Edge n)} (h : xs.Perm ys)
    (source target : Fin n) :
    (bellmanFord xs source).get target = (bellmanFord ys source).get target := by
  rw [bellmanFord_correct, bellmanFord_correct, graphOfEdges_perm h]

-- Cells count scalar edge fields and the two live distance vectors, not their bit lengths.
def workspaceCells (edges : List (Edge n)) (old next : DistanceArray n) : ℕ :=
  3 * edges.length + old.toArray.size + next.toArray.size

theorem workspaceCells_eq (edges : List (Edge n)) (old next : DistanceArray n) :
    workspaceCells edges old next = 3 * edges.length + 2 * n := by
  simp [workspaceCells]
  omega

theorem scan_memory (edges : List (Edge n)) (old next : DistanceArray n) (scanned : ℕ) :
    workspaceCells edges old (relaxEdges (edges.take scanned) old next) =
      3 * edges.length + 2 * n :=
  workspaceCells_eq edges old _

theorem bellmanFord_memory (edges : List (Edge n)) (source : Fin n)
    (round scanned : ℕ) :
    workspaceCells edges (labels edges source round)
      (relaxEdges (edges.take scanned) (labels edges source round)
        (labels edges source round)) = 3 * edges.length + 2 * n :=
  scan_memory edges _ _ scanned

theorem bellmanFord_linear_memory (edges : List (Edge n)) (source : Fin n)
    (round scanned : ℕ) :
    workspaceCells edges (labels edges source round)
      (relaxEdges (edges.take scanned) (labels edges source round)
        (labels edges source round)) ≤ 3 * (edges.length + n) := by
  rw [bellmanFord_memory]
  omega

end StreamingReachability.StoredEdges

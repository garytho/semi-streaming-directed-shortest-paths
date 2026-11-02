module

public import StreamingSSSP.Exact.Preprocess
public import StreamingSSSP.Graph.StoredEdges

@[expose] public section

namespace StreamingSSSP.Exact

variable {V : Type*} [Fintype V]

theorem tight_original_parent_exists (G : Graph V) (s : V) (W : ℕ)
    (distances : V → ℕ)
    (hspec : ∀ v, (preprocess G s W).dist s v = distances v)
    {v : V} (hv : v ≠ s) (hreachable : distances v < sentinel (Fintype.card V) W) :
    ∃ (u : V) (w : ℕ), G u v = w ∧
      distances u + Fintype.card V * w + 1 = distances v := by
  classical
  let F := preprocess G s W
  obtain ⟨xs, _, hx, _, hc⟩ := F.exists_dist_path (s := s) (t := v) (by simp [F, hspec v])
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hx.2
  have hysne : ys ≠ [] := by
    intro he
    have hhead := hx.1
    rw [hys, he] at hhead
    have hvs : v = s := by simpa using hhead
    exact hv hvs
  rcases List.eq_nil_or_concat ys with hnil | ⟨pre, u, hu⟩
  · exact (hysne hnil).elim
  · have hlist : xs = (pre ++ [u]) ++ [v] := by
      simpa [List.concat_eq_append] using hys.trans (congrArg (· ++ [v]) hu)
    have hprefix : Graph.Endpoints (pre ++ [u]) s u := by
      constructor
      · have hh := hx.1
        rw [hlist, List.head?_append_of_ne_nil _ (by simp)] at hh
        exact hh
      · simp
    have hsplit : F.pathCost (pre ++ [u]) + F u v = (distances v : Distance) := by
      have hh := hc.trans (hspec v)
      rw [hlist, F.pathCost_append_of_getLast hprefix.2] at hh
      simpa using hh
    obtain ⟨a, b, ha, hb, hab⟩ := finite_add hsplit
    have hc' : F.pathCost ((pre ++ [u]) ++ [v]) = F.dist s v := by
      rw [← hlist]
      exact hc
    have hshort : F.pathCost (pre ++ [u]) = F.dist s u :=
      F.shortest_path_prefix (post := [v]) (t := v) hprefix
        (by simp [Graph.Endpoints]) hc' (by rw [hc']; simp [F, hspec v])
    have hau : a = distances u := WithTop.coe_eq_coe.mp
      (ha.symm.trans (hshort.trans (hspec u)))
    have hbt : b < sentinel (Fintype.card V) W := by omega
    have hAedge : affineGraph G (Fintype.card V) 1 u v = b := by
      have hh := union_path_below (affineGraph G (Fintype.card V) 1)
        (sentinelGraph s (sentinel (Fintype.card V) W)) _ (sentinelGraph_lower s _)
        [u, v] b (by simpa [F, preprocess] using hb) hbt
      simpa using hh
    have hfinite : G u v ≠ ⊤ := by
      apply (mapWeights_ne_top G (fun w => Fintype.card V * w + 1) u v).mp
      change affineGraph G (Fintype.card V) 1 u v ≠ ⊤
      simp [hAedge]
    lift G u v to ℕ using hfinite with w hw
    refine ⟨u, w, hw.symm, ?_⟩
    have hwb : Fintype.card V * w + 1 = b := WithTop.coe_eq_coe.mp
      ((mapWeights_coe G _ hw.symm).symm.trans hAedge)
    omega

namespace ParentPass

open StoredEdges

variable {n : ℕ}

def Tight (source : Fin n) (W : ℕ) (distances : Fin n → ℕ) (e : Edge n) : Prop :=
  e.target ≠ source ∧ distances e.target < sentinel n W ∧
    distances e.source + n * e.weight + 1 = distances e.target

instance (source : Fin n) (W : ℕ) (distances : Fin n → ℕ) (e : Edge n) :
    Decidable (Tight source W distances e) := by
  unfold Tight
  infer_instance

abbrev State (n : ℕ) := Fin n → Option (Edge n)

def step (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (state : State n) (edge : Edge n) : State n :=
  fun v => if Tight source W distances edge ∧ v = edge.target then some edge else state v

def scan (source : Fin n) (W : ℕ) (distances : Fin n → ℕ) :
    List (Edge n) → State n → State n
  | [], state => state
  | edge :: rest, state => scan source W distances rest (step source W distances state edge)

def run (source : Fin n) (W : ℕ) (distances : Fin n → ℕ) (edges : List (Edge n)) : State n :=
  scan source W distances edges (fun _ => none)

theorem scan_valid (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (allEdges edges : List (Edge n)) (hsub : ∀ e ∈ edges, e ∈ allEdges)
    (state : State n)
    (hstate : ∀ v e, state v = some e →
      e ∈ allEdges ∧ e.target = v ∧ Tight source W distances e) :
    ∀ v e, scan source W distances edges state v = some e →
      e ∈ allEdges ∧ e.target = v ∧ Tight source W distances e := by
  induction edges generalizing state with
  | nil => exact hstate
  | cons edge rest ih =>
      apply ih (by intro e he; exact hsub e (by simp [he]))
      intro v e he
      dsimp [step] at he
      split_ifs at he with h
      · have heq : edge = e := Option.some.inj he
        subst e
        exact ⟨hsub edge (by simp), h.2.symm, h.1⟩
      · exact hstate v e he

theorem scan_assigned (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n)) (state : State n) (v : Fin n)
    (hstate : state v ≠ none) : scan source W distances edges state v ≠ none := by
  induction edges generalizing state with
  | nil => exact hstate
  | cons e edges ih =>
      apply ih
      dsimp [step]
      split_ifs <;> simp_all

theorem scan_fills (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n)) (state : State n) {e : Edge n}
    (he : e ∈ edges) (htight : Tight source W distances e) :
    scan source W distances edges state e.target ≠ none := by
  induction edges generalizing state with
  | nil => simp at he
  | cons edge rest ih =>
      rcases List.mem_cons.mp he with he | he
      · subst edge
        change scan source W distances rest (step source W distances state e) e.target ≠ none
        apply scan_assigned source W distances rest (step source W distances state e) e.target
        simp [step, htight]
      · exact ih (step source W distances state edge) he

theorem run_valid (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n)) :
    ∀ v e, run source W distances edges v = some e →
      e ∈ edges ∧ e.target = v ∧ Tight source W distances e :=
  scan_valid source W distances edges edges (fun _ h => h) _ (by simp)

theorem run_complete (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n))
    (hspec : ∀ v, (preprocess (graphOfEdges edges) source W).dist source v = distances v)
    {v : Fin n} (hv : v ≠ source) (hreachable : distances v < sentinel n W) :
    ∃ e, run source W distances edges v = some e := by
  obtain ⟨u, w, hw, heq⟩ := tight_original_parent_exists (graphOfEdges edges) source W
    distances hspec hv (by simpa using hreachable)
  obtain ⟨e, he, heu, hev, hew⟩ := exists_edge_eq edges (u := u) (v := v) (by simp [hw])
  have hew' : e.weight = w := WithTop.coe_eq_coe.mp (hew.trans hw)
  have htight : Tight source W distances e := by
    simp only [Tight, heu, hev, hew', Fintype.card_fin] at *
    exact ⟨hv, hreachable, heq⟩
  have hn := scan_fills source W distances edges (fun _ => none) he htight
  rw [hev] at hn
  exact Option.ne_none_iff_exists'.mp hn

theorem selected_edge_eq (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n))
    (hspec : ∀ v, (preprocess (graphOfEdges edges) source W).dist source v = distances v)
    {v : Fin n} {e : Edge n} (he : run source W distances edges v = some e) :
    graphOfEdges edges e.source v = (e.weight : Distance) := by
  obtain ⟨hemem, hev, htight⟩ := run_valid source W distances edges v e he
  have hn : 0 < n := by have hs := source.isLt; omega
  have hle : graphOfEdges edges e.source v ≤ (e.weight : Distance) := by
    simpa [hev] using graphOfEdges_le_edge edges hemem
  obtain ⟨w, hw, hwe⟩ := finite_of_le hle
  have hFedge : preprocess (graphOfEdges edges) source W e.source v ≤
      ((n * w + 1 : ℕ) : Distance) := by
    have hmap : affineGraph (graphOfEdges edges) n 1 e.source v = ((n * w + 1 : ℕ) : Distance) :=
      mapWeights_coe _ (fun z => n * z + 1) hw
    exact (min_le_left _ _).trans_eq (by simpa using hmap)
  have htri := (preprocess (graphOfEdges edges) source W).dist_le_dist_add_edge source e.source v
  have hdistle : (distances v : Distance) ≤
      ((distances e.source + (n * w + 1) : ℕ) : Distance) := by
    calc
      (distances v : Distance) ≤
          (distances e.source : Distance) + preprocess (graphOfEdges edges) source W e.source v := by
        simpa [hspec] using htri
      _ ≤ (distances e.source : Distance) + ((n * w + 1 : ℕ) : Distance) :=
        add_le_add le_rfl hFedge
      _ = _ := (Nat.cast_add _ _).symm
  have hnum : distances v ≤ distances e.source + (n * w + 1) := WithTop.coe_le_coe.mp hdistle
  have ht := htight.2.2
  rw [hev] at ht
  have hweq : w = e.weight := by nlinarith
  simpa [hweq] using hw

def graph (parents : State n) : Graph (Fin n) :=
  fun u v => match parents v with
    | none => ⊤
    | some e => if e.source = u then e.weight else ⊤

theorem graph_edge (parents : State n) {e : Edge n} {v : Fin n}
    (he : parents v = some e) : graph parents e.source v = (e.weight : Distance) := by
  simp [graph, he]

theorem graph_dominates (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n)) :
    ∀ u v, graphOfEdges edges u v ≤ graph (run source W distances edges) u v := by
  intro u v
  cases hp : run source W distances edges v with
  | none => simp [graph, hp]
  | some e =>
      by_cases heu : e.source = u
      · obtain ⟨hemem, hev, _⟩ := run_valid source W distances edges v e hp
        simpa [graph, hp, heu, hev] using graphOfEdges_le_edge edges hemem
      · simp [graph, hp, heu]

theorem parent_rank (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n)) {v : Fin n} {e : Edge n}
    (he : run source W distances edges v = some e) : distances e.source < distances v := by
  obtain ⟨_, hev, ht⟩ := run_valid source W distances edges v e he
  have hh := ht.2.2
  rw [hev] at hh
  omega

theorem parent_wellFounded (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n)) :
    WellFounded (fun u v => ∃ e, run source W distances edges v = some e ∧ e.source = u) := by
  apply (InvImage.wf distances Nat.lt_wfRel.wf).mono
  intro u v h
  obtain ⟨e, he, rfl⟩ := h
  exact parent_rank source W distances edges he

theorem parent_path (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n))
    (hspec : ∀ v, (preprocess (graphOfEdges edges) source W).dist source v = distances v)
    (v : Fin n) (hreachable : distances v < sentinel n W) :
    ∃ xs : List (Fin n), Graph.Endpoints xs source v ∧
      (affineGraph (graph (run source W distances edges)) n 1).pathCost xs = distances v := by
  generalize hd : distances v = d at *
  induction d using Nat.strong_induction_on generalizing v with
  | h d ih =>
      by_cases hv : v = source
      · subst v
        have hs0 : distances source = 0 := WithTop.coe_eq_coe.mp
          ((hspec source).symm.trans (Graph.dist_self _ _))
        have hd0 : d = 0 := by omega
        exact ⟨[source], by simp, by simp [hd0]⟩
      · have hreachable' : distances v < sentinel n W := by omega
        obtain ⟨e, he⟩ := run_complete source W distances edges hspec hv hreachable'
        obtain ⟨_, hev, ht⟩ := run_valid source W distances edges v e he
        have hrank := parent_rank source W distances edges he
        have hureach : distances e.source < sentinel n W := hrank.trans hreachable'
        obtain ⟨xs, hx, hc⟩ := ih (distances e.source) (by omega) e.source rfl hureach
        refine ⟨xs ++ [v], Graph.endpoints_append hx (by simp [Graph.Endpoints]), ?_⟩
        rw [Graph.pathCost_append_of_getLast _ hx.2]
        simp only [Graph.pathCost_cons_cons, Graph.pathCost_singleton, add_zero]
        have hedge : affineGraph (graph (run source W distances edges)) n 1 e.source v =
            ((n * e.weight + 1 : ℕ) : Distance) :=
          mapWeights_coe _ (fun z => n * z + 1) (graph_edge _ he)
        rw [hc, hedge]
        have hh := ht.2.2
        rw [hev] at hh
        exact (Nat.cast_add _ _).symm.trans (congrArg (fun k : ℕ => (k : Distance)) (by omega))

/-- The one-pass chosen parents form an acyclic shortest-path tree, including
inputs with zero weights and vertices unreachable from the source. -/
theorem tree_distances (source : Fin n) (W : ℕ) (distances : Fin n → ℕ)
    (edges : List (Edge n))
    (hW : WeightsBounded (graphOfEdges edges) W)
    (hspec : ∀ v, (preprocess (graphOfEdges edges) source W).dist source v = distances v) :
    (graph (run source W distances edges)).dist source = (graphOfEdges edges).dist source := by
  funext v
  have hmono := Graph.dist_mono (graph_dominates source W distances edges) source v
  by_cases hf : (graphOfEdges edges).dist source v = ⊤
  · simpa [hf] using top_le_iff.mp (hf ▸ hmono)
  · lift (graphOfEdges edges).dist source v to ℕ using hf with d hd
    obtain ⟨e, he, het, hed⟩ := preprocess_reachable_distance (graphOfEdges edges) source W hW hd.symm
    simp only [Fintype.card_fin] at het hed
    have hDv : distances v = e := WithTop.coe_eq_coe.mp ((hspec v).symm.trans he)
    obtain ⟨xs, hx, hc⟩ := parent_path source W distances edges hspec v (by simpa [hDv] using het)
    have hfinite : (graph (run source W distances edges)).pathCost xs ≠ ⊤ :=
      (affine_path_finite _ n 1 xs).mp (by simp [hc])
    lift (graph (run source W distances edges)).pathCost xs to ℕ using hfinite with c hcost
    have ha := affine_pathCost (graph (run source W distances edges)) n 1 xs c hcost.symm
    have hnum : n * c + 1 * (xs.length - 1) = distances v :=
      WithTop.coe_eq_coe.mp (ha.symm.trans hc)
    have hn : 0 < n := by have hs := source.isLt; omega
    have hcd : c ≤ d := by
      rw [← hed]
      apply (Nat.le_div_iff_mul_le hn).2
      nlinarith
    have htreele : (graph (run source W distances edges)).dist source v ≤ (d : Distance) :=
      ((graph (run source W distances edges)).dist_le_pathCost hx).trans
        (by rw [← hcost]; exact WithTop.coe_le_coe.mpr hcd)
    exact le_antisymm (by simpa [← hd] using htreele) hmono

end ParentPass

end StreamingSSSP.Exact

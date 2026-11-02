module

public import StreamingSSSP.Early.Geometry
public import StreamingSSSP.Graph.StoredEdges

@[expose] public section

namespace StreamingSSSP.Early

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

theorem bounded_nat_iff (n : ℕ) (R : ℝ) :
    Bounded (n : Distance) R ↔ (n : ℝ) ≤ R := by
  constructor
  · rintro ⟨m, hm, hR⟩
    have he : n = m := WithTop.coe_eq_coe.mp hm
    simpa only [he] using hR
  · exact fun h => ⟨n, rfl, h⟩

theorem bounded_sum_witness {a b : Distance} {R : ℝ} (h : Bounded (a + b) R) :
    ∃ m n : ℕ, a = m ∧ b = n ∧ (m : ℝ) + n ≤ R := by
  obtain ⟨m, hm, _⟩ := bounded_mono_distance
    (show a ≤ a + b from le_add_of_nonneg_right bot_le) h
  obtain ⟨n, hn, _⟩ := bounded_mono_distance
    (show b ≤ a + b from le_add_of_nonneg_left bot_le) h
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hm, hn, ← Nat.cast_add] at h
  simpa only [Nat.cast_add] using (bounded_nat_iff (m + n) R).mp h

/-- Exact-distance star, with no modification of the underlying graph. -/
def starGraph (G : Graph V) (p : V) (R : ℝ) : Graph V :=
  fun u v => if (u = p ∨ v = p) ∧ Within G u v R then G.dist u v else ⊤

theorem starGraph_in (G : Graph V) (p y : V) (R : ℝ) (h : Within G y p R) :
    starGraph G p R y p = G.dist y p := by
  simp [starGraph, h]

theorem starGraph_out (G : Graph V) (p z : V) (R : ℝ) (h : Within G p z R) :
    starGraph G p R p z = G.dist p z := by
  simp [starGraph, h]

theorem starGraph_noncontracting (G : Graph V) (p : V) (R : ℝ) (u v : V) :
    G.dist u v ≤ starGraph G p R u v := by
  unfold starGraph
  split_ifs <;> simp

def StarShortcut (H : Graph V) (y p z : V) (B : ℝ) : Prop :=
  ∃ a b : ℕ, H y p = a ∧ H p z = b ∧ (a : ℝ) + b ≤ B

omit [Fintype V] in
theorem starShortcut_of_bounded {H : Graph V} {y p z : V} {B : ℝ}
    (h : Bounded (H y p + H p z) B) : StarShortcut H y p z B :=
  bounded_sum_witness h

theorem StarShortcut.hopDist {H : Graph V} {y p z : V} {B : ℝ}
    (h : StarShortcut H y p z B) : Bounded (H.hopDist 2 y z) B := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  apply bounded_mono_distance (H.hopDist_le_pathCost
    (xs := [y, p, z]) (by simp [Graph.Endpoints]) (by simp))
  simpa only [Graph.pathCost_cons_cons, Graph.pathCost_singleton, ha, hb, add_zero,
    ← Nat.cast_add] using (bounded_nat_iff (a + b) B).mpr (by simpa using hab)

theorem path_endpoint_bounds (G : Graph V) {xs : List V} {y z u : V} {R : ℝ}
    (he : Graph.Endpoints xs y z) (hc : Bounded (G.pathCost xs) R) (hu : u ∈ xs) :
    Within G y u R ∧ Within G u z R := by
  obtain ⟨pre, post, hxs, hleft, hright⟩ := Graph.endpoints_split_at_mem he hu
  have hl : G.pathCost (pre ++ [u]) ≤ G.pathCost xs := by
    rw [hxs]
    simpa only [List.append_assoc, List.singleton_append] using
      G.pathCost_prefix_le (pre ++ [u]) post
  have hr : G.pathCost (u :: post) ≤ G.pathCost xs := by
    rw [hxs]
    exact G.pathCost_suffix_le pre (u :: post)
  exact ⟨bounded_mono_distance ((G.dist_le_pathCost hleft).trans hl) hc,
    bounded_mono_distance ((G.dist_le_pathCost hright).trans hr) hc⟩

omit [Fintype V] in
/-- Costs outside a contiguous middle path are charged only once. This
does not compare parent and child edge weights. -/
theorem path_sides_budget (G : Graph V) (pre middle post : List V)
    {y s t z : V} (he : Graph.Endpoints (pre ++ middle ++ post) y z)
    (hm : Graph.Endpoints middle s t) (c : ℕ)
    (hc : G.pathCost (pre ++ middle ++ post) = c) :
    ∃ l r : ℕ, Graph.Endpoints (pre ++ [s]) y s ∧
      Graph.Endpoints (t :: post) t z ∧
      G.pathCost (pre ++ [s]) = l ∧ G.pathCost (t :: post) = r ∧
      (l : ℝ) + r ≤ c := by
  obtain ⟨s', tail, hmid⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty hm)
  have hs : s' = s := by simpa [Graph.Endpoints, hmid] using hm.1
  subst s'
  have hleft : Graph.Endpoints (pre ++ [s]) y s := by
    refine ⟨?_, by simp⟩
    cases pre with
    | nil => simpa [hmid] using he.1
    | cons x pre => simpa using he.1
  have hright : Graph.Endpoints (t :: post) t z := by
    refine ⟨rfl, ?_⟩
    cases post with
    | nil =>
        have htz : t = z := by
          have hz : (s :: tail).getLast? = some z := by
            simpa only [List.append_nil, hmid, List.getLast?_append_cons] using he.2
          have ht : (s :: tail).getLast? = some t := by simpa only [hmid] using hm.2
          exact Option.some.inj (ht.symm.trans hz)
        simp [htz]
    | cons x post => simpa using he.2
  have hsplit :
      G.pathCost (pre ++ middle ++ post) =
        G.pathCost (pre ++ [s]) + (G.pathCost middle + G.pathCost (t :: post)) := by
    rw [hmid, List.append_assoc]
    change G.pathCost (pre ++ s :: (tail ++ post)) = _
    rw [G.pathCost_split pre (tail ++ post) s]
    change G.pathCost (pre ++ [s]) + G.pathCost ((s :: tail) ++ post) = _
    rw [G.pathCost_append_of_getLast (by simpa [hmid] using hm.2) post]
  have hside :
      G.pathCost (pre ++ [s]) + G.pathCost (t :: post) ≤
        G.pathCost (pre ++ middle ++ post) := by
    rw [hsplit]
    exact add_le_add le_rfl (le_add_of_nonneg_left bot_le)
  obtain ⟨l, r, hl, hr, hlr⟩ := bounded_sum_witness
    (bounded_mono_distance hside (show Bounded (G.pathCost (pre ++ middle ++ post)) c from
      ⟨c, hc, le_rfl⟩))
  exact ⟨l, r, hleft, hright, hl, hr, hlr⟩

/-- The bridge is in the actual child graph and the nesting is an equality
of actual vertex lists. Distance monotonicity alone suffices. -/
theorem nested_bridge_bounds (G F : Graph V) {Dold Dnew R : ℝ}
    (outer : ShortPath G Dold) (inner : ShortPath F Dnew)
    (hnested : ∃ pre post, outer.vertices = pre ++ inner.vertices ++ post)
    {y p z : V} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v) (hb : Bridge inner p R) :
    Within G y p (Dold + R) ∧ Within G p z (Dold + R) ∧
      Bounded (G.dist y p + G.dist p z) ((outer.cost : ℝ) + 2 * Dnew + 2 * R) := by
  obtain ⟨pre, post, hnested⟩ := hnested
  obtain ⟨⟨ib, hpb⟩, ⟨ia, hap⟩⟩ := hb
  have hamem : inner.vertex ia ∈ inner.vertices := List.get_mem _ _
  have hbmem : inner.vertex ib ∈ inner.vertices := List.get_mem _ _
  have houter (v : V) (hv : v ∈ inner.vertices) : v ∈ outer.vertices := by
    rw [hnested]
    exact List.mem_append_left _ (List.mem_append_right _ hv)
  have hcost : Bounded (G.pathCost outer.vertices) Dold :=
    ⟨outer.cost, outer.cost_eq, outer.cost_le⟩
  have hya := (path_endpoint_bounds G hends hcost (houter _ hamem)).1
  have hbz := (path_endpoint_bounds G hends hcost (houter _ hbmem)).2
  have hapG : Within G (inner.vertex ia) p R := bounded_mono_distance (hmono _ _) hap
  have hpbG : Within G p (inner.vertex ib) R := bounded_mono_distance (hmono _ _) hpb
  refine ⟨within_trans hya hapG, ?_, ?_⟩
  · simpa only [add_comm] using within_trans hpbG hbz
  · obtain ⟨s, tail, hmid⟩ := List.exists_cons_of_ne_nil inner.nonempty
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp
      (List.getLast?_eq_none_iff.not.mpr inner.nonempty)
    have hmidends : Graph.Endpoints inner.vertices s t := ⟨by simp [hmid], ht⟩
    have hmidcost : Bounded (F.pathCost inner.vertices) Dnew :=
      ⟨inner.cost, inner.cost_eq, inner.cost_le⟩
    have hsa : Within G s (inner.vertex ia) Dnew := bounded_mono_distance
      (hmono _ _) (path_endpoint_bounds F hmidends hmidcost hamem).1
    have hbt : Within G (inner.vertex ib) t Dnew := bounded_mono_distance
      (hmono _ _) (path_endpoint_bounds F hmidends hmidcost hbmem).2
    obtain ⟨l, r, hleft, hright, hl, hr, hlr⟩ :=
      path_sides_budget G pre inner.vertices post
        (by simpa only [← hnested] using hends) hmidends outer.cost
        (by simpa only [← hnested] using outer.cost_eq)
    have hyl : Within G y s l :=
      bounded_mono_distance (G.dist_le_pathCost hleft) ⟨l, hl, le_rfl⟩
    have hrz : Within G t z r :=
      bounded_mono_distance (G.dist_le_pathCost hright) ⟨r, hr, le_rfl⟩
    have hsum := bounded_add (within_trans (within_trans hyl hsa) hapG)
      (within_trans (within_trans hpbG hbt) hrz)
    exact bounded_mono_radius hsum (by linarith)

theorem nested_advance_star (G F : Graph V) {Dold Dnew eta : ℝ}
    (outer : ShortPath G Dold) (inner : ShortPath F Dnew)
    (hnested : ∃ pre post, outer.vertices = pre ++ inner.vertices ++ post)
    {y p z : V} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ Dold / 2) (heta : 2 ≤ eta) :
    Within G y p (eta * Dold) ∧ Within G p z (eta * Dold) ∧
      StarShortcut (starGraph G p (eta * Dold)) y p z
        ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  have hgeom := nested_bridge_bounds G F outer inner hnested hends hmono hb
  have hDold := outer.scale_nonneg
  have hDnew := inner.scale_nonneg
  have hscale' := mul_le_mul_of_nonneg_left hscale (show 0 ≤ eta by linarith)
  have hbudget : Dold + eta * Dnew ≤ eta * Dold := by nlinarith
  have hleft := within_mono hgeom.1 hbudget
  have hright := within_mono hgeom.2.1 hbudget
  refine ⟨hleft, hright, starShortcut_of_bounded ?_⟩
  rw [starGraph_in G p y _ hleft, starGraph_out G p z _ hright]
  exact bounded_mono_radius hgeom.2.2 (by nlinarith)

theorem global_advance_star (G F : Graph V) {Dnew Delta eta : ℝ}
    (outer : ShortPath G (3 * Delta)) (inner : ShortPath F Dnew)
    (hnested : ∃ pre post, outer.vertices = pre ++ inner.vertices ++ post)
    {y p z : V} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hsearch : eta * Dnew ≤ 5 * Delta) (heta : 2 ≤ eta) :
    Within G y p (8 * Delta) ∧ Within G p z (8 * Delta) ∧
      StarShortcut (starGraph G p (8 * Delta)) y p z
        ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  have hgeom := nested_bridge_bounds G F outer inner hnested hends hmono hb
  have hleft := within_mono hgeom.1 (by linarith : 3 * Delta + eta * Dnew ≤ 8 * Delta)
  have hright := within_mono hgeom.2.1 (by linarith : 3 * Delta + eta * Dnew ≤ 8 * Delta)
  refine ⟨hleft, hright, starShortcut_of_bounded ?_⟩
  rw [starGraph_in G p y _ hleft, starGraph_out G p z _ hright]
  have hDnew := inner.scale_nonneg
  exact bounded_mono_radius hgeom.2.2 (by nlinarith)

theorem nested_advance_star_of_infix (G F : Graph V) {Dold Dnew eta : ℝ}
    (outer : ShortPath G Dold) (inner : ShortPath F Dnew)
    (hnested : inner.vertices.IsInfix outer.vertices)
    {y p z : V} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ Dold / 2) (heta : 2 ≤ eta) :
    Within G y p (eta * Dold) ∧ Within G p z (eta * Dold) ∧
      StarShortcut (starGraph G p (eta * Dold)) y p z
        ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  obtain ⟨pre, post, h⟩ := hnested
  exact nested_advance_star G F outer inner ⟨pre, post, h.symm⟩ hends hmono hb hscale heta

theorem global_advance_star_from_initial_scale (G F : Graph V) {Dnew D0 Delta eta : ℝ}
    (outer : ShortPath G (3 * Delta)) (inner : ShortPath F Dnew)
    (hnested : inner.vertices.IsInfix outer.vertices)
    {y p z : V} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ D0) (hsearch : eta * D0 ≤ 5 * Delta) (heta : 2 ≤ eta) :
    Within G y p (8 * Delta) ∧ Within G p z (8 * Delta) ∧
      StarShortcut (starGraph G p (8 * Delta)) y p z
        ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  obtain ⟨pre, post, h⟩ := hnested
  exact global_advance_star G F outer inner ⟨pre, post, h.symm⟩ hends hmono hb
    ((mul_le_mul_of_nonneg_left hscale (by linarith)).trans hsearch) heta

namespace StarArrays

open StoredEdges

variable {n : ℕ}

def graph (p : Fin n) (forward backward : DistanceArray n) (R : ℝ) : Graph (Fin n) :=
  fun u v => if u = p ∧ Bounded (forward.get v) R then forward.get v else
    if v = p ∧ Bounded (backward.get u) R then backward.get u else ⊤

theorem graph_eq_star (G : Graph (Fin n)) (p : Fin n)
    (forward backward : DistanceArray n) (R : ℝ)
    (hf : ∀ v, forward.get v = G.dist p v)
    (hb : ∀ u, backward.get u = G.dist u p) :
    graph p forward backward R = starGraph G p R := by
  funext u v
  simp only [graph, hf, hb, starGraph, Within]
  by_cases hu : u = p <;> by_cases hv : v = p <;>
    by_cases h : Bounded (G.dist u v) R <;> simp_all

def reverseEdge (e : Edge n) : Edge n := ⟨e.target, e.source, e.weight⟩

def reverseEdges (edges : List (Edge n)) : List (Edge n) := edges.map reverseEdge

theorem reverseEdges_graph (edges : List (Edge n)) :
    graphOfEdges (reverseEdges edges) = (graphOfEdges edges).reverse := by
  funext u v
  induction edges with
  | nil => simp [reverseEdges, Graph.reverse]
  | cons e edges ih =>
      simp only [reverseEdges, List.map_cons, graphOfEdges_cons] at ih ⊢
      rw [ih]
      simp [edgeCost, reverseEdge, Graph.reverse, and_comm]

/-- The existing closed Bellman--Ford distance arrays realize the exact star.
The same `graph_eq_star` interface applies to any other verified exact rows. -/
def queried (edges : List (Edge n)) (p : Fin n) (R : ℝ) : Graph (Fin n) :=
  graph p (bellmanFord edges p) (bellmanFord (reverseEdges edges) p) R

theorem queried_eq_star (edges : List (Edge n)) (p : Fin n) (R : ℝ) :
    queried edges p R = starGraph (graphOfEdges edges) p R := by
  apply graph_eq_star
  · exact bellmanFord_correct edges p
  · intro u
    rw [bellmanFord_correct, reverseEdges_graph, Graph.dist_reverse]

def emit (source target : Fin n) (d : Distance) (R : ℝ) : List (Edge n) :=
  if Bounded d R then [⟨source, target, d.untopD 0⟩] else []

theorem mem_emit (source target : Fin n) (d : Distance) (R : ℝ) (e : Edge n) :
    e ∈ emit source target d R ↔
      ∃ w : ℕ, d = w ∧ (w : ℝ) ≤ R ∧ e = ⟨source, target, w⟩ := by
  by_cases h : Bounded d R
  · obtain ⟨w, hd, hw⟩ := h
    subst d
    have hemit : emit source target (w : Distance) R = [⟨source, target, w⟩] := by
      rw [emit, ite_eq_left (show Bounded (w : Distance) R from ⟨w, rfl, hw⟩)]
      exact congrArg (fun a : ℕ => ([⟨source, target, a⟩] : List (Edge n)))
        (WithTop.untopD_coe 0 w)
    rw [hemit, List.mem_singleton]
    constructor
    · exact fun he => ⟨w, rfl, hw, he⟩
    · rintro ⟨a, ha, _, he⟩
      have haw : w = a := WithTop.coe_eq_coe.mp ha
      simpa only [← haw] using he
  · simp only [emit, h, ↓reduceIte, List.not_mem_nil, false_iff]
    rintro ⟨w, hw, hR, _⟩
    exact h ⟨w, hw, hR⟩

/-- Every finite in/out query-array entry inside the requested radius
is emitted, including entries whose endpoint is another pivot. -/
def edges (p : Fin n) (forward backward : DistanceArray n) (R : ℝ) : List (Edge n) :=
  (List.finRange n).flatMap fun v =>
    emit p v (forward.get v) R ++ emit v p (backward.get v) R

theorem edges_eq_star (G : Graph (Fin n)) (p : Fin n)
    (forward backward : DistanceArray n) (R : ℝ)
    (hf : ∀ v, forward.get v = G.dist p v)
    (hb : ∀ u, backward.get u = G.dist u p) :
    graphOfEdges (edges p forward backward R) = starGraph G p R := by
  funext u v
  apply le_antisymm
  · by_cases h : (u = p ∨ v = p) ∧ Within G u v R
    · obtain ⟨w, hw, hR⟩ := h.2
      have hm : (⟨u, v, w⟩ : Edge n) ∈ edges p forward backward R := by
        rcases h.1 with hu | hv
        · subst u
          apply List.mem_flatMap.mpr
          refine ⟨v, List.mem_finRange v, List.mem_append_left _ ?_⟩
          exact (mem_emit _ _ _ _ _).mpr ⟨w, (hf v).trans hw, hR, rfl⟩
        · subst v
          apply List.mem_flatMap.mpr
          refine ⟨u, List.mem_finRange u, List.mem_append_right _ ?_⟩
          exact (mem_emit _ _ _ _ _).mpr ⟨w, (hb u).trans hw, hR, rfl⟩
      have hle := graphOfEdges_le_edge _ hm
      simpa [starGraph, h, hw] using hle
    · simp only [starGraph, h, ↓reduceIte, le_top]
  · apply (le_graphOfEdges_iff _ u v _).mpr
    intro e he hs ht
    obtain ⟨q, _, he⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨w, hw, hR, rfl⟩ := (mem_emit _ _ _ _ _).mp he
      have hd : G.dist p q = w := (hf q).symm.trans hw
      have hwithin : Within G p q R := ⟨w, hd, hR⟩
      change p = u at hs
      change q = v at ht
      rw [← hs, ← ht]
      exact (starGraph_out G p q R hwithin).le.trans hd.le
    · obtain ⟨w, hw, hR, rfl⟩ := (mem_emit _ _ _ _ _).mp he
      have hd : G.dist q p = w := (hb q).symm.trans hw
      have hwithin : Within G q p R := ⟨w, hd, hR⟩
      change q = u at hs
      change p = v at ht
      rw [← hs, ← ht]
      exact (starGraph_in G p q R hwithin).le.trans hd.le

/-- Exactness is needed only inside the star radius. Other entries of a
capped or sparse exact query array may be infinity. -/
def ExactAt (row : DistanceArray n) (d : Fin n → Distance) (R : ℝ) : Prop :=
  (∀ v, Bounded (d v) R → row.get v = d v) ∧
    ∀ v, Bounded (row.get v) R → row.get v = d v

theorem ExactAt.mono {row : DistanceArray n} {d : Fin n → Distance} {R S : ℝ}
    (h : ExactAt row d S) (hRS : R ≤ S) : ExactAt row d R :=
  ⟨fun v hv => h.1 v (bounded_mono_radius hv hRS),
    fun v hv => h.2 v (bounded_mono_radius hv hRS)⟩

theorem ExactAt.of_lower {row : DistanceArray n} {d : Fin n → Distance} {R : ℝ}
    (hlower : ∀ v, d v ≤ row.get v)
    (hexact : ∀ v, Bounded (d v) R → row.get v = d v) : ExactAt row d R :=
  ⟨hexact, fun v hv => hexact v (bounded_mono_distance (hlower v) hv)⟩

theorem emit_eq_of_exact {source target : Fin n} {d e : Distance} {R : ℝ}
    (hcomplete : Bounded d R → e = d) (hsound : Bounded e R → e = d) :
    emit source target e R = emit source target d R := by
  by_cases hd : Bounded d R
  · rw [hcomplete hd]
  · have he : ¬ Bounded e R := by
      intro h
      exact hd ((hsound h) ▸ h)
    simp only [emit, hd, he, ↓reduceIte]

theorem edges_eq_star_of_exactAt (G : Graph (Fin n)) (p : Fin n)
    (forward backward : DistanceArray n) (R : ℝ)
    (hf : ExactAt forward (fun v => G.dist p v) R)
    (hb : ExactAt backward (fun u => G.dist u p) R) :
    graphOfEdges (edges p forward backward R) = starGraph G p R := by
  let forward' : DistanceArray n := Vector.ofFn fun v => G.dist p v
  let backward' : DistanceArray n := Vector.ofFn fun u => G.dist u p
  have he : edges p forward backward R = edges p forward' backward' R := by
    unfold edges
    apply congrArg (fun f : Fin n → List (Edge n) => (List.finRange n).flatMap f)
    funext v
    have hf' : forward'.get v = G.dist p v := by simp [forward']
    have hb' : backward'.get v = G.dist v p := by simp [backward']
    rw [hf', hb', emit_eq_of_exact (hf.1 v) (hf.2 v),
      emit_eq_of_exact (hb.1 v) (hb.2 v)]
  rw [he]
  exact edges_eq_star G p forward' backward' R (by intro v; simp [forward'])
    (by intro u; simp [backward'])

theorem arrays_advance_star (G F : Graph (Fin n)) {Dold Dnew eta : ℝ}
    (outer : ShortPath G Dold) (inner : ShortPath F Dnew)
    (hnested : inner.vertices.IsInfix outer.vertices)
    {y p z : Fin n} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ Dold / 2) (heta : 2 ≤ eta)
    (forward backward : DistanceArray n)
    (hf : ExactAt forward (fun v => G.dist p v) (eta * Dold))
    (hin : ExactAt backward (fun u => G.dist u p) (eta * Dold)) :
    StarShortcut (graphOfEdges (edges p forward backward (eta * Dold))) y p z
      ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  rw [edges_eq_star_of_exactAt G p forward backward _ hf hin]
  exact (nested_advance_star_of_infix G F outer inner hnested hends hmono hb hscale heta).2.2

theorem arrays_global_star (G F : Graph (Fin n)) {Dnew D0 Delta eta : ℝ}
    (outer : ShortPath G (3 * Delta)) (inner : ShortPath F Dnew)
    (hnested : inner.vertices.IsInfix outer.vertices)
    {y p z : Fin n} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ D0) (hsearch : eta * D0 ≤ 5 * Delta) (heta : 2 ≤ eta)
    (forward backward : DistanceArray n)
    (hf : ExactAt forward (fun v => G.dist p v) (8 * Delta))
    (hin : ExactAt backward (fun u => G.dist u p) (8 * Delta)) :
    StarShortcut (graphOfEdges (edges p forward backward (8 * Delta))) y p z
      ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  rw [edges_eq_star_of_exactAt G p forward backward _ hf hin]
  exact (global_advance_star_from_initial_scale G F outer inner hnested hends hmono hb
    hscale hsearch heta).2.2

def queriedEdges (input : List (Edge n)) (p : Fin n) (R : ℝ) : List (Edge n) :=
  edges p (bellmanFord input p) (bellmanFord (reverseEdges input) p) R

theorem queriedEdges_eq_star (input : List (Edge n)) (p : Fin n) (R : ℝ) :
    graphOfEdges (queriedEdges input p R) = starGraph (graphOfEdges input) p R := by
  apply edges_eq_star
  · exact bellmanFord_correct input p
  · intro u
    rw [bellmanFord_correct, reverseEdges_graph, Graph.dist_reverse]

theorem queried_advance_star (input : List (Edge n)) (F : Graph (Fin n))
    {Dold Dnew eta : ℝ}
    (outer : ShortPath (graphOfEdges input) Dold) (inner : ShortPath F Dnew)
    (hnested : inner.vertices.IsInfix outer.vertices)
    {y p z : Fin n} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, (graphOfEdges input).dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ Dold / 2) (heta : 2 ≤ eta) :
    StarShortcut (graphOfEdges (queriedEdges input p (eta * Dold))) y p z
      ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  rw [queriedEdges_eq_star]
  exact (nested_advance_star_of_infix _ F outer inner hnested hends hmono hb hscale heta).2.2

theorem queried_global_star (input : List (Edge n)) (F : Graph (Fin n))
    {Dnew D0 Delta eta : ℝ}
    (outer : ShortPath (graphOfEdges input) (3 * Delta)) (inner : ShortPath F Dnew)
    (hnested : inner.vertices.IsInfix outer.vertices)
    {y p z : Fin n} (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, (graphOfEdges input).dist u v ≤ F.dist u v)
    (hb : Bridge inner p (eta * Dnew))
    (hscale : Dnew ≤ D0) (hsearch : eta * D0 ≤ 5 * Delta) (heta : 2 ≤ eta) :
    StarShortcut (graphOfEdges (queriedEdges input p (8 * Delta))) y p z
      ((outer.cost : ℝ) + 3 * eta * Dnew) := by
  rw [queriedEdges_eq_star]
  exact (global_advance_star_from_initial_scale _ F outer inner hnested hends hmono hb
    hscale hsearch heta).2.2

end StarArrays

end

end StreamingSSSP.Early

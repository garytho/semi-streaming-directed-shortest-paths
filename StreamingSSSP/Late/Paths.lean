module

public import StreamingSSSP.Hopset.Underlying
public import StreamingSSSP.Core.Rounding
public import StreamingSSSP.Early.Radii

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

def rounded (A : ℕ) {V : Type*} (G : Graph V) : Graph V :=
  fun u v => Core.roundDistance A (G u v)

theorem within_edge {V : Type*} [Fintype V] (G : Graph V) {u v : V}
    {a : ℕ} (h : G u v ≤ (a : Distance)) : Within G u v (a : ℝ) :=
  bounded_mono_distance ((G.dist_le_edge u v).trans h) ⟨a, rfl, le_rfl⟩

def join {V : Type*} (xs ys : List V) : List V := xs ++ ys.tail

theorem join_endpoints {V : Type*} {xs ys : List V} {s u t : V}
    (hx : Graph.Endpoints xs s u) (hy : Graph.Endpoints ys u t) :
    Graph.Endpoints (join xs ys) s t := by
  obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty hy)
  have hv : v = u := by simpa [Graph.Endpoints] using hy.1
  subst v
  exact Graph.endpoints_append hx hy

theorem join_cost {V : Type*} (G : Graph V) {xs ys : List V} {s u t : V}
    (hx : Graph.Endpoints xs s u) (hy : Graph.Endpoints ys u t) :
    G.pathCost (join xs ys) = G.pathCost xs + G.pathCost ys := by
  obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty hy)
  have hv : v = u := by simpa [Graph.Endpoints] using hy.1
  subst v
  exact G.pathCost_append_of_getLast hx.2 vs

theorem join_length {V : Type*} (xs ys : List V) (hy : ys ≠ []) :
    (join xs ys).length ≤ xs.length + ys.length - 1 := by
  have hp := List.length_pos_iff.mpr hy
  simp only [join, List.length_append, List.length_tail]
  omega

variable {n : ℕ}

/-- Proof data fixed before any current-level coins. The closure alternative is
the actual attained frozen-base shortest path, not a stored algorithmic record. -/
inductive Origin (R : Representation n) (G : Graph (Fin n)) (u v : Fin n) : Type
  | ordinary (eq : R.base G u v = R.graph G u v)
  | block (witness : R.ClosureWitness G u v)

namespace Origin

variable {R : Representation n} {G : Graph (Fin n)} {u v : Fin n}

def vertices : Origin R G u v → List (Fin n)
  | .ordinary _ => [u, v]
  | .block W => W.vertices

theorem endpoints (o : Origin R G u v) : Graph.Endpoints o.vertices u v := by
  cases o with
  | ordinary h => simp [vertices, Graph.Endpoints]
  | block W => exact W.endpoints

theorem cost (o : Origin R G u v) :
    (R.base G).pathCost o.vertices = R.graph G u v := by
  cases o with
  | ordinary h => simpa [vertices] using h
  | block W => exact W.weight_eq

theorem exists_origin (hf : R.graph G u v ≠ ⊤) : Nonempty (Origin R G u v) := by
  rcases R.exists_origin G u v hf with h | h
  · exact ⟨.ordinary h⟩
  · exact ⟨.block (Classical.choice h)⟩

end Origin

structure Edge (R : Representation n) (G : Graph (Fin n)) (u v : Fin n) where
  micro : ℕ
  weight : R.graph G u v = micro
  distinct : u ≠ v
  origin : Origin R G u v

namespace Edge

variable {R : Representation n} {G : Graph (Fin n)} {u v : Fin n}

def vertices (e : Edge R G u v) : List (Fin n) := e.origin.vertices

def Inside (e : Edge R G u v) (S : Finset (Fin n)) : Prop :=
  ∀ z ∈ e.vertices, z ∈ S

def searchWeight (e : Edge R G u v) (A : ℕ) : ℕ := Core.ceilNat A e.micro

theorem endpoints (e : Edge R G u v) : Graph.Endpoints e.vertices u v :=
  e.origin.endpoints

theorem cost (e : Edge R G u v) : (R.base G).pathCost e.vertices = e.micro :=
  e.origin.cost.trans e.weight

theorem endpoints_inside (e : Edge R G u v) {S : Finset (Fin n)} (h : e.Inside S) :
    u ∈ S ∧ v ∈ S :=
  ⟨h u (endpoints_mem e.endpoints).1, h v (endpoints_mem e.endpoints).2⟩

theorem restricted_weight (e : Edge R G u v) {S : Finset (Fin n)}
    (hS : e.Inside S) : R.restricted G S u v = e.micro := by
  have hge := R.restricted_mono G (S := Finset.univ) (T := S) (Finset.subset_univ S) u v
  rw [Representation.restricted_univ, e.weight] at hge
  apply le_antisymm _ hge
  cases he : e.origin with
  | ordinary h =>
      have hbase := closures_le_base (induced (R.base G) S) (R.blocks.map (· ∩ S)) u v
      have hin := e.endpoints_inside hS
      have hb : induced (R.base G) S u v = e.micro := by
        simp only [induced, ite_eq_left hin, h, e.weight]
      exact hbase.trans_eq hb
  | block W =>
      have hw : ∀ z ∈ W.vertices, z ∈ S := by
        simpa only [Inside, vertices, he, Origin.vertices] using hS
      rw [R.witness_survives G W e.distinct S hw, e.weight]

theorem search_edge (e : Edge R G u v) (A : ℕ) {S : Finset (Fin n)}
    (hS : e.Inside S) :
    rounded A (R.restricted G S) u v = (e.searchWeight A : Distance) := by
  simp only [rounded, e.restricted_weight hS, Core.roundDistance_coe, searchWeight]

theorem subpath_bounds (e : Edge R G u v) (A : ℕ) (hA : 0 < A)
    {S : Finset (Fin n)} (hS : e.Inside S) {z : Fin n} (hz : z ∈ e.vertices) :
    Within (rounded A (R.restricted G S)) u z (e.searchWeight A : ℝ) ∧
      Within (rounded A (R.restricted G S)) z v (e.searchWeight A : ℝ) := by
  let H := rounded A (R.restricted G S)
  have he : H u v ≤ (e.searchWeight A : Distance) := (e.search_edge A hS).le
  cases ho : e.origin with
  | ordinary h =>
      have hm : z = u ∨ z = v := by simpa [vertices, ho, Origin.vertices] using hz
      rcases hm with h | h
      · subst z
        exact ⟨within_self H _ (Nat.cast_nonneg _), within_edge H he⟩
      · subst z
        exact ⟨within_edge H he, within_self H _ (Nat.cast_nonneg _)⟩
  | block W =>
      have hzW : z ∈ W.vertices := by simpa [vertices, ho, Origin.vertices] using hz
      have hWS : ∀ y ∈ W.vertices, y ∈ W.block ∩ S := by
        intro y hy
        exact Finset.mem_inter.mpr ⟨W.inside y hy, hS y (by simpa [vertices, ho,
          Origin.vertices] using hy)⟩
      obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hzW
      have hpre : Graph.Endpoints (pre ++ [z]) u z := by
        refine ⟨?_, by simp⟩
        have hh := W.endpoints.1
        rw [hsplit] at hh
        cases pre <;> simpa [Graph.Endpoints] using hh
      have hpost : Graph.Endpoints (z :: post) z v := by
        refine ⟨rfl, ?_⟩
        simpa only [hsplit, List.getLast?_append_cons] using W.endpoints.2
      have hpreS : ∀ y ∈ pre ++ [z], y ∈ W.block ∩ S := by
        intro y hy
        apply hWS y
        rw [hsplit]
        simpa only [List.mem_append, List.mem_cons, List.mem_singleton] using
          (show y ∈ pre ∨ y = z ∨ y ∈ post from by
            rcases List.mem_append.mp hy with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl (List.mem_singleton.mp h)))
      have hpostS : ∀ y ∈ z :: post, y ∈ W.block ∩ S := by
        intro y hy
        apply hWS y
        rw [hsplit]
        exact List.mem_append_right _ hy
      constructor
      · by_cases huz : u = z
        · subst z
          exact within_self H u (Nat.cast_nonneg _)
        · have hb := R.restricted_subpath_edge G S W.block W.member [] (pre ++ [z])
            post hpre huz hpreS
          have hc : (R.base G).pathCost ([] ++ (pre ++ [z]) ++ post) = e.micro := by
            simpa only [List.nil_append, List.append_assoc, List.singleton_append,
              ← hsplit, W.weight_eq] using e.weight
          rw [hc] at hb
          apply within_edge H
          exact Core.roundDistance_mono hA hb
      · by_cases hzv : z = v
        · subst z
          exact within_self H v (Nat.cast_nonneg _)
        · have hb := R.restricted_subpath_edge G S W.block W.member pre (z :: post)
            [] hpost hzv hpostS
          have hc : (R.base G).pathCost (pre ++ (z :: post) ++ []) = e.micro := by
            rw [List.append_nil, ← hsplit, W.weight_eq, e.weight]
          rw [hc] at hb
          apply within_edge H
          exact Core.roundDistance_mono hA hb

end Edge

inductive Path (R : Representation n) (G : Graph (Fin n)) : Fin n → Fin n → Type
  | nil (u : Fin n) : Path R G u u
  | cons {u v t : Fin n} (edge : Edge R G u v) (tail : Path R G v t) : Path R G u t

namespace Path

variable {R : Representation n} {G : Graph (Fin n)} {s t u : Fin n}

def micro : {s t : Fin n} → Path R G s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons e Q => e.micro + Q.micro

def searchWeight (A : ℕ) : {s t : Fin n} → Path R G s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons e Q => e.searchWeight A + Q.searchWeight A

def vertices : {s t : Fin n} → Path R G s t → List (Fin n)
  | _, _, .nil v => [v]
  | s, _, .cons _ Q => s :: Q.vertices

def support : {s t : Fin n} → Path R G s t → List (Fin n)
  | _, _, .nil v => [v]
  | _, _, .cons e Q => e.vertices ++ Q.support

def expansion : {s t : Fin n} → Path R G s t → List (Fin n)
  | _, _, .nil v => [v]
  | _, _, .cons e Q => join e.vertices Q.expansion

def length : {s t : Fin n} → Path R G s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ Q => Q.length + 1

def Inside (Q : Path R G s t) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ Q.support, v ∈ S

def append : {s u t : Fin n} → Path R G s u → Path R G u t → Path R G s t
  | _, _, _, .nil _, Q => Q
  | _, _, _, .cons e P, Q => .cons e (P.append Q)

@[simp] theorem micro_append (P : Path R G s u) (Q : Path R G u t) :
    (P.append Q).micro = P.micro + Q.micro := by
  induction P with
  | nil => simp [append, micro]
  | cons e P ih => simp only [append, micro, ih, add_assoc]

@[simp] theorem searchWeight_append (A : ℕ) (P : Path R G s u) (Q : Path R G u t) :
    (P.append Q).searchWeight A = P.searchWeight A + Q.searchWeight A := by
  induction P with
  | nil => simp [append, searchWeight]
  | cons e P ih => simp only [append, searchWeight, ih, add_assoc]

@[simp] theorem length_append (P : Path R G s u) (Q : Path R G u t) :
    (P.append Q).length = P.length + Q.length := by
  induction P with
  | nil => simp [append, length]
  | cons e P ih => simp [append, length, ih]; omega

theorem endpoints (Q : Path R G s t) : Graph.Endpoints Q.vertices s t := by
  induction Q with
  | nil v => simp [vertices, Graph.Endpoints]
  | cons e Q ih =>
      refine ⟨rfl, ?_⟩
      have hn := Graph.endpoints_nonempty ih
      cases hQ : Q.vertices with
      | nil => exact False.elim (hn hQ)
      | cons v vs => simpa [vertices, hQ, Graph.Endpoints] using ih.2

theorem expansion_endpoints (Q : Path R G s t) : Graph.Endpoints Q.expansion s t := by
  induction Q with
  | nil v => simp [expansion, Graph.Endpoints]
  | cons e Q ih => exact join_endpoints e.endpoints ih

theorem expansion_cost (Q : Path R G s t) :
    (R.base G).pathCost Q.expansion = Q.micro := by
  induction Q with
  | nil v => simp [expansion, micro]
  | cons e Q ih =>
      rw [expansion, join_cost (R.base G) e.endpoints Q.expansion_endpoints,
        e.cost, ih]
      rfl

theorem expansion_support (Q : Path R G s t) {v : Fin n}
    (hv : v ∈ Q.expansion) : v ∈ Q.support := by
  induction Q with
  | nil w => exact hv
  | cons e Q ih =>
      rcases List.mem_append.mp hv with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (ih (List.mem_of_mem_tail h))

theorem endpoints_support (Q : Path R G s t) : s ∈ Q.support ∧ t ∈ Q.support :=
  ⟨Q.expansion_support (endpoints_mem Q.expansion_endpoints).1,
    Q.expansion_support (endpoints_mem Q.expansion_endpoints).2⟩

theorem inside_cons {v : Fin n} (e : Edge R G s v) (Q : Path R G v t)
    {S : Finset (Fin n)} :
    (Path.cons e Q).Inside S ↔ e.Inside S ∧ Q.Inside S := by
  simp only [Inside, support, Edge.Inside, List.mem_append]
  exact ⟨fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩,
    fun h v hv => hv.elim (h.1 v) (h.2 v)⟩

theorem inside_append (P : Path R G s u) (Q : Path R G u t)
    {S : Finset (Fin n)} :
    (P.append Q).Inside S ↔ P.Inside S ∧ Q.Inside S := by
  induction P with
  | nil v =>
      have hv : Q.Inside S → v ∈ S := fun h => h _ Q.endpoints_support.1
      simp only [append, Inside, support, List.mem_singleton, forall_eq]
      exact ⟨fun h => ⟨hv h, h⟩, fun h => h.2⟩
  | cons e P ih => simp only [append, inside_cons, ih, and_assoc]

theorem vertices_cost (Q : Path R G s t) (A : ℕ) {S : Finset (Fin n)}
    (hS : Q.Inside S) :
    (rounded A (R.restricted G S)).pathCost Q.vertices = Q.searchWeight A := by
  induction Q with
  | nil v => simp [vertices, searchWeight]
  | @cons u v t e Q ih =>
      obtain ⟨heS, hQS⟩ := (inside_cons e Q).mp hS
      obtain ⟨w, ws, hvs⟩ := List.exists_cons_of_ne_nil
        (Graph.endpoints_nonempty Q.endpoints)
      have hw : w = v := by simpa [hvs, Graph.Endpoints] using Q.endpoints.1
      subst w
      change (rounded A (R.restricted G S)).pathCost (u :: Q.vertices) = _
      rw [hvs, Graph.pathCost_cons_cons, e.search_edge A heS]
      have hi := ih hQS
      rw [hvs] at hi
      rw [hi]
      rfl

theorem forward (Q : Path R G s t) (A : ℕ) {S : Finset (Fin n)}
    (hS : Q.Inside S) :
    Within (rounded A (R.restricted G S)) s t (Q.searchWeight A : ℝ) :=
  bounded_mono_distance ((rounded A (R.restricted G S)).dist_le_pathCost Q.endpoints)
    ⟨_, Q.vertices_cost A hS, le_rfl⟩

theorem support_to_end (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    {S : Finset (Fin n)} (hS : Q.Inside S) {z : Fin n} (hz : z ∈ Q.support) :
    Within (rounded A (R.restricted G S)) z t (Q.searchWeight A : ℝ) := by
  induction Q with
  | nil v =>
      have hv : z = v := by simpa [support] using hz
      subst z
      exact within_self _ _ (by simp [searchWeight])
  | cons e Q ih =>
      obtain ⟨heS, hQS⟩ := (inside_cons e Q).mp hS
      rcases List.mem_append.mp hz with he | hQ
      · have ht := within_trans (e.subpath_bounds A hA heS he).2 (Q.forward A hQS)
        simpa only [searchWeight, Nat.cast_add] using ht
      · exact within_mono (ih hQS hQ) (by
          simp only [searchWeight, Nat.cast_add]
          exact le_add_of_nonneg_left (Nat.cast_nonneg _))

theorem start_to_support (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    {S : Finset (Fin n)} (hS : Q.Inside S) {z : Fin n} (hz : z ∈ Q.support) :
    Within (rounded A (R.restricted G S)) s z (Q.searchWeight A : ℝ) := by
  induction Q with
  | nil v =>
      have hv : z = v := by simpa [support] using hz
      subst z
      exact within_self _ _ (by simp [searchWeight])
  | cons e Q ih =>
      obtain ⟨heS, hQS⟩ := (inside_cons e Q).mp hS
      rcases List.mem_append.mp hz with he | hQ
      · exact within_mono (e.subpath_bounds A hA heS he).1 (by
          simp only [searchWeight, Nat.cast_add]
          exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have ht := within_trans (within_edge _ (e.search_edge A heS).le) (ih hQS hQ)
        simpa only [searchWeight, Nat.cast_add] using ht

theorem shortPath (Q : Path R G s t) (A : ℕ) {S : Finset (Fin n)}
    (hS : Q.Inside S) {D : ℝ} (hD : (Q.searchWeight A : ℝ) ≤ D) :
    Nonempty (ShortPath (rounded A (R.restricted G S)) D) :=
  ⟨⟨Q.vertices, Graph.endpoints_nonempty Q.endpoints, Q.searchWeight A,
    Q.vertices_cost A hS, hD⟩⟩

def vertex : {s t : Fin n} → Path R G s t → ℕ → Fin n
  | _, _, .nil v, _ => v
  | s, _, .cons _ _, 0 => s
  | _, _, .cons _ Q, i + 1 => Q.vertex i

def take : {s t : Fin n} → (Q : Path R G s t) → (i : ℕ) → Path R G s (Q.vertex i)
  | _, _, .nil v, _ => .nil v
  | s, _, .cons _ _, 0 => .nil s
  | _, _, .cons e Q, i + 1 => .cons e (Q.take i)

def suffix : {s t : Fin n} → (Q : Path R G s t) → (i : ℕ) → Path R G (Q.vertex i) t
  | _, _, .nil v, _ => .nil v
  | _, _, .cons e Q, 0 => .cons e Q
  | _, _, .cons _ Q, i + 1 => Q.suffix i

@[simp] theorem vertex_zero (Q : Path R G s t) : Q.vertex 0 = s := by cases Q <;> rfl

@[simp] theorem vertex_length (Q : Path R G s t) : Q.vertex Q.length = t := by
  induction Q with
  | nil => rfl
  | cons e Q ih => exact ih

theorem rejoin (Q : Path R G s t) (i : ℕ) : (Q.take i).append (Q.suffix i) = Q := by
  induction Q generalizing i with
  | nil => rfl
  | cons e Q ih =>
      cases i with
      | zero => rfl
      | succ i => exact congrArg (Path.cons e) (ih i)

theorem prefix_inside (Q : Path R G s t) {S : Finset (Fin n)}
    (hS : Q.Inside S) (i : ℕ) : (Q.take i).Inside S :=
  ((Q.take i).inside_append (Q.suffix i)).mp (by rwa [Q.rejoin i]) |>.1

theorem suffix_inside (Q : Path R G s t) {S : Finset (Fin n)}
    (hS : Q.Inside S) (i : ℕ) : (Q.suffix i).Inside S :=
  ((Q.take i).inside_append (Q.suffix i)).mp (by rwa [Q.rejoin i]) |>.2

theorem weight_split (Q : Path R G s t) (A i : ℕ) :
    (Q.take i).searchWeight A + (Q.suffix i).searchWeight A = Q.searchWeight A := by
  rw [← searchWeight_append, Q.rejoin]

theorem micro_split (Q : Path R G s t) (i : ℕ) :
    (Q.take i).micro + (Q.suffix i).micro = Q.micro := by
  rw [← micro_append, Q.rejoin]

theorem vertex_suffix (Q : Path R G s t) (i j : ℕ) :
    (Q.suffix i).vertex j = Q.vertex (i + j) := by
  induction Q generalizing i j with
  | nil => rfl
  | cons e Q ih =>
      cases i with
      | zero => rw [Nat.zero_add]; rfl
      | succ i => simpa only [suffix, Nat.succ_add, vertex] using ih i j

theorem vertex_mem (Q : Path R G s t) (i : ℕ) : Q.vertex i ∈ Q.vertices := by
  induction Q generalizing i with
  | nil => simp [vertex, vertices]
  | cons e Q ih =>
      cases i with
      | zero => simp [vertex, vertices]
      | succ i => exact List.mem_cons_of_mem _ (ih i)

theorem vertex_append_length (P : Path R G s u) (Q : Path R G u t) :
    (P.append Q).vertex P.length = u := by
  induction P with
  | nil => exact Q.vertex_zero
  | cons e P ih => exact ih Q

theorem mem_vertices_append_right (P : Path R G s u) (Q : Path R G u t)
    {z : Fin n} (hz : z ∈ Q.vertices) : z ∈ (P.append Q).vertices := by
  induction P with
  | nil => exact hz
  | cons e P ih => exact List.mem_cons_of_mem _ (ih Q hz)

theorem mem_vertices_append_left (P : Path R G s u) (Q : Path R G u t)
    {z : Fin n} (hz : z ∈ P.vertices) : z ∈ (P.append Q).vertices := by
  induction P with
  | nil v =>
      have he : z = v := by simpa [vertices] using hz
      subst z
      exact (endpoints_mem Q.endpoints).1
  | cons e P ih =>
      rcases List.mem_cons.mp hz with he | he
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ (ih Q he)

theorem vertex_support (Q : Path R G s t) (i : ℕ) : Q.vertex i ∈ Q.support := by
  have h := (Q.take i).endpoints_support.2
  let S := Q.support.toFinset
  have hS : Q.Inside S := by intro v hv; exact List.mem_toFinset.mpr hv
  exact List.mem_toFinset.mp (Q.prefix_inside hS i _ h)

theorem length_vertices (Q : Path R G s t) : Q.vertices.length = Q.length + 1 := by
  induction Q with
  | nil => rfl
  | cons e Q ih => simp only [vertices, List.length_cons, length, ih]

theorem length_suffix (Q : Path R G s t) (i : ℕ) :
    (Q.suffix i).length = Q.length - i := by
  induction Q generalizing i with
  | nil => simp [suffix, length]
  | cons e Q ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (Q.suffix i).length = Q.length + 1 - (i + 1)
          rw [Nat.add_sub_add_right]
          exact ih i

abbrev PackedEdge (R : Representation n) (G : Graph (Fin n)) :=
  Σ u : Fin n, Σ v : Fin n, Edge R G u v

def edges : {s t : Fin n} → Path R G s t → List (PackedEdge R G)
  | _, _, .nil _ => []
  | _, _, .cons e Q => ⟨_, _, e⟩ :: Q.edges

theorem sum_edge_weights (Q : Path R G s t) (A : ℕ) :
    (Q.edges.map fun e => e.2.2.searchWeight A).sum = Q.searchWeight A := by
  induction Q with
  | nil => rfl
  | cons e Q ih => simp only [edges, List.map_cons, List.sum_cons, searchWeight, ih]

theorem edge_decompose (Q : Path R G s t) {e : PackedEdge R G} (he : e ∈ Q.edges) :
    ∃ (P : Path R G s e.1) (T : Path R G e.2.1 t),
      Q = P.append (.cons e.2.2 T) := by
  induction Q with
  | nil => simp [edges] at he
  | cons f Q ih =>
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact ⟨.nil _, Q, rfl⟩
      · obtain ⟨P, T, h⟩ := ih he
        exact ⟨.cons f P, T, congrArg (Path.cons f) h⟩

end Path

end

end StreamingSSSP.Late

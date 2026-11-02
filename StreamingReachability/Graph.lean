module

public import Mathlib

@[expose] public section

namespace StreamingReachability

open scoped Classical

abbrev Distance := WithTop ℕ

abbrev Graph (V : Type*) := V → V → Distance

namespace Graph

variable {V : Type*}

def pathCost (G : Graph V) : List V → Distance
  | [] => 0
  | [_] => 0
  | u :: v :: xs => G u v + pathCost G (v :: xs)

@[simp] theorem pathCost_nil (G : Graph V) : G.pathCost [] = 0 := rfl

@[simp] theorem pathCost_singleton (G : Graph V) (u : V) :
    G.pathCost [u] = 0 := rfl

@[simp] theorem pathCost_cons_cons (G : Graph V) (u v : V) (xs : List V) :
    G.pathCost (u :: v :: xs) = G u v + G.pathCost (v :: xs) := rfl

def Endpoints (xs : List V) (s t : V) : Prop :=
  xs.head? = some s ∧ xs.getLast? = some t

@[simp] theorem endpoints_singleton (s t u : V) :
    Endpoints [u] s t ↔ u = s ∧ u = t := by
  simp [Endpoints]

theorem endpoints_nonempty {xs : List V} {s t : V} (h : Endpoints xs s t) :
    xs ≠ [] := by
  intro he
  simp [Endpoints, he] at h

theorem pathCost_tail_le (G : Graph V) (u : V) (xs : List V) :
    G.pathCost xs ≤ G.pathCost (u :: xs) := by
  cases xs with
  | nil => simp
  | cons v xs =>
      simp only [pathCost_cons_cons]
      exact le_add_of_nonneg_left (show 0 ≤ G u v from bot_le)

theorem pathCost_suffix_le (G : Graph V) (xs ys : List V) :
    G.pathCost ys ≤ G.pathCost (xs ++ ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      exact ih.trans (G.pathCost_tail_le x (xs ++ ys))

theorem pathCost_mono {G F : Graph V} (h : ∀ u v, G u v ≤ F u v)
    (xs : List V) : G.pathCost xs ≤ F.pathCost xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y xs => exact add_le_add (h x y) ih

theorem exists_simple_path (G : Graph V) (s : V) (xs : List V) :
    ∃ ys : List V, ys.Nodup ∧ ys.head? = some s ∧
      ys.getLast? = (s :: xs).getLast? ∧ ys.Sublist (s :: xs) ∧
      G.pathCost ys ≤ G.pathCost (s :: xs) := by
  classical
  induction xs generalizing s with
  | nil =>
      exact ⟨[s], by simp, rfl, rfl, List.Sublist.refl _, le_rfl⟩
  | cons x xs ih =>
      obtain ⟨ys, hn, hh, ht, hsub, hc⟩ := ih x
      by_cases hs : s ∈ ys
      · obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hs
        have hsuf : (s :: post).Sublist ys := by
          rw [hsplit]
          exact List.sublist_append_right pre (s :: post)
        refine ⟨s :: post, hn.sublist hsuf, rfl, ?_,
          hsuf.trans (hsub.trans (List.sublist_cons_self _ _)), ?_⟩
        · rw [hsplit] at ht
          simpa only [List.getLast?_append_cons, List.getLast?_cons_cons] using ht
        · have hsufcost : G.pathCost (s :: post) ≤ G.pathCost ys := by
            rw [hsplit]
            exact G.pathCost_suffix_le pre (s :: post)
          exact hsufcost.trans (hc.trans (G.pathCost_tail_le s (x :: xs)))
      · have hyne : ys ≠ [] := by
          intro he
          simp [he] at hh
        obtain ⟨y, zs, rfl⟩ := List.exists_cons_of_ne_nil hyne
        have hy : y = x := by simpa using hh
        subst y
        refine ⟨s :: x :: zs, List.nodup_cons.mpr ⟨hs, hn⟩, rfl, ?_,
          List.Sublist.cons_cons s hsub, ?_⟩
        · simpa using ht
        · exact add_le_add le_rfl hc

noncomputable def routes [Fintype V] : ℕ → Finset (List V)
  | 0 => {[]}
  | b + 1 => insert [] (Finset.univ.biUnion fun v => (routes b).image (List.cons v))

theorem mem_routes [Fintype V] (b : ℕ) (xs : List V) :
    xs ∈ routes (V := V) b ↔ xs.length ≤ b := by
  classical
  induction b generalizing xs with
  | zero => simp [routes]
  | succ b ih =>
      cases xs with
      | nil => simp [routes]
      | cons x xs => simp [routes, ih]

theorem simple_length_le [Fintype V] {xs : List V} (h : xs.Nodup) :
    xs.length ≤ Fintype.card V := by
  classical
  rw [← List.toFinset_card_of_nodup h]
  exact Finset.card_le_univ _

noncomputable def dist [Fintype V] (G : Graph V) (s t : V) : Distance :=
  (routes (V := V) (Fintype.card V)).inf fun xs =>
    if Endpoints xs s t then G.pathCost xs else ⊤

theorem dist_le_pathCost [Fintype V] (G : Graph V) {s t : V} {xs : List V}
    (h : Endpoints xs s t) : G.dist s t ≤ G.pathCost xs := by
  classical
  have hne := endpoints_nonempty h
  obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = s := by simpa [Endpoints] using h.1
  subst x
  obtain ⟨ys, hn, hh, ht, _, hc⟩ := G.exists_simple_path s tail
  have hends : Endpoints ys s t := ⟨hh, ht.trans h.2⟩
  have hmem : ys ∈ routes (V := V) (Fintype.card V) :=
    (mem_routes _ _).mpr (simple_length_le hn)
  exact (Finset.inf_le_of_le hmem (by simp [hends])).trans hc

@[simp] theorem dist_self [Fintype V] (G : Graph V) (s : V) : G.dist s s = 0 := by
  exact le_antisymm (G.dist_le_pathCost (xs := [s]) (by simp)) bot_le

theorem pathCost_append_of_getLast (G : Graph V) {xs : List V} {u : V}
    (h : xs.getLast? = some u) (ys : List V) :
    G.pathCost (xs ++ ys) = G.pathCost xs + G.pathCost (u :: ys) := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx : x = u := by simpa using h
          subst x
          simp
      | cons y xs =>
          have ht : (y :: xs).getLast? = some u := by simpa using h
          change G x y + G.pathCost ((y :: xs) ++ ys) =
            (G x y + G.pathCost (y :: xs)) + G.pathCost (u :: ys)
          rw [ih ht, add_assoc]

theorem endpoints_append {xs ys : List V} {s u t : V}
    (hx : Endpoints xs s u) (hy : Endpoints (u :: ys) u t) :
    Endpoints (xs ++ ys) s t := by
  refine ⟨(List.head?_append_of_ne_nil xs (endpoints_nonempty hx)).trans hx.1, ?_⟩
  cases ys with
  | nil =>
      have hut : u = t := by simpa [Endpoints] using hy.2
      simpa [hut] using hx.2
  | cons y ys =>
      simpa only [List.getLast?_append_cons, List.getLast?_cons_cons] using hy.2

theorem pathCost_prefix_le (G : Graph V) (xs ys : List V) :
    G.pathCost xs ≤ G.pathCost (xs ++ ys) := by
  cases xs with
  | nil => exact bot_le
  | cons x xs =>
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp
        (List.getLast?_eq_none_iff.not.mpr (List.cons_ne_nil x xs))
      rw [G.pathCost_append_of_getLast hu]
      exact le_add_of_nonneg_right bot_le

theorem pathCost_split (G : Graph V) (xs ys : List V) (u : V) :
    G.pathCost (xs ++ u :: ys) =
      G.pathCost (xs ++ [u]) + G.pathCost (u :: ys) := by
  simpa only [List.append_assoc, List.singleton_append] using
    G.pathCost_append_of_getLast (xs := xs ++ [u]) (by simp) ys

theorem pathCost_segment_le (G : Graph V) (pre middle post : List V) :
    G.pathCost middle ≤ G.pathCost (pre ++ middle ++ post) := by
  exact (G.pathCost_prefix_le middle post).trans
    (by simpa only [List.append_assoc] using G.pathCost_suffix_le pre (middle ++ post))

theorem le_dist_iff [Fintype V] (G : Graph V) (s t : V) (d : Distance) :
    d ≤ G.dist s t ↔ ∀ xs, Endpoints xs s t → d ≤ G.pathCost xs := by
  classical
  refine ⟨fun h xs hx => h.trans (G.dist_le_pathCost hx), ?_⟩
  intro h
  exact Finset.le_inf fun xs _ => by
    split_ifs with he
    · exact h xs he
    · exact le_top

theorem dist_mono [Fintype V] {G F : Graph V} (h : ∀ u v, G u v ≤ F u v)
    (s t : V) : G.dist s t ≤ F.dist s t := by
  apply (F.le_dist_iff s t _).mpr
  intro xs hx
  exact (G.dist_le_pathCost hx).trans (pathCost_mono h xs)

theorem exists_dist_path [Fintype V] (G : Graph V) {s t : V}
    (h : G.dist s t ≠ ⊤) :
    ∃ xs : List V, xs.Nodup ∧ Endpoints xs s t ∧
      xs.length ≤ Fintype.card V ∧ G.pathCost xs = G.dist s t := by
  classical
  have hr : (routes (V := V) (Fintype.card V)).Nonempty :=
    ⟨[], (mem_routes _ _).mpr (by simp)⟩
  obtain ⟨xs, _, hx⟩ := Finset.exists_mem_eq_inf
    (routes (V := V) (Fintype.card V)) hr
    (fun xs => if Endpoints xs s t then G.pathCost xs else ⊤)
  have he : Endpoints xs s t := by
    by_contra hn
    exact h (by simpa [dist, hn] using hx)
  have hc : G.dist s t = G.pathCost xs := by simpa [dist, he] using hx
  obtain ⟨_, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty he)
  obtain ⟨ys, hn, hh, ht, _, hcost⟩ := G.exists_simple_path _ tail
  have hends : Endpoints ys s t := ⟨hh.trans he.1, ht.trans he.2⟩
  exact ⟨ys, hn, hends, simple_length_le hn,
    le_antisymm (hcost.trans hc.ge) (G.dist_le_pathCost hends)⟩

theorem dist_le_edge [Fintype V] (G : Graph V) (s t : V) :
    G.dist s t ≤ G s t := by
  simpa using G.dist_le_pathCost (xs := [s, t]) (by simp [Endpoints])

theorem dist_triangle [Fintype V] (G : Graph V) (s u t : V) :
    G.dist s t ≤ G.dist s u + G.dist u t := by
  by_cases hsu : G.dist s u = ⊤
  · simp [hsu]
  by_cases hut : G.dist u t = ⊤
  · simp [hut]
  obtain ⟨xs, _, hx, _, hcx⟩ := G.exists_dist_path hsu
  obtain ⟨ys, _, hy, _, hcy⟩ := G.exists_dist_path hut
  obtain ⟨v, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty hy)
  have hv : v = u := by simpa [Endpoints] using hy.1
  subst v
  calc
    G.dist s t ≤ G.pathCost (xs ++ tail) := G.dist_le_pathCost (endpoints_append hx hy)
    _ = G.pathCost xs + G.pathCost (u :: tail) := G.pathCost_append_of_getLast hx.2 tail
    _ = G.dist s u + G.dist u t := by rw [hcx, hcy]

theorem dist_le_dist_add_edge [Fintype V] (G : Graph V) (s u t : V) :
    G.dist s t ≤ G.dist s u + G u t :=
  (G.dist_triangle s u t).trans (add_le_add le_rfl (G.dist_le_edge u t))

theorem dist_le_edge_add_dist [Fintype V] (G : Graph V) (s u t : V) :
    G.dist s t ≤ G s u + G.dist u t :=
  (G.dist_triangle s u t).trans (add_le_add (G.dist_le_edge s u) le_rfl)

def Reachable (G : Graph V) (s t : V) : Prop :=
  ∃ xs : List V, Endpoints xs s t ∧ G.pathCost xs ≠ ⊤

theorem dist_ne_top_iff [Fintype V] (G : Graph V) (s t : V) :
    G.dist s t ≠ ⊤ ↔ G.Reachable s t := by
  constructor
  · intro h
    obtain ⟨xs, _, he, _, hc⟩ := G.exists_dist_path h
    exact ⟨xs, he, by simpa [hc] using h⟩
  · rintro ⟨xs, he, hc⟩ htop
    exact hc (top_le_iff.mp (htop ▸ G.dist_le_pathCost he))

theorem pathCost_ne_top_iff (G : Graph V) (xs : List V) :
    G.pathCost xs ≠ ⊤ ↔ xs.IsChain (fun u v => G u v ≠ ⊤) := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
      cases xs with
      | nil => simp
      | cons v xs => simp only [pathCost_cons_cons, WithTop.add_ne_top,
          List.isChain_cons_cons, ih]

theorem reachable_iff_reflTransGen (G : Graph V) (s t : V) :
    G.Reachable s t ↔ Relation.ReflTransGen (fun u v => G u v ≠ ⊤) s t := by
  constructor
  · rintro ⟨xs, he, hc⟩
    obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty he)
    have hx : x = s := by simpa [Endpoints] using he.1
    subst x
    exact List.relationReflTransGen_of_exists_isChain_cons tail
      ((G.pathCost_ne_top_iff _).mp hc)
      ((List.getLast_eq_iff_getLast?_eq_some _).mpr he.2)
  · intro h
    obtain ⟨tail, hc, ht⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨s :: tail, ⟨rfl, (List.getLast_eq_iff_getLast?_eq_some _).mp ht⟩,
      (G.pathCost_ne_top_iff _).mpr hc⟩

theorem dist_eq_top_iff [Fintype V] (G : Graph V) (s t : V) :
    G.dist s t = ⊤ ↔ ¬G.Reachable s t := by
  simpa only [not_not] using not_congr (G.dist_ne_top_iff s t)

theorem endpoints_split_at_mem {xs : List V} {s t u : V}
    (he : Endpoints xs s t) (hu : u ∈ xs) :
    ∃ pre post, xs = pre ++ u :: post ∧
      Endpoints (pre ++ [u]) s u ∧ Endpoints (u :: post) u t := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hu
  refine ⟨pre, post, rfl, ⟨?_, by simp⟩, ⟨rfl, ?_⟩⟩
  · cases pre with
    | nil => simpa [Endpoints] using he.1
    | cons x pre => simpa [Endpoints] using he.1
  · simpa only [List.getLast?_append_cons] using he.2

theorem shortest_path_prefix [Fintype V] (G : Graph V)
    {pre post : List V} {s u t : V}
    (hp : Endpoints pre s u) (hs : Endpoints (u :: post) u t)
    (hc : G.pathCost (pre ++ post) = G.dist s t)
    (hf : G.pathCost (pre ++ post) ≠ ⊤) :
    G.pathCost pre = G.dist s u := by
  refine le_antisymm ?_ (G.dist_le_pathCost hp)
  have hsum : G.pathCost pre + G.pathCost (u :: post) = G.dist s t := by
    rwa [← G.pathCost_append_of_getLast hp.2 post]
  have hfinite : G.pathCost (u :: post) ≠ ⊤ :=
    (WithTop.add_ne_top.mp (by simpa [← hsum, hc] using hf)).2
  apply (WithTop.add_le_add_iff_right hfinite).mp
  rw [hsum]
  exact (G.dist_triangle s u t).trans
    (add_le_add le_rfl (G.dist_le_pathCost hs))

theorem shortest_path_suffix [Fintype V] (G : Graph V)
    {pre post : List V} {s u t : V}
    (hp : Endpoints pre s u) (hs : Endpoints (u :: post) u t)
    (hc : G.pathCost (pre ++ post) = G.dist s t)
    (hf : G.pathCost (pre ++ post) ≠ ⊤) :
    G.pathCost (u :: post) = G.dist u t := by
  refine le_antisymm ?_ (G.dist_le_pathCost hs)
  have hsum : G.pathCost pre + G.pathCost (u :: post) = G.dist s t := by
    rwa [← G.pathCost_append_of_getLast hp.2 post]
  have hfinite : G.pathCost pre ≠ ⊤ :=
    (WithTop.add_ne_top.mp (by simpa [← hsum, hc] using hf)).1
  apply (WithTop.add_le_add_iff_left hfinite).mp
  rw [hsum]
  exact (G.dist_triangle s u t).trans
    (add_le_add (G.dist_le_pathCost hp) le_rfl)

theorem exists_dist_predecessor [Fintype V] (G : Graph V) {s v : V}
    (hsv : s ≠ v) (hf : G.dist s v ≠ ⊤) :
    ∃ u, u ≠ v ∧ G.dist s u + G u v = G.dist s v := by
  obtain ⟨xs, hn, he, _, hc⟩ := G.exists_dist_path hf
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp he.2
  have hpne : pre ≠ [] := by
    intro hp
    have hvs : v = s := by simpa [Endpoints, hp] using he.1
    exact hsv hvs.symm
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp
    (List.getLast?_eq_none_iff.not.mpr hpne)
  have hvnot : v ∉ pre := by simpa using hn.disjoint
  have huv : u ≠ v := by
    intro huv
    exact hvnot (huv ▸ List.mem_of_getLast? hu)
  have hp : Endpoints pre s u :=
    ⟨(List.head?_append_of_ne_nil pre hpne).symm.trans he.1, hu⟩
  have hprefix := G.shortest_path_prefix hp (by simp [Endpoints]) hc
    (by simpa only [hc] using hf)
  refine ⟨u, huv, ?_⟩
  simpa only [pathCost_cons_cons, pathCost_singleton, add_zero, hprefix] using
    (G.pathCost_append_of_getLast hu [v]).symm.trans hc

theorem exists_shortest_predecessor [Fintype V] (G : Graph V)
    (hp : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v) {s v : V}
    (hsv : s ≠ v) (hf : G.dist s v ≠ ⊤) :
    ∃ u, u ≠ v ∧ G.dist s u + G u v = G.dist s v ∧
      G.dist s u < G.dist s v := by
  obtain ⟨u, huv, he⟩ := G.exists_dist_predecessor hsv hf
  have hsumfinite : G.dist s u + G u v ≠ ⊤ := by rwa [he]
  have huf : G.dist s u ≠ ⊤ := (WithTop.add_ne_top.mp hsumfinite).1
  have hpos : (0 : Distance) < G u v :=
    lt_of_lt_of_le (by norm_num) (hp u v huv)
  refine ⟨u, huv, he, ?_⟩
  simpa only [add_zero, he] using (WithTop.add_lt_add_iff_left huf).mpr hpos

theorem exists_shortest_predecessor_of_pos [Fintype V] (G : Graph V)
    (hp : ∀ u v, (1 : Distance) ≤ G u v) {s v : V}
    (hsv : s ≠ v) (hf : G.dist s v ≠ ⊤) :
    ∃ u, u ≠ v ∧ G.dist s u + G u v = G.dist s v ∧
      G.dist s u < G.dist s v :=
  G.exists_shortest_predecessor (fun u v _ => hp u v) hsv hf

def reverse (G : Graph V) : Graph V := fun u v => G v u

@[simp] theorem reverse_reverse (G : Graph V) : G.reverse.reverse = G := rfl

theorem endpoints_reverse {xs : List V} {s t : V} (h : Endpoints xs s t) :
    Endpoints xs.reverse t s := by
  simpa only [Endpoints, List.head?_reverse, List.getLast?_reverse] using h.symm

@[simp] theorem pathCost_reverse (G : Graph V) (xs : List V) :
    G.reverse.pathCost xs.reverse = G.pathCost xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y xs =>
          rw [List.reverse_cons,
            G.reverse.pathCost_append_of_getLast (u := y) (by simp), ih]
          simp [reverse, add_comm]

@[simp] theorem dist_reverse [Fintype V] (G : Graph V) (s t : V) :
    G.reverse.dist t s = G.dist s t := by
  have aux (F : Graph V) (u v : V) : F.reverse.dist v u ≤ F.dist u v := by
    apply (F.le_dist_iff u v _).mpr
    intro xs hx
    simpa using F.reverse.dist_le_pathCost (endpoints_reverse hx)
  exact le_antisymm (aux G s t) (aux G.reverse t s)

def comap {U : Type*} (G : Graph V) (f : U → V) : Graph U :=
  fun u v => G (f u) (f v)

@[simp] theorem pathCost_map {U : Type*} (G : Graph V) (f : U → V) (xs : List U) :
    G.pathCost (xs.map f) = (G.comap f).pathCost xs := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
      cases xs with
      | nil => simp
      | cons v xs => simpa [comap] using congrArg (fun d => G (f u) (f v) + d) ih

theorem endpoints_map {U : Type*} (f : U → V) {xs : List U} {s t : U}
    (h : Endpoints xs s t) : Endpoints (xs.map f) (f s) (f t) := by
  simp [Endpoints, List.head?_map, List.getLast?_map, h.1, h.2]

theorem dist_comap_le [Fintype V] {U : Type*} [Fintype U]
    (G : Graph V) (f : U → V) (s t : U) :
    G.dist (f s) (f t) ≤ (G.comap f).dist s t := by
  apply ((G.comap f).le_dist_iff s t _).mpr
  intro xs hx
  simpa using G.dist_le_pathCost (endpoints_map f hx)

theorem dist_comap_equiv [Fintype V] {U : Type*} [Fintype U]
    (G : Graph V) (e : U ≃ V) (s t : U) :
    (G.comap e).dist s t = G.dist (e s) (e t) := by
  refine le_antisymm ?_ (G.dist_comap_le e s t)
  have hg : (G.comap e).comap e.symm = G := by
    funext u v
    simp [comap]
  simpa only [hg, Equiv.symm_apply_apply] using
    (G.comap e).dist_comap_le e.symm (e s) (e t)

def restrict (G : Graph V) (S : Set V) : Graph S := G.comap Subtype.val

theorem dist_restrict_le [Fintype V] (G : Graph V) (S : Set V) [Fintype S]
    (s t : S) : G.dist s.val t.val ≤ (G.restrict S).dist s t :=
  G.dist_comap_le Subtype.val s t

theorem dist_restrict_mono (G : Graph V) {S T : Set V} [Fintype S] [Fintype T]
    (h : S ⊆ T) (s t : S) :
    (G.restrict T).dist ⟨s.val, h s.property⟩ ⟨t.val, h t.property⟩ ≤
      (G.restrict S).dist s t := by
  exact (G.restrict T).dist_comap_le (fun v : S => ⟨v.val, h v.property⟩) s t

def union (G F : Graph V) : Graph V := fun u v => min (G u v) (F u v)

@[simp] theorem union_apply (G F : Graph V) (u v : V) :
    G.union F u v = min (G u v) (F u v) := rfl

theorem dist_union_le_left [Fintype V] (G F : Graph V) (s t : V) :
    (G.union F).dist s t ≤ G.dist s t :=
  dist_mono (fun _ _ => min_le_left _ _) s t

theorem dist_union_le_right [Fintype V] (G F : Graph V) (s t : V) :
    (G.union F).dist s t ≤ F.dist s t :=
  dist_mono (fun _ _ => min_le_right _ _) s t

theorem dist_union_le_min [Fintype V] (G F : Graph V) (s t : V) :
    (G.union F).dist s t ≤ min (G.dist s t) (F.dist s t) :=
  le_min (G.dist_union_le_left F s t) (G.dist_union_le_right F s t)

end Graph

end StreamingReachability

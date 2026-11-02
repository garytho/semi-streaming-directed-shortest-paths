module

public import StreamingSSSP.Graph.StoredEdges

@[expose] public section

namespace StreamingSSSP.Implicit

open scoped Classical
open StoredEdges

variable {V : Type*}

noncomputable def induced (G : Graph V) (S : Finset V) : Graph V :=
  fun u v => if u ∈ S ∧ v ∈ S then G u v else ⊤

theorem le_induced (G : Graph V) (S : Finset V) (u v : V) :
    G u v ≤ induced G S u v := by
  by_cases h : u ∈ S ∧ v ∈ S <;> simp [induced, h]

theorem induced_mono {G F : Graph V} {S T : Finset V}
    (hG : ∀ u v, G u v ≤ F u v) (hS : T ⊆ S) (u v : V) :
    induced G S u v ≤ induced F T u v := by
  by_cases hT : u ∈ T ∧ v ∈ T
  · have hS' : u ∈ S ∧ v ∈ S := ⟨hS hT.1, hS hT.2⟩
    simpa only [induced, ite_eq_left hT, ite_eq_left hS'] using hG u v
  · simp [induced, hT]

theorem induced_inter (G : Graph V) (S B : Finset V) :
    induced (induced G S) B = induced G (B ∩ S) := by
  funext u v
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S <;>
    by_cases huB : u ∈ B <;> by_cases hvB : v ∈ B <;>
    simp [induced, huS, hvS, huB, hvB]

@[simp] theorem induced_univ [Fintype V] (G : Graph V) :
    induced G Finset.univ = G := by
  funext u v
  simp [induced]

noncomputable def closure [Fintype V] (G : Graph V) (B : Finset V) : Graph V :=
  fun u v => if u ∈ B ∧ v ∈ B ∧ u ≠ v then (induced G B).dist u v else ⊤

theorem closure_mono [Fintype V] {G F : Graph V} {B C : Finset V}
    (hG : ∀ u v, G u v ≤ F u v) (hB : C ⊆ B) (u v : V) :
    closure G B u v ≤ closure F C u v := by
  by_cases hC : u ∈ C ∧ v ∈ C ∧ u ≠ v
  · have hB' : u ∈ B ∧ v ∈ B ∧ u ≠ v := ⟨hB hC.1, hB hC.2.1, hC.2.2⟩
    simp only [closure, ite_eq_left hC, ite_eq_left hB']
    exact Graph.dist_mono (induced_mono hG hB) u v
  · simp [closure, hC]

theorem closure_induced [Fintype V] (G : Graph V) (S B : Finset V)
    (hB : B ⊆ S) : closure (induced G S) B = closure G B := by
  funext u v
  unfold closure
  rw [induced_inter, Finset.inter_eq_left.mpr hB]

noncomputable def closures [Fintype V] (G : Graph V) : List (Finset V) → Graph V
  | [] => G
  | B :: Bs => Graph.union (closure G B) (closures G Bs)

theorem closures_le_base [Fintype V] (G : Graph V) (Bs : List (Finset V)) (u v : V) :
    closures G Bs u v ≤ G u v := by
  induction Bs with
  | nil => exact le_rfl
  | cons B Bs ih => exact (min_le_right _ _).trans ih

theorem closures_le_member [Fintype V] (G : Graph V) (Bs : List (Finset V))
    {B : Finset V} (hB : B ∈ Bs) (u v : V) :
    closures G Bs u v ≤ closure G B u v := by
  induction Bs with
  | nil => simp at hB
  | cons C Cs ih =>
      rcases List.mem_cons.mp hB with he | ht
      · subst C
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih ht)

theorem closure_origin [Fintype V] (G : Graph V) (Bs : List (Finset V)) (u v : V) :
    G u v = closures G Bs u v ∨
      ∃ B ∈ Bs, closure G B u v = closures G Bs u v := by
  induction Bs with
  | nil => exact Or.inl rfl
  | cons B Bs ih =>
      by_cases h : closure G B u v ≤ closures G Bs u v
      · exact Or.inr ⟨B, by simp, (min_eq_left h).symm⟩
      · have he : closures G (B :: Bs) u v = closures G Bs u v :=
          min_eq_right (le_of_not_ge h)
        rcases ih with hb | ⟨C, hC, hc⟩
        · exact Or.inl (hb.trans he.symm)
        · exact Or.inr ⟨C, by simp [hC], hc.trans he.symm⟩

theorem le_closures [Fintype V] (H G : Graph V) (Bs : List (Finset V))
    (hG : ∀ u v, H u v ≤ G u v)
    (hB : ∀ B ∈ Bs, ∀ u v, H u v ≤ closure G B u v) :
    ∀ u v, H u v ≤ closures G Bs u v := by
  induction Bs with
  | nil => exact hG
  | cons B Bs ih =>
      intro u v
      exact le_min (hB B (by simp) u v)
        (ih (fun C hC => hB C (by simp [hC])) u v)

theorem closures_mono [Fintype V] {G F : Graph V} (Bs Cs : List (Finset V))
    (hG : ∀ u v, G u v ≤ F u v) (hB : ∀ B ∈ Bs, B ∈ Cs) :
    ∀ u v, closures G Cs u v ≤ closures F Bs u v := by
  apply le_closures
  · intro u v
    exact (closures_le_base G Cs u v).trans (hG u v)
  · intro B hBm u v
    exact (closures_le_member G Cs (hB B hBm) u v).trans
      (closure_mono hG (Finset.Subset.refl B) u v)

def Noncontracting [Fintype V] (G F : Graph V) : Prop :=
  ∀ u v, G.dist u v ≤ F u v

theorem noncontracting_path [Fintype V] (G F : Graph V) (h : Noncontracting G F)
    {xs : List V} {s t : V} (hx : Graph.Endpoints xs s t) :
    G.dist s t ≤ F.pathCost xs := by
  induction xs generalizing s with
  | nil => simp [Graph.Endpoints] at hx
  | cons u xs ih =>
      have hu : u = s := by simpa [Graph.Endpoints] using hx.1
      subst u
      cases xs with
      | nil =>
          have ht : s = t := by simpa using hx.2
          subst t
          simp
      | cons v xs =>
          have hv : Graph.Endpoints (v :: xs) v t := ⟨rfl, by simpa using hx.2⟩
          exact (G.dist_triangle s v t).trans (add_le_add (h s v) (ih hv))

theorem dist_le_of_noncontracting [Fintype V] (G F : Graph V)
    (h : Noncontracting G F) (s t : V) : G.dist s t ≤ F.dist s t := by
  apply (Graph.le_dist_iff F s t _).mpr
  intro xs hx
  exact noncontracting_path G F h hx

theorem distance_unchanged [Fintype V] (G F : Graph V)
    (h : Noncontracting G F) (hcontains : ∀ u v, F u v ≤ G u v) :
    F.dist = G.dist := by
  funext s t
  exact le_antisymm (Graph.dist_mono hcontains s t) (dist_le_of_noncontracting G F h s t)

theorem closure_noncontracting [Fintype V] (G F : Graph V) (B : Finset V)
    (h : Noncontracting G F) : Noncontracting G (closure F B) := by
  intro u v
  by_cases hb : u ∈ B ∧ v ∈ B ∧ u ≠ v
  · simp only [closure, ite_eq_left hb]
    exact (dist_le_of_noncontracting G F h u v).trans
      (Graph.dist_mono (le_induced F B) u v)
  · simp [closure, hb]

theorem closures_noncontracting [Fintype V] (G F : Graph V) (Bs : List (Finset V))
    (h : Noncontracting G F) : Noncontracting G (closures F Bs) :=
  le_closures G.dist F Bs h (fun B _ => closure_noncontracting G F B h)

structure Representation (n : ℕ) where
  explicit : List (Edge n)
  blocks : List (Finset (Fin n))

namespace Representation

variable {n : ℕ}

def base (R : Representation n) (G : Graph (Fin n)) : Graph (Fin n) :=
  Graph.union G (graphOfEdges R.explicit)

noncomputable def graph (R : Representation n) (G : Graph (Fin n)) : Graph (Fin n) :=
  closures (R.base G) R.blocks

noncomputable def restricted (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) : Graph (Fin n) :=
  closures (induced (R.base G) S) (R.blocks.map (· ∩ S))

def size (R : Representation n) : ℕ :=
  R.explicit.length + (R.blocks.map Finset.card).sum

def cells (R : Representation n) : ℕ :=
  3 * R.explicit.length + (R.blocks.map fun B => 1 + B.card).sum

theorem graph_le_original (R : Representation n) (G : Graph (Fin n)) (u v : Fin n) :
    R.graph G u v ≤ G u v :=
  (closures_le_base (R.base G) R.blocks u v).trans (min_le_left _ _)

theorem noncontracting (R : Representation n) (G : Graph (Fin n))
    (h : Noncontracting G (graphOfEdges R.explicit)) :
    Noncontracting G (R.graph G) := by
  apply closures_noncontracting G (R.base G) R.blocks
  intro u v
  exact le_min (G.dist_le_edge u v) (h u v)

theorem distances (R : Representation n) (G : Graph (Fin n))
    (h : Noncontracting G (graphOfEdges R.explicit)) :
    (R.graph G).dist = G.dist :=
  distance_unchanged G (R.graph G) (R.noncontracting G h) (R.graph_le_original G)

@[simp] theorem restricted_univ (R : Representation n) (G : Graph (Fin n)) :
    R.restricted G Finset.univ = R.graph G := by
  simp [restricted, graph]

theorem restricted_mono (R : Representation n) (G : Graph (Fin n))
    {S T : Finset (Fin n)} (hST : T ⊆ S) :
    ∀ u v, R.restricted G S u v ≤ R.restricted G T u v := by
  have hbase : ∀ u v, induced (R.base G) S u v ≤ induced (R.base G) T u v :=
    induced_mono (fun _ _ => le_rfl) hST
  have haux : ∀ Bs : List (Finset (Fin n)), ∀ u v,
      closures (induced (R.base G) S) (Bs.map (· ∩ S)) u v ≤
        closures (induced (R.base G) T) (Bs.map (· ∩ T)) u v := by
    intro Bs
    induction Bs with
    | nil => exact hbase
    | cons B Bs ih =>
        intro u v
        apply min_le_min _ (ih u v)
        exact closure_mono hbase (by
          intro z hz
          exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hz).1, hST (Finset.mem_inter.mp hz).2⟩) u v
  exact haux R.blocks

theorem restricted_noncontracting (R : Representation n) (G : Graph (Fin n))
    (h : Noncontracting G (graphOfEdges R.explicit)) (S : Finset (Fin n)) :
    Noncontracting G (R.restricted G S) := by
  have hh : Noncontracting G (induced (R.base G) S) := by
    intro u v
    exact (le_min (G.dist_le_edge u v) (h u v)).trans (le_induced (R.base G) S u v)
  exact closures_noncontracting G _ _ hh

theorem cells_le (R : Representation n) (hB : ∀ B ∈ R.blocks, B.Nonempty) :
    R.cells ≤ 3 * R.size := by
  have hsum : (R.blocks.map fun B => 1 + B.card).sum ≤
      3 * (R.blocks.map Finset.card).sum := by
    have haux : ∀ Bs : List (Finset (Fin n)), (∀ B ∈ Bs, B.Nonempty) →
        (Bs.map fun B => 1 + B.card).sum ≤ 3 * (Bs.map Finset.card).sum := by
      intro Bs
      induction Bs with
      | nil => simp
      | cons B Bs ih =>
          intro hne
          have hpos : 0 < B.card := Finset.card_pos.mpr (hne B (by simp))
          have hi := ih (fun C hC => hne C (by simp [hC]))
          simp only [List.map_cons, List.sum_cons]
          omega
    exact haux R.blocks hB
  unfold cells size
  omega

end Representation

end StreamingSSSP.Implicit

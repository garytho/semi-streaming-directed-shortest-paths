module

public import StreamingSSSP.Hopset.LateChoiceLaw
public import StreamingSSSP.Hopset.FullSemantics

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem finRange_map_get {A : Type*} (f : Fin ns → A) (i : Fin ns) :
    ((List.finRange ns).map f).toArray.toVector.get ⟨i.val, by simpa using i.isLt⟩ = f i := by
  simp [← List.ofFn_eq_map, Vector.get_eq_getElem]

theorem late_children_length (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (choices : Fin ns → Reference.Choice n cfg) (he : cfg.earlyLevel ≤ r) (hr : r < cfg.maximumLevel) :
    (geometricChildren cfg r stored input sets choices).toArray.size = ns := by
  simp only [geometricChildren, show ¬ r < cfg.earlyLevel by omega, hr, ↓reduceIte,
    List.size_toArray, List.length_map, List.length_finRange]

theorem queue_get_option {A : Type*} (queue : List A) (i : Fin queue.toArray.size) :
    queue[i.val]? = some (queue.toArray.toVector.get i) := by
  have hi : i.val < queue.length := by simpa using i.isLt
  simp [Vector.get_eq_getElem, hi]

theorem late_children_option (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (choices : Fin ns → Reference.Choice n cfg) (he : cfg.earlyLevel ≤ r) (hr : r < cfg.maximumLevel) (i : Fin ns) :
    (geometricChildren cfg r stored input sets choices)[i.val]? =
      some (Reference.lateChild (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (sets.get i)
        (choices i).pivots
        (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (choices i).owners)) := by
  have hlist : geometricChildren cfg r stored input sets choices = (List.finRange ns).map (fun i =>
      Reference.lateChild (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (sets.get i)
        (choices i).pivots
        (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (choices i).owners)) := by
    simp only [geometricChildren, show ¬ r < cfg.earlyLevel by omega, hr, ↓reduceIte]
  rw [hlist]
  simp [← List.ofFn_eq_map]

theorem late_children_get (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (choices : Fin ns → Reference.Choice n cfg) (he : cfg.earlyLevel ≤ r) (hr : r < cfg.maximumLevel) (i : Fin ns) :
    (geometricChildren cfg r stored input sets choices).toArray.toVector.get
        ⟨i.val, by rw [late_children_length cfg r stored input sets choices he hr]; exact i.isLt⟩ =
      Reference.lateChild (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (sets.get i)
        (choices i).pivots
        (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (choices i).owners) := by
  let j : Fin (geometricChildren cfg r stored input sets choices).toArray.size :=
    ⟨i.val, by rw [late_children_length cfg r stored input sets choices he hr]; exact i.isLt⟩
  exact Option.some.inj ((queue_get_option _ j).symm.trans
    (late_children_option cfg r stored input sets choices he hr i))

def nodeStage (cfg : Config) (index : ℕ) (entry : GeometricEntry n cfg) :
    List (Fin n × (Fin cfg.groups × Fin cfg.shifts)) :=
  if h : index < entry.queue.toArray.size then
    lateStage cfg (entry.queue.toArray.toVector.get ⟨index, h⟩) (entry.frame.choices ⟨index, h⟩)
  else []

theorem nodeStage_at (cfg : Config) (r : ℕ) (queue : List (Finset (Fin n))) (i : Fin queue.toArray.size)
    (frame : Frame n cfg queue.toArray.size) :
    nodeStage cfg i.val ⟨r, queue, frame⟩ =
      lateStage cfg (queue.toArray.toVector.get i) (frame.choices i) := by
  simp only [nodeStage, i.isLt, ↓reduceDIte]

def chainStages (cfg : Config) (index : ℕ) (trace : List (GeometricEntry n cfg)) :=
  trace.map (nodeStage cfg index)

end

end StreamingSSSP.Hopset.Batched

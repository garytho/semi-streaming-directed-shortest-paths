module

public import StreamingReachability.Core.SparseLabels
public import StreamingReachability.StreamingModel

@[expose] public section

namespace StreamingReachability.Core.OrdinaryScan

open StoredEdges

variable {n k : ℕ}

structure Search (n k : ℕ) where
  id : Fin k
  vertices : Finset (Fin n)
  source : Fin n
  backward : Bool
  radius : ℕ

def orient (backward : Bool) (e : Edge n) : Edge n :=
  if backward then ⟨e.target, e.source, e.weight⟩ else e

def Accepts (A r : ℕ) (settled : SparseLabels.Labels (Fin k × Fin n))
    (j : Search n k) (raw : Edge n) : Prop :=
  let e := orient j.backward raw
  r ≤ j.radius ∧ e.source ∈ j.vertices ∧ e.target ∈ j.vertices ∧
    (j.id, e.target) ∉ SparseLabels.support settled ∧
    SparseLabels.get settled (j.id, e.source) + (ceilNat A e.weight : Distance) ≤ (r : Distance)
  deriving Decidable

def edgeTargets (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n)) (e : Edge n) :
    Finset (Fin k × Fin n) :=
  (searches.filterMap fun j =>
    if Accepts A r settled j e then some (j.id, (orient j.backward e).target) else none).toFinset

theorem mem_edgeTargets (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n)) (e : Edge n) (p : Fin k × Fin n) :
    p ∈ edgeTargets A r searches settled e ↔
      ∃ j ∈ searches, Accepts A r settled j e ∧ (j.id, (orient j.backward e).target) = p := by
  simp only [edgeTargets, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, he⟩
    by_cases ha : Accepts A r settled j e
    · exact ⟨j, hj, ha, by simpa only [ha, ↓reduceIte, Option.some.injEq] using he⟩
    · simp [ha] at he
  · rintro ⟨j, hj, ha, he⟩
    exact ⟨j, hj, by simpa only [ha, ↓reduceIte] using congrArg some he⟩

def step (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n))
    (candidates : Finset (Fin k × Fin n)) (e : Edge n) : Finset (Fin k × Fin n) :=
  candidates ∪ edgeTargets A r searches settled e

def scan (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n))
    (input : List (Edge n)) (initial : Finset (Fin k × Fin n)) :
    Streaming.Metered (Finset (Fin k × Fin n)) :=
  Streaming.readPass (step A r searches settled) (fun C => 3 * C.card) input initial

theorem fold_membership (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n)) (input : List (Edge n))
    (initial : Finset (Fin k × Fin n)) (p : Fin k × Fin n) :
    p ∈ input.foldl (step A r searches settled) initial ↔
      p ∈ initial ∨ ∃ e ∈ input, p ∈ edgeTargets A r searches settled e := by
  induction input generalizing initial with
  | nil => simp
  | cons e es ih =>
      rw [List.foldl_cons, ih]
      simp only [step, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
      tauto

theorem scan_membership (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n)) (input : List (Edge n))
    (initial : Finset (Fin k × Fin n)) (p : Fin k × Fin n) :
    p ∈ (scan A r searches settled input initial).state ↔ p ∈ initial ∨
      ∃ e ∈ input, ∃ j ∈ searches, Accepts A r settled j e ∧
        (j.id, (orient j.backward e).target) = p := by
  rw [scan, Streaming.readPass_state, fold_membership]
  simp only [mem_edgeTargets]

theorem scan_reads (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n)) (input : List (Edge n))
    (initial : Finset (Fin k × Fin n)) :
    (scan A r searches settled input initial).reads = input.length :=
  Streaming.readPass_reads _ _ _ _

theorem scan_memory (A r : ℕ) (searches : List (Search n k))
    (settled : SparseLabels.Labels (Fin k × Fin n)) (input : List (Edge n))
    (initial : Finset (Fin k × Fin n)) :
    (scan A r searches settled input initial).peakCells ≤
      3 * (scan A r searches settled input initial).state.card := by
  let final := (scan A r searches settled input initial).state
  have hinit : initial ⊆ final := by
    intro p hp
    exact (scan_membership A r searches settled input initial p).mpr (Or.inl hp)
  have hstep (xs : List (Edge n)) (C : Finset (Fin k × Fin n))
      (hc : C ⊆ final) (hx : ∀ e ∈ xs, edgeTargets A r searches settled e ⊆ final)
      (peak : ℕ) (hp : peak ≤ 3 * final.card) :
      (xs.foldl (Streaming.readEdge (step A r searches settled) (fun C => 3 * C.card))
        ⟨C, 0, peak⟩).peakCells ≤ 3 * final.card := by
    have hgen (ys : List (Edge n)) (m : Streaming.Metered (Finset (Fin k × Fin n)))
        (hm : m.state ⊆ final) (hp : m.peakCells ≤ 3 * final.card)
        (hy : ∀ e ∈ ys, edgeTargets A r searches settled e ⊆ final) :
        (ys.foldl (Streaming.readEdge (step A r searches settled) (fun C => 3 * C.card))
          m).peakCells ≤ 3 * final.card := by
      induction ys generalizing m with
      | nil => exact hp
      | cons e es ih =>
          have hn : step A r searches settled m.state e ⊆ final :=
            Finset.union_subset hm (hy e (by simp))
          apply ih (Streaming.readEdge _ _ m e) hn
          · exact max_le hp (Nat.mul_le_mul_left 3 (Finset.card_le_card hn))
          · intro f hf
            exact hy f (by simp [hf])
    exact hgen xs _ hc hp hx
  apply hstep input initial hinit
  · intro e he p hp
    exact (scan_membership A r searches settled input initial p).mpr
      (Or.inr ⟨e, he, by
        obtain ⟨j, hj, ha, heq⟩ := (mem_edgeTargets A r searches settled e p).mp hp
        exact ⟨j, hj, ha, heq⟩⟩)
  · exact Nat.mul_le_mul_left 3 (Finset.card_le_card hinit)

end StreamingReachability.Core.OrdinaryScan

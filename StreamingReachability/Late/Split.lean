module

public import StreamingReachability.Late.Boundary

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t u : Fin n}

namespace Path

theorem append_assoc {v : Fin n} (P : Path R G s u) (Q : Path R G u v)
    (T : Path R G v t) : (P.append Q).append T = P.append (Q.append T) := by
  induction P with
  | nil => rfl
  | cons e P ih => exact congrArg (Path.cons e) (ih Q)

@[simp] theorem edges_append (P : Path R G s u) (Q : Path R G u t) :
    (P.append Q).edges = P.edges ++ Q.edges := by
  induction P with
  | nil => rfl
  | cons e P ih => simp only [append, edges, ih, List.cons_append]

theorem edges_sublist_left (P : Path R G s u) (Q : Path R G u t) :
    P.edges.Sublist (P.append Q).edges := by
  rw [edges_append]
  exact List.sublist_append_left _ _

theorem edges_sublist_right (P : Path R G s u) (Q : Path R G u t) :
    Q.edges.Sublist (P.append Q).edges := by
  rw [edges_append]
  exact List.sublist_append_right _ _

theorem vertices_support (Q : Path R G s t) {z : Fin n} (hz : z ∈ Q.vertices) :
    z ∈ Q.support := by
  induction Q with
  | nil => exact hz
  | cons e Q ih =>
      rcases List.mem_cons.mp hz with he | he
      · subst z
        exact List.mem_append_left _ (endpoints_mem e.endpoints).1
      · exact List.mem_append_right _ (ih he)

theorem vertices_inside (Q : Path R G s t) {S : Finset (Fin n)} (hS : Q.Inside S) :
    ∀ z ∈ Q.vertices, z ∈ S := fun z hz => hS z (Q.vertices_support hz)

def badEdges (X : Finset (Fin n)) (Q : Path R G s t) : ℕ :=
  (Q.edges.map fun e => if e.2.2.Inside X then 0 else 1).sum

@[simp] theorem badEdges_nil (X : Finset (Fin n)) (v : Fin n) :
    badEdges X (.nil (R := R) (G := G) v) = 0 := rfl

@[simp] theorem badEdges_cons (X : Finset (Fin n)) {v : Fin n}
    (e : Edge R G s v) (Q : Path R G v t) :
    badEdges X (.cons e Q) = (if e.Inside X then 0 else 1) + badEdges X Q := rfl

@[simp] theorem badEdges_append (X : Finset (Fin n)) (P : Path R G s u)
    (Q : Path R G u t) : badEdges X (P.append Q) = badEdges X P + badEdges X Q := by
  induction P with
  | nil => simp [append]
  | cons e P ih => simp only [append, badEdges_cons, ih, add_assoc]

theorem badEdges_zero (Q : Path R G s t) {X : Finset (Fin n)} (hX : Q.Inside X) :
    badEdges X Q = 0 := by
  induction Q with
  | nil => rfl
  | cons e Q ih =>
      obtain ⟨heX, hQX⟩ := (inside_cons e Q).mp hX
      simp [badEdges_cons, heX, ih hQX]

theorem inside_mono (Q : Path R G s t) {S T : Finset (Fin n)}
    (hS : Q.Inside S) (hST : S ⊆ T) : Q.Inside T :=
  fun v hv => hST (hS v hv)

theorem searchWeight_take_le (Q : Path R G s t) (A i : ℕ) :
    (Q.take i).searchWeight A ≤ Q.searchWeight A := by have := Q.weight_split A i; omega

theorem searchWeight_suffix_le (Q : Path R G s t) (A i : ℕ) :
    (Q.suffix i).searchWeight A ≤ Q.searchWeight A := by have := Q.weight_split A i; omega

theorem badEdges_subpath (P : Path R G s u) (Q : Path R G u t) (X : Finset (Fin n)) :
    badEdges X Q ≤ badEdges X (P.append Q) := by simp

end Path

structure ChildPiece (R : Representation n) (G : Graph (Fin n))
    (X : Finset (Fin n)) (A : ℕ) (d : ℝ) where
  source : Fin n
  target : Fin n
  path : Path R G source target
  inside : path.Inside X
  short : (path.searchWeight A : ℝ) ≤ d

/-- Every constructor partitions actual consecutive edges. Empty endpoint
pieces are permitted; they require no represented edge. -/
inductive Partition (R : Representation n) (G : Graph (Fin n))
    (X : Finset (Fin n)) (A : ℕ) (d : ℝ) :
    {s t : Fin n} → Path R G s t → Type
  | one {s t : Fin n} (Q : Path R G s t) (inside : Q.Inside X)
      (short : (Q.searchWeight A : ℝ) ≤ d) : Partition R G X A d Q
  | cut {s a b t : Fin n} (P : Path R G s a) (e : Edge R G a b) (Q : Path R G b t)
      (inside : P.Inside X) (short : (P.searchWeight A : ℝ) ≤ d)
      (rest : Partition R G X A d Q) : Partition R G X A d (P.append (.cons e Q))

namespace Partition

variable {X : Finset (Fin n)} {A : ℕ} {d : ℝ}

def firstWeight : {s t : Fin n} → {Q : Path R G s t} → Partition R G X A d Q → ℕ
  | _, _, _, .one Q _ _ => Q.searchWeight A
  | _, _, _, .cut P _ _ _ _ _ => P.searchWeight A

def boundaries : {s t : Fin n} → {Q : Path R G s t} → Partition R G X A d Q → ℕ
  | _, _, _, .one _ _ _ => 0
  | _, _, _, .cut _ _ _ _ _ rest => rest.boundaries + 1

def type2 : {s t : Fin n} → {Q : Path R G s t} → Partition R G X A d Q → ℕ
  | _, _, _, .one _ _ _ => 0
  | _, _, _, .cut _ e _ _ _ rest => (if e.Inside X then 1 else 0) + rest.type2

def pieces : {s t : Fin n} → {Q : Path R G s t} →
    Partition R G X A d Q → List (ChildPiece R G X A d)
  | _, _, _, .one Q hX hd => [⟨_, _, Q, hX, hd⟩]
  | _, _, _, .cut P _ _ hX hd rest => ⟨_, _, P, hX, hd⟩ :: rest.pieces

def Greedy : {s t : Fin n} → {Q : Path R G s t} → Partition R G X A d Q → Prop
  | _, _, _, .one _ _ _ => True
  | _, _, _, .cut _ e _ _ _ rest =>
      rest.Greedy ∧ (¬ e.Inside X ∨ d < (e.searchWeight A : ℝ) + rest.firstWeight)

theorem piece_count {Q : Path R G s t} (P : Partition R G X A d Q) :
    P.pieces.length = P.boundaries + 1 := by
  induction P with
  | one => rfl
  | cut _ _ _ _ _ rest ih => simp only [pieces, List.length_cons, boundaries, ih]

theorem boundary_count {Q : Path R G s t} (P : Partition R G X A d Q) :
    P.boundaries = P.type2 + Q.badEdges X := by
  induction P with
  | one Q hX hd => simp [boundaries, type2, Q.badEdges_zero hX]
  | cut Pre e Q hX hd rest ih =>
      simp only [boundaries, type2, Path.badEdges_append, Pre.badEdges_zero hX,
        Path.badEdges_cons, zero_add]
      by_cases he : e.Inside X <;> simp [he, ih] <;> omega

theorem type2_credit {Q : Path R G s t} (P : Partition R G X A d Q)
    (hP : P.Greedy) (_hd : 0 ≤ d) :
    (P.type2 : ℝ) * d + P.firstWeight ≤ (Q.searchWeight A : ℝ) := by
  induction P with
  | one Q hX hshort => simp [type2, firstWeight]
  | cut Pre e Q hX hshort rest ih =>
      have hi := ih hP.1
      simp only [type2, firstWeight, Path.searchWeight_append, Path.searchWeight,
        Nat.cast_add]
      by_cases he : e.Inside X
      · have hc : d < (e.searchWeight A : ℝ) + rest.firstWeight := hP.2.resolve_left
          (not_not.mpr he)
        simp only [he, ↓reduceIte, Nat.cast_one]
        nlinarith
      · simp only [he, ↓reduceIte, Nat.cast_zero, zero_add]
        have he0 : (0 : ℝ) ≤ e.searchWeight A := Nat.cast_nonneg _
        have hf0 : (0 : ℝ) ≤ rest.firstWeight := Nat.cast_nonneg _
        linarith

/-- Right-to-left greedy type 2 splitting, after removing every type 3 edge.
No replacement edge or recursive reachability certificate is an input. -/
theorem exists_greedy (Q : Path R G s t) (X : Finset (Fin n)) (A : ℕ) (d : ℝ)
    (hd : 0 ≤ d) (hvertices : ∀ v ∈ Q.vertices, v ∈ X) :
    ∃ P : Partition R G X A d Q, P.Greedy := by
  induction Q with
  | nil v =>
      refine ⟨.one (.nil v) (by
          simpa [Path.Inside, Path.support, Path.vertices] using hvertices)
        (by simpa [Path.searchWeight] using hd), ?_⟩
      simp only [Greedy]
  | @cons s v t e Q ih =>
      have hs : s ∈ X := hvertices s (by simp [Path.vertices])
      have hQ : ∀ z ∈ Q.vertices, z ∈ X :=
        fun z hz => hvertices z (List.mem_cons_of_mem _ hz)
      obtain ⟨P, hP⟩ := ih hQ
      cases P with
      | one Q hX hshort =>
          by_cases hmerge : e.Inside X ∧
              ((e.searchWeight A : ℝ) + Q.searchWeight A ≤ d)
          · refine ⟨.one (.cons e Q) ((Path.inside_cons e Q).mpr ⟨hmerge.1, hX⟩)
              (by simpa only [Path.searchWeight, Nat.cast_add] using hmerge.2), ?_⟩
            simp only [Greedy]
          · refine ⟨.cut (.nil s) e Q (by simpa [Path.Inside, Path.support] using hs)
              (by simpa [Path.searchWeight] using hd) (.one Q hX hshort), ?_⟩
            change True ∧ (¬ e.Inside X ∨ d < (e.searchWeight A : ℝ) + Q.searchWeight A)
            refine ⟨trivial, ?_⟩
            by_cases he : e.Inside X
            · exact Or.inr (lt_of_not_ge (fun h => hmerge ⟨he, h⟩))
            · exact Or.inl he
      | @cut _ a b _ Pre f Tail hPre hshort rest =>
          by_cases hmerge : e.Inside X ∧
              ((e.searchWeight A : ℝ) + Pre.searchWeight A ≤ d)
          · refine ⟨.cut (.cons e Pre) f Tail
              ((Path.inside_cons e Pre).mpr ⟨hmerge.1, hPre⟩)
              (by simpa only [Path.searchWeight, Nat.cast_add] using hmerge.2) rest, ?_⟩
            exact hP
          · refine ⟨.cut (.nil s) e (Pre.append (.cons f Tail))
              (by simpa [Path.Inside, Path.support] using hs)
              (by simpa [Path.searchWeight] using hd)
              (.cut Pre f Tail hPre hshort rest), ?_⟩
            change Greedy (.cut Pre f Tail hPre hshort rest) ∧
              (¬ e.Inside X ∨ d < (e.searchWeight A : ℝ) + Pre.searchWeight A)
            refine ⟨hP, ?_⟩
            by_cases he : e.Inside X
            · exact Or.inr (lt_of_not_ge (fun h => hmerge ⟨he, h⟩))
            · exact Or.inl he

theorem late_counts {Q : Path R G s t} (P : Partition R G X A d Q)
    (hP : P.Greedy) (hd : 0 < d) (hQ : (Q.searchWeight A : ℝ) ≤ 4 * d) :
    P.boundaries ≤ 4 + Q.badEdges X ∧ P.pieces.length ≤ 5 + Q.badEdges X := by
  have hc := P.type2_credit hP hd.le
  have hf : (0 : ℝ) ≤ P.firstWeight := Nat.cast_nonneg _
  have ht : P.type2 ≤ 4 := by
    by_contra hn
    have ht : (5 : ℝ) ≤ P.type2 := by exact_mod_cast (show 5 ≤ P.type2 from by omega)
    nlinarith
  have hb := P.boundary_count
  have hp := P.piece_count
  omega

end Partition

inductive FirstHit (R : Representation n) (G : Graph (Fin n)) (P : Fin n → Prop) :
    {s t : Fin n} → Path R G s t → Type
  | head {s t : Fin n} (Q : Path R G s t) (hit : P s) : FirstHit R G P Q
  | later {s a b t : Fin n} (Pre : Path R G s a) (e : Edge R G a b) (Tail : Path R G b t)
      (before : ∀ z ∈ Pre.vertices, ¬ P z) (hit : P b) :
      FirstHit R G P (Pre.append (.cons e Tail))
  | absent {s t : Fin n} (Q : Path R G s t) (nohit : ∀ z ∈ Q.vertices, ¬ P z) :
      FirstHit R G P Q

theorem first_hit (Q : Path R G s t) (P : Fin n → Prop) : Nonempty (FirstHit R G P Q) := by
  induction Q with
  | nil v =>
      by_cases h : P v
      · exact ⟨.head (.nil v) h⟩
      · exact ⟨.absent (.nil v) (by simpa [Path.vertices] using h)⟩
  | @cons s v t e Q ih =>
      by_cases hs : P s
      · exact ⟨.head (.cons e Q) hs⟩
      · obtain ⟨h⟩ := ih
        cases h with
        | head Q hv =>
            exact ⟨.later (.nil s) e Q (by simpa [Path.vertices] using hs) hv⟩
        | later Pre f Tail hPre hh =>
            exact ⟨.later (.cons e Pre) f Tail (by
              intro z hz
              rcases List.mem_cons.mp hz with he | he
              · simpa only [he] using hs
              · exact hPre z he) hh⟩
        | absent Q hQ =>
            exact ⟨.absent (.cons e Q) (by
              intro z hz
              rcases List.mem_cons.mp hz with he | he
              · simpa only [he] using hs
              · exact hQ z he)⟩

inductive LastHit (R : Representation n) (G : Graph (Fin n)) (P : Fin n → Prop) :
    {s t : Fin n} → Path R G s t → Type
  | finish {s t : Fin n} (Q : Path R G s t) (hit : P t) : LastHit R G P Q
  | before {s a b t : Fin n} (Pre : Path R G s a) (e : Edge R G a b) (Tail : Path R G b t)
      (hit : P a) (after : ∀ z ∈ Tail.vertices, ¬ P z) :
      LastHit R G P (Pre.append (.cons e Tail))
  | absent {s t : Fin n} (Q : Path R G s t) (nohit : ∀ z ∈ Q.vertices, ¬ P z) :
      LastHit R G P Q

theorem last_hit (Q : Path R G s t) (P : Fin n → Prop) : Nonempty (LastHit R G P Q) := by
  induction Q with
  | nil v =>
      by_cases h : P v
      · exact ⟨.finish (.nil v) h⟩
      · exact ⟨.absent (.nil v) (by simpa [Path.vertices] using h)⟩
  | @cons s v t e Q ih =>
      obtain ⟨h⟩ := ih
      cases h with
      | finish Q ht => exact ⟨.finish (.cons e Q) ht⟩
      | before Pre f Tail hh hTail => exact ⟨.before (.cons e Pre) f Tail hh hTail⟩
      | absent Q hQ =>
          by_cases hs : P s
          · exact ⟨.before (.nil s) e Q hs hQ⟩
          · exact ⟨.absent (.cons e Q) (by
              intro z hz
              rcases List.mem_cons.mp hz with he | he
              · simpa only [he] using hs
              · exact hQ z he)⟩

end

end StreamingReachability.Late

module

public import StreamingReachability.Approx.Augmented
public import StreamingReachability.Exact.QueryProgramBounds

@[expose] public section

namespace StreamingReachability.Exact.Implementation

open scoped Classical

variable {n : ℕ}

def encodeVertex : Option (Fin n) → Fin (n + 1)
  | none => Fin.last n
  | some v => v.castSucc

def decodeVertex (v : Fin (n + 1)) : Option (Fin n) :=
  if h : v.val < n then some ⟨v.val, h⟩ else none

theorem decode_encode (v : Option (Fin n)) : decodeVertex (encodeVertex v) = v := by
  cases v with
  | none => simp only [encodeVertex, decodeVertex, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  | some v =>
      simp only [encodeVertex, decodeVertex, Fin.val_castSucc, v.isLt, ↓reduceDIte]

theorem encode_decode (v : Fin (n + 1)) : encodeVertex (decodeVertex v) = v := by
  by_cases hv : v.val < n
  · simp only [decodeVertex, hv, ↓reduceDIte, encodeVertex]
    exact Fin.ext rfl
  · simp only [decodeVertex, hv, ↓reduceDIte, encodeVertex]
    apply Fin.ext
    have h := v.isLt
    simp only [Fin.val_last]
    omega

def vertexEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  ⟨decodeVertex, encodeVertex, encode_decode, decode_encode⟩

def integerLabels (answer : Approx.Labels n) : DescriptorProgram.Labels n :=
  Vector.ofFn (fun v => (answer.get v).untopD 0)

def integerLevelAnswer (answer : Approx.Labels (n + 1)) : DescriptorProgram.LevelAnswer n :=
  ⟨Vector.ofFn (fun v => (answer.get v.castSucc).untopD 0), (answer.get (Fin.last n)).untopD 0⟩

theorem integerLabels_accurate (input : List (StoredEdges.Edge n)) (source : Fin n) (denominator : ℕ)
    (answer : Approx.Labels n)
    (h : Approx.Accurate input source (max 1 denominator) answer) :
    IntegerApprox (StoredEdges.graphOfEdges input) source denominator (integerLabels answer).get := by
  intro v d hd
  obtain ⟨q, hq, hlo, hhi⟩ := h.2 v d hd
  simp only [integerLabels, Vector.get_ofFn, hq]
  by_cases hz : denominator = 0
  · exact ⟨hlo, by simp only [hz, Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.zero_le]⟩
  · have heq : max 1 denominator = denominator := Nat.max_eq_right (by omega)
    rw [heq] at hhi
    exact ⟨hlo, hhi⟩

theorem integerLevel_at (answer : Approx.Labels (n + 1)) (v : Option (Fin n)) :
    (integerLevelAnswer answer).at v = (answer.get (encodeVertex v)).untopD 0 := by
  cases v <;> simp only [integerLevelAnswer, DescriptorProgram.LevelAnswer.at, encodeVertex, Vector.get_ofFn]

theorem integerLevel_accurate (input : List (StoredEdges.Edge (n + 1))) (G : Graph (Option (Fin n)))
    (denominator : ℕ) (answer : Approx.Labels (n + 1))
    (hgraph : StoredEdges.graphOfEdges input = G.comap (vertexEquiv n))
    (h : Approx.Accurate input (Fin.last n) (max 1 denominator) answer) :
    IntegerApprox G none denominator (integerLevelAnswer answer).at := by
  have ha := integerLabels_accurate input (Fin.last n) denominator answer h
  intro v d hd
  have hsource : (vertexEquiv n) (Fin.last n) = none := decode_encode (n := n) none
  have htarget : (vertexEquiv n) (encodeVertex v) = v := decode_encode v
  have hdist : (StoredEdges.graphOfEdges input).dist (Fin.last n) (encodeVertex v) = (d : Distance) := by
    rw [hgraph, Graph.dist_comap_equiv, hsource, htarget]
    exact hd
  have hanswer := ha (encodeVertex v) d hdist
  simpa only [integerLabels, Vector.get_ofFn, integerLevel_at] using hanswer

end StreamingReachability.Exact.Implementation

module

public import StreamingReachability.Hopset.PathSlices
public import StreamingReachability.Early.Cover

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

structure VertexCover (size : ℕ) (L : Type*) where
  labels : Finset L
  interval : L → ℕ × ℕ
  bounds : ∀ a ∈ labels, (interval a).1 < (interval a).2 ∧ (interval a).2 ≤ size
  covers : ∀ i : Fin size, ∃ a ∈ labels, Early.Cells.Contains (interval a) i.val
  unique : ∀ a ∈ labels, ∀ b ∈ labels, ∀ i : Fin size,
    Early.Cells.Contains (interval a) i.val → Early.Cells.Contains (interval b) i.val → a = b

namespace VertexCover

variable {size : ℕ} {L : Type*}

theorem separated (C : VertexCover size L) (a : L) (ha : a ∈ C.labels) (b : L) (hb : b ∈ C.labels)
    (hne : a ≠ b) :
    (C.interval a).2 ≤ (C.interval b).1 ∨ (C.interval b).2 ≤ (C.interval a).1 := by
  by_cases hab : (C.interval a).2 ≤ (C.interval b).1
  · exact Or.inl hab
  · by_cases hba : (C.interval b).2 ≤ (C.interval a).1
    · exact Or.inr hba
    · have hA := C.bounds a ha
      have hB := C.bounds b hb
      let i : Fin size := ⟨max (C.interval a).1 (C.interval b).1, by omega⟩
      have hiA : Early.Cells.Contains (C.interval a) i.val := by dsimp [i, Early.Cells.Contains]; omega
      have hiB : Early.Cells.Contains (C.interval b) i.val := by dsimp [i, Early.Cells.Contains]; omega
      exact False.elim (hne (C.unique a ha b hb i hiA hiB))

theorem front_exists (C : VertexCover size L) (hs : 0 < size) :
    ∃ a ∈ C.labels, (C.interval a).1 = 0 := by
  obtain ⟨a, ha, hi⟩ := C.covers ⟨0, hs⟩
  have hlo : (C.interval a).1 ≤ 0 := hi.1
  exact ⟨a, ha, by omega⟩

theorem after_front (C : VertexCover size L) (a : L) (ha : a ∈ C.labels)
    (hzero : (C.interval a).1 = 0) (b : L) (hb : b ∈ C.labels) (hne : b ≠ a) :
    (C.interval a).2 ≤ (C.interval b).1 := by
  rcases C.separated a ha b hb (Ne.symm hne) with h | h
  · exact h
  · have hB := C.bounds b hb
    omega

def tail (C : VertexCover size L) (a : L) (ha : a ∈ C.labels)
    (hzero : (C.interval a).1 = 0) : VertexCover (size - (C.interval a).2) L where
  labels := C.labels.erase a
  interval := fun b => ((C.interval b).1 - (C.interval a).2, (C.interval b).2 - (C.interval a).2)
  bounds := by
    intro b hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    have hstart := C.after_front a ha hzero b hb hne
    have hB := C.bounds b hb
    dsimp only
    omega
  covers := by
    intro i
    let j : Fin size := ⟨i.val + (C.interval a).2, by
      have hi := i.isLt
      have hA := C.bounds a ha
      omega⟩
    obtain ⟨b, hb, hj⟩ := C.covers j
    have hne : b ≠ a := by
      intro he
      subst b
      dsimp only [j, Early.Cells.Contains] at hj
      omega
    refine ⟨b, Finset.mem_erase.mpr ⟨hne, hb⟩, ?_⟩
    have hstart := C.after_front a ha hzero b hb hne
    dsimp only [j, Early.Cells.Contains] at hj
    dsimp only [Early.Cells.Contains]
    omega
  unique := by
    intro b hb c hc i hbi hci
    obtain ⟨hnb, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨hnc, hc⟩ := Finset.mem_erase.mp hc
    let j : Fin size := ⟨i.val + (C.interval a).2, by
      have hi := i.isLt
      have hA := C.bounds a ha
      omega⟩
    have hsb := C.after_front a ha hzero b hb hnb
    have hsc := C.after_front a ha hzero c hc hnc
    apply C.unique b hb c hc j
    · dsimp only [Early.Cells.Contains] at hbi
      dsimp only [j, Early.Cells.Contains]
      omega
    · dsimp only [Early.Cells.Contains] at hci
      dsimp only [j, Early.Cells.Contains]
      omega

theorem tail_card (C : VertexCover size L) (a : L) (ha : a ∈ C.labels)
    (hzero : (C.interval a).1 = 0) :
    (C.tail a ha hzero).labels.card + 1 = C.labels.card :=
  Finset.card_erase_add_one ha

theorem internal_weights_le {m : ℕ} (C : VertexCover size L) (w : Fin m → ℕ) :
    (∑ a ∈ C.labels, ∑ k : Fin m,
      if (C.interval a).1 ≤ k.val ∧ k.val + 1 < (C.interval a).2 then w k else 0) ≤
      ∑ k : Fin m, w k := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k hk
  let A := C.labels.filter fun a => (C.interval a).1 ≤ k.val ∧ k.val + 1 < (C.interval a).2
  have hcard : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, haK⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbK⟩ := Finset.mem_filter.mp hb
    have hbound := C.bounds a ha
    let i : Fin size := ⟨k.val, by omega⟩
    exact C.unique a ha b hb i
      ⟨haK.1, by change k.val < (C.interval a).2; omega⟩
      ⟨hbK.1, by change k.val < (C.interval b).2; omega⟩
  rw [← Finset.sum_filter]
  change (∑ _a ∈ A, w k) ≤ w k
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, one_mul] using Nat.mul_le_mul_right (w k) hcard

end VertexCover

end

end StreamingReachability.Hopset

module

public import StreamingSSSP.Graph

@[expose] public section

namespace StreamingSSSP.Core

open scoped Classical

variable {V : Type*} [DecidableEq V]

def found (B known : Finset V) (d : V → Distance) (r : ℕ) : Finset V :=
  B.filter fun v => v ∉ known ∧ d v ≤ (r : Distance)

def GapWitness (B known : Finset V) (d f : V → Distance) (τ : ℕ) : Prop :=
  ∀ v ∈ B, v ∉ known → d v < f v →
    ∃ Z : Finset V, Z ⊆ B \ known ∧ Z.card = τ ∧ ∀ z ∈ Z, f z ≤ d v

theorem found_subset (B known : Finset V) (d f : V → Distance) (r : ℕ)
    (hdf : ∀ v ∈ B, d v ≤ f v) :
    found B known f r ⊆ found B known d r := by
  intro v hv
  obtain ⟨hvB, hvK, hvr⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvB, hvK, (hdf v hvB).trans hvr⟩

theorem gap_card_le_found (B known : Finset V) (d f : V → Distance)
    (r τ : ℕ) (hgap : GapWitness B known d f τ)
    {v : V} (hv : v ∈ B) (hvk : v ∉ known)
    (hvr : d v ≤ (r : Distance)) (hvf : d v < f v) :
    τ ≤ (found B known f r).card := by
  obtain ⟨Z, hZ, hc, hz⟩ := hgap v hv hvk hvf
  rw [← hc]
  apply Finset.card_le_card
  intro z hzm
  obtain ⟨hzB, hzK⟩ := Finset.mem_sdiff.mp (hZ hzm)
  exact Finset.mem_filter.mpr ⟨hzB, hzK, (hz z hzm).trans hvr⟩

theorem certificate_complete (B known : Finset V) (d f : V → Distance)
    (r τ : ℕ) (hdf : ∀ v ∈ B, d v ≤ f v)
    (hgap : GapWitness B known d f τ) (hsmall : (found B known f r).card < τ) :
    found B known f r = found B known d r := by
  apply Finset.Subset.antisymm (found_subset B known d f r hdf)
  intro v hv
  obtain ⟨hvB, hvK, hvr⟩ := Finset.mem_filter.mp hv
  by_contra hvf
  have hnot : ¬ f v ≤ (r : Distance) := by
    intro h
    exact hvf (Finset.mem_filter.mpr ⟨hvB, hvK, h⟩)
  have hstrict : d v < f v := hvr.trans_lt (lt_of_not_ge hnot)
  exact (not_le_of_gt hsmall) (gap_card_le_found B known d f r τ hgap hvB hvK hvr hstrict)

theorem certificate_exact (B known : Finset V) (d f : V → Distance)
    (r τ : ℕ) (hdf : ∀ v ∈ B, d v ≤ f v)
    (hgap : GapWitness B known d f τ) (hsmall : (found B known f r).card < τ) :
    ∀ v ∈ found B known f r, f v = d v := by
  intro v hv
  obtain ⟨hvB, hvK, hvF⟩ := Finset.mem_filter.mp hv
  apply le_antisymm _ (hdf v hvB)
  by_contra hfd
  have hstrict : d v < f v := lt_of_not_ge hfd
  have hvr := (hdf v hvB).trans hvF
  exact (not_le_of_gt hsmall) (gap_card_le_found B known d f r τ hgap hvB hvK hvr hstrict)

def nextDistance (B known : Finset V) (d : V → Distance) : Distance :=
  (B \ known).inf d

theorem nextDistance_mono (B known : Finset V) (d f : V → Distance)
    (hdf : ∀ v ∈ B, d v ≤ f v) :
    nextDistance B known d ≤ nextDistance B known f := by
  apply Finset.le_inf
  intro v hv
  exact (Finset.inf_le_of_le hv le_rfl).trans (hdf v (Finset.mem_sdiff.mp hv).1)

theorem certificate_next (B known : Finset V) (d f : V → Distance)
    (r τ : ℕ) (hdf : ∀ v ∈ B, d v ≤ f v)
    (hgap : GapWitness B known d f τ) (hsmall : (found B known f r).card < τ) :
    nextDistance B (known ∪ found B known f r) f =
      nextDistance B (known ∪ found B known f r) d := by
  apply le_antisymm _ (nextDistance_mono _ _ d f hdf)
  apply Finset.le_inf
  intro v hv
  obtain ⟨hvB, hvnot⟩ := Finset.mem_sdiff.mp hv
  have hvK : v ∉ known := fun h => hvnot (Finset.mem_union_left _ h)
  by_cases he : f v = d v
  · exact Finset.inf_le_of_le hv he.le
  · have hlt : d v < f v := lt_of_le_of_ne (hdf v hvB) (Ne.symm he)
    obtain ⟨Z, hZ, hc, hz⟩ := hgap v hvB hvK hlt
    have hex : ∃ z ∈ Z, z ∉ found B known f r := by
      by_contra h
      push Not at h
      have hsub : Z ⊆ found B known f r := h
      have hcard := Finset.card_le_card hsub
      omega
    obtain ⟨z, hzm, hzF⟩ := hex
    obtain ⟨hzB, hzK⟩ := Finset.mem_sdiff.mp (hZ hzm)
    have hznot : z ∉ known ∪ found B known f r := by simp [hzK, hzF]
    exact Finset.inf_le_of_le (Finset.mem_sdiff.mpr ⟨hzB, hznot⟩) (hz z hzm)

end StreamingSSSP.Core

module

public import StreamingReachability.Exact.Paths

@[expose] public section

namespace StreamingReachability.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

def EnvelopeCandidate (G : Graph V) (labels : V → ℕ) (slope : ℕ) (v : V)
    (k : ℕ) : Prop :=
  ∃ (u : V) (d : ℕ), G.dist u v = (d : Distance) ∧ k = labels u + slope * d

theorem envelope_exists (G : Graph V) (labels : V → ℕ) (slope : ℕ) (v : V) :
    ∃ k, EnvelopeCandidate G labels slope v k :=
  ⟨labels v, v, 0, by simp, by simp⟩

/-- The exact infimal convolution is used only in the proof, not by the algorithm. -/
noncomputable def envelope (G : Graph V) (labels : V → ℕ) (slope : ℕ) (v : V) : ℕ :=
  Nat.find (envelope_exists G labels slope v)

theorem envelope_witness (G : Graph V) (labels : V → ℕ) (slope : ℕ) (v : V) :
    ∃ (u : V) (d : ℕ), G.dist u v = (d : Distance) ∧
      envelope G labels slope v = labels u + slope * d :=
  Nat.find_spec (envelope_exists G labels slope v)

theorem envelope_le_candidate (G : Graph V) (labels : V → ℕ) (slope : ℕ)
    {u v : V} {d : ℕ} (hd : G.dist u v = d) :
    envelope G labels slope v ≤ labels u + slope * d :=
  Nat.find_min' (envelope_exists G labels slope v) ⟨u, d, hd, rfl⟩

theorem envelope_le_label (G : Graph V) (labels : V → ℕ) (slope : ℕ) (v : V) :
    envelope G labels slope v ≤ labels v := by
  simpa using envelope_le_candidate G labels slope (d := 0) (G.dist_self v)

theorem envelope_smooth (G : Graph V) (labels : V → ℕ) (slope : ℕ)
    {u v : V} {d : ℕ} (hd : G.dist u v = d) :
    envelope G labels slope v ≤ envelope G labels slope u + slope * d := by
  obtain ⟨a, k, hk, he⟩ := envelope_witness G labels slope u
  have ht : G.dist a v ≤ ((k + d : ℕ) : Distance) := by
    rw [Nat.cast_add]
    simpa only [hk, hd] using G.dist_triangle a u v
  obtain ⟨j, hj, hjle⟩ := finite_of_le ht
  have hh := envelope_le_candidate G labels slope hj
  rw [he]
  nlinarith [Nat.mul_le_mul_left slope hjle]

theorem envelope_edge (G : Graph V) (labels : V → ℕ) (slope : ℕ)
    {u v : V} {w : ℕ} (hw : G u v = w) :
    envelope G labels slope v ≤ envelope G labels slope u + slope * w := by
  obtain ⟨d, hd, hle⟩ := finite_of_le (hw ▸ G.dist_le_edge u v)
  exact (envelope_smooth G labels slope hd).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left slope hle) _)

def Noncontracting (G : Graph V) (s : V) (scale : ℕ) (labels : V → ℕ) : Prop :=
  ∀ v (d : ℕ), G.dist s v = (d : Distance) → scale * d ≤ labels v

def AdditivelySmooth (G : Graph V) (labels : V → ℕ) (slope error : ℕ) : Prop :=
  ∀ u v (d : ℕ), G.dist u v = (d : Distance) →
    (labels v : ℤ) ≤ labels u + (slope : ℤ) * d + error

theorem envelope_noncontracting (G : Graph V) (s : V) (scale slope : ℕ)
    (labels : V → ℕ) (hslope : scale ≤ slope)
    (hreach : ∀ u, G.dist s u ≠ ⊤)
    (hlabels : Noncontracting G s scale labels) :
    Noncontracting G s scale (envelope G labels slope) := by
  intro v d hd
  obtain ⟨u, k, hk, he⟩ := envelope_witness G labels slope v
  lift G.dist s u to ℕ using hreach u with j hj
  have hl := hlabels u j hj.symm
  have ht : d ≤ j + k := by
    have ht := G.dist_triangle s u v
    rw [hd, ← hj, hk] at ht
    have ht' : (d : Distance) ≤ ((j + k : ℕ) : Distance) := by
      calc
        (d : Distance) ≤ (j : Distance) + (k : Distance) := ht
        _ = ((j + k : ℕ) : Distance) := (Nat.cast_add j k).symm
    exact WithTop.coe_le_coe.mp ht'
  rw [he]
  nlinarith [Nat.mul_le_mul_left scale ht, Nat.mul_le_mul_right k hslope]

theorem bounded_labels_smooth (G : Graph V) (labels : V → ℕ) (slope error : ℕ)
    (h : ∀ v, labels v ≤ error) : AdditivelySmooth G labels slope error := by
  intro u v d _
  have hv := h v
  have hv' : (labels v : ℤ) ≤ error := by exact_mod_cast hv
  nlinarith [show (0 : ℤ) ≤ labels u by positivity,
    show (0 : ℤ) ≤ (slope : ℤ) * d by positivity]

end StreamingReachability.Exact

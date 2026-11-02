module

public import StreamingReachability.Hopset.OwnerGeometry

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem grouped_congr_on (S : Finset (Fin n)) (keep₁ keep₂ : Fin n → Bool)
    (key₁ key₂ : Fin n → List ℕ)
    (hkeep : ∀ v ∈ S, keep₁ v = keep₂ v) (hkey : ∀ v ∈ S, key₁ v = key₂ v) :
    grouped S keep₁ key₁ = grouped S keep₂ key₂ := by
  have hf : (members S).filter keep₁ = (members S).filter keep₂ := by
    apply List.filter_congr
    intro v hv
    exact hkeep v ((mem_members S v).mp hv)
  have hm : ((members S).filter keep₂).map key₁ =
      ((members S).filter keep₂).map key₂ := by
    apply List.map_congr_left
    intro v hv
    exact hkey v ((mem_members S v).mp (List.mem_filter.mp hv).1)
  have hk : groupKeys S keep₁ key₁ = groupKeys S keep₂ key₂ := by
    unfold groupKeys
    rw [hf, hm]
  unfold grouped
  rw [hk]
  apply List.map_congr_left
  intro key _
  ext v
  by_cases hv : v ∈ S
  · simp only [Finset.mem_filter, hv, true_and, hkeep v hv, hkey v hv]
  · simp [hv]

theorem labels_eq_filtered (cfg : Config) (r : ℕ) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns) (v : Fin n) :
    labels cfg r pivots reply i v =
      ((pivots.filter fun p => decide (p.setId = i)).flatMap fun p =>
        (if inFlag cfg r p reply v then [2 * p.vertex.val] else []) ++
          if outFlag cfg r p reply v then [2 * p.vertex.val + 1] else []) := by
  induction pivots with
  | nil => rfl
  | cons p pivots ih =>
      by_cases hi : p.setId = i <;> simp_all [labels]

theorem labels_of_geometry (cfg : Config) (r : ℕ) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns)
    (S P : Finset (Fin n)) (G : Graph (Fin n)) (rho : Fin n → ℝ)
    (hvertices : ((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex) = members P)
    (hflags : ∀ p ∈ pivots, p.setId = i → ∀ v ∈ S,
      (outFlag cfg r p reply v = true ↔ Early.Within G p.vertex v (rho p.vertex)) ∧
      (inFlag cfg r p reply v = true ↔ Early.Within G v p.vertex (rho p.vertex)))
    (v : Fin n) (hv : v ∈ S) :
    labels cfg r pivots reply i v = Geometry.labels G P rho v := by
  rw [labels_eq_filtered]
  calc
    _ = ((pivots.filter fun p => decide (p.setId = i)).flatMap fun p =>
        (if Early.Within G v p.vertex (rho p.vertex) then [2 * p.vertex.val] else []) ++
          if Early.Within G p.vertex v (rho p.vertex) then [2 * p.vertex.val + 1] else []) := by
      apply List.flatMap_congr
      intro p hp
      obtain ⟨hp, hi⟩ := List.mem_filter.mp hp
      have h := hflags p hp (of_decide_eq_true hi) v hv
      simp only [h.1, h.2]
    _ = (((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex).flatMap fun q =>
        (if Early.Within G v q (rho q) then [2 * q.val] else []) ++
          if Early.Within G q v (rho q) then [2 * q.val + 1] else []) := by
      rw [List.flatMap_map]
    _ = Geometry.labels G P rho v := by rw [hvertices]; rfl

theorem removed_false_of_geometry (cfg : Config) (r : ℕ) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns)
    (S P : Finset (Fin n)) (G : Graph (Fin n)) (rho : Fin n → ℝ)
    (hvertices : ((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex) = members P)
    (hflags : ∀ p ∈ pivots, p.setId = i → ∀ v ∈ S,
      (outFlag cfg r p reply v = true ↔ Early.Within G p.vertex v (rho p.vertex)) ∧
      (inFlag cfg r p reply v = true ↔ Early.Within G v p.vertex (rho p.vertex)))
    (v : Fin n) (hv : v ∈ S) :
    removed cfg r pivots reply i v = false ↔ Early.remaining G P rho v := by
  have hcover (q : Fin n) :
      q ∈ P ↔ ∃ p ∈ pivots, p.setId = i ∧ p.vertex = q := by
    rw [← mem_members P q, ← hvertices]
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨p, ⟨hp, hi⟩, he⟩
      exact ⟨p, hp, hi, he⟩
    · rintro ⟨p, hp, hi, he⟩
      exact ⟨p, ⟨hp, hi⟩, he⟩
  have htrue : removed cfg r pivots reply i v = true ↔
      ∃ q ∈ P, Early.Within G v q (rho q) ∧ Early.Within G q v (rho q) := by
    constructor
    · intro h
      obtain ⟨p, hp, hpred⟩ := List.any_eq_true.mp h
      obtain ⟨⟨hi, hin⟩, hout⟩ := (show (p.setId = i ∧ inFlag cfg r p reply v = true) ∧
          outFlag cfg r p reply v = true by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hpred)
      have hflags := hflags p hp hi v hv
      exact ⟨p.vertex, (hcover p.vertex).mpr ⟨p, hp, hi, rfl⟩,
        hflags.2.mp hin, hflags.1.mp hout⟩
    · rintro ⟨q, hq, hin, hout⟩
      obtain ⟨p, hp, hi, he⟩ := (hcover q).mp hq
      subst q
      have hflags := hflags p hp hi v hv
      apply List.any_eq_true.mpr
      refine ⟨p, hp, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hi, hflags.2.mpr hin⟩, hflags.1.mpr hout⟩
  have hfalse : removed cfg r pivots reply i v = false ↔ ¬ removed cfg r pivots reply i v = true := by
    cases removed cfg r pivots reply i v <;> simp
  rw [hfalse, htrue]
  simp [Early.remaining]

theorem local_core_of_geometry (cfg : Config) (r : ℕ) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns)
    (S P : Finset (Fin n)) (G : Graph (Fin n)) (rho : Fin n → ℝ)
    (hvertices : ((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex) = members P)
    (hflags : ∀ p ∈ pivots, p.setId = i → ∀ v ∈ S,
      (outFlag cfg r p reply v = true ↔ Early.Within G p.vertex v (rho p.vertex)) ∧
      (inFlag cfg r p reply v = true ↔ Early.Within G v p.vertex (rho p.vertex))) :
    grouped S (fun v => !removed cfg r pivots reply i v) (labels cfg r pivots reply i) =
      Geometry.core G S P rho := by
  apply grouped_congr_on
  · intro v hv
    have h := removed_false_of_geometry cfg r pivots reply i S P G rho hvertices hflags v hv
    cases he : removed cfg r pivots reply i v <;> simp_all
  · exact labels_of_geometry cfg r pivots reply i S P G rho hvertices hflags

theorem local_late_core_of_geometry (cfg : Config) (r : ℕ) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns)
    (S P : Finset (Fin n)) (G : Graph (Fin n)) (rho : Fin n → ℝ)
    (hvertices : ((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex) = members P)
    (hflags : ∀ p ∈ pivots, p.setId = i → ∀ v ∈ S,
      (outFlag cfg r p reply v = true ↔ Early.Within G p.vertex v (rho p.vertex)) ∧
      (inFlag cfg r p reply v = true ↔ Early.Within G v p.vertex (rho p.vertex))) :
    (S.filter fun v => labels cfg r pivots reply i v = []) =
      Reference.lateChild G S P rho := by
  ext v
  by_cases hv : v ∈ S
  · simp only [Finset.mem_filter, Reference.lateChild, hv, true_and,
      labels_of_geometry cfg r pivots reply i S P G rho hvertices hflags v hv]
  · simp [Reference.lateChild, hv]

end

end StreamingReachability.Hopset

module

public import StreamingSSSP.Hopset.PivotQueries
public import StreamingSSSP.Hopset.Reference

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

def sampledPivot (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (target : Target n ns) (index : ℕ)
    (owner : Fin cfg.groups × Fin cfg.shifts) : Pivot n ns :=
  ⟨target.setId, target.vertex,
    chooseEta cfg r (sets.get target.setId) reply (2 * index) (2 * index + 1) owner.1 owner.2,
    owner.2.val, 2 * index, 2 * index + 1⟩

theorem sampled_radius_eq (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target)
    (hk : target.kind = .pivot) (hsource : target.vertex ∈ sets.get target.setId)
    (owner : Fin cfg.groups × Fin cfg.shifts) :
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    let p := sampledPivot cfg r sets reply target index owner
    ((p.eta : ℝ) + Early.shiftValue owner.2) * Reference.distanceScale cfg r =
      Late.radius (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
        (Reference.distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos target.vertex owner := by
  dsimp only [sampledPivot]
  rw [pivot_eta_matches cfg r stored input hn hs hp hsize hnum sets targets index target ht hk hsource]
  simp only [Late.radius, Early.candidateRadius, Config.lambda, Config.width, Early.lambda,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Reference.distanceScale]

theorem raw_pivot_geometry (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target)
    (hk : target.kind = .pivot) (hsource : target.vertex ∈ sets.get target.setId)
    (owner : Fin cfg.groups × Fin cfg.shifts) :
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    let p := sampledPivot cfg r sets reply target index owner
    let G := Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale
    let D := Reference.distanceScale cfg r
    let rho := Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos target.vertex owner
    (∀ v ∈ sets.get target.setId,
      (outFlag cfg r p reply v = true ↔ Early.Within G target.vertex v rho) ∧
      (inFlag cfg r p reply v = true ↔ Early.Within G v target.vertex rho)) ∧
    fringe cfg r p.eta p.shift (sets.get target.setId) reply p.forward p.backward =
      sets.get target.setId ∩ Early.fringe G target.vertex rho D ∧
    bothBall cfg r (p.eta + 1) p.shift (sets.get target.setId) reply p.forward p.backward =
      sets.get target.setId ∩ Early.bothBall G target.vertex (rho + D) := by
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  let p := sampledPivot cfg r sets reply target index owner
  let S := sets.get target.setId
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let D := Reference.distanceScale cfg r
  let rho := Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos target.vertex owner
  have hD : 0 < D := by
    dsimp only [D, Reference.distanceScale]
    have hd := cfg.denominatorAt_pos r
    positivity
  have hG : Implicit.induced G S = G :=
    Late.search_induced stored (StoredEdges.graphOfEdges input) S cfg.inputScale
  have ha : Late.AccurateBalls G S target.vertex reply p.forward p.backward
      (Early.searchRadius cfg.k cfg.groups D) :=
    accurate_pivot_queries cfg r stored input hn hs hp hsize sets targets index target ht hk
  have hrho : ((p.eta : ℝ) + Early.shiftValue owner.2) * D = rho :=
    sampled_radius_eq cfg r stored input hn hs hp hsize hnum sets targets index target ht hk hsource owner
  have hbound := (Late.radius_bounds G D cfg.k cfg.groups cfg.shifts cfg.k_pos hD target.vertex owner).2
  have houter : rho + D ≤ Early.searchRadius cfg.k cfg.groups D := by
    unfold Early.nearRadius Early.searchRadius at *
    nlinarith
  have hcap : rho ≤ Early.searchRadius cfg.k cfg.groups D := by linarith
  have hplus : (((p.eta + 1 : ℕ) : ℝ) + Early.shiftValue owner.2) * D = rho + D := by
    rw [Nat.cast_add, Nat.cast_one, ← hrho]
    ring
  change ((p.eta : ℝ) + Early.shiftValue owner.2) *
    ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) = rho at hrho
  change (((p.eta + 1 : ℕ) : ℝ) + Early.shiftValue owner.2) *
    ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) = rho + D at hplus
  have heta : 1 ≤ p.eta := by
    have h := chooseEta_range cfg r S reply (2 * index) (2 * index + 1) owner.1 owner.2
    have hl : 0 < cfg.lambda := Nat.mul_pos cfg.width_pos cfg.groups_pos
    change 1 ≤ chooseEta cfg r S reply (2 * index) (2 * index + 1) owner.1 owner.2
    omega
  have hden : 0 < cfg.shifts * cfg.denominatorAt r :=
    Nat.mul_pos cfg.shifts_pos (cfg.denominatorAt_pos r)
  change (∀ v ∈ S, _) ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have h := ha v hv rho hcap
    have hf : Early.Bounded (lookup reply p.forward v) rho ↔ outFlag cfg r p reply v = true := by
      dsimp only [outFlag]
      rw [Late.withinFraction_iff_bounded _ _ _ hden]
      change Early.Bounded (lookup reply p.forward v) rho ↔
        Early.Bounded (lookup reply p.forward v)
          ((((p.eta * cfg.shifts + owner.2.val) * cfg.initialNumerator : ℕ) : ℝ) /
            ((cfg.shifts * cfg.denominatorAt r : ℕ) : ℝ))
      rw [Late.fraction_radius, hrho]
    have hb : Early.Bounded (lookup reply p.backward v) rho ↔ inFlag cfg r p reply v = true := by
      dsimp only [inFlag]
      rw [Late.withinFraction_iff_bounded _ _ _ hden]
      change Early.Bounded (lookup reply p.backward v) rho ↔
        Early.Bounded (lookup reply p.backward v)
          ((((p.eta * cfg.shifts + owner.2.val) * cfg.initialNumerator : ℕ) : ℝ) /
            ((cfg.shifts * cfg.denominatorAt r : ℕ) : ℝ))
      rw [Late.fraction_radius, hrho]
    exact ⟨hf.symm.trans h.1, hb.symm.trans h.2⟩
  · have he := Late.actual_fringe_eq_of_accurate cfg r p.eta heta owner.2 G S target.vertex
      hsource hG reply p.forward p.backward (Early.searchRadius cfg.k cfg.groups D) ha
      (hplus.trans_le houter)
    change fringe cfg r p.eta owner.2.val S reply p.forward p.backward = _
    rw [he, hrho]
    apply (Finset.inter_eq_right.mpr _).symm
    intro v hv
    exact Late.bothBall_subset_of_induced G S hG hsource _
      ((Early.mem_bothBall G target.vertex v _).mpr
        ((Early.mem_fringe G target.vertex v _ _).mp hv).1)
  · have he := Late.actual_bothBall_eq_of_accurate cfg r (p.eta + 1) owner.2 G S target.vertex
      hsource hG reply p.forward p.backward (Early.searchRadius cfg.k cfg.groups D) ha
      (hplus.trans_le houter)
    change bothBall cfg r (p.eta + 1) owner.2.val S reply p.forward p.backward = _
    rw [he, hplus]
    exact (Finset.inter_eq_right.mpr (Late.bothBall_subset_of_induced G S hG hsource _)).symm

end

end StreamingSSSP.Hopset

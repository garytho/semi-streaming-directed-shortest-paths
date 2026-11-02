module

public import StreamingSSSP.Hopset.StarPresence
public import StreamingSSSP.Hopset.SearchCaps

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem raw_two_star_route (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target) (hk : target.kind ≠ .pivot)
    (y z : Fin n) (W : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hin : Early.Within (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
      y target.vertex (targetRadius cfg r target.kind : ℝ))
    (hout : Early.Within (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
      target.vertex z (targetRadius cfg r target.kind : ℝ))
    (hbudget : Early.Bounded
      ((Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist y target.vertex +
        (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist target.vertex z)
      ((W : ℝ) + B))
    (F : Graph (Fin n))
    (hF : ∀ e ∈ emittedStars cfg targets
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance)) :
    ∃ debt : ℕ, (debt : ℝ) ≤ B ∧
      ∃ T : Late.Route F y z (cfg.inputScale * (W + debt)), T.hops ≤ 2 := by
  obtain ⟨a, b, ha, hb, hab⟩ := Early.bounded_sum_witness hbudget
  have hacap : a ≤ targetRadius cfg r target.kind := by
    have h := (bounded_integer_iff _ _).mp hin
    rw [ha] at h
    exact WithTop.coe_le_coe.mp h
  have hbcap : b ≤ targetRadius cfg r target.kind := by
    have h := (bounded_integer_iff _ _).mp hout
    rw [hb] at h
    exact WithTop.coe_le_coe.mp h
  obtain ⟨left, hleft⟩ := raw_star_route cfg r stored input hn hs hp hsize sets targets index target ht hk
    true y a hacap ha.le F hF
  obtain ⟨right, hright⟩ := raw_star_route cfg r stored input hn hs hp hsize sets targets index target ht hk
    false z b hbcap hb.le F hF
  let debt := (a + b) - W
  have hdebt : (debt : ℝ) ≤ B := nat_excess_le (a + b) W B hB (by simpa only [Nat.cast_add] using hab)
  have hcost : cfg.inputScale * a + cfg.inputScale * b ≤ cfg.inputScale * (W + debt) := by
    have h : a + b ≤ W + debt := by dsimp only [debt]; omega
    simpa only [Nat.mul_add] using Nat.mul_le_mul_left cfg.inputScale h
  refine ⟨debt, hdebt, (left.append right).weaken hcost, ?_⟩
  have hh := left.hops_append right
  simp only [Late.Route.hops_weaken]
  omega

end

end StreamingSSSP.Hopset

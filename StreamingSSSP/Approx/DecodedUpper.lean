module

public import StreamingSSSP.Approx.RoundingAccuracy

@[expose] public section

namespace StreamingSSSP.Approx

open scoped Classical
open Hopset

noncomputable section

variable {n : ℕ}

theorem decoded_upper (hn : 0 < n) (accuracy x scale : ℕ) (ha : 0 < accuracy) (hscale : 0 < scale)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source v : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hhopset : IsImplicitHopset (input.filterMap (microView (Parameters.queryUnit n accuracy x))) stored
      (Parameters.hopBound n accuracy x) (1 + 1 / (5 * (accuracy : ℝ))))
    (d : ℕ) (hd : (StoredEdges.graphOfEdges input).dist source v = (d : Distance))
    (hlo : scale ≤ d) (hhi : d < 2 * scale) :
    ∃ answer : ℕ,
      decoded (Parameters.queryUnit n accuracy x) scale
        (Core.BatchAPI.run (queryRequest stored x scale (8 * Parameters.queryUnit n accuracy x) source)
          (input.filterMap (microView (Parameters.queryUnit n accuracy x)))).records v = (answer : Distance) ∧
      d ≤ answer ∧ accuracy * answer ≤ (accuracy + 1) * d := by
  let unit := Parameters.queryUnit n accuracy x
  let hops := Parameters.hopBound n accuracy x
  let physical := input.filterMap (microView unit)
  let G := StoredEdges.graphOfEdges physical
  let F := Late.rounded scale (stored.graph G)
  let reply := (Core.BatchAPI.run (queryRequest stored x scale (8 * unit) source) physical).records
  have hunit : 0 < unit := Parameters.queryUnit_pos n accuracy x ha
  have hphysical := microView_positive unit hunit input hp
  have hscaled : G.dist source v = ((unit * d : ℕ) : Distance) := by
    change (StoredEdges.graphOfEdges (input.filterMap (microView unit))).dist source v = _
    rw [microView_graph, Graph.scaled_dist, hd]
    rfl
  obtain ⟨cost, hcost, hlower, herror⟩ := hhopset.2 source v (unit * d) hscaled
  have hfinite : (stored.graph G).hopDist hops source v ≠ ⊤ := by rw [hcost]; exact WithTop.natCast_ne_top _
  obtain ⟨Q, hsimple, hlength, hmicro⟩ := Late.exists_backed_hopPath hops source v hfinite
  have heq : Q.micro = cost := by exact_mod_cast hmicro.trans hcost
  have hreal : (Q.micro : ℝ) ≤ (1 + 1 / (5 * (accuracy : ℝ))) * unit * d := by
    rw [heq]
    simpa only [Nat.cast_mul, mul_assoc] using herror
  have hfive := fivefold_error accuracy unit d Q.micro ha hreal
  have hcoarse := fivefold_coarse accuracy unit d Q.micro ha hfive
  have hrawRound := Q.rounded_search_budget scale
  have hlen := Nat.mul_le_mul_left scale hlength
  have hround : scale * Q.searchWeight scale ≤ Q.micro + scale * hops :=
    hrawRound.trans (Nat.add_le_add le_rfl hlen)
  have hsmall : hops ≤ unit := by
    have h := Parameters.two_hops_le_unit n accuracy x ha
    change 2 * hops ≤ unit at h
    omega
  have hradius := rounded_radius_bound unit hops scale d Q.micro (Q.searchWeight scale) hscale hhi hsmall hcoarse hround
  have hinside : Q.Inside Finset.univ := fun w _ => Finset.mem_univ w
  have hpathCost : F.pathCost Q.vertices = (Q.searchWeight scale : Distance) := by
    have h := Q.vertices_cost scale hinside
    simp only [Implicit.Representation.restricted_univ] at h
    exact h
  have hmetric : F.dist source v ≤ (Q.searchWeight scale : Distance) :=
    (F.dist_le_pathCost Q.endpoints).trans_eq hpathCost
  obtain ⟨rounded, hrounded, hroundedBound⟩ := Exact.finite_of_le hmetric
  have hwithin : F.dist source v ≤ ((8 * unit : ℕ) : Distance) :=
    hmetric.trans (WithTop.coe_le_coe.mpr hradius)
  have hquery := query_lookup hn stored physical x scale (8 * unit) source v hs hphysical hscale hsize
  have hlookup : Core.BatchAPI.lookup reply 0 v = (rounded : Distance) := by
    calc
      _ = if F.dist source v ≤ ((8 * unit : ℕ) : Distance) then F.dist source v else ⊤ := hquery
      _ = F.dist source v := ite_eq_left hwithin
      _ = _ := hrounded
  have hdecode : decoded unit scale reply v = ((scale * rounded / unit : ℕ) : Distance) := by
    unfold decoded
    rw [hlookup]
    rfl
  have hroundFinal : scale * rounded ≤ Q.micro + scale * hops :=
    (Nat.mul_le_mul_left scale hroundedBound).trans hround
  have haccuracy := integer_decode_accuracy accuracy unit hops scale d Q.micro rounded hunit hlo
    (Parameters.five_accuracy_hops_le_unit n accuracy x) hfive hroundFinal
  have hnoncontract := decoded_lower hn unit scale x (8 * unit) hunit hscale input stored source v hp hs hsize hhopset.1
  rw [hd, hdecode] at hnoncontract
  exact ⟨scale * rounded / unit, hdecode, WithTop.coe_le_coe.mp hnoncontract, haccuracy⟩

end

end StreamingSSSP.Approx

module

public import StreamingSSSP.Exact.Schedule

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*}

def WeightsBounded (G : Graph V) (W : ℕ) : Prop :=
  ∀ u v (w : ℕ), G u v = w → w ≤ W

theorem pathCost_bound (G : Graph V) (W : ℕ) (hW : WeightsBounded G W)
    (xs : List V) (c : ℕ) (hc : G.pathCost xs = c) :
    c ≤ W * (xs.length - 1) := by
  induction xs generalizing c with
  | nil =>
      have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
      simp [hc0]
  | cons u xs ih =>
      cases xs with
      | nil =>
          have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
          simp [hc0]
      | cons v xs =>
          obtain ⟨a, b, ha, hb, hab⟩ := finite_add hc
          have haW := hW u v a ha
          have hi := ih b hb
          simp only [List.length_cons, Nat.add_sub_cancel] at *
          nlinarith

theorem dist_bound [Fintype V] (G : Graph V) (W : ℕ) (hW : WeightsBounded G W)
    {s v : V} {d : ℕ} (hd : G.dist s v = d) : d ≤ W * (Fintype.card V - 1) := by
  obtain ⟨xs, _, he, hl, hc⟩ := G.exists_dist_path (s := s) (t := v) (by simp [hd])
  have hp := pathCost_bound G W hW xs d (hc.trans hd)
  exact hp.trans (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hl 1))

noncomputable def sentinelGraph (source : V) (sentinel : ℕ) : Graph V :=
  fun u v => if u = source ∧ v ≠ source then sentinel else ⊤

def sentinel (n W : ℕ) : ℕ := n * (n * W + 1)

noncomputable def preprocess [Fintype V] (G : Graph V) (s : V) (W : ℕ) : Graph V :=
  (affineGraph G (Fintype.card V) 1).union
    (sentinelGraph s (sentinel (Fintype.card V) W))

theorem union_path_below (A F : Graph V) (threshold : ℕ)
    (hF : ∀ u v, (threshold : Distance) ≤ F u v)
    (xs : List V) (c : ℕ) (hc : (A.union F).pathCost xs = c) (hlt : c < threshold) :
    A.pathCost xs = c := by
  induction xs generalizing c with
  | nil => exact hc
  | cons u xs ih =>
      cases xs with
      | nil => exact hc
      | cons v xs =>
          obtain ⟨a, b, ha, hb, hab⟩ := finite_add hc
          have hat : a < threshold := by omega
          have hbt : b < threshold := by omega
          have hA : A u v = a := by
            have hFa : (a : Distance) < F u v :=
              (WithTop.coe_lt_coe.mpr hat).trans_le (hF u v)
            have hmin : min (A u v) (F u v) = (a : Distance) := ha
            have hlt : A u v < F u v := by
              by_contra hn
              have heq : min (A u v) (F u v) = F u v := min_eq_right (le_of_not_gt hn)
              rw [heq] at hmin
              exact (ne_of_lt hFa) hmin.symm
            simpa [min_eq_left hlt.le] using hmin
          rw [Graph.pathCost_cons_cons, hA, ih b hb hbt]
          calc
            (a : Distance) + (b : Distance) = ((a + b : ℕ) : Distance) :=
              (Nat.cast_add _ _).symm
            _ = (c : Distance) := by rw [hab]

theorem union_dist_below [Fintype V] (A F : Graph V) (threshold : ℕ)
    (hF : ∀ u v, (threshold : Distance) ≤ F u v)
    {s v : V} {d : ℕ} (hd : (A.union F).dist s v = d) (hlt : d < threshold) :
    A.dist s v = d := by
  obtain ⟨xs, _, he, _, hc⟩ := (A.union F).exists_dist_path (s := s) (t := v) (by simp [hd])
  have hA := union_path_below A F threshold hF xs d (hc.trans hd) hlt
  exact le_antisymm (hA ▸ A.dist_le_pathCost he)
    (hd ▸ Graph.dist_union_le_left A F s v)

theorem sentinelGraph_lower (s : V) (threshold : ℕ) (u v : V) :
    (threshold : Distance) ≤ sentinelGraph s threshold u v := by
  simp only [sentinelGraph]
  split_ifs <;> simp

theorem preprocess_reachable [Fintype V] (G : Graph V) (s : V) (W : ℕ) (v : V) :
    ∃ d : ℕ, (preprocess G s W).dist s v = d ∧ d ≤ sentinel (Fintype.card V) W := by
  by_cases hv : v = s
  · subst v
    exact ⟨0, by simp, Nat.zero_le _⟩
  · obtain ⟨d, hd, hdb⟩ := finite_of_le
      (show (preprocess G s W).dist s v ≤
        (sentinel (Fintype.card V) W : Distance) from
        ((preprocess G s W).dist_le_edge s v).trans (by
          simp [preprocess, Graph.union, sentinelGraph, hv]))
    exact ⟨d, hd, hdb⟩

theorem preprocess_reachable_distance [Fintype V] (G : Graph V) (s : V) (W : ℕ)
    (hW : WeightsBounded G W) {v : V} {d : ℕ} (hd : G.dist s v = d) :
    ∃ e : ℕ, (preprocess G s W).dist s v = e ∧
      e < sentinel (Fintype.card V) W ∧ e / Fintype.card V = d := by
  let n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨s⟩
  obtain ⟨e, he, hl, hu⟩ := affine_dist_bounds G n 1 hd
  have hdW := dist_bound G W hW hd
  have het : e < sentinel n W := by
    unfold sentinel
    have heW : e ≤ (n - 1) * (n * W + 1) := by
      calc
        e ≤ n * d + (n - 1) := by simpa using hu
        _ ≤ n * (W * (n - 1)) + (n - 1) := by gcongr
        _ = (n - 1) * (n * W + 1) := by ring
    exact heW.trans_lt (Nat.mul_lt_mul_of_pos_right
      (Nat.sub_lt hn (by decide)) (by omega))
  have hprele : (preprocess G s W).dist s v ≤ e := by
    rw [← he]
    exact Graph.dist_union_le_left _ _ s v
  obtain ⟨q, hq, hqe⟩ := finite_of_le hprele
  have hqA := union_dist_below (affineGraph G n 1) (sentinelGraph s (sentinel n W))
    (sentinel n W) (sentinelGraph_lower s _) hq (hqe.trans_lt het)
  have hqe' : q = e := WithTop.coe_eq_coe.mp (hqA.symm.trans he)
  refine ⟨e, by simpa [hqe'] using hq, het, ?_⟩
  apply Nat.le_antisymm
  · apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hn).2
    nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]
  · apply (Nat.le_div_iff_mul_le hn).2
    nlinarith

theorem preprocess_below_iff [Fintype V] (G : Graph V) (s : V) (W : ℕ)
    (hW : WeightsBounded G W) {v : V} {e : ℕ}
    (he : (preprocess G s W).dist s v = e) :
    e < sentinel (Fintype.card V) W ↔ G.dist s v ≠ ⊤ := by
  constructor
  · intro hlt
    have hA := union_dist_below _ _ _ (sentinelGraph_lower s _) he hlt
    obtain ⟨xs, _, hx, _, hc⟩ :=
      (affineGraph G (Fintype.card V) 1).exists_dist_path (s := s) (t := v) (by simp [hA])
    exact (G.dist_ne_top_iff s v).mpr ⟨xs, hx,
      (affine_path_finite G (Fintype.card V) 1 xs).mp (by simp [hc, hA])⟩
  · intro hfinite
    lift G.dist s v to ℕ using hfinite with d hd
    obtain ⟨q, hq, hqt, _⟩ := preprocess_reachable_distance G s W hW hd.symm
    have heq : e = q := WithTop.coe_eq_coe.mp (he.symm.trans hq)
    omega

def decode [Fintype V] (W : ℕ) (estimates : V → ℕ) : V → Distance :=
  fun v => if estimates v < sentinel (Fintype.card V) W
    then ((estimates v / Fintype.card V : ℕ) : Distance) else ⊤

theorem decode_correct [Fintype V] (G : Graph V) (s : V) (W : ℕ)
    (hW : WeightsBounded G W) (estimates : V → ℕ)
    (hestimates : ∀ v, (preprocess G s W).dist s v = estimates v) :
    decode W estimates = G.dist s := by
  funext v
  by_cases hf : G.dist s v = ⊤
  · have hn := (preprocess_below_iff G s W hW (hestimates v)).not.mpr (by simpa using hf)
    simp [decode, hn, hf]
  · lift G.dist s v to ℕ using hf with d hd
    obtain ⟨e, he, het, hed⟩ := preprocess_reachable_distance G s W hW hd.symm
    have hval : estimates v = e := WithTop.coe_eq_coe.mp ((hestimates v).symm.trans he)
    simp [decode, hval, het, hed, ← hd]

end StreamingSSSP.Exact

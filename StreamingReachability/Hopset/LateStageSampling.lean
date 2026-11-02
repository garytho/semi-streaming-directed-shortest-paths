module

public import StreamingReachability.Hopset.ActualLateConfig
public import StreamingReachability.Probability.SubsetFamily

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

def lateStage (cfg : Config) (S : Finset (Fin n)) (choice : Reference.Choice n cfg) :
    List (Fin n × (Fin cfg.groups × Fin cfg.shifts)) :=
  Early.Sampling.ownedSubset S.toList (fun v => decide (v ∈ choice.pivots)) choice.owners

theorem lateStage_filter (cfg : Config) (S : Finset (Fin n)) (coins : Fin n → Bool)
    (owners : Reference.Owners n cfg) :
    lateStage cfg S ⟨S.filter (fun v => coins v = true), owners⟩ =
      Early.Sampling.ownedSubset S.toList coins owners := by
  unfold lateStage Early.Sampling.ownedSubset
  apply List.filterMap_congr
  intro v hv
  have hvS := Finset.mem_toList.mp hv
  cases h : coins v <;> simp [hvS, h]

theorem late_stage_fresh (cfg : Config) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n))
    (f : List (Fin n × (Fin cfg.groups × Fin cfg.shifts)) → ℝ) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).expect (fun P =>
      (Reference.ownerLaw n cfg).expect (fun owners => f (lateStage cfg S ⟨P, owners⟩))) =
    (Early.Sampling.marked (fun _ : Fin n =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos) p hp hp1 S.toList).expect f := by
  calc
    _ = (Law.family n (fun _ => Law.coin p hp hp1)).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners => f (lateStage cfg S ⟨S.filter (fun v => coins v = true), owners⟩))) := by
      have h := Law.family_subset p hp hp1 (members S) (members_nodup S) (fun P =>
        (Reference.ownerLaw n cfg).expect (fun owners => f (lateStage cfg S ⟨P, owners⟩)))
      simpa only [members_toFinset] using h.symm
    _ = (Law.family n (fun _ => Law.coin p hp hp1)).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners => f (Early.Sampling.ownedSubset S.toList coins owners))) := by
      simp_rw [lateStage_filter]
    _ = _ := Early.Sampling.family_ownedSubset (fun _ : Fin n => Law.coin p hp hp1)
      (fun _ => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)
      p hp hp1 S.toList (Finset.nodup_toList S) (fun _ _ => rfl) f

theorem marked_one_allOwners (C : Late.Config) (vertices : List (Fin n))
    (f : C.Stage n → ℝ) :
    (Early.Sampling.marked (fun _ : Fin n => C.owner) 1 (by norm_num) le_rfl vertices).expect f =
      (C.allOwners vertices).expect f := by
  induction vertices generalizing f with
  | nil => simp [Early.Sampling.marked, Late.Config.allOwners]
  | cons v vertices ih =>
      simp only [Early.Sampling.marked, Late.Config.allOwners, Law.expect_bind, Law.expect_coin,
        sub_self, zero_mul, one_mul, zero_add, ↓reduceIte, Law.expect_map]
      apply congrArg C.owner.expect
      funext o
      exact ih (fun rest => f ((v, o) :: rest))

theorem late_stage_all (cfg : Config) (hn : 0 < n) (S : Finset (Fin n))
    (f : (actualLateConfig n hn cfg).Stage n → ℝ) :
    (Reference.ownerLaw n cfg).expect (fun owners => f (lateStage cfg S ⟨S, owners⟩)) =
      ((actualLateConfig n hn cfg).allOwners S.toList).expect f := by
  let g := fun P : Finset (Fin n) => (Reference.ownerLaw n cfg).expect (fun owners => f (lateStage cfg S ⟨P, owners⟩))
  have hone := Law.subset_one_expect (members S) g
  have hset : @List.toFinset (Fin n) (Classical.decEq (Fin n)) (members S) = S := by
    ext v
    simp
  rw [hset] at hone
  calc
    _ = (Law.subset (fun _ : Fin n => (1 : ℝ)) (fun _ => by norm_num) (fun _ => le_rfl) (members S)).expect g :=
      hone.symm
    _ = _ := (late_stage_fresh cfg 1 (by norm_num) le_rfl S f).trans
      (marked_one_allOwners (actualLateConfig n hn cfg) S.toList f)

theorem lateStage_pivots (cfg : Config) (S : Finset (Fin n)) (choice : Reference.Choice n cfg)
    (hP : choice.pivots ⊆ S) : Early.Sampling.pivots (lateStage cfg S choice) = choice.pivots := by
  rw [lateStage, Early.Sampling.ownedSubset_pivots]
  ext v
  simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_toList, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hP h, h⟩⟩

theorem lateStage_owner (cfg : Config) (S : Finset (Fin n)) (choice : Reference.Choice n cfg)
    (hP : choice.pivots ⊆ S) (p : Fin n) (hp : p ∈ choice.pivots)
    (fallback : Fin cfg.groups × Fin cfg.shifts) :
    Early.Sampling.ownerFor fallback (lateStage cfg S choice) p = choice.owners p :=
  Early.Sampling.ownedSubset_owner S.toList (Finset.nodup_toList S) _ _ fallback p
    (by rwa [← lateStage_pivots cfg S choice hP] at hp)

end

end StreamingReachability.Hopset

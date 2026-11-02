module

public import StreamingSSSP.Core.BatchStatistics
public import StreamingSSSP.Core.SharedOutcome
public import StreamingSSSP.Core.GlobalCharges

@[expose] public section

namespace StreamingSSSP.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

noncomputable def stepWork (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (old : States n nb nq) (k : Fin nq × Fin nb) : ℕ :=
  if r ≤ (c.searches.get k.1).radius then
    (SparseDriver.searchBlock hn (SparseDriver.ofCatalog c k.1) stored input r k.2
      (RecordMap.get Global.emptyBlock (old.get k.1).cache k.2)).reservations else 0

theorem job_key_eq (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache)
    {a b : Shared.Job n nb nq} (ha : a ∈ jobs c r old) (hb : b ∈ jobs c r old)
    (he : key a = key b) : a = b := by
  have h1 := job_canonical c r old hu ha
  have h2 := job_canonical c r old hu hb
  obtain ⟨hs, hi⟩ := Prod.mk.inj he
  have hc : canonical old a.searchId a.blockId = canonical old b.searchId b.blockId := by rw [hs, hi]
  exact h1.trans (hc.trans h2.symm)

theorem job_key_nodup (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) :
    ((jobs c r old).map key).Nodup :=
  List.Nodup.map_on (fun a ha b hb he => job_key_eq c r old hu ha hb he) (List.nodup_dedup _)

theorem job_work (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (r : ℕ) (old : States n nb nq) (hu : ∀ j, RecordMap.Unique (old.get j).cache)
    {job : Shared.Job n nb nq} (hj : job ∈ jobs c r old) :
    (Shared.Engine.referenceOutcome hn c stored input r job).reservations =
      stepWork hn c stored input r old (key job) := by
  obtain ⟨bs, hm, hnex, hsrc, _, _, _, ha⟩ := job_origin c r old hj
  have hg := RecordMap.get_mem Global.emptyBlock (old.get job.searchId).cache (hu _) hm
  unfold stepWork key
  rw [ite_eq_left ha, hg, SparseDriver.searchBlock, ite_eq_left hnex]
  simp only [SparseDriver.ofCatalog]
  unfold Shared.Engine.referenceOutcome
  rw [hsrc]

theorem reserve_round (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (x r : ℕ) (old : States n nb nq) (hu : ∀ j, RecordMap.Unique (old.get j).cache)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    reserve (round hn c stored input x r old).states =
      reserve old + ∑ j : Fin nq, ∑ i : Fin nb, stepWork hn c stored input r old (j, i) := by
  unfold reserve
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [round_get hn c stored input x r old hu hx j]
  by_cases ha : r ≤ (c.searches.get j).radius
  · rw [ite_eq_left ha, SparseDriver.observe_round hn _ stored input r _ (hu j), Global.round_reservations]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [stepWork, ha, ↓reduceIte, Global.searchOne, SparseDriver.reference,
      SparseDriver.observe, Vector.get_ofFn]
    exact congrArg Global.BlockResult.reservations
      (SparseDriver.searchBlock_eq hn (SparseDriver.ofCatalog c j) stored input r i _).symm
  · simp [ha, stepWork]

theorem round_reservation_charge (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    reserve old + (round hn c stored input x r old).reservations ≤
      reserve (round hn c stored input x r old).states := by
  let pending := jobs c r old
  have hmem (i : Fin pending.length) : pending.get i ∈ jobs c r old := List.get_mem pending i
  have hr := Shared.Engine.run_reservations hn c stored input x r pending.get
    (fun i => (Shared.block_card_le c _ _).trans (hx _))
    (fun i => (job_origin c r old (hmem i)).choose_spec.2.2.2.1)
    (fun i => (job_origin c r old (hmem i)).choose_spec.2.2.2.2.1)
    (fun i => (job_origin c r old (hmem i)).choose_spec.2.2.2.2.2.1)
  have hinj : Function.Injective (fun i : Fin pending.length => key (pending.get i)) := by
    intro i k he
    let i' : Fin (pending.map key).length := ⟨i.val, by simpa using i.isLt⟩
    let k' : Fin (pending.map key).length := ⟨k.val, by simpa using k.isLt⟩
    have hg : (pending.map key).get i' = (pending.map key).get k' := by
      simpa only [List.get_eq_getElem, List.getElem_map] using he
    have heq : i' = k' := (job_key_nodup c r old hu).get_inj_iff.mp hg
    exact Fin.ext (congrArg (fun t : Fin (pending.map key).length => t.val) heq)
  have hsum : (∑ i : Fin pending.length,
      (Shared.Engine.referenceOutcome hn c stored input r (pending.get i)).reservations) ≤
      ∑ k : Fin nq × Fin nb, stepWork hn c stored input r old k := by
    apply Finset.sum_le_sum_of_injOn (fun i : Fin pending.length => key (pending.get i))
    · intro i _ k _ he
      exact hinj he
    · exact Finset.subset_univ _
    · intro i _
      exact (job_work hn c stored input r old hu (hmem i)).le
    · intro _ _ _
      exact Nat.zero_le _
  rw [reserve_round hn c stored input x r old hu hx]
  apply Nat.add_le_add_left
  change (Shared.Engine.runTail hn c stored input r (Nat.log 2 x + 2) (tasks pending)).reservations ≤ _
  rw [Shared.Engine.runTail_eq]
  change (Shared.Engine.run hn c stored input r (Nat.log 2 x + 2) (Shared.Engine.starting pending.get)).reservations ≤ _
  rw [hr]
  simpa only [Fintype.sum_prod_type] using hsum

theorem execute_reservation_charge (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    (execute hn c stored input x r).reservations ≤ reserve (execute hn c stored input x r).states := by
  induction r with
  | zero =>
      simp [execute, reserve, initial, SparseDriver.initial, SparseDriver.observe,
        Global.reservationCount, Global.emptyBlock, RecordMap.get]
  | succ r ih =>
      have hu : ∀ j, RecordMap.Unique ((execute hn c stored input x r).states.get j).cache :=
        fun j => (execute_shape hn c stored input x r hx j).unique
      have hs := round_reservation_charge hn c stored input x r
        (execute hn c stored input x r).states hu hx
      change (execute hn c stored input x r).reservations +
        (round hn c stored input x r (execute hn c stored input x r).states).reservations ≤ _
      exact (Nat.add_le_add_right ih _).trans hs

theorem round_pass_bound (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (old : States n nb nq) :
    n * (round hn c stored input x r old).passes ≤
      n * (Nat.log 2 x + 3) + 2 * (round hn c stored input x r old).reservations := by
  have h := Shared.Engine.run_scan_bound hn c stored input r (Nat.log 2 x + 2) (tasks (jobs c r old))
  simp only [round, Shared.Engine.runTail_eq] at *
  nlinarith only [h]

theorem execute_pass_bound (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) :
    n * (execute hn c stored input x r).passes ≤
      n * r * (Nat.log 2 x + 3) + 2 * (execute hn c stored input x r).reservations := by
  induction r with
  | zero => simp [execute]
  | succ r ih =>
      have hs := round_pass_bound hn c stored input x r (execute hn c stored input x r).states
      simp only [execute] at *
      nlinarith only [ih, hs]

theorem core_pass_bound (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hR : ∀ j, (c.searches.get j).radius ≤ R) :
    n * (execute hn c stored input x (R + 1)).passes ≤
      n * (R + 1) * (Nat.log 2 x + 3) + 16 * x * Nrec c stored input := by
  have h := execute_pass_bound hn c stored input x (R + 1)
  have hr := execute_reservation_charge hn c stored input x (R + 1) hx
  have hb := final_reservation_bound hn c stored input x R hs hp hA hx hR
  nlinarith only [h, hr, hb]

end StreamingSSSP.Core.BatchDriver

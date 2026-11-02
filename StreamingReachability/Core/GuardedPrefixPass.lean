module

public import StreamingReachability.Core.GuardedWorkCharge

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.BatchDriver

variable {n nb ns nq : ℕ}

theorem jobs_charged (c : Shared.Catalog n nb ns nq) (x r : ℕ) (old : States n nb nq)
    (registry : RecordGuard.Registry n nq) (hshape : ∀ j, SparseDriver.Shape (old.get j))
    (hcover : GuardedDriver.Cover registry old)
    (hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (old.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (old.get j).cache i).known ⊆
        SparseLabels.support (old.get j).labels ∩ c.blocks.get i)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ i : Fin (jobs c r old).length,
      GuardedEngine.Charged c x registry.seen (key ((jobs c r old).get i))
        ((tasks (jobs c r old)).get i) := by
  intro i
  let job := (jobs c r old).get i
  have hr := jobs_registered c r old registry hshape hcover hknown i
  obtain ⟨bs, hm, _, hsrc, ht, _, hspent, _⟩ := job_origin c r old (List.get_mem _ i)
  rw [tasks, Vector.get_ofFn] at hr ⊢
  change GuardedEngine.Charged c x registry.seen (key job) (.active job)
  have hlen : 0 < job.sources.length := by
    rw [hsrc]
    exact (hshape job.searchId).active _ hm
  have hpos : 0 < (GuardedEngine.incidenceKeys c registry.seen (key job)).card := by
    apply lt_of_lt_of_le _ (Finset.card_le_card hr.2.2)
    rw [← SparseLabels.length_eq_card _ hr.2.1]
    exact hlen
  have ht' : job.threshold = 1 := ht
  have hs' : job.spentReservations = 0 := hspent
  refine ⟨(Shared.block_card_le c job.searchId job.blockId).trans (hx _), ?_, ?_⟩
  · simp only [hs', ht', Nat.zero_add, Nat.mul_one]
  · rw [ht']
    omega

end StreamingReachability.Core.BatchDriver

namespace StreamingReachability.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

theorem Blocks.charged {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ i, GuardedEngine.Charged c x b.registry.seen (p.origin i) (b.result.tasks.get i) := by
  have hf := p.facts hs hp hA hx
  have hpost := GuardedEngine.runAux_task_post hn c stored input budget p.rounds b.phases
    (fun reg i task => GuardedEngine.Registered c reg.seen (p.origin i) task ∧
      GuardedEngine.Charged c x reg.seen (p.origin i) task)
    (fun old next hm i task h =>
      ⟨GuardedEngine.registered_mono c hm _ _ h.1, GuardedEngine.charged_mono c x hm _ _ h.2⟩)
    (fun i job f old next task h he =>
      ⟨GuardedEngine.evaluate_registered c budget p.rounds _ job f old next task h.1 he,
        GuardedEngine.evaluate_charged c budget p.rounds x _ job f old next task h.1 h.2 he⟩)
    (BatchDriver.tasks p.jobs) p.registry b.registry 0 0 0 b.result
    (fun i => ⟨BatchDriver.jobs_registered c p.rounds p.state.states p.registry hf.shape hf.cover hf.known i,
      BatchDriver.jobs_charged c x p.rounds p.state.states p.registry hf.shape hf.cover hf.known hx i⟩) b.executed
  exact fun i => (hpost i).2

theorem Blocks.work_budget {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    b.result.reservations ≤ 4 * x * budget ∧
      Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active b.result.tasks) ≤ 2 * x * budget := by
  have hf := p.facts hs hp hA hx
  have hw := GuardedEngine.workSum_budget c x budget b.registry (b.valid hs hp hA hx) p.origin
    (BatchDriver.job_origin_injective c p.rounds p.state.states (fun j => (hf.shape j).unique))
    b.result.tasks (b.charged hs hp hA hx)
  have hstart : Shared.Engine.workSum (BatchDriver.tasks p.jobs) = 0 := by
    unfold Shared.Engine.workSum
    apply Finset.sum_eq_zero
    intro i _
    rw [BatchDriver.tasks, Vector.get_ofFn]
    change (p.jobs.get i).spentReservations = 0
    obtain ⟨_, _, _, _, _, _, hspent, _⟩ :=
      BatchDriver.job_origin c p.rounds p.state.states (List.get_mem p.jobs i)
    exact hspent
  have he : b.result = Shared.Engine.run hn c stored input p.rounds b.phases (BatchDriver.tasks p.jobs) := by
    rw [GuardedEngine.run_erases hn c stored input budget p.rounds b.phases _
      p.registry b.registry b.result b.executed, Shared.Engine.runTail_eq]
  have hwork := Shared.Engine.run_work hn c stored input p.rounds b.phases (BatchDriver.tasks p.jobs)
  rw [← he, hstart, Nat.zero_add] at hwork
  exact ⟨hwork ▸ hw.1, hw.2⟩

theorem Boundary.reservation_budget (p : Boundary hn c stored input budget x)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    p.state.reservations ≤ 8 * x * budget := by
  have hf := p.facts hs hp hA hx
  have he := GuardedDriver.prefix_state_eq hn c stored input budget x p.rounds
    p.first p.registry p.state p.executed
  have hbase := BatchDriver.execute_reservation_charge hn c stored input x p.rounds hx
  rw [← he] at hbase
  have hknown (j : Fin nq) (i : Fin nb) :
      (RecordMap.get Global.emptyBlock (p.state.states.get j).cache i).known.length ≤
        (GuardedEngine.incidenceKeys c p.registry.seen (j, i)).card := by
    rw [SparseLabels.length_eq_card _ (hf.known j i).1]
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hl, hb⟩ := Finset.mem_inter.mp ((hf.known j i).2 hv)
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.cover j v hl⟩, hb⟩
  have hpoint (j : Fin nq) (i : Fin nb) :
      (RecordMap.get Global.emptyBlock (p.state.states.get j).cache i).reservations ≤
        8 * x * (GuardedEngine.incidenceKeys c p.registry.seen (j, i)).card := by
    have hg := (BatchDriver.execute_global_invariant hn c stored input x p.rounds hs hp hA hx j).2 i
    rw [← he] at hg
    have hb := hg.reservation_bound
    have hc := ScheduleCharge.searches_le _ hg.charge_valid
    have hi := hg.insertion_count
    have hl := SparseLabels.length_eq_card _ hg.known_unique
    simp only [SparseDriver.observe, Vector.get_ofFn, Shared.referenceProblem] at hb hc hi hl
    have hm := Nat.mul_le_mul_right
      ((RecordMap.get Global.emptyBlock (p.state.states.get j).cache i).charge.insertions +
        (RecordMap.get Global.emptyBlock (p.state.states.get j).cache i).charge.searches)
      (Nat.mul_le_mul_left 4 ((Shared.block_card_le c j i).trans (hx i)))
    have hlen := hknown j i
    nlinarith only [hb, hc, hi, hl, hm, hlen]
  have hsum : BatchDriver.reserve p.state.states ≤ 8 * x * RecordGuard.weight c p.registry.seen := by
    unfold BatchDriver.reserve Global.reservationCount
    simp only [SparseDriver.observe, Vector.get_ofFn]
    calc
      _ ≤ ∑ j : Fin nq, ∑ i : Fin nb,
          8 * x * (GuardedEngine.incidenceKeys c p.registry.seen (j, i)).card :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hpoint j i))
      _ = 8 * x * ∑ k : Fin nq × Fin nb, (GuardedEngine.incidenceKeys c p.registry.seen k).card := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => (Finset.mul_sum _ _ _).symm)
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        rw [Fintype.sum_prod_type, RecordGuard.weight_sections]
        exact Finset.sum_le_sum (fun j _ => Nat.le_add_left _ _)
  exact hbase.trans (hsum.trans (Nat.mul_le_mul_left _ (hf.valid.1 ▸ hf.valid.2)))

theorem Boundary.pass_budget (p : Boundary hn c stored input budget x)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    n * p.state.passes ≤ n * p.rounds * (Nat.log 2 x + 3) + 16 * x * budget := by
  have he := GuardedDriver.prefix_state_eq hn c stored input budget x p.rounds
    p.first p.registry p.state p.executed
  have hpasses := BatchDriver.execute_pass_bound hn c stored input x p.rounds
  rw [← he] at hpasses
  have hreserve := p.reservation_budget hs hp hA hx
  nlinarith only [hpasses, hreserve]

theorem Blocks.pass_budget {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    n * b.result.scans ≤ n * b.phases + 8 * x * budget := by
  have he : b.result = Shared.Engine.run hn c stored input p.rounds b.phases (BatchDriver.tasks p.jobs) := by
    rw [GuardedEngine.run_erases hn c stored input budget p.rounds b.phases _
      p.registry b.registry b.result b.executed, Shared.Engine.runTail_eq]
  have hscan := Shared.Engine.run_scan_bound hn c stored input p.rounds b.phases (BatchDriver.tasks p.jobs)
  rw [← he] at hscan
  have hreserve := (b.work_budget hs hp hA hx).1
  nlinarith only [hscan, hreserve]

end StreamingReachability.Core.Live

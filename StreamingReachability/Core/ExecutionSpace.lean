module

public import StreamingReachability.Core.ExecutionPoints

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

theorem Boundary.facts (p : Boundary hn c stored input budget x)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    GuardedDriver.PrefixFacts c budget p.rounds p.registry p.state :=
  GuardedDriver.prefix_facts hn c stored input budget x p.rounds hs hp hA hx
    p.first p.registry p.state p.initialized p.executed

theorem Boundary.cells_le (p : Boundary hn c stored input budget x)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    p.cells ≤ 4 + 16 * budget :=
  GuardedDriver.prefix_space hn c stored input budget x p.rounds hs hp hA hx
    p.first p.registry p.state p.initialized p.executed

theorem Blocks.mono {p : Boundary hn c stored input budget x} (b : Blocks p) :
    p.registry.seen ⊆ b.registry.seen :=
  GuardedEngine.run_mono hn c stored input budget p.rounds b.phases _ p.registry b.registry b.result b.executed

theorem Blocks.valid {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    RecordGuard.Valid c budget b.registry :=
  GuardedEngine.runAux_post hn c stored input budget p.rounds b.phases (RecordGuard.Valid c budget)
    (fun job f old next task hv he => GuardedEngine.evaluate_valid c budget p.rounds job f old next task hv he)
    _ p.registry b.registry 0 0 0 b.result (p.facts hs hp hA hx).valid b.executed

theorem Blocks.registered {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ i, GuardedEngine.Registered c b.registry.seen (p.origin i) (b.result.tasks.get i) := by
  have hf := p.facts hs hp hA hx
  exact GuardedEngine.runAux_registered hn c stored input budget p.rounds b.phases p.origin
    _ p.registry b.registry 0 0 0 b.result
    (BatchDriver.jobs_registered c p.rounds p.state.states p.registry hf.shape hf.cover hf.known) b.executed

theorem Blocks.ready {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ i, Shared.Engine.Ready c x (b.result.tasks.get i) :=
  GuardedDriver.prefix_tasks_ready hn c stored input budget x p.rounds b.phases hs hp hA hx
    p.first p.registry b.registry p.state b.result p.initialized p.executed b.executed

theorem Blocks.package_active {p : Boundary hn c stored input budget x} (b : Blocks p)
    {slots : List (Fin p.jobs.length × Shared.Job n nb nq)} (hm : slots ∈ b.packages)
    {slot : Fin p.jobs.length × Shared.Job n nb nq} (hs : slot ∈ slots) :
    b.result.tasks.get slot.1 = .active slot.2 := by
  have h : slot ∈ b.packages.flatten := List.mem_flatten.mpr ⟨slots, hm, hs⟩
  rw [Blocks.packages, Packing.pack_flatten] at h
  exact (Shared.Engine.active_mem b.result.tasks slot.1 slot.2).mp (List.mem_reverse.mp h)

theorem Blocks.package_unique {p : Boundary hn c stored input budget x} (b : Blocks p) :
    RecordMap.Unique b.packages.flatten := by
  rw [Blocks.packages, Packing.pack_flatten]
  simpa [RecordMap.Unique, List.map_reverse] using Shared.Engine.active_unique b.result.tasks

theorem Blocks.cells_le {p : Boundary hn c stored input budget x} (b : Blocks p)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    b.cells ≤ 4 + 64 * budget := by
  have hf := p.facts hs hp hA hx
  have hv := b.valid hs hp hA hx
  have hi := BatchDriver.job_origin_injective c p.rounds p.state.states (fun j => (hf.shape j).unique)
  have hstart := GuardedEngine.tasksCells_bound c budget p.registry hf.valid p.origin hi _
    hf.slots (BatchDriver.jobs_registered c p.rounds p.state.states p.registry hf.shape hf.cover hf.known)
  have hcurrent := GuardedEngine.tasksCells_bound c budget b.registry hv p.origin hi _
    hf.slots (b.registered hs hp hA hx)
  have hstate := GuardedDriver.registered_state_space c budget p.registry p.state.states
    hf.valid hf.shape hf.cover hf.known
  have hreg := RecordGuard.registry_cells c budget b.registry hv
  have hplan := GuardedEngine.planCells_bound c b.result.tasks
  have hslots : p.jobs.length ≤ budget := hf.slots
  have hstart' : GuardedEngine.tasksCells (BatchDriver.tasks p.jobs) ≤ 14 * budget := hstart
  unfold Blocks.cells registryCells
  omega

theorem Packs.mono {p : Boundary hn c stored input budget x} {b : Blocks p} (s : Packs b) :
    b.registry.seen ⊆ s.registry.seen :=
  GuardedEngine.packs_post hn c stored input budget p.rounds (fun reg => b.registry.seen ⊆ reg.seen)
    (fun job f old next task hp he => hp.trans (GuardedEngine.evaluate_mono c budget p.rounds job f old next task he))
    _ b.registry s.registry s.result (Finset.Subset.refl _) s.executed

theorem Packs.valid {p : Boundary hn c stored input budget x} {b : Blocks p} (s : Packs b)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    RecordGuard.Valid c budget s.registry :=
  GuardedEngine.packs_valid hn c stored input budget p.rounds _ b.registry s.registry s.result
    (b.valid hs hp hA hx) s.executed

theorem Packs.registered {p : Boundary hn c stored input budget x} {b : Blocks p} (s : Packs b)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ pair ∈ s.result.updates, GuardedEngine.Registered c s.registry.seen (p.origin pair.1) pair.2 := by
  apply GuardedEngine.packs_registered hn c stored input budget p.rounds p.origin
    _ b.registry s.registry s.result _ s.executed
  intro slot hm
  obtain ⟨slots, hslots, hslot⟩ := List.mem_flatten.mp hm
  have he := b.package_active (List.mem_of_mem_take hslots) hslot
  simpa only [he] using b.registered hs hp hA hx slot.1

theorem Packs.unique_updates {p : Boundary hn c stored input budget x} {b : Blocks p} (s : Packs b) :
    RecordMap.Unique s.result.updates := by
  apply GuardedEngine.packs_unique hn c stored input budget p.rounds _ b.registry s.registry s.result _ s.executed
  exact ((List.take_sublist s.count b.packages).flatten.map Prod.fst).nodup b.package_unique

theorem Packs.cells_le {p : Boundary hn c stored input budget x} {b : Blocks p} (s : Packs b)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    s.cells ≤ 6 + 103 * budget := by
  have hf := p.facts hs hp hA hx
  have hb := b.cells_le hs hp hA hx
  have hv := s.valid hs hp hA hx
  have hr := RecordGuard.registry_cells c budget s.registry hv
  have hu := GuardedEngine.updatesCells_bound c budget s.registry hv p.origin
    (BatchDriver.job_origin_injective c p.rounds p.state.states (fun j => (hf.shape j).unique))
    s.result.updates s.unique_updates hf.slots (s.registered hs hp hA hx)
  have hslots : p.jobs.length ≤ budget := hf.slots
  unfold Packs.cells registryCells
  omega

theorem Processing.valid {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    (t : Processing s)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    RecordGuard.Valid c budget t.registry :=
  GuardedEngine.process_valid hn c budget p.rounds _ _ s.registry t.registry t.updates
    (s.valid hs hp hA hx) t.executed

theorem Processing.registered {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    (t : Processing s)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ pair ∈ t.updates, GuardedEngine.Registered c t.registry.seen (p.origin pair.1) pair.2 := by
  apply GuardedEngine.process_registered hn c budget p.rounds p.origin _ _ s.registry t.registry t.updates _ t.executed
  intro slot hm
  have he := b.package_active t.member (List.mem_of_mem_take hm)
  have hr := GuardedEngine.registered_mono c s.mono (p.origin slot.1) _ (b.registered hs hp hA hx slot.1)
  simpa only [he] using hr

theorem Processing.unique_updates {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    (t : Processing s) : RecordMap.Unique t.updates := by
  apply GuardedEngine.process_unique hn c budget p.rounds _ _ s.registry t.registry t.updates _ t.executed
  have hsub : t.slots.Sublist b.packages.flatten := List.sublist_flatten_of_mem t.member
  have hu : RecordMap.Unique t.slots := (hsub.map Prod.fst).nodup b.package_unique
  unfold RecordMap.Unique at hu ⊢
  rw [List.map_take]
  exact hu.take

theorem Processing.cells_le {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    (t : Processing s)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    t.cells ≤ 8 + 142 * budget := by
  have hf := p.facts hs hp hA hx
  have hb := s.cells_le hs hp hA hx
  have hv := t.valid hs hp hA hx
  have hr := RecordGuard.registry_cells c budget t.registry hv
  have hu := GuardedEngine.updatesCells_bound c budget t.registry hv p.origin
    (BatchDriver.job_origin_injective c p.rounds p.state.states (fun j => (hf.shape j).unique))
    t.updates t.unique_updates hf.slots (t.registered hs hp hA hx)
  have hslots : p.jobs.length ≤ budget := hf.slots
  unfold Processing.cells registryCells
  omega

end StreamingReachability.Core.Live

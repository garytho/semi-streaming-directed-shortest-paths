module

public import StreamingSSSP.Core.ExecutionSpace
public import StreamingSSSP.Core.TaskPosts
public import StreamingSSSP.Core.WordBounds
public import StreamingSSSP.Core.InterfaceCorrect

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingSSSP.Core.WordBounds

open StoredEdges

variable {n nb ns nq : ℕ}

theorem sparse_vector (labels : SparseLabels.Labels (Fin n)) (K : ℕ)
    (hu : (labels.map Prod.fst).Nodup) (hb : ∀ pair ∈ labels, pair.2 ≤ (K : Distance)) :
    ∀ v, Bounded K ((SparseLabels.vector labels).get v) := by
  intro v
  rw [SparseLabels.vector_get]
  by_cases hv : v ∈ SparseLabels.support labels
  · obtain ⟨pair, hp, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    right
    rw [← he, BatchAPI.labels_get_mem labels hu hp]
    exact hb pair hp
  · exact Or.inl (SparseLabels.get_eq_top_of_not_mem labels hv)

def SourceBound (K : ℕ) : Shared.Engine.Task n nb nq → Prop
  | .active job => ∀ v, Bounded K ((SparseLabels.vector job.sources).get v)
  | .finished _ => True

theorem evaluate_source_bound (c : Shared.Catalog n nb ns nq) (budget r K : ℕ)
    (job : Shared.Job n nb nq) (f : DistanceArray n) (old next : RecordGuard.Registry n nq)
    (task : Shared.Engine.Task n nb nq)
    (hb : SourceBound K (.active job))
    (he : GuardedEngine.evaluate c budget r job f old = .ok (next, task)) : SourceBound K task := by
  rw [GuardedEngine.evaluate_erases c budget r job f old next task he]
  unfold Shared.Engine.evaluate
  dsimp only
  split_ifs
  · trivial
  · simpa only [SourceBound, Shared.double] using hb

theorem bounded_payload_bits (A R n W : ℕ) {d : Distance} (hd : Bounded (A * R + n * W) d) :
    bitLength (d.untopD 0) ≤ bitLength (n + A * R + n * W) := by
  by_cases ht : d = ⊤
  · rw [ht]
    apply bitLength_mono
    simp
  · exact finite_label_bits A R n W hd ht

end StreamingSSSP.Core.WordBounds

namespace StreamingSSSP.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

theorem Boundary.known_words (p : Boundary hn c stored input budget x) (R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hclock : p.rounds ≤ R)
    (j : Fin nq) (i : Fin nb) :
    ∀ pair ∈ (RecordMap.get Global.emptyBlock (p.state.states.get j).cache i).known,
      pair.2 ≤ ((c.scale * R : ℕ) : Distance) := by
  have he := GuardedDriver.prefix_state_eq hn c stored input budget x p.rounds p.first p.registry p.state p.executed
  have hg := BatchDriver.execute_global_invariant hn c stored input x p.rounds hs hp hA hx j
  rw [← he] at hg
  let bs := (SparseDriver.observe (p.state.states.get j)).blocks.get i
  have hb : Global.BlockInvariant (Shared.referenceProblem c j)
      ((stored ++ input).filterMap (Shared.view c j)) (p.state.states.get j).settled
      (min p.rounds ((c.searches.get j).radius + 1)) i bs := hg.2 i
  intro pair hpair
  have hm : pair ∈ bs.known := by simpa only [bs, SparseDriver.observe, Vector.get_ofFn] using hpair
  have hv : pair.1 ∈ SparseLabels.support bs.known :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, hm, rfl⟩)
  have hnum := Global.known_bound (Shared.referenceProblem c j) _
    hg.1 i bs hb hv
  rw [← BatchAPI.labels_get_mem bs.known hb.known_unique hm, hb.known_exact pair.1 hv]
  exact hnum.trans (WithTop.coe_le_coe.mpr (Nat.mul_le_mul_left c.scale
    ((Nat.min_le_left _ _).trans hclock)))

theorem Boundary.initial_source_words (p : Boundary hn c stored input budget x) (R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hclock : p.rounds ≤ R) :
    ∀ i, WordBounds.SourceBound (c.scale * R) ((BatchDriver.tasks p.jobs).get i) := by
  have hf := p.facts hs hp hA hx
  intro i
  dsimp only [Boundary.jobs] at i ⊢
  let job := (BatchDriver.jobs c p.rounds p.state.states).get i
  have hr := BatchDriver.jobs_registered c p.rounds p.state.states p.registry hf.shape hf.cover hf.known i
  rw [BatchDriver.tasks, Vector.get_ofFn] at hr ⊢
  apply WordBounds.sparse_vector _ _ hr.2.1
  intro pair hm
  obtain ⟨bs, hmem, _, hsrc, _, _, _, _⟩ := BatchDriver.job_origin c p.rounds p.state.states
    (List.get_mem (BatchDriver.jobs c p.rounds p.state.states) i)
  have hget := RecordMap.get_mem Global.emptyBlock (p.state.states.get job.searchId).cache
    (hf.shape job.searchId).unique hmem
  have hp' : pair ∈ (RecordMap.get Global.emptyBlock (p.state.states.get job.searchId).cache job.blockId).known := by
    rw [hget, ← hsrc]
    exact hm
  exact p.known_words R hs hp hA hx hclock job.searchId job.blockId pair hp'

theorem Blocks.source_words {p : Boundary hn c stored input budget x} (b : Blocks p) (R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hclock : p.rounds ≤ R) :
    ∀ i, WordBounds.SourceBound (c.scale * R) (b.result.tasks.get i) :=
  GuardedEngine.runAux_task_post hn c stored input budget p.rounds b.phases
    (fun _ _ task => WordBounds.SourceBound (c.scale * R) task)
    (fun _ _ _ _ _ h => h)
    (fun _ job f old next task h he =>
      WordBounds.evaluate_source_bound c budget p.rounds (c.scale * R) job f old next task h he)
    _ p.registry b.registry 0 0 0 b.result (p.initial_source_words R hs hp hA hx hclock) b.executed

theorem stored_weights (c : Shared.Catalog n nb ns nq) (jobs : List (Shared.Job n nb nq))
    (stored input : List (Edge n)) (W : ℕ)
    (hs : ∀ e ∈ stored, e.weight ≤ W) (hp : ∀ e ∈ input, e.weight ≤ W)
    {w : Shared.Work n nb nq} (hw : w ∈ (Shared.scanPack c jobs stored input).state) :
    ∀ e ∈ Shared.storedEdges hn w, e.weight ≤ W := by
  rw [Shared.storedEdges_eq hn c jobs stored input hw, ViewedSkeleton.build_eq]
  apply WordBounds.skeleton_weights
  intro e he
  obtain ⟨raw, hr, hv⟩ := List.mem_filterMap.mp he
  rw [(Shared.view_properties c w.job.searchId raw e hv).2.2]
  rcases List.mem_append.mp hr with hr | hr
  · exact hs raw hr
  · exact hp raw hr

theorem Blocks.bf_words {p : Boundary hn c stored input budget x} (b : Blocks p) (R W : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hclock : p.rounds ≤ R)
    (hsW : ∀ e ∈ stored, e.weight ≤ W) (hpW : ∀ e ∈ input, e.weight ≤ W)
    (slots : List (Fin p.jobs.length × Shared.Job n nb nq)) (hslots : slots ∈ b.packages)
    {slot : Fin p.jobs.length × Shared.Job n nb nq} (hslot : slot ∈ slots)
    {w : Shared.Work n nb nq} (hw : w ∈ (Shared.scanPack c (slots.map Prod.snd) stored input).state)
    (round scanned : ℕ) (hround : round < n) (v : Fin n) :
    WordBounds.Bounded (c.scale * R + n * W)
      ((relaxEdges ((Shared.storedEdges hn w).take scanned)
        (runRounds (Shared.storedEdges hn w) round (SparseLabels.vector slot.2.sources))
        (runRounds (Shared.storedEdges hn w) round (SparseLabels.vector slot.2.sources))).get v) := by
  have hi := b.source_words R hs hp hA hx hclock slot.1
  rw [b.package_active hslots hslot] at hi
  have hweights := stored_weights (hn := hn) c _ stored input W hsW hpW hw
  have hRounds := WordBounds.rounds_bounded (Shared.storedEdges hn w) (SparseLabels.vector slot.2.sources)
    (c.scale * R) W round hi hweights
  have hrelax := WordBounds.relax_bounded ((Shared.storedEdges hn w).take scanned)
    (runRounds (Shared.storedEdges hn w) round (SparseLabels.vector slot.2.sources))
    (runRounds (Shared.storedEdges hn w) round (SparseLabels.vector slot.2.sources))
    (c.scale * R + round * W) W hRounds
    (fun u => WordBounds.bounded_mono (Nat.le_add_right _ _) (hRounds u))
    (fun e he => hweights e (List.mem_of_mem_take he)) v
  apply WordBounds.bounded_mono _ hrelax
  have hmul : round * W + W ≤ n * W := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right W (show round + 1 ≤ n by omega)
  omega

theorem Blocks.bf_payload_bits {p : Boundary hn c stored input budget x} (b : Blocks p) (R W : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hclock : p.rounds ≤ R)
    (hsW : ∀ e ∈ stored, e.weight ≤ W) (hpW : ∀ e ∈ input, e.weight ≤ W)
    (slots : List (Fin p.jobs.length × Shared.Job n nb nq)) (hslots : slots ∈ b.packages)
    {slot : Fin p.jobs.length × Shared.Job n nb nq} (hslot : slot ∈ slots)
    {w : Shared.Work n nb nq} (hw : w ∈ (Shared.scanPack c (slots.map Prod.snd) stored input).state)
    (round scanned : ℕ) (hround : round < n) (v : Fin n) :
    WordBounds.bitLength
      (((relaxEdges ((Shared.storedEdges hn w).take scanned)
        (runRounds (Shared.storedEdges hn w) round (SparseLabels.vector slot.2.sources))
        (runRounds (Shared.storedEdges hn w) round (SparseLabels.vector slot.2.sources))).get v).untopD 0) ≤
      WordBounds.bitLength (n + c.scale * R + n * W) :=
  WordBounds.bounded_payload_bits c.scale R n W
    (b.bf_words R W hs hp hA hx hclock hsW hpW slots hslots hslot hw round scanned hround v)

end StreamingSSSP.Core.Live

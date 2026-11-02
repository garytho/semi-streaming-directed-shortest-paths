module

public import StreamingSSSP.Core.ExecutionSpace

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingSSSP.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

def scanRows {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    (t : Processing s) (storedCount inputCount : ℕ) : List (Shared.Work n nb nq) :=
  (Shared.scanPack c (t.slots.map Prod.snd) (stored.take storedCount) (input.take inputCount)).state

theorem scanRows_invariant {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    (t : Processing s) (storedCount inputCount : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hspace : 2 * x * x ≤ n) :
    Shared.Invariant c n (scanRows t storedCount inputCount) := by
  have hr := b.ready hs hp hA hx
  have hc : ∀ slot ∈ Shared.Engine.active b.result.tasks, Shared.capacity c slot.2 ≤ n :=
    fun _ hm => (Shared.Engine.ready_capacity c x b.result.tasks hr hspace hm).2
  have hv : ∀ job ∈ t.slots.map Prod.snd, Shared.Valid c job := by
    intro job hm
    obtain ⟨slot, hslot, rfl⟩ := List.mem_map.mp hm
    exact (Shared.Engine.ready_capacity c x b.result.tasks hr hspace
      ((Shared.Engine.active_mem b.result.tasks slot.1 slot.2).mpr (b.package_active t.member hslot))).1
  have hload : Packing.load (Shared.capacity c) (t.slots.map Prod.snd) ≤ n := by
    have hpack := Packing.pack_bounded
      (J := Fin p.jobs.length × Shared.Job n nb nq) n (fun slot => Shared.capacity c slot.2)
      (Shared.Engine.active b.result.tasks) hc
    have hm : t.slots ∈ Packing.pack n (fun slot : Fin p.jobs.length × Shared.Job n nb nq =>
        Shared.capacity c slot.2) (Shared.Engine.active b.result.tasks) := t.member
    have hb := hpack t.slots hm
    change ((t.slots.map Prod.snd).map (Shared.capacity c)).sum ≤ n
    rw [List.map_map]
    exact hb
  have hi := Shared.initial_invariant c (t.slots.map Prod.snd) n hv hload
  rw [scanRows, Shared.scanPack, Streaming.readPass_state]
  exact Shared.fold_invariant c n (input.take inputCount) _
    (Shared.fold_invariant c n (stored.take storedCount) _ hi)

structure Scratch {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b} (t : Processing s) where
  storedCount : ℕ
  inputCount : ℕ
  work : Shared.Work n nb nq
  work_mem : work ∈ scanRows t storedCount inputCount
  row : Skeleton.Row n
  row_mem : row ∈ work.rows
  slot : Fin p.jobs.length × Shared.Job n nb nq
  slot_mem : slot ∈ t.slots
  raw : Edge n
  key : ℕ
  reservedCount : ℕ
  registry : RecordGuard.Registry n nq
  reserved : RecordGuard.reserveMany c budget
    (List.take reservedCount (((found (Shared.block c slot.2.searchId slot.2.blockId) (SparseLabels.support slot.2.sources)
        (StoredSearch.run (Shared.storedEdges hn work) (SparseLabels.vector slot.2.sources)).get
        (c.scale * p.rounds)).sort (· ≤ ·)).map fun v => (slot.2.searchId, v)))
      t.registry = .ok registry

def Scratch.found {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    {t : Processing s} (w : Scratch t) : Finset (Fin n) :=
  Core.found (Shared.block c w.slot.2.searchId w.slot.2.blockId) (SparseLabels.support w.slot.2.sources)
    (StoredSearch.run (Shared.storedEdges hn w.work) (SparseLabels.vector w.slot.2.sources)).get
    (c.scale * p.rounds)

/-- Includes simultaneously old/new scan rows, the stored BF edge list, its
three possible array references, and the per-row/set/sorting temporaries. -/
def Scratch.cells {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    {t : Processing s} (w : Scratch t) : ℕ :=
  t.cells + registryCells w.registry +
    Shared.cells (scanRows t w.storedCount w.inputCount) +
    Shared.cells (Shared.update c (scanRows t w.storedCount w.inputCount) w.raw) +
    3 * (Shared.storedEdges hn w.work).length + 3 * n +
    2 * ((Shared.block c w.slot.2.searchId w.slot.2.blockId).card +
      (SparseLabels.support w.slot.2.sources).card + w.found.card) +
    5 * w.found.card + 2 * TopRows.transitionCells n w.work.job.threshold w.key w.row.kept + 12

theorem Scratch.cells_le {p : Boundary hn c stored input budget x} {b : Blocks p} {s : Packs b}
    {t : Processing s} (w : Scratch t)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hspace : 2 * x * x ≤ n) :
    w.cells ≤ 256 * (n + budget + 1) := by
  have hi := scanRows_invariant t w.storedCount w.inputCount hs hp hA hx hspace
  have hrows := Shared.cells_bound c n _ hi
  have hnew := Shared.cells_bound c n _ (Shared.update_invariant c n _ w.raw hi)
  have he := Shared.storedEdges_length hn c n _ hi w.work_mem
  have hb : (Shared.block c w.slot.2.searchId w.slot.2.blockId).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (Shared.block c w.slot.2.searchId w.slot.2.blockId)
  have hk : (SparseLabels.support w.slot.2.sources).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (SparseLabels.support w.slot.2.sources)
  have hf : w.found.card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ w.found
  have hc : Shared.capacity c w.work.job ≤ n :=
    (List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map.mpr ⟨w.work, w.work_mem, rfl⟩)).trans hi.2
  have hτ : w.work.job.threshold ≤ n :=
    (Nat.le_mul_of_pos_left _ (hi.1 w.work w.work_mem).1.1).trans hc
  have ht := TopRows.transitionCells_le n w.work.job.threshold w.key w.row.kept
    ((hi.1 w.work w.work_mem).2.2 w.row w.row_mem)
  have hv := RecordGuard.reserveMany_valid c budget _ t.registry w.registry
    (t.valid hs hp hA hx) w.reserved
  have hr := RecordGuard.registry_cells c budget w.registry hv
  have hm := t.cells_le hs hp hA hx
  unfold Scratch.cells registryCells
  omega

end StreamingSSSP.Core.Live

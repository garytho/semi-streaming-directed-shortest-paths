module

public import StreamingReachability.Core.PartialCacheSpace
public import StreamingReachability.Core.PackingSpace

@[expose] public section

namespace StreamingReachability.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ}

def registryCells (registry : RecordGuard.Registry n nq) : ℕ := 2 + 3 * registry.seen.card

/-- Operational prefixes, not stored histories. Only their designated live buffers
are counted below; the input stream and shared catalog are read-only. -/
structure Boundary (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget x : ℕ) where
  rounds : ℕ
  first : RecordGuard.Registry n nq
  registry : RecordGuard.Registry n nq
  state : BatchDriver.Run n nb nq
  initialized : GuardedDriver.initSources c budget = .ok first
  executed : GuardedDriver.drive hn c stored input budget x rounds 0 first
    ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ = .ok (registry, state)

def Boundary.jobs {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} (p : Boundary hn c stored input budget x) :=
  BatchDriver.jobs c p.rounds p.state.states

def Boundary.origin {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} (p : Boundary hn c stored input budget x) :
    Fin p.jobs.length → Fin nq × Fin nb := fun i => BatchDriver.key (p.jobs.get i)

def Boundary.cells {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} (p : Boundary hn c stored input budget x) : ℕ :=
  BatchDriver.stateCells p.state.states + registryCells p.registry

structure Blocks {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} (p : Boundary hn c stored input budget x) where
  phases : ℕ
  registry : RecordGuard.Registry n nq
  result : Shared.Engine.Run n nb nq p.jobs.length
  executed : GuardedEngine.run hn c stored input budget p.rounds phases (BatchDriver.tasks p.jobs) p.registry =
    .ok (registry, result)

def Blocks.packages {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} {p : Boundary hn c stored input budget x} (b : Blocks p) :=
  Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active b.result.tasks)

def Blocks.cells {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} {p : Boundary hn c stored input budget x} (b : Blocks p) : ℕ :=
  BatchDriver.stateCells p.state.states + registryCells b.registry +
    GuardedEngine.tasksCells (BatchDriver.tasks p.jobs) + GuardedEngine.tasksCells b.result.tasks +
    2 * GuardedEngine.planCells c b.result.tasks

structure Packs {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} {p : Boundary hn c stored input budget x} (b : Blocks p) where
  count : ℕ
  registry : RecordGuard.Registry n nq
  result : Shared.Engine.Phase n nb nq p.jobs.length
  executed : GuardedEngine.packs hn c stored input budget p.rounds (b.packages.take count) b.registry =
    .ok (registry, result)

def Packs.cells {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} {p : Boundary hn c stored input budget x}
    {b : Blocks p} (s : Packs b) : ℕ :=
  b.cells + registryCells s.registry + 2 * GuardedEngine.updatesCells s.result.updates + 8 * p.jobs.length

structure Processing {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} {p : Boundary hn c stored input budget x}
    {b : Blocks p} (s : Packs b) where
  slots : List (Fin p.jobs.length × Shared.Job n nb nq)
  member : slots ∈ b.packages
  count : ℕ
  registry : RecordGuard.Registry n nq
  updates : RecordMap.Map (Fin p.jobs.length) (Shared.Engine.Task n nb nq)
  executed : GuardedEngine.process hn c budget p.rounds (slots.take count)
    ((Shared.scanPack c (slots.map Prod.snd) stored input).state.take count) s.registry =
      .ok (registry, updates)

def Processing.cells {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} {p : Boundary hn c stored input budget x}
    {b : Blocks p} {s : Packs b} (t : Processing s) : ℕ :=
  s.cells + registryCells t.registry + 2 * GuardedEngine.updatesCells t.updates + 8 * p.jobs.length

end StreamingReachability.Core.Live

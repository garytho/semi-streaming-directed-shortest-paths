module

public import StreamingSSSP.Core.ExecutionSpace

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingSSSP.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

structure Edges {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
    {stored input : List (Edge n)} {budget x : ℕ} (p : Boundary hn c stored input budget x) where
  blocks : Blocks p
  complete : blocks.phases = Nat.log 2 x + 2
  count : ℕ
  registry : RecordGuard.Registry n nq
  candidates : Vector (Finset (Fin n)) nq
  executed : GuardedDriver.ordinaryScan c budget p.rounds p.state.states ((stored ++ input).take count)
    blocks.registry (Vector.replicate nq ∅) = .ok (registry, candidates)

def Edges.cells {p : Boundary hn c stored input budget x} (e : Edges p) : ℕ :=
  e.blocks.cells + registryCells e.registry + 2 * BatchDriver.ordinaryCells e.candidates + 12

theorem Edges.valid {p : Boundary hn c stored input budget x} (e : Edges p)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    RecordGuard.Valid c budget e.registry :=
  GuardedDriver.ordinaryScan_post c budget p.rounds (RecordGuard.Valid c budget)
    (fun key old next hv he => RecordGuard.reserve_valid c budget key old next hv he)
    p.state.states _ e.blocks.registry e.registry _ e.candidates (e.blocks.valid hs hp hA hx) e.executed

theorem Edges.cover {p : Boundary hn c stored input budget x} (e : Edges p) :
    GuardedDriver.CandidatesCovered e.registry e.candidates :=
  GuardedDriver.ordinaryScan_cover c budget p.rounds p.state.states _ e.blocks.registry e.registry
    _ e.candidates (by intro j v hv; simp at hv) e.executed

theorem Edges.cells_le {p : Boundary hn c stored input budget x} (e : Edges p)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    e.cells ≤ 18 + 75 * budget := by
  have hb := e.blocks.cells_le hs hp hA hx
  have hv := e.valid hs hp hA hx
  have hr := RecordGuard.registry_cells c budget e.registry hv
  have hC := GuardedDriver.candidate_cells c budget e.registry e.candidates hv e.cover
    (p.facts hs hp hA hx).queries
  unfold Edges.cells registryCells
  omega

structure Queries {p : Boundary hn c stored input budget x} (e : Edges p) where
  raw : Edge n
  count : ℕ
  registry : RecordGuard.Registry n nq
  candidates : Vector (Finset (Fin n)) nq
  executed : GuardedDriver.ordinaryQueries c budget p.rounds p.state.states raw ((List.finRange nq).take count)
    e.registry e.candidates = .ok (registry, candidates)

def Queries.cells {p : Boundary hn c stored input budget x} {e : Edges p} (q : Queries e) : ℕ :=
  e.cells + registryCells q.registry + 2 * BatchDriver.ordinaryCells q.candidates + 2 * nq + 12

theorem Queries.cells_le {p : Boundary hn c stored input budget x} {e : Edges p} (q : Queries e)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    q.cells ≤ 32 + 88 * budget := by
  have hbase := e.cells_le hs hp hA hx
  have hv := GuardedDriver.ordinaryQueries_valid c budget p.rounds p.state.states q.raw _
    e.registry q.registry e.candidates q.candidates (e.valid hs hp hA hx) q.executed
  have hc := GuardedDriver.ordinaryQueries_cover c budget p.rounds p.state.states q.raw _
    e.registry q.registry e.candidates q.candidates e.cover q.executed
  have hq := (p.facts hs hp hA hx).queries
  have hC := GuardedDriver.candidate_cells c budget q.registry q.candidates hv hc hq
  have hr := RecordGuard.registry_cells c budget q.registry hv
  unfold Queries.cells registryCells
  omega

end StreamingSSSP.Core.Live

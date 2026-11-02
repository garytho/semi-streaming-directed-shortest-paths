module

public import StreamingSSSP.Core.ScratchSpace
public import StreamingSSSP.Core.CacheSpace
public import StreamingSSSP.Core.GuardedCharge

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingSSSP.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

def catalogCells (c : Shared.Catalog n nb ns nq) (stored : List (Edge n)) : ℕ :=
  4 * (nb + ns + nq + 1) + 3 * stored.length +
    2 * ∑ i : Fin nb, (c.blocks.get i).card + 2 * ∑ i : Fin ns, (c.sets.get i).card

def serializationCells (p : Boundary hn c stored input budget x) (count : ℕ) : ℕ :=
  p.cells + 8 * ((BatchAPI.serialize c p.state.states).take count).length + 12

theorem serialization_cells_le (p : Boundary hn c stored input budget x) (count : ℕ)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    serializationCells p count ≤ 16 + 24 * budget := by
  have hf := p.facts hs hp hA hx
  have hcharge := BatchAPI.serialize_charge_le c p.state.states p.registry hf.cover
    (fun j => (hf.shape j).labels_unique)
  have hlen : (BatchAPI.serialize c p.state.states).length ≤
      ((BatchAPI.serialize c p.state.states).map fun record => RecordGuard.vertexCharge c record.vertex).sum := by
    have h := List.sum_le_sum (l := BatchAPI.serialize c p.state.states)
      (f := fun _ => 1) (g := fun record => RecordGuard.vertexCharge c record.vertex)
      (fun record _ => by unfold RecordGuard.vertexCharge; omega)
    simpa using h
  have hpart := (List.take_sublist count (BatchAPI.serialize c p.state.states)).length_le
  have hb : RecordGuard.weight c p.registry.seen ≤ budget := hf.valid.1 ▸ hf.valid.2
  have hc := p.cells_le hs hp hA hx
  unfold serializationCells
  omega

inductive MemoryPoint (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget x : ℕ) where
  | initializing (count : ℕ) (registry : RecordGuard.Registry n nq)
      (checked : RecordGuard.reserveMany c budget
        (((List.finRange nq).map fun j => (j, (c.searches.get j).source)).take count) RecordGuard.empty = .ok registry)
  | boundary (p : Boundary hn c stored input budget x)
  | blocks (p : Boundary hn c stored input budget x) (b : Blocks p)
  | packs (p : Boundary hn c stored input budget x) (b : Blocks p) (s : Packs b)
  | processing (p : Boundary hn c stored input budget x) (b : Blocks p) (s : Packs b) (t : Processing s)
  | scratch (p : Boundary hn c stored input budget x) (b : Blocks p) (s : Packs b) (t : Processing s) (w : Scratch t)
  | edges (p : Boundary hn c stored input budget x) (e : Edges p)
  | queries (p : Boundary hn c stored input budget x) (e : Edges p) (q : Queries e)
  | commit (p : Boundary hn c stored input budget x) (f : Commit p)
  | cache (p : Boundary hn c stored input budget x) (f : Commit p) (a : Cache f)
  | serializing (p : Boundary hn c stored input budget x) (count : ℕ)

def MemoryPoint.cells : MemoryPoint hn c stored input budget x → ℕ
  | .initializing _ registry _ => registryCells registry + 6 * nq + 2 * nb + 12
  | .boundary p => p.cells
  | .blocks _ b => b.cells
  | .packs _ _ s => s.cells
  | .processing _ _ _ t => t.cells
  | .scratch _ _ _ _ w => w.cells
  | .edges _ e => e.cells
  | .queries _ _ q => q.cells
  | .commit _ f => f.cells
  | .cache _ _ a => a.cells
  | .serializing p count => serializationCells p count

def MemorySafe (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget x : ℕ) : Prop :=
  ∀ point : MemoryPoint hn c stored input budget x,
    point.cells ≤ 256 * (n + budget + 1) + 4 * catalogCells c stored

theorem every_prefix_space
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) (hspace : 2 * x * x ≤ n) :
    MemorySafe hn c stored input budget x := by
  intro point
  have hcat : 4 * (nb + ns + nq + 1) ≤ catalogCells c stored := by unfold catalogCells; omega
  cases point with
  | initializing count registry checked =>
      have hv := RecordGuard.reserveMany_valid c budget _ RecordGuard.empty registry
        (RecordGuard.empty_valid c budget) checked
      have hr := RecordGuard.registry_cells c budget registry hv
      change registryCells registry + 6 * nq + 2 * nb + 12 ≤ _
      unfold registryCells
      omega
  | boundary p =>
      have h := p.cells_le hs hp hA hx
      change p.cells ≤ _
      omega
  | blocks p b =>
      have h := b.cells_le hs hp hA hx
      change b.cells ≤ _
      omega
  | packs p b s =>
      have h := s.cells_le hs hp hA hx
      change s.cells ≤ _
      omega
  | processing p b s t =>
      have h := t.cells_le hs hp hA hx
      change t.cells ≤ _
      omega
  | scratch p b s t w =>
      exact (w.cells_le hs hp hA hx hspace).trans (Nat.le_add_right _ _)
  | edges p e =>
      have h := e.cells_le hs hp hA hx
      change e.cells ≤ _
      omega
  | queries p e q =>
      have h := q.cells_le hs hp hA hx
      change q.cells ≤ _
      omega
  | commit p f =>
      have h := f.cells_le hs hp hA hx
      change f.cells ≤ _
      omega
  | cache p f a =>
      have h := a.cells_le hs hp hA hx
      change a.cells ≤ _
      omega
  | serializing p count =>
      have h := serialization_cells_le p count hs hp hA hx
      change serializationCells p count ≤ _
      omega

end StreamingSSSP.Core.Live

namespace StreamingSSSP.Core.BatchAPI

abbrev MemorySafe {n : ℕ} (hn : 0 < n) (request : Request n) (budget : ℕ)
    (input : List (StoredEdges.Edge n)) :=
  Live.MemorySafe hn request.catalog request.explicit input budget request.workspace

theorem runGuarded_every_prefix_space {n : ℕ} (hn : 0 < n) (request : Request n) (budget : ℕ)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (hspace : 2 * request.workspace * request.workspace ≤ n) :
    MemorySafe hn request budget input :=
  Live.every_prefix_space hs hp hA hx hspace

end StreamingSSSP.Core.BatchAPI

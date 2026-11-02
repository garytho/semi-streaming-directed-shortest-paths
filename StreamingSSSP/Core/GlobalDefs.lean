module

public import StreamingSSSP.Core.GlobalGraph

@[expose] public section

namespace StreamingSSSP.Core.Global

open StoredEdges

variable {n b : ℕ}

structure Problem (n b : ℕ) where
  scale : ℕ
  source : Fin n
  blocks : Vector (Finset (Fin n)) b

structure BlockState (n : ℕ) where
  known : SparseLabels.Labels (Fin n)
  next : Distance
  charge : ScheduleCharge.State
  reservations : ℕ

def emptyBlock : BlockState n := ⟨[], ⊤, ⟨0, 0, false⟩, 0⟩

structure State (n b : ℕ) where
  labels : SparseLabels.Labels (Fin n)
  settled : Finset (Fin n)
  blocks : Vector (BlockState n) b

def initial (p : Problem n b) : State n b :=
  ⟨[(p.source, 0)], ∅, Vector.replicate b emptyBlock⟩

def emptyOutcome : BlockSearch.Outcome n := ⟨∅, [], ⊤, 1, 0, 0⟩

structure BlockResult (n : ℕ) where
  state : BlockState n
  vertices : Finset (Fin n)
  scans : ℕ
  reservations : ℕ

def searchBlock (hn : 0 < n) (A : ℕ) (B : Finset (Fin n)) (input : List (Edge n)) (r : ℕ)
    (old : BlockState n) : BlockResult n :=
  if old.next = (r : Distance) then
    let out := (BlockSearch.search hn B (SparseLabels.support old.known)
      (A * r) (SparseLabels.vector old.known) input).getD emptyOutcome
    ⟨⟨old.known ++ out.records, roundDistance A out.nextNumerator,
        ScheduleCharge.searched old.charge out.vertices.card,
        old.reservations + out.reservations⟩,
      out.vertices, out.scans, out.reservations⟩
  else ⟨old, ∅, 0, 0⟩

def searchOne (hn : 0 < n) (p : Problem n b) (input : List (Edge n)) (r : ℕ)
    (i : Fin b) (old : BlockState n) : BlockResult n :=
  searchBlock hn p.scale (p.blocks.get i) input r old

def edgeStep (A r : ℕ) (labels : SparseLabels.Labels (Fin n)) (settled : Finset (Fin n))
    (candidates : Finset (Fin n)) (e : Edge n) : Finset (Fin n) :=
  if e.source ∈ settled ∧ e.target ∉ settled ∧
      SparseLabels.get labels e.source + (ceilNat A e.weight : Distance) ≤ (r : Distance)
  then insert e.target candidates else candidates

def ordinaryStep (A r : ℕ) (old : State n b) :
    Finset (Fin n) → Edge n → Finset (Fin n) :=
  edgeStep A r old.labels old.settled

def ordinary (p : Problem n b) (input : List (Edge n)) (r : ℕ) (old : State n b) :
    Finset (Fin n) :=
  input.foldl (ordinaryStep p.scale r old) ∅

def newVertices (p : Problem n b) (input : List (Edge n)) (r : ℕ) (old : State n b)
    (results : Vector (BlockResult n) b) : Finset (Fin n) :=
  ((if r = 0 then {p.source} else ∅) ∪ ordinary p input r old ∪
    Finset.univ.biUnion (fun i => (results.get i).vertices)) \ old.settled

def externalBlock (A r : ℕ) (B U : Finset (Fin n))
    (old : BlockState n) : BlockState n :=
  let E := (U ∩ B) \ SparseLabels.support old.known
  { known := old.known ++ SparseLabels.ofSet E (fun _ => ((A * r : ℕ) : Distance))
    next := if E.card = 0 then old.next else ((r + 1 : ℕ) : Distance)
    charge := if E.card = 0 then old.charge else ScheduleCharge.externalInsert old.charge E.card
    reservations := old.reservations }

def insertExternal (p : Problem n b) (r : ℕ) (U : Finset (Fin n)) (i : Fin b)
    (old : BlockState n) : BlockState n :=
  externalBlock p.scale r (p.blocks.get i) U old

def round (hn : 0 < n) (p : Problem n b) (input : List (Edge n)) (r : ℕ)
    (old : State n b) : State n b :=
  let results := Vector.ofFn fun i => searchOne hn p input r i (old.blocks.get i)
  let U := newVertices p input r old results
  { labels := SparseLabels.addNew old.labels U (r : Distance)
    settled := old.settled ∪ U
    blocks := Vector.ofFn fun i => insertExternal p r U i (results.get i).state }

def execute (hn : 0 < n) (p : Problem n b) (input : List (Edge n)) : ℕ → State n b
  | 0 => initial p
  | r + 1 => round hn p input r (execute hn p input r)

noncomputable def target (p : Problem n b) (input : List (Edge n)) : Fin n → Distance :=
  (queryGraph input p.blocks.toList p.scale).dist p.source

noncomputable def targetNat (p : Problem n b) (input : List (Edge n)) (v : Fin n) : ℕ :=
  (target p input v).untopD 0

noncomputable def blockSeed (p : Problem n b) (input : List (Edge n))
    (settled : Finset (Fin n)) (i : Fin b) : Fin n → Distance :=
  scaledSeeds p.scale (settled ∩ p.blocks.get i) (targetNat p input)

noncomputable def blockDistance (p : Problem n b) (input : List (Edge n))
    (settled : Finset (Fin n)) (i : Fin b) : Fin n → Distance :=
  multiDist (BlockSearch.blockGraph input (p.blocks.get i)) (blockSeed p input settled i)

structure GlobalInvariant (p : Problem n b) (input : List (Edge n))
    (old : State n b) (r : ℕ) : Prop where
  settled_iff : ∀ v, v ∈ old.settled ↔ target p input v < (r : Distance)
  label_support : SparseLabels.support old.labels = old.settled ∪ {p.source}
  label_exact : ∀ v ∈ SparseLabels.support old.labels, SparseLabels.get old.labels v = target p input v
  label_unique : (old.labels.map Prod.fst).Nodup

structure BlockInvariant (p : Problem n b) (input : List (Edge n))
    (settled : Finset (Fin n)) (r : ℕ) (i : Fin b) (old : BlockState n) : Prop where
  known_support : SparseLabels.support old.known = settled ∩ p.blocks.get i
  known_exact : ∀ v ∈ SparseLabels.support old.known,
    SparseLabels.get old.known v = blockDistance p input settled i v
  known_unique : (old.known.map Prod.fst).Nodup
  next_lower : (r : Distance) ≤ old.next
  next_upper : ∀ v ∈ p.blocks.get i, v ∉ settled →
    old.next ≤ roundDistance p.scale (blockDistance p input settled i v)
  next_exact : old.charge.dirty = false →
    old.next = roundDistance p.scale
      (nextDistance (p.blocks.get i) (SparseLabels.support old.known) (blockDistance p input settled i))
  charge_valid : ScheduleCharge.valid old.charge
  insertion_count : old.charge.insertions = (SparseLabels.support old.known).card
  reservation_bound : old.reservations ≤
    4 * (p.blocks.get i).card * (old.charge.insertions + old.charge.searches)

def Invariant (p : Problem n b) (input : List (Edge n)) (old : State n b) (r : ℕ) : Prop :=
  GlobalInvariant p input old r ∧
    ∀ i, BlockInvariant p input old.settled r i (old.blocks.get i)

end StreamingSSSP.Core.Global

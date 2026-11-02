module

public import StreamingSSSP.Exact.Main

@[expose] public section

namespace StreamingSSSP.Exact.DescriptorProgram

open StoredEdges

variable {n : ℕ}

abbrev Labels (n : ℕ) := Vector ℕ n

/-- The virtual source occupies one additional scalar, not another vertex array. -/
structure LevelAnswer (n : ℕ) where
  vertices : Labels n
  source : ℕ

def LevelAnswer.at (answer : LevelAnswer n) : Option (Fin n) → ℕ
  | none => answer.source
  | some v => answer.vertices.get v

def LevelAnswer.ofFn (answer : Option (Fin n) → ℕ) : LevelAnswer n :=
  ⟨Vector.ofFn (fun v => answer (some v)), answer none⟩

@[simp] theorem LevelAnswer.at_ofFn (answer : Option (Fin n) → ℕ) :
    (LevelAnswer.ofFn answer).at = answer := by
  funext v
  cases v <;> simp [LevelAnswer.at, LevelAnswer.ofFn]

/-- Requests contain the explicit endpoint transducer, never a semantic graph
or an input edge list. The last request is one scan of the original stream. -/
inductive Request (n : ℕ) where
  | base (descriptor : BaseDescriptor (Fin n)) (source : Fin n)
      (denominator clock : ℕ)
  | level (descriptor : LevelDescriptor (Fin n)) (denominator clock : ℕ)
  | parents (source : Fin n) (weightBound : ℕ) (distances : Labels n)

def Request.Reply : Request n → Type
  | .base .. => Labels n
  | .level .. => LevelAnswer n
  | .parents .. => Vector (Option (Edge n)) n

/-- A finite, computable free query program. A compiler supplies only replies
to the three request constructors. -/
inductive Program (n : ℕ) (α : Type*) where
  | pure (value : α)
  | ask (request : Request n) (next : request.Reply → Program n α)

namespace Program

variable {α β : Type*}

def bind : Program n α → (α → Program n β) → Program n β
  | .pure value, next => next value
  | .ask request resume, next => .ask request (fun reply => bind (resume reply) next)

def run (reply : (request : Request n) → request.Reply) : Program n α → α
  | .pure value => value
  | .ask request resume => run reply (resume (reply request))

def trace {Event : Type*} (observe : Request n → List Event)
    (reply : (request : Request n) → request.Reply) : Program n α → List Event
  | .pure _ => []
  | .ask request resume => observe request ++ trace observe reply (resume (reply request))

theorem run_bind (reply : (request : Request n) → request.Reply)
    (program : Program n α) (next : α → Program n β) :
    run reply (bind program next) = run reply (next (run reply program)) := by
  induction program with
  | pure value => rfl
  | ask request resume ih => exact ih (reply request)

theorem trace_bind {Event : Type*} (observe : Request n → List Event)
    (reply : (request : Request n) → request.Reply)
    (program : Program n α) (next : α → Program n β) :
    trace observe reply (bind program next) =
      trace observe reply program ++ trace observe reply (next (run reply program)) := by
  induction program with
  | pure value => rfl
  | ask request resume ih =>
      simp only [bind, trace, run, ih (reply request), List.append_assoc]

end Program

def baseDescriptor (potential : Labels n) (denominator : ℕ) : BaseDescriptor (Fin n) :=
  ⟨potential.get, inflation n, 3 * n * denominator⟩

def levelDescriptor (potential labels : Labels n)
    (slope width shift denominator : ℕ) : LevelDescriptor (Fin n) :=
  ⟨potential.get, labels.get, inflation n, slope, width, shift,
    3 * (n + 1) * denominator⟩

def baseQuery (potential : Labels n) (source : Fin n)
    (denominator clock cap : ℕ) : Program n (Labels n) :=
  .ask (.base (baseDescriptor potential denominator) source (3 * denominator) clock)
    (fun raw => .pure (Vector.ofFn
      (positiveAnswer n denominator (fun v => min cap (raw.get v)))))

def levelQuery (potential labels : Labels n)
    (slope width shift denominator clock cap : ℕ) : Program n (LevelAnswer n) :=
  .ask (.level (levelDescriptor potential labels slope width shift denominator)
      (3 * denominator) clock)
    (fun raw => .pure (LevelAnswer.ofFn
      (positiveAnswer (n + 1) denominator (fun v => min cap (raw.at v)))))

/-- Both answers are decoded and materialized before the next request.
The recursive state contains only the current vectors and scalar parameters. -/
def smoothRounds (potential : Labels n) (M cap offset : ℕ) :
    ℕ → ℕ → Labels n → Program n (Labels n)
  | 0, _, labels => .pure labels
  | rounds + 1, slope, labels =>
      let K := M * (2 * 2 ^ rounds)
      Program.bind
        (levelQuery potential labels (slope + 1) (8 * K) 0 (100 * M)
          (offset + (2 * rounds + 1)) cap)
        (fun answer₀ =>
          Program.bind
            (levelQuery potential labels (slope + 1) (8 * K) (4 * K) (100 * M)
              (offset + (2 * rounds + 2)) cap)
            (fun answer₁ =>
              smoothRounds potential M cap offset rounds (slope + 1)
                (Vector.ofFn (partialLabels labels.get K answer₀.at answer₁.at))))

def smoothing (source : Fin n) (potential : Labels n) (rounds cap offset : ℕ) :
    Program n (Labels n) :=
  let C := smoothingScale rounds
  Program.bind (baseQuery potential source 1 offset cap) (fun answer =>
    smoothRounds potential (C + rounds) cap offset rounds C
      (Vector.ofFn (fun v => C * answer.get v)))

def updatePotential (potential labels : Labels n) (rounds : ℕ) : Labels n :=
  let update := roundedUpdate labels.get (smoothingScale rounds) (smoothingScale_pos rounds)
  Vector.ofFn (fun v => potential.get v + update v)

def outerRounds (source : Fin n) (rounds cap : ℕ) :
    ℕ → Labels n → Program n (Labels n)
  | 0, potential => .pure potential
  | iterations + 1, potential =>
      let offset := iterations * (1 + 2 * rounds)
      Program.bind (smoothing source potential rounds cap offset) (fun labels =>
        outerRounds source rounds cap iterations (updatePotential potential labels rounds))

def estimates (source : Fin n) (exponent : ℕ) : Program n (Labels n) :=
  let bits := inputBits n exponent
  outerRounds source (smoothingRounds bits) (replyCap bits) (bits + 1)
    (Vector.ofFn (fun _ => 0))

/-- Runtime inputs are `n`, the source/exponent, and descriptor/scan replies.
In particular this definition has no graph or edge-stream argument. -/
def exact (source : Fin n) (exponent : ℕ) : Program n (Result n) :=
  Program.bind (estimates source exponent) (fun distances =>
    .ask (.parents source (n ^ exponent) distances) (fun parents =>
      .pure ⟨decode (n ^ exponent) distances.get, parents.get⟩))

end StreamingSSSP.Exact.DescriptorProgram

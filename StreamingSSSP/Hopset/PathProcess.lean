module

public import StreamingSSSP.Hopset.EarlyPathFamilies
public import StreamingSSSP.Hopset.NodeBalls

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

structure Layer (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) where
  level : ℕ
  queue : List (Finset (Fin n))
  paths : List (TrackedPath stored input queue.toArray.toVector)
  choices : Fin queue.toArray.size → Reference.Choice n cfg

def Layer.control {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} (layer : Layer cfg stored input) : Batched.ControlEntry n cfg :=
  ⟨layer.level, layer.queue, layer.choices⟩

def Layer.pieces {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} (hnum : 0 < cfg.initialNumerator) (layer : Layer cfg stored input) :=
  splitAll cfg layer.level hnum layer.paths

structure State (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) where
  known : Fin n → Option (Fin r)
  queue : List (Finset (Fin n))
  paths : List (TrackedPath stored input queue.toArray.toVector)
  layers : List (Layer cfg stored input)

namespace State

variable {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {r : ℕ}

def history (st : State cfg stored input r) : List (Batched.ControlEntry n cfg) :=
  st.layers.map Layer.control

def update (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (st : State cfg stored input r)
    (sample : (Fin n → Bool) × (Fin st.queue.toArray.size → Reference.Owners n cfg)) :
    State cfg stored input (r + 1) :=
  let choices := Batched.currentChoices cfg st.queue.toArray.toVector sample.1 sample.2
  { known := fun v => RankPrefix.nextKnown r (st.known v) (sample.1 v)
    queue := Batched.geometricChildren cfg r stored input st.queue.toArray.toVector choices
    paths := advanceAll cfg r hnum he choices (splitAll cfg r hnum st.paths)
      (splitAll_short cfg r hnum st.paths)
    layers := st.layers ++ [⟨r, st.queue, st.paths, choices⟩] }

def rawCount (st : State cfg stored input r) : ℕ :=
  if Batched.AllGood cfg stored input r st.queue then st.paths.length else 0

def primeCount (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r) : ℕ :=
  if Batched.AllGood cfg stored input r st.queue then (splitAll cfg r hnum st.paths).length else 0

def splitCount (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r) : ℕ :=
  if Batched.AllGood cfg stored input r st.queue then splits cfg r hnum st.paths else 0

def rawRelated (st : State cfg stored input r) : ℕ :=
  if Batched.AllGood cfg stored input r st.queue then related cfg r st.known st.paths else 0

def primeRelated (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r) : ℕ :=
  if Batched.AllGood cfg stored input r st.queue then related cfg r st.known (splitAll cfg r hnum st.paths) else 0

theorem rawCount_le (st : State cfg stored input r) : st.rawCount ≤ st.paths.length := by
  unfold rawCount
  split_ifs <;> omega

theorem rawRelated_le (st : State cfg stored input r) : st.rawRelated ≤ related cfg r st.known st.paths := by
  unfold rawRelated
  split_ifs <;> omega

theorem primeCount_eq (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r) :
    st.primeCount hnum = st.rawCount + st.splitCount hnum := by
  unfold primeCount rawCount splitCount
  split_ifs
  · exact splitAll_length cfg r hnum st.paths
  · omega

theorem splitCount_credit (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r) :
    (st.splitCount hnum : ℝ) * Reference.distanceScale cfg r ≤ weight cfg.inputScale st.paths := by
  unfold splitCount
  split_ifs
  · exact splits_credit cfg r hnum st.paths
  · simp

theorem ambient_balls (st : State cfg stored input r)
    (hg : Batched.AllGood cfg stored input r st.queue) (hb : 1 ≤ Parameters.ballSize n r) :
    ∀ i v,
      (Early.searchIn (Backend.roundedRestricted stored input (st.queue.toArray.toVector.get i) cfg.inputScale) v
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ Parameters.ballSize n r ∧
      (Early.searchOut (Backend.roundedRestricted stored input (st.queue.toArray.toVector.get i) cfg.inputScale) v
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ Parameters.ballSize n r := by
  intro i
  exact Reference.ballsGood_all_vertices cfg stored input r (st.queue.toArray.toVector.get i)
    (hg _ (Batched.queue_get_mem st.queue i)) hb

theorem primeRelated_le (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r)
    (hb : 1 ≤ Parameters.ballSize n r) :
    st.primeRelated hnum ≤ st.rawRelated + 2 * Parameters.ballSize n r * st.splitCount hnum := by
  by_cases hg : Batched.AllGood cfg stored input r st.queue
  · simp only [primeRelated, rawRelated, splitCount, hg, ↓reduceIte]
    exact splitAll_related cfg r hnum st.known st.paths (Parameters.ballSize n r)
      (fun i v => (st.ambient_balls hg hb i v).1) (fun i v => (st.ambient_balls hg hb i v).2)
  · simp only [primeRelated, rawRelated, splitCount, hg, ↓reduceIte, Nat.mul_zero, Nat.add_zero, le_refl]

theorem update_weight_le (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (st : State cfg stored input r)
    (sample : (Fin n → Bool) × (Fin st.queue.toArray.size → Reference.Owners n cfg)) :
    weight cfg.inputScale (st.update hnum he sample).paths ≤ weight cfg.inputScale st.paths :=
  (advanceAll_weight cfg r hnum he _ _ (splitAll_short cfg r hnum st.paths)).trans
    (splitAll_weight cfg r hnum st.paths)

end State

def liftCount {A : Type*} (f : A → ℕ) : Option A → ℝ
  | none => 0
  | some a => (f a : ℝ)

def pathStep (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (r : ℕ) :
    Option (State cfg stored input r) → Law (Option (State cfg stored input (r + 1)))
  | none => Law.pure none
  | some st =>
      if he : r < cfg.earlyLevel then
        if Batched.AllGood cfg stored input r st.queue then
          (currentDraw cfg ps r st.known st.queue.toArray.size).map (fun sample => some (st.update hnum he sample))
        else Law.pure none
      else Law.pure none

def pathStateLaw (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (root : State cfg stored input 0) :
    (r : ℕ) → Law (Option (State cfg stored input r))
  | 0 => Law.pure (some root)
  | r + 1 => (pathStateLaw cfg ps hnum stored input root r).bind (pathStep cfg ps hnum stored input r)

end

end StreamingSSSP.Hopset.Following

module

public import StreamingReachability.Core.GuardedPrefixPass
public import StreamingReachability.Core.GuardedFusedDriver

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

theorem Packs.pass_budget {p : Boundary hn c stored input budget x} {b : Blocks p} (s : Packs b)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    n * s.result.scans ≤ n + 4 * x * budget := by
  have he : s.result.scans = (b.packages.take s.count).length := by
    rw [GuardedEngine.packs_erases hn c stored input budget p.rounds _ b.registry s.registry s.result s.executed,
      Shared.Engine.executePacks_scans]
  have hlen : (b.packages.take s.count).length ≤ b.packages.length :=
    (List.take_sublist s.count b.packages).length_le
  have hpack := Packing.pack_scan_bound n
    (fun slot : Fin p.jobs.length × Shared.Job n nb nq => Shared.capacity c slot.2)
    (Shared.Engine.active b.result.tasks)
  have hload := (b.work_budget hs hp hA hx).2
  rw [he]
  have hm := Nat.mul_le_mul_left n hlen
  change n * b.packages.length ≤ _ at hpack
  nlinarith only [hm, hpack, hload]

inductive PassPrefix (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget x R : ℕ) where
  | initializing
  | boundary (p : Boundary hn c stored input budget x) (clock : p.rounds ≤ R + 1)
  | blocks (p : Boundary hn c stored input budget x) (b : Blocks p)
      (clock : p.rounds ≤ R) (phaseClock : b.phases ≤ Nat.log 2 x + 2)
  | skeleton (p : Boundary hn c stored input budget x) (b : Blocks p) (s : Packs b)
      (clock : p.rounds ≤ R) (phaseClock : b.phases < Nat.log 2 x + 2)
  | ordinary (p : Boundary hn c stored input budget x) (b : Blocks p)
      (clock : p.rounds ≤ R) (complete : b.phases = Nat.log 2 x + 2)

def PassPrefix.passes {R : ℕ} : PassPrefix hn c stored input budget x R → ℕ
  | .initializing => 0
  | .boundary p _ => p.state.passes
  | .blocks p b _ _ => p.state.passes + b.result.scans
  | .skeleton p b s _ _ => p.state.passes + b.result.scans + s.result.scans + 1
  | .ordinary p b _ _ => p.state.passes + b.result.scans + 1

theorem PassPrefix.mul_bound {R : ℕ} (point : PassPrefix hn c stored input budget x R)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    n * point.passes ≤ n * (R + 1) * (Nat.log 2 x + 3) + 32 * x * budget := by
  cases point with
  | initializing => exact Nat.zero_le _
  | boundary p clock =>
      have h := p.pass_budget hs hp hA hx
      have hc := Nat.mul_le_mul_right (Nat.log 2 x + 3) (Nat.mul_le_mul_left n clock)
      change n * p.state.passes ≤ _
      nlinarith only [h, hc]
  | blocks p b clock phaseClock =>
      have h := p.pass_budget hs hp hA hx
      have hb := b.pass_budget hs hp hA hx
      have hc := Nat.mul_le_mul_right (Nat.log 2 x + 3) (Nat.mul_le_mul_left n clock)
      have hk := Nat.mul_le_mul_left n phaseClock
      change n * (p.state.passes + b.result.scans) ≤ _
      nlinarith only [h, hb, hc, hk]
  | skeleton p b s clock phaseClock =>
      have h := p.pass_budget hs hp hA hx
      have hb := b.pass_budget hs hp hA hx
      have hpacks := s.pass_budget hs hp hA hx
      have hc := Nat.mul_le_mul_right (Nat.log 2 x + 3) (Nat.mul_le_mul_left n clock)
      have hk := Nat.mul_le_mul_left n (show b.phases + 2 ≤ Nat.log 2 x + 3 by omega)
      change n * (p.state.passes + b.result.scans + s.result.scans + 1) ≤ _
      nlinarith only [h, hb, hpacks, hc, hk]
  | ordinary p b clock complete =>
      have h := p.pass_budget hs hp hA hx
      have hb := b.pass_budget hs hp hA hx
      have hc := Nat.mul_le_mul_right (Nat.log 2 x + 3) (Nat.mul_le_mul_left n clock)
      rw [complete] at hb
      change n * (p.state.passes + b.result.scans + 1) ≤ _
      nlinarith only [h, hb, hc]

theorem divide_pass_bound {n p C K : ℕ} (hn : 0 < n) (h : n * p ≤ n * C + K) :
    p ≤ C + K / n := by
  by_contra hp
  have hstep : C + K / n + 1 ≤ p := by omega
  have hscaled := Nat.mul_le_mul_left n hstep
  have hmod := Nat.mod_lt K hn
  have hsplit := Nat.mod_add_div K n
  nlinarith only [h, hscaled, hmod, hsplit]

theorem PassPrefix.bound {R : ℕ} (point : PassPrefix hn c stored input budget x R)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    point.passes ≤ (R + 1) * (Nat.log 2 x + 3) + 32 * x * budget / n := by
  apply divide_pass_bound hn
  simpa only [Nat.mul_assoc] using point.mul_bound hs hp hA hx

end StreamingReachability.Core.Live

namespace StreamingReachability.Core.BatchAPI

abbrev PassPrefix {n : ℕ} (hn : 0 < n) (request : Request n) (budget : ℕ)
    (input : List (StoredEdges.Edge n)) :=
  Live.PassPrefix hn request.catalog request.explicit input budget request.workspace request.radius

theorem prefix_pass_bound {n : ℕ} (hn : 0 < n) (request : Request n) (budget : ℕ)
    (input : List (StoredEdges.Edge n)) (point : PassPrefix hn request budget input)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    point.passes ≤ (request.radius + 1) * (Nat.log 2 request.workspace + 3) +
      32 * request.workspace * budget / n :=
  point.bound hs hp hA hx

end StreamingReachability.Core.BatchAPI

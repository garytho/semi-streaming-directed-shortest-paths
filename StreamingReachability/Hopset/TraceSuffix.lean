module

public import StreamingReachability.Hopset.FullSemantics
public import StreamingReachability.Hopset.FullTraceSplit

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

theorem FullValid.drop {fuel q : ℕ} {queue : List (Finset (Fin n))}
    {trace : List (GeometricEntry n cfg)} (h : FullValid cfg stored input rank fuel q queue trace)
    (left : ℕ) (hle : left ≤ fuel) :
    FullValid cfg stored input rank (fuel - left) (q + left)
      (afterQueue queue (trace.take left)) (trace.drop left) := by
  induction left generalizing fuel q queue trace with
  | zero => simpa only [Nat.sub_zero, Nat.add_zero, List.take_zero, afterQueue, List.drop_zero] using h
  | succ left ih =>
      cases h with
      | done => omega
      | @next fuel q queue frame tail valid rest =>
          have ht := ih rest (by omega)
          have hlevel : q + 1 + left = q + (left + 1) := by omega
          simpa only [Nat.succ_sub_succ_eq_sub, List.take_succ_cons, List.drop_succ_cons,
            afterQueue, hlevel] using ht

theorem FullValid.current_good {fuel q : ℕ} {queue : List (Finset (Fin n))}
    {trace : List (GeometricEntry n cfg)} (h : FullValid cfg stored input rank (fuel + 1) q queue trace)
    (hg : TraceGood cfg stored input trace) : AllGood cfg stored input q queue := by
  cases h with
  | next valid rest => exact hg _ List.mem_cons_self

theorem TraceGood.drop {trace : List (GeometricEntry n cfg)} (hg : TraceGood cfg stored input trace) (left : ℕ) :
    TraceGood cfg stored input (trace.drop left) :=
  fun entry he => hg entry (List.mem_of_mem_drop he)

end

end StreamingReachability.Hopset.Batched

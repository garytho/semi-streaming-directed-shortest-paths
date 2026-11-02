module

public import StreamingSSSP.Approx.Metadata
public import StreamingSSSP.Core.Main

@[expose] public section

namespace StreamingSSSP.Approx

open scoped Classical BigOperators
open Hopset

variable {n : ℕ}

def queryCatalog (stored : Implicit.Representation n) (scale radius : ℕ) (source : Fin n) :
    Core.Shared.Catalog n stored.blocks.length 1 1 :=
  { scale := scale
    blocks := stored.blocks.toArray.toVector
    sets := Vector.replicate 1 Finset.univ
    searches := Vector.replicate 1 ⟨0, source, false, radius⟩ }

def queryRequest (stored : Implicit.Representation n) (x scale radius : ℕ) (source : Fin n) : Core.BatchAPI.Request n :=
  .ofCatalog stored.explicit (queryCatalog stored scale radius source) x

theorem queryCatalog_blocks (stored : Implicit.Representation n) (scale radius : ℕ) (source : Fin n) :
    (queryCatalog stored scale radius source).blocks.toList = stored.blocks := by
  simp only [queryCatalog, Array.toVector, Vector.toList_mk, List.toList_toArray]

theorem queryCatalog_small (stored : Implicit.Representation n) (x scale radius : ℕ) (source : Fin n)
    (hs : ∀ B ∈ stored.blocks, B.card ≤ x) :
    ∀ i, ((queryCatalog stored scale radius source).blocks.get i).card ≤ x := by
  intro i
  apply hs
  have hm : (queryCatalog stored scale radius source).blocks.get i ∈
      (queryCatalog stored scale radius source).blocks.toList := by
    have h := List.get_mem (queryCatalog stored scale radius source).blocks.toList
      ⟨i.val, by simpa only [Vector.length_toList] using i.isLt⟩
    simpa only [List.get_eq_getElem, Vector.getElem_toList, Vector.get_eq_getElem] using h
  simpa only [queryCatalog_blocks] using hm

noncomputable section

theorem query_lookup (hn : 0 < n) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (x scale radius : ℕ) (source v : Fin n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hscale : 0 < scale) (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    Core.BatchAPI.lookup (Core.BatchAPI.run (queryRequest stored x scale radius source) input).records 0 v =
      if (Late.rounded scale (stored.graph (StoredEdges.graphOfEdges input))).dist source v ≤ (radius : Distance)
      then (Late.rounded scale (stored.graph (StoredEdges.graphOfEdges input))).dist source v else ⊤ := by
  let c := queryCatalog stored scale radius source
  have h := Backend.raw_lookup c stored input hn hs hp (queryCatalog_blocks stored scale radius source) hscale x
    (queryCatalog_small stored x scale radius source hsize) 0 v
  have hgraph : Backend.roundedRestricted stored input Finset.univ scale =
      Late.rounded scale (stored.graph (StoredEdges.graphOfEdges input)) := by
    funext u w
    simp only [Backend.roundedRestricted, Late.rounded, Implicit.Representation.restricted_univ]
  simp only [c, queryCatalog, Core.Shared.vertices, Vector.get_replicate, Bool.false_eq_true, ↓reduceIte] at h
  rw [hgraph] at h
  exact h

theorem query_charge_bound (hn : 0 < n) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (x scale radius : ℕ) (source : Fin n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hscale : 0 < scale) (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    Core.BatchAPI.replyCharge (queryRequest stored x scale radius source)
      (Core.BatchAPI.run (queryRequest stored x scale radius source) input).records ≤ n + volume stored.blocks := by
  let c := queryCatalog stored scale radius source
  rw [Core.BatchAPI.raw_reply_charge _ input hn hs hp hscale (queryCatalog_small stored x scale radius source hsize)]
  have hc : (∑ i : Fin stored.blocks.length, (c.blocks.get i).card) = volume stored.blocks := by
    have h := congrArg (fun bs : List (Finset (Fin n)) => (bs.map Finset.card).sum) (Backend.vector_indices c.blocks)
    simp only [← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn, Function.comp_def] at h
    rw [show c.blocks.toList = stored.blocks from queryCatalog_blocks stored scale radius source] at h
    exact h
  change Core.BatchDriver.Nrec c stored.explicit input ≤ _
  simp only [Core.BatchDriver.Nrec, Fin.sum_univ_one]
  apply Nat.add_le_add
  · simpa only [Fintype.card_fin] using Finset.card_le_univ (Core.BatchDriver.reached c stored.explicit input 0)
  · rw [← hc]
    exact Finset.sum_le_sum (fun i _ => Finset.card_le_card Finset.inter_subset_right)

theorem query_noAbort (hn : 0 < n) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (x scale radius : ℕ) (source : Fin n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hscale : 0 < scale) (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    Core.BatchAPI.runGuarded (queryRequest stored x scale radius source) (n + volume stored.blocks) input =
      .ok (Core.BatchAPI.run (queryRequest stored x scale radius source) input) :=
  Core.GuardedDriver.run_complete _ _ input hn hs hp hscale
    (queryCatalog_small stored x scale radius source hsize)
    (query_charge_bound hn stored input x scale radius source hs hp hscale hsize)

theorem query_handler (hn : 0 < n) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (x scale radius : ℕ) (source : Fin n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hscale : 0 < scale) (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    Backend.guardedHandler input (queryRequest stored x scale radius source) (n + volume stored.blocks) =
      Law.pure (some (Core.BatchAPI.run (queryRequest stored x scale radius source) input).records) := by
  simp only [Backend.guardedHandler, query_noAbort hn stored input x scale radius source hs hp hscale hsize]

end

end StreamingSSSP.Approx

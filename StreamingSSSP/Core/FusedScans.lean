module

public import StreamingSSSP.Streaming.FusedPass
public import StreamingSSSP.Core.ScanFusion

@[expose] public section

namespace StreamingSSSP.Core.Shared

open StoredEdges

variable {E : Type*} {n nb ns nq : ℕ}

def scanPackFused (outer : E → Option (Edge n)) (c : Catalog n nb ns nq)
    (jobs : List (Job n nb nq)) (stored : List (Edge n)) (input : List E) :
    Streaming.FusedMetered (List (Work n nb nq)) :=
  Streaming.fusedPass outer (update c) cells input
    (stored.foldl (update c) (jobs.map (start c)))

theorem scanPackFused_erase (outer : E → Option (Edge n)) (c : Catalog n nb ns nq)
    (jobs : List (Job n nb nq)) (stored : List (Edge n)) (input : List E) :
    (scanPackFused outer c jobs stored input).erase = scanPack c jobs stored (input.filterMap outer) :=
  Streaming.fusedPass_erase _ _ _ _ _

end StreamingSSSP.Core.Shared

module

public import StreamingSSSP.Exact.Resources
public import StreamingSSSP.Exact.QueryProgramBounds
public meta import StreamingSSSP.Exact.Rounding
public meta import StreamingSSSP.Exact.Tree
public meta import StreamingSSSP.Exact.Preprocess
public meta import StreamingSSSP.Exact.QueryProgram

@[expose] public section

namespace StreamingSSSP.Exact.Tests

open StoredEdges

def boundaryLabels (v : Fin 3) : ℕ :=
  if v = 0 then 0 else if v = 1 then 25550 else 25650

example : (safeShiftIndex boundaryLabels 100 (by decide)).val = 1 := by decide

example : (List.finRange 3).map (roundedUpdate boundaryLabels 100 (by decide)) =
    [0, 1, 1] := by decide

def zeroCycleEdges : List (Edge 5) :=
  [⟨2, 1, 0⟩, ⟨0, 1, 0⟩, ⟨1, 2, 0⟩, ⟨2, 3, 2⟩, ⟨0, 2, 1⟩]

def transformedLabels (v : Fin 5) : ℕ := #[0, 1, 2, 13, 55][v]

example : (List.finRange 5).map (fun v =>
    (ParentPass.run 0 2 transformedLabels zeroCycleEdges v).map (fun e => e.source.val)) =
    [none, some 0, some 1, some 2, none] := by decide

example : (List.finRange 5).map (decode 2 transformedLabels) =
    [(0 : Distance), 0, 0, 2, ⊤] := by decide

example : (positiveAnswer 5 10 (fun _ : Fin 1 => 6)) 0 = 0 := by decide

#eval (List.finRange 3).map (roundedUpdate boundaryLabels 100 (by decide))
#eval (List.finRange 5).map (fun v =>
  (ParentPass.run 0 2 transformedLabels zeroCycleEdges v).map (fun e => e.source.val))
#eval (List.finRange 5).map (decode 2 transformedLabels)

def descriptorReply (request : DescriptorProgram.Request 2) : request.Reply :=
  match request with
  | .base .. => Vector.ofFn (fun v => if v = 0 then 0 else 6)
  | .level .. => DescriptorProgram.LevelAnswer.ofFn (fun _ => 0)
  | .parents .. => Vector.ofFn (fun _ => none)

def descriptorSummary : DescriptorProgram.Request 2 → List (List ℕ)
  | .base descriptor _ denominator clock =>
      [[0, clock, denominator, descriptor.positiveScale]]
  | .level descriptor denominator clock =>
      [[1, clock, denominator, descriptor.slope, descriptor.width, descriptor.shift,
        descriptor.labels 1]]
  | .parents .. => [[2]]

def descriptorRound : DescriptorProgram.Program 2 (DescriptorProgram.Labels 2) :=
  DescriptorProgram.smoothing 0 (Vector.ofFn (fun _ => 0)) 1 1000 7

example : (DescriptorProgram.Program.run descriptorReply descriptorRound).toList = [0, 0] := by
  decide

example : DescriptorProgram.Program.trace descriptorSummary descriptorReply descriptorRound =
    [[0, 7, 3, 6], [1, 8, 60300, 201, 3216, 0, 200],
      [1, 9, 60300, 201, 3216, 1608, 200]] := by decide

#eval DescriptorProgram.Program.trace descriptorSummary descriptorReply descriptorRound

end StreamingSSSP.Exact.Tests

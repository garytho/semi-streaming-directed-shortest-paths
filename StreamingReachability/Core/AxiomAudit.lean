module

public import StreamingReachability.Core

open Lean in
run_elab do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`StreamingReachability.Core).isPrefixOf name ||
        (`StreamingReachability.Streaming).isPrefixOf name then
      let dependencies ← collectAxioms name
      let unexpected := dependencies.filter fun dep => !allowed.contains dep
      unless unexpected.isEmpty do
        throwError m!"Unexpected axioms in {name}: {unexpected.toList}"
      count := count + 1
  logInfo m!"Audited {count} core/streaming declarations: only propext, Classical.choice, Quot.sound."

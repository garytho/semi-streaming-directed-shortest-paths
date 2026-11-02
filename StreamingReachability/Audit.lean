module

public import StreamingReachability.Main

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`StreamingReachability).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless axiomName == `propext || axiomName == `Classical.choice ||
            axiomName == `Quot.sound do
          throwError "Nonstandard foundation {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Streaming audit: {checked} declarations; only standard Lean foundations."

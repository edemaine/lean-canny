import LeanCanny
import Lean.Util.CollectAxioms

/-! Audit every declaration in the project's namespace, including transitive dependencies.
Run with `lake env lean scripts/CheckAxioms.lean` after `lake build`.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`LeanCanny).isPrefixOf name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  if checked = 0 then
    throwError "No LeanCanny declarations found"
  logInfo m!"Audited {checked} declarations: only propext, Classical.choice, and Quot.sound allowed."

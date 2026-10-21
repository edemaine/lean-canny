import SpacePrototype
import BoundedFoldPrototype
import Lean.Util.CollectAxioms

open LeanCanny.SpacePrototype

#guard scan slowChild (7, 4) == 5
#guard scan slowChild (7, 0) == 0
#guard scan slowChild (0, 6) == 0
#guard scan (fun p => p.2) (4, 3) == 3
#guard LeanCanny.BoundedFoldPrototype.fold LeanCanny.BoundedFoldPrototype.modularChild
  (fun _ => 0) (7, 4) 4 == 5

open Lean in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`LeanCanny.SpacePrototype).isPrefixOf name ||
        (`LeanCanny.BoundedFoldPrototype).isPrefixOf name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  if checked = 0 then
    throwError "No prototype declarations found"
  logInfo m!"Audited {checked} prototype declarations."

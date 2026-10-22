import LeanCanny.Abstract
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-! Public definitions and statements must depend only on this abstract and
background libraries. Implementation declarations may occur in theorem proofs,
which are checked separately for unexpected axioms. -/

open Lean in
run_cmd do
  let env ← getEnv
  let abstractModule := `LeanCanny.Abstract
  let mut pending : Array Name := #[]
  let mut roots : Nat := 0
  for (name, info) in env.constants.toList do
    if (`LeanCanny.Abstract).isPrefixOf name then
      roots := roots + 1
      pending := pending ++ info.type.getUsedConstants
      if !info.isTheorem then
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx.toNat]!
      if (`LeanCanny).isPrefixOf owner && owner != abstractModule then
        throwError "Public abstract depends on implementation declaration {name} from {owner}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if !info.isTheorem then
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
  if roots = 0 then throwError "No abstract declarations found"
  logInfo m!"Audited {roots} abstract declarations and {visited.size} statement/definition dependencies: no implementation references or unexpected axioms."

#print axioms LeanCanny.Abstract.etr_mem_PSPACE
#print axioms LeanCanny.Abstract.existsReal_subset_PSPACE

import RealCountingHierarchy.Abstract
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-! Audit the independent CH abstract's public definitions, inferred types,
instances, and theorem statements transitively. Bridge and implementation
references are permitted only inside checked theorem proofs. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut pending : Array Name := #[]
  let mut roots : Nat := 0
  for (name, info) in env.constants.toList do
    if (`RealCountingHierarchy.Abstract).isPrefixOf name then
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
      if ((`LeanCanny).isPrefixOf owner || (`RealCountingHierarchy).isPrefixOf owner) &&
          owner != `RealCountingHierarchy.Abstract then
        throwError "CH abstract statement/definition depends on implementation declaration {name} from {owner}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if !info.isTheorem then
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
  if roots = 0 then throwError "No CH abstract declarations found"
  logInfo m!"Audited {roots} CH abstract declarations and {visited.size} statement/definition dependencies: no implementation references or unexpected axioms."

#print axioms RealCountingHierarchy.Abstract.etr_mem_CountingLevel
#print axioms RealCountingHierarchy.Abstract.existsReal_subset_CountingLevel
#print axioms RealCountingHierarchy.Abstract.existsForall_mem_CountingLevel

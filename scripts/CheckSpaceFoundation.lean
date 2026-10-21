import LeanCanny
import Lean.Util.FoldConsts

open Turing.MultiTapeTM

/-! Check the public endpoints against the native class and accept an arbitrary
native space-bounded child, with no legacy evaluator or execution clock. -/

example : LeanCanny.PSPACE = Cslib.Complexity.PSPACE encBits := rfl

example : LeanCanny.P = Cslib.Complexity.P encBits := rfl

example {L K : Set (List Bool)} : LeanCanny.PolyTimeReduces L K ↔
    Cslib.Complexity.PolyTimeReducible encBits encBits L K := Iff.rfl

example {L K : Set (List Bool)} {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hcorrect : ∀ x, x ∈ L ↔ f x ∈ K) (hK : K ∈ LeanCanny.ExistsReal) :
    L ∈ LeanCanny.ExistsReal :=
  LeanCanny.existsReal_of_reduction ⟨f, hf, hcorrect⟩ hK

example : LeanCanny.ExistsReal ⊆ Cslib.Complexity.PSPACE encBits ↔
    LeanCanny.ETR.language ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.existsReal_subset_PSPACE_iff

example {F : LeanCanny.Algebra.MatrixPower.ModularFamily}
    (a : LeanCanny.Algebra.MatrixPower.ModularAccess F) (ha : a.ControlsPolyTime)
    (he : ComputableTidilyInPolySpace a.entry encBits encBits) :
    ComputableTidilyInPolySpace F.value encBits encBits :=
  (LeanCanny.Algebra.MatrixPower.ModularAccess.evaluatorWithEntry a ha ⟨he⟩).computable

example {F : LeanCanny.Algebra.Berkowitz.ModularFamily}
    (a : LeanCanny.Algebra.Berkowitz.ModularAccess F) (ha : a.ControlsPolyTime)
    (he : ComputableTidilyInPolySpace a.access.entry encBits encBits) :
    F.zeroLanguage ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.Algebra.Berkowitz.ModularAccess.zeroLanguage_mem_PSPACE_of_evaluator a ha ⟨he⟩

example {S : LeanCanny.ETR.TubeLevelSign.Source} {B : LeanCanny.ETR.TubeLevelSign.Budget S}
    (a : LeanCanny.Algebra.SignPatternBits.Access (LeanCanny.ETR.TubeLevelSign.family S B))
    (hF : LeanCanny.Algebra.SignPatternBits.ControlsPolyTime (LeanCanny.ETR.TubeLevelSign.family S B))
    (hroot : ComputableTidilyInPolySpace a.rootCoefficient encBits encBits)
    (hquery : ComputableTidilyInPolySpace a.polynomialCoefficient encBits encBits) :
    LeanCanny.ETR.TubeLevelSign.sampleLanguage S ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.ETR.TubeLevelSign.sampleLanguage_mem_PSPACE a hF ⟨hroot⟩ ⟨hquery⟩

#eval "Native PSPACE endpoints and arbitrary native child certificates checked."

/-! The structural class theorems must use native time certificates too. -/

open Lean in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if (`Complexitylib).isPrefixOf name then
      throwError "Project imports obsolete foundation module: {name}"
  let mut pending := #[`LeanCanny.P, `LeanCanny.PolyTimeReduces, `LeanCanny.ExistsReal,
    `LeanCanny.P_subset_existsReal, `LeanCanny.existsReal_subset_PSPACE_iff,
    `LeanCanny.Computation.mem_PSPACE_of_reduction]
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    for forbidden in #[`Complexity.FP, `Complexity.P, `Complexity.MapReducesPoly,
        `LeanCanny.Computation.TidyFP] do
      if forbidden.isPrefixOf name then
        throwError "Structural class theorem depends on legacy time foundation: {name}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  logInfo m!"Audited {visited.size} transitive constants: native P, reductions, and class closure."

/-! Check actual proof dependencies, including opaque theorem bodies:
polynomial-time support must not reintroduce the old space class. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut pending : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`LeanCanny).isPrefixOf name then pending := pending.push name
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    for forbidden in #[`Complexity.PSPACE, `Complexity.NPSPACE, `Complexity.DSPACE,
        `Complexity.NSPACE, `Complexity.SpaceIter,
        `LeanCanny.Computation.SubroutineIteration, `LeanCanny.Computation.WindowedMachine] do
      if forbidden.isPrefixOf name then
        throwError "Project proof depends on obsolete space foundation: {name}"
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  logInfo m!"Audited {visited.size} transitive constants: no legacy space foundation."

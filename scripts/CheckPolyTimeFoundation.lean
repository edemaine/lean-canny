import LeanCanny.Computation.PolyTimeIteration
import LeanCanny.Computation.PolyTimeQuantifiers
import LeanCanny.Computation.PolyTimeRange
import LeanCanny.Computation.PolyTimeBinary
import LeanCanny.Computation.PolyTimeArithmetic
import LeanCanny.Tactic.PolyTime
import LeanCanny.Encoding.Data
import Lean.Util.CollectAxioms

/-! The replacement foundation must compile without importing any legacy
Complexitylib module. This check remains separate while clients are migrated. -/

open Turing.MultiTapeTM
open LeanCanny

example {f : List Bool → List Bool} : f ∈ LeanCanny.FP ↔
    ComputableTidilyInPolyTime f encBits encBits := Iff.rfl

example {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolyTime f encBits encBits) :
    (fun z => LeanCanny.pair (f z) z) ∈ LeanCanny.FP :=
  LeanCanny.mem_FP_pairWithInput hf

example {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => pair (f z) (g z).reverse) ∈ FP := by
  polytime

example {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun z => n z + 1) := by
  polytime

#guard LeanCanny.pairFst [true, true, true] == [true]
#guard LeanCanny.pairFst [false, false, true, false] == [false]
#guard LeanCanny.pairSnd [true, false, true] == []
#guard LeanCanny.pairSnd [true, true, true] == []
#guard LeanCanny.pairSnd (LeanCanny.pair [true, false] [false, true]) == [false, true]

open Lean in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if (`Complexitylib).isPrefixOf name then
      throwError "Native polynomial-time foundation imports legacy module: {name}"
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`LeanCanny).isPrefixOf name then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  logInfo m!"Audited {checked} native declarations: no legacy imports or nonstandard axioms."

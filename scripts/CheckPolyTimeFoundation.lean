import LeanCanny.Computation.PolyTimeIteration
import LeanCanny.Computation.PolyTimeQuantifiers
import LeanCanny.Computation.PolyTimeRange
import LeanCanny.Computation.PolyTimeBinary
import LeanCanny.Computation.PolyTimeBinaryNat
import LeanCanny.Computation.PolyTimeArithmetic
import LeanCanny.Tactic.PolyTime
import LeanCanny.Encoding.Data
import Lean.Util.CollectAxioms

/-! The replacement foundation must compile without importing any legacy
Complexitylib module. This independent check does not need the rest of the
Canny development. -/

open Turing.MultiTapeTM
open LeanCanny

example {f : List Bool → List Bool} : f ∈ LeanCanny.FP ↔
    ComputableTidilyInPolyTime f encBits encBits := Iff.rfl

example {f : List Bool → ℕ} : LeanCanny.BinaryFn f ↔
    ComputableTidilyInPolyTime f encBits encNat := Iff.rfl

example {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolyTime f encBits encBits) :
    (fun z => LeanCanny.pair (f z) z) ∈ LeanCanny.FP :=
  LeanCanny.mem_FP_pairWithInput hf

example {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => pair (f z) (g z).reverse) ∈ FP := by
  polytime

example {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun z => n z + 1) := by
  polytime

/- The compatibility layer must preserve local and named routine calls,
encoded unary results, and bounded predicate scans without custom search. -/
open scoped Classical in
example {f : List Bool → ℕ}
    (hf : (fun z => List.replicate (f z) true) ∈ FP) :
    (fun z => List.replicate (f (pairFst z) + 1) true) ∈ FP := by
  polytime

open scoped Classical in
example {p : List Bool → Prop} (hp : FPPred p) :
    FPPred (fun z => p (pairFst z) ∧ (pairSnd z).length < z.length + 1) := by
  polytime

open scoped Classical in
example {p : List Bool → Prop} (hp : FPPred p) :
    UnaryFn (fun z => (if p (pairFst z) then z.length else 0) + 1) := by
  polytime

open scoped Classical in
example {p : List Bool → Prop} {n : List Bool → ℕ}
    (hp : FPPred p) (hn : UnaryFn n) :
    FPPred (fun z => (∀ i < n z, p (pair z (List.replicate i true))) ∧ p (pairFst z)) := by
  polytime

open scoped Classical in
example {p : List Bool → Prop} {n : List Bool → ℕ}
    (hp : FPPred p) (hn : UnaryFn n) :
    FPPred (fun z => ∃ i < n z, p (pair z (List.replicate i true))) := by
  polytime

open scoped Classical in
example {p : List Bool → Prop} {n : List Bool → ℕ}
    (hp : FPPred p) (hn : UnaryFn n) :
    UnaryFn (fun z => ((Finset.range (n z)).filter
      fun i => p (pair z (List.replicate i true))).card) := by
  polytime

example {step init : List Bool → List Bool} {count : List Bool → ℕ}
    (hs : step ∈ FP) (hi : init ∈ FP) (hc : UnaryFn count) {growth : ℕ}
    (hg : ∀ w, (step w).length ≤ w.length + growth) :
    (fun z => step^[count z] (init z)) ∈ FP := by
  polytime

example {n f : List Bool → ℕ} (hn : UnaryFn n) (hf : UnaryFn f) :
    UnaryFn (fun z => Finset.sum (Finset.range (n z))
      (fun i => f (pair z (List.replicate i true))) + z.length) := by
  polytime

open scoped Classical in
example {p q : List Bool → Prop} (hp : FPPred p) (hq : FPPred q) :
    FPPred (fun z => ¬p (pairFst z) ∨ q (pairSnd z)) := by
  polytime

open scoped Classical in
example {f : List Bool → List Bool} {n : List Bool → ℕ}
    (hf : f ∈ FP) (hn : UnaryFn n) :
    FPPred (fun z => (f z)[n z]?.getD false = true) := by
  polytime

example {f : List Bool → List Bool} {n : List Bool → ℕ}
    (hf : f ∈ FP) (hn : UnaryFn n) :
    (fun z => (f z).take (n z) ++ (f z).drop (n z)) ∈ FP := by
  polytime

example {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => max (f z / (g z + 1)) (f z % (g z + 1)) + (f z).size) := by
  polytime

open scoped Classical in
example {p : List Bool → Prop} {f : List Bool → List Bool}
    (hp : FPPred p) (hf : f ∈ FP) :
    (fun z => pair (if p (pairFst z) then f z else []) z) ∈ FP := by
  polytime

example {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun z => pair (n (pairFst z)).bits z) ∈ FP := by
  polytime

namespace AutomationRegression
private def tagged (w : List Bool) : List Bool := pair [] w

@[program_certificate]
private theorem tagged_computable : ComputableTidilyInPolyTime tagged encBits encBits := by
  unfold tagged
  fun_prop

attribute [local irreducible] tagged

example {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => tagged (f (pairSnd z))) ∈ FP := by
  polytime

-- An unknown routine must still require a computation certificate.
example (_f : List Bool → List Bool) : True := by
  fail_if_success have : _f ∈ FP := by polytime
  trivial
end AutomationRegression

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
    let natCodec := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `LeanCanny.Encoding.NatBits
      | none => false
    if (`LeanCanny).isPrefixOf name || natCodec then
      checked := checked + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
  logInfo m!"Audited {checked} native declarations: no legacy imports or nonstandard axioms."

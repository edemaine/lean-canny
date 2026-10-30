/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PairedScanController
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native space and orbit-size bounds for paired recursive scans

The counter is binary. The controller stores the original task and three
Boolean values, independently of the number or running time of its child
requests. Its native certificates can be passed to the recursive stack
compiler once the actual query family has supplied decreasing ranks.
-/

@[expose] public section
namespace LeanCanny.Computation.PairedScan.Program
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable (P : PairedScan.Program)

theorem certificates (hc : BinaryFn P.count) (hl : SpaceFunction P.left) (hr : SpaceFunction P.right) :
    P.controller.Certificates (encQ := encBits) (encS := PairedScan.encState) := by
  have hcount := ComputableTidilyInPolySpace.of_polyTime hc
  have hleft := hl.computable
  have hright := hr.computable
  have hreply : ComputableTidilyInPolyTime reply encBits encBool :=
    (ComputableTidilyInPolyTime.decide_eq encBits).comp
      (ComputableTidilyInPolyTime.id'.prod (ComputableTidilyInPolyTime.const [true]))
  have hbits : ComputableTidilyInPolySpace BinaryNatCode.encode encNat encBits :=
    .of_polyTime natBits_computable
  constructor
  · change ComputableTidilyInPolySpace (fun q : List Bool => (q, 0, false, false, false)) _ _
    fun_prop
  all_goals dsimp only [controller, PairedScan.encState, entry]
  all_goals fun_prop (config := { maxSteps := 512, maxTransitionDepth := 2 })

theorem state_length (q : List Bool) (k : ℕ) (phase l a : Bool) :
    (PairedScan.encState (q, k, phase, l, a)).length =
      2 * q.length + 2 * (encNat k).length + 9 := by
  simp only [PairedScan.encState, length_encPair, encBits_apply, encBool_apply, List.length_singleton]
  omega

theorem orbit_length (answer : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (ht : t ≤ 2 * P.count q) :
    (PairedScan.encState ((P.controller.reference answer)^[t] (initial q))).length ≤
      2 * q.length + 2 * (encNat (P.count q)).length + 9 := by
  have HM := Nat.mod_lt t (by decide : 0 < 2)
  have HD := Nat.mod_add_div t 2
  have HK : t / 2 ≤ P.count q := by omega
  have HL := ComputableTidilyInO.length_encNat_mono HK
  by_cases he : t % 2 = 0
  · have HE : t = 2 * (t / 2) := by omega
    rw [HE, P.iterate_even answer q _ HK, state_length]
    omega
  · have HE : t = 2 * (t / 2) + 1 := by omega
    have HK' : t / 2 < P.count q := by omega
    rw [HE, P.iterate_odd answer q _ HK', state_length]
    omega

theorem value_length (answer : List Bool → List Bool) (q : List Bool) :
    (P.value answer q).length = 1 := rfl

end LeanCanny.Computation.PairedScan.Program

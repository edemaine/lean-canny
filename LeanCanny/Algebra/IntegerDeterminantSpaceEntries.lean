/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerDeterminantPSPACE
public import LeanCanny.Algebra.BerkowitzSpaceEntries

/-!
# Integer determinant zero testing with space-bounded residue access

The modulus scan runs the strengthened modular determinant decider. Its
original-entry evaluator may itself use polynomial space; the nested evaluator
certificates account for the scan, outer power, moment, and entry states.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.IntegerAccess
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

structure ControlsPolyTime {F : IntegerFamily} (a : IntegerAccess F) : Prop where
  dimension : a.dimension ∈ FP
  budget : a.budget ∈ FP

theorem modular_controls {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime) :
    a.modular.ControlsPolyTime := by
  have hd := mem_FP_comp pairFst_mem_FP ha.dimension
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  constructor
  · simpa only [modular] using hd
  · simpa only [modular] using hm

theorem bound_mem_FP_of_controls {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime) :
    bound a ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair ha.budget ha.budget) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP (BinaryNatCode.encode 4))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := bound a) h ?_
  intro c
  simp only [Function.comp_apply, bound]

noncomputable def modularEntry {F : IntegerFamily} (a : IntegerAccess F) (E : SpaceFunction a.entry) :
    SpaceFunction a.modular.access.entry := by
  refine E.congr ?_
  funext p
  simp only [modular]

noncomputable def deciderWithEntry {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceDecider F.zeroLanguage := by
  rw [← scan_language_eq F]
  exact BoundedScan.decider
    (ModularAccess.deciderWithEntry a.modular (modular_controls a ha) (modularEntry a E))
    (bound a) (bound_mem_FP_of_controls a ha) (fun c => 2 * F.budget c + 4) (bound_code a)

theorem zeroLanguage_mem_PSPACE_of_evaluator {F : IntegerFamily} (a : IntegerAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) : F.zeroLanguage ∈ PSPACE :=
  (deciderWithEntry a ha E).mem_PSPACE

end LeanCanny.Algebra.Berkowitz.IntegerAccess

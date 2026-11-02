/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeDenominator
public import LeanCanny.Algebra.IntegralMixedVirtualContextDenominator
/-! # Canonical outputs of charged denominator kernels, independent of a frontend -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorCanonicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
attribute [local irreducible] IntegralMixedPhysicalDenominatorBits.value IntegralMixedVirtualDenominatorBits.value

theorem physical (P : Parameters) (a : Access P) (F : IntegralMixedPhysicalCriticalBits.Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (R : Routing) (hr : RoutingAccess R) (hp : IntegralMixedPhysicalNativeDenominatorBits.Primitive P F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (IntegralMixedPhysicalNativeDenominatorBits.machine P a F h g R hr hp).model q := by
  refine ⟨(IntegralMixedPhysicalCriticalBits.denominator F (IntegralMixedPhysicalTaskBits.saved P q) : ZMod (modulus P q)), ?_⟩
  calc
    _ = IntegralMixedPhysicalDenominatorBits.valueAt F (IntegralMixedPhysicalTaskBits.saved P q) (modulus P q) := rfl
    _ = IntegralMixedPhysicalDenominatorBits.value P F q := (IntegralMixedPhysicalDenominatorBits.snapshot P F q).symm
    _ = _ := (congrFun (IntegralMixedPhysicalNativeDenominatorBits.machine_model P a F h g R hr hp) q).symm

theorem virtual (P : Parameters) (a : Access P) (F : IntegralMixedCutSource.Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (hr : RoutingAccess R) (hp : IntegralMixedVirtualContextDenominatorBits.Primitive P F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (IntegralMixedVirtualContextDenominatorBits.machine P a F h g R hr hp).model q := by
  refine ⟨(IntegralMixedVirtualSweepSource.denominator F (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)), ?_⟩
  calc
    _ = IntegralMixedVirtualDenominatorBits.valueAt F (IntegralMixedVirtualTaskBits.saved P q) (modulus P q) := rfl
    _ = IntegralMixedVirtualDenominatorBits.value P F q := (IntegralMixedVirtualDenominatorBits.snapshot P F q).symm
    _ = _ := (congrFun (IntegralMixedVirtualContextDenominatorBits.machine_model P a F h g R hr hp) q).symm
end LeanCanny.Algebra.IntegralMixedDenominatorCanonicalBits

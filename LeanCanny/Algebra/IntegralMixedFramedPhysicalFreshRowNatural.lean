/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalCreatingRows
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockPoweredExact
/-! # A native powered critical row in uniform natural columns -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowNatural
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength keyAt instruction)
open IntegralMixedFramedPhysicalIndex (arity criticalEquiv)
open IntegralMixedFramedPhysicalRowTransport (keyRow)
open IntegralMixedFramedPhysicalBlockBits (poweredExact spatialCount)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem powered_row (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q context : List Bool)
    (hb : prefixLength P (IntegralMixedPhysicalTaskBits.saved P (base q))≤
      P.cap (pairFst (IntegralMixedPhysicalTaskBits.saved P (base q))))
    (hc : (instruction P D (IntegralMixedPhysicalTaskBits.saved P (base q))).command=
      .critical (IntegralMixedFramedPhysicalBits.rule P D (IntegralMixedPhysicalTaskBits.saved P (base q))))
    (j : FlatAffineCriticalStage.Variables (spatialCount P D J base q)) :
    rename Fin.val (poweredExact P D J base q j)=
      keyRow P D (keyAt (pairFst (IntegralMixedPhysicalTaskBits.saved P (base q)))
        (prefixLength P (IntegralMixedPhysicalTaskBits.saved P (base q))+1) context)
        (arity (commands P D (IntegralMixedPhysicalTaskBits.saved P (base q)))+(criticalEquiv j).val) :=by
  rw [IntegralMixedFramedPhysicalBlockBits.poweredExact_step]
  exact (IntegralMixedFramedPhysicalCreatingRows.critical_creating_rows P D J
    (IntegralMixedPhysicalTaskBits.saved P (base q)) context hb
    (IntegralMixedFramedPhysicalBits.rule P D (IntegralMixedPhysicalTaskBits.saved P (base q))) hc j).symm

end LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowNatural

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockLayout
public import LeanCanny.Algebra.IntegralMixedFramedCriticalRows
/-! # Exact columns of the literal next critical step at a saved source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalSourceAtBits (family)
open IntegralMixedFramedPhysicalIndex (enumerate criticalColumns)
open FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def oldEquiv (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :
    (family P D J base).physical q≃Fin (oldCount P D base q) :=
  enumerate (IntegralMixedFramedHistoryFamilyBits.commands P D (IntegralMixedPhysicalTaskBits.saved P (base q)))

noncomputable def columns (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :
    ((family P D J base).physical q⊕Variables (spatialCount P D J base q))→Fin (fullCount P D J base q) :=
  criticalColumns (P:=(family P D J base).spatial q) (B:=(family P D J base).width q)
    ((family P D J base).rule q) (oldEquiv P D J base q)

theorem columns_old (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : (family P D J base).physical q) :
    columns P D J base q (Sum.inl i)=oldIndex P D J base q (oldEquiv P D J base q i) := by
  apply Fin.ext
  exact IntegralMixedFramedPhysicalIndex.criticalColumns_old _ _ i

theorem columns_ambient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q)) :
    columns P D J base q (ambient i)=ambientIndex P D J base q i := by
  apply Fin.ext
  exact IntegralMixedFramedPhysicalIndex.criticalColumns_ambient _ _ i

theorem columns_multiplier (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (spatialCount P D J base q+1)) :
    columns P D J base q (multiplier i)=multiplierIndex P D J base q i := by
  apply Fin.ext
  exact IntegralMixedFramedPhysicalIndex.criticalColumns_multiplier _ _ i

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits

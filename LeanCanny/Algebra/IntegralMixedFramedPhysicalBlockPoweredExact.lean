/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockExact
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockRowsSpace
public import LeanCanny.Algebra.CoordinatePowerRename
/-! # Physical powers agree with the literal creating critical step -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalSourceAtBits (family)
open FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MvPolynomial.rename MvPolynomial.pderiv

noncomputable local instance physicalFintype (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (base : List Bool→List Bool) (q : List Bool) :
    Fintype ((family P D J base).physical q) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0)
    (IntegralMixedFramedHistoryFamilyBits.commands P D (IntegralMixedPhysicalTaskBits.saved P (base q)))))

theorem powers_columns (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :
    (fun i=>powers P D J base (pair q (BinaryNatCode.encode (columns P D J base q i).val)))=
      PhysicalPowerCriticalRows.powers (fun _=>1) (degree P D J base q) (physicalPower P base q) := by
  funext i
  rcases i with i|i
  · rw [columns_old,powers_old]
    rfl
  · rcases i with i|i
    · change powers P D J base (pair q (BinaryNatCode.encode (columns P D J base q (ambient i)).val))=physicalPower P base q
      rw [columns_ambient,powers_ambient]
    · change powers P D J base (pair q (BinaryNatCode.encode (columns P D J base q (multiplier i)).val))=
        (degree P D J base q-1)*physicalPower P base q
      rw [columns_multiplier,powers_multiplier]

noncomputable def poweredExact (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (j : Variables (spatialCount P D J base q)) :=
  CoordinatePowerSubstitution.substitute
    (fun i : Fin (fullCount P D J base q)=>powers P D J base (pair q (BinaryNatCode.encode i.val)))
    (unpoweredExact P D J base q j)

theorem poweredExact_rows (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (j : Variables (spatialCount P D J base q)) :
    poweredExact P D J base q j=rename (columns P D J base q)
      (PhysicalPowerCriticalRows.rows
        (IntegralMixedPhysicalOriginalSourceBits.polynomial (family P D J base) q)
        (criticalData P D J base q).frozen
        (PhysicalPowerCriticalRows.coordinateNormals 2 (criticalData P D J base q).scales (criticalData P D J base q).free)
        (IntegralHistorySampler.historyHeights ((family P D J base).state q).sampler (criticalData P D J base q).heights)
        (fun _=>1) (degree P D J base q) (physicalPower P base q) j) := by
  rw [poweredExact,unpoweredExact,CoordinatePowerSubstitution.rename]
  rw [show (fun i : Fin (fullCount P D J base q)=>powers P D J base (pair q (BinaryNatCode.encode i.val)))∘
    columns P D J base q=PhysicalPowerCriticalRows.powers (fun _=>1) (degree P D J base q) (physicalPower P base q)
    from powers_columns P D J base q]
  rfl

theorem physicalPower_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :
    physicalPower P base q=UniformIntegralPowerSchedule.physical ((family P D J base).cap q)
      (2^(family P D J base).width q) ((family P D J base).birth q) := by
  have HB:=IntegralMixedFramedOldHeightBits.bank_birth P D J (base q)
  have HW:=(IntegralMixedFramedHistoryFamilyBits.geometry P D J).width (base q)
  have HC : (family P D J base).cap q=P.cap (RankedHistoryTask.root (base q))+1 := by
    change P.cap (pairFst (IntegralMixedPhysicalTaskBits.saved P (base q)))+1=_
    simp only [IntegralMixedPhysicalTaskBits.saved,pairFst_pair]
  change _=UniformIntegralPowerSchedule.physical ((family P D J base).cap q)
    (2^(IntegralMixedFramedOldHeightBits.bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P (base q)))
    ((IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P (base q)))
  rw [HC,HW,HB]
  rfl

theorem poweredExact_step (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (j : Variables (spatialCount P D J base q)) :
    poweredExact P D J base q j=
      PolynomialSystemReindex.system
        (IntegralMixedFramedPhysicalIndex.stepEquiv (.critical ((family P D J base).rule q)) (oldEquiv P D J base q))
        (IntegralMixedFullHistoryScript.step ((family P D J base).state q) ((family P D J base).birth_bound q)
          (.critical ((family P D J base).rule q))).sampler.rows
        (IntegralMixedFramedPhysicalIndex.stepEquiv (.critical ((family P D J base).rule q)) (oldEquiv P D J base q)
          (Sum.inl (Sum.inr j))) := by
  rw [poweredExact_rows,physicalPower_eq P D J base q]
  exact (IntegralMixedFramedPhysicalIndex.critical_new_row ((family P D J base).state q)
    (oldEquiv P D J base q) ((family P D J base).birth_bound q) ((family P D J base).rule q) j).symm

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits

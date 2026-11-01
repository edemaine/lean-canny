/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeZero
public import LeanCanny.Algebra.LowestCoefficientRecursiveFlags
/-! # Canonical flag and trailing-index queries for normalization -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def matrixDimension (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  dimension F (IntegralMixedVirtualTaskBits.saved P q)

theorem matrixDimension_binary (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    BinaryFn (matrixDimension P F) := dimension_binary P a F h

def zeroTask (P : Parameters) :=
  IntegralMixedNormalizationFieldBits.query P pairFst .originalGridTerm (fun _ => 2)
    (fun z => Nat.fromBitsLE (pairSnd z))

theorem zeroTask_FP (P : Parameters) (a : Access P) : zeroTask P ∈ FP :=
  IntegralMixedNormalizationFieldBits.query_FP P a pairFst pairFst_mem_FP .originalGridTerm _ _
    (BinaryFn.const 2) (BinaryFn.fromBits pairSnd_mem_FP)

abbrev ZeroMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .originalGridTerm q → modulus P q = 2 → answer q = zeroValue P F q

theorem zeroTask_truth (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : ZeroMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5)
    (i : ℕ) (hi : i < matrixDimension P F q + 1) :
    answer (zeroTask P (pair q (BinaryNatCode.encode i))) = [true] ↔
      (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff i = 0 := by
  let z := pair q (BinaryNatCode.encode i)
  let c := zeroTask P z
  have HP : pairFst z = q := pairFst_pair _ _
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c zeroTask
    rw [IntegralMixedNormalizationFieldBits.query_birth, IntegralMixedNormalizationFieldBits.query_root, HP]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    unfold c zeroTask
    rw [IntegralMixedNormalizationFieldBits.query_routine, HP]
    exact hr
  have HT : isPhase .originalGridTerm c := IntegralMixedNormalizationFieldBits.query_phase P pairFst .originalGridTerm _ _ z
  have HC : (2 : ℕ) ≤ numericCap P (RankedHistoryTask.root (pairFst z)) :=
    (by decide : 2 ≤ 6).trans (IntegralMixedRoutineTaskBits.routine_cap P _)
  have HM : modulus P c = 2 := IntegralMixedNormalizationFieldBits.query_modulus P pairFst .originalGridTerm _ _ z HC (by decide)
  have HS : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q := by
    unfold c zeroTask
    rw [IntegralMixedNormalizationFieldBits.query_saved, HP]
  have HI : get P .coefficient c = i := by
    have HB : i ≤ numericCap P (RankedHistoryTask.root q) := (by omega : i ≤ matrixDimension P F q).trans (dimension_cap P F g q hv)
    have HA := IntegralMixedNormalizationFieldBits.query_coefficient P pairFst .originalGridTerm (fun _ => 2)
      (fun z => Nat.fromBitsLE (pairSnd z)) z (by
        simpa only [z, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HB)
    unfold c zeroTask
    simpa only [z, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HA
  change answer c = [true] ↔ _
  rw [hx c HV HR HT HM, zeroValue, ite_eq_left HM, HS, HI]
  by_cases HZ : (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff i = 0 <;> simp only [HZ, ite_true, ite_false]
  simp

theorem characteristic_natDegree (P : Parameters) (F : Family) (q : List Bool) :
    (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.natDegree = matrixDimension P F q := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rfl

def indexTask (P : Parameters) (F : Family) :=
  IntegralMixedNormalizationFieldBits.query P id .clearedGridSum
    (fun q => matrixDimension P F q + 1) (get P .coefficient)

theorem indexTask_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : indexTask P F ∈ FP :=
  IntegralMixedNormalizationFieldBits.query_FP P a id id_mem_FP .clearedGridSum _ _
    ((matrixDimension_binary P a F h).add (BinaryFn.const 1)) (get_binary P a .coefficient)

theorem indexTask_modulus (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) : modulus P (indexTask P F q) = matrixDimension P F q + 1 := by
  have HC := augmented_cap P F g q hv
  change (matrixDimension P F q + 2) * 1 ≤ _ at HC
  rw [Nat.mul_one] at HC
  exact IntegralMixedNormalizationFieldBits.query_modulus P id .clearedGridSum _ _ q
    (by simpa only [id_eq] using (by omega : matrixDimension P F q + 1 ≤ numericCap P (RankedHistoryTask.root q))) (Nat.zero_lt_succ _)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

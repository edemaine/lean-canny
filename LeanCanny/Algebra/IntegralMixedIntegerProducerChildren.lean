/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerLeaves
public import LeanCanny.Algebra.IntegralMixedCoefficientQueryFrames
/-! # Integer companion coefficient children stay in the same creating prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientTask (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : List Bool → List Bool :=
  IntegralMixedCoefficientQueryBits.writer P .companion .criticalCoefficient ∘ IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P D)

theorem coefficientTask_FP (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D) : coefficientTask P D ∈ FP :=
  mem_FP_comp (IntegralScalarGeneratorBits.coefficientQuery_FP (scalarFamily P D) (scalarAccess P a D h))
    (IntegralMixedCoefficientQueryBits.writer_FP P a .companion .criticalCoefficient)

theorem coefficientTask_frame (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 6) (hp : isPhase .companion q) :
    IntegralMixedRoutineTaskBits.Frame P q (coefficientTask P D q) := by
  have HP : pairFst (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P D) q) = q := pairFst_pair _ _
  have HF := IntegralMixedCoefficientQueryBits.writer_frame_phase P .companion .criticalCoefficient
    (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily P D) q) (by rw [HP, hr]; rfl)
    (by rw [HP]; change phase q = 26 at hp; change 25 < phase q; omega)
  simpa only [HP, coefficientTask, Function.comp_apply] using HF

theorem oldRank_cap (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    oldRank P D q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HB : oldRank P D q ≤ rankCap P (RankedHistoryTask.root q) := by
    unfold oldRank
    rw [(IntegralMixedFullHistoryFamilyBits.geometry P D).birth, (IntegralMixedFullHistoryFamilyBits.geometry P D).width]
    exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (min_le_right _ _)
  exact HB.trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem scalarDegree_cap (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (scalarFamily P D).scalarDegree q ≤ numericCap P (RankedHistoryTask.root q) := by
  change 2 ^ (bank P D).width (IntegralMixedVirtualTaskBits.saved P q) ≤ _
  rw [(IntegralMixedFullHistoryFamilyBits.geometry P D).width]
  exact (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

attribute [local irreducible] PaddedIntegralGeneratorFinBits.Family.coefficient rawScalar

theorem writer_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (k : ℕ)
    (hk : k ≤ numericCap P (RankedHistoryTask.root q)) (r t : Fin (oldRank P D q)) :
    coefficientValue P D (IntegralMixedCoefficientQueryBits.writer P .companion .criticalCoefficient
      (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
      residueBits ((family P D).coefficient q k r t) := by
  let z := pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  let c := IntegralMixedCoefficientQueryBits.writer P .companion .criticalCoefficient z
  have HP : pairFst z = q := pairFst_pair _ _
  have HR : r.val ≤ numericCap P (RankedHistoryTask.root q) := r.isLt.le.trans (oldRank_cap P D q)
  have HT : t.val ≤ numericCap P (RankedHistoryTask.root q) := t.isLt.le.trans (oldRank_cap P D q)
  have Hfields (f : Field) : get P f c =
      if f = .slot14 then 6 else
      if f = .row then min (Nat.fromBitsLE (IntegralPowerProductBits.rowWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .col then min (Nat.fromBitsLE (IntegralPowerProductBits.colWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .coefficient then min (Nat.fromBitsLE (IntegralPowerProductBits.factorWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
        get P f (pairFst z) := IntegralMixedCoefficientQueryBits.writer_get P .companion .criticalCoefficient z f
  simp only [z, IntegralPowerProductBits.rowWord, IntegralPowerProductBits.colWord,
    IntegralPowerProductBits.factorWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at Hfields
  have HI : get P .row c = r.val := by simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left HR] using Hfields .row
  have HJ : get P .col c = t.val := by simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left HT] using Hfields .col
  have HK : get P .coefficient c = k := by simpa only [reduceCtorEq, ite_true, ite_false, min_eq_left hk] using Hfields .coefficient
  have HS : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q :=
    (IntegralMixedCoefficientQueryBits.writer_saved P .companion .criticalCoefficient z).trans (congrArg (IntegralMixedVirtualTaskBits.saved P) HP)
  have HM : modulus P c = modulus P q :=
    (IntegralMixedCoefficientQueryBits.writer_modulus P .companion .criticalCoefficient z).trans (congrArg (modulus P) HP)
  have HRank : oldRank P D c = oldRank P D q := congrArg (fun key => count ((bank P D).birth key) ((bank P D).width key)) HS
  have HC : rawScalar P D c = residueBits ((polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).coeff k : ZMod (modulus P q)) := by
    unfold rawScalar
    rw [HS, HK, HM]
  change coefficientValue P D c = _
  unfold coefficientValue
  rw [HI, HJ, HRank, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt, HC, coefficient_matrix]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.ext_iff]
  by_cases he : r.val = t.val
  · rw [ite_eq_left he, ite_eq_left he, mul_one]
  · rw [ite_eq_right he, ite_eq_right he, mul_zero]
    exact ArithmeticBits.zero_residueBits _

theorem coefficientTask_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    coefficientValue P D (coefficientTask P D q) = residueBits
      ((scalarFamily P D).coefficient q (IntegralScalarGeneratorBits.index (scalarFamily P D) q)
        ((scalarFamily P D).oldRow q) ((scalarFamily P D).oldCol q)) := by
  have HK : IntegralScalarGeneratorBits.index (scalarFamily P D) q ≤ numericCap P (RankedHistoryTask.root q) :=
    (Nat.sub_le _ _).trans (((scalarFamily P D).row q).isLt.le.trans (scalarDegree_cap P D q))
  exact writer_value P D q _ HK _ _

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits

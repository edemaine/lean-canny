/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceOperations

/-! # A native unit test for counting roots in algebraic slices -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower
open BoundedProjectionTestMoments
open scoped Classical

noncomputable def unitTest : Test where
  polynomial _ := 1
  degree _ := 0
  mass _ := 0
  polynomial_degree _ := by simp
  polynomial_mass _ := by simp only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one, pow_zero, le_refl]

def unitCoefficient (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd (pairFst q)) = 0 then ArithmeticBits.one (BinaryNat.succ (pairSnd q)) else []
theorem unitCoefficient_FP : unitCoefficient ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have ho := mem_FP_comp (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  exact (hi.eq (BinaryFn.const 0)).ite_mem_FP ho (constFn_mem_FP [])

noncomputable def unitTestAccess : unitTest.Access where
  degree_binary := BinaryFn.const 0
  mass_binary := BinaryFn.const 0
  coefficient := unitCoefficient
  evaluator := SpaceFunction.ofFP _ unitCoefficient_FP
  coefficient_eq c k m hm := by
    let : NeZero m := ⟨hm.ne'⟩
    have hd : BinaryNat.succ (BinaryNatCode.encode (m - 1)) = BinaryNatCode.encode m := by
      simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    simp only [unitCoefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    by_cases hk : k = 0
    · rw [ite_eq_left hk]
      change ArithmeticBits.one (BinaryNat.succ (BinaryNatCode.encode (m - 1))) = _
      rw [hd]
      simpa only [unitTest, hk, Polynomial.coeff_one_zero, IntegerTarskiSeedBits.integerResidue, Int.cast_one] using
        ArithmeticBits.one_residueBits m
    · rw [ite_eq_right hk]
      simp [unitTest, Polynomial.coeff_one, hk, IntegerTarskiSeedBits.integerResidue, residueBits, BinaryNatCode.encode]

noncomputable def unit : Family := ofTest unitTest
noncomputable def unitAccess : unit.Access := ofTestAccess unitTestAccess

theorem unit_specialized (P : BoundedFullWriter.Readers) (u : List Bool) (hu : u ∈ valid P) :
    specialized P unit u = 1 := by
  rw [specialized, ite_eq_left hu]
  change (ofTest unitTest).slice (pairFst u) (point P u) = _
  rw [ofTest_slice]
  simp only [unitTest, Polynomial.map_one]

end LeanCanny.Encoding.BoundedAlgebraicSlice

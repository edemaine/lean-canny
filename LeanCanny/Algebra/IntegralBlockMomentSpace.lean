/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockMomentCorrect

/-! # Native coefficient entries of algebra-valued matrix moments

The augmented integer block matrix is powered natively. Its output is the
requested multiplication-matrix entry of the original algebra-valued moment.
Only the original row, column, and matrix coefficient readers are supplied;
their full space costs are included.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool := by
  letI := F.ring c
  exact residueBits ((Algebra.leftMulMatrix (F.basis c)
    (borderMoment (F.row c) (F.column c) (F.matrix c) (F.exponent c)) (F.basisRow c) (F.basisCol c) : ℤ) : ZMod (F.modulus c))

noncomputable def powerFamily (F : Family) : MatrixPower.ModularFamily where
  dimension c := (F.dimension c + 2) * F.rank c
  modulus := F.modulus
  exponent c := F.exponent c + 2
  row c := finProdFinEquiv ((0 : Fin (F.dimension c + 2)), F.basisRow c)
  col c := finProdFinEquiv (Fin.last (F.dimension c + 1), F.basisCol c)
  matrix c := (F.powerMatrix c).map (Int.castRingHom (ZMod (F.modulus c)))
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def powerAccess (F : Family) (a : Access F) : MatrixPower.ModularAccess (powerFamily F) where
  dimension c := BinaryNatCode.encode ((F.dimension c + 2) * F.rank c)
  modulus c := BinaryNatCode.encode (F.modulus c)
  exponent c := BinaryNatCode.encode (F.exponent c + 2)
  row c := BinaryNatCode.encode ((powerFamily F).row c).val
  col c := BinaryNatCode.encode ((powerFamily F).col c).val
  entry := entryProgram F a
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq := entry_correct F a

theorem power_controls (F : Family) (a : Access F) : (powerAccess F a).ControlsPolyTime := by
  have HR : BinaryFn (fun c => ((powerFamily F).row c).val) :=
    BinaryFn.of_eq a.basisRow (fun c => by
      change (F.basisRow c).val = (F.basisRow c).val + F.rank c * 0
      simp only [Nat.mul_zero, Nat.add_zero])
  have HC : BinaryFn (fun c => ((powerFamily F).col c).val) :=
    a.basisCol.add (a.rank.mul (a.dimension.add (BinaryFn.const 1)))
  exact ⟨((a.dimension.add (BinaryFn.const 2)).mul a.rank).bits_mem_FP, a.modulus.bits_mem_FP,
    (a.exponent.add (BinaryFn.const 2)).bits_mem_FP, HR.bits_mem_FP, HC.bits_mem_FP⟩

theorem power_value (F : Family) : (powerFamily F).value = F.value := by
  funext c
  let := F.ring c
  rw [MatrixPower.ModularFamily.value]
  change residueBits ((((F.powerMatrix c).map (Int.castRingHom (ZMod (F.modulus c)))) ^ (F.exponent c + 2))
    (finProdFinEquiv ((0 : Fin (F.dimension c + 2)), F.basisRow c))
    (finProdFinEquiv (Fin.last (F.dimension c + 1), F.basisCol c))) = _
  rw [← Matrix.map_pow, Matrix.map_apply]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c)))
    (IntegralCoefficientBlocks.moment_coefficient (F.basis c) (F.matrix c) (F.row c) (F.column c)
      (F.exponent c) (F.basisRow c) (F.basisCol c))

theorem evaluator (F : Family) (a : Access F) (R : SpaceFunction a.row) (C : SpaceFunction a.column)
    (E : SpaceFunction a.entry) : SpaceFunction F.value :=
  (MatrixPower.ModularAccess.evaluatorWithEntry (powerAccess F a) (power_controls F a)
    (entry_evaluator F a R C E)).congr (power_value F)

end LeanCanny.Algebra.IntegralBlockMomentBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockEntry

/-! # Native relative characteristic-coefficient multiplication matrices

Integer block powering evaluates the relative Berkowitz construction.
The requested coefficient keeps its degree over the parameter algebra;
out-of-range coefficient queries return zero. Only the original algebra
matrix-entry program is supplied, and its entire space cost is charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Berkowitz.powerMatrix Matrix.charpoly

def coefficientRank (S : Source) (c : List Bool) : Fin (S.dimension c + 1) :=
  ⟨S.coefficient c % (S.dimension c + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def powerFamily (S : Source) : MatrixPower.ModularFamily where
  dimension := powerDimension S
  modulus := S.modulus
  exponent := S.dimension
  row c := finProdFinEquiv ((Berkowitz.powerQuery (S.dimension c) (coefficientRank S c)).row, S.basisRow c)
  col c := finProdFinEquiv ((Berkowitz.powerQuery (S.dimension c) (coefficientRank S c)).col, S.basisCol c)
  matrix c := (S.powerMatrix c).map (Int.castRingHom (ZMod (S.modulus c)))
  modulus_ne_zero := S.modulus_ne_zero

noncomputable def powerAccess (S : Source) (a : Access S) : MatrixPower.ModularAccess (powerFamily S) where
  dimension c := BinaryNatCode.encode (powerDimension S c)
  modulus c := BinaryNatCode.encode (S.modulus c)
  exponent c := BinaryNatCode.encode (S.dimension c)
  row c := BinaryNatCode.encode ((powerFamily S).row c).val
  col c := BinaryNatCode.encode ((powerFamily S).col c).val
  entry := entryProgram S a
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq := entry_correct S a

theorem power_controls (S : Source) (a : Access S) : (powerAccess S a).ControlsPolyTime := by
  have HK : BinaryFn (fun c => (coefficientRank S c).val) := a.coefficient.mod (a.dimension.add (BinaryFn.const 1))
  have HR : BinaryFn (fun c => ((powerFamily S).row c).val) := by
    refine BinaryFn.of_eq (a.basisRow.add (a.rank.mul HK)) (fun c => ?_)
    change (S.basisRow c).val + S.rank c * (coefficientRank S c).val =
      (S.basisRow c).val + S.rank c * ((coefficientRank S c).val + (S.dimension c + 1) * 0)
    simp only [Nat.mul_zero, Nat.add_zero]
  have HC : BinaryFn (fun c => ((powerFamily S).col c).val) := by
    refine BinaryFn.of_eq (a.basisCol.add (a.rank.mul ((a.dimension.add (BinaryFn.const 1)).mul a.dimension))) (fun c => ?_)
    change (S.basisCol c).val + S.rank c * ((S.dimension c + 1) * S.dimension c) =
      (S.basisCol c).val + S.rank c * (0 + (S.dimension c + 1) * S.dimension c)
    rw [Nat.zero_add]
  exact ⟨(IntegralCoefficientBlocks.dimension_binary a.dimension a.rank).bits_mem_FP,
    a.modulus.bits_mem_FP, a.dimension.bits_mem_FP, HR.bits_mem_FP, HC.bits_mem_FP⟩

theorem power_value (S : Source) (c : List Bool) (hk : S.coefficient c ≤ S.dimension c) :
    (powerFamily S).value c = S.value c := by
  let := S.ring c
  have HD : (coefficientRank S c).val = S.coefficient c := Nat.mod_eq_of_lt (by omega)
  have HM := IntegralCoefficientBlocks.characteristic_coefficient (S.basis c) (S.matrix c)
    (coefficientRank S c) (S.basisRow c) (S.basisCol c)
  rw [HD] at HM
  rw [MatrixPower.ModularFamily.value]
  change residueBits ((((S.powerMatrix c).map (Int.castRingHom (ZMod (S.modulus c)))) ^ S.dimension c)
    (finProdFinEquiv ((Berkowitz.powerQuery (S.dimension c) (coefficientRank S c)).row, S.basisRow c))
    (finProdFinEquiv ((Berkowitz.powerQuery (S.dimension c) (coefficientRank S c)).col, S.basisCol c))) = _
  rw [← Matrix.map_pow, Matrix.map_apply]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (S.modulus c))) HM

theorem high_value (S : Source) (c : List Bool) (hk : S.dimension c < S.coefficient c) : S.value c = [] := by
  let := S.ring c
  let := S.nontrivial c
  have HD : (S.matrix c).charpoly.natDegree < S.coefficient c := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using hk
  have HC := Polynomial.coeff_eq_zero_of_natDegree_lt HD
  simp only [Source.value, Source.coefficientMatrix, HC, map_zero, Matrix.zero_apply,
    Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

attribute [local irreducible] Source.value Source.powerMatrix entryProgram

theorem evaluator (S : Source) (a : Access S) (E : SpaceFunction a.entry) : SpaceFunction S.value := by
  have HE : SpaceFunction (powerAccess S a).entry := by
    change SpaceFunction (entryProgram S a)
    exact entry_evaluator S a E
  have P : SpaceFunction (powerFamily S).value :=
    MatrixPower.ModularAccess.evaluatorWithEntry (powerAccess S a) (power_controls S a) HE
  have Z := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have HG := a.coefficient.le a.dimension
  refine (SpaceFunction.branch (fun c => decide (S.coefficient c ≤ S.dimension c)) HG.flag_mem_FP P Z).congr ?_
  funext c
  simp only [decide_eq_true_eq]
  by_cases hk : S.coefficient c ≤ S.dimension c
  · rw [ite_eq_left hk]
    exact power_value S c hk
  · rw [ite_eq_right hk]
    exact (high_value S c (by omega)).symm

end LeanCanny.Algebra.IntegralBerkowitzBlockBits

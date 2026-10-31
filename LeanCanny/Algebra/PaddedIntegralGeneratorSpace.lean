/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterMatrix
public import LeanCanny.Algebra.IntegralNormalizationMatrixSpace

/-! # Native padded generator entries from original coefficient matrices

Shift columns use a binary identity test. Padding and invalid advertised
degrees give zero blocks. Every other block streams one normalization
product from the original coefficient matrix reader. The scalar degree,
old rank, and product length all remain binary.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  width : List Bool → ℕ
  scalarDegree : List Bool → ℕ
  selectedDegree : List Bool → ℕ
  modulus : List Bool → ℕ
  oldRow : (c : List Bool) → Fin (width c)
  oldCol : (c : List Bool) → Fin (width c)
  row : (c : List Bool) → Fin (scalarDegree c)
  col : (c : List Bool) → Fin (scalarDegree c)
  coefficient : (c : List Bool) → ℕ → Matrix (Fin (width c)) (Fin (width c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (if (F.col c).val + 1 < F.scalarDegree c then
    (if (F.row c).val = (F.col c).val + 1 then (if F.oldRow c = F.oldCol c then 1 else 0) else 0)
    else if F.selectedDegree c ≤ F.scalarDegree c ∧ F.scalarDegree c - F.selectedDegree c ≤ (F.row c).val then
      -((F.coefficient c ((F.row c).val - (F.scalarDegree c - F.selectedDegree c)) *
        F.coefficient c (F.selectedDegree c) ^
          (F.selectedDegree c - 1 - ((F.row c).val - (F.scalarDegree c - F.selectedDegree c)))) (F.oldRow c) (F.oldCol c))
    else 0)

structure Access (F : Family) where
  width : BinaryFn F.width
  scalarDegree : BinaryFn F.scalarDegree
  selectedDegree : BinaryFn F.selectedDegree
  modulus : BinaryFn F.modulus
  oldRow : BinaryFn (fun c => (F.oldRow c).val)
  oldCol : BinaryFn (fun c => (F.oldCol c).val)
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c k (i j : Fin (F.width c)),
    entry (pair c (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (F.coefficient c k i j)

noncomputable def normalizationFamily (F : Family) : IntegralNormalizationMatrixBits.Family where
  width := F.width
  degree := F.selectedDegree
  index c := (F.row c).val - (F.scalarDegree c - F.selectedDegree c)
  modulus := F.modulus
  row := F.oldRow
  col := F.oldCol
  coefficient := F.coefficient
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def normalizationAccess (F : Family) (a : Access F) :
    IntegralNormalizationMatrixBits.Access (normalizationFamily F) where
  width := a.width
  degree := a.selectedDegree
  index := a.row.sub (a.scalarDegree.sub a.selectedDegree)
  modulus := a.modulus
  row := a.oldRow
  col := a.oldCol
  entry := a.entry
  entry_eq := a.entry_eq

theorem evaluator_with_normalization (F : Family) (a : Access F)
    (HN : SpaceFunction (normalizationFamily F).negativeValue) : SpaceFunction F.value := by
  have HZ : SpaceFunction (fun c => residueBits (0 : ZMod (F.modulus c))) :=
    (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (by funext c; simp [residueBits, BinaryNatCode.encode])
  have HO : SpaceFunction (fun c => residueBits (1 : ZMod (F.modulus c))) :=
    (SpaceFunction.ofFP _ (mem_FP_comp a.modulus.bits_mem_FP ArithmeticBits.one_mem_FP)).congr
      (funext fun c => ArithmeticBits.one_residueBits (F.modulus c))
  have HS := SpaceFunction.branch (fun c => decide (F.oldRow c = F.oldCol c))
    (a.oldRow.eq a.oldCol).flag_mem_FP HO HZ
  have HI := SpaceFunction.branch (fun c => decide ((F.row c).val = (F.col c).val + 1))
    (a.row.eq (a.col.add (BinaryFn.const 1))).flag_mem_FP HS HZ
  have HP := SpaceFunction.branch (fun c => decide
    (F.selectedDegree c ≤ F.scalarDegree c ∧ F.scalarDegree c - F.selectedDegree c ≤ (F.row c).val))
    ((a.selectedDegree.le a.scalarDegree).and ((a.scalarDegree.sub a.selectedDegree).le a.row)).flag_mem_FP HN HZ
  have HT := SpaceFunction.branch (fun c => decide ((F.col c).val + 1 < F.scalarDegree c))
    ((a.col.add (BinaryFn.const 1)).lt a.scalarDegree).flag_mem_FP HI HP
  refine HT.congr (funext fun c => ?_)
  simp only [Family.value, IntegralNormalizationMatrixBits.Family.negativeValue, normalizationFamily,
    decide_eq_true_eq]
  split_ifs <;> rfl

theorem value_packet {A : Type*} [CommRing A] [Nontrivial A] (F : Family) (c : List Bool)
    (b : Module.Basis (Fin (F.width c)) ℤ A) (p : Polynomial A)
    (hc : ∀ k, F.coefficient c k = (Algebra.leftMulMatrix b (p.coeff k)).map (Int.castRingHom (ZMod (F.modulus c)))) :
    F.value c = residueBits
      ((Algebra.leftMulMatrix (b.smulTower (IntegralCoordinateBasis.relativeBasis
        (PaddedIntegralNormalization.polynomial p (F.selectedDegree c) (F.scalarDegree c))
        (PaddedIntegralNormalization.monic _ _ _) (PaddedIntegralNormalization.natDegree _ _ _)))
        (AdjoinRoot.root _) (F.oldRow c, F.row c) (F.oldCol c, F.col c) : ℤ) : ZMod (F.modulus c)) := by
  rw [Family.value, PaddedIntegralParameterExtension.tower_root_matrix]
  split_ifs <;> try simp only [Int.cast_one, Int.cast_zero]
  rw [hc, hc, ← Matrix.map_pow, ← Matrix.map_mul]
  simp only [Matrix.map_apply, Int.cast_neg]
  rfl

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value :=
  evaluator_with_normalization F a
    (IntegralNormalizationMatrixBits.negative_evaluator (normalizationFamily F) (normalizationAccess F a) E)

end LeanCanny.Algebra.PaddedIntegralGeneratorBits

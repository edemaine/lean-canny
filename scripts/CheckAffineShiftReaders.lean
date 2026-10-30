import LeanCanny.Encoding.AffineShiftCoordinateSpace

/-! Native coordinate polynomials from original rows and genuine height shifts.
Run with `lake env lean -DwarningAsError=true scripts/CheckAffineShiftReaders.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation MatrixPower
open MacaulayFullBoxBits (ctx uv shift ctx_FP uv_FP shift_FP)
open scoped Classical

namespace AffineShiftReaderRegression
noncomputable section

private def F : AffineShiftCoordinateBits.Family where
  arity _ := 1
  width _ := 1
  degree _ _ := 1
  rows _ i := MvPolynomial.X i
  shifts _ _ := Polynomial.X
  coordinate _ := 0

private lemma width (c : List Bool) : F.width c = AffineRingCoordinates.width
    (fun i : Fin (F.arity c) => F.degree c i.val) := by
  norm_num [F, AffineRingCoordinates.width, Macaulay.level, AffineRingGramEliminant.degrees,
    Fin.sum_univ_succ]

private lemma degree : BinaryFn (fun q => F.degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) := BinaryFn.const 1

private lemma controls : F.parameter.affine.homogeneous.layout.Controls := F.controls (UnaryFn.const 1) degree width

private lemma modulus_FP : (fun q => pairSnd (ctx q)) ∈ FP := mem_FP_comp ctx_FP pairSnd_mem_FP

private lemma originalEvaluator : SpaceFunction F.integerCoefficient :=
  FixedWidthRowBits.variable_evaluator _ _ F.row shift (fun q => pairSnd (ctx q))
    (UnaryFn.const 1) (UnaryFn.const 1) (F.row_unary controls) shift_FP modulus_FP

private lemma shiftEvaluator : SpaceFunction F.shiftCoefficient := by
  have hk : (fun q => pairFst (uv q)) ∈ FP := mem_FP_comp uv_FP pairFst_mem_FP
  have E1 := SpaceFunction.ofFP _ (mem_FP_comp (mem_FP_comp modulus_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP)
  have E := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairFst (uv q)) = 1))
    ((BinaryFn.fromBits hk).eq (BinaryFn.const 1)).flag_mem_FP E1 (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine E.congr (funext fun q => ?_)
  change (if decide (Nat.fromBitsLE (pairFst (uv q)) = 1) then
    ArithmeticBits.one (BinaryNat.succ (pairSnd (ctx q))) else []) =
      residueBits (((Polynomial.X : Polynomial ℤ).coeff (Nat.fromBitsLE (pairFst (uv q)))) : ZMod _)
  simp only [decide_eq_true_eq, Polynomial.coeff_X, eq_comm (a := (1 : ℕ))]
  split_ifs
  · rw [BinaryNat.succ_eq_bits]
    exact ArithmeticBits.one_residueBits _
  · simp [residueBits, BinaryNatCode.encode]

-- The actual affine-shift coordinate certificate is computed, with no
-- homogeneous coefficient, determinant, level, or width reader supplied.
example : CertifiedPolynomial.BivariateReader (fun c => Geometry.AffineShiftCoordinates.coordinate
    (F.rows c) (F.shifts c) (fun i => F.degree c i.val) (F.coordinate c)) := by
  apply F.canonicalReader (UnaryFn.const 1) degree (UnaryFn.const 0) (fun _ => 1) (BinaryFn.const 1)
    _ width originalEvaluator shiftEvaluator
  intro c i
  simp [F]

-- The computed polynomial retains the moving root x = t at every parameter.
example (t : ℝ) : (F.parameter.annihilator []).eval₂
    (SymbolicScaledSquarefree.scalarEvaluation t) t = 0 := by
  rw [F.annihilator_eq [] (width [])]
  refine AffineRingCoordinates.eval_eq_zero _ _ _ ?_ (fun _ => t) ?_ (F.coordinate [])
  · intro i
    apply AffineConstantParameterShift.degree_le
    intro j
    exact (MvPolynomial.totalDegree_X (R := ℤ) j).le
  · intro i
    rw [AffineConstantParameterShift.eval]
    change (MvPolynomial.X i : MvPolynomial (Fin (F.arity [])) ℤ).eval₂ (Int.castRingHom ℝ) (fun _ => t) -
      (SymbolicScaledSquarefree.scalarEvaluation t) Polynomial.X = 0
    rw [MvPolynomial.eval₂_X]
    simp [SymbolicScaledSquarefree.scalarEvaluation]

end
end AffineShiftReaderRegression

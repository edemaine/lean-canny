/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineParameterCoordinateSpace
public import LeanCanny.Algebra.PolynomialParameterShiftSpace
public import LeanCanny.Geometry.AffineShiftCoordinates

/-! # Native complete coordinate readers for varying affine heights

The original integer row coefficients and the polynomial height shifts
construct the full coordinate annihilator. Both source costs are retained.
The polynomial is exactly the coordinate certificate used by the affine slab
arcs when the native width agrees with its canonical Macaulay width.
-/

@[expose] public section
namespace LeanCanny.Encoding.AffineShiftCoordinateBits
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open MacaulayFullBoxBits (ctx idx shift uv ctx_FP idx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ → ℕ
  rows : (c : List Bool) → Fin (arity c) → MvPolynomial (Fin (arity c)) ℤ
  shifts : (c : List Bool) → Fin (arity c) → Polynomial ℤ
  coordinate : (c : List Bool) → Fin (arity c)

noncomputable def Family.parameter (F : Family) : AffineParameterCoordinateBits.Family where
  arity := F.arity
  width := F.width
  degree := F.degree
  rows c := AffineConstantParameterShift.system (F.rows c) (F.shifts c)
  coordinate := F.coordinate

/-- Canonical Macaulay metadata is computed from the original dimension and
binary row allowances. In particular, neither the level nor its width is an
additional metadata oracle. -/
theorem Family.controls (F : Family) (hn : UnaryFn F.arity)
    (hd : BinaryFn (fun q => F.degree (pairFst q) (Nat.fromBitsLE (pairSnd q))))
    (hw : ∀ c, F.width c = AffineRingCoordinates.width (fun i : Fin (F.arity c) => F.degree c i.val)) :
    F.parameter.affine.homogeneous.layout.Controls := by
  have hi := bits_mem_FP UnaryFn.index
  have hr : BinaryFn (fun q => F.degree (pairFst q) (pairSnd q).length) := by
    apply BinaryFn.of_eq (hd.comp (mem_FP_pair pairFst_mem_FP hi))
    intro q
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits]
  have hterm := hr.sub (BinaryFn.const 1)
  have hs := (BinaryFn.sum hn hterm).add (BinaryFn.const 1)
  have hl : BinaryFn (fun c => Macaulay.level (AffineRingGramEliminant.degrees
      (fun i : Fin (F.arity c) => F.degree c i.val))) := by
    apply hs.of_eq
    intro c
    simp only [pairFst_pair, pairSnd_pair,
      List.length_replicate, Macaulay.level, AffineRingGramEliminant.degrees, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, Nat.sub_self, zero_add]
    exact congrArg (fun z => z + 1) (Fin.sum_univ_eq_sum_range (fun i => F.degree c i - 1) (F.arity c)).symm
  have hwidth : UnaryFn F.width := (UnaryFn.length hl.bits_mem_FP).of_eq (fun c =>
    (Nat.size_eq_bits_len _).trans (hw c).symm)
  refine ⟨hn.add (UnaryFn.const 1), hwidth, hl, ?_⟩
  have hidx := (BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.const 1)
  have ht : BinaryFn (fun q => F.degree (pairFst q) (Nat.fromBitsLE (pairSnd q) - 1)) := by
    apply BinaryFn.of_eq (hd.comp (mem_FP_pair pairFst_mem_FP hidx.bits_mem_FP))
    intro q
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hz := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)
  apply (BinaryFn.ite hz (BinaryFn.const 1) ht).of_eq
  intro q
  rfl

noncomputable def Family.row (F : Family) (q : List Bool) : Fin (F.arity (base q)) :=
  ⟨min (Nat.fromBitsLE (idx q)) (F.arity (base q) - 1), by
    have := (F.coordinate (base q)).isLt
    omega⟩

lemma Family.row_unary (F : Family) (h : F.parameter.affine.homogeneous.layout.Controls) :
    UnaryFn (fun q => (F.row q).val) :=
  UnaryFn.fromBitsLE_min idx_FP (((F.parameter.affine.arity_unary h).comp base_FP).sub (UnaryFn.const 1))

noncomputable def Family.selected (F : Family) (q : List Bool) : MvPolynomial (Fin (F.arity (base q))) ℤ :=
  F.rows (base q) (F.row q)

noncomputable def Family.selectedShift (F : Family) (q : List Bool) : Polynomial ℤ :=
  F.shifts (base q) (F.row q)

noncomputable def Family.integerCoefficient (F : Family) : List Bool → List Bool :=
  FixedWidthRowBits.value (F.arity ∘ base) (F.width ∘ base) F.selected shift (fun q => pairSnd (ctx q))

noncomputable def Family.shiftCoefficient (F : Family) : List Bool → List Bool :=
  PolynomialParameterShiftBits.scalar F.selectedShift (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))

theorem Family.rowEvaluator (F : Family) (h : F.parameter.affine.homogeneous.layout.Controls)
    (EP : SpaceFunction F.integerCoefficient) (ES : SpaceFunction F.shiftCoefficient) :
    SpaceFunction F.parameter.rowCoefficient := by
  have E := PolynomialParameterShiftBits.evaluator
    ((F.parameter.affine.arity_unary h).comp base_FP) (h.width.comp base_FP)
    F.selected F.selectedShift shift (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))
    shift_FP (mem_FP_comp uv_FP pairFst_mem_FP) (mem_FP_comp ctx_FP pairSnd_mem_FP) EP ES
  exact E.congr (funext fun _ => rfl)

noncomputable def Family.reader (F : Family) (h : F.parameter.affine.homogeneous.layout.Controls)
    (hc : UnaryFn (fun c => (F.coordinate c).val)) (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i, (F.shifts c i).natDegree ≤ B c)
    (EP : SpaceFunction F.integerCoefficient) (ES : SpaceFunction F.shiftCoefficient) :
    CertifiedPolynomial.BivariateReader F.parameter.annihilator :=
  F.parameter.reader h hc B hB
    (fun c i u => (AffineConstantParameterShift.parameter_degree_le (F.rows c) (F.shifts c) i u).trans (hbound c i))
    (F.rowEvaluator h EP ES)

lemma Family.annihilator_eq (F : Family) (c : List Bool)
    (hw : F.width c = AffineRingCoordinates.width (fun i : Fin (F.arity c) => F.degree c i.val)) :
    F.parameter.annihilator c = Geometry.AffineShiftCoordinates.coordinate (F.rows c) (F.shifts c)
      (fun i => F.degree c i.val) (F.coordinate c) := by
  change AffineRingGramEliminant.annihilator _ _ (F.width c) _ = _
  rw [hw]
  rfl

/-- The canonical reader computes the actual coordinate polynomial used in
the constructed affine-height slabs, rather than an arbitrary annihilator. -/
noncomputable def Family.canonicalReader (F : Family) (hn : UnaryFn F.arity)
    (hd : BinaryFn (fun q => F.degree (pairFst q) (Nat.fromBitsLE (pairSnd q))))
    (hc : UnaryFn (fun c => (F.coordinate c).val)) (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i, (F.shifts c i).natDegree ≤ B c)
    (hw : ∀ c, F.width c = AffineRingCoordinates.width (fun i : Fin (F.arity c) => F.degree c i.val))
    (EP : SpaceFunction F.integerCoefficient) (ES : SpaceFunction F.shiftCoefficient) :
    CertifiedPolynomial.BivariateReader (fun c => Geometry.AffineShiftCoordinates.coordinate
      (F.rows c) (F.shifts c) (fun i => F.degree c i.val) (F.coordinate c)) := by
  have he := funext (fun c => F.annihilator_eq c (hw c))
  exact he ▸ F.reader (F.controls hn hd hw) hc B hB hbound EP ES

noncomputable def Family.coordinateDegree (F : Family) (c : List Bool) : ℕ :=
  ProjectiveValueGram.dimension (F.arity c) (F.width c) + 1

theorem Family.coordinateDegree_binary (F : Family) (hn : UnaryFn F.arity)
    (hd : BinaryFn (fun q => F.degree (pairFst q) (Nat.fromBitsLE (pairSnd q))))
    (hw : ∀ c, F.width c = AffineRingCoordinates.width (fun i : Fin (F.arity c) => F.degree c i.val)) :
    BinaryFn F.coordinateDegree :=
  (F.parameter.affine.homogeneous.dimension_binary (F.controls hn hd hw)).add (BinaryFn.const 1)

/-- No exact-degree scan is needed for the grid's coordinate metadata.
Infinity exclusion proves that the native determinant allowance is exact. -/
theorem Family.coordinate_degree_eq (F : Family) (c : List Bool)
    (hd : ∀ i : Fin (F.arity c), 0 < F.degree c i.val)
    (hcone : AffineFiniteCoordinates.NoInfinity (F.rows c) (fun i => F.degree c i.val))
    (hw : F.width c = AffineRingCoordinates.width (fun i : Fin (F.arity c) => F.degree c i.val)) :
    (Geometry.AffineShiftCoordinates.coordinate (F.rows c) (F.shifts c)
      (fun i => F.degree c i.val) (F.coordinate c)).natDegree = F.coordinateDegree c := by
  have he := (AffineRingCoordinates.exact_degree_and_positive_leading
    (SymbolicScaledSquarefree.scalarEvaluation 0) (AffineConstantParameterShift.system (F.rows c) (F.shifts c))
    (fun i => F.degree c i.val) hd
    (AffineConstantParameterShift.noInfinity (F.rows c) (F.shifts c) (fun i => F.degree c i.val) hd hcone _)
    (F.coordinate c)).1
  change _ = AffineRingGramEliminant.dimension (F.arity c)
    (AffineRingCoordinates.width (fun i : Fin (F.arity c) => F.degree c i.val)) + 1 at he
  rw [← hw] at he
  exact he

end LeanCanny.Encoding.AffineShiftCoordinateBits

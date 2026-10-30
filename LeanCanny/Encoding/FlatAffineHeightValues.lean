/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightGrid
public import LeanCanny.Algebra.IntegerGridValueGramSpace
public import LeanCanny.Algebra.UniformValueGramControls
public import LeanCanny.Algebra.SingleParameterShiftSpace
public import LeanCanny.Algebra.AffineValueGramBounds
public import LeanCanny.Geometry.IntegerGridValueReader
public import LeanCanny.Encoding.FlatAffinePowerInfinity
public import LeanCanny.Encoding.FlatAffinePowerBounds

/-! # Native equation-value certificates on actual varying-height grids

The original affine source and signed records compute every coordinate
polynomial and the selected shifted equation. Binary determinant degree
allowances supply the grid metadata. No coordinate or value coefficient
reader is an additional premise.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightValues
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open MacaulayFullBoxBits (ctx shift uv ctx_FP shift_FP uv_FP)
open AffineValueGramBits (base base_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinateDegree (F : Inputs) (u : List Bool) : ℕ := FlatAffinePowerGramLayout.dimension F u + 1

noncomputable def testDegree (F : Inputs) (row : (u : List Bool) → Fin (count F u)) (u : List Bool) : ℕ :=
  FlatAffinePowerPositive.degree F u (row u)

noncomputable def width (F : Inputs) (row : (u : List Bool) → Fin (count F u)) (u : List Bool) : ℕ :=
  (Macaulay.level (ProjectiveValueGram.degrees (fun _ : Fin (count F u) => coordinateDegree F u) (testDegree F row u))).size

noncomputable def family (F : Inputs) (height row : (u : List Bool) → Fin (count F u)) : IntegerGridValueGramBits.Family where
  arity := count F
  width := width F row
  degree u _ := coordinateDegree F u
  testDegree := testDegree F row
  coordinate := FlatAffineHeightGrid.coordinate F height
  test u := AffineConstantParameterShift.system (FlatAffinePowerPositive.system F u)
    (fun i => if i = height u then Polynomial.X else 0) (row u)

lemma annihilator_comp (F : Inputs) (height row : (u : List Bool) → Fin (count F u))
    (f : List Bool → List Bool) (u : List Bool) :
    (family (FlatAffineFullSourceContext.comp F f) (fun z => height (f z)) (fun z => row (f z))).affine.homogeneous.annihilator u =
      (family F height row).affine.homogeneous.annihilator (f u) := by
  have hs := funext (FlatAffinePowerPositive.system_comp F f u)
  have hc := funext (FlatAffineHeightGrid.coordinate_comp F height f u)
  have hdim : coordinateDegree (FlatAffineFullSourceContext.comp F f) u = coordinateDegree F (f u) := by
    unfold coordinateDegree FlatAffinePowerGramLayout.dimension
    rw [FlatAffinePowerGramLayout.width_eq, FlatAffinePowerGramLayout.width_eq]
    rfl
  dsimp only [ProjectiveValueGramBits.Family.annihilator, AffineValueGramBits.Family.homogeneous,
    IntegerGridValueGramBits.Family.affine, family]
  simp only [hc, hs, hdim, testDegree, width]
  rfl

lemma annihilator_row_congr (F : Inputs) (height row row' : (u : List Bool) → Fin (count F u))
    (u : List Bool) (hr : row u = row' u) :
    (family F height row).affine.homogeneous.annihilator u =
      (family F height row').affine.homogeneous.annihilator u := by
  dsimp only [ProjectiveValueGramBits.Family.annihilator, AffineValueGramBits.Family.homogeneous,
    IntegerGridValueGramBits.Family.affine, family, width, testDegree]
  rw [hr]

theorem coordinateDegree_binary {F : Inputs} (h : F.Access) : BinaryFn (coordinateDegree F) :=
  (FlatAffinePowerGramLayout.dimension_binary h).add (BinaryFn.const 1)

theorem controls {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hr : UnaryFn (fun u => (row u).val)) : (family F height row).affine.homogeneous.layout.Controls :=
  (family F height row).affine.homogeneous.uniform_controls (coordinateDegree F)
    (FlatAffineFullSourcePositive.count_unary h) (coordinateDegree_binary h)
    (BinaryFn.ofUnary (FlatAffinePowerPositive.degree_unary h row hr)) (fun _ _ => rfl) (fun _ => rfl)

theorem testEvaluator {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (hr : UnaryFn (fun u => (row u).val)) :
    SpaceFunction (family F height row).testCoefficient := by
  have hn := (FlatAffineFullSourcePositive.count_unary h).comp base_FP
  have hw := (controls h height row hr).width.comp base_FP
  have hm : (fun q => pairSnd (ctx q)) ∈ FP := mem_FP_comp ctx_FP pairSnd_mem_FP
  have hk : (fun q => pairFst (uv q)) ∈ FP := mem_FP_comp uv_FP pairFst_mem_FP
  have EP := FlatAffinePowerPositive.evaluator (FlatAffineFullSourceContext.access h base_FP)
    (fun q => row (base q)) (hr.comp base_FP) hw shift_FP hm
  have EP' : SpaceFunction (FixedWidthRowBits.value (fun q => count F (base q)) (fun q => width F row (base q))
      (fun q => FlatAffinePowerPositive.system F (base q) (row (base q))) shift (fun q => pairSnd (ctx q))) := by
    refine EP.congr (funext fun q => ?_)
    change residueBits (((FlatAffinePowerPositive.system (FlatAffineFullSourceContext.comp F base) q (row (base q))).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (width F row (base q))
        (Nat.fromBitsLE (shift q)))) : ZMod (Nat.fromBitsLE (pairSnd (ctx q)) + 1)) = _
    rw [FlatAffinePowerPositive.system_comp]
    rfl
  have ES := PolynomialParameterShiftBits.singleScalarEvaluator (fun q => (row (base q)).val)
    (fun q => (height (base q)).val) (hr.comp base_FP) (hh.comp base_FP)
    (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) hk hm
  have ES' : SpaceFunction (PolynomialParameterShiftBits.scalar
      (fun q => if row (base q) = height (base q) then Polynomial.X else 0)
      (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))) :=
    ES.congr (funext fun q => by simp only [PolynomialParameterShiftBits.scalar, Fin.ext_iff])
  have E := PolynomialParameterShiftBits.evaluator hn hw
    (fun q => FlatAffinePowerPositive.system F (base q) (row (base q)))
    (fun q => if row (base q) = height (base q) then Polynomial.X else 0)
    shift (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) shift_FP hk hm EP' ES'
  exact E.congr (funext fun _ => rfl)

lemma dimension_eq (F : Inputs) (u : List Bool) :
    FlatAffinePowerGramLayout.dimension F u = AffineRingCoordinates.dimension (FlatAffinePowerPositive.degree F u) := by
  unfold FlatAffinePowerGramLayout.dimension AffineRingCoordinates.dimension
  rw [FlatAffinePowerGramLayout.width_eq]
  rfl

lemma coordinate_inner_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u)) (k : ℕ) :
    ((FlatAffineHeightGrid.coordinate F height u i).coeff k).natDegree ≤ coordinateDegree F u := by
  have h := Geometry.AffineShiftCoordinates.coordinate_parameter_degree_le (FlatAffinePowerPositive.system F u)
    (fun j => if j = height u then Polynomial.X else 0) (FlatAffinePowerPositive.degree F u) 1
    (fun j => by split_ifs <;> simp) i k
  simp only [Nat.mul_one] at h
  exact h.trans ((dimension_eq F u).symm.le.trans (Nat.le_succ _))

lemma test_inner_bound (F : Inputs) (height row : (u : List Bool) → Fin (count F u))
    (u : List Bool) (e : Fin (count F u) →₀ ℕ) :
    (((family F height row).test u).coeff e).natDegree ≤ coordinateDegree F u := by
  have h := AffineConstantParameterShift.parameter_degree_le (FlatAffinePowerPositive.system F u)
    (fun i => if i = height u then Polynomial.X else 0) (row u) e
  have hs : (if row u = height u then (Polynomial.X : Polynomial ℤ) else 0).natDegree ≤ 1 := by
    split_ifs <;> simp
  exact h.trans (hs.trans (Nat.le_add_left 1 _))

/-- Complete native value access from the actual source, with all grid
coordinate readers, homogenization, and both Gram determinants internal. -/
noncomputable def reader {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (hr : UnaryFn (fun u => (row u).val)) :
    CertifiedPolynomial.BivariateReader (family F height row).affine.homogeneous.annihilator :=
  (family F height row).reader (controls h height row hr) (coordinateDegree F) (coordinateDegree_binary h)
    (coordinate_inner_bound F height) (test_inner_bound F height row)
    (FlatAffineHeightGrid.coefficientEvaluator h height hh) (testEvaluator h height row hh hr)

theorem coordinate_degree_eq (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (i : Fin (count F u)) :
    (FlatAffineHeightGrid.coordinate F height u i).natDegree = coordinateDegree F u := by
  have he := (AffineRingCoordinates.exact_degree_and_positive_leading
    (SymbolicScaledSquarefree.scalarEvaluation 0)
    (AffineConstantParameterShift.system (FlatAffinePowerPositive.system F u)
      (fun j => if j = height u then Polynomial.X else 0)) (FlatAffinePowerPositive.degree F u)
    (FlatAffinePowerPositive.degree_pos F u)
    (AffineConstantParameterShift.noInfinity (FlatAffinePowerPositive.system F u)
      (fun j => if j = height u then Polynomial.X else 0) (FlatAffinePowerPositive.degree F u)
      (FlatAffinePowerPositive.degree_pos F u) (FlatAffinePowerPositive.noInfinity F hcone u) _) i).1
  change (FlatAffineHeightGrid.coordinate F height u i).natDegree =
    AffineRingCoordinates.dimension (FlatAffinePowerPositive.degree F u) + 1 at he
  exact he.trans (congrArg (fun z => z + 1) (dimension_eq F u).symm)

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height row : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (family F height row).affine.homogeneous.annihilator u ≠ 0 := by
  apply (family F height row).ne_zero u
  · intro i
    exact (coordinate_degree_eq F hcone height u i).symm
  · intro i
    change 0 < (FlatAffineHeightGrid.coordinate F height u i).natDegree
    rw [coordinate_degree_eq F hcone height u i]
    exact Nat.zero_lt_succ _
  · exact FlatAffinePowerPositive.degree_pos F u (row u)
  · exact Nat.lt_size_self _

/-- The native value polynomial retains the equation value at every grid
root over every field specialization. No regularity or cone premise is needed. -/
theorem eval_eq_zero (F : Inputs) (height row : (u : List Bool) → Fin (count F u))
    (u : List Bool) {K : Type*} [Field K] (rho : Polynomial ℤ →+* K) (x : Fin (count F u) → K)
    (hx : ∀ i, (FlatAffineHeightGrid.coordinate F height u i).eval₂ rho (x i) = 0) :
    ((family F height row).affine.homogeneous.annihilator u).eval₂ rho
      (((family F height row).test u).eval₂ rho x) = 0 := by
  refine (family F height row).eval_eq_zero u rho x ?_ ?_ (Nat.lt_size_self _) hx
  · intro i
    exact (Geometry.AffineShiftCoordinates.coordinate_degree_le (FlatAffinePowerPositive.system F u)
      (fun j => if j = height u then Polynomial.X else 0) (FlatAffinePowerPositive.degree F u) i).trans
      (congrArg (fun z => z + 1) (dimension_eq F u).symm).le
  · exact AffineConstantParameterShift.degree_le _ _ _ (FlatAffinePowerPositive.polynomial_degree F u) (row u)

noncomputable def valueDimension (F : Inputs) (row : (u : List Bool) → Fin (count F u)) (u : List Bool) : ℕ :=
  ProjectiveValueGram.dimension (count F u) (width F row u)

theorem valueDimension_binary {F : Inputs} (h : F.Access) (height row : (u : List Bool) → Fin (count F u))
    (hr : UnaryFn (fun u => (row u).val)) : BinaryFn (valueDimension F row) :=
  (family F height row).affine.homogeneous.dimension_binary (controls h height row hr)

theorem degree_le (F : Inputs) (height row : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    ((family F height row).affine.homogeneous.annihilator u).natDegree ≤ valueDimension F row u + 1 :=
  ProjectiveValueGram.annihilator_degree_le _ _ _ _ _

theorem parameter_degree_le (F : Inputs) (height row : (u : List Bool) → Fin (count F u)) (u : List Bool) (k : ℕ) :
    (((family F height row).affine.homogeneous.annihilator u).coeff k).natDegree ≤
      valueDimension F row u * coordinateDegree F u := by
  let G := family F height row
  have hb := G.original_inner_bound (coordinateDegree F) (coordinate_inner_bound F height) (test_inner_bound F height row)
  exact G.affine.parameter_degree_le (coordinateDegree F) hb u k

end LeanCanny.Encoding.FlatAffineHeightValues

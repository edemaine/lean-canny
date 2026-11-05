/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedSlackRadiusModel
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource

/-! # A formal radius presentation of the actual marked integer prelude

The old candidate algebra and coordinate leaves are fixed. The sphere,
regular slack and four dyadic leaves use the same formal physical radius.
The existing native tag dispatcher is retained, including its default leaf.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR Polynomial
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliarySlackMatrix (parameters count charge)
open IntegralMixedAuxiliaryMarkedIntegerSource (number tag oldKey tail coordinateQuery)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def sphere (key : List Bool) : (ℤ[X])[X] :=
  IntegralMixedFramedSlackRadiusModel.spherePolynomial (parameters n t) (planAt hn ht ha)
    (dataAt hn ht ha) (count n) key

noncomputable def regular (key : List Bool) : (ℤ[X])[X] :=
  IntegralMixedFramedSlackRadiusModel.regularPolynomial (parameters n t) (planAt hn ht ha)
    (dataAt hn ht ha) (count n) (charge t) key

theorem sphere_map_eval (R : List Bool → ℕ) (key : List Bool) :
    (sphere hn ht ha key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R key)) =
      (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha R).polynomial key := by
  exact IntegralMixedFramedSlackRadiusModel.spherePolynomial_map_eval (parameters n t)
    (planAt hn ht ha) (dataAt hn ht ha) (IntegralMixedAuxiliarySlackSource.syntaxInput hn ht ha)
    (IntegralMixedAuxiliarySlackSource.inputs hn ht ha) (count n) R key

theorem regular_map_eval (R : List Bool → ℕ) (key : List Bool) :
    (regular hn ht ha key).map (Polynomial.evalRingHom ((2 : ℤ) ^ R key)) =
      (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha R).polynomial key := by
  exact IntegralMixedFramedSlackRadiusModel.regularPolynomial_map_eval (parameters n t)
    (planAt hn ht ha) (dataAt hn ht ha) (IntegralMixedAuxiliarySlackSource.syntaxInput hn ht ha)
    (IntegralMixedAuxiliarySlackSource.inputs hn ht ha) (count n) (charge t) R key

noncomputable def constant (p : ℤ[X]) : (ℤ[X])[X] := p.map (Polynomial.C : ℤ →+* ℤ[X])

theorem constant_map_eval (p : ℤ[X]) (r : ℤ) :
    (constant p).map (Polynomial.evalRingHom r) = p := by
  rw [constant, Polynomial.map_map]
  have h : (Polynomial.evalRingHom r).comp (Polynomial.C : ℤ →+* ℤ[X]) = RingHom.id ℤ := by
    ext z
    exact Polynomial.eval_C
  rw [h, Polynomial.map_id]

noncomputable def powerLeaf (offset slope : ℕ) : (ℤ[X])[X] :=
  Polynomial.X - Polynomial.C (IntegralMixedFramedSlackRadiusModel.power offset slope)

theorem powerLeaf_map_eval (offset slope R : ℕ) :
    (powerLeaf offset slope).map (Polynomial.evalRingHom ((2 : ℤ) ^ R)) =
      PowerIntegerPolynomial.polynomial False (offset + slope * R) := by
  simp only [powerLeaf, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coe_evalRingHom, IntegralMixedFramedSlackRadiusModel.power_eval,
    PowerIntegerPolynomial.polynomial, PowerIntegerPolynomial.value, ite_false]

noncomputable def polynomial (q : List Bool) : (ℤ[X])[X] :=
  let ctx := pairFst q
  let saved := oldKey n t ctx
  let N := count n saved
  let D := charge t saved
  if tag q < number n ctx then
    constant ((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial (coordinateQuery n q))
  else if tag q = number n ctx then sphere hn ht ha saved
  else if tag q = number n ctx + 2 then regular hn ht ha saved
  else if tag q = number n ctx + 4 then powerLeaf 0 1
  else if tag q = number n ctx + 5 then
    powerLeaf (BoundedRegularSource.regularizationExponent N D D 0) (BoundedRegularRadius.regularizationSlope N D)
  else if tag q = number n ctx + 6 then
    powerLeaf (BoundedZeroSource.perturbationExponent N D D 0) (BoundedRegularRadius.perturbationSlope N D)
  else if tag q = number n ctx + 7 then
    powerLeaf (BoundedZeroSource.penaltyExponent N D 0) (BoundedZeroSource.powerDegree D)
  else Polynomial.X

theorem polynomial_map_eval (R : List Bool → ℕ) (q : List Bool) :
    (polynomial hn ht ha q).map (Polynomial.evalRingHom ((2 : ℤ) ^ R (pairFst q))) =
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial q := by
  have hs := sphere_map_eval hn ht ha (R ∘ tail) (oldKey n t (pairFst q))
  have hr := regular_map_eval hn ht ha (R ∘ tail) (oldKey n t (pairFst q))
  simp only [Function.comp_apply, IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail] at hs hr
  simp only [polynomial, IntegralMixedAuxiliaryMarkedIntegerSource.source,
    IntegerPolynomialSourceChoice.choose, IntegerPolynomialSourceChoice.reindex,
    PowerIntegerPolynomial.source, IntegerPolynomialZeroRootSource.source, Function.comp_apply]
  split_ifs
  · exact constant_map_eval _ _
  · exact hs
  · exact hr
  · simpa only [Nat.zero_add, Nat.one_mul] using powerLeaf_map_eval 0 1 (R (pairFst q))
  · rw [powerLeaf_map_eval, ← BoundedRegularRadius.regularization_affine]
    simp only [IntegralMixedAuxiliaryParametricSlackSource.regularizationAt, Function.comp_apply,
      IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
  · rw [powerLeaf_map_eval, ← BoundedRegularRadius.perturbation_affine]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.beta, Function.comp_apply,
      IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
  · rw [powerLeaf_map_eval, ← BoundedRegularRadius.penalty_affine]
    simp only [IntegralMixedAuxiliaryParametricSlackSource.penaltyAt, Function.comp_apply,
      IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
  · rw [Polynomial.map_X]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusModel

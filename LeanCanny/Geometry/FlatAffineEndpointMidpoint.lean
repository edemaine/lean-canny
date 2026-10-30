/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointTrailing
public import LeanCanny.Encoding.FlatAffineEndpointValidity
public import LeanCanny.Geometry.AlgebraicBranchSign
public import LeanCanny.Algebra.FrozenAffineLift
public import LeanCanny.Geometry.EndpointMidpoint

/-! # Computed midpoint certificates control actual endpoint branches

Valid degree records capture every original extended root. The native value
annihilator therefore annihilates every branch midpoint test. Avoiding its
computed trailing factor makes both strict midpoint signs constant.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineEndpointMidpoint
open Set LeanCanny.Algebra LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def rows (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :=
  AffineShiftCoordinates.rows (FlatAffineEndpointPreparation.system F height r)
    (fun i => if i = FlatAffineEndpointGram.active F height r then Polynomial.X else 0)

theorem coordinate_degree_eq (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (i : Fin (FlatAffineEndpointRows.arity F r)) :
    (FlatAffineEndpointGrid.coordinate F height r i).natDegree = FlatAffineEndpointValues.coordinateDegree F r := by
  let p := FlatAffineEndpointPreparation.system F height r
  let d := FlatAffineEndpointPreparation.degrees F r
  let c := fun j => if j = FlatAffineEndpointGram.active F height r then (Polynomial.X : Polynomial ℤ) else 0
  have hd := FlatAffineEndpointValidity.degrees_pos F hcone height r hr a ha
  have hp := FlatAffineEndpointValidity.noInfinity F hcone height r hr a ha
  exact (AffineRingCoordinates.exact_degree_and_positive_leading
    (SymbolicScaledSquarefree.scalarEvaluation 0) (AffineConstantParameterShift.system p c) d hd
    (AffineConstantParameterShift.noInfinity p c d hd hp _) i).1

theorem nonzero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (index : (r : List Bool) → Fin (count F (pairFst r)))
    (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    FlatAffineEndpointTrailing.polynomial F height index r ≠ 0 := by
  apply (FlatAffineEndpointValues.family F height index).ne_zero r
  · intro i
    exact (coordinate_degree_eq F hcone height r hr a ha i).symm
  · intro i
    change 0 < (FlatAffineEndpointGrid.coordinate F height r i).natDegree
    rw [coordinate_degree_eq F hcone height r hr a ha i]
    exact Nat.zero_lt_succ _
  · exact Nat.zero_lt_one
  · exact Nat.lt_size_self _

theorem coordinate_root (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r) (t : ℝ)
    (x : Fin (FlatAffineEndpointRows.arity F r) → ℝ) (hx : PolynomialGridValues.value (rows F height r) (t, x) = 0)
    (i : Fin (FlatAffineEndpointRows.arity F r)) :
    (FlatAffineEndpointGrid.coordinate F height r i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) (x i) = 0 := by
  have H := congrFun (AffineShiftCoordinates.capture (FlatAffineEndpointPreparation.system F height r)
    (fun j => if j = FlatAffineEndpointGram.active F height r then Polynomial.X else 0)
    (FlatAffineEndpointPreparation.degrees F r) (FlatAffineEndpointValidity.degree_bound F height r hr) t x hx) i
  simpa only [SquarefreeRootFamily.value_apply, Pi.zero_apply, FlatAffineEndpointGrid.coordinate] using H

noncomputable def value {n : ℕ} (i : Fin n) (x : Fin (3 * n + 1) → ℝ) : ℝ :=
  2 * x (FrozenAffineCopies.block (0 : Fin 3) i) - x (FrozenAffineCopies.block (1 : Fin 3) i) -
    x (FrozenAffineCopies.block (2 : Fin 3) i)

theorem value_relation (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (t : ℝ) (x : Fin (FlatAffineEndpointRows.arity F r) → ℝ) (hx : PolynomialGridValues.value (rows F height r) (t, x) = 0) :
    (SquarefreeRootFamily.realPolynomial (FlatAffineEndpointTrailing.polynomial F height index r)).eval₂
      (Polynomial.evalRingHom t) (value (index r) x) = 0 := by
  rw [SquarefreeRootFamily.eval_realPolynomial]
  exact FlatAffineEndpointValues.eval_eq_zero F height index r (SymbolicScaledSquarefree.scalarEvaluation t) x
    (coordinate_root F height r hr t x hx)

theorem sign_iff (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    {a b : ℝ} (f : C(Ioo a b, Fin (FlatAffineEndpointRows.arity F r) → ℝ))
    (hf : ∀ t, PolynomialGridValues.value (rows F height r) (t.val, f t) = 0)
    (ht : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t
      (FlatAffineEndpointTrailing.polynomial F height index r).trailingCoeff ≠ 0) (s t : Ioo a b) :
    (value (index r) (f s) < 0 ↔ value (index r) (f t) < 0) ∧
      (0 < value (index r) (f s) ↔ 0 < value (index r) (f t)) := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hc : Continuous (fun v : Ioo a b => value (index r) (f v)) :=
    ((continuous_const.mul ((continuous_apply _).comp f.continuous)).sub
      ((continuous_apply _).comp f.continuous)).sub ((continuous_apply _).comp f.continuous)
  apply AlgebraicBranchSign.sign_iff (SquarefreeRootFamily.realPolynomial (FlatAffineEndpointTrailing.polynomial F height index r))
    Subtype.val (fun v => value (index r) (f v)) continuous_subtype_val hc (fun v => value_relation F height index r hr v.val (f v) (hf v)) ?_ s t
  intro v
  rw [Connectivity.IntegerGridArcs.trailing_realPolynomial, Polynomial.eval_map]
  exact ht v.val v.property

theorem candidate_relation (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (index : (r : List Bool) → Fin (count F (pairFst r))) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a t : ℝ) (current left right : Fin (count F (pairFst r)) → ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (hc : ∀ i, (FlatAffinePowerPositive.system F (pairFst r) i).eval₂ (Int.castRingHom ℝ) current =
      if i = height (pairFst r) then t else 0)
    (hl : ∀ i, (FlatAffinePowerPositive.system F (pairFst r) i).eval₂ (Int.castRingHom ℝ) left =
      if i = height (pairFst r) then a else 0)
    (hy : ∀ i, (FlatAffinePowerPositive.system F (pairFst r) i).eval₂ (Int.castRingHom ℝ) right =
      if i = height (pairFst r) then a else 0) :
    (SquarefreeRootFamily.realPolynomial (FlatAffineEndpointTrailing.polynomial F height index r)).eval₂
      (Polynomial.evalRingHom t) (2 * current (index r) - left (index r) - right (index r)) = 0 := by
  let z := FrozenAffineCopies.point a ![current, left, right]
  let rho := SymbolicScaledSquarefree.scalarEvaluation t
  have H := FrozenAffineCopies.lift (FlatAffinePowerPositive.system F (pairFst r))
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) (height (pairFst r)) rho a current left right ha
    (by simpa only [rho, SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hc) hl hy
  have hz : PolynomialGridValues.value (rows F height r) (t, z) = 0 := by
    apply (AffineShiftCoordinates.roots_iff _ _ t z).mpr
    exact (AffineConstantParameterShift.roots_iff _ _ rho z).mp H
  have Hv := value_relation F height index r hr t z hz
  simpa [z, value] using Hv

noncomputable def equation (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (r : List Bool) (t : ℝ) (x : Fin (count F (pairFst r)) → ℝ) : Prop :=
  ∀ i, (FlatAffinePowerPositive.system F (pairFst r) i).eval₂ (Int.castRingHom ℝ) x =
    if i = height (pairFst r) then t else 0

noncomputable def testPolynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (r : List Bool) (i : Fin (count F (pairFst r))) : Polynomial (Polynomial ℤ) :=
  FlatAffineEndpointTrailing.polynomial F height (fun s => FlatAffineHeightGram.rawRow F (pairFst s) i.val) r

theorem matches_iff (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (hr : FlatAffineEndpointValidity.Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    {c d : ℝ} (curve : ℝ → Fin (count F (pairFst r)) → ℝ) (hc : ContinuousOn curve (Icc c d))
    (hcurve : ∀ t ∈ Ioo c d, equation F height r t (curve t))
    (x : Fin (count F (pairFst r)) → ℝ) (hx : equation F height r a x)
    (ht : ∀ i t, t ∈ Ioo c d → SymbolicScaledSquarefree.scalarEvaluation t (testPolynomial F height r i).trailingCoeff ≠ 0)
    (s t : Ioo c d) :
    EndpointMidpoint.Matches {y | equation F height r a y} x (curve s.val) ↔
      EndpointMidpoint.Matches {y | equation F height r a y} x (curve t.val) := by
  apply EndpointMidpoint.matches_iff_of_relations curve hc {y | equation F height r a y} x
    (fun _ i => SquarefreeRootFamily.realPolynomial (testPolynomial F height r i)) ?_ ?_ s t
  · intro y hy i v hv
    have H := candidate_relation F height (fun z => FlatAffineHeightGram.rawRow F (pairFst z) i.val) r hr
      a v (curve v) x y ha (hcurve v hv) hx hy
    simpa only [FlatAffineHeightGram.rawRow_val, testPolynomial] using H
  · intro y _ i v hv
    rw [Connectivity.IntegerGridArcs.trailing_realPolynomial, Polynomial.eval_map]
    exact ht i v hv

end LeanCanny.Geometry.FlatAffineEndpointMidpoint

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCoordinateSquarefree
public import LeanCanny.Algebra.IntegralMixedLimitCoordinate
/-! # Actual limit-coordinate factors at the original degree allowance

The bounded coefficient formula is a finite sum at the stored deformation
index. It is functorial without transporting a computed natDegree. Native
equality follows from the proved original coordinate-degree bound and the
actual bounded-cleared-dilation coefficient formula.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedLimitCoordinate
open IntegralMixedHistory Polynomial
open scoped Classical BigOperators
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {n m :ℕ}

noncomputable def factor (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :A[X]:=
  ∑l ∈Finset.range (k+1),monomial l
    (((CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j).coeff l).coeff (k-l)*
      (algebraMap R A x.commonDenominator)^(CoefficientMixedCoordinateSquarefree.degree D r-l))

theorem coefficient (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k l :ℕ) :
    (factor x low leading D r slope j k).coeff l=
      if l≤k then
        ((CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j).coeff l).coeff (k-l)*
          (algebraMap R A x.commonDenominator)^(CoefficientMixedCoordinateSquarefree.degree D r-l)
      else 0:=by
  simp [factor,coeff_monomial]

variable {φ :R→+*S} {ψ :A→+*B} {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}

theorem factor_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (factor x low leading D r slope j k).map ψ=
      factor y (low.map φ) (φ leading) D r (φ slope) j k:=by
  have HC (l :ℕ) :ψ (((CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j).coeff l).coeff (k-l))=
      ((CoefficientMixedCriticalSweep.coordinateWithSlope y (low.map φ) (φ leading) D r (φ slope) j).coeff l).coeff (k-l):=by
    simpa only [coeff_map,Polynomial.coe_mapRingHom] using
      congrArg (fun p=>(p.coeff l).coeff (k-l))
        (CoefficientMixedCriticalSweep.coordinateWithSlope_map H low leading D r slope j)
  unfold factor
  change (Polynomial.mapRingHom ψ) _=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  simp only [Polynomial.coe_mapRingHom,map_monomial,map_mul,map_pow,HC,H.coefficients,H.commonDenominator]

theorem factor_currentQ_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (factor x low leading D r x.commonDenominator j k).map ψ=
      factor y (low.map φ) (φ leading) D r y.commonDenominator j k:=by
  rw [factor_map H,H.commonDenominator]

private theorem integer_algebraMap (z :ℤ) :algebraMap ℤ A z=(z:A):=by
  have H :algebraMap ℤ A=Int.castRingHom A:=RingHom.ext_int _ _
  exact congrArg (fun f :ℤ→+*A=>f z) H

/-- The degree bound is derived from the actual native coordinate construction. -/
theorem factor_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (k :Fin (IntegralMixedLimitCoordinate.ChoiceBound P r)) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope j k.val=
      IntegralMixedLimitCoordinate.factor x hm r j k:=by
  ext l
  rw [coefficient]
  unfold IntegralMixedLimitCoordinate.factor IntegralMixedLimitCoordinate.coefficient IntegralMixedLimitCoordinate.series
  rw [BoundedClearedDilation.swapped_coefficient _ _ _ (IntegralMixedCriticalSweep.coordinate_degree x hm r j)]
  rw [CoefficientMixedCriticalSweep.coordinateWithSlope_ofState x hm r j]
  simp only [CoefficientHeightBank.commonDenominator_ofState,integer_algebraMap,
    CoefficientMixedCoordinateSquarefree.degree]

theorem factor_currentQ_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (k :Fin (IntegralMixedLimitCoordinate.ChoiceBound P r)) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree r
      (CoefficientHeightBank.ofState x).commonDenominator j k.val=
      IntegralMixedLimitCoordinate.factor x hm (CoefficientMixedCriticalSweep.currentRule x r) j k:=by
  change factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree
    (CoefficientMixedCriticalSweep.currentRule x r) (CoefficientMixedCriticalSweep.currentRule x r).slope j k.val=_
  exact factor_ofState x hm (CoefficientMixedCriticalSweep.currentRule x r) j k

end LeanCanny.Algebra.CoefficientMixedLimitCoordinate

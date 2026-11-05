/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCriticalSweep
public import LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
/-! # Actual squarefree exceptional factors over a coefficient ring

The principal subresultant uses the original advertised coordinate degree and
stored index. Its coordinate polynomial is constructed from the actual bank
and source, with an explicit coefficient-ring slope. No degree selection or
trailing-coefficient extraction is performed by these factories.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCoordinateSquarefree
open IntegralMixedHistory Polynomial PrincipalSubresultant
open scoped Classical
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {n m :ℕ}

def degree (D :ℕ) (r :IntegralMixedCriticalSweep.Rule n) :ℕ:=
  PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) D

noncomputable def principal (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :A[X]:=
  psc (CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j)
    (CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j).derivative
    (degree D r) (degree D r-1) k

noncomputable def exceptional (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :A[X]:=
  (CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j).coeff (degree D r)*
    principal x low leading D r slope j k

variable {φ :R→+*S} {ψ :A→+*B} {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}

theorem principal_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (principal x low leading D r slope j k).map ψ=
      principal y (low.map φ) (φ leading) D r (φ slope) j k:=by
  unfold principal
  change (Polynomial.mapRingHom ψ) _=_
  rw [←psc_map_map,←Polynomial.derivative_map,
    CoefficientMixedCriticalSweep.coordinateWithSlope_map H]

theorem exceptional_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (exceptional x low leading D r slope j k).map ψ=
      exceptional y (low.map φ) (φ leading) D r (φ slope) j k:=by
  have HC:=congrArg (fun p=>p.coeff (degree D r))
    (CoefficientMixedCriticalSweep.coordinateWithSlope_map H low leading D r slope j)
  have HT :((CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope j).coeff
      (degree D r)).map ψ=
      (CoefficientMixedCriticalSweep.coordinateWithSlope y (low.map φ) (φ leading) D r (φ slope) j).coeff
        (degree D r):=by
    simpa only [coeff_map,Polynomial.coe_mapRingHom] using HC
  rw [exceptional,Polynomial.map_mul,principal_map H,HT]
  rfl

theorem exceptional_currentQ_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (exceptional x low leading D r x.commonDenominator j k).map ψ=
      exceptional y (low.map φ) (φ leading) D r y.commonDenominator j k:=by
  rw [exceptional_map H,H.commonDenominator]

theorem principal_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    principal (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope j k=
      IntegralMixedCoordinateSquarefree.principal x hm r j k:=by
  unfold principal IntegralMixedCoordinateSquarefree.principal
  rw [CoefficientMixedCriticalSweep.coordinateWithSlope_ofState x hm r j]
  rfl

/-- Exactly the native exceptional factor at the same stored squarefree index. -/
theorem exceptional_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (i :Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) :
    exceptional (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope j i.val=
      IntegralMixedCoordinateSquarefree.exceptional x hm r j i:=by
  unfold exceptional IntegralMixedCoordinateSquarefree.exceptional
  rw [CoefficientMixedCriticalSweep.coordinateWithSlope_ofState x hm r j,principal_ofState x hm r j i.val]
  rfl

theorem exceptional_currentQ_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (i :Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r)) :
    exceptional (CoefficientHeightBank.ofState x) P.low P.leading P.degree r
      (CoefficientHeightBank.ofState x).commonDenominator j i.val=
      IntegralMixedCoordinateSquarefree.exceptional x hm (CoefficientMixedCriticalSweep.currentRule x r) j i:=by
  unfold exceptional principal IntegralMixedCoordinateSquarefree.exceptional
    IntegralMixedCoordinateSquarefree.principal
  rw [CoefficientMixedCriticalSweep.coordinate_currentQ_ofState x hm r j]
  rfl

end LeanCanny.Algebra.CoefficientMixedCoordinateSquarefree

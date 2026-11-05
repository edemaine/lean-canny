/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCriticalPolynomial
public import LeanCanny.Algebra.IntegralMixedCoordinateTrailing
/-! # Actual mixed sweeps with a coefficient-ring slope

Bank expressions, coordinate products/cofactors and the native critical rule
construct the coordinate equations. The slope is an explicit coefficient-ring
value; fixed-integer and computed current-denominator cases specialize exactly.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCriticalSweep
open IntegralMixedHistory Polynomial
open scoped Classical BigOperators
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {n m :ℕ}

noncomputable def heightsWithSlope (x :CoefficientHeightBank R A m)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n+1)) :A[X]:=
  C (x.expression (r.critical.heights i))+
    if i=r.height then C (algebraMap R A slope)*X else 0

noncomputable def numeratorsWithSlope (x :CoefficientHeightBank R A m)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :ℕ) :A[X]:=
  if hi :i<n+1 then heightsWithSlope x r slope ⟨i,hi⟩*
    C (algebraMap R A (∏j ∈Finset.univ.erase ⟨i,hi⟩,
      CoefficientMixedCriticalPolynomial.scales x r.critical j))
  else 0

noncomputable def coordinateWithSlope (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) :A[X][X]:=
  ClearedCoordinateCritical.annihilator D
    (C (algebraMap R A (CoefficientMixedCriticalPolynomial.denominator x r.critical)))
    (numeratorsWithSlope x r slope) r.critical.offset.val (IntegralMixedCriticalSweep.fit r).le
    (low.map (Polynomial.C.comp (algebraMap R A))) (C (algebraMap R A leading))
    (IntegralMixedCriticalSweep.objective r) j

/-- A stored coefficient choice; its trailing validity is a separate guard. -/
noncomputable def factorWithSlope (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :A[X]:=
  (coordinateWithSlope x low leading D r slope j).coeff k

noncomputable def heights (x :CoefficientHeightBank R A m)
    (r :IntegralMixedCriticalSweep.Rule n) (i :Fin (n+1)) :A[X]:=
  heightsWithSlope x r (r.slope:R) i

noncomputable def coordinate (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) :A[X][X]:=
  coordinateWithSlope x low leading D r (r.slope:R) j

noncomputable def factor (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :A[X]:=
  factorWithSlope x low leading D r (r.slope:R) j k

variable {φ :R→+*S} {ψ :A→+*B} {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}

theorem heightsWithSlope_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n+1)) :
    (heightsWithSlope x r slope i).map ψ=heightsWithSlope y r (φ slope) i:=by
  unfold heightsWithSlope
  split_ifs
  · rw [Polynomial.map_add,Polynomial.map_C,H.expression,Polynomial.map_mul,
      Polynomial.map_C,H.coefficients,map_X]
  · rw [Polynomial.map_add,Polynomial.map_C,H.expression,Polynomial.map_zero]

theorem numeratorsWithSlope_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :ℕ) :
    (numeratorsWithSlope x r slope i).map ψ=numeratorsWithSlope y r (φ slope) i:=by
  unfold numeratorsWithSlope
  split_ifs with hi
  · have HP :φ (∏j ∈Finset.univ.erase (⟨i,hi⟩:Fin (n+1)),
        CoefficientMixedCriticalPolynomial.scales x r.critical j)=
        ∏j ∈Finset.univ.erase (⟨i,hi⟩:Fin (n+1)),
          CoefficientMixedCriticalPolynomial.scales y r.critical j:=by
      simp only [map_prod,CoefficientMixedCriticalPolynomial.scales_map H]
    rw [Polynomial.map_mul,heightsWithSlope_map H,Polynomial.map_C,H.coefficients,HP]
  · exact Polynomial.map_zero ψ

theorem coordinateWithSlope_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (j :Fin (n-r.critical.offset.val+1)) :
    (coordinateWithSlope x low leading D r slope j).map (Polynomial.mapRingHom ψ)=
      coordinateWithSlope y (low.map φ) (φ leading) D r (φ slope) j:=by
  have HC :(Polynomial.mapRingHom ψ).comp (Polynomial.C.comp (algebraMap R A))=
      (Polynomial.C.comp (algebraMap S B)).comp φ:=by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,map_C,H.coefficients]
  have HL :(low.map (Polynomial.C.comp (algebraMap R A))).map (Polynomial.mapRingHom ψ)=
      (low.map φ).map (Polynomial.C.comp (algebraMap S B)):=by
    rw [MvPolynomial.map_map,MvPolynomial.map_map,HC]
  unfold coordinateWithSlope
  rw [PurePowerAnnihilatorMap.cleared]
  simp only [Polynomial.coe_mapRingHom,map_C,H.coefficients,
    CoefficientMixedCriticalPolynomial.denominator_map H,numeratorsWithSlope_map H,HL]

theorem factorWithSlope_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (factorWithSlope x low leading D r slope j k).map ψ=
      factorWithSlope y (low.map φ) (φ leading) D r (φ slope) j k:=by
  have HC:=congrArg (fun p=>p.coeff k) (coordinateWithSlope_map H low leading D r slope j)
  simpa only [factorWithSlope,coeff_map,Polynomial.coe_mapRingHom] using HC

theorem coordinate_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) :
    (coordinate x low leading D r j).map (Polynomial.mapRingHom ψ)=
      coordinate y (low.map φ) (φ leading) D r j:=by
  simpa only [coordinate,map_intCast] using
    coordinateWithSlope_map H low leading D r (r.slope:R) j

theorem factor_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (factor x low leading D r j k).map ψ=factor y (low.map φ) (φ leading) D r j k:=by
  simpa only [factor,map_intCast] using
    factorWithSlope_map H low leading D r (r.slope:R) j k

/-- Here the changing slope is computed from actual bank denominators. -/
theorem coordinate_currentQ_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (j :Fin (n-r.critical.offset.val+1)) :
    (coordinateWithSlope x low leading D r x.commonDenominator j).map (Polynomial.mapRingHom ψ)=
      coordinateWithSlope y (low.map φ) (φ leading) D r y.commonDenominator j:=by
  rw [coordinateWithSlope_map H,H.commonDenominator]

private theorem integer_algebraMap (z :ℤ) :algebraMap ℤ A z=(z:A):=by
  have H :algebraMap ℤ A=Int.castRingHom A:=RingHom.ext_int _ _
  exact congrArg (fun f :ℤ→+*A=>f z) H

private theorem integer_constant (z :ℤ) :C (algebraMap ℤ A z)=(z:Polynomial A):=by
  have H :Polynomial.C.comp (algebraMap ℤ A)=Int.castRingHom (Polynomial A):=
    RingHom.ext_int _ _
  exact congrArg (fun f :ℤ→+*Polynomial A=>f z) H

theorem heightsWithSlope_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (r :IntegralMixedCriticalSweep.Rule n) (i :Fin (n+1)) :
    heightsWithSlope (CoefficientHeightBank.ofState x) r r.slope i=
      IntegralMixedCriticalSweep.heights x r i:=by
  simp only [heightsWithSlope,CoefficientHeightBank.expression_ofState,
    IntegralMixedCriticalSweep.heights,integer_algebraMap]

theorem numeratorsWithSlope_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (i :ℕ) :
    numeratorsWithSlope (CoefficientHeightBank.ofState x) r r.slope i=
      CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales
        (IntegralMixedCriticalSweep.heights x r) i:=by
  unfold numeratorsWithSlope CoordinateFrozenCriticalElimination.numerators
  split_ifs
  · rw [heightsWithSlope_ofState]
    congr 1
  · rfl

/-- Exact native sweep coordinate, including its formal sweep variable. -/
theorem coordinateWithSlope_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) :
    coordinateWithSlope (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope j=
      IntegralMixedCriticalSweep.coordinate x hm r j:=by
  have HI :Polynomial.C.comp (algebraMap ℤ x.sampler.scalarPrefix.carrier)=
      Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier):=RingHom.ext_int _ _
  unfold coordinateWithSlope IntegralMixedCriticalSweep.coordinate CoordinateFrozenCriticalElimination.polynomial
  rw [CoefficientMixedCriticalPolynomial.denominator_ofState x hm r.critical,HI]
  simp only [integer_constant]
  congr 1
  funext i
  exact numeratorsWithSlope_ofState x hm r i

theorem factorWithSlope_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (i :Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    factorWithSlope (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope j i.val=
      IntegralMixedCoordinateTrailing.factor x hm r j i:=by
  rw [factorWithSlope,coordinateWithSlope_ofState x hm r j]
  rfl

theorem heights_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (r :IntegralMixedCriticalSweep.Rule n) (i :Fin (n+1)) :
    heights (CoefficientHeightBank.ofState x) r i=IntegralMixedCriticalSweep.heights x r i:=
  heightsWithSlope_ofState x r i

theorem coordinate_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) :
    coordinate (CoefficientHeightBank.ofState x) P.low P.leading P.degree r j=
      IntegralMixedCriticalSweep.coordinate x hm r j:=coordinateWithSlope_ofState x hm r j

theorem factor_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (i :Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree r j i.val=
      IntegralMixedCoordinateTrailing.factor x hm r j i:=factorWithSlope_ofState x hm r j i

/-- The existing native rule with its slope computed from the actual state. -/
noncomputable def currentRule {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (r :IntegralMixedCriticalSweep.Rule n) :IntegralMixedCriticalSweep.Rule n:=
  {r with slope:=commonDenominator x, slope_ne_zero:=commonDenominator_ne_zero x}

theorem coordinate_currentQ_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) :
    coordinateWithSlope (CoefficientHeightBank.ofState x) P.low P.leading P.degree r
      (CoefficientHeightBank.ofState x).commonDenominator j=
      IntegralMixedCriticalSweep.coordinate x hm (currentRule x r) j:=by
  change coordinateWithSlope (CoefficientHeightBank.ofState x) P.low P.leading P.degree
    (currentRule x r) (currentRule x r).slope j=_
  exact coordinateWithSlope_ofState x hm (currentRule x r) j

theorem factor_currentQ_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (j :Fin (n-r.critical.offset.val+1)) (i :Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    factorWithSlope (CoefficientHeightBank.ofState x) P.low P.leading P.degree r
      (CoefficientHeightBank.ofState x).commonDenominator j i.val=
      IntegralMixedCoordinateTrailing.factor x hm (currentRule x r) j i:=by
  rw [factorWithSlope,coordinate_currentQ_ofState x hm r j]
  rfl

end LeanCanny.Algebra.CoefficientMixedCriticalSweep

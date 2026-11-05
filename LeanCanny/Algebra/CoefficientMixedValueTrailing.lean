/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCoordinateSquarefree
public import LeanCanny.Algebra.IntegralMixedValueTrailing
public import LeanCanny.Algebra.RelativeAffineGridValueMap
/-! # The actual mixed value certificate over a coefficient ring

Original source/gradient rows are computed and cleared using the actual bank.
The existing grid-value Gram constructor then supplies the value polynomial.
The stored coefficient index and slope are explicit; no trailing selection is
performed, and no coordinate polynomial or reduction matrix is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedValueTrailing
open IntegralMixedHistory Polynomial
open scoped Classical
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {n m :ℕ}

noncomputable def sourceRow (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (i :Fin (n-r.critical.offset.val+1)) :
    MvPolynomial (Fin (n+1)) R:=
  if i=IntegralMixedCriticalSweep.objective r then
    FermatCriticalHomogenization.polynomial low leading D
  else MvPolynomial.pderiv
    (ClearedCoordinateCritical.freeIndex r.critical.offset.val (IntegralMixedCriticalSweep.fit r).le i)
    (FermatCriticalHomogenization.polynomial low leading D)

noncomputable def row (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n-r.critical.offset.val+1)) :
    MvPolynomial (Fin (n-r.critical.offset.val+1)) (Polynomial A):=
  ClearedCoordinateBlock.specialize D
    (C (algebraMap R A (CoefficientMixedCriticalPolynomial.denominator x r.critical)))
    (CoefficientMixedCriticalSweep.numeratorsWithSlope x r slope)
    r.critical.offset.val (n-r.critical.offset.val+1)
    ((sourceRow low leading D r i).map (Polynomial.C.comp (algebraMap R A)))

noncomputable def polynomial (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n-r.critical.offset.val+1)) :A[X][X]:=
  RelativeAffineGridValueGram.annihilator
    (CoefficientMixedCriticalSweep.coordinateWithSlope x low leading D r slope)
    (row x low leading D r slope i) (fun _=>CoefficientMixedCoordinateSquarefree.degree D r) D

noncomputable def factor (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R)
    (i :Fin (n-r.critical.offset.val+1)) (k :ℕ) :A[X]:=
  (polynomial x low leading D r slope i).coeff k

theorem sourceRow_map (φ :R→+*S) (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (i :Fin (n-r.critical.offset.val+1)) :
    (sourceRow low leading D r i).map φ=sourceRow (low.map φ) (φ leading) D r i:=by
  unfold sourceRow
  split_ifs
  · exact FermatCriticalHomogenization.map_polynomial φ low leading D
  · rw [←MvPolynomial.pderiv_map,FermatCriticalHomogenization.map_polynomial]

variable {φ :R→+*S} {ψ :A→+*B} {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}

theorem row_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n-r.critical.offset.val+1)) :
    (row x low leading D r slope i).map (Polynomial.mapRingHom ψ)=
      row y (low.map φ) (φ leading) D r (φ slope) i:=by
  have HC :(Polynomial.mapRingHom ψ).comp (Polynomial.C.comp (algebraMap R A))=
      (Polynomial.C.comp (algebraMap S B)).comp φ:=by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,map_C,H.coefficients]
  have HL :((sourceRow low leading D r i).map (Polynomial.C.comp (algebraMap R A))).map
      (Polynomial.mapRingHom ψ)=
      (sourceRow (low.map φ) (φ leading) D r i).map (Polynomial.C.comp (algebraMap S B)):=by
    rw [←sourceRow_map φ low leading D r i,MvPolynomial.map_map,MvPolynomial.map_map,HC]
  unfold row
  rw [ClearedCoordinateMap.specialize]
  simp only [Polynomial.coe_mapRingHom,map_C,H.coefficients,
    CoefficientMixedCriticalPolynomial.denominator_map H,
    CoefficientMixedCriticalSweep.numeratorsWithSlope_map H,HL]

theorem polynomial_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n-r.critical.offset.val+1)) :
    (polynomial x low leading D r slope i).map (Polynomial.mapRingHom ψ)=
      polynomial y (low.map φ) (φ leading) D r (φ slope) i:=by
  unfold polynomial
  rw [RelativeAffineGridValueMap.annihilator]
  simp only [CoefficientMixedCriticalSweep.coordinateWithSlope_map H,row_map H]

theorem factor_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (i :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (factor x low leading D r slope i k).map ψ=
      factor y (low.map φ) (φ leading) D r (φ slope) i k:=by
  have HC:=congrArg (fun p=>p.coeff k) (polynomial_map H low leading D r slope i)
  simpa only [factor,coeff_map,Polynomial.coe_mapRingHom] using HC

theorem factor_currentQ_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ)
    (r :IntegralMixedCriticalSweep.Rule n) (i :Fin (n-r.critical.offset.val+1)) (k :ℕ) :
    (factor x low leading D r x.commonDenominator i k).map ψ=
      factor y (low.map φ) (φ leading) D r y.commonDenominator i k:=by
  rw [factor_map H,H.commonDenominator]

private theorem integer_constant (z :ℤ) :C (algebraMap ℤ A z)=(z:Polynomial A):=by
  have H :Polynomial.C.comp (algebraMap ℤ A)=Int.castRingHom (Polynomial A):=
    RingHom.ext_int _ _
  exact congrArg (fun f :ℤ→+*Polynomial A=>f z) H

theorem sourceRow_native (P :SpatialSource n) (r :IntegralMixedCriticalSweep.Rule n)
    (i :Fin (n-r.critical.offset.val+1)) :
    sourceRow P.low P.leading P.degree r i=IntegralMixedSweepRows.integerRow P r i:=rfl

theorem row_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (i :Fin (n-r.critical.offset.val+1)) :
    row (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope i=
      IntegralMixedSweepRows.row x hm r i:=by
  have HI :Polynomial.C.comp (algebraMap ℤ x.sampler.scalarPrefix.carrier)=
      Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier):=RingHom.ext_int _ _
  have HN :CoefficientMixedCriticalSweep.numeratorsWithSlope (CoefficientHeightBank.ofState x)
      r r.slope=IntegralMixedSweepRows.numerators x hm r:=by
    funext j
    exact CoefficientMixedCriticalSweep.numeratorsWithSlope_ofState x hm r j
  unfold row IntegralMixedSweepRows.row IntegralMixedSweepRows.denominator
  rw [CoefficientMixedCriticalPolynomial.denominator_ofState x hm r.critical,
    HI,sourceRow_native,HN]
  simp only [integer_constant]

theorem polynomial_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (i :Fin (n-r.critical.offset.val+1)) :
    polynomial (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope i=
      IntegralMixedGridValue.polynomial x hm r i:=by
  have HG :CoefficientMixedCriticalSweep.coordinateWithSlope (CoefficientHeightBank.ofState x)
      P.low P.leading P.degree r r.slope=IntegralMixedCriticalSweep.coordinate x hm r:=by
    funext j
    exact CoefficientMixedCriticalSweep.coordinateWithSlope_ofState x hm r j
  unfold polynomial IntegralMixedGridValue.polynomial
  rw [HG,row_ofState x hm r i]
  rfl

theorem factor_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (i :Fin (n-r.critical.offset.val+1)) (k :Fin (IntegralMixedValueTrailing.ChoiceBound P r)) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree r r.slope i k.val=
      IntegralMixedValueTrailing.factor x hm r i k:=by
  rw [factor,polynomial_ofState x hm r i]
  rfl

theorem factor_currentQ_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n)
    (i :Fin (n-r.critical.offset.val+1)) (k :Fin (IntegralMixedValueTrailing.ChoiceBound P r)) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree r
      (CoefficientHeightBank.ofState x).commonDenominator i k.val=
      IntegralMixedValueTrailing.factor x hm (CoefficientMixedCriticalSweep.currentRule x r) i k:=by
  change factor (CoefficientHeightBank.ofState x) P.low P.leading P.degree
    (CoefficientMixedCriticalSweep.currentRule x r) (CoefficientMixedCriticalSweep.currentRule x r).slope i k.val=_
  exact factor_ofState x hm (CoefficientMixedCriticalSweep.currentRule x r) i k

end LeanCanny.Algebra.CoefficientMixedValueTrailing

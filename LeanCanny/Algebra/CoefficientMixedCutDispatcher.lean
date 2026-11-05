/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedValueTrailing
public import LeanCanny.Algebra.CoefficientMixedLimitCoordinate
public import LeanCanny.Algebra.IntegralMixedCutMatrix
/-! # The actual four-kind mixed dispatcher over a coefficient base

The existing native Kind supplies bounded logical rows and coefficient indices.
Its source degree stays the original metadata; source coefficients, bank and
explicit slope are specialized. Truncation is the literal native truncation.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCutDispatcher
open IntegralMixedHistory IntegralMixedRelativeCuts
open scoped Classical
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {n m :ℕ} {P :SpatialSource n}

noncomputable def factor (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) :Kind P r→Polynomial A
  | .coordinate j k=>CoefficientMixedCriticalSweep.factorWithSlope x low leading P.degree r slope j k.val
  | .squarefree j k=>CoefficientMixedCoordinateSquarefree.exceptional x low leading P.degree r slope j k.val
  | .value i k=>CoefficientMixedValueTrailing.factor x low leading P.degree r slope i k.val
  | .limitCoordinate j k=>CoefficientMixedLimitCoordinate.factor x low leading P.degree r slope j k.val

noncomputable def raw (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (c :Kind P r) (d :ℕ) :Polynomial A:=
  IntegralRelativeTruncation.truncate (factor x low leading r slope c) d

theorem factor_map {φ :R→+*S} {ψ :A→+*B}
    {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}
    (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (c :Kind P r) :
    (factor x low leading r slope c).map ψ=factor y (low.map φ) (φ leading) r (φ slope) c:=by
  cases c with
  | coordinate j k=>exact CoefficientMixedCriticalSweep.factorWithSlope_map H low leading P.degree r slope j k.val
  | squarefree j k=>exact CoefficientMixedCoordinateSquarefree.exceptional_map H low leading P.degree r slope j k.val
  | value i k=>exact CoefficientMixedValueTrailing.factor_map H low leading P.degree r slope i k.val
  | limitCoordinate j k=>exact CoefficientMixedLimitCoordinate.factor_map H low leading P.degree r slope j k.val

private theorem truncate_map (ψ :A→+*B) (p :Polynomial A) (d :ℕ) :
    (IntegralRelativeTruncation.truncate p d).map ψ=IntegralRelativeTruncation.truncate (p.map ψ) d:=by
  ext k
  rw [Polynomial.coeff_map,IntegralRelativeTruncation.coefficient,IntegralRelativeTruncation.coefficient]
  split_ifs
  · exact (Polynomial.coeff_map ψ k).symm
  · exact map_zero ψ

theorem raw_map {φ :R→+*S} {ψ :A→+*B}
    {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}
    (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R)
    (r :IntegralMixedCriticalSweep.Rule n) (slope :R) (c :Kind P r) (d :ℕ) :
    (raw x low leading r slope c d).map ψ=raw y (low.map φ) (φ leading) r (φ slope) c d:=by
  rw [raw,truncate_map,factor_map H]
  rfl

theorem factor_ofState {cap width :ℕ} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (c :Kind P r) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading r r.slope c=
      IntegralMixedRelativeCuts.factor x hm r c:=by
  cases c with
  | coordinate j k=>exact CoefficientMixedCriticalSweep.factorWithSlope_ofState x hm r j k
  | squarefree j k=>exact CoefficientMixedCoordinateSquarefree.exceptional_ofState x hm r j k
  | value i k=>exact CoefficientMixedValueTrailing.factor_ofState x hm r i k
  | limitCoordinate j k=>exact CoefficientMixedLimitCoordinate.factor_ofState x hm r j k

theorem raw_ofState {cap width :ℕ} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (c :Kind P r) (d :ℕ) :
    raw (CoefficientHeightBank.ofState x) P.low P.leading r r.slope c d=
      IntegralMixedCutMatrix.raw x hm r c d:=by
  rw [raw,factor_ofState x hm r c]
  rfl

/-- Only the native rule parameter changes; all four tags and indices are kept. -/
def currentKind {cap width :ℕ} {ι :Type} (x :State P cap width m ι)
    (r :IntegralMixedCriticalSweep.Rule n) :Kind P r→Kind P (CoefficientMixedCriticalSweep.currentRule x r)
  | .coordinate j k=>.coordinate j k
  | .squarefree j k=>.squarefree j k
  | .value i k=>.value i k
  | .limitCoordinate j k=>.limitCoordinate j k

theorem factor_currentQ_ofState {cap width :ℕ} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (c :Kind P r) :
    factor (CoefficientHeightBank.ofState x) P.low P.leading r
      (CoefficientHeightBank.ofState x).commonDenominator c=
      IntegralMixedRelativeCuts.factor x hm (CoefficientMixedCriticalSweep.currentRule x r) (currentKind x r c):=by
  cases c with
  | coordinate j k=>exact CoefficientMixedCriticalSweep.factor_currentQ_ofState x hm r j k
  | squarefree j k=>exact CoefficientMixedCoordinateSquarefree.exceptional_currentQ_ofState x hm r j k
  | value i k=>exact CoefficientMixedValueTrailing.factor_currentQ_ofState x hm r i k
  | limitCoordinate j k=>exact CoefficientMixedLimitCoordinate.factor_currentQ_ofState x hm r j k

theorem raw_currentQ_ofState {cap width :ℕ} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :IntegralMixedCriticalSweep.Rule n) (c :Kind P r) (d :ℕ) :
    raw (CoefficientHeightBank.ofState x) P.low P.leading r
      (CoefficientHeightBank.ofState x).commonDenominator c d=
      IntegralMixedCutMatrix.raw x hm (CoefficientMixedCriticalSweep.currentRule x r) (currentKind x r c) d:=by
  rw [raw,factor_currentQ_ofState x hm r c]
  rfl

end LeanCanny.Algebra.CoefficientMixedCutDispatcher

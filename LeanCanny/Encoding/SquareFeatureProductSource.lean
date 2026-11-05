/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeatureCoefficientReader
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
/-! # Charged sources for all formal squared-feature product coefficients

The datum is a selected product coefficient. No feature product term is
serialized, and no sign or coefficient value at a sampled point is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.SquareFeatureProductSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open SquareFeatureProductFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : Family) : IntegralFramedBankPolynomialModel.Source where
  arity z := F.arity (pairFst z)
  width z := width F (pairFst z)
  degree z := degree F (pairFst z)
  mass z := mass F (pairFst z)
  polynomial z := SquareFeatureCoefficientReader.coefficient F (pairFst z) (Nat.fromBitsLE (pairSnd z))
  fit _z i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    (SquareFeatureCoefficientReader.coefficient_fit F _ _)
  polynomial_degree _z := SquareFeatureCoefficientReader.coefficient_degree F _ _
  polynomial_mass _z := SquareFeatureCoefficientReader.coefficient_mass F _ _

noncomputable def access (F : Family) (A : Access F) : IntegralFramedBankPolynomialModel.Access (source F) where
  arity := A.arity.comp pairFst_mem_FP
  width := (width_unary F A).comp pairFst_mem_FP
  degree := (degree_binary F A).comp pairFst_mem_FP
  mass := (mass_binary F A).comp pairFst_mem_FP
  coefficient := SquareFeatureCoefficientReader.value F
  evaluator := SquareFeatureCoefficientReader.evaluator F A
  packet := SquareFeatureCoefficientReader.value_packet F

end LeanCanny.Encoding.SquareFeatureProductSource

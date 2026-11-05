/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeatureBivariateProduct
public import LeanCanny.Algebra.FixedWidthBivariateRowSpace
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # Every coefficient of the literal squared-feature product is streamed

The selected coefficient is datum, not a different sampled point. Arbitrary
coefficient indices and caller moduli are retained by the same reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureCoefficientReader
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Polynomial FixedWidthPolynomial
open SquareFeatureProductFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def separate (F : Family) (c : List Bool) :=
  MvPolynomial.finSuccEquiv ℤ (F.arity c) (polynomial F c)
noncomputable def coefficient (F : Family) (c : List Bool) (k : ℕ) := (separate F c).coeff k
theorem coefficient_degree (F : Family) (c : List Bool) (k : ℕ) :
    (coefficient F c k).totalDegree ≤ degree F c :=
  (MvTwoParameterCoefficient.one_degree (polynomial F c) k).trans (polynomial_degree F c)
theorem coefficient_mass (F : Family) (c : List Bool) (k : ℕ) :
    MvMass.mass (coefficient F c k) ≤ 2^mass F c :=
  (MvTwoParameterCoefficient.one_mass (polynomial F c) k).trans (polynomial_mass F c)
theorem coefficient_fit (F : Family) (c : List Bool) (k : ℕ) :
    (coefficient F c k).totalDegree < 2^width F c := (MvTwoParameterCoefficient.one_degree (polynomial F c) k).trans_lt (fit F c)

noncomputable def reader (F : Family) (A : Access F) : CertifiedPolynomial.BivariateReader
    (FixedWidthBivariateReader.polynomial F.arity (width F) (separate F)) where
  coefficient := (SquareFeatureBivariateProduct.reader F A).coefficient
  evaluator := (SquareFeatureBivariateProduct.reader F A).evaluator
  coefficient_eq q u v := by
    rw [(SquareFeatureBivariateProduct.reader F A).coefficient_eq]
    rw [SquareFeatureBivariateProduct.product_map]
    rfl

def context := RationalSubstitution.IntegerBits.context
def source (z : List Bool) := pairFst (context z)
def selected (z : List Bool) := Nat.fromBitsLE (pairSnd (context z))
theorem source_FP : source ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP
theorem selected_binary : BinaryFn selected := BinaryFn.fromBits
  (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)

noncomputable def value (F : Family) : List Bool → List Bool :=
  FixedWidthRowBits.value (F.arity ∘ source) (width F ∘ source)
    (fun z => coefficient F (source z) (selected z))
    RationalSubstitution.IntegerBits.selectedDegree pairSnd

theorem evaluator (F : Family) (A : Access F) : SpaceFunction (value F) := by
  exact FixedWidthBivariateRowBits.evaluator F.arity (width F) (separate F) (reader F A)
    A.arity (width_unary F A) (coefficient_fit F) source source_FP selected selected_binary
    RationalSubstitution.IntegerBits.selectedDegree pairSnd
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP

theorem value_packet (F : Family) (z bits modulus : List Bool) :
    value F (pair (pair z bits) modulus) =
      residueBits (((coefficient F (pairFst z) (Nat.fromBitsLE (pairSnd z))).coeff
        (nativeExponent (Equiv.refl _) (width F (pairFst z)) (Nat.fromBitsLE bits)) : ℤ) :
          ZMod (Nat.fromBitsLE modulus+1)) := by
  let h (c : List Bool) (k r m : ℕ) := residueBits (((coefficient F c k).coeff
    (nativeExponent (Equiv.refl _) (width F c) r) : ℤ) : ZMod (m+1))
  change h (source (pair (pair z bits) modulus)) (selected (pair (pair z bits) modulus))
    (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree (pair (pair z bits) modulus)))
    (Nat.fromBitsLE (pairSnd (pair (pair z bits) modulus))) = h (pairFst z) (Nat.fromBitsLE (pairSnd z))
      (Nat.fromBitsLE bits) (Nat.fromBitsLE modulus)
  congr 1 <;> simp only [source, context, selected, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]

theorem packet (F : Family) (c bits modulus : List Bool) (k : ℕ) :
    value F (pair (pair (pair c (BinaryNatCode.encode k)) bits) modulus) =
      residueBits (((coefficient F c k).coeff (nativeExponent (Equiv.refl _) (width F c)
        (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus+1)) := by
  rw [value_packet]
  let h (c : List Bool) (k : ℕ) := residueBits (((coefficient F c k).coeff
    (nativeExponent (Equiv.refl _) (width F c) (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus+1))
  change h (pairFst (pair c (BinaryNatCode.encode k)))
    (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode k)))) = h c k
  rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.SquareFeatureCoefficientReader

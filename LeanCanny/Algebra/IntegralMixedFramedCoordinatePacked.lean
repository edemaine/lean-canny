/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCoefficientSpace
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
/-! # Actual coordinate equations as integer multivariate test polynomials

The first variable is E; the tail is the same weighted old joint tuple.
Declared Y/E bounds describe only the test circuit. The spatial source and
its degree are unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def head (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) :
    Polynomial (MvPolynomial (Fin (IntegralMixedFramedCoordinateCoefficientSpaceBits.arity P D H parent q+1)) ℤ) := by
  let key:=IntegralMixedVirtualTaskBits.saved P (parent q)
  let x:=(family P D H).state key
  let := x.sampler.scalarPrefix.ring
  exact SelectedMultivariatePolynomialLift.lift
    (IntegralMixedCriticalSweep.coordinate x ((family P D H).birth_bound key) ((family P D H).rule key)
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H) key (get P .slot13 (parent q))))
    (SelectedPoweredPolynomialLift.representative x.sampler.scalarPrefix.basis
      (UniformIntegralPowerSchedule.weights (IntegralMixedFramedAllCoordinateSourceBits.horizon P (parent q))
        (2^(family P D H).width key) ((family P D H).birth key))) (d q) (e q)

theorem coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e y k : List Bool→ℕ) (q : List Bool)
    (v : Fin (IntegralMixedFramedCoordinateCoefficientSpaceBits.arity P D H parent q)→₀ℕ) :
    ((head P D H parent d e q).coeff (y q)).coeff (v.cons (k q))=
      if y q≤d q then if k q≤e q then
        (IntegralMixedFramedCoordinateCoefficientSpaceBits.polynomial P D H parent y k q).coeff v else 0 else 0 := by
  unfold head
  rw [SelectedMultivariatePolynomialLift.coefficient]
  rfl

def parameter (W : List Bool→ℕ) (target : List Bool→List Bool) (q : List Bool) :=
  Nat.fromBitsLE (IntegerParameterCoefficientBits.parameter W target q)
theorem parameter_binary (W : List Bool→ℕ) (target : List Bool→List Bool) (hW : UnaryFn W) (ht : target∈FP) :
    BinaryFn (parameter W target) := BinaryFn.fromBits (IntegerParameterCoefficientBits.parameter_mem_FP W target hW ht)

theorem native_coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e y W : List Bool→ℕ) (target : List Bool→List Bool) (q : List Bool) :
    ((head P D H parent d e q).coeff (y q)).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W q) (Nat.fromBitsLE (target q)))=
      if y q≤d q then if parameter W target q≤e q then
        (IntegralMixedFramedCoordinateCoefficientSpaceBits.polynomial P D H parent y (parameter W target) q).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W q)
            (Nat.fromBitsLE (IntegerParameterCoefficientBits.spatial W target q))) else 0 else 0 := by
  let m:=IntegralMixedFramedCoordinateCoefficientSpaceBits.arity P D H parent q
  let v:=FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin m)) (W q)
    (Nat.fromBitsLE (IntegerParameterCoefficientBits.spatial W target q))
  have HV : v.cons (parameter W target q)=
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (m+1))) (W q) (Nat.fromBitsLE (target q)) := by
    ext j
    refine Fin.cases ?_ (fun i=>?_) j
    · rw [Finsupp.cons_zero]
      exact (IntegerParameterCoefficientBits.parameter_nativeExponent W target m q).symm
    · rw [Finsupp.cons_succ]
      exact congrArg (fun t:Fin m→₀ℕ=>t i) (IntegerParameterCoefficientBits.tail_nativeExponent W target m q).symm
  rw [←HV,coefficient]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits

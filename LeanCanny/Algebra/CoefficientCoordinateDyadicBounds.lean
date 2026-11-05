/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialDyadicInterpolation
public import LeanCanny.Algebra.ParameterMatrixMassBounds
public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalizationBounds
public import LeanCanny.Algebra.IntegralCoordinateBasisFin

/-! # Parameter bounds from actual specialized coordinate matrices

The parent specialization invariant identifies every formal matrix entry with
an actual native integer entry. Affine native growth beyond the incoming
cutoff then bounds the parameter degree and mass before specialization.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientCoordinateDyadicBounds
open Polynomial
open scoped Classical

variable {A : Type*} [CommRing A] [Algebra ℤ[X] A]
  {B : ℕ → Type*} [∀ r, CommRing (B r)] {m N : ℕ}

theorem degree_mass (b : CoefficientCoordinateBasis ℤ[X] A m N)
    (c : ∀ r, CoefficientCoordinateBasis ℤ (B r) m N) (v : A)
    (ψ : ∀ r, A →+* B r) (C K H : ℕ)
    (hb : ∀ r, C ≤ r → CoefficientCoordinateBasis.Specializes
      (Polynomial.evalRingHom ((2 : ℤ) ^ r)) (ψ r) b (c r))
    (hn : ∀ r, C ≤ r → ∀ i j,
      (Algebra.leftMulMatrix (c r).basis (ψ r v) i j).natAbs ≤ 2 ^ (K * r + H))
    (i j : Fin m → Fin N) :
    (Algebra.leftMulMatrix b.basis v i j).natDegree ≤ K ∧
      coefficientMass (Algebra.leftMulMatrix b.basis v i j) ≤
        2 ^ IntegerPolynomialDyadic.massBudget C K H := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have he := congrArg (fun M => M i j) ((hb r hr).matrix_map v)
  change (Algebra.leftMulMatrix b.basis v i j).eval ((2 : ℤ) ^ r) = _ at he
  rw [he]
  exact hn r hr i j

theorem degree_mass_finBasis {width : ℕ}
    (b : CoefficientCoordinateBasis ℤ[X] A m (2 ^ width))
    (c : ∀ r, IntegralCoordinateBasis (B r) m (2 ^ width)) (v : A)
    (ψ : ∀ r, A →+* B r) (C K H : ℕ)
    (hb : ∀ r, C ≤ r → CoefficientCoordinateBasis.Specializes
      (Polynomial.evalRingHom ((2 : ℤ) ^ r)) (ψ r) b
      (CoefficientCoordinateBasis.ofIntegral (c r)))
    (hn : ∀ r, C ≤ r → ∀ i j,
      (Algebra.leftMulMatrix (c r).finBasis (ψ r v) i j).natAbs ≤ 2 ^ (K * r + H))
    (i j : Fin m → Fin (2 ^ width)) :
    (Algebra.leftMulMatrix b.basis v i j).natDegree ≤ K ∧
      coefficientMass (Algebra.leftMulMatrix b.basis v i j) ≤
        2 ^ IntegerPolynomialDyadic.massBudget C K H := by
  apply degree_mass b (fun r => CoefficientCoordinateBasis.ofIntegral (c r)) v ψ C K H hb
  intro r hr s t
  have he := hn r hr (IntegralCoordinateBasis.boxEquiv m width s)
    (IntegralCoordinateBasis.boxEquiv m width t)
  simpa only [IntegralCoordinateBasis.finBasis, CoefficientCoordinateBasis.ofIntegral,
    Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply] using he

def cutBudget (rank C K H : ℕ) : ℕ :=
  ParameterMatrixMassBounds.characteristicBudget rank (IntegerPolynomialDyadic.massBudget C K H) + 1

theorem cutBudget_affine (rank C K H : ℕ) :
    cutBudget rank C K H = 2 * rank * K * C + cutBudget rank 0 K H := by
  unfold cutBudget ParameterMatrixMassBounds.characteristicBudget IntegerPolynomialDyadic.massBudget
  ring

theorem cutBudget_binary {rank C K H : List Bool → ℕ}
    (hr : BinaryFn rank) (hc : BinaryFn C) (hk : BinaryFn K) (hh : BinaryFn H) :
    BinaryFn (fun q => cutBudget (rank q) (C q) (K q) (H q)) :=
  (ParameterMatrixMassBounds.characteristicBudget_binary hr
    (IntegerPolynomialDyadic.massBudget_binary hc hk hh)).add (BinaryFn.const 1)

theorem normalizeAt_map_native_after_growth {width : ℕ}
    (b : CoefficientCoordinateBasis ℤ[X] A m (2 ^ width))
    (c : ∀ r, IntegralCoordinateBasis (B r) m (2 ^ width)) (p : A[X])
    (ψ : ∀ r, A →+* B r) (d C K H radius : ℕ)
    (hb : ∀ r, C ≤ r → CoefficientCoordinateBasis.Specializes
      (Polynomial.evalRingHom ((2 : ℤ) ^ r)) (ψ r) b
      (CoefficientCoordinateBasis.ofIntegral (c r)))
    (hn : ∀ r, C ≤ r → ∀ i j,
      (Algebra.leftMulMatrix (c r).finBasis ((p.map (ψ r)).coeff d) i j).natAbs ≤
        2 ^ (K * r + H))
    (hr : max C (cutBudget ((2 ^ width) ^ m) C K H) ≤ radius) :
    (CoefficientRelativeLeadingNormalization.normalizeAt b.basis p d
      (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly.natTrailingDegree).map (ψ radius) =
      IntegralRelativeLeadingNormalization.normalize (c radius).finBasis (p.map (ψ radius)) d := by
  apply CoefficientRelativeLeadingNormalization.normalizeAt_map_native_finBasis_after_radius
    b (c radius) radius (ψ radius) (hb radius (le_trans (le_max_left _ _) hr)) p d
    (IntegerPolynomialDyadic.massBudget C K H)
  · intro i j
    apply (degree_mass_finBasis b c (p.coeff d) ψ C K H hb _ i j).2
    intro r hcr s t
    simpa only [Polynomial.coeff_map] using hn r hcr s t
  · exact le_trans (le_max_right _ _) hr

end LeanCanny.Algebra.CoefficientCoordinateDyadicBounds

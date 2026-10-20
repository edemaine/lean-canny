/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.RadiusSource
public import LeanCanny.Geometry.RadiusCriticalEquations

/-! # Bounded integer critical equations for the encoded ETR source

There is one value equation and one equation per spatial coordinate. Singular
active points yield common zeros, with all shift coordinates set to zero.
Their degrees and count have FP upper-bound writers on every encoded input.
No coefficient-access implementation or elimination claim is made here.
-/

@[expose] public section

namespace LeanCanny.ETR.RadiusCriticalSource
open Complexity
open LeanCanny.Encoding
open Geometry

abbrev Index (bits : List Bool) := Option (Fin (CompactSource.term bits).arity)

noncomputable def polynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : Index bits) :
    MvPolynomial (PerturbedSource.Variable bits) ℤ :=
  PolynomialPerturbation.criticalPolynomial (CompactSource.polynomial bits) s j

theorem equations_iff (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : ℝ) (z : PerturbedSource.Point bits) :
    (∀ j, (polynomial bits s j).eval₂ (Int.castRingHom ℝ)
      (PolynomialPerturbation.assignment epsilon delta z) = 0) ↔
      ActiveRadius.energy (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s z.1 = delta ^ 2 ∧
        fderiv ℝ (ActiveRadius.energy (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s) z.1 = 0 :=
  PolynomialPerturbation.critical_equations_iff _ _ _ _ _

theorem singular_implies_equations (bits : List Bool) (epsilon delta : ℝ)
    (s : Finset (PerturbedSource.Index bits)) (z : PerturbedSource.Point bits)
    (hz : z ∈ PerturbedSource.feasible bits epsilon delta)
    (ha : ∀ i ∈ s, PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon z i = 0)
    (hs : ¬ Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap
      (PolynomialPerturbation.constraintMap (CompactSource.polynomial bits) epsilon) s delta) z)) :
    ∀ j, (polynomial bits s j).eval₂ (Int.castRingHom ℝ)
      (PolynomialPerturbation.assignment epsilon delta (z.1, 0)) = 0 :=
  PolynomialPerturbation.singular_implies_critical_equations _ _ _ _ _ hz ha hs

def countCode (bits : List Bool) : List Bool := BinaryNatCode.encode (CompactSource.size bits + 1)

theorem countCode_FP : countCode ∈ FP := by
  have h := bits_mem_FP (CompactSource.size_unary.add (UnaryFn.const 1))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem count_le_code (bits : List Bool) : Fintype.card (Index bits) ≤ Nat.fromBitsLE (countCode bits) := by
  simp only [Index, Fintype.card_option, Fintype.card_fin, countCode, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact Nat.add_le_add_right (CompactSource.term bits).arity_le_dataSize 1

theorem degree_le_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : Index bits) :
    (polynomial bits s j).totalDegree ≤ Nat.fromBitsLE (RadiusSource.degreeCode bits) := by
  have h := PolynomialPerturbation.criticalPolynomial_degree (CompactSource.polynomial bits) s j
  have hp := CompactSource.polynomial_degree bits
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

end LeanCanny.ETR.RadiusCriticalSource

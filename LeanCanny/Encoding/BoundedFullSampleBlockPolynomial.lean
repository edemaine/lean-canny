/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleBlock
public import LeanCanny.Encoding.BoundedCriticalProjection

/-! # Multivariate coefficients and bounds for cleared full-source blocks

The parameter occupies coordinate zero. The free block occupies the remaining
coordinates. Kronecker substitution agrees exactly with the native streamed
rational-substitution family and recovers each collected integer coefficient.
Degree and mass budgets are derived from source and parent controls.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleBlockPolynomial
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open BoundedFullSampleBlock
open BoundedCriticalSampleBlockSource
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (F : Inputs) (u : List Bool) : MvPolynomial (Fin (F.dim u + 1)) ℤ :=
  IndexedMultivariateRational.cleared (arity F u) ((family F).terms u) (clearing F u)
    ((family F).coefficient u) (FixedWidthPolynomial.entry (sourceWidth F u))
    (coordinate F.parent F.offset F.dim true u) (coordinate F.parent F.offset F.dim false u)

theorem polynomial_degree (F : Inputs) (u : List Bool) : (polynomial F u).totalDegree ≤ degreeBound F u :=
  IndexedMultivariateRational.totalDegree_cleared_le _ _ _ _ _ _ _ _
    ((family F).indexed.exponent_le u)
    (fun i _ => coordinate_degree F.parent F.offset F.dim true u i)
    (fun i _ => coordinate_degree F.parent F.offset F.dim false u i)

theorem support_fits (F : Inputs) (u : List Bool) (m : Fin (F.dim u + 1) →₀ ℕ)
    (hm : m ∈ (polynomial F u).support) (i : Fin (F.dim u + 1)) : m i < 2 ^ width F u :=
  ((monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree _ i)).trans_lt
    ((polynomial_degree F u).trans_lt (degree_lt F u))

theorem encode_polynomial (F : Inputs) (u : List Bool) :
    FixedWidthKronecker.encode (F.dim u + 1) (width F u) (polynomial F u) = (family F).polynomial u := by
  unfold polynomial
  rw [IndexedMultivariateRational.encode_cleared]
  simp only [BoundedCriticalSampleBlockCodes.encode_coordinate]
  exact (family F).polynomial_eq u

noncomputable def coefficient (F : Inputs) := PrimitivePairBits.coefficient (family F).polynomial

theorem evaluator {F : Inputs} (h : F.PolyTime)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (coefficient F) :=
  BoundedFullSampleBlock.evaluator h htP htS

theorem coefficient_packet (F : Inputs) (u : List Bool)
    (r : Fin (FixedWidthPolynomial.count (F.dim u + 1) (width F u))) (m : ℕ) (hm : 0 < m) :
    coefficient F (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((polynomial F u).coeff (FixedWidthPolynomial.vector _ _ r) : ℤ) : ZMod m) := by
  unfold coefficient PrimitivePairBits.coefficient
  simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  change MatrixPower.residueBits ((((family F).polynomial u).coeff r.val : ℤ) : ZMod m) = _
  apply congrArg (fun z : ℤ => MatrixPower.residueBits (z : ZMod m))
  rw [← encode_polynomial, FixedWidthKronecker.coefficient _ _ _ (support_fits F u) r]

noncomputable def encodedMass (F : Inputs) : List Bool → ℕ :=
  (family F).mass (BoundedCriticalProjection.sourceBits F.source)
    (fun u => BoundedCriticalRationalCoordinates.coordinateMass F.parent (pairFst u))

theorem encoded_mass (F : Inputs) (u : List Bool) : coefficientMass ((family F).polynomial u) ≤
    2 ^ encodedMass F u := by
  apply (family F).polynomial_mass
  · intro c r _
    exact (MvMass.coeff_le _ _).trans (BoundedCriticalProjection.source_mass F.source c)
  · intro c i _
    exact BoundedCriticalSampleBlockCodes.encoded_mass F.parent (width F) F.offset F.dim true c i
  · intro c i _
    exact BoundedCriticalSampleBlockCodes.encoded_mass F.parent (width F) F.offset F.dim false c i

theorem coefficient_bound (F : Inputs) (u : List Bool)
    (r : Fin (FixedWidthPolynomial.count (F.dim u + 1) (width F u))) :
    ((polynomial F u).coeff (FixedWidthPolynomial.vector _ _ r)).natAbs ≤ 2 ^ encodedMass F u := by
  rw [← FixedWidthKronecker.coefficient _ _ _ (support_fits F u) r, encode_polynomial]
  exact (coeff_natAbs_le_coefficientMass _ _).trans (encoded_mass F u)

noncomputable def mass (F : Inputs) (u : List Bool) : ℕ := span F u + encodedMass F u

theorem polynomial_mass (F : Inputs) (u : List Bool) : MvMass.mass (polynomial F u) ≤ 2 ^ mass F u := by
  rw [← FixedWidthPolynomial.sum_monomials_eq (F.dim u + 1) (width F u) _ (support_fits F u)]
  calc
    _ ≤ ∑ r : Fin (FixedWidthPolynomial.count (F.dim u + 1) (width F u)),
        MvMass.mass (MvPolynomial.monomial (FixedWidthPolynomial.vector _ _ r)
          ((polynomial F u).coeff (FixedWidthPolynomial.vector _ _ r))) := MvMass.sum_le _ _
    _ ≤ ∑ _r : Fin (FixedWidthPolynomial.count (F.dim u + 1) (width F u)), 2 ^ encodedMass F u := by
      apply Finset.sum_le_sum
      intro r _
      rw [MvMass.monomial]
      exact coefficient_bound F u r
    _ = FixedWidthPolynomial.count (F.dim u + 1) (width F u) * 2 ^ encodedMass F u := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = _ := by rw [FixedWidthPolynomial.count, ← pow_mul, ← pow_add]; rfl

theorem terms_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (family F).terms :=
  BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (arity_unary h) (sourceWidth_unary h))
    (FixedWidthPolynomial.countCode_code (arity F) (sourceWidth F)))

theorem encodedMass_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (encodedMass F) :=
  ((terms_binary h).size.add (BoundedCriticalProjection.sourceBits_binary h.source)).add
    (((BinaryFn.ofUnary (arity_unary h)).mul (clearing_binary h)).mul
      ((BoundedCriticalRationalCoordinates.coordinateMass_binary h.parent).comp pairFst_mem_FP))

theorem mass_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (mass F) :=
  (BinaryFn.ofUnary (span_unary h)).add (encodedMass_binary h)

end LeanCanny.Encoding.BoundedFullSampleBlockPolynomial

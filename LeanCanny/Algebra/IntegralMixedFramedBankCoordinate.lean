/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankCofactor
public import LeanCanny.Algebra.FixedWidthKronecker
/-! # Literal common-cleared coordinate polynomials of a joint prefix

Coordinate i is its actual integer cofactor times the fixed odd power of
the SAME joint prefix variable i. No independent coordinate-root choices
or root-lifting premise occurs in this representation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankDenominatorBits (count count_unary index state)
open IntegralMixedFramedCompanionQueryBits (root callerModulus)
open scoped Classical BigOperators

def horizon (P : Parameters) (q : List Bool) := P.cap (root q)+1
def scalarDegree (P : Parameters) (q : List Bool) := 2^P.width (root q)
noncomputable def weight (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  UniformIntegralPowerSchedule.power (horizon P) (scalarDegree P) (count P D H)
    (pair q (PaddedIntegralGeneratorSource.row q))

theorem weight_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (weight P D H) :=
  (UniformIntegralPowerSchedule.power_binary
    ((a.cap.comp IntegralMixedFramedCompanionQueryBits.root_FP).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (a.width.comp IntegralMixedFramedCompanionQueryBits.root_FP))
    (count_unary P a D H)).comp (mem_FP_pair id_mem_FP PaddedIntegralGeneratorSource.row_FP)

theorem weight_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hi : index q<count P D H q) :
    weight P D H q=UniformIntegralPowerSchedule.weights (horizon P q) (scalarDegree P q) (count P D H q) ⟨index q,hi⟩ := by
  have HI : Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)<count P D H q := hi
  simp only [weight,UniformIntegralPowerSchedule.power,UniformIntegralPowerSchedule.age,
    UniformIntegralPowerSchedule.weights,pairFst_pair,pairSnd_pair,IntegralMixedFramedBankDenominatorBits.index,
    min_eq_left HI.le]

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    MvPolynomial (Fin (count P D H q)) ℤ :=
  if hi : index q<count P D H q then
    MvPolynomial.C (IntegralMixedFramedBankProductBits.integer P D H index q)*
      MvPolynomial.X ⟨index q,hi⟩^weight P D H q
  else 0

noncomputable def clippedIndex (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  min (index q) (count P D H q)
theorem clippedIndex_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (clippedIndex P D H) :=
  UnaryFn.fromBitsLE_min PaddedIntegralGeneratorSource.row_FP (count_unary P a D H)

noncomputable def encodedDegree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (q : List Bool) := weight P D H q*2^(clippedIndex P D H q*W q)
theorem encodedDegree_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (hW : UnaryFn W) : BinaryFn (encodedDegree P D H W) :=
  (weight_binary P a D H).mul ((BinaryFn.const 2).powUnary ((clippedIndex_unary P a D H).mul hW))

theorem encoded_polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (W : List Bool → ℕ) (q : List Bool) :
    FixedWidthKronecker.encode (count P D H q) (W q) (polynomial P D H q)=
      if index q<count P D H q then Polynomial.monomial (encodedDegree P D H W q)
        (IntegralMixedFramedBankProductBits.integer P D H index q) else 0 := by
  unfold polynomial
  split_ifs with hi
  · rw [map_mul,map_pow]
    simp only [FixedWidthKronecker.encode,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
    rw [← pow_mul,Polynomial.C_mul_X_pow_eq_monomial]
    unfold encodedDegree clippedIndex
    rw [min_eq_left hi.le,Nat.mul_comm (2^(index q*W q))]
  · exact map_zero _

theorem polynomial_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (polynomial P D H q).totalDegree≤weight P D H q := by
  unfold polynomial
  split_ifs
  · exact (MvPolynomial.totalDegree_mul _ _).trans_eq (by rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X_pow,Nat.zero_add])
  · simp

end LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBits

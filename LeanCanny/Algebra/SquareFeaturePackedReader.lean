/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeatureProductFamily
public import LeanCanny.Algebra.FixedWidthKroneckerSpace
public import LeanCanny.Algebra.FixedWidthBoxRepackSpace
public import LeanCanny.Algebra.PrimitivePairReaders
/-! # Native packed feature coefficients at the whole-product width

Only retained factors use the supplied original coefficient access. Other
indices are zero, including every index when the product count is zero.
-/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeaturePackedReader
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open SquareFeatureProductFamily
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def sourceKey := RationalSubstitution.IntegerBits.context
def parent (z : List Bool) := pairFst (sourceKey z)
def index (z : List Bool) := Nat.fromBitsLE (pairSnd (sourceKey z))
def target := RationalSubstitution.IntegerBits.selectedDegree
theorem sourceKey_FP : sourceKey ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
theorem parent_FP : parent ∈ FP := mem_FP_comp sourceKey_FP pairFst_mem_FP
theorem index_binary : BinaryFn index := BinaryFn.fromBits (mem_FP_comp sourceKey_FP pairSnd_mem_FP)
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP

noncomputable def masked (F : Family) (q : List Bool) : MvPolynomial (Fin (F.arity (pairFst q))) ℤ :=
  if Nat.fromBitsLE (pairSnd q) < F.count (pairFst q) then F.feature (pairFst q) (Nat.fromBitsLE (pairSnd q)) else 0
noncomputable def rowArity (F : Family) (z : List Bool) := F.arity (parent z)
noncomputable def rowInputWidth (F : Family) (z : List Bool) := inputWidth F (parent z)
noncomputable def rowWidth (F : Family) (z : List Bool) := width F (parent z)
noncomputable def rowPolynomial (F : Family) (z : List Bool) : MvPolynomial (Fin (rowArity F z)) ℤ :=
  masked F (sourceKey z)
noncomputable def rowDegree (F : Family) (z : List Bool) := degree F (parent z)
noncomputable def packed (F : Family) (q : List Bool) : Polynomial ℤ :=
  FixedWidthKronecker.encode (F.arity (pairFst q)) (width F (pairFst q)) (masked F q)

theorem masked_degree (F : Family) (q : List Bool) : (masked F q).totalDegree ≤ F.degree (pairFst q) := by
  unfold masked
  split_ifs with hi
  · exact F.feature_degree _ _ hi
  · simp
theorem masked_wide_degree (F : Family) (q : List Bool) : (masked F q).totalDegree ≤ degree F (pairFst q) := by
  unfold masked
  split_ifs with hi
  · apply (F.feature_degree _ _ hi).trans
    have HN : 1 ≤ F.count (pairFst q) := by omega
    unfold degree
    exact (by omega : F.degree (pairFst q) ≤ 2*F.degree (pairFst q)+1).trans
      (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2*F.degree (pairFst q)+1) HN)
  · simp
theorem masked_mass (F : Family) (q : List Bool) : MvMass.mass (masked F q) ≤ 2^F.mass (pairFst q) := by
  unfold masked
  split_ifs with hi
  · exact F.feature_mass _ _ hi
  · simp

def valid (F : Family) (z : List Bool) : Prop := index z < F.count (parent z)
noncomputable instance squareFeaturePackedValidDecidable (F : Family) : DecidablePred (valid F) := fun _ => Classical.propDecidable _
theorem valid_FP (F : Family) (A : Access F) : FPPred (valid F) := index_binary.lt (A.count.comp parent_FP)

def query (bits modulus : List Bool → List Bool) (z : List Bool) :=
  pair (pair (pair (parent z) (BinaryNatCode.encode (index z))) (bits z)) (modulus z)
theorem query_FP (bits modulus : List Bool → List Bool) (hb : bits ∈ FP) (hm : modulus ∈ FP) :
    query bits modulus ∈ FP := mem_FP_pair (mem_FP_pair (mem_FP_pair parent_FP index_binary.bits_mem_FP) hb) hm
noncomputable def read (F : Family) (A : Access F) (bits modulus : List Bool → List Bool) (z : List Bool) :=
  if valid F z then A.coefficient (query bits modulus z) else []
theorem read_evaluator (F : Family) (A : Access F) (bits modulus : List Bool → List Bool)
    (hb : bits ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (read F A bits modulus) := by
  have HE := SpaceFunction.branch (fun z => decide (valid F z)) (valid_FP F A).flag_mem_FP
    (A.evaluator.precompose (query bits modulus) (query_FP bits modulus hb hm))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact HE.congr (funext fun z => by simp only [read, decide_eq_true_eq, Function.comp_apply])

theorem read_packet (F : Family) (A : Access F) (bits modulus : List Bool → List Bool) (z : List Bool) :
    read F A bits modulus z = FixedWidthRowBits.value (rowArity F) (rowInputWidth F)
      (rowPolynomial F) bits modulus z := by
  by_cases hi : valid F z
  · rw [read, ite_eq_left hi, query, A.packet _ _ hi]
    dsimp only [FixedWidthRowBits.value, rowPolynomial, rowArity, rowInputWidth, masked, parent, index]
    dsimp only [valid, index, parent] at hi
    rw [ite_eq_left hi]
  · rw [read, ite_eq_right hi]
    dsimp only [FixedWidthRowBits.value, rowPolynomial, rowArity, rowInputWidth, masked, parent, index]
    dsimp only [valid, index, parent] at hi
    rw [ite_eq_right hi]
    simp [residueBits, BinaryNatCode.encode]

theorem row_evaluator (F : Family) (A : Access F) (bits modulus : List Bool → List Bool)
    (hb : bits ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (rowArity F) (rowInputWidth F) (rowPolynomial F) bits modulus) :=
  (read_evaluator F A bits modulus hb hm).congr (funext (read_packet F A bits modulus))

theorem packed_evaluator (F : Family) (A : Access F) : SpaceFunction (PrimitivePairBits.coefficient (packed F)) := by
  have HA : UnaryFn (rowArity F) := A.arity.comp parent_FP
  have HB : UnaryFn (rowInputWidth F) := (inputWidth_unary F A).comp parent_FP
  have HV : UnaryFn (rowWidth F) := (width_unary F A).comp parent_FP
  have HP : ∀ z e, e ∈ (rowPolynomial F z).support → ∀ i, e i < 2^rowInputWidth F z := by
    intro z e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans ((MvPolynomial.degreeOf_le_totalDegree _ i).trans
      (masked_degree F (sourceKey z)))).trans_lt ((Nat.lt_succ_self _).trans (Nat.lt_size_self _))
  have HR := FixedWidthQuery.repack_mem_FP HA HV HA HB target_FP
  have ER := row_evaluator F A (FixedWidthQuery.repack (rowArity F) (rowWidth F) (rowArity F) (rowInputWidth F) target)
    pairSnd HR pairSnd_mem_FP
  have EW := FixedWidthBoxRepackBits.evaluator (rowArity F) (rowInputWidth F) (rowWidth F)
    (rowPolynomial F) HP target pairSnd HA HB HV target_FP ER
  have HD : ∀ z, (rowPolynomial F z).totalDegree ≤ rowDegree F z := fun z => masked_wide_degree F (sourceKey z)
  have HF : ∀ z, rowDegree F z < 2^rowWidth F z := fun z =>
    (Nat.lt_succ_self _).trans (Nat.lt_size_self _)
  have EK := FixedWidthKroneckerBits.evaluator (rowArity F) (rowWidth F) (rowDegree F) (rowPolynomial F)
    target pairSnd HA HV target_FP HD HF EW
  exact EK.congr (funext fun z => rfl)

theorem kronecker_mass (n W : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    coefficientMass (FixedWidthKronecker.encode n W p) ≤ MvMass.mass p := by
  conv_lhs => rw [p.as_sum, map_sum]
  apply (coefficientMass_sum_le _ _).trans
  simp only [FixedWidthKronecker.monomial, coefficientMass_monomial]
  exact le_rfl

theorem packed_mass (F : Family) (q : List Bool) : coefficientMass (packed F q) ≤ 2^F.mass (pairFst q) :=
  (kronecker_mass _ _ _).trans (masked_mass F q)

theorem packed_degree (F : Family) (q : List Bool) : (packed F q).natDegree ≤
    FixedWidthPolynomial.count (F.arity (pairFst q)) (width F (pairFst q)) := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply FixedWidthKronecker.coefficient_of_ge _ _ _ _ k hk.le
  intro e he i
  exact ((MvPolynomial.monomial_le_degreeOf i he).trans ((MvPolynomial.degreeOf_le_totalDegree _ i).trans
    (masked_wide_degree F q))).trans_lt ((Nat.lt_succ_self _).trans (Nat.lt_size_self _))

end LeanCanny.Algebra.SquareFeaturePackedReader

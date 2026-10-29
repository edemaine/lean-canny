/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildRecords
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # A short-record spanning matrix for regular child candidates

Every sparse monomial has a record of the constructed polynomial length.
All records span the full regular-child function space, without selecting a
basis. Their Gram matrix has rank exactly the regular child count.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildRecordSpan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open RationalParentChildRecords Submodule
open RationalParentChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildQueries.roots RationalParentChildRegularCount.count
  RationalParentChildCoordinates.parameterDegree RationalParentChildThom.labelWidth

abbrev Root (P : Inputs) (c : List Bool) := RationalParentChildThom.Root P c
abbrev Feature (P : Inputs) (c : List Bool) := RationalParentChildThom.Feature P c
abbrev Index (P : Inputs) (c : List Bool) := Fin (2 ^ RationalParentChildRecords.length P c)

noncomputable def row (P : Inputs) (c r : List Bool) : Root P c → ℚ :=
  SparseFeatureRecords.value (Nat.succ_pos _) (slots P c) (width P c)
    (fun i : Feature P c => fun x => (RationalParentChildThom.signature P c x i : ℚ)) r

theorem row_apply (P : Inputs) (c r : List Bool) (x : Root P c) :
    row P c r x = SparseFeatureRecords.value (Nat.succ_pos _) (slots P c) (width P c)
      (fun i : Feature P c => (RationalParentChildThom.signature P c x i : ℚ)) r := by
  simp only [row, SparseFeatureRecords.value, Finset.prod_apply, SparseFeatureRecords.factor,
    ite_apply, Pi.one_apply]

theorem signature_apply (P : Inputs) (c : List Bool) (x : Root P c) (i : Feature P c) :
    RationalParentChildThom.signature P c x i = SignType.sign
      (((RationalParentChildThom.polynomial P c i.val).map (Int.castRingHom ℝ)).eval x.val) := by
  simp only [RationalParentChildThom.signature, ThomEncoding.signature, ThomEncoding.sign,
    RationalParentChildThom.polynomial, Polynomial.iterate_derivative_map]

theorem slot_coordinate (P : Inputs) (c r : List Bool) (i : ℕ)
    (hi : i < recordSlots P (pair c r)) :
    slot P (pair c r) i = SparseFeatureRecords.coordinate (width P c) r i := by
  rw [slot, FixedWidthQuery.entry, ite_eq_left hi]
  simp only [FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, pairSnd_pair,
    SparseFeatureRecords.coordinate]

theorem sign_polynomial (P : Inputs) (c r : List Bool) (i : ℕ)
    (hi : i < recordSlots P (pair c r)) (x : Root P c) :
    (SignType.sign (((polynomial P (pair c r) i).map (Int.castRingHom ℝ)).eval x.val) : ℚ) =
      SparseFeatureRecords.factor (Nat.succ_pos _)
        (fun k : Feature P c => (RationalParentChildThom.signature P c x k : ℚ))
        (SparseFeatureRecords.coordinate (width P c) r i) := by
  have hs := slot_coordinate P c r i hi
  by_cases hz : SparseFeatureRecords.coordinate (width P c) r i = 0
  · simp only [polynomial, hs, hz, ite_true, Polynomial.map_one, Polynomial.eval_one,
      sign_one, SignType.cast, SparseFeatureRecords.factor_zero]
  · rw [polynomial, ite_eq_right (by rwa [hs]), SparseFeatureRecords.factor, ite_eq_right hz, signature_apply]
    simp only [order, hs, pairFst_pair, SparseFeatureRecords.pick, Nat.succ_sub_one]

theorem moment_eq_sum_values (P : Inputs) (c r : List Bool) :
    (moment P (pair c r) : ℚ) = ∑ x : Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (recordSlots P (pair c r)) (width P c)
        (fun i : Feature P c => (RationalParentChildThom.signature P c x i : ℚ)) r := by
  rw [moment, RationalParentChildReindexedQueries.moment]
  simp only [RationalParentChildQueries.product]
  simp only [family, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, algebraMap_int_eq]
  rw [Int.cast_sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro x _
  simp only [SparseFeatureRecords.value, Int.cast_prod, SignType.intCast_cast]
  apply Finset.prod_congr rfl
  intro i hi
  exact sign_polynomial P c r i (Finset.mem_range.mp hi) x

theorem moment_eq_sum_rows (P : Inputs) (c r : List Bool) (hr : r.length = RationalParentChildRecords.length P c) :
    (moment P (pair c r) : ℚ) = ∑ x : Root P c, row P c r x := by
  rw [moment_eq_sum_values, recordSlots_packet P c r hr]
  exact Finset.sum_congr rfl (fun x _ => (row_apply P c r x).symm)

theorem feature_fits (P : Inputs) (c : List Bool) :
    RationalParentChildCoordinates.parameterDegree P c + 1 < 2 ^ width P c := by
  unfold width
  rw [pow_add]
  have hd := Nat.lt_size_self (RationalParentChildCoordinates.parameterDegree P c)
  have hp := Nat.two_pow_pos (RationalParentChildCoordinates.parameterDegree P c).size
  norm_num
  omega

theorem monomial_has_record (P : Inputs) (c : List Bool) (d : Feature P c →₀ ℕ)
    (hs : d.support.card ≤ RationalParentChildThom.labelWidth P c) (he : ∀ i, d i ≤ 2) :
    ∃ r, r.length = RationalParentChildRecords.length P c ∧
      row P c r = RationalParentChildThom.vector P c d := by
  have ht := SparseFeatureRecords.total_exponent_le d _ hs he
  obtain ⟨r, hr, hv⟩ := SparseFeatureRecords.exists_record
    (M := Root P c → ℚ) (Nat.succ_pos (RationalParentChildCoordinates.parameterDegree P c))
    (slots P c) (width P c) (feature_fits P c) d ht
  refine ⟨r, hr, ?_⟩
  unfold row
  rw [hv]
  simp only [RationalParentChildThom.vector, MonomialEvaluationBasis.vector,
    MvPolynomial.aeval_monomial, map_one, one_mul]

theorem span_rows (P : Inputs) (c : List Bool) :
    Submodule.span ℚ (row P c '' {r | r.length = RationalParentChildRecords.length P c}) = ⊤ := by
  apply top_unique
  rw [← RationalParentChildThom.sparse_span P c]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨r, hr, hv⟩ := monomial_has_record P c d hd.1 hd.2
  rw [← hv]
  exact Submodule.subset_span ⟨r, hr, rfl⟩

noncomputable def matrix (P : Inputs) (c : List Bool) : Matrix (Index P c) (Root P c) ℚ :=
  Matrix.of (fun i => row P c (ImplicitGraph.word (RationalParentChildRecords.length P c) i.val))

theorem span_matrix_rows (P : Inputs) (c : List Bool) : Submodule.span ℚ (Set.range (matrix P c).row) = ⊤ := by
  apply top_unique
  rw [← span_rows P c]
  apply Submodule.span_le.mpr
  rintro _ ⟨r, hr, rfl⟩
  have hi : Nat.fromBitsLE r < 2 ^ RationalParentChildRecords.length P c := by
    rw [← hr]
    exact Nat.fromBitsLE_lt_pow_length r
  apply Submodule.subset_span
  refine ⟨⟨Nat.fromBitsLE r, hi⟩, ?_⟩
  change row P c (ImplicitGraph.word (RationalParentChildRecords.length P c) (Nat.fromBitsLE r)) = row P c r
  rw [← hr, ImplicitGraph.word_fromBitsLE]

theorem rank_matrix (P : Inputs) (c : List Bool) : (matrix P c).rank = RationalParentChildRegularCount.count P c := by
  rw [Matrix.rank_eq_finrank_span_row, span_matrix_rows, finrank_top, Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_coe]
  exact RationalParentChildQueries.roots_card P c

noncomputable def gram (P : Inputs) (c : List Bool) : Matrix (Index P c) (Index P c) ℚ :=
  matrix P c * (matrix P c).transpose

theorem rank_gram (P : Inputs) (c : List Bool) : (gram P c).rank = RationalParentChildRegularCount.count P c := by
  rw [gram, Matrix.rank_self_mul_transpose, rank_matrix]

/-- Packet `pair context (pair rowIndex columnIndex)`. -/
noncomputable def gramQuery (P : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst q)
    (ImplicitGraph.word (RationalParentChildRecords.length P (pairFst q)) (Nat.fromBitsLE (pairFst (pairSnd q))) ++
      ImplicitGraph.word (RationalParentChildRecords.length P (pairFst q)) (Nat.fromBitsLE (pairSnd (pairSnd q))))

theorem gramQuery_FP {P : Inputs} (h : P.Access) : gramQuery P ∈ FP := by
  have hw := (RationalParentChildRecords.length_unary h).comp pairFst_mem_FP
  have hL := ImplicitGraph.word_computable hw (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
  have hR := ImplicitGraph.word_computable hw (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
  have H := mem_FP_pair pairFst_mem_FP (appendFn_mem_FP hL hR)
  exact mem_FP_of_eq H (fun _ => by simp only [gramQuery, Function.comp_apply])

noncomputable def entry (P : Inputs) (q : List Bool) : ℤ := moment P (gramQuery P q)

theorem entry_evaluator {P : Inputs} (h : P.Access) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P q)) := by
  have E := (RationalParentChildRecords.evaluator h).precompose (gramQuery P) (gramQuery_FP h)
  exact E

theorem dimension_binary {P : Inputs} (h : P.Access) :
    BinaryFn (fun c => 2 ^ RationalParentChildRecords.length P c) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (RationalParentChildRecords.length_unary h)

theorem entry_bounds (P : Inputs) (q : List Bool) :
    -((2 ^ RationalParentChildThom.labelWidth P (pairFst q) : ℕ) : ℤ) ≤ entry P q ∧
      entry P q ≤ ((2 ^ RationalParentChildThom.labelWidth P (pairFst q) : ℕ) : ℤ) := by
  have hv := moment_bound P (gramQuery P q)
  have he : pairFst (gramQuery P q) = pairFst q := by simp only [gramQuery, pairFst_pair]
  rw [he] at hv
  change (moment P (gramQuery P q)).natAbs ≤ _ at hv
  have hc : (-(moment P (gramQuery P q)).natAbs : ℤ) ≤ moment P (gramQuery P q) ∧
      moment P (gramQuery P q) ≤ (moment P (gramQuery P q)).natAbs := by omega
  constructor <;> dsimp only [entry] <;> omega

theorem entry_packet (P : Inputs) (c : List Bool) (i j : Index P c) :
    (entry P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) = gram P c i j := by
  rw [gram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp only [entry, gramQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  let r := ImplicitGraph.word (RationalParentChildRecords.length P c) i.val
  let s := ImplicitGraph.word (RationalParentChildRecords.length P c) j.val
  have hr : r.length = RationalParentChildRecords.length P c := ImplicitGraph.length_word _ _
  have hs : s.length = RationalParentChildRecords.length P c := ImplicitGraph.length_word _ _
  have hc : recordSlots P (pair c (r ++ s)) = slots P c + slots P c := by
    simp only [recordSlots, pairFst_pair, pairSnd_pair, List.length_append, hr, hs, RationalParentChildRecords.length]
    rw [← Nat.add_mul, Nat.mul_div_cancel _ (width_pos P c)]
  rw [moment_eq_sum_values, hc]
  change (∑ x : Root P c, SparseFeatureRecords.value (Nat.succ_pos _)
    (slots P c + slots P c) (width P c)
    (fun k : Feature P c => (RationalParentChildThom.signature P c x k : ℚ)) (r ++ s)) = _
  simp_rw [SparseFeatureRecords.value_append _ _ _ _ _ r s hr]
  apply Finset.sum_congr rfl
  intro x _
  rw [← row_apply P c r x, ← row_apply P c s x]
  rfl

end LeanCanny.Encoding.RationalParentChildRecordSpan

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullHeadBounds
/-! # Original numeric controls for all complete physical coordinate heads -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullHeadControls
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem degree_aux (P : IntegralCriticalHistoryTask.Parameters)
    (T : IntegralMixedHeaderTablesBits.Tables) (root : List Bool) (b : ℕ) (u v : List Bool) (j : ℕ) :
    IntegralMixedFramedPhysicalRowDegree.degree P T
      (pair (IntegralMixedFramedHistoryFamilyBits.keyAt root b u) (BinaryNatCode.encode j)) =
    IntegralMixedFramedPhysicalRowDegree.degree P T
      (pair (IntegralMixedFramedHistoryFamilyBits.keyAt root b v) (BinaryNatCode.encode j)) := by
  simp only [IntegralMixedFramedPhysicalRowDegree.degree,
    IntegralMixedFramedPhysicalRowDegree.scalarDegree, IntegralMixedFramedPhysicalRowDegree.physicalPower,
    IntegralMixedFramedPhysicalRowDegree.Frozen, IntegralMixedFramedPhysicalRowDegree.header,
    IntegralMixedFramedPhysicalRowSelector.IsScalar, IntegralMixedFramedPhysicalRowSelector.localRow,
    IntegralMixedFramedPhysicalRowSelector.fullArity, IntegralMixedFramedPhysicalRowSelector.birthPacket,
    IntegralMixedFramedPhysicalRowSelector.rowBirth, IntegralMixedFramedPhysicalIndex.prefixArity,
    IntegralMixedFramedPhysicalIndex.span, IntegralMixedFramedHistoryFamilyBits.prefixLength,
    IntegralMixedFullHistoryFamilyBits.prefixLength, IntegralMixedFramedHistoryFamilyBits.keyAt,
    pairFst_pair, pairSnd_pair]

private theorem dimension_binary_of_readers (count : List Bool → ℕ) (d : List Bool → ℕ → ℕ)
    (hc : UnaryFn count) (hd : BinaryFn (fun q => d (pairFst q) (pairSnd q).length)) :
    BinaryFn (fun q => AffineRingCoordinates.dimension (fun i : Fin (count q) => d q i.val)) := by
  have hs := (BinaryFn.sum hc (hd.sub (BinaryFn.const 1))).add (BinaryFn.const 1)
  have hl : BinaryFn (fun q => Macaulay.level
      (AffineRingGramEliminant.degrees (fun i : Fin (count q) => d q i.val))) := by
    apply BinaryFn.of_eq hs
    intro q
    simp only [Macaulay.level, AffineRingGramEliminant.degrees, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, Nat.sub_self, zero_add, pairFst_pair, pairSnd_pair,
      List.length_replicate]
    exact congrArg (fun z : ℕ => z + 1) (Fin.sum_univ_eq_sum_range (fun i => d q i - 1) (count q)).symm
  have hw : UnaryFn (fun q => AffineRingCoordinates.width (fun i : Fin (count q) => d q i.val)) :=
    UnaryFn.of_eq (UnaryFn.length hl.bits_mem_FP) (fun _ => BinaryNatCode.length_encode _)
  have he := (hc.add (UnaryFn.const 1)).mul hw
  have hn := (BinaryFn.ofUnary (hc.add (UnaryFn.const 3))).mul ((BinaryFn.const 2).powUnary he)
  apply BinaryFn.of_eq hn
  intro q
  unfold AffineRingCoordinates.dimension AffineRingGramEliminant.dimension FixedWidthPolynomial.count
  rw [← pow_mul]
  rw [Nat.mul_comm (AffineRingCoordinates.width _) (count q + 1)]

def context (q : List Bool) := pairFst q
def stage (q : List Bool) := min (pairSnd q).length (IntegralMixedCausalRecordPlanBits.count (context q))
theorem stage_le (q : List Bool) : stage q ≤ IntegralMixedCausalRecordPlanBits.count (context q) := min_le_right _ _
theorem context_FP : context ∈ FP := pairFst_mem_FP
theorem stage_unary : UnaryFn stage :=
  (UnaryFn.length pairSnd_mem_FP).min (IntegralMixedCausalRecordPlanBits.count_unary.comp context_FP)

def key {n : List Bool → ℕ} (q : List Bool) := CoefficientMarkedRecordRowLayout.key (n := n) (context q) (stage q) []

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

include hn in
theorem key_FP : key (n := n) ∈ FP := by
  have hb := (((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).comp context_FP).add
    (UnaryFn.const 8)).add stage_unary
  apply mem_FP_of_eq (mem_FP_pair context_FP (mem_FP_pair (BinaryFn.ofUnary hb).bits_mem_FP (constFn_mem_FP [])))
  intro q
  simp only [key, CoefficientMarkedRecordRowLayout.key, IntegralMixedFramedHistoryFamilyBits.keyAt,
    CoefficientMarkedPreludeActual.indices_length]

noncomputable def count (q : List Bool) :=
  (CoefficientMarkedRecordRows.symbolic hn ht ha (context q) (stage q) (stage_le q)).count

theorem count_unary : UnaryFn (count hn ht ha) := by
  let C := IntegralMixedAuxiliaryMarkedRecordPlan.controls hn ht ha (BinaryFn.const 0)
  have hc := IntegralFramedPhysicalSquare.count_unary
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha (fun _ => 0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha (fun _ => 0))
    C.scalar.tables C.scalar.native C.scalar.represents (key (n := n)) (key_FP hn)
  apply UnaryFn.of_eq hc
  intro q
  exact CoefficientMarkedRecordRowLayout.count_eq hn ht ha (context q) (fun _ => 0) (stage q) (stage_le q) []

noncomputable def degree (q : List Bool) (j : ℕ) :=
  CoefficientMarkedRecordFullHeads.degrees hn ht ha (context q) (stage q) [] j

theorem degree_binary : BinaryFn (fun q => degree hn ht ha (pairFst q) (pairSnd q).length) := by
  have htable : IntegralMixedHeaderTablesBits.Access (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) := by
    rw [← CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha (BinaryFn.const 0)]
    exact IntegralMixedPhysicalMarkedPlan.tables_native hn ht ha (BinaryFn.const 0) false
  have hd := IntegralMixedFramedPhysicalRowDegree.degree_binary
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) htable
  have hq := mem_FP_pair (mem_FP_comp pairFst_mem_FP (key_FP hn))
    (BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)).bits_mem_FP
  exact BinaryFn.of_eq (hd.comp hq) (fun q => by simp only [degree, key,
    CoefficientMarkedRecordFullHeads.degrees, Function.comp_apply])

noncomputable def dimension (q : List Bool) :=
  CoefficientMarkedRecordFullHeadBounds.dimension hn ht ha (context q) (stage q) (stage_le q) []

theorem dimension_binary : BinaryFn (dimension hn ht ha) :=
  dimension_binary_of_readers (count hn ht ha) (degree hn ht ha) (count_unary hn ht ha) (degree_binary hn ht ha)

attribute [local irreducible] dimension

theorem dimension_aux (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (u v : List Bool) :
    CoefficientMarkedRecordFullHeadBounds.dimension hn ht ha ctx k hk u =
      CoefficientMarkedRecordFullHeadBounds.dimension hn ht ha ctx k hk v := by
  have hd : CoefficientMarkedRecordFullHeads.degrees hn ht ha ctx k u =
      CoefficientMarkedRecordFullHeads.degrees hn ht ha ctx k v := by
    funext j
    exact degree_aux (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) ctx
      ((CoefficientMarkedPreludeActual.indices n ctx).length + k) u v j
  unfold CoefficientMarkedRecordFullHeadBounds.dimension
  exact congrArg (fun d : ℕ → ℕ => AffineRingCoordinates.dimension
    (fun i : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count => d i.val)) hd

theorem dimension_packet (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    dimension hn ht ha (pair ctx (List.replicate k true)) =
      CoefficientMarkedRecordFullHeadBounds.dimension hn ht ha ctx k hk [] := by
  simp only [dimension, context, stage, pairFst_pair, pairSnd_pair, List.length_replicate, min_eq_left hk]

/-- A finite original metadata sum bounds every prefix and every auxiliary context. -/
noncomputable def budget (ctx : List Bool) :=
  ∑ k ∈ Finset.range (IntegralMixedCausalRecordPlanBits.count ctx + 1),
    dimension hn ht ha (pair ctx (List.replicate k true))

theorem budget_binary : BinaryFn (budget hn ht ha) :=
  BinaryFn.sum (IntegralMixedCausalRecordPlanBits.count_unary.add (UnaryFn.const 1)) (dimension_binary hn ht ha)

theorem dimension_le_budget (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) :
    CoefficientMarkedRecordFullHeadBounds.dimension hn ht ha ctx k hk aux ≤ budget hn ht ha ctx := by
  rw [dimension_aux hn ht ha ctx k hk aux [], ← dimension_packet hn ht ha ctx k hk]
  unfold budget
  exact Finset.single_le_sum (f := fun j : ℕ => dimension hn ht ha (pair ctx (List.replicate j true)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

noncomputable def slope (ctx : List Bool) :=
  budget hn ht ha ctx * IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope hn ht ha ctx
noncomputable def offset (ctx : List Bool) :=
  (budget hn ht ha ctx).size * budget hn ht ha ctx +
    budget hn ht ha ctx * (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset hn ht ha ctx + 1)
noncomputable def coefficientBudget (ctx : List Bool) :=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (slope hn ht ha ctx) (offset hn ht ha ctx)

theorem slope_binary : BinaryFn (slope hn ht ha) :=
  (budget_binary hn ht ha).mul (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowSlope_binary hn ht ha)
theorem offset_binary : BinaryFn (offset hn ht ha) :=
  ((budget_binary hn ht ha).size.mul (budget_binary hn ht ha)).add
    ((budget_binary hn ht ha).mul ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rowOffset_binary hn ht ha).add
      (BinaryFn.const 1)))
theorem coefficientBudget_binary : BinaryFn (coefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (slope_binary hn ht ha) (offset_binary hn ht ha)

attribute [local irreducible] budget slope offset coefficientBudget
  CoefficientMarkedRecordFullHeadBounds.dimension CoefficientMarkedRecordFullHeads.polynomial
  CoefficientMarkedRecordRows.symbolic

/-- All original prefixes and auxiliary contexts share these computed coefficient bounds. -/
theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (i : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count) (j : ℕ) :
    ((CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk aux i).coeff j).natDegree ≤ slope hn ht ha ctx ∧
      coefficientMass ((CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk aux i).coeff j) ≤
        2 ^ coefficientBudget hn ht ha ctx := by
  have hn0 := dimension_le_budget hn ht ha ctx k hk aux
  have hs : CoefficientMarkedRecordFullHeadBounds.slope hn ht ha ctx k hk aux ≤ slope hn ht ha ctx := by
    unfold CoefficientMarkedRecordFullHeadBounds.slope slope
    exact Nat.mul_le_mul_right _ hn0
  have ho : CoefficientMarkedRecordFullHeadBounds.offset hn ht ha ctx k hk aux ≤ offset hn ht ha ctx := by
    unfold CoefficientMarkedRecordFullHeadBounds.offset offset
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.size_le_size hn0) hn0) (Nat.mul_le_mul_right _ hn0)
  unfold coefficientBudget
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have hm := (coeff_natAbs_le_coefficientMass
    ((CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk aux i).map (evalRingHom ((2 : ℤ)^r))) j).trans
      (CoefficientMarkedRecordFullHeadBounds.evaluated_mass hn ht ha ctx k hk aux i r hr)
  have he := Nat.add_le_add (Nat.mul_le_mul_right r hs) ho
  exact (show (((CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk aux i).coeff j).eval
    ((2 : ℤ)^r)).natAbs ≤ _ by simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] using hm).trans
      (Nat.pow_le_pow_right (by decide) he)

end LeanCanny.Encoding.CoefficientMarkedRecordFullHeadControls

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerHeight
/-! # Original-only growth for every raw continuation record

Three affine nodes and literal scales 1/2 bound arbitrary midpoint records.
The factor absorbs the horizon and current-Q slope growth. The source mass
and integer-source envelope are derived from the original n, term and radius.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedStepHeight IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def seed {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (root : List Bool) :=
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR root+IntegralMixedAuxiliaryOuterIntegerSource.exponent n t R root+1

theorem seed_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : BinaryFn (seed hn ht ha hR) :=
  ((IntegralMixedAuxiliaryMarkedIntegerPlan.seed_binary hn ht ha hR).add
    (IntegralMixedAuxiliaryOuterIntegerSource.exponent_binary hn ht hR)).add (BinaryFn.const 1)

private theorem mass_le_seed {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (root : List Bool) (i : ℕ) (hi : i<number n root+10) :
    (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R).mass (pair root (BinaryNatCode.encode i))≤seed hn ht ha hR root := by
  have HE : IntegralMixedAuxiliaryOuterIntegerSource.exponent n t R root+1≤seed hn ht ha hR root := by unfold seed; omega
  have HM : IntegralMixedAuxiliaryMarkedIntegerPlan.integerMass hn ht ha hR root≤seed hn ht ha hR root := by
    unfold seed IntegralMixedAuxiliaryMarkedIntegerPlan.seed
    omega
  simp only [IntegralMixedAuxiliaryOuterIntegerSource.source,IntegerPolynomialSourceChoice.choose,
    PowerIntegerPolynomial.source,IntegralMixedAuxiliaryMarkedIntegerSource.tag,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,Function.comp_apply]
  split_ifs with hp hn'
  · exact HE
  · exact HE
  · have HO:=IntegerPolynomialFiniteMassEnvelope.mass_le
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
      (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR) (fun c=>number n c+8)
      ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8)) root i (by omega)
    exact HO.trans HM

noncomputable def factor {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (root : List Bool) :=
  (parameters hn ht ha).cap root+1

theorem factor_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) : BinaryFn (factor hn ht ha) :=
  BinaryFn.ofUnary ((access hn ht ha).cap.add (UnaryFn.const 1))

theorem factor_positive {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (root : List Bool) :
    1≤factor hn ht ha root := Nat.succ_le_succ (Nat.zero_le _)

theorem sourceBounds {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (root : List Bool) :
    InstructionBounds (seed hn ht ha hR root+1) (factor hn ht ha root)
      ((parameters hn ht ha).sourceWidth root) ((parameters hn ht ha).degree root) 3
      (⟨IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root,source_cap hn ht ha R root,
        IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction ((parameters hn ht ha).ambient root) ((parameters hn ht ha).width root)) := by
  have HB:=IntegralMixedAuxiliaryMarkedIntegerPlan.default_height hn ht ha hR root
  have HF:=factor_positive hn ht ha root
  have HS : IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR root≤seed hn ht ha hR root := by unfold seed; omega
  have HE : 1*(IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR root+1)+1≤
      factor hn ht ha root*(seed hn ht ha hR root+1)+1 := by nlinarith
  constructor
  · intro e
    exact (HB.low e).trans (Nat.pow_le_pow_right (by decide) HE)
  · exact HB.leading.trans HE
  · exact HB.width
  · exact HB.degree
  · exact HB.auxiliary
  · intro k
    exact (HB.command k).trans (Nat.pow_le_pow_right (by decide) HE)

theorem familyInputs {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) :
    FamilyInputs (parameters hn ht ha) (plan hn ht ha R) (fun _=>3) (factor hn ht ha)
      (seed hn ht ha hR) := by
  apply IntegralMixedSourceIntegerRecordAppend.familyInputs (parameters hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root) (positive hn ht ha)
    (fun root _=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root) (spatial_cap hn ht ha)
    (fun c=>number n c+10) (source_cap hn ht ha R) (IntegralMixedAuxiliaryOuterIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryOuterIntegerSource.nonzero hn ht ha R)
    (source_degree_cap hn ht ha R) (room hn ht ha)
    (fun _=>3) (factor hn ht ha) (seed hn ht ha hR)
  · exact fun _=>le_rfl
  · exact fun root _=>sourceBounds hn ht ha hR root
  · intro root i hi
    have H:=mass_le_seed hn ht ha hR root i hi
    have HF:=factor_positive hn ht ha root
    nlinarith
  · intro root
    have HF:=factor_positive hn ht ha root
    nlinarith
  · exact fun _=>le_rfl

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterRecordPlan

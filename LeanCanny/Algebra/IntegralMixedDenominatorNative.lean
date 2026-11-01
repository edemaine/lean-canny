/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorMetadata
public import LeanCanny.Algebra.ModularProductSpace
/-! # Native mixed denominator controls with charged primitive scalar leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedDenominatorBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem binary_bounded_unary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : UnaryFn g) (h : ∀ p, f p ≤ g p) : UnaryFn f :=
  (UnaryFn.fromBitsLE_of_le hf.bits_mem_FP hg (fun p => by
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact h p)).of_eq (fun _ => Nat.fromBitsLE_bits _)

theorem offset_unary (F : Family) (a : Access F) : UnaryFn (fun p => offset F (pairFst p) (IntegralDenominatorPass.cursor p)) :=
  binary_bounded_unary a.offset (a.ambient.comp pairFst_mem_FP) (fun _ => offset_le F _ _)

theorem prefix_unary (F : Family) (a : Access F) : UnaryFn (fun p => min (IntegralDenominatorPass.cursor p) (count F (pairFst p))) := by
  have HI : BinaryFn IntegralDenominatorPass.cursor := BinaryFn.fromBits BoundedFold.counter_mem_FP
  have HN : UnaryFn (fun p => count F (pairFst p)) := a.count.comp pairFst_mem_FP
  have HM : BinaryFn (fun p => min (IntegralDenominatorPass.cursor p) (count F (pairFst p))) :=
    (BinaryFn.ite (HI.le (BinaryFn.ofUnary HN)) HI (BinaryFn.ofUnary HN)).of_eq (fun _ => by rw [← min_def])
  exact binary_bounded_unary HM HN (fun _ => min_le_right _ _)

theorem nativeAccess (F : Family) (a : Access F) : IntegralDenominatorPassSpace.Native (program F) where
  count := a.count
  modulus := a.modulus
  arity := (UnaryFn.ite a.critical ((prefix_unary F a).mul ((a.ambient.comp pairFst_mem_FP).add (UnaryFn.const 1))) (UnaryFn.const 0)).of_eq
    (fun p => (descriptor_arity F (pairFst p) (IntegralDenominatorPass.cursor p)).symm)
  degree := (BinaryFn.ite a.critical (a.degree.comp pairFst_mem_FP) (BinaryFn.const 1)).of_eq
    (fun p => (descriptor_degree F (pairFst p) (IntegralDenominatorPass.cursor p)).symm)
  exponent := by
    have HF : UnaryFn (fun p => F.ambient (pairFst p) - offset F (pairFst p) (IntegralDenominatorPass.cursor p) + 1) :=
      ((a.ambient.comp pairFst_mem_FP).sub (offset_unary F a)).add (UnaryFn.const 1)
    have HD : BinaryFn (fun p => (F.spatial (pairFst p)).degree) := a.degree.comp pairFst_mem_FP
    have HE := ((PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary HF) HD).add (BinaryFn.const 1)).mul
      (PurePowerReductionBounds.dimension_binary HF HD)
    exact (BinaryFn.ite a.critical HE (BinaryFn.const 1)).of_eq
      (fun p => (descriptor_exponent F (pairFst p) (IntegralDenominatorPass.cursor p)).symm)
  index := by
    have HA : UnaryFn (fun z => F.ambient (pairFst (pairFst z)) + 1) :=
      ((a.ambient.comp pairFst_mem_FP).comp pairFst_mem_FP).add (UnaryFn.const 1)
    have HJ := BinaryFn.fromBits pairSnd_mem_FP
    exact (BinaryFn.ite (a.critical.comp pairFst_mem_FP) (HJ.div (BinaryFn.ofUnary HA)) (BinaryFn.const 0)).of_eq
      (fun z => (descriptor_index F (pairFst (pairFst z)) (IntegralDenominatorPass.cursor (pairFst z)) (Nat.fromBitsLE (pairSnd z))).symm)

theorem scale_packet (F : Family) (p : List Bool) (j : ℕ) :
    scaleReader F (pair p (BinaryNatCode.encode j)) = residueBits (scaleAt F p j) := by
  unfold scaleReader
  rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def scaleProductReader (F : Family) (p : List Bool) : List Bool :=
  residueBits (scaleProduct F (pairFst p) (IntegralDenominatorPass.cursor p) : ZMod (F.modulus (pairFst p)))

theorem scaleProduct_evaluator (F : Family) (a : Access F) : SpaceFunction (scaleProductReader F) := by
  have HA : UnaryFn (fun p => F.ambient (pairFst p) + 1) := (a.ambient.comp pairFst_mem_FP).add (UnaryFn.const 1)
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  have E := ModularProduct.evaluatorWithModulus a.scales
    (fun p => BinaryNatCode.encode (F.ambient (pairFst p) + 1)) (fun p => BinaryNatCode.encode (F.modulus (pairFst p)))
    (BinaryFn.ofUnary HA).bits_mem_FP HM.bits_mem_FP (fun p => F.modulus (pairFst p))
    (funext fun _ => Nat.fromBitsLE_bits _) (scaleAt F)
    (fun p => Nat.pos_of_ne_zero (F.modulus_ne_zero (pairFst p))) (fun p j _ => scale_packet F p j)
  refine E.congr (funext fun p => ?_)
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold scaleProductReader scaleProduct
  rw [Int.cast_prod]
  rfl

theorem leading_evaluator (F : Family) (a : Access F) : SpaceFunction (fun p => residueBits
    ((descriptorAt F (pairFst p) (IntegralDenominatorPass.cursor p)).leading : ZMod (F.modulus (pairFst p)))) := by
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := a.modulus.comp pairFst_mem_FP
  have HD : BinaryFn (fun p => (F.spatial (pairFst p)).degree) := a.degree.comp pairFst_mem_FP
  have ES : SpaceFunction (fun p => residueBits ((F.spatial (pairFst p)).leading : ZMod (F.modulus (pairFst p)))) :=
    a.spatialLeading.precompose pairFst pairFst_mem_FP
  have EP := ModularScalarSpace.pow HM (fun p => F.modulus_ne_zero (pairFst p)) _ HD _ (scaleProduct_evaluator F a)
  have EC := ModularScalarSpace.mul HM _ _ ES EP
  have E := SpaceFunction.branch (fun p => decide (critical F (pairFst p) (IntegralDenominatorPass.cursor p))) a.critical.flag_mem_FP EC a.integerLeading
  refine E.congr (funext fun p => ?_)
  rw [descriptor_leading]
  by_cases h : critical F (pairFst p) (IntegralDenominatorPass.cursor p)
  · simp only [h, decide_true, ite_true, Int.cast_mul, Int.cast_pow]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, integerLeadingReader]

theorem access (F : Family) (a : Access F) : IntegralDenominatorPassSpace.Access (program F) where
  toNative := nativeAccess F a
  leading := leading_evaluator F a

theorem denominator_evaluator (F : Family) (a : Access F) (index : List Bool → ℕ) (hi : BinaryFn index) :
    SpaceFunction (fun c => residueBits (((denominators (F.spatial c) [] (F.rules c))[index c]?).getD 0 : ZMod (F.modulus c))) := by
  have E := IntegralDenominatorPassSpace.integer_reader_evaluator (program F) (access F a) index hi
  refine E.congr (funext fun c => ?_)
  rw [show (program F).count c = count F c from rfl, integers_full]
end LeanCanny.Algebra.IntegralMixedDenominatorScriptBits

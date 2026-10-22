/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableLeafPath
public import LeanCanny.Algebra.SymbolicCoordinatePathSpace
public import LeanCanny.ETR.CoercivePreparationControls
public import LeanCanny.ETR.CoerciveCoordinateEncoding

/-! # Actual prepared coordinate paths with native envelope controls -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveCoordinatePathSource
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation
open CoerciveSourceSampling CoercivePreparationControls
open SymbolicFixedTable SymbolicScaledSquarefree
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix
set_option allowUnsafeReducibility true in
attribute [local reducible] CoercivePreparationControls.family

noncomputable def depth (c : List Bool) : ℕ := (dimension (pairFst c) + 1).size
noncomputable def leaf (c : List Bool) : ℕ := min (Nat.fromBitsLE (pairSnd c)) (dimension (pairFst c))
noncomputable def stage (c : List Bool) (s : ℕ) : ℕ := min s (depth c - 1)
noncomputable def base (c : List Bool) : ℕ := (family (pairFst c)).fixedBase ^ 16
noncomputable def exponent (c : List Bool) (s : ℕ) : ℕ := base c ^ (16 ^ stage c s)

noncomputable def inner (c : List Bool) (s : ℕ) : SymbolicBalancedCoordinate.Coordinate :=
  leafStep (fun j => SymbolicScaledSquarefree.polynomial ((family (pairFst c)).padded j))
    (family (pairFst c)).directions (leaf c) (stage c s)

theorem depth_pos (c : List Bool) : 0 < depth c := by
  have h := Nat.lt_size_self (dimension (pairFst c) + 1)
  by_contra hz
  have he : depth c = 0 := by omega
  change dimension (pairFst c) + 1 < 2 ^ depth c at h
  rw [he, pow_zero] at h
  omega

theorem stage_lt (c : List Bool) (s : ℕ) : stage c s < depth c := by
  have h := Nat.min_le_right s (depth c - 1)
  have := depth_pos c
  unfold stage
  omega

theorem exponent_le (c : List Bool) (s : ℕ) : exponent c s ≤ referenceExponent (pairFst c) := by
  have hs := stage_lt c s
  have hbase : 1 ≤ base c := ((family (pairFst c)).fixedBase_four.trans
    (family (pairFst c)).fixedBase_le_pow).trans' (by decide)
  have h := Nat.pow_le_pow_right hbase
    (Nat.pow_le_pow_right (by decide : 1 ≤ 16) hs.le)
  exact h.trans (family (pairFst c)).fixedEnvelope_le

noncomputable def source : SymbolicCoordinatePathBits.Source where
  inner := inner
  exponent := exponent
  depth := depth
  cap c := referenceExponent (pairFst c)
  innerBound c := referenceExponent (pairFst c)
  exponent_le := exponent_le
  numeratorInner c s := ((family (pairFst c)).leafStep_bounds (leaf c) (stage c s) (stage_lt c s)).numeratorInner
  denominatorInner c s := ((family (pairFst c)).leafStep_bounds (leaf c) (stage c s) (stage_lt c s)).denominatorInner

theorem path_congr (e f : ℕ → ℕ) (a b : ℕ → SymbolicBalancedCoordinate.Coordinate) (k : ℕ)
    (he : ∀ s < k, e s = f s) (ha : ∀ s < k, a s = b s) :
    SymbolicCoordinatePath.path e a k = SymbolicCoordinatePath.path f b k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [SymbolicCoordinatePath.path, SymbolicCoordinatePath.path,
      ih (fun s hs => he s (by omega)) (fun s hs => ha s (by omega)), he k (by omega), ha k (by omega)]

theorem coordinate_eq (bits : List Bool) (i : Fin (dimension bits + 1)) :
    source.coordinate (pair bits (BinaryNatCode.encode i.val)) = (family bits).fixedCoordinate i := by
  let c := pair bits (BinaryNatCode.encode i.val)
  have hc : pairFst c = bits := pairFst_pair _ _
  have hl : leaf c = i.val := by
    simp only [leaf, c, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.min_eq_left (by omega)
  have hd : depth c = (dimension bits + 1).size := by unfold depth; rw [hc]
  have hstage (s : ℕ) (hs : s < (dimension bits + 1).size) : stage c s = s := by
    unfold stage
    apply Nat.min_eq_left
    rw [hd]
    omega
  change SymbolicCoordinatePath.path (exponent c) (inner c) (depth c) = _
  rw [hd, (family bits).fixedCoordinate_eq_path]
  apply path_congr
  · intro s hs
    change base c ^ (16 ^ stage c s) = _
    rw [hstage s hs]
    simp only [base, hc]
  · intro s hs
    simp only [inner, hc, hl, hstage s hs]

theorem depth_unary : UnaryFn depth := ((dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1)).size

theorem base_binary : BinaryFn base := by
  have hd : BinaryFn (fun c => CoerciveNativeAnnihilators.degreeBound (pairFst c)) := CoerciveNativeAnnihilators.degreeBound_binary.comp pairFst_mem_FP
  have hb : BinaryFn (fun c => CoerciveNativeAnnihilators.massExponent (pairFst c)) := CoerciveNativeAnnihilators.massExponent_binary.comp pairFst_mem_FP
  have h := ((((hd.add (BinaryFn.const 1)).add hd).add hb).add (BinaryFn.const 4)).powUnary (UnaryFn.const 16)
  apply BinaryFn.of_bits
  apply mem_FP_of_eq h.bits_mem_FP
  intro c
  rfl

theorem indexedStage_unary : UnaryFn (fun p => stage (pairFst p) (Nat.fromBitsLE (pairSnd p))) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP ((depth_unary.comp pairFst_mem_FP).sub (UnaryFn.const 1))

theorem indexedPower_unary : UnaryFn (fun p => 16 ^ stage (pairFst p) (Nat.fromBitsLE (pairSnd p))) := by
  have h := (BinaryFn.const 16).powUnary indexedStage_unary
  have hb := (UnaryFn.const 256).mul
    (((dimension_unary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 2)).pow_const 4)
  have H := UnaryFn.fromBitsLE_min h.bits_mem_FP hb
  apply H.of_eq
  intro p
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  apply Nat.min_eq_left
  have hs := stage_lt (pairFst p) (Nat.fromBitsLE (pairSnd p))
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 16) (show stage (pairFst p) (Nat.fromBitsLE (pairSnd p)) ≤
    (dimension (pairFst (pairFst p)) + 1).size + 1 by exact hs.le.trans (Nat.le_succ _))).trans
      (FiniteAnnihilatorTree.heightExponent_le (dimension (pairFst (pairFst p)) + 1))

theorem indexedExponent_binary : BinaryFn (SymbolicCoordinatePathBits.indexedExponent source) := by
  have hb : BinaryFn (fun p => base (pairFst p)) := base_binary.comp pairFst_mem_FP
  exact hb.powUnary indexedPower_unary

theorem cap_binary : BinaryFn source.cap := referenceExponent_binary.comp pairFst_mem_FP

theorem source_depth_binary : BinaryFn source.depth := BinaryFn.of_bits (bits_mem_FP depth_unary)
theorem innerBound_binary : BinaryFn source.innerBound := referenceExponent_binary.comp pairFst_mem_FP

def pathQuery (p : List Bool) : List Bool :=
  pair (pair (pair (pairFst (pairFst p)) (pairFst (pairSnd (pairFst p)))) (pairSnd p))
    (pair (pairSnd (pairSnd (pairSnd (pairFst p)))) (pairFst (pairSnd (pairSnd (pairFst p)))))

theorem pathQuery_FP : pathQuery ∈ FP := by
  have hctx := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hp := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hi := mem_FP_comp hp pairFst_mem_FP
  have hd := mem_FP_comp hp pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair (mem_FP_pair hctx hi) pairSnd_mem_FP)
    (mem_FP_pair (mem_FP_comp hd pairSnd_mem_FP) (mem_FP_comp hd pairFst_mem_FP))
  exact mem_FP_of_eq h (fun _ => rfl)

noncomputable def pathCoefficient (numerator : Bool) : List Bool → List Bool :=
  SymbolicFixedTableEntryBits.coefficient (source.component numerator) ∘ pathQuery

noncomputable def readers
    (N : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicCoordinatePathBits.indexedNumerator source)))
    (D : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (SymbolicCoordinatePathBits.indexedDenominator source))) :
    CoerciveCoordinateEncoding.Readers where
  numerator := pathCoefficient true
  denominator := pathCoefficient false
  numerator_space := (SymbolicCoordinatePathBits.coefficientEvaluator source true cap_binary source_depth_binary
    innerBound_binary indexedExponent_binary N D).precompose pathQuery pathQuery_FP
  denominator_space := (SymbolicCoordinatePathBits.coefficientEvaluator source false cap_binary source_depth_binary
    innerBound_binary indexedExponent_binary N D).precompose pathQuery pathQuery_FP
  numerator_eq bits i j k m hm := by
    simp only [pathCoefficient, Function.comp_apply, pathQuery, SymbolicFixedTableEntryBits.coefficient,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Nat.sub_add_cancel (show 1 ≤ m by omega), SymbolicCoordinatePathBits.Source.component,
      ite_true]
    have he := coordinate_eq bits i
    simp only [BinaryNatCode.encode] at he
    rw [he]
    rfl
  denominator_eq bits i j k m hm := by
    simp only [pathCoefficient, Function.comp_apply, pathQuery, SymbolicFixedTableEntryBits.coefficient,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Nat.sub_add_cancel (show 1 ≤ m by omega), SymbolicCoordinatePathBits.Source.component, Bool.false_eq_true,
      ite_false]
    have he := coordinate_eq bits i
    simp only [BinaryNatCode.encode] at he
    rw [he]
    rfl

end LeanCanny.ETR.CoerciveCoordinatePathSource

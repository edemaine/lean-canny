/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeIndex
/-! # Native powers of the actual leading matrix

The exponent is the target field. Matrix children retain the immutable source
key and request phase-zero entries at the same caller modulus.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem matrixDimension_pos (P : Parameters) (F : Family) (q : List Bool) : 0 < matrixDimension P F q :=
  pow_pos (Nat.two_pow_pos _) _

noncomputable def topPowerFamily (P : Parameters) (F : Family) : MatrixPower.ModularFamily where
  dimension := matrixDimension P F
  modulus := modulus P
  exponent := get P .target
  row q := ⟨get P .row q % matrixDimension P F q, Nat.mod_lt _ (matrixDimension_pos P F q)⟩
  col q := ⟨get P .col q % matrixDimension P F q, Nat.mod_lt _ (matrixDimension_pos P F q)⟩
  matrix q i j := (top F (IntegralMixedVirtualTaskBits.saved P q) i j : ZMod (modulus P q))
  modulus_ne_zero := modulus_ne_zero P

noncomputable def topPowerEntry (P : Parameters) (F : Family) (z : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    (top F (IntegralMixedVirtualTaskBits.saved P (pairFst z)))
    (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex z)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex z)) :
      ZMod (modulus P (pairFst z)))

noncomputable def topPowerAccess (P : Parameters) (F : Family) : ModularAccess (topPowerFamily P F) where
  dimension q := BinaryNatCode.encode (matrixDimension P F q)
  modulus q := BinaryNatCode.encode (modulus P q)
  exponent q := BinaryNatCode.encode (get P .target q)
  row q := BinaryNatCode.encode (get P .row q % matrixDimension P F q)
  col q := BinaryNatCode.encode (get P .col q % matrixDimension P F q)
  entry := topPowerEntry P F
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq q i j := by
    let z := pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    have HP : pairFst z = q := pairFst_pair _ _
    have HI : MatrixMoment.EntryBits.rowIndex z = BinaryNatCode.encode i.val := by
      simp only [z, MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair]
    have HJ : MatrixMoment.EntryBits.colIndex z = BinaryNatCode.encode j.val := by
      simp only [z, MatrixMoment.EntryBits.colIndex, pairSnd_pair]
    change topPowerEntry P F z = _
    unfold topPowerEntry
    rw [HP, HI, HJ]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [IntegralCriticalTotalSnapshotBits.integerEntry_fin]
    rfl

theorem topPower_controls (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (topPowerAccess P F).ControlsPolyTime where
  dimension := (matrixDimension_binary P a F h).bits_mem_FP
  modulus := (modulus_binary P a).bits_mem_FP
  exponent := (get_binary P a .target).bits_mem_FP
  row := ((get_binary P a .row).mod (matrixDimension_binary P a F h)).bits_mem_FP
  col := ((get_binary P a .col).mod (matrixDimension_binary P a F h)).bits_mem_FP

noncomputable def topPowerValue (P : Parameters) (F : Family) := (topPowerFamily P F).value

theorem topPowerValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = topPowerValue P F q := ⟨_, rfl⟩

abbrev TopPowerRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin ((topPowerFamily P F).dimension q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((topPowerFamily P F).matrix q i j)

theorem topPower_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : TopMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    TopPowerRepliesAt P F answer q := by
  intro i j
  let c := IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 := by
    simpa only [c, IntegralMixedMatrixFrames.matrix_routine, pairFst_pair] using hr
  exact (hx c HV HR (IntegralCriticalFlatMatrixQuery.writer_phase P .originalCoefficient _)).trans
    (child_value P F g .originalCoefficient q hv i j)

noncomputable def stage1 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := ModularRecursiveStage.stage (topPowerAccess P F) (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient)
  certificates := ModularRecursiveStage.certificates (topPowerAccess P F) (topPower_controls P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient) (IntegralCriticalFlatMatrixQuery.writer_FP P a .originalCoefficient)
  selected := selected P .derivativeCoefficient
  selected_FP := selected_FP P a .derivativeCoefficient
  model := topPowerValue P F
  clock := ModularRecursiveStage.clock (topPowerFamily P F)
  clock_binary := ModularRecursiveStage.clock_binary (topPowerAccess P F) (topPower_controls P a F h)
  stateBound := ModularRecursiveStage.stateBound (topPowerFamily P F)
  stateBound_unary := ModularRecursiveStage.stateBound_unary (topPowerAccess P F) (topPower_controls P a F h)

attribute [local irreducible] topPowerFamily topPowerAccess

theorem correct1 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : TopMatches P F answer) :
    Correct (stage1 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H := (selected_iff P .derivativeCoefficient q).mp hq
    exact ModularRecursiveStage.halted_after_local (topPowerAccess P F) (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient) answer q (topPower_replies P F g answer hx q H.1 H.2.1)
  · intro q t hq hh
    have H := (selected_iff P .derivativeCoefficient q).mp hq
    exact ModularRecursiveStage.output_when_halted_local (topPowerAccess P F) (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient) answer q (topPower_replies P F g answer hx q H.1 H.2.1) t hh
  · intro q t hq
    have H := (selected_iff P .derivativeCoefficient q).mp hq
    simpa only [stage1, encBits_apply] using ModularRecursiveStage.state_length_local
      (topPowerAccess P F) (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient) answer q (topPower_replies P F g answer hx q H.1 H.2.1) t
  · intro q c budget hq hc
    have H := (selected_iff P .derivativeCoefficient q).mp hq
    obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
      (topPowerAccess P F) (IntegralCriticalFlatMatrixQuery.writer P .originalCoefficient) answer q (topPower_replies P F g answer hx q H.1 H.2.1) budget c hc
    have HP := H.2.2
    change phase q = 1 at HP
    have HF := IntegralMixedMatrixFrames.matrix_frame P .originalCoefficient
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (by simp only [pairFst_pair]; change 0 < phase q; omega)
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

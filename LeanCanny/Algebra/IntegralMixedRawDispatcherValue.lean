/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawDispatcher
/-! # The joined raw model is the literal truncated source for every actual cut kind -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem raw_zero_degree (P : Parameters) (F : Family) (q : List Bool)
    (hd : ¬get P .coefficient q ≤ F.degree (IntegralMixedVirtualTaskBits.saved P q)) :
    IntegralMixedNormalizationTopBits.rawCutValue P F q = [] := by
  unfold IntegralMixedNormalizationTopBits.rawCutValue
  rw [source_coefficient, ite_eq_right hd]
  simp only [IntegralCriticalTotalSnapshotBits.integerEntry, Matrix.zero_apply, dite_eq_ite, ite_self,
    Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem model_raw (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 4)
    (hp : isPhase .companion q) (hx : IntegralMixedVirtualContextBits.context P q) :
    (machine P a F h k hd).model q = IntegralMixedNormalizationTopBits.rawCutValue P F q := by
  rw [machine_model]
  by_cases hdeg : get P .coefficient q ≤ F.degree (IntegralMixedVirtualTaskBits.saved P q)
  · have HC : IntegralMixedPreparedCoordinateNative.Selected P F q ∨ IntegralMixedPreparedSquarefreeNative.Selected P F q ∨
        IntegralMixedPreparedValueNative.Selected P F q := by
      have HT := IntegralMixedRawKindBits.tag_bounds F (IntegralMixedVirtualTaskBits.saved P q)
      by_cases h2 : IntegralMixedRawKindBits.tag F (IntegralMixedVirtualTaskBits.saved P q) = 2
      · exact Or.inl ⟨hv,hr,hp,hx,h2,hdeg⟩
      · by_cases h3 : IntegralMixedRawKindBits.tag F (IntegralMixedVirtualTaskBits.saved P q) = 3
        · exact Or.inr (Or.inl ⟨hv,hr,hp,hx,h3,hdeg⟩)
        · exact Or.inr (Or.inr ⟨hv,hr,hp,hx,by omega,hdeg⟩)
    change (if IntegralMixedPreparedCoordinateNative.Selected P F q then IntegralMixedNormalizationTopBits.rawCutValue P F q else
      if IntegralMixedPreparedSquarefreeNative.Selected P F q then IntegralMixedNormalizationTopBits.rawCutValue P F q else
      if IntegralMixedPreparedValueNative.Selected P F q then IntegralMixedNormalizationTopBits.rawCutValue P F q else _) = _
    by_cases hC : IntegralMixedPreparedCoordinateNative.Selected P F q
    · rw [ite_eq_left hC]
    · rw [ite_eq_right hC]
      by_cases hS : IntegralMixedPreparedSquarefreeNative.Selected P F q
      · rw [ite_eq_left hS]
      · rw [ite_eq_right hS]
        have hV : IntegralMixedPreparedValueNative.Selected P F q := by rcases HC with H | H | H; contradiction; contradiction; exact H
        rw [ite_eq_left hV]
  · have HC : ¬IntegralMixedPreparedCoordinateNative.Selected P F q := fun H => hdeg H.2.2.2.2.2
    have HS : ¬IntegralMixedPreparedSquarefreeNative.Selected P F q := fun H => hdeg H.2.2.2.2.2
    have HV : ¬IntegralMixedPreparedValueNative.Selected P F q := fun H => hdeg H.2.2.2.2.2
    have HF : ¬IntegralMixedValueFactorScopedBits.Selected P F q := by intro H; have HP := H.1.2.2.1; change phase q = 25 at HP; change phase q = 26 at hp; omega
    have HG : ¬IntegralMixedSquarefreeFactorBits.Selected P F q := by intro H; have HP := H.2.2.1; change phase q = 24 at HP; change phase q = 26 at hp; omega
    rw [raw_zero_degree P F q hdeg]
    change (if IntegralMixedPreparedCoordinateNative.Selected P F q then _ else
      if IntegralMixedPreparedSquarefreeNative.Selected P F q then _ else
      if IntegralMixedPreparedValueNative.Selected P F q then _ else
      if IntegralMixedValueFactorScopedBits.Selected P F q then _ else
      if IntegralMixedSquarefreeFactorBits.Selected P F q then _ else []) = []
    rw [ite_eq_right HC, ite_eq_right HS,
      ite_eq_right HV, ite_eq_right HF,
      ite_eq_right HG]

end LeanCanny.Algebra.IntegralMixedRawDispatcherBits

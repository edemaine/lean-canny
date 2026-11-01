/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeLowerCoefficient
/-! # Native final coefficients of the actual normalized relative cut -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def top14 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected14Matrix P F q && decide (get P .coefficient q = F.degree (IntegralMixedVirtualTaskBits.saved P q) ∧ get P .row q = get P .col q)

noncomputable def low14 (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected14Matrix P F q && decide (get P .coefficient q < F.degree (IntegralMixedVirtualTaskBits.saved P q))

theorem top14_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : (fun q => [top14 P F q]) ∈ FP := by
  have HD : BinaryFn (fun q => F.degree (IntegralMixedVirtualTaskBits.saved P q)) := hd.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact mem_FP_of_eq ((FPPred.of_flag (selected14Matrix_FP P a F h)).and
    (((get_binary P a .coefficient).eq HD).and ((get_binary P a .row).eq (get_binary P a .col)))).flag_mem_FP
    (fun q => by cases hb : selected14Matrix P F q <;> simp [top14, hb])

theorem low14_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : (fun q => [low14 P F q]) ∈ FP := by
  have HD : BinaryFn (fun q => F.degree (IntegralMixedVirtualTaskBits.saved P q)) := hd.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact mem_FP_of_eq ((FPPred.of_flag (selected14Matrix_FP P a F h)).and
    ((get_binary P a .coefficient).lt HD)).flag_mem_FP
    (fun q => by cases hb : selected14Matrix P F q <;> simp [low14, hb])

theorem top14_iff (P : Parameters) (F : Family) (q : List Bool) : top14 P F q = true ↔
    selected14Matrix P F q = true ∧ get P .coefficient q = F.degree (IntegralMixedVirtualTaskBits.saved P q) ∧ get P .row q = get P .col q := by
  simp only [top14, Bool.and_eq_true, decide_eq_true_eq]

theorem low14_iff (P : Parameters) (F : Family) (q : List Bool) : low14 P F q = true ↔
    selected14Matrix P F q = true ∧ get P .coefficient q < F.degree (IntegralMixedVirtualTaskBits.saved P q) := by
  simp only [low14, Bool.and_eq_true, decide_eq_true_eq]

noncomputable def stage14 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : Machine :=
  ((leadingStage P a F h).withGuard (top14 P F) (top14_FP P a F h hd)).choose
    (((lowerCoefficientStage P a F h).withGuard (low14 P F) (low14_FP P a F h hd)).choose zero)

theorem correct14 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hi : IndexMatches P F (fun q => residueBits (x q)))
    (hc : CharacteristicMatches P F (fun q => residueBits (x q)))
    (hp : ProductMatches P F (fun q => residueBits (x q))) :
    Correct (stage14 P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold stage14
  apply choose_correct
  · apply withGuard_correct
    · exact leading_correct P a F h g x hi hc
    · intro q hq
      change selected P .eulerSum q = true
      exact (selected_iff P .eulerSum q).mpr ((selected14Matrix_iff P F q).mp ((top14_iff P F q).mp hq).1).1
  · apply choose_correct
    · apply withGuard_correct
      · exact lowerCoefficient_correct P a F h x hp
      · intro q hq
        change selected14Matrix P F q = true
        exact ((low14_iff P F q).mp hq).1
    · exact zero_correct _ _

attribute [local irreducible] top14 low14 leadingValue productValue normalizedValue

private theorem chooseModel (M N : Machine) (q : List Bool) :
    (M.choose N).model q = if M.selected q then M.model q else N.model q := rfl

theorem stage14_selected (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (stage14 P a F h hd).selected q = true := by
  change (top14 P F q || (low14 P F q || true)) = true
  simp only [Bool.or_true]

theorem stage14_model (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (stage14 P a F h hd).model q = if top14 P F q then leadingValue P F q else if low14 P F q then productValue P F q else [] := by
  unfold stage14
  rw [chooseModel, chooseModel]
  rfl


theorem stage14_model_valid (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) (hp : isPhase .eulerSum q) :
    (stage14 P a F h hd).model q = normalizedValue P F q := by
  rw [stage14_model]
  by_cases HA : matrixAxes P F q
  · have HM : selected14Matrix P F q = true := (selected14Matrix_iff P F q).mpr ⟨⟨hv, hr, hp⟩, HA⟩
    by_cases HK : get P .coefficient q = F.degree (IntegralMixedVirtualTaskBits.saved P q)
    · rw [normalizedValue_top P F q HA HK]
      by_cases HE : get P .row q = get P .col q <;> simp [top14, low14, HM, HK, HE]
    · by_cases HL : get P .coefficient q < F.degree (IntegralMixedVirtualTaskBits.saved P q)
      · rw [normalizedValue_low P F q HL]
        simp only [top14, low14, HM, HK, HL, false_and, decide_false, decide_true, Bool.true_and,
          Bool.false_eq_true, ite_false, ite_true]
      · have HD : F.degree (IntegralMixedVirtualTaskBits.saved P q) < get P .coefficient q := by omega
        rw [normalizedValue_above P F q HD]
        simp only [top14, low14, HM, HK, HL, false_and, decide_false, Bool.true_and,
          Bool.false_eq_true, ite_false]
  · have HM : selected14Matrix P F q = false := by
      unfold selected14Matrix
      rw [show decide (matrixAxes P F q) = false from decide_eq_false HA]
      simp only [Bool.and_false]
    rw [normalizedValue_outside P F q HA]
    simp only [top14, low14, HM, Bool.false_and, Bool.false_eq_true, ite_false]

theorem stage14_canonical (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (stage14 P a F h hd).model q := by
  rw [stage14_model]
  split_ifs
  · exact leadingValue_canonical P F q
  · exact productValue_canonical P F q
  · exact ⟨0, (ArithmeticBits.zero_residueBits (modulus P q)).symm⟩

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

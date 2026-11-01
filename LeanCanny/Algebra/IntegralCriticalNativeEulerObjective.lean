/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native phase fifteen from the actual frozen lower coefficient and Euler sum -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeEulerObjectiveBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily IntegralCriticalHistoryTask.get
  IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank

noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.euler F
noncomputable def program (F : Scripts) := IntegralEulerBits.ObjectiveStage.program (source F)
  (IntegralCriticalFlatEulerBits.next F.toParameters .frozenLower) (IntegralCriticalFlatEulerBits.next F.toParameters .eulerSum)

noncomputable def machine (F : Scripts) (h : Controls F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (program F).controller
  certificates := IntegralEulerBits.ObjectiveStage.certificates (source F) (eulerAccess F h) _ _
    (IntegralCriticalFlatEulerBits.next_FP F.toParameters h.task.toAccess .frozenLower)
    (IntegralCriticalFlatEulerBits.next_FP F.toParameters h.task.toAccess .eulerSum)
  selected := selected F .eulerObjective
  selected_FP := selected_FP F h .eulerObjective
  model := IntegralCriticalActualScalarModels.objective F
  clock := fun _ => 2
  clock_binary := BinaryFn.const 2
  stateBound := IntegralCriticalFlatFrozenLowerBits.stateBound (source F).toGradient.toFrozen
  stateBound_unary := IntegralCriticalFlatFrozenLowerBits.stateBound_unary (source F).toGradient.toFrozen (eulerAccess F h).toGradient.toFrozen

theorem lower_reply (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    answer F x (IntegralCriticalFlatEulerBits.next F.toParameters .frozenLower q) = (source F).toGradient.toFrozen.lowerValue q :=
  (matches_next F x hm .frozenLower (by decide) q hv).trans (IntegralCriticalActualScalarModels.objective_lower_child F q)

theorem sum_reply (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    answer F x (IntegralCriticalFlatEulerBits.next F.toParameters .eulerSum q) = (source F).sumValue q :=
  (matches_next F x hm .eulerSum (by decide) q hv).trans (IntegralCriticalActualScalarModels.objective_sum_child F q)

theorem post_value (S : IntegralEulerBits.Source) (q : List Bool) :
    IntegralEulerBits.ObjectiveStage.post S (pair q (pair (S.toGradient.toFrozen.lowerValue q) (S.sumValue q))) = S.objectiveValue q := by
  unfold IntegralEulerBits.ObjectiveStage.post
  simp only [pairFst_pair, pairSnd_pair]
  exact IntegralEulerBits.objective_value S q

theorem value_local (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F).value (answer F x) q = (source F).objectiveValue q := by
  change (TwoCall.program _ _ (IntegralEulerBits.ObjectiveStage.post (source F))).value (answer F x) q = _
  rw [TwoCall.value_eq, lower_reply F x hm q hv, sum_reply F x hm q hv, post_value]

theorem state_local (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) (t : ℕ) :
    (RecursiveFold.encState (((program F).controller.reference (answer F x))^[t] ((program F).initial q))).length ≤
      IntegralCriticalFlatFrozenLowerBits.stateBound (source F).toGradient.toFrozen q := by
  let : NeZero ((source F).modulus q) := ⟨(source F).modulus_ne_zero q⟩
  have HB (z : ZMod ((source F).modulus q)) : (residueBits z).length ≤ ((source F).modulus q).size := residueBits_length_le _ _
  have HL : ((source F).toGradient.toFrozen.lowerValue q).length ≤ ((source F).modulus q).size := by
    unfold IntegralFrozenPowerBits.Source.lowerValue
    exact HB _
  have HO : ((source F).objectiveValue q).length ≤ ((source F).modulus q).size := by
    unfold IntegralEulerBits.Source.objectiveValue
    exact HB _
  have H := TwoCall.state_length (IntegralCriticalFlatEulerBits.next F.toParameters .frozenLower)
    (IntegralCriticalFlatEulerBits.next F.toParameters .eulerSum) (IntegralEulerBits.ObjectiveStage.post (source F)) (answer F x) q t
  rw [lower_reply F x hm q hv, sum_reply F x hm q hv, post_value] at H
  change _ ≤ 2 * q.length + 2 * (2 : ℕ).size + ((source F).modulus q).size + 2
  have HE : (encNat 2).length = (2 : ℕ).size := by simp [encNat_apply, Nat.size_eq_bits_len]
  rw [HE] at H
  exact H.trans (by omega)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (machine F h) (answer F x) (Frame F) := by
  constructor
  · intro q _
    exact (program F).halted_after (answer F x) q
  · intro q t hq hh
    exact ((program F).output_when_halted (answer F x) q t hh).trans
      ((value_local F x hm q ((selected_iff F .eulerObjective q).mp hq).1).trans
        (IntegralCriticalActualScalarModels.objective_eq F q).symm)
  · intro q t hq
    exact state_local F x hm q ((selected_iff F .eulerObjective q).mp hq).1 t
  · intro q c budget hq hc
    have HP := ((selected_iff F .eulerObjective q).mp hq).2
    change phase q = 15 at HP
    have HC := fold_requests_bound (program F) (answer F x) budget q c hc
    rcases (IntegralEulerBits.ObjectiveStage.requests_iff (source F) _ _ (answer F x) q c).mp HC with rfl | rfl
    · exact frame_next F .frozenLower q (by change 12 < phase q; omega)
    · exact frame_next F .eulerSum q (by change 14 < phase q; omega)

end LeanCanny.Algebra.IntegralCriticalNativeEulerObjectiveBits

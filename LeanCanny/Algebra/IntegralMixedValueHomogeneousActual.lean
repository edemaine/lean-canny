/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousPoint

/-! # Total native homogeneous-row correctness with invalid labels preserved -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousActual
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueHomogeneousQueries IntegralMixedValueHomogeneousPoint
open scoped Classical

theorem value_finite (P : Parameters) (F : Family) (g : RootGeometry P F) (reply : List Bool → List Bool)
    (q : List Bool) (s : Fin ((parameters P F).free q + 1))
    (k : Fin (count ((parameters P F).free q + 1) ((parameters P F).width q)))
    (r t : Fin ((parameters P F).rank q))
    (hs : get P .slot8 q = s.val) (hk : get P .target q = k.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (he : RepliesAt P F reply q) :
    (IntegralMixedValueHomogeneousRequest.program P F).value reply q =
      residueBits (IntegralMixedValueHomogeneousMatrix.entry (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q s k r t : ZMod (modulus P q)) := by
  cases s using Fin.cases with
  | zero => exact value_zero P F g reply q k r t hs hk hr ht he
  | succ j => exact value_succ P F g reply q j k r t hs hk hr ht he

theorem value_at (P : Parameters) (F : Family) (g : RootGeometry P F) (reply : List Bool → List Bool)
    (q : List Bool) (he : RepliesAt P F reply q) :
    (IntegralMixedValueHomogeneousRequest.program P F).value reply q =
      IntegralMixedValueHomogeneousMatrix.value P F q := by
  by_cases HL : IntegralMixedValueHomogeneousMatrix.Labels (IntegralMixedVirtualTaskBits.family P F) q
      (get P .slot8 q) (get P .target q) (get P .row q) (get P .col q)
  · let s : Fin ((parameters P F).free q + 1) := ⟨get P .slot8 q, HL.1⟩
    let k : Fin (count ((parameters P F).free q + 1) ((parameters P F).width q)) := ⟨get P .target q, HL.2.1⟩
    let r : Fin ((parameters P F).rank q) := ⟨get P .row q, HL.2.2.1⟩
    let t : Fin ((parameters P F).rank q) := ⟨get P .col q, HL.2.2.2⟩
    change _ = residueBits (IntegralMixedValueHomogeneousMatrix.totalEntry
      (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F) q
        s.val k.val r.val t.val : ZMod (modulus P q))
    rw [IntegralMixedValueHomogeneousMatrix.total_finite]
    exact value_finite P F g reply q s k r t rfl rfl rfl rfl he
  · have HN : ¬IntegralMixedValueHomogeneousRequest.request P F q := by
      intro H
      exact HL ((IntegralMixedValueHomogeneousMatrix.labels_iff
        (IntegralMixedVirtualTaskBits.family P F) q _ _ _ _).mpr H.1)
    rw [IntegralMixedValueHomogeneousRequest.value_eq, ite_eq_right HN]
    unfold IntegralMixedValueHomogeneousMatrix.value
    rw [IntegralMixedValueHomogeneousMatrix.total_invalid _ _ _ _ _ _ _ HL]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) :
    modulus P (query P F q) = modulus P q := by
  unfold query
  split_ifs
  · exact originalTask_modulus P F q
  · exact coordinateTask_modulus P F q

theorem current_integer (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ℤ, currentValue P F q = residueBits (z : ZMod (modulus P (query P F q))) := by
  unfold currentValue
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, IntegralMixedVirtualTaskBits.value_snapshot P F (query P F q)⟩

theorem current_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = currentValue P F q := by
  obtain ⟨z, HZ⟩ := current_integer P F q
  refine ⟨(z : ZMod (modulus P q)), ?_⟩
  rw [HZ]
  exact (congrArg (fun m : ℕ => residueBits (z : ZMod m)) (query_modulus P F q)).symm

theorem state_length (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (he : RepliesAt P F reply q) :
    (SingleCall.encState (((IntegralMixedValueHomogeneousRequest.program P F).controller.reference reply)^[t]
      (SingleCall.Program.initial q))).length ≤ IntegralMixedValueHomogeneousRequest.stateBound P q := by
  apply IntegralMixedValueHomogeneousRequest.state_length P F reply q t
  intro HR
  obtain ⟨z, HZ⟩ := current_canonical P F q
  exact ⟨z, (he HR).trans HZ.symm⟩

end LeanCanny.Algebra.IntegralMixedValueHomogeneousActual

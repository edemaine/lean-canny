/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscCharacteristicOutput
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Native natural PSC determinant coefficients from actual phase-three factors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical

def Selected4 (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  Domain P F q ∧ isPhase .factorPower q ∧ get P .row q < (characteristic P F).rank q ∧ get P .col q < (characteristic P F).rank q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected4 P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected4_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : FPPred (Selected4 P F) :=
  (domain_FP P a F h).and ((isPhase_FP .factorPower).and
    (((get_binary P a .row).lt (characteristicAccess P a F h).rank).and ((get_binary P a .col).lt (characteristicAccess P a F h).rank)))

abbrev FactorMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, selected P F .monomialFactor q = true → answer q = factorValue P F q

abbrev FactorRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i j : Fin (IntegralBerkowitzBlockBits.powerDimension (characteristic P F) q),
    answer (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod ((characteristic P F).modulus q))

theorem factor_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : FactorMatches P F answer) (q : List Bool) (hq : Domain P F q) : FactorRepliesAt P F answer q := by
  intro i j
  let z := pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have HD : Domain P F (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor z) :=
    matrixWriter_domain P F .monomialFactor z (by simpa only [z, pairFst_pair] using hq)
  have HS : selected P F .monomialFactor (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor z) = true :=
    (selected_iff P F .monomialFactor _).mpr ⟨HD, IntegralCriticalFlatMatrixQuery.writer_phase P .monomialFactor z⟩
  exact (hx _ HS).trans ((factor_child P F g .monomialFactor q hq.1 i j).trans
    (congrArg (fun m : ℕ => residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod m))
      (characteristic_modulus P F q).symm))

noncomputable def stage4 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralBerkowitzBlockBits.RecursiveStage.controller (characteristic P F) (characteristicAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor)
  certificates := IntegralBerkowitzBlockBits.RecursiveStage.certificates (characteristic P F) (characteristicAccess P a F h)
    (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) (IntegralCriticalFlatMatrixQuery.writer_FP P a .monomialFactor)
  selected q := decide (Selected4 P F q)
  selected_FP := (selected4_FP P a F h).flag_mem_FP
  model := characteristicValue P F
  clock := ModularRecursiveStage.clock (IntegralBerkowitzBlockBits.powerFamily (characteristic P F))
  clock_binary := IntegralBerkowitzBlockBits.RecursiveStage.clock_binary (characteristic P F) (characteristicAccess P a F h)
  stateBound := ModularRecursiveStage.stateBound (IntegralBerkowitzBlockBits.powerFamily (characteristic P F))
  stateBound_unary := IntegralBerkowitzBlockBits.RecursiveStage.stateBound_unary (characteristic P F) (characteristicAccess P a F h)

attribute [local irreducible] IntegralMixedPscCharacteristicBits.source characteristicAccess

theorem correct4 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool) (hx : FactorMatches P F answer) :
    Correct (stage4 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    have H : Selected4 P F q := of_decide_eq_true hq
    exact IntegralBerkowitzBlockBits.RecursiveStage.halted_after_local (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q (factor_replies P F g answer hx q H.1)
  · intro q t hq hh
    have H : Selected4 P F q := of_decide_eq_true hq
    exact (IntegralBerkowitzBlockBits.RecursiveStage.output_when_halted_local (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q (factor_replies P F g answer hx q H.1) t hh).trans
      (characteristic_value_finite P F q H.2.2.1 H.2.2.2)
  · intro q t hq
    have H : Selected4 P F q := of_decide_eq_true hq
    change (((IntegralBerkowitzBlockBits.RecursiveStage.controller (characteristic P F) (characteristicAccess P a F h)
      (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor)).reference answer)^[t]
      ((IntegralBerkowitzBlockBits.RecursiveStage.controller (characteristic P F) (characteristicAccess P a F h)
        (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor)).initial q)).length ≤ _
    exact IntegralBerkowitzBlockBits.RecursiveStage.state_length_local
      (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q
      (factor_replies P F g answer hx q H.1) t

  · intro q c budget hq hc
    have H : Selected4 P F q := of_decide_eq_true hq
    obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds_local
      (characteristic P F) (characteristicAccess P a F h) (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor) answer q
      (factor_replies P F g answer hx q H.1) budget c hc
    have HP := H.2.1
    change phase q = 4 at HP
    have HF := IntegralMixedMatrixFrames.matrix_frame P .monomialFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (by simp only [pairFst_pair]; change 3 < phase q; omega)
    simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedPscUpperBits

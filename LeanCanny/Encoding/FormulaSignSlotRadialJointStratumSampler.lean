/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumNative
public import LeanCanny.Encoding.ImplicitSourceComponentSampler
/-! # Bounded native samples of the actual implicit joint stratum

The source uses the original binary feature product and one final witness
variable. Every component has an accepted own grid word. Acceptance checks
the actual Core and exact-zero-count certificate at that decoded point.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointStratum.source

theorem positive (u : List Bool) : 0 < (S).arity u := Nat.zero_lt_succ _

noncomputable abbrev input := ImplicitSourceGramGrid.input S positive
noncomputable abbrev language : Language := ImplicitSourceComponentSampler.language S positive

theorem mem_PSPACE : language ∈ PSPACE :=
  ImplicitSourceComponentSampler.mem_PSPACE S FormulaSignSlotRadialJointStratumNative.access positive

noncomputable abbrev tableBound := ImplicitSourceGramGridWordBudget.tableBound S
noncomputable abbrev ownwordBound := ImplicitSourceGramGridWordBudget.ownwordBound S
  FormulaSignSlotRadialJointStratumNative.access positive

theorem tableBound_unary : UnaryFn tableBound :=
  ImplicitSourceGramGridWordBudget.tableBound_unary S FormulaSignSlotRadialJointStratumNative.access

theorem ownwordBound_unary : UnaryFn ownwordBound :=
  ImplicitSourceGramGridWordBudget.ownwordBound_unary S FormulaSignSlotRadialJointStratumNative.access positive

theorem accepted_iff (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid input c w) :
    pair c w ∈ language ↔
      (FormulaSignSlotRadialJointCore.equation
        (FormulaSignSlotRadialJointStratum.header (ImplicitSourceGramGrid.header c))).eval
          (LeanCanny.ETR.Formula.extend (FormulaSignSlotRadialJointStratum.oldPoint
            (ImplicitSourceGramGrid.header c) (SquareSampleCompleteVertices.candidate input c w hw).val)) = 0 ∧
        SquareFeatureProduct.Certificate
          (FormulaSignSlotRadialJointStratum.values (ImplicitSourceGramGrid.header c)
            (SquareSampleCompleteVertices.candidate input c w hw).val)
          (FormulaSignSlotRadialJointStratum.selected (ImplicitSourceGramGrid.header c))
          ((SquareSampleCompleteVertices.candidate input c w hw).val
            (Fin.last (FormulaSignSlotRadialJointStratum.oldArity (ImplicitSourceGramGrid.header c)))) := by
  rw [ImplicitSourceComponentSampler.packet S positive c w hw]
  exact FormulaSignSlotRadialJointStratum.zero_iff _ _

theorem component_hit (u : List Bool)
    (x : Zeros (((S).polynomial u).map (Int.castRingHom ℝ))) :
    ∃ Gamma : List Bool, Gamma.length ≤ tableBound u ∧
      ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid input (pair u Gamma) w),
        w.length = SquareSampleCompleteVertices.width input (pair u Gamma) ∧
        w.length ≤ ownwordBound u ∧ pair (pair u Gamma) w ∈ language ∧
        ∃ a : Zeros (((S).polynomial u).map (Int.castRingHom ℝ)),
          JoinedIn (Zeros (((S).polynomial u).map (Int.castRingHom ℝ))) x.val a.val ∧
            HEq (SquareSampleCompleteVertices.candidate input (pair u Gamma) w hw).val a.val :=
  ImplicitSourceComponentSampler.component_hit S FormulaSignSlotRadialJointStratumNative.access positive u x

theorem nonempty_iff (u : List Bool) :
    Nonempty (Zeros (((S).polynomial u).map (Int.castRingHom ℝ))) ↔
      ∃ Gamma : List Bool, Gamma.length ≤ tableBound u ∧
        ∃ w : List Bool, w.length ≤ ownwordBound u ∧ pair (pair u Gamma) w ∈ language :=
  ImplicitSourceComponentSampler.nonempty_iff S FormulaSignSlotRadialJointStratumNative.access positive u

end LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler

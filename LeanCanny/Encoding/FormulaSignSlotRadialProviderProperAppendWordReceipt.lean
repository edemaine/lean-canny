/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWord
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordReceipt
/-! # A fresh complete proper word retains every constructed local and padding readback -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "S" => IntegralFramedPhysicalBankTerm.input B
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank
structure ProperWordData (root : List Bool)
    (canonical actual full : IntegralMixedFramedRunObservation.Data)
    (commands : List (Instruction ((P).ambient root) ((P).width root))) (paddingCount : ℕ)
    (localTuple : ℕ→ℝ) (p0 : Fin ((P).ambient root+1)→ℝ) where
  tuple :ℕ→ℝ
  sample : FormulaSignSlotRadialProviderRetainedAppend.BankWord B (pair root []) tuple
  canonical_roots :canonical.Roots localTuple
  local_roots :actual.Roots localTuple
  roots :full.Roots tuple
  preserved :∀i,i<canonical.arity→tuple i=localTuple i
  padding_blocks :∀j :Fin (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length,∀i,
    tuple (arity commands+(2*(P).ambient root+4)*((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length-1-j.val)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root)
        ((commands).length+((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length-1-j.val))=p0 i
  values :∀i :Fin ((commands).length+(IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length),
    full.point tuple i.val=
      IntegralMixedPointCompanion.values p0 (fun j=>canonical.point localTuple j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount) i

variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
attribute [local irreducible] fullObservation canonicalObservation compiledObservation compiledProgram

noncomputable abbrev WordReceipt (z : ℕ→ℝ) (p0 : Fin ((P).ambient r+1)→ℝ) :=
  ProperWordData r (canonicalObservation old hv hd left right R side)
    (compiledObservation old hv hd left right R side) (fullObservation old hv hd left right R side)
    (compiledProgram old hv hd left right R side) (tailCount old hv hd left right R side) z p0

abbrev WordReceipt.word {old hv hd left right R side z p0} (W : WordReceipt old hv hd left right R side z p0) := W.sample.word
abbrev WordReceipt.valid {old hv hd left right R side z p0} (W : WordReceipt old hv hd left right R side z p0) := W.sample.valid
abbrev WordReceipt.width {old hv hd left right R side z p0} (W : WordReceipt old hv hd left right R side z p0) := W.sample.width
abbrev WordReceipt.joint {old hv hd left right R side z p0} (W : WordReceipt old hv hd left right R side z p0) := W.sample.joint

theorem exists_word_receipt (z : ℕ→ℝ)
    (hz : (canonicalObservation old hv hd left right R side).Roots z)
    (p0 : Fin ((P).ambient r+1)→ℝ)
    (hp0 : (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree).eval₂
      (Int.castRingHom ℝ) p0=0)
    (hg0 : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p0=0) :
    Nonempty (WordReceipt old hv hd left right R side z p0) := by
  obtain ⟨u,hu,hO,hB,hV⟩ := exists_padding_tuple old hv hd left right R side z
    (tuple_roots old hv hd left right R side z hz) p0 hp0 hg0
  have HW := sample_full_tuple old hv hd left right R side u hu
  unfold Sampled FormulaSignSlotRadialProviderRetainedAppend.JointSampled at HW
  obtain ⟨w,hw,hwidth,hjoint⟩ := HW
  have HA : arity (compiledProgram old hv hd left right R side)=
      (canonicalObservation old hv hd left right R side).arity := by
    simpa only [compiledObservation,IntegralMixedFramedRunObservation.ofCommands] using
      tuple_arity old hv hd left right R side
  refine ⟨⟨u,⟨w,hw,hwidth,hjoint⟩,hz,tuple_roots old hv hd left right R side z hz,hu,?_,hB,?_⟩⟩
  · intro i hi
    exact hO i (hi.trans_eq HA.symm)
  · intro i
    simpa only [tuple_point old hv hd left right R side] using hV i

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

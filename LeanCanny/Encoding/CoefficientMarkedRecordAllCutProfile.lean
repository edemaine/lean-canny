/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCutSource
/-! # Every coefficient of the literal next causal cut has original affine growth -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordAllCutProfile
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open CoefficientMarkedRecordProfile (atInstruction instruction_eq)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandCoefficient {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (hm : m ≤ S) (c : IntegralMixedFullHistoryScript.Command P B) (tau i j : ℕ) : ℤ :=
  match c with
  | .cut r k _ _ _ => IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix x hm r k tau) i j
  | _ => 0

noncomputable def instructionCoefficient {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (hm : m ≤ S) (c : Instruction a B) (tau i j : ℕ) : ℤ :=
  commandCoefficient (reframe x c.source c.source_cap) hm c.command tau i j

private theorem coefficient_reframe {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (hm : m ≤ S) (Q : SpatialSource a)
    (hQ : PurePowerReductionBounds.dimension (a + 1) Q.degree ≤ 2 ^ B)
    (c : Instruction a B) (tau i j : ℕ) :
    instructionCoefficient (reframe x Q hQ) hm c tau i j = instructionCoefficient x hm c tau i j := rfl

private theorem coefficient_congr {a S B m k : ℕ} {P : SpatialSource a} {I J : Type}
    (x : State P S B m I) (y : State P S B k J) (he : m = k) (hi : I = J) (hxy : HEq x y)
    (hx : m ≤ S) (hy : k ≤ S) (c : Instruction a B) (tau i j : ℕ) :
    instructionCoefficient x hx c tau i j = instructionCoefficient y hy c tau i j := by
  cases he
  cases hi
  exact congrArg (fun z => instructionCoefficient z hx c tau i j) (eq_of_heq hxy)

private noncomputable def planCoefficient (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (root : List Bool) (birth : ℕ)
    (hb : birth ≤ P.cap root + 1) (tau i j : ℕ) : ℤ :=
  instructionCoefficient (IntegralMixedFramedFamilyRunView.runAt P D root birth hb)
    (by rw [paddedPast_length]; exact hb)
    ((chronological (D.rules root) birth).getD (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)) tau i j

private theorem plan_congr (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (root root' : List Bool) (birth birth' : ℕ)
    (hr : root' = root) (he : birth' = birth) (hb : birth ≤ P.cap root + 1) (hb' : birth' ≤ P.cap root' + 1)
    (tau i j : ℕ) : planCoefficient P D root' birth' hb' tau i j = planCoefficient P D root birth hb tau i j := by
  cases hr
  cases he
  rfl

private theorem plan_le (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (tau i j M : ℕ)
    (hcoeff : (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).kind key) tau) i j).natAbs ≤ M) :
    (planCoefficient P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)
      (min_le_right _ _) tau i j).natAbs ≤ M := by
  change (commandCoefficient ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
    (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command tau i j).natAbs ≤ M
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command with
  | integer q hq hd => simp only [commandCoefficient, Int.natAbs_zero]; exact Nat.zero_le _
  | critical r => simp only [commandCoefficient, Int.natAbs_zero]; exact Nat.zero_le _
  | cut r c d ha hd =>
    have HS : IntegralMixedFramedHistoryFamilyBits.selection P D H key = ⟨r, c, d, ha⟩ := by
      unfold IntegralMixedFramedHistoryFamilyBits.selection
      rw [hc]
    change (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
        (IntegralMixedFramedHistoryFamilyBits.selection P D H key).rule
        (IntegralMixedFramedHistoryFamilyBits.selection P D H key).kind tau) i j).natAbs ≤ M at hcoeff
    rw [HS] at hcoeff
    exact hcoeff

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem natural_bound (R : List Bool → ℕ) (key : List Bool) (tau i j : ℕ) :
    let G := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix (G.state key) (G.birth_bound key) (G.rule key) (G.kind key) tau) i j).natAbs ≤
      2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha (pairFst key) * R (pairFst key) +
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha (pairFst key)) := by
  dsimp only
  unfold IntegralCriticalTotalSnapshotBits.integerEntry
  split_ifs with hi hj
  · exact IntegralMixedAuxiliaryMarkedRecordRadiusHeight.raw_coefficient_bound hn ht ha R key tau ⟨i, hi⟩ ⟨j, hj⟩
  all_goals exact Nat.zero_le _

private theorem plan_bound (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (tau i j : ℕ) :
    (planCoefficient (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) ctx
      ((CoefficientMarkedPreludeActual.indices n ctx).length + k)
      (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk) tau i j).natAbs ≤
      2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx +
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx) := by
  let key := IntegralMixedFramedHistoryFamilyBits.keyAt ctx ((CoefficientMarkedPreludeActual.indices n ctx).length + k) []
  have H := plan_le (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    key tau i j _ (natural_bound hn ht ha R key tau i j)
  have E := plan_congr (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) ctx (pairFst key)
    ((CoefficientMarkedPreludeActual.indices n ctx).length + k)
    (IntegralMixedFramedHistoryFamilyBits.prefixLength (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) key)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk))
    (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk) (min_le_right _ _) tau i j
  rw [E] at H
  simpa only [key, IntegralMixedFramedHistoryFamilyBits.keyAt_root] using H

theorem native_coefficient_bound (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k<IntegralMixedCausalRecordPlanBits.count ctx) (tau i j:ℕ):
    (instructionCoefficient
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius
        (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k)
        (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le))
      (by
        rw [CoefficientMarkedRecordActual.codes_length]
        exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
      (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius
        (CoefficientMarkedRecordNative.run hn ht ha ctx radius
          (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
          (CoefficientMarkedRecordActual.codes ctx k)
          (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le))
        (IntegralMixedCausalRecordPlanBits.code ctx k)) tau i j).natAbs≤
      2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx*radius ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius
  let birth:=(CoefficientMarkedPreludeActual.indices n ctx).length+k
  let x:=CoefficientMarkedRecordNative.run hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k)
    (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)
  let y:=IntegralMixedFramedFamilyRunView.runAt P D ctx birth
    (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
  let initial:=CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
  have HM:(CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length=
      (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D ctx) (D.rules ctx) birth).length:=by
    rw [paddedPast_length,CoefficientMarkedRecordActual.codes_length]
  have HI:= (CoefficientMarkedRecordSerializer.index_eq hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k)
    (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)).trans
    (congrArg (Index (Fin 0)) (CoefficientMarkedRecordActual.padded_prefix hn ht ha ctx radius k hk.le).symm)
  have HX:=CoefficientMarkedRecordActual.native_runAt hn ht ha ctx radius k hk.le
  have H:=plan_bound hn ht ha ctx radius k hk.le tau i j
  change (instructionCoefficient y _ (atInstruction hn ht ha ctx radius k) tau i j).natAbs≤_ at H
  rw [instruction_eq hn ht ha ctx radius k hk] at H
  have HE:=coefficient_congr x
    (reframe y (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius) initial.critical_cap)
    HM HI HX
    (by
      rw [CoefficientMarkedRecordActual.codes_length]
      exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
    (by
      rw [paddedPast_length]
      exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
    (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius x (IntegralMixedCausalRecordPlanBits.code ctx k)) tau i j
  rw [coefficient_reframe] at HE
  exact (congrArg Int.natAbs HE).trans_le H


/-- The literal truncated raw cut, at every coefficient and natural matrix entry. -/
theorem raw_coefficient_bound (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (tau i j : ℕ) :
    let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
        ((CoefficientMarkedRecordCutSource.nativeRaw hn ht ha ctx R k hk.le).coeff tau)) i j).natAbs ≤
      2 ^ (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx * R ctx +
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx) := by
  dsimp only
  have H := native_coefficient_bound hn ht ha ctx R k hk tau i j
  unfold instructionCoefficient CoefficientMarkedRecordNative.instruction IntegralMixedCausalRecordBits.instantiate
    IntegralMixedCausalUnitRecordBits.record at H
  simp only [hc, Bool.false_eq_true, ite_false, IntegralMixedCausalRecordBits.Template.command, commandCoefficient] at H
  unfold CoefficientMarkedRecordCutSource.nativeRaw
  rw [IntegralMixedCutMatrix.raw_coefficient_matrix]
  split_ifs with htau
  · exact H
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, Matrix.zero_apply, dite_eq_ite, ite_self, Int.natAbs_zero]
    exact Nat.zero_le _

end LeanCanny.Encoding.CoefficientMarkedRecordAllCutProfile

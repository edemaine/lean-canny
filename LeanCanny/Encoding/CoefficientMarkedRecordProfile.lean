/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordActual
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRawHeight
/-! # Actual causal cut matrices inherit the original radius profile -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProfile
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def commandTop {a S B m:ℕ} {P:SpatialSource a} {I:Type}
    (x:State P S B m I) (hm:m≤S) (c:IntegralMixedFullHistoryScript.Command P B) (i j:ℕ):ℤ:=
  match c with
  | .cut r k d _ _=>IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix x hm r k d) i j
  | _=>0

noncomputable def instructionTop {a S B m:ℕ} {P:SpatialSource a} {I:Type}
    (x:State P S B m I) (hm:m≤S) (c:Instruction a B) (i j:ℕ):ℤ:=
  commandTop (reframe x c.source c.source_cap) hm c.command i j

private theorem instructionTop_reframe {a S B m:ℕ} {P:SpatialSource a} {I:Type}
    (x:State P S B m I) (hm:m≤S) (Q:SpatialSource a)
    (hQ:PurePowerReductionBounds.dimension (a+1) Q.degree≤2^B)
    (c:Instruction a B) (i j:ℕ):
    instructionTop (reframe x Q hQ) hm c i j=instructionTop x hm c i j:=rfl

private theorem common_eq {a S B m k:ℕ} {P:SpatialSource a} {I J:Type}
    (x:State P S B m I) (y:State P S B k J) (hm:m=k) (hi:I=J) (hxy:HEq x y):
    commonDenominator x=commonDenominator y:=by
  cases hm
  cases hi
  exact congrArg (fun z=>commonDenominator z) (eq_of_heq hxy)

private theorem commands_succ (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k<IntegralMixedCausalRecordPlanBits.count ctx):
    CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius
      (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx (k+1))
      (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx _ (by omega))=
    CoefficientMarkedRecordNative.instruction hn ht ha ctx radius
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius
        (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k)
        (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le))
      (IntegralMixedCausalRecordPlanBits.code ctx k)::
    CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius
      (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k)
      (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le):=by
  simp only [CoefficientMarkedRecordActual.codes_succ]
  rw [CoefficientMarkedRecordSerializer.commands_cons]
  apply congrArg₂ List.cons _ rfl
  let x:=CoefficientMarkedRecordNative.run hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k)
    (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)
  let cs:=CoefficientMarkedRecordSerializer.commands hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k)
    (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)
  let initial:=CoefficientMarkedPreludePrefix.initial hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
  let y:=run initial cs (by
    rw [CoefficientMarkedRecordSerializer.commands_length]
    exact CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)
  have HM:=common_eq x (reframe y (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius) initial.critical_cap)
    (CoefficientMarkedRecordSerializer.commands_length hn ht ha ctx radius _ _ _).symm
    (CoefficientMarkedRecordSerializer.index_eq hn ht ha ctx radius _ _ _)
    (CoefficientMarkedRecordSerializer.run_framed hn ht ha ctx radius _ _ _)
  rw [reframe_denominator] at HM
  have HI:=instantiate_congr y x
    (CoefficientMarkedRecordSerializer.record hn ht ha ctx radius
      ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length)
      (IntegralMixedCausalRecordPlanBits.code ctx k)) HM.symm
  exact HI

noncomputable def atInstruction (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ):
    Instruction (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx):=
  (chronological ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx)
    ((CoefficientMarkedPreludeActual.indices n ctx).length+k)).getD
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius) ctx)

theorem instruction_eq (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k<IntegralMixedCausalRecordPlanBits.count ctx):
    atInstruction hn ht ha ctx radius k=
      CoefficientMarkedRecordNative.instruction hn ht ha ctx radius
        (CoefficientMarkedRecordNative.run hn ht ha ctx radius
          (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
          (CoefficientMarkedRecordActual.codes ctx k)
          (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le))
        (IntegralMixedCausalRecordPlanBits.code ctx k):=by
  have H:=congrArg List.head? ((CoefficientMarkedRecordActual.commands_prefix hn ht ha ctx radius (k+1) (by omega)).trans
    (commands_succ hn ht ha ctx radius k hk))
  rw [List.head?_drop,List.head?_cons] at H
  have HL:=CoefficientMarkedRecordActual.plan_length hn ht ha ctx radius
  have HC:chronological ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius).rules ctx)
      ((CoefficientMarkedPreludeActual.indices n ctx).length+k)=some
      (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius
        (CoefficientMarkedRecordNative.run hn ht ha ctx radius
          (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
          (CoefficientMarkedRecordActual.codes ctx k)
          (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le))
        (IntegralMixedCausalRecordPlanBits.code ctx k)):=by
    unfold chronological
    rw [List.getElem?_reverse' (i:=(CoefficientMarkedPreludeActual.indices n ctx).length+k)
      (j:=IntegralMixedCausalRecordPlanBits.count ctx-(k+1)) (by omega)]
    exact H
  unfold atInstruction
  rw [HC]
  rfl


private theorem instructionTop_congr {a S B m k:ℕ} {P:SpatialSource a} {I J:Type}
    (x:State P S B m I) (y:State P S B k J) (he:m=k) (hi:I=J) (hxy:HEq x y)
    (hx:m≤S) (hy:k≤S) (c:Instruction a B) (i j:ℕ):
    instructionTop x hx c i j=instructionTop y hy c i j:=by
  cases he
  cases hi
  exact congrArg (fun z=>instructionTop z hx c i j) (eq_of_heq hxy)

private noncomputable def planTop (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (root:List Bool) (birth:ℕ)
    (hb:birth≤P.cap root+1) (i j:ℕ):ℤ:=
  instructionTop (IntegralMixedFramedFamilyRunView.runAt P D root birth hb)
    (by
      rw [paddedPast_length]
      exact hb)
    ((chronological (D.rules root) birth).getD
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)) i j

private theorem planTop_congr (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (root root':List Bool) (birth birth':ℕ)
    (hr:root'=root) (he:birth'=birth) (hb:birth≤P.cap root+1) (hb':birth'≤P.cap root'+1)
    (i j:ℕ):planTop P D root' birth' hb' i j=planTop P D root birth hb i j:=by
  cases hr
  cases he
  rfl

private theorem planTop_le (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (i j M:ℕ)
    (htop:(IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedNormalizationTopBits.top (IntegralMixedFramedHistoryFamilyBits.family P D H) key) i j).natAbs≤M):
    (planTop P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)
      (min_le_right _ _) i j).natAbs≤M:=by
  change (commandTop ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
    (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command i j).natAbs≤M
  cases hc:(IntegralMixedFramedHistoryFamilyBits.instruction P D key).command with
  | integer q hq hd=>simp only [commandTop,Int.natAbs_zero];exact Nat.zero_le _
  | critical r=>simp only [commandTop,Int.natAbs_zero];exact Nat.zero_le _
  | cut r c d ha hd=>
    change (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedCutMatrix.coefficientMatrix ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
        (IntegralMixedFramedHistoryFamilyBits.selection P D H key).rule
        (IntegralMixedFramedHistoryFamilyBits.selection P D H key).kind
        (IntegralMixedFramedHistoryFamilyBits.selection P D H key).degree) i j).natAbs≤M at htop
    have HS:IntegralMixedFramedHistoryFamilyBits.selection P D H key=⟨r,c,d,ha⟩:=by
      unfold IntegralMixedFramedHistoryFamilyBits.selection
      rw [hc]
    have HE:=congrArg (fun s:IntegralMixedFullHistoryFamilyBits.Selection
      (IntegralMixedFramedHistoryFamilyBits.instruction P D key).source=>
      IntegralCriticalTotalSnapshotBits.integerEntry
        (IntegralMixedCutMatrix.coefficientMatrix ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
          ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key) s.rule s.kind s.degree) i j) HS
    exact (congrArg Int.natAbs HE).symm.trans_le htop

private theorem plan_top_bound (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (i j:ℕ):
    (planTop (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius) ctx
      ((CoefficientMarkedPreludeActual.indices n ctx).length+k)
      (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk) i j).natAbs≤
    2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx*radius ctx+
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx):=by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt ctx ((CoefficientMarkedPreludeActual.indices n ctx).length+k) []
  have H:=planTop_le (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius)
    (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha radius) key i j _
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.natural_top_bound hn ht ha radius key i j)
  have E:=planTop_congr (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha radius) ctx (pairFst key)
    ((CoefficientMarkedPreludeActual.indices n ctx).length+k)
    (IntegralMixedFramedHistoryFamilyBits.prefixLength (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) key)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _
      (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk))
    (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk) (min_le_right _ _) i j
  rw [E] at H
  simpa only [key,IntegralMixedFramedHistoryFamilyBits.keyAt_root] using H


theorem native_top_bound (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k<IntegralMixedCausalRecordPlanBits.count ctx) (i j:ℕ):
    (instructionTop
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
        (IntegralMixedCausalRecordPlanBits.code ctx k)) i j).natAbs≤
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
  have H:=plan_top_bound hn ht ha ctx radius k hk.le i j
  change (instructionTop y _ (atInstruction hn ht ha ctx radius k) i j).natAbs≤_ at H
  rw [instruction_eq hn ht ha ctx radius k hk] at H
  have HE:=instructionTop_congr x
    (reframe y (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx radius) initial.critical_cap)
    HM HI HX
    (by
      rw [CoefficientMarkedRecordActual.codes_length]
      exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
    (by
      rw [paddedPast_length]
      exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
    (CoefficientMarkedRecordNative.instruction hn ht ha ctx radius x (IntegralMixedCausalRecordPlanBits.code ctx k)) i j
  rw [instructionTop_reframe] at HE
  exact (congrArg Int.natAbs HE).trans_le H


/-- The selected raw coefficient belongs to the literal original causal cut. -/
theorem original_cut_top_bound (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k<IntegralMixedCausalRecordPlanBits.count ctx)
    (hc:IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k)=false)
    (i j:ℕ):
    let x:=CoefficientMarkedRecordNative.run hn ht ha ctx radius
      (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k)
      (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk.le)
    let c:=CoefficientMarkedRecordNative.cut hn ht ha ctx radius
      ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length)
      (IntegralMixedCausalRecordPlanBits.code ctx k)
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
        ((IntegralMixedCutMatrix.raw x
          (by
            rw [CoefficientMarkedRecordActual.codes_length]
            exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk.le)
          (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
          (c.kind (commonDenominator x) (commonDenominator_ne_zero x)) c.degree).coeff c.degree)) i j).natAbs≤
      2^(IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx*radius ctx+
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx):=by
  dsimp only
  have H:=native_top_bound hn ht ha ctx radius k hk i j
  unfold instructionTop CoefficientMarkedRecordNative.instruction instantiate
    IntegralMixedCausalUnitRecordBits.record at H
  simp only [hc,Bool.false_eq_true,ite_false,Template.command,commandTop] at H
  rw [IntegralMixedCutMatrix.raw_coefficient_matrix,ite_eq_left le_rfl]
  exact H

end LeanCanny.Encoding.CoefficientMarkedRecordProfile

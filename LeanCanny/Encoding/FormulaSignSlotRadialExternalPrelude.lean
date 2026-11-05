/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalCoordinates
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerData
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRealization
public import LeanCanny.Encoding.BoundedRegularLowHeight
public import LeanCanny.Geometry.ParameterizedBoundaryRadiusBudget
public import LeanCanny.Geometry.AuxiliaryCandidateRegularLift
/-! # The actual external-coordinate finite algebra, with unchanged spatial syntax

Only the integer leaves and their scalar width change. The spatial source
is the literal original closed-source regular lift at one shared radius.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalPrelude
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "A" => FormulaSignSlotRadialJointStratumNative.access

noncomputable abbrev number := FormulaSignSlotRadialExternalContext.number
abbrev original := FormulaSignSlotRadialExternalContext.original
noncomputable abbrev source := FormulaSignSlotRadialExternalCoordinates.source
theorem source_access : IntegerPolynomialRootQueriesBits.Access source := FormulaSignSlotRadialExternalCoordinates.access
theorem source_nonzero (q : List Bool) : source.polynomial q≠0 := FormulaSignSlotRadialExternalCoordinates.nonzero q
noncomputable abbrev degreeBound := FormulaSignSlotRadialExternalCoordinates.degreeBound
noncomputable def count (ctx : List Bool) := number ctx+1
theorem count_unary : UnaryFn count := FormulaSignSlotRadialExternalContext.number_unary.add (UnaryFn.const 1)

def jointHeader (ctx : List Bool) := FormulaSignSlotRadialJointStratum.header
  (ImplicitSourceGramGrid.header (FormulaSignSlotRadialExternalContext.gridContext ctx))
theorem jointHeader_FP : jointHeader ∈ FP := by polytime [jointHeader,ImplicitSourceGramGrid.header,
  FormulaSignSlotRadialJointStratum.header,FormulaSignSlotRadialExternalContext.gridContext,
  FormulaSignSlotRadialExternalContext.metadata]
noncomputable def oldRadius := IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha
theorem oldRadius_binary : BinaryFn oldRadius := IntegralMixedAuxiliaryCandidateRadius.radius_binary hn ht ha
noncomputable def jointRadius (H : List Bool) := max
  (oldRadius (FormulaSignSlotRadialJointLayout.source false H))
  (oldRadius (FormulaSignSlotRadialJointLayout.source true H))

private theorem binary_max {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun c => max (f c) (g c)) :=
  (BinaryFn.ite (hf.le hg) hg hf).of_eq (fun _ => Nat.max_def.symm)

theorem jointRadius_binary : BinaryFn jointRadius := binary_max
  (oldRadius_binary.comp (FormulaSignSlotRadialJointLayout.source_FP false))
  (oldRadius_binary.comp (FormulaSignSlotRadialJointLayout.source_FP true))

noncomputable def joiningExponent (u : List Bool) :=
  Geometry.ParameterizedBoundaryRadiusHead.radiusExponent (n u) (t u).toData.size (t u).toData.size
theorem joiningExponent_binary : BinaryFn joiningExponent :=
  Geometry.ParameterizedBoundaryRadiusBudget.radiusExponent_binary hn
    (BinaryFn.ofUnary (Geometry.AuxiliaryCandidateRegularLift.allowance_unary ht))
    (BinaryFn.ofUnary (Geometry.AuxiliaryCandidateRegularLift.allowance_unary ht))
noncomputable def jointJoiningExponent (H : List Bool) := max
  (joiningExponent (FormulaSignSlotRadialJointLayout.source false H))
  (joiningExponent (FormulaSignSlotRadialJointLayout.source true H))
theorem jointJoiningExponent_binary : BinaryFn jointJoiningExponent := binary_max
  (joiningExponent_binary.comp (FormulaSignSlotRadialJointLayout.source_FP false))
  (joiningExponent_binary.comp (FormulaSignSlotRadialJointLayout.source_FP true))
noncomputable def joiningCutoff (ctx : List Bool) := max
  (joiningExponent (original ctx)) (jointJoiningExponent (jointHeader ctx))
theorem joiningCutoff_binary : BinaryFn joiningCutoff := binary_max
  (joiningExponent_binary.comp FormulaSignSlotRadialExternalContext.original_FP)
  (jointJoiningExponent_binary.comp jointHeader_FP)

noncomputable def radius (ctx : List Bool) :=
  max (oldRadius (original ctx)) (jointRadius (jointHeader ctx))+
    ImplicitSourceGramGrid.mass S (FormulaSignSlotRadialExternalContext.gridContext ctx)+
    (max (number ctx) (ImplicitSourceGramGrid.count S (FormulaSignSlotRadialExternalContext.gridContext ctx))).size+2+
    joiningCutoff ctx

theorem radius_binary : BinaryFn radius := by
  have HO : BinaryFn (fun c => oldRadius (original c)) :=
    oldRadius_binary.comp FormulaSignSlotRadialExternalContext.original_FP
  have HJ : BinaryFn (fun c => jointRadius (jointHeader c)) := jointRadius_binary.comp jointHeader_FP
  have HM : BinaryFn (fun c => ImplicitSourceGramGrid.mass S (FormulaSignSlotRadialExternalContext.gridContext c)) :=
    (ImplicitSourceGramGrid.mass_binary S A).comp FormulaSignSlotRadialExternalContext.gridContext_FP
  have HC : UnaryFn (fun c => ImplicitSourceGramGrid.count S (FormulaSignSlotRadialExternalContext.gridContext c)) :=
    (ImplicitSourceGramGrid.count_unary S A).comp FormulaSignSlotRadialExternalContext.gridContext_FP
  exact (((binary_max HO HJ).add HM).add
    (binary_max (BinaryFn.ofUnary FormulaSignSlotRadialExternalContext.number_unary) (BinaryFn.ofUnary HC)).size).add
    (BinaryFn.const 2) |>.add joiningCutoff_binary

theorem joiningExponent_le_radius (ctx : List Bool) : joiningExponent (original ctx)≤radius ctx :=
  (le_max_left _ _).trans (Nat.le_add_left _ _)

noncomputable def parameters := IntegralMixedSourceIntegerPrelude.parameters
  (fun c => number c+3) (IntegralMixedAuxiliaryMarkedIntegerPlan.degree t) degreeBound count
theorem access : Access parameters := IntegralMixedSourceIntegerPrelude.access
  (FormulaSignSlotRadialExternalContext.number_unary.add (UnaryFn.const 3))
  (IntegralMixedAuxiliaryMarkedIntegerPlan.degree_binary ht)
  FormulaSignSlotRadialExternalCoordinates.degreeBound_binary count_unary

noncomputable def readers := BoundedRegularLowCoefficient.readers number (t ∘ original) radius
theorem readers_native : readers.PolyTime := BoundedRegularLowCoefficient.readers_native
  FormulaSignSlotRadialExternalContext.number_unary
  (mem_FP_comp FormulaSignSlotRadialExternalContext.original_FP ht) radius_binary
noncomputable def spatial (ctx : List Bool) : SpatialSource (parameters.ambient ctx) :=
  BoundedRegularLowModularTerm.source readers ctx
theorem spatial_eq (ctx : List Bool) : spatial ctx=IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx := rfl
theorem spatial_degree (ctx : List Bool) : (spatial ctx).degree=parameters.degree ctx :=
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t radius ctx
theorem source_cap (ctx : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap (parameters.ambient ctx+1) (parameters.degree ctx)≤2^parameters.width ctx :=
  IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _ ctx
theorem source_degree_cap (ctx : List Bool) (i : ℕ) :
    source.degree (pair ctx (BinaryNatCode.encode i))≤2^parameters.width ctx := by
  have H := FormulaSignSlotRadialExternalCoordinates.degree_le (pair ctx (BinaryNatCode.encode i))
  rw [pairFst_pair] at H
  exact H.trans (IntegralMixedSourceIntegerPrelude.bound_cap _ _ _ _ ctx)
theorem room (ctx : List Bool) : count ctx+2≤parameters.cap ctx+1 := by
  change count ctx+2≤count ctx+2+1
  omega

noncomputable def plan := IntegralMixedSourceIntegerPrelude.plan parameters spatial spatial_degree source_cap
  source count source_nonzero source_degree_cap room
theorem ambient_positive (ctx : List Bool) : 0<parameters.ambient ctx := by change 0<number ctx+3; omega
theorem source_width (ctx : List Bool) : (parameters.degree ctx).size≤parameters.sourceWidth ctx := le_rfl
noncomputable def data := IntegralMixedSourceIntegerPrelude.data parameters spatial spatial_degree source_cap
  source count source_nonzero source_degree_cap room ambient_positive source_width
noncomputable def tables := IntegralMixedSourceIntegerPrelude.tables parameters count
theorem tables_native : IntegralMixedHeaderTablesBits.Access tables :=
  IntegralMixedSourceIntegerPrelude.tables_native parameters access count_unary
theorem tables_represents : IntegralMixedFramedHeaderBits.Represents parameters plan data tables :=
  IntegralMixedSourceIntegerPrelude.tables_represents parameters spatial spatial_degree source_cap source count
    source_nonzero source_degree_cap room ambient_positive source_width
theorem instruction_source (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction parameters plan key).source=spatial (pairFst key) :=
  IntegralMixedSourceIntegerPrelude.instruction_source parameters spatial spatial_degree source_cap source count
    source_nonzero source_degree_cap room key

noncomputable def savedReaders := readers.comp pairFst
theorem savedReaders_native : savedReaders.PolyTime := readers_native.comp pairFst_mem_FP
private theorem source_comp (R : BoundedFullWriter.Readers) (f : List Bool → List Bool) (key : List Bool) :
    HEq (BoundedRegularLowModularTerm.source R (f key)) (BoundedRegularLowModularTerm.source (R.comp f) key) := HEq.rfl
theorem snapshot : BoundedRegularFramedOriginalBits.Snapshot parameters plan savedReaders where
  ambient _ := rfl
  source key := (heq_of_eq (instruction_source key)).trans (source_comp readers pairFst key)

noncomputable def run (ctx : List Bool) := IntegralMixedFramedHistoryScript.run
  (IntegralMixedFramedHistoryFamilyBits.initial parameters plan ctx) (plan.rules ctx)
  (by have H := plan.room ctx; omega)

private theorem realizes_plan (P : Parameters) (Q : ∀r,SpatialSource (P.ambient r))
    (hdegree : ∀r,(Q r).degree=P.degree r)
    (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
    (T : IntegerPolynomialRootQueriesBits.Source) (N : List Bool → ℕ)
    (hz : ∀q,T.polynomial q≠0) (hd : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
    (hroom : ∀r,N r+2≤P.cap r+1) (r : List Bool) (v : ℕ → ℝ)
    (hv : ∀i<N r,(T.polynomial (pair r (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    let D := IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap T N hz hd hroom
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run (IntegralMixedFramedHistoryFamilyBits.initial P D r) (D.rules r)
        (by have H := D.room r; omega)) (fun j => v (N r-1-j)) := by
  let D := IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap T N hz hd hroom
  let hq := fun c => (IntegralMixedFramedHistoryFamilyBits.initial P D c).critical_cap
  exact IntegralMixedSourceIntegerPrelude.realizes P Q hq T N hz hd r
    (IntegralMixedFramedHistoryFamilyBits.initial P D r) (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) (by rw [IntegralMixedSourceIntegerPrelude.commands_length]; have H := hroom r; omega) v hv

attribute [local irreducible] run plan parameters spatial FormulaSignSlotRadialExternalCoordinates.source
  FormulaSignSlotRadialExternalCoordinates.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree

theorem realizes (ctx : List Bool) (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx) :
    @IntegralMixedIntegerRealization.Realizes (parameters.ambient ctx)
      (parameters.cap ctx+1) (parameters.width ctx)
      (IntegralMixedFramedHistoryScript.source (plan.initialSource ctx) (plan.rules ctx))
      (plan.rules ctx).length (IntegralMixedFramedHistoryScript.Index (Fin 0) (plan.rules ctx)) (run ctx)
      (fun j => FormulaSignSlotRadialExternalCoordinates.values ctx hw (count ctx-1-j)) := by
  unfold run plan
  exact realizes_plan parameters spatial spatial_degree source_cap source count source_nonzero source_degree_cap room
    ctx (FormulaSignSlotRadialExternalCoordinates.values ctx hw)
    (fun i _ => FormulaSignSlotRadialExternalCoordinates.roots ctx hw i)

end LeanCanny.Encoding.FormulaSignSlotRadialExternalPrelude

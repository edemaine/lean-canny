/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerNative
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordBounds
public import LeanCanny.Algebra.IntegerPolynomialSourceChoice
/-! # Literal provider preludes followed by the actual causal record table

The first root field retains the entire provider context, including the
external own word. The second field holds the chronological record table.
The integer leaves and spatial polynomial read only that literal provider.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source

def providerContext (root : List Bool) := pairFst root
def root (provider records aux : List Bool) := pair provider (pair records aux)
theorem providerContext_FP : providerContext ∈ FP := pairFst_mem_FP
theorem providerContext_root (provider records aux : List Bool) :
    providerContext (root provider records aux) = provider := pairFst_pair _ _
theorem records_root (provider records aux : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (root provider records aux) = records := by
  simp only [IntegralMixedCausalRecordPlanBits.records,root,pairSnd_pair,pairFst_pair]

def sourceQuery (q : List Bool) := pair (providerContext (pairFst q)) (pairSnd q)
theorem sourceQuery_FP : sourceQuery ∈ FP := mem_FP_pair
  (mem_FP_comp (f := pairFst) (g := providerContext) pairFst_mem_FP providerContext_FP) pairSnd_mem_FP

noncomputable def source := IntegerPolynomialSourceChoice.reindex
  FormulaSignSlotRadialProviderIntegerPlan.source sourceQuery
theorem source_access : IntegerPolynomialRootQueriesBits.Access source :=
  IntegerPolynomialSourceChoice.reindex_access _ FormulaSignSlotRadialProviderIntegerPlan.source_access sourceQuery_FP
theorem source_nonzero (q : List Bool) : source.polynomial q ≠ 0 :=
  FormulaSignSlotRadialProviderIntegerPlan.source_nonzero (sourceQuery q)

private theorem reindex_degree (Q : IntegerPolynomialRootQueriesBits.Source) (f : List Bool → List Bool)
    (q : List Bool) : (IntegerPolynomialSourceChoice.reindex Q f).degree q = Q.degree (f q) := rfl
theorem source_degree_packet (root bits : List Bool) : source.degree (pair root bits) =
    FormulaSignSlotRadialProviderIntegerPlan.source.degree (pair (providerContext root) bits) := by
  rw [source,reindex_degree]
  simp only [sourceQuery,pairFst_pair,pairSnd_pair]

noncomputable def count (root : List Bool) := FormulaSignSlotRadialProviderIntegerPlan.count (providerContext root)
theorem count_unary : UnaryFn count := FormulaSignSlotRadialProviderIntegerPlan.count_unary.comp providerContext_FP
noncomputable def fullCount (root : List Bool) := count root + IntegralMixedCausalRecordPlanBits.count root
theorem fullCount_unary : UnaryFn fullCount := count_unary.add IntegralMixedCausalRecordPlanBits.count_unary
noncomputable def degreeBound (root : List Bool) := FormulaSignSlotRadialProviderIntegerPlan.degreeBound (providerContext root)
theorem degreeBound_binary : BinaryFn degreeBound :=
  FormulaSignSlotRadialProviderIntegerSource.degreeBound_binary.comp providerContext_FP

noncomputable def parameters := IntegralMixedSourceIntegerPrelude.parameters
  (FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient ∘ providerContext)
  (FormulaSignSlotRadialProviderIntegerPlan.parameters.degree ∘ providerContext) degreeBound fullCount
theorem access : Access parameters := IntegralMixedSourceIntegerPrelude.access
  (FormulaSignSlotRadialProviderIntegerPlan.access.ambient.comp providerContext_FP)
  (FormulaSignSlotRadialProviderIntegerPlan.access.degree.comp providerContext_FP) degreeBound_binary fullCount_unary

noncomputable def spatial (root : List Bool) : SpatialSource (parameters.ambient root) :=
  FormulaSignSlotRadialProviderIntegerPlan.spatial (providerContext root)
theorem positive (root : List Bool) : 0 < parameters.ambient root :=
  FormulaSignSlotRadialProviderIntegerPlan.ambient_positive (providerContext root)
theorem spatial_degree (root : List Bool) : (spatial root).degree = parameters.degree root :=
  FormulaSignSlotRadialProviderIntegerPlan.spatial_degree (providerContext root)
theorem spatial_cap (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap (parameters.ambient root+1) (parameters.degree root) ≤
      2^parameters.width root := IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _ root
theorem source_cap (root : List Bool) : PurePowerReductionBounds.dimension (parameters.ambient root+1)
    (spatial root).degree ≤ 2^parameters.width root := by
  rw [spatial_degree]
  exact (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
    PurePowerReductionBounds.dimension (parameters.ambient root+1) (parameters.degree root) ≤
      IntegralMixedExceptionalBounds.auxiliaryCap (parameters.ambient root+1) (parameters.degree root)).trans (spatial_cap root)

theorem degreeBound_cap (root : List Bool) : degreeBound root ≤ 2^parameters.width root :=
  IntegralMixedSourceIntegerPrelude.bound_cap _ _ _ _ root

theorem source_width (root : List Bool) : (parameters.degree root).size ≤ parameters.sourceWidth root := le_rfl

attribute [local irreducible] source parameters

theorem source_degree_cap (root : List Bool) (i : ℕ) :
    source.degree (pair root (BinaryNatCode.encode i)) ≤ 2^parameters.width root := by
  rw [source_degree_packet]
  have H : FormulaSignSlotRadialProviderIntegerPlan.source.degree
      (pair (providerContext root) (BinaryNatCode.encode i)) ≤ degreeBound root := by
    simpa only [degreeBound,pairFst_pair] using FormulaSignSlotRadialProviderIntegerSource.degree_le
      (pair (providerContext root) (BinaryNatCode.encode i))
  exact H.trans (degreeBound_cap root)
theorem room (root : List Bool) : IntegralMixedCausalRecordPlanBits.count root + count root + 2 ≤ parameters.cap root+1 := by
  unfold parameters
  change _ ≤ count root + IntegralMixedCausalRecordPlanBits.count root + 2 + 1
  omega

noncomputable def plan := IntegralMixedSourceIntegerRecordAppend.plan parameters (fun root _ => spatial root)
  positive (fun root _ => spatial_degree root) spatial_cap count source source_nonzero source_degree_cap room
noncomputable def data := IntegralMixedSourceIntegerRecordAppend.data parameters (fun root _ => spatial root)
  positive (fun root _ => spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room source_width

theorem integerOriginal : IntegralMixedIntegerFamilyBits.Original parameters
    (IntegralMixedFramedIntegerBits.polynomial parameters plan) :=
  IntegralMixedSourceIntegerRecordAppend.integerOriginal parameters (fun root _ => spatial root) positive
    (fun root _ => spatial_degree root) spatial_cap count source source_nonzero source_degree_cap room access source_access count_unary

theorem instruction_source (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction parameters plan key).source = spatial (pairFst key) :=
  IntegralMixedSourceIntegerRecordAppend.instruction_source parameters (fun root _ => spatial root) positive
    (fun root _ => spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room key

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan

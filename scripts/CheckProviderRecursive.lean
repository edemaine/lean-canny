import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendIdentity
import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNoCriticalComplete
import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeBounds
import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalScalar
import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowMeanRoots

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
set_option backward.isDefEq.respectTransparency false

example (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    FormulaSignSlotRadialProviderProperCritical.NoCritical q ↔
      FormulaSignSlotRadialProviderProperCritical.OriginalSliceCriticalFree q hv hd :=
  FormulaSignSlotRadialProviderProperCritical.noCritical_iff_original_critical_free q hv hd

example (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old) :
    ∃q,FormulaSignSlotRadialProviderAtomic.Valid q ∧ FormulaSignSlotRadialProviderEdge.Adjacent old q := by
  obtain ⟨q,hq,_,_,_,_,hEdge,_⟩ := FormulaSignSlotRadialProviderRetainedAppend.exists_identity_child old hv hd
  exact ⟨q,hq,hEdge⟩

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor

variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old} {e : ℕ} {he : e<FormulaSignSlotRadialProviderAtomic.endBirth (FormulaSignSlotRadialProviderAtomic.dimension old) (FormulaSignSlotRadialProviderAtomic.initial old) old}
  {p : Fin (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (preparedRoot old e)+1)→ℝ}

example (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.Valid (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old e W.word) := W.atomic_valid

example (W : WordReceipt old hv hd e he p) :
    HEq (FormulaSignSlotRadialProviderAtomic.point (packet (FormulaSignSlotRadialProviderAtomic.dimension old) old e W.word) W.atomic_valid) p :=
  W.point_heq W.atomic_valid

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend

#check FormulaSignSlotRadialProviderRetainedAppend.exists_valid_at
#check FormulaSignSlotRadialProviderRetainedAppend.exists_identity_child
#check FormulaSignSlotRadialProviderRetainedAppend.WordReceipt.before_probe
#check FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt
#check FormulaSignSlotRadialProviderBadProbeBounds.bounds
#check FormulaSignSlotRadialProviderCutInterval.interval_generators_scalar
#check FormulaSignSlotRadialProviderProperRow.actual_mean_roots

#print axioms FormulaSignSlotRadialProviderRetainedAppend.exists_valid_at
#print axioms FormulaSignSlotRadialProviderRetainedAppend.exists_identity_child
#print axioms FormulaSignSlotRadialProviderRetainedAppend.identity_of_atomic_point_heq
#print axioms FormulaSignSlotRadialProviderRetainedAppend.WordReceipt.atomic_valid
#print axioms FormulaSignSlotRadialProviderRetainedAppend.WordReceipt.point_heq
#print axioms FormulaSignSlotRadialProviderRetainedAppend.WordReceipt.before_probe
#print axioms FormulaSignSlotRadialProviderRetainedAppend.WordReceipt.all_critical
#print axioms FormulaSignSlotRadialProviderRetainedAppend.WordReceipt.latest_companions
#print axioms FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt
#print axioms FormulaSignSlotRadialProviderProperCritical.noCritical_iff_original_critical_free
#print axioms FormulaSignSlotRadialProviderBadProbeBounds.bounds
#print axioms FormulaSignSlotRadialProviderCutInterval.interval_generators_scalar
#print axioms FormulaSignSlotRadialProviderProperRow.actual_mean_roots

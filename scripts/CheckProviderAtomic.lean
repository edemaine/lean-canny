import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSize
import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordEndpointRealization
import LeanCanny.Encoding.FormulaSignSlotRadialProviderPair
import LeanCanny.Encoding.FormulaSignSlotRadialProviderBallConnections

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotRadialProviderAtomic

example : language∈PSPACE := mem_PSPACE

example (c q : List Bool) (hq : Valid q) (hc : provider q=c) : q.length≤providerVertexBudget c := by
  rw [←hc]
  exact vertex_length_provider q hq

example (c : List Bool) :
    HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial (FormulaSignSlotRadialProviderPair.oldOf c))
      (FormulaSignSlotRadialProviderIntegerPlan.spatial c) := FormulaSignSlotRadialProviderPair.spatial_shared c

example (c : List Bool)
    (x y : BoundedZeroSource.Bounded (FormulaSignSlotRadialProviderBallConnections.equation c)
      (FormulaSignSlotRadialProviderBallConnections.radius c)) :
    y.val∈connectedComponentIn (BoundedZeroSource.Original (FormulaSignSlotRadialProviderBallConnections.equation c)) x.val ↔
      y.val∈connectedComponentIn (BoundedZeroSource.Bounded (FormulaSignSlotRadialProviderBallConnections.equation c)
        (FormulaSignSlotRadialProviderBallConnections.radius c)) x.val :=
  FormulaSignSlotRadialProviderBallConnections.component_iff c x y

#check FormulaSignSlotRadialProviderRecordEndpointRealization.exists_external_saved_realization
#check FormulaSignSlotRadialProviderRecordEndpointRealization.old_saved_realization
#print axioms FormulaSignSlotRadialProviderAtomic.mem_PSPACE
#print axioms FormulaSignSlotRadialProviderAtomic.provider_vertex_polynomial
#print axioms FormulaSignSlotRadialProviderRecordPlan.certifiedCallerBounds
#print axioms FormulaSignSlotRadialProviderRecordPlan.certified_prelude_key_realizes
#print axioms FormulaSignSlotRadialProviderRecordEndpointRealization.exists_external_saved_realization
#print axioms FormulaSignSlotRadialProviderRecordEndpointRealization.old_saved_realization
#print axioms FormulaSignSlotRadialProviderPair.spatial_shared
#print axioms FormulaSignSlotRadialProviderBallConnections.component_iff

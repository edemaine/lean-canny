import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCanonicalPoints
import LeanCanny.Encoding.FormulaSignSlotRadialProviderNoBadComplete
import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPhysical
import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPaddingPhysical

open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.Geometry
open LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
set_option backward.isDefEq.respectTransparency false

example : nativeReachLanguage∈PSPACE := native_reach_mem_PSPACE
example : nativeConnectedLanguage∈PSPACE := native_connected_mem_PSPACE

example (c : List Bool) : DepthComplete c
    (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.number c+3) :=
  depth_complete_terminal c

example (c a b : List Bool) (ha : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hb : FormulaSignSlotRadialProviderAtomic.Valid b)
    (hca : FormulaSignSlotRadialProviderAtomic.provider a=c)
    (hcb : FormulaSignSlotRadialProviderAtomic.provider b=c)
    (HE : pointAt c a ha hca=pointAt c b hb hcb) : RawReachable c a b :=
  raw_reachable_of_pointAt_eq c a b ha hb hca hcb HE

example (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (hab : FormulaSignSlotRadialProviderAtomic.field q hv (IntegralMixedRoadmapProper.producer false q)<
      FormulaSignSlotRadialProviderAtomic.field q hv (IntegralMixedRoadmapProper.producer true q)) :
    FormulaSignSlotRadialProviderProper.NoBad q ↔
      FormulaSignSlotRadialProviderProper.OriginalBadFree q hv :=
  FormulaSignSlotRadialProviderProper.noBad_iff_original_bad_free q hv hd hab

#check parent_slice_iff
#check parent_joinedIn
#check parentPoint_occurrence
#check terminal_pointAt_eq_of_joined
#check terminal_fiber_glue
#check FormulaSignSlotRadialProviderProperAppend.SampledLevel.local_geometric_point
#check FormulaSignSlotRadialProviderProperAppend.SampledLevel.padding_geometric_point

#print axioms native_reach_mem_PSPACE
#print axioms native_connected_mem_PSPACE
#print axioms label_reachable_iff
#print axioms connected_iff_native
#print axioms point_reachable_iff_raw
#print axioms identity_joined
#print axioms terminal_provider_fiber_finite
#print axioms terminal_pointAt_eq_of_joined
#print axioms terminal_fiber_glue
#print axioms depth_complete_terminal
#print axioms parent_slice_iff
#print axioms parent_joinedIn
#print axioms parentPoint_occurrence
#print axioms FormulaSignSlotRadialProviderProper.noBad_iff_original_bad_free
#print axioms FormulaSignSlotRadialProviderProperAppend.SampledLevel.local_geometric_point
#print axioms FormulaSignSlotRadialProviderProperAppend.SampledLevel.padding_geometric_point

#print axioms parent_source_proper
#print axioms canonical_height_mem_realCriticalValues
#print axioms canonical_child_partials
#print axioms providerPoint_slice_image
#print axioms providerPoint_joined_iff
#print axioms providerPoint_eq_pointAt_of_native_heq

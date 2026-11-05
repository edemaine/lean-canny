import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstSeedConstruct
import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicReplayFields
import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPastCut
import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayRetention
import LeanCanny.Encoding.FormulaSignSlotRadialProviderCrossPoint

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotRadialProviderAtomic

example (q : List Bool) (hv : Valid q) :
    IntegralMixedAtomicOccurrence.Occurrence (source q) (depth q) (levels q hv) (point q hv) :=
  occurrence q hv

example (q : List Bool) (hv : Valid q) :
    ∀i<FormulaSignSlotRadialExternalPrelude.number (provider q)+8,
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
        (pair (provider q) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (field q hv i)=0 :=
  MarkedPrelude.source_roots q hv

example (q : List Bool) (hv : Valid q) (he : FormulaSignSlotRadialExternalContext.external (provider q)) :
    ∃ha : FormulaSignSlotRadialExternalReplay.accepted (provider q),
      ∀i : Fin (FormulaSignSlotRadialExternalPrelude.number (provider q)),
        (BoundedRegularSource.markedProjection _ _ _ _ (MarkedPrelude.markedPoint q hv)).val i=
          FormulaSignSlotRadialExternalCoordinates.point (provider q)
            (FormulaSignSlotRadialExternalReplay.accepted_valid _ ha) i.val :=
  ReplayFields.external_projection q hv he

#check FormulaSignSlotRadialProviderFirstSeed.exists_external_seed
#check FormulaSignSlotRadialProviderFirstSeed.exists_old_seed
#check FormulaSignSlotRadialProviderRetainedAppend.past_fields
#check FormulaSignSlotRadialProviderRetainedAppend.past_critical
#check FormulaSignSlotRadialProviderRetainedAppend.past_cut_receipt
#check FormulaSignSlotRadialProviderAtomic.replay_of_initial_fields
#check FormulaSignSlotRadialProviderCrossPoint.language_native_iff

#print axioms FormulaSignSlotRadialProviderAtomic.occurrence
#print axioms FormulaSignSlotRadialProviderAtomic.signature_readback
#print axioms FormulaSignSlotRadialProviderAtomic.MarkedPrelude.source_roots
#print axioms FormulaSignSlotRadialProviderAtomic.MarkedPrelude.markedPoint
#print axioms FormulaSignSlotRadialProviderAtomic.MarkedLanguage.holds_of_equations
#print axioms FormulaSignSlotRadialProviderAtomic.ReplayFields.external_projection
#print axioms FormulaSignSlotRadialProviderAtomic.ReplayFields.old_projection
#print axioms FormulaSignSlotRadialProviderFirstSeed.exists_external_seed
#print axioms FormulaSignSlotRadialProviderFirstSeed.exists_old_seed
#print axioms FormulaSignSlotRadialProviderRecordPrefix.creating_heq
#print axioms FormulaSignSlotRadialProviderRecordPrefix.cut_snapshot
#print axioms FormulaSignSlotRadialProviderRetainedAppend.past_fields
#print axioms FormulaSignSlotRadialProviderRetainedAppend.past_critical
#print axioms FormulaSignSlotRadialProviderRetainedAppend.past_cut_receipt
#print axioms FormulaSignSlotRadialProviderAtomic.replay_of_initial_fields
#print axioms FormulaSignSlotRadialProviderCrossPoint.language_native_iff

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalCorrelation
/-! # Actual appended-command provenance removes the correlation active guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank tables

variable (q : List Bool)
  (r : IntegralMixedHistory.CriticalRule ((bank hn ht ha hR outer).parameters.ambient
    (pairFst (key n outer true q))))
  (hc : (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
    (bank hn ht ha hR outer).plan (pairFst (key n outer true q)) (birth n outer false q)).command=.critical r)

include hc in
theorem correlation_active :
    IntegralMixedFramedCriticalGuardBits.Active (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
      (stage n outer) (pair q []) :=by
  constructor
  · simp only [stage,IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair]
    have HB:=IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer true q
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HB
    rw [HB,IntegralMixedPhysicalCriticalPrefixes.consecutive]
    omega
  · rw [IntegralMixedFramedCriticalGuardBits.header_actual _ _ _ _ (represents hn ht ha hR outer)]
    have HH : (IntegralMixedCommandHeaderBits.command
        (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
          (bank hn ht ha hR outer).plan (pairFst (key n outer true q)) (birth n outer false q)).command).context=1 :=by
      rw [hc]
      rfl
    simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,stage] using
      (congrArg (fun z=>(IntegralMixedCommandHeaderBits.command
        (IntegralMixedFramedRootPullback.instructionAt (bank hn ht ha hR outer).parameters
          (bank hn ht ha hR outer).plan (pairFst (key n outer true z)) (birth n outer false z)).command).context)
        (pairFst_pair q [])).trans HH

include hc in
theorem correlation_creating_column :
    IntegralMixedFramedCriticalGuardBits.physical (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
      (stage n outer) (pair q [])=
    IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (bank hn ht ha hR outer).parameters
        (bank hn ht ha hR outer).plan (pairFst (key n outer true q)))
      ((bank hn ht ha hR outer).plan.rules (pairFst (key n outer true q))) (birth n outer false q))+
        r.offset.val+r.coordinate%((bank hn ht ha hR outer).parameters.ambient
          (pairFst (key n outer true q))-r.offset.val+1) :=by
  have HE : IntegralMixedFramedCriticalGuardBits.physical (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
      (stage n outer) (pair q [])=
    IntegralMixedFramedCriticalGuardBits.physical (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (key n outer true) (birth n outer false) q :=by
    simp only [IntegralMixedFramedCriticalGuardBits.physical,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralMixedFramedCriticalGuardBits.header,stage,IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair]
  rw [HE]
  exact IntegralMixedFramedCriticalGuardBits.physical_at_critical _ _ _ _ (represents hn ht ha hR outer)
    (key n outer true) (birth n outer false) q r hc

noncomputable def newestPoint (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) : ℝ :=
  IntegralFramedPhysicalSquare.point (bank hn ht ha hR outer).parameters
    (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
    (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
    (key n outer true) (positive hn ht ha hR outer true) q v hv
    ⟨0,positive hn ht ha hR outer true q⟩

noncomputable def creatingSelected (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) : ℝ :=
  IntegralMixedFramedBankObservation.extend
    (IntegralFramedPhysicalSquare.joint (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
      (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
      (key n outer true) (positive hn ht ha hR outer true) q v hv)
    (IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (bank hn ht ha hR outer).parameters
        (bank hn ht ha hR outer).plan (pairFst (key n outer true q)))
      ((bank hn ht ha hR outer).plan.rules (pairFst (key n outer true q))) (birth n outer false q))+
        r.offset.val+r.coordinate%((bank hn ht ha hR outer).parameters.ambient
          (pairFst (key n outer true q))-r.offset.val+1))^
    UniformIntegralPowerSchedule.physical ((bank hn ht ha hR outer).parameters.cap
      (pairFst (key n outer true q))+1)
      (2^(bank hn ht ha hR outer).parameters.width (pairFst (key n outer true q))) (birth n outer false q)

include hc in
theorem correlation_iff_creating (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) :
    correlation hn ht ha hR outer (pair q v)=InfinitesimalSign.encode 0 ↔
      newestPoint hn ht ha hR outer q v hv=creatingSelected hn ht ha hR outer q r v hv :=by
  have HA:=correlation_active hn ht ha hR outer q r hc
  rw [correlation_iff_newest hn ht ha hR outer q v hv HA]
  change newestPoint hn ht ha hR outer q v hv=_ ↔ _
  apply Iff.of_eq
  apply congrArg (fun z : ℝ=>newestPoint hn ht ha hR outer q v hv=z)
  unfold creatingSelected IntegralMixedFramedBankObservation.extend
  rw [←correlation_creating_column hn ht ha hR outer q r hc]
  have HL:=IntegralMixedFramedCriticalGuardBits.physical_lt (bank hn ht ha hR outer).parameters
    (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
    (represents hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
    (stage n outer) (pair q []) HA
  have HL':=HL
  rw [guard_count hn ht ha hR outer q []] at HL'
  change _<IntegralFramedPhysicalSquare.count (bank hn ht ha hR outer).parameters
    (bank hn ht ha hR outer).plan (key n outer true q) at HL'
  rw [dite_eq_left HL']
  simp only [IntegralMixedFramedCriticalGuardBits.physicalPower,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,stage,pairFst_pair]
  rfl

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalIntervalReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalCreatingCorrelation
/-! # Interval endpoints belong to the same fixed parent word

The all-old-bank equality scan transports the two chronological endpoint
labels to the child. The appended chronological label reads newest index0.
-/
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
local notation "B" => bank hn ht ha hR outer
local notation "T" => tables hn ht ha hR outer

theorem env_old (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (i : ℕ) (hi : i<birth n outer false q) :
    IntegralFramedPhysicalBankTerm.env (childBank hn ht ha hR outer) T (represents hn ht ha hR outer) q v hv i=
      IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR outer true q v hv
        (birth n outer false q-1-i) :=by
  have HA : i<(IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (key n outer true q)).count :=by
    change i<(IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth (key n outer true q)
    rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer,
      IntegralMixedPhysicalCriticalPrefixes.consecutive]
    omega
  have HP:=IntegralFramedPhysicalBankTerm.env_coordinate (childBank hn ht ha hR outer) T
    (represents hn ht ha hR outer) q v hv i HA
  refine HP.trans ?_
  unfold IntegralMixedPhysicalCriticalBankEquality.point
  apply congrArg (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (key n outer true) (positive hn ht ha hR outer true) q v hv)
  apply Fin.ext
  rw [IntegralFramedPhysicalIntegerLeaves.coordinate_packet,
    IntegralMixedPhysicalCriticalBankEquality.coordinate_val hn ht ha hR outer true q _ 0 (by omega)]
  change (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth
    (key n outer true q)-1-i=birth n outer false q-1-i+1
  rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer,
    IntegralMixedPhysicalCriticalPrefixes.consecutive]
  omega

theorem env_newest (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) :
    IntegralFramedPhysicalBankTerm.env (childBank hn ht ha hR outer) T (represents hn ht ha hR outer) q v hv
      (birth n outer false q)=newestPoint hn ht ha hR outer q v hv :=by
  have HA : birth n outer false q<
      (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (key n outer true q)).count :=by
    change _<(IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth (key n outer true q)
    rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer,
      IntegralMixedPhysicalCriticalPrefixes.consecutive]
    omega
  have HP:=IntegralFramedPhysicalBankTerm.env_coordinate (childBank hn ht ha hR outer) T
    (represents hn ht ha hR outer) q v hv (birth n outer false q) HA
  refine HP.trans ?_
  unfold newestPoint
  apply congrArg (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (key n outer true) (positive hn ht ha hR outer true) q v hv)
  apply Fin.ext
  rw [IntegralFramedPhysicalIntegerLeaves.coordinate_packet]
  change (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth
    (key n outer true q)-1-birth n outer false q=0
  rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer,
    IntegralMixedPhysicalCriticalPrefixes.consecutive]
  omega

noncomputable def endpointValue (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (i : ℕ) : ℝ :=
  IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR outer false q
    (IntegralMixedPhysicalCriticalQuery.parentWord q) hp (birth n outer false q-1-i)

theorem interval_iff_parent (q v : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (hg : Guard n outer q) (haq : IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR outer (pair q v)) :
    (value hn ht ha hR outer false (pair q v)=InfinitesimalSign.encode 1 ∧
      value hn ht ha hR outer true (pair q v)=InfinitesimalSign.encode 1) ↔
    endpointValue hn ht ha hR outer q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q))<
        newestPoint hn ht ha hR outer q v hv ∧
      newestPoint hn ht ha hR outer q v hv<
        endpointValue hn ht ha hR outer q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q)) :=by
  have HB:=IntegralMixedPhysicalCriticalPrefixes.birth_pos n outer false q
  have HE:=(IntegralMixedPhysicalCriticalBankEquality.agrees_iff hn ht ha hR outer q v hp hv).mp haq
  rw [interval_iff hn ht ha hR outer q v hv hg]
  dsimp only
  rw [env_old hn ht ha hR outer q v hv _ hg.2.1,env_old hn ht ha hR outer q v hv _ hg.2.2,
    env_newest hn ht ha hR outer q v hv,←HE _ (by omega),←HE _ (by omega)]
  rfl

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval

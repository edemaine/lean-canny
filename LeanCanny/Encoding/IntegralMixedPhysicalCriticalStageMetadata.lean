/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalCreatingCorrelation
public import LeanCanny.Geometry.IntegralMixedPrefixPointReadback
public import LeanCanny.Geometry.IntegralMixedAtomicFrameRecord
/-! # Literal metadata of the appended point-rule probe

Header and column equalities take values in source-independent types. This
retains the actual parent source without casting its algebra or frame.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra
theorem PrefixFrozen.pointData_selected {n m : ℕ} (F : Frame n) (HP : PrefixFrozen F)
    (HA : AtomicRows F m) (h : Fin (n+1)) (hh : h∉F.frozen) :
    (HA.pointData h h hh hh).rule.offset.val+
      (HA.pointData h h hh hh).rule.coordinate%(n-(HA.pointData h h hh hh).rule.offset.val+1)=h.val :=by
  rw [HA.pointData_rule]
  have HE:=congrArg Fin.val (pointRule_index F h hh h hh)
  rw [HP.permutation] at HE
  exact HE
end LeanCanny.Geometry.IntegralMixedFrozenFrame

namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalCriticalPrefixes (birth key)
open IntegralMixedFramedHistoryFamilyBits (family commands instruction prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank tables
local notation "B" => bank hn ht ha hR outer
local notation "T" => tables hn ht ha hR outer

theorem stage_parent (q : List Bool) : stage n outer (pair q [])=
    prefixLength (B).parameters (key n outer false q) :=by
  have HE:=IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer false q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
  simpa only [stage,pairFst_pair] using HE.symm

theorem root_parent (q : List Bool) :
    pairFst (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true) (pair q []))=
      pairFst (key n outer false q) :=by
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,key,
    IntegralMixedFramedHistoryFamilyBits.keyAt,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]

private noncomputable def headerAt (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (root : List Bool) (j : ℕ) : IntegralMixedCommandHeaderBits.Header :=
  IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D root j).command

theorem header_parent (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.header T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q [])=
    IntegralMixedCommandHeaderBits.command (instruction (B).parameters (B).plan (key n outer false q)).command :=by
  rw [IntegralMixedFramedCriticalGuardBits.header_actual _ _ _ _ (represents hn ht ha hR outer)]
  exact congrArg₂ (headerAt (B).parameters (B).plan)
    (root_parent (n:=n) outer q) (stage_parent hn ht ha hR outer q)

private noncomputable def arityAt (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (root : List Bool) (j : ℕ) : ℕ :=
  IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryScript.paddedPast
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) j)

theorem prefix_arity_parent (q : List Bool) :
    IntegralMixedFramedPhysicalIndex.prefixArity (B).parameters T
      (IntegralMixedFramedCriticalGuardBits.packet
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []))=
      IntegralMixedFramedPhysicalIndex.arity (commands (B).parameters (B).plan (key n outer false q)) :=by
  unfold IntegralMixedFramedCriticalGuardBits.packet
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet _ _ _ _ (represents hn ht ha hR outer)]
  exact congrArg₂ (arityAt (B).parameters (B).plan)
    (root_parent (n:=n) outer q) (stage_parent hn ht ha hR outer q)

theorem power_parent (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q [])=
      UniformIntegralPowerSchedule.physical ((family (B).parameters (B).plan (B).data).cap (key n outer false q))
        (2^(family (B).parameters (B).plan (B).data).width (key n outer false q))
        ((family (B).parameters (B).plan (B).data).birth (key n outer false q)) :=by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [root_parent (n:=n) outer q,stage_parent hn ht ha hR outer q,
    IntegralMixedFramedHistoryFamilyBits.family_birth]
  rfl

theorem child_key (q : List Bool) : key n outer true q=
    IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst (key n outer false q))
      (prefixLength (B).parameters (key n outer false q)+1) q :=by
  have HE:=IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer false q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
  rw [HE,←IntegralMixedPhysicalCriticalPrefixes.consecutive]
  simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]

theorem parent_room (q : List Bool) : prefixLength (B).parameters (key n outer false q)≤
    (B).parameters.cap (pairFst (key n outer false q)) :=by
  have HE:=IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer false q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
  rw [HE]
  have HR:=IntegralMixedPhysicalCriticalPrefixes.below_cap hn ht ha hR outer false q
  simpa only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair] using HR.le

theorem active_parent (q : List Bool)
    (r : IntegralMixedHistory.CriticalRule ((B).parameters.ambient (pairFst (key n outer false q))))
    (hc : (instruction (B).parameters (B).plan (key n outer false q)).command=.critical r) :
    IntegralMixedFramedCriticalGuardBits.Active (B).parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []) :=by
  constructor
  · simp only [stage,IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair]
    have HE:=IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer true q
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HE
    rw [HE,IntegralMixedPhysicalCriticalPrefixes.consecutive]
    omega
  · rw [header_parent hn ht ha hR outer q,hc]
    rfl

theorem physical_pointRule (q : List Bool)
    (F : IntegralMixedFrozenFrame.Frame ((B).parameters.ambient (pairFst (key n outer false q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (B).parameters (B).plan (B).data).birth (key n outer false q)))
    (h : Fin ((B).parameters.ambient (pairFst (key n outer false q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (B).parameters (B).plan (key n outer false q)).command=.critical (HA.pointData h h hh hh).rule) :
    IntegralMixedFramedCriticalGuardBits.physical (B).parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q [])=
      IntegralMixedFramedPhysicalIndex.arity (commands (B).parameters (B).plan (key n outer false q))+h.val :=by
  unfold IntegralMixedFramedCriticalGuardBits.physical
  rw [prefix_arity_parent hn ht ha hR outer q,header_parent hn ht ha hR outer q,hc]
  change _+(HA.pointData h h hh hh).rule.offset.val+
    (HA.pointData h h hh hh).rule.coordinate%(_-(HA.pointData h h hh hh).rule.offset.val+1)=_
  rw [Nat.add_assoc,HP.pointData_selected F HA h hh]

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval

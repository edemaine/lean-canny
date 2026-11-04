/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalPointRecord
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalLanguageCorrectness
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalCommand
/-! # Actual chronological critical probes select the geometric coarse frame -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalCriticalPrefixes (birth key input)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open IntegralMixedPhysicalMarkedPlan (bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank
local notation "B"=>bank hn ht ha hR outer
local notation "G"=>family (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "N"=> IntegralCriticalHistoryTask.Parameters.ambient (IntegralFramedBankQuery.Bank.parameters B)

noncomputable def frame (q labels : List Bool) (H : IntegralMixedChronologicalFrameCode.Good
    (N (IntegralMixedPhysicalCriticalQuery.root q)) (birth n outer false q) labels) :=
  (IntegralMixedChronologicalFrameCode.descriptor _ _ labels H).frame

theorem command (q ctx w labels : List Bool) (a b h : ℕ)
    (HG : IntegralMixedChronologicalFrameCode.PointGood
      (N (IntegralMixedPhysicalCriticalQuery.root q)) (birth n outer false q) labels h h)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx
      (IntegralMixedChronologicalFrameCode.code (N (IntegralMixedPhysicalCriticalQuery.root q)) labels h h) w a b) :
    (IntegralMixedFramedRootPullback.instructionAt (B).parameters (B).plan
      (IntegralMixedPhysicalCriticalQuery.root q) (birth n outer false q)).command=
      .critical ((IntegralMixedChronologicalFrameCode.descriptor _ _ labels HG.1).atomic.pointData
        ⟨h,HG.2.2.1⟩ ⟨h,HG.2.2.1⟩
        (by rw [IntegralMixedChronologicalFrame.Descriptor.frozen_mem,
          IntegralMixedChronologicalFrameCode.descriptor_length];exact Nat.not_lt_of_ge HG.2.1)
        (by rw [IntegralMixedChronologicalFrame.Descriptor.frozen_mem,
          IntegralMixedChronologicalFrameCode.descriptor_length];exact Nat.not_lt_of_ge HG.2.1)).rule :=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor _ _ labels HG.1
  let hh : (⟨h,HG.2.2.1⟩ : Fin (N (IntegralMixedPhysicalCriticalQuery.root q)+1))∉d.frame.frozen:=by
    rw [d.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length]
    exact Nat.not_lt_of_ge HG.2.1
  have HC:=IntegralMixedPhysicalCriticalCommand.packet_command hn ht ha hR outer q
    (IntegralMixedChronologicalFrameCode.rawData _ _ labels h h HG) ctx w a b rfl
    (hq.trans (congrArg (fun c=>IntegralMixedPhysicalCriticalQuery.packet ctx c w a b)
      (IntegralMixedChronologicalFrameCode.rawData_code _ _ labels h h HG).symm))
  have HD : (IntegralMixedChronologicalFrameCode.rawData _ _ labels h h HG).rule=
      (d.atomic.pointData ⟨h,HG.2.2.1⟩ ⟨h,HG.2.2.1⟩ hh hh).rule:=by
    rw [d.atomic_pointData]
    rfl
  rw [HD] at HC
  exact HC

private theorem command_transport (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (k : List Bool) (r : List Bool) (b : ℕ)
    (hr : r=pairFst k) (hb : b=IntegralMixedFramedHistoryFamilyBits.prefixLength P k)
    (labels : List Bool) (h : ℕ)
    (HG : IntegralMixedChronologicalFrameCode.PointGood (P.ambient r) b labels h h)
    (HC : (IntegralMixedFramedRootPullback.instructionAt P D r b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData _ _ labels h h HG).rule)
    (HK : IntegralMixedChronologicalFrameCode.PointGood (P.ambient (pairFst k))
      (IntegralMixedFramedHistoryFamilyBits.prefixLength P k) labels h h) :
    (instruction P D k).command=.critical (IntegralMixedChronologicalFrameCode.rawData _ _ labels h h HK).rule :=by
  subst r
  subst b
  exact HC

private theorem raw_rule_birth {n a b : ℕ} (he : a=b) (labels : List Bool) (h : ℕ)
    (HA : IntegralMixedChronologicalFrameCode.PointGood n a labels h h)
    (HB : IntegralMixedChronologicalFrameCode.PointGood n b labels h h) :
    (IntegralMixedChronologicalFrameCode.rawData n a labels h h HA).rule=
      (IntegralMixedChronologicalFrameCode.rawData n b labels h h HB).rule :=by
  cases he
  rfl

theorem command_key (q ctx w labels : List Bool) (a b h : ℕ)
    (HG : IntegralMixedChronologicalFrameCode.PointGood (N (pairFst (key n outer false q)))
      ((G).birth (key n outer false q)) labels h h)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx
      (IntegralMixedChronologicalFrameCode.code (N (pairFst (key n outer false q))) labels h h) w a b) :
    (instruction (B).parameters (B).plan (key n outer false q)).command=
      .critical ((IntegralMixedChronologicalFrameCode.descriptor _ _ labels HG.1).atomic.pointData
        ⟨h,HG.2.2.1⟩ ⟨h,HG.2.2.1⟩
        (by rw [IntegralMixedChronologicalFrame.Descriptor.frozen_mem,
          IntegralMixedChronologicalFrameCode.descriptor_length];exact Nat.not_lt_of_ge HG.2.1)
        (by rw [IntegralMixedChronologicalFrame.Descriptor.frozen_mem,
          IntegralMixedChronologicalFrameCode.descriptor_length];exact Nat.not_lt_of_ge HG.2.1)).rule :=by
  have HR : IntegralMixedPhysicalCriticalQuery.root q=pairFst (key n outer false q):=by
    simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
  have HB : birth n outer false q=IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters
      (key n outer false q):=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth (B).parameters (B).plan (B).data]
    exact (IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer false q).symm
  have HK : IntegralMixedChronologicalFrameCode.PointGood
      (N (IntegralMixedPhysicalCriticalQuery.root q)) (birth n outer false q) labels h h:=by
    rw [HR,←IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer false q]
    exact HG
  have HQ : q=IntegralMixedPhysicalCriticalQuery.packet ctx
      (IntegralMixedChronologicalFrameCode.code (N (IntegralMixedPhysicalCriticalQuery.root q)) labels h h) w a b:=by
    rw [HR]
    exact hq
  have HC:=IntegralMixedPhysicalCriticalCommand.packet_command hn ht ha hR outer q
    (IntegralMixedChronologicalFrameCode.rawData _ _ labels h h HK) ctx w a b rfl
    (HQ.trans (congrArg (fun c=>IntegralMixedPhysicalCriticalQuery.packet ctx c w a b)
      (IntegralMixedChronologicalFrameCode.rawData_code _ _ labels h h HK).symm))
  have HP : IntegralMixedChronologicalFrameCode.PointGood (N (pairFst (key n outer false q)))
      (IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters (key n outer false q)) labels h h:=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth (B).parameters (B).plan (B).data]
    exact HG
  have HE:=command_transport (B).parameters (B).plan (key n outer false q) _ _ HR HB labels h HK HC HP
  rw [(IntegralMixedChronologicalFrameCode.descriptor _ _ labels HG.1).atomic_pointData]
  change (instruction (B).parameters (B).plan (key n outer false q)).command=
    .critical (IntegralMixedChronologicalFrameCode.rawData _ _ labels h h HG).rule
  exact HE.trans (congrArg IntegralMixedFullHistoryScript.Command.critical
    (raw_rule_birth (IntegralMixedFramedHistoryFamilyBits.family_birth (B).parameters (B).plan (B).data
      (key n outer false q)).symm labels h HP HG))

theorem empty_iff (q ctx w labels : List Bool) (a b h : ℕ)
    (HG : IntegralMixedChronologicalFrameCode.PointGood (N (pairFst (key n outer false q)))
      ((G).birth (key n outer false q)) labels h h)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx
      (IntegralMixedChronologicalFrameCode.code (N (pairFst (key n outer false q))) labels h h) w a b)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hg : IntegralMixedPhysicalCriticalInterval.Guard n outer q)
    (hn0 : 0<(G).ambient (key n outer false q)) (charge : ℕ)
    (hd : ((G).spatial (key n outer false q)).degree=BoundedZeroSource.powerDegree charge) :
    q∉IntegralMixedPhysicalCriticalInterval.language hn ht ha hR outer ↔
      Disjoint (Set.Ioo
        (IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha hR outer q hp
          (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q)))
        (IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha hR outer q hp
          (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))))
        (IntegralMixedFrozenFrame.realCriticalValues ((G).spatial (key n outer false q))
          (IntegralMixedFrozenFrame.line (IntegralMixedChronologicalFrameCode.descriptor _ _ labels HG.1).frame
            ⟨h,HG.2.2.1⟩)
          (IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha hR outer q hp) ⟨h,HG.2.2.1⟩) :=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor _ _ labels HG.1
  have hh : (⟨h,HG.2.2.1⟩ : Fin (N (pairFst (key n outer false q))+1))∉d.frame.frozen:=by
    rw [d.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length]
    exact Nat.not_lt_of_ge HG.2.1
  exact IntegralMixedPhysicalCriticalInterval.not_language_iff_disjoint hn ht ha hR outer q hp hg
    d.frame d.prefix_frozen d.free_normal d.atomic _ hh
    (command_key hn ht ha hR outer q ctx w labels a b h HG hq) hn0 charge hd
    ((G).scalar_cap (key n outer false q))

end LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical

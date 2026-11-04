/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalRule
public import LeanCanny.Algebra.IntegralMixedNumericalSweepBad
/-! # Genuine canonical bad-free intervals satisfy the actual native NoBad guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem bad_source_transport {a b S B m T C l :ℕ} {P :SpatialSource a} {Q :SpatialSource b} {ι κ :Type}
    (hab :a=b) (hP :HEq P Q) (x :State P S B m ι) (hm :m≤S) (y :State Q T C l κ) (hl :l≤T)
    (r :Rule a) (s :Rule b) (hr :r.slope=commonDenominator x) (hs :s.slope=commonDenominator y)
    (hoff :r.critical.offset.val=s.critical.offset.val) (hobj :r.critical.objective=s.critical.objective)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (ψ :y.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values :Fin m→ℝ) (other :Fin l→ℝ)
    (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (K :∀i,ψ (y.bank.numerator i)/(y.bank.denominator i:ℝ)=other i)
    (HN :∀i,i<r.critical.offset.val→IntegralMixedNumericalSweep.normalized r values i=
      IntegralMixedNumericalSweep.normalized s other i)
    (old :IntegralMixedRelativeCuts.Choices x hm r φ) (next :IntegralMixedRelativeCuts.Choices y hl s ψ) (v :ℝ):
    v∈IntegralMixedSelectedCriticalCuts.bad y hl s ψ next↔v∈IntegralMixedSelectedCriticalCuts.bad x hm r φ old:=by
  subst b
  have HQ :P=Q:=eq_of_heq hP
  subst Q
  exact IntegralMixedNumericalSweep.bad_iff x hm y hl r s hr hs (Fin.ext hoff) hobj φ ψ values other H K HN old next v

private theorem source_rename_id {a :ℕ} (Q :SpatialSource a):
    IntegralMixedCoordinateRename.spatial Q (Equiv.refl _)=Q:=by
  cases Q
  simp only [IntegralMixedCoordinateRename.spatial,Equiv.refl_symm,Equiv.coe_refl,MvPolynomial.rename_id,AlgHom.id_apply]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapLocalFrame.field IntegralMixedRoadmapBadProbeParent.snapshot
  IntegralMixedMarkedPrefixFieldReadback.parentPoint IntegralMixedPrefixSnapshot.Data.bad

private theorem original_bad_selected (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HR :IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (IntegralMixedRoadmapLocalFrame.rowKey q))
    (φ :((G).state (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ :∀i,φ (((G).state (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
          ((G).birth (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)-1-i.val))
    (choices :IntegralMixedRelativeCuts.Choices ((G).state (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)) φ) (v :ℝ):
    v∈IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)
      (IntegralMixedRoadmapAtomic.word q) (IntegralMixedRoadmapProper.labels q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)↔
    v∈IntegralMixedSelectedCriticalCuts.bad ((G).state (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)) φ choices:=by
  let key:=IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q
  let fields:=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
  have HS:=IntegralMixedRoadmapLocalFrame.old_snapshot_original hn ht ha hR0 q hv
  have HB :(G).birth key=IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q):=
    (congrArg IntegralMixedPrefixSnapshot.Data.birth HS).trans
      (IntegralMixedRoadmapBadProbeParent.birth hn ht ha hR0 _
        (IntegralMixedRoadmapLocalFrame.bad_record_positive hn ht ha hR0 q hv))
  have HE:=IntegralMixedPrefixSnapshot.Data.bad_transport _ _ HS (IntegralMixedRoadmapProper.labels q)
    (fun i=>fields ((G).birth key-1-i))
    (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)
      (IntegralMixedRoadmapAtomic.word q) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv))
    (fun i hi=>(congrArg fields (congrArg (fun b :ℕ=>b-1-i) HB)).trans
      (IntegralMixedRoadmapLocalFrame.bad_parent_values hn ht ha hR0 q hv i (hi.trans_eq HB)).symm)
  have HSelected:=IntegralMixedRoadmapLocalFrame.old_bad_iff hn ht ha hR0 q hv HR φ Hφ choices v
  have HMem:=Iff.of_eq (congrArg (fun s :Set ℝ=>v∈s) HE)
  exact HMem.symm.trans HSelected

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "CR"=>cutRule x (Descriptor.frame d) (next d hk) g hg
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "a"=>left.value V
local notation "b"=>right.value V
noncomputable local instance properAppendLocalBadIndexFintype :Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) oldCs):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapProperParent.hom IntegralMixedRoadmapProperRow.parentKey

private theorem bad_canonical_offset :(CR).critical.offset.val=IntegralMixedRoadmapAtomic.depth old+1:=
  (frozen_card d hk).trans (congrArg (·+1)
    (IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he))

private theorem bad_canonical_objective :(CR).critical.objective=0:=by
  change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm g).val-(frame d hk).frozen.card=0
  rw [(prefix_frozen d hk).permutation,frozen_card]
  have H:=IntegralMixedRoadmapProperParent.objective_value hn ht ha hR0 old hv hd
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  omega

/-- Only genuine mathematical canonical bad-freeness is supplied. All native
probes, exact coefficient guards, words and interpreting homs are internal. -/
theorem WordReceipt.no_bad_of_canonical {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (hab :a<b)
    (havoid :∀v,v∈Set.Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm CR phi
      (IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd)):
    IntegralMixedRoadmapProper.NoBad hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word):=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  let j:=IntegralMixedRoadmapAtomic.depth q
  let key:=IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q
  let fields:=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hV
  have HD :0<IntegralMixedRoadmapAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  have HJ :IntegralMixedRoadmapAtomic.depth old+1≤j:=by dsimp only [j,q];rw [depth_packet]
  have HJN :j≤D:=by
    have H:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hV
    dsimp only [q] at H
    rw [dimension_packet] at H
    exact H
  have HR:=IntegralMixedRoadmapProperRow.row_good_of_valid hn ht ha hR0 q hV HD j le_rfl
    (by dsimp only [q];rw [dimension_packet];exact HJN)
  obtain ⟨ψ,Hψ⟩:=IntegralMixedRoadmapProperRow.exists_original_interpretation hn ht ha hR0 q hV j
  let choices:=Classical.choice (IntegralMixedRelativeCuts.exists_choices ((G).state key) ((G).birth_bound key) ((G).rule key) ψ)
  have HO:=bad_canonical_offset hn ht ha hR0 old hv hd
  have HSource :HEq Q ((G).spatial key):=by
    have HE :IntegralMixedCoordinateRename.spatial Q (FrozenCoordinateOrdering.permutation (frame d hk).frozen)=Q:=by
      rw [(prefix_frozen d hk).permutation]
      exact source_rename_id Q
    exact ((row_source hn ht ha hR0 old hv hd left right R side W.word j).trans (heq_of_eq HE)).symm
  have HBad (v :ℝ):v∈IntegralMixedSelectedCriticalCuts.bad ((G).state key) ((G).birth_bound key)
      ((G).rule key) ψ choices↔v∈IntegralMixedSelectedCriticalCuts.bad x hm CR phi
        (IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd):=by
    exact bad_source_transport
      (row_ambient hn ht ha hR0 old hv hd left right R side W.word j).symm HSource
      x hm ((G).state key) ((G).birth_bound key) CR ((G).rule key) rfl
      (row_current hn ht ha hR0 old hv hd left right R side W.word hV j HJ HJN)
      (HO.trans (row_offset hn ht ha hR0 old hv hd left right R side W.word hV j HJ HJN).symm)
      ((bad_canonical_objective hn ht ha hR0 old hv hd).trans
        (row_objective hn ht ha hR0 old hv hd left right R side W.word hV j HJ HJN).symm)
      phi ψ V (fun i :Fin ((G).birth key)=>fields ((G).birth key-1-i.val))
      (IntegralMixedRoadmapProperParent.hom_values hn ht ha hR0 old hv hd) Hψ
      (fun ell hell=>(W.row_normalized hn ht ha hR0 old hv hd left right R side hV hOld j HJ HJN ell
        (hell.trans_eq HO)).symm) (IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd) choices v
  have HE:=W.original_endpoint_fields hn ht ha hR0 old hv hd left right R side N hV
  have HEf :fields (IntegralMixedRoadmapProper.producer false q)=a ∧
      fields (IntegralMixedRoadmapProper.producer true q)=b:=HE
  have HOrder :fields (IntegralMixedRoadmapProper.producer false q)<fields (IntegralMixedRoadmapProper.producer true q):=by
    rw [HEf.1,HEf.2]
    exact hab
  apply (IntegralMixedRoadmapLocalFrame.noBad_iff_original_bad_free hn ht ha hR0 q hV HR HOrder).mpr
  intro v hvI hvBad
  have HI :v∈Set.Ioo a b:=by
    change v∈Set.Ioo (fields (IntegralMixedRoadmapProper.producer false q))
      (fields (IntegralMixedRoadmapProper.producer true q)) at hvI
    simpa only [HEf.1,HEf.2] using hvI
  exact havoid v HI ((HBad v).mp ((original_bad_selected hn ht ha hR0 q hV HR ψ Hψ choices v).mp hvBad))

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

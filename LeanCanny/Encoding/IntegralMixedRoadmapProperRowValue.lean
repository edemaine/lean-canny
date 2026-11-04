/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex
public import LeanCanny.Encoding.IntegralMixedRoadmapProperInputComposition
public import LeanCanny.Encoding.IntegralMixedRoadmapProperFieldReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # A row statistic's selected scalar is its own joint-word bank value -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  parent terminal creating context count IntegralFramedPhysicalSquare.point IntegralMixedPhysicalFieldEquality.point

private theorem point_fin_congr (Q : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan Q)
    (A : IntegralMixedFramedHistoryFamilyBits.Data Q E) (L F C : List Bool→ℕ)
    (h : IntegralMixedFramedStepHeight.FamilyInputs Q E L F C) (key : List Bool→List Bool)
    (hp hq : ∀z,0<(IntegralMixedFramedHistoryFamilyBits.family Q E A).birth (key z)) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E A L F C h key hp) z w)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E A L F C h key hq) z w)
    (i j : Fin ((IntegralMixedFramedHistoryFamilyBits.family Q E A).birth (key z))) (he : i.val=j.val) :
    IntegralFramedPhysicalSquare.point Q E A L F C h key hp z w hv i=
      IntegralFramedPhysicalSquare.point Q E A L F C h key hq z w hw j :=by
  have H : hp=hq:=Subsingleton.elim _ _
  subst hq
  have HI : i=j:=Fin.ext he
  subst j
  rfl

private theorem own_count (mode : Bool) (z : List Bool) :
    (G).birth (terminal hn ht ha hR0 mode z)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((BK).key (context hn ht ha hR0 mode z)) :=by
  unfold terminal
  exact IntegralMixedFramedHistoryFamilyBits.family_birth P BP BH _

private theorem own_scalar_value (mode : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 mode) (positive hn ht ha hR0 mode)) z w)
    (p : ℕ) (hp : p<(G).birth (terminal hn ht ha hR0 mode z)) :
    IntegralFramedPhysicalSquare.point P BP BH BL BF BC BS (terminal hn ht ha hR0 mode)
      (positive hn ht ha hR0 mode) z w hv ⟨(G).birth (terminal hn ht ha hR0 mode z)-1-p,by omega⟩=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (context hn ht ha hR0 mode z) w
        ((valid_at_context hn ht ha hR0 mode z w).mp hv) p :=by
  have HV:=(valid_at_context hn ht ha hR0 mode z w).mp hv
  have HF:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0)
    (context hn ht ha hR0 mode z) w HV p (hp.trans_eq (own_count hn ht ha hR0 mode z))
  rw [point_at_context hn ht ha hR0 mode z w hv HV]
  apply Eq.trans ?_ HF.symm
  have HT : terminal hn ht ha hR0 mode z=(BK).key (context hn ht ha hR0 mode z):=by
    unfold terminal;rfl
  have HC:=own_count hn ht ha hR0 mode z
  convert point_fin_congr P BP BH BL BF BC BS (BK).key (BK).positive
    (IntegralMixedPhysicalPointCompanionScan.full_positive hn ht ha (radius_binary hR0) false)
    (context hn ht ha hR0 mode z) w HV HV
    ⟨(G).birth (terminal hn ht ha hR0 mode z)-1-p,by rw [←HT];omega⟩
    ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength P ((BK).key (context hn ht ha hR0 mode z))-1-p,by
      rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
      have HPP:=hp.trans_eq HC
      omega⟩
    (congrArg (fun a : ℕ=>a-1-p) HC) using 1
  unfold terminal
  rfl

noncomputable def originalValue (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (p : ℕ):=
  IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) p

theorem native_scalar_value (mode right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 mode) (positive hn ht ha hR0 mode))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord mode u))
    (p : ℕ) (hp : p<creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u))
    (hfit : creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)≤
      (G).birth (terminal hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))) :
    IntegralFramedPhysicalSquare.point P BP BH BL BF BC BS (terminal hn ht ha hR0 mode)
      (positive hn ht ha hR0 mode) (IntegralMixedRoadmapProperRowWitness.key u)
      (IntegralMixedRoadmapProperRowWitness.ownWord mode u) hw
      ⟨(G).birth (terminal hn ht ha hR0 mode (IntegralMixedRoadmapProperRowWitness.key u))-1-p,by omega⟩=
      originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv p :=by
  have HF : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 mode u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
    cases mode
    · exact HL.2.2.2.2.1
    · exact HL.2.2.2.2.2
  obtain ⟨hL,hR,HE⟩:=IntegralMixedRoadmapProperRowWitness.fieldMatch_sound hn ht ha hR0 mode u HF
  exact (own_scalar_value hn ht ha hR0 mode _ _ hw p (hp.trans_le hfit)).trans (HE p hp).symm

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

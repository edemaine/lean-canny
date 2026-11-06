/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperInputComposition
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperFieldReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # A row statistic's selected scalar is its own joint-word bank value -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  parent terminal creating context count IntegralFramedPhysicalSquare.point FormulaSignSlotRadialProviderFieldEquality.point

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
    (G).birth (terminal mode z)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((BK).key (context mode z)) :=by
  unfold terminal
  exact IntegralMixedFramedHistoryFamilyBits.family_birth P BP BH _

private theorem point_value_comp (Q : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan Q)
    (J : IntegralMixedFramedHistoryFamilyBits.Data Q E) (LL FF CC : List Bool→ℕ)
    (hh : IntegralMixedFramedStepHeight.FamilyInputs Q E LL FF CC)
    (k l : List Bool→List Bool)
    (hk : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (k c))
    (hl : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (l c))
    (f : List Bool→List Bool) (he : k=l∘f) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E J LL FF CC hh k hk) c w)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E J LL FF CC hh l hl) (f c) w)
    (i : Fin ((IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (k c)))
    (j : Fin ((IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (l (f c))))
    (hij : i.val=j.val) :
    IntegralFramedPhysicalSquare.point Q E J LL FF CC hh k hk c w hv i=
      IntegralFramedPhysicalSquare.point Q E J LL FF CC hh l hl (f c) w hw j :=by
  subst k
  have HP : hk=(fun c=>hl (f c)):=Subsingleton.elim _ _
  subst hk
  have HI : i=j:=Fin.ext hij
  subst j
  exact congrFun (IntegralFramedPhysicalSquare.point_comp Q E J LL FF CC hh l hl f c w hv hw) i

private theorem own_scalar_value (mode : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (Input (terminal mode) (positive mode)) z w)
    (p : ℕ) (hp : p<(G).birth (terminal mode z)) :
    IntegralFramedPhysicalSquare.point P BP BH BL BF BC BS (terminal mode)
      (positive mode) z w hv ⟨(G).birth (terminal mode z)-1-p,by omega⟩=
      FormulaSignSlotRadialProviderFieldEquality.point (context mode z) w
        ((valid_at_context mode z w).mp hv) p :=by
  have HV:=(valid_at_context mode z w).mp hv
  have HP : p<FormulaSignSlotRadialProviderFieldEquality.count (context mode z):=by
    unfold FormulaSignSlotRadialProviderFieldEquality.count
    simpa only [terminal,Function.comp_apply] using hp
  have HF:=(FormulaSignSlotRadialProviderFieldEquality.point_env (context mode z) w HV p HP).trans
    (IntegralFramedPhysicalBankTerm.env_chronological BK FormulaSignSlotRadialProviderRecordPlan.tables
      FormulaSignSlotRadialProviderAtomic.bank_represents (context mode z) w HV p HP)
  have HX:=point_value_comp P BP BH BL BF BC BS (terminal mode) (BK).key
    (positive mode) (BK).positive (context mode) (by unfold terminal;rfl) z w hv HV
    ⟨(G).birth (terminal mode z)-1-p,by omega⟩
    ⟨(G).birth ((BK).key (context mode z))-1-p,by
      change (G).birth ((BK).key (context mode z))-1-p<FormulaSignSlotRadialProviderFieldEquality.count (context mode z)
      unfold FormulaSignSlotRadialProviderFieldEquality.count at *
      omega⟩ (by simp only [terminal,Function.comp_apply])
  exact HX.trans HF.symm

noncomputable def originalValue (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (p : ℕ):=
  FormulaSignSlotRadialProviderFieldEquality.point
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) p

theorem native_scalar_value (mode right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal mode) (positive mode))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord mode u))
    (p : ℕ) (hp : p<creating (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (hfit : creating (FormulaSignSlotRadialProviderProperRowWitness.key u)≤
      (G).birth (terminal mode (FormulaSignSlotRadialProviderProperRowWitness.key u))) :
    IntegralFramedPhysicalSquare.point P BP BH BL BF BC BS (terminal mode)
      (positive mode) (FormulaSignSlotRadialProviderProperRowWitness.key u)
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord mode u) hw
      ⟨(G).birth (terminal mode (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-p,by omega⟩=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv p :=by
  have HF : FormulaSignSlotRadialProviderProperRowWitness.fieldMatch mode u∈
      FormulaSignSlotRadialProviderFieldEqualityList.language:=by
    cases mode
    · exact HL.2.2.2.2.1
    · exact HL.2.2.2.2.2
  obtain ⟨hL,hR,HE⟩:=FormulaSignSlotRadialProviderProperRowWitness.fieldMatch_sound mode u HF
  exact (own_scalar_value mode _ _ hw p (hp.trans_le hfit)).trans (HE p hp).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow

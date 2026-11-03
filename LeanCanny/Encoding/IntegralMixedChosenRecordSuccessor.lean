/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordReadback
public import LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
public import LeanCanny.Encoding.IntegralMixedCausalCutDegree
/-! # Chosen critical and cut records are the actual local causal successor

Original word equality selects the creating record. The already interpreted
saved prefix supplies current Q. These identities combine with the correlated
critical/cut extension constructors; they assume no solvability of other rows.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P S hn hd hcap N T hz hT hroom))
local notation "D"=>plan P S hn hd hcap N T hz hT hroom

include hd hcap in
theorem spatial_cap_at (root : List Bool) (b : ℕ) :
    IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (S root (N root+b)).degree≤2^P.width root:=by
  rw [hd]
  exact hcap root

theorem critical_successor_at_bank (key : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count (pairFst key))
    (hk : prefixLength P key=N (pairFst key)+b)
    (d : IntegralMixedCriticalRecordConstructor.Data (P.ambient (pairFst key)) (N (pairFst key)+b))
    (hcode : IntegralMixedCausalRecordPlanBits.code (pairFst key) b=d.code) :
    let source:=S (pairFst key) (N (pairFst key)+b)
    let hc:=spatial_cap_at P S hd hcap N (pairFst key) b
    let record:=IntegralMixedCausalUnitRecordBits.record source (hn (pairFst key)) (N (pairFst key)+b) d.code hc
    let x:=(family P D H).state key
    instruction P D key=instantiate x record ∧
      record.template.command (commonDenominator x) (commonDenominator_ne_zero x)=.critical d.rule:=by
  refine ⟨(instruction_at_bank P S hn hd hcap N T hz hT hroom H key b hb hk).trans ?_,?_⟩
  · apply congrArg (instantiate ((family P D H).state key))
    unfold step
    rw [hcode]
  · exact IntegralMixedCriticalRecordConstructor.command_decode _ _ d _ _ _

theorem cut_successor_at_bank (key : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count (pairFst key))
    (hk : prefixLength P key=N (pairFst key)+b) (code : List Bool)
    (hcut : IntegralMixedUnitRecordCode.critical code=false) (d : ℕ)
    (hdegree : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1)
      (S (pairFst key) (N (pairFst key)+b)).degree)
    (hcode : IntegralMixedCausalRecordPlanBits.code (pairFst key) b=IntegralMixedCausalRecordDegree.withDegree code d) :
    let source:=S (pairFst key) (N (pairFst key)+b)
    let hc:=spatial_cap_at P S hd hcap N (pairFst key) b
    let record:=IntegralMixedCausalUnitRecordBits.record source (hn (pairFst key)) (N (pairFst key)+b)
      (IntegralMixedCausalRecordDegree.withDegree code d) hc
    let x:=(family P D H).state key
    let cut:=IntegralMixedCausalUnitRecordBits.cut source (hn (pairFst key)) (N (pairFst key)+b) code hc
    let Q:=commonDenominator x
    let hQ:=commonDenominator_ne_zero x
    instruction P D key=instantiate x record ∧
      record.template.command Q hQ=.cut (cut.rule Q hQ) (cut.kind Q hQ) d hdegree (hdegree.trans hc):=by
  refine ⟨(instruction_at_bank P S hn hd hcap N T hz hT hroom H key b hb hk).trans ?_,?_⟩
  · apply congrArg (instantiate ((family P D H).state key))
    unfold step
    rw [hcode]
  · exact IntegralMixedCausalRecordDegree.command _ _ _ code hcut d hdegree _ _ _

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend

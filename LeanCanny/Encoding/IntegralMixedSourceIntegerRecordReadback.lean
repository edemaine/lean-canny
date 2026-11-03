/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPrefix
public import LeanCanny.Algebra.IntegralMixedCausalPlanLookup
/-! # Chronological source records are instantiated at the actual saved bank

Both the creating source and affine reference birth come from the literal
record row. Instantiation inserts this saved prefix's common denominator,
not a denominator from a separately sampled or reinterpreted history.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>plan P S hn hd hcap N T hz hT hroom
local notation "I"=>preludePlan P S hd hcap N T hz hT hroom

noncomputable def causalRecords (root : List Bool) :=
  later P S hn hd hcap N root++IntegralMixedSourceIntegerPrelude.records P (fun root=>S root 0)
    (fun root=>(initial P I root).critical_cap) T N hz hT root

theorem causalRecords_length (root : List Bool) :
    (causalRecords P S hn hd hcap N T hz hT hroom root).length=
      IntegralMixedCausalRecordPlanBits.count root+N root:=by
  rw [causalRecords,List.length_append,later_length,IntegralMixedSourceIntegerPrelude.records_length]

theorem causalRecords_at (root : List Bool) (b : ℕ) (hb : b<IntegralMixedCausalRecordPlanBits.count root) :
    ((causalRecords P S hn hd hcap N T hz hT hroom root).reverse[N root+b]?)=
      some (step P S hn hd hcap N root b):=by
  rw [causalRecords,List.reverse_append,List.getElem?_append_right
    (by rw [List.length_reverse,IntegralMixedSourceIntegerPrelude.records_length]; omega),
    List.length_reverse,IntegralMixedSourceIntegerPrelude.records_length,
    show N root+b-N root=b by omega,later,List.reverse_reverse,List.getElem?_map,List.getElem?_range hb]
  rfl

theorem commands_causalRecords (root : List Bool) :
    (D).rules root=IntegralMixedCausalPlanBits.commands (initial P D root)
      (causalRecords P S hn hd hcap N T hz hT hroom root)
      (by rw [causalRecords_length]; have HR:=hroom root; omega):=rfl

variable (H : IntegralMixedFramedHistoryFamilyBits.Data P
  (plan P S hn hd hcap N T hz hT hroom))

private theorem run_denominator_congr {n cap B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State Q cap B 0 ι) (cs ds : List (Instruction n B))
    (hc : cs.length≤cap+1) (hd : ds.length≤cap+1) (he : cs=ds) :
    commonDenominator (run x cs hc)=commonDenominator (run x ds hd):=by
  cases he
  rfl

attribute [local irreducible] plan preludePlan causalRecords later step
  IntegralMixedSourceIntegerPrelude.records

theorem instruction_at_bank (key : List Bool) (b : ℕ)
    (hb : b<IntegralMixedCausalRecordPlanBits.count (pairFst key))
    (hk : prefixLength P key=N (pairFst key)+b) :
    instruction P D key=instantiate ((family P D H).state key)
      (step P S hn hd hcap N (pairFst key) b):=by
  let root:=pairFst key
  let rs:=causalRecords P S hn hd hcap N T hz hT hroom root
  have hlen : rs.length≤(P.cap root+1)+1:=by
    rw [causalRecords_length]
    have HR:=hroom root
    omega
  let bi : Fin rs.length:=⟨N root+b,by rw [causalRecords_length]; exact Nat.add_lt_add_left hb (N root) |>.trans_eq (Nat.add_comm _ _)⟩
  have HE : rs.reverse[bi.val]=step P S hn hd hcap N root b:=by
    have HL : bi.val<rs.reverse.length:=by rw [List.length_reverse]; exact bi.isLt
    have HT:=causalRecords_at P S hn hd hcap N T hz hT hroom root b hb
    exact Option.some.inj ((List.getElem?_eq_getElem HL).symm.trans HT)
  have HC:=IntegralMixedCausalPlanBits.chronological_instantiate (initial P D root) rs hlen
    (defaultInstruction P D root) bi
  rw [HE] at HC
  let old:=run (initial P D root)
    (paddedPast (defaultInstruction P D root) (IntegralMixedCausalPlanBits.commands (initial P D root) rs hlen) bi.val)
    (by rw [paddedPast_length]; exact bi.isLt.le.trans hlen)
  have HL : instruction P D key=
      (chronological (IntegralMixedCausalPlanBits.commands (initial P D root) rs hlen) bi.val).getD
        (defaultInstruction P D root):=by
    unfold instruction
    rw [commands_causalRecords P S hn hd hcap N T hz hT hroom,hk]
  have HI : instruction P D key=instantiate old (step P S hn hd hcap N root b):=
    HL.trans (congrArg (fun o=>o.getD (defaultInstruction P D root)) HC)
  have Hcommands : paddedPast (defaultInstruction P D root)
      (IntegralMixedCausalPlanBits.commands (initial P D root) rs hlen) bi.val=commands P D key:=by
    rw [←commands_causalRecords P S hn hd hcap N T hz hT hroom]
    exact congrArg (paddedPast (defaultInstruction P D root) ((D).rules root)) hk.symm
  have HQ : commonDenominator old=commonDenominator ((family P D H).state key):=
    run_denominator_congr (initial P D root) _ _ _
      (((family P D H).birth_bound key).trans (Nat.le_succ _)) Hcommands
  exact HI.trans (instantiate_congr old ((family P D H).state key) _ HQ)

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend

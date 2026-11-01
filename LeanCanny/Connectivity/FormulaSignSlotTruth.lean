/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotAtomicReplies
/-! # Arbitrary original Boolean truth equals native sign-label circuit truth -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotTruth
open ETR LeanCanny.Computation LeanCanny.Encoding BooleanCircuitSpace
open FormulaBooleanCircuitSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  FormulaView.normalize FormulaBooleanCircuitSource.node FormulaBooleanCircuitSource.gateTag
  FormulaBooleanCircuitSource.left FormulaBooleanCircuitSource.right

def frozenAtom (c label : List Bool) (q : List Bool) : Bool :=
  FormulaSignSlotCircuit.atom (pair (pair c label) (pairSnd q))

private theorem op_zero (a l r : Bool) : operation 0 a l r=false := by cases a <;> cases l <;> cases r <;> decide
private theorem op_atom (a l r : Bool) : operation 2 a l r=a := by cases a <;> cases l <;> cases r <;> decide
private theorem op_not (a l r : Bool) : operation 3 a l r= !l := by cases a <;> cases l <;> cases r <;> decide
private theorem op_and (a l r : Bool) : operation 4 a l r=(l&&r) := by cases a <;> cases l <;> cases r <;> decide
private theorem op_or (a l r : Bool) : operation 5 a l r=(l||r) := by cases a <;> cases l <;> cases r <;> decide

private theorem wire_binary (b : List Bool → Bool) (env : ℕ → ℝ)
    (c pre suffix : List Bool) (disjoin : Bool) (p q : Formula)
    (hc : FormulaView.normalize c=pre++(binary disjoin p q).encode++suffix)
    (hL : wireValue circuit b c (wire c (pre++header (binaryTag disjoin)))=decide (p.Holds env))
    (hR : wireValue circuit b c (wire c (pre++header (binaryTag disjoin)++p.encode))=decide (q.Holds env)) :
    wireValue circuit b c (wire c pre)=decide ((binary disjoin p q).Holds env) := by
  have ht : circuit.tag (pair c (BinaryNatCode.encode (wire c pre)))=binaryTag disjoin := by
    have H := gateTag_node _ (binary disjoin p q) (node_at c pre suffix (binary disjoin p q) hc)
    cases disjoin <;> exact H
  have hcL : FormulaView.normalize c=(pre++header (binaryTag disjoin))++p.encode++(q.encode++[true]++suffix) := by
    simpa only [encode_binary,List.append_assoc] using hc
  have hcR : FormulaView.normalize c=(pre++header (binaryTag disjoin)++p.encode)++q.encode++([true]++suffix) := by
    simpa only [encode_binary,List.append_assoc] using hc
  have hl := wire_child_lt c pre (header (binaryTag disjoin)) _ p hcL (by simp [header])
  have hr : wire c (pre++header (binaryTag disjoin)++p.encode)<wire c pre := by
    have HCR : FormulaView.normalize c=pre++(header (binaryTag disjoin)++p.encode)++q.encode++([true]++suffix) := by
      simpa only [List.append_assoc] using hcR
    simpa only [List.append_assoc] using wire_child_lt c pre (header (binaryTag disjoin)++p.encode)
      ([true]++suffix) q HCR (by simp [header])
  have hleft : circuit.left (pair c (BinaryNatCode.encode (wire c pre)))=wire c (pre++header (binaryTag disjoin)) :=
    left_binary_at c pre suffix disjoin p q hc
  have hright : circuit.right (pair c (BinaryNatCode.encode (wire c pre)))=wire c (pre++header (binaryTag disjoin)++p.encode) :=
    right_binary_at c pre suffix disjoin p q hc
  rw [wireValue_step,ht,hleft,hright,read_wire circuit b c _ _ hl,
    read_wire circuit b c _ _ hr,hL,hR]
  cases disjoin <;> simp only [binary,binaryTag,Bool.false_eq_true,ite_false,ite_true,
    op_and,op_or,Formula.Holds]
  all_goals by_cases HP : p.Holds env <;> by_cases HQ : q.Holds env <;> simp [HP,HQ]

private theorem wire_lt_count (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++p.encode++suffix) :
    wire (Input.field 2 c) pre < ClosedFormulaGateMetadata.count c := by
  have H : 0 < p.encode.length := by simp [Formula.encode]
  simp only [wire,ClosedFormulaGateMetadata.count,hc,List.length_append]
  omega

theorem wire_truth (c label : List Bool) (env : ℕ → ℝ)
    (H : (FormulaSignSlotSource.stratum (pair c label)).Holds env)
    (p : Formula) (pre suffix : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++p.encode++suffix)
    (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    wireValue circuit (frozenAtom c label) (Input.field 2 c) (wire (Input.field 2 c) pre)=decide (p.Holds env) := by
  induction p generalizing pre suffix with
  | falsum =>
    have ht : circuit.tag (pair (Input.field 2 c) (BinaryNatCode.encode (wire (Input.field 2 c) pre)))=0 :=
      gateTag_node _ Formula.falsum (node_at _ pre suffix .falsum hc)
    rw [wireValue_step,ht,op_zero]
    simp only [Formula.Holds,decide_false]
  | eqZero t =>
    have hn := node_at _ pre suffix (.eqZero t) hc
    have ht : circuit.tag (pair (Input.field 2 c) (BinaryNatCode.encode (wire (Input.field 2 c) pre)))=2 := gateTag_node _ (.eqZero t) hn
    rw [wireValue_step,ht,op_atom]
    simp only [frozenAtom,pairSnd_pair,Formula.Holds]
    apply FormulaSignSlotCircuit.atom_eq_zero c label _ (wire_lt_count c pre suffix _ hc) env H t
    · rw [FormulaSignSlotCircuit.readerQuery_pair]
      exact hn
    · exact hs
  | ltZero t =>
    have hn := node_at _ pre suffix (.ltZero t) hc
    have ht : circuit.tag (pair (Input.field 2 c) (BinaryNatCode.encode (wire (Input.field 2 c) pre)))=2 := gateTag_node _ (.ltZero t) hn
    rw [wireValue_step,ht,op_atom]
    simp only [frozenAtom,pairSnd_pair,Formula.Holds]
    apply FormulaSignSlotCircuit.atom_lt_zero c label _ (wire_lt_count c pre suffix _ hc) env H t
    · rw [FormulaSignSlotCircuit.readerQuery_pair]
      exact hn
    · exact hs
  | not p IH =>
    have ht : circuit.tag (pair (Input.field 2 c) (BinaryNatCode.encode (wire (Input.field 2 c) pre)))=3 :=
      gateTag_node _ (.not p) (node_at _ pre suffix (.not p) hc)
    have hcL : FormulaView.normalize (Input.field 2 c)=(pre++header 3)++p.encode++([true]++suffix) := by
      simpa only [encode_not,List.append_assoc] using hc
    have hl := wire_child_lt (Input.field 2 c) pre (header 3) _ p hcL (by simp [header])
    have hleft : circuit.left (pair (Input.field 2 c) (BinaryNatCode.encode (wire (Input.field 2 c) pre)))=
        wire (Input.field 2 c) (pre++header 3) := left_not _ pre suffix p hc
    rw [wireValue_step,ht,op_not,hleft,
      read_wire circuit (frozenAtom c label) _ _ _ hl,IH _ _ hcL hs]
    simp only [Formula.Holds,decide_not]
  | and p q IHp IHq =>
    have HC : FormulaView.normalize (Input.field 2 c)=pre++(binary false p q).encode++suffix := hc
    apply wire_binary _ env _ pre suffix false p q HC
    · apply IHp _ (q.encode++[true]++suffix)
      · simpa only [encode_binary,List.append_assoc] using HC
      · exact (le_max_left _ _).trans hs
    · apply IHq _ ([true]++suffix)
      · simpa only [encode_binary,List.append_assoc] using HC
      · exact (le_max_right _ _).trans hs
  | or p q IHp IHq =>
    have HC : FormulaView.normalize (Input.field 2 c)=pre++(binary true p q).encode++suffix := hc
    apply wire_binary _ env _ pre suffix true p q HC
    · apply IHp _ (q.encode++[true]++suffix)
      · simpa only [encode_binary,List.append_assoc] using HC
      · exact (le_max_left _ _).trans hs
    · apply IHq _ ([true]++suffix)
      · simpa only [encode_binary,List.append_assoc] using HC
      · exact (le_max_right _ _).trans hs

end LeanCanny.Connectivity.FormulaSignSlotTruth

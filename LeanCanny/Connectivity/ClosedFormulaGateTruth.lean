/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ClosedFormulaGateNodes
public import LeanCanny.Connectivity.MonotoneGateCircles
public import LeanCanny.Connectivity.ClosedFormulaWitness
/-! # The native monotone gate base is the actual original closed formula -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaGateTruth
open ETR Set LeanCanny.Encoding LeanCanny.Computation
open BooleanCircuitSpace FormulaBooleanCircuitSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev F := ClosedFormulaGateMetadata.family
noncomputable abbrev circuit := MonotoneGateArithmetic.circuit F
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  ClosedFormulaGateMetadata.kind ClosedFormulaGateMetadata.atom
  FormulaBooleanCircuitSource.wire FormulaBooleanCircuitSource.left FormulaBooleanCircuitSource.right

noncomputable def statuses (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) : Fin (ClosedFormulaGateMetadata.count c) → Prop :=
  fun i => 0≤MonotoneGateCircles.atomValue F c i x
noncomputable def atom (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) : List Bool → Bool :=
  MonotoneBooleanCircuit.atom circuit c (statuses c x)
noncomputable def wire (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) (i : ℕ) : Bool :=
  wireValue circuit (atom c x) c i

theorem index_lt (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++p.encode++suffix) :
    FormulaBooleanCircuitSource.wire (Input.field 2 c) pre < ClosedFormulaGateMetadata.count c := by
  have HP : 0 < p.encode.length := by simp [Formula.encode]
  change FormulaBooleanCircuitSource.wire (Input.field 2 c) pre < ClosedFormulaGateMetadata.count c
  unfold ClosedFormulaGateMetadata.count FormulaBooleanCircuitSource.wire
  rw [hc]
  simp only [List.length_append]
  omega

theorem step (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) (i : ℕ) (hi : i < ClosedFormulaGateMetadata.count c) :
    wire c x i=operation (ClosedFormulaGateMetadata.kind (pair c (List.replicate i true)))
      (atom c x (pair c (BinaryNatCode.encode i)))
      ((values circuit (atom c x) c i)[F.left (pair c (List.replicate i true))]?.getD false)
      ((values circuit (atom c x) c i)[F.right (pair c (List.replicate i true))]?.getD false) := by
  unfold wire
  rw [wireValue_step]
  simp only [circuit,MonotoneGateArithmetic.circuit,MonotoneGateArithmetic.call_pair F c i hi.le]
  rfl

theorem atom_value (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) (i : ℕ) (hi : i < ClosedFormulaGateMetadata.count c) :
    atom c x (pair c (BinaryNatCode.encode i)) = decide
      (0≤(ClosedFormulaGateMetadata.atom (pair c (List.replicate i true))).eval (Formula.extend x)) := by
  simp only [atom,MonotoneBooleanCircuit.atom,circuit,MonotoneGateArithmetic.circuit,
    pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,statuses,
    MonotoneGateCircles.atomValue,F,ClosedFormulaGateMetadata.family]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,dite_eq_left hi]

private theorem op_zero (a l r : Bool) : operation 0 a l r=false := by cases a <;> cases l <;> cases r <;> decide
private theorem op_one (a l r : Bool) : operation 1 a l r=true := by cases a <;> cases l <;> cases r <;> decide
private theorem op_atom (a l r : Bool) : operation 2 a l r=a := by cases a <;> cases l <;> cases r <;> decide
private theorem op_and (a l r : Bool) : operation 4 a l r=(l&&r) := by cases a <;> cases l <;> cases r <;> decide
private theorem op_or (a l r : Bool) : operation 5 a l r=(l||r) := by cases a <;> cases l <;> cases r <;> decide

private theorem wire_binary (c pre suffix : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) (d : Bool) (p q : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++(binary d p q).encode++suffix)
    (hL : wire c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)))=decide (p.Holds (Formula.extend x)))
    (hR : wire c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)++p.encode))=decide (q.Holds (Formula.extend x))) :
    wire c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre)=decide ((binary d p q).Holds (Formula.extend x)) := by
  have hn := ClosedFormulaGateMetadata.node_at c pre suffix (binary d p q) hc
  have ht : ClosedFormulaGateMetadata.kind (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=binaryTag d := by
    cases d
    · exact ClosedFormulaGateMetadata.kind_and _ p q hn
    · exact ClosedFormulaGateMetadata.kind_or _ p q hn
  have hcL : FormulaView.normalize (Input.field 2 c)=pre++header (binaryTag d)++p.encode++(q.encode++[true]++suffix) := by
    simpa only [encode_binary,List.append_assoc] using hc
  have hcR : FormulaView.normalize (Input.field 2 c)=pre++(header (binaryTag d)++p.encode)++q.encode++([true]++suffix) := by
    simpa only [encode_binary,List.append_assoc] using hc
  have hl := wire_child_lt (Input.field 2 c) pre _ _ p hcL (by simp [header])
  have hr : FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)++p.encode) < FormulaBooleanCircuitSource.wire (Input.field 2 c) pre := by
    simpa only [List.append_assoc] using wire_child_lt (Input.field 2 c) pre _ _ q hcR (by simp [header])
  have hleft : F.left (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)) := by
    change FormulaBooleanCircuitSource.left (ClosedFormulaGateMetadata.query _)=_
    rw [ClosedFormulaGateMetadata.query_pair]
    exact left_binary_at _ pre suffix d p q hc
  have hright : F.right (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)++p.encode) := by
    change FormulaBooleanCircuitSource.right (ClosedFormulaGateMetadata.query _)=_
    rw [ClosedFormulaGateMetadata.query_pair]
    exact right_binary_at _ pre suffix d p q hc
  rw [step c x _ (index_lt c pre suffix _ hc),ht,hleft,hright,
    read_wire circuit (atom c x) c _ _ hl,read_wire circuit (atom c x) c _ _ hr]
  change operation (binaryTag d) _ (wire c x _) (wire c x _)=_
  rw [hL,hR]
  cases d <;> simp [binary,binaryTag,op_and,op_or,Formula.Holds]

theorem wire_formula {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c pre suffix : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++p.encode++suffix)
    (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    wire c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre)=decide (p.Holds (Formula.extend x)) := by
  induction hp generalizing pre suffix with
  | falsum =>
    rw [step c x _ (index_lt c pre suffix _ hc),ClosedFormulaGateMetadata.kind_falsum _ (ClosedFormulaGateMetadata.node_at c pre suffix _ hc),op_zero]
    simp [Formula.Holds]
  | verum =>
    rw [step c x _ (index_lt c pre suffix _ hc),ClosedFormulaGateMetadata.kind_verum _ (ClosedFormulaGateMetadata.node_at c pre suffix _ hc),op_one]
    simp [Formula.Holds]
  | eqZero t =>
    have hn := ClosedFormulaGateMetadata.node_at c pre suffix (.eqZero t) hc
    rw [step c x _ (index_lt c pre suffix _ hc),ClosedFormulaGateMetadata.kind_eqZero _ t hn,op_atom,atom_value c x _ (index_lt c pre suffix _ hc)]
    have HT : t.arity≤ClosedFormulaGateMetadata.dimension (pairFst (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))) := by
      simpa only [pairFst_pair,Formula.arity] using hs
    rw [ClosedFormulaGateMetadata.atom_eqZero _ t hn HT]
    simp only [Term.eval,Int.cast_neg,Int.cast_one,Formula.Holds]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro H; nlinarith [sq_nonneg (t.eval (Formula.extend x))]
    · intro H; rw [H]; norm_num
  | nonnegative t =>
    have hn := ClosedFormulaGateMetadata.node_at c pre suffix (.not (.ltZero t)) hc
    rw [step c x _ (index_lt c pre suffix _ hc),ClosedFormulaGateMetadata.kind_nonnegative _ t hn,op_atom,atom_value c x _ (index_lt c pre suffix _ hc)]
    have HT : t.arity≤ClosedFormulaGateMetadata.dimension (pairFst (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))) := by
      simpa only [pairFst_pair,Formula.arity] using hs
    rw [ClosedFormulaGateMetadata.atom_nonnegative _ t hn HT]
    simp only [Formula.Holds,not_lt]
  | @and p q hp hq ihp ihq =>
    have HC : FormulaView.normalize (Input.field 2 c)=pre++(binary false p q).encode++suffix := hc
    apply wire_binary c pre suffix x false p q HC
    · apply ihp (pre++header (binaryTag false)) (q.encode++[true]++suffix) ?_ (le_trans (Nat.le_max_left _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC
    · apply ihq (pre++header (binaryTag false)++p.encode) ([true]++suffix) ?_ (le_trans (Nat.le_max_right _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC
  | @or p q hp hq ihp ihq =>
    have HC : FormulaView.normalize (Input.field 2 c)=pre++(binary true p q).encode++suffix := hc
    apply wire_binary c pre suffix x true p q HC
    · apply ihp (pre++header (binaryTag true)) (q.encode++[true]++suffix) ?_ (le_trans (Nat.le_max_left _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC
    · apply ihq (pre++header (binaryTag true)++p.encode) ([true]++suffix) ?_ (le_trans (Nat.le_max_right _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC

end LeanCanny.Connectivity.ClosedFormulaGateTruth

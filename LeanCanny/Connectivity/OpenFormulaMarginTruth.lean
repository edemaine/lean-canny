/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginValues
/-! # Every original strict-positive subformula has its exact actual native margin -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaBooleanCircuitSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind
  FormulaBooleanCircuitSource.wire FormulaBooleanCircuitSource.left FormulaBooleanCircuitSource.right
  PositiveMarginValues.value PositiveMarginValues.full PositiveMarginValues.childValue

theorem wire_formula {p : Formula} (hp : OpenFormulaMargin.Open p)
    (c pre suffix : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++p.encode++suffix)
    (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    entry c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre)=OpenFormulaMargin.margin (Formula.extend x) p := by
  induction hp generalizing pre suffix with
  | falsum =>
    have HI:=index_lt c pre suffix _ hc
    have HN:=ClosedFormulaGateMetadata.node_at c pre suffix Formula.falsum hc
    have HK : F.kind (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=0 :=
      OpenFormulaGateMetadata.kind_false _ HN
    rw [entry_valid c x _ HI,PositiveMarginValues.value_zero F c x _ HK]
    rfl
  | verum =>
    have HI:=index_lt c pre suffix _ hc
    have HN:=ClosedFormulaGateMetadata.node_at c pre suffix (Formula.not .falsum) hc
    have HK : F.kind (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=1 :=
      OpenFormulaGateMetadata.kind_verum _ HN
    rw [entry_valid c x _ HI,PositiveMarginValues.value_one F c x _ HK]
    rfl
  | ltZero t =>
    have HI:=index_lt c pre suffix _ hc
    have HN:=ClosedFormulaGateMetadata.node_at c pre suffix (Formula.ltZero t) hc
    have HK : F.kind (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=2 :=
      OpenFormulaGateMetadata.kind_lt _ t HN
    have HT : t.arity≤ClosedFormulaGateMetadata.dimension (pairFst (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))) := by
      simpa only [pairFst_pair,Formula.arity] using hs
    have HA : F.atom (pair c (List.replicate (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre) true))=.mul (.const (-1)) t :=
      OpenFormulaGateMetadata.atom_lt _ t HN HT
    rw [entry_valid c x _ HI,PositiveMarginValues.value_atom F c x _ (source_scope c _ HI) HK,HA]
    simp only [Term.eval,Int.cast_neg,Int.cast_one,neg_one_mul,OpenFormulaMargin.margin]
  | @and p q hp hq IHp IHq =>
    have HC : FormulaView.normalize (Input.field 2 c)=pre++(binary false p q).encode++suffix := hc
    apply value_binary c pre suffix x false p q HC
    · apply IHp (pre++header (binaryTag false)) (q.encode++[true]++suffix) ?_ (le_trans (Nat.le_max_left _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC
    · apply IHq (pre++header (binaryTag false)++p.encode) ([true]++suffix) ?_ (le_trans (Nat.le_max_right _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC
  | @or p q hp hq IHp IHq =>
    have HC : FormulaView.normalize (Input.field 2 c)=pre++(binary true p q).encode++suffix := hc
    apply value_binary c pre suffix x true p q HC
    · apply IHp (pre++header (binaryTag true)) (q.encode++[true]++suffix) ?_ (le_trans (Nat.le_max_left _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC
    · apply IHq (pre++header (binaryTag true)++p.encode) ([true]++suffix) ?_ (le_trans (Nat.le_max_right _ _) hs)
      simpa only [encode_binary,List.append_assoc] using HC

end LeanCanny.Connectivity.OpenFormulaMarginValues

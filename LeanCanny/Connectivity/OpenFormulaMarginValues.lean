/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.OpenFormulaGateNodes
public import LeanCanny.Connectivity.PositiveMarginNatValue
public import LeanCanny.Connectivity.OpenFormulaMargin
public import LeanCanny.Connectivity.ClosedFormulaGateTruth
/-! # Actual source margin values follow the original Boolean constructors -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaBooleanCircuitSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev F := OpenFormulaGateMetadata.family
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind
  FormulaBooleanCircuitSource.wire FormulaBooleanCircuitSource.left FormulaBooleanCircuitSource.right
  PositiveMarginValues.value PositiveMarginValues.full PositiveMarginValues.childValue PositiveMarginValues.natValue

noncomputable def entry (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) (i : ℕ) : ℝ :=
  PositiveMarginValues.natValue F c x i

theorem index_lt (c pre suffix : List Bool) (p : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++p.encode++suffix) :
    FormulaBooleanCircuitSource.wire (Input.field 2 c) pre < ClosedFormulaGateMetadata.count c :=
  ClosedFormulaGateTruth.index_lt c pre suffix p hc

theorem source_scope (c : List Bool) :
    ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c := by
  intro i _
  simpa only [F,OpenFormulaGateMetadata.family,pairFst_pair] using
    OpenFormulaGateMetadata.atom_scope (pair c (List.replicate i true))

theorem entry_valid (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) (i : ℕ)
    (hi : i < ClosedFormulaGateMetadata.count c) : entry c x i=PositiveMarginValues.value F c x ⟨i,hi⟩ :=
  PositiveMarginValues.natValue_valid F c x i hi

theorem child_as_entry (c : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ)
    (i : Fin (F.count c)) (j : ℕ) (hj : j < i.val) : PositiveMarginValues.childValue F c x i j=entry c x j :=
  PositiveMarginValues.child_natValue F c x i j hj

theorem value_binary (c pre suffix : List Bool) (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ)
    (d : Bool) (p q : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=pre++(binary d p q).encode++suffix)
    (hL : entry c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)))=OpenFormulaMargin.margin (Formula.extend x) p)
    (hR : entry c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)++p.encode))=OpenFormulaMargin.margin (Formula.extend x) q) :
    entry c x (FormulaBooleanCircuitSource.wire (Input.field 2 c) pre)=OpenFormulaMargin.margin (Formula.extend x) (binary d p q) := by
  have HN:=ClosedFormulaGateMetadata.node_at c pre suffix (binary d p q) hc
  have HI:=index_lt c pre suffix _ hc
  let i : Fin (F.count c):=⟨FormulaBooleanCircuitSource.wire (Input.field 2 c) pre,HI⟩
  have hcL : FormulaView.normalize (Input.field 2 c)=pre++header (binaryTag d)++p.encode++(q.encode++[true]++suffix) := by
    simpa only [encode_binary,List.append_assoc] using hc
  have hcR : FormulaView.normalize (Input.field 2 c)=pre++(header (binaryTag d)++p.encode)++q.encode++([true]++suffix) := by
    simpa only [encode_binary,List.append_assoc] using hc
  have HL:=wire_child_lt (Input.field 2 c) pre _ _ p hcL (by simp [header])
  have HR : FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)++p.encode) < i.val := by
    simpa only [List.append_assoc] using wire_child_lt (Input.field 2 c) pre _ _ q hcR (by simp [header])
  have HLeft : F.left (pair c (List.replicate i.val true))=FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)) := by
    change FormulaBooleanCircuitSource.left (ClosedFormulaGateMetadata.query _)=_
    rw [ClosedFormulaGateMetadata.query_pair]
    exact left_binary_at _ pre suffix d p q hc
  have HRight : F.right (pair c (List.replicate i.val true))=FormulaBooleanCircuitSource.wire (Input.field 2 c) (pre++header (binaryTag d)++p.encode) := by
    change FormulaBooleanCircuitSource.right (ClosedFormulaGateMetadata.query _)=_
    rw [ClosedFormulaGateMetadata.query_pair]
    exact right_binary_at _ pre suffix d p q hc
  have HV : PositiveMarginValues.value F c x i=
      if d then PositiveMarginValues.childValue F c x i (F.left (pair c (List.replicate i.val true)))+
        PositiveMarginValues.childValue F c x i (F.right (pair c (List.replicate i.val true))) else
        PositiveMarginValues.childValue F c x i (F.left (pair c (List.replicate i.val true)))*
          PositiveMarginValues.childValue F c x i (F.right (pair c (List.replicate i.val true))) := by
    cases d
    · exact PositiveMarginValues.value_mul F c x i (OpenFormulaGateMetadata.kind_and _ p q HN)
    · exact PositiveMarginValues.value_add F c x i (OpenFormulaGateMetadata.kind_or _ p q HN)
  rw [HLeft,HRight,child_as_entry c x i _ HL,child_as_entry c x i _ HR,hL,hR] at HV
  rw [entry_valid c x _ HI]
  exact HV.trans (by cases d <;> rfl)

end LeanCanny.Connectivity.OpenFormulaMarginValues

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.StrictOrSourceMetadata
public import LeanCanny.Connectivity.StrictUnionWitnessSource
/-! # An actual canonical strict-OR input reduces natively to one component-preserving equation -/
@[expose] public section
namespace LeanCanny.Connectivity.StrictOrNativeReduction
open ETR Set LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev F := StrictOrSourceMetadata.family
attribute [local irreducible] pair Input.field FormulaView.normalize
  StrictOrSourceMetadata.dimension StrictOrSourceMetadata.count StrictOrSourceMetadata.raw StrictOrSourceMetadata.atom

 theorem source_scope (c : List Bool) :
    ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c := by
  intro i _
  simpa only [F,StrictOrSourceMetadata.family,pairFst_pair] using
    StrictOrSourceMetadata.atom_scope (pair c (List.replicate i true))

theorem original_holds {p : Formula} (hp : StrictOrSyntax.Strict p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤StrictOrSourceMetadata.dimension c)
    (x : Fin (StrictOrSourceMetadata.dimension c) → ℝ) :
    (StrictUnionWitnessFormula.originalDescription (F.dimension c) (F.count c)
      (StrictUnionWitnessSource.terms F c)).formula.Holds (Formula.extend x) ↔ p.Holds (Formula.extend x) := by
  unfold StrictUnionWitnessFormula.originalDescription
  rw [StrictUnionWitnessFormula.original_holds]
  simp only [StrictUnionWitnessFormula.family,StrictUnionWitnessSource.terms,F,StrictOrSourceMetadata.family]
  constructor
  · rintro ⟨i,HI⟩
    rw [StrictOrSourceMetadata.atom_pair hp c hc hs i.val] at HI
    by_cases H : i.val < (StrictOrSyntax.atoms p).length
    · rw [List.getElem?_eq_getElem H,Option.getD_some] at HI
      exact (StrictOrSyntax.holds_iff hp (Formula.extend x)).mpr ⟨_,List.getElem_mem H,HI⟩
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt H),Option.getD_none] at HI
      norm_num [Term.eval] at HI
  · intro H
    obtain ⟨t,HT,HP⟩ := (StrictOrSyntax.holds_iff hp (Formula.extend x)).mp H
    obtain ⟨i,hi,HE⟩ := List.mem_iff_getElem.mp HT
    have HCount : i < StrictOrSourceMetadata.count c := by
      unfold StrictOrSourceMetadata.count
      rw [StrictOrSourceMetadata.raw_eq hp c hc]
      exact hi.trans_le (SumSquares.forest_length_ge _)
    refine ⟨⟨i,HCount⟩,?_⟩
    rw [StrictOrSourceMetadata.atom_pair hp c hc hs i,List.getElem?_eq_getElem hi,Option.getD_some,HE]
    exact HP

theorem original_connected_iff {p : Formula} (hp : StrictOrSyntax.Strict p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤StrictOrSourceMetadata.dimension c) :
    (StrictUnionWitnessFormula.originalDescription (F.dimension c) (F.count c) (StrictUnionWitnessSource.terms F c)).Connected ↔
      (Description.mk (StrictOrSourceMetadata.dimension c) p).Connected := by
  have HW := StrictUnionWitnessSource.original_wellFormed F c (source_scope c)
  have HP : (Description.mk (StrictOrSourceMetadata.dimension c) p).WellFormed := hs
  have HE : (StrictUnionWitnessFormula.originalDescription (F.dimension c) (F.count c) (StrictUnionWitnessSource.terms F c)).realization=
      (Description.mk (StrictOrSourceMetadata.dimension c) p).realization := by
    ext x
    exact original_holds hp c hc hs x
  simp only [Description.Connected,HW,HP,true_and]
  rw [HE]

noncomputable def writer (c : List Bool) : List Bool := StrictUnionWitnessSource.equationWriter F c

theorem writer_FP : writer ∈ FP := StrictUnionWitnessSource.equationWriter_FP F StrictOrSourceMetadata.access

theorem language_iff {p : Formula} (hp : StrictOrSyntax.Strict p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤StrictOrSourceMetadata.dimension c) :
    writer c∈connectedLanguage ↔ (Input.whole (Description.mk (StrictOrSourceMetadata.dimension c) p)).encode∈connectedLanguage := by
  have H:=StrictUnionWitnessSource.equation_language_iff F c (source_scope c)
  rw [whole_encode_mem_iff] at H ⊢
  exact H.trans (original_connected_iff hp c hc hs)

theorem dimension_whole (d : Description) : StrictOrSourceMetadata.dimension (Input.whole d).encode=d.dimension := by
  unfold StrictOrSourceMetadata.dimension ClosedFormulaGateMetadata.dimension
  rw [Input.field_whole_dimension,Codec.unaryValue_toBits]

theorem canonical_language_iff (d : Description) (hp : StrictOrSyntax.Strict d.formula) (hd : d.WellFormed) :
    writer (Input.whole d).encode∈connectedLanguage ↔ (Input.whole d).encode∈connectedLanguage := by
  have HC : FormulaView.normalize (Input.field 2 (Input.whole d).encode)=d.formula.encode := by
    rw [Input.field_whole_space,FormulaView.normalize_encode]
  have HS : d.formula.arity≤StrictOrSourceMetadata.dimension (Input.whole d).encode := by rw [dimension_whole]; exact hd
  have H:=language_iff hp (Input.whole d).encode HC HS
  have HE : Description.mk (StrictOrSourceMetadata.dimension (Input.whole d).encode) d.formula=d := by rw [dimension_whole]
  rw [HE] at H
  exact H

end LeanCanny.Connectivity.StrictOrNativeReduction
